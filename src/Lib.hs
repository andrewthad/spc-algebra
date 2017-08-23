{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall #-}

module Lib where

import Topaz.Types
import Topaz.Rec (Rec(..))
import Control.Applicative
import Data.Kind (Type)
import Data.Type.Equality
import Data.Monoid
import Data.Proxy
import Data.Function
import qualified Topaz.Rec as R
import qualified GHC.OldList as L

data Field = Name | Age | Height
data Universe = UniverseString | UniverseInt | UniversePerson
-- data Atom xs = AtomType Type | AtomSub xs
data Atom k where
  AtomType :: Type -> Atom k
  AtomSub :: forall (as :: [k]). Proxy as -> Atom k

data DeepRec :: (k -> Type) -> Deep j k -> Type where
  DeepRec :: Rec f rs -> Rec (NestRec f) ns -> DeepRec f ('Deep b ns rs)

data Deep b a = Deep b [Nest a] [a]

type family InterpretField (f :: Field) :: Universe where
  InterpretField 'Name = 'UniverseString
  InterpretField 'Age = 'UniverseInt
  InterpretField 'Height = 'UniverseInt

type family GroundUniverse (u :: Universe) :: Atom Field where
  GroundUniverse 'UniverseString = 'AtomType String
  GroundUniverse 'UniverseInt = 'AtomType Int
  -- GroundUniverse 'UniversePerson = Atom

type family Interpretation f :: u
type family Interpret (x :: f) :: (Interpretation f)
type family Ground f (x :: Interpretation f) :: Atom f

type instance Interpretation Field = Universe
type instance Interpret x = InterpretField x
type instance Ground Field (x :: Universe) = GroundUniverse x

data Value j (f :: j) where
  ValueSub :: forall (j :: Type) (xs :: [j]) (f :: j) (p :: Proxy xs). 
       (p ~ 'Proxy, 'AtomSub p ~ Ground j (Interpret f))
    => [Rec (Value j) (xs :: [j])]
    -> Value j f
  ValueType :: forall x (f :: j). ('AtomType x ~ Ground j (Interpret f))
    => x -> Value j f

coerceValue :: forall (f :: k) (g :: k). (Interpret f :~: Interpret g) -> Value k f -> Value k g
coerceValue Refl (ValueType x) = ValueType x
coerceValue Refl (ValueSub x) = ValueSub x

 
-- newtype Value x = Value { getValue :: Ground (Interpret x) }

data Relation k (as :: [k]) where
  Table :: forall k (as :: [k]). [Rec (Value k) as] -> Relation k as
  Union :: Relation k as -> Relation k as -> Relation k as
  Join :: Relation k as -> Relation k bs -> Relation k (as ++ bs)
  Antijoin :: Rec (Elem as) bs -> Relation k as -> Relation k bs -> Relation k as
  Project :: Rec (Elem as) bs -> Relation k as -> Relation k bs
  Restrict :: Restriction as -> Relation k as -> Relation k as
  Group :: forall k (as :: [k]) (bs :: [k]) (c :: k) (p :: Proxy as). (p ~ 'Proxy)
    => Rec (Elem as) bs -> Relation k as -> (Ground k (Interpret c) :~: 'AtomSub p) -> Relation k (c ': bs)

data Restriction as where
  RestrictionValue :: forall k (as :: [k]) (r :: k). Elem as r -> Value k r -> Restriction as
  RestrictionColumns :: (Interpret a :~: Interpret b) -> Elem as a -> Elem as b -> Restriction as

evaluate :: forall k (as :: [k]).
     (forall (x :: k). Value k x -> Value k x -> Bool)
  -> (forall (x :: k). Value k x -> Value k x -> Ordering)
  -> Relation k as 
  -> [Rec (Value k) as]
evaluate runEq runOrd = go
  where
  go :: forall (bs :: [k]). Relation k bs -> [Rec (Value k) bs]
  go (Table xs) = xs
  go (Union as bs) = go as ++ go bs
  go (Project ixs r) = map (R.gets ixs) (go r)
  go (Join as bs) = liftA2 R.append (go as) (go bs)
  go (Antijoin ixs as bs) =
    let asVals = go as
        bsVals = go bs
     in L.filter (\r -> 
          let asSub = R.gets ixs r 
          in not (L.any (\theBs -> liftRecEq runEq theBs asSub) bsVals)
        ) asVals
  go (Restrict res as) = let recs = (go as) in case res of
    RestrictionValue ix v ->
      L.filter (\r -> runEq (R.get ix r) v) recs
    RestrictionColumns refl@Refl ixA ixB ->
      L.filter (\r -> 
        let valA = R.get ixA r in
        runEq
          valA -- (Value (getValue (R.get ixA r)) `asTypeOf` valA)
          (coerceValue refl (R.get ixB r)) -- (Value (getValue (R.get ixB r)) `asTypeOf` valA)
      ) recs
  go (Group ixs as Refl) = go as
    & L.sortBy (liftRecOrd runOrd)
    & L.groupBy (liftRecEq runEq)
    & map (\xs@(x : _) ->
        let groupByVals = R.gets ixs x
         in RecCons (ValueSub xs) groupByVals
      )

liftRecEq :: (forall x. f x -> f x -> Bool) -> Rec f rs -> Rec f rs -> Bool
liftRecEq f as = getAll . R.foldMap getConst . R.zipWith (\x y -> Const (All (f x y))) as

liftRecOrd :: (forall x. f x -> f x -> Ordering) -> Rec f rs -> Rec f rs -> Ordering
liftRecOrd f as = R.foldMap getConst . R.zipWith (\x y -> Const (f x y)) as

