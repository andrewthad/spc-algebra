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
import Data.Functor.Compose
import qualified Topaz.Rec as R
import qualified GHC.OldList as L

data Field = Name | Age | Height
data Universe = UniverseString | UniverseInt | UniversePerson
-- data Atom xs = AtomType Type | AtomSub xs
data Atom k where
  AtomType :: Type -> Atom k
  AtomSub :: forall (as :: [k]). Proxy as -> Atom k

data ShallowRec :: (k -> Type) -> Shallow j k -> Type where
  ShallowRec :: Rec f rs -> Rec (DeepRec f) ns -> ShallowRec f ('Shallow ns rs)

data DeepRec :: (k -> Type) -> Deep j k -> Type where
  DeepRec :: Rec (Compose [] (ShallowRec f)) gs -> Rec f rs -> Rec (DeepRec f) ns -> DeepRec f ('Deep b ns gs rs)

-- data TaggedRecs :: Pair t (Shallow j k) -> Type where
--   TaggedRecs :: [ShallowRec f ('Shallow ns rs)] -> TaggedRecs ('Pair t ('Shallow ns rs))

data Pair a b = Pair a b
data Shallow b a = Shallow [Deep b a] [a]
data Deep b a = Deep b [Deep b a] [Shallow b a] [a]

data DeepElem :: Deep b a -> a -> Type where
  DeepElemValue :: forall (a :: k) (as :: [k]) (b :: j) (ds :: [Deep j k]) (ss :: [Shallow j k]).
    Elem as a -> DeepElem ('Deep b ds ss as) a
  DeepElemKey :: DeepElem ('Deep b xs ys zs) a -> Elem cs ('Deep b xs ys zs) -> DeepElem ('Deep p cs ms ns) a

-- data DeepKey :: [Deep b a] -> b -> Type where
--   DeepKeyHere :: DeepKey ('Deep b ds ss as ': xs) b
--   DeepKeyThere :: DeepKey ds b -> DeepKey (e ': ds) b

indexDeep :: DeepElem d a -> DeepRec f d -> f a
indexDeep (DeepElemValue e) (DeepRec _ rs _) = R.get e rs
indexDeep (DeepElemKey de dk) (DeepRec _ _ ds) = indexDeep de (R.get dk ds)

-- indexDeepKey :: DeepKey ds b -> Deep ds 

type family InterpretField (f :: Field) :: Universe where
  InterpretField 'Name = 'UniverseString
  InterpretField 'Age = 'UniverseInt
  InterpretField 'Height = 'UniverseInt

type family GroundUniverse (u :: Universe) :: Type where
  GroundUniverse 'UniverseString = String
  GroundUniverse 'UniverseInt = Int
  -- GroundUniverse 'UniversePerson = Atom

type family Interpretation f :: u
type family Interpret (x :: f) :: (Interpretation f)
type family Ground (x :: k) :: Type

type instance Interpretation Field = Universe
type instance Interpret x = InterpretField x
type instance Ground (x :: Universe) = GroundUniverse x

newtype Value x = Value { getValue :: Ground (Interpret x) }

coerceValue :: forall (f :: k) (g :: k). (Interpret f :~: Interpret g) -> Value f -> Value g
coerceValue Refl (Value x) = Value x

 
-- newtype Value x = Value { getValue :: Ground (Interpret x) }

data Relation :: [Deep k v] -> [v] -> Type where
  Table :: [ShallowRec Value ('Shallow ds as)] -> Relation ds as
  Union :: Relation ds as -> Relation ds as -> Relation ds as
  Join :: Relation ds as -> Relation es bs -> Relation (ds ++ es) (as ++ bs)
  -- Antijoin :: Rec (Elem as) bs -> Relation as -> Relation bs -> Relation as
  -- Project :: Rec (Elem as) bs -> Relation as -> Relation bs
  -- Restrict :: Restriction as -> Relation as -> Relation as
  -- Group :: forall k (as :: [k]) (bs :: [k]) (c :: k) (p :: Proxy as). (p ~ 'Proxy)
  --   => Rec (Elem as) bs -> Relation k as -> (Ground (Interpret c) :~: p) -> Relation k (c ': bs)
  Group :: 
       Rec (DeepElem ds) xs 
    -> Rec (Elem vs) ys 
    -> Relation ds vs 
    -> Relation ('Deep b '[] '[ 'Shallow ds vs] '[]) (ys ++ xs)

data Restriction as where
  RestrictionValue :: forall k (as :: [k]) (r :: k). Elem as r -> Value r -> Restriction as
  RestrictionColumns :: (Interpret a :~: Interpret b) -> Elem as a -> Elem as b -> Restriction as

evaluate :: forall k j (ds :: [Deep j k]) (as :: [k]).
     (forall (x :: k). Value x -> Value x -> Bool)
  -> (forall (x :: k). Value x -> Value x -> Ordering)
  -> Relation ds as 
  -> [ShallowRec Value ('Shallow ds as)]
evaluate runEq runOrd = go
  where
  go :: forall (es :: [Deep j k]) (bs :: [k]). Relation es bs -> [ShallowRec Value ('Shallow es bs)]
  go (Table xs) = xs
  go (Union as bs) = go as ++ go bs
  -- go (Project ixs r) = map (R.gets ixs) (go r)
  -- go (Join as bs) = liftA2 R.append (go as) (go bs)
  -- go (Antijoin ixs as bs) =
  --   let asVals = go as
  --       bsVals = go bs
  --    in L.filter (\r -> 
  --         let asSub = R.gets ixs r 
  --         in not (L.any (\theBs -> liftRecEq runEq theBs asSub) bsVals)
  --       ) asVals
  -- go (Restrict res as) = let recs = (go as) in case res of
  --   RestrictionValue ix v ->
  --     L.filter (\r -> runEq (R.get ix r) v) recs
  --   RestrictionColumns refl@Refl ixA ixB ->
  --     L.filter (\r -> 
  --       let valA = R.get ixA r in
  --       runEq
  --         valA -- (Value (getValue (R.get ixA r)) `asTypeOf` valA)
  --         (coerceValue refl (R.get ixB r)) -- (Value (getValue (R.get ixB r)) `asTypeOf` valA)
  --     ) recs
  -- go (Group ixs as Refl) = go as
  --   & L.sortBy (liftRecOrd runOrd)
  --   & L.groupBy (liftRecEq runEq)
  --   & map (\xs@(x : _) ->
  --       let groupByVals = R.gets ixs x
  --        in RecCons (ValueSub xs) groupByVals
  --     )

liftRecEq :: (forall x. f x -> f x -> Bool) -> Rec f rs -> Rec f rs -> Bool
liftRecEq f as = getAll . R.foldMap getConst . R.zipWith (\x y -> Const (All (f x y))) as

liftRecOrd :: (forall x. f x -> f x -> Ordering) -> Rec f rs -> Rec f rs -> Ordering
liftRecOrd f as = R.foldMap getConst . R.zipWith (\x y -> Const (f x y)) as

