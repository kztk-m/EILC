{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE FlexibleInstances          #-}

module Data.Incrementalized.Bag
  (
    Bag(..), Delta(..),

    foldBag, myFoldMap,

    foldBagF, foldMapF,

    singletonBagF,
    singletonMapF,

    -- * Functions used in Spliced Code
    singletonBagI, singletonBagTr,
    singletonMapI, singletonMapTr,

    foldBagI, foldBagTr,
    foldMapI, foldMapTr,

    -- * Some Examples (will be moved)
    mapReduce, histogram,
  )
where

import qualified Data.Map.Strict                     as M

import           Prelude                             hiding (id, (.))

import           Data.IFq


import           Data.Delta
import           Data.Group
import           Data.Incrementalized                (fromFunctionsCode,
                                                      fromStatelessCode)
import           Data.Incrementalized.Function
import           Data.Incrementalized.Group
import           Data.Incrementalized.Numeric
import           Data.Monoid                         (Sum (..))
import           Data.Proxy                          (Proxy (Proxy))
import           Data.Typeable                       (Typeable)
import qualified Language.Haskell.TH.Syntax          as TH
import           Language.Unembedding
import           Language.Unembedding.PseudoFunction


import           Data.Incrementalized.Bag.Core



-- [???] I don't know but the following code causes GHC to panic.
foldBagF :: forall term e a t.(Diff a,Typeable a, Ord a, Group t, DiffGroupReplace t, Typeable t, PFunTerm IFqS term, App2 IFqS term e) => (e a -> e t) -> e (Bag a) -> e t
foldBagF = liftSO2 (Proxy @'[ '[a], '[] ]) $ fromPFun foldBagC


-- [???] I don't know but the following code causes GHC to panic.
foldMapF :: forall term e k a t.(Diff a, Typeable a, Semigroup a, Ord k, Diff k, Typeable k, Abelian t, DiffGroupReplace t, Typeable t, PFunTerm IFqS term, App2 IFqS term e) => (e k -> e a -> e t) -> e (Map k a) -> e t
foldMapF f = liftSO2 (Proxy @'[ '[(k,a)], '[] ]) (fromPFun foldMapC) (\ab -> f (fstF ab) (sndF ab))

singletonBagI :: a -> (Bag a, a)
singletonBagI a = (singletonBag a, a)

singletonBagTr :: (Ord a, Diff a) => Delta a -> a -> (Delta (Bag a), a)
singletonBagTr da a =
  let !a' = a /+ da
  in (replaceTo $ singletonBag a', a')


-- singletonBagTr ::
--   Coercible (Delta a) a => Delta a -> Delta (Bag a)
-- singletonBagTr da = DeltaBag (GroupChange (singletonBag $ coerce da))

singletonBagF ::
  (Typeable a, Ord a, Diff a,  App2 IFqS term e) => e a -> e (Bag a)
singletonBagF =
  lift (fromFunctionsCode [|| singletonBagI ||] [|| singletonBagTr ||])
  -- lift (fromStatelessCode (\a -> [|| singletonBag $$a ||]) (\da -> [|| singletonBagTr $$da ||]))

singletonMapI :: (k, v) -> (Map k v, (k,v))
singletonMapI (k, v) = (Map (M.singleton k v), (k, v))

singletonMapTr :: (Ord k, Diff k, Diff v, Group v) => Delta (k, v) -> (k, v) -> (Delta (Map k v), (k, v))
singletonMapTr (PairDelta dk dv) (k, v) =
    let k' = k /+ dk
        v' = v /+ dv
    in (replaceTo (Map (M.singleton k' v')), (k',v'))

singletonMapF ::
  (App IFqS e, Group v, Diff v, Diff k, Ord k,
   Typeable v, Typeable k) =>
  e k -> e v -> e (Map k v)
singletonMapF k v =
  lift (fromFunctionsCode [|| singletonMapI ||] [|| singletonMapTr ||]) $ pair k v

mapReduce ::
  forall term e k1 v1 k2 v2 v3 .
  (App2 IFqS term e, PFunTerm IFqS term,
    Typeable k1, Diff k1, Ord k1,
    Typeable v1, Diff v1, Semigroup v1,
    Typeable k2, Ord k2, Diff k2,
    Ord v2, Typeable v2, Diff v2,
    Typeable v3, Abelian v3, Diff v3) =>
  (e k1 -> e v1 -> e (Bag (k2, v2))) -> (e k2 -> e (Bag v2) -> e v3) -> e (Map k1 v1) -> e (Map k2 v3)
mapReduce mapper reducer = reducePerKey . groupByKey . mapPerKey
  where
    mapPerKey :: e (Map k1 v1) -> e (Bag (k2, v2))
    mapPerKey  = foldMapF mapper
    groupByKey :: e (Bag (k2, v2)) -> e (Map k2 (Bag v2))
    groupByKey = foldBagF (\kv ->
                             share (fstF kv) $ \key ->
                             share (sndF kv) $ \val ->
                             singletonMapF key (singletonBagF val))
    reducePerKey :: e (Map k2 (Bag v2)) -> e (Map k2 v3)
    reducePerKey = foldMapF (\key bag -> singletonMapF key (reducer key bag))

constF :: (Diff n, Typeable n, TH.Lift n, App IFqS e) => n -> e n
constF n = lift u2n unit
  where
    u2n = fromStatelessCode (const [|| n ||]) (const [|| mempty ||])

newtype MyInt = MyInt Int
  deriving newtype (Num, Real, Integral, Enum, Eq, Ord)
  deriving stock TH.Lift
  deriving (Semigroup, Monoid, Group, Abelian) via Sum Int

newtype instance Delta MyInt = DeltaMyInt (GroupChangeWithReplace MyInt)
  deriving newtype (Semigroup, Monoid)

deriving via FromMonoid MyInt instance Diff MyInt
deriving via FromMonoid MyInt instance DiffMinus MyInt
deriving via FromMonoid MyInt instance DiffReplace MyInt

instance DiffGroupReplace MyInt


histogram ::
  forall e term w.
  (Diff w, Typeable w, Ord w, App2 IFqS term e, PFunTerm IFqS term)
  => e (Map Int (Bag w)) -> e (Map w MyInt)
histogram = mapReduce hmap hreduce
  where
    hmap :: e Int -> e (Bag w) -> e (Bag (w, MyInt))
    hmap    _ = foldBagF (\n -> singletonBagF (pair n (constF 1)))
    hreduce :: e w -> e (Bag MyInt) -> e MyInt
    hreduce _ = foldBagF id



