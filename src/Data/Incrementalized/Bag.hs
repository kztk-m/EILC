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
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE FlexibleInstances          #-}

module Data.Incrementalized.Bag
  (
    module Data.Incrementalized.Fixed,

    Bag, Map(..), Delta(..),

    foldBag, myFoldMap,

    foldBagF, foldMapF,

    singletonBagF,
    singletonMapF,

    -- * Functions used in Spliced Code
    singletonBagI, singletonBagTr,
    singletonMapI, singletonMapTr,

    -- foldBagI, foldBagTr,
    -- foldMapI, foldMapTr,

    -- * Some Examples (will be moved)
    mapReduce, histogram,
  )
where


import           Prelude                             hiding (id, (.))

import           Data.IFq


import           Data.Delta
import           Data.Group
import           Data.Incrementalized                (fromFunctionsCode,
                                                      fromStatelessCode)
import           Data.Incrementalized.Fixed
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



-- -- [???] I don't know but the following code causes GHC to panic.
-- foldBagF :: forall term e a t.(Typeable a, Ord a, Group t, Eq t, DiffGroupChange t, Typeable t, PFunTerm IFqS term, App2 IFqS term e) => (e (Fixed a) -> e t) -> e (Bag a) -> e t
-- foldBagF f =
--   lift foldUListC . liftSO2 (Proxy @'[ '[(Fixed a, Sum Int)], '[] ]) (fromPFun convertMapC) (f . fstF)

foldBagF :: forall term e a t.(Typeable a, Ord a, Abelian t, Eq t, DiffGroupChange t, Typeable t, PFunTerm IFqS term, App2 IFqS term e) => (e (Fixed a) -> e t) -> e (Bag a) -> e t
foldBagF h = foldMapF (\x y -> lift powC $ pair (h x) y)

  -- liftSO2 (Proxy @'[ '[a], '[] ]) $ fromPFun foldBagC

-- [???] I don't know but the following code causes GHC to panic.
foldMapF :: forall term e k a t.(DiffGroupChange a, Typeable a, Monoid a, Eq a, Ord k, Typeable k, Eq t, Abelian t, DiffGroupChange t, Typeable t, PFunTerm IFqS term, App2 IFqS term e) => (e (Fixed k) -> e a -> e t) -> e (Map (Fixed k) a) -> e t
foldMapF f = -- liftSO2 (Proxy @'[ '[(k,a)], '[] ]) (fromPFun foldMapC) (\ab -> f (fstF ab) (sndF ab))
  lift foldUListC . liftSO2 (Proxy @'[ '[(Fixed k,a)], '[] ]) (fromPFun convertMapC) (\ab -> f (fstF ab) (sndF ab))

-- singletonBagTr ::
--   Coercible (Delta a) a => Delta a -> Delta (Bag a)
-- singletonBagTr da = DeltaBag (GroupChange (singletonBag $ coerce da))

singletonBagF ::
  (Typeable a, Ord a, App2 IFqS term e) => e (Fixed a) -> e (Bag a)
singletonBagF =
  lift (fromStatelessCode (\a -> [|| singletonBag $$a ||]) (\a -> [|| singletonBagTr $$a ||]))
  -- lift (fromFunctionsCode [|| singletonBagI ||] [|| singletonBagTr ||])
  -- lift (fromStatelessCode (\a -> [|| singletonBag $$a ||]) (\da -> [|| singletonBagTr $$da ||]))


singletonMapF ::
  (App IFqS e, Group v, DiffGroupChange v, Eq v, Ord k,
   Typeable v, Typeable k) =>
  e (Fixed k) -> e v -> e (Map (Fixed k) v)
singletonMapF k v =
  lift (fromFunctionsCode [|| singletonMapI ||] [|| singletonMapTr ||]) $ pair k v

mapReduce ::
  forall term e k1 v1 k2 v2 v3 .
  (App2 IFqS term e, PFunTerm IFqS term,
    Typeable k1, Ord k1,
    Typeable v1, DiffGroupChange v1, Monoid v1, Eq v1,
    Typeable k2, Ord k2,
    Ord v2, Typeable v2,
    Typeable v3, Abelian v3, DiffGroupChange v3, Eq v3) =>
  (e (Fixed k1) -> e v1 -> e (Bag (k2, v2))) -> (e (Fixed k2) -> e (Bag v2) -> e v3) -> e (Map (Fixed k1) v1) -> e (Map (Fixed k2) v3)
mapReduce mapper reducer = reducePerKey . groupByKey . mapPerKey
  where
    mapPerKey :: e (Map (Fixed k1) v1) -> e (Bag (k2, v2))
    mapPerKey  = foldMapF mapper
    groupByKey :: e (Bag (k2, v2)) -> e (Map (Fixed k2) (Bag v2))
    groupByKey = foldBagF (\kv ->
                             share (fstFixedF kv) $ \key ->
                             share (sndFixedF kv) $ \val ->
                             singletonMapF key (singletonBagF val))
    reducePerKey :: e (Map (Fixed k2) (Bag v2)) -> e (Map (Fixed k2) v3)
    reducePerKey = foldMapF (\key bag -> singletonMapF key (reducer key bag))

constF :: (Diff n, Typeable n, TH.Lift n, App IFqS e) => n -> e n
constF n = lift u2n unit
  where
    u2n = fromStatelessCode (const [|| n ||]) (const [|| mempty ||])

newtype MyInt = MyInt Int
  deriving newtype (Num, Real, Integral, Enum, Eq, Ord)
  deriving stock TH.Lift
  deriving (Semigroup, Monoid, Group, Abelian) via Sum Int

newtype instance Delta MyInt = DeltaMyInt (GroupChange MyInt)
  deriving newtype (Semigroup, Monoid)

deriving via WithGroupChange MyInt instance Diff MyInt
deriving via WithGroupChange MyInt instance DiffMinus MyInt
deriving via WithGroupChange MyInt instance DiffGroupChange MyInt


histogram ::
  forall e term w.
  (Typeable w, Ord w, App2 IFqS term e, PFunTerm IFqS term)
  => e (Map (Fixed Int) (Bag w)) -> e (Map (Fixed w) MyInt)
histogram = mapReduce hmap hreduce
  where
    hmap :: e (Fixed Int) -> e (Bag w) -> e (Bag (w, MyInt))
    hmap    _ = foldBagF (\n -> singletonBagF (pairFixedF n (constF 1)))
    hreduce :: e (Fixed w) -> e (Bag MyInt) -> e MyInt
    hreduce _ = foldBagF getFixedF


