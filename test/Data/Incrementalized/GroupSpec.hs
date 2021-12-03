{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleInstances          #-}
module Data.Incrementalized.GroupSpec
  (
    testGroup
  ) where

import           Data.Monoid                (Sum (..))
import           Test.Hspec
import           Test.QuickCheck

import           Data.Delta
import           Data.DeltaSpec
import           Data.Incrementalized.Group

import           Data.Typeable

deriving newtype instance Arbitrary a => Arbitrary (FromMonoid a)

instance Arbitrary a => Arbitrary (GroupChangeWithReplace a) where
  arbitrary = either GroupChange Replace <$>
              frequency [ (3, arbitrary),
                          (1, arbitrary) ]

  shrink = fmap (either GroupChange Replace) . shrink . g2e
    where
      g2e (GroupChange a) = Left a
      g2e (Replace     a) = Right a

deriving newtype instance Arbitrary a => Arbitrary (Delta (FromMonoid a))

propIntOk :: Spec
propIntOk = do
  let p = Proxy :: Proxy (FromMonoid (Sum Int))
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p
    checkDiffReplaceLaws p

propIntProductOk :: Spec
propIntProductOk = do
  let p = Proxy :: Proxy (FromMonoid (Sum Int, Sum Int, ()))
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p
    checkDiffReplaceLaws p

testGroup :: Spec
testGroup = describe "Group Change" $ do
  propIntOk
  propIntProductOk
