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

deriving newtype instance Arbitrary a => Arbitrary (GroupChange a)
deriving newtype instance Arbitrary a => Arbitrary (WithGroupChange a)
deriving newtype instance Arbitrary a => Arbitrary (WithGroupChangeReplace a)

instance Arbitrary a => Arbitrary (GroupChangeWithReplace a) where
  arbitrary = either InjGroupChange Replace <$>
              frequency [ (3, arbitrary),
                          (1, arbitrary) ]

  shrink = fmap (either InjGroupChange Replace) . shrink . g2e
    where
      g2e (InjGroupChange a) = Left a
      g2e (Replace     a)    = Right a

deriving newtype instance Arbitrary a => Arbitrary (Delta (WithGroupChange a))
deriving newtype instance Arbitrary a => Arbitrary (Delta (WithGroupChangeReplace a))

propIntOk :: Spec
propIntOk = do
  let p = Proxy :: Proxy (WithGroupChange (Sum Int))
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p
--    checkDiffReplaceLaws p

propIntProductOk :: Spec
propIntProductOk = do
  let p = Proxy :: Proxy (WithGroupChange (Sum Int, Sum Int, ()))
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p
--    checkDiffReplaceLaws p

propIntProductROk :: Spec
propIntProductROk = do
  let p = Proxy :: Proxy (WithGroupChangeReplace (Sum Int, Sum Int, ()))
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p
    checkDiffReplaceLaws p

testGroup :: Spec
testGroup = describe "Group Change" $ do
  propIntOk
  propIntProductOk
  propIntProductROk
