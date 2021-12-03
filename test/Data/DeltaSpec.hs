{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.DeltaSpec
  (
    checkDiffLaws, checkDiffMinusLaws, checkDiffReplaceLaws,
    describeProxy,

    testDelta
  )
where

import           Data.Delta

import           Data.Typeable
import           Test.Hspec
import           Test.QuickCheck

propDiff1
  :: (Diff a, Eq a, Show a) => a -> Property
propDiff1 x
  = x /+ mempty === x

propCheckEmpty :: (Diff a, Eq a) => a -> Delta a -> Property
propCheckEmpty x dx =
  -- checks contraposition
  x /+ dx /= x ==> not (checkEmpty dx)


propDiff2
  :: (Diff a, Show a, Eq a) => a -> Delta a -> Delta a -> Property
propDiff2 x dx1 dx2
  = x /+ (dx1 <> dx2) === (x /+ dx1) /+ dx2

propDiffMinus
  :: (DiffMinus a, Show a, Eq a) => a -> a -> Property
propDiffMinus x y
  = x /+ (y /- x) === y

propDiffReplace
  :: (DiffReplace a, Show a, Eq a) => a -> a -> Property
propDiffReplace x y
  = x /+ replaceTo y === y


describeProxy :: Typeable a1 => Proxy a1 -> SpecWith a2 -> SpecWith a2
describeProxy (p :: Proxy a) ts = do
  describe (show $ typeRep p) ts

checkDiffLaws ::
  (Diff a, Eq a, Arbitrary a, Arbitrary (Delta a), Show a, Show (Delta a)) =>
  Proxy a -> Spec
checkDiffLaws (_ :: Proxy a) = do
  it "satisfies the Diff law for mempty" $
    property $ \(x :: a) -> propDiff1 x
  it "satisfies the Diff law for mappend" $
    property $ \(x :: a) dx1 dx2 -> propDiff2 x dx1 dx2
  -- it "equips checkEmpty that soundly checks whether an update is an identity" $
  --   property $ \(x :: a) dx -> propCheckEmpty x dx

checkDiffMinusLaws ::
  (DiffMinus a, Eq a, Arbitrary a, Arbitrary (Delta a), Show a, Show (Delta a)) =>
  Proxy a -> Spec
checkDiffMinusLaws (_ :: Proxy a) = do
  it "satisfies the DiffMinus law" $
    property $ \(x :: a) y -> propDiffMinus x y

checkDiffReplaceLaws ::
  (DiffReplace a, Eq a, Arbitrary a, Arbitrary (Delta a), Show a, Show (Delta a)) =>
  Proxy a -> Spec
checkDiffReplaceLaws (_ :: Proxy a) = do
  it "satisifes the DiffReplace law" $
    property $ \(x :: a) y -> propDiffReplace x y

deriving newtype instance Arbitrary (Delta Int)
deriving newtype instance Arbitrary (Delta ())
deriving newtype instance Arbitrary (Delta Word)

instance (Arbitrary (Delta a), Arbitrary (Delta b)) => Arbitrary (Delta (a, b)) where
  arbitrary = fmap (uncurry PairDelta) arbitrary
  shrink (PairDelta a b) =
    uncurry PairDelta <$> shrink (a, b)


propIntOk :: Spec
propIntOk = do
  let p = Proxy :: Proxy Int
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p

propWordOk :: Spec
propWordOk = do
  let p = Proxy :: Proxy Word
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p

propUnitOk :: Spec
propUnitOk = do
  let p = Proxy :: Proxy ()
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p
    checkDiffReplaceLaws p

propProductOk :: Spec
propProductOk = do
  let p = Proxy :: Proxy ((Int, Word), ())
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p


testDelta :: Spec
testDelta = describe "Diff instances of primitives" $ do
  propUnitOk
  propIntOk
  propWordOk
  propProductOk

