{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Main (main) where

import           Test.Hspec
import           Test.QuickCheck

import           Data.Delta

import           Data.Typeable

deriving newtype instance Arbitrary (Delta Int)

instance Arbitrary (Delta (Int, Int)) where
  arbitrary = fmap (uncurry PairDelta) arbitrary
  shrink (PairDelta a b) =
    fmap (uncurry PairDelta) $ shrink (a, b)

-- deriving newtype instance Arbitrary (Delta (Int, Int))

propDiff1
  :: (Diff a, Eq a) => a -> Bool
propDiff1
  = \x -> x /+ mempty == x

propDiff2
  :: (Diff a, Eq a) => a -> Delta a -> Delta a -> Bool
propDiff2
  = \x dx1 dx2 -> x /+ (dx1 <> dx2) == (x /+ dx1) /+ dx2

propDiffMinus
  :: (DiffMinus a, Eq a) => a -> a -> Bool
propDiffMinus
  = \x y -> x /+ (y /- x) == y

propDiffReplace
  :: (DiffReplace a, Eq a) => a -> a -> Bool
propDiffReplace
  = \x y -> x /+ replaceTo y == y

describeProxy (p :: Proxy a) ts = do
  describe (show $ typeRep p) ts

checkDiffLaws (_ :: Proxy a) = do
  it "satisfies the Diff law for mempty" $
    property $ \(x :: a) -> propDiff1 x
  it "satisfies the Diff law for mappend" $
    property $ \(x :: a) dx1 dx2 -> propDiff2 x dx1 dx2

checkDiffMinusLaws (_ :: Proxy a) = do
  it "satisfies the DiffMinus law" $
    property $ \(x :: a) y -> propDiffMinus x y

checkDiffReplaceLaws (_ :: Proxy a) = do
  it "satisifes the DiffReplace law" $
    property $ \(x :: a) y -> propDiffReplace x y

main :: IO ()
main = hspec $ do
  let pInt = Proxy :: Proxy Int
  describeProxy pInt $ do
    checkDiffLaws pInt
    checkDiffMinusLaws pInt
  let pPairInt = Proxy :: Proxy (Int, Int)
  describeProxy pPairInt $ do
    checkDiffLaws pPairInt
    checkDiffMinusLaws pPairInt

