{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}

module Data.Incrementalized.NumericSpec where

import           Data.Delta
import           Data.DeltaSpec
import           Data.IFq
import           Data.IFqTU
import           Data.Incrementalized
import           Data.Incrementalized.Numeric
import           Data.Monoid                    (Sum (..))
import           Language.Unembedding

import           Data.Incrementalized.GroupSpec
import           Data.IncrementalizedSpec

import           Data.Proxy

import           Test.Hspec
import           Test.QuickCheck

deriving newtype instance Arbitrary (Delta Int)
deriving newtype instance Arbitrary (Delta (Sum Int))

doublePlus :: IncrementalizedFunc Int Int
doublePlus  = $$( compileCode $ runMonoWith ( Proxy :: Proxy IFqTU ) $ \x -> x + x )

doubleConst :: IncrementalizedFunc Int Int
doubleConst = $$( compileCode $ runMonoWith ( Proxy :: Proxy IFqTU ) $ \x -> 2 * x )

xxy :: IncrementalizedFunc (Int, Int) Int
xxy = $$( compileCode $ runMonoWith ( Proxy :: Proxy IFqTU ) $ \xy -> share (fstF xy) $ \x -> x + x + sndF xy )

propIntOk :: Spec
propIntOk = do
  let p = Proxy :: Proxy Int
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p
    checkDiffReplaceLaws p

propProductOk :: Spec
propProductOk = do
  let p = Proxy :: Proxy (Int, (Int, ()))
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p
    checkDiffReplaceLaws p

propDoublePlus :: Spec
propDoublePlus = do
  it "doublePlus is incrementalized" $ do
    propIncrementalizedFunc doublePlus
  it "doublePlus 'doubles'" $ do
    property $ \x -> fst (doublePlus x) === (x + x :: Int)

propDoubleConst :: Spec
propDoubleConst = do
  it "doubleConst is incrementalized" $ do
    propIncrementalizedFunc doubleConst
  it "doubleConst 'doubles'" $ do
    property $ \x -> fst (doubleConst x) === (x + x :: Int)

xxyOk :: Spec
xxyOk = do
  it "xxy is incrementalized" $ do
    propIncrementalizedFunc xxy
  it "xxy computes 'x + x + y'" $ do
    property $ \(x,y) -> fst (xxy (x,y)) === (x + x + y :: Int)

testNumeric :: Spec
testNumeric = do
  describe "Numeric operations (currently, on Int)" $ do
    propIntOk
    propProductOk
    propDoublePlus
    propDoubleConst
    xxyOk


