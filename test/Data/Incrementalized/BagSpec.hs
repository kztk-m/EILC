{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
module Data.Incrementalized.BagSpec where

import           Data.Monoid
import           Data.Proxy

import           Data.Delta
import           Data.Incrementalized.Bag
import           Data.Incrementalized.Group       ()

import           Data.IFq
import           Data.IFqTU
import           Language.Unembedding

import           Data.DeltaSpec
import           Data.Incrementalized.GroupSpec   ()
import           Data.Incrementalized.NumericSpec ()
import           Data.IncrementalizedSpec

import           Test.Hspec
import           Test.QuickCheck                  hiding (Fixed (..))

import           Data.Incrementalized
import qualified Data.Map                         as M
import           Test.Hspec.QuickCheck            (modifyMaxSize)

deriving newtype instance Arbitrary a => Arbitrary (Fixed a)

instance (Ord k, Arbitrary k, Arbitrary a) => Arbitrary (Map k a) where
  arbitrary = Map Prelude.. M.fromList <$> listOf ls
    where ls = (,) <$> arbitrary <*> arbitrary

deriving newtype instance (Ord k, Arbitrary k, Arbitrary a) => Arbitrary (Delta (Map (Fixed k) a))

-- deriving newtype instance (Ord a, Arbitrary a) => Arbitrary (Delta (Bag a))

propBagOk :: Spec
propBagOk = do
  let p = Proxy :: Proxy (Bag (Sum Int))
  describeProxy p $ do
    checkDiffLaws p
    checkDiffMinusLaws p
--    checkDiffReplaceLaws p

simpleFoldBag :: IncrementalizedFunc (Bag (Sum Int)) (Sum Int)
simpleFoldBag = $$( compileCode $ runMonoWith (Proxy :: Proxy IFqTU) $ \x ->
                     foldBagF getFixedF x )

simpleFoldBag2 :: IncrementalizedFunc (Sum Int, Bag (Sum Int)) (Sum Int)
simpleFoldBag2 = $$( compileCode $ runMonoWith (Proxy :: Proxy IFqTU) $ \xy ->
                      share (fstF xy) $ \a ->
                      share (sndF xy) $ \bs ->
                      foldBagF (\b -> a * getFixedF b) bs )

dotBags :: IncrementalizedFunc (Bag (Sum Int), Bag (Sum Int)) (Sum Int)
dotBags = $$( compileCode $ runMonoWith (Proxy :: Proxy IFqTU) $ \x ->
                share (fstF x) $ \a ->
                share (sndF x) $ \b ->
                flip foldBagF a $ \e ->
                flip foldBagF b $ \e' ->
                getFixedF e * getFixedF e' )



simpleFoldBagOk :: Spec
simpleFoldBagOk = do
  it "simpleFoldBag is incrementalized" $ do
    propIncrementalizedFunc simpleFoldBag
  it "simpleFoldBag sums Bag elements" $ do
    property $ \b ->
     fst (simpleFoldBag b) === foldBag getFixed b

simpleFoldBag2Ok :: Spec
simpleFoldBag2Ok = modifyMaxSize (min 25) $ do
  it "simpleFoldBag2 is incrementalized" $ do
    propIncrementalizedFunc simpleFoldBag2
  it "simpleFoldBag2 correct" $ do
    property $ \(x,b) ->
     fst (simpleFoldBag2 (x,b)) === foldBag (( x * ) Prelude.. getFixed ) b

dotBagsOk :: Spec
dotBagsOk = modifyMaxSize (min 10) $ do
  it "dotBags is incrementalized" $ do
    propIncrementalizedFunc dotBags
  it "dotBags sums bags"  $ do
    property $ \(b1, b2) ->
      fst (dotBags (b1,b2)) === (flip foldBag b1 $ \e -> flip foldBag b2 $ \e' -> getFixed e * getFixed e')

testBag :: Spec
testBag = describe "Bag related properties" $ do
  propBagOk
  simpleFoldBagOk
  simpleFoldBag2Ok
  dotBagsOk
