{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell   #-}
module Data.Incrementalized.SeqSpec where

import           Data.Delta
import           Data.IFq
import           Data.IFqTU                       (IFqTU)
import           Data.Incrementalized
import           Data.Incrementalized.Numeric     ()
import           Data.Incrementalized.Seq
import qualified Data.JoinList                    as JoinList
import           Language.Unembedding

import           Data.Foldable                    (toList)
import           Data.Proxy                       (Proxy (Proxy))
import qualified Data.Sequence                    as Seq
import           Prelude                          hiding (id, (.))
import           Test.Hspec
import           Test.QuickCheck

import qualified Control.Monad
import           Data.DeltaSpec
import           Data.Incrementalized.NumericSpec ()
import           Data.IncrementalizedSpec
import           Test.Hspec.QuickCheck            (modifyMaxSize)

arbitraryNN :: (Num a, Ord a, Arbitrary a) => Gen a
arbitraryNN = getNonNegative <$> arbitrary

instance Arbitrary a => Arbitrary (Seq a) where
  arbitrary = Seq . Seq.fromList <$> arbitrary
  shrink = map (Seq . Seq.fromList) . shrinkList shrink . toList

instance (Arbitrary a, Arbitrary (Delta a)) => Arbitrary (Delta (Seq a)) where
  arbitrary = DeltaSeq . JoinList.fromList <$> arbitrary
  shrink (DeltaSeq ds) = map (DeltaSeq . JoinList.fromList . reverse) $ shrinkList shrink $ reverse $ toList ds

instance (Arbitrary a, Arbitrary (Delta a)) => Arbitrary (AtomicDelta (Seq a)) where
  arbitrary =
    oneof [ SIns <$> arbitraryNN <*> arbitrary,
            SDel <$> arbitraryNN <*> arbitraryNN,
            SRep <$> arbitraryNN <*> arbitrary,
            SRearr <$> arbitraryNN <*> arbitraryNN <*> arbitraryNN ]
  shrink (SIns i a)  = SIns i <$> shrink a
  shrink (SRep i da) = SRep i <$> shrink da
  shrink _           = []


propSeqOk :: Spec
propSeqOk = do
  let p = Proxy :: Proxy (Seq Int)
  describeProxy p $ do
    checkDiffLaws p
--    checkDiffMinusLaws p

cartesian :: IncrementalizedFunc (Seq Int, Seq Int) (Seq (Int,Int))
cartesian = $$( compileCode $ runMonoWith (Proxy :: Proxy IFqTU) $ \z ->
                  share (fstF z) $ \as ->
                  share (sndF z) $ \bs ->
                  concatF $ mapF (\a -> mapF (pair a) bs) as )

concatInc :: IncrementalizedFunc (Seq (Seq Int)) (Seq Int)
concatInc= $$( compileCode $ runMonoWith (Proxy :: Proxy IFqTU) concatF)


cartesianFOk :: Spec
cartesianFOk = modifyMaxSize (min 10) $ do
  it "cartesianF is incrementalized" $ do
    propIncrementalizedFunc cartesian
  it "cartesianF implements cartesian products" $ do
    property $ \(a,b) ->
     fst (cartesian (a,b)) === ((,) <$> a <*> b)

concatIncOk :: Spec
concatIncOk = modifyMaxSize (min 20) $ do
  it "concatInc is incrementalized" $ do
    propIncrementalizedFunc concatInc
  it "concnatInc concats sequences" $ do
    property $ \xss ->
     fst (concatInc xss) === Control.Monad.join xss



testSeq :: Spec
testSeq = do
  describe "Properties for Sequences" $ do
    propSeqOk
    concatIncOk
    cartesianFOk

