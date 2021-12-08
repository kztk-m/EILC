{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-orphans #-}


module Data.Incrementalized.BoolSpec
  (
    testBool
  ) where

import           Data.Delta

import           Data.IFq
import           Data.IFqTU

import           Language.Unembedding

import           Data.Incrementalized
import           Data.Incrementalized.Numeric     ()
import           Data.Proxy

import           Data.Incrementalized.Bool

import           Data.DeltaSpec                   ()
import           Data.Incrementalized.NumericSpec ()
import           Data.IncrementalizedSpec

import           Test.Hspec
import           Test.QuickCheck

ifElseDouble :: IncrementalizedFunc (Bool, Int) Int
ifElseDouble = $$( compileCode $ runMonoWith (Proxy :: Proxy IFqTU) $ \bn ->
                     share (sndF bn) $ \n -> if_ (fstF bn) n (2 * n) )

instance Arbitrary (Delta Bool) where
  arbitrary = elements [DBKeep, DBNot]
  shrink DBNot = [DBKeep]
  shrink _     = []


-- func = $$( compileCode $ runMonoWith (Proxy :: Proxy IFqTU) $ \ab ->
--              share (sndF ab) $ \b -> if_ (fstF ab) b (2 * b) )

propFuncIfDouble :: Spec
propFuncIfDouble = do
  it "ifElseDouble is incrementalized" $ do
    propIncrementalizedFunc ifElseDouble
  it "ifElseDouble works as expected" $ do
    property $ \(b, n) ->
      fst (ifElseDouble (b,n)) === if b then n else 2 * n


testBool :: Spec
testBool = describe "Unembedded code that involves 'if_'" $ do
  propFuncIfDouble


