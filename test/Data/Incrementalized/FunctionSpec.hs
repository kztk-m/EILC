{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Incrementalized.FunctionSpec
  (
    testFunctions
  )
where

import           Data.Delta

import           Data.IFqT
import           Data.IFqTU
import           Data.Incrementalized
import           Data.Incrementalized.Function         ()
import           Data.Interaction
import           Language.Unembedding

import           Data.DeltaSpec                        ()
import           Data.IncrementalizedSpec

import           Data.Typeable
import           Test.Hspec
import           Test.QuickCheck

import           Data.Incrementalized.FunctionSpecCore



incTwiceTwiceIncT :: Int -> (Int, Interaction (Delta Int) (Delta Int))
incTwiceTwiceIncT = $$( compileCode $ runMonoWith (Proxy :: Proxy IFqT)  twiceTwiceInc )

incTwiceTwiceIncU :: Int -> (Int, Interaction (Delta Int) (Delta Int))
incTwiceTwiceIncU = $$( compileCode $ runMonoWith (Proxy :: Proxy IFqTU) twiceTwiceInc )

propT :: Spec
propT =
  it "incrementalizes 'twice twice inc' when using IFqT" $
    propIncrementalizedFunc incTwiceTwiceIncT

propU :: Spec
propU =
  it "incrementalizes 'twice twice inc' when using IFqTU" $
    propIncrementalizedFunc incTwiceTwiceIncU

propTOk :: Spec
propTOk = do
  it "implements 'twice twice inc' (via IFqT)" $ do
    property $ \a ->
      let (b, _) = incTwiceTwiceIncT a
          twice f x = f (f x)
      in b === twice twice succ a

propCoincide :: Spec
propCoincide = do
  it "yields the same functions" $
    property $ \a das ->
    let (b1, i1) = incTwiceTwiceIncT a
        (b2, i2) = incTwiceTwiceIncU a
    in b1 === b2 .&&.
       iterations i1 das === iterations i2 das

testFunctions :: Spec
testFunctions = do
  describe "Umembedded code for 'twice twice inc'" $ do
    propT
    propU
    propTOk
    propCoincide



