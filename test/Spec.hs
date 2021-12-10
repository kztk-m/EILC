{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Main (main) where

import           Data.DeltaSpec                    ()
import           Data.Incrementalized.BagSpec
import           Data.Incrementalized.BoolSpec
import           Data.Incrementalized.FunctionSpec
import           Data.Incrementalized.GroupSpec
import           Data.Incrementalized.NumericSpec
import           Data.Incrementalized.SeqSpec
import           Test.Hspec


main :: IO ()
main = hspec $ do
  testGroup
  testFunctions
  testNumeric
  testBool
  testBag
  testSeq
