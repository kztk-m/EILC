{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Main (main) where

import           Data.DeltaSpec
import           Data.Incrementalized.FunctionSpec
import           Data.Incrementalized.GroupSpec
import           Test.Hspec


main :: IO ()
main = hspec $ do
  testDelta
  testGroup
  testFunctions
