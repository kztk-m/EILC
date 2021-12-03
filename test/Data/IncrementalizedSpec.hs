{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TemplateHaskell  #-}
module Data.IncrementalizedSpec where

import           Data.Delta
import           Data.Interaction

import           Test.QuickCheck

type IncrementalizedFunc a b = a -> (b, Interaction (Delta a) (Delta b))

propIncrementalizedFunc ::
  (Diff a, Arbitrary a, Arbitrary (Delta a), Show a, Show (Delta a), Diff b, Eq b, Show b)
  => IncrementalizedFunc a b -> Property
propIncrementalizedFunc f  =
  property $ \a ->
  let (b, i) = f a
  in property $ \das -> fst (f $ foldl (/+) a das) === foldl (/+) b (iterations i das)


