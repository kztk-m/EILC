{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TemplateHaskell  #-}
module Data.IncrementalizedSpec where

import           Data.Delta
import           Data.Interaction

import           Test.QuickCheck

type IncrementalizedFunc a b = a -> (b, Interaction (Delta a) (Delta b))

propIncrementalizedFunc ::
  (Diff a, Arbitrary a, Arbitrary (Delta a), Show a, Show (Delta a), Show (Delta b), Diff b, Eq b, Show b)
  => IncrementalizedFunc a b -> Property
propIncrementalizedFunc f  =
  property $ \a ->
  let (b, i) = f a
  in property $ \das ->
    let a' = foldl (/+) a das
        dbs = iterations i das
    in label ("length of a change sequence: " ++ show (length das)) $
       whenFail (do putStrLn $ "Failure happended when input is updated to: " ++ show a'
                    putStrLn $ "Translated updates:" ++ show dbs) $
       fst (f a') === foldl (/+) b dbs


