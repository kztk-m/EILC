{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Incrementalized.FunctionSpecCore where

import           Data.Code
import           Data.Incrementalized
import           Data.Incrementalized.Numeric ()
import           Language.Unembedding

twiceTwiceInc ::
  (K cat Int, K cat (IHom cat Int Int), K cat (IHom cat (IHom cat Int Int) (IHom cat Int Int)),
    FunTerm cat term, App2 cat term e, Num (e Int),
    IncrementalizedQ cat,
    CodeType cat ~ PackedCode) => e Int -> e Int
twiceTwiceInc x0 =
  (lam (\f -> lam $ \x -> f `app` (f `app` x)) `app` lam (\f -> lam $ \x -> f `app` (f `app` x))) `app` lam (+ 1) `app` x0
--  where
--    incC = fromStatelessCode (\x -> [|| (succ :: Int -> Int) $$x ||]) Prelude.id
