{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Code (
  Code, CodeC(..), toCode,

  -- * Query
  isSimple,

  -- * Sharing
  mkLet, shareNonGen, mkLetEnv, mkLetEnvD,

  -- * Newtype/Datatype Wrappers
  PackedCode(..), PackedCodeDiff(..), PackedCodeDelta(..)

  ) where

import           Data.Delta         (Delta, Diff)
import           Data.Function      ((&))

import           Data.Env

import           Data.Code.CodeType

toCode :: CodeC (Code a) -> Code a
toCode (CodeC m) = m id

mkLet :: Code a -> CodeC (Code a)
mkLet e = do
  b <- isSimple e
  if b
    then
    -- suppress inserting "let" if an expression is enough simple
    return e
    else
    CodeC $ \k ->
    -- Used _v to avoid "unused ..." errors.
    [|| let !_v = $$( e ) in $$(k [|| _v ||]) ||]

-- | A 'mkLet' variant that does not generalize types.
shareNonGen :: Code a -> CodeC (Code a)
shareNonGen e = CodeC $ \k ->
  [|| $$e & (\ !_v -> $$(k [|| _v ||]))||]

-- | Newtype Wrapper for 'Code'
newtype PackedCode a = PackedCode { unPackCode :: Code a }

data PackedCodeDelta a where
  PackedCodeDelta :: Diff a => Code (Delta a) -> PackedCodeDelta a

data PackedCodeDiff a where
  PackedCodeDiff :: Diff a => Code a -> PackedCodeDiff a

mkLetEnv :: Env PackedCode aa -> CodeC (Env PackedCode aa)
mkLetEnv = traverseEnv (\(PackedCode c) -> PackedCode <$> mkLet c)

mkLetEnvD :: Env PackedCodeDelta aa -> CodeC (Env PackedCodeDelta aa)
mkLetEnvD = traverseEnv (\(PackedCodeDelta c) -> PackedCodeDelta <$> mkLet c)
