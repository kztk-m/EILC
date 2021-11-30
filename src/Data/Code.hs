{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE CPP             #-}
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

import           Data.Delta          (Delta, Diff)
import           Data.Function       ((&))
import qualified Language.Haskell.TH as TH

import           Data.Env

isSimple :: Code a -> CodeC Bool

#if MIN_VERSION_GLASGOW_HASKELL(9,0,1,0)
isSimple m = CodeC $ \k -> TH.Code $ do
  e <- TH.unTypeCode m
  TH.examineCode $ k (isSimpleExp e)

type Code a = TH.Code TH.Q a
#else
isSimple m = CodeC $ \k -> do
  e <- TH.unType <$> m
  k (isSimpleExp e)

type Code a = TH.Q (TH.TExp a)
#endif


newtype CodeC a = CodeC { runCodeC :: forall r. (a -> Code r) -> Code r }


isSimpleExp :: TH.Exp -> Bool
isSimpleExp (TH.VarE _)    = True
isSimpleExp (TH.ConE _)    = True
isSimpleExp (TH.ParensE e) = isSimpleExp e
isSimpleExp (TH.LitE _)    = True
isSimpleExp _              = False

toCode :: CodeC (Code a) -> Code a
toCode (CodeC m) = m id

instance Functor CodeC where
  fmap f (CodeC m) = CodeC $ \k -> m (k . f)

instance Applicative CodeC where
  pure a = CodeC $ \k -> k a
  CodeC f <*> CodeC a = CodeC $ \k -> a $ \a' -> f $ \f' -> k (f' a')

instance Monad CodeC where
  return = pure
  m >>= f = CodeC $ \k -> runCodeC m $ \a -> runCodeC (f a) k

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
