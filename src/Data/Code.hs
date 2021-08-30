{-# LANGUAGE GADTs           #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Code where

import           Data.Delta          (Delta, Diff)
import qualified Language.Haskell.TH as TH

type Code a = TH.Q (TH.TExp a)

newtype CodeC a = CodeC { runCodeC :: forall r. (a -> Code r) -> Code r }

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
mkLet e = CodeC $ \k ->
  [|| let v = $$( e ) in $$(k [|| v ||]) ||]

newtype PackedCode a = PackedCode { getCode :: Code a }

data PackedCodeDelta a where
  PackedCodeDelta :: Diff a => Code (Delta a) -> PackedCodeDelta a

