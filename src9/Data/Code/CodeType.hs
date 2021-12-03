{-# LANGUAGE RankNTypes #-}

module Data.Code.CodeType
  (
    Code, CodeC(..), isSimple,
  )
where

import qualified Language.Haskell.TH as TH

type Code a = TH.Code TH.Q a

newtype CodeC a = CodeC { runCodeC :: forall r. (a -> Code r) -> Code r }

instance Functor CodeC where
  fmap f (CodeC m) = CodeC $ \k -> m (k . f)

instance Applicative CodeC where
  pure a = CodeC $ \k -> k a
  CodeC f <*> CodeC a = CodeC $ \k -> a $ \a' -> f $ \f' -> k (f' a')

instance Monad CodeC where
  return = pure
  m >>= f = CodeC $ \k -> runCodeC m $ \a -> runCodeC (f a) k

isSimple :: Code a -> CodeC Bool
isSimple m = CodeC $ \k -> TH.Code $ do
  e <- TH.unTypeCode m
  TH.examineCode $ k (isSimpleExp e)


isSimpleExp :: TH.Exp -> Bool
isSimpleExp (TH.VarE _)    = True
isSimpleExp (TH.ConE _)    = True
isSimpleExp (TH.ParensE e) = isSimpleExp e
isSimpleExp (TH.LitE _)    = True
isSimpleExp _              = False

