{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE DerivingStrategies #-}

module Data.JoinList
  (
    JoinList(..), JoinListNE(..)
  )
  where

data JoinListNE a = JLSingle a | JLJoin !(JoinListNE a) !(JoinListNE a)
  deriving stock (Functor, Foldable, Traversable)
data JoinList a = JLNil | JLNonEmpty !(JoinListNE a)
  deriving stock (Functor, Foldable, Traversable)

instance Semigroup (JoinListNE a) where
  (<>) = JLJoin

instance Semigroup (JoinList a) where
  JLNil <> xs                    = xs
  JLNonEmpty xs <> JLNil         = JLNonEmpty xs
  JLNonEmpty xs <> JLNonEmpty ys = JLNonEmpty (xs <> ys)

instance Monoid (JoinList a) where
  mempty = JLNil

concatMapNE :: (a -> JoinListNE b) -> JoinListNE a -> JoinListNE b
concatMapNE f (JLSingle a)   = f a
concatMapNE f (JLJoin xs ys) = concatMapNE f xs <> concatMapNE f ys

instance Applicative JoinListNE where
  pure = JLSingle
  fs <*> xs = flip concatMapNE fs $ \f -> fmap f xs

instance Applicative JoinList where
  pure = JLNonEmpty . pure
  JLNil <*> _                     = JLNil
  _ <*> JLNil                     = JLNil
  JLNonEmpty fs <*> JLNonEmpty xs = JLNonEmpty (fs <*> xs)


