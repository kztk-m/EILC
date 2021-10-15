module Data.Interaction where

newtype Interaction a b = Interaction { runInteraction :: a -> (b, Interaction a b) }

iterations :: Interaction a b -> [a] -> [b]
iterations _ []       = []
iterations i (a : as) =
  let (b, i') = runInteraction i a
  in b : iterations i' as
{-# INLINABLE iterations #-}
