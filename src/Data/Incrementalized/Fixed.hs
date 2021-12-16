{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
module Data.Incrementalized.Fixed
  ( Fixed(..), Delta(..),

    fstFixedC, sndFixedC, pairFixedC, getFixedC,

    fstFixedF, sndFixedF, pairFixedF, getFixedF,

  ) where

import           Data.Group
import           Language.Haskell.TH.Syntax (Lift)

import           Data.String

import           Data.Delta
import           Data.IFq
import           Data.Incrementalized
import           Data.Typeable
import           Language.Unembedding

-- | @Fixed a@ is a variant of @a@ to which changes are always the empty change.
newtype Fixed a = Fixed { getFixed :: a }
  deriving newtype (Num, Ord, Eq, Enum, Bounded, IsString, Semigroup, Monoid, Group, Abelian)
  deriving stock   (Show, Read, Functor, Foldable, Traversable, Lift)

-- | @NoUpdate@ is only the change allowed for @Fixed a@.
--
--   prop> a /+ NoUpdate == a
--   prop> checkEmpty NoUpdate == True
data instance Delta (Fixed a) = NoUpdate
  deriving stock Show

instance Semigroup (Delta (Fixed a)) where
  _ <> _ = NoUpdate

instance Monoid (Delta (Fixed a)) where
  mempty = NoUpdate


instance Diff (Fixed a) where
  a /+ _ = a
  checkEmpty _ = True

fstFixedC :: IFqS (Fixed (a, b)) (Fixed a)
fstFixedC = fromStatelessCode (\a -> [|| Fixed $ fst (getFixed $$a) ||]) (const [|| mempty ||])

sndFixedC :: IFqS (Fixed (a, b)) (Fixed b)
sndFixedC = fromStatelessCode (\a -> [|| Fixed $ snd (getFixed $$a) ||]) (const [|| mempty ||])

pairFixedC :: IFqS (Fixed a, Fixed b) (Fixed (a, b))
pairFixedC = fromStatelessCode (\x -> [|| let (Fixed a, Fixed b) = $$x in Fixed (a, b) ||]) (const [|| mempty ||])

getFixedC :: Diff a => IFqS (Fixed a) a
getFixedC = fromStatelessCode (\x -> [|| getFixed $$x ||]) (const [|| mempty ||])

fstFixedF :: (App IFqS e, Typeable a, Typeable b) => e (Fixed (a, b)) -> e (Fixed a)
fstFixedF = lift fstFixedC

sndFixedF :: (App IFqS e, Typeable a, Typeable b) => e (Fixed (a, b)) -> e (Fixed b)
sndFixedF = lift sndFixedC

pairFixedF :: (Typeable a, Typeable b, App IFqS e) => e (Fixed a) -> e (Fixed b) -> e (Fixed (a, b))
pairFixedF x y = lift pairFixedC (pair x y)

getFixedF :: (Typeable a, Diff a, App IFqS e) => e (Fixed a) -> e a
getFixedF = lift getFixedC

