{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Incrementalized.Group
   (
     FromMonoid(..), Delta(..)
   ) where

import           Data.Coerce (Coercible, coerce)
import           Data.Delta
import           Data.Group

-- A newtype wrapper
newtype FromMonoid a = FromMonoid { getMonoid :: a }
  deriving newtype (Semigroup, Monoid, Group, Eq, Ord, Enum, Num)
  deriving stock (Show, Functor, Foldable, Traversable)

instance Applicative FromMonoid where
  pure = coerce
  (<*>) = (coerce :: ((a -> b) -> a -> b) -> (FromMonoid (a -> b) -> FromMonoid a -> FromMonoid b)) ($)

newtype instance Delta (FromMonoid a) = DeltaFromMonoid { getDeltaFromMonoid :: a }
  deriving newtype (Semigroup, Monoid, Group, Eq, Ord, Enum, Num)
  deriving stock Show

coerceVia :: Coercible a b => (a -> b) -> a -> b
coerceVia _ = coerce
{-# INLINE coerceVia #-}

instance (Eq a, Monoid a) => Diff (FromMonoid a) where
  -- | (/+) is defined by (<>). Then, it is rather obvious for
  --   the following properties to hold.
  --
  --      - @a /+ da1 /+ da2 = a /+ (da1 <> da2)@
  --      - @a /+ mempty = a@
  a /+ b = coerceVia FromMonoid (coerce a <> coerce b)

  -- | Hoping that equivalence check with mempty is rather light-weight.
  checkEmpty a = mempty == coerceVia getDeltaFromMonoid a

instance (Eq a, Group a) => DiffMinus (FromMonoid a) where
  -- |
  -- @a /- b@ is implemented as @invert b <> a@.
  --
  -- @
  -- FromMonoid b /+ (FromMonoid a /- FromMonoid b)
  -- = { by definition }
  --   b <> invert b <> a
  -- = { associativity }
  --   (b <> invert b) <> a
  -- = { inverse element }
  --   mempty <> a
  -- = { monoid law }
  --   a
  -- @
  a /- b = coerceVia DeltaFromMonoid (invert (coerce b) <> coerce a)


