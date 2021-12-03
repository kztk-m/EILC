{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Incrementalized.Group
   (
     FromMonoid(..), Delta(..),
     GroupChangeWithReplace(..),

     DiffGroupReplace(..)
   ) where

import           Data.Coerce (Coercible, coerce)
import           Data.Delta
import           Data.Group


-- | @'GroupChangeWithReplace' a@ is a Delta type made from a group a.
--   Notice that this itself does not form a group, as there is no inverse element for 'Replace a'.
data GroupChangeWithReplace a = GroupChange !a | Replace !a
  deriving stock (Show, Eq)

instance Semigroup a => Semigroup (GroupChangeWithReplace a) where
  Replace a <> GroupChange b     = Replace (a <> b)
  GroupChange a <> GroupChange b = GroupChange (a <> b)
  _ <> Replace a                 = Replace a

instance Monoid a => Monoid (GroupChangeWithReplace a) where
  mempty = GroupChange mempty

-- A newtype wrapper
newtype FromMonoid a = FromMonoid { getMonoid :: a }
  deriving newtype (Semigroup, Monoid, Group, Eq, Ord, Enum, Num)
  deriving stock (Show, Functor, Foldable, Traversable)

instance Applicative FromMonoid where
  pure = coerce
  (<*>) = (coerce :: ((a -> b) -> a -> b) -> (FromMonoid (a -> b) -> FromMonoid a -> FromMonoid b)) ($)

newtype instance Delta (FromMonoid a) = DeltaFromMonoid { getGroupChangeWithReplace :: GroupChangeWithReplace a }
  deriving newtype (Semigroup, Monoid, Eq)
  deriving stock Show

instance (Eq a, Monoid a) => Diff (FromMonoid a) where
  a /+ (DeltaFromMonoid (GroupChange b)) = coerceVia FromMonoid (coerce a <> b)
  _ /+ (DeltaFromMonoid (Replace b))     = coerceVia FromMonoid b

  checkEmpty (DeltaFromMonoid (GroupChange a)) = mempty == a
  checkEmpty (DeltaFromMonoid (Replace _))     = False

instance (Eq a, Group a) => DiffMinus (FromMonoid a) where
  FromMonoid a /- FromMonoid b = coerceVia DeltaFromMonoid $ GroupChange $ invert b <> a

instance (Eq a, Monoid a) => DiffReplace (FromMonoid a) where
  replaceTo = coerceVia DeltaFromMonoid . Replace . coerceVia getMonoid

coerceVia :: Coercible a b => (a -> b) -> a -> b
coerceVia _ = coerce
{-# INLINE coerceVia #-}

class (Coercible (Delta a) (GroupChangeWithReplace a),
       Coercible (GroupChangeWithReplace a) (Delta a),
       DiffReplace a) => DiffGroupReplace a where
  toGroupDelta :: a -> Delta a
  toGroupDelta a = coerce (GroupChange a)

instance (Monoid a, Eq a) => DiffGroupReplace (FromMonoid a)
