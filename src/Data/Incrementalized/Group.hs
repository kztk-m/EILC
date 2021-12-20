{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Incrementalized.Group
   (
     GroupChange(..), GroupChangeWithReplace(..),
     applyGroupChange, applyGroupChangeReplace,

     Delta(..),
     WithGroupChange(..),
     WithGroupChangeReplace(..),

     DiffGroupChange(..), DiffGroupChangeReplace(..)
   ) where

import           Control.DeepSeq (NFData (rnf))
import           Data.Coerce     (coerce)
import           Data.Delta
import           Data.Group

newtype GroupChange a = GroupChange { getGroupChange :: a }
  deriving stock   (Show)
  deriving newtype (Semigroup, Monoid, Group, Eq, Ord, Enum, Num)
  deriving newtype NFData

applyGroupChange :: Semigroup a => a -> GroupChange a -> a
applyGroupChange a (GroupChange a') = a <> a'

-- | @'GroupChangeWithReplace' a@ is a Delta type made from a group a.
--   Notice that this itself does not form a group, as there is no inverse element for 'Replace a'.
data GroupChangeWithReplace a = InjGroupChange !(GroupChange a) | Replace !a
  deriving stock (Show, Eq, Ord)

instance NFData a => NFData (GroupChangeWithReplace a) where
  rnf (InjGroupChange c) = rnf c
  rnf (Replace a)        = rnf a

instance Semigroup a => Semigroup (GroupChangeWithReplace a) where
  Replace a <> InjGroupChange b        = Replace (a <> getGroupChange b)
  InjGroupChange a <> InjGroupChange b = InjGroupChange (a <> b)
  _ <> Replace a                       = Replace a

instance Monoid a => Monoid (GroupChangeWithReplace a) where
  mempty = InjGroupChange mempty

applyGroupChangeReplace :: Semigroup a => a -> GroupChangeWithReplace a -> a
applyGroupChangeReplace _ (Replace b)         = b
applyGroupChangeReplace a (InjGroupChange da) = applyGroupChange a da

-- A newtype wrapper
newtype WithGroupChange a = WithGroupChange { detachGroupChange :: a }
  deriving newtype (Semigroup, Monoid, Group, Eq, Ord, Enum, Num, Bounded)
  deriving stock (Show, Functor, Foldable, Traversable)
  deriving newtype NFData

newtype instance Delta (WithGroupChange a) = DWithGroupChange (GroupChange a)
  deriving newtype (Semigroup, Monoid)
  deriving stock Show
  deriving newtype NFData

instance (Monoid a, Eq a) => Diff (WithGroupChange a) where
  WithGroupChange a /+ DWithGroupChange da = WithGroupChange $ applyGroupChange a da
  checkEmpty (DWithGroupChange da) = mempty == da

instance (Group a, Eq a) => DiffMinus (WithGroupChange a) where
  WithGroupChange a /- WithGroupChange b = DWithGroupChange $ GroupChange $ invert b <> a

newtype WithGroupChangeReplace a = WithGroupChangeReplace { detachGroupChangeReplace :: a }
  deriving newtype (Semigroup, Monoid, Group, Eq, Ord, Enum, Bounded)
  deriving stock (Show, Functor, Foldable, Traversable)
  deriving newtype NFData

newtype instance Delta (WithGroupChangeReplace a) = DWithGroupChangeReplace (GroupChangeWithReplace a)
  deriving newtype (Semigroup, Monoid)
  deriving stock (Show)
  deriving newtype NFData

instance (Monoid a, Eq a) => Diff (WithGroupChangeReplace a) where
  WithGroupChangeReplace a /+ DWithGroupChangeReplace da = WithGroupChangeReplace $ applyGroupChangeReplace a da
  checkEmpty (DWithGroupChangeReplace (InjGroupChange a)) = mempty == a
  checkEmpty _                                            = False

instance (Group a, Eq a) => DiffMinus (WithGroupChangeReplace a) where
  WithGroupChangeReplace a /- WithGroupChangeReplace b = DWithGroupChangeReplace $ InjGroupChange $ GroupChange $ invert b <> a

instance (Monoid a, Eq a) => DiffReplace (WithGroupChangeReplace a) where
  replaceTo (WithGroupChangeReplace a) = DWithGroupChangeReplace (Replace a)

class Diff t => DiffGroupChange t where
  toGroupChange    :: Delta t -> GroupChange t
  fromGroupChange  :: GroupChange t -> Delta t

instance (Eq t, Monoid t) => DiffGroupChange (WithGroupChange t) where
  toGroupChange = coerce
  fromGroupChange = coerce

class Diff t => DiffGroupChangeReplace t where
  toGroupChangeReplace   :: Delta t -> GroupChangeWithReplace t
  fromGroupChangeReplace :: GroupChangeWithReplace t -> Delta t

instance (Eq t, Monoid t) => DiffGroupChangeReplace (WithGroupChangeReplace t) where
  toGroupChangeReplace = coerce
  fromGroupChangeReplace = coerce

-- instance Applicative FromMonoid where
--   pure = coerce
--   (<*>) = (coerce :: ((a -> b) -> a -> b) -> (FromMonoid (a -> b) -> FromMonoid a -> FromMonoid b)) ($)

-- newtype instance Delta (FromMonoid a) = DeltaFromMonoid { getGroupChangeWithReplace :: GroupChangeWithReplace a }
--   deriving newtype (Semigroup, Monoid, Eq)
--   deriving stock Show

-- instance (Eq a, Monoid a) => Diff (FromMonoid a) where
--   a /+ (DeltaFromMonoid (InjGroupChange b)) = coerceVia FromMonoid (coerce a <> b)
--   _ /+ (DeltaFromMonoid (Replace b))        = coerceVia FromMonoid b

--   checkEmpty (DeltaFromMonoid (GroupChange a)) = mempty == a
--   checkEmpty (DeltaFromMonoid (Replace _))     = False

-- instance (Eq a, Group a) => DiffMinus (FromMonoid a) where
--   FromMonoid a /- FromMonoid b = coerceVia DeltaFromMonoid $ GroupChange $ invert b <> a

-- instance (Eq a, Monoid a) => DiffReplace (FromMonoid a) where
--   replaceTo = coerceVia DeltaFromMonoid . Replace . coerceVia getMonoid

-- coerceVia :: Coercible a b => (a -> b) -> a -> b
-- coerceVia _ = coerce
-- {-# INLINE coerceVia #-}

-- class (Coercible (Delta a) (GroupChangeWithReplace a),
--        Coercible (GroupChangeWithReplace a) (Delta a),
--        DiffReplace a) => DiffGroupReplace a where
--   toGroupDelta :: a -> Delta a
--   toGroupDelta a = coerce (GroupChange a)

-- instance (Monoid a, Eq a) => DiffGroupReplace (FromMonoid a)
