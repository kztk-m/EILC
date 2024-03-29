{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Delta (
  Diff(..), Delta(..), HasAtomicDelta(..), AtomicDelta(..),
  DiffMinus(..), DiffReplace(..),

  pairDelta, fstDelta, sndDelta,
  DiffTypeable,

  -- * Utilities to define Diff instances
  applyDeltaFromHasAtomicDelta, checkEmptyFromAtomicDelta,

  -- * Some Useful Functions
  iterTr, iterTrStateless, nilChangeOf,

  -- * Deltas as Collections
  foldrDelta, foldl'Delta
  ) where

-- We want to define a class with
--
--     injMonoid :: a -> m a
--     monoidMap :: Monoid n => (a -> n) -> m a -> n
--     m a is always a monoid
--
-- Then, m must be Applicative as
--
-- f <*> x = monoidMap f $ \f' -> monoidMap x $ \x' -> injMonoid (f' a')

-- We want to define a class with
--
--     injMonoid :: a -> m a
--     monoidMap :: Monoid n => (a -> n) -> m a -> n
--     m a is always a monoid
--
-- Then, m must be Applicative as
--
-- f <*> x = monoidMap f $ \f' -> monoidMap x $ \x' -> injMonoid (f' a')
import           Control.DeepSeq       (NFData (..))
import           Data.Coerce           (Coercible, coerce)
import           Data.Functor.Identity
import           Data.Kind             (Type)
import           Data.Monoid           (Endo (..))
import           Data.Typeable         (Typeable)

-- $setup
-- >>> :set -XGeneralizedNewtypeDeriving -XStandaloneDeriving -XDerivingStrategies -XFlexibleInstances
-- >>> import Test.QuickCheck.Arbitrary
-- >>> deriving newtype instance Arbitrary (Delta Integer)


-- Stolen from Data.Functor.Utils (hidden package in base)
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _ = coerce
{-# INLINE (#.) #-}

-- We generally assume that Delta a is a monoid
data family Delta (a :: Type) :: Type
class Monoid (Delta a) => Diff a where
  -- | Applying delta.
  -- prop> a /+ da /+ da' == a /+ (da <> da')
  (/+) :: a -> Delta a -> a

  -- default (/+) :: HasAtomicDelta a => a -> Delta a -> a
  -- a /+ da = foldl'Delta applyAtomicDelta a da
  -- {-# INLINABLE (/+) #-}

  -- | Sound check of emptiness
  -- That is, if @checkEmpty da@ holds, then @a /+ da@ must be @a@ for any @a@.
  --
  -- (The contraposition is used below for automatic testing.)
  -- prop> a /+ da /= a ==> checkEmpty da == False
  checkEmpty :: Delta a -> Bool

  -- default checkEmpty :: HasAtomicDelta a => Delta a -> Bool
  -- checkEmpty = foldrDelta (\_ _ -> False) True
  -- {-# INLINABLE checkEmpty #-}

applyDeltaFromHasAtomicDelta :: HasAtomicDelta a => a -> Delta a -> a
applyDeltaFromHasAtomicDelta = foldl'Delta applyAtomicDelta

checkEmptyFromAtomicDelta :: HasAtomicDelta a => Delta a -> Bool
checkEmptyFromAtomicDelta = foldrDelta (\_ _ -> False) True

class Diff a => DiffMinus a where
  -- | prop> a /+ (a' /- a) == a'
  (/-) :: a -> a -> Delta a

class Diff a => DiffReplace a where
  -- | prop> a /+ replaceTo b == b
  replaceTo :: a -> Delta a

-- | A type-restricted version of @const mempty@.
nilChangeOf :: Monoid (Delta a) => a -> Delta a
nilChangeOf _ = mempty

-- The following definitions are taken from Data.Foldable
foldrDelta :: HasAtomicDelta a => (AtomicDelta a -> b -> b) -> b -> Delta a -> b
foldrDelta f z t = appEndo (monoidMap (Endo #. f) t) z
{-# INLINE foldrDelta #-}

foldl'Delta :: HasAtomicDelta a => (b -> AtomicDelta a -> b) -> b -> Delta a -> b
foldl'Delta f z0 xs = foldrDelta f' id xs z0
      where f' x k z = k $! f z x
{-# INLINE foldl'Delta #-}

class (Monoid (Delta a), Diff a) => HasAtomicDelta a where
  data family AtomicDelta a :: Type

  monoidMap :: Monoid m => (AtomicDelta a -> m) -> Delta a -> m
  injDelta  :: AtomicDelta a -> Delta a

  applyAtomicDelta :: a -> AtomicDelta a -> a
  applyAtomicDelta a da = a /+ injDelta da

newtype StateWriterLL s w = StateWriterLL { unStateWriterLL :: s -> (w, s) }

instance Semigroup w => Semigroup (StateWriterLL s w) where
  f <> g = coerce @(s -> (w, s)) $ \s ->
    let (m1, s1) = coerce @(StateWriterLL s w) @(s -> (w, s)) f s
        (m2, s2) = coerce g s1
    in (m1 <> m2, s2)
  {-# INLINABLE (<>) #-}

instance Monoid w => Monoid (StateWriterLL s w) where
  mempty = coerce @(s -> (w, s)) $ \s -> (mempty , s)
  {-# INLINABLE mempty #-}

iterTrStateless :: (HasAtomicDelta a, Monoid (Delta b)) => (AtomicDelta a -> Delta b) -> (Delta a -> Delta b)
iterTrStateless = monoidMap
{-# INLINE iterTrStateless #-}

iterTr :: (HasAtomicDelta a, Monoid (Delta b)) => (AtomicDelta a -> c -> (Delta b, c)) -> (Delta a -> c -> (Delta b, c))
iterTr f = unStateWriterLL . monoidMap (StateWriterLL . f)
{-# INLINABLE iterTr #-}

newtype instance Delta ()     = DeltaUnit ()
  deriving stock (Show, Eq)
  deriving newtype NFData 

data instance Delta (a, b) = PairDelta (Delta a) (Delta b)
deriving stock instance (Show (Delta a), Show (Delta b)) => Show (Delta (a, b))


instance (NFData (Delta a), NFData (Delta b)) => NFData (Delta (a, b)) where
  rnf (PairDelta da db) = rnf (da, db)

instance Semigroup (Delta ()) where
  _ <> _ = coerce ()
  {-# INLINE (<>) #-}

instance Monoid (Delta ())    where
  mempty = coerce ()
  {-# INLINE mempty #-}

instance Diff () where
  a /+ _ = a
  {-# INLINE (/+) #-}

  checkEmpty _ = True
  {-# INLINE checkEmpty #-}

instance DiffMinus () where
  _ /- _ = coerce ()

instance DiffReplace () where
  replaceTo _ = coerce ()

instance (Diff a, Diff b) => Diff (a, b) where
  (a, b) /+ PairDelta da db = (a /+ da, b /+ db)
  {-# INLINE (/+) #-}

  checkEmpty (PairDelta da db) = checkEmpty da && checkEmpty db
  {-# INLINE checkEmpty #-}

instance (DiffMinus a, DiffMinus b) => DiffMinus (a, b) where
  (a', b') /- (a, b) = PairDelta (a' /- a) (b' /- b)

instance (DiffReplace a, DiffReplace b) => DiffReplace (a, b) where
  replaceTo (a, b) = PairDelta (replaceTo a) (replaceTo b)

instance (Semigroup (Delta a), Semigroup (Delta b)) => Semigroup (Delta (a, b)) where
  PairDelta da1 db1 <> PairDelta da2 db2 = PairDelta (da1 <> da2) (db1 <> db2)
  {-# INLINE (<>) #-}

instance (Monoid (Delta a), Monoid (Delta b)) => Monoid (Delta (a, b)) where
  mempty = PairDelta mempty mempty
  {-# INLINE mempty #-}

-- For compatibility
pairDelta :: Delta a -> Delta b -> Delta (a, b)
pairDelta = PairDelta
{-# INLINE pairDelta #-}

fstDelta :: Delta (a, b) -> Delta a
fstDelta (PairDelta da _) = da
{-# INLINE fstDelta #-}

sndDelta :: Delta (a, b) -> Delta b
sndDelta (PairDelta _ db) = db
{-# INLINE sndDelta #-}

instance (HasAtomicDelta a, HasAtomicDelta b) => HasAtomicDelta (a, b) where
  data AtomicDelta (a, b) = ADFst (AtomicDelta a) | ADSnd (AtomicDelta b)

  injDelta (ADFst ad) = PairDelta (injDelta ad) mempty
  injDelta (ADSnd ad) = PairDelta mempty (injDelta ad)

  monoidMap f (PairDelta da db) = monoidMap (f . ADFst) da <> monoidMap (f . ADSnd) db

deriving stock instance (Show (AtomicDelta a), Show (AtomicDelta b)) => Show (AtomicDelta (a, b))

newtype instance Delta (Identity a) = IdentityDelta (Delta a)
deriving newtype instance Semigroup (Delta a) => Semigroup (Delta (Identity a))
deriving newtype instance Monoid    (Delta a) => Monoid (Delta (Identity a))

deriving newtype instance Diff a => Diff (Identity a)
deriving newtype instance DiffMinus a => DiffMinus (Identity a)

instance HasAtomicDelta a => HasAtomicDelta (Identity a) where
  newtype instance AtomicDelta (Identity a) = ADIdentity { runADIdentity :: AtomicDelta a }

  injDelta (ADIdentity ad) = IdentityDelta (injDelta ad)
  monoidMap f (IdentityDelta da) = monoidMap (f . ADIdentity) da

deriving via AtomicDelta a instance Show (AtomicDelta a) => Show (AtomicDelta (Identity a))



-- | @'DiffTypeable' a@ equivalent to @(Diff a, Typeable a)@.
class (Diff a, Typeable a) => DiffTypeable a
instance (Diff a, Typeable a) => DiffTypeable a

