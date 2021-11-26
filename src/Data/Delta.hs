{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Delta where

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
import           Data.Coerce           (Coercible, coerce)
import           Data.Functor.Identity
import           Data.Kind             (Type)
import           Data.Monoid           (Endo (..), Sum (..))
import           Data.Typeable         (Typeable)

{-# ANN module "HLint: ignore Use tuple-section" #-}

-- Stolen from Data.Functor.Utils (hidden package in base)
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _ = coerce
{-# INLINE (#.) #-}

-- We generally assume that Delta a is a monoid
data family Delta (a :: Type) :: Type
class Monoid (Delta a) => Diff a where
  -- | Applying delta.
  -- prop> a /+ da /+ da' = a /+ (da <> da')
  (/+) :: a -> Delta a -> a

  default (/+) :: HasAtomicDelta a => a -> Delta a -> a
  a /+ da = foldl'Delta applyAtomicDelta a da
  {-# INLINABLE (/+) #-}

  -- | Sound check of emptiness
  -- prop> checkEmpty da == True ==> a /+ da == a
  checkEmpty :: Delta a -> Bool

  default checkEmpty :: HasAtomicDelta a => Delta a -> Bool
  checkEmpty = foldrDelta (\_ _ -> False) True
  {-# INLINABLE checkEmpty #-}

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

data instance Delta ()     = UnitDelta
  deriving Show

data instance Delta (a, b) = PairDelta (Delta a) (Delta b)
deriving instance (Show (Delta a), Show (Delta b)) => Show (Delta (a, b))

instance Semigroup (Delta ()) where
  _ <> _ = UnitDelta
  {-# INLINE (<>) #-}

instance Monoid (Delta ())    where
  mempty = UnitDelta
  {-# INLINE mempty #-}

instance Diff () where
  a /+ _ = a
  {-# INLINE (/+) #-}

  checkEmpty _ = True
  {-# INLINE checkEmpty #-}

instance (Diff a, Diff b) => Diff (a, b) where
  (a, b) /+ PairDelta da db = (a /+ da, b /+ db)
  {-# INLINE (/+) #-}

  checkEmpty (PairDelta da db) = checkEmpty da && checkEmpty db
  {-# INLINE checkEmpty #-}

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

deriving instance (Show (AtomicDelta a), Show (AtomicDelta b)) => Show (AtomicDelta (a, b))

newtype instance Delta (Identity a) = IdentityDelta (Delta a)
instance Semigroup (Delta a) => Semigroup (Delta (Identity a)) where
  IdentityDelta da <> IdentityDelta da' = IdentityDelta (da <> da')

instance Monoid (Delta a) => Monoid (Delta (Identity a)) where
  mempty = IdentityDelta mempty

instance Diff a => Diff (Identity a) where
  (/+) = coerce ((/+) :: a -> Delta a -> a)
  {-# INLINE (/+) #-}

  checkEmpty = coerce (checkEmpty :: Delta a -> Bool)
  {-# INLINE checkEmpty #-}


instance HasAtomicDelta a => HasAtomicDelta (Identity a) where
  newtype instance AtomicDelta (Identity a) = ADIdentity { runADIdentity :: AtomicDelta a }

  injDelta (ADIdentity ad) = IdentityDelta (injDelta ad)
  monoidMap f (IdentityDelta da) = monoidMap (f . ADIdentity) da

deriving instance Show (AtomicDelta a) => Show (AtomicDelta (Identity a))

newtype instance Delta Int = DInt Int
  deriving (Semigroup, Monoid) via (Sum Int)
  deriving Num via Int
  deriving stock Show

instance Diff Int where
  a /+ DInt da = a + da
  {-# INLINE (/+) #-}

  checkEmpty (DInt n) = n == 0
  {-# INLINE checkEmpty #-}

newtype instance Delta Word = DWord Int
  deriving (Semigroup, Monoid) via (Sum Int)
  deriving Num via Int
  deriving stock Show

instance Diff Word where
  a /+ DWord da = a + fromIntegral da
  {-# INLINE (/+) #-}

  checkEmpty (DWord n) = n == 0
  {-# INLINE checkEmpty #-}

newtype instance Delta Double = DDouble Double
  deriving (Semigroup, Monoid) via (Sum Double)
  deriving Num via Double
  deriving stock Show

instance Diff Double where
  a /+ DDouble da = a + da
  {-# INLINE (/+) #-}

  checkEmpty (DDouble n) = n == 0
  {-# INLINE checkEmpty #-}

class (Diff a, Typeable a) => DiffTypeable a
instance (Diff a, Typeable a) => DiffTypeable a

