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

  -- -- Especially for functions, empty update is not unique and cannot be obtained of the air.
  -- emptify :: Delta a -> Delta a
  -- default emptify :: Monoid (Delta a) => Delta a -> Delta a
  -- emptify = const mempty

  -- emptyOf :: a -> Delta a
  -- default emptyOf :: Monoid (Delta a) => a -> Delta a
  -- emptyOf = const mempty

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

instance (Diff a, Diff b) => Diff (a, b) where
  (a, b) /+ PairDelta da db = (a /+ da, b /+ db)
  {-# INLINE (/+) #-}

  checkEmpty (PairDelta da db) = checkEmpty da && checkEmpty db

  -- emptify (PairDelta da db) = PairDelta (emptify da) (emptify db)
  -- emptyOf (a, b) = PairDelta (emptyOf a) (emptyOf b)

instance (Semigroup (Delta a), Semigroup (Delta b)) => Semigroup (Delta (a, b)) where
  PairDelta da1 db1 <> PairDelta da2 db2 = PairDelta (da1 <> da2) (db1 <> db2)
  {-# INLINE (<>) #-}

instance (Monoid (Delta a), Monoid (Delta b)) => Monoid (Delta (a, b)) where
  mempty = PairDelta mempty mempty

-- For compatibility
pairDelta :: Delta a -> Delta b -> Delta (a, b)
pairDelta = PairDelta

fstDelta :: Delta (a, b) -> Delta a
fstDelta (PairDelta da _) = da

sndDelta :: Delta (a, b) -> Delta b
sndDelta (PairDelta _ db) = db

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
  Identity a /+ (IdentityDelta da) = Identity (a /+ da)

  checkEmpty (IdentityDelta da) = checkEmpty da

  -- emptify = coerce (emptify :: Delta a -> Delta a)
  -- emptyOf = coerce (emptyOf :: a -> Delta a)

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

-- class (Applicative m, Alternative m, Foldable m) => MonoidF m

-- injMonoid :: MonoidF m => a -> m a
-- injMonoid = pure -- compatibility

-- monoidMap :: (MonoidF m, Monoid n) => (a -> n) -> m a -> n
-- monoidMap = foldMap

-- monoidFromList :: MonoidF m => [a] -> m a
-- monoidFromList = foldr ((<|>) . injMonoid) empty

-- -- Expecting foldr/build
-- {-# INLINE monoidFromList #-}


-- -- mmap :: (MonoidF a m, MonoidF b n) => (a -> b) -> m -> n
-- -- mmap f = monoidMap (injMonoid . f)

-- instance MonoidF []

-- newtype FreeMonoidF a =
--     FreeMonoidF { foldFreeMonoidF :: forall n. Monoid n => (a -> n) -> n }

-- instance Show a => Show (FreeMonoidF a) where
--   showsPrec k xs = showParen (k > 9) s
--     where
--       s = Text.Show.showString "monoidFromList" . showChar ' ' . shows (foldFreeMonoidF xs $ \x -> [x])


-- instance Functor FreeMonoidF where
--   fmap f xs = FreeMonoidF $ \h -> foldFreeMonoidF xs (h . f)
--   {-# INLINE fmap #-}

-- instance Semigroup (FreeMonoidF a) where
--   xs <> ys = FreeMonoidF $ \h -> foldFreeMonoidF xs h <> foldFreeMonoidF ys h
--   {-# INLINE (<>) #-}

-- instance Monoid (FreeMonoidF a) where
--   mempty = FreeMonoidF $ const mempty
--   {-# INLINE mempty #-}

-- instance Applicative FreeMonoidF where
--   pure a = FreeMonoidF $ \h -> h a
--   {-# INLINE pure #-}
--   f <*> x = foldFreeMonoidF f $ \f' -> foldFreeMonoidF x $ \x' -> pure (f' x')
--   {-# INLINE (<*>) #-}

-- instance Alternative FreeMonoidF where
--   empty = mempty
--   {-# INLINE empty #-}

--   (<|>) = (<>)
--   {-# INLINE (<|>) #-}

-- instance Foldable FreeMonoidF where
--   foldMap h as = foldFreeMonoidF as h
--   {-# INLINE foldMap #-}

-- instance MonoidF FreeMonoidF

-- -- Non-injectivity is usually a source of a trouble.
-- data family AtomicDelta (a :: Type) :: Type

-- newtype instance AtomicDelta (Identity a) = ADIdentity { runADIdentity :: AtomicDelta a }
-- data instance AtomicDelta ()
-- data instance AtomicDelta (a, b) = ADFst (AtomicDelta a) | ADSnd (AtomicDelta b)

-- deriving instance (Show (AtomicDelta a), Show (AtomicDelta b)) => Show (AtomicDelta (a, b))

-- fstDelta :: Delta (a, b) -> Delta a
-- fstDelta = foldMap fstDeltaA

-- fstDeltaA :: AtomicDelta (a, b) -> Delta a
-- fstDeltaA (ADFst da) = injMonoid da
-- fstDeltaA _          = mempty

-- sndDelta :: Delta (a, b) -> Delta b
-- sndDelta = foldMap sndDeltaA

-- sndDeltaA :: AtomicDelta (a, b) -> Delta b
-- sndDeltaA (ADSnd db) = injMonoid db
-- sndDeltaA _          = mempty

-- pairDelta :: Delta a -> Delta b -> Delta (a, b)
-- pairDelta xs ys = fmap ADFst xs <> fmap ADSnd ys

-- class Diff a where
--   applyAtomicDelta :: a -> AtomicDelta a -> a

--   -- | Applying delta.
--   -- prop> a /+ da /+ da' = a /+ (da <> da')
--   (/+) :: a -> Delta a -> a
--   a /+ das =
--     -- appEndo (getDual (monoidMap (\da -> Dual $ Endo $ \a -> applyAtomicDelta a da) das)) a
--     foldl applyAtomicDelta a das

-- instance Diff () where
--   applyAtomicDelta () _ = ()

-- instance (Diff a, Diff b) => Diff (a, b) where
--   -- (a, b) /+ (da, db) = (a /+ da, b /+ db)
--   applyAtomicDelta (a, b) (ADFst da) = (applyAtomicDelta a da, b)
--   applyAtomicDelta (a, b) (ADSnd db) = (a, applyAtomicDelta b db)

-- type Delta a = FreeMonoidF (AtomicDelta a)


-- -- State-Writer, both are composed left-to-right
-- newtype StateWriterLL s w = StateWriterLL { unStateWriterLL :: s -> (w, s) }

-- instance Semigroup w => Semigroup (StateWriterLL s w) where
--   f <> g = StateWriterLL $ \s ->
--     let (m1, s1) = unStateWriterLL f s
--         (m2, s2) = unStateWriterLL g s1
--     in (m1 <> m2, s2)
--   {-# INLINABLE (<>) #-}

-- instance Monoid w => Monoid (StateWriterLL s w) where
--   mempty = StateWriterLL $ \s -> (mempty , s)

-- iterTrStateless :: (AtomicDelta a -> Delta b) -> (Delta a -> Delta b)
-- iterTrStateless = foldMap

-- iterTr :: (AtomicDelta a -> c -> (Delta b, c)) -> (Delta a -> c -> (Delta b, c))
-- iterTr f = unStateWriterLL . monoidMap (StateWriterLL . f)
