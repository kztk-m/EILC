{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
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

import           Control.Applicative   (Alternative (empty, (<|>)))
import           Data.Functor.Identity
import           Data.Kind             (Type)
import qualified Text.Show
class (Applicative m, Alternative m, Foldable m) => MonoidF m

injMonoid :: MonoidF m => a -> m a
injMonoid = pure -- compatibility

monoidMap :: (MonoidF m, Monoid n) => (a -> n) -> m a -> n
monoidMap = foldMap

monoidFromList :: MonoidF m => [a] -> m a
monoidFromList = foldr ((<|>) . injMonoid) empty

-- mmap :: (MonoidF a m, MonoidF b n) => (a -> b) -> m -> n
-- mmap f = monoidMap (injMonoid . f)

instance MonoidF []

newtype FreeMonoidF a =
    FreeMonoidF { foldFreeMonoidF :: forall n. Monoid n => (a -> n) -> n }

instance Show a => Show (FreeMonoidF a) where
  showsPrec k xs = showParen (k > 9) s
    where
      s = Text.Show.showString "monoidFromList" . showChar ' ' . shows (foldFreeMonoidF xs $ \x -> [x])


instance Functor FreeMonoidF where
  fmap f xs = FreeMonoidF $ \h -> foldFreeMonoidF xs (h . f)
  {-# INLINE fmap #-}

instance Semigroup (FreeMonoidF a) where
  xs <> ys = FreeMonoidF $ \h -> foldFreeMonoidF xs h <> foldFreeMonoidF ys h
  {-# INLINE (<>) #-}

instance Monoid (FreeMonoidF a) where
  mempty = FreeMonoidF $ const mempty
  {-# INLINE mempty #-}

instance Applicative FreeMonoidF where
  pure a = FreeMonoidF $ \h -> h a
  {-# INLINE pure #-}
  f <*> x = foldFreeMonoidF f $ \f' -> foldFreeMonoidF x $ \x' -> pure (f' x')
  {-# INLINE (<*>) #-}

instance Alternative FreeMonoidF where
  empty = mempty
  {-# INLINE empty #-}

  (<|>) = (<>)
  {-# INLINE (<|>) #-}

instance Foldable FreeMonoidF where
  foldMap h as = foldFreeMonoidF as h
  {-# INLINE foldMap #-}

instance MonoidF FreeMonoidF

-- Non-injectivity is usually a source of a trouble.
data family AtomicDelta (a :: Type) :: Type

newtype instance AtomicDelta (Identity a) = ADIdentity { runADIdentity :: AtomicDelta a }
data instance AtomicDelta ()
data instance AtomicDelta (a, b) = ADFst (AtomicDelta a) | ADSnd (AtomicDelta b)

deriving instance (Show (AtomicDelta a), Show (AtomicDelta b)) => Show (AtomicDelta (a, b))

fstDelta :: Delta (a, b) -> Delta a
fstDelta = foldMap fstDeltaA

fstDeltaA :: AtomicDelta (a, b) -> Delta a
fstDeltaA (ADFst da) = injMonoid da
fstDeltaA _          = mempty

sndDelta :: Delta (a, b) -> Delta b
sndDelta = foldMap sndDeltaA

sndDeltaA :: AtomicDelta (a, b) -> Delta b
sndDeltaA (ADSnd db) = injMonoid db
sndDeltaA _          = mempty

pairDelta :: Delta a -> Delta b -> Delta (a, b)
pairDelta xs ys = fmap ADFst xs <> fmap ADSnd ys

class Diff a where
  applyAtomicDelta :: a -> AtomicDelta a -> a

  -- | Applying delta.
  -- prop> a /+ da /+ da' = a /+ (da <> da')
  (/+) :: a -> Delta a -> a
  a /+ das =
    -- appEndo (getDual (monoidMap (\da -> Dual $ Endo $ \a -> applyAtomicDelta a da) das)) a
    foldl applyAtomicDelta a das

instance Diff () where
  applyAtomicDelta () _ = ()

instance (Diff a, Diff b) => Diff (a, b) where
  -- (a, b) /+ (da, db) = (a /+ da, b /+ db)
  applyAtomicDelta (a, b) (ADFst da) = (applyAtomicDelta a da, b)
  applyAtomicDelta (a, b) (ADSnd db) = (a, applyAtomicDelta b db)


-- FIXME: use Hughes lists or something similar
-- type Delta a = [AtomicDelta a]
type Delta a = FreeMonoidF (AtomicDelta a)


-- State-Writer, both are composed left-to-right
newtype StateWriterLL s w = StateWriterLL { unStateWriterLL :: s -> (w, s) }

instance Semigroup w => Semigroup (StateWriterLL s w) where
  f <> g = StateWriterLL $ \s ->
    let (m1, s1) = unStateWriterLL f s
        (m2, s2) = unStateWriterLL g s1
    in (m1 <> m2, s2)

instance Monoid w => Monoid (StateWriterLL s w) where
  mempty = StateWriterLL $ \s -> (mempty , s)

iterTrStateless :: (AtomicDelta a -> Delta b) -> (Delta a -> Delta b)
iterTrStateless = foldMap

iterTr :: (AtomicDelta a -> c -> (Delta b, c)) -> (Delta a -> c -> (Delta b, c))
iterTr f = unStateWriterLL . monoidMap (StateWriterLL . f)
