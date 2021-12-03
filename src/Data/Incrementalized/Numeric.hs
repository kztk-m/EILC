{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}


{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE BangPatterns               #-}

-- | Numeric operations

module Data.Incrementalized.Numeric
  (
    Delta(..),

    uniI, uniTr, binI, binTr, negateTr, absTr,
  )
where

import           Data.Coerce                (Coercible, coerce)
import           Data.Group                 ()
import           Data.Monoid                (Sum (..))

import           Data.Delta
import           Data.IFq
import           Data.Incrementalized       (fromFunctionsCode,
                                             fromStatelessCode)
import           Data.Incrementalized.Group
import           Language.Unembedding



newtype instance Delta Integer = DeltaInteger (GroupChangeWithReplace Integer)
  deriving (Semigroup, Monoid) via GroupChangeWithReplace (Sum Integer)
  deriving stock Show
  deriving newtype Eq

deriving via FromMonoid (Sum Integer) instance Diff Integer
deriving via FromMonoid (Sum Integer) instance DiffMinus Integer
deriving via FromMonoid (Sum Integer) instance DiffReplace Integer
deriving via FromMonoid (Sum Integer) instance DiffGroupReplace Integer

uniI ::
  forall n. (n -> n) -> n -> (n , n)
uniI op x = (op x, x)

binI ::
  forall n. (n -> n -> n) -> (n, n) -> (n, (n, n))
binI op (x,y) = (op x y, (x,y))

binTr ::
  forall n.
  (Coercible (Delta n) (GroupChangeWithReplace n),
   Coercible (GroupChangeWithReplace n) (Delta n)) =>
  (n -> n -> n) -> (n -> n -> n) -> (n -> n -> n -> n -> n) -> Delta (n, n) -> (n, n) -> (Delta n, (n,n))
binTr mapp op dop (PairDelta dx0 dy0) (x,y) =
  case (coerce @(Delta n) @(GroupChangeWithReplace n) dx0, coerce dy0) of
    (GroupChange dx, GroupChange dy) -> (coerce (GroupChange $ dop dx dy x y), (x `mapp` dx, y `mapp` dy))
    (Replace x', GroupChange dy) ->
      let !y' = y `mapp` dy
      in (coerce $ Replace (op x' y'), (x', y'))
    (GroupChange dx, Replace y') ->
      let !x' = x `mapp` dx
      in (coerce $ Replace (op x' y'), (x', y'))
    (Replace x', Replace y') ->
      (coerce $ Replace (op x' y'), (x', y'))

uniTr ::
  forall n.
  (Coercible (Delta n) (GroupChangeWithReplace n),
   Coercible (GroupChangeWithReplace n) (Delta n)) =>
  (n -> n -> n) -> (n -> n) -> (n -> n -> n) -> Delta n -> n -> (Delta n, n)
uniTr mapp op dop dx0 x =
  case coerce @(Delta n) @(GroupChangeWithReplace n) dx0 of
    GroupChange dx -> (coerce (GroupChange $ dop dx x), x `mapp` dx)
    Replace x'     -> (coerce (Replace $ op x'),        x')

negateTr ::
  forall n.
  (Num n,
   Coercible (Delta n) (GroupChangeWithReplace n),
   Coercible (GroupChangeWithReplace n) (Delta n))
  => Delta n -> Delta n
negateTr n0 = case coerce @(Delta n) @(GroupChangeWithReplace n) n0 of
  Replace x      -> coerce $ Replace (negate x)
  GroupChange dx -> coerce $ GroupChange (negate dx)


absTr :: (Ord n, Num n) => n -> n -> n
absTr dn n
  | n >= 0 && n + dn >= 0 =  dn
  | n >= 0 && n + dn < 0 = - 2 * n - dn -- (- (n + dn)) - n
  | n < 0  && n - dn >= 0 = 2 * n + dn
  | otherwise            = -dn

signumTr :: (Ord n, Num n) => n -> n -> n
signumTr dn n
  | n >= 0 && n + dn >= 0 = 0
  | n >= 0 && n + dn < 0  = -2
  | n < 0  && n + dn > 0  = 2
  | otherwise  = 0

instance HasNum IFqS Integer where
  addS      = fromFunctionsCode [|| binI (+) ||] [|| binTr (+) (+) (\dx dy _ _ -> dx + dy :: Integer) ||]
  multiplyS = fromFunctionsCode [|| binI (*) ||] [|| binTr (+) (*) (\dx dy x y -> dx * y + x * dy :: Integer) ||]
  absS = fromFunctionsCode [|| uniI abs ||] [|| uniTr (+) (abs :: Integer -> Integer) absTr ||]
  signumS = fromFunctionsCode [|| uniI signum ||] [|| uniTr (+) (signum :: Integer -> Integer) signumTr ||]
  fromIntegerS n = fromStatelessCode (const [|| fromInteger n ||]) (const [|| mempty ||])
  negateS = fromStatelessCode (\n -> [|| negate $$n ||]) (\da -> [|| negateTr ($$da :: Delta Integer) ||])
  subtractS = fromFunctionsCode [|| binI (-) ||] [|| binTr (+) (-) (\dx dy _ _ -> dx - dy :: Integer) ||]


-- instance Diff Integer where
--   a /+ DInteger da = a + da
--   checkEmpty (DInteger n) = n == 0

-- instance DiffMinus Integer where
--   a /- b = DInteger (a - b)

newtype instance Delta Int = DeltaInt (GroupChangeWithReplace Int)
  deriving (Semigroup, Monoid) via GroupChangeWithReplace (Sum Int)
  deriving stock Show
  deriving newtype Eq

deriving via FromMonoid (Sum Int) instance Diff Int
deriving via FromMonoid (Sum Int) instance DiffMinus Int
deriving via FromMonoid (Sum Int) instance DiffReplace Int
deriving via FromMonoid (Sum Int) instance DiffGroupReplace Int

-- instance Diff Int where
--   a /+ DInt da = a + da
--   {-# INLINE (/+) #-}

--   checkEmpty (DInt n) = n == 0
--   {-# INLINE checkEmpty #-}

-- instance DiffMinus Int where
--   a /- b = DInt (a - b)

-- newtype instance Delta Word = DeltaWord (Change
--   deriving (Semigroup, Monoid) via (Sum Int)
--   deriving Num via Int
--   deriving stock Show
--   deriving newtype Eq

instance HasNum IFqS Int where
  addS      = fromFunctionsCode [|| binI (+) ||] [|| binTr (+) (+) (\dx dy _ _ -> dx + dy :: Int) ||]
  multiplyS = fromFunctionsCode [|| binI (*) ||] [|| binTr (+) (*) (\dx dy x y -> dx * y + x * dy :: Int) ||]
  absS = fromFunctionsCode [|| uniI abs ||] [|| uniTr (+) (abs :: Int -> Int) absTr ||]
  signumS = fromFunctionsCode [|| uniI signum ||] [|| uniTr (+) (signum :: Int -> Int) signumTr ||]
  fromIntegerS n = fromStatelessCode (const [|| fromInteger n ||]) (const [|| mempty ||])
  negateS = fromStatelessCode (\n -> [|| negate $$n ||]) (\da -> [|| negateTr ($$da :: Delta Int) ||])
  subtractS = fromFunctionsCode [|| binI (-) ||] [|| binTr (+) (-) (\dx dy _ _ -> dx - dy :: Int) ||]


newtype instance Delta (Sum n) = DeltaSum { getDeltaSum :: Delta n }

deriving stock instance Show (Delta n) => Show (Delta (Sum n))

deriving newtype instance Semigroup (Delta n) => Semigroup (Delta (Sum n))
deriving newtype instance Monoid    (Delta n) => Monoid    (Delta (Sum n))

deriving via n instance Diff n => Diff (Sum n)
deriving via n instance DiffMinus n => DiffMinus (Sum n)
deriving via n instance DiffReplace n => DiffReplace (Sum n)

instance DiffGroupReplace (Sum Int)
instance DiffGroupReplace (Sum Integer)
instance DiffGroupReplace (Sum Double)

instance HasNum IFqS (Sum Int) where
  addS      = fromFunctionsCode [|| binI (+) ||] [|| binTr (+) (+) (\dx dy _ _ -> dx + dy :: Sum Int) ||]
  multiplyS = fromFunctionsCode [|| binI (*) ||] [|| binTr (+) (*) (\dx dy x y -> dx * y + x * dy :: Sum Int) ||]
  absS = fromFunctionsCode [|| uniI abs ||] [|| uniTr (+) (abs :: Sum Int -> Sum Int) absTr ||]
  signumS = fromFunctionsCode [|| uniI signum ||] [|| uniTr (+) (signum :: Sum Int -> Sum Int) signumTr ||]
  fromIntegerS n = fromStatelessCode (const [|| fromInteger n ||]) (const [|| mempty ||])
  negateS = fromStatelessCode (\n -> [|| negate $$n ||]) (\da -> [|| negateTr ($$da :: Delta (Sum Int)) ||])
  subtractS = fromFunctionsCode [|| binI (-) ||] [|| binTr (+) (-) (\dx dy _ _ -> dx - dy :: Sum Int) ||]

-- instance Diff Word where
--   a /+ DWord da = a + fromIntegral da
--   {-# INLINE (/+) #-}

--   checkEmpty (DWord n) = n == 0
--   {-# INLINE checkEmpty #-}

-- instance DiffMinus Word where
--   a /- b = DWord (fromIntegral a - fromIntegral b)

-- | This definition does not care machine errors.
newtype instance Delta Double = DeltaDouble (GroupChangeWithReplace Double)
  deriving (Semigroup, Monoid) via GroupChangeWithReplace (Sum Double)
  deriving stock Show
  deriving newtype Eq

deriving via FromMonoid (Sum Double) instance Diff Double
deriving via FromMonoid (Sum Double) instance DiffMinus Double
deriving via FromMonoid (Sum Double) instance DiffReplace Double
deriving via FromMonoid (Sum Double) instance DiffGroupReplace Double


instance HasNum IFqS Double where
  addS      = fromFunctionsCode [|| binI (+) ||] [|| binTr (+) (+) (\dx dy _ _ -> dx + dy :: Double) ||]
  multiplyS = fromFunctionsCode [|| binI (*) ||] [|| binTr (+) (*) (\dx dy x y -> dx * y + x * dy :: Double) ||]
  absS = fromFunctionsCode [|| uniI abs ||] [|| uniTr (+) (abs :: Double -> Double) absTr ||]
  signumS = fromFunctionsCode [|| uniI signum ||] [|| uniTr (+) (signum :: Double -> Double) signumTr ||]
  fromIntegerS n = fromStatelessCode (const [|| fromInteger n ||]) (const [|| mempty ||])
  negateS = fromStatelessCode (\n -> [|| negate $$n ||]) (\da -> [|| negateTr ($$da :: Delta Double) ||])
  subtractS = fromFunctionsCode [|| binI (-) ||] [|| binTr (+) (-) (\dx dy _ _ -> dx - dy :: Double) ||]


-- instance Diff Double where
--   a /+ DDouble da = a + da
--   {-# INLINE (/+) #-}

--   checkEmpty (DDouble n) = n == 0
--   {-# INLINE checkEmpty #-}

-- instance DiffMinus Double where
--   a /- b = DDouble (a - b)
