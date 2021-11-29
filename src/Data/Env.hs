{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Env
  (
    Env(..), pattern (:>),

    -- * Operations
    mapEnv, traverseEnv, headEnv, tailEnv,
    headTailEnv, lenEnv, zipWithEnv,

    Append, appendEnv,

    -- * Constraints
    AllIn, AllInF,
  ) where

import           Data.Kind (Constraint, Type)

-- $setup
-- >>> import Data.Functor.Identity (Identity(..))
-- >>> import Control.Applicative (Const(..))

data Env (f :: k -> Type) (as :: [k]) where
  ENil  :: Env f '[]
  ECons :: f a -> Env f as -> Env f (a ': as)

type family AllInF f as c :: Constraint where
  AllInF f '[] c = ()
  AllInF f (a ': as) c = (c (f a), AllInF f as c)

deriving stock instance (AllInF f as Show) => Show (Env f as)

pattern (:>) :: () => (rs ~ (a : as)) => f a -> Env f as -> Env f rs
pattern a :> as = ECons a as

infixr 5 :>

type family AllIn as c :: Constraint where
  AllIn '[] c = ()
  AllIn (a ': as) c = (c a, AllIn as c)

-- | Mapping function
mapEnv :: (forall a. f a -> g a) -> Env f as -> Env g as
mapEnv _ ENil         = ENil
mapEnv h (ECons x xs) = ECons (h x) (mapEnv h xs)

-- | Mapping function with effect.
traverseEnv :: Applicative k => (forall a. f a -> k (g a)) -> Env f as -> k (Env g as)
traverseEnv _ ENil         = pure ENil
traverseEnv h (ECons x xs) = ECons <$> h x <*> traverseEnv h xs

-- | Extract head.
--
-- >>> headEnv (ECons (Identity 1) (ECons (Identity 2) ENil))
-- Identity 1
headEnv :: Env f (a ': as) -> f a
headEnv (ECons a _) = a

-- | Extract tail.
--
-- >>> tailEnv (ECons (Identity 1) (ECons (Identity 2) ENil))
-- ECons (Identity 2) ENil
tailEnv :: Env f (a ': as) -> Env f as
tailEnv (ECons _ r) = r

-- | Extract both head and tail.
--
-- >>> headTailEnv (ECons (Identity 1) (ECons (Identity 2) ENil))
-- (Identity 1,ECons (Identity 2) ENil)
headTailEnv :: Env f (a ': as) -> (f a, Env f as)
headTailEnv (ECons a as) = (a, as)

-- | Zipping
--
-- >>> zipWithEnv (\(Const b) (Identity a) -> if b then Just a else Nothing) (ECons (Const True) (ECons (Const False) ENil)) (ECons (Identity 1) (ECons (Identity 2) ENil))
-- ECons (Just 1) (ECons Nothing ENil)
zipWithEnv :: (forall a. f a -> g a -> h a) -> Env f as -> Env g as -> Env h as
zipWithEnv _ ENil ENil                 = ENil
zipWithEnv k (ECons x xs) (ECons y ys) = ECons (k x y) $ zipWithEnv k xs ys

-- | The length of an environment.
--
-- >>> lenEnv ENil
-- 0
-- >>> lenEnv (ECons (Identity 1) (ECons (Identity 2) ENil))
-- 2
lenEnv :: Env f as -> Int
lenEnv ENil        = 0
lenEnv (ECons _ r) = 1 + lenEnv r

type family Append (xs :: [k]) (ys :: [k]) where
  Append '[] ys       = ys
  Append (x ': xs) ys = x ': Append xs ys

appendEnv :: Env f xs -> Env f ys -> Env f (Append xs ys)
appendEnv ENil ys         = ys
appendEnv (ECons x xs) ys = ECons x (appendEnv xs ys)
