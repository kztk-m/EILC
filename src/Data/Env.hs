{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Data.Env where

import           Data.Kind (Constraint, Type)

data Env (f :: k -> Type) (as :: [k]) where
  ENil  :: Env f '[]
  ECons :: f a -> Env f as -> Env f (a ': as)

pattern (:>) :: () => (rs ~ (a : as)) => f a -> Env f as -> Env f rs
pattern a :> as = ECons a as

infixr 5 :>

type family AllIn as c :: Constraint where
  AllIn '[] c = ()
  AllIn (a ': as) c = (c a, AllIn as c)


-- class AllIn (as :: [k]) (c :: k -> Constraint)  where
--   indAs :: Proxy c -> forall p. p '[] -> (forall b bs. (c b, AllIn bs c) => p bs -> p (b ': bs)) -> p as

-- instance AllIn '[] c where
--   indAs _ p0 _ = p0
-- instance (c a, AllIn as c) => AllIn (a ': as) c where
--   indAs pc p0 pstep = pstep (indAs pc p0 pstep)

mapEnv :: (forall a. f a -> g a) -> Env f as -> Env g as
mapEnv _ ENil         = ENil
mapEnv h (ECons x xs) = ECons (h x) (mapEnv h xs)

mapEnvA :: Applicative k => (forall a. f a -> k (g a)) -> Env f as -> k (Env g as)
mapEnvA _ ENil         = pure ENil
mapEnvA h (ECons x xs) = ECons <$> h x <*> mapEnvA h xs

headEnv :: Env f (a ': as) -> f a
headEnv (ECons a _) = a

tailEnv :: Env f (a ': as) -> Env f as
tailEnv (ECons _ r) = r

headTailEnv :: Env f (a ': as) -> (f a, Env f as)
headTailEnv (ECons a as) = (a, as)

zipWithEnv :: (forall a. f a -> g a -> h a) -> Env f as -> Env g as -> Env h as
zipWithEnv _ ENil ENil                 = ENil
zipWithEnv k (ECons x xs) (ECons y ys) = ECons (k x y) $ zipWithEnv k xs ys

lenEnv :: Env f as -> Int
lenEnv ENil        = 0
lenEnv (ECons _ r) = 1 + lenEnv r

type family Append (xs :: [k]) (ys :: [k]) where
  Append '[] ys       = ys
  Append (x ': xs) ys = x ': Append xs ys

appendEnv :: Env f xs -> Env f ys -> Env f (Append xs ys)
appendEnv ENil ys         = ys
appendEnv (ECons x xs) ys = ECons x (appendEnv xs ys)
