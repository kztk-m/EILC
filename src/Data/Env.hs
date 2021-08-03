{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE TypeOperators   #-}

module Data.Env where

import           Data.Kind (Type)

data Env (f :: k -> Type) (as :: [k]) where
  ENil  :: Env f '[]
  ECons :: f a -> Env f as -> Env f (a ': as)

pattern (:>) :: () => (rs ~ (a : as)) => f a -> Env f as -> Env f rs
pattern a :> as = ECons a as

infixr 5 :>

mapEnv :: (forall a. f a -> g a) -> Env f as -> Env g as
mapEnv _ ENil         = ENil
mapEnv h (ECons x xs) = ECons (h x) (mapEnv h xs)

lenEnv :: Env f as -> Int
lenEnv ENil        = 0
lenEnv (ECons _ r) = 1 + lenEnv r

type family Append (xs :: [k]) (ys :: [k]) where
  Append '[] ys       = ys
  Append (x ': xs) ys = x ': Append xs ys

appendEnv :: Env f xs -> Env f ys -> Env f (Append xs ys)
appendEnv ENil ys         = ys
appendEnv (ECons x xs) ys = ECons x (appendEnv xs ys)
