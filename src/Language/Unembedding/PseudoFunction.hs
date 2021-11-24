{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

module Language.Unembedding.PseudoFunction where

import           Data.Kind            (Constraint, Type)
import           Language.Unembedding

import           Data.Env
-- import           Data.Proxy           (Proxy (..))

data ExTerm cat term as a b = forall c. ExTerm (term as (PFun cat c a b))

class Term cat term => PFunTerm cat (term :: [k] -> k -> Type) where
  data PFun cat c :: k -> k -> k
  type KK cat c :: Constraint

  pAbsTerm ::
    (AllIn as (K cat), K cat a, K cat b) =>
    term (a ': as) b -> (forall c. KK cat c => term as (PFun cat c a b) -> r) -> r
    -- ExTerm cat term as a b

  pAppTerm ::
    (AllIn as (K cat), K cat a, K cat b, KK cat c) =>
    term as (PFun cat c a b) -> term as a -> term as b

{-

Unfortunately, we are not able to make

  pAbs :: (e a -> e b) -> exists c. e (PFun cat c a b)

at least by using the standard way of unembedding where we interpret e as

  e a = forall env. SList env -> term env a

Notice that in pAbsTerm the choice of c depends on term (a ': as) b. However,
to have pAbs, we need to obtain env to make a term. However, the type

  exists c. e (PFun cat c a b)

requires us to determine c before we take env.

-}
