{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE InstanceSigs              #-}
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
import           Data.Proxy           (Proxy (Proxy))
-- import           Data.Proxy           (Proxy (..))

data ExTerm cat term as a b = forall c. ExTerm (term as (PFun cat c a b))



class HasPFun (cat :: k -> k -> Type) where
  type KK cat :: k -> Constraint
  data PFun (cat :: k -> k -> Type) (c :: k) :: k -> k -> k

class (HasPFun cat, LetTerm cat term) => PFunTerm cat (term :: [k] -> k -> Type) | term -> cat where
  pAbsTerm ::
    (AllIn as (K cat), K cat a, K cat b) =>
    term (a ': as) b -> (forall c. (KK cat c, K cat (PFun cat c a b)) => term as (PFun cat c a b) -> r) -> r
    -- ExTerm cat term as a b

  pAppTerm ::
    (AllIn as (K cat), K cat a, K cat b, K cat (PFun cat c a b), KK cat c) =>
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

class (HasPFun cat, App cat e) => LetPFun cat e where
  letPFun :: (K cat a, K cat b, K cat r) => (e a -> e b) -> (forall c. (KK cat c, K cat (PFun cat c a b)) => e (PFun cat c a b) -> e r) -> e r

instance PFunTerm cat term => LetPFun cat (TSem cat term) where
  letPFun ::
    forall a b r. (K cat a, K cat b, K cat r)
    => (TSem cat term  a -> TSem cat term b)
    -> (forall c. (KK cat c, K cat (PFun cat c a b)) => TSem cat term (PFun cat c a b) -> TSem cat term r)
    -> TSem cat term r
  letPFun k1 k2 = TSem $ \(tenv :: Env Proxy as) ->
    let tenvA = ECons (Proxy :: Proxy a) tenv
        body  = runTSem (k1 $ TSem $ \tenv' -> diffT tenvA tenv' $ var0Term tenv) tenvA
    in pAbsTerm body $ \(tm :: term as (PFun cat c a b)) ->
                         runTSem (k2 @c $ TSem $ \tenv' -> diffT tenv tenv' tm) tenv


papp ::
  forall cat term e c a b.
  (PFunTerm cat term, App2 cat term e, K cat a, K cat b, K cat (PFun cat c a b), KK cat c)
  => e (PFun cat c a b) -> e a -> e b
papp = liftSO2 (Proxy @'[ '[], '[] ]) pAppTerm

