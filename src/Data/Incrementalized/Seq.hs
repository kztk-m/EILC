{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
module Data.Incrementalized.Seq
  (
    Seq(..), Delta(..), AtomicDelta(..), fromList,

    singletonF, emptyF, nullF, appendF, concatF, mapF, filterF,

    -- * Component functions
    singletonTr, nullInit, nullTrAtomic,
    appendInit, appendTrAtomic, AppendCache,
    concatInit, concatTrAtomic, MapCache(..),
    mapInit, mapTr, mapTrChanged, mapTrUnchangedAtomic,
    filterInit, filterTr, filterTrChanged, filterTrUnchangedAtomic,
  ) where

import           Prelude                             hiding (id, (.))

import           Data.Delta
import           Data.IFq
import           Data.Incrementalized.Function
import           Data.Proxy                          (Proxy (Proxy))
import           Data.Typeable                       (Typeable)
import           Language.Unembedding                as Unemb
import           Language.Unembedding.PseudoFunction (PFunTerm)

import           Data.Incrementalized.Seq.Core


mapF ::
  forall term e a b.
  (Diff a, Typeable a, Diff b, Typeable b, PFunTerm IFqS term, App2 IFqS term e)
  => (e a -> e b) -> e (Seq a) -> e (Seq b)
mapF =
  Unemb.liftSO2 (Proxy @'[ '[a], '[] ]) (fromPFun mapC)

filterF ::
  forall term e a.
  (Diff a, Typeable a, PFunTerm IFqS term, App2 IFqS term e)
  => (e a -> e Bool) -> e (Seq a) -> e (Seq a)
filterF =
  Unemb.liftSO2 (Proxy @'[ '[a], '[] ]) (fromPFun filterC)
