{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TypeFamilies    #-}

module Data.Conn
  (
    Conn(..), NEConn(..),

    -- * Mapping
    map2Conn,

    -- * Construction, Decomposition
    singleton, pattern CSingle, Join, joinConn, decompConn,

    -- * Witness of Emptiness
    IsNone(..), isNone, isNoneAnd
  ) where

import           Data.JoinList (JoinList (..), JoinListNE (..))

data Conn f as where
  CNone :: Conn f 'JLNil
  CNE :: !(NEConn f as) -> Conn f ('JLNonEmpty as)

data NEConn f as where
  COne :: !(f a) -> NEConn f ('JLSingle a)
  CJoin :: !(NEConn f as) -> !(NEConn f bs) -> NEConn f ('JLJoin as bs)

pattern CSingle :: () => r ~ 'JLNonEmpty ('JLSingle a) => f a -> Conn f r
pattern CSingle a = CNE (COne a)


singleton :: f a -> Conn f ('JLNonEmpty ('JLSingle a))
singleton = CSingle

map2Conn :: (forall a. f a -> g a) -> Conn f as -> Conn g as
map2Conn _ CNone     = CNone
map2Conn f (CNE cne) = CNE (map2NEConn f cne)

map2NEConn :: (forall a. f a -> g a) -> NEConn f as -> NEConn g as
map2NEConn f (COne a)      = COne (f a)
map2NEConn f (CJoin c1 c2) = CJoin (map2NEConn f c1) (map2NEConn f c2)

type family Join (as :: JoinList k) (bs :: JoinList k) :: JoinList k where
  Join 'JLNil a = a
  Join ('JLNonEmpty a) 'JLNil = 'JLNonEmpty a
  Join ('JLNonEmpty a) ('JLNonEmpty b) = 'JLNonEmpty ('JLJoin a b)

joinConn :: Conn f as -> Conn f bs -> Conn f (Join as bs)
joinConn CNone c         = c
joinConn (CNE x) CNone   = CNE x
joinConn (CNE x) (CNE y) = CNE (CJoin x y)

data IsNone as where
  IsNoneTrue :: IsNone 'JLNil
  IsNoneFalse :: IsNone ('JLNonEmpty sh)

isNoneAnd :: IsNone as -> IsNone bs -> IsNone (Join as bs)
isNoneAnd IsNoneTrue b            = b
isNoneAnd IsNoneFalse IsNoneTrue  = IsNoneFalse
isNoneAnd IsNoneFalse IsNoneFalse = IsNoneFalse

decompConn
  :: IsNone as -> IsNone bs -> Conn f (Join as bs) -> (Conn f as, Conn f bs)
decompConn IsNoneTrue _ c                            = (CNone, c)
decompConn IsNoneFalse IsNoneTrue (CNE x)            = (CNE x, CNone)
decompConn IsNoneFalse IsNoneFalse (CNE (CJoin x y)) = (CNE x, CNE y)

isNone :: Conn proxy cs -> IsNone cs
isNone CNone   = IsNoneTrue
isNone (CNE _) = IsNoneFalse

