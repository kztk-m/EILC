{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE TypeFamilies   #-}
module Data.Conn where
import           Data.Data (Typeable)



data NETree a = NEOne a | NEJoin !(NETree a) !(NETree a)
data Tree a = None | NE (NETree a)

data Conn f as where
  CNone :: Conn f 'None
  CNE   :: !(NEConn f as) -> Conn f ('NE as)

data NEConn f as where
  COne  :: !(f a) -> NEConn f ('NEOne a)
  CJoin :: !(NEConn f as) -> !(NEConn f bs) -> NEConn f ('NEJoin as bs)

map2Conn :: (forall a. f a -> g a) -> Conn f as -> Conn g as
map2Conn _ CNone     = CNone
map2Conn f (CNE cne) = CNE (map2NEConn f cne)

map2NEConn :: (forall a. f a -> g a) -> NEConn f as -> NEConn g as
map2NEConn f (COne a)      = COne (f a)
map2NEConn f (CJoin c1 c2) = CJoin (map2NEConn f c1) (map2NEConn f c2)


type family Join (as :: Tree k) (bs :: Tree k) :: Tree k where
  Join 'None a      = a
  Join ('NE a) 'None = 'NE a
  Join ('NE a) ('NE b) = 'NE ('NEJoin a b)

joinConn :: Conn f as -> Conn f bs -> Conn f (Join as bs)
joinConn CNone c         = c
joinConn (CNE x) CNone   = CNE x
joinConn (CNE x) (CNE y) = CNE (CJoin x y)

data IsNone as where
  IsNoneTrue  :: IsNone 'None
  IsNoneFalse :: IsNone ('NE sh)

isNoneAnd :: IsNone as -> IsNone bs -> IsNone (Join as bs)
isNoneAnd IsNoneTrue  b           = b
isNoneAnd IsNoneFalse IsNoneTrue  = IsNoneFalse
isNoneAnd IsNoneFalse IsNoneFalse = IsNoneFalse

decompConn :: IsNone as -> IsNone bs -> Conn f (Join as bs) -> (Conn f as, Conn f bs)
decompConn IsNoneTrue  _            c                = (CNone, c)
decompConn IsNoneFalse IsNoneTrue  (CNE x)           = (CNE x, CNone)
decompConn IsNoneFalse IsNoneFalse (CNE (CJoin x y)) = (CNE x, CNE y)

isNone :: Conn proxy cs -> IsNone cs
isNone CNone   = IsNoneTrue
isNone (CNE _) = IsNoneFalse

