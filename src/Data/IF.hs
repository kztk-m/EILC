{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}

module Data.IF
  (
    IF (..), IFT(..), Delta(..),
    PackedDelta(..), PackedDiff(..)
  ) where

import           Data.Delta
import           Data.Env
import           Data.Functor.Identity
import           Language.Unembedding


import           Data.Coerce           (coerce)
import           Data.Incrementalized
import           Data.Interaction
import           Data.Typeable         (Typeable)
import           Prelude               hiding (id, (.))

-- | Incremtalized function
--
-- For @h = IF f tr@, it is expected that the following laws to hold.
--
-- @
-- f (a /+ da) == (let (b, c) = f a in let (db, c') = tr da c in (b /+ db, c'))
-- tr mempty c == (mempty, c)
-- tr (da1 <> da2) c = (let (db1, c1) = tr da1 c in (db2, c2) = tr da2 c1 in (db1 <> db2, c2))
-- @
data IF a b = forall c. Typeable c => IF !(a -> (b, c)) !(Delta a -> c -> (Delta b, c))

instance CategoryK IF where
  type K IF = DiffTypeable
  id = IF (\a -> (a, ())) (\da _ -> (da, ()))
  IF f2 tr2 . IF f1 tr1 = IF f tr
    where
      f a =
        let (b, c1) = f1 a
            (c, c2) = f2 b
        in (c, (c1, c2))
      tr da (c1,c2) =
        let (db, c1') = tr1 da c1
            (dc, c2') = tr2 db c2
        in (dc, (c1', c2'))

instance HasProduct IF where
  type Unit IF = ()
  type Prod IF a b = (a, b)
  unitOk _ = Wit
  prodOk _ _ _ = Wit

instance Cartesian IF where
  multS (IF f1 tr1) (IF f2 tr2) = IF f tr
    where
      f s =
        let (a, c1) = f1 s
            (b, c2) = f2 s
        in ( (a, b), (c1, c2) )
      tr ds (c1, c2) =
        let (da, c1') = tr1 ds c1
            (db, c2') = tr2 ds c2
        in ( pairDelta da db , (c1', c2') )
  unitS = fromStatelessIdentity (const ()) (const mempty)
  fstS _ _ = fromStatelessIdentity fst fstDelta
  sndS _ _ = fromStatelessIdentity snd sndDelta

instance IncrementalizedQ IF where
  type CodeType IF = Identity
  fromStateless f tr = IF (\a -> (coerce f a, ())) (\da _ -> (coerce tr da, ()))
  fromFunctions _ f tr = IF (runIdentity f) (coerce tr)
  compile (IF f tr) = Identity $ \a ->
    let (b, c0) = f a
        int c = Interaction $ \da ->
          let (db, c') = tr da c
          in (db, int c')
    in (b, int c0)

data PackedDelta a where
  PackedDelta :: Monoid (Delta a) => { unpackDelta :: Delta a } -> PackedDelta a
data PackedDiff a where
  PackedDiff :: Diff a => { unpackDiff :: a } -> PackedDiff a

newtype IFT as b = IFT (IF (Env PackedDiff as) b)

data instance Delta (Env PackedDiff as) where
  DNil    :: Delta (Env PackedDiff '[])
  DMEmpty :: Delta (Env PackedDiff as)
  DCons   :: Diff a => Delta a -> Delta (Env PackedDiff as) -> Delta (Env PackedDiff (a ': as))

instance Semigroup (Delta (Env PackedDiff as)) where
  d <> DMEmpty                 = d
  DMEmpty <> d                 = d
  DNil <> DNil                 = DNil
  DCons da das <> DCons db dbs = DCons (da <> db) (das <> dbs)

instance Monoid (Delta (Env PackedDiff as)) where
  mempty = DMEmpty

instance Diff (Env PackedDiff as) where
  a /+ DMEmpty = a
  ENil /+ DNil = ENil
  ECons (PackedDiff a) as /+ DCons da das = ECons (PackedDiff (a /+ da)) (as /+ das)

  checkEmpty DMEmpty        = True
  checkEmpty DNil           = True
  checkEmpty (DCons da das) = checkEmpty da && checkEmpty das

-- witTypeableEnv :: AllIn s DiffTypeable => Wit (Typeable s)

instance Term IF IFT where
  mapTerm (IF f2 tr2) (IFT (IF f1 tr1)) = IFT (IF f tr)
    where
      f s =
        let (a, c1) = f1 s
            (b, c2) = f2 a
        in (b, (c1, c2))
      tr ds (c1, c2) =
        let (da , c1') = tr1 ds c1
            (db , c2') = tr2 da c2
        in (db, (c1' , c2'))

  multTerm (IFT (IF f1 tr1)) (IFT (IF f2 tr2)) = IFT (IF f tr)
    where
      f s = let (a , c1) = f1 s
                (b , c2) = f2 s
            in ( (a , b) , (c1 , c2) )
      tr ds (c1 , c2) =
        let (da , c1') = tr1 ds c1
            (db , c2') = tr2 ds c2
        in (pairDelta da db , (c1' , c2') )
  unitTerm _ = IFT $ fromStatelessIdentity (const ()) (const mempty)

  var0Term _ = IFT $ IF f tr
    where
      f :: Env PackedDiff (a ': as) -> (a, ())
      f (ECons (PackedDiff a) _) = (a, ())
      tr :: Diff a => Delta (Env PackedDiff (a ': as)) -> () -> (Delta a, ())
      tr (DCons da _) _ = (da, ())
      tr DMEmpty      _ = (mempty, ())

  weakenTerm (IFT (IF f tr)) = IFT (IF f' tr')
    where
      f' (ECons _ as) = f as
      tr' (DCons _ as) c = tr as c
      tr' DMEmpty      c = tr DMEmpty c

  unliftTerm (IFT (IF f tr)) = IF f' tr'
    where
      f' a = f (ECons (PackedDiff a) ENil)
      tr' da = tr (DCons da DNil)

instance LetTerm IF IFT where
  letTerm (IFT (IF f1 tr1)) (IFT (IF f2 tr2)) = IFT (IF f tr)
    where
      f s =
        let (a, c1) = f1 s
            (b, c2) = f2 (ECons (PackedDiff a) s)
        in (b, (c1, c2))
      tr ds (c1, c2) =
        let (da, c1') = tr1 ds c1
            (db, c2') = tr2 (DCons da ds) c2
        in (db , (c1', c2'))

