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
module Data.IF where

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
-- prop> let IF f tr = h in f (a /+ da) == let (b, c) = f a in let (db, c') = tr da c in (b /+ db, c')
-- prop> let IF _ tr = h in tr mempty c == (mempty, c)
-- prop> let IF _ tr = h in tr (da1 <> da2) c = let (db1, c1) = tr da1 c in (db2, c2) = tr da2 c1 in (db1 <> db2, c2)
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




-- -- simplarly to IF but a is applied partially beforehand
-- data IV a b = forall c. IV !(b, c) !(Delta a -> c -> (Delta b, c))

-- -- iterTr f [] c = ([], c)
-- -- iterTr f (da : das) c =
-- --   let (db,  c1) = f da c
-- --       (res, c2) = iterTr f das c1
-- --   in (db <> res, c2)

-- instance CategoryK IF where
-- --  type K IF = HasAtomicDelta

--   id = IF (\a -> (a, ())) (\da c -> (da , c))

--   IF f2 tr2 . IF f1 tr1 = IF f tr
--     where
--       f a = let (b, c1) = f1 a
--                 (c, c2) = f2 b
--             in (c, (c1, c2))

--       tr da (c1 , c2) =
--         let (dbs , c1') = tr1 da c1
--             (dc , c2')  = tr2 dbs c2
--         in (dc , (c1' , c2'))

-- prodIF :: IF s a -> IF s b -> IF s (a, b)
-- prodIF (IF f1 tr1) (IF f2 tr2) = IF f tr
--   where
--     f s = let (a, c1) = f1 s
--               (b, c2) = f2 s
--           in ( (a, b), (c1, c2) )

--     tr ds (c1 , c2) =
--       let (da , c1') = tr1 ds c1
--           (db , c2') = tr2 ds c2
--       in ( pairDelta da db , (c1' , c2') )

-- toIF :: Diff a => (a -> b) -> (a -> Delta a -> Delta b) -> IF a b
-- toIF f df = IF (\a -> (f a, a)) (\da a -> (df a da, a /+ da))

-- -- runIF :: IF a b -> a -> (b, [Delta a] -> [Delta b])
-- -- runIF (IF f tr) a =
-- --   let (b, c) = f a
-- --   in (b, comp c)
-- --   where
-- --     comp _ [] = []
-- --     comp c (da : das) =
-- --       let (db, c') = tr da c
-- --       in db : comp c' das

-- class Incr e where
--   liftI :: Diff a => (a -> b) -> (a -> Delta a -> Delta b) -> e a -> e b
--   shareI :: e a -> (e a -> e b) -> e b

--   pairI :: e a -> e b -> e (a, b)

-- data Index f as where
--   IndexZ :: f a -> Index f (a ': as)
--   IndexS :: Index f as -> Index f (b ': as)


-- newtype PackedAtomicDelta f a = PackedAtomicDelta { getAtomicDelta :: AtomicDelta (f a) }


-- newtype PackedDelta f a = PackedDelta (Delta (f a))

-- newtype instance Delta (Env f as) = DeltaEnv { getDeltaEnv :: Env (PackedDelta f) as }

-- instance AllInFF Delta f as Semigroup => Semigroup (Delta (Env f as)) where
--   DeltaEnv ENil <> DeltaEnv ENil = DeltaEnv ENil
--   DeltaEnv (ECons (PackedDelta da) das) <> DeltaEnv (ECons (PackedDelta da') das') = DeltaEnv (ECons (PackedDelta $ da <> da') $ coerce (DeltaEnv das <> DeltaEnv das'))


-- type family AllInFF f g as c :: Constraint where
--   AllInFF f g '[] c      = ()
--   AllInFF f g (a ': as) c = (c (f (g a)), AllInFF f g as c)


-- type family AllInF f as c :: Constraint where
--   AllInF f '[] c = ()
--   AllInF f (a ': as) c = (c (f a), AllInF f as c)
-- instance AllInF f as Diff => Diff (Env f as) where
--   ENil /+ _                             = ENil
--   ECons a as /+ DeltaEnv (ECons (PackedDelta da) das) = ECons (a /+ da) (as /+ DeltaEnv das)

-- instance AllInF f as HasAtomicDelta => HasAtomicDelta (Env f as) where
--   newtype instance AtomicDelta (Env f as) = AtomicDeltaEnv { getAtomicDeltaEnv :: Index (PackedAtomicDelta f) as }

--   injDelta (AtomicDeltaEnv (IndexZ (PackedAtomicDelta da))) = DeltaEnv (ECons (PackedDelta $ injDelta da) mempty)
--   injDelta (AtomicDeltaEnv (IndexS x)) = DeltaEnv (ECons (PackedDelta mempty) (getDeltaEnv $ injDelta $ AtomicDeltaEnv x))

--   monoidMap f (DeltaEnv ENil) = mempty
--   monoidMap f (DeltaEnv (ECons (PackedDelta da) das)) = monoidMap (f . AtomicDeltaEnv . IndexZ . PackedAtomicDelta) da <> monoidMap (f . AtomicDeltaEnv . IndexS . getAtomicDeltaEnv) (DeltaEnv das)




-- tailIF :: IF (Env Identity (a : as)) (Env Identity as)
-- tailIF = IF (\(ECons _ r) -> (r, ()))
-- --            (iterTr $ \(ECons _ dr) _ -> (dr, ()))
--             (\(DeltaEnv (ECons _ ds)) _ -> (DeltaEnv ds, ()))
--             -- (iterTr $ \(AtomicDeltaEnv x) _ ->
--             --   case x of
--             --     IndexZ _  -> (mempty, ())
--             --     IndexS am -> (pure (AtomicDeltaEnv am), ()))

-- headIF :: IF (Env Identity (a : as)) a
-- headIF = IF (\(ECons a _) -> (coerce a, ()))
-- --            (iterTr $ \(ECons da _) _ -> (coerce da, ()))
--             (\(DeltaEnv (ECons (PackedDelta (IdentityDelta da)) _)) _ -> (da, ()))
--             -- (iterTr $ \(AtomicDeltaEnv x) _ -> case x of
--             --   IndexZ da -> (pure $ runADIdentity $ getAtomicDelta da , ())
--             --   IndexS _  -> (mempty, ()))


-- newtype UnembIncr b = UnembIncr { runUnembIncr :: forall as. Env Proxy as -> IF (Env Identity as) b  }

-- instance Incr UnembIncr where
--   liftI f df (UnembIncr x) = UnembIncr (\tenv -> toIF f df . x tenv)

--   shareI (UnembIncr e0) k = UnembIncr $ \tenv ->
--     let tenv1 = ECons Proxy tenv
--         arg   = UnembIncr $ \tenv' -> diff tenv1 tenv' headIF
--     in runUnembIncr (k arg) tenv1. toEnv . prodIF (e0 tenv) id
--     where
--       diff :: Env Proxy as -> Env Proxy bs -> IF (Env Identity as) a -> IF (Env Identity bs) a
--       diff tenv1 tenv2 = diff' (lenEnv tenv2 - lenEnv tenv1) tenv1 tenv2
--         where
--           diff' :: Int -> Env Proxy xs -> Env Proxy ys -> IF (Env Identity xs) a -> IF (Env Identity ys) a
--           diff' 0 _ _ x             = Unsafe.unsafeCoerce x
--           diff' n γ1 (ECons _ γ2) x = diff' (n-1) γ1 γ2 x . tailIF
--           diff' _ _ _ _             = error "Unreachable"


--       toEnv :: IF (a, Env Identity as) (Env Identity (a ': as))
--       toEnv = IF (\(a, as) -> (ECons (Identity a) as, ()))
--                  -- (\(da, das) _ -> (ECons (PackedDelta da) das, ()))
--                  (iterTr $ \x _ -> case x of
--                    ADFst da  -> (injDelta  $ AtomicDeltaEnv $ IndexZ (PackedAtomicDelta $ ADIdentity da), ())
--                    ADSnd das -> (injDelta $ AtomicDeltaEnv $ IndexS $ coerce das, ()))

--   pairI (UnembIncr x) (UnembIncr y) = UnembIncr $ \tenv -> prodIF (x tenv) (y tenv)

-- runIncrMono :: (HasAtomicDelta a, HasAtomicDelta b) => (UnembIncr a -> UnembIncr b) -> IF a b
-- runIncrMono f = runUnembIncr (shareI (UnembIncr $ \(ECons Proxy _) -> Unsafe.unsafeCoerce headIF) f) (ECons Proxy ENil) . singleton
--   where
--     singleton :: HasAtomicDelta a => IF a (Env Identity '[a])
--     singleton = IF (\a -> (ECons (Identity a) ENil, ()))
-- --                   (\da _ -> (ECons (PackedDelta da) ENil, ()))
--                    (iterTr $ \da _ -> (injDelta $ AtomicDeltaEnv $ IndexZ $ coerce da, ()))



-- -- >>> let (res, tr) = runIF (runIncrMono aveD) (Bag [1..100])
-- -- >>> res
-- -- >>> let dbs = tr [Bag [1], Bag [2], Bag [30]]
-- -- >>> dbs
-- -- >>> res /+ mconcat dbs
-- -- Variable not in scope: runIF :: IF a0 b0 -> t0 -> (a, b)
-- -- Variable not in scope: aveD :: UnembIncr a0 -> UnembIncr b0
-- -- Data constructor not in scope: Bag :: [a1] -> t0

-- --- >>> (100000 + sum [1..100]) / 101
-- -- 1040.09900990099
