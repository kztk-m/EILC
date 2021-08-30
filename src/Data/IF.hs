{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
module Data.IF where

import           Data.Delta
import           Data.Env
import           Data.Functor.Identity
import           Data.Proxy
import           Language.Unembedding
import qualified Unsafe.Coerce         as Unsafe

import           Data.Coerce           (coerce)
import           Prelude               hiding (id, (.))

-- | Incremtalized function
--
-- prop> let (b, tr) = runIF f a in f (foldl (/+) a das) == foldl (/+) b (tr das)
-- Or, equivalently
-- prop> let (b, tr) = runIF f a in f (a /+ mconcat das) == b /+ mconcat das
data IF a b = forall c. IF !(a -> (b, c)) !(Delta a -> c -> (Delta b, c))

-- simplarly to IF but a is applied partially beforehand
data IV a b = forall c. IV !(b, c) !(Delta a -> c -> (Delta b, c))

-- iterTr f [] c = ([], c)
-- iterTr f (da : das) c =
--   let (db,  c1) = f da c
--       (res, c2) = iterTr f das c1
--   in (db <> res, c2)

instance CategoryK IF where
  id = IF (\a -> (a, ())) (\da c -> (da , c))

  IF f2 tr2 . IF f1 tr1 = IF f tr
    where
      f a = let (b, c1) = f1 a
                (c, c2) = f2 b
            in (c, (c1, c2))

      tr da (c1 , c2) =
        let (dbs , c1') = tr1 da c1
            (dc , c2')  = tr2 dbs c2
        in (dc , (c1' , c2'))

prodIF :: IF s a -> IF s b -> IF s (a, b)
prodIF (IF f1 tr1) (IF f2 tr2) = IF f tr
  where
    f s = let (a, c1) = f1 s
              (b, c2) = f2 s
          in ( (a, b), (c1, c2) )

    tr ds (c1 , c2) =
      let (da , c1') = tr1 ds c1
          (db , c2') = tr2 ds c2
      in ( fmap ADFst da <> fmap ADSnd db , (c1' , c2') )

toIF :: Diff a => (a -> b) -> (a -> Delta a -> Delta b) -> IF a b
toIF f df = IF (\a -> (f a, a)) (\da a -> (df a da, a /+ da))

-- runIF :: IF a b -> a -> (b, [Delta a] -> [Delta b])
-- runIF (IF f tr) a =
--   let (b, c) = f a
--   in (b, comp c)
--   where
--     comp _ [] = []
--     comp c (da : das) =
--       let (db, c') = tr da c
--       in db : comp c' das

class Incr e where
  liftI :: Diff a => (a -> b) -> (a -> Delta a -> Delta b) -> e a -> e b
  shareI :: e a -> (e a -> e b) -> e b

  pairI :: e a -> e b -> e (a, b)

data Index f as where
  IndexZ :: f a -> Index f (a ': as)
  IndexS :: Index f as -> Index f (b ': as)


newtype PackedAtomicDelta f a = PackedAtomicDelta { getAtomicDelta :: AtomicDelta (f a) }

-- type instance Delta (Env f as) = Env (PackedDelta f) as
newtype instance AtomicDelta (Env f as) = AtomicDeltaEnv (Index (PackedAtomicDelta f) as)


tailIF :: IF (Env Identity (a : as)) (Env Identity as)
tailIF = IF (\(ECons _ r) -> (r, ()))
--            (iterTr $ \(ECons _ dr) _ -> (dr, ()))
            (iterTr $ \(AtomicDeltaEnv x) _ ->
              case x of
                IndexZ _  -> (mempty, ())
                IndexS am -> (pure (AtomicDeltaEnv am), ()))

headIF :: IF (Env Identity (a : as)) a
headIF = IF (\(ECons a _) -> (coerce a, ()))
--            (iterTr $ \(ECons da _) _ -> (coerce da, ()))
            (iterTr $ \(AtomicDeltaEnv x) _ -> case x of
              IndexZ da -> (pure $ runADIdentity $ getAtomicDelta da , ())
              IndexS _  -> (mempty, ()))


newtype UnembIncr b = UnembIncr { runUnembIncr :: forall as. Env Proxy as -> IF (Env Identity as) b  }

instance Incr UnembIncr where
  liftI f df (UnembIncr x) = UnembIncr (\tenv -> toIF f df . x tenv)

  shareI (UnembIncr e0) k = UnembIncr $ \tenv ->
    let tenv1 = ECons Proxy tenv
        arg   = UnembIncr $ \tenv' -> diff tenv1 tenv' headIF
    in runUnembIncr (k arg) tenv1. toEnv . prodIF (e0 tenv) id
    where
      diff :: Env Proxy as -> Env Proxy bs -> IF (Env Identity as) a -> IF (Env Identity bs) a
      diff tenv1 tenv2 = diff' (lenEnv tenv2 - lenEnv tenv1) tenv1 tenv2
        where
          diff' :: Int -> Env Proxy xs -> Env Proxy ys -> IF (Env Identity xs) a -> IF (Env Identity ys) a
          diff' 0 _ _ x             = Unsafe.unsafeCoerce x
          diff' n γ1 (ECons _ γ2) x = diff' (n-1) γ1 γ2 x . tailIF
          diff' _ _ _ _             = error "Unreachable"


      toEnv :: IF (a, Env Identity as) (Env Identity (a ': as))
      toEnv = IF (\(a, as) -> (ECons (Identity a) as, ()))
                 -- (\(da, das) _ -> (ECons (PackedDelta da) das, ()))
                 (iterTr $ \x _ -> case x of
                   ADFst da  -> (pure $ AtomicDeltaEnv $ IndexZ (PackedAtomicDelta $ ADIdentity da), ())
                   ADSnd das -> (pure $ AtomicDeltaEnv $ IndexS $ coerce das, ()))

  pairI (UnembIncr x) (UnembIncr y) = UnembIncr $ \tenv -> prodIF (x tenv) (y tenv)

runIncrMono :: (UnembIncr a -> UnembIncr b) -> IF a b
runIncrMono f = runUnembIncr (shareI (UnembIncr $ \(ECons Proxy _) -> Unsafe.unsafeCoerce headIF) f) (ECons Proxy ENil) . singleton
  where
    singleton :: IF a (Env Identity '[a])
    singleton = IF (\a -> (ECons (Identity a) ENil, ()))
--                   (\da _ -> (ECons (PackedDelta da) ENil, ()))
                   (iterTr $ \da _ -> (pure $ AtomicDeltaEnv $ IndexZ $ coerce da, ()))



-- >>> let (res, tr) = runIF (runIncrMono aveD) (Bag [1..100])
-- >>> res
-- >>> let dbs = tr [Bag [1], Bag [2], Bag [30]]
-- >>> dbs
-- >>> res /+ mconcat dbs
-- Variable not in scope: runIF :: IF a0 b0 -> t0 -> (a, b)
-- Variable not in scope: aveD :: UnembIncr a0 -> UnembIncr b0
-- Data constructor not in scope: Bag :: [a1] -> t0

--- >>> (100000 + sum [1..100]) / 101
-- 1040.09900990099
