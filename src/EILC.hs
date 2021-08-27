{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module EILC where

import           Data.Coerce           (coerce)
import           Data.Functor.Identity
import           Data.Typeable         (Proxy (..))
import           Prelude               hiding (id, (.))

import qualified Language.Haskell.TH   as TH

import           Control.Applicative   (Alternative (..))
import           Data.Env
import           Data.Kind             (Type)
import           Language.Unembedding
import qualified Text.Show


-- We want to define a class with
--
--     injMonoid :: a -> m a
--     monoidMap :: Monoid n => (a -> n) -> m a -> n
--     m a is always a monoid
--
-- Then, m must be Applicative as
--
-- f <*> x = monoidMap f $ \f' -> monoidMap x $ \x' -> injMonoid (f' a')

class (Applicative m, Alternative m, Foldable m) => MonoidF m

injMonoid :: MonoidF m => a -> m a
injMonoid = pure -- compatibility

monoidMap :: (MonoidF m, Monoid n) => (a -> n) -> m a -> n
monoidMap = foldMap

monoidFromList :: MonoidF m => [a] -> m a
monoidFromList = foldr ((<|>) . injMonoid) empty

-- mmap :: (MonoidF a m, MonoidF b n) => (a -> b) -> m -> n
-- mmap f = monoidMap (injMonoid . f)

instance MonoidF []

newtype FreeMonoidF a =
    FreeMonoidF { foldFreeMonoidF :: forall n. Monoid n => (a -> n) -> n }

instance Show a => Show (FreeMonoidF a) where
  showsPrec k xs = showParen (k > 9) s
    where
      s = Text.Show.showString "monoidFromList" . showChar ' ' . shows (foldFreeMonoidF xs $ \x -> [x])


instance Functor FreeMonoidF where
  fmap f xs = FreeMonoidF $ \h -> foldFreeMonoidF xs (h . f)
  {-# INLINE fmap #-}

instance Semigroup (FreeMonoidF a) where
  xs <> ys = FreeMonoidF $ \h -> foldFreeMonoidF xs h <> foldFreeMonoidF ys h

instance Monoid (FreeMonoidF a) where
  mempty = FreeMonoidF $ const mempty

instance Applicative FreeMonoidF where
  pure a = FreeMonoidF $ \h -> h a
  f <*> x = foldFreeMonoidF f $ \f' -> foldFreeMonoidF x $ \x' -> pure (f' x')

instance Alternative FreeMonoidF where
  empty = mempty
  (<|>) = (<>)

instance Foldable FreeMonoidF where
  foldMap h as = foldFreeMonoidF as h
  {-# INLINE foldMap #-}

instance MonoidF FreeMonoidF

-- FIXME: use Hughes lists or something similar
-- type Delta a = [AtomicDelta a]
type Delta a = FreeMonoidF (AtomicDelta a)

-- Non-injectivity is usually a source of a trouble.
data family AtomicDelta (a :: Type) :: Type

newtype instance AtomicDelta (Identity a) = DIdentity a
data instance AtomicDelta ()
data instance AtomicDelta (a, b) = ADFst (AtomicDelta a) | ADSnd (AtomicDelta b)

deriving instance (Show (AtomicDelta a), Show (AtomicDelta b)) => Show (AtomicDelta (a, b))

fstDelta :: Delta (a, b) -> Delta a
fstDelta = foldMap fstDeltaA

fstDeltaA :: AtomicDelta (a, b) -> Delta a
fstDeltaA (ADFst da) = injMonoid da
fstDeltaA _          = mempty

sndDelta :: Delta (a, b) -> Delta b
sndDelta = foldMap sndDeltaA

sndDeltaA :: AtomicDelta (a, b) -> Delta b
sndDeltaA (ADSnd db) = injMonoid db
sndDeltaA _          = mempty

pairDelta :: Delta a -> Delta b -> Delta (a, b)
pairDelta xs ys = fmap ADFst xs <> fmap ADSnd ys

class Diff a where
  applyAtomicDelta :: a -> AtomicDelta a -> a

  -- | Applying delta.
  -- prop> a /+ da /+ da' = a /+ (da <> da')
  (/+) :: a -> Delta a -> a
  a /+ das =
    -- appEndo (getDual (monoidMap (\da -> Dual $ Endo $ \a -> applyAtomicDelta a da) das)) a
    foldl applyAtomicDelta a das

instance Diff () where
  applyAtomicDelta () _ = ()

instance (Diff a, Diff b) => Diff (a, b) where
  -- (a, b) /+ (da, db) = (a /+ da, b /+ db)
  applyAtomicDelta (a, b) (ADFst da) = (applyAtomicDelta a da, b)
  applyAtomicDelta (a, b) (ADSnd db) = (a, applyAtomicDelta b db)

-- State-Writer, both are composed left-to-right
newtype StateWriterLL s w = StateWriterLL { unStateWriterLL :: s -> (w, s) }

instance Semigroup w => Semigroup (StateWriterLL s w) where
  f <> g = StateWriterLL $ \s ->
    let (m1, s1) = unStateWriterLL f s
        (m2, s2) = unStateWriterLL g s1
    in (m1 <> m2, s2)

instance Monoid w => Monoid (StateWriterLL s w) where
  mempty = StateWriterLL $ \s -> (mempty , s)

-- | Incremtalized function
--
-- prop> let (b, tr) = runIF f a in f (foldl (/+) a das) == foldl (/+) b (tr das)
-- Or, equivalently
-- prop> let (b, tr) = runIF f a in f (a /+ mconcat das) == b /+ mconcat das
data IF a b = forall c. IF !(a -> (b, c)) !(AtomicDelta a -> c -> (Delta b, c))

-- simplarly to IF but a is applied partially beforehand
data IV a b = forall c. IV !(b, c) !(AtomicDelta a -> c -> (Delta b, c))

iterTrStateless :: (AtomicDelta a -> Delta b) -> (Delta a -> Delta b)
iterTrStateless = foldMap

iterTr :: (AtomicDelta a -> c -> (Delta b, c)) -> (Delta a -> c -> (Delta b, c))
iterTr f = unStateWriterLL . monoidMap (StateWriterLL . f)
-- iterTr f [] c = ([], c)
-- iterTr f (da : das) c =
--   let (db,  c1) = f da c
--       (res, c2) = iterTr f das c1
--   in (db <> res, c2)

instance CategoryK IF where
  id = IF (\a -> (a, ())) (\da c -> (injMonoid da , c))

  IF f2 tr2 . IF f1 tr1 = IF f tr
    where
      f a = let (b, c1) = f1 a
                (c, c2) = f2 b
            in (c, (c1, c2))

      tr da (c1 , c2) =
        let (dbs , c1') = tr1 da c1
            (dc , c2')  = iterTr tr2 dbs c2
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

toIF :: Diff a => (a -> b) -> (a -> AtomicDelta a -> Delta b) -> IF a b
toIF f df = IF (\a -> (f a, a)) (\da a -> (df a da, applyAtomicDelta a da))

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

data DEnv f as where
  DENil :: DEnv f '[]
  DECons :: Delta (f a) -> DEnv f as -> DEnv f (a ': as)

-- newtype PackedDelta f a = PackedDelta { getDelta :: Delta (f a) }

newtype PackedAtomicDelta f a = PackedAtomicDelta { getAtomicDelta :: AtomicDelta (f a) }

-- type instance Delta (Env f as) = Env (PackedDelta f) as
newtype instance AtomicDelta (Env f as) = AtomicDeltaEnv (Index (PackedAtomicDelta f) as)


-- tailIF :: IF (Env Identity (a : as)) (Env Identity as)
-- tailIF = IF (\(ECons _ r) -> (r, ()))
--             (\(ECons _ dr) _ -> (dr, ()))

-- headIF :: IF (Env Identity (a : as)) a
-- headIF = IF (\(ECons a _) -> (coerce a, ()))
--             (\(ECons da _) _ -> (coerce da, ()))


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
--                  (\(da, das) _ -> (ECons (PackedDelta da) das, ()))

--   pairI (UnembIncr x) (UnembIncr y) = UnembIncr $ \tenv -> prodIF (x tenv) (y tenv)

-- runIncrMono :: (UnembIncr a -> UnembIncr b) -> IF a b
-- runIncrMono f = runUnembIncr (shareI (UnembIncr $ \(ECons Proxy _) -> Unsafe.unsafeCoerce headIF) f) (ECons Proxy ENil) . singleton
--   where
--     singleton :: IF a (Env Identity '[a])
--     singleton = IF (\a -> (ECons (Identity a) ENil, ()))
--                    (\da _ -> (ECons (PackedDelta da) ENil, ()))



-- >>> let (res, tr) = runIF (runIncrMono aveD) (Bag [1..100])
-- >>> res
-- >>> let dbs = tr [Bag [1], Bag [2], Bag [30]]
-- >>> dbs
-- >>> res /+ mconcat dbs
-- 50.5
-- [Sum {getSum = -0.4900990099009874},Sum {getSum = -0.4706853038245029},Sum {getSum = -0.18970112316771548}]
-- 49.349514563106794

--- >>> (100000 + sum [1..100]) / 101
-- 1040.09900990099

{-
There are a few obvious sources of overhead.

  - Abstraction overhead: handling of contexts, and handling of type environments
  - Overhead due to handling of "C"; in the above example, C is mostly () except divD
  - It does not handle the special case: da = mempty (where db must also be mempty)

Everything is orthogonal. A possible solution for each issue is:

  - To use metaprogramming to compute such overhead away
  - To use the join list that has the canonical empty representation for c
  - To handle Maybe (Delta a) instead of Delta a

Since the third one is rather easy, here we focus on the former two.

To overcome the second one, we use the following type instead.
-}

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

data IFt a b = forall cs. IFt (IsNone cs) (a -> (b, Conn Identity cs)) (AtomicDelta a -> Conn Identity cs -> (Delta b, Conn Identity cs))

instance CategoryK IFt where
  id = IFt IsNoneTrue (\a -> (a, CNone)) (\da c -> (injMonoid da, c))

  IFt isNone2 f2 tr2 . IFt isNone1 f1 tr1 = IFt (isNoneAnd isNone1 isNone2) f tr
    where
      f a = let (b, c1) = f1 a
                (c, c2) = f2 b
            in ( c, joinConn c1 c2 )

      tr da cc = case decompConn isNone1 isNone2 cc of
        (c1, c2) -> let (db, c1') = tr1 da c1
                        (dc, c2') = iterTr tr2 db c2
                    in (dc, joinConn c1' c2')

unitIFt :: IFt s ()
unitIFt = IFt IsNoneTrue (const ((), CNone)) (\_ _ -> (mempty, CNone))

multIFt :: IFt s a -> IFt s b -> IFt s (a, b)
multIFt (IFt isNone1 f1 tr1) (IFt isNone2 f2 tr2) = IFt (isNoneAnd isNone1 isNone2) f tr
  where
    f s = ( (a, b), joinConn c1 c2)
      where
        (a, c1) = f1 s
        (b, c2) = f2 s

    tr ds cc | (c1, c2) <- decompConn isNone1 isNone2 cc =
      let
        (da, c1') = tr1 ds c1
        (db, c2') = tr2 ds c2
      in ( pairDelta da db, joinConn c1' c2' )


-- Then, we focus on the first:
--
--  - Abstraction overhead: handling of contexts, and handling of type environments

-- First, we prepare Code type

type Code a = TH.Q (TH.TExp a)

{-
Then, let us focus on `IFt`. Here, we want to remove the cost of function compsotions.
Naively, we can think about the following datatype.

   data IFq a b = forall cs. IFt (IsNone cs) (Code a -> (Code b, Conn Code cs)) (Code (Delta a) -> Conn Code cs -> (Code (Delta b), Conn Code cs))

(Here, we ignore for simplicity that Code must be fully-applied.)

This is OK, but has a problem that we cannot share the computation between two `Code`.

A common workaround is to use a continuation monad, of which continuation intuitively represents a common context.
-}

newtype CodeC a = CodeC { runCodeC :: forall r. (a -> Code r) -> Code r }

toCode :: CodeC (Code a) -> Code a
toCode (CodeC m) = m id

instance Functor CodeC where
  fmap f (CodeC m) = CodeC $ \k -> m (k . f)

instance Applicative CodeC where
  pure a = CodeC $ \k -> k a
  CodeC f <*> CodeC a = CodeC $ \k -> a $ \a' -> f $ \f' -> k (f' a')

instance Monad CodeC where
  return = pure
  m >>= f = CodeC $ \k -> runCodeC m $ \a -> runCodeC (f a) k

data CEnv as where
  CENil :: CEnv '[]
  CECons :: Code a -> CEnv as -> CEnv (a ': as)


mkLet :: Code a -> CodeC (Code a)
mkLet e = CodeC $ \k ->
  [|| let v = $$( e ) in $$(k [|| v ||]) ||]

newtype PackedCode a = PackedCode { getCode :: Code a }

mkLetConn :: Conn PackedCode cs -> CodeC (Conn PackedCode cs)
mkLetConn CNone = return CNone
mkLetConn (CNE e) = CNE <$> mkLetConn' e
  where
    mkLetConn' :: NEConn PackedCode cs -> CodeC (NEConn PackedCode cs)
    mkLetConn' (COne a)      = COne . PackedCode <$> mkLet (coerce a)
    mkLetConn' (CJoin c1 c2) = CJoin <$> mkLetConn' c1 <*> mkLetConn' c2


isNone :: Conn Proxy cs -> IsNone cs
isNone CNone   = IsNoneTrue
isNone (CNE _) = IsNoneFalse






-- data IFq a b =
--   forall cs.
--     IFq (Conn Proxy cs)
--         (Code a -> CodeC (Code b, Conn PackedCode cs))
--         (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

data IFq a b where
  IFq :: Conn Proxy cs -> (Code a -> CodeC (Code b, Conn PackedCode cs)) -> (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs)) -> IFq a b



instance CategoryK IFq where
  type K IFq = Diff
  id = IFq CNone (\a -> return (a, CNone))
                 (\da _ -> return (da , CNone))

  IFq sh2 f2 tr2 . IFq sh1 f1 tr1 = IFq (joinConn sh1 sh2) f tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (dbs, c1') <- tr1 da c1
        (dcs, c2') <- tr2 dbs c2
        return (dcs, joinConn c1' c2')

ifqFromStateless :: (Code a -> Code b) -> (Code (Delta a) -> Code (Delta b)) -> IFq a b
ifqFromStateless f df = IFq CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df da) ; return (v, CNone) })

ifqFromD :: Diff a => (Code a -> Code b) -> (Code a -> Code (Delta a) -> Code (Delta b)) -> IFq a b
ifqFromD f df = IFq (CNE (COne Proxy))
                    (\a -> do { v <- mkLet (f a) ; return (v, CNE (COne (PackedCode a))) })
                    (\da (CNE (COne (PackedCode a))) -> do { v <- mkLet (df a da) ; a' <- mkLet [|| $$a /+ $$da ||] ; return (v, CNE (COne (PackedCode a'))) })

ifqFromFunctions :: Code (a -> (b, c)) -> Code (Delta a -> c -> (Delta b, c)) -> IFq a b
ifqFromFunctions f df =
  IFq (CNE (COne Proxy))
      (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
      (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
        [|| let (db, c') = $$df $$da $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])


multIFq :: IFq s a -> IFq s b -> IFq s (a, b)
multIFq (IFq sh1 f1 tr1) (IFq sh2 f2 tr2) = IFq (joinConn sh1 sh2) f tr
  where
    f s = do
      (a, c1) <- f1 s
      (b, c2) <- f2 s
      r <- mkLet [|| ($$a, $$b) ||]
      return (r , joinConn c1 c2)

    tr ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
      (da, c1') <- tr1 ds c1
      (db, c2') <- tr2 ds c2
      r <- mkLet [|| pairDelta $$da $$db ||]
      return ( r, joinConn c1' c2' )


newtype Interaction a b = Interaction { runInteraction :: a -> (b, Interaction a b) }

iterations :: Interaction a b -> [a] -> [b]
iterations _ []       = []
iterations i (a : as) =
  let (b, i') = runInteraction i a
  in b : iterations i' as


unCNE :: Conn f ('NE cs) -> NEConn f cs
unCNE (CNE cs) = cs

unCOne :: NEConn f ('NEOne c) -> f c
unCOne (COne c) = c

unCJoin :: NEConn f ('NEJoin c1 c2) -> (NEConn f c1, NEConn f c2)
unCJoin (CJoin c1 c2) = (c1, c2)

-- dumpIFq :: IFq a b -> IO ()
-- dumpIFq (IFq IsNoneTrue f tr) = do
--   putStrLn "IsNone: True"
--   e <- TH.runQ [|| \x -> $$(runCodeC (f [|| x ||]) fst ) ||]
--   putStrLn "=== f ==="
--   putStrLn $ TH.pprint $ TH.unType e
--   de <- TH.runQ [|| \x -> $$(runCodeC (tr [|| x ||] CNone) fst) ||]
--   putStrLn "=== df ==="
--   putStrLn $ TH.pprint $ TH.unType de
-- dumpIFq (IFq IsNoneFalse f _) = do
--   putStrLn "IsNone: False"
--   putStrLn "=== <f, c> ==="
--   e <- TH.runQ [|| \x -> $$( runCodeC (f [|| x ||]) $ \(y, c) -> [|| ($$y , $$(conn2code c)) ||]) ||]
--   putStrLn $ TH.pprint $ TH.unType e
--   putStrLn "printing df is not implemented"

conn2code :: Conn PackedCode cs -> Code (Conn Identity cs)
conn2code CNone   = [|| CNone ||]
conn2code (CNE c) = [|| CNE $$(conn2code' c) ||]

conn2code' :: NEConn PackedCode cs -> Code (NEConn Identity cs)
conn2code' (COne (PackedCode c)) = [|| COne (Identity $$c) ||]
conn2code' (CJoin c1 c2)         = [|| CJoin $$(conn2code' c1) $$(conn2code' c2) ||]


code2conn :: forall cs r. Conn Proxy cs -> Code (Conn Identity cs) -> (Conn PackedCode cs -> Code r) -> Code r
code2conn CNone      c k = [|| let _ = $$c in $$(k CNone) ||]
code2conn (CNE pcne) c k = code2conn' pcne [|| unCNE $$c ||] (k . CNE)

code2conn' :: forall cs' r. NEConn Proxy cs' -> Code (NEConn Identity cs') -> (NEConn PackedCode cs' -> Code r) -> Code r
code2conn' (COne _) c k = k (COne $ PackedCode [|| runIdentity (unCOne $$c) ||])
code2conn' (CJoin pc1 pc2) c k =
  [|| let (c1, c2) = unCJoin $$c
      in $$(code2conn' pc1 [|| c1 ||] $ \c1' -> code2conn' pc2 [|| c2 ||] $ \c2' -> k (CJoin c1' c2')) ||]

ensureDiffType :: (Proxy a -> Proxy b -> a -> (b, Interaction (Delta a) (Delta b))) -> (a -> (b, Interaction (Delta a) (Delta b)))
ensureDiffType f = f Proxy Proxy

mkInteraction :: Proxy a -> Proxy b -> (Delta a -> (Delta b, Interaction (Delta a) (Delta b))) -> Interaction (Delta a) (Delta b)
mkInteraction _ _ = Interaction

eqProxy :: Proxy a -> Proxy a -> b -> b
eqProxy _ _ x = x

{-
Rethinking `mkRTr`.

     mkRTr :: forall cs.
               Code (Proxy a) -> Code (Proxy b)
               -> (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
               -> Conn PackedCode cs
               -> Code (Interaction (Delta a) (Delta b))

The goal is we want to make a function

    let
      ff = mkAbs pc $ \cs -> Interaction $ \a ->
              $$(tr [|| a ||] (toConn c1 .. cn) $ \(db, cs') -> [|| ($$db, $$(mkApp [|| ff ||] cs') ||] )
    in $$(mkApp [|| ff ||] cs)

So, our goal is to write a function mkApp and mkAbs.

    mkAbs :: Conn Proxy cs -> (Conn PackedCode cs -> Code a) -> (Code (Func cs a))
    mkApp :: Code (Func cs a) -> Conn PackedCode cs -> Code a

First, let me think of Func cs a.

   Func None a = a
   Func (NE cne) a = Func' cne a

   Func (One c) a       = c -> a
   Func (CJoin c1 c2) a = Func c1 (Func c2 a)

-}

type family Func (cs :: Tree Type) (a :: Type) :: Type where
  Func 'None a    = a
  Func ('NE ne) a = Func' ne a

type family Func' (cs :: NETree Type) (a :: Type ) :: Type where
  Func' ('NEOne c) a      = c -> a
  Func' ('NEJoin c1 c2) a = Func' c1 (Func' c2 a)


mkAbs :: forall cs a. Conn Proxy cs -> (Conn PackedCode cs -> Code a) -> Code (Func cs a)
mkAbs CNone k    = k CNone
mkAbs (CNE cs) k = mkAbs' cs (k . CNE)

mkAbs' :: NEConn Proxy cs -> (NEConn PackedCode cs -> Code a) -> Code (Func' cs a)
mkAbs' (COne _) k      = [|| \a -> $$(k (COne $ PackedCode [|| a ||])) ||]
mkAbs' (CJoin c1 c2) k = mkAbs' c1 $ \c1' -> mkAbs' c2 $ \c2' -> k (CJoin c1' c2')

mkApp :: forall cs a. Code (Func cs a) -> Conn PackedCode cs -> Code a
mkApp f CNone    = f
mkApp f (CNE cs) = mkApp' f cs

mkApp' :: Code (Func' cs a) -> NEConn PackedCode cs -> Code a
mkApp' f (COne (PackedCode a)) = [|| $$f $$a ||]
mkApp' f (CJoin c1 c2)         = mkApp' (mkApp' f c1) c2

type family Flatten cs where
  Flatten 'None   = '[]
  Flatten ('NE x) = Flatten' x '[]

type family Flatten' cs r where
  Flatten' ('NEOne c) r = c ': r
  Flatten' ('NEJoin cs1 cs2) r = Flatten' cs1 (Flatten' cs2 r)

conn2cenv :: Conn PackedCode cs -> Code (Env Identity (Flatten cs))
conn2cenv CNone    = [|| ENil ||]
conn2cenv (CNE cs) = conn2cenv' cs [|| ENil ||]

conn2cenv' :: NEConn PackedCode cs -> Code (Env Identity rs) -> Code (Env Identity (Flatten' cs rs))
conn2cenv' (COne (PackedCode c)) r = [|| ECons (Identity $$c) $$r ||]
conn2cenv' (CJoin c1 c2) r         = conn2cenv' c1 (conn2cenv' c2 r)

cenv2conn :: forall cs r. Conn Proxy cs -> Code (Env Identity (Flatten cs)) -> (Conn PackedCode cs -> Code r) -> Code r
cenv2conn CNone  env k = [|| case $$env of { ENil -> $$(k CNone) } ||]
cenv2conn (CNE (p :: NEConn Proxy cs')) env k = cenv2conn' @cs' @'[] @r p env $ \c env' ->
  [|| case $$env' of { ENil -> $$(k (CNE c)) } ||]

cenv2conn' :: forall cs ds r. NEConn Proxy cs -> Code (Env Identity (Flatten' cs ds)) -> (NEConn PackedCode cs -> Code (Env Identity ds) -> Code r) -> Code r
cenv2conn' (COne _) env k =
  [||
    let x = headEnv $$env
        xs = tailEnv $$env
    in $$( k (COne (PackedCode [|| runIdentity x ||])) [|| xs ||] )
  ||]
cenv2conn' (CJoin p1 p2) env k =
  cenv2conn' p1 env $ \c1 env' -> cenv2conn' p2 env' $ \c2 env'' -> k (CJoin c1 c2) env''



runIFq :: forall a b. IFq a b -> Code (a -> (b, Interaction (Delta a) (Delta b) ))
runIFq = \case (IFq _ f tr) ->
                 [|| ensureDiffType $ \pa pb a ->
                         $$(toCode $ do (b, c) <- f [|| a ||]
                                        let rtr = mkRTr [|| pa ||] [|| pb ||] tr c
                                        return [|| ($$b, $$rtr) ||])
                  ||]
  where
    mkRTr :: forall cs. Code (Proxy a) -> Code (Proxy b) -> (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs)) -> Conn PackedCode cs -> Code (Interaction (Delta a) (Delta b))
    mkRTr pa pb tr c =
      [||
         let func = $$(mkAbs pc $ \cs ->
                        [|| mkInteraction $$pa $$pb $ \da ->
                               $$( runCodeC (tr [|| da ||] cs) $ \(db, cs') -> [|| ($$db, $$( mkApp [|| func ||] cs' )) ||] )
                        ||])
         in $$( mkApp [|| func ||] c )
      ||]
      -- [|| let func cp = mkInteraction $$pa $$pb $ \da ->
      --                       $$(code2conn pc [|| cp ||] $ \cs ->
      --                           runCodeC (tr [|| da ||] cs) $ \(db, cs') -> [|| ($$db, func $$(conn2code cs')) ||])
      --     in func $$(conn2code c) ||]
      where
        pc = map2Conn (const Proxy) c


{-
This construction seems to work, and is expected also to address the issue of the overhead due to unembedding, as
computations caused by unembedding happens in the first stage (or, meta level or host level).
-}

{-
Let us see its effect by actual unembedding. Here, since we do not want to
prepare unembedded types for each C, we will prepare one type that works for all.
-}

-- newtype Sem cat b = Sem { runSem :: forall as. Env Proxy as -> cat (Env Identity as) b }

--   -- Having `share` here is too specific.
--   -- share :: e a -> (e a -> e b) -> e b


-- class Category cat => AppS cat where
--   multS :: cat s a -> cat s b -> cat s (a, b)
--   unitS :: cat s ()

--   headS :: cat (Env Identity (a ': as)) a
--   tailS :: cat (Env Identity (a ': as)) (Env Identity as)

--   singletonS :: cat a (Env Identity '[a])

--   econsS :: cat (a , Env Identity as) (Env Identity (a ': as))

instance Cartesian IFq where
  multS = multIFq
  unitS = IFq CNone (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| mempty ||], CNone))

  fstS _ _ = IFq CNone
                (\as    -> do { v <- mkLet [|| fst $$as  ||] ; return (v, CNone)})
                (\das _ -> do { v <- mkLet [|| fstDelta $$das ||] ; return (v, CNone) })
--                (\das _ -> do { vda <- mkLet [|| fst $$das ||]; return (vda, CNone) } )

  sndS _ _ = IFq CNone
                (\as    -> do { v <- mkLet [|| snd $$as ||] ; return (v, CNone)})
                (\das _ -> do { v <- mkLet [|| sndDelta $$das ||] ; return (v, CNone) })
--                (\das _ -> do { vda <- mkLet [|| snd $$das ||]; return (vda, CNone) } )

-- instance AppS IFq where
--   multS = multIFq
--   unitS = IFq IsNoneTrue (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| () ||], CNone))

--   headS = IFq IsNoneTrue
--               (\as    -> do { v <- mkLet [|| case $$as of { ECons (Identity a) _ -> a } ||] ; return (v, CNone)})
--               (\das _ -> do { vda <- mkLet [|| case $$das of { ECons (PackedDelta da) _ -> da } ||]; return (vda, CNone) } )

--   tailS = IFq IsNoneTrue
--               (\as    -> do { v <- mkLet [|| case $$as of { ECons _ as' -> as' } ||] ; return (v, CNone)})
--               (\das _ -> do { v <- mkLet [|| case $$das of { ECons _ das' -> das' } ||]; return (v, CNone) } )

--   singletonS = IFq IsNoneTrue
--                    (\a  -> do { v <- mkLet [|| ECons (Identity $$a) ENil ||] ; return (v, CNone) })
--                    (\da _ -> do { v <- mkLet [|| ECons (PackedDelta $$da) ENil ||] ; return (v, CNone) })

--   econsS = IFq IsNoneTrue econs decons
--     where
--       econs x = do { v <- mkLet [|| case $$x of { (a, as) -> ECons (Identity a) as } ||]; return (v, CNone) }
--       decons x _ = do { v <- mkLet [|| case $$x of { (da, das) -> ECons (PackedDelta da) das } ||]; return (v, CNone) }

-- instance AppS cat => App cat (Sem cat) where
--   lift x (Sem e) = Sem $ \tenv -> x . e tenv

--   unit = Sem $ const unitS
--   pair (Sem e1) (Sem e2) = Sem $ \tenv -> multS (e1 tenv) (e2 tenv)

--   -- share (Sem e0) k = Sem $ \tenv ->
--   --   let tenva = ECons Proxy tenv
--   --       arg = Sem $ \tenv' -> diffS tenva tenv' headS
--   --   in runSem (k arg) tenva . econsS . multS (e0 tenv) id

-- diffS :: AppS cat => Env Proxy as -> Env Proxy bs -> cat (Env Identity as) a -> cat (Env Identity bs) a
-- diffS tenv1 tenv2 | trace (printf "Diff: #tenv1 = %d and #tenv2 = %d" (lenEnv tenv1) (lenEnv tenv2)) False = undefined
-- diffS tenv1 tenv2 =
--   diff' (lenEnv tenv2 - lenEnv tenv1) tenv1 tenv2
--   where
--     diff' :: AppS cat => Int -> Env Proxy xs -> Env Proxy ys -> cat (Env Identity xs) a -> cat (Env Identity ys) a
--     diff' 0 _ _ x             = Unsafe.unsafeCoerce x
--     diff' n γ1 (ECons _ γ2) x = diff' (n-1) γ1 γ2 x . tailS
--     diff' _ _ _ _             = error "Unreachable"

-- runAppMono :: AppS cat => (Sem cat a -> Sem cat b) -> cat a b
-- runAppMono f = runSem (f $ Sem $ \tenv -> diffS tenv1 tenv headS) tenv1 . singletonS
--   where
--     tenv1 = ECons Proxy ENil


-- runAppMono :: Cartesian cat => (TSem (TermFromCat cat) a -> TSem (TermFromCat cat) b) -> cat a b
-- runAppMono = runMono

dumpCode :: Code a -> IO ()
dumpCode c = do
  e <- TH.runQ c
  putStrLn $ TH.pprint (TH.unType e)


{-

The following is the generated code for `runIFq (runAppMono ave)`

(ensureDiffType
       $ (\ pa_anpS pb_anpT a_anpU
            -> let v_anpV = (a_anpU, ()) in
               let v_anpW = case v_anpV of { (a_anpX, _) -> a_anpX } in
               let v_anpY = case v_anpW of { Bag as_anpZ -> sum as_anpZ } in
               let v_anq0 = case v_anpV of { (a_anq1, _) -> a_anq1 } in
               let v_anq2 = case v_anq0 of { Bag as_anq3 -> length as_anq3 } in
               let v_anq4 = fromIntegral v_anq2 :: Double in
               let v_anq5 = (v_anpY, v_anq4) in
               let v_anq6 = (uncurry (/)) v_anq5
               in
                 (v_anq6,
                  let
                    func_anq7
                      = \ a_anq8
                          -> ((mkInteraction pa_anpS) pb_anpT
                                $ (\ da_anq9
                                     -> let v_anqa = (da_anq9, ()) in
                                        let v_anqb = case v_anqa of { (da_anqc, _) -> da_anqc } in
                                        let
                                          v_anqd
                                            = case v_anqb of {
                                                Bag as'_anqe -> Sum (sum as'_anqe) } in
                                        let v_anqf = case v_anqa of { (da_anqg, _) -> da_anqg } in
                                        let
                                          v_anqh
                                            = case v_anqf of {
                                                Bag as_anqi -> Sum (length as_anqi) } in
                                        let v_anqj = Sum (fromIntegral (getSum v_anqh) :: Double) in
                                        let v_anqk = (v_anqd, v_anqj) in
                                        let
                                          v_anql
                                            = let
                                                (x_anqo, y_anqp) = a_anq8
                                                (dx_anqm, dy_anqn) = v_anqk
                                              in
                                                (Sum
                                                   $ (((x_anqo /+ dx_anqm) / (y_anqp /+ dy_anqn))
                                                        - (x_anqo / y_anqp))) in
                                        let v_anqq = (a_anq8 /+ v_anqk)
                                        in (v_anql, func_anq7 v_anqq)))
                  in func_anq7 v_anq5)))

Issue: the code involves redundant manipulations of products, such as:

      ...
               let v_anpV = (a_anpU, ()) in
               let v_anpW = case v_anpV of { (a_anpX, _) -> a_anpX } in
      ...

-}

{-

So, we need to focus on "fan-in"s, of which structure can be determined statically whereas their contents are not.

From the unembedding perspective, this would mean that we consider `mcat` instead of `cat`, where.

   mcat '[a] b ~ cat a b

We are expecting to have corresponding operations to `AppS`. For some operators they are
easily derived.

   multM :: mcat s a -> mcat s b -> mcat s (a, b)
   unitM :: mcat s ()

   headM :: mcat (a ': as) a

But, how about the corresponding operators to the below ones?

  tailS      :: cat (Env Identity (a ': as)) (Env Identity as)
  singletonS :: cat a (Env Identity '[a])
  econsS     :: cat (a , Env Identity as) (Env Identity (a ': as))

The use of tailS can only be found in `diffS` to implement weakening. So,
it's enough to add weakening operator:

  weakenM :: mcat as a -> mcat (b ': as) a

The use of singletonS is now clear. It converts `mcat` to `cat`.

  toSingleM :: mcat '[a] b -> cat a b

Similarly, we can give a combinator that can substitute for `econsS`.

  letM :: mcat s a -> mcat (a ': s) b -> mcat s b

TODO: how such ideas can be related to operad?

-}




runAppMono' :: (Term cat term, K cat a, K cat b) => (TSem cat term a -> TSem cat term b) -> cat a b
runAppMono' = runMono

-- newtype PackedCodeDelta a = PackedCodeDelta { getCodeDelta :: Code (Delta a) }
data PackedCodeDelta a where
  PackedCodeDelta :: Diff a => Code (Delta a) -> PackedCodeDelta a

data IFqT as b =
  forall cs. IFqT (Env Proxy as)
                  (Conn Proxy cs)
                  (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
                  (Env PackedCodeDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

instance HasProduct IFq where
  type Unit IFq = ()
  type Prod IFq a b = (a, b)

  unitOk _ = Wit
  prodOk _ _ _ = Wit


instance Term IFq IFqT where
  mapTerm (IFq sh2 f2 tr2) (IFqT tenv sh1 f1 tr1) = IFqT tenv (joinConn sh1 sh2) f tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (db, c1') <- tr1 da c1
        (dc, c2') <- tr2 db c2
        return (dc, joinConn c1' c2')

  multTerm (IFqT tenv sh1 f1 tr1) (IFqT _ sh2 f2 tr2) = IFqT tenv (joinConn sh1 sh2) f tr
    where
      f s = do
        (a, c1) <- f1 s
        (b, c2) <- f2 s
        r <- mkLet [|| ($$a, $$b) ||]
        return (r , joinConn c1 c2)

      tr ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (da, c1') <- tr1 ds c1
        (db, c2') <- tr2 ds c2
        r <- mkLet [|| pairDelta $$da $$db ||]
        return ( r, joinConn c1' c2' )

  unitTerm tenv = IFqT tenv CNone (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| mempty ||], CNone))

  var0Term tenv = IFqT (ECons Proxy tenv)
                       CNone
                       (\(ECons (PackedCode a) _) -> return (a, CNone))
                       (\(ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

  weakenTerm (IFqT tenv i f tr) = IFqT (ECons Proxy tenv) i f' tr'
    where
      f'  (ECons _ s) = f s
      tr' (ECons _ s) = tr s

  unliftTerm (IFqT _ i f tr) = IFq i f' tr'
    where
      f'  a  = f  (ECons (PackedCode       a) ENil)
      tr' da = tr (ECons (PackedCodeDelta da) ENil)

letTermIFqT :: Diff b1 => IFqT as b1 -> IFqT (b1 : as) b2 -> IFqT as b2
letTermIFqT (IFqT tenv sh1 f1 tr1) (IFqT _ sh2 f2 tr2) = IFqT tenv (joinConn sh1 sh2) f tr
  where
    f s = do
      (a, c1) <- f1 s
      v <- mkLet a
      (b, c2) <- f2 (ECons (PackedCode v) s)
      return (b, joinConn c1 c2)

    tr s cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
      (da, c1') <- tr1 s c1
      dv <- mkLet da
      (db, c2') <- tr2 (ECons (PackedCodeDelta dv) s) c2
      return (db, joinConn c1' c2')


-- To check generated code:
--    $ stack repl
--    > :set -XTemplateHaskell
--    > :set -ddump-splices
--    > let _ = $$( runIFq (runAppMono' FUNC) )


{-

Now, generated code for `ave` type checks.

    runIFq (runAppMono' ave)
  ======>
    (ensureDiffType
       $ (\ pa_a1o97 pb_a1o98 a_a1o99
            -> let
                 v_a1o9a = case a_a1o99 of { Bag as_a1o9b -> sum as_a1o9b } in
               let
                 v_a1o9c = case a_a1o99 of { Bag as_a1o9d -> length as_a1o9d } in
               let v_a1o9e = fromIntegral v_a1o9c :: Double in
               let v_a1o9f = (v_a1o9a, v_a1o9e) in
               let v_a1o9g = (uncurry (/)) v_a1o9f
               in
                 (v_a1o9g,
                  let
                    func_a1o9h cp_a1o9i
                      = ((mkInteraction pa_a1o97) pb_a1o98
                           $ (\ da_a1o9j
                                -> let
                                     v_a1o9k
                                       = case da_a1o9j of {
                                           Bag as'_a1o9l -> Sum (sum as'_a1o9l) } in
                                   let
                                     v_a1o9m
                                       = case da_a1o9j of {
                                           Bag as_a1o9n -> Sum (length as_a1o9n) } in
                                   let v_a1o9o = Sum (fromIntegral (getSum v_a1o9m) :: Double) in
                                   let v_a1o9p = (v_a1o9k, v_a1o9o) in
                                   let
                                     v_a1o9q
                                       = let
                                           (x_a1o9t, y_a1o9u)
                                             = runIdentity (unCOne (unCNE cp_a1o9i))
                                           (dx_a1o9r, dy_a1o9s) = v_a1o9p
                                         in
                                           (Sum
                                              $ (((x_a1o9t /+ dx_a1o9r) / (y_a1o9u /+ dy_a1o9s))
                                                   - (x_a1o9t / y_a1o9u))) in
                                   let v_a1o9v = (runIdentity (unCOne (unCNE cp_a1o9i)) /+ v_a1o9p)
                                   in (v_a1o9q, func_a1o9h (CNE (COne (Identity v_a1o9v))))))
                  in func_a1o9h (CNE (COne (Identity v_a1o9f))))))

2021-07-07: Now, it generates the following code.

    runIFq (runAppMono' ave)
  ======>
    (ensureDiffType
       $ (\ pa_a9yH pb_a9yI a_a9yJ
            -> let v_a9yK = case a_a9yJ of { Bag as_a9yL -> sum as_a9yL } in
               let v_a9yM = case a_a9yJ of { Bag as_a9yN -> length as_a9yN } in
               let v_a9yO = fromIntegral v_a9yM :: Double in
               let v_a9yP = (v_a9yK, v_a9yO) in
               let v_a9yQ = (uncurry (/)) v_a9yP
               in
                 (v_a9yQ,
                  let
                    func_a9yR
                      = \ a_a9yS
                          -> ((mkInteraction pa_a9yH) pb_a9yI
                                $ (\ da_a9yT
                                     -> let
                                          v_a9yU
                                            = case da_a9yT of {
                                                Bag as'_a9yV -> Sum (sum as'_a9yV) } in
                                        let
                                          v_a9yW
                                            = case da_a9yT of {
                                                Bag as_a9yX -> Sum (length as_a9yX) } in
                                        let v_a9yY = Sum (fromIntegral (getSum v_a9yW) :: Double) in
                                        let v_a9yZ = (v_a9yU, v_a9yY) in
                                        let
                                          v_a9z0
                                            = let
                                                (x_a9z3, y_a9z4) = a_a9yS
                                                (dx_a9z1, dy_a9z2) = v_a9yZ
                                              in
                                                (Sum
                                                   $ (((x_a9z3 /+ dx_a9z1) / (y_a9z4 /+ dy_a9z2))
                                                        - (x_a9z3 / y_a9z4))) in
                                        let v_a9z5 = (a_a9yS /+ v_a9yZ)
                                        in (v_a9z0, func_a9yR v_a9z5)))
                  in func_a9yR v_a9yP)))



-}

-- FIXME: tentative
share :: forall e r1 r2. (Diff r1, App2 IFq IFqT e) => e r1 -> (e r1 -> e r2) -> e r2
share = liftSO2 (Proxy @'[ '[], '[r1] ] ) letTermIFqT
  -- _ $ liftSO (packTermF letTermIFqT)
  -- liftSO (packTermF letTermIFqT) (ECons (Fun ENil (\ENil -> e)) (ECons (Fun (ECons Proxy ENil) (\(ECons x ENil) -> k x)) ENil))
  -- liftSO (\(ECons (TermF e1) (ECons (TermF e2) ENil)) -> letTermIFqT e1 e2) (ECons (Fun ENil (\ENil -> e)) (ECons (Fun (ECons Proxy ENil) (\(ECons x ENil) -> k x)) ENil))


data IFqA a b where
  IFqA ::
    Conn Proxy cs
    -> (Code a -> CodeC (Code b, Conn PackedCode cs))
    -> (Code (AtomicDelta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
    -> IFqA a b

-- Just to surpress type errors.
foldrDelta :: (AtomicDelta a -> b -> b) -> b -> Delta a -> b
foldrDelta = foldr
{-# INLINE foldrDelta #-}

iterTrC ::
  forall cs a b.
  Conn Proxy cs
  -> (Code (AtomicDelta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
  -> (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
iterTrC proxy h das0 cs0 = CodeC $ \(k :: (Code (Delta b), Conn PackedCode cs) -> Code r) ->
  [||
    -- f :: AtomicDelta a -> (Delta b -> Func cs r) -> Delta b -> Func cs r
    let f da cont = \acc -> $$(mkAbs proxy $ \cs ->
                runCodeC (h [|| da ||] cs) $ \(dbs1, cs') ->
                  mkApp @cs @r [|| cont (acc <> $$dbs1) ||] cs')
    in $$(mkApp [|| foldrDelta f (\acc -> $$(mkAbs proxy $ \cs -> k ([|| acc ||], cs))) $$das0  mempty ||] cs0)
   ||]

-- ifqAFromStateless :: (Code a -> Code b) -> (Code (Delta a) -> Code (Delta b)) -> IFqA a b
-- ifqAFromStateless f df =
--   IFqA CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df [|| injMonoid $$da ||]) ; return (v, CNone) })

-- ifqAFromD :: Diff a => (Code a -> Code b) -> (Code a -> Code (Delta a) -> Code (Delta b)) -> IFqA a b
-- ifqAFromD f df =
--   IFqA
--     (CNE (COne Proxy))
--     (\a -> do { v <- mkLet (f a) ; return (v, CNE (COne (PackedCode a))) })
--     (\da (CNE (COne (PackedCode a))) -> do { v <- mkLet (df a [|| injMonoid $$da ||]) ; a' <- mkLet [|| applyAtomicDelta $$a $$da ||] ; return (v, CNE (COne (PackedCode a'))) })

-- ifqAFromFunctions :: Code (a -> (b, c)) -> Code (Delta a -> c -> (Delta b, c)) -> IFqA a b
-- ifqAFromFunctions f df =
--   IFqA (CNE (COne Proxy))
--        (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
--        (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
--         [|| let (db, c') = $$df (injMonoid $$da) $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

ifqAFromStatelessA :: (Code a -> Code b) -> (Code (AtomicDelta a) -> Code (Delta b)) -> IFqA a b
ifqAFromStatelessA f df =
  IFqA CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df da) ; return (v, CNone) })

ifqFromStatelessA :: (Code a -> Code b) -> (Code (AtomicDelta a) -> Code (Delta b)) -> IFq a b
ifqFromStatelessA f df = ifqa2ifq $ ifqAFromStatelessA f df

ifqAFromAD :: Diff a => (Code a -> Code b) -> (Code a -> Code (AtomicDelta a) -> Code (Delta b)) -> IFqA a b
ifqAFromAD f df =
  IFqA
    (CNE (COne Proxy))
    (\a -> do { v <- mkLet (f a) ; return (v, CNE (COne (PackedCode a))) })
    (\da (CNE (COne (PackedCode a))) -> do { v <- mkLet (df a da) ; a' <- mkLet [|| applyAtomicDelta $$a $$da ||] ; return (v, CNE (COne (PackedCode a'))) })

ifqFromAD :: Diff a => (Code a -> Code b) -> (Code a -> Code (AtomicDelta a) -> Code (Delta b)) -> IFq a b
ifqFromAD f df = ifqa2ifq $ ifqAFromAD f df


ifqAFromFunctionsA :: Code (a -> (b, c)) -> Code (AtomicDelta a -> c -> (Delta b, c)) -> IFqA a b
ifqAFromFunctionsA f df =
  IFqA (CNE (COne Proxy))
       (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
       (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
        [|| let (db, c') = $$df $$da $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

ifqFromFunctionsA :: Code (a -> (b, c)) -> Code (AtomicDelta a -> c -> (Delta b, c)) -> IFq a b
ifqFromFunctionsA f df = ifqa2ifq $ ifqAFromFunctionsA f df


instance CategoryK IFqA where
  type K IFqA = Diff
  id = IFqA CNone (\a -> return (a, CNone)) (\da _ -> return ([|| injMonoid $$da ||], CNone))
  IFqA sh2 f2 tr2 . IFqA sh1 f1 tr1 = IFqA (joinConn sh1 sh2) f tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (dbs, c1') <- tr1 da c1
        (dcs, c2') <- iterTrC sh2 tr2 dbs c2
        return (dcs, joinConn c1' c2')



ifqa2ifq :: IFqA a b -> IFq a b
ifqa2ifq (IFqA sh f tr) = IFq sh f (iterTrC sh tr)




data IFqTE as b =
  forall cs. IFqTE (Env Proxy as)
                   (Conn Proxy cs)
                   (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
                   (Env PackedCode as -> Env PackedCodeDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

instance Term IFq IFqTE where
  mapTerm (IFq sh2 f2 tr2) (IFqTE tenv sh1 f1 tr1) = IFqTE tenv (joinConn sh1 sh2) f tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr a da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (db, c1') <- tr1 a da c1
        (dc, c2') <- tr2 db c2
        return (dc, joinConn c1' c2')

  multTerm (IFqTE tenv sh1 f1 tr1) (IFqTE _ sh2 f2 tr2) = IFqTE tenv (joinConn sh1 sh2) f tr
    where
      f s = do
        (a, c1) <- f1 s
        (b, c2) <- f2 s
        r <- mkLet [|| ($$a, $$b) ||]
        return (r , joinConn c1 c2)

      tr s ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (da, c1') <- tr1 s ds c1
        (db, c2') <- tr2 s ds c2
        r <- mkLet [|| pairDelta $$da $$db ||]
        return ( r, joinConn c1' c2' )

  unitTerm tenv = IFqTE tenv CNone (\_ -> return ([|| () ||], CNone)) (\_ _ _ -> return ([|| mempty ||], CNone))

  var0Term tenv = IFqTE (ECons Proxy tenv)
                       CNone
                       (\(ECons (PackedCode a) _) -> return (a, CNone))
                       (\_ (ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

  weakenTerm (IFqTE tenv i f tr) = IFqTE (ECons Proxy tenv) i f' tr'
    where
      f'  (ECons _ s) = f s
      tr' (ECons _ s) (ECons _ ds) = tr s ds

  unliftTerm :: forall a b. Diff a =>  IFqTE '[a] b -> IFq a b
  unliftTerm (IFqTE _ (i :: Conn Proxy cs) f tr) = IFq @(Join ('NE ('NEOne a)) cs) @a @b sh f' tr'
    where
      sh :: Conn Proxy (Join ('NE ('NEOne a)) cs)
      sh = joinConn (CNE (COne (Proxy @a))) i

      f' :: Code a -> CodeC (Code b, Conn PackedCode (Join ('NE ('NEOne a)) cs))
      f'  a    = do
        (b, c) <- f (ECons (PackedCode       a) ENil)
        return (b, joinConn (CNE (COne (PackedCode a))) c)

      tr' :: Diff a => Code (Delta a) -> Conn PackedCode (Join ('NE ('NEOne a)) cs)
             -> CodeC (Code (Delta b), Conn PackedCode (Join ('NE ('NEOne a)) cs))
      tr' da cc | (c0, c) <- decompConn (IsNoneFalse :: IsNone ('NE ('NEOne a))) (isNone i) cc = do
        let CNE (COne (PackedCode a)) = c0
        (db, c') <- tr (ECons (PackedCode a) ENil) (ECons (PackedCodeDelta da) ENil) c
        return (db, joinConn (CNE (COne (PackedCode [|| $$a /+ $$da ||]))) c')

letTermIFqTE :: forall as a b. Diff a => IFqTE as a -> IFqTE (a : as) b -> IFqTE as b
letTermIFqTE (IFqTE tenv (sh1 :: Conn Proxy cs1) f1 tr1)
             (IFqTE _    (sh2 :: Conn Proxy cs2) f2 tr2) = IFqTE tenv sh f tr
  where
    shA :: Conn Proxy ('NE ('NEOne a))
    shA = CNE (COne (Proxy @a))

    sh :: Conn Proxy (Join ('NE ('NEOne a)) (Join cs1 cs2))
    sh = joinConn shA (joinConn sh1 sh2)

    f :: Env PackedCode as
         -> CodeC (Code b, Conn PackedCode (Join ('NE ('NEOne a)) (Join cs1 cs2)))
    f s = do
      (a, c1) <- f1 s
      v <- mkLet a
      (b, c2) <- f2 (ECons (PackedCode v) s)
      return (b, joinConn (CNE (COne (PackedCode v))) (joinConn c1 c2))

    tr s ds cc | (cA, c12) <- decompConn (isNone shA) (isNone (joinConn sh1 sh2)) cc,
              (c1, c2) <- decompConn (isNone sh1) (isNone sh2) c12 = do
      let CNE (COne (PackedCode a)) = cA
      (da, c1') <- tr1 s ds c1
      dv <- mkLet da
      (db, c2') <- tr2 (ECons (PackedCode a) s) (ECons (PackedCodeDelta dv) ds) c2
      return (db, joinConn (CNE (COne (PackedCode [|| $$a /+ $$dv ||]))) (joinConn c1' c2'))

-- runIFqA :: IFqA a b -> Code (a -> (b, Interaction (Delta a) (Delta b) ))
-- runIFqA = runIFq . ifqa2ifq


-- data PackedCodeAtomicDelta a where
--   PackedCodeAtomicDelta :: Diff a => Code (AtomicDelta a) -> PackedCodeAtomicDelta a

-- mkUpdateEnv :: Index PackedCodeAtomicDelta as -> Env PackedCode as -> CodeC (Env PackedCode as)
-- mkUpdateEnv (IndexZ (PackedCodeAtomicDelta da)) (ECons (PackedCode a) as) = do
--   a' <- mkLet [|| applyAtomicDelta $$a $$da ||]
--   return (ECons (PackedCode a') as)
-- mkUpdateEnv (IndexS ix) (ECons a as) = do
--   as' <- mkUpdateEnv ix as
--   return $ ECons a as'



-- data IFqAT as b =
--   forall cs. IFqAT (Env Proxy as)
--                    (Conn Proxy cs)
--                    (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
--                    (Index PackedCodeAtomicDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))


-- instance HasProduct IFqA where
--   type Unit IFqA = ()
--   type Prod IFqA a b = (a, b)

--   unitOk _ = Wit
--   prodOk _ _ _ = Wit

-- instance Term IFqA IFqAT where
--   mapTerm (IFqA sh2 f2 tr2) (IFqAT tenv sh1 f1 tr1) = IFqAT tenv (joinConn sh1 sh2) f tr
--     where
--       f a = do
--         (b, c1) <- f1 a
--         (c, c2) <- f2 b
--         return (c, joinConn c1 c2)

--       tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--         (db, c1') <- tr1 da c1
--         (dc, c2') <- iterTrC sh2 tr2 db c2
--         return (dc, joinConn c1' c2')

--   multTerm (IFqAT tenv sh1 f1 tr1) (IFqAT _ sh2 f2 tr2) = IFqAT tenv (joinConn sh1 sh2) f tr
--     where
--       f s = do
--         (a, c1) <- f1 s
--         (b, c2) <- f2 s
--         r <- mkLet [|| ($$a, $$b) ||]
--         return (r , joinConn c1 c2)

--       tr ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--         (da, c1') <- tr1 ds c1
--         (db, c2') <- tr2 ds c2
--         r <- mkLet [|| pairDelta $$da $$db ||]
--         return ( r, joinConn c1' c2' )

--   unitTerm tenv = IFqAT tenv CNone (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| mempty ||], CNone))

--   var0Term tenv = IFqAT (ECons Proxy tenv)
--                         CNone
--                         (\(ECons (PackedCode a) _) -> return (a, CNone))
--                         (\denv _ -> case denv of
--                             IndexZ (PackedCodeAtomicDelta da) -> return ([|| injMonoid $$da ||], CNone)
--                             _         -> return ([|| mempty ||], CNone))
-- --                         (\(ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

--   weakenTerm (IFqAT tenv i f tr) = IFqAT (ECons Proxy tenv) i f' tr'
--     where
--       f'  (ECons _ s) = f s
--       tr' (IndexS ix) = tr ix
--       tr' _           = \cs -> return ([|| mempty ||],  cs)

--   unliftTerm (IFqAT _ i f tr) = IFqA i f' tr'
--     where
--       f'  a  = f  (ECons (PackedCode       a) ENil)
--       tr' da = tr (IndexZ (PackedCodeAtomicDelta da))


-- letTermIFqAT :: Diff b1 => IFqAT as b1 -> IFqAT (b1 : as) b2 -> IFqAT as b2
-- letTermIFqAT (IFqAT tenv sh1 f1 tr1) (IFqAT _ sh2 f2 tr2) = IFqAT tenv (joinConn sh1 sh2) f tr
--   where
--     f s = do
--       (a, c1) <- f1 s
--       v <- mkLet a
--       (b, c2) <- f2 (ECons (PackedCode v) s)
--       return (b, joinConn c1 c2)

--     tr s cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--       (da, c1') <- tr1 s c1
--       dvs <- mkLet da
--       (db1, c2' ) <- tr2 (IndexS s) c2
--       (db2, c2'') <- iterTrC sh2 (\dv -> tr2 (IndexZ $ PackedCodeAtomicDelta dv)) dvs c2'
--       return ([|| $$db1 <> $$db2 ||], joinConn c1' c2'')

-- -- FIXME: tentative
-- shareA :: forall e r1 r2. (Diff r1, App2 IFqA IFqAT e) => e r1 -> (e r1 -> e r2) -> e r2
-- shareA = liftSO2 (Proxy @'[ '[], '[r1] ] ) letTermIFqAT



-- data IFqATM as b =
--   forall cs. IFqATM (Env Proxy as)
--                     (Conn Proxy cs)
--                     (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
--                     (Env PackedCodeAtomicDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

-- instance Term IFqA IFqATM where
--   mapTerm (IFqA sh2 f2 tr2) (IFqATM tenv sh1 f1 tr1) = IFqATM tenv (joinConn sh1 sh2) f tr
--     where
--       f a = do
--         (b, c1) <- f1 a
--         (c, c2) <- f2 b
--         return (c, joinConn c1 c2)

--       tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--         (db, c1') <- tr1 da c1
--         (dc, c2') <- iterTrC sh2 tr2 db c2
--         return (dc, joinConn c1' c2')

--   multTerm (IFqATM tenv sh1 f1 tr1) (IFqATM _ sh2 f2 tr2) = IFqATM tenv (joinConn sh1 sh2) f tr
--     where
--       f s = do
--         (a, c1) <- f1 s
--         (b, c2) <- f2 s
--         r <- mkLet [|| ($$a, $$b) ||]
--         return (r , joinConn c1 c2)

--       tr ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--         (da, c1') <- tr1 ds c1
--         (db, c2') <- tr2 ds c2
--         r <- mkLet [|| pairDelta $$da $$db ||]
--         return ( r, joinConn c1' c2' )

--   unitTerm tenv = IFqATM tenv CNone (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| mempty ||], CNone))

--   var0Term tenv = IFqATM (ECons Proxy tenv)
--                          CNone
--                          (\(ECons (PackedCode a) _) -> return (a, CNone))
--                          (\denv _ -> case denv of
--                             ECons (PackedCodeAtomicDelta da) _ -> return ([|| injMonoid $$da ||], CNone))
-- --                         (\(ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

--   weakenTerm (IFqATM tenv i f tr) = IFqATM (ECons Proxy tenv) i f' tr'
--     where
--       f'  (ECons _ s) = f s
--       tr' (ECons _ denv) = tr denv

--   unliftTerm (IFqATM _ i f tr) = IFqA i f' tr'
--     where
--       f'  a  = f  (ECons (PackedCode       a) ENil)
--       tr' da = tr (ECons (PackedCodeAtomicDelta da) ENil)

-- -- Given : Env PackedCodeAtomicDelta (a : as) -> cs -> CodeC (Code (Delta b), cs)
-- -- Find : Code (Delta a) -> Env PackedCodeAtomicDelta as -> cs -> CodeC (Code (Delta b), cs)

-- letTermIFqATM :: Diff b1 => IFqATM as b1 -> IFqATM (b1 : as) b2 -> IFqATM as b2
-- letTermIFqATM (IFqATM tenv sh1 f1 tr1) (IFqATM _ sh2 f2 tr2) = IFqATM tenv (joinConn sh1 sh2) f tr
--   where
--     f s = do
--       (a, c1) <- f1 s
--       v <- mkLet a
--       (b, c2) <- f2 (ECons (PackedCode v) s)
--       return (b, joinConn c1 c2)

--     tr s cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--       (da, c1') <- tr1 s c1
--       dvs <- mkLet da
--       (db1, c2' ) <- tr2 (IndexS s) c2
--       (db2, c2'') <- iterTrC sh2 (\dv -> tr2 (IndexZ $ PackedCodeAtomicDelta dv)) dvs c2'
--       return ([|| $$db1 <> $$db2 ||], joinConn c1' c2'')





