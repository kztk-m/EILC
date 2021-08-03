{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module EILC where

import           Control.Category      (Category (..))
import           Data.Coerce           (coerce)
import           Data.Functor.Identity
import           Data.Monoid           (Sum (..))
import           Data.Typeable         (Proxy (..))
import           Prelude               hiding (id, (.))
import qualified Unsafe.Coerce         as Unsafe

import qualified Language.Haskell.TH   as TH

import           Data.Env
import           Data.Kind             (Type)
import           Language.Unembedding

type family Delta (a :: Type) :: Type

type instance Delta (Identity a) = Delta a
type instance Delta () = ()
type instance Delta (a, b) = (Delta a, Delta b)


class Monoid (Delta a) => Diff a where
  -- | Applying delta.
  -- prop> a /+ da /+ da' = a /+ (da <> da')
  (/+) :: a -> Delta a -> a

instance Diff () where
  _ /+ _ = ()

instance (Diff a, Diff b) => Diff (a, b) where
  (a, b) /+ (da, db) = (a /+ da, b /+ db)




-- | Incremtalized function
--
-- prop> let (b, tr) = runIF f a in f (foldl (/+) a das) == foldl (/+) b (tr das)
-- Or, equivalently
-- prop> let (b, tr) = runIF f a in f (a /+ mconcat das) == b /+ mconcat das
data IF a b = forall c. IF !(a -> (b, c)) !(Delta a -> c -> (Delta b, c))

-- simplarly to IF but a is applied partially beforehand
data IV a b = forall c. IV !(b, c) !(Delta a -> c -> (Delta b, c))

instance Category IF where
  id = IF (\a -> (a, ())) (\da c -> (da , c))

  IF f2 tr2 . IF f1 tr1 = IF f tr
    where
      f a = let (b, c1) = f1 a
                (c, c2) = f2 b
            in (c, (c1, c2))

      tr da (c1 , c2) =
        let (db , c1') = tr1 da c1
            (dc , c2') = tr2 db c2
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
      in ( (da, db) , (c1' , c2') )

toIF :: Diff a => (a -> b) -> (a -> Delta a -> Delta b) -> IF a b
toIF f df = IF (\a -> (f a, a)) (\da a -> (df a da, a /+ da))

runIF :: IF a b -> a -> (b, [Delta a] -> [Delta b])
runIF (IF f tr) a =
  let (b, c) = f a
  in (b, comp c)
  where
    comp _ [] = []
    comp c (da : das) =
      let (db, c') = tr da c
      in db : comp c' das

class Incr e where
  liftI :: Diff a => (a -> b) -> (a -> Delta a -> Delta b) -> e a -> e b
  shareI :: e a -> (e a -> e b) -> e b

  pairI :: e a -> e b -> e (a, b)


data DEnv f as where
  DENil :: DEnv f '[]
  DECons :: Delta (f a) -> DEnv f as -> DEnv f (a ': as)

newtype PackedDelta f a = PackedDelta { getDelta :: Delta (f a) }

type instance Delta (Env f as) = Env (PackedDelta f) as

tailIF :: IF (Env Identity (a : as)) (Env Identity as)
tailIF = IF (\(ECons _ r) -> (r, ()))
            (\(ECons _ dr) _ -> (dr, ()))

headIF :: IF (Env Identity (a : as)) a
headIF = IF (\(ECons a _) -> (coerce a, ()))
            (\(ECons da _) _ -> (coerce da, ()))


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
                 (\(da, das) _ -> (ECons (PackedDelta da) das, ()))

  pairI (UnembIncr x) (UnembIncr y) = UnembIncr $ \tenv -> prodIF (x tenv) (y tenv)

runIncrMono :: (UnembIncr a -> UnembIncr b) -> IF a b
runIncrMono f = runUnembIncr (shareI (UnembIncr $ \(ECons Proxy _) -> Unsafe.unsafeCoerce headIF) f) (ECons Proxy ENil) . singleton
  where
    singleton :: IF a (Env Identity '[a])
    singleton = IF (\a -> (ECons (Identity a) ENil, ()))
                   (\da _ -> (ECons (PackedDelta da) ENil, ()))

newtype Bag a = Bag [a] deriving (Monoid, Semigroup)
type instance Delta (Bag a) = Bag a -- only insertion is considered.

instance Diff (Bag a) where
  Bag xs /+ Bag ys = Bag (ys ++ xs)

type instance Delta Int    = Sum Int
type instance Delta Double = Sum Double

instance Diff Int where
  a /+ da = a + getSum da

instance Diff Double where
  a /+ da = a + getSum da

sumD :: Bag Double -> Delta (Bag Double) -> Delta Double
sumD _ (Bag xs) = Sum $ Prelude.sum xs

lenD :: Bag Double -> Delta (Bag Double) -> Delta Int
lenD _ (Bag xs) = Sum $ length xs

i2d :: Int -> Double
i2d = fromIntegral

i2dD :: Int -> Delta Int -> Delta Double
i2dD _ d = Sum $ fromIntegral $ getSum d

divD :: (Double, Double) -> (Delta Double, Delta Double) -> Delta Double
divD (x, y) (dx, dy) = Sum $ (x /+ dx) / (y /+ dy) - x / y

sumF :: Incr e => e (Bag Double) -> e Double
sumF = liftI (\(Bag xs) -> sum xs) sumD

lenF :: Incr e => e (Bag Double) -> e Int
lenF = liftI (\(Bag xs) -> length xs) lenD

i2dF :: Incr e => e Int -> e Double
i2dF = liftI i2d i2dD

divF :: Incr e => e (Double, Double) -> e Double
divF = liftI (uncurry (/)) divD

aveD :: Incr e => e (Bag Double) -> e Double
aveD x = shareI x $ \y -> divF (pairI (sumF y) (i2dF (lenF y)))

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

data IFt a b = forall cs. IFt (IsNone cs) (a -> (b, Conn Identity cs)) (Delta a -> Conn Identity cs -> (Delta b, Conn Identity cs))

instance Category IFt where
  id = IFt IsNoneTrue (\a -> (a, CNone)) (\da c -> (da, c))

  IFt isNone2 f2 tr2 . IFt isNone1 f1 tr1 = IFt (isNoneAnd isNone1 isNone2) f tr
    where
      f a = let (b, c1) = f1 a
                (c, c2) = f2 b
            in ( c, joinConn c1 c2 )

      tr da cc = case decompConn isNone1 isNone2 cc of
        (c1, c2) -> let (db, c1') = tr1 da c1
                        (dc, c2') = tr2 db c2
                    in (dc, joinConn c1' c2')

unitIFt :: IFt s ()
unitIFt = IFt IsNoneTrue (const ((), CNone)) (\_ _ -> ((), CNone))

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
      in ( (da, db), joinConn c1' c2' )


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

data IFq a b =
  forall cs. IFq (IsNone cs)
                 (Code a -> CodeC (Code b, Conn PackedCode cs))
                 (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

instance Category IFq where
  id = IFq IsNoneTrue (\a -> return (a, CNone))
                      (\da _ -> return (da, CNone))

  IFq isNone2 f2 tr2 . IFq isNone1 f1 tr1 = IFq (isNoneAnd isNone1 isNone2) f tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr da cc | (c1, c2) <- decompConn isNone1 isNone2 cc = do
        (db, c1') <- tr1 da c1
        (dc, c2') <- tr2 db c2
        return (dc, joinConn c1' c2')

ifqFromStateless :: (Code a -> Code b) -> (Code (Delta a) -> Code (Delta b)) -> IFq a b
ifqFromStateless f df = IFq IsNoneTrue (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df da) ; return (v, CNone) })

ifqFromD :: Diff a => (Code a -> Code b) -> (Code a -> Code (Delta a) -> Code (Delta b)) -> IFq a b
ifqFromD f df = IFq IsNoneFalse
                    (\a -> do { v <- mkLet (f a) ; return (v, CNE (COne (PackedCode a))) })
                    (\da (CNE (COne (PackedCode a))) -> do { v <- mkLet (df a da) ; a' <- mkLet [|| $$a /+ $$da ||] ; return (v, CNE (COne (PackedCode a'))) })

multIFq :: IFq s a -> IFq s b -> IFq s (a, b)
multIFq (IFq isNone1 f1 tr1) (IFq isNone2 f2 tr2) = IFq (isNoneAnd isNone1 isNone2) f tr
  where
    f s = do
      (a, c1) <- f1 s
      (b, c2) <- f2 s
      r <- mkLet [|| ($$a, $$b) ||]
      return (r , joinConn c1 c2)

    tr ds cc | (c1, c2) <- decompConn isNone1 isNone2 cc = do
      (da, c1') <- tr1 ds c1
      (db, c2') <- tr2 ds c2
      r <- mkLet [|| ($$da, $$db) ||]
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

dumpIFq :: IFq a b -> IO ()
dumpIFq (IFq IsNoneTrue f tr) = do
  putStrLn "IsNone: True"
  e <- TH.runQ [|| \x -> $$(runCodeC (f [|| x ||]) fst ) ||]
  putStrLn "=== f ==="
  putStrLn $ TH.pprint $ TH.unType e
  de <- TH.runQ [|| \x -> $$(runCodeC (tr [|| x ||] CNone) fst) ||]
  putStrLn "=== df ==="
  putStrLn $ TH.pprint $ TH.unType de
dumpIFq (IFq IsNoneFalse f _) = do
  putStrLn "IsNone: False"
  putStrLn "=== <f, c> ==="
  e <- TH.runQ [|| \x -> $$( runCodeC (f [|| x ||]) $ \(y, c) -> [|| ($$y , $$(conn2code c)) ||]) ||]
  putStrLn $ TH.pprint $ TH.unType e
  putStrLn "printing df is not implemented"

conn2code :: Conn PackedCode cs -> Code (Conn Identity cs)
conn2code CNone   = [|| CNone ||]
conn2code (CNE c) = [|| CNE $$(conn2code' c) ||]

conn2code' :: NEConn PackedCode cs -> Code (NEConn Identity cs)
conn2code' (COne (PackedCode c)) = [|| COne (Identity $$c) ||]
conn2code' (CJoin c1 c2)         = [|| CJoin $$(conn2code' c1) $$(conn2code' c2) ||]

code2conn :: forall cs r. Conn Proxy cs -> Code (Conn Identity cs) -> (Conn PackedCode cs -> Code r) -> Code r
code2conn CNone      _ k = k CNone
code2conn (CNE pcne) c k = code2conn' pcne [|| unCNE $$c ||] (\x -> k (CNE x))

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

mkAbs :: Conn Proxy cs -> (Conn PackedCode cs -> Code a) -> Code (Func cs a)
mkAbs CNone k    = k CNone
mkAbs (CNE cs) k = mkAbs' cs (k . CNE)

mkAbs' :: NEConn Proxy cs -> (NEConn PackedCode cs -> Code a) -> Code (Func' cs a)
mkAbs' (COne _) k      = [|| \a -> $$(k (COne $ PackedCode [|| a ||])) ||]
mkAbs' (CJoin c1 c2) k = mkAbs' c1 $ \c1' -> mkAbs' c2 $ \c2' -> k (CJoin c1' c2')

mkApp :: Code (Func cs a) -> Conn PackedCode cs -> Code a
mkApp f CNone    = f
mkApp f (CNE cs) = mkApp' f cs

mkApp' :: Code (Func' cs a) -> NEConn PackedCode cs -> Code a
mkApp' f (COne (PackedCode a)) = [|| $$f $$a ||]
mkApp' f (CJoin c1 c2)         = mkApp' (mkApp' f c1) c2


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
  unitS = IFq IsNoneTrue (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| () ||], CNone))

  fstS _ _ = IFq IsNoneTrue
                (\as    -> do { v <- mkLet [|| case $$as of { (a, _) -> a } ||] ; return (v, CNone)})
                (\das _ -> do { vda <- mkLet [|| case $$das of { (da,_) -> da } ||]; return (vda, CNone) } )

  sndS _ _ = IFq IsNoneTrue
                (\as    -> do { v <- mkLet [|| case $$as of { (_, a) -> a } ||] ; return (v, CNone)})
                (\das _ -> do { vda <- mkLet [|| case $$das of { (_, da) -> da } ||]; return (vda, CNone) } )

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


runAppMono :: Cartesian cat => (TSem (TermFromCat cat) a -> TSem (TermFromCat cat) b) -> cat a b
runAppMono = runMono


ave :: App IFq e => (e (Bag Double) -> e Double)
ave = \x -> mysum x `mydiv` i2d (len x)
  where
    lenC :: IFq (Bag Double) Int
    lenC = ifqFromStateless (\a  -> [|| case $$a of { Bag as -> length as } ||])
                            (\da -> [|| case $$da of { Bag as -> Sum (length as) } ||])

    i2dC :: IFq Int Double
    i2dC = ifqFromStateless (\a -> [|| fromIntegral $$a :: Double ||]) (\da -> [|| Sum (fromIntegral (getSum $$da) :: Double) ||])

    sumC :: IFq (Bag Double) Double
    sumC = ifqFromStateless (\a  -> [|| case $$a of { Bag as -> sum as } ||])
                            (\da -> [|| case $$da of { Bag as' -> Sum (sum as') } ||])

    divC :: IFq (Double, Double) Double
    divC = ifqFromD (\z -> [|| uncurry (/) $$z ||])
                    (\z dz -> [|| let {(x, y) = $$z ; (dx, dy) = $$dz} in Sum $ (x /+ dx) / (y /+ dy) - x / y ||])

    len = lift lenC
    i2d = lift i2dC
    mysum = lift sumC
    mydiv x y = lift divC (pair x y)


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




runAppMono' :: Term cat term => (TSem term a -> TSem term b) -> cat a b
runAppMono' = runMono

newtype PackedCodeDelta a = PackedCodeDelta { getCodeDelta :: Code (Delta a) }

data IFqT as b =
  forall cs. IFqT (IsNone cs)
                  (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
                  (Env PackedCodeDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

instance HasProduct IFq where
  type Unit IFq = ()
  type Prod IFq a b = (a, b)

instance Term IFq IFqT where
  mapTerm (IFq isNone2 f2 tr2) (IFqT isNone1 f1 tr1) = IFqT (isNoneAnd isNone1 isNone2) f tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr da cc | (c1, c2) <- decompConn isNone1 isNone2 cc = do
        (db, c1') <- tr1 da c1
        (dc, c2') <- tr2 db c2
        return (dc, joinConn c1' c2')

  multTerm (IFqT isNone1 f1 tr1) (IFqT isNone2 f2 tr2) = IFqT (isNoneAnd isNone1 isNone2) f tr
    where
      f s = do
        (a, c1) <- f1 s
        (b, c2) <- f2 s
        r <- mkLet [|| ($$a, $$b) ||]
        return (r , joinConn c1 c2)

      tr ds cc | (c1, c2) <- decompConn isNone1 isNone2 cc = do
        (da, c1') <- tr1 ds c1
        (db, c2') <- tr2 ds c2
        r <- mkLet [|| ($$da, $$db) ||]
        return ( r, joinConn c1' c2' )

  unitTerm = IFqT IsNoneTrue (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| () ||], CNone))

  var0Term = IFqT IsNoneTrue (\(ECons (PackedCode a) _) -> return (a, CNone))
                             (\(ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

  weakenTerm (IFqT i f tr) = IFqT i f' tr'
    where
      f'  (ECons _ s) = f s
      tr' (ECons _ s) = tr s

  unliftTerm (IFqT i f tr) = IFq i f' tr'
    where
      f'  a  = f  (ECons (PackedCode       a) ENil)
      tr' da = tr (ECons (PackedCodeDelta da) ENil)

letTermIFqT :: IFqT as b1 -> IFqT (b1 : as) b2 -> IFqT as b2
letTermIFqT (IFqT isNone1 f1 tr1) (IFqT isNone2 f2 tr2) = IFqT (isNoneAnd isNone1 isNone2) f tr
  where
    f s = do
      (a, c1) <- f1 s
      v <- mkLet a
      (b, c2) <- f2 (ECons (PackedCode v) s)
      return (b, joinConn c1 c2)

    tr s cc | (c1, c2) <- decompConn isNone1 isNone2 cc = do
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

appC :: IFq (Bag Double, Bag Double) (Bag Double)
appC = ifqFromStateless (\z -> [|| case $$z of { (Bag xs, Bag ys) -> Bag (xs ++ ys) } ||])
                        (\dz -> [|| case $$dz of { (Bag dx, Bag dy) -> Bag (dx ++ dy) } ||])
appF :: App IFq e => e (Bag Double) -> e (Bag Double) -> e (Bag Double)
appF x y = lift appC (pair x y)

-- FIXME: tentative
share :: forall e r1 r2. App2 IFq IFqT e => e r1 -> (e r1 -> e r2) -> e r2
share = liftSO2 (Proxy @'[ '[], '[r1] ] ) letTermIFqT
  -- _ $ liftSO (packTermF letTermIFqT)
  -- liftSO (packTermF letTermIFqT) (ECons (Fun ENil (\ENil -> e)) (ECons (Fun (ECons Proxy ENil) (\(ECons x ENil) -> k x)) ENil))
  -- liftSO (\(ECons (TermF e1) (ECons (TermF e2) ENil)) -> letTermIFqT e1 e2) (ECons (Fun ENil (\ENil -> e)) (ECons (Fun (ECons Proxy ENil) (\(ECons x ENil) -> k x)) ENil))

cascadeAppS :: (App2 IFq IFqT e) => Int -> e (Bag Double) -> (e (Bag Double) -> e b) -> e b
cascadeAppS 0 x f = f x
cascadeAppS n x f = share (appF x x) $ \y -> cascadeAppS (n-1) y f

cascadeAppC :: (App2 IFq IFqT e) => Int -> e (Bag Double) -> (e (Bag Double) -> e b) -> e b
cascadeAppC 0 x f = f x
cascadeAppC n x f = let y = appF x x in cascadeAppC (n-1) y f


aveDupDup :: (App2 IFq IFqT e) => e (Bag Double) -> e Double
aveDupDup x = cascadeAppS 4 x ave

aveDupDup' :: (App2 IFq IFqT e) => e (Bag Double) -> e Double
aveDupDup' x = cascadeAppC 4 x ave

{-

To check how "share" works, compare the difference between aveDupDup and aveDupDup':

*EILC EILC> let _  = $$( runIFq (runAppMono' aveDupDup') )
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
<interactive>:20:14-44: Splicing expression
    runIFq (runAppMono' aveDupDup')
  ======>
    (ensureDiffType
       $ (\ pa_alZU pb_alZV a_alZW
            -> let v_alZX = (a_alZW, a_alZW) in
               let
                 v_alZY
                   = case v_alZX of {
                       (Bag xs_alZZ, Bag ys_am00) -> Bag (xs_alZZ ++ ys_am00) } in
               let v_am01 = (a_alZW, a_alZW) in
               let
                 v_am02
                   = case v_am01 of {
                       (Bag xs_am03, Bag ys_am04) -> Bag (xs_am03 ++ ys_am04) } in
               let v_am05 = (v_alZY, v_am02) in
               let
                 v_am06
                   = case v_am05 of {
                       (Bag xs_am07, Bag ys_am08) -> Bag (xs_am07 ++ ys_am08) } in
               let v_am09 = (a_alZW, a_alZW) in
               let
                 v_am0a
                   = case v_am09 of {
                       (Bag xs_am0b, Bag ys_am0c) -> Bag (xs_am0b ++ ys_am0c) } in
               let v_am0d = (a_alZW, a_alZW) in
               let
                 v_am0e
                   = case v_am0d of {
                       (Bag xs_am0f, Bag ys_am0g) -> Bag (xs_am0f ++ ys_am0g) } in
               let v_am0h = (v_am0a, v_am0e) in
               let
                 v_am0i
                   = case v_am0h of {
                       (Bag xs_am0j, Bag ys_am0k) -> Bag (xs_am0j ++ ys_am0k) } in
               let v_am0l = (v_am06, v_am0i) in
               let
                 v_am0m
                   = case v_am0l of {
                       (Bag xs_am0n, Bag ys_am0o) -> Bag (xs_am0n ++ ys_am0o) } in
               let v_am0p = (a_alZW, a_alZW) in
               let
                 v_am0q
                   = case v_am0p of {
                       (Bag xs_am0r, Bag ys_am0s) -> Bag (xs_am0r ++ ys_am0s) } in
               let v_am0t = (a_alZW, a_alZW) in
               let
                 v_am0u
                   = case v_am0t of {
                       (Bag xs_am0v, Bag ys_am0w) -> Bag (xs_am0v ++ ys_am0w) } in
               let v_am0x = (v_am0q, v_am0u) in
               let
                 v_am0y
                   = case v_am0x of {
                       (Bag xs_am0z, Bag ys_am0A) -> Bag (xs_am0z ++ ys_am0A) } in
               let v_am0B = (a_alZW, a_alZW) in
               let
                 v_am0C
                   = case v_am0B of {
                       (Bag xs_am0D, Bag ys_am0E) -> Bag (xs_am0D ++ ys_am0E) } in
               let v_am0F = (a_alZW, a_alZW) in
               let
                 v_am0G
                   = case v_am0F of {
                       (Bag xs_am0H, Bag ys_am0I) -> Bag (xs_am0H ++ ys_am0I) } in
               let v_am0J = (v_am0C, v_am0G) in
               let
                 v_am0K
                   = case v_am0J of {
                       (Bag xs_am0L, Bag ys_am0M) -> Bag (xs_am0L ++ ys_am0M) } in
               let v_am0N = (v_am0y, v_am0K) in
               let
                 v_am0O
                   = case v_am0N of {
                       (Bag xs_am0P, Bag ys_am0Q) -> Bag (xs_am0P ++ ys_am0Q) } in
               let v_am0R = (v_am0m, v_am0O) in
               let
                 v_am0S
                   = case v_am0R of {
                       (Bag xs_am0T, Bag ys_am0U) -> Bag (xs_am0T ++ ys_am0U) } in
               let v_am0V = case v_am0S of { Bag as_am0W -> sum as_am0W } in
               let v_am0X = (a_alZW, a_alZW) in
               let
                 v_am0Y
                   = case v_am0X of {
                       (Bag xs_am0Z, Bag ys_am10) -> Bag (xs_am0Z ++ ys_am10) } in
               let v_am11 = (a_alZW, a_alZW) in
               let
                 v_am12
                   = case v_am11 of {
                       (Bag xs_am13, Bag ys_am14) -> Bag (xs_am13 ++ ys_am14) } in
               let v_am15 = (v_am0Y, v_am12) in
               let
                 v_am16
                   = case v_am15 of {
                       (Bag xs_am17, Bag ys_am18) -> Bag (xs_am17 ++ ys_am18) } in
               let v_am19 = (a_alZW, a_alZW) in
               let
                 v_am1a
                   = case v_am19 of {
                       (Bag xs_am1b, Bag ys_am1c) -> Bag (xs_am1b ++ ys_am1c) } in
               let v_am1d = (a_alZW, a_alZW) in
               let
                 v_am1e
                   = case v_am1d of {
                       (Bag xs_am1f, Bag ys_am1g) -> Bag (xs_am1f ++ ys_am1g) } in
               let v_am1h = (v_am1a, v_am1e) in
               let
                 v_am1i
                   = case v_am1h of {
                       (Bag xs_am1j, Bag ys_am1k) -> Bag (xs_am1j ++ ys_am1k) } in
               let v_am1l = (v_am16, v_am1i) in
               let
                 v_am1m
                   = case v_am1l of {
                       (Bag xs_am1n, Bag ys_am1o) -> Bag (xs_am1n ++ ys_am1o) } in
               let v_am1p = (a_alZW, a_alZW) in
               let
                 v_am1q
                   = case v_am1p of {
                       (Bag xs_am1r, Bag ys_am1s) -> Bag (xs_am1r ++ ys_am1s) } in
               let v_am1t = (a_alZW, a_alZW) in
               let
                 v_am1u
                   = case v_am1t of {
                       (Bag xs_am1v, Bag ys_am1w) -> Bag (xs_am1v ++ ys_am1w) } in
               let v_am1x = (v_am1q, v_am1u) in
               let
                 v_am1y
                   = case v_am1x of {
                       (Bag xs_am1z, Bag ys_am1A) -> Bag (xs_am1z ++ ys_am1A) } in
               let v_am1B = (a_alZW, a_alZW) in
               let
                 v_am1C
                   = case v_am1B of {
                       (Bag xs_am1D, Bag ys_am1E) -> Bag (xs_am1D ++ ys_am1E) } in
               let v_am1F = (a_alZW, a_alZW) in
               let
                 v_am1G
                   = case v_am1F of {
                       (Bag xs_am1H, Bag ys_am1I) -> Bag (xs_am1H ++ ys_am1I) } in
               let v_am1J = (v_am1C, v_am1G) in
               let
                 v_am1K
                   = case v_am1J of {
                       (Bag xs_am1L, Bag ys_am1M) -> Bag (xs_am1L ++ ys_am1M) } in
               let v_am1N = (v_am1y, v_am1K) in
               let
                 v_am1O
                   = case v_am1N of {
                       (Bag xs_am1P, Bag ys_am1Q) -> Bag (xs_am1P ++ ys_am1Q) } in
               let v_am1R = (v_am1m, v_am1O) in
               let
                 v_am1S
                   = case v_am1R of {
                       (Bag xs_am1T, Bag ys_am1U) -> Bag (xs_am1T ++ ys_am1U) } in
               let v_am1V = case v_am1S of { Bag as_am1W -> length as_am1W } in
               let v_am1X = fromIntegral v_am1V :: Double in
               let v_am1Y = (v_am0V, v_am1X) in
               let v_am1Z = (uncurry (/)) v_am1Y
               in
                 (v_am1Z,
                  let
                    func_am20
                      = \ a_am21
                          -> ((mkInteraction pa_alZU) pb_alZV
                                $ (\ da_am22
                                     -> let v_am23 = (da_am22, da_am22) in
                                        let
                                          v_am24
                                            = case v_am23 of {
                                                (Bag dx_am25, Bag dy_am26)
                                                  -> Bag (dx_am25 ++ dy_am26) } in
                                        let v_am27 = (da_am22, da_am22) in
                                        let
                                          v_am28
                                            = case v_am27 of {
                                                (Bag dx_am29, Bag dy_am2a)
                                                  -> Bag (dx_am29 ++ dy_am2a) } in
                                        let v_am2b = (v_am24, v_am28) in
                                        let
                                          v_am2c
                                            = case v_am2b of {
                                                (Bag dx_am2d, Bag dy_am2e)
                                                  -> Bag (dx_am2d ++ dy_am2e) } in
                                        let v_am2f = (da_am22, da_am22) in
                                        let
                                          v_am2g
                                            = case v_am2f of {
                                                (Bag dx_am2h, Bag dy_am2i)
                                                  -> Bag (dx_am2h ++ dy_am2i) } in
                                        let v_am2j = (da_am22, da_am22) in
                                        let
                                          v_am2k
                                            = case v_am2j of {
                                                (Bag dx_am2l, Bag dy_am2m)
                                                  -> Bag (dx_am2l ++ dy_am2m) } in
                                        let v_am2n = (v_am2g, v_am2k) in
                                        let
                                          v_am2o
                                            = case v_am2n of {
                                                (Bag dx_am2p, Bag dy_am2q)
                                                  -> Bag (dx_am2p ++ dy_am2q) } in
                                        let v_am2r = (v_am2c, v_am2o) in
                                        let
                                          v_am2s
                                            = case v_am2r of {
                                                (Bag dx_am2t, Bag dy_am2u)
                                                  -> Bag (dx_am2t ++ dy_am2u) } in
                                        let v_am2v = (da_am22, da_am22) in
                                        let
                                          v_am2w
                                            = case v_am2v of {
                                                (Bag dx_am2x, Bag dy_am2y)
                                                  -> Bag (dx_am2x ++ dy_am2y) } in
                                        let v_am2z = (da_am22, da_am22) in
                                        let
                                          v_am2A
                                            = case v_am2z of {
                                                (Bag dx_am2B, Bag dy_am2C)
                                                  -> Bag (dx_am2B ++ dy_am2C) } in
                                        let v_am2D = (v_am2w, v_am2A) in
                                        let
                                          v_am2E
                                            = case v_am2D of {
                                                (Bag dx_am2F, Bag dy_am2G)
                                                  -> Bag (dx_am2F ++ dy_am2G) } in
                                        let v_am2H = (da_am22, da_am22) in
                                        let
                                          v_am2I
                                            = case v_am2H of {
                                                (Bag dx_am2J, Bag dy_am2K)
                                                  -> Bag (dx_am2J ++ dy_am2K) } in
                                        let v_am2L = (da_am22, da_am22) in
                                        let
                                          v_am2M
                                            = case v_am2L of {
                                                (Bag dx_am2N, Bag dy_am2O)
                                                  -> Bag (dx_am2N ++ dy_am2O) } in
                                        let v_am2P = (v_am2I, v_am2M) in
                                        let
                                          v_am2Q
                                            = case v_am2P of {
                                                (Bag dx_am2R, Bag dy_am2S)
                                                  -> Bag (dx_am2R ++ dy_am2S) } in
                                        let v_am2T = (v_am2E, v_am2Q) in
                                        let
                                          v_am2U
                                            = case v_am2T of {
                                                (Bag dx_am2V, Bag dy_am2W)
                                                  -> Bag (dx_am2V ++ dy_am2W) } in
                                        let v_am2X = (v_am2s, v_am2U) in
                                        let
                                          v_am2Y
                                            = case v_am2X of {
                                                (Bag dx_am2Z, Bag dy_am30)
                                                  -> Bag (dx_am2Z ++ dy_am30) } in
                                        let
                                          v_am31
                                            = case v_am2Y of {
                                                Bag as'_am32 -> Sum (sum as'_am32) } in
                                        let v_am33 = (da_am22, da_am22) in
                                        let
                                          v_am34
                                            = case v_am33 of {
                                                (Bag dx_am35, Bag dy_am36)
                                                  -> Bag (dx_am35 ++ dy_am36) } in
                                        let v_am37 = (da_am22, da_am22) in
                                        let
                                          v_am38
                                            = case v_am37 of {
                                                (Bag dx_am39, Bag dy_am3a)
                                                  -> Bag (dx_am39 ++ dy_am3a) } in
                                        let v_am3b = (v_am34, v_am38) in
                                        let
                                          v_am3c
                                            = case v_am3b of {
                                                (Bag dx_am3d, Bag dy_am3e)
                                                  -> Bag (dx_am3d ++ dy_am3e) } in
                                        let v_am3f = (da_am22, da_am22) in
                                        let
                                          v_am3g
                                            = case v_am3f of {
                                                (Bag dx_am3h, Bag dy_am3i)
                                                  -> Bag (dx_am3h ++ dy_am3i) } in
                                        let v_am3j = (da_am22, da_am22) in
                                        let
                                          v_am3k
                                            = case v_am3j of {
                                                (Bag dx_am3l, Bag dy_am3m)
                                                  -> Bag (dx_am3l ++ dy_am3m) } in
                                        let v_am3n = (v_am3g, v_am3k) in
                                        let
                                          v_am3o
                                            = case v_am3n of {
                                                (Bag dx_am3p, Bag dy_am3q)
                                                  -> Bag (dx_am3p ++ dy_am3q) } in
                                        let v_am3r = (v_am3c, v_am3o) in
                                        let
                                          v_am3s
                                            = case v_am3r of {
                                                (Bag dx_am3t, Bag dy_am3u)
                                                  -> Bag (dx_am3t ++ dy_am3u) } in
                                        let v_am3v = (da_am22, da_am22) in
                                        let
                                          v_am3w
                                            = case v_am3v of {
                                                (Bag dx_am3x, Bag dy_am3y)
                                                  -> Bag (dx_am3x ++ dy_am3y) } in
                                        let v_am3z = (da_am22, da_am22) in
                                        let
                                          v_am3A
                                            = case v_am3z of {
                                                (Bag dx_am3B, Bag dy_am3C)
                                                  -> Bag (dx_am3B ++ dy_am3C) } in
                                        let v_am3D = (v_am3w, v_am3A) in
                                        let
                                          v_am3E
                                            = case v_am3D of {
                                                (Bag dx_am3F, Bag dy_am3G)
                                                  -> Bag (dx_am3F ++ dy_am3G) } in
                                        let v_am3H = (da_am22, da_am22) in
                                        let
                                          v_am3I
                                            = case v_am3H of {
                                                (Bag dx_am3J, Bag dy_am3K)
                                                  -> Bag (dx_am3J ++ dy_am3K) } in
                                        let v_am3L = (da_am22, da_am22) in
                                        let
                                          v_am3M
                                            = case v_am3L of {
                                                (Bag dx_am3N, Bag dy_am3O)
                                                  -> Bag (dx_am3N ++ dy_am3O) } in
                                        let v_am3P = (v_am3I, v_am3M) in
                                        let
                                          v_am3Q
                                            = case v_am3P of {
                                                (Bag dx_am3R, Bag dy_am3S)
                                                  -> Bag (dx_am3R ++ dy_am3S) } in
                                        let v_am3T = (v_am3E, v_am3Q) in
                                        let
                                          v_am3U
                                            = case v_am3T of {
                                                (Bag dx_am3V, Bag dy_am3W)
                                                  -> Bag (dx_am3V ++ dy_am3W) } in
                                        let v_am3X = (v_am3s, v_am3U) in
                                        let
                                          v_am3Y
                                            = case v_am3X of {
                                                (Bag dx_am3Z, Bag dy_am40)
                                                  -> Bag (dx_am3Z ++ dy_am40) } in
                                        let
                                          v_am41
                                            = case v_am3Y of {
                                                Bag as_am42 -> Sum (length as_am42) } in
                                        let v_am43 = Sum (fromIntegral (getSum v_am41) :: Double) in
                                        let v_am44 = (v_am31, v_am43) in
                                        let
                                          v_am45
                                            = let
                                                (x_am48, y_am49) = a_am21
                                                (dx_am46, dy_am47) = v_am44
                                              in
                                                (Sum
                                                   $ (((x_am48 /+ dx_am46) / (y_am49 /+ dy_am47))
                                                        - (x_am48 / y_am49))) in
                                        let v_am4a = (a_am21 /+ v_am44)
                                        in (v_am45, func_am20 v_am4a)))
                  in func_am20 v_am1Y)))

*EILC EILC> let _  = $$( runIFq (runAppMono' aveDupDup) )
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 1 and #tenv2 = 1
Diff: #tenv1 = 2 and #tenv2 = 2
Diff: #tenv1 = 2 and #tenv2 = 2
Diff: #tenv1 = 3 and #tenv2 = 3
Diff: #tenv1 = 3 and #tenv2 = 3
Diff: #tenv1 = 4 and #tenv2 = 4
Diff: #tenv1 = 4 and #tenv2 = 4
Diff: #tenv1 = 5 and #tenv2 = 5
Diff: #tenv1 = 5 and #tenv2 = 5
<interactive>:21:14-43: Splicing expression
    runIFq (runAppMono' aveDupDup)
  ======>
    (ensureDiffType
       $ (\ pa_amIw pb_amIx a_amIy
            -> let v_amIz = (a_amIy, a_amIy) in
               let
                 v_amIA
                   = case v_amIz of {
                       (Bag xs_amIB, Bag ys_amIC) -> Bag (xs_amIB ++ ys_amIC) } in
               let v_amID = v_amIA in
               let v_amIE = (v_amID, v_amID) in
               let
                 v_amIF
                   = case v_amIE of {
                       (Bag xs_amIG, Bag ys_amIH) -> Bag (xs_amIG ++ ys_amIH) } in
               let v_amII = v_amIF in
               let v_amIJ = (v_amII, v_amII) in
               let
                 v_amIK
                   = case v_amIJ of {
                       (Bag xs_amIL, Bag ys_amIM) -> Bag (xs_amIL ++ ys_amIM) } in
               let v_amIN = v_amIK in
               let v_amIO = (v_amIN, v_amIN) in
               let
                 v_amIP
                   = case v_amIO of {
                       (Bag xs_amIQ, Bag ys_amIR) -> Bag (xs_amIQ ++ ys_amIR) } in
               let v_amIS = v_amIP in
               let v_amIT = case v_amIS of { Bag as_amIU -> sum as_amIU } in
               let v_amIV = case v_amIS of { Bag as_amIW -> length as_amIW } in
               let v_amIX = fromIntegral v_amIV :: Double in
               let v_amIY = (v_amIT, v_amIX) in
               let v_amIZ = (uncurry (/)) v_amIY
               in
                 (v_amIZ,
                  let
                    func_amJ0
                      = \ a_amJ1
                          -> ((mkInteraction pa_amIw) pb_amIx
                                $ (\ da_amJ2
                                     -> let v_amJ3 = (da_amJ2, da_amJ2) in
                                        let
                                          v_amJ4
                                            = case v_amJ3 of {
                                                (Bag dx_amJ5, Bag dy_amJ6)
                                                  -> Bag (dx_amJ5 ++ dy_amJ6) } in
                                        let v_amJ7 = v_amJ4 in
                                        let v_amJ8 = (v_amJ7, v_amJ7) in
                                        let
                                          v_amJ9
                                            = case v_amJ8 of {
                                                (Bag dx_amJa, Bag dy_amJb)
                                                  -> Bag (dx_amJa ++ dy_amJb) } in
                                        let v_amJc = v_amJ9 in
                                        let v_amJd = (v_amJc, v_amJc) in
                                        let
                                          v_amJe
                                            = case v_amJd of {
                                                (Bag dx_amJf, Bag dy_amJg)
                                                  -> Bag (dx_amJf ++ dy_amJg) } in
                                        let v_amJh = v_amJe in
                                        let v_amJi = (v_amJh, v_amJh) in
                                        let
                                          v_amJj
                                            = case v_amJi of {
                                                (Bag dx_amJk, Bag dy_amJl)
                                                  -> Bag (dx_amJk ++ dy_amJl) } in
                                        let v_amJm = v_amJj in
                                        let
                                          v_amJn
                                            = case v_amJm of {
                                                Bag as'_amJo -> Sum (sum as'_amJo) } in
                                        let
                                          v_amJp
                                            = case v_amJm of {
                                                Bag as_amJq -> Sum (length as_amJq) } in
                                        let v_amJr = Sum (fromIntegral (getSum v_amJp) :: Double) in
                                        let v_amJs = (v_amJn, v_amJr) in
                                        let
                                          v_amJt
                                            = let
                                                (x_amJw, y_amJx) = a_amJ1
                                                (dx_amJu, dy_amJv) = v_amJs
                                              in
                                                (Sum
                                                   $ (((x_amJw /+ dx_amJu) / (y_amJx /+ dy_amJv))
                                                        - (x_amJw / y_amJx))) in
                                        let v_amJy = (a_amJ1 /+ v_amJs)
                                        in (v_amJt, func_amJ0 v_amJy)))
                  in func_amJ0 v_amIY)))

-}


-- >>> let f = $$(runIFq (runAppMono' ave))
-- >>> let (res, tr) = f (Bag [1..100])
-- >>> res
-- >>> let dbs = iterations tr [Bag [1], Bag [2], Bag [30]]
-- >>> dbs
-- >>> res /+ mconcat dbs
-- 50.5
-- [Sum {getSum = -0.4900990099009874},Sum {getSum = -0.4706853038245029},Sum {getSum = -0.18970112316771548}]
-- 49.349514563106794

-- >>> let f = $$(runIFq (runAppMono' aveDupDup))
-- >>> let (res, tr) = f (Bag [1..100])
-- >>> res
-- >>> let dbs = iterations tr [Bag [1], Bag [2], Bag [30]]
-- >>> dbs
-- >>> res /+ mconcat dbs
-- 50.5
-- [Sum {getSum = -0.4900990099009874},Sum {getSum = -0.4706853038245029},Sum {getSum = -0.18970112316771548}]
-- 49.349514563106794


-- >>> let f = $$(runIFq (runAppMono' aveDupDup'))
-- >>> let (res, tr) = f (Bag [1..100])
-- >>> res
-- >>> let dbs = iterations tr [Bag [1], Bag [2], Bag [30]]
-- >>> dbs
-- >>> res /+ mconcat dbs
-- 50.5
-- [Sum {getSum = -0.4900990099009874},Sum {getSum = -0.4706853038245029},Sum {getSum = -0.18970112316771548}]
-- 49.349514563106794











