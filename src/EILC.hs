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
import           Data.Kind             (Constraint, Type)
import           Data.Monoid           (Sum (..))
import           Data.Typeable         (Proxy (..))
import           Prelude               hiding (id, (.))
import qualified Unsafe.Coerce         as Unsafe

import           Debug.Trace           (trace)
import qualified Language.Haskell.TH   as TH
import           Text.Printf           (printf)

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

data Env f as where
  ENil  :: Env f '[]
  ECons :: f a -> Env f as -> Env f (a ': as)

lenEnv :: Env f as -> Int
lenEnv ENil        = 0
lenEnv (ECons _ r) = 1 + lenEnv r

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
  - To use "difference lists" for c
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


-- runIFq :: forall a b. IFq a b -> Code (a -> (b, Interaction (Delta a) (Delta b) ))
-- runIFq =
--   \case (IFq _ f tr) ->
--           [||
--               let ff :: forall aa bb.  aa -> (bb, Interaction (Delta aa) (Delta bb))
--                   ff a = $$(toCode $ do { (b, c) <- f [|| a ||]
--                                         ; let mkRtr :: forall cs. (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs)) -> Conn PackedCode cs -> Code (Interaction (Delta a) (Delta b))
--                                               mkRtr tr c =
--                                                 [|| let func cp = Interaction $ \da ->
--                                                             $$(code2conn pc [|| cp ||] $ \cs ->
--                                                                 runCodeC (tr [|| da ||] cs) $ \(db, cs') -> [|| ($$db, func pa pb $$(conn2code cs')) ||])
--                                                     in

--                                         ; let rtr = mkRTr tr c
--                                         ; return [|| ($$b , $$rtr) ||] } )
--               in ff
--             ||]

ensureDiffType :: (Proxy a -> Proxy b -> a -> (b, Interaction (Delta a) (Delta b))) -> (a -> (b, Interaction (Delta a) (Delta b)))
ensureDiffType f = f Proxy Proxy

mkInteraction :: Proxy a -> Proxy b -> (Delta a -> (Delta b, Interaction (Delta a) (Delta b))) -> Interaction (Delta a) (Delta b)
mkInteraction _ _ = Interaction

eqProxy :: Proxy a -> Proxy a -> b -> b
eqProxy _ _ x = x

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
      [|| let func cp = mkInteraction $$pa $$pb $ \da ->
                            $$(code2conn pc [|| cp ||] $ \cs ->
                                runCodeC (tr [|| da ||] cs) $ \(db, cs') -> [|| ($$db, func $$(conn2code cs')) ||])
          in func $$(conn2code c) ||]
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

newtype Sem cat b = Sem { runSem :: forall as. Env Proxy as -> cat (Env Identity as) b }

class App cat e | e -> cat where
  lift :: cat a b -> e a -> e b
  unit :: e ()
  pair :: e a -> e b -> e (a, b)
  share :: e a -> (e a -> e b) -> e b


class Category cat => AppS cat where
  multS :: cat s a -> cat s b -> cat s (a, b)
  unitS :: cat s ()

  headS :: cat (Env Identity (a ': as)) a
  tailS :: cat (Env Identity (a ': as)) (Env Identity as)

  singletonS :: cat a (Env Identity '[a])

  econsS :: cat (a , Env Identity as) (Env Identity (a ': as))


instance AppS IFq where
  multS = multIFq
  unitS = IFq IsNoneTrue (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| () ||], CNone))

  headS = IFq IsNoneTrue
              (\as    -> do { v <- mkLet [|| case $$as of { ECons (Identity a) _ -> a } ||] ; return (v, CNone)})
              (\das _ -> do { vda <- mkLet [|| case $$das of { ECons (PackedDelta da) _ -> da } ||]; return (vda, CNone) } )

  tailS = IFq IsNoneTrue
              (\as    -> do { v <- mkLet [|| case $$as of { ECons _ as' -> as' } ||] ; return (v, CNone)})
              (\das _ -> do { v <- mkLet [|| case $$das of { ECons _ das' -> das' } ||]; return (v, CNone) } )

  singletonS = IFq IsNoneTrue
                   (\a  -> do { v <- mkLet [|| ECons (Identity $$a) ENil ||] ; return (v, CNone) })
                   (\da _ -> do { v <- mkLet [|| ECons (PackedDelta $$da) ENil ||] ; return (v, CNone) })

  econsS = IFq IsNoneTrue econs decons
    where
      econs x = do { v <- mkLet [|| case $$x of { (a, as) -> ECons (Identity a) as } ||]; return (v, CNone) }
      decons x _ = do { v <- mkLet [|| case $$x of { (da, das) -> ECons (PackedDelta da) das } ||]; return (v, CNone) }

instance AppS cat => App cat (Sem cat) where
  lift x (Sem e) = Sem $ \tenv -> x . e tenv

  unit = Sem $ const unitS
  pair (Sem e1) (Sem e2) = Sem $ \tenv -> multS (e1 tenv) (e2 tenv)

  share (Sem e0) k = Sem $ \tenv ->
    let tenva = ECons Proxy tenv
        arg = Sem $ \tenv' -> diffS tenva tenv' headS
    in runSem (k arg) tenva . econsS . multS (e0 tenv) id

diffS :: AppS cat => Env Proxy as -> Env Proxy bs -> cat (Env Identity as) a -> cat (Env Identity bs) a
diffS tenv1 tenv2 | trace (printf "Diff: #tenv1 = %d and #tenv2 = %d" (lenEnv tenv1) (lenEnv tenv2)) False = undefined
diffS tenv1 tenv2 =
  diff' (lenEnv tenv2 - lenEnv tenv1) tenv1 tenv2
  where
    diff' :: AppS cat => Int -> Env Proxy xs -> Env Proxy ys -> cat (Env Identity xs) a -> cat (Env Identity ys) a
    diff' 0 _ _ x             = Unsafe.unsafeCoerce x
    diff' n γ1 (ECons _ γ2) x = diff' (n-1) γ1 γ2 x . tailS
    diff' _ _ _ _             = error "Unreachable"

runAppMono :: AppS cat => (Sem cat a -> Sem cat b) -> cat a b
runAppMono f = runSem (f $ Sem $ \tenv -> diffS tenv1 tenv headS) tenv1 . singletonS
  where
    tenv1 = ECons Proxy ENil


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
       $ (\ pa_a18gW pb_a18gX a_a18gY
            -> let v_a18gZ = (ECons (Identity a_a18gY)) ENil in
               let
                 v_a18h0
                   = case v_a18gZ of { ECons (Identity a_a18h1) _ -> a_a18h1 } in
               let v_a18h2 = case v_a18h0 of { Bag as_a18h3 -> sum as_a18h3 } in
               let
                 v_a18h4
                   = case v_a18gZ of { ECons (Identity a_a18h5) _ -> a_a18h5 } in
               let
                 v_a18h6 = case v_a18h4 of { Bag as_a18h7 -> length as_a18h7 } in
               let v_a18h8 = fromIntegral v_a18h6 :: Double in
               let v_a18h9 = (v_a18h2, v_a18h8) in
               let v_a18ha = (uncurry (/)) v_a18h9
               in
                 (v_a18ha,
                  let
                    func_a18hb cp_a18hc
                      = ((mkInteraction pa_a18gW) pb_a18gX
                           $ (\ da_a18hd
                                -> let v_a18he = (DECons da_a18hd) DENil in
                                   let
                                     v_a18hf = case v_a18he of { DECons da_a18hg _ -> da_a18hg } in
                                   let
                                     v_a18hh
                                       = case v_a18hf of { Bag as'_a18hi -> Sum (sum as'_a18hi) } in
                                   let
                                     v_a18hj = case v_a18he of { DECons da_a18hk _ -> da_a18hk } in
                                   let
                                     v_a18hl
                                       = case v_a18hj of {
                                           Bag as_a18hm -> Sum (length as_a18hm) } in
                                   let v_a18hn = Sum (fromIntegral (getSum v_a18hl) :: Double) in
                                   let v_a18ho = (v_a18hh, v_a18hn) in
                                   let
                                     v_a18hp
                                       = let
                                           (x_a18hs, y_a18ht)
                                             = runIdentity (unCOne (unCNE cp_a18hc))
                                           (dx_a18hq, dy_a18hr) = v_a18ho
                                         in
                                           (Sum
                                              $ (((x_a18hs /+ dx_a18hq) / (y_a18ht /+ dy_a18hr))
                                                   - (x_a18hs / y_a18ht))) in
                                   let v_a18hu = (runIdentity (unCOne (unCNE cp_a18hc)) /+ v_a18ho)
                                   in (v_a18hp, func_a18hb (CNE (COne (Identity v_a18hu))))))
                  in func_a18hb (CNE (COne (Identity v_a18h9))))))

This code unfortunately does not type check due to the separate use of ECons and DECons; we are not able to know such intermediates
types are related by `Delta`.

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


class Category cat => Term unit prod cat (term :: [k] -> k -> Type) | term -> cat, cat -> term, term -> unit, term -> prod, cat -> unit, cat -> prod  where
  -- prop> mapTerm (f . g) = mapTerm f . mapTerm g
  mapTerm  :: cat a b -> term s a -> term s b

  multTerm :: term s a -> term s b -> term s (prod a b)
  unitTerm :: term s unit

  var0Term   :: term (a ': s) a
  weakenTerm :: term s a -> term (b ': s) a

  letTerm    :: term s a -> term (a ': s) b -> term s b
  unliftTerm :: term '[a] b -> cat a b

newtype TSem term b = TSem { runTSem :: forall as. Env Proxy as -> term as b }


instance Term () (,) cat term => App cat (TSem term) where
  lift x (TSem e) = TSem $ \tenv -> mapTerm x (e tenv)

  unit = TSem $ const unitTerm
  pair (TSem e1) (TSem e2) = TSem $ \tenv -> multTerm (e1 tenv) (e2 tenv)

  share (TSem e0) k = TSem $ \tenv ->
    let tenva = ECons Proxy tenv
        arg = TSem $ \tenv' -> diffT tenva tenv' var0Term
    in letTerm (e0 tenv) (runTSem (k arg) tenva)

diffT :: Term unit prod cat term => Env Proxy as -> Env Proxy bs -> term as a -> term bs a
diffT tenv1 tenv2 | trace (printf "Diff: #tenv1 = %d and #tenv2 = %d" (lenEnv tenv1) (lenEnv tenv2)) False = undefined
diffT tenv1 tenv2 =
  diff' (lenEnv tenv2 - lenEnv tenv1) tenv1 tenv2
  where
    diff' :: Term unit prod cat term => Int -> Env Proxy xs -> Env Proxy ys -> term xs a -> term ys a
    diff' 0 _ _ x             = Unsafe.unsafeCoerce x
    diff' n γ1 (ECons _ γ2) x = weakenTerm $ diff' (n-1) γ1 γ2 x
    diff' _ _ _ _             = error "Unreachable"

runAppMono' :: Term unit prod cat term => (TSem term a -> TSem term b) -> cat a b
runAppMono' f = unliftTerm $ runTSem (f $ TSem $ \tenv -> diffT tenv1 tenv var0Term) tenv1
  where
    tenv1 = ECons Proxy ENil

newtype PackedCodeDelta a = PackedCodeDelta { getCodeDelta :: Code (Delta a) }

data IFqT as b =
  forall cs. IFqT (IsNone cs)
                  (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
                  (Env PackedCodeDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

instance Term () (,) IFq IFqT where
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

  letTerm (IFqT isNone1 f1 tr1) (IFqT isNone2 f2 tr2) = IFqT (isNoneAnd isNone1 isNone2) f tr
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













