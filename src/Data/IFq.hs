{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.IFq where




{-
There are a few obvious sources of overhead (in the implementation of Data.IF)

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

import           Data.Functor.Identity (Identity (..))
import           Data.Kind             (Type)
import           Prelude               hiding (id, (.))


import           Data.Coerce           (coerce)
import           Data.Proxy            (Proxy (..))


import           Data.Code
import           Data.Delta
import           Data.Env
import           Data.Incrementalized
import           Data.Interaction
import           Language.Unembedding

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
  type K IFt = HasAtomicDelta
  id = IFt IsNoneTrue (\a -> (a, CNone)) (\da c -> (injDelta da, c))

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

{-
Then, let us focus on `IFt`. Here, we want to remove the cost of function compsotions.
Naively, we can think about the following datatype.

   data IFq a b = forall cs. IFt (IsNone cs) (Code a -> (Code b, Conn Code cs)) (Code (Delta a) -> Conn Code cs -> (Code (Delta b), Conn Code cs))

(Here, we ignore for simplicity that Code must be fully-applied.)

This is OK, but has a problem that we cannot share the computation between two `Code`.

A common workaround is to use a continuation monad, of which continuation intuitively represents a common context.
-}



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

-- ifqFromStateless :: (Code a -> Code b) -> (Code (Delta a) -> Code (Delta b)) -> IFq a b
-- ifqFromStateless f df = IFq CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df da) ; return (v, CNone) })

-- ifqFromD :: Diff a => (Code a -> Code b) -> (Code a -> Code (Delta a) -> Code (Delta b)) -> IFq a b
-- ifqFromD f df = IFq (CNE (COne Proxy))
--                     (\a -> do { v <- mkLet (f a) ; return (v, CNE (COne (PackedCode a))) })
--                     (\da (CNE (COne (PackedCode a))) -> do { v <- mkLet (df a da) ; a' <- mkLet [|| $$a /+ $$da ||] ; return (v, CNE (COne (PackedCode a'))) })

-- ifqFromFunctions :: Code (a -> (b, c)) -> Code (Delta a -> c -> (Delta b, c)) -> IFq a b
-- ifqFromFunctions f df =
--   IFq (CNE (COne Proxy))
--       (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
--       (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
--         [|| let (db, c') = $$df $$da $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

instance IncrementalizedQ IFq where
  fromStateless f df =
    IFq CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df da) ; return (v, CNone) })

  fromFunctions f df =
    IFq (CNE (COne Proxy))
        (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
        (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
          [|| let (db, c') = $$df $$da $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

  compile (IFq _ f tr) = runIFq f tr

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

mkAbsBang :: forall cs a. Conn Proxy cs -> (Conn PackedCode cs -> Code a) -> Code (Func cs a)
mkAbsBang CNone k    = k CNone
mkAbsBang (CNE cs) k = mkAbsBang' cs (k . CNE)

mkAbsBang' :: NEConn Proxy cs -> (NEConn PackedCode cs -> Code a) -> Code (Func' cs a)
mkAbsBang' (COne _) k      = [|| \ !a -> $$(k (COne $ PackedCode [|| a ||])) ||]
mkAbsBang' (CJoin c1 c2) k = mkAbsBang' c1 $ \c1' -> mkAbsBang' c2 $ \c2' -> k (CJoin c1' c2')


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



runIFq :: forall a b cs.
  (Code a -> CodeC (Code b, Conn PackedCode cs))
   -> (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
    -> Code (a -> (b, Interaction (Delta a) (Delta b) ))
runIFq = \f tr ->
                 [|| ensureDiffType $ \pa pb a ->
                         $$(toCode $ do (b, c) <- f [|| a ||]
                                        let rtr = mkRTr [|| pa ||] [|| pb ||] tr c
                                        return [|| ($$b, $$rtr) ||])
                  ||]
  where
    mkRTr :: forall cs'. Code (Proxy a) -> Code (Proxy b) -> (Code (Delta a) -> Conn PackedCode cs' -> CodeC (Code (Delta b), Conn PackedCode cs')) -> Conn PackedCode cs' -> Code (Interaction (Delta a) (Delta b))
    mkRTr pa pb tr c =
      [||
         let func = $$(mkAbsBang pc $ \cs ->
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

instance HasProduct IFq where
  type Unit IFq = ()
  type Prod IFq a b = (a, b)

  unitOk _ = Wit
  prodOk _ _ _ = Wit
