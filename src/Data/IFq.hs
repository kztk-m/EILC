{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
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
import           Data.Code.Lifting
import           Data.Conn
import           Data.Delta
import           Data.Env
import           Data.Incrementalized
import           Data.Interaction
import           Data.Typeable         (Typeable)
import           Language.Unembedding



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








-- data IFq a b =
--   forall cs.
--     IFq (Conn Proxy cs)
--         (Code a -> CodeC (Code b, Conn PackedCode cs))
--         (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

data IFq a b where
  IFq :: Conn WitTypeable cs -> (Code a -> CodeC (Code b, Conn PackedCode cs)) -> (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs)) -> IFq a b


convTEnv :: AllIn as DiffTypeable => Env proxy as -> Env WitTypeable as
convTEnv ENil         = ENil
convTEnv (ECons _ as) = ECons WitTypeable (convTEnv as)
instance CategoryK IFq where
  type K IFq = DiffTypeable
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
    IFq (CNE (COne WitTypeable))
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



data IFqS a b where
  IFqS :: Conn WitTypeable cs -> CodeC (Code a -> CodeC (Code b, Conn PackedCode cs), Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs)) -> IFqS a b

instance CategoryK IFqS where
  type K IFqS = DiffTypeable

  id = IFqS CNone $
        return (\a -> return (a, CNone),
                \da _ -> return (da , CNone))

  IFqS sh2 m2 . IFqS sh1 m1 = IFqS (joinConn sh1 sh2) $ do
    (f1, tr1) <- m1
    (f2, tr2) <- m2
    let
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (dbs, c1') <- tr1 da c1
        (dcs, c2') <- tr2 dbs c2
        return (dcs, joinConn c1' c2')
    return (f , tr)


instance HasProduct IFqS where
  type Unit IFqS = ()
  type Prod IFqS a b = (a, b)

  unitOk _ = Wit
  prodOk _ _ _ = Wit

instance IncrementalizedQ IFqS where
  fromStateless f df =
    IFqS CNone $
      return (\a -> do { v <- mkLet (f a); return (v, CNone) },
              \da _ -> do { v <- mkLet (df da) ; return (v, CNone) })

  fromFunctions f df =
    IFqS (CNE (COne WitTypeable)) $
      return
        (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||],
         \da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
           [|| let (db, c') = $$df $$da $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

  compile (IFqS _ m) = toCode $ do
    (f, tr) <- m
    return $ runIFq f tr
