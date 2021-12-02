{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
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
module Data.IFq (
  IFqS(..), IFq(..), convTEnv,

  fstF, sndF,

  -- * Exporting for spliced code
  mkInteraction, ensureDiffType,
  ) where


import           Prelude              hiding (id, (.))

import           Data.Coerce          (coerce)
import           Data.Proxy           (Proxy (..))
import           Data.Typeable        (Typeable)


import           Data.Code
import           Data.Code.Lifting
import           Data.Conn
import           Data.Delta
import           Data.Env
import           Data.Incrementalized
import           Data.Interaction
import           Language.Unembedding


-- mkLetConn :: Conn PackedCode cs -> CodeC (Conn PackedCode cs)
-- mkLetConn CNone = return CNone
-- mkLetConn (CNE e) = CNE <$> mkLetConn' e
--   where
--     mkLetConn' :: NEConn PackedCode cs -> CodeC (NEConn PackedCode cs)
--     mkLetConn' (COne a)      = COne . PackedCode <$> mkLet (coerce a)
--     mkLetConn' (CJoin c1 c2) = CJoin <$> mkLetConn' c1 <*> mkLetConn' c2


data CodeInteractionStep a b =
  forall cs. CodeInteractionStep (Conn PackedCode cs) (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

data IFq a b where
  IFq :: (Code a -> CodeC (Code b, CodeInteractionStep a b))  -> IFq a b


convTEnv :: AllIn as DiffTypeable => Env proxy as -> Env WitTypeable as
convTEnv ENil         = ENil
convTEnv (ECons _ as) = ECons WitTypeable (convTEnv as)
instance CategoryK IFq where
  type K IFq = DiffTypeable

  id = IFq $ \a -> do
    return (a, CodeInteractionStep CNone (\da _ -> return (da, CNone)))

  IFq h2 . IFq h1 = IFq $ \a -> do
    (b, CodeInteractionStep c1init step1) <- h1 a
    (c, CodeInteractionStep c2init step2) <- h2 b
    let step da cc | (c1, c2) <- decompConn (isNone c1init) (isNone c2init) cc = do
          (db, c1') <- step1 da c1
          (dc, c2') <- step2 db c2
          return (dc, joinConn c1' c2')
    return (c, CodeInteractionStep (joinConn c1init c2init) step)


  -- IFq sh2 f2 tr2 . IFq sh1 f1 tr1 = IFq (joinConn sh1 sh2) f tr
  --   where
  --     f a = do
  --       (b, c1) <- f1 a
  --       (c, c2) <- f2 b
  --       return (c, joinConn c1 c2)

  --     tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
  --       (dbs, c1') <- tr1 da c1
  --       (dcs, c2') <- tr2 dbs c2
  --       return (dcs, joinConn c1' c2')


instance IncrementalizedQ IFq where
  type CodeType IFq = PackedCode

  fromStateless f df = IFq $ \a -> do
    v <- mkLet (coerce f a)
    return (v, CodeInteractionStep CNone step)
    where
      step da _ = do
        v <- mkLet (coerce df da)
        return (v, CNone)

--    IFq CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df da) ; return (v, CNone) })

  fromFunctions _ f df = IFq $ \a -> do
    (b, c0) <- CodeC $ \k -> [||
        let (b, c) = $$(unPackCode f) $$a
        in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))))
      ||]
    let step da (CNE (COne (PackedCode c))) = CodeC $ \k ->
          [||
             let (db, c') = $$(unPackCode df) $$da $$c
             in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||]))))
           ||]
    return (b, CodeInteractionStep c0 step)

    -- IFq (CNE (COne WitTypeable))
    --     (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
    --     (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
    --       [|| let (db, c') = $$df $$da $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

  compile (IFq h) = PackedCode [|| \a -> $$(toCode $ do
            (b, CodeInteractionStep c0 step) <- h [|| a ||]
            i <- CodeC $ \k -> [||
                  let int = $$(mkAbsBang c0 $ \cs ->
                                [|| Interaction $ \da ->
                                        $$(runCodeC (step [|| da ||] cs) $ \(db, cs') -> [|| ($$db, $$(mkApp [|| int ||] cs')) ||])
                                 ||])
                  in $$(k (mkApp [|| int ||] c0))
                 ||]
            return [|| ($$b, $$i) ||]
        )
    ||]

multIFq :: IFq s a -> IFq s b -> IFq s (a, b)
multIFq (IFq h1) (IFq h2) = IFq $ \s -> do
  (a, CodeInteractionStep c1init step1) <- h1 s
  (b, CodeInteractionStep c2init step2) <- h2 s
  let step ds cc | (c1, c2) <- decompConn (isNone c1init) (isNone c2init) cc = do
        (da, c1') <- step1 ds c1
        (db, c2') <- step2 ds c2
        r <- mkLet [|| pairDelta $$da $$db ||]
        return (r, joinConn c1' c2')
  r <- mkLet [|| ($$a , $$b) ||]
  return (r, CodeInteractionStep (joinConn c1init c2init) step)



ensureDiffType :: (Proxy a -> Proxy b -> a -> (b, Interaction (Delta a) (Delta b))) -> (a -> (b, Interaction (Delta a) (Delta b)))
ensureDiffType f = f Proxy Proxy

mkInteraction :: Proxy a -> Proxy b -> (Delta a -> (Delta b, Interaction (Delta a) (Delta b))) -> Interaction (Delta a) (Delta b)
mkInteraction _ _ = Interaction

-- eqProxy :: Proxy a -> Proxy a -> b -> b
-- eqProxy _ _ x = x

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
  unitS = fromStatelessCode (const [|| () ||]) (const [|| mempty ||])
    -- IFq CNone (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| mempty ||], CNone))

  fstS _ _ = fromStatelessCode
              (\as -> [|| fst $$as ||])
              (\das -> [|| fstDelta $$das ||])

  sndS _ _ = fromStatelessCode
              (\as  -> [|| snd $$as ||])
              (\das -> [|| sndDelta $$das ||])

--   fstS _ _ = IFq CNone
--                 (\as    -> do { v <- mkLet [|| fst $$as  ||] ; return (v, CNone)})
--                 (\das _ -> do { v <- mkLet [|| fstDelta $$das ||] ; return (v, CNone) })
-- --                (\das _ -> do { vda <- mkLet [|| fst $$das ||]; return (vda, CNone) } )

--   sndS _ _ = IFq CNone
--                 (\as    -> do { v <- mkLet [|| snd $$as ||] ; return (v, CNone)})
--                 (\das _ -> do { v <- mkLet [|| sndDelta $$das ||] ; return (v, CNone) })
-- --                (\das _ -> do { vda <- mkLet [|| snd $$das ||]; return (vda, CNone) } )

instance HasProduct IFq where
  type Unit IFq = ()
  type Prod IFq = (,)

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
  type Prod IFqS = (,)

  unitOk _ = Wit
  prodOk _ _ _ = Wit

instance Cartesian IFqS where
  multS (IFqS sh1 m1) (IFqS sh2 m2) = IFqS (joinConn sh1 sh2) $ do
    (f1, tr1) <- m1
    (f2, tr2) <- m2
    let f s = do
          (a, c1) <- f1 s
          (b, c2) <- f2 s
          return ([|| ($$a, $$b) ||], joinConn c1 c2)

        tr ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
                     (da, c1') <- tr1 ds c1
                     (db, c2') <- tr2 ds c2
                     return ([|| pairDelta $$da $$db ||], joinConn c1' c2')

    return (f, tr)

  unitS = fromStatelessCode (const [|| () ||]) (const [|| mempty ||])
    -- IFq CNone (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| mempty ||], CNone))

  fstS _ _ = fromStatelessCode
              (\as -> [|| fst $$as ||])
              (\das -> [|| fstDelta $$das ||])

  sndS _ _ = fromStatelessCode
              (\as  -> [|| snd $$as ||])
              (\das -> [|| sndDelta $$das ||])


instance IncrementalizedQ IFqS where
  type CodeType IFqS = PackedCode

  fromStateless f df =
    IFqS CNone $
      return (\a -> do { v <- mkLet (coerce f a); return (v, CNone) },
              \da _ -> do { v <- mkLet (coerce df da) ; return (v, CNone) })

  fromFunctions _ (PackedCode f) (PackedCode df) =
    IFqS (CNE (COne WitTypeable)) $
      return
        (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||],
         \da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
           [|| let (db, c') = $$df $$da $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

  compile (IFqS _ m) = PackedCode $ toCode $ do
    (f, tr) <- m
    return $ runIFq f tr

fstF :: forall e a b. (Diff a, Typeable a, Diff b, Typeable b, App IFqS e) => e (a, b) -> e a
fstF = lift (fstS Proxy Proxy)

sndF :: forall e a b. (Diff a, Typeable a, Diff b, Typeable b, App IFqS e) => e (a, b) -> e b
sndF = lift (sndS Proxy Proxy)

