-- {-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}


module Data.IFFT where

import           Data.Typeable        (Proxy (..))

import           Data.Code
import           Data.Delta           (Delta, Diff, DiffTypeable, pairDelta)
import           Data.Env             (AllIn, Env (..))
import           Language.Unembedding (CategoryK (..), HasProduct (..),
                                       LetTerm (..), Term (..), Wit (Wit))

import           Data.Code.Lifting    (DFunc)
import           Data.Incrementalized (IncrementalizedQ (..))
import           Data.Interaction     (Interaction (..))

{-# ANN module "HLint: ignore Use tuple-section" #-}

-- newtype PackedDelta a = PackedDelta (Delta a)
data PackedDelta a where
  PackedDelta :: Diff a => Delta a -> PackedDelta a



newtype InteractionT as b =
  InteractionT { runInteractionT :: DFunc as (b, InteractionT as b) }



data IFFT as b =
  IFFT
    !(Env Proxy as)
    !(Env PackedCode as -> CodeC (Code b, Code (Interaction (Env PackedDelta as) (Delta b))))

-- data IFFT as b =
--   IFFT
--     !(Env Proxy as)
--     !(Env PackedCode as -> CodeC (Code b, Code (InteractionT as (Delta b))))


newtype IFF a b =
  IFF (Code a -> CodeC (Code b, Code (Interaction (Delta a) (Delta b))))

idInteraction :: Interaction a a
idInteraction = Interaction $ \a -> (a, idInteraction)
{-# INLINABLE idInteraction #-}

composeInteraction :: Interaction b c -> Interaction a b -> Interaction a c
composeInteraction i2 i1 = Interaction $ \a ->
  let (b, i1') = runInteraction i1 a
      (c, i2') = runInteraction i2 b
  in (c, composeInteraction i2' i1')
{-# INLINABLE composeInteraction #-}

instance CategoryK IFF where
  type K IFF = DiffTypeable

  id = IFF $ \a -> return (a, [|| idInteraction ||])
  IFF h2 . IFF h1 = IFF $ \a -> do
    (b, i1) <- h1 a
    (c, i2) <- h2 b
    return (c, [|| composeInteraction $$i2 $$i1 ||])



instance HasProduct IFF where
  type Unit IFF = ()
  type Prod IFF a b = (a, b)

  unitOk _ = Wit
  prodOk _ _ _ = Wit

staticInteraction :: (a -> b) -> Interaction a b
staticInteraction f = Interaction $ \a ->
  (f a, staticInteraction f)

unfoldI :: c -> (a -> c -> (b, c)) -> Interaction a b
unfoldI seed0 step = go seed0
  where
    go s = Interaction $ \a ->
      let (b, s') = step a s
      in (b, go s')



instance IncrementalizedQ IFF where
  fromStateless f df = IFF $ \a -> do
    b <- mkLet $ f a
    return (b, [|| staticInteraction (\da -> $$(df [|| da ||])) ||])

  fromFunctions f df = IFF $ \a -> do
    (b, c) <- CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], [|| c ||])) ||]
    return (b, [|| unfoldI $$c $$df ||] )

  compile (IFF h) = [|| \a -> $$(runCodeC (h [|| a ||]) $ \(b, i) -> [|| ($$b, $$i) ||]) ||]




-- mkInt ::
--   forall as a b cs.
--   (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
--   -> Code (Interaction (Env PackedDelta as) (Delta a))
--   -> Conn PackedCode cs
--   -> Code (Interaction (Env PackedDelta as) (Delta b))
-- mkInt tr ia0 cs0 =
--   [||
--     let intr ia = $$(mkAbs sh $ \cs ->
--           [|| Interaction $ \denv ->
--                 let (da, ia') = runInteraction ia denv
--                 in $$(runCodeC (tr [|| da ||] cs) $ \(db, cs') ->
--                     [|| ($$db, $$(mkApp [|| intr ia' ||] cs')) ||]
--                   )
--           ||])
--     in $$(mkApp [|| intr  $$ia0 ||] cs0)
--   ||]
--   where
--     sh = map2Conn (const Proxy) cs0

alwaysUnit :: Monoid m => Interaction s m
alwaysUnit = Interaction $ const (mempty , alwaysUnit)
{-# INLINABLE alwaysUnit #-}

pairInteraction ::
  Interaction s (Delta a) -> Interaction s (Delta b) -> Interaction s (Delta (a, b))
pairInteraction ia ib = Interaction $ \denv ->
  let (da, ia') = runInteraction ia denv
      (db, ib') = runInteraction ib denv
  in (pairDelta da db, pairInteraction ia' ib')
{-# INLINABLE pairInteraction #-}

var0Interaction :: Interaction (Env PackedDelta (a ': s)) (Delta a)
var0Interaction = Interaction $ \(ECons (PackedDelta da) _) ->
  (da, var0Interaction)
{-# INLINABLE var0Interaction #-}

weakenInteraction ::
  Interaction (Env f s) a
  -> Interaction (Env f (b : s)) a
weakenInteraction i = Interaction $ \(ECons _ denv) ->
  let (da, i') = runInteraction i denv
  in (da, weakenInteraction i')

unliftInteraction ::
  Diff a =>
  Interaction (Env PackedDelta '[a]) (Delta b)
  -> Interaction (Delta a) (Delta b)
unliftInteraction i = Interaction $ \da ->
  let (b, i') = runInteraction i (ECons (PackedDelta da) ENil)
  in (b, unliftInteraction i')


-- instance Term IFF IFFT where
--   mapTerm (IFF h2) (IFFT tenv h1) = IFFT tenv $ \env -> do
--     (a, i1) <- h1 env
--     (b, i2) <- h2 a
--     i <- CodeC $ \k -> [||
--           let mapTermIntWork j1 j2 = InteractionT $$(mkAbsD tenv $ \s -> [||
--                 let (da, j1') = $$(mkAppD [|| runInteractionT j1 ||] s)
--                     (db, j2') = runInteraction j2 da
--                 in (db, mapTermIntWork j1' j2') ||])
--               mapTermInt = mapTermIntWork $$i1 $$i2
--           in $$(k [|| mapTermInt ||])
--       ||]
--     return (b, i)

--   multTerm :: forall s a b. AllIn s Diff => IFFT s a -> IFFT s b -> IFFT s (a, b)
--   multTerm (IFFT tenv h1) (IFFT _ h2) = IFFT tenv $ \env -> do
--     (a, i1) <- h1 env
--     (b, i2) <- h2 env
--     i <- CodeC $ \k -> [||
--           let multTermIntWork j1 j2 = InteractionT $$(mkAbsD @s @(Delta (a, b), InteractionT s (Delta (a, b))) tenv $ \s -> [||
--                 let (da, j1') = $$(mkAppD [|| runInteractionT j1 ||] s)
--                     (db, j2') = $$(mkAppD [|| runInteractionT j2 ||] s)
--                 in (pairDelta da db, multTermIntWork j1' j2') ||])
--               multTermInt = multTermIntWork $$i1 $$i2
--           in $$(k [|| multTermInt ||])
--       ||]
--     return ([|| ($$a, $$b) ||], i )

--   unitTerm tenv = IFFT tenv $ \env -> do
--     i <- CodeC $ \k -> [||
--           let unitTermIntWork = InteractionT $$(mkAbsD tenv $ \s ->

--       ||]

--   var0Term = _
--   weakenTerm = _
--   unliftTerm = _

letInteraction ::
  Diff a =>
  Interaction (Env PackedDelta s) (Delta a)
  -> Interaction (Env PackedDelta (a : s)) (Delta b)
  -> Interaction (Env PackedDelta s) (Delta b)
letInteraction i1 i2 = Interaction $ \s ->
  let (a, i1') = runInteraction i1 s
      (b, i2') = runInteraction i2 (ECons (PackedDelta a) s)
  in (b, letInteraction i1' i2')


instance Term IFF IFFT where
  -- mapTerm (IFq _ f2 tr2) (IFFT tenv h1) = IFFT tenv $ \env -> do
  --   (a, ia0) <- h1 env
  --   (b, cs0) <- f2 a
  --   it <- mkLet $ mkInt tr2 ia0 cs0
  --   return (b, it)

  mapTerm (IFF h2) (IFFT tenv h1) = IFFT tenv $ \env -> do
    (a, i1) <- h1 env
    (b, i2) <- h2 a
    return (b, [|| composeInteraction $$i2 $$i1 ||])

  multTerm (IFFT tenv h1) (IFFT _ h2) = IFFT tenv $ \env -> do
    (a, ia0) <- h1 env
    (b, ib0) <- h2 env
    return ( [|| ($$a, $$b) ||], [|| pairInteraction $$ia0 $$ib0 ||] )

  unitTerm tenv = IFFT tenv $ \_ ->
    return ([|| () ||], [|| alwaysUnit ||])

  var0Term tenv = IFFT (ECons Proxy tenv) $ \(ECons (PackedCode a) _) ->
    return ([|| $$a ||], [|| var0Interaction ||])

  weakenTerm (IFFT tenv h) = IFFT (ECons Proxy tenv) $ \(ECons _ as) -> do
    (da, ia') <- h as
    return (da, [|| weakenInteraction $$ia' ||])

  unliftTerm (IFFT _ h) = IFF $ \a -> do
    (b, i) <- h (ECons (PackedCode a) ENil)
    return (b, [|| unliftInteraction $$i ||])

instance LetTerm IFF IFFT where
  letTerm (IFFT tenv h1) (IFFT _ h2) = IFFT tenv $ \env -> do
    (a, i1) <- h1 env
    (b, i2) <- h2 (ECons (PackedCode a) env)
    return (b, [|| letInteraction $$i1 $$i2 ||])

