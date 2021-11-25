{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE InstanceSigs          #-}

module Data.Incrementalized.Function (
    toDynI, fromDynI, -- trDFunT,
    -- FunT(..), type Delta (..), IsEmpty(..),
    ensureSameType,
    PFun(..), type Delta (..), FunD
  ) where

import           Data.Dynamic                        (Dynamic, fromDynamic,
                                                      toDyn)
import           Data.Functor.Identity               (Identity (..))
import           Data.Maybe                          (fromJust)
import           Data.Typeable                       (Proxy (..), Typeable)


import           Control.Arrow                       (Arrow (second))

import           Data.Code
import           Data.Code.Lifting
import           Data.Conn
import           Data.Delta                          (Delta (PairDelta),
                                                      Diff (..), DiffTypeable,
                                                      nilChangeOf)
import           Data.Env                            (AllIn, Env (..), mapEnv)

import           Data.IFq                            (IFqS (..))
import           Data.IFqT                           (IFqT (..))


import           Language.Unembedding                hiding (Fun)
import           Language.Unembedding.PseudoFunction

import           Data.Function
import           Data.IFqTU                          (Extr, IFqTU (..),
                                                      SBool (..), SafeTail,
                                                      extendEnv, extractEnv,
                                                      safeTail, witExtr)
import           Data.JoinList

{-
See ./note/meeting_doc_Nov_2021.
-}


-- type MyState s a = s -> (a, s)




-- data FunD a b =
--   FunD !(a -> (b, Dynamic))
--        !(Delta a -> MyState Dynamic (Delta b)) -- must satisfy tr 0 d = (0, d)

-- data instance Delta (FunD a b) =
--   DFunD { dfunIsEmpty :: !Bool,
--           dfunTrNN :: !(MyState Dynamic (Delta b)) }

-- instance Semigroup (Delta b) => Semigroup (Delta (FunD a b)) where
--   DFunD b1 dfNN1 <> DFunD b2 dfNN2 = DFunD (b1 && b2) $ \s ->
--     let (db1, s1) = dfNN1 s
--         (db2, s2) = dfNN2 s1
--     in (db1 <> db2, s2)

-- instance Monoid (Delta b) => Monoid (Delta (FunD a b)) where
--   mempty = DFunD True (\s -> (mempty , s))

-- instance (Diff a, Diff b) => Diff (FunD a b) where
--   FunD f ftr /+ DFunD True _ = FunD f ftr
--   FunD f ftr /+ DFunD _ ftr' = FunD (\a -> let (b, s) = f a in
--                                            let (db, s') = ftr' s in
--                                              (b /+ db, s')) ftr

--   checkEmpty (DFunD b _) = b

  -- emptify (DFunD _ ftr) = DFunD True $ \a -> first emptify $ ftr a

  -- emptyOf (FunD _ ftr) = DFunD True $ \(c,a) -> ftr (emptyOf a) (c, a)

type FunD = PFun IFqS Dynamic

toDynI :: Typeable cs => Env Identity cs -> Dynamic
toDynI = toDyn

fromDynI :: Typeable cs => Dynamic -> Env Identity cs
fromDynI = fromJust Prelude.. fromDynamic

allEmptyDelta :: forall xs. Env PackedCodeDelta xs -> Code Bool
allEmptyDelta ENil = [|| True ||]
allEmptyDelta (ECons (PackedCodeDelta da) ENil) = [|| checkEmpty $$da ||]
allEmptyDelta (ECons (PackedCodeDelta da) das)  = [|| checkEmpty $$da && $$(allEmptyDelta das) ||]

ensureSameType :: a -> a -> ()
ensureSameType _ _ = ()

data instance Delta (PFun IFqS c a b) = DeltaPFun Bool !(c -> (Delta b, c))

instance Semigroup (Delta b) => Semigroup (Delta (PFun IFqS c a b)) where
  DeltaPFun b1 df1 <> DeltaPFun b2 df2 = DeltaPFun (b1 && b2) $ \c ->
    let (db1, c1) = df1 c
        (db2, c2) = df2 c1
    in (db1 <> db2, c2)

instance Monoid (Delta b) => Monoid (Delta (PFun IFqS c a b)) where
  mempty = DeltaPFun True $ \c -> (mempty, c)

instance Diff b => Diff (PFun IFqS c a b) where
  f /+ DeltaPFun True _ = f
  PFun f derive_f /+ DeltaPFun _ df = PFun f' derive_f
    where
      f' a = let
              (b, c) = f a
              (db, c') = df c
             in (b /+ db, c')

  checkEmpty (DeltaPFun b _) = b


type ConnSingle f t = Conn f ('JLNonEmpty ('JLSingle t))


pAppImpl ::
  forall as c a b.
  (AllIn as DiffTypeable, DiffTypeable a, DiffTypeable b, Typeable c) =>
  Env WitTypeable as ->
  IFqT (PFun IFqS c a b ': a ': as) b
pAppImpl tenv = IFqT (ECons WitTypeable (ECons WitTypeable tenv)) sh $ do
  let
    ff :: Env PackedCodeDiff (PFun IFqS c a b ': a ': as)
          -> CodeC (Code b, ConnSingle PackedCode (c, Delta a -> c -> (Delta b, c)))
    ff (ECons (PackedCodeDiff pf) (ECons (PackedCodeDiff a) _)) = do
      (b, cc) <- CodeC $ \k -> [||
          let PFun f deriv_f = $$pf
              (b, c) = f $$a
          in $$(k ([|| b ||], [|| (c, deriv_f) ||]))
        ||]
      return (b, CSingle $ PackedCode cc)

    tr_ff :: Env PackedCodeDelta (PFun IFqS c a b ': a ': as)
            -> ConnSingle PackedCode (c, Delta a -> c -> (Delta b, c))
            -> CodeC (Code (Delta b), ConnSingle PackedCode (c, Delta a -> c -> (Delta b, c)))
    tr_ff (ECons (PackedCodeDelta pdf) (ECons (PackedCodeDelta da) _)) (CNE (COne (PackedCode cc))) = CodeC $ \k ->
      [||
          let (c, deriv_f) = $$cc
              DeltaPFun b df = $$pdf
              (db1, c1) = if b then (mempty, c) else df c
              (db2, c2) = deriv_f $$da c1
              db = db1 <> db2
          in $$(k ([|| db ||], CSingle $ PackedCode [|| (c2, deriv_f) ||]))
      ||]


  return (ff, tr_ff)
  where
    sh = CSingle WitTypeable

fromDyn :: Typeable a => Dynamic -> a
fromDyn = fromJust Prelude.. fromDynamic

toDynIF :: Typeable c => IFqS (PFun IFqS c a b) (FunD a b)
toDynIF = IFqS CNone (return (\a -> return (ff a, CNone), \da _ -> return (tr_ff da, CNone)))
  where
    ff a = [|| let PFun f deriv_f = $$a
               in PFun (second toDyn Prelude.. f) (\da d -> second toDyn $ deriv_f da (fromJust $ fromDynamic d)) ||]

    tr_ff x = [|| let DeltaPFun b df = $$x
                  in DeltaPFun b (\d -> second toDyn $ df (fromJust $ fromDynamic d)) ||]

fromDynIF :: IFqS (FunD a b) (PFun IFqS Dynamic a b)
fromDynIF = IFqS CNone (return (\a -> return (a, CNone), \da _ -> return (da, CNone)))

asType :: a -> a -> a
asType a _ = a

data instance PFun IFqS c a b = PFun !(a -> (b, c)) !(Delta a -> c -> (Delta b, c))
instance PFunTerm IFqS IFqT where
  type KK IFqS = Typeable

  pAbsTerm (IFqT (ECons _ tenv) (sh :: Conn WitTypeable cs) m) kk = case wit of
    Wit -> kk $ IFqT tenv CNone $ do
        (f, tr) <- m
        lamTr :: Code (Delta a -> Env Identity (Flatten cs) -> DFunc as (Delta b, Env Identity (Flatten cs))) <-
            mkLetMono [||
                  -- inefficiency: denv may contain unused variables.
                  \da c -> $$(mkAbsD tenv $ \denv -> toCode $ do
                      cs <- CodeC $ cenv2conn sh [|| c ||]
                      (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) denv) cs
                      return [|| ($$db, $$(conn2cenv cs') `asType` c) ||])
                ||]
        let
          h ::  Env PackedCodeDiff as -> Code (PFun IFqS (Env Identity (Flatten cs)) a b)
          h env =
            [|| PFun (\a -> $$(toCode $ do
                        (b, cs) <- f (ECons (PackedCodeDiff [|| a ||]) env)
                        return [|| ($$b, $$(conn2cenv cs) ) ||]))
                      (\da c ->
                          let (db, c') = $$(mkAppD [|| $$lamTr da c ||] $ mapEnv (\(PackedCodeDiff a) -> PackedCodeDelta [|| nilChangeOf $$a ||]) env)
                          in (db, c'))
            ||]

          trh :: Env PackedCodeDelta as -> Code (Delta (PFun IFqS (Env Identity (Flatten cs)) a b))
          trh denv =  [||
              DeltaPFun $$(allEmptyDelta denv) $ \d ->
                let (db, d') = $$(mkAppD [|| $$lamTr mempty d ||] denv)
                in (db, d')
              ||]
        return (\env -> return (h env, CNone),
                \denv _ -> return (trh denv, CNone))
    where
      wit :: Wit (Typeable (Flatten cs))
      wit = witTypeableFlatten sh

      mkLetMono :: Code a -> CodeC (Code a)
      mkLetMono e = CodeC $ \k -> [|| $$e & \lamTr -> $$(k [|| lamTr ||]) ||]

  pAppTerm t1@(IFqT tenv _ _) t2 =
    letTerm t2 $ letTerm (weakenTerm t1) $ pAppImpl tenv


pAppImplU ::
  forall as c a b.
  (AllIn as DiffTypeable, DiffTypeable a, DiffTypeable b, Typeable c) =>
  Env WitTypeable as ->
  IFqTU (PFun IFqS c a b ': a ': as) b
pAppImplU tenv = IFqTU (ECons WitTypeable (ECons WitTypeable tenv)) sh (ECons STrue $ ECons STrue ENil) $ do
  let
    ff :: Env PackedCodeDiff (PFun IFqS c a b ': a ': '[])
          -> CodeC (Code b, ConnSingle PackedCode (c, Delta a -> c -> (Delta b, c)))
    ff (ECons (PackedCodeDiff pf) (ECons (PackedCodeDiff a) _)) = do
      (b, cc) <- CodeC $ \k -> [||
          let PFun f deriv_f = $$pf
              (b, c) = f $$a
          in $$(k ([|| b ||], [|| (c, deriv_f) ||]))
        ||]
      return (b, CSingle $ PackedCode cc)

    tr_ff :: Env PackedCodeDelta (PFun IFqS c a b ': a ': '[])
            -> ConnSingle PackedCode (c, Delta a -> c -> (Delta b, c))
            -> CodeC (Code (Delta b), ConnSingle PackedCode (c, Delta a -> c -> (Delta b, c)))
    tr_ff (ECons (PackedCodeDelta pdf) (ECons (PackedCodeDelta da) _)) (CNE (COne (PackedCode cc))) = CodeC $ \k ->
      [||
          let (c, deriv_f) = $$cc
              DeltaPFun b df = $$pdf
              (db1, c1) = if b then (mempty, c) else df c
              (db2, c2) = deriv_f $$da c1
              db = db1 <> db2
          in $$(k ([|| db ||], CSingle $ PackedCode [|| (c2, deriv_f) ||]))
      ||]


  return (ff, tr_ff)
  where
    sh = CSingle WitTypeable


instance PFunTerm IFqS IFqTU where
  type KK IFqS = Typeable

  pAbsTerm (IFqTU (ECons _ (tenv :: Env WitTypeable as)) (sh :: Conn WitTypeable cs) (u :: Env SBool us) m) kk = case (wit, wit2) of
    (Wit, Wit) -> kk $ IFqTU tenv CNone u' $ do
      (f, tr) <- m
      lamTr :: Code (Delta a -> Env Identity (Flatten cs) -> DFunc (Extr as (SafeTail us)) (Delta b, Env Identity (Flatten cs))) <-
        mkLetMono [||
                  \da c -> $$(mkAbsD (extractEnv tenv u') $ \denv -> toCode $ do
                      cs <- CodeC $ cenv2conn sh [|| c ||]
                      (db, cs') <- tr (extendEnv tenv u (PackedCodeDelta [|| da ||]) denv) cs
                      return [|| ($$db, $$(conn2cenv cs') `asType` c) ||])
          ||]
      let h ::  Env PackedCodeDiff (Extr as (SafeTail us)) -> Code (PFun IFqS (Env Identity (Flatten cs)) a b)
          h env =
            [|| PFun (\a -> $$(toCode $ do
                        (b, cs) <- f (extendEnv tenv u (PackedCodeDiff [|| a ||]) env)
                        return [|| ($$b, $$(conn2cenv cs) ) ||]))
                      (\da c ->
                          let (db, c') = $$(mkAppD [|| $$lamTr da c ||] $ mapEnv (\(PackedCodeDiff a) -> PackedCodeDelta [|| nilChangeOf $$a ||]) env)
                          in (db, c'))
            ||]

          trh :: Env PackedCodeDelta (Extr as (SafeTail us)) -> Code (Delta (PFun IFqS (Env Identity (Flatten cs)) a b))
          trh denv =  [||
              DeltaPFun $$(allEmptyDelta denv) $ \d ->
                let (db, d') = $$(mkAppD [|| $$lamTr mempty d ||] denv)
                in (db, d')
              ||]
      return (\env -> return (h env, CNone),
              \denv _ -> return (trh denv, CNone))
    where
      u' = safeTail u

      wit :: Wit (Typeable (Flatten cs))
      wit = witTypeableFlatten sh

      wit2 :: Wit (AllIn (Extr as (SafeTail us)) DiffTypeable)
      wit2 = witExtr (Proxy :: Proxy DiffTypeable) tenv u'

      mkLetMono :: Code a -> CodeC (Code a)
      mkLetMono e = CodeC $ \k -> [|| $$e & \lamTr -> $$(k [|| lamTr ||]) ||]

  pAppTerm t1@(IFqTU tenv _ _ _) t2 =
    letTerm t2 $ letTerm (weakenTerm t1) $ pAppImplU tenv



-- cLamT :: forall s a b. (Diff a, AllIn s DiffTypeable) => IFqT (a ': s) b -> IFqT s (FunD a b)
-- cLamT (IFqT (ECons _ tenv) (sh :: Conn WitTypeable cs) m) = IFqT tenv CNone $
--   case wit of
--     Wit -> do
--     (f, tr) <- m
--     lamTr :: Code (Delta a -> Dynamic -> DFunc s (Delta b, Dynamic))
--       <- CodeC $ \k -> [||
--         let lamTr da d = $$(mkAbsD tenv $ \denv -> toCode $ do
--                 c <- CodeC $ \kk -> [|| let c = fromDynI d in $$(kk [|| c ||]) ||]
--                 cs <- CodeC $ cenv2conn sh c
--                 (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) denv) cs
--                 c' <- CodeC $ \kk -> [|| let c' = $$(conn2cenv cs') in $$(kk [|| c' ||]) ||]
--                 return [||
--                   let _ = ensureSameType $$c $$c'
--                   in ($$db, toDynI $$c') ||])
--         in $$(k [|| lamTr ||])
--       ||]
--     let
--       h :: Env PackedCodeDiff s -> Code (FunD a b)
--       h env = [||
--         FunD (\a -> $$(toCode $ do
--                 (b, cs) <- f (ECons (PackedCodeDiff [|| a ||]) env)
--                 return [|| ($$b, toDynI $$(conn2cenv cs)) ||]))
--               (\da d ->
--                  let (db, d') = $$(mkAppD [|| $$lamTr da d ||] $ mapEnv (\(PackedCodeDiff e) -> PackedCodeDelta [|| mempty ||]) env)
--                  in (db, d'))
--                 ||]
--             -- (\da (d, a) -> $$(toCode $ do
--             --     cs <- CodeC $ cenv2conn sh [|| fromDynI d ||]
--             --     denv <- mkLetEnvD $ mapEnv (\(PackedCodeDiff e) -> PackedCodeDelta [|| emptyOf $$e ||]) env
--             --     (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) denv) cs
--             --     return [|| ($$db, (toDynI $$(conn2cenv cs'), a)) ||])) ||]

--       trh :: Env PackedCodeDelta s -> Code (Delta (FunD a b))
--       trh denv = [|| DFunD $$(allEmptyDelta denv) $ \d ->
--         let (db, d') = $$(mkAppD [|| $$lamTr mempty d ||] denv)
--         in (db, d') ||]
--       -- trh denv = [|| DFunD $$(allEmptyDelta denv) $ \(d, a) -> $$(toCode $ do
--       --             cs <- CodeC $ cenv2conn sh [|| fromDynI d ||]
--       --             (db, cs') <- tr (ECons (PackedCodeDelta [|| emptyOf a ||]) denv) cs
--       --             return [|| ($$db, (toDynI $$(conn2cenv cs'), a)) ||])
--       --   ||]

--     return (\env -> return (h env, CNone),
--             \denv _ -> return (trh denv, CNone))
--   where
--     wit :: Wit (Typeable (Flatten cs))
--     wit = witTypeableFlatten sh

-- opAppT :: forall a b. (Typeable a, Typeable b, Diff b) => IFqS (FunD a b, a) b
-- opAppT = IFqS sh $
--   return (ff, ttr)
--   where
--     sh :: ConnSingle WitTypeable (Dynamic, Delta a -> MyState Dynamic (Delta b))
--     sh = CNE $ COne WitTypeable

--     ff :: Code (FunD a b , a) -> CodeC (Code b, ConnSingle PackedCode (Dynamic, Delta a -> MyState Dynamic (Delta b)))
--     ff fa = CodeC $ \k -> [||
--         let (FunD f df, a) = $$fa
--             (b, d) = f a
--         in $$(k ([|| b ||], CNE $ COne $ PackedCode [|| (d, df) ||]) )
--       ||]

--     ttr :: Code (Delta (FunD a b, a))
--            -> ConnSingle PackedCode (Dynamic, Delta a -> MyState Dynamic (Delta b))
--            -> CodeC (Code (Delta b), ConnSingle PackedCode (Dynamic, Delta a -> MyState Dynamic (Delta b)))
--     ttr dfa (CNE (COne (PackedCode cd))) = CodeC $ \k -> [||
--             let (d, df) = $$cd
--                 PairDelta (DFunD _ trNN) da = $$dfa
--                 (db1, d1) = trNN d
--                 (db2, d2) = df da d1
--             in $$(k ([|| db1 <> db2 ||], CNE $ COne $ PackedCode [|| (d2, df) ||]))
--       ||]


-- instance FunTerm IFqS IFqT where
--   type IHom IFqS = FunD
--   lamTerm = cLamT
--   appTerm e1 e2 = mapTerm opAppT $ multTerm e1 e2

instance FunTerm IFqS IFqT where
  type IHom IFqS = FunD
  lamTerm t = pAbsTerm t (mapTerm toDynIF)
  appTerm e1 e2 = pAppTerm (mapTerm fromDynIF e1) e2

instance FunTerm IFqS IFqTU where
  type IHom IFqS = FunD
  lamTerm t = pAbsTerm t (mapTerm toDynIF)
  appTerm e1 e2 = pAppTerm (mapTerm fromDynIF e1) e2

-- problematic x0 =
--   -- (lam (\f -> lam $ \x -> f `app` (f `app` x)) `app` lam (\f -> lam $ \x -> f `app` (f `app` x))) `app` lam (lift incC) `app` x0
--   lam (\f -> lam $ \x -> f `app` (f `app` x)) `app` lam (lift incC) `app` x0
--   where
--     incC = fromStateless (\x -> [|| succ $$x ||]) Prelude.id

{-
let h = $$( compile $ (runMonoWith (Proxy :: Proxy IFqT) problematic :: IFqS Int Int))
-}

