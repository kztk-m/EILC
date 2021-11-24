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
    FunD(..), type Delta (..)
  ) where

import           Control.Arrow                       (Arrow (second), first)
import           Data.Code
import           Data.Code.Lifting
import           Data.Conn
import           Data.Delta                          (Delta (PairDelta),
                                                      Diff (..), DiffTypeable,
                                                      nilChangeOf, pairDelta)
import           Data.Dynamic                        (Dynamic, fromDynamic,
                                                      toDyn)
import           Data.Env                            (AllIn, Env (..),
                                                      headTailEnv, mapEnv)
import           Data.Functor.Identity               (Identity (..))
import           Data.IFq                            (IFqS (..), ensureDiffType,
                                                      mkInteraction)
import           Data.IFqT                           (IFqT (..))
-- import           Data.IFqTEU
import           Data.Incrementalized                (IncrementalizedQ (fromStateless))
import           Data.Interaction                    (Interaction (Interaction))
import           Data.Maybe                          (fromJust)
import           Data.Typeable                       (Typeable)
import           Debug.Trace                         (trace)
import           Language.Unembedding                hiding (Fun)
import           Language.Unembedding.PseudoFunction

import           Data.Function
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



instance PFunTerm IFqS IFqT where
  data instance PFun IFqS c a b = PFun !(a -> (b, c)) !(Delta a -> c -> (Delta b, c))
  type KK IFqS c = Typeable c

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
  --   forall as c a b.
  --   (AllIn as DiffTypeable, DiffTypeable a, DiffTypeable b) =>
  --   IFqT as (PFun IFqS c a b) -> IFqT as a -> IFqT as b
  -- pAppTerm (IFqT tenv (sh1 :: Conn proxy cs1) m1) (IFqT _ (sh2 :: Conn proxy cs2) m2) = IFqT tenv (joinConn sh1 sh2) $ do
  --   (f1, tr1) <- m1
  --   (f2, tr2) <- m2
  --   let
  --     ff :: Env PackedCodeDiff as -> CodeC (Code b, ConnSingle PackedCode (c, Delta a -> c -> (Delta b, c)))
  --     ff env = do
  --       (f_packed, c1) <- f1 env
  --       (a, c2)        <- f2 env
  --       (b, cc) <- CodeC $ \k -> [||
  --                 let PFun f deriv_f = $$f_packed
  --                     (b, c) = f $$a
  --                 in $$(k [|| (b, (c, deriv_f) ) ||])
  --               ||]
  --       return (b, CSingle cc)
  --   _




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

-- problematic x0 =
--   -- (lam (\f -> lam $ \x -> f `app` (f `app` x)) `app` lam (\f -> lam $ \x -> f `app` (f `app` x))) `app` lam (lift incC) `app` x0
--   lam (\f -> lam $ \x -> f `app` (f `app` x)) `app` lam (lift incC) `app` x0
--   where
--     incC = fromStateless (\x -> [|| succ $$x ||]) Prelude.id

{-
let h = $$( compile $ (runMonoWith (Proxy :: Proxy IFqT) problematic :: IFqS Int Int))
-}


-- spliced :: Int -> (Int, Interaction (Delta Int) (Delta Int))
-- spliced =
--     (\ da_aObn c_aObo a_aObp -> c_aObo `seqENil` (let _v_aObq = da_aObn in (_v_aObq, enilOfIdentity `asType` c_aObo)))
--        & (\ lamTr_aObr
--             -> (\ da_aObs c_aObt a_aObu a_aObv -> let (x_aObw, xs_aObx) = headTailEnv c_aObt in
--                                                   let (x_aOby, xs_aObz) = headTailEnv xs_aObx
--                                                   in
--                                                     (xs_aObz
--                                                        `seqENil`
--                                                          (let _v_aObA = da_aObs in
--                                                           let _v_aObB = a_aObu in
--                                                           let
--                                                             (c_aObE, deriv_f_aObF) = runIdentity x_aObw
--                                                             DeltaPFun b_aObC df_aObD = _v_aObB
--                                                             (db1_aObG, c1_aObH) = if b_aObC then (mempty, c_aObE) else df_aObD c_aObE
--                                                             (db2_aObI, c2_aObJ) = deriv_f_aObF _v_aObA c1_aObH
--                                                             db_aObK = (db1_aObG <> db2_aObI) in
--                                                           let _v_aObL = db_aObK in
--                                                           let _v_aObM = a_aObu in
--                                                           let
--                                                             (c_aObP, deriv_f_aObQ) = runIdentity x_aOby
--                                                             DeltaPFun b_aObN df_aObO = _v_aObM
--                                                             (db1_aObR, c1_aObS) = if b_aObN then (mempty, c_aObP) else df_aObO c_aObP
--                                                             (db2_aObT, c2_aObU) = deriv_f_aObQ _v_aObL c1_aObS
--                                                             db_aObV = (db1_aObR <> db2_aObT)
--                                                           in
--                                                             (db_aObV,
--                                                              ECons (Identity (c2_aObJ, deriv_f_aObF)) (ECons (Identity (c2_aObU, deriv_f_aObQ)) enilOfIdentity) `asType` c_aObt))))
--                   & (\ lamTr_aObW
--                        -> (\ da_aObX c_aObY a_aObZ -> c_aObY
--                                          `seqENil`
--                                            (let
--                                               DeltaPFun b_aOc0 df_aOc1
--                                                 = DeltaPFun (checkEmpty da_aObX && checkEmpty a_aObZ) (\ d_aOc2 -> let (db_aOc3, d'_aOc4) = lamTr_aObW mempty d_aOc2 da_aObX a_aObZ in (db_aOc3, d'_aOc4))
--                                             in DeltaPFun b_aOc0 (\ d_aOc5 -> second toDyn $ df_aOc1 (fromJust $ fromDynamic d_aOc5)),
--                                             enilOfIdentity `asType` c_aObY))
--                              & (\ lamTr_aOc6
--                                   -> ensureDiffType (\ pa_aOc7 pb_aOc8 a_aOc9
--                                              -> let _v_aOca = a_aOc9 in
--                                                 let
--                                                   _v_aOcb
--                                                     = let
--                                                         PFun f_aOcc deriv_f_aOcd
--                                                           = PFun (\ a_aOce -> let _v_aOcf = succ a_aOce in (_v_aOcf, enilOfIdentity))
--                                                               (\ da_aOcg c_aOch -> let (db_aOci, c'_aOcj) = lamTr_aObr da_aOcg c_aOch (nilChangeOf a_aOc9) in (db_aOci, c'_aOcj))
--                                                       in
--                                                         PFun (second toDyn Data.Function.. f_aOcc)
--                                                           (\ da_aOck d_aOcl -> second toDyn $ deriv_f_aOcd da_aOck (fromJust $ fromDynamic d_aOcl)) in
--                                                 let
--                                                   _v_aOcm
--                                                     = let
--                                                         PFun f_aOcn deriv_f_aOco
--                                                           = PFun
--                                                                (\ a_aOcp
--                                                                   -> (let
--                                                                         PFun f_aOcq deriv_f_aOcr
--                                                                           = PFun
--                                                                                (\ a_aOcs
--                                                                                   -> let _v_aOct = a_aOcs in
--                                                                                      let _v_aOcu = a_aOcp in
--                                                                                      let
--                                                                                        PFun f_aOcv deriv_f_aOcw = _v_aOcu
--                                                                                        (b_aOcx, c_aOcy) = f_aOcv _v_aOct in
--                                                                                      let _v_aOcz = b_aOcx in
--                                                                                      let _v_aOcA = a_aOcp in
--                                                                                      let
--                                                                                        PFun f_aOcB deriv_f_aOcC = _v_aOcA
--                                                                                        (b_aOcD, c_aOcE) = f_aOcB _v_aOcz
--                                                                                      in (b_aOcD, ECons (Identity (c_aOcy, deriv_f_aOcw)) (ECons (Identity (c_aOcE, deriv_f_aOcC)) enilOfIdentity)))
--                                                                               (\ da_aOcF c_aOcG
--                                                                                  -> let (db_aOcH, c'_aOcI) = lamTr_aObW da_aOcF c_aOcG (nilChangeOf a_aOcp) (nilChangeOf a_aOc9)
--                                                                                     in (db_aOcH, c'_aOcI))
--                                                                       in
--                                                                         PFun (second toDyn Data.Function.. f_aOcq)
--                                                                           (\ da_aOcJ d_aOcK -> second toDyn $ deriv_f_aOcr da_aOcJ (fromJust $ fromDynamic d_aOcK)),
--                                                                       enilOfIdentity))
--                                                               (\ da_aOcL c_aOcM -> let (db_aOcN, c'_aOcO) = lamTr_aOc6 da_aOcL c_aOcM (nilChangeOf a_aOc9) in (db_aOcN, c'_aOcO))
--                                                       in
--                                                         PFun (second toDyn Data.Function.. f_aOcn)
--                                                           (\ da_aOcP d_aOcQ -> second toDyn $ deriv_f_aOco da_aOcP (fromJust $ fromDynamic d_aOcQ)) in
--                                                 let
--                                                   PFun f_aOcR deriv_f_aOcS = _v_aOcm
--                                                   (b_aOcT, c_aOcU) = f_aOcR _v_aOcb in
--                                                 let _v_aOcV = b_aOcT in
--                                                 let
--                                                   PFun f_aOcW deriv_f_aOcX = _v_aOcV
--                                                   (b_aOcY, c_aOcZ) = f_aOcW _v_aOca
--                                                 in
--                                                   (b_aOcY,
--                                                    let
--                                                      func_aOd0
--                                                        = \ !a_aOd1 !a_aOd2 -> mkInteraction pa_aOc7 pb_aOc8 (\ da_aOd3
--                                                                            -> let _v_aOd4 = da_aOd3 in
--                                                                               let
--                                                                                 _v_aOd5
--                                                                                   = let
--                                                                                       DeltaPFun b_aOd6 df_aOd7
--                                                                                         = DeltaPFun (checkEmpty da_aOd3) (\ d_aOd8 -> let (db_aOd9, d'_aOda) = ((lamTr_aObr mempty) d_aOd8) da_aOd3 in (db_aOd9, d'_aOda))
--                                                                                     in DeltaPFun b_aOd6 (\ d_aOdb -> second toDyn $ df_aOd7 (fromJust $ fromDynamic d_aOdb)) in
--                                                                               let
--                                                                                 _v_aOdc
--                                                                                   = let
--                                                                                       DeltaPFun b_aOdd df_aOde
--                                                                                         = DeltaPFun (checkEmpty da_aOd3) (\ d_aOdf -> let (db_aOdg, d'_aOdh) = ((lamTr_aOc6 mempty) d_aOdf) da_aOd3 in (db_aOdg, d'_aOdh))
--                                                                                     in DeltaPFun b_aOdd (\ d_aOdi -> second toDyn $ df_aOde (fromJust $ fromDynamic d_aOdi)) in
--                                                                               let
--                                                                                 (c_aOdl, deriv_f_aOdm) = a_aOd1
--                                                                                 DeltaPFun b_aOdj df_aOdk = _v_aOdc
--                                                                                 (db1_aOdn, c1_aOdo) = if b_aOdj then (mempty, c_aOdl) else df_aOdk c_aOdl
--                                                                                 (db2_aOdp, c2_aOdq) = deriv_f_aOdm _v_aOd5 c1_aOdo
--                                                                                 db_aOdr = (db1_aOdn <> db2_aOdp) in
--                                                                               let _v_aOds = db_aOdr in
--                                                                               let
--                                                                                 (c_aOdv, deriv_f_aOdw) = a_aOd2
--                                                                                 DeltaPFun b_aOdt df_aOdu = _v_aOds
--                                                                                 (db1_aOdx, c1_aOdy) = if b_aOdt then (mempty, c_aOdv) else df_aOdu c_aOdv
--                                                                                 (db2_aOdz, c2_aOdA) = deriv_f_aOdw _v_aOd4 c1_aOdy
--                                                                                 db_aOdB = (db1_aOdx <> db2_aOdz)
--                                                                               in (db_aOdB, func_aOd0 (c2_aOdq, deriv_f_aOdm) (c2_aOdA, deriv_f_aOdw)))
--                                                    in func_aOd0 (c_aOcU, deriv_f_aOcS) (c_aOcZ, deriv_f_aOcX))))))
