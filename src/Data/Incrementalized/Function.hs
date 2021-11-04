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
{-# LANGUAGE BangPatterns          #-}
module Data.Incrementalized.Function (
    toDynI, fromDynI, -- trDFunT,
    -- FunT(..), type Delta (..), IsEmpty(..),
    ensureSameType,
    FunD(..), type Delta (..)
  ) where

import           Control.Arrow         (first)
import           Data.Code
import           Data.Code.Lifting
import           Data.Conn
import           Data.Delta            (Delta (PairDelta), Diff (..),
                                        DiffTypeable, pairDelta)
import           Data.Dynamic          (Dynamic, fromDynamic, toDyn)
import           Data.Env              (AllIn, Env (..), headTailEnv, mapEnv)
import           Data.Functor.Identity (Identity (..))
import           Data.IFq              (IFqS (..), ensureDiffType,
                                        mkInteraction)
import           Data.IFqT             (IFqT (..))
import           Data.IFqTEU
import           Data.Incrementalized  (IncrementalizedQ (fromStateless))
import           Data.Interaction      (Interaction (Interaction))
import           Data.Maybe            (fromJust)
import           Data.Typeable         (Typeable)
import           Debug.Trace           (trace)
import           Language.Unembedding  hiding (Fun)

{-

Usual function:

  (Γ × A ==> B)
  -------------
  Γ ==> [A, B]

  app :: [A, B] × A ==> B

Common approach is to make a closure:

   [A, B] = ∃Γ. (Γ × A ==> B) × Γ

Then, we can apply it by merely by using application in terms of ==>.

In the cache-transfer system, they used:

   [A, B] C  = ∃Γ. (Γ × A -> B × C) × Γ
   Δ[A, B] C = ∃Γ. (Γ × A -> B × C) × (Γ × A -> Δ(Γ × A) -> C -> (ΔB × C)) × Γ × ΔΓ

where C is exposed. Notice that Δ part also contains (Γ × A -> B × C) to avoid matching of Γ type (if their Δ retains the original function why do they need to expose C)?

Then, we have

  (/+) :: [A, B] C -> Δ[A, B] C -> [A, B] C
  (_, _) /+ (f, trF, θ', dθ') = (f, θ' /+ dθ')

that is, the change to the closure is the change to the free variables in them.


-}

type MyState s a = s -> (a, s)

-- FIXME: the @a@ below only convey @emptyOF a@. We should prepare a special type for this purpose.
data FunD a b =
  FunD !(a -> (b, (Dynamic, a)))
       !(Delta a -> MyState (Dynamic, a) (Delta b)) -- must satisfy tr 0 d = (0, d)

data instance Delta (FunD a b) =
  DFunD { dfunIsEmpty :: !Bool,
          dfunTrNN :: !(MyState (Dynamic, a) (Delta b)) }

instance Semigroup (Delta b) => Semigroup (Delta (FunD a b)) where
  DFunD b1 dfNN1 <> DFunD b2 dfNN2 = DFunD (b1 && b2) $ \s ->
    let (db1, s1) = dfNN1 s
        (db2, s2) = dfNN2 s1
    in (db1 <> db2, s2)

instance (Diff a, Diff b) => Diff (FunD a b) where
  FunD f ftr /+ DFunD True _ = FunD f ftr
  FunD f ftr /+ DFunD _ ftr' = FunD (\a -> let (b, s) = f a in
                                           let (db, s') = ftr' s in
                                             (b /+ db, s')) ftr

  checkEmpty (DFunD b _) = b

  emptify (DFunD _ ftr) = DFunD True $ \a -> first emptify $ ftr a

  emptyOf (FunD _ ftr) = DFunD True $ \(c,a) -> ftr (emptyOf a) (c, a)

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

cLamT :: forall s a b. (Diff a, AllIn s DiffTypeable) => IFqT (a ': s) b -> IFqT s (FunD a b)
cLamT (IFqT (ECons _ tenv) (sh :: Conn WitTypeable cs) m) = IFqT tenv CNone $
  case wit of
    Wit -> do
    (f, tr) <- m
    lamTr :: Code (Delta a -> Dynamic -> DFunc s (Delta b, Dynamic))
      <- CodeC $ \k -> [||
        let lamTr da d = $$(mkAbsD tenv $ \denv -> toCode $ do
                c <- CodeC $ \kk -> [|| let c = fromDynI d in $$(kk [|| c ||]) ||]
                cs <- CodeC $ cenv2conn sh c
                (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) denv) cs
                c' <- CodeC $ \kk -> [|| let c' = $$(conn2cenv cs') in $$(kk [|| c' ||]) ||]
                return [||
                  let _ = ensureSameType $$c $$c'
                  in ($$db, toDynI $$c') ||])
        in $$(k [|| lamTr ||])
      ||]
    let
      h :: Env PackedCodeDiff s -> Code (FunD a b)
      h env = [||
        FunD (\a -> $$(toCode $ do
                (b, cs) <- f (ECons (PackedCodeDiff [|| a ||]) env)
                return [|| ($$b, (toDynI $$(conn2cenv cs), a)) ||]))
              (\da (d, a) ->
                 let (db, d') = $$(mkAppD [|| $$lamTr da d ||] $ mapEnv (\(PackedCodeDiff e) -> PackedCodeDelta [|| emptyOf $$e ||]) env)
                 in (db, (d', a)))
                ||]
            -- (\da (d, a) -> $$(toCode $ do
            --     cs <- CodeC $ cenv2conn sh [|| fromDynI d ||]
            --     denv <- mkLetEnvD $ mapEnv (\(PackedCodeDiff e) -> PackedCodeDelta [|| emptyOf $$e ||]) env
            --     (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) denv) cs
            --     return [|| ($$db, (toDynI $$(conn2cenv cs'), a)) ||])) ||]

      trh :: Env PackedCodeDelta s -> Code (Delta (FunD a b))
      trh denv = [|| DFunD $$(allEmptyDelta denv) $ \(d, a) ->
        let (db, d') = $$(mkAppD [|| $$lamTr (emptyOf a) d ||] denv)
        in (db, (d', a)) ||]
      -- trh denv = [|| DFunD $$(allEmptyDelta denv) $ \(d, a) -> $$(toCode $ do
      --             cs <- CodeC $ cenv2conn sh [|| fromDynI d ||]
      --             (db, cs') <- tr (ECons (PackedCodeDelta [|| emptyOf a ||]) denv) cs
      --             return [|| ($$db, (toDynI $$(conn2cenv cs'), a)) ||])
      --   ||]

    return (\env -> return (h env, CNone),
            \denv _ -> return (trh denv, CNone))
  where
    wit :: Wit (Typeable (Flatten cs))
    wit = witTypeableFlatten sh

type ConnSingle f t = Conn f ('NE ('NEOne t))

opAppT :: forall a b. (Typeable a, Typeable b, Diff b) => IFqS (FunD a b, a) b
opAppT = IFqS sh $
  return (ff, ttr)
  where
    sh :: ConnSingle WitTypeable ((Dynamic, a), Delta a -> MyState (Dynamic, a) (Delta b))
    sh = CNE $ COne WitTypeable

    ff :: Code (FunD a b , a) -> CodeC (Code b, ConnSingle PackedCode ((Dynamic, a), Delta a -> MyState (Dynamic, a) (Delta b)))
    ff fa = CodeC $ \k -> [||
        let (FunD f df, a) = $$fa
            (b, d) = f a
        in $$(k ([|| b ||], CNE $ COne $ PackedCode [|| (d, df) ||]) )
      ||]

    ttr :: Code (Delta (FunD a b, a))
           -> ConnSingle PackedCode ((Dynamic, a), Delta a -> MyState (Dynamic, a) (Delta b))
           -> CodeC (Code (Delta b), ConnSingle PackedCode ((Dynamic, a), Delta a -> MyState (Dynamic, a) (Delta b)))
    ttr dfa (CNE (COne (PackedCode cd))) = CodeC $ \k -> [||
            let (d, df) = $$cd
                PairDelta (DFunD _ trNN) da = $$dfa
                (db1, d1) = trNN d
                (db2, d2) = df da d1
            in $$(k ([|| db1 <> db2 ||], CNE $ COne $ PackedCode [|| (d2, df) ||]))
      ||]


instance FunTerm IFqS IFqT where
  type IHom IFqS = FunD
  lamTerm = cLamT
  appTerm e1 e2 = mapTerm opAppT $ multTerm e1 e2



-- -- TODO: We should have a special treatment for the case where Dynamic ~ ()
-- newtype FunT a b = FunT (a -> (b, Dynamic))


-- {-
-- The one below is not that useful as it fails the separability.

-- data instance Delta (FunT a b) where
--   DFunT
--     ::
--     !IsEmpty -- true if it is an empty change.
--     -- NB: there is no guanrantee that Delta b is empty if Delta a is, especially
--     -- when the original function uses free variables. The above Bool denotes a such a
--     -- flag. That is, if the above is True, then the function is the empty change.
--     -> !(Delta a -> Dynamic -> (Delta b, Dynamic))
--     -> Delta (FunT a b)

-- Specifically, df c (da <> da') need not be
--    let (db,  c1) = df c da
--        (db', c2) = df c1 da'
--    in (db <> db', c2)
-- because df may not be a nil change, meaning that df c empty /= (empty, c) for some c.

-- So, we should separate it to a pair of functions: a nil change and a may-not nil change.

--    <df_nil, df> c da =
--        let (db1, c1) = df c
--            (db2, c2) = df_nil da c1
--        in (db1 <> db2)

-- so that we can compose it as:

--    <df_nil, df> c (da <> da') =
--        let (db1, c1) = df c
--            (db2, c2) = df_nil da c1
--            (db3, c3) = df_nil da' c2
--        in (db1 <> db2 <> db3)

-- -}

-- data instance Delta (FunT a b) =
--   DFunT
--     !IsEmpty -- true if its non-nil-change actually does nothing. That is, df0 d = (d, mempty)
--     !(Dynamic -> (Delta b, Dynamic)) -- non nil change
--     !(Delta a -> Dynamic -> (Delta b, Dynamic)) -- nil change


-- trDFunT :: Semigroup (Delta b) => Delta (FunT a b) -> (Delta a -> Dynamic -> (Delta b, Dynamic))
-- trDFunT (DFunT _ dfNN df) da c =
--   let (db1, c1) = dfNN c
--       (db2, c2) = df da c1
--   in (db1 <> db2, c2)


-- -- data instance Delta (FunT a b) where
-- --   DFunT
-- --     ::
-- --     !IsEmpty -- true if it is an empty change.
-- --     -- NB: there is no guanrantee that Delta b is empty if Delta a is, especially
-- --     -- when the original function uses free variables. The above Bool denotes a such a
-- --     -- flag. That is, if the above is True, then the function is the empty change.
-- --     -> !(Delta a -> Dynamic -> (Delta b, Dynamic))
-- --     -> Delta (FunT a b)


-- -- data IsEmpty
-- --   = FromMEmpty
-- --   | Empty
-- --   | Unk

-- data IsEmpty = Empty | Unk

-- instance Semigroup IsEmpty where
--   -- FromMEmpty <> FromMEmpty = FromMEmpty
--   -- FromMEmpty <> Empty      = Empty
--   -- FromMEmpty <> Unk        = Unk
--   -- Empty <> FromMEmpty      = Empty
--   Empty <> Empty = Empty
--   Empty <> Unk   = Unk
--   Unk <> _       = Unk


-- applyDeltaFunT :: (Diff a, Diff b) => FunT a b -> Delta (FunT a b) -> FunT a b
-- -- applyDeltaFunT f (DFunT FromMEmpty _ _) = f
-- applyDeltaFunT f (DFunT Empty _ _)      = f
-- applyDeltaFunT (FunT f) (DFunT Unk dfNN _) = FunT $ \a ->
--   let (b,  c)  = f a
--       (db, c1) = dfNN c
--   in (b /+ db, c1)

-- {-

-- -}

-- instance Semigroup (Delta b) => Semigroup (Delta (FunT a b)) where
--   DFunT b1 dfNN1 df1 <> DFunT b2 dfNN2 df2 = DFunT (b1 <> b2) dfNN df
--     where
--       dfNN c = let (db1, c1) = dfNN1 c
--                    (db2, c2) = dfNN2 c1
--                in (db1 <> db2, c2)
--       -- The definition below looks weird but recall that df mempty c = (mempty, c)
--       -- So,
--       --    let (db1, c1) = df1 da c
--       --        (db2, c2) = df2 mempty c1
--       --    in (db1 <> db2, c2)
--       -- is df1

--       df = df2 -- Really?
--       -- df = case (b1, b2) of
--       --   (FromMEmpty, _) -> df2
--       --   _               -> df1

-- -- instance (Diff a, Monoid (Delta b)) => Monoid (Delta (FunT a b)) where
-- --   -- This is correct only when `da` is mempty.
-- --   -- Fortunately, the part cannot carry interesting information as deltas.
-- --   mempty = DFunT FromMEmpty (\c -> (mempty, c)) $ \da c ->
-- --             if checkEmpty da then
-- --               (mempty, c)
-- --             else
-- --               error "mempty cannot handle non-nil changes."

-- instance (Diff a, Diff b) => Diff (FunT a b) where
--   (/+) = applyDeltaFunT

-- --  checkEmpty (DFunT FromMEmpty _ _) = True
--   checkEmpty (DFunT Empty _ _) = True
--   checkEmpty (DFunT Unk _ _)   = False

-- --  emptify (DFunT FromMEmpty _ df) = DFunT FromMEmpty (\c -> (mempty, c)) df
--   emptify (DFunT _ dfNN df)          = DFunT Empty (first emptify Prelude.. dfNN) df



-- allEmptyDelta :: forall xs. Env PackedCodeDelta xs -> Code Bool
-- allEmptyDelta ENil = [|| True ||]
-- allEmptyDelta (ECons (PackedCodeDelta da) ENil) = [|| checkEmpty $$da ||]
-- allEmptyDelta (ECons (PackedCodeDelta da) das)  = [|| checkEmpty $$da && $$(allEmptyDelta das) ||]

-- toDynI :: Typeable cs => Env Identity cs -> Dynamic
-- toDynI = toDyn

-- fromDynI :: Typeable cs => Dynamic -> Env Identity cs
-- fromDynI = fromJust Prelude.. fromDynamic

-- cLamT :: forall s a b. Diff a => IFqT (a ': s) b -> IFqT s (FunT a b)
-- cLamT (IFqT (ECons _ tenv) (sh :: Conn WitTypeable cs) m) = IFqT tenv CNone $
--   case wit of
--     Wit -> do
--       (f, tr) <- m
--       let
--         h :: Env PackedCode s -> Code (a -> (b, Dynamic))
--         h env = [|| \a -> $$(toCode $ do
--                       (b, c') <- f (ECons (PackedCode [|| a ||]) env)
--                       return [|| ($$b, toDyn $$(conn2cenv c')) ||]) ||]
--         trH :: Env PackedCodeDelta s -> Code (Maybe (Delta a) -> Dynamic -> (Delta b, Dynamic))
--         trH denv = [|| \maybe_da d -> $$(toCode $ do
--                           -- For typing
--                           c  <- mkLet [|| fromDynI d ||]
--                           cs <- CodeC $ cenv2conn sh c
--                           denv' <- mkLetEnvD $ mapEnv (\(PackedCodeDelta de) -> PackedCodeDelta [|| maybe Prelude.id (const emptify) maybe_da $$de ||]) denv
--                           da'   <- mkLet [|| fromMaybe mempty maybe_da ||]
--                           (db, cs') <- tr (ECons (PackedCodeDelta da') denv') cs
--                           return [|| ($$db, toDynI $$(conn2cenv cs')) ||] ) ||]


--         -- trH denv = [|| \da c ->
--         --                 $$(cenv2conn sh [|| fromJust (fromDynamic c) ||] $ \cs -> toCode $ do
--         --                     (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) denv) cs
--         --                     return [|| ($$db, toDyn $$(conn2cenv cs')) ||]) ||]
--       let
--         f' env = do
--             let ff = [|| FunT $$(h env) ||]
--             return (ff, CNone)
--         tr' denv _ = do
--           trfunc <- mkLet $ trH denv
--           let ftr = [|| DFunT (if $$(allEmptyDelta denv) then Empty else Unk) ($$trfunc Nothing) ($$trfunc Prelude.. Just) ||]
--           return (ftr, CNone)
--       return (f', tr')
--     where
--       wit :: Wit (Typeable (Flatten cs))
--       wit = witTypeableFlatten sh

-- opAppT :: forall a b. Diff b => IFqS (FunT a b, a) b
-- opAppT = IFqS sh $
--   return (f, tr)
--   where
--     sh :: Conn WitTypeable ('NE ('NEOne Dynamic))
--     sh = CNE $ COne WitTypeable

--     f :: Code (FunT a b, a) -> CodeC (Code b, Conn PackedCode ('NE ('NEOne Dynamic)))
--     f cp = do
--       (b, c) <- CodeC $ \k -> [|| case $$cp of
--                         (FunT ff, a) ->
--                           let (b, c) = ff a
--                           in $$(k ([|| b ||] , [|| c ||])) ||]
--       return (b, CNE $ COne $ PackedCode c)

--     tr
--       :: Code (Delta (FunT a b, a))
--          -> Conn PackedCode ('NE ('NEOne Dynamic))
--          -> CodeC (Code (Delta b), Conn PackedCode ('NE ('NEOne Dynamic)))
--     tr dp (CNE (COne (PackedCode c))) = do
--       (db, c') <- CodeC $ \k ->
--                   [|| let PairDelta dfunT da = $$dp
--                           (!db, c') = trDFunT dfunT da $$c
--                       in $$(k ([|| db ||], [|| c' ||]) ) ||]
--       return (db, CNE $ COne $ PackedCode c')

-- instance FunTerm IFqS IFqT where
--   type IHom IFqS = FunT
--   lamTerm = cLamT
--   appTerm e1 e2 = mapTerm opAppT $ multTerm e1 e2


-- problematic :: (K cat a, K cat (IHom cat a a), App2 cat term e, FunTerm cat term) => e a -> e a
problematic x0 =
  -- (lam (\f -> lam $ \x -> f `app` (f `app` x)) `app` lam (\f -> lam $ \x -> f `app` (f `app` x))) `app` lam (lift incC) `app` x0
  lam (\f -> lam $ \x -> f `app` (f `app` x)) `app` lam (lift incC) `app` x0
  where
    incC = fromStateless (\x -> [|| succ $$x ||]) Prelude.id

{-
let h = $$( compile $ (runMonoWith (Proxy :: Proxy IFqT) problematic :: IFqS Int Int
-}

spliced :: Int -> (Int , Interaction (Delta Int) (Delta Int))
spliced =
   let
      lamTr_a2hR5 da_a2hR6 d_a2hR7
        = \ a_a2hR8 a_a2hR9 -> trace ("lamTr1") $
                               let c_a2hRa = fromDynI d_a2hR7 in
                               let (x_a2hRb, xs_a2hRc) = headTailEnv c_a2hRa in
                               let (x_a2hRd, xs_a2hRe) = headTailEnv xs_a2hRc
                               in
                                 (xs_a2hRe
                                    `seqENil`
                                      (let _v_a2hRf = pairDelta a_a2hR8 da_a2hR6 in
                                       let
                                         (d_a2hRi, df_a2hRj) = runIdentity x_a2hRb
                                         PairDelta (DFunD _ trNN_a2hRg) da_a2hRh = _v_a2hRf
                                         (db1_a2hRk, d1_a2hRl) = trNN_a2hRg d_a2hRi
                                         (db2_a2hRm, d2_a2hRn) = df_a2hRj da_a2hRh d1_a2hRl in
                                       let _v_a2hRo = pairDelta a_a2hR8 (db1_a2hRk <> db2_a2hRm) in
                                       let
                                         (d_a2hRr, df_a2hRs) = runIdentity x_a2hRd
                                         PairDelta (DFunD _ trNN_a2hRp) da_a2hRq = _v_a2hRo
                                         (db1_a2hRt, d1_a2hRu) = trNN_a2hRp d_a2hRr
                                         (db2_a2hRv, d2_a2hRw) = df_a2hRs da_a2hRq d1_a2hRu in
                                       let c'_a2hRx = ECons (Identity (d2_a2hRn, df_a2hRj)) (ECons (Identity (d2_a2hRw, df_a2hRs)) enilOfIdentity) in
                                       let _ = ensureSameType c_a2hRa c'_a2hRx in (db1_a2hRt <> db2_a2hRv, toDynI c'_a2hRx))) in
    let
      lamTr_a2hRy da_a2hRz d_a2hRA
        = \ a_a2hRB
            -> trace ("lamTr2") $
               let c_a2hRC = fromDynI d_a2hRA
               in
                 (c_a2hRC
                    `seqENil`
                      (let c'_a2hRD = enilOfIdentity in
                       let _ = ensureSameType c_a2hRC c'_a2hRD
                       in
                         (DFunD (checkEmpty da_a2hRz && checkEmpty a_a2hRB) (\ (d_a2hRE, a_a2hRF)
                                  -> let (db_a2hRG, d'_a2hRH) = lamTr_a2hR5 (emptyOf a_a2hRF) d_a2hRE da_a2hRz a_a2hRB in (db_a2hRG, (d'_a2hRH, a_a2hRF))),
                          toDynI c'_a2hRD))) in
    let
      lamTr_a2hRI da_a2hRJ d_a2hRK
        = trace "lamTr3" $ \ a_a2hRL
            -> let c_a2hRM = fromDynI d_a2hRK
               in
                 (c_a2hRM
                    `seqENil`
                      (let _v_a2hRN = da_a2hRJ in
                       let c'_a2hRO = enilOfIdentity in let _ = ensureSameType c_a2hRM c'_a2hRO in (_v_a2hRN, toDynI c'_a2hRO)))
    in
      ensureDiffType (\ pa_a2hRP pb_a2hRQ a_a2hRR
              -> let
                   _v_a2hRS
                     = (FunD
                           (\ a_a2hRT
                              -> (FunD
                                     (\ a_a2hRU
                                        -> let _v_a2hRV = (a_a2hRT, a_a2hRU) in
                                           let
                                             (FunD f_a2hRW df_a2hRX, a_a2hRY) = _v_a2hRV
                                             (b_a2hRZ, d_a2hS0) = f_a2hRW a_a2hRY in
                                           let _v_a2hS1 = (a_a2hRT, b_a2hRZ) in
                                           let
                                             (FunD f_a2hS2 df_a2hS3, a_a2hS4) = _v_a2hS1
                                             (b_a2hS5, d_a2hS6) = f_a2hS2 a_a2hS4
                                           in (b_a2hS5, (toDynI (ECons (Identity (d_a2hS0, df_a2hRX)) (ECons (Identity (d_a2hS6, df_a2hS3)) enilOfIdentity)), a_a2hRU)))
                                    (\ da_a2hS7 (d_a2hS8, a_a2hS9)
                                       -> let (db_a2hSa, d'_a2hSb) = (lamTr_a2hR5 da_a2hS7) d_a2hS8 (emptyOf a_a2hRT) (emptyOf a_a2hRR)
                                          in (db_a2hSa, (d'_a2hSb, a_a2hS9))),
                                  (toDynI enilOfIdentity, a_a2hRT)))
                          (\ da_a2hSc (d_a2hSd, a_a2hSe)
                             -> let (db_a2hSf, d'_a2hSg) = lamTr_a2hRy da_a2hSc d_a2hSd (emptyOf a_a2hRR) in (db_a2hSf, (d'_a2hSg, a_a2hSe))),
                        FunD (\ a_a2hSh -> let _v_a2hSi = succ a_a2hSh in (_v_a2hSi, (toDynI enilOfIdentity, a_a2hSh)))
                          (\ da_a2hSj (d_a2hSk, a_a2hSl)
                             -> let (db_a2hSm, d'_a2hSn) = lamTr_a2hRI da_a2hSj d_a2hSk (emptyOf a_a2hRR) in (db_a2hSm, (d'_a2hSn, a_a2hSl)))) in
                 let
                   (FunD f_a2hSo df_a2hSp, a_a2hSq) = _v_a2hRS
                   (b_a2hSr, d_a2hSs) = f_a2hSo a_a2hSq in
                 let _v_a2hSt = (b_a2hSr, a_a2hRR) in
                 let
                   (FunD f_a2hSu df_a2hSv, a_a2hSw) = _v_a2hSt
                   (b_a2hSx, d_a2hSy) = f_a2hSu a_a2hSw
                 in
                   (b_a2hSx,
                    let
                      func_a2hSz
                        = \ !a_a2hSA !a_a2hSB -> mkInteraction pa_a2hRP pb_a2hRQ (\ da_a2hSC
                                            -> let
                                                 _v_a2hSD
                                                   = pairDelta
                                                        (DFunD (checkEmpty da_a2hSC)
                                                           $ (\ (d_a2hSE, a_a2hSF)
                                                                -> let (db_a2hSG, d'_a2hSH) = ((lamTr_a2hRy (emptyOf a_a2hSF)) d_a2hSE) da_a2hSC in (db_a2hSG, (d'_a2hSH, a_a2hSF))))
                                                       (DFunD (checkEmpty da_a2hSC) (\ (d_a2hSI, a_a2hSJ)
                                                               -> let (db_a2hSK, d'_a2hSL) = ((lamTr_a2hRI (emptyOf a_a2hSJ)) d_a2hSI) da_a2hSC in (db_a2hSK, (d'_a2hSL, a_a2hSJ)))) in
                                               let
                                                 (d_a2hSO, df_a2hSP) = a_a2hSA
                                                 PairDelta (DFunD _ trNN_a2hSM) da_a2hSN = _v_a2hSD
                                                 (db1_a2hSQ, d1_a2hSR) = trNN_a2hSM d_a2hSO
                                                 (db2_a2hSS, d2_a2hST) = df_a2hSP da_a2hSN d1_a2hSR in
                                               let _v_a2hSU = pairDelta (db1_a2hSQ <> db2_a2hSS) da_a2hSC in
                                               let
                                                 (d_a2hSX, df_a2hSY) = a_a2hSB
                                                 PairDelta (DFunD _ trNN_a2hSV) da_a2hSW = _v_a2hSU
                                                 (db1_a2hSZ, d1_a2hT0) = trNN_a2hSV d_a2hSX
                                                 (db2_a2hT1, d2_a2hT2) = df_a2hSY da_a2hSW d1_a2hT0
                                               in (db1_a2hSZ <> db2_a2hT1, func_a2hSz (d2_a2hST, df_a2hSP) (d2_a2hT2, df_a2hSY)))
                    in func_a2hSz (d_a2hSs, df_a2hSp) (d_a2hSy, df_a2hSv)))
