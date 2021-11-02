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
    toDynI, fromDynI, trDFunT,
    FunT(..), type Delta (..), IsEmpty(..),
  ) where

import           Data.Code
import           Data.Code.Lifting
import           Data.Conn
import           Data.Delta            (Delta (PairDelta), Diff (..), pairDelta)
import           Data.Dynamic          (Dynamic, fromDynamic, toDyn)
import           Data.Env              (Env (..), headTailEnv, mapEnv)
import           Data.Functor.Identity (Identity (..))
import           Data.IFq              (IFqS (..), ensureDiffType,
                                        mkInteraction)
import           Data.IFqT             (IFqT (..))
import           Data.IFqTEU
import           Data.Incrementalized  (IncrementalizedQ (fromStateless))
import           Data.Interaction      (Interaction (Interaction))
import           Data.Maybe            (fromJust, fromMaybe, isJust)
import           Data.Typeable         (Typeable, eqT, type (:~:) (..))
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

-- TODO: We should have a special treatment for the case where Dynamic ~ ()
newtype FunT a b = FunT (a -> (b, Dynamic))


{-
The one below is not that useful as it fails the separability.

data instance Delta (FunT a b) where
  DFunT
    ::
    !IsEmpty -- true if it is an empty change.
    -- NB: there is no guanrantee that Delta b is empty if Delta a is, especially
    -- when the original function uses free variables. The above Bool denotes a such a
    -- flag. That is, if the above is True, then the function is the empty change.
    -> !(Delta a -> Dynamic -> (Delta b, Dynamic))
    -> Delta (FunT a b)

Specifically, df c (da <> da') need not be
   let (db,  c1) = df c da
       (db', c2) = df c1 da'
   in (db <> db', c2)
because df may not be a nil change, meaning that df c empty /= (empty, c) for some c.

So, we should separate it to a pair of functions: a nil change and a may-not nil change.

   <df_nil, df> c da =
       let (db1, c1) = df c
           (db2, c2) = df_nil da c1
       in (db1 <> db2)

so that we can compose it as:

   <df_nil, df> c (da <> da') =
       let (db1, c1) = df c
           (db2, c2) = df_nil da c1
           (db3, c3) = df_nil da' c2
       in (db1 <> db2 <> db3)

-}

data instance Delta (FunT a b) =
  DFunT
    !IsEmpty -- true if its non-nil-change actually does nothing. That is, df0 d = (d, mempty)
    !(Dynamic -> (Delta b, Dynamic)) -- non nil change
    !(Delta a -> Dynamic -> (Delta b, Dynamic)) -- nil change


trDFunT :: Semigroup (Delta b) => Delta (FunT a b) -> (Delta a -> Dynamic -> (Delta b, Dynamic))
trDFunT (DFunT _ dfNN df) da c =
  let (db1, c1) = dfNN c
      (db2, c2) = df da c1
  in (db1 <> db2, c2)


-- data instance Delta (FunT a b) where
--   DFunT
--     ::
--     !IsEmpty -- true if it is an empty change.
--     -- NB: there is no guanrantee that Delta b is empty if Delta a is, especially
--     -- when the original function uses free variables. The above Bool denotes a such a
--     -- flag. That is, if the above is True, then the function is the empty change.
--     -> !(Delta a -> Dynamic -> (Delta b, Dynamic))
--     -> Delta (FunT a b)


data IsEmpty
  = FromMEmpty
  | Empty
  | Unk

instance Semigroup IsEmpty where
  FromMEmpty <> FromMEmpty = FromMEmpty
  FromMEmpty <> Empty      = Empty
  FromMEmpty <> Unk        = Unk
  Empty <> FromMEmpty      = Empty
  Empty <> Empty           = Empty
  Empty <> Unk             = Unk
  Unk <> _                 = Unk


applyDeltaFunT :: (Diff a, Diff b) => FunT a b -> Delta (FunT a b) -> FunT a b
applyDeltaFunT f (DFunT FromMEmpty _ _) = f
applyDeltaFunT f (DFunT Empty _ _)      = f
applyDeltaFunT (FunT f) (DFunT Unk dfNN _) = FunT $ \a ->
  let (b,  c)  = f a
      (db, c1) = dfNN c
  in (b /+ db, c1)

instance Semigroup (Delta b) => Semigroup (Delta (FunT a b)) where
  DFunT b1 dfNN1 df1 <> DFunT b2 dfNN2 df2 = DFunT (b1 <> b2) dfNN df
    where
      dfNN c = let (db1, c1) = dfNN1 c
                   (db2, c2) = dfNN2 c1
               in (db1 <> db2, c2)
      -- The definition below looks weird but recall that df mempty c = (mempty, c)
      -- So,
      --    let (db1, c1) = df1 da c
      --        (db2, c2) = df2 mempty c1
      --    in (db1 <> db2, c2)
      -- is df1

      df = case (b1, b2) of
        (FromMEmpty, _) -> df2
        _               -> df1

instance (Diff a, Monoid (Delta b)) => Monoid (Delta (FunT a b)) where
  -- This is correct only when `da` is mempty.
  -- Fortunately, the part cannot carry interesting information as deltas.
  mempty = DFunT FromMEmpty (\c -> (mempty, c)) $ \da c ->
            if checkEmpty da then
              (mempty, c)
            else
              error "mempty cannot handle non-nil changes."

instance (Diff a, Diff b) => Diff (FunT a b) where
  (/+) = applyDeltaFunT

  checkEmpty (DFunT FromMEmpty _ _) = True
  checkEmpty (DFunT Empty _ _)      = True
  checkEmpty (DFunT Unk _ _)        = False

  emptify (DFunT FromMEmpty _ df) = DFunT FromMEmpty (\c -> (mempty, c)) df
  emptify (DFunT _ _ df)          = DFunT Empty (\c -> (mempty, c)) df



allEmptyDelta :: forall xs. Env PackedCodeDelta xs -> Code Bool
allEmptyDelta ENil = [|| True ||]
allEmptyDelta (ECons (PackedCodeDelta da) ENil) = [|| checkEmpty $$da ||]
allEmptyDelta (ECons (PackedCodeDelta da) das)  = [|| checkEmpty $$da && $$(allEmptyDelta das) ||]

toDynI :: Typeable cs => Env Identity cs -> Dynamic
toDynI = toDyn

fromDynI :: Typeable cs => Dynamic -> Env Identity cs
fromDynI = fromJust Prelude.. fromDynamic

cLamT :: forall s a b. Diff a => IFqT (a ': s) b -> IFqT s (FunT a b)
cLamT (IFqT (ECons _ tenv) (sh :: Conn WitTypeable cs) m) = IFqT tenv CNone $
  case wit of
    Wit -> do
      (f, tr) <- m
      let
        h :: Env PackedCode s -> Code (a -> (b, Dynamic))
        h env = [|| \a -> $$(toCode $ do
                      (b, c') <- f (ECons (PackedCode [|| a ||]) env)
                      return [|| ($$b, toDyn $$(conn2cenv c')) ||]) ||]
        trH :: Env PackedCodeDelta s -> Code (Maybe (Delta a) -> Dynamic -> (Delta b, Dynamic))
        trH denv = [|| \maybe_da d -> $$(toCode $ do
                          -- For typing
                          c  <- mkLet [|| fromDynI d ||]
                          cs <- CodeC $ cenv2conn sh c
                          denv' <- mkLetEnvD $ mapEnv (\(PackedCodeDelta de) -> PackedCodeDelta [|| maybe Prelude.id (const emptify) maybe_da $$de ||]) denv
                          da'   <- mkLet [|| fromMaybe mempty maybe_da ||]
                          (db, cs') <- tr (ECons (PackedCodeDelta da') denv') cs
                          return [|| ($$db, toDynI $$(conn2cenv cs')) ||] ) ||]


        -- trH denv = [|| \da c ->
        --                 $$(cenv2conn sh [|| fromJust (fromDynamic c) ||] $ \cs -> toCode $ do
        --                     (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) denv) cs
        --                     return [|| ($$db, toDyn $$(conn2cenv cs')) ||]) ||]
      let
        f' env = do
            let ff = [|| FunT $$(h env) ||]
            return (ff, CNone)
        tr' denv _ = do
          trfunc <- mkLet $ trH denv
          let ftr = [|| DFunT (if $$(allEmptyDelta denv) then Empty else Unk) ($$trfunc Nothing) ($$trfunc Prelude.. Just) ||]
          return (ftr, CNone)
      return (f', tr')
    where
      wit :: Wit (Typeable (Flatten cs))
      wit = witTypeableFlatten sh

opAppT :: forall a b. Diff b => IFqS (FunT a b, a) b
opAppT = IFqS sh $
  return (f, tr)
  where
    sh :: Conn WitTypeable ('NE ('NEOne Dynamic))
    sh = CNE $ COne WitTypeable

    f :: Code (FunT a b, a) -> CodeC (Code b, Conn PackedCode ('NE ('NEOne Dynamic)))
    f cp = do
      (b, c) <- CodeC $ \k -> [|| case $$cp of
                        (FunT ff, a) ->
                          let (b, c) = ff a
                          in $$(k ([|| b ||] , [|| c ||])) ||]
      return (b, CNE $ COne $ PackedCode c)

    tr
      :: Code (Delta (FunT a b, a))
         -> Conn PackedCode ('NE ('NEOne Dynamic))
         -> CodeC (Code (Delta b), Conn PackedCode ('NE ('NEOne Dynamic)))
    tr dp (CNE (COne (PackedCode c))) = do
      (db, c') <- CodeC $ \k ->
                  [|| let PairDelta dfunT da = $$dp
                          (!db, c') = trDFunT dfunT da $$c
                      in $$(k ([|| db ||], [|| c' ||]) ) ||]
      return (db, CNE $ COne $ PackedCode c')

instance FunTerm IFqS IFqT where
  type IHom IFqS = FunT
  lamTerm = cLamT
  appTerm e1 e2 = mapTerm opAppT $ multTerm e1 e2


-- problematic :: (K cat a, K cat (IHom cat a a), App2 cat term e, FunTerm cat term) => e a -> e a
problematic x0 =
  -- (lam (\f -> lam $ \x -> f `app` (f `app` x)) `app` lam (\f -> lam $ \x -> f `app` (f `app` x))) `app` lam (lift incC) `app` x0
  lam (\f -> lam $ \x -> f `app` (f `app` x)) `app` lam (lift incC) `app` x0
  where
    incC = fromStateless (\x -> [|| succ $$x ||]) Prelude.id

spliced :: (Int -> (Int, Interaction (Delta Int) (Delta Int)))
spliced =
    ensureDiffType (\ pa_aWdc pb_aWdd a_aWde
            -> let
                 twice_inc --twice
                   = (FunT
                        (\ a_aWdg -- f
                           -> (FunT
                                 (\ a_aWdh -- x
                                    -> let _v_aWdi = (a_aWdg, a_aWdh)
                                       in
                                         case _v_aWdi of {
                                           (FunT ff_aWdj, a_aWdk)
                                             -> let (b_aWdl, c_aWdm) = ff_aWdj a_aWdk in
                                                let _v_aWdn = (a_aWdg, b_aWdl)
                                                in
                                                  case _v_aWdn of {
                                                    (FunT ff_aWdo, a_aWdp)
                                                      -> let (b_aWdq, c_aWdr) = ff_aWdo a_aWdp
                                                         in (b_aWdq, toDyn (ECons (Identity c_aWdm) (ECons (Identity c_aWdr) enilOfIdentity))) } }),
                               toDyn enilOfIdentity)),
                      FunT (\ a_aWds -> let _v_aWdt = succ a_aWds in (_v_aWdt, toDyn enilOfIdentity)))
               in
                 case twice_inc of {
                   (FunT ff_twice, f_inc)
                     -> let (b_aWdw, c_aWdx) = ff_twice f_inc in
                        let _v_aWdy = (b_aWdw, a_aWde)
                        in
                          case _v_aWdy of {
                            (FunT ff_twice_inc, a_aWdA)
                              -> let (b_aWdB, c_aWdC) = ff_twice_inc a_aWdA
                                 in
                                   (b_aWdB,
                                    let
                                      loop
                                        = \ !a_aWdE !a_aWdF -> mkInteraction pa_aWdc pb_aWdd (\ da
                                                            -> let
                                                                 _v_aWdH
                                                                   = \ maybe_df d_aWdJ
                                                                       -> let _v_aWdK = fromDynI d_aWdJ
                                                                          in
                                                                            (_v_aWdK
                                                                               `seqENil`
                                                                                 (let _v_aWdL = maybe Prelude.id (const emptify) maybe_df da in
                                                                                  let df' = fromMaybe mempty maybe_df in -- mempty comes here
                                                                                  let
                                                                                    _v_aWdN
                                                                                      = \ maybe_da_aWdO d_aWdP
                                                                                          -> let _v_aWdQ = fromDynI d_aWdP in
                                                                                             let (x_aWdR, xs_aWdS) = headTailEnv _v_aWdQ in
                                                                                             let (x_aWdT, xs_aWdU) = headTailEnv xs_aWdS
                                                                                             in
                                                                                               (xs_aWdU
                                                                                                  `seqENil`
                                                                                                    (let _v_aWdV = maybe Prelude.id (const emptify) maybe_da_aWdO _v_aWdL in
                                                                                                     let _v_aWdW = maybe Prelude.id (const emptify) maybe_da_aWdO df' in -- mempty goes here
                                                                                                     let _v_aWdX = fromMaybe mempty maybe_da_aWdO in
                                                                                                     let _v_aWdY = pairDelta _v_aWdW _v_aWdX in
                                                                                                     let
                                                                                                       PairDelta dfunT_aWdZ da_aWe0 = _v_aWdY
                                                                                                       (!db_aWe1, c'_aWe2) = trace ("da_aWe0: " ++ show da_aWe0) $ trDFunT dfunT_aWdZ da_aWe0 (runIdentity x_aWdR) in
                                                                                                     let _v_aWe3 = pairDelta _v_aWdW db_aWe1 in
                                                                                                     let
                                                                                                       PairDelta dfunT_aWe4 da_aWe5 = _v_aWe3
                                                                                                       (!db_aWe6, c'_aWe7) = trDFunT dfunT_aWe4 da_aWe5 (runIdentity x_aWdT)
                                                                                                     in (db_aWe6, toDynI (ECons (Identity c'_aWe2) (ECons (Identity c'_aWe7) enilOfIdentity)))))
                                                                                  in
                                                                                    (DFunT (if checkEmpty df' && checkEmpty _v_aWdL then Empty else Unk) (_v_aWdN Nothing)
                                                                                       (_v_aWdN Prelude.. Just),
                                                                                     toDynI enilOfIdentity))) in
                                                               let
                                                                 _v_aWe8
                                                                   = \ maybe_da_aWe9 d_aWea
                                                                       -> let _v_aWeb = fromDynI d_aWea
                                                                          in
                                                                            (_v_aWeb
                                                                               `seqENil`
                                                                                 (let _v_aWec = maybe Prelude.id (const emptify) maybe_da_aWe9 da in
                                                                                  let _v_aWed = fromMaybe mempty maybe_da_aWe9 in let _v_aWee = _v_aWed in (_v_aWee, toDynI enilOfIdentity))) in
                                                               let
                                                                 _v_aWef
                                                                   = pairDelta (DFunT (if checkEmpty da then Empty else Unk) (_v_aWdH Nothing) (_v_aWdH Prelude.. Just))
                                                                       (DFunT (if checkEmpty da then Empty else Unk) (_v_aWe8 Nothing) (_v_aWe8 Prelude.. Just)) in
                                                               let
                                                                 PairDelta dfunT_aWeg da_aWeh = _v_aWef
                                                                 (!db_aWei, c'_aWej) = trDFunT dfunT_aWeg da_aWeh a_aWdE in
                                                               let _v_aWek = pairDelta db_aWei da in
                                                               let
                                                                 PairDelta dfunT_aWel da_aWem = _v_aWek
                                                                 (!db_aWen, c'_aWeo) = trDFunT dfunT_aWel da_aWem a_aWdF
                                                               in (db_aWen, loop c'_aWej c'_aWeo))
                                    in loop c_aWdx c_aWdC) } })


-- applyDeltaFunT f (DFunT FromMEmpty _) = f
-- applyDeltaFunT f (DFunT Empty _) = f
-- applyDeltaFunT (FunT (f :: a -> (b, c))) (DFunT _ (tr :: (Delta a -> c' -> (Delta b, c'))))
--   = case (eqT :: Maybe (c :~: c')) of
--       Nothing   -> error "Cannot happen... Maybe."
--       Just Refl -> FunT $ \a ->
--         let (b,  c)  = f a
--             (db, c') = tr mempty c
--         in (b /+ db, c')

-- instance (Monoid (Delta a), Monoid (Delta b)) => Semigroup (Delta (FunT a b)) where
--   DFunT b1 (tr1 :: (Delta a -> c -> (Delta b, c))) <> DFunT b2 (tr2 :: (Delta a -> c' -> (Delta b, c')))
--     = case eqT :: Maybe (c :~: c') of
--         Nothing -> error "Cannot happen...Maybe."
--         Just Refl -> DFunT (b1 <> b2) $ \da c ->
--           case (b1, b2) of
--             (FromMEmpty, _) ->
--               let (db , c1) = tr1 mempty c
--                   (db', c2) = tr2 da c1
--               in (db <> db', c2)
--             _ ->
--               let (db , c1) = tr1 da c
--                   (db', c2) = tr2 mempty c1
--               in (db <> db', c2)


-- instance (Monoid (Delta b), Diff a) => Monoid (Delta (FunT a b)) where
--   -- This is correct only when `_da` is mempty
--   mempty = DFunT FromMEmpty $ \da c ->
--     if checkEmpty da then
--       (mempty, c)
--     else
--       error "mempty cannot handle non-nil changes."

-- instance (Diff a, Diff b) => Diff (FunT a b) where
--   (/+) = applyDeltaFunT

--   checkEmpty (DFunT FromMEmpty _) = True
--   checkEmpty (DFunT Empty _)      = True
--   checkEmpty (DFunT _ _)          = False


-- type EncCS cs2 = Env Identity (Flatten cs2)

-- allEmptyDelta :: forall xs. Env PackedCodeDelta xs -> Code Bool
-- allEmptyDelta ENil = [|| True ||]
-- allEmptyDelta (ECons (PackedCodeDelta da) ENil) = [|| checkEmpty $$da ||]
-- allEmptyDelta (ECons (PackedCodeDelta da) das)  = [|| checkEmpty $$da && $$(allEmptyDelta das) ||]

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
--         trH :: Env PackedCodeDelta s -> Code (Delta a -> Dynamic -> (Delta b, Dynamic))
--         trH denv = [|| \da c ->
--                         $$(cenv2conn sh [|| fromJust (fromDynamic c) ||] $ \cs -> toCode $ do
--                             (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) denv) cs
--                             return [|| ($$db, toDyn $$(conn2cenv cs')) ||]) ||]
--       let
--         f' env = do
--             ff <- mkLet [|| FunT $$(h env) ||]
--             return (ff, CNone)
--         tr' denv _ = do
--           ftr <- mkLet [|| DFunT (if $$(allEmptyDelta denv) then Empty else Unk) $$(trH denv) ||]
--           return (ftr, CNone)
--       return (f', tr')
--     where
--       wit :: Wit (Typeable (Flatten cs))
--       wit = witTypeableFlatten sh

-- cLamTEUS :: forall s a b. (Typeable a, Diff a) => IFqTEUS (a ': s) b -> IFqTEUS s (FunT a b)
-- cLamTEUS (IFqTEUS (ECons _ tenv) (sh :: Conn WitTypeable cs) (u :: Env SBool us_f) (ut :: Env SBool us_tr) m) = IFqTEUS tenv CNone (safeTail u) (safeTail ut) $ case wit of
--   Wit -> do
--     (f, tr) <- m
--     let
--       h :: Env PackedCode (Extr s (SafeTail us_f)) -> CodeC (Code (a -> (b, Dynamic)))
--       h env = case u of
--         ENil -> do
--           (b, c) <- f ENil
--           -- let floating
--           bc <- mkLet b
--           cc <- mkLet $ conn2cenv c
--           return $ case ut of { ECons STrue _ -> [|| \a -> ($$bc, toDyn ($$cc, a)) ||]; _ -> [|| const ($$bc, toDyn $$cc) ||]}
--         ECons SFalse _ -> do -- intentionally identical code to the above
--           (b, c) <- f env
--           -- let floating
--           bc <- mkLet b
--           cc <- mkLet $ conn2cenv c
--           return $ case ut of { ECons STrue _ -> [|| \a -> ($$bc, toDyn ($$cc, a)) ||]; _ -> [|| const ($$bc, toDyn $$cc) ||]}
--         ECons STrue _ -> return $
--           [|| \a -> $$(toCode $ do
--             (b, c) <- f (ECons (PackedCode [|| a ||]) env)
--             return [|| ($$b, $$(preserveA [|| a ||] (conn2cenv c) )) ||])  ||]

--       h_tr ::
--         Env PackedCode (Extr s (SafeTail us_tr))
--         -> Env PackedCodeDelta (Extr s (SafeTail us_f))
--         -> Code (Delta a -> Dynamic -> (Delta b, Dynamic))
--       h_tr env denv = case ut of
--         -- FIXME: further hosting is possible when we know we do not need da.
--         -- Also, we should care the case where f does not use d.
--         ENil ->
--           [|| \da d -> $$(code2conn sh [|| fromJust (fromDynamic d) ||] $ \cs -> toCode $ do
--                                       (db, cs') <- tr env (extendEnv tenv u (PackedCodeDelta [|| da ||]) denv) cs
--                                       return [|| ($$db, toDyn $$(conn2code cs')) ||]) ||]
--         ECons SFalse _ ->
--           [|| \da d -> $$(code2conn sh [|| fromJust (fromDynamic d) ||] $ \cs -> toCode $ do
--                                     (db, cs') <- tr env (extendEnv tenv u (PackedCodeDelta [|| da ||]) denv) cs
--                                     return [|| ($$db, toDyn $$(conn2code cs')) ||]) ||]
--         ECons STrue _ ->
--           [|| \da d ->
--                 let (Just (c', a)) = fromDynamic d
--                 in $$(code2conn sh [|| c' ||] $ \cs -> toCode $ do
--                     (db, cs') <- tr (extendEnv tenv ut (PackedCode [|| a ||]) env) (extendEnv tenv u (PackedCodeDelta [|| da ||]) denv) cs
--                     a' <- mkLet [|| a /+ da ||]
--                     return [|| ($$db, toDyn ($$(conn2code cs'), $$a') ) ||]) ||]

--     let
--       f' :: Env PackedCode (Extr s (SafeTail us_f)) -> CodeC (Code (FunT a b), Conn PackedCode 'None)
--       f' env = do
--         ff <- h env
--         funT <- mkLet [|| FunT $$ff ||]
--         return (funT, CNone)
--       tr'
--         :: Env PackedCode (Extr s (SafeTail us_tr))
--           -> Env PackedCodeDelta (Extr s (SafeTail us_f))
--           -> Conn PackedCode 'None
--           -> CodeC (Code (Delta (FunT a b)), Conn PackedCode 'None)
--       tr' env denv _ = do
--           ftr <- mkLet [|| DFunT (if $$(allEmptyDelta denv) then Empty else Unk) $$(h_tr env denv) ||]
--           return (ftr, CNone)
--     return (f', tr')
--   where
--     wit :: Wit (Typeable (Flatten cs), Typeable cs)
--     wit = witTypeableConn sh

--     preserveA :: (Typeable a, Typeable c) => Code a -> Code c -> Code Dynamic
--     preserveA a c = case ut of { ECons STrue _ -> [|| toDyn ($$a, $$c) ||]; _ -> [|| toDyn $$c ||]}


-- opAppT :: forall a b. Diff b => IFqS (FunT a b, a) b
-- opAppT = IFqS sh $ do
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
--                   [|| let PairDelta (DFunT _ ftr) da = $$dp
--                           (db, c') = ftr da $$c
--                       in $$(k ([|| db ||], [|| c' ||])) ||]
--       return (db, CNE $ COne $ PackedCode c')


-- instance FunTerm IFqS IFqT where
--   type IHom IFqS a b = FunT a b
--   lamTerm = cLamT
--   appTerm e1 e2 = mapTerm opAppT $ multTerm e1 e2

-- instance FunTerm IFqS IFqTEUS where
--   type IHom IFqS a b = FunT a b
--   lamTerm = cLamTEUS
--   appTerm e1 e2 = mapTerm opAppT $ multTerm e1 e2




-- data FunT a b where
--   MkFunT
--     :: (Typeable env, Typeable c)
--     => (a -> env -> (b, c))
--     -> env
--     -> FunT a b

-- data instance Delta (FunT a b) where
--   MkFunTD
--     :: (Diff env, Typeable env, Typeable c)
--     => (Delta a -> Delta env -> c -> (Delta b, c))
--     -> Delta env
--     -> Delta (FunT a b)
--   FunTDEmpty :: Delta (FunT a b)

-- instance Semigroup (Delta (FunT a b)) where
--   FunTDEmpty <> a          = a
--   a <> FunTDEmpty          = a

--   -- FIXME: I don't think it is correct but compatible with (/+)
--   _ <> a@(MkFunTD _ _ _ _) = a

-- instance Monoid (Delta (FunT a b)) where
--   mempty = FunTDEmpty

-- instance Diff (FunT a b) where
--   a /+ FunTDEmpty           = a
--   _ /+ MkFunTD f _ env denv = MkFunT f (env /+ denv)

--   checkEmpty FunTDEmpty           = True
--   checkEmpty (MkFunTD _ _ _ denv) = checkEmpty denv

-- type EncCS cs2 = Env Identity (Flatten cs2)

-- -- This should be moved to appropriate module.
-- packEnv :: Env PackedCode s -> Code (Env Identity s)
-- packEnv ENil                      = [|| ENil ||]
-- packEnv (ECons (PackedCode a) as) = [|| ECons (Identity $$a) $$(packEnv as) ||]

-- unpackEnv :: Env proxy s -> Code (Env Identity s) -> (Env PackedCode s -> Code r) -> Code r
-- unpackEnv ENil c k =
--   [|| case $$c of { ENil -> $$(k ENil) } ||]
-- unpackEnv (ECons _ s) c k =
--   [|| let (Identity _a, as) = headTailEnv $$c
--       in $$(unpackEnv s [|| as ||] (k . ECons (PackedCode [|| _a ||]))) ||]

-- cLamT :: forall s a b. IFqT (a ': s) b -> IFqT s (FunT a b)
-- cLamT (IFqT (ECons _ tenv) (sh :: Conn Proxy cs) m) = IFqT tenv sh' $ do
--   (f, tr) <- m
--   let
--     h :: Code (a -> Env Identity s -> (b, EncCS cs))
--     h = [|| \a penv -> $$(unpackEnv tenv [|| penv ||] $ \env -> toCode $ do
--       (b, c') <- f (ECons (PackedCode [|| a ||]) env)
--       return [|| ($$b, $$(conn2cenv c')) ||]) ||]
--   func <- mkLet h
--   let
--     trH :: Code (Delta a -> Delta (Env Identity s) -> EncCS cs -> (Delta b, EncCS cs))
--     trH = [|| \da denv ecs ->
--                   _
--            ||]
--     funT :: Env PackedCode s -> CodeC (Code (FunT a b), Conn PackedCode 'None)
--     funT env = return ( [|| MkFunT $$func $$(packEnv env) ||] , CNone)

--     funTD :: Env PackedCodeDelta s
--               -> Conn PackedCode 'None
--               -> CodeC (Code (Delta (FunT a b)), Conn PackedCode 'None)
--     funTD denv _ = return ( [|| MkFunTD $$func $$trH _ _ ||], CNone )
--   return (funT, _)
--   where
--     sh' = CNone












