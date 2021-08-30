{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module EILC (
  module Data.Code,
  module Data.Delta,
  module Data.IFq,
  module Data.IFqT,
  module Data.IFqTE,
  ) where

import           Data.Coerce           (coerce)
import           Data.Functor.Identity
import           Data.Typeable         (Proxy (..))
import           Prelude               hiding (id, (.))

import qualified Language.Haskell.TH   as TH

import           Control.Applicative   (Alternative (..))
import           Data.Env
import           Data.Kind             (Type)
import           Language.Unembedding
import qualified Text.Show

import           Data.Code
import           Data.Delta
import           Data.IFq

import           Data.IFqT
import           Data.IFqTE


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



dumpCode :: Code a -> IO ()
dumpCode c = do
  e <- TH.runQ c
  putStrLn $ TH.pprint (TH.unType e)





runAppMono' :: (Term cat term, K cat a, K cat b) => (TSem cat term a -> TSem cat term b) -> cat a b
runAppMono' = runMono

-- newtype PackedCodeDelta a = PackedCodeDelta { getCodeDelta :: Code (Delta a) }



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



data IFqA a b where
  IFqA ::
    Conn Proxy cs
    -> (Code a -> CodeC (Code b, Conn PackedCode cs))
    -> (Code (AtomicDelta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
    -> IFqA a b

-- Just to surpress type errors.
foldrDelta :: (AtomicDelta a -> b -> b) -> b -> Delta a -> b
foldrDelta = foldr
{-# INLINE foldrDelta #-}

iterTrC ::
  forall cs a b.
  Conn Proxy cs
  -> (Code (AtomicDelta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
  -> (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
iterTrC proxy h das0 cs0 = CodeC $ \(k :: (Code (Delta b), Conn PackedCode cs) -> Code r) ->
  [||
    -- f :: AtomicDelta a -> (Delta b -> Func cs r) -> Delta b -> Func cs r
    let f da cont = \acc -> $$(mkAbs proxy $ \cs ->
                runCodeC (h [|| da ||] cs) $ \(dbs1, cs') ->
                  mkApp @cs @r [|| cont (acc <> $$dbs1) ||] cs')
    in $$(mkApp [|| foldrDelta f (\acc -> $$(mkAbs proxy $ \cs -> k ([|| acc ||], cs))) $$das0  mempty ||] cs0)
   ||]

-- ifqAFromStateless :: (Code a -> Code b) -> (Code (Delta a) -> Code (Delta b)) -> IFqA a b
-- ifqAFromStateless f df =
--   IFqA CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df [|| injMonoid $$da ||]) ; return (v, CNone) })

-- ifqAFromD :: Diff a => (Code a -> Code b) -> (Code a -> Code (Delta a) -> Code (Delta b)) -> IFqA a b
-- ifqAFromD f df =
--   IFqA
--     (CNE (COne Proxy))
--     (\a -> do { v <- mkLet (f a) ; return (v, CNE (COne (PackedCode a))) })
--     (\da (CNE (COne (PackedCode a))) -> do { v <- mkLet (df a [|| injMonoid $$da ||]) ; a' <- mkLet [|| applyAtomicDelta $$a $$da ||] ; return (v, CNE (COne (PackedCode a'))) })

-- ifqAFromFunctions :: Code (a -> (b, c)) -> Code (Delta a -> c -> (Delta b, c)) -> IFqA a b
-- ifqAFromFunctions f df =
--   IFqA (CNE (COne Proxy))
--        (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
--        (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
--         [|| let (db, c') = $$df (injMonoid $$da) $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

ifqAFromStatelessA :: (Code a -> Code b) -> (Code (AtomicDelta a) -> Code (Delta b)) -> IFqA a b
ifqAFromStatelessA f df =
  IFqA CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df da) ; return (v, CNone) })

ifqFromStatelessA :: (Code a -> Code b) -> (Code (AtomicDelta a) -> Code (Delta b)) -> IFq a b
ifqFromStatelessA f df = ifqa2ifq $ ifqAFromStatelessA f df

ifqAFromAD :: Diff a => (Code a -> Code b) -> (Code a -> Code (AtomicDelta a) -> Code (Delta b)) -> IFqA a b
ifqAFromAD f df =
  IFqA
    (CNE (COne Proxy))
    (\a -> do { v <- mkLet (f a) ; return (v, CNE (COne (PackedCode a))) })
    (\da (CNE (COne (PackedCode a))) -> do { v <- mkLet (df a da) ; a' <- mkLet [|| applyAtomicDelta $$a $$da ||] ; return (v, CNE (COne (PackedCode a'))) })

ifqFromAD :: Diff a => (Code a -> Code b) -> (Code a -> Code (AtomicDelta a) -> Code (Delta b)) -> IFq a b
ifqFromAD f df = ifqa2ifq $ ifqAFromAD f df


ifqAFromFunctionsA :: Code (a -> (b, c)) -> Code (AtomicDelta a -> c -> (Delta b, c)) -> IFqA a b
ifqAFromFunctionsA f df =
  IFqA (CNE (COne Proxy))
       (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
       (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
        [|| let (db, c') = $$df $$da $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

ifqFromFunctionsA :: Code (a -> (b, c)) -> Code (AtomicDelta a -> c -> (Delta b, c)) -> IFq a b
ifqFromFunctionsA f df = ifqa2ifq $ ifqAFromFunctionsA f df


instance CategoryK IFqA where
  type K IFqA = Diff
  id = IFqA CNone (\a -> return (a, CNone)) (\da _ -> return ([|| injMonoid $$da ||], CNone))
  IFqA sh2 f2 tr2 . IFqA sh1 f1 tr1 = IFqA (joinConn sh1 sh2) f tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (dbs, c1') <- tr1 da c1
        (dcs, c2') <- iterTrC sh2 tr2 dbs c2
        return (dcs, joinConn c1' c2')



ifqa2ifq :: IFqA a b -> IFq a b
ifqa2ifq (IFqA sh f tr) = IFq sh f (iterTrC sh tr)





-- runIFqA :: IFqA a b -> Code (a -> (b, Interaction (Delta a) (Delta b) ))
-- runIFqA = runIFq . ifqa2ifq


-- data PackedCodeAtomicDelta a where
--   PackedCodeAtomicDelta :: Diff a => Code (AtomicDelta a) -> PackedCodeAtomicDelta a

-- mkUpdateEnv :: Index PackedCodeAtomicDelta as -> Env PackedCode as -> CodeC (Env PackedCode as)
-- mkUpdateEnv (IndexZ (PackedCodeAtomicDelta da)) (ECons (PackedCode a) as) = do
--   a' <- mkLet [|| applyAtomicDelta $$a $$da ||]
--   return (ECons (PackedCode a') as)
-- mkUpdateEnv (IndexS ix) (ECons a as) = do
--   as' <- mkUpdateEnv ix as
--   return $ ECons a as'



-- data IFqAT as b =
--   forall cs. IFqAT (Env Proxy as)
--                    (Conn Proxy cs)
--                    (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
--                    (Index PackedCodeAtomicDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))


-- instance HasProduct IFqA where
--   type Unit IFqA = ()
--   type Prod IFqA a b = (a, b)

--   unitOk _ = Wit
--   prodOk _ _ _ = Wit

-- instance Term IFqA IFqAT where
--   mapTerm (IFqA sh2 f2 tr2) (IFqAT tenv sh1 f1 tr1) = IFqAT tenv (joinConn sh1 sh2) f tr
--     where
--       f a = do
--         (b, c1) <- f1 a
--         (c, c2) <- f2 b
--         return (c, joinConn c1 c2)

--       tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--         (db, c1') <- tr1 da c1
--         (dc, c2') <- iterTrC sh2 tr2 db c2
--         return (dc, joinConn c1' c2')

--   multTerm (IFqAT tenv sh1 f1 tr1) (IFqAT _ sh2 f2 tr2) = IFqAT tenv (joinConn sh1 sh2) f tr
--     where
--       f s = do
--         (a, c1) <- f1 s
--         (b, c2) <- f2 s
--         r <- mkLet [|| ($$a, $$b) ||]
--         return (r , joinConn c1 c2)

--       tr ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--         (da, c1') <- tr1 ds c1
--         (db, c2') <- tr2 ds c2
--         r <- mkLet [|| pairDelta $$da $$db ||]
--         return ( r, joinConn c1' c2' )

--   unitTerm tenv = IFqAT tenv CNone (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| mempty ||], CNone))

--   var0Term tenv = IFqAT (ECons Proxy tenv)
--                         CNone
--                         (\(ECons (PackedCode a) _) -> return (a, CNone))
--                         (\denv _ -> case denv of
--                             IndexZ (PackedCodeAtomicDelta da) -> return ([|| injMonoid $$da ||], CNone)
--                             _         -> return ([|| mempty ||], CNone))
-- --                         (\(ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

--   weakenTerm (IFqAT tenv i f tr) = IFqAT (ECons Proxy tenv) i f' tr'
--     where
--       f'  (ECons _ s) = f s
--       tr' (IndexS ix) = tr ix
--       tr' _           = \cs -> return ([|| mempty ||],  cs)

--   unliftTerm (IFqAT _ i f tr) = IFqA i f' tr'
--     where
--       f'  a  = f  (ECons (PackedCode       a) ENil)
--       tr' da = tr (IndexZ (PackedCodeAtomicDelta da))


-- letTermIFqAT :: Diff b1 => IFqAT as b1 -> IFqAT (b1 : as) b2 -> IFqAT as b2
-- letTermIFqAT (IFqAT tenv sh1 f1 tr1) (IFqAT _ sh2 f2 tr2) = IFqAT tenv (joinConn sh1 sh2) f tr
--   where
--     f s = do
--       (a, c1) <- f1 s
--       v <- mkLet a
--       (b, c2) <- f2 (ECons (PackedCode v) s)
--       return (b, joinConn c1 c2)

--     tr s cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--       (da, c1') <- tr1 s c1
--       dvs <- mkLet da
--       (db1, c2' ) <- tr2 (IndexS s) c2
--       (db2, c2'') <- iterTrC sh2 (\dv -> tr2 (IndexZ $ PackedCodeAtomicDelta dv)) dvs c2'
--       return ([|| $$db1 <> $$db2 ||], joinConn c1' c2'')

-- -- FIXME: tentative
-- shareA :: forall e r1 r2. (Diff r1, App2 IFqA IFqAT e) => e r1 -> (e r1 -> e r2) -> e r2
-- shareA = liftSO2 (Proxy @'[ '[], '[r1] ] ) letTermIFqAT



-- data IFqATM as b =
--   forall cs. IFqATM (Env Proxy as)
--                     (Conn Proxy cs)
--                     (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
--                     (Env PackedCodeAtomicDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

-- instance Term IFqA IFqATM where
--   mapTerm (IFqA sh2 f2 tr2) (IFqATM tenv sh1 f1 tr1) = IFqATM tenv (joinConn sh1 sh2) f tr
--     where
--       f a = do
--         (b, c1) <- f1 a
--         (c, c2) <- f2 b
--         return (c, joinConn c1 c2)

--       tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--         (db, c1') <- tr1 da c1
--         (dc, c2') <- iterTrC sh2 tr2 db c2
--         return (dc, joinConn c1' c2')

--   multTerm (IFqATM tenv sh1 f1 tr1) (IFqATM _ sh2 f2 tr2) = IFqATM tenv (joinConn sh1 sh2) f tr
--     where
--       f s = do
--         (a, c1) <- f1 s
--         (b, c2) <- f2 s
--         r <- mkLet [|| ($$a, $$b) ||]
--         return (r , joinConn c1 c2)

--       tr ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--         (da, c1') <- tr1 ds c1
--         (db, c2') <- tr2 ds c2
--         r <- mkLet [|| pairDelta $$da $$db ||]
--         return ( r, joinConn c1' c2' )

--   unitTerm tenv = IFqATM tenv CNone (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| mempty ||], CNone))

--   var0Term tenv = IFqATM (ECons Proxy tenv)
--                          CNone
--                          (\(ECons (PackedCode a) _) -> return (a, CNone))
--                          (\denv _ -> case denv of
--                             ECons (PackedCodeAtomicDelta da) _ -> return ([|| injMonoid $$da ||], CNone))
-- --                         (\(ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

--   weakenTerm (IFqATM tenv i f tr) = IFqATM (ECons Proxy tenv) i f' tr'
--     where
--       f'  (ECons _ s) = f s
--       tr' (ECons _ denv) = tr denv

--   unliftTerm (IFqATM _ i f tr) = IFqA i f' tr'
--     where
--       f'  a  = f  (ECons (PackedCode       a) ENil)
--       tr' da = tr (ECons (PackedCodeAtomicDelta da) ENil)

-- -- Given : Env PackedCodeAtomicDelta (a : as) -> cs -> CodeC (Code (Delta b), cs)
-- -- Find : Code (Delta a) -> Env PackedCodeAtomicDelta as -> cs -> CodeC (Code (Delta b), cs)

-- letTermIFqATM :: Diff b1 => IFqATM as b1 -> IFqATM (b1 : as) b2 -> IFqATM as b2
-- letTermIFqATM (IFqATM tenv sh1 f1 tr1) (IFqATM _ sh2 f2 tr2) = IFqATM tenv (joinConn sh1 sh2) f tr
--   where
--     f s = do
--       (a, c1) <- f1 s
--       v <- mkLet a
--       (b, c2) <- f2 (ECons (PackedCode v) s)
--       return (b, joinConn c1 c2)

--     tr s cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--       (da, c1') <- tr1 s c1
--       dvs <- mkLet da
--       (db1, c2' ) <- tr2 (IndexS s) c2
--       (db2, c2'') <- iterTrC sh2 (\dv -> tr2 (IndexZ $ PackedCodeAtomicDelta dv)) dvs c2'
--       return ([|| $$db1 <> $$db2 ||], joinConn c1' c2'')





