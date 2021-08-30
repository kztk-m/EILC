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

import           Prelude    hiding (id, (.))


import           Data.Code
import           Data.Delta
import           Data.IFq

import           Data.IFqT
import           Data.IFqTE




-- data IFqA a b where
--   IFqA ::
--     Conn Proxy cs
--     -> (Code a -> CodeC (Code b, Conn PackedCode cs))
--     -> (Code (AtomicDelta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
--     -> IFqA a b

-- -- Just to surpress type errors.
-- foldrDelta :: (AtomicDelta a -> b -> b) -> b -> Delta a -> b
-- foldrDelta = foldr
-- {-# INLINE foldrDelta #-}

-- iterTrC ::
--   forall cs a b.
--   Conn Proxy cs
--   -> (Code (AtomicDelta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
--   -> (Code (Delta a) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))
-- iterTrC proxy h das0 cs0 = CodeC $ \(k :: (Code (Delta b), Conn PackedCode cs) -> Code r) ->
--   [||
--     -- f :: AtomicDelta a -> (Delta b -> Func cs r) -> Delta b -> Func cs r
--     let f da cont = \acc -> $$(mkAbs proxy $ \cs ->
--                 runCodeC (h [|| da ||] cs) $ \(dbs1, cs') ->
--                   mkApp @cs @r [|| cont (acc <> $$dbs1) ||] cs')
--     in $$(mkApp [|| foldrDelta f (\acc -> $$(mkAbs proxy $ \cs -> k ([|| acc ||], cs))) $$das0  mempty ||] cs0)
--    ||]

-- -- ifqAFromStateless :: (Code a -> Code b) -> (Code (Delta a) -> Code (Delta b)) -> IFqA a b
-- -- ifqAFromStateless f df =
-- --   IFqA CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df [|| injMonoid $$da ||]) ; return (v, CNone) })

-- -- ifqAFromD :: Diff a => (Code a -> Code b) -> (Code a -> Code (Delta a) -> Code (Delta b)) -> IFqA a b
-- -- ifqAFromD f df =
-- --   IFqA
-- --     (CNE (COne Proxy))
-- --     (\a -> do { v <- mkLet (f a) ; return (v, CNE (COne (PackedCode a))) })
-- --     (\da (CNE (COne (PackedCode a))) -> do { v <- mkLet (df a [|| injMonoid $$da ||]) ; a' <- mkLet [|| applyAtomicDelta $$a $$da ||] ; return (v, CNE (COne (PackedCode a'))) })

-- -- ifqAFromFunctions :: Code (a -> (b, c)) -> Code (Delta a -> c -> (Delta b, c)) -> IFqA a b
-- -- ifqAFromFunctions f df =
-- --   IFqA (CNE (COne Proxy))
-- --        (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
-- --        (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
-- --         [|| let (db, c') = $$df (injMonoid $$da) $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

-- ifqAFromStatelessA :: (Code a -> Code b) -> (Code (AtomicDelta a) -> Code (Delta b)) -> IFqA a b
-- ifqAFromStatelessA f df =
--   IFqA CNone (\a -> do { v <- mkLet (f a); return (v, CNone) }) (\da _ -> do { v <- mkLet (df da) ; return (v, CNone) })

-- ifqFromStatelessA :: (Code a -> Code b) -> (Code (AtomicDelta a) -> Code (Delta b)) -> IFq a b
-- ifqFromStatelessA f df = ifqa2ifq $ ifqAFromStatelessA f df

-- ifqAFromAD :: Diff a => (Code a -> Code b) -> (Code a -> Code (AtomicDelta a) -> Code (Delta b)) -> IFqA a b
-- ifqAFromAD f df =
--   IFqA
--     (CNE (COne Proxy))
--     (\a -> do { v <- mkLet (f a) ; return (v, CNE (COne (PackedCode a))) })
--     (\da (CNE (COne (PackedCode a))) -> do { v <- mkLet (df a da) ; a' <- mkLet [|| applyAtomicDelta $$a $$da ||] ; return (v, CNE (COne (PackedCode a'))) })

-- ifqFromAD :: Diff a => (Code a -> Code b) -> (Code a -> Code (AtomicDelta a) -> Code (Delta b)) -> IFq a b
-- ifqFromAD f df = ifqa2ifq $ ifqAFromAD f df


-- ifqAFromFunctionsA :: Code (a -> (b, c)) -> Code (AtomicDelta a -> c -> (Delta b, c)) -> IFqA a b
-- ifqAFromFunctionsA f df =
--   IFqA (CNE (COne Proxy))
--        (\a -> CodeC $ \k -> [|| let (b, c) = $$f $$a in $$(k ([|| b ||], CNE (COne (PackedCode [|| c ||]))) ) ||])
--        (\da (CNE (COne (PackedCode c))) -> CodeC $ \k ->
--         [|| let (db, c') = $$df $$da $$c in $$(k ([|| db ||], CNE (COne (PackedCode [|| c' ||])))) ||])

-- ifqFromFunctionsA :: Code (a -> (b, c)) -> Code (AtomicDelta a -> c -> (Delta b, c)) -> IFq a b
-- ifqFromFunctionsA f df = ifqa2ifq $ ifqAFromFunctionsA f df


-- instance CategoryK IFqA where
--   type K IFqA = Diff
--   id = IFqA CNone (\a -> return (a, CNone)) (\da _ -> return ([|| injMonoid $$da ||], CNone))
--   IFqA sh2 f2 tr2 . IFqA sh1 f1 tr1 = IFqA (joinConn sh1 sh2) f tr
--     where
--       f a = do
--         (b, c1) <- f1 a
--         (c, c2) <- f2 b
--         return (c, joinConn c1 c2)

--       tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
--         (dbs, c1') <- tr1 da c1
--         (dcs, c2') <- iterTrC sh2 tr2 dbs c2
--         return (dcs, joinConn c1' c2')



-- ifqa2ifq :: IFqA a b -> IFq a b
-- ifqa2ifq (IFqA sh f tr) = IFq sh f (iterTrC sh tr)




