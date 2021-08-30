{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeOperators             #-}

{-# LANGUAGE NoMonomorphismRestriction #-}


module Data.IFqTE where

import           Data.Code            (Code, CodeC, PackedCode (..),
                                       PackedCodeDelta (..), mkLet)
import           Data.Delta           (Delta, Diff ((/+)), pairDelta)
import           Data.Env             (Env (..))
import           Data.IFq             (Conn (..), IFq (..), IsNone (..), Join,
                                       NEConn (..), NETree (..), Tree (NE),
                                       decompConn, isNone, joinConn)
import           Data.Proxy           (Proxy (Proxy))
import           Language.Unembedding (LetTerm (..), Term (..))


data IFqTE as b =
  forall cs. IFqTE (Env Proxy as)
                   (Conn Proxy cs)
                   (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
                   (Env PackedCode as -> Env PackedCodeDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

instance Term IFq IFqTE where
  mapTerm (IFq sh2 f2 tr2) (IFqTE tenv sh1 f1 tr1) = IFqTE tenv (joinConn sh1 sh2) f tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr a da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (db, c1') <- tr1 a da c1
        (dc, c2') <- tr2 db c2
        return (dc, joinConn c1' c2')

  multTerm (IFqTE tenv sh1 f1 tr1) (IFqTE _ sh2 f2 tr2) = IFqTE tenv (joinConn sh1 sh2) f tr
    where
      f s = do
        (a, c1) <- f1 s
        (b, c2) <- f2 s
        r <- mkLet [|| ($$a, $$b) ||]
        return (r , joinConn c1 c2)

      tr s ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (da, c1') <- tr1 s ds c1
        (db, c2') <- tr2 s ds c2
        r <- mkLet [|| pairDelta $$da $$db ||]
        return ( r, joinConn c1' c2' )

  unitTerm tenv = IFqTE tenv CNone (\_ -> return ([|| () ||], CNone)) (\_ _ _ -> return ([|| mempty ||], CNone))

  var0Term tenv = IFqTE (ECons Proxy tenv)
                       CNone
                       (\(ECons (PackedCode a) _) -> return (a, CNone))
                       (\_ (ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

  weakenTerm (IFqTE tenv i f tr) = IFqTE (ECons Proxy tenv) i f' tr'
    where
      f'  (ECons _ s) = f s
      tr' (ECons _ s) (ECons _ ds) = tr s ds

  unliftTerm :: forall a b. Diff a =>  IFqTE '[a] b -> IFq a b
  unliftTerm (IFqTE _ (i :: Conn Proxy cs) f tr) = IFq @(Join ('NE ('NEOne a)) cs) @a @b sh f' tr'
    where
      sh :: Conn Proxy (Join ('NE ('NEOne a)) cs)
      sh = joinConn (CNE (COne (Proxy @a))) i

      f' :: Code a -> CodeC (Code b, Conn PackedCode (Join ('NE ('NEOne a)) cs))
      f'  a    = do
        (b, c) <- f (ECons (PackedCode       a) ENil)
        return (b, joinConn (CNE (COne (PackedCode a))) c)

      tr' :: Diff a => Code (Delta a) -> Conn PackedCode (Join ('NE ('NEOne a)) cs)
             -> CodeC (Code (Delta b), Conn PackedCode (Join ('NE ('NEOne a)) cs))
      tr' da cc | (c0, c) <- decompConn (IsNoneFalse :: IsNone ('NE ('NEOne a))) (isNone i) cc = do
        let CNE (COne (PackedCode a)) = c0
        (db, c') <- tr (ECons (PackedCode a) ENil) (ECons (PackedCodeDelta da) ENil) c
        return (db, joinConn (CNE (COne (PackedCode [|| $$a /+ $$da ||]))) c')

instance LetTerm IFq IFqTE where
  letTerm :: forall as a b. Diff a => IFqTE as a -> IFqTE (a ': as) b -> IFqTE as b
  letTerm (IFqTE tenv (sh1 :: Conn Proxy cs1) f1 tr1)
          (IFqTE _    (sh2 :: Conn Proxy cs2) f2 tr2) = IFqTE tenv sh f tr
    where
      shA :: Conn Proxy ('NE ('NEOne a))
      shA = CNE (COne (Proxy @a))

      sh :: Conn Proxy (Join ('NE ('NEOne a)) (Join cs1 cs2))
      sh = joinConn shA (joinConn sh1 sh2)

      f :: Env PackedCode as
          -> CodeC (Code b, Conn PackedCode (Join ('NE ('NEOne a)) (Join cs1 cs2)))
      f s = do
        (a, c1) <- f1 s
        v <- mkLet a
        (b, c2) <- f2 (ECons (PackedCode v) s)
        return (b, joinConn (CNE (COne (PackedCode v))) (joinConn c1 c2))

      tr s ds cc | (cA, c12) <- decompConn (isNone shA) (isNone (joinConn sh1 sh2)) cc,
                (c1, c2) <- decompConn (isNone sh1) (isNone sh2) c12 = do
        let CNE (COne (PackedCode a)) = cA
        (da, c1') <- tr1 s ds c1
        dv <- mkLet da
        (db, c2') <- tr2 (ECons (PackedCode a) s) (ECons (PackedCodeDelta dv) ds) c2
        return (db, joinConn (CNE (COne (PackedCode [|| $$a /+ $$dv ||]))) (joinConn c1' c2'))
