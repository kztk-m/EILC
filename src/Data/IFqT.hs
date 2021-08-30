{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TemplateHaskell           #-}

module Data.IFqT where

import           Data.Code            (Code, CodeC, PackedCode (PackedCode),
                                       PackedCodeDelta (PackedCodeDelta), mkLet)
import           Data.Delta           (Delta, pairDelta)
import           Data.Env             (Env (..))
import           Data.IFq             (Conn (..), IFq (..), decompConn, isNone,
                                       joinConn)
import           Data.Proxy           (Proxy (Proxy))
import           Language.Unembedding (LetTerm (..), Term (..))

data IFqT as b =
  forall cs. IFqT (Env Proxy as)
                  (Conn Proxy cs)
                  (Env PackedCode as -> CodeC (Code b, Conn PackedCode cs))
                  (Env PackedCodeDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))


instance Term IFq IFqT where
  mapTerm (IFq sh2 f2 tr2) (IFqT tenv sh1 f1 tr1) = IFqT tenv (joinConn sh1 sh2) f tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (db, c1') <- tr1 da c1
        (dc, c2') <- tr2 db c2
        return (dc, joinConn c1' c2')

  multTerm (IFqT tenv sh1 f1 tr1) (IFqT _ sh2 f2 tr2) = IFqT tenv (joinConn sh1 sh2) f tr
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

  unitTerm tenv = IFqT tenv CNone (\_ -> return ([|| () ||], CNone)) (\_ _ -> return ([|| mempty ||], CNone))

  var0Term tenv = IFqT (ECons Proxy tenv)
                       CNone
                       (\(ECons (PackedCode a) _) -> return (a, CNone))
                       (\(ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

  weakenTerm (IFqT tenv i f tr) = IFqT (ECons Proxy tenv) i f' tr'
    where
      f'  (ECons _ s) = f s
      tr' (ECons _ s) = tr s

  unliftTerm (IFqT _ i f tr) = IFq i f' tr'
    where
      f'  a  = f  (ECons (PackedCode       a) ENil)
      tr' da = tr (ECons (PackedCodeDelta da) ENil)

instance LetTerm IFq IFqT where
  letTerm (IFqT tenv sh1 f1 tr1) (IFqT _ sh2 f2 tr2) = IFqT tenv (joinConn sh1 sh2) f tr
    where
      f s = do
        (a, c1) <- f1 s
        v <- mkLet a
        (b, c2) <- f2 (ECons (PackedCode v) s)
        return (b, joinConn c1 c2)

      tr s cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (da, c1') <- tr1 s c1
        dv <- mkLet da
        (db, c2') <- tr2 (ECons (PackedCodeDelta dv) s) c2
        return (db, joinConn c1' c2')
