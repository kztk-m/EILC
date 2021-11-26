{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

module Data.IFqT where

import           Data.Code            (Code, CodeC, PackedCode,
                                       PackedCodeDelta (PackedCodeDelta),
                                       PackedCodeDiff (..), mkLet)
import           Data.Conn            (Conn (..), decompConn, isNone, joinConn)
import           Data.Delta           (Delta, pairDelta)
import           Data.Env             (Env (..))
import           Data.IFq             (IFqS (..), convTEnv)

import           Data.Code.Lifting    (WitTypeable (WitTypeable))
import           Language.Unembedding (LetTerm (..), Term (..))



data IFqT as b =
  forall cs. IFqT (Env WitTypeable as)
                  (Conn WitTypeable cs)
                  (CodeC (Env PackedCodeDiff  as -> CodeC (Code b, Conn PackedCode cs),
                          Env PackedCodeDelta as -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs)))


instance Term IFqS IFqT where
  mapTerm (IFqS sh2 m2) (IFqT tenv sh1 m1) = IFqT tenv (joinConn sh1 sh2) $ do
    (f1 , tr1) <- m1
    (f2 , tr2) <- m2
    let
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (db, c1') <- tr1 da c1
        (dc, c2') <- tr2 db c2
        return (dc, joinConn c1' c2')
    return (f , tr)


  multTerm (IFqT tenv sh1 m1) (IFqT _ sh2 m2) = IFqT tenv (joinConn sh1 sh2) $ do
    (f1 , tr1) <- m1
    (f2 , tr2) <- m2
    let
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
    return (f , tr)

  unitTerm tenv = IFqT (convTEnv tenv) CNone $
    return (\_ -> return ([|| () ||], CNone), \_ _ -> return ([|| mempty ||], CNone))

  var0Term tenv = IFqT (ECons WitTypeable $ convTEnv tenv) CNone $
                    return
                       (\(ECons (PackedCodeDiff a) _) -> return (a, CNone),
                        \(ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

  weakenTerm (IFqT tenv i m) = IFqT (ECons WitTypeable tenv) i $ do
    (f, tr) <- m
    let
      f'  (ECons _ s) = f s
      tr' (ECons _ s) = tr s
    return (f' , tr')

  unliftTerm (IFqT _ i m) = IFqS i $ do
    (f, tr) <- m
    let
      f'  a  = f  (ECons (PackedCodeDiff  a) ENil)
      tr' da = tr (ECons (PackedCodeDelta da) ENil)
    return (f' , tr')


instance LetTerm IFqS IFqT where
  letTerm (IFqT tenv sh1 m1) (IFqT _ sh2 m2) = IFqT tenv (joinConn sh1 sh2) $ do
    (f1, tr1) <- m1
    (f2, tr2) <- m2
    let
      f s = do
        (a, c1) <- f1 s
        v <- mkLet a
        (b, c2) <- f2 (ECons (PackedCodeDiff v) s)
        return (b, joinConn c1 c2)

      tr s cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (da, c1') <- tr1 s c1
        dv <- mkLet da
        (db, c2') <- tr2 (ECons (PackedCodeDelta dv) s) c2
        return (db, joinConn c1' c2')
    return (f, tr)
