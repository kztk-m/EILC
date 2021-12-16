{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Incrementalized.Bool
  (
    Delta(..),

    delay, Lazy,

    IfTerm(..), if_,

    notF, notC,

  ) where

import           Prelude                             hiding (id, (.))

import           Data.Delta

import           Data.Code
import           Data.Code.Lifting                   (WitTypeable (WitTypeable))
import           Data.Conn
import           Data.Env
import           Data.IFq
import           Data.IFqT
import           Data.IFqTU
import           Data.JoinList
import           Data.Typeable                       (Proxy (Proxy), Typeable)
import           Language.Unembedding
import           Language.Unembedding.PseudoFunction

-- As an interesting case study, here we handle Booleans here.

-- As an interesting case study, here we handle Booleans here.
import           Data.Incrementalized                (IncrementalizedQ,
                                                      fromStatelessCode)
import           Data.Incrementalized.Function

-- $setup
-- >>> :set -XTemplateHaskell -XFlexibleContexts -XGADTs -XTypeApplications -XRankNTypes -XScopedTypeVariables
-- >>> import Data.Incrementalized (fromStatelessCode, compileCode)
-- >>> import Data.Interaction (iterations)
-- >>> let doubleC = fromStatelessCode (\x -> [|| 2 * $$x ||] :: Code Int) (\dx -> [|| 2 * $$dx ||])
-- >>> :{
-- fstF :: forall cat e a b.
--         (Cartesian cat, Prod cat a b ~ (a, b), App cat e, K cat a, K cat b, K cat (a, b))
--          => e (a, b) -> e a
-- fstF = lift (fstS (Proxy @a) (Proxy @b))
-- sndF :: forall cat e a b.
--         (Cartesian cat, Prod cat a b ~ (a, b), App cat e, K cat a, K cat b, K cat (a, b))
--          => e (a, b) -> e b
-- sndF = lift (sndS (Proxy @a) (Proxy @b))
-- :}
--
-- >>> let func = $$( compileCode $ runMonoWith (Proxy :: Proxy IFqTU) $ \ab -> share (sndF ab) $ \b -> if_ (fstF ab) b (lift doubleC b) )

-- | Delta Booleans.
data instance Delta Bool = DBKeep | DBNot
  deriving stock (Show, Eq)

instance Semigroup (Delta Bool) where
  -- | Essentially, '<>' is defined as the exclusive or.
  DBKeep <> DBKeep = DBKeep
  DBKeep <> DBNot  = DBNot
  DBNot  <> DBKeep = DBNot
  DBNot  <> DBNot  = DBKeep
  {-# INLINE (<>) #-}

instance Monoid (Delta Bool) where
  mempty = DBKeep
  {-# INLINE mempty #-}

instance Diff Bool where
  x /+ DBKeep = x
  x /+ DBNot  = not x
  {-# INLINE (/+) #-}

  checkEmpty DBKeep = True
  checkEmpty DBNot  = False
  {-# INLINE checkEmpty #-}

instance DiffMinus Bool where
  x /- y = if x == y then DBKeep else DBNot

notC :: IFqS Bool Bool
notC = fromStatelessCode (\a -> [|| not $$a ||]) id

notF :: App IFqS e => e Bool -> e Bool
notF = lift notC


type Lazy cat c a = PFun cat c () a

{-# ANN delay "hlint: ignore Eta reduce" #-}
delay :: forall cat term s a r.
         (K cat a, K cat (), AllIn s (K cat), PFunTerm cat term) =>
         term s a -> (forall c. KK cat c => term s (Lazy cat c a) -> r) -> r
delay t k = pAbsTerm (weakenTerm t :: term (() ': s) a) k

type IFCache c1 c2 a =
  'JLNonEmpty ('JLSingle (a, Either c1 c2, () -> (a, c1), () -> (a, c2)))

-- Currently, I don't know whether or not we should provide a typeclass for

ifObliviousC ::
  forall s a c1 c2.
  (DiffMinus a, DiffTypeable a, Typeable c1, Typeable c2) =>
  Env WitTypeable s -> IFqT (Bool : Lazy IFqS c1 a : Lazy IFqS c2 a : s) a
ifObliviousC tenv = IFqT (ECons WitTypeable $ ECons WitTypeable $ ECons WitTypeable tenv) sh $ do
  return (f, tr)
  where
    sh :: Conn WitTypeable (IFCache c1 c2 a)
    sh = CNE $ COne  WitTypeable

    f :: Env PackedCodeDiff (Bool : Lazy IFqS c1 a : Lazy IFqS c2 a : s)
         -> CodeC (Code a, Conn PackedCode (IFCache c1 c2 a))
    f (ECons (PackedCodeDiff b) (ECons (PackedCodeDiff pf1) (ECons (PackedCodeDiff pf2) _))) = CodeC $ \k ->
      [||
        let PFunIFqS (FunCache _ f1 _) = $$pf1
            PFunIFqS (FunCache _ f2 _) = $$pf2
            (a, c) = if $$b then
                       let (res, c0) = f1 ()
                       in (res, Left c0)
                     else
                       let (res, c0) = f2 ()
                       in (res, Right c0)
        in $$(k ([|| a ||], CNE $ COne $ PackedCode [|| (a, c, f1, f2) ||]))
       ||]

    tr :: Env PackedCodeDelta (Bool : Lazy IFqS c1 a : Lazy IFqS c2 a : s)
          -> Conn PackedCode (IFCache c1 c2 a)
          -> CodeC (Code (Delta a), Conn PackedCode (IFCache c1 c2 a))
    tr (ECons (PackedCodeDelta db) (ECons (PackedCodeDelta pdf1) (ECons (PackedCodeDelta pdf2) _)))
       (CNE (COne (PackedCode cc))) = CodeC $ \k ->
      [||
      let DeltaPFunIFqS (DeltaFunCache b1 df1) = $$pdf1
          DeltaPFunIFqS (DeltaFunCache b2 df2) = $$pdf2
          (a, c1or2, f1, f2) = $$cc
          f1' = if b1 then f1 else changeFunction f1 df1
          f2' = if b2 then f2 else changeFunction f2 df2
          (a', da, c1or2') = case (c1or2, $$db) of
            (Left c1, DBKeep) ->
              let (da0, c1') = df1 c1
              in (a /+ da0, da0,      Left c1')
            (Left _, DBNot) ->
              let (a'0, c2) = f2' ()
              in (a'0,      a'0 /- a, Right c2)
            (Right c2, DBKeep) ->
              let (da0, c2') = df2 c2
              in (a /+ da0, da0,      Right c2')
            (Right _,  DBKeep) ->
              let (a'0, c1) = f1' ()
              in (a'0,       a'0 /- a, Left c1)
      in $$(k ([|| da ||], CNE $ COne $ PackedCode [|| (a', c1or2', f1', f2')  ||]))
      ||]

ifObliviousCU ::
  forall s a c1 c2.
  (DiffMinus a, DiffTypeable a, Typeable c1, Typeable c2) =>
  Env WitTypeable s -> IFqTU (Bool : Lazy IFqS c1 a : Lazy IFqS c2 a : s) a
ifObliviousCU tenv = IFqTU (ECons WitTypeable $ ECons WitTypeable $ ECons WitTypeable tenv) sh (ECons STrue $ ECons STrue $ ECons STrue ENil) $ do
  return (f, tr)
  where
    sh :: Conn WitTypeable (IFCache c1 c2 a)
    sh = CNE $ COne  WitTypeable

    f :: Env PackedCodeDiff (Bool ': Lazy IFqS c1 a ': Lazy IFqS c2 a : '[])
         -> CodeC (Code a, Conn PackedCode (IFCache c1 c2 a))
    f (ECons (PackedCodeDiff b) (ECons (PackedCodeDiff pf1) (ECons (PackedCodeDiff pf2) ENil))) = CodeC $ \k ->
      [||
        let PFunIFqS (FunCache _ f1 _) = $$pf1
            PFunIFqS (FunCache _ f2 _) = $$pf2
            (a, c) = if $$b then
                       let (res, c0) = f1 ()
                       in (res, Left c0)
                     else
                       let (res, c0) = f2 ()
                       in (res, Right c0)
        in $$(k ([|| a ||], CNE $ COne $ PackedCode [|| (a, c, f1, f2) ||]))
       ||]

    tr :: Env PackedCodeDelta (Bool ': Lazy IFqS c1 a ': Lazy IFqS c2 a ': '[])
          -> Conn PackedCode (IFCache c1 c2 a)
          -> CodeC (Code (Delta a), Conn PackedCode (IFCache c1 c2 a))
    tr (ECons (PackedCodeDelta db) (ECons (PackedCodeDelta pdf1) (ECons (PackedCodeDelta pdf2) ENil)))
       (CNE (COne (PackedCode cc))) = CodeC $ \k ->
      [||
      let DeltaPFunIFqS (DeltaFunCache b1 df1) = $$pdf1
          DeltaPFunIFqS (DeltaFunCache b2 df2) = $$pdf2
          (a, c1or2, f1, f2) = $$cc
          f1' = if b1 then f1 else changeFunction f1 df1
          f2' = if b2 then f2 else changeFunction f2 df2
          (a', da, c1or2') = case (c1or2, $$db) of
            (Left c1, DBKeep) ->
              let (da0, c1') = df1 c1
              in (a /+ da0, da0,      Left c1')
            (Left _, DBNot) ->
              let (a'0, c2) = f2' ()
              in (a'0,      a'0 /- a, Right c2)
            (Right c2, DBKeep) ->
              let (da0, c2') = df2 c2
              in (a /+ da0, da0,      Right c2')
            (Right _,  DBNot) ->
              let (a'0, c1) = f1' ()
              in (a'0,       a'0 /- a, Left c1)
      in $$(k ([|| da ||], CNE $ COne $ PackedCode [|| (a', c1or2', f1', f2')  ||]))
      ||]


ifTermOT ::
  (AllIn s DiffTypeable, Typeable a, DiffMinus a)
  => IFqT s Bool -> IFqT s a -> IFqT s a -> IFqT s a
ifTermOT e0@(IFqT tenv _ _) e1 e2 =
  delay e2 $ \e2' ->
  delay e1 $ \e1' ->
  letTerm e2' $
  letTerm (weakenTerm e1') $
  letTerm (weakenTerm $ weakenTerm e0) $ ifObliviousC tenv

ifTermOTU ::
  (AllIn s DiffTypeable, Typeable a, DiffMinus a)
  => IFqTU s Bool -> IFqTU s a -> IFqTU s a -> IFqTU s a
ifTermOTU e0@(IFqTU tenv _ _ _) e1 e2 =
  delay e2 $ \e2' ->
  delay e1 $ \e1' ->
  letTerm e2' $
  letTerm (weakenTerm e1') $
  letTerm (weakenTerm $ weakenTerm e0) $ ifObliviousCU tenv

class (IncrementalizedQ cat, Term cat term) => IfTerm cat term k | term -> k, term -> cat where
  ifTerm :: (AllIn s (K cat), K cat a, k a) => term s Bool -> term s a -> term s a -> term s a

instance IfTerm IFqS IFqT DiffMinus where
  ifTerm = ifTermOT

instance IfTerm IFqS IFqTU DiffMinus where
  ifTerm = ifTermOTU

if_ ::
  (IfTerm cat term k, App2 cat term e, K cat a, k a)
  => e Bool -> e a -> e a -> e a
if_ = liftSO3 (Proxy @'[ '[], '[], '[] ]) ifTerm


{- $

>>> let (res, i) = func (True, 1)
>>> res
1
>>> let ds = [ pairDelta mempty (1 :: Delta Int), pairDelta DBNot mempty, pairDelta mempty 2 ]
>>> let dress = iterations i ds
>>> dress
[DInt 1,DInt 2,DInt 4]
>>> foldl (/+) (True, 1) ds
(False,4)
>>> foldl (/+) res dress
8
>>> fst $ func $ foldl (/+) (True, 1) ds
8

prop> let ds = [ pairDelta (if b then DBKeep else DBNot) (fromIntegral d :: Delta Int) | (b, d) <- xs ] in let (res, i) = func x0 in fst (func $ foldl (/+) x0 ds) == foldl (/+) res (iterations i ds)

-}


{-

[Note] Can we construct a retentive variant of the if expression?


-}


-- -- Invariant:
-- --   If the third component is True,  the fourth component is Right.
-- --   If the third component is False, the fourth component is Right.
-- type IFCacheR c1 c2 a =
--   'JLNonEmpty ('JLSingle (a, BranchCache c1 c2 a, () -> (a, c1), () -> (a, c2)))

-- data BranchCache c1 c2 a
--   = FromT c1 (Maybe c2)
--   | FromF (Maybe c1) c2



