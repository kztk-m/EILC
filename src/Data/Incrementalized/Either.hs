{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}

module Data.Incrementalized.Either (
    Delta(..), leftF, rightF, eitherF,

    SumTerm(..),
  ) where

import           Data.Delta
import           Prelude                             hiding (id, (.))


import           Data.Code
import           Data.Code.Lifting                   (WitTypeable (WitTypeable))
import           Data.Conn
import           Data.Env
import           Data.IFq
import           Data.IFqTU
import           Data.Incrementalized                (IncrementalizedQ,
                                                      fromStatelessCode)
import           Data.Incrementalized.Function
import           Data.JoinList
import           Data.Typeable                       (Proxy (Proxy), Typeable)
import           Language.Unembedding
import           Language.Unembedding.PseudoFunction

{- |
One may think we should prepare InLeft da and InRight db, but it is unclear how
they behave when applied to inappropriate form (e.g., Right b /+ InLeft da). One
idea is they should leave the original value (e.g., Right b /+ InLeft da = Right
b), but then, we are not able to define InLeft da <> InRight db to satisfy (x /+
(InLeft da <> InRight db) = x /+ InLeft da /+ InRight db). Another approach is
to make Right b /+ InLeft da undefined, but in many reasons, we do not want to
make (/+) partial. So, we instead prepare DEitherInPlace da db, which use da
if the original value has the form of Left a, and db for Right b.

Similarly, one may think we should prepare LeftToRight b and RightToLeft a, but
it is unclear how LeftToRight b/RightToLeft a behaves for Right a'/Left b'.
Following the similar discussions above, we repare `DEitherReplace ab` that
replaces original one with `ab` unconditionally.
-}
data instance Delta (Either a b) = DEitherInPlace (Delta a) (Delta b) | DEitherReplace (Either a b)

applyDeltaEither :: (Diff a, Diff b) => Either a b -> Delta (Either a b) -> Either a b
applyDeltaEither (Left a)  (DEitherInPlace da _) = Left (a /+ da)
applyDeltaEither (Right b) (DEitherInPlace _ db) = Right (b /+ db)
applyDeltaEither _         (DEitherReplace x)    = x

instance (Diff a, Diff b) => Semigroup (Delta (Either a b)) where
  DEitherInPlace da1 db1 <> DEitherInPlace da2 db2 = DEitherInPlace (da1 <> da2) (db1 <> db2)
  _ <> DEitherReplace x = DEitherReplace x
  DEitherReplace x <> DEitherInPlace da db = DEitherReplace (applyDeltaEither x (DEitherInPlace da db))

instance (Diff a, Diff b) => Monoid (Delta (Either a b)) where
  mempty = DEitherInPlace mempty mempty

instance (Diff a, Diff b) => Diff (Either a b) where
  a /+ da = applyDeltaEither a da

  checkEmpty (DEitherReplace _)     = False
  checkEmpty (DEitherInPlace da db) = checkEmpty da && checkEmpty db

instance (Diff a, Diff b) => DiffReplace (Either a b) where
  replaceTo = DEitherReplace

instance (DiffMinus a, DiffMinus b) => DiffMinus (Either a b) where
  Left a' /- Left a   = DEitherInPlace (a' /- a) mempty
  Right b' /- Right b = DEitherInPlace mempty (b' /- b)
  x /- _              = DEitherReplace x

leftC :: Monoid (Delta b) => IFqS a (Either a b)
leftC = fromStatelessCode (\a -> [|| Left $$a ||]) (\da -> [|| DEitherInPlace $$da mempty ||])

rightC :: Monoid (Delta a) => IFqS b (Either a b)
rightC = fromStatelessCode (\a -> [|| Right $$a ||]) (\db -> [|| DEitherInPlace mempty $$db ||])

leftF :: (App IFqS e, Diff a, Typeable a, Diff b, Typeable b) => e a -> e (Either a b)
leftF = lift leftC

rightF :: (App IFqS e, Diff a, Typeable a, Diff b, Typeable b) => e b -> e (Either a b)
rightF = lift rightC

type EitherCache c1 c2 a b r =
  'JLNonEmpty ('JLSingle (r, Either c1 c2, FunCache c1 a r, FunCache c2 b r))

eitherTermCU ::
  forall s a b r ca cb.
  (DiffMinus r, DiffTypeable r, DiffTypeable a, DiffTypeable b, Typeable ca, Typeable cb) =>
  Env WitTypeable s
   -> IFqTU (Either a b ': PFun IFqS ca a r ': PFun IFqS cb b r ': s) r
eitherTermCU tenv = IFqTU (ECons WitTypeable $ ECons WitTypeable $ ECons WitTypeable tenv) sh (ECons STrue $ ECons STrue $ ECons STrue ENil) $ do
  return (h, hTr)
  where
    sh :: Conn WitTypeable (EitherCache ca cb a b r)
    sh = CNE $ COne WitTypeable

    h :: Env PackedCodeDiff (Either a b ': PFun IFqS ca a r ': PFun IFqS cb b r : '[])
         -> CodeC (Code r, Conn PackedCode (EitherCache ca cb a b r))
    h (ECons (PackedCodeDiff x) (ECons (PackedCodeDiff pf) (ECons (PackedCodeDiff pg) _))) = CodeC $ \k ->
      [||
          let PFunIFqS ff@(FunCache _ f _) = $$pf
              PFunIFqS gg@(FunCache _ g _) = $$pg
              (r, c) = case $$x of
                        Left  a -> let (rr, cc) = f a in (rr, Left cc)
                        Right b -> let (rr, cc) = g b in (rr, Right cc)
          in $$(k ([|| r ||],  CNE $ COne $ PackedCode [|| (r, c, ff, gg) ||]))
      ||]

    hTr ::
      Env PackedCodeDelta (Either a b ': PFun IFqS ca a r ': PFun IFqS cb b r : '[])
      -> Conn PackedCode (EitherCache ca cb a b r)
      -> CodeC (Code (Delta r), Conn PackedCode (EitherCache ca cb a b r))
    hTr (ECons (PackedCodeDelta qdx) (ECons (PackedCodeDelta qdf) (ECons (PackedCodeDelta qdg) _))) (CNE (COne (PackedCode cc))) = CodeC $ \k ->
      [||
          let (rprev, c, ff@(FunCache _ _ deriv_f), gg@(FunCache _ _ deriv_g)) = $$cc
              DeltaPFunIFqS dff = $$qdf
              DeltaPFunIFqS dgg = $$qdg
              ff'@(FunCache _ f' _) = ff /+ dff
              gg'@(FunCache _ g' _) = gg /+ dgg
              (rnew, dres, c') = case (c, $$qdx) of
                (Left ca, DEitherInPlace da _) ->
                  let (dr, ca') = deriv_f da ca in (rprev /+ dr, dr, Left ca')
                (Right cb, DEitherInPlace _ db) ->
                  let (dr, cb') = deriv_g db cb in (rprev /+ dr, dr, Right cb')
                (_, DEitherReplace (Left a)) ->
                  let (r, ca') = f' a in (r, r /- rprev, Left ca')
                (_, DEitherReplace (Right b)) ->
                  let (r, cb') = g' b in (r, r /- rprev, Right cb')
          in $$(k ([|| dres ||], CNE $ COne $ PackedCode [|| (rnew, c', ff', gg') ||]))
      ||]


class (IncrementalizedQ cat, Term cat term) => SumTerm cat term k | term -> k, term -> cat where
  eitherTerm :: (AllIn s (K cat), K cat a, K cat b, K cat r, k r) => term s (Either a b) -> term (a ': s) r -> term (b ': s) r -> term s r

instance SumTerm IFqS IFqTU DiffMinus where
  eitherTerm e0@(IFqTU tenv _ _ _) e1 e2 =
    pAbsTerm e2 $ \e2' ->
      pAbsTerm e1 $ \e1' ->
        letTerm e2' $
        letTerm (weakenTerm e1') $
        letTerm (weakenTerm $ weakenTerm e0) $
        eitherTermCU tenv

eitherF ::
  forall cat term k e a b r.
  (SumTerm cat term k, App2 cat term e, K cat a, K cat b, K cat r, k r)
  => e (Either a b) -> (e a -> e r) -> (e b -> e r) -> e r
eitherF = liftSO3 (Proxy @'[ '[], '[a], '[b] ]) eitherTerm
