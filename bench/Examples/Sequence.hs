{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}

module Examples.Sequence (
  -- S(..), type AtomicDelta(..),
  -- emptyF, singletonF, concatF, mapF,

  -- cartesian, cartesianHO, cartesianHORaw,
  -- testCode,  testCodeHO, testCodeHORaw,

  cartesian, testCode, testCodeRaw,
  ) where

import           Prelude                             hiding ((.))

import           Data.Dynamic
import           Data.Incrementalized
import qualified Data.Sequence                       as Seq
import           Data.Typeable                       (Proxy (Proxy))



import           Data.Interaction                    (Interaction (..))
import           EILC
import           Language.Unembedding
import           Language.Unembedding.PseudoFunction

import           Data.Incrementalized.Function
import           Data.Incrementalized.Numeric        ()

import           Data.IF                             (IF)

import           Data.Incrementalized.Seq            (Seq)
import qualified Data.Incrementalized.Seq            as ISeq


-- newtype S a = S { unS :: Seq.Seq a }
--   deriving newtype Show
--   deriving newtype (NFData, Functor, Applicative, Foldable, Monad)
--   -- NB: deriving of Traversable via GeneralizedNewtypeDeriving causes an error

-- newtype DList a = DList ([a] -> [a])

-- instance NFData (DList a) where
--   -- evaluating f [] is meaningless
--   rnf (DList f) = seq f ()

-- instance Semigroup (DList a) where
--   (<>)  = coerce @(([a] -> [a]) -> ([a] -> [a]) -> ([a] -> [a])) (Prelude..)
--   {-# INLINE (<>) #-}

-- instance Monoid (DList a) where
--   mempty = coerce @([a] -> [a]) Prelude.id
--   {-# INLINE mempty #-}

-- instance Show a => Show (DList a) where
--   show (DList f) = show (f [])

-- data JList a = JNil | JAppend !(JList a) !(JList a) | JSingleton !a
--   deriving stock Functor

-- instance Foldable JList where
--   foldMap f js = goNil js
--     where
--       goNil JNil            = mempty
--       goNil (JSingleton a)  = f a
--       goNil (JAppend j1 j2) = go j1 $! goNil j2

--       go JNil r             = r
--       go (JSingleton a)  !r = let !b = f a in b <> r
--       go (JAppend j1 j2) !r = go j1 $! go j2 r

-- instance Show a => Show (JList a) where
--   show js = show (Data.Foldable.toList js)

-- instance NFData a => NFData (JList a) where
--   rnf JNil           = ()
--   rnf (JAppend _ _)  = ()
--   rnf (JSingleton a) = rnf a

-- instance Semigroup (JList a) where
--   JNil <> as = as
--   as <> JNil = as
--   as <> bs   = JAppend as bs
--   {-# INLINABLE (<>) #-}

-- instance Monoid (JList a) where
--   mempty = JNil
--   {-# INLINE mempty #-}

-- newtype instance Delta (S a) = DS (JList (AtomicDelta (S a)))
--   deriving newtype (Semigroup, Monoid)

-- deriving newtype instance NFData (AtomicDelta (S a)) => NFData (Delta (S a))

-- deriving newtype instance (Show (Delta a) , Show a) => Show (Delta (S a))

-- type DeltaS a = AtomicDelta (S a)


-- instance Diff a => Diff (S a) where
--   checkEmpty (DS JNil) = True
--   checkEmpty _         = False
--   {-# INLINABLE checkEmpty #-}

-- instance Diff a => HasAtomicDelta (S a) where
--   -- Taken from https://github.com/yurug/cts
--   data AtomicDelta (S a)
--     = SIns   !Int !(S a)     -- ^ SIns i s inserts s at the ith position
--     | SDel   !Int !Int       -- ^ SDel i n deletes n elements from the ith position in a sequence
--     | SRep   !Int !(Delta a) -- ^ SRep i da applies the delta da to the ith element.
--     | SRearr !Int !Int !Int  -- ^ SRearr i n j cuts n elements from the ith position and insert the cut sequence into the jth position (after cuting).

--   applyAtomicDelta (S seq0) ds = S (ad seq0 ds)
--     where
--       ad :: Seq.Seq a -> DeltaS a -> Seq.Seq a
--       ad s0 (SIns n (S s)) = insSeq n s s0
--       ad s0 (SDel i n)     = delSeq i n s0
--       ad s0 (SRep i da)    = repSeq i da s0
--       ad s0 (SRearr i n j) = rearrSeq i n j s0

--   injDelta ad = DS $ JSingleton ad -- DS (DList (ad :))
--   monoidMap f (DS js) = foldMap f js

--   -- monoidMap f (DS (DList x)) = foldMap f (x [])

-- -- smart? constructor
-- srep :: Diff a => Int -> Delta a -> Delta (S a)
-- srep i da
--   | checkEmpty da = mempty
--   | otherwise     = injDelta $ SRep i da

-- deriving stock instance (Show (Delta a), Show a) => Show (AtomicDelta (S a))


-- insSeq :: Int -> Seq.Seq a -> Seq.Seq a -> Seq.Seq a
-- insSeq !i !s' !s0 =
--     let !(!s1, !s2) = Seq.splitAt i s0
--     in s1 Seq.>< s' Seq.>< s2
-- {-# INLINABLE insSeq #-}

-- delSeq :: Int -> Int -> Seq.Seq a -> Seq.Seq a
-- delSeq !i !n !s0 =
--     let !(!s1, stemp) = Seq.splitAt i s0
--         !s2 = Seq.drop n stemp
--     in s1 Seq.>< s2
-- {-# INLINABLE delSeq #-}

-- repSeq :: Diff a => Int -> Delta a -> Seq.Seq a -> Seq.Seq a
-- repSeq !i !da = Seq.adjust' (/+ da) i
-- {-# INLINABLE repSeq #-}

-- rearrSeq :: Int -> Int -> Int -> Seq.Seq a -> Seq.Seq a
-- rearrSeq !i !n !j !s0 =
--     let !(!s1, s23) = Seq.splitAt i s0
--         !(!s2, !s3) = Seq.splitAt n s23
--     in insSeq j s2 $! (s1 Seq.>< s3)
-- {-# INLINABLE rearrSeq #-}

-- -- APIs
-- dsingleton :: Diff a => Delta a -> Delta (S a)
-- dsingleton = srep 0
-- {-# INLINABLE dsingleton #-}

-- singletonF :: (IncrementalizedQ c,
--                CodeType c ~ PackedCode,
--                K c a, K c (S a), K c ~ Diff, App2 c t e) => e a -> e (S a)
-- singletonF = lift singletonC
--   where
--     singletonC =
--       fromStatelessCode
--       (\a -> [|| S (Seq.singleton $! $$a) ||])
--       (\da -> [|| dsingleton $! $$da ||])
-- {-# INLINABLE singletonF #-}

-- dempty :: Delta (S a)
-- dempty = mempty
-- {-# INLINABLE dempty #-}

-- emptyF :: (IncrementalizedQ c,
--            CodeType c ~ PackedCode,
--            K c (Unit c), K c (S a), App2 c t e) => e (S a)
-- emptyF = lift emptyC unit
--   where
--       emptyC = fromStatelessCode (const [|| S Seq.empty ||]) (const [|| dempty ||])
-- {-# INLINABLE emptyF #-}

-- -- emptyRaw ::
-- --   (K cat (Unit cat), K cat (S a), App cat e, IncrementalizedQ cat,
-- --     CodeType cat ~ Identity) => e (S a)
-- -- emptyRaw = lift emptyC unit
-- --   where
-- --     emptyC = fromStatelessIdentity (const $ S Seq.empty) (const dempty)

-- -- lengths of inner sequences.
-- type ConcatC = Seq.Seq Int

-- s2c :: S (S a) -> ConcatC
-- s2c (S s0) = fmap (Seq.length . unS) s0

-- concatC :: S (S a) -> (S a, ConcatC)
-- concatC s0 =
--   let !res = Control.Monad.join s0
--       !c = s2c s0
--   in (res, c)

-- insAtC :: Int -> ConcatC -> ConcatC -> ConcatC
-- insAtC i is is0 =
--   Data.Foldable.foldl' (flip (Seq.insertAt i)) is0 is

-- trConcatCAtomic :: Diff a => DeltaS (S a) -> ConcatC -> (Delta (S a), ConcatC)
-- trConcatCAtomic (SIns i s') c =
--   -- in this case, a sequence s' is inserted at ith element
--   let !toI = sum (Seq.take i c)
--       !c'  = insAtC i (s2c s') c
--   in (injDelta $! SIns toI (Control.Monad.join s'), c')
-- trConcatCAtomic (SDel i n) c =
--   let (!c1, !c23) = Seq.splitAt i c
--       (!c2, !c3)  = Seq.splitAt n c23
--       !toI        = sum c1
--       !toN        = sum c2
--       !c'         = c1 Seq.>< c3
--   in (injDelta $! SDel toI toN, c')
-- trConcatCAtomic (SRearr i n j) c =
--   let (!c1, !c23) = Seq.splitAt i c
--       (!c2, !c3)  = Seq.splitAt n c23
--       !toI        = sum c1
--       !toN        = sum c2
--       !c13        = c1 Seq.>< c3
--       !toJ        = sum $ Seq.take j c13
--       !c'         = insAtC j c2 c13
--   in (injDelta $! SRearr toI toN toJ, c' )
-- trConcatCAtomic (SRep i ds) c =
--   let !ci = fromJust $ Seq.lookup i c
--       !offset = sum $ Seq.take i c
--       !(!ds', !ci') = iterTr (goAtomic offset) ds ci
--       !c' = Seq.update i ci' c
--   in (ds', c')
--   where
--     goAtomic :: Diff a => Int -> DeltaS a -> Int -> (Delta (S a), Int)
--     goAtomic !offset (SIns j as) ci =
--       let !ci' = ci + Seq.length (unS as)
--       in (injDelta $! SIns (offset + j) as, ci')
--     goAtomic !offset (SDel j n) ci =
--       let -- adjust n to satisfy the invaliant n + j <= ci
--           !n'  = n + (if j + n > ci then ci - (j + n) else 0)
--           !ci' = ci - n'
--       in (injDelta $! SDel (offset + j) n', ci')
--     goAtomic !offset (SRep j da) ci =
--       (srep (offset + j) da, ci)
--     goAtomic !offset (SRearr j n k) ci =
--       (injDelta $! SRearr (offset + j) n (offset + k), ci)

-- concatF :: (IncrementalizedQ c, App2 c t e, K c ~ DiffTypeable,
--             CodeType c ~ PackedCode,
--             K c a, K c (S (S a)), K c (S a))
--            => e (S (S a)) -> e (S a)
-- concatF = lift (fromFunctionsCode [|| concatC ||] [|| iterTr trConcatCAtomic ||])
-- {-# INLINABLE concatF #-}

-- concatRaw ::
--   (K cat (S (S a)), K cat (S a), App cat e, IncrementalizedQ cat,
--    Diff a, CodeType cat ~ Identity) =>
--   e (S (S a)) -> e (S a)
-- concatRaw = lift (fromFunctionsIdentity concatC (iterTr trConcatCAtomic))

-- type a @+ b = Join a b
-- infixr 5 @+


-- class MapAPI cat term | term -> cat where
--   mapAPI :: (K cat ~ DiffTypeable, DiffTypeable a, DiffTypeable b, AllIn s DiffTypeable) => term (a ': s) b -> term (S a ': s) (S b)


-- fromPF ::
--   forall cat term s (a :: Type) (b :: Type) f .
--   (LetTerm cat term, PFunTerm cat term, K cat ~ DiffTypeable, KK cat ~ Typeable,
--    forall (c :: Type). Diff (PFun cat (f c) (S a) (S b)),
--    Typeable cat, Typeable f, AllIn s DiffTypeable, DiffTypeable a, DiffTypeable b
--   ) =>
--   -- Skolem function f is used to represent existential quantification in this scope.
--   (forall (c :: Type). Typeable c => cat (PFun cat c a b) (PFun cat (f c) (S a) (S b)))
--   -> term (a ': s) b
--   -> term s (S a)
--   -> term s (S b)
-- fromPF h e1 e2 =
--   pAbsTerm e1 $ \e1' ->
--   pAppTerm (mapTerm h e1') e2


-- mapTr ::
--   (Diff a, Diff b)
--   => (a -> (b, c)) -> (Bool -> Delta a -> c -> (Delta b, c))
--   -> Seq c -> Delta (S a) -> (Delta (S b), Seq c )
-- mapTr f dfb !cs ds =
--   let !(!dbs1, !cs')  = mapTrUnchanged (dfb True mempty) cs
--       !(!dbs2, !cs'') = iterTr (mapTrChanged f (dfb False)) ds cs'
--       !dbs' = dbs1 <> dbs2
--   in (dbs', cs'')

-- sequenceDelta :: Diff a => Seq (Delta a) -> Delta (S a)
-- sequenceDelta s =
--   mconcat $ zipWith srep [0..] (Data.Foldable.toList s)

-- -- Hanldes changes to environments.
-- mapTrUnchanged ::
--   Diff b
--   => (c -> (Delta b, c))
--   -> Seq.Seq c -> (Delta (S b), Seq.Seq c)
-- mapTrUnchanged unchanged cs =
--   let !(!dbs, !cs') = Seq.unzip $ fmap unchanged cs
--   in (sequenceDelta dbs, cs')

-- mapTrChanged ::
--   Diff b
--   => (a -> (b, c))
--   -> (Delta a -> c -> (Delta b, c))
--   -> AtomicDelta (S a) -> Seq c -> (Delta (S b), Seq c)
-- mapTrChanged f _df (SIns i (S as)) cs     =
--   let !(!bs, !cs') = Seq.unzip $ fmap f as
--   in (injDelta $! SIns i (S bs), insSeq i cs' cs)
-- mapTrChanged _ _df (SDel i n) cs     =
--   let !cs' = delSeq i n cs
--   in (injDelta $! SDel i n, cs')
-- mapTrChanged _ df (SRep i da) cs    =
--   let !ci = Seq.index cs i
--       !(!db, !ci') = df da ci
--   in (srep i db, Seq.update i ci' cs)
-- mapTrChanged _ _df (SRearr i n j) cs =
--   let !cs' = rearrSeq i n j cs
--   in (injDelta $! SRearr i n j, cs')


-- type EncCS cs2 = Env Identity (Flatten cs2)

-- type MapC s cs =
--    'JLNonEmpty ('JLSingle (Seq (EncCS cs)))
--     @+ UnFlatten s

-- instance MapAPI IFqS IFqT where
--   mapAPI = cMapT

-- cMapT :: forall s a b. (Diff a, Typeable a, Diff b, AllIn s DiffTypeable) => IFqT (a ': s) b -> IFqT (S a ': s) (S b)
-- cMapT (IFqT (ECons _ tenv) (sh :: Conn WitTypeable cs) m) = IFqT (ECons WitTypeable tenv) sh' $ do
--   (f, tr) <- m
--   let
--     h :: Env PackedCodeDiff s -> Code (a -> (b, EncCS cs))
--     h env = [||
--         \a -> $$( runCodeC (f (ECons (PackedCodeDiff [|| a ||]) env)) $ \(b, c') -> [|| ($$b, $$(conn2cenv c')) ||])
--       ||]
--   func :: Code (EFunc s (a -> (b, EncCS cs))) <-
--     mkLet (mkAbsED_ tenv $ \env -> h env)
--   let
--     f' ::
--       Env PackedCodeDiff (S a ': s)
--       -> CodeC (Code (S b), Conn PackedCode (MapC s cs))
--     f' (ECons (PackedCodeDiff as) env) = do
--       (bs, cs) <- CodeC $ \k -> [||
--             let (bs, cs) = Seq.unzip $ fmap $$(mkAppED @s @(a -> (b, EncCS cs)) func env)  (unS $$as)
--             in $$(k ([|| S bs ||], CNE $ COne $ PackedCode [|| cs ||]))
--         ||]
--       return (bs, joinConn cs $ convertEnv $ mapEnv (\(PackedCodeDiff a) -> PackedCode a) env)


--     trh :: Env PackedCodeDelta s -> Conn WitTypeable cs -> Code (Bool -> Delta a -> EncCS cs -> (Delta b, EncCS cs))
--     trh env pcs = [|| \b da c ->
--       $$(cenv2conn pcs [|| c ||] $ \cs -> toCode $ do
--           env' <- mkLetEnvD $ mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) env
--           (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) env') cs
--           return [|| ($$db, $$(conn2cenv cs') ) ||])
--       ||]

--     tr' ::
--       Env PackedCodeDelta (S a ': s) -> Conn PackedCode (MapC s cs)
--       -> CodeC (Code (Delta (S b)), Conn PackedCode (MapC s cs))
--     tr' (ECons (PackedCodeDelta das) denv) conn | (CNE (COne (PackedCode cs)), cenv) <- decompConn (isNone shA) (isNone $ convertEnv tenv) conn = do
--       let env = unconvertEnv tenv cenv
--       --  Potential source of slow down => We should use function changes instead.
--       env' <- mkLetEnv $ zipWithEnv (\(PackedCode a) (PackedCodeDelta da) -> PackedCode [|| $$a /+ $$da ||]) env denv
--       (dbs, cs') <- CodeC $ \k -> [||
--           let fElem  = $$(mkAppE func env')
--               trElem = $$(trh denv sh)
--               (dbs, cs2') = -- mapTr fElem trElem $$cs $$das
--                 if $$(allEmptyDelta denv) then iterTr (mapTrChanged fElem (trElem False)) $$das $$cs else mapTr fElem trElem $$cs $$das
--           in $$(k ([|| dbs ||], [|| cs2' ||]))
--         ||]
--       return ([|| $$dbs ||], joinConn (CNE $ COne $ PackedCode cs') (convertEnv env'))
--   return (f' , tr')
--   where
--     sh' :: Conn WitTypeable (MapC s cs)
--     sh' = joinConn shA (convertEnv tenv)

--     shA :: Conn WitTypeable ('JLNonEmpty ('JLSingle (Seq (EncCS cs))))
--     shA = case witTypeableFlatten sh of { Wit -> CNE (COne WitTypeable) }

-- mapF :: forall cat term e a b.
--         (MapAPI cat term, LetTerm cat term, App2 cat term e, K cat ~ DiffTypeable, Diff a, Typeable a, Diff b, Typeable b) => (e a -> e b) -> e (S a) -> e (S b)
-- mapF = flip (liftSO2 (Proxy @'[ '[], '[a] ]) $ \e1 e2 -> letTerm e1 (mapAPI e2))


-- fstF ::
--   forall cat e a b.
--   (Cartesian cat, Prod cat a b ~ (a, b), App cat e, K cat a, K cat b, K cat (a, b))
--   => e (a, b) -> e a
-- fstF = lift (fstS (Proxy @a) (Proxy @b))

-- sndF ::
--   forall cat e a b.
--   (Cartesian cat, Prod cat a b ~ (a, b), App cat e, K cat a, K cat b, K cat (a, b))
--   => e (a, b) -> e b
-- sndF = lift (sndS (Proxy @a) (Proxy @b))

-- cartesian ::
--   (IncrementalizedQ cat, MapAPI cat term, LetTerm cat term,
--    CodeType cat ~ PackedCode,
--    K cat ~ DiffTypeable, Prod cat a b ~ (a, b), App2 cat term e, Diff a, Typeable a, Diff b, Typeable b)
--   => e (S a) -> e (S b) -> e (S (a, b))
-- cartesian as bs =
--   concatMapF (\a -> mapF (pair a) bs) as
--   where
--     concatMapF f x = concatF (mapF f x)

-- Fmaphobase ::
--   (Diff a, Diff b) =>
--   FunCache c a b -> (FunCache (Seq c) (S a) (S b), FunCache c a b)
-- fMapHOBase (FunCache ws f df) = (FunCache ws h dh, FunCache ws f df)
--   where
--     h (S as) =
--       let (bs, cs) = Seq.unzip $ fmap f as
--       in (S bs, cs)
--     dh das cs =
--       let (db, cs') = iterTr (mapTrChanged f df) das cs
--       in (db, cs')

-- fMapHO :: (Diff a, Diff b) =>
--            PFun IFqS c a b -> (PFun IFqS (Seq c) (S a) (S b), PFun IFqS c a b)
-- fMapHO (PFunIFqS h) = PFunIFqS *** PFunIFqS $ fMapHOBase h

-- fMapHORaw :: (Diff a, Diff b) =>
--            PFun IF c a b -> (PFun IF (Seq c) (S a) (S b), PFun IF c a b)
-- fMapHORaw (PFunIF h) = PFunIF *** PFunIF $ fMapHOBase h

-- trMapHOBase ::
--   (Diff b) =>
--   Delta (FunCache c a b) -> FunCache c a b -> (Delta (FunCache (Seq c) (S a) (S b)), FunCache c a b)
-- trMapHOBase dft ft | checkEmpty dft = (DeltaFunCache True (\d -> (mempty , d)), ft)
-- trMapHOBase dft@(DeltaFunCache _ dfNN) ft = (DeltaFunCache False dfNNMap, ft /+ dft)
--   where
--     dfNNMap cs =
--       let (db, cs') = mapTrUnchanged dfNN cs
--       in (db, cs')


-- trMapHO :: (Diff b) => Delta (PFun IFqS c a b) -> PFun IFqS c a b -> (Delta (PFun IFqS (Seq c) (S a) (S b)), PFun IFqS c a b)
-- trMapHO (DeltaPFunIFqS dft) (PFunIFqS ft) = DeltaPFunIFqS *** PFunIFqS  $ trMapHOBase dft ft

-- trMapHORaw :: (Diff b) => Delta (PFun IF c a b) -> PFun IF c a b -> (Delta (PFun IF (Seq c) (S a) (S b)), PFun IF c a b)
-- trMapHORaw (DeltaPFunIF dft) (PFunIF ft) = DeltaPFunIF *** PFunIF  $ trMapHOBase dft ft


-- mapHOC :: (IncrementalizedQ IFqS, Typeable a, Typeable b, Diff a, Diff b, Typeable c)
--          => IFqS (PFun IFqS c a b) (PFun IFqS (Seq c) (S a) (S b))
-- mapHOC = fromFunctionsCode [|| fMapHO ||] [|| trMapHO ||]

-- mapHOCRaw :: (IncrementalizedQ cat, Typeable c, Typeable a, Typeable b, Diff a,
--               Diff b, CodeType cat ~ Identity) =>
--              cat (PFun IF c a b) (PFun IF (Seq c) (S a) (S b))
-- mapHOCRaw = fromFunctionsIdentity fMapHORaw trMapHORaw

-- mapHOAPI ::
--   (IncrementalizedQ IFqS, PFunTerm IFqS term,
--    AllIn s DiffTypeable, DiffTypeable a, DiffTypeable b)
--   => term (a ': s) b -> term s (S a) -> term s (S b)
-- mapHOAPI = fromPF mapHOC

-- mapHOAPIRaw ::
--   (AllIn s DiffTypeable, PFunTerm IF term, Typeable a, Typeable b,
--    Diff a, Diff b) =>
--   term (a : s) b -> term s (S a) -> term s (S b)
-- mapHOAPIRaw = fromPF mapHOCRaw


-- mapHO ::
--   forall term e a b.
--   (App2 IFqS term e, PFunTerm IFqS term, Diff a, Diff b, Typeable a, Typeable b) =>
--   (e a -> e b) -> e (S a) -> e (S b)
-- mapHO = liftSO2 (Proxy @'[ '[a], '[] ]) mapHOAPI

-- mapHORaw ::
--   forall term e a b.
--   (App2 IF term e, PFunTerm IF term, Diff a, Diff b, Typeable a, Typeable b) =>
--   (e a -> e b) -> e (S a) -> e (S b)
-- mapHORaw = liftSO2 (Proxy @'[ '[a], '[] ]) mapHOAPIRaw

-- -- mapHOF :: (Diff a, Diff b, Typeable a) => FunD a b -> (FunD (S a) (S b), FunD a b)
-- -- mapHOF (FunD f df) = (FunD h dh, FunD f df)
-- --   where
-- --     h (S as) =
-- --         let (bs, cs) = Seq.unzip $ fmap f as
-- --         in (S bs, (toDyn cs, S as))

-- --     dh das (d, orig) =
-- --         let Just cs = fromDynamic d
-- --             (db, cs') = iterTr (mapTrChanged f df) das cs
-- --         in (db, (toDyn cs', orig))

-- -- mapHOTR :: (Diff a, Diff b, Typeable a) => Delta (FunD a b) -> FunD a b -> (Delta (FunD (S a) (S b)), FunD a b)
-- -- mapHOTR (DFunD True _dfNN) ft@(FunD f df) =
-- --   (DFunD True (\d -> (mempty, d)), ft)
-- --   -- where
-- --   --   dfMap das d =
-- --   --     let Just cs = fromDynamic d
-- --   --         (db, cs') = iterTr (mapTrChanged f df) das cs
-- --   --     in (db, toDyn cs')
-- -- mapHOTR dft@(DFunD _ dfNN) ft@(FunD f df) =
-- --   (DFunD False dfNNMap, ft /+ dft)
-- --   where
-- --     dfNNMap (d, orig) =
-- --       let Just cs = fromDynamic d
-- --           (db, cs') = mapTrUnchanged dfNN cs
-- --       in (db, (toDyn cs', orig))


-- -- mapHOC :: (IncrementalizedQ cat, Typeable a, Typeable b, Diff a, Diff b)
-- --          => cat (FunD a b) (FunD (S a) (S b))
-- -- mapHOC = fromFunctions [|| mapHOF ||] [|| mapHOTR ||]

-- -- mapHO :: (K cat (FunD a b), K cat (FunD (S a) (S b)), App2 cat term e, FunTerm cat term, IHom cat ~ FunD, K cat ~ DiffTypeable,
-- --           IncrementalizedQ cat, Typeable a, Typeable b, Diff a, Diff b) =>
-- --           (e a -> e b) -> e (S a) -> e (S b)
-- -- mapHO f x = lift mapHOC (lam f) `app` x

-- cartesianHO ::
--   forall term e a b.
--   (PFunTerm IFqS term,
--    App2 IFqS term e, Diff a, Typeable a, Diff b, Typeable b)
--    => e (S a) -> e (S b) -> e (S (a, b))
-- cartesianHO as bs = concatMapHO (\a -> mapHO (pair a) bs) as
--   where
--     concatMapHO f x = concatF (mapHO f x)

-- cartesianHORaw ::
--   (Typeable b, Typeable a, Diff b, Diff a, PFunTerm IF term,
--    App2 IF term e) =>
--   e (S a) -> e (S b) -> e (S (a, b))
-- cartesianHORaw as bs = concatMapHORaw (\a -> mapHORaw (pair a) bs) as
--   where
--     concatMapHORaw f x = concatRaw (mapHORaw f x)


-- -- type family PairIfUsed a us cs where
-- --   PairIfUsed a '[] cs = EncCS cs
-- --   PairIfUsed a ('False ': _) cs = EncCS cs
-- --   PairIfUsed a ('True  ': _) cs = (a, EncCS cs)

-- allEmptyDelta :: forall xs. Env PackedCodeDelta xs -> Code Bool
-- allEmptyDelta ENil = [|| True ||]
-- allEmptyDelta (ECons (PackedCodeDelta da) ENil) = [|| checkEmpty $$da ||]
-- allEmptyDelta (ECons (PackedCodeDelta da) das)  = [|| checkEmpty $$da && $$(allEmptyDelta das) ||]

mapInitRaw ::
  (Diff a, Diff b) =>
  PFun IF c a b -> PFun IF (ISeq.MapCache a b c) (Seq a) (Seq b)
mapInitRaw (PFunIF (FunCache isClosed f deriv_f)) =
  PFunIF (FunCache isClosed h deriv_h)
  where
    h (ISeq.Seq as) =
      let (!bs, !cs) = Seq.unzip $ fmap f as
      in (ISeq.Seq bs,
           case isClosed of { Closed -> ISeq.MapCacheClosed cs; Open ->  ISeq.MapCacheOpen f cs})
    deriv_h das (ISeq.MapCacheClosed cs) =
      let (!db, !cs') = iterTr (ISeq.mapTrUnchangedAtomic f deriv_f) das cs
      in (db, ISeq.MapCacheClosed cs')
    deriv_h das (ISeq.MapCacheOpen ff cs) =
      let (!db, !cs') = iterTr (ISeq.mapTrUnchangedAtomic ff deriv_f) das cs
      in (db, ISeq.MapCacheOpen ff cs')

mapTrRaw ::
  (Diff b)
  => Delta (PFun IF c a b)
  -> Delta (PFun IF (ISeq.MapCache a b c) (Seq a) (Seq b))
mapTrRaw (DeltaPFunIF (DeltaFunCache True _)) = mempty
mapTrRaw (DeltaPFunIF (DeltaFunCache _ df)) = DeltaPFunIF (DeltaFunCache False dh)
  where
    dh (ISeq.MapCacheClosed cs) = (mempty, ISeq.MapCacheClosed cs)
    dh (ISeq.MapCacheOpen f cs) =
      let (!db, !cs') = ISeq.mapTrChanged df cs
      in (db, ISeq.MapCacheOpen (changeFunction f df) cs')

mapCRaw ::
  (Diff a, Diff b)
  => IF (PFun IF c a b) (PFun IF (ISeq.MapCache a b c) (Seq a) (Seq b))
mapCRaw = fromStatelessIdentity mapInitRaw mapTrRaw


mapRaw ::
  forall term e a b.
  (Diff a, Typeable a, Diff b, Typeable b, PFunTerm IF term, App2 IF term e)
  => (e a -> e b) -> e (Seq a) -> e (Seq b)
mapRaw =
 liftSO2 (Proxy @'[ '[a], '[] ]) $ \e1 e2 ->
  pAbsTerm e1 $ \e1' ->
  pAppTerm (mapTerm mapCRaw e1') e2


cartesian ::
  (PFunTerm IFqS term, App2 IFqS term e, Diff a, Typeable a, Diff b, Typeable b)
  => e (Seq a) -> e (Seq b) -> e (Seq (a, b))
cartesian as bs =
  concatMapF (\a -> ISeq.mapF (pair a) bs) as
  where
    concatMapF f x = ISeq.concatF (ISeq.mapF f x)

concatRaw ::
  (Diff a, Typeable a, App IF e) =>e (Seq (Seq a)) -> e (Seq a)
concatRaw = lift (fromFunctionsIdentity ISeq.concatInit (iterTr ISeq.concatTrAtomic))


cartesianRaw ::
  (PFunTerm IF term, App2 IF term e, Diff a, Typeable a, Diff b, Typeable b)
  => e (Seq a) -> e (Seq b) -> e (Seq (a, b))
cartesianRaw as bs =
  concatMapRaw (\a -> mapRaw (pair a) bs) as
  where
    concatMapRaw f x = concatRaw (mapRaw f x)


type TestType =
    ((Seq Int, Seq Int)
    -> (Seq (Int, Int),
        Interaction (Delta (Seq Int, Seq Int)) (Delta (Seq (Int, Int)))))

type TestCodeType = Code TestType


-- testCode :: (cat ~ IFqS, MapAPI cat term, LetTerm cat term, IncrementalizedQ cat) => Proxy term -> TestCodeType
-- testCode proxy = compileCode $ runMonoWith proxy $ \xs -> cartesian (fstF xs) (sndF xs)

-- testCodeHO ::
--   (PFunTerm IFqS t) => Proxy t -> TestCodeType
-- testCodeHO proxy = compileCode $ runMonoWith proxy $ \xs -> cartesianHO (fstF xs) (sndF xs)



testCode :: (PFunTerm IFqS t) => Proxy t -> TestCodeType
testCode proxy = compileCode $ runMonoWith proxy $ \z ->
  share (fstF z) $ \xs ->
  share (sndF z) $ \ys ->
  cartesian xs ys
-- testCodeHO proxy = compileCode $ runMonoWith proxy $ \xs -> cartesian (fstF xs) (sndF xs)

testCodeRaw :: (PFunTerm IF t) => Proxy t -> TestType
testCodeRaw proxy = compileIdentity $ runMonoWith proxy $ \z ->
  share (fstRaw z) $ \xs ->
  share (sndRaw z) $ \ys ->
  cartesianRaw xs ys

-- fstF ::
--   forall cat e a b.
--   (Cartesian cat, Prod cat a b ~ (a, b), App cat e, K cat a, K cat b, K cat (a, b))
--   => e (a, b) -> e a
fstRaw :: forall e a b. (App IF e, K IF a, K IF b, K IF (a, b)) => e (a, b) -> e a
fstRaw = lift (fstS (Proxy @a) (Proxy @b))

sndRaw :: forall e a b. (App IF e, K IF a, K IF b, K IF (a, b)) => e (a, b) -> e b
sndRaw = lift (sndS (Proxy @a) (Proxy @b))

-- sndF ::
--   forall cat e a b.
--   (Cartesian cat, Prod cat a b ~ (a, b), App cat e, K cat a, K cat b, K cat (a, b))
--   => e (a, b) -> e b
-- sndF = lift (sndS (Proxy @a) (Proxy @b))



-- >>> let f = $$( testCode $ Proxy @IFqT )
-- >>> let (res, tr) = f (S $ Seq.fromList [1,2,3], S $ Seq.fromList [10, 20, 30])
-- >>> res
-- >>> let (dr1, tr1) = runInteraction tr $ mconcat $ map injDelta [ADFst $ SIns 3 (S $ Seq.fromList [4])]
-- >>> dr1
-- >>> let (dr2, tr2) = runInteraction tr $ mconcat $ map injDelta  [ADFst $ SDel 0 1]
-- >>> dr2
-- >>> let (dr3, tr3) = runInteraction tr $ mconcat $ map injDelta [ADSnd $ SIns 3 (S $ Seq.fromList [40])]
-- >>> dr3
-- >>> let (dr4, tr4) = runInteraction tr $ mconcat $ map injDelta  [ADSnd $ SDel 0 1]
-- >>> dr4
-- S {unS = fromList [(1,10),(1,20),(1,30),(2,10),(2,20),(2,30),(3,10),(3,20),(3,30)]}
-- DS [SIns 9 (S {unS = fromList [(4,10),(4,20),(4,30)]})]
-- DS [SDel 0 3]
-- DS [SIns 3 (S {unS = fromList [(1,40)]}),SIns 7 (S {unS = fromList [(2,40)]}),SIns 11 (S {unS = fromList [(3,40)]})]
-- DS [SDel 0 1,SDel 2 1,SDel 4 1]

