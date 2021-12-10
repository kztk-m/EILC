{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

-- This module is prepared to avoid GHC's bug
module Data.Incrementalized.Seq.Core
   (
     Seq (..), Delta (..), AtomicDelta(..), fromList,

     singletonF, emptyF, concatF,

     -- * Component functions
     singletonTr, concatInit, concatTrAtomic, MapCache(..),
     mapC, mapInit, mapTr, mapTrChanged, mapTrUnchangedAtomic,
   ) where

import qualified Data.Foldable
import qualified Data.Sequence                 as Seq
import           Prelude                       hiding (id, (.))
import qualified Text.Show                     as TS

import qualified Control.Monad
import           Data.Delta
import           Data.IFq
import           Data.Incrementalized
import           Data.Incrementalized.Function
import           Data.JoinList                 hiding (fromList)
import           Data.Typeable                 (Typeable)
import           Language.Unembedding          as Unemb

-- import           Debug.Trace                   (trace)
-- import           Text.Printf

newtype Seq a = Seq { unSeq :: Seq.Seq a }
  deriving stock (Eq, Functor, Foldable, Traversable)
  deriving newtype (Semigroup, Monoid, Applicative, Monad)

fromList :: [a] -> Seq a
fromList = Seq . Seq.fromList

instance Show a => Show (Seq a) where
  showsPrec k xs =
    TS.showParen (k > 9) $ TS.showString "fromList" . TS.showString " " . shows (Data.Foldable.toList xs)

newtype instance Delta (Seq a)
  = DeltaSeq (JoinList (AtomicDelta (Seq a)))
    deriving newtype (Semigroup, Monoid)

deriving stock instance (Show a, Show (Delta a)) => Show (Delta (Seq a))
deriving stock instance (Eq a, Eq (Delta a)) => Eq (Delta (Seq a))

instance Diff a => Diff (Seq a) where
  (/+) = applyDeltaFromHasAtomicDelta

  checkEmpty (DeltaSeq JLNil) = True
  checkEmpty _                = False

instance Diff a => HasAtomicDelta (Seq a) where
  data AtomicDelta (Seq a)
    = SIns   !Int !(Seq a)     -- ^ SIns i s inserts s at the ith position
    | SDel   !Int !Int       -- ^ SDel i n deletes n elements from the ith position in a sequence
    | SRep   !Int !(Delta a) -- ^ SRep i da applies the delta da to the ith element.
    | SRearr !Int !Int !Int  -- ^ SRearr i n j cuts n elements from the ith position and insert the cut sequence into the jth position (after cuting).

  injDelta = DeltaSeq . Data.JoinList.singleton

  monoidMap f (DeltaSeq das) = Data.Foldable.foldMap f das

  applyAtomicDelta (Seq seq0) ds = Seq (ad seq0 ds)
    where
      ad :: Seq.Seq a -> AtomicDelta (Seq a) -> Seq.Seq a
      ad s0 (SIns n (Seq s)) = insSeq n s s0
      ad s0 (SDel i n)       = delSeq i n s0
      ad s0 (SRep i da)      = repSeq i da s0
      ad s0 (SRearr i n j)   = rearrSeq i n j s0

deriving stock instance (Show a, Show (Delta a)) => Show (AtomicDelta (Seq a))
deriving stock instance (Eq a, Eq (Delta a)) => Eq (AtomicDelta (Seq a))


-- smart? constructor
srep :: Diff a => Int -> Delta a -> Delta (Seq a)
srep i da
  | checkEmpty da = mempty
  | otherwise     = injDelta $ SRep i da

insSeq :: Int -> Seq.Seq a -> Seq.Seq a -> Seq.Seq a
insSeq !i !s' !s0 =
    let !(!s1, !s2) = Seq.splitAt i s0
    in s1 Seq.>< s' Seq.>< s2
{-# INLINABLE insSeq #-}

delSeq :: Int -> Int -> Seq.Seq a -> Seq.Seq a
delSeq !i !n !s0 =
    let !(!s1, stemp) = Seq.splitAt i s0
        !s2 = Seq.drop n stemp
    in s1 Seq.>< s2
{-# INLINABLE delSeq #-}

repSeq :: Diff a => Int -> Delta a -> Seq.Seq a -> Seq.Seq a
repSeq !i !da = Seq.adjust' (/+ da) i
{-# INLINABLE repSeq #-}

rearrSeq :: Int -> Int -> Int -> Seq.Seq a -> Seq.Seq a
rearrSeq !i !n !j !s0 =
    let !(!s1, s23) = Seq.splitAt i s0
        !(!s2, !s3) = Seq.splitAt n s23
    in insSeq j s2 $! (s1 Seq.>< s3)
{-# INLINABLE rearrSeq #-}

-- APIs

singletonTr :: Diff a => Delta a -> Delta (Seq a)
singletonTr = srep 0
{-# INLINABLE singletonTr #-}

singletonC ::
  Diff a => IFqS a (Seq a)
singletonC = fromStatelessCode
  (\a -> [|| Seq (Seq.singleton $! $$a) ||])
  (\da -> [|| singletonTr $! $$da ||])

singletonF ::
  (App IFqS e, Diff a, Typeable a) => e a -> e (Seq a)
singletonF = Unemb.lift singletonC

emptyC :: IFqS () (Seq a)
emptyC =
  fromStatelessCode (const [|| Seq Seq.empty ||]) (const [|| mempty ||])

emptyF :: (App IFqS e, Diff a, Typeable a) => e (Seq a)
emptyF = Unemb.lift emptyC Unemb.unit


type ConcatCache = Seq.Seq Int

makeConcatCache :: Seq (Seq a) -> ConcatCache
makeConcatCache (Seq s0) = fmap (Seq.length . unSeq) s0

concatInit :: Seq (Seq a) -> (Seq a, ConcatCache)
concatInit s0 =
  let !res = Control.Monad.join s0
      !c   = makeConcatCache s0
  in (res, c)

insAtC :: Int -> ConcatCache -> ConcatCache -> ConcatCache
insAtC = insSeq
  -- Data.Foldable.foldl' (flip (Seq.insertAt ii)) is0 is


concatTrAtomic ::
  Diff a =>
  AtomicDelta (Seq (Seq a)) -> ConcatCache -> (Delta (Seq a), ConcatCache)
concatTrAtomic (SIns i s') c =
  -- in this case, a sequence s' is inserted at ith element
  let !toI = sum (Seq.take i c)
      !c'  = insAtC i (makeConcatCache s') c
  in (injDelta $! SIns toI (Control.Monad.join s'), c')
concatTrAtomic (SDel i n) c =
  let (!c1, !c23) = Seq.splitAt i c
      (!c2, !c3)  = Seq.splitAt n c23
      !toI        = sum c1
      !toN        = sum c2
      !c'         = c1 Seq.>< c3
  in (injDelta $! SDel toI toN, c')
concatTrAtomic (SRearr i n j) c =
  let (!c1, !c23) = Seq.splitAt i c
      (!c2, !c3)  = Seq.splitAt n c23
      !toI        = sum c1
      !toN        = sum c2
      !c13        = c1 Seq.>< c3
      !toJ        = sum $ Seq.take j c13
      !c'         = insAtC j c2 c13
  in -- trace (printf "SRearr %d %d %d" i n j ++ " -> " ++ printf "SRearr %d %d %d" toI toN toJ ++ " when cache is: " ++ show c ++ " -> " ++ show c) $
     (injDelta $! SRearr toI toN toJ, c' )

concatTrAtomic (SRep i ds) c
  | Nothing  <- Seq.lookup i c = (mempty, c)
  | Just !ci <- Seq.lookup i c =
  let !offset = sum $ Seq.take i c
      !(!ds', !ci') = iterTr (goAtomic offset) ds ci
      !c' = Seq.update i ci' c
  in (ds', c')
  where
    goAtomic :: Diff a => Int -> AtomicDelta (Seq a) -> Int -> (Delta (Seq a), Int)
    goAtomic !offset (SIns j as) ci =
      let !j' = min j ci -- adjust j to satisfy the invariant j <= ci
          !ci' = ci + Seq.length (unSeq as)
      in -- trace (printf "SIns %d ..." j ++ " -> " ++ printf "SIns %d ..." (offset + j') ++ printf " when ci = %d, ci' = %d" ci ci' )
        (injDelta $! SIns (offset + j') as, ci')
    goAtomic !offset (SDel j n) ci =
      let -- adjust n to satisfy the invariant n + j <= ci
          !j'  = min j ci
          !n'  = n + (if j' + n > ci then ci - (j' + n) else 0)
          !ci' = ci - n'
      in (injDelta $! SDel (offset + j') n', ci')
    goAtomic !offset (SRep j da) ci =
      if j < ci then
        (srep (offset + j) da, ci)
      else -- SRep does nothing as j is out-of-index.
        (mempty, ci)
    goAtomic !offset (SRearr j n k) ci =
      let -- adjust j to satisfy the invariant j <= ci
          !j' = min j ci
          -- adjust n to satisfy the invariant n + j' <= ci
          !n' = n + (if j' + n > ci then ci - (j' + n) else 0)
          -- adjust k to satisfy the invarinat k <= ci - n'
          !k' = min k (ci - n')
      in -- trace (printf "SRearr %d %d %d" i n j ++ " -> " ++ printf "SRearr %d %d %d" (offset + j') n' (offset + k') ++ printf " when ci = %d" ci) $
         (injDelta $! SRearr (offset + j') n' (offset + k'), ci)

concatC :: Diff a => IFqS (Seq (Seq a)) (Seq a)
concatC = fromFunctionsCode [|| concatInit ||] [|| iterTr concatTrAtomic ||]

concatF :: (Diff a, Typeable a, App IFqS e) => e (Seq (Seq a)) -> e (Seq a)
concatF = Unemb.lift concatC

sequenceDelta :: (Foldable f, Diff a) => f (Delta a) -> Delta (Seq a)
sequenceDelta s =
  mconcat $ zipWith srep [0..] (Data.Foldable.toList s)

-- When a function to map is not changed.
mapTrUnchangedAtomic ::
  Diff b
  => (a -> (b, c))
  -> (Delta a -> c -> (Delta b, c))
  -> AtomicDelta (Seq a) -> Seq.Seq c -> (Delta (Seq b), Seq.Seq c)
mapTrUnchangedAtomic f deriv_f dseq cs = case dseq of
  SIns i (Seq as) ->
    let !(!bs, !cs') = Seq.unzip $ fmap f as
    in (injDelta $! SIns i (Seq bs), insSeq i cs' cs)
  SDel i n ->
    let !cs' = delSeq i n cs
    in (injDelta $! SDel i n, cs')
  SRep i da ->
    case Seq.lookup i cs of
      Just !ci ->
        let !(!db, !ci') = deriv_f da ci
        in (srep i db, Seq.update i ci' cs)
      Nothing ->
        (mempty, cs)
  SRearr i n j ->
    let !cs' = rearrSeq i n j cs
    in (injDelta $! SRearr i n j, cs')

-- When a function is changed
mapTrChanged ::
  Diff b
  => (c -> (Delta b, c))
  -> Seq.Seq c -> (Delta (Seq b), Seq.Seq c)
mapTrChanged df cs =
  let !(!dbs, !cs') = Seq.unzip $ fmap df cs
  in (sequenceDelta dbs, cs')

data MapCache a b c
  = MapCacheOpen   !(a -> (b, c)) !(Seq.Seq c)
  | MapCacheClosed !(Seq.Seq c)

mapInit ::
  (Diff a, Diff b) =>
  PFun IFqS c a b -> PFun IFqS (MapCache a b c) (Seq a) (Seq b)
mapInit (PFunIFqS (FunCache isClosed f deriv_f)) =
  PFunIFqS (FunCache isClosed h deriv_h)
  where
    h (Seq as) =
      let (!bs, !cs) = Seq.unzip $ fmap f as
      in (Seq bs,
           case isClosed of { Closed -> MapCacheClosed cs; Open ->  MapCacheOpen f cs})
    deriv_h das (MapCacheClosed cs) =
      let (!db, !cs') = iterTr (mapTrUnchangedAtomic f deriv_f) das cs
      in (db, MapCacheClosed cs')
    deriv_h das (MapCacheOpen ff cs) =
      let (!db, !cs') = iterTr (mapTrUnchangedAtomic ff deriv_f) das cs
      in (db, MapCacheOpen ff cs')

mapTr ::
  (Diff b)
  => Delta (PFun IFqS c a b)
  -> Delta (PFun IFqS (MapCache a b c) (Seq a) (Seq b))
mapTr (DeltaPFunIFqS (DeltaFunCache True _)) = mempty
mapTr (DeltaPFunIFqS (DeltaFunCache _ df)) = DeltaPFunIFqS (DeltaFunCache False dh)
  where
    dh (MapCacheClosed cs) = (mempty, MapCacheClosed cs)
    dh (MapCacheOpen f cs) =
      let (!db, !cs') = mapTrChanged df cs
      in (db, MapCacheOpen (changeFunction f df) cs')


mapC ::
  (Diff a, Diff b)
  => IFqS (PFun IFqS c a b) (PFun IFqS (MapCache a b c) (Seq a) (Seq b))
mapC = fromStatelessCode (\a -> [|| mapInit $$a ||]) (\da -> [|| mapTr $$da ||])

