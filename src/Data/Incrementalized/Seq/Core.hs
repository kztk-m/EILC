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

     singletonF, emptyF, appendF, concatF, nullF,

     -- * Component functions
     singletonTr, nullInit, nullTrAtomic,
     appendInit, appendTrAtomic, AppendCache,
     concatInit, concatTrAtomic, MapCache(..),
     mapC, mapInit, mapTr, mapTrChanged, mapTrUnchangedAtomic,

     filterC, filterInit, filterTr, filterTrChanged, filterTrUnchangedAtomic,
   ) where

import qualified Data.Foldable
import qualified Data.Sequence                 as Seq
import qualified Data.Sequence.Internal        as SeqI
import           Prelude                       hiding (id, (.))
import qualified Text.Show                     as TS

-- import           Control.Arrow                 ((***))
import           Control.DeepSeq               (NFData, rnf)
import qualified Control.Monad
import           Data.Delta
import           Data.Foldable                 (foldl')
import           Data.IFq
import           Data.Incrementalized
import           Data.Incrementalized.Bool
import           Data.Incrementalized.Function
import           Data.JoinList                 hiding (fromList)
import           Data.Typeable                 (Typeable)
import           Language.Unembedding          as Unemb

-- import           Debug.Trace                   (trace)
-- import           Text.Printf

-- class NFDataSpine a where
--   rnfSpine :: a -> ()

-- forceSpine :: NFDataSpine a => a -> a
-- forceSpine x = rnfSpine x `seq` x
-- instance NFDataSpine (Seq.Seq a) where
--   rnfSpine (SeqI.Seq x) = rnfSpine x

-- instance NFDataSpine a => NFDataSpine (SeqI.FingerTree a) where
--   rnfSpine SeqI.EmptyT         = ()
--   rnfSpine (SeqI.Single a)     = rnfSpine a
--   rnfSpine (SeqI.Deep _ _ f _) = rnfSpine f

-- instance NFDataSpine (SeqI.Elem a) where
--   rnfSpine _ = ()

-- instance NFDataSpine a => NFDataSpine (SeqI.Node a) where
--   rnfSpine (SeqI.Node2 _ x y)   = rnfSpine x `seq` rnfSpine y
--   rnfSpine (SeqI.Node3 _ x y z) = rnfSpine x `seq` rnfSpine y `seq` rnfSpine z

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


instance NFData a => NFData (Seq a) where
  rnf (Seq a) = rnf a


instance (NFData a, NFData (Delta a)) => NFData (AtomicDelta (Seq a)) where
  rnf (SIns _ s)     = rnf s
  rnf (SDel _ _)     = ()
  rnf (SRep _ da)    = rnf da
  rnf (SRearr _ _ _) = ()

instance (NFData a, NFData (Delta a)) => NFData (Delta (Seq a)) where
  rnf (DeltaSeq a) = rnf a

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

instance Diff a => DiffReplace (Seq a) where
  replaceTo b = injDelta (SDel 0 maxBound) <> injDelta (SIns 0 b)

instance Diff a => DiffMinus (Seq a) where
  -- | @b /- a@ produce a change that removes a completely and then inserts b.
  Seq b /- Seq a = injDelta (SDel 0 (Seq.length a)) <> injDelta (SIns 0 $ Seq b)

-- smart? constructor
srep :: Diff a => Int -> Delta a -> Delta (Seq a)
srep i da
  | checkEmpty da = mempty
  | otherwise     = injDelta $ SRep i da

-- deleting 0 elements is identity.
-- "filter" is the only API that can violate this invariant.
sdel :: Diff a => Int -> Int -> Delta (Seq a)
sdel _ 0 = mempty
sdel i n = injDelta $ SDel i n

-- inesrting 0 elements is identity.
-- "filter" is the only API that can violate this invariant.
sins :: Diff a => Int -> Seq a -> Delta (Seq a)
sins _ (Seq xs) | Seq.null xs = mempty
sins n xs = injDelta $ SIns n xs


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

data AppendCache = AppendCache !Int !Int

appendInit :: (Seq a, Seq a) -> (Seq a, AppendCache)
appendInit (Seq a1 , Seq a2) =
  (Seq $ a1 Seq.>< a2, AppendCache (Seq.length a1) (Seq.length a2))

appendTrAtomic ::
  Diff a =>
  AtomicDelta (Seq a, Seq a)
  -> AppendCache
  -> (Delta (Seq a), AppendCache)
appendTrAtomic dab (AppendCache l1 l2) = case dab of
  ADFst (SIns i as) ->
    let !i' = min i l1
    in (injDelta $ SIns i' as, AppendCache (l1 + Seq.length (unSeq as)) l2)
  ADFst (SDel i n) ->
    let !i' = min i l1
        !n' = min n (l1 - i')
    in (injDelta $ SDel i' n', AppendCache (l1 - n') l2)
  ADFst (SRep i da) ->
    if 0 <= i && i < l1 then
      (srep i da, AppendCache l1 l2)
    else
      (mempty, AppendCache l1 l2)
  ADFst (SRearr i n j) ->
    let !i' = min i l1
        !n' = min n (l1 - i')
        !j' = min j (l1 - n')
    in (injDelta $ SRearr i' n' j', AppendCache l1 l2)
  ADSnd (SIns i as) ->
    let !i' = min i l2
    in (injDelta $ SIns (i' + l1) as, AppendCache l1 (l2 + Seq.length (unSeq as)))
  ADSnd (SDel i n) ->
    let !i' = min i l2
        !n' = min n (l2 - i')
    in (injDelta $ SDel (i' + l1) n', AppendCache l1 (l2 - n'))
  ADSnd (SRep i da) ->
    if 0 <= i && i < l2 then
      (srep (i + l1) da, AppendCache l1 l2)
    else
      (mempty, AppendCache l1 l2)
  ADSnd (SRearr i n j) ->
    let !i' = min i l1
        !n' = min n (l1 - i')
        !j' = min j (l1 - n')
    in (injDelta $ SRearr (l1 + i') n' (l1 + j'), AppendCache l1 l2)

appendC :: Diff a => IFqS (Seq a, Seq a) (Seq a)
appendC = fromFunctionsCode [|| appendInit ||] [|| iterTr appendTrAtomic ||]

appendF :: (Diff a, Typeable a, App IFqS e) => e (Seq a) -> e (Seq a) -> e (Seq a)
appendF x y = lift appendC (pair x y)

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
      c'  = insAtC i (makeConcatCache s') c
  in (injDelta $! SIns toI (Control.Monad.join s'), c')
concatTrAtomic (SDel i n) c =
  let (!c1, !c23) = Seq.splitAt i c
      (!c2, !c3)  = Seq.splitAt n c23
      !toI        = sum c1
      !toN        = sum c2
      c'         = c1 Seq.>< c3
  in (injDelta $! SDel toI toN, c')
concatTrAtomic (SRearr i n j) c =
  let (!c1, !c23) = Seq.splitAt i c
      (!c2, !c3)  = Seq.splitAt n c23
      !toI        = sum c1
      !toN        = sum c2
      !c13        = c1 Seq.>< c3
      !toJ        = sum $ Seq.take j c13
      c'         = insAtC j c2 c13
  in -- trace (printf "SRearr %d %d %d" i n j ++ " -> " ++ printf "SRearr %d %d %d" toI toN toJ ++ " when cache is: " ++ show c ++ " -> " ++ show c) $
     (injDelta $! SRearr toI toN toJ, c' )

concatTrAtomic (SRep i ds) c
  | Nothing  <- Seq.lookup i c = (mempty, c)
  | Just !ci <- Seq.lookup i c =
  let !offset = sum $ Seq.take i c
      !(!ds', !ci') = iterTr (goAtomic offset) ds ci
      c' = Seq.update i ci' c
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
      let (!bs, !cs) = {-# SCC "mapInit:fmap" #-} Seq.unzip $ fmap f as
          !mcs = case isClosed of { Closed -> MapCacheClosed cs; Open ->  MapCacheOpen f cs}
      in (Seq bs, mcs)
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


{-
How filter should behaves?

If a function itself does not change, situation is rather easy:

   fitler f (a /+ da) = filter f a /+ ???

To compute the indices appropriate, we need to keep track of which elements has been filtered:

   Ins i as |-->
     let cT = length $ filter id $ take i c
         bs = map (f &&& id) as
         as' = map snd $ filter fst bs
         cs' = map fst $ bs
     in (Ins cT as', cs')

   ...

We also need to store caches used for functions.

But, things become harder when we allow function changes. We need to
store the original values for this case because a function becomes
True for an element must insert the element.

-}

data FTriple a c = FTriple !a !Bool !c

type CommonFilterCache a c = Seq.Seq (FTriple a c)

data FilterCache a c
  = FilterCacheOpen   !(a -> (Bool, c)) !(CommonFilterCache a c)
  | FilterCacheClosed !(CommonFilterCache a c)

-- getBoolCache :: FilterCache a c -> Seq.Seq (Bool, c)
-- getBoolCache (FilterCacheOpen _ _ cs) = cs
-- getBoolCache (FilterCacheClosed _ cs) = cs

-- setBoolCache :: FilterCache a c -> Seq.Seq (Bool,c) -> FilterCache a c
-- setBoolCache (FilterCacheOpen f orig _) cs      = FilterCacheOpen f orig cs
-- setBoolCache (FilterCacheClosed orig _)      cs = FilterCacheClosed orig cs

-- modifyBoolCache u cc = setBoolCache cc (u $ getBoolCache cc)

-- getOrigSeq :: FilterCache a c -> Seq.Seq a
-- getOrigSeq (FilterCacheOpen _ orig _) = orig
-- getOrigSeq (FilterCacheClosed orig _) = orig

-- modifyOrigSeq :: (Seq.Seq a -> Seq.Seq a) -> FilterCache a c -> FilterCache a c
-- modifyOrigSeq u (FilterCacheOpen f orig cs) = FilterCacheOpen f (u orig) cs
-- modifyOrigSeq _ (FilterCacheClosed orig cs) = FilterCacheClosed (u orig) cs

fst3 :: FTriple a c  -> a
fst3 (FTriple a _ _) = a
snd3 :: FTriple a c -> Bool
snd3 (FTriple _ b _) = b



filterTrUnchangedAtomic ::
  (Diff a)
  => (a -> (Bool, c))
  -> (Delta a -> c -> (Delta Bool, c))
  -> AtomicDelta (Seq a) -> CommonFilterCache a c -> (Delta (Seq a), CommonFilterCache a c)
filterTrUnchangedAtomic p deriv_p dseq cc = case dseq of
  SIns i (Seq as) ->
    let !i'  = length $ Seq.filter snd3 $ Seq.take i cc
        !bs  = fmap (\a -> let (b, c) = p a in FTriple a b c) as
        !as' = fst3 <$> Seq.filter snd3 bs
        cc' = insSeq i bs cc
    in (sins i' (Seq as'), cc')
  SDel i n ->
    let (!cs1, cs23) = Seq.splitAt i cc
        !cs2         = Seq.take n cs23
        !i' = length $ Seq.filter snd3 cs1
        !n' = length $ Seq.filter snd3 cs2
        cc' = delSeq i n cc
    in (sdel i' n', cc')
  SRep i da ->
    case Seq.lookup i cc of
      Just (FTriple ai bi ci) ->
        let !i' = length $ Seq.filter snd3 $ Seq.take i cc
            (!db, ci') = deriv_p da ci
            ai' = ai /+ da
            cc' = Seq.update i (FTriple ai' (bi /+ db) ci') cc
            !up  = case (bi, db) of
                    (True,  DBNot) -> injDelta (SDel i' 1)
                    (True,  DBKeep) -> injDelta (SRep i' da)
                    (False, DBNot) -> injDelta (SIns i' (Seq $ Seq.singleton ai'))
                    _              -> mempty
        in (up, cc')
      Nothing -> (mempty, cc)
  SRearr i n j ->
    let (!cs1, cs23) = Seq.splitAt i cc
        (!cs2, !cs3) = Seq.splitAt n cs23
        !i' = length $ Seq.filter snd3 cs1
        !n' = length $ Seq.filter snd3 cs2
        !j' = length $ Seq.take j (cs1 Seq.>< cs3)
        cc' = rearrSeq i n j cc
    in (injDelta $ SRearr i' n' j', cc')


filterTrChanged ::
  (Diff a)
  => (c -> (Delta Bool, c))
  -> CommonFilterCache a c -> (Delta (Seq a), CommonFilterCache a c)
filterTrChanged df cs =
  let (ds, cs',_) =
        foldl' (\(deltas, accCS, !i) (FTriple a b c) ->
                     let (db, c') = df c
                         b' = b /+ db
                         accCS' = accCS Seq.|> FTriple a b' c'
                     in case (b, db) of
                          (True,  DBNot) -> (deltas <> injDelta (SDel i 1), accCS', i)
                          (False, DBNot) -> (deltas <> injDelta (SIns i (Seq $ Seq.singleton a)), accCS', i + 1)
                          (True,  DBKeep) -> (deltas, accCS', i + 1)
                          (False, DBKeep) -> (deltas, accCS', i)) (mempty, Seq.empty, 0) cs
  in (ds, cs')

filterInit ::
  (Diff a) =>
  PFun IFqS c a Bool -> PFun IFqS (FilterCache a c) (Seq a) (Seq a)
filterInit (PFunIFqS (FunCache isClosed f deriv_f)) =
  PFunIFqS (FunCache isClosed h deriv_h)
  where
    h (Seq as) =
      let (!bs, !cs) = {-# SCC "filterInit:fmap" #-} Seq.unzip $ fmap (\a -> let (b, c) = f a in ((b, a), FTriple a b c))  as
          !rs  = Seq $ snd <$> Seq.filter fst bs
          !fcs = case isClosed of { Closed -> FilterCacheClosed cs; Open ->  FilterCacheOpen f cs}
      in (rs, fcs)
    deriv_h das (FilterCacheClosed cs) =
      let (!db, !cs') = iterTr (filterTrUnchangedAtomic f deriv_f) das cs
      in (db, FilterCacheClosed cs')
    deriv_h das (FilterCacheOpen ff cs) =
      let (!db, !cs') = iterTr (filterTrUnchangedAtomic ff deriv_f) das cs
      in (db, FilterCacheOpen ff cs')


filterTr ::
  (Diff a)
  => Delta (PFun IFqS c a Bool)
  -> Delta (PFun IFqS (FilterCache a c) (Seq a) (Seq a))
filterTr (DeltaPFunIFqS (DeltaFunCache True _)) = mempty
filterTr (DeltaPFunIFqS (DeltaFunCache _ df)) = DeltaPFunIFqS (DeltaFunCache False dh)
  where
    dh (FilterCacheClosed cs) = (mempty, FilterCacheClosed cs)
    dh (FilterCacheOpen f cs) =
      let (!db, !cs') = filterTrChanged df cs
      in (db, FilterCacheOpen (changeFunction f df) cs')


filterC ::
  (Diff a)
  => IFqS (PFun IFqS c a Bool) (PFun IFqS (FilterCache a c) (Seq a) (Seq a))
filterC = fromStatelessCode (\a -> [|| filterInit $$a ||]) (\da -> [|| filterTr $$da ||])

nullInit :: Seq a -> (Bool, Int)
nullInit (Seq a) = (Seq.null a, Seq.length a)

nullTrAtomic ::
  AtomicDelta (Seq a)
  -> Int
  -> (Delta Bool, Int)
nullTrAtomic da len = case da of
  SIns _ (Seq as) ->
    let !b = Seq.null as
        !b0 = len == 0
        !b' = b0 || b
    in (b' /- b0, len + Seq.length as)
  SDel i n ->
    let !i' = min i len
        !n' = min n (len - i')
        !b0 = len == 0
        !b' = len - n' == 0
    in (b' /- b0, len - n')
  SRep _ _ -> (mempty, len)
  SRearr _ _ _ -> (mempty, len)

nullC :: Diff a => IFqS (Seq a) Bool
nullC = fromFunctionsCode [|| nullInit ||] [|| iterTr nullTrAtomic ||]

nullF :: (Diff a, Typeable a, App IFqS e) => e (Seq a) -> e Bool
nullF = lift nullC
