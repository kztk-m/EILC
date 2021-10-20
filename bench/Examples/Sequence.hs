{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Examples.Sequence (
  S(..), type AtomicDelta(..),
  emptyF, singletonF, concatF, mapF,

  cartesian,
  testCode,
  ) where

import           Prelude               hiding ((.))
import qualified Prelude

import qualified Control.Monad
import           Data.Coerce           (coerce)
import           Data.Maybe            (fromJust)
import qualified Data.Sequence         as Seq
import           EILC
import           Language.Unembedding

import qualified Data.Foldable         (toList)

import           Data.Sequence         (Seq)
import           Data.Typeable         (Proxy (Proxy))

import           Data.Monoid

import           Data.Functor.Identity (Identity (Identity))

import           Data.Incrementalized

import           Data.Env

import           Control.DeepSeq
import           Data.IFFT
import           Data.IFqTEU
import           Data.Interaction      (Interaction (..))

newtype S a = S { unS :: Seq.Seq a }
  deriving Show
  deriving newtype (NFData, Functor, Applicative, Foldable, Monad)
  -- NB: deriving of Traversable via GeneralizedNewtypeDeriving causes an error

newtype DList a = DList ([a] -> [a])

instance NFData (DList a) where
  -- evaluating f [] is meaningless
  rnf (DList f) = seq f ()

instance Semigroup (DList a) where
  (<>)  = coerce @(([a] -> [a]) -> ([a] -> [a]) -> ([a] -> [a])) (Prelude..)
  {-# INLINE (<>) #-}

instance Monoid (DList a) where
  mempty = coerce @([a] -> [a]) Prelude.id
  {-# INLINE mempty #-}

instance Show a => Show (DList a) where
  show (DList f) = show (f [])

data JList a = JNil | JAppend !(JList a) !(JList a) | JSingleton !a
  deriving Functor

instance Foldable JList where
  foldMap f js = goNil js
    where
      goNil JNil            = mempty
      goNil (JSingleton a)  = f a
      goNil (JAppend j1 j2) = go j1 $! goNil j2

      go JNil r            = r
      go (JSingleton a)  r = f a <> r
      go (JAppend j1 j2) r = go j1 $! go j2 r

instance Show a => Show (JList a) where
  show js = show (Data.Foldable.toList js)

instance NFData a => NFData (JList a) where
  rnf JNil           = ()
  rnf (JAppend _ _)  = ()
  rnf (JSingleton a) = rnf a

instance Semigroup (JList a) where
  JNil <> as = as
  as <> JNil = as
  as <> bs   = JAppend as bs
  {-# INLINABLE (<>) #-}

instance Monoid (JList a) where
  mempty = JNil
  {-# INLINE mempty #-}

newtype instance Delta (S a) = DS (JList (AtomicDelta (S a)))
  deriving (Semigroup, Monoid)

deriving instance NFData (AtomicDelta (S a)) => NFData (Delta (S a))

deriving instance (Show (Delta a) , Show a) => Show (Delta (S a))

type DeltaS a = AtomicDelta (S a)


instance Diff a => Diff (S a) where
  checkEmpty (DS JNil) = True
  checkEmpty _         = False
  {-# INLINABLE checkEmpty #-}

instance Diff a => HasAtomicDelta (S a) where
  -- Taken from https://github.com/yurug/cts
  data AtomicDelta (S a)
    = SIns   !Int !(S a)     -- ^ SIns i s inserts s at the ith position
    | SDel   !Int !Int       -- ^ SDel i n deletes n elements from the ith position in a sequence
    | SRep   !Int !(Delta a) -- ^ SRep i da applies the delta da to the ith element.
    | SRearr !Int !Int !Int  -- ^ SRearr i n j cuts n elements from the ith position and insert the cut sequence into the jth position (after cuting).

  applyAtomicDelta (S seq0) ds = S (ad seq0 ds)
    where
      ad :: Seq.Seq a -> DeltaS a -> Seq.Seq a
      ad s0 (SIns n (S s)) = insSeq n s s0
      ad s0 (SDel i n)     = delSeq i n s0
      ad s0 (SRep i da)    = repSeq i da s0
      ad s0 (SRearr i n j) = rearrSeq i n j s0
  -- a /+ das = foldl applyDelta a das
  --   where
  --     applyDelta (S s0) (SIns i (S s')) = S $ insSeq i s' s0
  --     applyDelta (S s0) (SDel i n)      = S $ delSeq i n s0
  --     applyDelta (S s0) (SRep i da)     = S $ repSeq i da s0
  --     applyDelta (S s0) (SRearr i n j)  = S $ rearrSeq i n j s0

  injDelta ad = DS $ JSingleton ad -- DS (DList (ad :))
  monoidMap f (DS js) = foldMap f js

  -- monoidMap f (DS (DList x)) = foldMap f (x [])

-- smart? constructor
srep :: Diff a => Int -> Delta a -> Delta (S a)
srep i da
  | checkEmpty da = mempty
  | otherwise     = injDelta $ SRep i da

deriving instance (Show (Delta a), Show a) => Show (AtomicDelta (S a))


insSeq :: Int -> Seq.Seq a -> Seq.Seq a -> Seq.Seq a
insSeq i s' s0 =
    let (s1, s2) = Seq.splitAt i s0
    in s1 Seq.>< s' Seq.>< s2
{-# INLINABLE insSeq #-}

delSeq :: Int -> Int -> Seq.Seq a -> Seq.Seq a
delSeq i n s0 =
    let (s1, stemp) = Seq.splitAt i s0
        s2 = Seq.drop n stemp
    in s1 Seq.>< s2
{-# INLINABLE delSeq #-}

repSeq :: Diff a => Int -> Delta a -> Seq.Seq a -> Seq.Seq a
repSeq i da = Seq.adjust' (/+ da) i
{-# INLINABLE repSeq #-}

rearrSeq :: Int -> Int -> Int -> Seq.Seq a -> Seq.Seq a
rearrSeq i n j s0 =
    let (s1, s23) = Seq.splitAt i s0
        (s2, s3)  = Seq.splitAt n s23
    in insSeq j s2 (s1 Seq.>< s3)
{-# INLINABLE rearrSeq #-}

-- APIs
dsingleton :: Diff a => Delta a -> Delta (S a)
dsingleton = srep 0
{-# INLINABLE dsingleton #-}

singletonF :: (IncrementalizedQ c, K c a, K c (S a), K c ~ Diff, App2 c t e) => e a -> e (S a)
singletonF = lift singletonC
  where
    singletonC =
      fromStateless (\a -> [|| S (Seq.singleton $! $$a) ||])
                    (\da -> [|| dsingleton $$da ||])
      -- ifqFromStatelessA (\a -> [|| S (Seq.singleton $$a) ||])
      --                   (\da -> [|| dsingleton $$da ||])
{-# INLINABLE singletonF #-}

dempty :: Delta (S a)
dempty = mempty
{-# INLINABLE dempty #-}

emptyF :: (IncrementalizedQ c, K c (Unit c), K c (S a), App2 c t e) => e (S a)
emptyF = lift emptyC unit
  where
      emptyC = fromStateless (const [|| S Seq.empty ||]) (const [|| dempty ||])
--    emptyC = ifqFromStatelessA (const [|| S Seq.empty ||]) (const [|| dempty ||])
{-# INLINABLE emptyF #-}

-- lengths of inner sequences.
type ConcatC = Seq.Seq Int

s2c :: S (S a) -> ConcatC
s2c (S s0) = fmap (Seq.length . unS) s0

concatC :: S (S a) -> (S a, ConcatC)
concatC s0 =
  let !res = Control.Monad.join s0
  in (res, s2c s0)

-- trConcatC :: Delta (S (S a)) -> ConcatC -> (Delta (S a), ConcatC)
-- trConcatC [] conn = ([], conn)
-- trConcatC (dss : rest) conn =
--   let (ds1, conn1) = trConcatCAtomic dss conn
--       (ds2, conn2) = trConcatC rest conn1
--   in (ds1 <> ds2, conn2)

insAtC :: Int -> ConcatC -> ConcatC -> ConcatC
insAtC i is is0 =
  foldl (flip (Seq.insertAt i)) is0 is

trConcatCAtomic :: Diff a => DeltaS (S a) -> ConcatC -> (Delta (S a), ConcatC)
trConcatCAtomic (SIns i s') c =
  -- in this case, a sequence s' is inserted at ith element
  let toI = sum (Seq.take i c)
  in (injDelta (SIns toI (Control.Monad.join s')), insAtC i (s2c s') c)
trConcatCAtomic (SDel i n) c =
  let (c1, c23) = Seq.splitAt i c
      (c2, c3)  = Seq.splitAt n c23
      toI       = sum c1
      toN       = sum c2
  in (injDelta (SDel toI toN), c1 Seq.>< c3)
trConcatCAtomic (SRearr i n j) c =
  let (c1, c23) = Seq.splitAt i c
      (c2, c3)  = Seq.splitAt n c23
      toI       = sum c1
      toN       = sum c2
      c13       = c1 Seq.>< c3
      toJ       = sum $ Seq.take j c13
  in (injDelta (SRearr toI toN toJ), insAtC j c2 c13 )
trConcatCAtomic (SRep i ds) c =
  let ci = fromJust $ Seq.lookup i c
      offset = sum $ Seq.take i c
      (ds', ci') = iterTr (goAtomic offset) ds ci
  in (ds', Seq.update i ci' c)
  where
    goAtomic :: Diff a => Int -> DeltaS a -> Int -> (Delta (S a), Int)
    goAtomic offset (SIns j as) ci =
      (injDelta (SIns (offset + j) as), ci + Seq.length (unS as))
    goAtomic offset (SDel j n) ci =
      let -- adjust n to satisfy the invaliant n + j <= ci
          n' = n + (if j + n > ci then ci - (j + n) else 0)
      in (injDelta (SDel (offset + j) n'), ci - n')
    goAtomic offset (SRep j da) ci =
      (srep (offset + j) da, ci)
    goAtomic offset (SRearr j n k) ci =
      (injDelta (SRearr (offset + j) n (offset + k)), ci)

concatF :: (IncrementalizedQ c, App2 c t e, K c ~ Diff, K c a, K c (S (S a)), K c (S a))
           => e (S (S a)) -> e (S a)
concatF = lift $ fromFunctions [|| concatC ||] [|| iterTr trConcatCAtomic ||]
{-# INLINABLE concatF #-}


type family UnFlatten cs = c | c -> cs where
  UnFlatten '[]       = 'None
  UnFlatten (x ': xs) = 'NE (UnFlatten' x xs)

type family UnFlatten' c cs = r | r -> c cs where
  UnFlatten' x '[]      = 'NEOne x
  UnFlatten' x (y : ys) = 'NEJoin ('NEOne x) (UnFlatten' y ys)

convertEnv :: Env f env -> Conn f (UnFlatten env)
convertEnv ENil         = CNone
convertEnv (ECons a as) = CNE $ convertEnv' a as

convertEnv' :: f a -> Env f as -> NEConn f (UnFlatten' a as)
convertEnv' x ENil         = COne x
convertEnv' x (ECons y ys) = CJoin (COne x) (convertEnv' y ys)

unconvertEnv :: Env Proxy env -> Conn f (UnFlatten env) -> Env f env
unconvertEnv ENil CNone = ENil
unconvertEnv (ECons _ ps) (CNE x) =
  let (y, ys) = unconvertEnv' ps x
  in ECons y ys

unconvertEnv' :: Env Proxy env -> NEConn f (UnFlatten' a env) -> (f a, Env f env)
unconvertEnv' ENil (COne x) = (x, ENil)
unconvertEnv' (ECons _ ps) (CJoin (COne x) xs) =
  let (y, ys) = unconvertEnv' ps xs
  in (x, ECons y ys)

type a @+ b = Join a b
infixr 5 @+


class MapAPI term where
  mapAPI :: (Diff a, Diff b) => term (a ': s) b -> term (S a ': s) (S b)

mapTr ::
  (Diff a, Diff b)
  => (a -> (b, c)) -> (Bool -> Delta a -> c -> (Delta b, c))
  -> Seq c -> Delta (S a) -> (Delta (S b), Seq c )
mapTr f dfb cs ds =
  let -- FIXME: can we avoid this step in some ways?
      (dbs1, cs') = mapTrUnchanged (dfb True mempty) cs
      (dbs2, cs'') = iterTr (mapTrChanged f (dfb False)) ds cs'
  in (dbs1 <> dbs2, cs'')

sequenceDelta :: Diff a => Seq (Delta a) -> Delta (S a)
sequenceDelta s =
  mconcat $ zipWith srep [0..] (Data.Foldable.toList s)
  -- mconcat $ zipWith (fmap . SRep) [0..] (Data.Foldable.toList s)

-- Hanldes changes to environments.
mapTrUnchanged ::
  Diff b
  => (c -> (Delta b, c))
  -> Seq.Seq c -> (Delta (S b), Seq.Seq c)
mapTrUnchanged unchanged cs =
  let (dbs, cs') = Seq.unzip $ fmap unchanged cs
  in (sequenceDelta dbs, cs')

mapTrChanged ::
  Diff b
  => (a -> (b, c))
  -> (Delta a -> c -> (Delta b, c))
  -> AtomicDelta (S a) -> Seq c -> (Delta (S b), Seq c)
mapTrChanged f _df (SIns i (S as)) cs     =
  let (bs, cs') = Seq.unzip $ fmap f as
  in (injDelta (SIns i (S bs)), insSeq i cs' cs)
mapTrChanged _ _df (SDel i n) cs     =
  let cs' = delSeq i n cs
  in (injDelta (SDel i n), cs')
mapTrChanged _ df (SRep i da) cs    =
  let ci = Seq.index cs i
      (db, ci') = df da ci
  in (srep i db, Seq.update i ci' cs)
mapTrChanged _ _df (SRearr i n j) cs =
  let cs' = rearrSeq i n j cs
  in (injDelta (SRearr i n j), cs')
-- mapTr ::
--   (a -> (b, c))
--   -> (c -> (Delta b, c))            -- unchanged part
--   -> (AtomicDelta a -> c -> (Delta b, c)) -- changed part
--   -> Seq.Seq c -> AtomicDelta (S a) -> (Delta (S b), Seq.Seq c )
-- mapTr f unchanged _changed cs (SIns i (S as))     =
--   let (newBs, newCs) = Seq.unzip $ fmap f as
--       (dbs, cs') = Seq.unzip $ fmap unchanged cs
--   in (sequenceDelta dbs <> [ SIns i (S newBs) ], insSeq i newCs cs')

-- mapTr _ unchanged _changed cs (SDel i n)     =
--   let (dbs, cs') = Seq.unzip $ delSeq i n (fmap unchanged cs)
--   in ([SDel i n] <> sequenceDelta dbs , cs')
-- mapTr _ unchanged changed cs (SRep i da)     =
--   let ci = Seq.index cs i -- remember the original list
--       (dbs, cs') = Seq.unzip $ Seq.update i (changed da ci) $ fmap unchanged cs
--   in (sequenceDelta dbs, cs')
-- mapTr _ unchanged _changed cs (SRearr i n j) =
--   let (dbs, cs') = Seq.unzip $ rearrSeq i n j (fmap unchanged cs)
--   in ([ SRearr i n j ] <> sequenceDelta dbs , cs')


type EncCS cs2 = Env Identity (Flatten cs2)

type MapC s cs =
   'NE ('NEOne (Seq (EncCS cs)))
    @+ UnFlatten s

instance MapAPI IFqT where
  mapAPI = cMapT

cMapT :: forall s a b. (Diff a, Diff b) => IFqT (a ': s) b -> IFqT (S a ': s) (S b)
cMapT (IFqT (ECons _ tenv) (sh :: Conn Proxy cs) f tr) =
  IFqT (ECons Proxy tenv) sh' f' tr'
  where
    sh' :: Conn Proxy (MapC s cs)
    sh' = joinConn shA (convertEnv tenv)

    shA :: Conn Proxy ('NE ('NEOne (Seq (EncCS cs))))
    shA = CNE (COne Proxy)

    f' ::
      Env PackedCode (S a ': s)
      -> CodeC (Code (S b), Conn PackedCode (MapC s cs))
    f' (ECons (PackedCode as) env) = do
      (bs, cs) <- CodeC $ \k -> [||
            let (bs, cs) = Seq.unzip $ fmap $$(h env)  (unS $$as)
            in $$(k ([|| S bs ||], CNE $ COne $ PackedCode [|| cs ||]))
        ||]
      return (bs, joinConn cs $ convertEnv env)

    h :: Env PackedCode s -> Code (a -> (b, EncCS cs))
    h env = [||
        \a -> $$( runCodeC (f (ECons (PackedCode [|| a ||]) env)) $ \(b, c') -> [|| ($$b, $$(conn2cenv c')) ||])
      ||]

    trh :: Env PackedCodeDelta s -> Conn Proxy cs -> Code (Bool -> Delta a -> EncCS cs -> (Delta b, EncCS cs))
    trh env pcs = [|| \b da c ->
      $$(cenv2conn pcs [|| c ||] $ \cs -> toCode $ do
          env' <- mkLetEnvD $ mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) env
          (db, cs') <- tr (ECons (PackedCodeDelta [|| da ||]) env') cs
          return [|| ($$db, $$(conn2cenv cs') ) ||])
      ||]

    tr' ::
      Env PackedCodeDelta (S a ': s) -> Conn PackedCode (MapC s cs)
      -> CodeC (Code (Delta (S b)), Conn PackedCode (MapC s cs))
    tr' (ECons (PackedCodeDelta das) denv) conn | (CNE (COne (PackedCode cs)), cenv) <- decompConn (isNone shA) (isNone $ convertEnv tenv) conn = do
      let env = unconvertEnv tenv cenv
      --  Potential source of slow down. mapTEU is a fixed version
      env' <- mkLetEnv $ zipWithEnv (\(PackedCode a) (PackedCodeDelta da) -> PackedCode [|| $$a /+ $$da ||]) env denv
      (dbs, cs') <- CodeC $ \k -> [||
          let fElem  = $$(h env')
              trElem = $$(trh denv sh)
              (dbs, cs2') = mapTr fElem trElem $$cs $$das
          in $$(k ([|| dbs ||], [|| cs2' ||]))
        ||]
      return ([|| $$dbs ||], joinConn (CNE $ COne $ PackedCode cs') (convertEnv env'))


mkLetEnv :: Env PackedCode aa -> CodeC (Env PackedCode aa)
mkLetEnv = mapEnvA (\(PackedCode c) -> PackedCode <$> mkLet c)

mkLetEnvD :: Env PackedCodeDelta aa -> CodeC (Env PackedCodeDelta aa)
mkLetEnvD = mapEnvA (\(PackedCodeDelta c) -> PackedCodeDelta <$> mkLet c)

type MapCE a cs = 'NE ('NEOne (Seq (a, EncCS cs)))

trackInputInC :: (a -> (b, c)) -> (a -> (b, (a, c)))
trackInputInC f a = let (b, c) = f a in (b, (a, c))

instance MapAPI IFqTE where
  mapAPI = cMapTE

cMapTE ::
  forall s a b.
  (Diff a, Diff b) => IFqTE (a ': s) b -> IFqTE (S a ': s) (S b)
cMapTE (IFqTE (ECons _ tenv) (sh :: Conn Proxy cs) f tr)
  = IFqTE (ECons Proxy tenv) sh' f' tr'
  where
    sh' :: Conn Proxy (MapCE a cs)
    sh' = CNE (COne Proxy)

    f' ::
      Env PackedCode (S a ': s)
      -> CodeC (Code (S b), Conn PackedCode (MapCE a cs))
    f' (ECons (PackedCode as) env) = do
      (bs, cs) <- CodeC $ \k -> [||
            let (bs, cs) = Seq.unzip $ fmap (trackInputInC $$(h env))  (unS $$as)
            in $$(k ([|| S bs ||], CNE $ COne $ PackedCode [|| cs ||]))
        ||]
      return (bs, cs)

    h :: Env PackedCode s -> Code (a -> (b, EncCS cs))
    h env = [||
        \a -> $$( runCodeC (f (ECons (PackedCode [|| a ||]) env)) $ \(b, c') -> [|| ($$b, $$(conn2cenv c')) ||])
      ||]

    trh :: Env PackedCode s -> Env PackedCodeDelta s -> Conn Proxy cs -> Code (Bool -> Delta a -> (a, EncCS cs) -> (Delta b, (a, EncCS cs)))
    trh env denv pcs = [|| \b da (a, c) ->
      $$(cenv2conn pcs [|| c ||] $ \cs ->
        let denv' = mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) denv
        in runCodeC (tr (ECons (PackedCode [|| a ||]) env) (ECons (PackedCodeDelta [|| da ||]) denv') cs) $ \(db, cs') ->
          [|| ($$db, (a /+ da, $$(conn2cenv cs') )) ||])
      ||]

    tr' ::
      Env PackedCode (S a ': s) -> Env PackedCodeDelta (S a ': s) -> Conn PackedCode (MapCE a cs)
      -> CodeC (Code (Delta (S b)), Conn PackedCode (MapCE a cs))
    tr' (ECons _ env) (ECons (PackedCodeDelta das) denv) (CNE (COne (PackedCode cs))) = do
      (dbs, cs') <- CodeC $ \k -> [||
          let fElem  = trackInputInC $$(h env)
              trElem = $$(trh env denv sh)
              (dbs, cs2') = mapTr fElem trElem $$cs $$das
          in $$(k ([|| dbs ||], [|| cs2' ||]))
        ||]
      return ([|| $$dbs ||], CNE $ COne $ PackedCode cs')

mkMapInt ::
  forall s a b.
  (Diff a, Diff b) =>
  Code (Env Identity s)
  -> Code (Env Identity s -> a -> (b, Interaction (Env PackedDelta (a ': s)) (Delta b)))
  -> Code (Env PackedDelta s -> Bool -> Delta a -> Interaction (Env PackedDelta (a ': s)) (Delta b) -> (Delta b, Interaction (Env PackedDelta (a ': s)) (Delta b)))
  -> Code (Seq (Interaction (Env PackedDelta (a : s)) (Delta b)))
  -> CodeC (Code (Interaction (Env PackedDelta (S a : s)) (Delta (S b))))
mkMapInt env h' trh c0 = CodeC $ \k -> [||
      let mapInt c = Interaction $ \(ECons (PackedDelta das) denv) ->
            let f = $$h' $ zipWithEnv (\(Identity a) (PackedDelta da) -> Identity $ a /+ da) $$env denv
                trF = $$trh denv
                (dbs, c') = mapTr f trF c das
            in (dbs, mapInt c') -- (dbs, mapInt c')
      in $$(k [|| mapInt $$c0 ||])
  ||]

packEnv :: Env PackedCode s -> Code (Env Identity s)
packEnv ENil                      = [|| ENil ||]
packEnv (ECons (PackedCode a) as) = [|| ECons (Identity $$a) $$(packEnv as) ||]

unpackEnv :: Env proxy s -> Code (Env Identity s) -> (Env PackedCode s -> Code r) -> Code r
unpackEnv ENil c k =
  [|| case $$c of { ENil -> $$(k ENil) } ||]
unpackEnv (ECons _ s) c k =
  [|| let (Identity _a, as) = headTailEnv $$c
      in $$(unpackEnv s [|| as ||] (k . ECons (PackedCode [|| _a ||]))) ||]

instance MapAPI IFFT where
  mapAPI = cMapF

cMapF :: forall s a b. (Diff a, Diff b) => IFFT (a ': s) b -> IFFT (S a ': s) (S b)
cMapF (IFFT (ECons _ tenv) h) = IFFT (ECons Proxy tenv) $ \(ECons (PackedCode as) env) -> do
  let cenv = packEnv env
  (bs, is) <- CodeC $ \k -> [||
        let (bs, is) = Seq.unzip $ fmap ($$h'' $$cenv) (unS $$as)
        in $$(k ([|| S bs ||] , [|| is ||]) )
    ||]
  i <- mkMapInt cenv h'' trh is
  return (bs, i)
  where
    h'' :: Code (Env Identity s -> a -> (b, Interaction (Env PackedDelta (a ': s)) (Delta b)))
    h'' = [|| \penv a -> $$(unpackEnv tenv [|| penv ||] $ \env -> runCodeC (h $ ECons (PackedCode [|| a ||]) env) $ \(b, i) -> [|| ($$b, $$i) ||]) ||]

    trh :: Code (Env PackedDelta s -> Bool -> Delta a -> Interaction (Env PackedDelta (a ': s)) (Delta b) -> (Delta b, Interaction (Env PackedDelta (a ': s)) (Delta b)))
    trh = [|| \denv doesUpdateEnv da i ->
                      let denv' = if doesUpdateEnv then denv else mapEnv (\(PackedDelta _) -> PackedDelta mempty) denv
                      in runInteraction i (ECons (PackedDelta da) denv') ||]


mapF :: forall cat term e a b. (MapAPI term, LetTerm cat term, App2 cat term e, K cat ~ Diff, Diff a, Diff b) => (e a -> e b) -> e (S a) -> e (S b)
mapF = flip (liftSO2 (Proxy @'[ '[], '[a] ]) $ \e1 e2 -> letTerm e1 (mapAPI e2))


fstF :: (IncrementalizedQ c, App2 c t e, K c ~ Diff, Diff a, Diff b) => e (a, b) -> e a
fstF = lift $ fromStateless (\a -> [|| fst $$a ||]) (\dz -> [|| fstDelta $$dz||])

sndF :: (IncrementalizedQ c, App2 c t e, K c ~ Diff, Diff a, Diff b) => e (a, b) -> e b
sndF = lift $ fromStateless (\a -> [|| snd $$a ||]) (\dz -> [|| sndDelta $$dz ||])

cartesian :: (IncrementalizedQ cat, MapAPI term, LetTerm cat term, K cat ~ Diff, Prod cat a b ~ (a, b), App2 cat term e, Diff a, Diff b) => e (S a) -> e (S b) -> e (S (a, b))
cartesian as bs =
  concatMapF (\a -> mapF (pair a) bs) as
  where
    concatMapF f x = concatF (mapF f x)


type family PairIfUsed a us cs where
  PairIfUsed a '[] cs = EncCS cs
  PairIfUsed a ('False ': _) cs = EncCS cs
  PairIfUsed a ('True  ': _) cs = (a, EncCS cs)

-- type MapCEU a cs1 cs2 us2 =
--     cs1
-- --    @+ 'NE ('NEOne (Seq.Seq (Conn Identity cs2)))
--     @+ 'NE ('NEOne (Seq (PairIfUsed a us2 cs2)))

type MapCEU a us cs = 'NE ('NEOne (Seq (PairIfUsed a us cs)))

instance MapAPI IFqTEU where
  mapAPI = cMapTEU

cMapTEU :: forall s a b. (Diff a, Diff b) => IFqTEU (a ': s) b -> IFqTEU (S a ': s) (S b)
cMapTEU (IFqTEU (ECons _ tenv) (sh ::Conn Proxy cs) (u :: Env SBool f_us) f (ut :: Env SBool tr_us) tr)
  = IFqTEU (ECons Proxy tenv) sh' u' f' ut' tr'
  where
    sh' :: Conn Proxy (MapCEU a tr_us cs)
    sh' = CNE $ COne $ Proxy @(Seq (PairIfUsed a tr_us cs))

    tail' :: forall f xs. Env f xs -> Env f (SafeTail xs)
    tail' ENil         = ENil
    tail' (ECons _ xs) = xs

    u' :: Env SBool ('True ': SafeTail f_us)
    u' = ECons STrue (tail' u)

    ut' :: Env SBool ('False ': MergeUses (SafeTail f_us) (SafeTail tr_us))
    ut' = ECons SFalse ut0

    (ut0, extF, extT) = mergeTupled (tail' u) (tail' ut) tenv

    f' ::
      Env PackedCode (S a : Extr s (SafeTail f_us))
      -> CodeC (Code (S b), Conn PackedCode (MapCEU a tr_us cs))
    f' (ECons (PackedCode as) env) = CodeC $ \k ->
        [|| let (bs, cs) = Seq.unzip $ fmap $$(h env) (unS $$as)
            in $$(k ([|| S bs ||], CNE $ COne $ PackedCode [|| cs ||])) ||]

    h :: Env PackedCode (Extr s (SafeTail f_us)) -> Code (a -> (b, PairIfUsed a tr_us cs))
    h = case ut of
      ENil           -> h0
      ECons SFalse _ -> h0
      ECons STrue  _ -> \env -> [|| trackInputInC $$(h0 env) ||]
      where
        h0 :: Env PackedCode (Extr s (SafeTail f_us)) -> Code (a -> (b, EncCS cs))
        h0 env = [|| \a -> $$(
                      toCode $ do
                        (b, c') <- f (extendEnv tenv u (PackedCode [|| a ||]) env)
                        return [|| ($$b , $$(conn2cenv c')) ||]
                    )
                  ||]

    allFalse :: forall xs. Env SBool xs -> Bool
    allFalse ENil              = True
    allFalse (ECons SFalse xs) = allFalse xs
    allFalse (ECons STrue _)   = False

    tr' ::
      Env PackedCode (Extr s (MergeUses (SafeTail f_us) (SafeTail tr_us)))
      -> Env PackedCodeDelta (S a : Extr s (SafeTail f_us))
      -> Conn PackedCode (MapCEU a tr_us cs)
      -> CodeC (Code (Delta (S b)),
                Conn PackedCode (MapCEU a tr_us cs))
    tr' env (ECons (PackedCodeDelta das) denv) (CNE (COne (PackedCode c))) = do
      let fenv = rearrEnv extF env
      let trenv = rearrEnv extT env
      (dbs, c') <- CodeC $ \k ->
        if allFalse (tail' u) -- that is, f of map f is closed
          then
            [|| let fElem  = $$(h fenv)
                    trElem = $$(trh trenv denv sh)
                    (dbs, c') = iterTr (mapTrChanged fElem (trElem False)) $$das $$c
                in $$(k ([|| dbs ||], [|| c' ||])) ||]
          else
            [||
              let fElem  = $$(h fenv)
                  trElem = $$(trh trenv denv sh)
                  (dbs, c') = mapTr fElem trElem $$c $$das
              in $$(k ([|| dbs ||], [|| c' ||]))
            ||]
      return (dbs, CNE $ COne $ PackedCode c')

    trh
      :: Env PackedCode (Extr s (SafeTail tr_us))
         -> Env PackedCodeDelta (Extr s (SafeTail f_us))
         -> Conn Proxy cs
         -> Code (Bool
                  -> Delta a
                  -> PairIfUsed a tr_us cs
                  -> (Delta b, PairIfUsed a tr_us cs))
    trh trenv denv pcs = case ut of
      ENil ->
          [|| \_ da c ->
            $$(cenv2conn pcs [|| c ||] $ \cs ->
              runCodeC (tr (extractingByNilIsNil $ ECons Proxy tenv) (extendEnv tenv u (PackedCodeDelta [|| da ||]) denv) cs) $ \(db, cs') -> [|| ($$db, $$(conn2cenv cs')) ||]) ||]
      ECons SFalse _ ->
          [|| \b da c ->
            $$(cenv2conn pcs [|| c ||] $ \cs -> toCode $ do
                denv' <- mkLetEnvD $ mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) denv
                (db, cs') <- tr trenv (extendEnv tenv u (PackedCodeDelta [|| da ||]) denv') cs
                return [|| ($$db, $$(conn2cenv cs')) ||]
              ) ||]
      ECons STrue _ ->
          [|| \b da (a, c) ->
            $$(cenv2conn pcs [|| c ||] $ \cs -> toCode $ do
                denv' <- mkLetEnvD $ mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) denv
                (db, cs') <- tr (extendEnv tenv ut (PackedCode [|| a ||]) trenv) (extendEnv tenv u (PackedCodeDelta [|| da ||]) denv') cs
                return  [|| ($$db, (a /+ da, $$(conn2cenv cs') )) ||])
          ||]




-- cMapTEU :: forall s a b. (Diff a, Diff b, AllIn s Diff) => IFqTEU s (S a) -> IFqTEU (a ': s) b -> IFqTEU s (S b)
-- cMapTEU e1 e2 =
--   letTerm e1 (cMapTEU' e2)


-- To avoid errors caused by "stack repl"


type TestCodeType =
  Code
    ((S Int, S Int)
    -> (S (Int, Int),
        Interaction (Delta (S Int, S Int)) (Delta (S (Int, Int)))))


testCode :: (K cat ~ Diff, MapAPI term, LetTerm cat term, Prod cat Int Int ~ (Int, Int), IncrementalizedQ cat, Term cat term) => Proxy term -> TestCodeType
testCode proxy = compile $ runMonoWith proxy $ \xs -> cartesian (fstF xs) (sndF xs)



-- >>> let f = $$( testCode $ Proxy @IFqTEU )
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


