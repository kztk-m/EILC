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
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ViewPatterns               #-}

module Examples.Sequence (
  emptyF, singletonF, concatF, mapF,

  cartesian,
  MyInt(..),
  testCode,
  ) where

import           Prelude               hiding ((.))

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

import           Data.IFFT
import           Data.IFqTEU
import           Data.Interaction      (Interaction (..))
newtype S a = S { unS :: Seq.Seq a }
  deriving Show

-- Taken from https://github.com/yurug/cts
data instance AtomicDelta (S a)
 = SIns !Int !(S a) -- ^ SIns i s inserts s at the ith position
 | SDel !Int !Int   -- ^ SDel i n deletes n elements from the ith position in a sequence
 | SRep !Int !(AtomicDelta a) -- ^ SRep i da applies the delta da to the ith element.
 | SRearr !Int !Int !Int -- ^ SRearr i n j cuts n elements from the ith position and insert the cut sequence into the jth position (after cuting).

deriving instance (Show (AtomicDelta a), Show a) => Show (AtomicDelta (S a))

type DeltaS a = AtomicDelta (S a)


instance Diff a => Diff (S a) where
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

repSeq :: Diff a => Int -> AtomicDelta a -> Seq.Seq a -> Seq.Seq a
repSeq i da = Seq.adjust' (`applyAtomicDelta` da) i
{-# INLINABLE repSeq #-}

rearrSeq :: Int -> Int -> Int -> Seq.Seq a -> Seq.Seq a
rearrSeq i n j s0 =
    let (s1, s23) = Seq.splitAt i s0
        (s2, s3)  = Seq.splitAt n s23
    in insSeq j s2 (s1 Seq.>< s3)
{-# INLINABLE rearrSeq #-}

-- APIs
dsingleton :: AtomicDelta a -> Delta (S a)
dsingleton da = injMonoid $ coerce $ SRep 0 da
{-# INLINABLE dsingleton #-}

singletonF :: (IncrementalizedQ c, K c a, K c (S a), App2 c t e) => e a -> e (S a)
singletonF = lift singletonC
  where
    singletonC =
      fromStateless (\a -> [|| S (Seq.singleton $$a) ||])
                    (\da -> [|| iterTrStateless dsingleton $$da ||])
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

type ConcatC = Seq.Seq Int


concatSeq :: S (S a) -> S a
concatSeq (S s0) = S $ foldr (\(S a) r -> a Seq.>< r) Seq.empty s0

s2c :: S (S a) -> ConcatC
s2c (S s0) = fmap (\(S a) -> Seq.length a) s0

concatC :: S (S a) -> (S a, ConcatC)
concatC s0 = (concatSeq s0, s2c s0)

-- trConcatC :: Delta (S (S a)) -> ConcatC -> (Delta (S a), ConcatC)
-- trConcatC [] conn = ([], conn)
-- trConcatC (dss : rest) conn =
--   let (ds1, conn1) = trConcatCAtomic dss conn
--       (ds2, conn2) = trConcatC rest conn1
--   in (ds1 <> ds2, conn2)

insAtC :: Int -> ConcatC -> ConcatC -> ConcatC
insAtC i is is0 =
  foldl (flip (Seq.insertAt i)) is0 is

trConcatCAtomic :: DeltaS (S a) -> ConcatC -> (Delta (S a), ConcatC)
trConcatCAtomic (SIns i s') c =
  -- in this case, a sequence s' is inserted at ith element
  let toI = sum (Seq.take i c)
  in (injMonoid (SIns toI (concatSeq s')), insAtC i (s2c s') c)
trConcatCAtomic (SDel i n) c =
  let (c1, c23) = Seq.splitAt i c
      (c2, c3)  = Seq.splitAt n c23
      toI       = sum c1
      toN       = sum c2
  in (injMonoid (SDel toI toN), c1 Seq.>< c3)
trConcatCAtomic (SRearr i n j) c =
  let (c1, c23) = Seq.splitAt i c
      (c2, c3)  = Seq.splitAt n c23
      toI       = sum c1
      toN       = sum c2
      c13       = c1 Seq.>< c3
      toJ       = sum $ Seq.take j c13
  in (injMonoid (SRearr toI toN toJ), insAtC j c2 c13 )
trConcatCAtomic (SRep i ds) c =
  let ci = fromJust $ Seq.lookup i c
      offset = sum $ Seq.take i c
      (ds', ci') = goAtomic offset ds ci
  in (ds', Seq.update i ci' c)
  where
    -- go :: Int -> Delta (S a) -> Int -> (Delta (S a), Int)
    -- go _ [] ci = ([], ci)
    -- go offset (x : xs) ci =
    --   let (ds1, ci1) = goAtomic offset x ci
    --       (ds2, ci2) = go offset xs ci1
    --   in (ds1 <> ds2, ci2)

    goAtomic :: Int -> DeltaS a -> Int -> (Delta (S a), Int)
    goAtomic offset (SIns j as) ci =
      (injMonoid (SIns (offset + j) as), ci + Seq.length (unS as))
    goAtomic offset (SDel j n) ci =
      let -- adjust n to satisfy the invaliant n + j <= ci
          n' = n + (if j + n > ci then ci - (j + n) else 0)
      in (injMonoid (SDel (offset + j) n'), ci - n')
    goAtomic offset (SRep j da) ci =
      (injMonoid (SRep (offset + j) da), ci)
    goAtomic offset (SRearr j n k) ci =
      (injMonoid (SRearr (offset + j) n (offset + k)), ci)

concatF :: (IncrementalizedQ c, App2 c t e, K c (S (S a)), K c (S a))
           => e (S (S a)) -> e (S a)
concatF = lift $ fromFunctions [|| concatC ||] [|| iterTr trConcatCAtomic ||]
  -- lift $ ifqFromFunctionsA [|| concatC ||] [|| trConcatCAtomic ||]
{-# INLINABLE concatF #-}


-- mapTr ::
--   Monoid (Delta a)
--   => (a -> (b, c)) -> (Delta a -> c -> (Delta b, c))
--   -> Seq.Seq (c, a) -> Delta (S a) -> (Delta (S b), Seq.Seq (c, a) )
-- mapTr _f tr cs [] =
--     let (dbs, cs') = unzip $ map (\(c,a) -> let (b, c') = tr mempty a c in (b, (c', a))) cs
--     in (zipWith (\i db -> SRep i db) [0..] dbs, cs')
-- mapTr f tr cs (d : ds) =
--   let (d1, cs1) = trOne f tr cs d
--       (d2, cs2) = mapTr f tr cs1 ds
--   in (d1 <> d2, cs2)

-- trOne :: (a -> (b, c)) -> (Delta a -> c -> (Delta b, c))
--          -> Seq.Seq (c, a) -> DeltaS a -> (Delta (S b), Seq.Seq (c, a) )
-- trOne = _

-- trOne :: (a -> (b, c)) -> (Delta a -> c -> (Delta b, c))
--          -> Seq.Seq c -> DeltaS a -> (Delta (S b), Seq.Seq c)
-- trOne f _ cs (SIns i (S as)) =
--   let (bs, cs') = Seq.unzip $ fmap f as
--   in ([SIns i (S bs)], foldl (flip (Seq.insertAt i)) cs' cs)
-- trOne _ _ cs (SDel i n) =
--   ([SDel i n], delSeq i n cs)
-- trOne _ _ cs (SRearr i n j) =
--   ([SRearr i n j], rearrSeq i n j cs)
-- trOne _ tr cs (SRep i da) =
--   let ci = fromJust $ Seq.lookup i cs
--       (db, ci') = tr da ci
--   in ([SRep i db], Seq.update i ci' cs)



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

-- mkMapTr ::
--   Conn Proxy cs2
--   -> Code (a -> (b, Conn Identity cs2))
--   -> (Index PackedCodeAtomicDelta (a : s) -> Conn PackedCode cs2 -> CodeC (Code (Delta b), Conn PackedCode cs2))
--   -> (Index PackedCodeAtomicDelta s -> Code (Seq.Seq (Conn Identity cs2, a)) -> Code (AtomicDelta (S a)) ->
--         CodeC (Code (Delta (S b)), Code (Seq.Seq (Conn Identity cs2, a))))
-- mkMapTr sh f tr denv cs dseq = [||
--     case $$dseq of

--   ||]

class MapAPI term where
  mapAPI :: Diff a => term (a ': s) b -> term (S a ': s) (S b)

mapTr ::
  (a -> (b, c)) -> (Bool -> Delta a -> c -> (Delta b, c))
  -> Seq c -> Delta (S a) -> (Delta (S b), Seq c )
mapTr f dfb cs ds =
  let -- FIXME: can we avoid this step in some ways?
      (dbs1, cs') = mapTrUnchanged (dfb True mempty) cs
      (dbs2, cs'') = iterTr (mapTrChanged f (dfb False . pure)) ds cs'
  in (dbs1 <> dbs2, cs'')

sequenceDelta :: Seq (Delta a) -> Delta (S a)
sequenceDelta s =
  mconcat $ zipWith (fmap . SRep) [0..] (Data.Foldable.toList s)

mapTrUnchanged ::
  (c -> (Delta b, c))
  -> Seq.Seq c -> (Delta (S b), Seq.Seq c)
mapTrUnchanged unchanged cs =
  let (dbs, cs') = Seq.unzip $ fmap unchanged cs
  in (sequenceDelta dbs, cs')

mapTrChanged ::
  (a -> (b, c))
  -> (AtomicDelta a -> c -> (Delta b, c))
  -> AtomicDelta (S a) -> Seq c -> (Delta (S b), Seq c)
mapTrChanged f _adf (SIns i (S as)) cs     =
  let (bs, cs') = Seq.unzip $ fmap f as
  in (injMonoid (SIns i (S bs)), insSeq i cs' cs)
mapTrChanged _ _adf (SDel i n) cs     =
  let cs' = delSeq i n cs
  in (injMonoid (SDel i n), cs')
mapTrChanged _ adf (SRep i da) cs    =
  let ci = Seq.index cs i
      (db, ci') = adf da ci
  in (fmap (SRep i) db, Seq.update i ci' cs)
mapTrChanged _ _adf (SRearr i n j) cs =
  let cs' = rearrSeq i n j cs
  in (injMonoid (SRearr i n j), cs')
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
-- type MapC s cs1 cs2 =
--     cs1
-- --    @+ 'NE ('NEOne (Seq.Seq (Conn Identity cs2)))
--     @+ 'NE ('NEOne (Seq (EncCS cs2)))
--     @+ UnFlatten s

type MapC' s cs =
   'NE ('NEOne (Seq (EncCS cs)))
    @+ UnFlatten s

instance MapAPI IFqT where
  mapAPI = cMapT'

cMapT' :: forall s a b. Diff a => IFqT (a ': s) b -> IFqT (S a ': s) (S b)
cMapT' (IFqT (ECons _ tenv) (sh :: Conn Proxy cs) f tr) =
  IFqT (ECons Proxy tenv) sh' f' tr'
  where
    sh' :: Conn Proxy (MapC' s cs)
    sh' = joinConn shA (convertEnv tenv)

    shA :: Conn Proxy ('NE ('NEOne (Seq (EncCS cs))))
    shA = CNE (COne Proxy)

    f' ::
      Env PackedCode (S a ': s)
      -> CodeC (Code (S b), Conn PackedCode (MapC' s cs))
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
      Env PackedCodeDelta (S a ': s) -> Conn PackedCode (MapC' s cs)
      -> CodeC (Code (Delta (S b)), Conn PackedCode (MapC' s cs))
    tr' (ECons (PackedCodeDelta das) denv) conn | (CNE (COne (PackedCode cs)), cenv) <- decompConn (isNone shA) (isNone $ convertEnv tenv) conn = do
      let env = unconvertEnv tenv cenv
      -- FIXME: potential source of slow down.
      env' <- mkLetEnv $ zipWithEnv (\(PackedCode a) (PackedCodeDelta da) -> PackedCode [|| $$a /+ $$da ||]) env denv
      (dbs, cs') <- CodeC $ \k -> [||
          let fElem  = $$(h env')
              trElem = $$(trh denv sh)
              (dbs, cs2') = mapTr fElem trElem $$cs $$das
          in $$(k ([|| dbs ||], [|| cs2' ||]))
        ||]
      return ([|| $$dbs ||], joinConn (CNE $ COne $ PackedCode cs') (convertEnv env'))

-- cMapT :: forall s a b. Diff a => IFqT s (S a) -> IFqT (a ': s) b -> IFqT s (S b)
-- cMapT (IFqT tenv (sh1 :: Conn Proxy cs1) f1 tr1)
--      (IFqT _    (sh2 :: Conn Proxy cs2) f2 tr2) =
--       IFqT @s @(S b) @(MapC s cs1 cs2) tenv sh f tr
--        -- IFqT @s @(S b) @(Join cs1 ('NE ('NEOne (Seq.Seq (Conn Identity cs2))))) sh f tr
--   where
--     sh :: Conn Proxy (MapC s cs1 cs2)
--     sh = joinConn sh1 shMap

--     shMap :: Conn Proxy ('NE ('NEOne (Seq.Seq (EncCS cs2))) @+ UnFlatten s)
--     shMap = joinConn shA (convertEnv tenv)

--     shA :: Conn Proxy ('NE ('NEOne (Seq.Seq (EncCS cs2))))
--     shA = CNE (COne Proxy)


-- --     f :: Env PackedCode s -> CodeC (Code (S b), Conn PackedCode (Join cs1 ('NE ('NEOne (Seq.Seq (Conn Identity cs2))))))
--     f :: Env PackedCode s
--          -> CodeC
--               (Code (S b), Conn PackedCode (MapC s cs1 cs2))
--     f env = do
--       (as, c)  <- f1 env
--       (bs, cs) <- CodeC $ \k -> [||
--           let (bs, cs) = Seq.unzip $ fmap $$(h env) (unS $$as)
--           in $$(k ([|| S bs ||], CNE $ COne $ PackedCode [|| cs ||]))
--         ||]
--       return (bs, joinConn c (joinConn cs (convertEnv env)))

--     h :: Env PackedCode s -> Code (a -> (b, EncCS cs2))
--     h env = [||
--         \a -> $$( runCodeC (f2 (ECons (PackedCode [|| a ||]) env)) $ \(b, c') -> [|| ($$b, $$(conn2cenv c')) ||])
--       ||]

--     trh :: Env PackedCodeDelta s -> Conn Proxy cs2 -> Code (Bool -> Delta a -> EncCS cs2 -> (Delta b, EncCS cs2))
--     trh env pcs = [|| \b da c ->
--       $$(cenv2conn pcs [|| c ||] $ \cs ->
--         let env' = mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) env
--         in runCodeC (tr2 (ECons (PackedCodeDelta [|| da ||]) env') cs) $ \(db, cs') ->
--           [|| ($$db, $$(conn2cenv cs') ) ||])
--       ||]

--     -- trh :: Env PackedCodeDelta s -> Conn Proxy cs2 -> Code (Delta a -> Conn Identity cs2 -> (Delta b , Conn Identity cs2))
--     -- trh env pcs = [|| \da c ->
--     --     $$(code2conn pcs [|| c ||] $ \cs ->
--     --       runCodeC (tr2 (ECons (PackedCodeDelta [|| da ||]) env) cs) $ \(db, cs') ->
--     --         [|| ($$db, $$(conn2code cs')) ||])
--     --   ||]


--     -- procUnchanged ::
--     --   Env PackedCodeDelta s -> Conn Proxy cs2
--     --     -> Code (Conn Identity cs2 -> (Delta b, Conn Identity cs2))
--     -- procUnchanged denv pcs = [|| \c ->
--     --       $$(code2conn pcs [|| c ||] $ \cs ->
--     --         runCodeC (tr2 (IndexS denv) cs) $ \(db, cs') ->
--     --           [|| ($$db, $$(conn2code cs')) ||])
--     --   ||]

--     -- procChanged ::
--     --   Index PackedCodeAtomicDelta s -> Conn Proxy cs2
--     --   -> Code (AtomicDelta a -> Conn Identity cs2 -> (Delta b, Conn Identity cs2))
--     -- procChanged denv pcs = [|| \da c ->
--     --   $$(code2conn pcs [|| c ||] $ \cs -> toCode $ do
--     --     (db1, cs1) <- tr2 (IndexS denv) cs
--     --     (db2, cs2) <- tr2 (IndexZ (PackedCodeAtomicDelta [|| da ||])) cs1
--     --     return [|| ($$db1 <> $$db2, $$(conn2code cs2)) ||])
--     --   ||]

--     -- procChangedAfterEnvChange ::
--     --   Conn Proxy cs2
--     --   -> Code (AtomicDelta a -> Conn Identity cs2 -> (Delta b, Conn Identity cs2))
--     -- procChangedAfterEnvChange pcs = [|| \da c ->
--     --     $$(code2conn pcs [|| c ||] $ \cs -> toCode $ do
--     --       (db, cs') <- tr2 (IndexZ (PackedCodeAtomicDelta [|| da ||])) cs
--     --       return [|| ($$db, $$(conn2code cs')) ||])
--     --   ||]

--     -- procUpdate ::
--     --   Conn Proxy cs2
--     --   -> Index PackedCodeAtomicDelta s
--     --   -> Code (Maybe (AtomicDelta a) -> Conn Identity cs2 -> (Delta b, Conn Identity cs2))
--     -- procUpdate pcs denv = [|| \mda c ->
--     --   let delta = case mda of { Just da ->
--     --   $$(code2conn pcs [|| c ||] $ \cs -> toCode $ do
--     --     (db, cs') <- iterTrC pcs tr2 (


--     tr :: Env PackedCodeDelta s
--          -> Conn PackedCode (MapC s cs1 cs2)
--          -> CodeC
--               (Code (Delta (S b)), Conn PackedCode (MapC s cs1 cs2))
--     tr denv conn | (c1, c23) <- decompConn (isNone sh1) (isNone shMap) conn, (c2, c3) <- decompConn (isNone shA) (isNone $ convertEnv tenv) c23 =
--       case c2 of
--         CNE (COne (PackedCode cs2)) -> do
--           let env = unconvertEnv tenv c3

--           -- FIXME: This is a source of potential slow down.
--           env' <- mkLetEnv $ zipWithEnv (\(PackedCode a) (PackedCodeDelta da) -> PackedCode [|| $$a /+ $$da ||]) env denv

--           (das, c1') <- tr1 denv c1
--           (dbs, cs2') <- CodeC $ \k -> [||
--               let fElem  = $$(h env')
--                   trElem = $$(trh denv sh2)
--                   (dbs, cs2') = mapTr fElem trElem $$cs2 $$das
--               in $$(k ([|| dbs ||], [|| cs2' ||]))
--             ||]



--           -- FIXME: potential source of slow down.
--           return ([|| $$dbs ||], joinConn c1' (joinConn (CNE $ COne $ PackedCode cs2') (convertEnv env')))

mkLetEnv :: Env PackedCode aa -> CodeC (Env PackedCode aa)
mkLetEnv = mapEnvA (\(PackedCode c) -> PackedCode <$> mkLet c)

mkLetEnvD :: Env PackedCodeDelta aa -> CodeC (Env PackedCodeDelta aa)
mkLetEnvD = mapEnvA (\(PackedCodeDelta c) -> PackedCodeDelta <$> mkLet c)

-- type MapCE a cs1 cs2 =
--     cs1
-- --    @+ 'NE ('NEOne (Seq.Seq (Conn Identity cs2)))
--     @+ 'NE ('NEOne (Seq (a, EncCS cs2)))

type MapCE' a cs = 'NE ('NEOne (Seq (a, EncCS cs)))

trackInputInC :: (a -> (b, c)) -> (a -> (b, (a, c)))
trackInputInC f a = let (b, c) = f a in (b, (a, c))

instance MapAPI IFqTE where
  mapAPI = cMapTE'

cMapTE' ::
  forall s a b.
  Diff a => IFqTE (a ': s) b -> IFqTE (S a ': s) (S b)
cMapTE' (IFqTE (ECons _ tenv) (sh :: Conn Proxy cs) f tr)
  = IFqTE (ECons Proxy tenv) sh' f' tr'
  where
    sh' :: Conn Proxy (MapCE' a cs)
    sh' = CNE (COne Proxy)

    f' ::
      Env PackedCode (S a ': s)
      -> CodeC (Code (S b), Conn PackedCode (MapCE' a cs))
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
      Env PackedCode (S a ': s) -> Env PackedCodeDelta (S a ': s) -> Conn PackedCode (MapCE' a cs)
      -> CodeC (Code (Delta (S b)), Conn PackedCode (MapCE' a cs))
    tr' (ECons _ env) (ECons (PackedCodeDelta das) denv) (CNE (COne (PackedCode cs))) = do
      (dbs, cs') <- CodeC $ \k -> [||
          let fElem  = trackInputInC $$(h env)
              trElem = $$(trh env denv sh)
              (dbs, cs2') = mapTr fElem trElem $$cs $$das
          in $$(k ([|| dbs ||], [|| cs2' ||]))
        ||]
      return ([|| $$dbs ||], CNE $ COne $ PackedCode cs')

-- cMapTE :: forall s a b. Diff a => IFqTE s (S a) -> IFqTE (a ': s) b -> IFqTE s (S b)
-- cMapTE (IFqTE tenv (sh1 :: Conn Proxy cs1) f1 tr1)
--       (IFqTE _    (sh2 :: Conn Proxy cs2) f2 tr2) =
--     IFqTE @s @(S b) @(MapCE a cs1 cs2) tenv sh f tr
--   where
--     sh :: Conn Proxy (MapCE a cs1 cs2)
--     sh = joinConn sh1 shMap

--     shMap :: Conn Proxy ('NE ('NEOne (Seq (a, EncCS cs2))))
--     shMap = CNE (COne (Proxy @(Seq (a, EncCS cs2))))

--     h :: Env PackedCode s -> Code (a -> (b, EncCS cs2))
--     h env = [||
--         \a -> $$( runCodeC (f2 (ECons (PackedCode [|| a ||]) env)) $ \(b, c') -> [|| ($$b, $$(conn2cenv c')) ||])
--       ||]

--     f ::
--       Env PackedCode s
--       -> CodeC (Code (S b), Conn PackedCode (MapCE a cs1 cs2))
--     f env = do
--       (as, c)  <- f1 env
--       (bs, cs) <- CodeC $ \k -> [||
--           let (bs, cs) = Seq.unzip $ fmap (trackInputInC $$(h env)) (unS $$as)
--           in $$(k ([|| S bs ||], CNE $ COne $ PackedCode [|| cs ||]))
--         ||]
--       return (bs, joinConn c cs)

--     trh :: Env PackedCode s -> Env PackedCodeDelta s -> Conn Proxy cs2 -> Code (Bool -> Delta a -> (a, EncCS cs2) -> (Delta b, (a, EncCS cs2)))
--     trh env denv pcs = [|| \b da (a, c) ->
--       $$(cenv2conn pcs [|| c ||] $ \cs ->
--         let denv' = mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) denv
--         in runCodeC (tr2 (ECons (PackedCode [|| a ||]) env) (ECons (PackedCodeDelta [|| da ||]) denv') cs) $ \(db, cs') ->
--           [|| ($$db, (a /+ da, $$(conn2cenv cs') )) ||])
--       ||]

--     tr :: Env PackedCode s -> Env PackedCodeDelta s
--          -> Conn PackedCode (MapCE a cs1 cs2)
--          -> CodeC (Code (Delta (S b)), Conn PackedCode (MapCE a cs1 cs2))
--     tr env denv conn | (c1, c2) <- decompConn (isNone sh1) (isNone shMap) conn =
--       case c2 of
--         CNE (COne (PackedCode cs2)) -> do
--           -- FIXME: This is a source of potential slow down.
--           env' <- mkLetEnv $ zipWithEnv (\(PackedCode a) (PackedCodeDelta da) -> PackedCode [|| $$a /+ $$da ||]) env denv

--           (das, c1') <- tr1 env denv c1
--           (dbs, cs2') <- CodeC $ \k -> [||
--               let fElem  = trackInputInC $$(h env')
--                   trElem = $$(trh env denv sh2)
--                   (dbs, cs2') = mapTr fElem trElem $$cs2 $$das
--               in $$(k ([|| dbs ||], [|| cs2' ||]))
--             ||]

--           -- FIXME: potential source of slow down.
--           return ([|| $$dbs ||], joinConn c1' (CNE $ COne $ PackedCode cs2'))

mkMapInt ::
  forall s a b.
  Diff a =>
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
unpackEnv ENil _ k = k ENil
unpackEnv (ECons _ s) c k =
  [|| let (Identity a, as) = headTailEnv $$c
      in $$(unpackEnv s [|| as ||] (k . ECons (PackedCode [|| a ||]))) ||]

instance MapAPI IFFT where
  mapAPI = cMapF

cMapF :: forall s a b. Diff a => IFFT (a ': s) b -> IFFT (S a ': s) (S b)
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
    -- h' :: Env PackedCode s -> Code (a -> (b, Interaction (Env PackedDelta (a ': s)) (Delta b)))
    -- h' env = [|| \a -> $$(runCodeC (h $ ECons (PackedCode [|| a ||]) env) $ \(b, i) -> [|| ($$b, $$i) ||]) ||]

    trh :: Code (Env PackedDelta s -> Bool -> Delta a -> Interaction (Env PackedDelta (a ': s)) (Delta b) -> (Delta b, Interaction (Env PackedDelta (a ': s)) (Delta b)))
    trh = [|| \denv doesUpdateEnv da i ->
                      let denv' = if doesUpdateEnv then denv else mapEnv (\(PackedDelta _) -> PackedDelta mempty) denv
                      in runInteraction i (ECons (PackedDelta da) denv') ||]


mapF :: forall cat term e a b. (MapAPI term, LetTerm cat term, App2 cat term e, K cat ~ Diff, Diff a, Diff b) => (e a -> e b) -> e (S a) -> e (S b)
mapF = flip (liftSO2 (Proxy @'[ '[], '[a] ]) $ \e1 e2 -> letTerm e1 (mapAPI e2))


fstF :: (IncrementalizedQ c, App2 c t e, K c ~ Diff, Diff a, Diff b) => e (a, b) -> e a
fstF = lift $ fromStateless (\a -> [|| fst $$a ||]) (\dz -> [|| iterTrStateless fstDeltaA $$dz||])

sndF :: (IncrementalizedQ c, App2 c t e, K c ~ Diff, Diff a, Diff b) => e (a, b) -> e b
sndF = lift $ fromStateless (\a -> [|| snd $$a ||]) (\dz -> [|| iterTrStateless sndDeltaA $$dz ||])



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

type MapCEU' a us cs = 'NE ('NEOne (Seq (PairIfUsed a us cs)))

instance MapAPI IFqTEU where
  mapAPI = cMapTEU'

cMapTEU' :: forall s a b. Diff a => IFqTEU (a ': s) b -> IFqTEU (S a ': s) (S b)
cMapTEU' (IFqTEU (ECons _ tenv) (sh ::Conn Proxy cs) (u :: Env SBool f_us) f (ut :: Env SBool tr_us) tr)
  = IFqTEU (ECons Proxy tenv) sh' u' f' ut' tr'
  where
    sh' :: Conn Proxy (MapCEU' a tr_us cs)
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
      -> CodeC (Code (S b), Conn PackedCode (MapCEU' a tr_us cs))
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

    tr' ::
      Env PackedCode (Extr s (MergeUses (SafeTail f_us) (SafeTail tr_us)))
      -> Env PackedCodeDelta (S a : Extr s (SafeTail f_us))
      -> Conn PackedCode (MapCEU' a tr_us cs)
      -> CodeC (Code (Delta (S b)),
                Conn PackedCode (MapCEU' a tr_us cs))
    tr' env (ECons (PackedCodeDelta das) denv) (CNE (COne (PackedCode c))) = do
      let fenv = rearrEnv extF env
      let trenv = rearrEnv extT env
      -- FIXME: We need not use mapTrUnchanged (called from mapTr) if
      -- tail' u is empty.
      (dbs, c' :: Code (Seq (PairIfUsed a tr_us cs))) <- CodeC $ \k -> [||
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
            $$(cenv2conn pcs [|| c ||] $ \cs ->
              let denv' = mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) denv
              in runCodeC (tr trenv (extendEnv tenv u (PackedCodeDelta [|| da ||]) denv') cs) $ \(db, cs') -> [|| ($$db, $$(conn2cenv cs')) ||]) ||]
      ECons STrue _ ->
          [|| \b da (a, c) ->
            $$(cenv2conn pcs [|| c ||] $ \cs ->
              let denv' = mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) denv
              in runCodeC (tr (extendEnv tenv ut (PackedCode [|| a ||]) trenv) (extendEnv tenv u (PackedCodeDelta [|| da ||]) denv') cs) $ \(db, cs') ->
                [|| ($$db, (a /+ da, $$(conn2cenv cs') )) ||])
          ||]




-- cMapTEU :: forall s a b. (Diff a, Diff b, AllIn s Diff) => IFqTEU s (S a) -> IFqTEU (a ': s) b -> IFqTEU s (S b)
-- cMapTEU e1 e2 =
--   letTerm e1 (cMapTEU' e2)


-- To avoid errors caused by "stack repl"
newtype MyInt = MyInt { unMyInt :: Int }
  deriving newtype (Read, Show, Num, Enum, Real, Integral, Eq, Ord)

newtype instance AtomicDelta MyInt = ADInt (Sum Int) deriving Show

instance Diff MyInt where
  applyAtomicDelta a (coerce -> getSum -> n) = a + n


type TestCodeType =
  Code
    ((S MyInt, S MyInt)
    -> (S (MyInt, MyInt),
        Interaction (Delta (S MyInt, S MyInt)) (Delta (S (MyInt, MyInt)))))


testCode :: (K cat ~ Diff, MapAPI term, LetTerm cat term, Prod cat MyInt MyInt ~ (MyInt, MyInt), IncrementalizedQ cat, Term cat term) => Proxy term -> TestCodeType
testCode proxy = compile $ runMonoWith proxy $ \xs -> cartesian (fstF xs) (sndF xs)


-- >>> let f = $$( testCode $ Proxy @IFqTEU )
-- >>> let (res, tr) = f (S $ Seq.fromList [1,2,3], S $ Seq.fromList [10, 20, 30])
-- >>> res
-- >>> let (dr1, tr1) = runInteraction tr $ monoidFromList [ADFst $ SIns 3 (S $ Seq.fromList [4])]
-- >>> dr1
-- >>> let (dr2, tr2) = runInteraction tr $ monoidFromList [ADFst $ SDel 0 1]
-- >>> dr2
-- >>> let (dr3, tr3) = runInteraction tr $ monoidFromList [ADSnd $ SIns 3 (S $ Seq.fromList [40])]
-- >>> dr3
-- >>> let (dr4, tr4) = runInteraction tr $ monoidFromList [ADSnd $ SDel 0 1]
-- >>> dr4
-- S {unS = fromList [(1,10),(1,20),(1,30),(2,10),(2,20),(2,30),(3,10),(3,20),(3,30)]}
-- monoidFromList [SIns 9 (S {unS = fromList [(4,10),(4,20),(4,30)]})]
-- monoidFromList [SDel 0 3]
-- monoidFromList [SIns 3 (S {unS = fromList [(1,40)]}),SIns 7 (S {unS = fromList [(2,40)]}),SIns 11 (S {unS = fromList [(3,40)]})]
-- monoidFromList [SDel 0 1,SDel 2 1,SDel 4 1]


