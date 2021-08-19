{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE ViewPatterns              #-}

module Examples.Sequence where

import           Data.Coerce           (coerce)
import           Data.Maybe            (fromJust)
import qualified Data.Sequence         as Seq
import           EILC
import           Language.Unembedding

import           Data.Env
import qualified Data.Foldable         (toList)
import           Data.Functor.Identity (Identity (Identity, runIdentity))
import           Data.List             (uncons)
import           Data.Monoid           (Sum (getSum))
import           Data.Sequence         (Seq)
import           Data.Typeable         (Proxy (Proxy))
import           Debug.Trace           (trace)

newtype S a = S { unS :: Seq.Seq a }
  deriving Show

-- Taken from https://github.com/yurug/cts
data instance AtomicDelta (S a)
 = SIns Int (S a) -- ^ SIns i s inserts s at the ith position
 | SDel Int Int   -- ^ SDel i n deletes n elements from the ith position in a sequence
 | SRep Int (AtomicDelta a) -- ^ SRep i da applies the delta da to the ith element.
 | SRearr Int Int Int -- ^ SRearr i n j cuts n elements from the ith position and insert the cut sequence into the jth position (after cuting).

deriving instance (Show (AtomicDelta a), Show a) => Show (AtomicDelta (S a))

type DeltaS a = AtomicDelta (S a)


instance Diff a => Diff (S a) where
    applyAtomicDelta (S s0) ds = S (ad s0 ds)
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

delSeq :: Int -> Int -> Seq.Seq a -> Seq.Seq a
delSeq i n s0 =
    let (s1, stemp) = Seq.splitAt i s0
        s2 = Seq.drop n stemp
    in s1 Seq.>< s2

repSeq :: Diff a => Int -> AtomicDelta a -> Seq.Seq a -> Seq.Seq a
repSeq i da = Seq.adjust' (`applyAtomicDelta` da) i

rearrSeq :: Int -> Int -> Int -> Seq.Seq a -> Seq.Seq a
rearrSeq i n j s0 =
    let (s1, s23) = Seq.splitAt i s0
        (s2, s3)  = Seq.splitAt n s23
    in insSeq j s2 (s1 Seq.>< s3)


-- APIs
dsingleton :: AtomicDelta a -> Delta (S a)
dsingleton da = [coerce $ SRep 0 da]

singletonF :: (App2 IFqA IFqAT e, Diff a) => e a -> e (S a)
singletonF = lift singletonC
  where
    singletonC =
      ifqAFromStatelessA (\a -> [|| S (Seq.singleton $$a) ||])
                         (\da -> [|| dsingleton $$da ||])

dempty :: Delta (S a)
dempty = []

emptyF :: (App2 IFqA IFqAT e, Diff a) => e (S a)
emptyF = lift emptyC unit
  where
    emptyC = ifqAFromStatelessA (const [|| S Seq.empty ||]) (const [|| dempty ||])

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
  in ([SIns toI (concatSeq s')], insAtC i (s2c s') c)
trConcatCAtomic (SDel i n) c =
  let (c1, c23) = Seq.splitAt i c
      (c2, c3)  = Seq.splitAt n c23
      toI       = sum c1
      toN       = sum c2
  in ([SDel toI toN], c1 Seq.>< c3)
trConcatCAtomic (SRearr i n j) c =
  let (c1, c23) = Seq.splitAt i c
      (c2, c3)  = Seq.splitAt n c23
      toI       = sum c1
      toN       = sum c2
      c13       = c1 Seq.>< c3
      toJ       = sum $ Seq.take j c13
  in ([SRearr toI toN toJ], insAtC j c2 c13 )
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

    goAtomic :: Int -> DeltaS a -> Int -> ([DeltaS a], Int)
    goAtomic offset (SIns j as) ci =
      ([SIns (offset + j) as], ci + Seq.length (unS as))
    goAtomic offset (SDel j n) ci =
      let -- adjust n to satisfy the invaliant n + j <= ci
          n' = n + (if j + n > ci then ci - (j + n) else 0)
      in ([SDel (offset + j) n'], ci - n')
    goAtomic offset (SRep j da) ci =
      ([SRep (offset + j) da], ci)
    goAtomic offset (SRearr j n k) ci =
      ([SRearr (offset + j) n (offset + k)], ci)

concatF :: (App2 IFqA IFqAT e, Diff a) => e (S (S a)) -> e (S a)
concatF = lift $ ifqAFromFunctionsA [|| concatC ||] [|| trConcatCAtomic ||]



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


type family Flatten cs where
  Flatten 'None   = '[]
  Flatten ('NE x) = Flatten' x '[]

type family Flatten' cs r where
  Flatten' ('NEOne c) r = c ': r
  Flatten' ('NEJoin cs1 cs2) r = Flatten' cs1 (Flatten' cs2 r)

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

sequenceDelta :: Seq (Delta a) -> Delta (S a)
sequenceDelta s =
  concat $ zipWith (\i -> map (SRep i)) [0..] (Data.Foldable.toList s)

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
  in ([SIns i (S bs)], insSeq i cs' cs)
mapTrChanged _ _adf (SDel i n) cs     =
  let cs' = delSeq i n cs
  in ([SDel i n], cs')
mapTrChanged _ adf (SRep i da) cs    =
  let ci = Seq.index cs i
      (db, ci') = adf da ci
  in (map (SRep i) db, Seq.update i ci' cs)
mapTrChanged _ _adf (SRearr i n j) cs =
  let cs' = rearrSeq i n j cs
  in ([SRearr i n j], cs')
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


type MapC s cs1 cs2 =
    cs1
    @+ 'NE ('NEOne (Seq.Seq (Conn Identity cs2)))
    @+ UnFlatten s

mapT :: forall s a b. Diff a => IFqAT s (S a) -> IFqAT (a ': s) b -> IFqAT s (S b)
mapT (IFqAT tenv (sh1 :: Conn Proxy cs1) f1 tr1)
     (IFqAT _    (sh2 :: Conn Proxy cs2) f2 tr2) =
      IFqAT @s @(S b) @(MapC s cs1 cs2) tenv sh f tr
       -- IFqT @s @(S b) @(Join cs1 ('NE ('NEOne (Seq.Seq (Conn Identity cs2))))) sh f tr
  where
    sh :: Conn Proxy (MapC s cs1 cs2)
    sh = joinConn sh1 shMap

    shMap :: Conn Proxy ('NE ('NEOne (Seq.Seq (Conn Identity cs2))) @+ UnFlatten s)
    shMap = joinConn shA (convertEnv tenv)

    shA :: Conn Proxy ('NE ('NEOne (Seq.Seq (Conn Identity cs2))))
    shA = CNE (COne Proxy)


--     f :: Env PackedCode s -> CodeC (Code (S b), Conn PackedCode (Join cs1 ('NE ('NEOne (Seq.Seq (Conn Identity cs2))))))
    f :: Env PackedCode s
         -> CodeC
              (Code (S b), Conn PackedCode (MapC s cs1 cs2))
    f env = do
      (as, c)  <- f1 env
      (bs, cs) <- CodeC $ \k -> [||
          let (bs, cs) = Seq.unzip $ fmap $$(h env) (unS $$as)
          in $$(k ([|| S bs ||], CNE $ COne $ PackedCode [|| cs ||]))
        ||]
      return (bs, joinConn c (joinConn cs (convertEnv env)))

    h :: Env PackedCode s -> Code (a -> (b, Conn Identity cs2))
    h env = [||
        \a -> $$( runCodeC (f2 (ECons (PackedCode [|| a ||]) env)) $ \(b, c') -> [|| ($$b, $$(conn2code c')) ||])
      ||]

    -- trh :: Env PackedCodeDelta s -> Conn Proxy cs2 -> Code (Delta a -> Conn Identity cs2 -> (Delta b , Conn Identity cs2))
    -- trh env pcs = [|| \da c ->
    --     $$(code2conn pcs [|| c ||] $ \cs ->
    --       runCodeC (tr2 (ECons (PackedCodeDelta [|| da ||]) env) cs) $ \(db, cs') ->
    --         [|| ($$db, $$(conn2code cs')) ||])
    --   ||]

    -- mkLetEnv = mapEnvA (\(PackedCode c) -> do { v <- mkLet c ; pure (PackedCode v) })

    procUnchanged ::
      Index PackedCodeAtomicDelta s -> Conn Proxy cs2
        -> Code (Conn Identity cs2 -> (Delta b, Conn Identity cs2))
    procUnchanged denv pcs = [|| \c ->
          $$(code2conn pcs [|| c ||] $ \cs ->
            runCodeC (tr2 (IndexS denv) cs) $ \(db, cs') ->
              [|| ($$db, $$(conn2code cs')) ||])
      ||]

    -- procChanged ::
    --   Index PackedCodeAtomicDelta s -> Conn Proxy cs2
    --   -> Code (AtomicDelta a -> Conn Identity cs2 -> (Delta b, Conn Identity cs2))
    -- procChanged denv pcs = [|| \da c ->
    --   $$(code2conn pcs [|| c ||] $ \cs -> toCode $ do
    --     (db1, cs1) <- tr2 (IndexS denv) cs
    --     (db2, cs2) <- tr2 (IndexZ (PackedCodeAtomicDelta [|| da ||])) cs1
    --     return [|| ($$db1 <> $$db2, $$(conn2code cs2)) ||])
    --   ||]

    procChangedAfterEnvChange ::
      Conn Proxy cs2
      -> Code (AtomicDelta a -> Conn Identity cs2 -> (Delta b, Conn Identity cs2))
    procChangedAfterEnvChange pcs = [|| \da c ->
        $$(code2conn pcs [|| c ||] $ \cs -> toCode $ do
          (db, cs') <- tr2 (IndexZ (PackedCodeAtomicDelta [|| da ||])) cs
          return [|| ($$db, $$(conn2code cs')) ||])
      ||]

    tr :: Index PackedCodeAtomicDelta s
         -> Conn PackedCode (MapC s cs1 cs2)
         -> CodeC
              (Code (Delta (S b)), Conn PackedCode (MapC s cs1 cs2))
    tr denv conn | (c1, c23) <- decompConn (isNone sh1) (isNone shMap) conn, (c2, c3) <- decompConn (isNone shA) (isNone $ convertEnv tenv) c23 =
      case c2 of
        CNE (COne (PackedCode cs2)) -> do
          let env = unconvertEnv tenv c3
          -- mkLetEnv $
          --            zipWithEnv (\(PackedCode a) (PackedCodeDelta da) -> PackedCode [|| $$a /+ $$da ||]) env denv

          -- First compute the effect of denv
          env' <- mkUpdateEnv denv env
          (dbs1, cs2')  <- CodeC $ \k -> [|| let (dbs, cs2') = mapTrUnchanged $$(procUnchanged denv sh2) $$cs2 in $$(k ([|| dbs ||], [|| cs2' ||])) ||]
          (das, c1') <- tr1 denv c1

          -- Then, compute the effect of das
          (dbs2, cs2'') <- CodeC $ \k -> [|| let (dbs, cs2'') = iterTr (mapTrChanged $$(h env') $$(procChangedAfterEnvChange sh2)) $$das $$cs2' in $$(k ([|| dbs ||], [|| cs2'' ||]) ) ||]
--          (dbs, cs2' :: Code (Seq.Seq (Conn Identity cs2, a))) <- CodeC $ \k -> [|| let (dbs, cs2') = mapTr $$(h env') $$(trh denv sh2) $$cs2 $$das in $$(k ([|| dbs ||], [|| cs2' ||])) ||]
--          (dbs, cs2') <- CodeC $ \k -> [|| let (dbs, cs2') = mapTr $$(h env') $$(procUnchanged denv sh2) $$(procChanged denv sh2) $$cs2 $$das in $$(k ([|| dbs ||], [|| cs2' ||])) ||]
          -- FIXME: potential source of slow down.
          return ([|| $$dbs1 <> $$dbs2 ||], joinConn c1' (joinConn (CNE $ COne $ PackedCode cs2'') (convertEnv env')))

mapF :: forall e a b. (App2 IFqA IFqAT e, Diff a) => (e a -> e b) -> e (S a) -> e (S b)
mapF = flip (liftSO2 (Proxy @'[ '[], '[a] ]) mapT)

fstF :: (App2 IFqA IFqAT e, Diff a, Diff b) => e (a, b) -> e a
fstF = lift $ ifqAFromStatelessA (\a -> [|| fst $$a ||]) (\dz -> [|| case $$dz of { ADFst da -> [da] ; _ -> mempty } ||])

sndF :: (App2 IFqA IFqAT e, Diff a, Diff b) => e (a, b) -> e b
sndF = lift $ ifqAFromStatelessA (\a -> [|| snd $$a ||]) (\dz -> [|| case $$dz of { ADSnd db -> [db] ; _ -> mempty } ||])



cartesian :: (App2 IFqA IFqAT e, Diff a, Diff b) => e (S a) -> e (S b) -> e (S (a, b))
cartesian as bs =
  concatMapF (\a -> mapF (pair a) bs) as
  where
    concatMapF f x = concatF (mapF f x)

newtype instance AtomicDelta Int = ADInt (Sum Int) deriving Show

instance Diff Int where
  applyAtomicDelta a (coerce -> getSum -> n) = a + n


testCode ::
  Code
    ((S Int, S Int)
    -> (S (Int, Int),
        Interaction (Delta (S Int, S Int)) (Delta (S (Int, Int)))))
testCode = runIFqA $ runMono $ \xs -> cartesian (fstF xs) (sndF xs)


-- >>> let f = $$( testCode )
-- >>> let (res, tr) = f (S $ Seq.fromList [1,2,3], S $ Seq.fromList [10, 20, 30])
-- >>> res
-- >>> let (dr1, tr1) = runInteraction tr [ADFst $ SIns 3 (S $ Seq.fromList [4])]
-- >>> dr1
-- >>> let (dr2, tr2) = runInteraction tr [ADFst $ SDel 0 1]
-- >>> dr2
-- >>> let (dr3, tr3) = runInteraction tr [ADSnd $ SIns 3 (S $ Seq.fromList [40])]
-- >>> dr3
-- >>> let (dr4, tr4) = runInteraction tr [ADSnd $ SDel 0 1]
-- >>> dr4
-- S {unS = fromList [(1,10),(1,20),(1,30),(2,10),(2,20),(2,30),(3,10),(3,20),(3,30)]}
-- [SIns 9 (S {unS = fromList [(4,10),(4,20),(4,30)]})]
-- [SDel 0 3]
-- [SIns 3 (S {unS = fromList [(1,40)]}),SIns 7 (S {unS = fromList [(2,40)]}),SIns 11 (S {unS = fromList [(3,40)]})]
-- [SDel 0 1,SDel 2 1,SDel 4 1]
