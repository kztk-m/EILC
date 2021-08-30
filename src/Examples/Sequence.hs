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

import           Prelude               hiding ((.))

import           Data.Coerce           (coerce)
import           Data.Maybe            (fromJust)
import qualified Data.Sequence         as Seq
import           EILC
import           Language.Unembedding

import           Data.Env
import qualified Data.Foldable         (toList)
import           Data.Functor.Identity (Identity (Identity, runIdentity))
import           Data.Sequence         (Seq)
import           Data.Typeable         (Proxy (Proxy))

import           Data.Monoid

import           Data.Code
import           Data.Delta

import           Data.Incrementalized

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
dsingleton da = injMonoid $ coerce $ SRep 0 da

singletonF :: (App2 IFq t e, Diff a) => e a -> e (S a)
singletonF = lift singletonC
  where
    singletonC =
      fromStateless (\a -> [|| S (Seq.singleton $$a) ||])
                    (\da -> [|| iterTrStateless dsingleton $$da ||])
      -- ifqFromStatelessA (\a -> [|| S (Seq.singleton $$a) ||])
      --                   (\da -> [|| dsingleton $$da ||])

dempty :: Delta (S a)
dempty = mempty

emptyF :: (App2 IFq t e, Diff a) => e (S a)
emptyF = lift emptyC unit
  where
      emptyC = fromStateless (const [|| S Seq.empty ||]) (const [|| dempty ||])
--    emptyC = ifqFromStatelessA (const [|| S Seq.empty ||]) (const [|| dempty ||])

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

concatF :: (App2 IFq t e, Diff a) => e (S (S a)) -> e (S a)
concatF = lift $ fromFunctions [|| concatC ||] [|| iterTr trConcatCAtomic ||]
  -- lift $ ifqFromFunctionsA [|| concatC ||] [|| trConcatCAtomic ||]



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
type MapC s cs1 cs2 =
    cs1
--    @+ 'NE ('NEOne (Seq.Seq (Conn Identity cs2)))
    @+ 'NE ('NEOne (Seq (EncCS cs2)))
    @+ UnFlatten s

mapT :: forall s a b. Diff a => IFqT s (S a) -> IFqT (a ': s) b -> IFqT s (S b)
mapT (IFqT tenv (sh1 :: Conn Proxy cs1) f1 tr1)
     (IFqT _    (sh2 :: Conn Proxy cs2) f2 tr2) =
      IFqT @s @(S b) @(MapC s cs1 cs2) tenv sh f tr
       -- IFqT @s @(S b) @(Join cs1 ('NE ('NEOne (Seq.Seq (Conn Identity cs2))))) sh f tr
  where
    sh :: Conn Proxy (MapC s cs1 cs2)
    sh = joinConn sh1 shMap

    shMap :: Conn Proxy ('NE ('NEOne (Seq.Seq (EncCS cs2))) @+ UnFlatten s)
    shMap = joinConn shA (convertEnv tenv)

    shA :: Conn Proxy ('NE ('NEOne (Seq.Seq (EncCS cs2))))
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

    h :: Env PackedCode s -> Code (a -> (b, EncCS cs2))
    h env = [||
        \a -> $$( runCodeC (f2 (ECons (PackedCode [|| a ||]) env)) $ \(b, c') -> [|| ($$b, $$(conn2cenv c')) ||])
      ||]

    trh :: Env PackedCodeDelta s -> Conn Proxy cs2 -> Code (Bool -> Delta a -> EncCS cs2 -> (Delta b, EncCS cs2))
    trh env pcs = [|| \b da c ->
      $$(cenv2conn pcs [|| c ||] $ \cs ->
        let env' = mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) env
        in runCodeC (tr2 (ECons (PackedCodeDelta [|| da ||]) env') cs) $ \(db, cs') ->
          [|| ($$db, $$(conn2cenv cs') ) ||])
      ||]

    -- trh :: Env PackedCodeDelta s -> Conn Proxy cs2 -> Code (Delta a -> Conn Identity cs2 -> (Delta b , Conn Identity cs2))
    -- trh env pcs = [|| \da c ->
    --     $$(code2conn pcs [|| c ||] $ \cs ->
    --       runCodeC (tr2 (ECons (PackedCodeDelta [|| da ||]) env) cs) $ \(db, cs') ->
    --         [|| ($$db, $$(conn2code cs')) ||])
    --   ||]


    -- procUnchanged ::
    --   Env PackedCodeDelta s -> Conn Proxy cs2
    --     -> Code (Conn Identity cs2 -> (Delta b, Conn Identity cs2))
    -- procUnchanged denv pcs = [|| \c ->
    --       $$(code2conn pcs [|| c ||] $ \cs ->
    --         runCodeC (tr2 (IndexS denv) cs) $ \(db, cs') ->
    --           [|| ($$db, $$(conn2code cs')) ||])
    --   ||]

    -- procChanged ::
    --   Index PackedCodeAtomicDelta s -> Conn Proxy cs2
    --   -> Code (AtomicDelta a -> Conn Identity cs2 -> (Delta b, Conn Identity cs2))
    -- procChanged denv pcs = [|| \da c ->
    --   $$(code2conn pcs [|| c ||] $ \cs -> toCode $ do
    --     (db1, cs1) <- tr2 (IndexS denv) cs
    --     (db2, cs2) <- tr2 (IndexZ (PackedCodeAtomicDelta [|| da ||])) cs1
    --     return [|| ($$db1 <> $$db2, $$(conn2code cs2)) ||])
    --   ||]

    -- procChangedAfterEnvChange ::
    --   Conn Proxy cs2
    --   -> Code (AtomicDelta a -> Conn Identity cs2 -> (Delta b, Conn Identity cs2))
    -- procChangedAfterEnvChange pcs = [|| \da c ->
    --     $$(code2conn pcs [|| c ||] $ \cs -> toCode $ do
    --       (db, cs') <- tr2 (IndexZ (PackedCodeAtomicDelta [|| da ||])) cs
    --       return [|| ($$db, $$(conn2code cs')) ||])
    --   ||]

    -- procUpdate ::
    --   Conn Proxy cs2
    --   -> Index PackedCodeAtomicDelta s
    --   -> Code (Maybe (AtomicDelta a) -> Conn Identity cs2 -> (Delta b, Conn Identity cs2))
    -- procUpdate pcs denv = [|| \mda c ->
    --   let delta = case mda of { Just da ->
    --   $$(code2conn pcs [|| c ||] $ \cs -> toCode $ do
    --     (db, cs') <- iterTrC pcs tr2 (


    tr :: Env PackedCodeDelta s
         -> Conn PackedCode (MapC s cs1 cs2)
         -> CodeC
              (Code (Delta (S b)), Conn PackedCode (MapC s cs1 cs2))
    tr denv conn | (c1, c23) <- decompConn (isNone sh1) (isNone shMap) conn, (c2, c3) <- decompConn (isNone shA) (isNone $ convertEnv tenv) c23 =
      case c2 of
        CNE (COne (PackedCode cs2)) -> do
          let env = unconvertEnv tenv c3

          -- FIXME: This is a source of potential slow down.
          env' <- mkLetEnv $ zipWithEnv (\(PackedCode a) (PackedCodeDelta da) -> PackedCode [|| $$a /+ $$da ||]) env denv

          (das, c1') <- tr1 denv c1
          (dbs, cs2') <- CodeC $ \k -> [||
              let fElem  = $$(h env')
                  trElem = $$(trh denv sh2)
                  (dbs, cs2') = mapTr fElem trElem $$cs2 $$das
              in $$(k ([|| dbs ||], [|| cs2' ||]))
            ||]



          -- FIXME: potential source of slow down.
          return ([|| $$dbs ||], joinConn c1' (joinConn (CNE $ COne $ PackedCode cs2') (convertEnv env')))

mkLetEnv :: Env PackedCode aa -> CodeC (Env PackedCode aa)
mkLetEnv = mapEnvA (\(PackedCode c) -> PackedCode <$> mkLet c)


type MapCE a cs1 cs2 =
    cs1
--    @+ 'NE ('NEOne (Seq.Seq (Conn Identity cs2)))
    @+ 'NE ('NEOne (Seq (a, EncCS cs2)))

trackInputInC :: (a -> (b, c)) -> (a -> (b, (a, c)))
trackInputInC f a = let (b, c) = f a in (b, (a, c))


mapTE :: forall s a b. Diff a => IFqTE s (S a) -> IFqTE (a ': s) b -> IFqTE s (S b)
mapTE (IFqTE tenv (sh1 :: Conn Proxy cs1) f1 tr1)
      (IFqTE _    (sh2 :: Conn Proxy cs2) f2 tr2) =
    IFqTE @s @(S b) @(MapCE a cs1 cs2) tenv sh f tr
  where
    sh :: Conn Proxy (MapCE a cs1 cs2)
    sh = joinConn sh1 shMap

    shMap :: Conn Proxy ('NE ('NEOne (Seq (a, EncCS cs2))))
    shMap = CNE (COne (Proxy @(Seq (a, EncCS cs2))))

    h :: Env PackedCode s -> Code (a -> (b, EncCS cs2))
    h env = [||
        \a -> $$( runCodeC (f2 (ECons (PackedCode [|| a ||]) env)) $ \(b, c') -> [|| ($$b, $$(conn2cenv c')) ||])
      ||]

    f ::
      Env PackedCode s
      -> CodeC (Code (S b), Conn PackedCode (MapCE a cs1 cs2))
    f env = do
      (as, c)  <- f1 env
      (bs, cs) <- CodeC $ \k -> [||
          let (bs, cs) = Seq.unzip $ fmap (trackInputInC $$(h env)) (unS $$as)
          in $$(k ([|| S bs ||], CNE $ COne $ PackedCode [|| cs ||]))
        ||]
      return (bs, joinConn c cs)

    trh :: Env PackedCode s -> Env PackedCodeDelta s -> Conn Proxy cs2 -> Code (Bool -> Delta a -> (a, EncCS cs2) -> (Delta b, (a, EncCS cs2)))
    trh env denv pcs = [|| \b da (a, c) ->
      $$(cenv2conn pcs [|| c ||] $ \cs ->
        let denv' = mapEnv (\(PackedCodeDelta cdx) -> PackedCodeDelta [|| if b then $$cdx else mempty ||]) denv
        in runCodeC (tr2 (ECons (PackedCode [|| a ||]) env) (ECons (PackedCodeDelta [|| da ||]) denv') cs) $ \(db, cs') ->
          [|| ($$db, (a /+ da, $$(conn2cenv cs') )) ||])
      ||]

    tr :: Env PackedCode s -> Env PackedCodeDelta s
         -> Conn PackedCode (MapCE a cs1 cs2)
         -> CodeC (Code (Delta (S b)), Conn PackedCode (MapCE a cs1 cs2))
    tr env denv conn | (c1, c2) <- decompConn (isNone sh1) (isNone shMap) conn =
      case c2 of
        CNE (COne (PackedCode cs2)) -> do
          -- FIXME: This is a source of potential slow down.
          env' <- mkLetEnv $ zipWithEnv (\(PackedCode a) (PackedCodeDelta da) -> PackedCode [|| $$a /+ $$da ||]) env denv

          (das, c1') <- tr1 env denv c1
          (dbs, cs2') <- CodeC $ \k -> [||
              let fElem  = trackInputInC $$(h env')
                  trElem = $$(trh env denv sh2)
                  (dbs, cs2') = mapTr fElem trElem $$cs2 $$das
              in $$(k ([|| dbs ||], [|| cs2' ||]))
            ||]

          -- FIXME: potential source of slow down.
          return ([|| $$dbs ||], joinConn c1' (CNE $ COne $ PackedCode cs2'))



mapF :: forall e a b. (App2 IFq IFqT e, Diff a) => (e a -> e b) -> e (S a) -> e (S b)
mapF = flip (liftSO2 (Proxy @'[ '[], '[a] ]) mapT)

mapFE :: forall e a b. (App2 IFq IFqTE e, Diff a) => (e a -> e b) -> e (S a) -> e (S b)
mapFE = flip (liftSO2 (Proxy @'[ '[], '[a] ]) mapTE)

fstF :: (App2 IFq t e, Diff a, Diff b) => e (a, b) -> e a
fstF = lift $ fromStateless (\a -> [|| fst $$a ||]) (\dz -> [|| iterTrStateless fstDeltaA $$dz||])

sndF :: (App2 IFq t e, Diff a, Diff b) => e (a, b) -> e b
sndF = lift $ fromStateless (\a -> [|| snd $$a ||]) (\dz -> [|| iterTrStateless sndDeltaA $$dz ||])



cartesian :: (App2 IFq IFqT e, Diff a, Diff b) => e (S a) -> e (S b) -> e (S (a, b))
cartesian as bs =
  concatMapF (\a -> mapF (pair a) bs) as
  where
    concatMapF f x = concatF (mapF f x)


cartesianE :: (App2 IFq IFqTE e, Diff a, Diff b) => e (S a) -> e (S b) -> e (S (a, b))
cartesianE as bs =
  concatMapF (\a -> mapFE (pair a) bs) as
  where
    concatMapF f x = concatF (mapFE f x)

newtype instance AtomicDelta Int = ADInt (Sum Int) deriving Show

instance Diff Int where
  applyAtomicDelta a (coerce -> getSum -> n) = a + n


testCode ::
  Code
    ((S Int, S Int)
    -> (S (Int, Int),
        Interaction (Delta (S Int, S Int)) (Delta (S (Int, Int)))))
testCode = runIFq $ runMono $ \xs -> cartesian (fstF xs) (sndF xs)


testCodeE ::
  Code
    ((S Int, S Int)
    -> (S (Int, Int),
        Interaction (Delta (S Int, S Int)) (Delta (S (Int, Int)))))
testCodeE = runIFq $ runMono $ \xs -> cartesianE (fstF xs) (sndF xs)


{-

Code obtained from testCode
-----------------------------

spliced :: (Diff a, Diff b) =>
  (S a, S b)
  -> (S (a, b), Interaction (Delta (S a, S b)) (Delta (S (a, b))))
spliced =
    ensureDiffType (\ pa_a1BI4 pb_a1BI5 a_a1BI6
            -> let v_a1BI7 = fst a_a1BI6 in
               let
                 (bs_a1BI8, cs_a1BI9)
                   = (Seq.unzip
                        $ fmap
                             (\ a_a1BIa
                                -> let v_a1BIb = snd a_a1BI6 in
                                   let
                                     (bs_a1BIc, cs_a1BId)
                                       = (Seq.unzip
                                            $ fmap
                                                 (\ a_a1BIe
                                                    -> let v_a1BIf = (a_a1BIa, a_a1BIe)
                                                       in (v_a1BIf, ENil))
                                                (unS v_a1BIb))
                                   in
                                     (S bs_a1BIc,
                                      ECons (Identity cs_a1BId)
                                        (ECons (Identity a_a1BIa)
                                           (ECons (Identity a_a1BI6) ENil))))
                            (unS v_a1BI7)) in
               let (b_a1BIg, c_a1BIh) = concatC (S bs_a1BI8)
               in
                 (b_a1BIg,
                  let
                    func_a1BIi
                      = \ a_a1BIj a_a1BIk a_a1BIl -> mkInteraction pa_a1BI4 pb_a1BI5 (\ da_a1BIm
                                               -> let v_a1BIn = (a_a1BIk /+ da_a1BIm) in
                                                  let
                                                    v_a1BIo
                                                      = iterTrStateless fstDeltaA da_a1BIm in
                                                  let
                                                    fElem_a1BIq
                                                      = \ a_a1BIt
                                                          -> let v_a1BIu = snd v_a1BIn in
                                                             let
                                                               (bs_a1BIv, cs_a1BIw)
                                                                 = (Seq.unzip
                                                                      $ fmap
                                                                           (\ a_a1BIx
                                                                              -> let
                                                                                   v_a1BIy
                                                                                     = (a_a1BIt,
                                                                                        a_a1BIx)
                                                                                 in
                                                                                   (v_a1BIy, ENil))
                                                                          (unS v_a1BIu))
                                                             in
                                                               (S bs_a1BIv,
                                                                ECons (Identity cs_a1BIw)
                                                                  (ECons (Identity a_a1BIt)
                                                                     (ECons (Identity v_a1BIn)
                                                                        ENil)))
                                                    trElem_a1BIp
                                                      = \ b_a1BIz da_a1BIA c_a1BIB
                                                          -> let
                                                               x_a1BID = headEnv c_a1BIB
                                                               xs_a1BIC = tailEnv c_a1BIB in
                                                             let
                                                               x_a1BIF = headEnv xs_a1BIC
                                                               xs_a1BIE = tailEnv xs_a1BIC in
                                                             let
                                                               x_a1BIH = headEnv xs_a1BIE
                                                               xs_a1BIG = tailEnv xs_a1BIE
                                                             in
                                                               case xs_a1BIG of {
                                                                 ENil
                                                                   -> let
                                                                        v_a1BII
                                                                          = (runIdentity x_a1BIH
                                                                               /+
                                                                                 (if b_a1BIz then
                                                                                      da_a1BIm
                                                                                  else
                                                                                      mempty)) in
                                                                      let
                                                                        v_a1BIJ
                                                                          = (runIdentity x_a1BIF
                                                                               /+ da_a1BIA) in
                                                                      let
                                                                        v_a1BIK
                                                                          = iterTrStateless
                                                                               sndDeltaA
                                                                              (if b_a1BIz then
                                                                                   da_a1BIm
                                                                               else
                                                                                   mempty) in
                                                                      let
                                                                        fElem_a1BIM
                                                                          = \ a_a1BIP
                                                                              -> let
                                                                                   v_a1BIQ
                                                                                     = (v_a1BIJ,
                                                                                        a_a1BIP)
                                                                                 in (v_a1BIQ, ENil)
                                                                        trElem_a1BIL
                                                                          = \ b_a1BIR
                                                                              da_a1BIS
                                                                              c_a1BIT
                                                                              -> case c_a1BIT of {
                                                                                   ENil
                                                                                     -> let
                                                                                          v_a1BIU
                                                                                            = pairDelta
                                                                                                 (if b_a1BIR then
                                                                                                      da_a1BIA
                                                                                                  else
                                                                                                      mempty)
                                                                                                da_a1BIS
                                                                                        in
                                                                                          (v_a1BIU,
                                                                                           ENil) }
                                                                        (dbs_a1BIN, cs2'_a1BIO)
                                                                          = mapTr fElem_a1BIM
                                                                                trElem_a1BIL
                                                                               (runIdentity
                                                                                  x_a1BID)
                                                                              v_a1BIK
                                                                      in
                                                                        (dbs_a1BIN,
                                                                         ECons
                                                                            (Identity cs2'_a1BIO)
                                                                           (ECons
                                                                               (Identity v_a1BIJ)
                                                                              (ECons
                                                                                  (Identity
                                                                                     v_a1BII)
                                                                                 ENil))) }
                                                    (dbs_a1BIr, cs2'_a1BIs)
                                                      = mapTr fElem_a1BIq trElem_a1BIp a_a1BIj
                                                          v_a1BIo in
                                                  let
                                                    (db_a1BIV, c'_a1BIW)
                                                      = iterTr trConcatCAtomic dbs_a1BIr a_a1BIl
                                                  in
                                                    (db_a1BIV,
                                                     func_a1BIi cs2'_a1BIs v_a1BIn c'_a1BIW))
                  in func_a1BIi cs_a1BI9 a_a1BI6 c_a1BIh))
-}


{-

Code obtained from testCodeE
-----------------------------

spliced2 :: (Diff a, Diff b) =>
  (S a, S b)
  -> (S (a, b), Interaction (Delta (S a, S b)) (Delta (S (a, b))))
spliced2 =
      ensureDiffType (\ pa_a1vbs pb_a1vbt a_a1vbu
            -> let v_a1vbv = fst a_a1vbu in
               let
                 (bs_a1vbw, cs_a1vbx)
                   = (Seq.unzip
                        $ fmap
                             (trackInputInC
                                (\ a_a1vby
                                   -> let v_a1vbz = snd a_a1vbu in
                                      let
                                        (bs_a1vbA, cs_a1vbB)
                                          = (Seq.unzip
                                               $ fmap
                                                    (trackInputInC
                                                       (\ a_a1vbC
                                                          -> let v_a1vbD = (a_a1vby, a_a1vbC)
                                                             in (v_a1vbD, ENil)))
                                                   (unS v_a1vbz))
                                      in (S bs_a1vbA, ECons (Identity cs_a1vbB) ENil)))
                            (unS v_a1vbv)) in
               let (b_a1vbE, c_a1vbF) = concatC (S bs_a1vbw)
               in
                 (b_a1vbE,
                  let
                    func_a1vbG
                      = \ a_a1vbH a_a1vbI a_a1vbJ -> mkInteraction pa_a1vbs pb_a1vbt (\ da_a1vbK
                                               -> let v_a1vbL = (a_a1vbH /+ da_a1vbK) in
                                                  let
                                                    v_a1vbM
                                                      = iterTrStateless fstDeltaA da_a1vbK in
                                                  let
                                                    fElem_a1vbO
                                                      = trackInputInC
                                                          (\ a_a1vbR
                                                             -> let v_a1vbS = snd v_a1vbL in
                                                                let
                                                                  (bs_a1vbT, cs_a1vbU)
                                                                    = (Seq.unzip
                                                                         $ fmap
                                                                              (trackInputInC
                                                                                 (\ a_a1vbV
                                                                                    -> let
                                                                                         v_a1vbW
                                                                                           = (a_a1vbR,
                                                                                              a_a1vbV)
                                                                                       in
                                                                                         (v_a1vbW,
                                                                                          ENil)))
                                                                             (unS v_a1vbS))
                                                                in
                                                                  (S bs_a1vbT,
                                                                   ECons (Identity cs_a1vbU)
                                                                     ENil))
                                                    trElem_a1vbN
                                                      = \ b_a1vbX da_a1vbY (a_a1vbZ, c_a1vc0)
                                                          -> let
                                                               x_a1vc2 = headEnv c_a1vc0
                                                               xs_a1vc1 = tailEnv c_a1vc0
                                                             in
                                                               case xs_a1vc1 of {
                                                                 ENil
                                                                   -> let
                                                                        v_a1vc3
                                                                          = (a_a1vbH
                                                                               /+
                                                                                 (if b_a1vbX then
                                                                                      da_a1vbK
                                                                                  else
                                                                                      mempty)) in
                                                                      let
                                                                        v_a1vc4
                                                                          = (a_a1vbZ /+ da_a1vbY) in
                                                                      let
                                                                        v_a1vc5
                                                                          = iterTrStateless
                                                                               sndDeltaA
                                                                              (if b_a1vbX then
                                                                                   da_a1vbK
                                                                               else
                                                                                   mempty) in
                                                                      let
                                                                        fElem_a1vc7
                                                                          = trackInputInC
                                                                              (\ a_a1vca
                                                                                 -> let
                                                                                      v_a1vcb
                                                                                        = (v_a1vc4,
                                                                                           a_a1vca)
                                                                                    in
                                                                                      (v_a1vcb,
                                                                                       ENil))
                                                                        trElem_a1vc6
                                                                          = \ b_a1vcc
                                                                              da_a1vcd
                                                                              (a_a1vce, c_a1vcf)
                                                                              -> case c_a1vcf of {
                                                                                   ENil
                                                                                     -> let
                                                                                          v_a1vcg
                                                                                            = pairDelta
                                                                                                 (if b_a1vcc then
                                                                                                      da_a1vbY
                                                                                                  else
                                                                                                      mempty)
                                                                                                da_a1vcd
                                                                                        in
                                                                                          (v_a1vcg,
                                                                                           (a_a1vce
                                                                                               /+
                                                                                                 da_a1vcd,
                                                                                            ENil)) }
                                                                        (dbs_a1vc8, cs2'_a1vc9)
                                                                          = mapTr fElem_a1vc7
                                                                                trElem_a1vc6
                                                                               (runIdentity
                                                                                  x_a1vc2)
                                                                              v_a1vc5
                                                                      in
                                                                        (dbs_a1vc8,
                                                                         (a_a1vbZ /+ da_a1vbY,
                                                                          ECons
                                                                             (Identity cs2'_a1vc9)
                                                                            ENil)) }
                                                    (dbs_a1vbP, cs2'_a1vbQ)
                                                      = mapTr fElem_a1vbO trElem_a1vbN a_a1vbI
                                                          v_a1vbM in
                                                  let
                                                    (db_a1vch, c'_a1vci)
                                                      = iterTr trConcatCAtomic dbs_a1vbP a_a1vbJ
                                                  in
                                                    (db_a1vch,
                                                     func_a1vbG (a_a1vbH /+ da_a1vbK) cs2'_a1vbQ
                                                       c'_a1vci))
                  in func_a1vbG a_a1vbu cs_a1vbx c_a1vbF))
-}

-- >>> let f = $$( testCode )
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


{-
   (ensureDiffType
       $ (\ pa_ah3U pb_ah3V a_ah3W
            -> let v_ah3X = fst a_ah3W in
               let
                 (bs_ah3Y, cs_ah3Z)
                   = (Seq.unzip
                        $ (fmap
                             (\ a_ah40
                                -> let v_ah41 = snd a_ah3W in
                                   let
                                     (bs_ah42, cs_ah43)
                                       = (Seq.unzip
                                            $ (fmap
                                                 (\ a_ah44
                                                    -> let v_ah45 = (a_ah40, a_ah44)
                                                       in (v_ah45, CNone)))
                                                (unS v_ah41))
                                   in
                                     (S bs_ah42,
                                      CNE
                                        ((CJoin (COne (Identity cs_ah43)))
                                           ((CJoin (COne (Identity a_ah40)))
                                              (COne (Identity a_ah3W)))))))
                            (unS v_ah3X)) in
               let (b_ah46, c_ah47) = concatC (S bs_ah3Y)
               in
                 (b_ah46,
                  let
                    func_ah48
                      = \ a_ah49
                          -> \ a_ah4a
                               -> \ a_ah4b
                                    -> ((mkInteraction pa_ah3U) pb_ah3V
                                          $ (\ da_ah4c
                                               -> let v_ah4d = (a_ah4a /+ da_ah4c) in
                                                  let
                                                    f_ah4e da_ah4f cont_ah4g
                                                      = \ acc_ah4h
                                                          -> let v_ah4i = fstDeltaA da_ah4f
                                                             in cont_ah4g (acc_ah4h <> v_ah4i)
                                                  in
                                                    (((foldrDelta f_ah4e)
                                                        (\ acc_ah4j
                                                           -> let
                                                                fElem_ah4l
                                                                  = \ a_ah4o
                                                                      -> let v_ah4p = snd v_ah4d in
                                                                         let
                                                                           (bs_ah4q, cs_ah4r)
                                                                             = (Seq.unzip
                                                                                  $ (fmap
                                                                                       (\ a_ah4s
                                                                                          -> let
                                                                                               v_ah4t
                                                                                                 = (a_ah4o,
                                                                                                    a_ah4s)
                                                                                             in
                                                                                               (v_ah4t,
                                                                                                CNone)))
                                                                                      (unS v_ah4p))
                                                                         in
                                                                           (S bs_ah4q,
                                                                            CNE
                                                                              ((CJoin
                                                                                  (COne
                                                                                     (Identity
                                                                                        cs_ah4r)))
                                                                                 ((CJoin
                                                                                     (COne
                                                                                        (Identity
                                                                                           a_ah4o)))
                                                                                    (COne
                                                                                       (Identity
                                                                                          v_ah4d)))))
                                                                trElem_ah4k
                                                                  = \ b_ah4u da_ah4v c_ah4w
                                                                      -> let
                                                                           (c1_ah4x, c2_ah4y)
                                                                             = unCJoin
                                                                                 (unCNE c_ah4w) in
                                                                         let
                                                                           (c1_ah4z, c2_ah4A)
                                                                             = unCJoin c2_ah4y in
                                                                         let
                                                                           v_ah4B
                                                                             = (runIdentity
                                                                                  (unCOne c2_ah4A)
                                                                                  /+
                                                                                    (if b_ah4u then
                                                                                         da_ah4c
                                                                                     else
                                                                                         mempty)) in
                                                                         let
                                                                           v_ah4C
                                                                             = (runIdentity
                                                                                  (unCOne c1_ah4z)
                                                                                  /+ da_ah4v) in
                                                                         let
                                                                           f_ah4D da_ah4E cont_ah4F
                                                                             = \ acc_ah4G
                                                                                 -> let
                                                                                      v_ah4H
                                                                                        = sndDeltaA
                                                                                            da_ah4E
                                                                                    in
                                                                                      cont_ah4F
                                                                                        (acc_ah4G
                                                                                           <>
                                                                                             v_ah4H)
                                                                         in
                                                                           (((foldrDelta f_ah4D)
                                                                               (\ acc_ah4I
                                                                                  -> let
                                                                                       fElem_ah4K
                                                                                         = \ a_ah4N
                                                                                             -> let
                                                                                                  v_ah4O
                                                                                                    = (v_ah4C,
                                                                                                       a_ah4N)
                                                                                                in
                                                                                                  (v_ah4O,
                                                                                                   CNone)
                                                                                       trElem_ah4J
                                                                                         = \ b_ah4P
                                                                                             da_ah4Q
                                                                                             c_ah4R
                                                                                             -> let
                                                                                                  _ = c_ah4R in
                                                                                                let
                                                                                                  v_ah4S
                                                                                                    = (pairDelta
                                                                                                         (if b_ah4P then
                                                                                                              da_ah4v
                                                                                                          else
                                                                                                              mempty))
                                                                                                        da_ah4Q
                                                                                                in
                                                                                                  (v_ah4S,
                                                                                                   CNone)
                                                                                       (dbs_ah4L,
                                                                                        cs2'_ah4M)
                                                                                         = (((mapTr
                                                                                                fElem_ah4K)
                                                                                               trElem_ah4J)
                                                                                              (runIdentity
                                                                                                 (unCOne
                                                                                                    c1_ah4x)))
                                                                                             acc_ah4I
                                                                                     in
                                                                                       (dbs_ah4L,
                                                                                        CNE
                                                                                          ((CJoin
                                                                                              (COne
                                                                                                 (Identity
                                                                                                    cs2'_ah4M)))
                                                                                             ((CJoin
                                                                                                 (COne
                                                                                                    (Identity
                                                                                                       v_ah4C)))
                                                                                                (COne
                                                                                                   (Identity
                                                                                                      v_ah4B)))))))
                                                                              (if b_ah4u then
                                                                                   da_ah4c
                                                                               else
                                                                                   mempty))
                                                                             mempty
                                                                (dbs_ah4m, cs2'_ah4n)
                                                                  = (((mapTr fElem_ah4l)
                                                                        trElem_ah4k)
                                                                       a_ah49)
                                                                      acc_ah4j in
                                                              let
                                                                f_ah4T da_ah4U cont_ah4V
                                                                  = \ acc_ah4W
                                                                      -> \ a_ah4X
                                                                           -> let
                                                                                (db_ah4Y, c'_ah4Z)
                                                                                  = (trConcatCAtomic
                                                                                       da_ah4U)
                                                                                      a_ah4X
                                                                              in
                                                                                (cont_ah4V
                                                                                   (acc_ah4W
                                                                                      <> db_ah4Y))
                                                                                  c'_ah4Z
                                                              in
                                                                ((((foldrDelta f_ah4T)
                                                                     (\ acc_ah50
                                                                        -> \ a_ah51
                                                                             -> (acc_ah50,
                                                                                 ((func_ah48
                                                                                     cs2'_ah4n)
                                                                                    v_ah4d)
                                                                                   a_ah51)))
                                                                    dbs_ah4m)
                                                                   mempty)
                                                                  a_ah4b))
                                                       da_ah4c)
                                                      mempty))
                  in ((func_ah48 cs_ah3Z) a_ah3W) c_ah47)))
-}
