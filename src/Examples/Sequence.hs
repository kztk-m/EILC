{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Examples.Sequence where

import           Data.Coerce           (coerce)
import           Data.Maybe            (fromJust)
import qualified Data.Sequence         as Seq
import           EILC
import           Language.Unembedding

import           Data.Env
import           Data.Functor.Identity (Identity (Identity))
import           Data.List             (uncons)
import           Data.Typeable         (Proxy (Proxy))

newtype S a = S { unS :: Seq.Seq a }

-- Taken from https://github.com/yurug/cts
data DeltaS a
 = SIns Int (S a) -- ^ SIns i s inserts s at the ith position
 | SDel Int Int   -- ^ SDel i n deletes n elements from the ith position in a sequence
 | SRep Int (Delta a) -- ^ SRep i da applies the delta da to the ith element.
 | SRearr Int Int Int -- ^ SRearr i n j cuts n elements from the ith position and insert the cut sequence into the jth position (after cuting).

type instance Delta (S a) = [DeltaS a]

instance Diff a => Diff (S a) where
  a /+ das = foldl applyDelta a das
    where
      applyDelta (S s0) (SIns i (S s')) = S $ insSeq i s' s0
      applyDelta (S s0) (SDel i n)      = S $ delSeq i n s0
      applyDelta (S s0) (SRep i da)     = S $ repSeq i da s0
      applyDelta (S s0) (SRearr i n j)  = S $ rearrSeq i n j s0

insSeq :: Int -> Seq.Seq a -> Seq.Seq a -> Seq.Seq a
insSeq i s' s0 =
    let (s1, s2) = Seq.splitAt i s0
    in s1 Seq.>< s' Seq.>< s2

delSeq :: Int -> Int -> Seq.Seq a -> Seq.Seq a
delSeq i n s0 =
    let (s1, stemp) = Seq.splitAt i s0
        s2 = Seq.drop n stemp
    in s1 Seq.>< s2

repSeq :: Diff a => Int -> Delta a -> Seq.Seq a -> Seq.Seq a
repSeq i da s0 = Seq.adjust' (/+ da) i s0

rearrSeq :: Int -> Int -> Int -> Seq.Seq a -> Seq.Seq a
rearrSeq i n j s0 =
    let (s1, s23) = Seq.splitAt i s0
        (s2, s3)  = Seq.splitAt n s23
    in insSeq j s2 (s1 Seq.>< s3)


-- APIs
dsingleton :: Delta a -> Delta (S a)
dsingleton da = [SRep 0 da]

singletonF :: (App2 IFq IFqT e, Diff a) => e a -> e (S a)
singletonF = lift singletonC
  where
    singletonC =
      ifqFromStateless (\a -> [|| S (Seq.singleton $$a) ||])
                       (\da -> [|| dsingleton $$da ||])

dempty :: Delta (S a)
dempty = []

emptyF :: (App2 IFq IFqT e, Diff a) => e (S a)
emptyF = lift emptyC unit
  where
    emptyC = ifqFromStateless (const [|| S Seq.empty ||]) (const [|| dempty ||])

type ConcatC = Seq.Seq Int


concatSeq :: S (S a) -> S a
concatSeq (S s0) = S $ foldr (\(S a) r -> a Seq.>< r) Seq.empty s0

s2c :: S (S a) -> ConcatC
s2c (S s0) = fmap (\(S a) -> Seq.length a) s0

concatC :: S (S a) -> (S a, ConcatC)
concatC s0 = (concatSeq s0, s2c s0)

trConcatC :: Delta (S (S a)) -> ConcatC -> (Delta (S a), ConcatC)
trConcatC [] conn = ([], conn)
trConcatC (dss : rest) conn =
  let (ds1, conn1) = trConcatCAtomic dss conn
      (ds2, conn2) = trConcatC rest conn1
  in (ds1 <> ds2, conn2)

insAtC :: Int -> ConcatC -> ConcatC -> ConcatC
insAtC i is is0 =
  foldl (\c n -> Seq.insertAt i n c) is0 is

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
      (ds', ci') = go offset ds ci
  in (ds', Seq.update i ci' c)
  where
    go :: Int -> Delta (S a) -> Int -> (Delta (S a), Int)
    go _ [] ci = ([], ci)
    go offset (x : xs) ci =
      let (ds1, ci1) = goAtomic offset x ci
          (ds2, ci2) = go offset xs ci1
      in (ds1 <> ds2, ci2)

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

concatF :: (App2 IFq IFqT e, Diff a) => e (S (S a)) -> e (S a)
concatF = lift $ ifqFromFunctions [|| concatC ||] [|| trConcatC ||]

mapTr :: (a -> (b, c)) -> (Delta a -> c -> (Delta b, c))
         -> Seq.Seq c -> Delta (S a) -> (Delta (S b), Seq.Seq c)
mapTr f tr cs [] = ([], cs)
mapTr f tr cs (d : ds) =
  let (d1, cs1) = trOne f tr cs d
      (d2, cs2) = mapTr f tr cs1 ds
  in (d1 <> d2, cs2)

trOne :: (a -> (b, c)) -> (Delta a -> c -> (Delta b, c))
         -> Seq.Seq c -> DeltaS a -> (Delta (S b), Seq.Seq c)
trOne f _ cs (SIns i (S as)) =
  let (bs, cs') = Seq.unzip $ fmap f as
  in ([SIns i (S bs)], foldl (\r b -> Seq.insertAt i b r) cs' cs)
trOne _ _ cs (SDel i n) =
  ([SDel i n], delSeq i n cs)
trOne _ _ cs (SRearr i n j) =
  ([SRearr i n j], rearrSeq i n j cs)
trOne _ tr cs (SRep i da) =
  let ci = fromJust $ Seq.lookup i cs
      (db, ci') = tr da ci
  in ([SRep i db], Seq.update i ci' cs)


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

mapT :: forall s a b. Diff a => IFqT s (S a) -> IFqT (a ': s) b -> IFqT s (S b)
mapT (IFqT tenv (sh1 :: Conn Proxy cs1) f1 tr1)
     (IFqT _    (sh2 :: Conn Proxy cs2) f2 tr2) =
      IFqT @s @(S b) @(Join cs1 (Join ('NE ('NEOne (Seq.Seq (Conn Identity cs2)))) (UnFlatten s))) tenv sh f tr
       -- IFqT @s @(S b) @(Join cs1 ('NE ('NEOne (Seq.Seq (Conn Identity cs2))))) sh f tr
  where
    sh :: Conn Proxy (Join cs1 (Join ('NE ('NEOne (Seq.Seq (Conn Identity cs2)))) (UnFlatten s)))
    sh = joinConn sh1 shMap

    shMap :: Conn Proxy (Join ('NE ('NEOne (Seq.Seq (Conn Identity cs2)))) (UnFlatten s))
    shMap = joinConn shA (convertEnv tenv)

    shA :: Conn Proxy ('NE ('NEOne (Seq.Seq (Conn Identity cs2))))
    shA = CNE (COne Proxy)


--     f :: Env PackedCode s -> CodeC (Code (S b), Conn PackedCode (Join cs1 ('NE ('NEOne (Seq.Seq (Conn Identity cs2))))))
    f :: Env PackedCode s
         -> CodeC
              (Code (S b),
               Conn PackedCode
                  (Join
                    cs1 (Join ('NE ('NEOne (Seq.Seq (Conn Identity cs2)))) (UnFlatten s))))
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

    trh :: Env PackedCodeDelta s -> Conn Proxy cs2 -> Code (Delta a -> Conn Identity cs2 -> (Delta b , Conn Identity cs2))
    trh env pcs = [|| \da c ->
        $$(code2conn pcs [|| c ||] $ \cs ->
          runCodeC (tr2 (ECons (PackedCodeDelta [|| da ||]) env) cs) $ \(db, cs') ->
            [|| ($$db, $$(conn2code cs')) ||])
      ||]

    tr :: Env PackedCodeDelta s
         -> Conn PackedCode (Join cs1 (Join ('NE ('NEOne (Seq.Seq (Conn Identity cs2)))) (UnFlatten s)))
         -> CodeC
              (Code (Delta (S b)),
               Conn PackedCode (Join cs1 (Join ('NE ('NEOne (Seq.Seq (Conn Identity cs2)))) (UnFlatten s))))
    tr denv conn | (c1, c23) <- decompConn (isNone sh1) (isNone shMap) conn, (c2, c3) <- decompConn (isNone shA) (isNone $ convertEnv tenv) c23 =
      case c2 of
        CNE (COne (PackedCode cs2)) -> do
          let env = unconvertEnv tenv c3
          (das, c1') <- tr1 denv c1
          (dbs, cs2' :: Code (Seq.Seq (Conn Identity cs2))) <- CodeC $ \k -> [|| let (dbs, cs2') = mapTr $$(h env) $$(trh denv sh2) $$cs2 $$das in $$(k ([|| dbs ||], [|| cs2' ||])) ||]
          -- FIXME: potential source of slow down.
          let env' = zipWithEnv (\(PackedCode a) (PackedCodeDelta da) -> PackedCode [|| $$a /+ $$da ||]) env denv
          return (dbs, joinConn c1' (joinConn (CNE $ COne $ PackedCode cs2') (convertEnv env')))

mapF :: forall e a b. (App2 IFq IFqT e, Diff a) => (e a -> e b) -> e (S a) -> e (S b)
mapF = flip (liftSO2 (Proxy @'[ '[], '[a] ]) mapT)

cartesian :: (App2 IFq IFqT e, Diff a, Diff b) => e (S a) -> e (S b) -> e (S (a, b))
cartesian as bs =
  concatMapF (\a -> mapF (\b -> pair a b) bs) as
  where
    concatMapF f x = concatF (mapF f x)
