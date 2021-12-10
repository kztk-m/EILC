{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# OPTIONS_GHC -Wno-orphans #-}


import           Examples.Sequence

import           Control.DeepSeq
import           Control.Monad                (join)
import           Criterion.Main
import qualified Data.Sequence                as S

import           Data.Delta
import           Data.Interaction

import           Data.List                    (foldl')

-- import           Data.IFFT         (IFFT)
import           Data.IFqT                    (IFqT)
import           Data.IFqTU                   (IFqTU)

import           Data.IF                      (IFT)
import           Data.Incrementalized.Group
import           Data.Incrementalized.Numeric
import           Data.Incrementalized.Seq     as IS
import           Data.Proxy                   (Proxy (..))

import           Data.JoinList

sequence1 :: Seq Int
sequence1 = IS.fromList [1..100]

sequence2 :: Seq Int
sequence2 = IS.fromList [1..100]

instance NFData a => NFData (Seq a) where
  rnf (Seq a) = rnf a

instance NFData a => NFData (JoinList a) where
  rnf JLNil          = ()
  rnf (JLNonEmpty a) = rnf a

instance NFData a => NFData (JoinListNE a) where
  rnf (JLSingle a)   = rnf a
  rnf (JLJoin xs ys) = rnf (xs, ys)

instance (NFData a, NFData (Delta a)) => NFData (AtomicDelta (Seq a)) where
  rnf (SIns _ s)     = rnf s
  rnf (SDel _ _)     = ()
  rnf (SRep _ da)    = rnf da
  rnf (SRearr _ _ _) = ()

instance (NFData a, NFData (Delta a)) => NFData (Delta (Seq a)) where
  rnf (DeltaSeq a) = rnf a

instance (NFData (Delta a), NFData (Delta b)) => NFData (Delta (a, b)) where
  rnf (PairDelta da db) = rnf (da, db)

instance NFData (Delta Int) where
  rnf (DeltaInt x) = rnf x

instance NFData a => NFData (GroupChange a) where
  rnf (GroupChange a) = rnf a

mkInitSequence :: Int -> Seq Int
mkInitSequence n = IS.fromList $ take n [1..]

mkInitSequences :: Int -> (Seq Int, Seq Int)
mkInitSequences n = (mkInitSequence n, mkInitSequence n)

insOuter :: Int -> [Delta (Seq Int, Seq Int)]
insOuter n = [ injDelta $ ADFst $ mkCons i | i <- ns ]
  where
    ns = take n [1..] -- this is different from [1..n]
    mkCons e = SIns 0 (Seq $ S.singleton e)

insInner :: Int -> [Delta (Seq Int, Seq Int)]
insInner n = [ injDelta $ ADSnd $ mkCons i | i <- ns ]
  where
    ns = take n [1..] -- this is different from [1..n]
    mkCons e = SIns 0 (Seq $ S.singleton e)

-- ops :: Int -> [Delta (S Int, S Int)]
-- ops n =
--   interleave [pure $ ADFst $ mkCons i | i <- ns] [pure $ ADSnd $ mkCons i | i <- ns]
--   where
--     ns = take n [1..] -- this is different from [1..n]
--     interleave [] ys         = ys
--     interleave (x:xs) []     = x:xs
--     interleave (x:xs) (y:ys) = x:y:interleave xs ys
--     mkCons e = SIns 0 (S $ S.singleton e)

tryInc :: (Diff b) => (a -> (b, Interaction (Delta a) (Delta b))) -> a -> [Delta a] -> b
tryInc h initial ds =
  let (!res, !it) = h initial
      !dres = iterations it ds
  in foldl' (/+) res dres

tryScratch :: (NFData b, Diff a) => (a -> b) -> a -> [Delta a] -> b
tryScratch = go
  where
    go f a [] = f a
    go f a (da : ds) =
      let !a' = a /+ da
      in f a' `deepseq` go f a' ds


cartesianS :: (Seq Int, Seq Int) -> Seq (Int, Int)
cartesianS (xs, ys) =
  join $ fmap (\x -> fmap (\y -> (x,y)) ys) xs

dCartesianT, dCartesianTU, dCartesianRaw ::
  (Seq Int, Seq Int) -> (Seq (Int, Int), Interaction (Delta (Seq Int, Seq Int)) (Delta (Seq (Int, Int))))

dCartesianT   = $$( testCode (Proxy :: Proxy IFqT) )
-- dCartesianTHO = $$( testCodeHO (Proxy :: Proxy IFqT) )
dCartesianTU  = $$( testCode (Proxy :: Proxy IFqTU) )
dCartesianRaw = testCodeRaw (Proxy :: Proxy IFT)
-- dCartesianTE  = $$( testCode (Proxy :: Proxy IFqTE ) )
-- dCartesianTEUS = $$( testCode (Proxy :: Proxy IFqTEUS ) )
-- dCartesianF   = $$( testCode (Proxy :: Proxy IFFT ) )


forProf :: ()
forProf =
  rnf $ tryInc dCartesianTU (mkInitSequences 1000) (insOuter 100 <> insInner 100)

doBench :: String -> (Seq Int, Seq Int) -> [Delta (Seq Int, Seq Int)] -> Benchmark
doBench gname a0 ds =
  env (return (a0, ds)) $ \ ~(a0', ds') ->
    bgroup gname [
      bench "Scratch" $ nf (tryScratch cartesianS a0') ds',
      bench "T"       $ nf (tryInc dCartesianT a0') ds' ,
      bench "T-Opt"   $ nf (tryInc dCartesianTU  a0') ds',
      bench "Raw"     $ nf (tryInc dCartesianRaw a0') ds'
    ]


main :: IO ()
-- main = print $! forProf
main = defaultMain [
    doBench "100-1-0" (mkInitSequences 100) (insOuter 1),
    doBench "100-0-1" (mkInitSequences 100) (insInner 1),
    doBench "200-1-0" (mkInitSequences 200) (insOuter 1),
    doBench "200-0-1" (mkInitSequences 200) (insInner 1),
    doBench "200-10-0" (mkInitSequences 200) (insOuter 10),
    doBench "200-0-10" (mkInitSequences 200) (insInner 10),
    doBench "200-20-0" (mkInitSequences 200) (insOuter 20),
    doBench "200-0-20" (mkInitSequences 200) (insInner 20)
  ]
