{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-orphans #-}


import           Examples.Sequence

import           Control.DeepSeq
import           Criterion.Main
import qualified Data.Sequence     as S

import           Data.Delta
import           Data.Interaction

import           Data.List         (foldl')

import           Data.IFFT         (IFFT)
import           Data.IFqT         (IFqT)
import           Data.IFqTE        (IFqTE)
import           Data.IFqTEU       (IFqTEU)

import           Data.Proxy        (Proxy (..))

sequence1 :: S Int
sequence1 = S $ S.fromList [1..100]

sequence2 :: S Int
sequence2 = S $ S.fromList [1..100]

instance (NFData a, NFData (Delta a)) => NFData (AtomicDelta (S a)) where
  rnf (SIns _ s)     = rnf s
  rnf (SDel _ _)     = ()
  rnf (SRep _ da)    = rnf da
  rnf (SRearr _ _ _) = ()

instance (NFData (Delta a), NFData (Delta b)) => NFData (Delta (a, b)) where
  rnf (PairDelta da db) = rnf (da, db)

instance NFData (Delta Int) where
  rnf (DInt x) = rnf x

mkInitSequence :: Int -> S Int
mkInitSequence n = S $ S.fromList $ take n [1..]

mkInitSequences :: Int -> (S Int, S Int)
mkInitSequences n = (mkInitSequence n, mkInitSequence n)

insOuter :: Int -> [Delta (S Int, S Int)]
insOuter n = [ injDelta $ ADFst $ mkCons i | i <- ns ]
  where
    ns = take n [1..] -- this is different from [1..n]
    mkCons e = SIns 0 (S $ S.singleton e)

insInner :: Int -> [Delta (S Int, S Int)]
insInner n = [ injDelta $ ADSnd $ mkCons i | i <- ns ]
  where
    ns = take n [1..] -- this is different from [1..n]
    mkCons e = SIns 0 (S $ S.singleton e)

-- ops :: Int -> [Delta (S Int, S Int)]
-- ops n =
--   interleave [pure $ ADFst $ mkCons i | i <- ns] [pure $ ADSnd $ mkCons i | i <- ns]
--   where
--     ns = take n [1..] -- this is different from [1..n]
--     interleave [] ys         = ys
--     interleave (x:xs) []     = x:xs
--     interleave (x:xs) (y:ys) = x:y:interleave xs ys
--     mkCons e = SIns 0 (S $ S.singleton e)

tryInc :: (NFData (Delta a), NFData b, NFData (Delta b), Diff b) => (a -> (b, Interaction (Delta a) (Delta b))) -> a -> [Delta a] -> b
tryInc h initial ds =
  let (!res, !it) = h initial
      !dres = iterations it ds
  in foldl' (/+) res dres

tryScratch :: (NFData b, NFData a, Diff a) => (a -> (b, Interaction (Delta a) (Delta b))) -> a -> [Delta a] -> b
tryScratch h = go (fst . h)
  where
    go f a [] = f a
    go f a (da : ds) =
      let !a' = a /+ da
      in f a' `seq` go f a' ds



dCartesianT, dCartesianTE, dCartesianTEU, dCartesianF :: (S Int, S Int) -> (S (Int, Int), Interaction (Delta (S Int, S Int)) (Delta (S (Int, Int))))

dCartesianT   = $$( testCode (Proxy :: Proxy IFqT) )
dCartesianTE  = $$( testCode (Proxy :: Proxy IFqTE ) )
dCartesianTEU = $$( testCode (Proxy :: Proxy IFqTEU ) )
dCartesianF   = $$( testCode (Proxy :: Proxy IFFT ) )


doBench :: String -> (S Int, S Int) -> [Delta (S Int, S Int)] -> Benchmark
doBench gname a0 ds =
  env (return (a0, ds)) $ \ ~(a0', ds') ->
    bgroup gname [
      bench "S"    $ nf (tryScratch dCartesianT a0') ds',
      bench "T"    $ nf (tryInc dCartesianT a0') ds' ,
      bench "TE"   $ nf (tryInc dCartesianTE a0') ds' ,
      bench "TEU"  $ nf (tryInc dCartesianTEU a0') ds' ,
      bench "F"    $ nf (tryInc dCartesianF a0') ds'
    ]


main :: IO ()
main = defaultMain [
    doBench "100-1-0" (mkInitSequences 100) (insOuter 1),
    doBench "100-0-1" (mkInitSequences 100) (insInner 1),
    doBench "200-1-0" (mkInitSequences 200) (insOuter 1),
    doBench "200-0-1" (mkInitSequences 200) (insInner 1)
  ]
