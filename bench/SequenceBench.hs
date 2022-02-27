{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# OPTIONS_GHC -Wno-orphans #-}


import           Examples.Sequence

import           Control.DeepSeq
import           Criterion.Main
import qualified Data.Sequence            as S

import           Data.Delta
import           Data.Interaction

import           Data.List                (foldl')

-- import           Data.IFFT         (IFFT)
import           Data.IFqT                (IFqT)
import           Data.IFqTU               (IFqTU)

import           Data.IF                  (IFT)
import           Data.Incrementalized.Seq as IS
import           Data.Proxy               (Proxy (..))

import           BenchUtil

sequence1 :: Seq Int
sequence1 = IS.fromList [1..100]

sequence2 :: Seq Int
sequence2 = IS.fromList [1..100]


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

-- tryScratch :: (NFData b, Diff a) => (a -> b) -> a -> [Delta a] -> b
-- tryScratch = go
--   where
--     go f a [] = f a
--     go f a (da : ds) =
--       let !a' = a /+ da
--       in f a' `deepseq` go f a' ds


cartesianS :: (Seq Int, Seq Int) -> Seq (Int, Int)
cartesianS (xs, ys) =
  -- xs >>= \x -> fmap (\y -> (x,y)) ys
  (,) <$> xs <*> ys

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

-- doBench :: String -> (Seq Int, Seq Int) -> [Delta (Seq Int, Seq Int)] -> Benchmark
-- doBench gname a0 ds =
--   env (return (a0, ds)) $ \ ~(a0', ds') ->
--     bgroup gname [
--       bench "Scratch" $ nf (tryScratch cartesianS a0') ds',
--       bench "T"       $ nf (tryInc dCartesianT a0') ds' ,
--       bench "T-Opt"   $ nf (tryInc dCartesianTU  a0') ds',
--       bench "Raw"     $ nf (tryInc dCartesianRaw a0') ds'
--     ]

bfunc :: [BenchType (Seq Int, Seq Int) (Seq (Int, Int))]
bfunc = [ Scratch "Scratch" cartesianS,
--          Incrementalized "T" dCartesianT,
          -- Scratch "Scratch (from T-Opt)" (fst . dCartesianTU),
          Incrementalized "Raw" dCartesianRaw,
          Incrementalized "T-Opt" dCartesianTU
        ]

main :: IO ()
-- main = print $! forProf
main = defaultMain [
  -- benchsuit "100-1-0" (mkInitSequences 100) (insOuter 1) bfunc,
  -- benchsuit "100-0-1" (mkInitSequences 100) (insInner 1) bfunc,
  benchsuit "200-0-0" (mkInitSequences 200) [] bfunc,
  -- benchsuit "400-0-0" (mkInitSequences 400) [] bfunc,
  -- benchsuit "600-0-0" (mkInitSequences 600) [] bfunc,
  benchsuit "200-1-0" (mkInitSequences 200) (insOuter 1) bfunc,
  benchsuit "200-0-1" (mkInitSequences 200) (insInner 1) bfunc,
  benchsuit "200-10-0" (mkInitSequences 200) (insOuter 10) bfunc,
  benchsuit "200-0-10" (mkInitSequences 200) (insInner 10) bfunc,
  benchsuit "200-20-0" (mkInitSequences 200) (insOuter 20) bfunc,
  benchsuit "200-0-20" (mkInitSequences 200) (insInner 20) bfunc
    -- doBench "100-1-0" (mkInitSequences 100) (insOuter 1),
    -- doBench "100-0-1" (mkInitSequences 100) (insInner 1),
    -- doBench "200-1-0" (mkInitSequences 200) (insOuter 1),
    -- doBench "200-0-1" (mkInitSequences 200) (insInner 1),
    -- doBench "200-10-0" (mkInitSequences 200) (insOuter 10),
    -- doBench "200-0-10" (mkInitSequences 200) (insInner 10),
    -- doBench "200-20-0" (mkInitSequences 200) (insOuter 20),
    -- doBench "200-0-20" (mkInitSequences 200) (insInner 20)
  ]
