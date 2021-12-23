{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE FlexibleContexts #-}
module BenchUtil
  (
    BenchType(..), benchsuit, benchsuit',
  ) where

import           Control.DeepSeq
import           Criterion
import           Data.Delta
import           Data.Interaction
import           Data.List        (foldl', scanl')

data BenchType a b
  = Scratch !String !(a -> b)
  | Incrementalized !String !(a -> (b, Interaction (Delta a) (Delta b)))

data FirstRun a b
  = FRFromScratch         !String !b !(a -> b)
  | FRFromIncrementalized !String !b !(Interaction (Delta a) (Delta b))

instance NFData b => NFData (FirstRun a b) where
  rnf (FRFromScratch s b f)         = rnf (s, b, f)
  rnf (FRFromIncrementalized s b i) = rnf (s, b, i)
-- With initial running cost
benchsuit ::
  (NFData a, NFData b, Diff a, Diff b, NFData (Delta a))
  => String -> a -> [Delta a] -> [BenchType a b] -> Benchmark
benchsuit gname input deltas0 bs =
  env ini $ \ ~(inputs, deltas) ->
    let doBench (Scratch bname f) = bench bname $ nf (map f) inputs
        doBench (Incrementalized bname f) = bench bname $
          nf (\ds ->
                let (b, i)   = f (head inputs)
                    odeltas =  iterations i ds
                in b `deepseq` foldl' (/+) b odeltas) deltas
    in bgroup gname $ map doBench bs
  where
    ini = return (scanl' (/+) input deltas0, deltas0)

-- Without initial running cost
benchsuit' ::
  (NFData a, NFData b, Diff a, Diff b, NFData (Delta a))
  => String -> a -> [Delta a] -> [BenchType a b] -> Benchmark
benchsuit' gname input deltas0 bs =
  let frs = map firstrun bs
  in frs `deepseq`
      env ini $ \ ~(inputs, deltas) ->
      let doBench (FRFromScratch bname _ f) =
            let loop []     = ()
                loop (i:is) = deepseq (f i) (loop is)
            in bench bname $ nf loop inputs
          doBench (FRFromIncrementalized bname o int) = bench bname $
            nf (\ds -> let !odeltas = iterations int ds
                      in foldl' (/+) o odeltas) deltas
      in bgroup gname $ map doBench frs
    where
      ini = return (tail $ scanl' (/+) input deltas0, deltas0)
      firstrun (Scratch bn f) = let b = f input in FRFromScratch bn b f
      firstrun (Incrementalized bn f) = let (b, i) = f input in FRFromIncrementalized bn b i
