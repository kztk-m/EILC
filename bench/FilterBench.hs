{-# LANGUAGE TemplateHaskell #-}
import           Criterion.Main


import           Data.Delta
import           Examples.Filter

-- import qualified Data.Incrementalized.Seq as IS
import           Data.Interaction

import           BenchUtil

inc_q1 :: Tree -> (Tree, Interaction (Delta Tree) (Delta Tree))
inc_q1 = $$( qq1 )

bfunc :: [BenchType Tree Tree]
bfunc = [ Scratch "scratch_raw" q1R ,
          Scratch "scratch_inc" (fst . inc_q1) ,
          Incrementalized "inc" inc_q1 ]

main :: IO ()
main = defaultMain [
  benchsuit "add 'Second Edition'" exampleInput [exampleDelta] bfunc,
  benchsuit "add 'Second Edition'-L" largerInput [exampleDelta] bfunc
    -- env (return (exampleInput , exampleDelta, inc_q1 exampleInput)) $ \ ~(t, dt, (res, i)) ->
    --    bgroup "_" [
    --      bench "scratch_raw" $ nf q1R            (t /+ dt),
    --      bench "scratch_inc" $ nf (fst . inc_q1) (t /+ dt),
    --      bench "inc"         $ nf (\d -> res /+ fst (runInteraction i d)) dt
    --    ]
  ]
