{-# LANGUAGE TemplateHaskell #-}
import           Criterion.Main


import           Data.Delta
import           Examples.Filter

import qualified Data.Incrementalized.Seq as IS
import           Data.Interaction


inc_q1 :: Tree -> (IS.Seq Tree, Interaction (Delta Tree) (Delta (IS.Seq Tree)))
inc_q1 = $$( qq1 )


main :: IO ()
main = defaultMain [
    env (return (exampleInput , exampleDelta, inc_q1 exampleInput)) $ \ ~(t, dt, (res, i)) ->
       bgroup "_" [
         bench "scratch" $ nf (fst . inc_q1) (t /+ dt),
         bench "inc"     $ nf (\d -> res /+ fst (runInteraction i d)) dt
       ]
  ]
