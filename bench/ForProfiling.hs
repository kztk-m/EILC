{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE TemplateHaskell #-}
import           Control.DeepSeq  (NFData, deepseq, rnf)
import           Data.Delta
import           Data.Interaction
import           Examples.Filter


inc_q1 :: Tree -> (Tree, Interaction (Delta Tree) (Delta Tree))
inc_q1 = $$( qq1 )

nf :: NFData b => Int -> (a -> b) -> a -> b
nf 0 f x = f x
nf 1 f x = f x
nf n f x =
  let res = f x
  in deepseq res (nf (n-1) f x)


main :: IO ()
main = do
  let res = nf 100 (\input ->
        let (r, i) = inc_q1 input
            (dr, _i') = runInteraction i exampleDelta
        in r /+ dr) largerInput
  print $ rnf res
