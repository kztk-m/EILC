{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE TemplateHaskell #-}
import           Control.DeepSeq  (NFData, deepseq, rnf)
import           Data.Delta
import           Data.Foldable    (foldl')
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
  let res = nf 10 (\input ->
        let (r, i) = inc_q1 input
            drs = iterations i (exampleDeltas 100) -- [exampleDelta]
        in foldl' (/+) r drs) largerInput
  print $ rnf res
