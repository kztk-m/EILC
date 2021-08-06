{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Examples.Average where

import           EILC
import           Language.Unembedding

import           Data.Semigroup       (Sum (..))

newtype Bag a = Bag [a] deriving (Monoid, Semigroup)
type instance Delta (Bag a) = Bag a -- only insertion is considered.

instance Diff (Bag a) where
  Bag xs /+ Bag ys = Bag (ys ++ xs)

type instance Delta Int    = Sum Int
type instance Delta Double = Sum Double

instance Diff Int where
  a /+ da = a + getSum da

instance Diff Double where
  a /+ da = a + getSum da


appC :: IFq (Bag Double, Bag Double) (Bag Double)
appC = ifqFromStateless (\z -> [|| case $$z of { (Bag xs, Bag ys) -> Bag (xs ++ ys) } ||])
                        (\dz -> [|| case $$dz of { (Bag dx, Bag dy) -> Bag (dx ++ dy) } ||])
appF :: App IFq e => e (Bag Double) -> e (Bag Double) -> e (Bag Double)
appF x y = lift appC (pair x y)


cascadeAppS :: (App2 IFq IFqT e) => Int -> e (Bag Double) -> (e (Bag Double) -> e b) -> e b
cascadeAppS 0 x f = f x
cascadeAppS n x f = share (appF x x) $ \y -> cascadeAppS (n-1) y f

cascadeAppC :: (App2 IFq IFqT e) => Int -> e (Bag Double) -> (e (Bag Double) -> e b) -> e b
cascadeAppC 0 x f = f x
cascadeAppC n x f = let y = appF x x in cascadeAppC (n-1) y f


aveDupDup :: (App2 IFq IFqT e) => e (Bag Double) -> e Double
aveDupDup x = cascadeAppS 4 x ave

aveDupDup' :: (App2 IFq IFqT e) => e (Bag Double) -> e Double
aveDupDup' x = cascadeAppC 4 x ave

ave :: App IFq e => (e (Bag Double) -> e Double)
ave = \x -> mysum x `mydiv` i2d (len x)
  where
    lenC :: IFq (Bag Double) Int
    lenC = ifqFromStateless (\a  -> [|| case $$a of { Bag as -> length as } ||])
                            (\da -> [|| case $$da of { Bag as -> Sum (length as) } ||])

    i2dC :: IFq Int Double
    i2dC = ifqFromStateless (\a -> [|| fromIntegral $$a :: Double ||]) (\da -> [|| Sum (fromIntegral (getSum $$da) :: Double) ||])

    sumC :: IFq (Bag Double) Double
    sumC = ifqFromStateless (\a  -> [|| case $$a of { Bag as -> sum as } ||])
                            (\da -> [|| case $$da of { Bag as' -> Sum (sum as') } ||])

    divC :: IFq (Double, Double) Double
    divC = ifqFromD (\z -> [|| uncurry (/) $$z ||])
                    (\z dz -> [|| let {(x, y) = $$z ; (dx, dy) = $$dz} in Sum $ (x /+ dx) / (y /+ dy) - x / y ||])

    len = lift lenC
    i2d = lift i2dC
    mysum = lift sumC
    mydiv x y = lift divC (pair x y)



sumD :: Bag Double -> Delta (Bag Double) -> Delta Double
sumD _ (Bag xs) = Sum $ Prelude.sum xs

lenD :: Bag Double -> Delta (Bag Double) -> Delta Int
lenD _ (Bag xs) = Sum $ length xs

i2dD :: Int -> Delta Int -> Delta Double
i2dD _ d = Sum $ fromIntegral $ getSum d

divD :: (Double, Double) -> (Delta Double, Delta Double) -> Delta Double
divD (x, y) (dx, dy) = Sum $ (x /+ dx) / (y /+ dy) - x / y

sumF :: Incr e => e (Bag Double) -> e Double
sumF = liftI (\(Bag xs) -> sum xs) sumD

lenF :: Incr e => e (Bag Double) -> e Int
lenF = liftI (\(Bag xs) -> length xs) lenD

i2dF :: Incr e => e Int -> e Double
i2dF = liftI fromIntegral i2dD

divF :: Incr e => e (Double, Double) -> e Double
divF = liftI (uncurry (/)) divD

aveD :: Incr e => e (Bag Double) -> e Double
aveD x = shareI x $ \y -> divF (pairI (sumF y) (i2dF (lenF y)))


-- >>> let f = $$(runIFq (runAppMono' ave))
-- >>> let (res, tr) = f (Bag [1..100])
-- >>> res
-- >>> let dbs = iterations tr [Bag [1], Bag [2], Bag [30]]
-- >>> dbs
-- >>> res /+ mconcat dbs
-- 50.5
-- [Sum {getSum = -0.4900990099009874},Sum {getSum = -0.4706853038245029},Sum {getSum = -0.18970112316771548}]
-- 49.349514563106794

-- >>> let f = $$(runIFq (runAppMono' aveDupDup))
-- >>> let (res, tr) = f (Bag [1..100])
-- >>> res
-- >>> let dbs = iterations tr [Bag [1], Bag [2], Bag [30]]
-- >>> dbs
-- >>> res /+ mconcat dbs
-- 50.5
-- [Sum {getSum = -0.4900990099009874},Sum {getSum = -0.4706853038245029},Sum {getSum = -0.18970112316771548}]
-- 49.349514563106794


-- >>> let f = $$(runIFq (runAppMono' aveDupDup'))
-- >>> let (res, tr) = f (Bag [1..100])
-- >>> res
-- >>> let dbs = iterations tr [Bag [1], Bag [2], Bag [30]]
-- >>> dbs
-- >>> res /+ mconcat dbs
-- 50.5
-- [Sum {getSum = -0.4900990099009874},Sum {getSum = -0.4706853038245029},Sum {getSum = -0.18970112316771548}]
-- 49.349514563106794


