{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE UndecidableSuperClasses    #-}

module Examples.Average where

import           EILC
import           Language.Unembedding


import           Data.Incrementalized
import           Data.Proxy           (Proxy (..))

newtype Bag a = Bag [a] deriving (Monoid, Semigroup)

-- newtype instance AtomicDelta (Bag a) = ADBag (Bag a) -- only insertions are considered

-- instance Diff (Bag a) where
--   applyAtomicDelta (Bag xs) (coerce -> Bag ys) = Bag (ys ++ xs)

newtype instance Delta (Bag a) = DBag (Bag a)
  deriving (Semigroup, Monoid)

instance Diff (Bag a) where
  Bag a /+ (DBag (Bag da)) = Bag (da ++ a)

  checkEmpty (DBag (Bag da)) = null da


-- newtype instance AtomicDelta Int = ADInt (Sum Int) deriving Show
-- newtype instance AtomicDelta Double = ADDouble (Sum Double) deriving Show

-- instance Diff Int where
--   applyAtomicDelta n (coerce -> getSum -> m) = n + m

-- instance Diff Double where
--   applyAtomicDelta n (coerce -> m) = n + m




-- type instance Delta (Bag a) = Bag a -- only insertion is considered.

-- instance Diff (Bag a) where
--   Bag xs /+ Bag ys = Bag (ys ++ xs)

-- type instance Delta Int    = Sum Int
-- type instance Delta Double = Sum Double

-- instance Diff Int where
--   a /+ da = a + getSum da

-- instance Diff Double where
--   a /+ da = a + getSum da


-- appC :: IFq (Bag Double, Bag Double) (Bag Double)
appC :: IncrementalizedQ cat => cat  (Bag Double, Bag Double) (Bag Double)
appC = fromStateless (\z -> [|| case $$z of { (Bag xs, Bag ys) -> Bag (xs ++ ys) } ||])
                     (\dz -> [|| fstDelta $$dz <> sndDelta $$dz ||])
--                        (\dz -> [|| case $$dz of { (Bag dx, Bag dy) -> Bag (dx ++ dy) } ||])



-- appF :: App IFq e => e (Bag Double) -> e (Bag Double) -> e (Bag Double)
appF ::
  (K cat ~ Diff, Diff a, Diff b,
  App cat e, IncrementalizedQ cat,
  Prod cat a b ~ (Bag Double, Bag Double)) =>
  e a -> e b -> e (Bag Double)
appF x y = lift appC (pair x y)

cascadeAppS ::
  (K cat ~ Diff, Diff b,
  LetTerm cat term, App2 cat term e, IncrementalizedQ cat,
  Prod cat (Bag Double) (Bag Double) ~ (Bag Double, Bag Double)) =>
  Int -> e (Bag Double) -> (e (Bag Double) -> e b) -> e b
cascadeAppS 0 x f = f x
cascadeAppS n x f = share (appF x x) $ \y -> cascadeAppS (n-1) y f

cascadeAppC ::
  (K cat ~ Diff, App cat e,
  IncrementalizedQ cat,
  Prod cat (Bag Double) (Bag Double) ~ (Bag Double, Bag Double)) =>
  Int -> e (Bag Double) -> (e (Bag Double) -> p) -> p
cascadeAppC 0 x f = f x
cascadeAppC n x f = let y = appF x x in cascadeAppC (n-1) y f


aveDupDup :: (App2 IFq IFqT e) => e (Bag Double) -> e Double
aveDupDup x = cascadeAppS 4 x ave

aveDupDup' :: (App2 IFq IFqT e) => e (Bag Double) -> e Double
aveDupDup' x = cascadeAppC 4 x ave

ave ::
  (IncrementalizedQ cat, App2 cat t e,
   Diff ~ K cat,
   Prod cat Double Double ~ (Double, Double))
  => (e (Bag Double) -> e Double)
ave = \x -> mysum x `mydiv` i2d (len x)
  where
    lenC :: IncrementalizedQ cat => cat (Bag Double) Int
    lenC = fromStateless (\a  -> [|| case $$a of { Bag as -> length as } ||])
                         (\da -> [|| case $$da of { DBag (Bag as) -> DInt (length as) } ||])
--                         (\da -> [|| fmap (\x -> case x of { DBag (Bag as) -> DInt (length as) }) $$da ||])

    i2dC :: IncrementalizedQ cat => cat Int Double
    i2dC = fromStateless (\a  -> [|| fromIntegral $$a :: Double ||])
    --                      (\da -> [|| fmap (\(DInt x) -> DDouble (Sum $ fromIntegral $ getSum x)) $$da ||])
                         (\da -> [|| case $$da of { DInt x -> DDouble (fromIntegral x) } ||])
    -- (\da -> [|| Sum (fromIntegral (getSum $$da) :: Double) ||])

    sumC :: IncrementalizedQ cat => cat (Bag Double) Double
    sumC = fromStateless (\a  -> [|| case $$a of { Bag as -> sum as } ||])
                         (\da -> [|| case $$da of { DBag (Bag as) -> DDouble (sum as) } ||])
--                         (\da -> [|| fmap (\ (DBag (Bag as)) -> DDouble (sum as) ) $$da ||])
--                            (\da -> [|| case $$da of { Bag as' -> Sum (sum as') } ||])

    divC :: IncrementalizedQ cat => cat (Double, Double) Double
    divC = fromD (\z -> [|| uncurry (/) $$z ||])
                 (\z dz -> [|| let {(x, y) = $$z; dx = fstDelta $$dz ; dy = sndDelta $$dz } in DDouble $ (x /+ dx) / (y /+ dy) - x / y ||])
--                    (\z dz -> [|| let {(x, y) = $$z ; (dx, dy) = $$dz} in Sum $ (x /+ dx) / (y /+ dy) - x / y ||])

    len = lift lenC
    i2d = lift i2dC
    mysum = lift sumC
    mydiv x y = lift divC (pair x y)


runMonoWith :: (Term cat term, K cat a, K cat b) => Proxy term -> (TSem cat term a -> TSem cat term b) -> cat a b
runMonoWith _ = runMono


-- sumD :: Bag Double -> Delta (Bag Double) -> Delta Double
-- sumD _ (Bag xs) = Sum $ Prelude.sum xs

-- lenD :: Bag Double -> Delta (Bag Double) -> Delta Int
-- lenD _ (Bag xs) = Sum $ length xs

-- i2dD :: Int -> Delta Int -> Delta Double
-- i2dD _ d = Sum $ fromIntegral $ getSum d

-- divD :: (Double, Double) -> (Delta Double, Delta Double) -> Delta Double
-- divD (x, y) (dx, dy) = Sum $ (x /+ dx) / (y /+ dy) - x / y

-- sumF :: Incr e => e (Bag Double) -> e Double
-- sumF = liftI (\(Bag xs) -> sum xs) sumD

-- lenF :: Incr e => e (Bag Double) -> e Int
-- lenF = liftI (\(Bag xs) -> length xs) lenD

-- i2dF :: Incr e => e Int -> e Double
-- i2dF = liftI fromIntegral i2dD

-- divF :: Incr e => e (Double, Double) -> e Double
-- divF = liftI (uncurry (/)) divD

-- aveD :: Incr e => e (Bag Double) -> e Double
-- aveD x = shareI x $ \y -> divF (pairI (sumF y) (i2dF (lenF y)))


-- >>> let f = $$(runIFq (runMonoWith (Proxy :: Proxy IFqT) ave))
-- >>> let (res, tr) = f (Bag [1..100])
-- >>> res
-- >>> let (dbs, _) = runInteraction tr $ monoidFromList [ADBag $ Bag [1], ADBag $ Bag [2], ADBag $ Bag [30]]
-- >>> dbs
-- >>> res /+ dbs
-- 50.5
-- monoidFromList [ADDouble (Sum {getSum = -1.1504854368932058})]
-- 49.349514563106794

-- >>> let f = $$(runIFq (runMonoWith (Proxy :: Proxy IFqT) aveDupDup))
-- >>> let (res, tr) = f (Bag [1..100])
-- >>> res
-- >>> let (dbs, _) = runInteraction tr $ monoidFromList [ADBag $ Bag [1], ADBag $ Bag [2], ADBag $ Bag [30]]
-- >>> dbs
-- >>> res /+ dbs
-- 50.5
-- monoidFromList [ADDouble (Sum {getSum = -1.1504854368932058})]
-- 49.349514563106794


-- >>> let f = $$(runIFq (runMonoWith (Proxy :: Proxy IFqT) aveDupDup'))
-- >>> let (res, tr) = f (Bag [1..100])
-- >>> res
-- >>> let (dbs, _) = runInteraction tr $ monoidFromList [ADBag $ Bag [1], ADBag $ Bag [2], ADBag $ Bag [30]]
-- >>> dbs
-- >>> res /+ dbs
-- 50.5
-- monoidFromList [ADDouble (Sum {getSum = -1.1504854368932058})]
-- 49.349514563106794


