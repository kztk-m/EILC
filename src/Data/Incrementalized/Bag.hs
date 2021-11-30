{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Data.Incrementalized.Bag where

import qualified Data.Map.Strict                     as M

import           Prelude                             hiding (id, (.))

import           Data.Code
import           Data.Conn
import           Data.IFq

import           Control.Arrow                       (second)
import           Data.Coerce                         (Coercible, coerce)
import           Data.Delta
import           Data.Env
import qualified Data.Foldable
import           Data.Group
import           Data.Incrementalized                (fromFunctionsCode)
import           Data.Incrementalized.Function
import           Data.Incrementalized.Group
import           Data.Kind                           (Type)
import           Data.Maybe                          (fromJust)
import           Data.Proxy                          (Proxy (Proxy))
import           Data.Typeable                       (Typeable)
import           Language.Unembedding
import           Language.Unembedding.PseudoFunction

-- | @Bag a@ is defined to be a mapping from elements to their quanties.
newtype Bag a = Bag { unBag :: M.Map a Int }

normalize :: Bag a -> Bag a
normalize (Bag a) = Bag $ M.filter (/= 0) a

singletonBag :: a -> Bag a
singletonBag a = Bag (M.singleton a 1)

instance Ord a => Semigroup (Bag a) where
  Bag as <> Bag bs = normalize $ Bag $  M.unionWith (+) as bs

instance Ord a => Monoid (Bag a) where
  mempty = Bag M.empty

instance Ord a => Group (Bag a) where
  invert (Bag a) = Bag $ M.map negate a

instance Ord a => Eq (Bag a) where
  -- | We assume that @as@ and @bs@ are already normalized.
  Bag as == Bag bs = as == bs

deriving via FromMonoid (Bag a) instance Ord a => Diff (Bag a)
deriving via FromMonoid (Bag a) instance Ord a => DiffMinus (Bag a)

newtype instance Delta (Bag a) = DeltaBag (Bag a)
  deriving newtype (Monoid , Semigroup)

foldBag :: Group t => (a -> t) -> Bag a -> t
foldBag f = foldr ((<>) . h) mempty . M.toList . unBag
  where
    h (a , k)  = Data.Group.pow (f a) k

data FoldBagC c
  = NothingFB
  | JustFB  [(c,Int)] -- ^ Element (c, k) means k-copies of c.

fromJustFB :: FoldBagC c -> [(c, Int)]
fromJustFB (JustFB x) = x
fromJustFB _          = error "fromJustFB: NothingFB"

foldBagTrUnchanged ::
  (Coercible t (Delta t), Group t)
  => (a -> t) -> Delta (Bag a) -> Delta t
foldBagTrUnchanged f (DeltaBag a) = coerce $ foldBag f a


foldBagTrChanged ::
  Group (Delta t) =>
  (c -> (Delta t, c)) -> FoldBagC c -> (Delta t, FoldBagC c)
foldBagTrChanged f = second JustFB . mconcat . map h . fromJustFB
  where
    h (c, k) =
      let (dt, c') = f c
      in (Data.Group.pow dt k, [(c',k)])

foldBagInit ::
  Group t =>
  (a -> (t, c)) -> Bag a -> (t, FoldBagC c)
foldBagInit f =
  second JustFB . foldr ((<>) . h) mempty . M.toList . unBag
  where
    h (a, k) =
      let (t, c) = f a
      in (Data.Group.pow t k, [(c,k)])

foldBagI ::
  (Coercible t (Delta t), Group t)
  => PFun IFqS c a t -> (PFun IFqS (FoldBagC c) (Bag a) t, ())
foldBagI (PFunIFqS (FunCache ic f _)) =
  case ic of
    Closed ->
      (PFunIFqS (FunCache ic
                  (second (const NothingFB) . foldBagInit f)
                  (\da c -> (foldBagTrUnchanged (fst . f) da, c))), ())
    Open ->
      (PFunIFqS (FunCache ic
                  (foldBagInit f)
                  (\da c -> (foldBagTrUnchanged (fst . f) da, c))), ())


foldBagTr ::
  (Group (Delta t))
  => Delta (PFun IFqS c a t)
  -> ()
  -> (Delta (PFun IFqS (FoldBagC c) (Bag a) t), ())
foldBagTr (DeltaPFunIFqS (DeltaFunCache isNil df)) _ =
  if isNil then
    (DeltaPFunIFqS (DeltaFunCache True $ \c -> (mempty, c)), ())
  else
    let df' = foldBagTrChanged df
    in (DeltaPFunIFqS (DeltaFunCache False df'), ())

foldBagC ::
  (Coercible t (Delta t),Group t, Group (Delta t)) =>
  IFqS (PFun IFqS c a t) (PFun IFqS (FoldBagC c) (Bag a) t)
foldBagC = fromFunctionsCode [|| foldBagI ||] [|| foldBagTr ||]




-- foldBagTerm ::
--   (Diff a, Ord a, Typeable a,
--    Coercible t (Delta t), Group t, Group (Delta t), Diff t, Typeable t,
--    PFunTerm IFqS term, AllIn s DiffTypeable)
--   => term (a ': s) t
--   -> term s (Bag a)
--   -> term s t
-- foldBagTerm t1 t2 =
--   pAbsTerm t1 $ \t1' ->
--   pAppTerm (mapTerm foldBagC t1') t2


-- I don't know but the following code causes GHC to panic.
foldBagF ::  forall term e a t.(Diff a, Ord a, Typeable a, Coercible t (Delta t),Group t, Group (Delta t), Diff t, Typeable t, PFunTerm IFqS term, App2 IFqS term e) => (e a -> e t) -> e (Bag a) -> e t
foldBagF = liftSO2 (Proxy @'[ '[a], '[] ]) $ fromPFun foldBagC

foldMap ::
  (Monoid b) => (k -> a -> b) -> M.Map k a -> b
foldMap f = Data.Foldable.fold . M.mapWithKey f


-- mempty element should behave as if there is no such element.
newtype Map k a = Map (M.Map k a)
  deriving newtype (Foldable, Functor, Show)

instance (Semigroup a, Ord k) => Semigroup (Map k a) where
  Map as <> Map bs = Map $ M.unionWith (<>) as bs

instance (Semigroup a, Ord k) => Monoid (Map k a) where
  mempty = Map M.empty

instance (Group a, Ord k) => Group (Map k a) where
  invert (Map m) = Map (M.map invert m)

instance (Ord k, Semigroup a) => Diff (Map k a) where
  Map mp /+ DeltaMap (Map mp') = Map (M.unionWith (<>) mp mp')
  checkEmpty (DeltaMap (Map mp)) = M.null mp

instance (Ord k, Group a) => DiffMinus (Map k a) where
  mp /- mp' = DeltaMap $ coerce (invert mp' <> mp)

newtype instance Delta (Map k a) = DeltaMap (Map k a)
  deriving newtype (Monoid , Semigroup, Show)


