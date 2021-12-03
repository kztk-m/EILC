{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
module Data.Incrementalized.Bag.Core
  (
    Bag(..), singletonBag, Delta(..),
    foldBag,

    FoldBagC(..), foldBagC, foldBagI, foldBagTr,

    Map(..),
    myFoldMap,
    FoldMapC(..), foldMapC, foldMapI, foldMapTr,
  )
where

import           Data.Coerce                   (coerce)
import           Data.Foldable                 (fold)
import           Data.Group

import           Control.Arrow                 (first, second, (&&&), (***))

import           Data.Delta
import           Data.IFq
import           Data.Incrementalized
import           Data.Incrementalized.Function
import           Data.Incrementalized.Group
import qualified Data.Map.Strict               as M

-- | @Bag a@ is defined to be a mapping from elements to their quanties.
newtype Bag a = Bag { unBag :: M.Map a Int }
  deriving stock Show

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

instance Ord a => Abelian (Bag a)

instance Ord a => Eq (Bag a) where
  as == bs = unBag (normalize as) == unBag (normalize bs)

newtype instance Delta (Bag a) = DeltaBag (GroupChangeWithReplace (Bag a))
  deriving newtype (Semigroup, Monoid)
  deriving stock Show

instance Ord a => Diff (Bag a) where
  as /+ DeltaBag (GroupChange bs) = as <> bs
  _  /+ DeltaBag (Replace bs)     = bs

  checkEmpty (DeltaBag (GroupChange (Bag as))) = M.null as
  checkEmpty _                                 = False

instance Ord a => DiffMinus (Bag a) where
  as /- bs = DeltaBag (GroupChange (invert bs <> as))

instance Ord a => DiffReplace (Bag a) where
  replaceTo as = DeltaBag (Replace as)

instance Ord a => DiffGroupReplace (Bag a)



foldBag :: Group t => (a -> t) -> Bag a -> t
foldBag f = foldr ((<>) . h) mempty . M.toList . unBag
  where
    h (a , k)  = Data.Group.pow (f a) k

data FoldBagC a b c
  = NothingFB
  | JustFB  (a -> (b, c), [(c,Int)]) -- ^ Element (c, k) means k-copies of c.


-- fromJustFB :: FoldBagC a b c -> [(c, Int)]
-- fromJustFB (JustFB x) = x
-- fromJustFB _          = error "fromJustFB: NothingFB"

foldBagTrUnchangedOpt ::
  (Group t, DiffGroupReplace t)
  => (a -> t) -> Delta (Bag a) -> Delta t
foldBagTrUnchangedOpt f (DeltaBag (GroupChange   a)) = toGroupDelta $ foldBag f a
foldBagTrUnchangedOpt f (DeltaBag (Replace a))       = replaceTo $ foldBag f a


foldBagTrUnchanged ::
  (Group t, DiffGroupReplace t)
  => Delta (Bag a) -> FoldBagC a t c -> (Delta t, FoldBagC a t c)
foldBagTrUnchanged _ NothingFB = error "Impossible"
foldBagTrUnchanged (DeltaBag (GroupChange as)) (JustFB (f, cs)) =
  let (r, cs') = mconcat $ map h $ M.toList $ unBag as
  in (toGroupDelta r, JustFB (f, cs ++ cs'))
  where
    h (a, k) =
      let (t, c') = f a
      in (Data.Group.pow t k, [(c',k)])
foldBagTrUnchanged (DeltaBag (Replace as)) (JustFB (f, _)) =
  let (r, cs) = mconcat $ map h $ M.toList $ unBag as
  in (replaceTo r, JustFB (f, cs))
  where
    h (a, k) =
      let (t, c') = f a
      in (Data.Group.pow t k, [(c',k)])



{-
Interesting, if we allow non nil function update, we are not able to handle the case where a bag
associates an element a negative quantity.
-}
foldBagTrChanged ::
  (Diff t) =>
  (c -> (Delta t, c)) -> FoldBagC a t c -> (Delta t, FoldBagC a t c)
foldBagTrChanged _df NothingFB = error "Impossible"
foldBagTrChanged df (JustFB (f, cs)) =
  let (r,cs') = mconcat $ map h cs
  in (r, JustFB (changeFunction f df, cs'))
  where
    h (c, k)
      | k < 0 = error "foldBagTrChanged cannot handle negative quantity"
      | otherwise =
        let (dt, c') = df c
        -- following code is wrong: but, how we deal with this?
        in (mconcat (replicate k dt), [(c',k)])


foldBagInit ::
  Group t =>
  (a -> (t, c)) -> Bag a -> (t, FoldBagC a t c)
foldBagInit f =
  second (\cs -> JustFB (f, cs)) . foldr ((<>) . h) mempty . M.toList . unBag
  where
    h (a, k) =
      let (t, c) = f a
      in (Data.Group.pow t k, [(c,k)])

foldBagI ::
  (Group t, DiffGroupReplace t)
  => PFun IFqS c a t -> (PFun IFqS (FoldBagC a t c) (Bag a) t, ())
foldBagI (PFunIFqS (FunCache ic f _)) =
  case ic of
    Closed ->
      (PFunIFqS (FunCache ic
                  (second (const NothingFB) . foldBagInit f)
                  (\da c -> (foldBagTrUnchangedOpt (fst . f) da, c))), ())
    Open ->
      (PFunIFqS (FunCache ic
                  (foldBagInit f)
                  foldBagTrUnchanged), ())


foldBagTr ::
  (Diff t)
  => Delta (PFun IFqS c a t)
  -> ()
  -> (Delta (PFun IFqS (FoldBagC a t c) (Bag a) t), ())
foldBagTr (DeltaPFunIFqS (DeltaFunCache isNil df)) _ =
  if isNil then
    (DeltaPFunIFqS (DeltaFunCache True $ \c -> (mempty, c)), ())
  else
    let df' = foldBagTrChanged df
    in (DeltaPFunIFqS (DeltaFunCache False df'), ())

foldBagC ::
  (Group t, DiffGroupReplace t) =>
  IFqS (PFun IFqS c a t) (PFun IFqS (FoldBagC a t c) (Bag a) t)
foldBagC = fromFunctionsCode [|| foldBagI ||] [|| foldBagTr ||]

myFoldMap :: (Monoid b) => (k -> a -> b) -> M.Map k a -> b
myFoldMap f = Data.Foldable.fold . M.mapWithKey f


-- mempty element should behave as if there is no such element.
newtype Map k a = Map (M.Map k a)
  deriving newtype (Foldable, Functor, Show)

instance (Semigroup a, Ord k) => Semigroup (Map k a) where
  Map as <> Map bs = Map $ M.unionWith (<>) as bs

instance (Semigroup a, Ord k) => Monoid (Map k a) where
  mempty = Map M.empty

instance (Group a, Ord k) => Group (Map k a) where
  invert (Map m) = Map (M.map invert m)

instance (Abelian a, Ord k) => Abelian (Map k a)

newtype instance Delta (Map k a) = DeltaMap (GroupChangeWithReplace (Map k a))
  deriving newtype (Semigroup, Monoid)

instance (Ord k, Semigroup a) => Diff (Map k a) where
  Map mp /+ DeltaMap (GroupChange (Map mp')) = Map (M.unionWith (<>) mp mp')
  Map _  /+ DeltaMap (Replace     mp)        = mp

  checkEmpty (DeltaMap (GroupChange (Map mp))) = M.null mp
  checkEmpty _                                 = False

instance (Ord k, Group a) => DiffMinus (Map k a) where
  mp /- mp' = DeltaMap $ GroupChange $ coerce (invert mp' <> mp)


instance (Ord k, Group a) => DiffReplace (Map k a) where
  replaceTo = DeltaMap . Replace

instance (Ord k, Group a) => DiffGroupReplace (Map k a)


{-

How to incrementalize foldMap?

(1) If a function is primitive-like (yielding no change), things would
be easier. The change to foldMap f a for the change da to a is given by:

   foldMap f (a /+ da) = foldMap (fst f) a /+ foldMap (fst f) da

The cache for f is ignored.

(2) If a function is also changed, we need to keep a Map k [c] to make c
available to where f is used. Also, we need to keep track of f itself
as it is used in the derivative code.

   foldMap (f /+ df) (a /+ da) (f', cs) =
      let (dr, cs') = M.unzip $ M.mapWithKey (first mconcat . unzip $ map df) cs
          newF = f' /+ df
          (dr2, cs2) = first Data.Foldable.fold $ M.unzip $ M.mapWithKey newF da
      in (foldMap f a /+ mconcat dr /+ , (newF, cs'))

-}

data FoldMapC k a b c
  = NothingFM
  | JustFM  ((k, a) -> (b, c)) (M.Map k [c]) -- ^ Element (c, k) means k-copies of c.

foldMapTrUnchangedOpt ::
  (Abelian b, DiffGroupReplace b) =>
  (k -> a -> b) -> Delta (Map k a) -> Delta b
foldMapTrUnchangedOpt f (DeltaMap (GroupChange (Map m))) = toGroupDelta $ myFoldMap f m
foldMapTrUnchangedOpt f (DeltaMap (Replace     (Map m))) = replaceTo    $ myFoldMap f m

foldMapTrUnchanged ::
  (Diff b, Ord k, Abelian b, DiffGroupReplace b) =>
  Delta (Map k a) -> FoldMapC k a b c -> (Delta b, FoldMapC k a b c)
foldMapTrUnchanged _ NothingFM = error "Impossible"
foldMapTrUnchanged (DeltaMap (GroupChange (Map m))) (JustFM f cs) =
  let (dr, cs') = ((Data.Foldable.fold . fmap fst) &&& fmap snd) $ M.mapWithKey (curry $ (toGroupDelta *** (:[])) . f) m
  in (dr, JustFM f (M.unionWith (<>) cs cs'))
foldMapTrUnchanged (DeltaMap (Replace (Map m))) (JustFM f _) =
  let (r, cs) = (Data.Foldable.fold . fmap fst &&& fmap snd) $ M.mapWithKey (curry $ second (:[]) . f) m
  in (replaceTo r, JustFM f cs)


foldMapTrChanged ::
  (Diff b)
  => (c -> (Delta b, c))
  -> FoldMapC k a b c -> (Delta b, FoldMapC k a b c)
foldMapTrChanged _  NothingFM = error "Impossible"
foldMapTrChanged df (JustFM f cs) =
  let (dr1, cs1) = first Data.Foldable.fold $ (fmap fst &&& fmap snd) $ fmap (first mconcat . unzip . map df) cs
      f' = changeFunction f df
      --      (dr2, cs2) = ((Data.Foldable.fold . fmap fst) &&& fmap snd) $ M.mapWithKey (curry $ second (:[]) . f) m
  in (dr1 , JustFM f' cs1)

foldMapInit ::
  Abelian b
  => ((k, a) -> (b, c))
  -> Map k a -> (b, FoldMapC k a b c)
foldMapInit f (Map m) =
  let (r, cs) = ((Data.Foldable.fold . fmap fst) &&& fmap snd) $ M.mapWithKey (curry $ second (:[]) . f) m
  in (r, JustFM f cs)


foldMapI ::
  (Abelian b, DiffGroupReplace b, Ord k)
  => PFun IFqS c (k, a) b -> (PFun IFqS (FoldMapC k a b c) (Map k a) b, ())
foldMapI (PFunIFqS (FunCache isNil f _))
  | Closed <- isNil =
      (PFunIFqS (FunCache Closed (second (const NothingFM) . foldMapInit f)
                                 (\da c -> (foldMapTrUnchangedOpt (curry $ fst . f) da, c))), ())
  | Open <- isNil =
      (PFunIFqS (FunCache Open
                  (foldMapInit f)
                  foldMapTrUnchanged), ())

foldMapTr ::
  (Diff b)
  => Delta (PFun IFqS c (k, a) b)
  -> ()
  -> (Delta (PFun IFqS (FoldMapC k a b c) (Map k a) b), ())
foldMapTr (DeltaPFunIFqS (DeltaFunCache isNil df)) _ =
  if isNil then
    (DeltaPFunIFqS (DeltaFunCache True $ \c -> (mempty, c)), ())
  else
    let df' = foldMapTrChanged df
    in (DeltaPFunIFqS (DeltaFunCache False df'), ())

foldMapC ::
  (Ord k, Abelian b, DiffGroupReplace b) =>
  IFqS (PFun IFqS c (k,a) b) (PFun IFqS (FoldMapC k a b c) (Map k a) b)
foldMapC = fromFunctionsCode [|| foldMapI ||] [|| foldMapTr ||]
