{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
module Data.Incrementalized.Bag.Core
  (
    Map(..), Bag, Delta(..),

    Fixed(..),
    fstFixedC, sndFixedC, pairFixedC, unfixedC,

    foldBag, myFoldMap,

    singletonBag, singletonBagI, singletonBagTr,
    singletonMap, singletonMapI, singletonMapTr,


    foldUList, foldUListC,

    convertMap, convertMapC, ConvertMapCache(..),
    convertMapInit, convertMapTr,


  )
  -- (
  --   Bag(..), singletonBag, Delta(..),
  --   foldBag,

  --   FoldBagC(..), foldBagC, foldBagI, foldBagTr,

  --   Map(..),
  --   myFoldMap,
  --   FoldMapC(..), foldMapC, foldMapI, foldMapTr,
  -- )
where

import           Prelude                       hiding (id, (.))

import           Data.Coerce                   (coerce)
import           Data.Foldable                 (toList)
import           Data.Group


import           Data.Delta
import           Data.IFq
import           Data.Incrementalized
import           Data.Incrementalized.Function
import           Data.Incrementalized.Group
import qualified Data.Map.Strict               as M


import           Data.Code
import           Data.Conn
import           Data.Function                 (on)
import           Data.JoinList                 as JL
import           Data.Monoid                   (Sum)
import           Language.Haskell.TH.Syntax    (Lift)
import           Language.Unembedding


newtype Fixed a = Fixed { getFixed :: a }
  deriving newtype (Num, Ord, Eq, Semigroup, Monoid, Group, Abelian)
  deriving stock   (Show, Functor, Foldable, Traversable, Lift)

data instance Delta (Fixed a) = NoUpdate
  deriving stock Show

instance Semigroup (Delta (Fixed a)) where
  _ <> _ = NoUpdate

instance Monoid (Delta (Fixed a)) where
  mempty = NoUpdate


instance Diff (Fixed a) where
  a /+ _ = a
  checkEmpty _ = True

-- | A map to be folded.
newtype Map k a = Map (M.Map k a)
  deriving newtype (Foldable, Functor, Show)

instance (Semigroup a, Ord k) => Semigroup (Map k a) where
  Map as <> Map bs = Map $ M.unionWith (<>) as bs

instance (Monoid a, Ord k) => Monoid (Map k a) where
  mempty = Map M.empty

instance (Group a, Ord k) => Group (Map k a) where
  invert = fmap invert

instance (Abelian a, Ord k) => Abelian (Map k a)

newtype instance Delta (Map (Fixed k) a) = DMap (Map (Fixed k) a)
  deriving newtype (Semigroup, Monoid)
  deriving stock Show

instance (Monoid a, Ord k, Eq a) => Eq (Map (Fixed k) a) where
  Map xs == Map ys = eq xs ys
    where
      eq = (==) `on` M.filter (/= mempty)

deriving via WithGroupChange (Map (Fixed k) a) instance (Monoid a, Ord k, Eq a) => Diff (Map (Fixed k) a)
deriving via WithGroupChange (Map (Fixed k) a) instance (Group a, Ord k, Eq a) => DiffMinus (Map (Fixed k) a)
deriving via WithGroupChange (Map (Fixed k) a) instance (Monoid a, Ord k, Eq a) => DiffGroupChange (Map (Fixed k) a)

fstFixedC :: IFqS (Fixed (a, b)) (Fixed a)
fstFixedC = fromStatelessCode (\a -> [|| Fixed $ fst (getFixed $$a) ||]) (const [|| mempty ||])

sndFixedC :: IFqS (Fixed (a, b)) (Fixed b)
sndFixedC = fromStatelessCode (\a -> [|| Fixed $ snd (getFixed $$a) ||]) (const [|| mempty ||])

pairFixedC :: IFqS (Fixed a, Fixed b) (Fixed (a, b))
pairFixedC = fromStatelessCode (\x -> [|| let (Fixed a, Fixed b) = $$x in Fixed (a, b) ||]) (const [|| mempty ||])

unfixedC :: Diff a => IFqS (Fixed a) a
unfixedC = fromStatelessCode (\x -> [|| getFixed $$x ||]) (const [|| mempty ||])

-- instance (Semigroup a, Ord k) => Semigroup (Map k a) where
--   Map as <> Map bs = Map $ M.unionWith (<>) as bs

-- instance (Semigroup a, Ord k) => Monoid (Map k a) where
--   mempty = Map M.empty

-- instance (Group a, Ord k) => Group (Map k a) where
--   invert (Map m) = Map (M.map invert m)

-- instance (Abelian a, Ord k) => Abelian (Map k a)


-- newtype instance Delta (Map k a) = DeltaMap (JoinList (AtomicDelta (Map k a)))
--   deriving newtype (Semigroup, Monoid)


-- instance (Diff k, Ord k, Diff a) => Diff (Map k a) where
--   (/+) = foldl'Delta applyAtomicDelta
--   -- FIXME: Should we check more deaper?
--   checkEmpty = foldrDelta (\_ _ -> False) True

-- instance (Diff k, Ord k, Diff a) => HasAtomicDelta (Map k a) where
--   data AtomicDelta (Map k a)
--     = KeyUpdate k (Delta k)
--     | ValUpdate k (Delta a)
--     | ValInsert k a
-- --    | KeyDelete k

--   injDelta = DeltaMap . pure
--   monoidMap f (DeltaMap ls) = Data.Foldable.foldMap f ls

--   applyAtomicDelta (Map mp) (ValUpdate k dv)
--     | checkEmpty dv = Map mp
--     | otherwise = Map $ case M.lookup k mp of
--         Just v  -> M.insert k (v /+ dv) mp
--         Nothing -> error "applyAtomicDelta: Update by a missing key"
--   applyAtomicDelta (Map mp) (ValInsert k v)
--     = Map $ case M.lookup k mp of
--               Just _  -> error "applyAtomicDelta: Inserting an entry with an existing key"
--               Nothing -> M.insert k v mp
--   applyAtomicDelta (Map mp) (KeyUpdate k dk)
--     | checkEmpty dk = Map mp
--     | otherwise = Map $ case M.lookup k mp of
--         Just v  -> M.insert k' v $ M.delete k mp
--         Nothing -> mp
--     where
--       k' = k /+ dk
--   -- applyAtomicDelta (Map mp) (KeyDelete k)
--   --   = Map $ M.delete k mp

-- Intermediate form for "foldMap"
newtype UList a = Unordered { getUnordered :: [a] }
  deriving newtype (Semigroup, Monoid)

instance (Monoid a, Eq a) => Eq (UList a) where
  Unordered xs == Unordered ys = ((==) `on` filter (/= mempty)) xs ys

newtype instance Delta (UList a) = DUList (UList a)
  deriving newtype (Semigroup, Monoid)

deriving via WithGroupChange (UList a) instance (Monoid a , Eq a) => Diff (UList a)
deriving via WithGroupChange (UList a) instance (Monoid a , Eq a) => DiffGroupChange (UList a)

-- We assume that @UList a@ elements will be folded by using the
-- commutative and associative operator (<>).
--
-- Notice that the commutative monoid structure does not mean we can
-- reflect an update to some element by an update to any element.
-- Consider the list `[2,3]` where `2` is updated by `+2`, while the
-- list will be reduced by `(*)`.

-- newtype instance Delta (UList a) = DeltaUList (JoinList (AtomicDelta (UList a)))
--   deriving newtype (Semigroup, Monoid)

-- instance Diff a => Diff (UList a) where
--   (/+) = applyDeltaFromHasAtomicDelta
--   checkEmpty = checkEmptyFromAtomicDelta

-- instance Diff a => HasAtomicDelta (UList a) where
--   data AtomicDelta (UList a) = Ins a | UpdAt Int (Delta a)

--   injDelta = DeltaUList . pure
--   monoidMap f (DeltaUList das) = Data.Foldable.foldMap f das


foldUList :: Monoid t => UList t -> t
foldUList (Unordered xs) = mconcat xs

foldUListC :: forall t. (Monoid t, DiffGroupChange t) => IFqS (UList t) t
foldUListC = IFqS CNone $ return (f, tr)
  where
    f :: Code (UList t) -> CodeC (Code t, Conn PackedCode 'JLNil)
    f c_ulist = CodeC $ \k -> [|| let r = mconcat (getUnordered $$c_ulist) in $$(k ([|| r ||], CNone)) ||]

    tr :: Code (Delta (UList t)) -> Conn PackedCode 'JLNil -> CodeC (Code (Delta t), Conn PackedCode 'JLNil)
    tr c_dulist _ = CodeC $ \k ->
      [|| let DUList dulist = $$c_dulist
              t_to_mappend  = mconcat (getUnordered dulist)
          in $$(k ([|| fromGroupChange (GroupChange t_to_mappend) ||], CNone))
       ||]



-- type FoldUListCache cs = 'JLNonEmpty ('JLSingle [Env Identity (Flatten cs)])

-- foldUListCTr ::
--   DiffGroupChange t
--   =>
--   Delta (UList t) -> c -> (Delta t, c)
-- foldUListCTr =
--   iterTr foldUListCTrAtomic

-- foldUListCTrAtomic ::
--   DiffGroupChange t
--   => AtomicDelta (UList t) -> c -> (Delta t, c)
-- foldUListCTrAtomic dt cs =
--   case dt of
--     Ins   a    -> (fromGroupChange (GroupChange a) , cs)
--     UpdAt _ da -> (da, cs)


-- foldUListC :: forall t. HasMonoid IFqS t => IFqS (UList t) t
-- foldUListC = case (mappendS :: IFqS (t,t) t, memptyS :: IFqS () t) of
--   (IFqS (sh_mappend :: Conn WitTypeable cs) m_mappendS, IFqS _sh_mempty  m_mempty) ->
--     case wit of
--       Wit -> IFqS sh $ do
--         (f_mappend, tr_mappend) <- m_mappendS
--         (f_mempty , _tr_mempty)  <- m_mempty

--         -- f_mempty cannot use "cache" as there is no change on its
--         -- input (of type ()). Also, tr_mempty always yield nil
--         -- changes, and thus _tr_mempty does no interesting work.
--         (memp0, _) <- f_mempty [|| () ||]
--         memp <- mkLet memp0
--         let
--           f :: Code (UList t) -> CodeC (Code t, Conn PackedCode (FoldUListCache cs))
--           f code_us = CodeC $ \k ->
--             [||
--               let (res, cc) = foldr (\a (r, clist) -> $$(toCode $ do
--                                                             (rr, cs) <- f_mappend [|| (a,r) ||]
--                                                             return [|| ($$rr, $$(conn2cenv cs) : clist) ||]
--                                                         )) ($$memp , []) $ getUnordered $$code_us
--               in $$(k ([|| res ||], CSingle $ PackedCode [|| cc ||]))
--              ||]
--           tr_mp :: Code (Delta t -> Delta t -> Env Identity (Flatten cs) -> (Delta t, Env Identity (Flatten cs)))
--           tr_mp = [|| \t1 t2 packed_cs -> $$(toCode $ do
--                                                 cs <- CodeC $ \k -> cenv2conn sh_mappend [|| packed_cs ||] k
--                                                 (r, cs') <- tr_mappend [|| PairDelta t1 t2 ||] cs
--                                                 return [|| ($$r, $$(conn2cenv cs')) ||]
--                                             )
--                     ||]

--           tr :: Code (Delta (UList t))
--                 -> Conn PackedCode (FoldUListCache cs)
--                 -> CodeC (Code (Delta t), Conn PackedCode (FoldUListCache cs))
--           tr code_dus (CNE (COne cc)) = _

--         return (f, _)
--         where
--           sh :: Conn WitTypeable (FoldUListCache cs)
--           sh = CSingle WitTypeable
--     where
--       wit :: Wit (Typeable (Flatten cs))
--       wit = witTypeableFlatten sh_mappend

convertMap :: (k -> a -> t) -> Map k a -> UList t
convertMap f (Map mp) = Unordered $ Data.Foldable.toList $ M.mapWithKey f mp

newtype ConvertMapCache k a b c = ConvertMapCache (Fixed k -> a -> (b, c), M.Map (Fixed k) c)

convertMapI :: (Fixed k -> a -> (t, c)) -> Map (Fixed k) a -> (UList t, ConvertMapCache k a t c)
convertMapI f (Map mp) =
  let mp' = M.mapWithKey f mp
  in (Unordered $ toList $ fmap fst mp', ConvertMapCache (f, fmap snd mp'))

convertMapTrU ::
  (Ord k, DiffGroupChange a, DiffGroupChange t)
  => (Delta (Fixed k) -> Delta a -> c -> (Delta t, c))
  -> Delta (Map (Fixed k) a) -> ConvertMapCache k a t c -> (Delta (UList t), ConvertMapCache k a t c)
convertMapTrU deriv_f (DMap (Map mp)) (ConvertMapCache (f, cs)) =
  procUpd (M.toList mp) [] cs
  where
    procUpd [] du c = (DUList $ Unordered du, ConvertMapCache (f, c))
    procUpd ((k, v) : us) du c =
      case M.lookup k c of
        Just ck ->
          let (dt, ck') = deriv_f mempty (fromGroupChange (GroupChange v)) ck
          in procUpd us (coerce (toGroupChange dt) : du) (M.insert k ck' c)
        Nothing ->
          let (t, ck) = f k v
          in procUpd us (t : du) (M.insert k ck c)

convertMapTrC ::
  (DiffGroupChange t)
  => (c -> (Delta t, c))
  -> ConvertMapCache k a t c -> (Delta (UList t), ConvertMapCache k a t c)
convertMapTrC df (ConvertMapCache (f, cs)) =
  let mp' = fmap df cs
      cs' = fmap snd mp'
      ts  = M.elems $ fmap ((coerce :: GroupChange t -> t) . toGroupChange . fst) mp'
  in (DUList $ Unordered ts, ConvertMapCache (curry $ changeFunction (uncurry f) df, cs') )

convertMapInit ::
  (Ord k , DiffGroupChange a, DiffGroupChange t)
  => PFun IFqS c (Fixed k, a) t -> PFun IFqS (ConvertMapCache k a t c) (Map (Fixed k) a) (UList t)
convertMapInit (PFunIFqS (FunCache isClosed f df)) =
  PFunIFqS $ FunCache isClosed (convertMapI (curry f))
                               (convertMapTrU (\dk da -> df (PairDelta dk da)))

convertMapTr ::
  (DiffGroupChange t)
  => Delta (PFun IFqS c (Fixed k, a) t)
  -> Delta (PFun IFqS (ConvertMapCache k a t c) (Map (Fixed k) a) (UList t))
convertMapTr (DeltaPFunIFqS (DeltaFunCache isNil df))
  | isNil     = mempty
  | otherwise = DeltaPFunIFqS (DeltaFunCache False $ convertMapTrC df)

convertMapC ::
  (Ord k , DiffGroupChange a, DiffGroupChange t)
  => IFqS (PFun IFqS c (Fixed k, a) t) (PFun IFqS (ConvertMapCache k a t c) (Map (Fixed k) a) (UList t))
convertMapC = fromStatelessCode (\a -> [|| convertMapInit $$a ||]) (\da -> [|| convertMapTr $$da ||]   )

type Bag a = Map (Fixed a) (Sum Int)

foldBag :: Monoid t => (Fixed k -> t) -> Bag k -> t
foldBag f = foldUList . convertMap (\k _ -> f k)


myFoldMap :: Monoid c => (k -> a -> c) -> Map k a -> c
myFoldMap f = foldUList . convertMap f

singletonMap :: k -> v -> Map k v
singletonMap k v = Map $ M.singleton k v

singletonBag :: Fixed k -> Bag k
singletonBag k = singletonMap k 1

singletonBagI :: Fixed a -> Bag a
singletonBagI = singletonBag

singletonBagTr :: (Ord a) => Delta (Fixed a) -> Delta (Bag a)
singletonBagTr _ = mempty

singletonMapI :: (Fixed k, v) -> (Map (Fixed k) v, Fixed k)
singletonMapI (k, v) = (Map (M.singleton k v), k)

singletonMapTr :: (DiffGroupChange v) => Delta (Fixed k, v) -> Fixed k -> (Delta (Map (Fixed k) v), Fixed k)
singletonMapTr (PairDelta _ dv) k = (DMap $ Map $ M.singleton k v, k)
  where
    GroupChange v = toGroupChange dv
    -- let k' = k /+ dk
    --     v' = v /+ dv
    -- in (replaceTo (Map (M.singleton k' v')), (k',v'))


-- convertMapI :: (k -> a -> (t, c)) -> Map k a -> (UList t, M.Map k c)
-- convertMapI f (Map mp) =
--   let mp' = M.mapWithKey f mp
--   in (Unordered $ toList $ fmap fst mp', fmap snd mp')

-- convertMapTrUnchanged ::
--   (Diff k, Ord k, Diff a, Diff t)
--   => (k -> a -> (t, c))
--   -> (Delta k -> Delta a -> c -> (Delta t, c))
--   -> Delta (Map k a) -> M.Map k c -> (Delta (UList t), M.Map k c)
-- convertMapTrUnchanged f deriv_f = iterTr convertMapTrUnchangedAtomic
--   where
--     convertMapTrUnchangedAtomic (KeyUpdate _k dk) c
--       | checkEmpty dk = (mempty, c)
--       | otherwise     = error "Key update is not supported"
--     convertMapTrUnchangedAtomic (ValUpdate k da) c
--       = let ck = c M.! k
--             (dt, ck') = deriv_f mempty da ck
--             i = M.findIndex k c
--             c' = M.insert k ck' c
--         in (injDelta (UpdAt i dt), c')
--     convertMapTrUnchangedAtomic (ValInsert k v) c
--       = let (t, ck) = f k v
--             c' = M.insert k ck c
--         in (injDelta (Ins t), c')



-- -- | @Bag a@ is defined to be a mapping from elements to their quanties.
-- newtype Bag a = Bag { unBag :: M.Map a Int }
--   deriving stock Show

-- normalize :: Bag a -> Bag a
-- normalize (Bag a) = Bag $ M.filter (/= 0) a

-- singletonBag :: a -> Bag a
-- singletonBag a = Bag (M.singleton a 1)

-- instance Ord a => Semigroup (Bag a) where
--   Bag as <> Bag bs = normalize $ Bag $  M.unionWith (+) as bs

-- instance Ord a => Monoid (Bag a) where
--   mempty = Bag M.empty

-- instance Ord a => Group (Bag a) where
--   invert (Bag a) = Bag $ M.map negate a

-- instance Ord a => Abelian (Bag a)

-- instance Ord a => Eq (Bag a) where
--   as == bs = unBag (normalize as) == unBag (normalize bs)

-- newtype instance Delta (Bag a) = DeltaBag (GroupChangeWithReplace (Bag a))
--   deriving newtype (Semigroup, Monoid)
--   deriving stock Show

-- instance Ord a => Diff (Bag a) where
--   as /+ DeltaBag (GroupChange bs) = as <> bs
--   _  /+ DeltaBag (Replace bs)     = bs

--   checkEmpty (DeltaBag (GroupChange (Bag as))) = M.null as
--   checkEmpty _                                 = False

-- instance Ord a => DiffMinus (Bag a) where
--   as /- bs = DeltaBag (GroupChange (invert bs <> as))

-- instance Ord a => DiffReplace (Bag a) where
--   replaceTo as = DeltaBag (Replace as)

-- instance Ord a => DiffGroupReplace (Bag a)

-- -- [FIxME] Following implementations are wrong.

-- foldBag :: Group t => (a -> t) -> Bag a -> t
-- foldBag f = foldr ((<>) . h) mempty . M.toList . unBag
--   where
--     h (a , k)  = Data.Group.pow (f a) k


-- data FoldBagC a b c
--   = NothingFB
--   | JustFB  (a -> (b, c), [(c,Int)]) -- ^ Element (c, k) means k-copies of c.


-- -- fromJustFB :: FoldBagC a b c -> [(c, Int)]
-- -- fromJustFB (JustFB x) = x
-- -- fromJustFB _          = error "fromJustFB: NothingFB"

-- foldBagTrUnchangedOpt ::
--   (Group t, DiffGroupReplace t)
--   => (a -> t) -> Delta (Bag a) -> Delta t
-- foldBagTrUnchangedOpt f (DeltaBag (GroupChange   a)) = toGroupDelta $ foldBag f a
-- foldBagTrUnchangedOpt f (DeltaBag (Replace a))       = replaceTo $ foldBag f a


-- foldBagTrUnchanged ::
--   (Group t, DiffGroupReplace t)
--   => Delta (Bag a) -> FoldBagC a t c -> (Delta t, FoldBagC a t c)
-- foldBagTrUnchanged _ NothingFB = error "Impossible"
-- foldBagTrUnchanged (DeltaBag (GroupChange as)) (JustFB (f, cs)) =
--   let (r, cs') = mconcat $ map h $ M.toList $ unBag as
--   in (toGroupDelta r, JustFB (f, cs ++ cs'))
--   where
--     h (a, k) =
--       let (t, c') = f a
--       in (Data.Group.pow t k, [(c',k)])
-- foldBagTrUnchanged (DeltaBag (Replace as)) (JustFB (f, _)) =
--   let (r, cs) = mconcat $ map h $ M.toList $ unBag as
--   in (replaceTo r, JustFB (f, cs))
--   where
--     h (a, k) =
--       let (t, c') = f a
--       in (Data.Group.pow t k, [(c',k)])



-- {-
-- Interesting, if we allow non nil function update, we are not able to handle the case where a bag
-- associates an element a negative quantity.
-- -}
-- foldBagTrChanged ::
--   (Diff t) =>
--   (c -> (Delta t, c)) -> FoldBagC a t c -> (Delta t, FoldBagC a t c)
-- foldBagTrChanged _df NothingFB = error "Impossible"
-- foldBagTrChanged df (JustFB (f, cs)) =
--   let (r,cs') = mconcat $ map h cs
--   in (r, JustFB (changeFunction f df, cs'))
--   where
--     h (c, k)
--       | k < 0 = error "foldBagTrChanged cannot handle negative quantity"
--       | otherwise =
--         let (dt, c') = df c
--         -- following code is wrong: but, how we deal with this?
--         in (mconcat (replicate k dt), [(c',k)])


-- foldBagInit ::
--   Group t =>
--   (a -> (t, c)) -> Bag a -> (t, FoldBagC a t c)
-- foldBagInit f =
--   second (\cs -> JustFB (f, cs)) . foldr ((<>) . h) mempty . M.toList . unBag
--   where
--     h (a, k) =
--       let (t, c) = f a
--       in (Data.Group.pow t k, [(c,k)])

-- foldBagI ::
--   (Group t, DiffGroupReplace t)
--   => PFun IFqS c a t -> (PFun IFqS (FoldBagC a t c) (Bag a) t, ())
-- foldBagI (PFunIFqS (FunCache ic f _)) =
--   case ic of
--     Closed ->
--       (PFunIFqS (FunCache ic
--                   (second (const NothingFB) . foldBagInit f)
--                   (\da c -> (foldBagTrUnchangedOpt (fst . f) da, c))), ())
--     Open ->
--       (PFunIFqS (FunCache ic
--                   (foldBagInit f)
--                   foldBagTrUnchanged), ())


-- foldBagTr ::
--   (Diff t)
--   => Delta (PFun IFqS c a t)
--   -> ()
--   -> (Delta (PFun IFqS (FoldBagC a t c) (Bag a) t), ())
-- foldBagTr (DeltaPFunIFqS (DeltaFunCache isNil df)) _ =
--   if isNil then
--     (DeltaPFunIFqS (DeltaFunCache True $ \c -> (mempty, c)), ())
--   else
--     let df' = foldBagTrChanged df
--     in (DeltaPFunIFqS (DeltaFunCache False df'), ())

-- foldBagC ::
--   (Group t, DiffGroupReplace t) =>
--   IFqS (PFun IFqS c a t) (PFun IFqS (FoldBagC a t c) (Bag a) t)
-- foldBagC = fromFunctionsCode [|| foldBagI ||] [|| foldBagTr ||]

-- myFoldMap :: (Monoid b) => (k -> a -> b) -> M.Map k a -> b
-- myFoldMap f = Data.Foldable.fold . M.mapWithKey f


-- -- mempty element should behave as if there is no such element.
-- newtype Map k a = Map (M.Map k a)
--   deriving newtype (Foldable, Functor, Show)

-- instance (Semigroup a, Ord k) => Semigroup (Map k a) where
--   Map as <> Map bs = Map $ M.unionWith (<>) as bs

-- instance (Semigroup a, Ord k) => Monoid (Map k a) where
--   mempty = Map M.empty

-- instance (Group a, Ord k) => Group (Map k a) where
--   invert (Map m) = Map (M.map invert m)

-- instance (Abelian a, Ord k) => Abelian (Map k a)

-- newtype instance Delta (Map k a) = DeltaMap (GroupChangeWithReplace (Map k a))
--   deriving newtype (Semigroup, Monoid)

-- instance (Ord k, Semigroup a) => Diff (Map k a) where
--   Map mp /+ DeltaMap (GroupChange (Map mp')) = Map (M.unionWith (<>) mp mp')
--   Map _  /+ DeltaMap (Replace     mp)        = mp

--   checkEmpty (DeltaMap (GroupChange (Map mp))) = M.null mp
--   checkEmpty _                                 = False

-- instance (Ord k, Group a) => DiffMinus (Map k a) where
--   mp /- mp' = DeltaMap $ GroupChange $ coerce (invert mp' <> mp)


-- instance (Ord k, Group a) => DiffReplace (Map k a) where
--   replaceTo = DeltaMap . Replace

-- instance (Ord k, Group a) => DiffGroupReplace (Map k a)


-- {-

-- How to incrementalize foldMap?

-- (1) If a function is primitive-like (yielding no change), things would
-- be easier. The change to foldMap f a for the change da to a is given by:

--    foldMap f (a /+ da) = foldMap (fst f) a /+ foldMap (fst f) da

-- The cache for f is ignored.

-- (2) If a function is also changed, we need to keep a Map k [c] to make c
-- available to where f is used. Also, we need to keep track of f itself
-- as it is used in the derivative code.

--    foldMap (f /+ df) (a /+ da) (f', cs) =
--       let (dr, cs') = M.unzip $ M.mapWithKey (first mconcat . unzip $ map df) cs
--           newF = f' /+ df
--           (dr2, cs2) = first Data.Foldable.fold $ M.unzip $ M.mapWithKey newF da
--       in (foldMap f a /+ mconcat dr /+ , (newF, cs'))

-- -}

-- data FoldMapC k a b c
--   = NothingFM
--   | JustFM  ((k, a) -> (b, c)) (M.Map k [c]) -- ^ Element (c, k) means k-copies of c.

-- foldMapTrUnchangedOpt ::
--   (Abelian b, DiffGroupReplace b) =>
--   (k -> a -> b) -> Delta (Map k a) -> Delta b
-- foldMapTrUnchangedOpt f (DeltaMap (GroupChange (Map m))) = toGroupDelta $ myFoldMap f m
-- foldMapTrUnchangedOpt f (DeltaMap (Replace     (Map m))) = replaceTo    $ myFoldMap f m

-- foldMapTrUnchanged ::
--   (Diff b, Ord k, Abelian b, DiffGroupReplace b) =>
--   Delta (Map k a) -> FoldMapC k a b c -> (Delta b, FoldMapC k a b c)
-- foldMapTrUnchanged _ NothingFM = error "Impossible"
-- foldMapTrUnchanged (DeltaMap (GroupChange (Map m))) (JustFM f cs) =
--   let (dr, cs') = ((Data.Foldable.fold . fmap fst) &&& fmap snd) $ M.mapWithKey (curry $ (toGroupDelta *** (:[])) . f) m
--   in (dr, JustFM f (M.unionWith (<>) cs cs'))
-- foldMapTrUnchanged (DeltaMap (Replace (Map m))) (JustFM f _) =
--   let (r, cs) = (Data.Foldable.fold . fmap fst &&& fmap snd) $ M.mapWithKey (curry $ second (:[]) . f) m
--   in (replaceTo r, JustFM f cs)


-- foldMapTrChanged ::
--   (Diff b)
--   => (c -> (Delta b, c))
--   -> FoldMapC k a b c -> (Delta b, FoldMapC k a b c)
-- foldMapTrChanged _  NothingFM = error "Impossible"
-- foldMapTrChanged df (JustFM f cs) =
--   let (dr1, cs1) = first Data.Foldable.fold $ (fmap fst &&& fmap snd) $ fmap (first mconcat . unzip . map df) cs
--       f' = changeFunction f df
--       --      (dr2, cs2) = ((Data.Foldable.fold . fmap fst) &&& fmap snd) $ M.mapWithKey (curry $ second (:[]) . f) m
--   in (dr1 , JustFM f' cs1)

-- foldMapInit ::
--   Abelian b
--   => ((k, a) -> (b, c))
--   -> Map k a -> (b, FoldMapC k a b c)
-- foldMapInit f (Map m) =
--   let (r, cs) = ((Data.Foldable.fold . fmap fst) &&& fmap snd) $ M.mapWithKey (curry $ second (:[]) . f) m
--   in (r, JustFM f cs)


-- foldMapI ::
--   (Abelian b, DiffGroupReplace b, Ord k)
--   => PFun IFqS c (k, a) b -> (PFun IFqS (FoldMapC k a b c) (Map k a) b, ())
-- foldMapI (PFunIFqS (FunCache isNil f _))
--   | Closed <- isNil =
--       (PFunIFqS (FunCache Closed (second (const NothingFM) . foldMapInit f)
--                                  (\da c -> (foldMapTrUnchangedOpt (curry $ fst . f) da, c))), ())
--   | Open <- isNil =
--       (PFunIFqS (FunCache Open
--                   (foldMapInit f)
--                   foldMapTrUnchanged), ())

-- foldMapTr ::
--   (Diff b)
--   => Delta (PFun IFqS c (k, a) b)
--   -> ()
--   -> (Delta (PFun IFqS (FoldMapC k a b c) (Map k a) b), ())
-- foldMapTr (DeltaPFunIFqS (DeltaFunCache isNil df)) _ =
--   if isNil then
--     (DeltaPFunIFqS (DeltaFunCache True $ \c -> (mempty, c)), ())
--   else
--     let df' = foldMapTrChanged df
--     in (DeltaPFunIFqS (DeltaFunCache False df'), ())

-- foldMapC ::
--   (Ord k, Abelian b, DiffGroupReplace b) =>
--   IFqS (PFun IFqS c (k,a) b) (PFun IFqS (FoldMapC k a b c) (Map k a) b)
-- foldMapC = fromFunctionsCode [|| foldMapI ||] [|| foldMapTr ||]
