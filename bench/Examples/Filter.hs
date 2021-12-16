{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleContexts   #-}
module Examples.Filter where

import           Data.Coerce                         (coerce)
import qualified Data.List
import qualified Data.Sequence                       as S
import           Data.String

import           Data.Delta
import           Data.JoinList


import           Data.IFq
import           Data.Incrementalized
import qualified Data.Incrementalized.Bool           as I
import qualified Data.Incrementalized.Fixed          as I
import qualified Data.Incrementalized.Seq            as IS
import           Data.Typeable

import           Data.Foldable                       (toList)
import           Language.Unembedding
import           Language.Unembedding.PseudoFunction

{-
HaXML-like filters are good examples for unembedding-based approach, because

 * HaXML-filters are indeed functions of type Tree -> [Tree]. Thus,
   the library uses a lot of higher-order functions, i.e., combinators
   that manipulate HaXML filters.

 * It essentially involves a data structures---rose trees.

Let us consider a following version of labeled rose-trees.
-}

data Tree = Elem !(I.Fixed String) !(IS.Seq Tree)
          | Attr !(I.Fixed String) !MyString
          | Text !MyString
  deriving stock (Show , Eq)
-- data Attr = Attr !(I.Fixed String) !MyString
--  deriving stock (Show , Eq)

{-
Intuitively, a fragment `<p class="c">Hey <em>You</em></p>` is represented as:
-}

exampleTree :: Tree
exampleTree = Elem "p" (IS.fromList [Attr "class" "c", Text "Hey ", Elem "em" $ IS.fromList [Text "You"]])

type Filter = Tree -> IS.Seq Tree

type MyString = IS.Seq MyChar

instance IsString (IS.Seq MyChar) where
  fromString = IS.fromList Prelude.. map MyChar

newtype MyChar = MyChar Char
  deriving stock (Show, Eq)

data instance Delta MyChar = DReplaceChar !MyChar | DKeepChar

instance Semigroup (Delta MyChar) where
  _ <> a = a

instance Monoid (Delta MyChar) where
  mempty = DKeepChar

instance Diff MyChar where
  s /+ DKeepChar      = s
  _ /+ DReplaceChar s = s

  checkEmpty DKeepChar = True
  checkEmpty _         = False

{-
Then, how we can design changes? A conjecture is that XML is processed
by navigating elements from the room. So, adding elements to child
would be better than addition constructors. So, we may prepare:
-}


newtype instance Delta Tree = DTree (JoinList (AtomicDelta Tree))

instance Semigroup (Delta Tree) where
  (<>) = coerce ((<>) :: JoinList (AtomicDelta Tree) -> JoinList (AtomicDelta Tree) -> JoinList (AtomicDelta Tree))

instance Monoid (Delta Tree) where
  mempty = coerce (mempty :: JoinList (AtomicDelta Tree))

instance Diff Tree where
  (/+) = applyDeltaFromHasAtomicDelta
  checkEmpty = checkEmptyFromAtomicDelta

-- insAt :: Int -> a -> [a] -> [a]
-- insAt 0  b as       = b : as
-- insAt _n b []       = [b] -- _n > 0
-- insAt n  b (a : as) = a : insAt (n - 1) b as

-- deleteAt :: Int -> [a] -> [a]
-- deleteAt 0 (_ : as) = as
-- deleteAt n (a : as) = a : deleteAt (n-1) as
-- deleteAt _ []       = error "deleteAt: empty list"

-- lookupAttr :: String -> [Attr] -> Maybe MyString
-- lookupAttr _ [] = Nothing
-- lookupAttr k (Attr k' v' : as)
--   | k == I.getFixed k'   = Just v'
--   | otherwise = lookupAttr k as

-- modifyAttr :: String -> [Attr] -> (MyString -> MyString) -> [Attr]
-- modifyAttr _k [] _u = []
-- modifyAttr k (Attr k' v' : as) u
--   | k == I.getFixed k'   = Attr k' (u v') : as
--   | otherwise = Attr k' v' : modifyAttr k as u

instance HasAtomicDelta Tree where
  -- This change structure is not complete in the sense that
  -- there is not necessarly a change dt for given two trees t1 and t2 such that
  -- t1 /+ dt = t2.
  data instance AtomicDelta Tree
    = DModChildren (Delta (IS.Seq Tree))
    | DModTag  String
    --  | DInsAttr Attr         -- insert an attribute
    --  | DDelAttr String       -- delete an attribute by its name
    | DModAttr String (Delta MyString) -- change the attribute's value
    | DModText (Delta MyString) -- modifies a string
    --  | DElem    String     -- enclose it by an element
    --  | DPick    Int          -- promote a child as a root

  injDelta = DTree Prelude.. pure
  monoidMap f (DTree as) = foldMap f as

  applyAtomicDelta t0 (DModChildren dt) =
    case t0 of
      Elem tag ts ->
        Elem tag (ts /+ dt)
      _ ->
        t0
  applyAtomicDelta t0 (DModTag tag') = case t0 of
    Elem _ ts -> Elem (I.Fixed tag') ts
    _         -> t0
  -- applyAtomicDelta t0 (DInsAttr attr) =
  --   case t0 of
  --     Elem tag attrs ts -> Elem tag (attr : attrs) ts
  --     _                 -> t0
  -- applyAtomicDelta t0 (DModAttr key ds) =
  --   case t0 of
  --     Elem tag attrs ts -> Elem tag (modifyAttr key attrs $ \s -> s /+ ds) ts
  --     _                 -> t0
  applyAtomicDelta t0 (DModAttr key dval) = case t0 of
    Attr _ val -> Attr (I.Fixed key) (val /+ dval)
    _          -> t0
  -- applyAtomicDelta t0 (DDelAttr key) =
  --   case t0 of
  --     Elem tag attrs ts -> Elem tag (filter (\(Attr k _) -> I.getFixed k == key) attrs) ts
  --     _                 -> t0
  applyAtomicDelta t0 (DModText ds) =
    case t0 of
      Text s -> Text (s /+ ds)
      _      -> t0
  -- applyAtomicDelta t0 (DElem tag) = Elem (I.Fixed tag) [] (IS.fromList [t0])
  -- applyAtomicDelta t0 (DPick i) =
  --   case t0 of
  --     Elem _tag _attrs ts
  --       | 0 <= i && i < length ts ->
  --           IS.unSeq ts `S.index` i
  --     _ ->
  --       t0

children :: Filter
children (Elem _ ts) = ts
children _           = IS.fromList []


{-
childrenTrA (DModChildren td) = td      if the original t is Elem
                              = mempty  otherwise
childrenTrA _                 = mempty
-}

childrenInit :: Tree -> (IS.Seq Tree, Bool)
childrenInit (Elem _ ts) = (ts, True)
childrenInit _           = (IS.fromList [], False)

childrenTrA :: AtomicDelta Tree -> Bool -> (Delta (IS.Seq Tree), Bool)
childrenTrA (DModChildren td) isElm
  | isElm    = (td, isElm)
  | otherwise = (mempty, isElm)
childrenTrA _ isElm = (mempty, isElm)

childrenC :: IFqS Tree (IS.Seq Tree)
childrenC = fromFunctionsCode [|| childrenInit ||] [|| iterTr childrenTrA ||]

childrenF :: App IFqS e => EFilter e
childrenF = lift childrenC

type EFilter e = e Tree -> e (IS.Seq Tree)

concatMapF ::
  (Diff a, Typeable a, Diff b, Typeable b, PFunTerm IFqS t, App2 IFqS t e)
  => (e a -> e (IS.Seq b)) -> e (IS.Seq a) -> e (IS.Seq b)
concatMapF f = IS.concatF Prelude.. IS.mapF f

(>>>) :: (PFunTerm IFqS t, App2 IFqS t e) => EFilter e -> EFilter e -> EFilter e
(>>>) f1 f2 x = concatMapF f2 (f1 x)

keepF :: (Diff a, Typeable a, App IFqS e) => e a -> e (IS.Seq a)
keepF = IS.singletonF

noneF :: (Diff b, Typeable b, App IFqS e) => e a -> e (IS.Seq b)
noneF = const IS.emptyF

isElem :: Tree -> Bool
isElem (Elem _ _) = True
isElem _          = False

isText :: Tree -> Bool
isText (Text _) = True
isText _        = False

isAttr :: Tree -> Bool
isAttr (Attr _ _) = True
isAttr _          = False

attrOf :: String -> Tree -> Bool
attrOf s (Attr k _) | s == I.getFixed k = True
attrOf _ _ = False

tagOf :: String -> Tree -> Bool
tagOf s (Elem k _) | s == I.getFixed k = True
tagOf _ _ = False

isElemF :: (App IFqS e) => e Tree -> e Bool
isElemF = lift isElemC
  where
    isElemC :: IFqS Tree Bool
    isElemC = fromStatelessCode (\t -> [|| isElem $$t ||]) (const [|| mempty ||])

textOfInit :: String -> Tree -> (Bool, Maybe MyString)
textOfInit s (Text (IS.Seq ss)) = (coerce (toList ss) == s, Just (IS.Seq ss))
textOfInit _ _                  = (False, Nothing)

textOfTrA ::
  String
  -> AtomicDelta Tree
  -> Maybe MyString
  -> (Delta Bool, Maybe MyString)
textOfTrA s (DModText ds) (Just s0) =
  let
    b0 = coerce (toList s0) == s
    b = coerce (toList $ s0 /+ ds) == s
  in (b /- b0, Just (s0 /+ ds))
textOfTrA _ _ c = (mempty, c)




hasTagOfInit :: String -> Tree -> (Bool, Maybe String)
hasTagOfInit s (Elem k _) = (s == I.getFixed k, Just (I.getFixed k))
hasTagOfInit _ _          = (False, Nothing)

hasTagOfTr :: String -> AtomicDelta Tree -> Maybe String -> (Delta Bool, Maybe String)
hasTagOfTr s (DModTag t) (Just tOld) =
  (if (s == t) == (s == tOld) then I.DBKeep else I.DBNot, Just t)
hasTagOfTr _ _ c  = (mempty, c)

hasTagOfF :: App IFqS e => String -> e Tree -> e Bool
hasTagOfF s = lift (fromFunctionsCode [|| hasTagOfInit s ||] [|| iterTr (hasTagOfTr s) ||])

hasAttrOfInit :: String -> Tree -> (Bool, Maybe String)
hasAttrOfInit s (Attr k _) = (s == I.getFixed k, Just (I.getFixed k))
hasAttrOfInit _ _          = (False, Nothing)

hasAttrOfTr :: String -> AtomicDelta Tree -> Maybe String -> (Delta Bool, Maybe String)
hasAttrOfTr s (DModAttr t _) (Just tOld) =
  (if (s == t) == (s == tOld) then I.DBKeep else I.DBNot, Just t)
hasAttrOfTr _ _ c = (mempty,c )

hasAttrValInit :: String -> String -> Tree -> (Bool, Maybe (String, MyString))
hasAttrValInit sk sv (Attr k v) = (b, Just (I.getFixed k, v))
  where
    b = (sk == I.getFixed k) &&
        (sv == coerce (toList v))
hasAttrValInit _ _ _ = (False, Nothing)

hasAttrValTrA ::
  String -> String
  -> AtomicDelta Tree
  -> Maybe (String, MyString)
  -> (Delta Bool, Maybe (String, MyString))
hasAttrValTrA sk sv (DModAttr k dv) (Just (k0, v0)) =
  (b /- b0, Just (k, v) )
  where
    v  = v0 /+ dv
    b0 = (sk == k0) &&
         (sv == coerce (toList v0))
    b  = (sk == k) &&
         (sv == coerce (toList v))


hasAttrOfF :: App IFqS e => String -> e Tree -> e Bool
hasAttrOfF s = lift (fromFunctionsCode [|| hasAttrOfInit s ||] [|| iterTr (hasAttrOfTr s) ||])

hasAttrValOfF :: App IFqS e => String -> String -> e Tree -> e Bool
hasAttrValOfF sk sv = lift (fromFunctionsCode [|| hasAttrValInit sk sv ||] [|| iterTr (hasAttrValTrA sk sv) ||])


isTextOfF :: App IFqS e => String -> e Tree -> e Bool
isTextOfF s = lift (fromFunctionsCode [|| textOfInit s ||] [|| iterTr (textOfTrA s) ||])

-- mkElemF :: App IFqS e => String -> [EFilter e] -> EFilter e

makeElemInit :: String -> IS.Seq Tree -> Tree
makeElemInit s = Elem (I.Fixed s)

makeElemTr ::  Delta (IS.Seq Tree) -> Delta Tree
makeElemTr ds = injDelta (DModChildren ds)

makeElemC :: String -> IFqS (IS.Seq Tree) Tree
makeElemC s =
  fromStatelessCode
  (\a -> [|| makeElemInit s $$a ||])
  (\da -> [|| makeElemTr $$da ||])

makeElemF :: (App IFqS e) => String -> e (IS.Seq Tree) -> e Tree
makeElemF s = lift (makeElemC s)

-- derived filters

mkElemF :: App IFqS e => String -> [EFilter e] -> EFilter e
mkElemF s cs =
  keepF Prelude.. makeElemF s Prelude.. catF cs

catF :: App IFqS e => [EFilter e] -> EFilter e
catF []     = noneF
catF [x]    = x
catF (x:xs) = \e -> IS.appendF (x e) (catF xs e)

childrenByF :: (PFunTerm IFqS t, App2 IFqS t e) => EFilter e -> EFilter e
childrenByF f = f >>> childrenF

elmF :: (PFunTerm IFqS t, App2 IFqS t e) => EFilter e
elmF = IS.filterF isElemF Prelude.. keepF

tagF :: (PFunTerm IFqS t, App2 IFqS t e) => String -> EFilter e
tagF s = IS.filterF (hasTagOfF s) Prelude.. keepF

attrF :: (PFunTerm IFqS t, App2 IFqS t e) => String -> EFilter e
attrF s = IS.filterF (hasAttrOfF s) Prelude.. keepF

attrvalF :: (PFunTerm IFqS t, App2 IFqS t e) => String -> String -> EFilter e
attrvalF s v = IS.filterF (hasAttrValOfF s v) Prelude.. keepF

textOfF :: (PFunTerm IFqS t, App2 IFqS t e) => String -> EFilter e
textOfF s = IS.filterF (isTextOfF s) Prelude.. keepF



(/>) :: (App2 IFqS t e, PFunTerm IFqS t) => EFilter e -> EFilter e -> EFilter e
f /> g = f >>> childrenF >>> g

withF :: (App2 IFqS t e, PFunTerm IFqS t) => EFilter e -> EFilter e -> EFilter e
f `withF` g = IS.filterF (I.notF Prelude.. IS.nullF Prelude.. g) Prelude.. f


q1 :: (App2 IFqS t e, PFunTerm IFqS t) => EFilter e
q1 = mkElemF "bib" [ keepF /> (tagF "book" `withF` byAW  >>> h) ]
  where
    byAW =
      keepF /> tagF "publisher" /> textOfF "Addision-Wesley"

    h = mkElemF "book"
        [ keepF /> attrF "year",
          keepF /> tagF "title" ]
        `withF`
        keepF /> attrvalF "year" "1991"
        -- `withF`
        -- keepF /> tagF "publisher" /> ifTxtF _ noneF
        -- `withF`
        -- keepF /> ifFindF "year" _


