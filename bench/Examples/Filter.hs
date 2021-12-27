{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module Examples.Filter where

import           Control.DeepSeq

import           Data.Coerce                         (coerce)
import qualified Data.Sequence                       as S
import           Data.String
import           Prelude                             hiding (id, (.))
import qualified Prelude
import qualified Text.Show                           as TS

import           Data.Delta
import           Data.JoinList


import           Data.IFq
import           Data.Incrementalized
import qualified Data.Incrementalized.Bool           as I
import qualified Data.Incrementalized.Fixed          as I
import qualified Data.Incrementalized.Seq            as IS
import           Data.Typeable

import           Data.Code                           (Code)
import           Data.Foldable                       (toList)
import           Data.IFqTU                          (IFqTU)
import           Data.Incrementalized.Either         (Delta (DEitherInPlace),
                                                      SumTerm, eitherF)
import           Data.Interaction                    (Interaction (..))
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
  deriving stock Eq
-- data Attr = Attr !(I.Fixed String) !MyString
--  deriving stock (Show , Eq)

instance NFData Tree where
  rnf (Elem s ts) = rnf (s, IS.unSeq ts)
  rnf (Attr s v)  = rnf (s, IS.unSeq v)
  rnf (Text v)    = rnf (IS.unSeq v)

instance Show Tree where
  showsPrec k (Elem s ts) = TS.showParen (k > 9) $
    TS.showString "Elem" . TS.showChar ' ' . shows (I.getFixed s) . TS.showChar ' ' . TS.showString "(" . TS.showString "fromList" . TS.showChar ' ' . TS.showListWith shows (toList ts) . TS.showString ")"
  showsPrec k (Attr s v) = TS.showParen (k > 9) $
    TS.showString "Attr" . TS.showChar ' ' . shows (I.getFixed s) . TS.showChar ' ' . TS.shows (map unMyChar $ toList v)
  showsPrec k (Text s)   = TS.showParen (k > 9) $
    TS.showString "Text" . TS.showChar ' ' . TS.shows (map unMyChar $ toList s)

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

instance NFData MyChar where
  rnf (MyChar c) = rnf c

unMyChar :: MyChar -> Char
unMyChar (MyChar c) = c

data instance Delta MyChar = DReplaceChar !MyChar | DKeepChar
  deriving stock Show

instance NFData (Delta MyChar) where
  rnf (DReplaceChar _) = ()
  rnf DKeepChar        = ()

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
  deriving stock Show
  deriving newtype NFData
instance Semigroup (Delta Tree) where
  (<>) = coerce ((<>) :: JoinList (AtomicDelta Tree) -> JoinList (AtomicDelta Tree) -> JoinList (AtomicDelta Tree))

instance Monoid (Delta Tree) where
  mempty = coerce (mempty :: JoinList (AtomicDelta Tree))

instance Diff Tree where
  (/+) = applyDeltaFromHasAtomicDelta
  checkEmpty = checkEmptyFromAtomicDelta


instance HasAtomicDelta Tree where
  -- This change structure is not complete in the sense that
  -- there is not necessarly a change dt for given two trees t1 and t2 such that
  -- t1 /+ dt = t2.
  data instance AtomicDelta Tree
    = DModChildren (Delta (IS.Seq Tree))
    | DModTag  String
    | DModAttr String (Delta MyString) -- change the attribute's value
    | DModText (Delta MyString) -- modifies a string
    deriving stock Show

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

{-
[Note]

Currently, we consider index-based update operations. On the one hand, such
updates are hard to write in general. On the other hand, indexed-based updates
naturally fit for lists, and hence for rose-trees whose children are given by
lists.

What kind of lists we should consider to support updates such as "insert ...
under /b/c"? There are a few possible approaches:

  - A list should support a mass update operation: SAll da which applies da to
    all the elements uniformly. Handling such an operation would be costly
    because it updates every element in a list at once. Also, we need to prepare
    an update for a node that perform an update conditionally.

  - Instead, we just support a conditional update operation such as: SAllWith da
    p that applies da to all the elements that satisfies p. While in this
    approach we need to change the change structure for nodes, how to handle
    changes for lists would become much more complicated than the previous
    approach.

Anyway, our concern here is rather on how to combine primitives, instead of how
to define primitives.

-}


instance NFData (AtomicDelta Tree) where
  rnf (DModChildren dt) = rnf dt
  rnf (DModTag s)       = rnf s
  rnf (DModAttr s v)    = rnf (s, v)
  rnf (DModText s)      = rnf s

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

{-
[Note]

An observation is that it is often less meaningful to have an incrementalized
version of a predicate. For a predicate `p :: a -> Bool`, often the best we can
is to recompute `p` for `a /+ da` and produce a delta by `p (a /+ da) - p a`,
which is very default for all functions. Thus, we want to have such trivial
lifting typically for predicate-like functions.

(2021-12-17) Now, they are provided as 'trivialIncrementalization***" in
Data.Incrementalized.

We could do some optimization for our case, leveraging the fact that the
function that updates on `Tree` cannot change the top-level constructor. So, we
only store the cache when the input has a relevant form to a predicate.

-}

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
hasAttrValTrA _ _ _ c = (mempty, c)

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

-- textOfF :: (PFunTerm IFqS t, App2 IFqS t e) => String -> EFilter e
-- textOfF s = IS.filterF (isTextOfF s) Prelude.. keepF

textOfF :: (App2 IFqS t e, SumTerm IFqS t DiffMinus, I.IfTerm IFqS t DiffMinus) => String -> EFilter e
textOfF s = ifTxtF (\str e -> I.if_ (liftPredicate [|| \ss -> s == toString ss ||] str) (keepF e) IS.emptyF) noneF


(/>) :: (App2 IFqS t e, PFunTerm IFqS t) => EFilter e -> EFilter e -> EFilter e
f /> g = f >>> childrenF >>> g

withF :: (App2 IFqS t e, PFunTerm IFqS t) => EFilter e -> EFilter e -> EFilter e
f `withF` g = IS.filterF (I.notF Prelude.. IS.nullF Prelude.. g) Prelude.. f

liftPredicate :: (App IFqS e, Diff a, Typeable a) => Code (a -> Bool) -> e a -> e Bool
liftPredicate p = lift (trivialIncrementalizationCode p)

q1Filter :: forall t e. (App2 IFqS t e, SumTerm IFqS t DiffMinus, I.IfTerm IFqS t DiffMinus, PFunTerm IFqS t) => EFilter e
q1Filter = mkElemF "bib" [
   keepF />
    ((tagF "book" `withF` byAW `withF` after1991)
      >>> mkElemF "book" [
        keepF /> attrF "year",
        keepF /> tagF "title"
     ])
   ]
  where
    byAW :: EFilter e
    byAW =
      keepF /> tagF "publisher" /> textOfF "Addison-Wesley"

    after1991 :: EFilter e
    after1991 =
      keepF /> ifAttrF "year" (\s a ->
                   I.if_ (liftPredicate [|| \str ->
                                            (read (toString str) :: Int) > 1991 ||] s)
                         (IS.singletonF a) IS.emptyF) noneF

toString :: MyString -> String
toString = map unMyChar . Data.Foldable.toList

elm :: I.Fixed String -> [Tree] -> Tree
elm s ts = Elem s $ IS.fromList ts

exampleInput :: Tree
exampleInput =
  elm "bib" [
    elm "book" [
      Attr "year" "1994",
      elm "title" [ Text "TCP/IP Illustrated" ],
      elm "author" [ elm "last" [ Text "Stevens" ], elm "first" [ Text "W." ] ],
      elm "publisher" [ Text "Addison-Wesley" ],
      elm "price" [ Text "65.95" ] ],
    elm "book" [
      Attr "year" "1992",
      elm "title" [ Text "Advanced Programming in the Unix environment" ],
      elm "author" [ elm "last" [ Text "Stevens" ], elm "first" [ Text "W." ] ],
      elm "publisher" [ Text "Addison-Wesley" ],
      elm "price" [ Text "65.95" ] ],
    elm "book" [
      Attr "year" "2000",
      elm "title" [ Text "Data on the Web" ],
      elm "author" [ elm "last" [ Text "Abiteboul" ], elm "first" [ Text "Serge" ] ],
      elm "author" [ elm "last" [ Text "Buneman" ], elm "first" [ Text "Peter" ] ],
      elm "author" [ elm "last" [ Text "Suciu" ], elm "first" [ Text "Dan" ] ],
      elm "publisher" [ Text "Morgan Kaufmann Publishers" ],
      elm "price" [ Text "39.95" ] ],
    elm "book" [
      Attr "year" "1999",
      elm "title" [ Text "The Economics of Technology and Content for Digital TV" ],
      elm "editor" [ elm "last" [ Text "Gerbarg" ], elm "first" [ Text "Darcy" ], elm "affiliation" [Text "CITI"] ],
      elm "publisher" [ Text "Kluwer Academic Publishers" ],
      elm "price" [ Text "129.95" ] ]
  ]

largerInput :: Tree
largerInput =
    elm "bib" $ [
      elm "book" [
        Attr "year" "1994",
        elm "title" [ Text "TCP/IP Illustrated" ],
        elm "author" [ elm "last" [ Text "Stevens" ], elm "first" [ Text "W." ] ],
        elm "publisher" [ Text "Addison-Wesley" ],
        elm "price" [ Text "65.95" ] ],
      elm "book" [
        Attr "year" "1992",
        elm "title" [ Text "Advanced Programming in the Unix environment" ],
        elm "author" [ elm "last" [ Text "Stevens" ], elm "first" [ Text "W." ] ],
        elm "publisher" [ Text "Addison-Wesley" ],
        elm "price" [ Text "65.95" ] ]
    ] ++ take 100 (dummyBooks 0)


dummyBooks :: Int -> [Tree]
dummyBooks n =
  elm (fromString "book") [
    Attr "year" (fromString $ show $ 1990 + n `mod` 4),
    elm "title" [ Text $ fromString $ "dummy book" ++ show n ],
    elm "publisher" [ Text (if n `mod` 3 == 0 then "Addison-Wesley" else "Dummy Publisher") ],
    elm "price" [ Text "99.95" ]
  ] : dummyBooks (n + 1)


exampleDelta :: Delta Tree
exampleDelta = Control.DeepSeq.force $
  injDelta $ DModChildren $ injDelta $ IS.SRep 0 $
  injDelta $ DModChildren $ injDelta $ IS.SRep 1 $
  injDelta $ DModChildren $ injDelta $ IS.SRep 0 $
  injDelta $ DModText $ injDelta $ IS.SIns (length ("TCP/IP Illustrated" :: String)) " (Second Edition)"

exampleDeltas :: Int -> [Delta Tree]
exampleDeltas n = Control.DeepSeq.force $
  concatMap (\t -> [ h t , del]) (take n $ dummyBooks 0)
  where
    del = injDelta $ DModChildren $ injDelta $ IS.SDel 0 1
    h x = injDelta $ DModChildren $ injDelta $ IS.SIns 0 (IS.Seq $ S.singleton x)

qq1 :: Code (Tree -> (Tree, Interaction (Delta Tree) (Delta Tree)))
qq1 = compileCode $ runMonoWith (Proxy :: Proxy IFqTU) (unsingletonF . q1Filter)


--- >>> exampleDelta
-- DTree (fromList [DModChildren (DeltaSeq (fromList [SRep 0 (DTree (fromList [DModChildren (DeltaSeq (fromList [SRep 1 (DTree (fromList [DModChildren (DeltaSeq (fromList [SRep 0 (DTree (fromList [DModText (DeltaSeq (fromList [SIns 18 (fromList [MyChar ' ',MyChar '(',MyChar 'S',MyChar 'e',MyChar 'c',MyChar 'o',MyChar 'n',MyChar 'd',MyChar ' ',MyChar 'E',MyChar 'd',MyChar 'i',MyChar 't',MyChar 'i',MyChar 'o',MyChar 'n',MyChar ')'])]))]))]))]))]))]))]))])

-- HLS goes to panic for the following code. So, I manually pasted the results from GHCi.
-- To do so, we need TemplateHaskell and TypeFamilies.
-- >>> q1 = $$( qq1 )
-- >>> let (r, i) = q1 exampleInput
-- >>> r
-- >>> exampleInput /+ exampleDelta
-- >>> fst $ runInteraction i exampleDelta
-- >>> r /+ (fst $ runInteraction i exampleDelta) == fst (q1 $ exampleInput /+ exampleDelta)
-- Elem "bib" (fromList [Elem "book" (fromList [Attr "year" "1994",Elem "title" (fromList [Text "TCP/IP Illustrated"])]),Elem "book" (fromList [Attr "year" "1992",Elem "title" (fromList [Text "Advanced Programming in the Unix environment"])])])
-- Elem "bib" (fromList [Elem "book" (fromList [Attr "year" "1994",Elem "title" (fromList [Text "TCP/IP Illustrated (Second Edition)"]),Elem "author" (fromList [Elem "last" (fromList [Text "Stevens"]),Elem "first" (fromList [Text "W."])]),Elem "publisher" (fromList [Text "Addison-Wesley"]),Elem "price" (fromList [Text "65.95"])]),Elem "book" (fromList [Attr "year" "1992",Elem "title" (fromList [Text "Advanced Programming in the Unix environment"]),Elem "author" (fromList [Elem "last" (fromList [Text "Stevens"]),Elem "first" (fromList [Text "W."])]),Elem "publisher" (fromList [Text "Addison-Wesley"]),Elem "price" (fromList [Text "65.95"])]),Elem "book" (fromList [Attr "year" "2000",Elem "title" (fromList [Text "Data on the Web"]),Elem "author" (fromList [Elem "last" (fromList [Text "Abiteboul"]),Elem "first" (fromList [Text "Serge"])]),Elem "author" (fromList [Elem "last" (fromList [Text "Buneman"]),Elem "first" (fromList [Text "Peter"])]),Elem "author" (fromList [Elem "last" (fromList [Text "Suciu"]),Elem "first" (fromList [Text "Dan"])]),Elem "publisher" (fromList [Text "Morgan Kaufmann Publishers"]),Elem "price" (fromList [Text "39.95"])]),Elem "book" (fromList [Attr "year" "1999",Elem "title" (fromList [Text "The Economics of Technology and Content for Digital TV"]),Elem "editor" (fromList [Elem "last" (fromList [Text "Gerbarg"]),Elem "first" (fromList [Text "Darcy"]),Elem "affiliation" (fromList [Text "CITI"])]),Elem "publisher" (fromList [Text "Kluwer Academic Publishers"]),Elem "price" (fromList [Text "129.95"])])])
-- DTree (fromList [DModChildren (DeltaSeq (fromList [SRep 0 (DTree (fromList [DModChildren (DeltaSeq (fromList [SRep 1 (DTree (fromList [DModChildren (DeltaSeq (fromList [SRep 0 (DTree (fromList [DModText (DeltaSeq (fromList [SIns 18 (fromList [MyChar ' ',MyChar '(',MyChar 'S',MyChar 'e',MyChar 'c',MyChar 'o',MyChar 'n',MyChar 'd',MyChar ' ',MyChar 'E',MyChar 'd',MyChar 'i',MyChar 't',MyChar 'i',MyChar 'o',MyChar 'n',MyChar ')'])]))]))]))]))]))]))]))])
-- True




{-
[Note]

HaXML provides two important functions that investigate attributes and texts.

    ifTxt  :: (String -> CFilter i) -> CFilter i -> CFilter i
    ifFind :: String ->(String -> CFilter i) -> CFilter i -> CFilter i

Intuitively, `ifTxt yes no` runs `yes s` if an input is a text node whose
content is `s`, and `no` otherwise. Function `ifFind k yes no` has a similar
behavior but it test an input has an attribute of label `k` and the `yes` filter
will be applied to its corresponding value.

Of course, we do not want to directly support these function as they share some
common work. So, we may provide a generic destructor for sum types (`Either`, in
Haskell).

    eitherF :: ... => e (Either a b) -> (e a -> e r) -> (e b -> e r) -> e r

-}

checkTextInit :: Tree -> (Either (MyString, Tree) Tree, Bool)
checkTextInit t@(Text s) = (Left (s, t), True)
checkTextInit t          = (Right t, True)

checkTextTrA :: AtomicDelta Tree -> Bool -> (Delta (Either (MyString, Tree) Tree), Bool)
checkTextTrA dt@(DModText t) True = (DEitherInPlace (PairDelta t $ injDelta dt) mempty , True)
checkTextTrA dt              True = (DEitherInPlace (PairDelta mempty $ injDelta dt) mempty, True)
checkTextTrA dt             False = (DEitherInPlace mempty (injDelta dt), False)

checkTextC :: IFqS Tree (Either (MyString, Tree) Tree)
checkTextC = fromFunctionsCode [|| checkTextInit ||] [|| iterTr checkTextTrA ||]

ifTxtF :: (App2 IFqS t e, SumTerm IFqS t DiffMinus) => (e MyString -> EFilter e) -> EFilter e -> EFilter e
ifTxtF f g e = eitherF (lift checkTextC e) (\x -> f (fstF x) (sndF x)) g

checkAttrInit :: String -> Tree -> (Either (MyString , Tree) Tree, Bool)
checkAttrInit s t@(Attr k v) | s == I.getFixed k = (Left (v, t), True)
checkAttrInit _ t                                = (Right t, False)

checkAttrTrA :: String -> AtomicDelta Tree -> Bool -> (Delta (Either (MyString, Tree) Tree), Bool)
checkAttrTrA s dt@(DModAttr k dv) True | s == k = (DEitherInPlace (PairDelta dv (injDelta dt)) mempty, True)
checkAttrTrA _ dt True = (DEitherInPlace (PairDelta mempty (injDelta dt)) mempty, True)
checkAttrTrA _ dt False = (DEitherInPlace mempty (injDelta dt), False)

checkAttrC :: String -> IFqS Tree (Either (MyString, Tree) Tree)
checkAttrC s = fromFunctionsCode [|| checkAttrInit s ||] [|| iterTr (checkAttrTrA s) ||]

ifAttrF :: (App2 IFqS t e, SumTerm IFqS t DiffMinus) => String -> (e MyString -> EFilter e) -> EFilter e -> EFilter e
ifAttrF s f g e = eitherF (lift (checkAttrC s) e) (\x -> f (fstF x) (sndF x)) g

unsingletonInit :: IS.Seq a -> a
unsingletonInit (IS.Seq s@(a S.:<| _)) | S.length s == 1 = a
unsingletonInit _                    = error "unsingletonF: non-singleton"

unsingletonTrA :: Diff a => AtomicDelta (IS.Seq a) -> Delta a
unsingletonTrA (IS.SRep n da)
  | n == 0 = da
  | otherwise = error $ "unsingletonF: out of range " ++ show n
unsingletonTrA (IS.SDel i n)
  | i > 0 || n == 0 = mempty
  | otherwise       = error "unsingletonF: deletion of more than zero element is not allowed"
unsingletonTrA (IS.SIns _ (IS.Seq s))
  | S.null s  = mempty
  | otherwise = error "unsingletonF: insertion is not allowed"
unsingletonTrA (IS.SRearr _ _ _) = mempty


unsingletonC :: (Diff a) => IFqS (IS.Seq a) a
unsingletonC = fromStatelessCode (\a -> [|| unsingletonInit $$a ||]) (\da -> [|| iterTrStateless unsingletonTrA $$da ||])

unsingletonF :: (Typeable a, Diff a, App IFqS e) => e (IS.Seq a) -> e a
unsingletonF = lift unsingletonC

-- Filters using lists for comparison

type RFilter = Tree -> [Tree]

keepR :: RFilter
keepR = (:[])

noneR :: RFilter
noneR = const []

(>>>#) :: RFilter -> RFilter -> RFilter
f >>># g = concatMap g . f

childrenR :: RFilter
childrenR (Elem _ ts) = toList ts -- conversion happens
childrenR _           = []

tagR :: String -> RFilter
tagR s t@(Elem s' _) | s == I.getFixed s' = [t]
tagR _ _ = []

attrR :: String -> RFilter
attrR s t@(Attr s' _) | s == I.getFixed s' = [t]
attrR _ _ = []

mkElemR :: String -> [RFilter] -> RFilter
mkElemR s rs = keepR . Elem (I.Fixed s) . IS.fromList . cats rs
  where
    cats ts e = concatMap ($ e) ts

withR :: RFilter -> RFilter -> RFilter
f `withR` g = filter (not . null . g) . f

ifTxtR :: (MyString -> RFilter) -> RFilter -> RFilter
ifTxtR f _ t@(Text s) = f s t
ifTxtR _ g t          = g t

ifAttrR :: String -> (MyString -> RFilter) -> RFilter -> RFilter
ifAttrR s f _ t@(Attr s' v) | s == I.getFixed s' = f v t
ifAttrR _ _ g t                                  = g t

(/>#) :: RFilter -> RFilter -> RFilter
f /># g = f >>># childrenR >>># g

q1FilterR :: RFilter
q1FilterR = mkElemR "bib" [
   keepR />#
    ((tagR "book" `withR` byAW `withR` after1991)
      >>># mkElemR "book" [
        keepR /># attrR "year",
        keepR /># tagR "title"
     ])
   ]
  where
    byAW =
      keepR /># tagR "publisher" /># textOfR "Addison-Wesley"

    after1991 =
      keepR /># ifAttrR "year" (\s -> if (read (toString s) :: Int) > 1991 then keepR else noneR) noneR

    textOfR str = ifTxtR (\s -> if toString s == str then keepR else noneR) noneR

q1R :: Tree -> Tree
q1R = unsingleton . q1FilterR
  where
    unsingleton [a] = a
    unsingleton _   = error "unsingleton: expected singleton"
