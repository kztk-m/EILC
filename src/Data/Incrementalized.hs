{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
module Data.Incrementalized
  (
    IncrementalizedQ(..),

    fromStatelessCode, fromFunctionsCode, compileCode, trivialIncrementalizationCode,
    fromStatelessIdentity, fromFunctionsIdentity, compileIdentity, trivialIncrementalizationIdentity,
  ) where

import           Data.Delta            (Delta, Diff (..), DiffMinus (..))
import           Data.Interaction      (Interaction)
import           Data.Kind             (Type)
import           Data.Typeable         (Typeable)

import           Data.Code
import           Data.Coerce           (coerce)
import           Data.Functor.Identity (Identity (..))
import           Data.Proxy            (Proxy (Proxy))

class IncrementalizedQ cat where
  {-# MINIMAL fromStateless, fromFunctions, compile #-}
  type CodeType cat :: Type -> Type

  fromStateless ::
    (CodeType cat a  -> CodeType cat b)
    -> (CodeType cat (Delta a) -> CodeType cat (Delta b))
    -> cat a b

  fromFunctions ::
    Typeable c
    => proxy c
    -> CodeType cat (a -> (b , c))
    -> CodeType cat (Delta a -> c -> (Delta b, c))
    -> cat a b

  compile ::
    cat a b -> CodeType cat (a -> (b, Interaction (Delta a) (Delta b) ))


trivialInit :: (a -> b) -> a -> (b, (a, b))
trivialInit f a = seq b (b, (a, b))
  where
    b = f a
trivialTr ::
  (Diff a, DiffMinus b) =>
  (a -> b)
  -> Delta a
  -> (a, b)
  -> (Delta b, (a, b))
trivialTr f da (a, b) = (b' /- b, (a', b'))
  where
    a' = a /+ da
    b' = f a'

trivialIncrementalizationCode ::
  (IncrementalizedQ cat, CodeType cat ~ PackedCode, Typeable a, Typeable b, Diff a, DiffMinus b)
  => Code (a -> b)
  -> cat a b
trivialIncrementalizationCode cf =
  fromFunctionsCode [|| trivialInit $$cf ||] [|| trivialTr $$cf ||]

trivialIncrementalizationIdentity ::
  (IncrementalizedQ cat, CodeType cat ~ Identity, Typeable a, Typeable b, Diff a, DiffMinus b)
  => (a -> b)
  -> cat a b
trivialIncrementalizationIdentity f =
  fromFunctionsIdentity (trivialInit f) (trivialTr f)

fromStatelessCode ::
  forall cat a b.
  (IncrementalizedQ cat, CodeType cat ~ PackedCode)
  => (Code a -> Code b)
  -> (Code (Delta a) -> Code (Delta b))
  -> cat a b
fromStatelessCode = coerce (fromStateless :: (PackedCode a -> PackedCode b) -> (PackedCode (Delta a) -> PackedCode (Delta b)) -> cat a b)

fromFunctionsCode ::
  forall cat a b c.
  (IncrementalizedQ cat, CodeType cat ~ PackedCode, Typeable c)
  => Code (a -> (b, c))
  -> Code (Delta a -> c -> (Delta b, c))
  -> cat a b
fromFunctionsCode = coerce (fromFunctions Proxy :: PackedCode (a -> (b, c)) -> PackedCode (Delta a -> c -> (Delta b, c)) -> cat a b)

compileCode ::
  forall cat a b.
  (IncrementalizedQ cat, CodeType cat ~ PackedCode)
  => cat a b -> Code (a -> (b, Interaction (Delta a) (Delta b)))
compileCode =
  coerce (compile :: cat a b -> PackedCode (a -> (b, Interaction (Delta a) (Delta b))))

fromStatelessIdentity ::
  forall cat a b.
  (IncrementalizedQ cat, CodeType cat ~ Identity)
  => (a -> b)
  -> (Delta a -> Delta b)
  -> cat a b
fromStatelessIdentity = coerce (fromStateless :: (Identity a -> Identity b) -> (Identity (Delta a) -> Identity (Delta b)) -> cat a b)

fromFunctionsIdentity ::
  forall cat a b c.
  (IncrementalizedQ cat, CodeType cat ~ Identity, Typeable c)
  => (a -> (b, c))
  -> (Delta a -> c -> (Delta b, c))
  -> cat a b
fromFunctionsIdentity =
  coerce (fromFunctions Proxy :: Identity (a -> (b, c)) -> Identity (Delta a -> c -> (Delta b, c)) -> cat a b)

compileIdentity ::
  forall cat a b.
  (IncrementalizedQ cat, CodeType cat ~ Identity)
  => cat a b -> (a -> (b, Interaction (Delta a) (Delta b)))
compileIdentity =
  coerce (compile :: cat a b -> Identity (a -> (b, Interaction (Delta a) (Delta b))))








