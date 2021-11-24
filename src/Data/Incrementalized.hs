{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
module Data.Incrementalized where

import           Data.Code        (Code)
import           Data.Delta       (AtomicDelta, Delta, Diff (..),
                                   HasAtomicDelta (..), iterTr, iterTrStateless)
import           Data.Interaction (Interaction)
import           Data.Kind        (Type)
import           Data.Typeable    (Typeable)

class IncrementalizedQ cat where
  {-# MINIMAL fromStateless, fromFunctions, compile #-}
  type CodeType cat a :: Type

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










