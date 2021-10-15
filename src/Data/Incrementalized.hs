{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
module Data.Incrementalized where

import           Data.Code        (Code)
import           Data.Delta       (AtomicDelta, Delta, Diff (..), iterTr,
                                   iterTrStateless)
import           Data.Interaction (Interaction)

class IncrementalizedQ cat where
  {-# MINIMAL (fromStateless|fromStatelessAtomic), (fromFunctions|fromFunctionsAtomic), compile #-}

  fromStateless ::
    (Code a  -> Code b)
    -> (Code (Delta a) -> Code (Delta b))
    -> cat a b
  fromStateless f df =
    fromStatelessAtomic f (\ada -> [|| let da = pure $$ada in $$(df [|| da ||]) ||])

  fromStatelessAtomic ::
    (Code a  -> Code b)
    -> (Code (AtomicDelta a) -> Code (Delta b))
    -> cat a b
  fromStatelessAtomic f df =
    fromStateless f (\da -> [|| iterTrStateless (\da' -> $$(df [|| da' ||])) $$da ||])

  fromD ::
    Diff a =>
    (Code a  -> Code b)
    -> (Code a -> Code (Delta a) -> Code (Delta b))
    -> cat a b
  fromD f df = -- fromDAtomic f (\a ada -> [|| let da = pure $$ada in $$(df a [|| da ||]) ||])
    fromFunctions
       [|| \a -> ($$(f [|| a ||]), a) ||]
       [|| \da a -> let db = $$(df [|| a ||] [|| da ||]) in (db, a /+ da) ||]
  fromDAtomic ::
    Diff a =>
    (Code a  -> Code b)
    -> (Code a -> Code (AtomicDelta a) -> Code (Delta b))
    -> cat a b
  fromDAtomic f df =
    fromFunctionsAtomic
       [|| \a -> ($$(f [|| a ||]), a) ||]
       [|| \da a -> let db = $$(df [|| a ||] [|| da ||]) in (db, applyAtomicDelta a da) ||]

  fromFunctions ::
    Code (a -> (b , c))
    -> Code (Delta a -> c -> (Delta b, c))
    -> cat a b
  fromFunctions f df =
    fromFunctionsAtomic f [|| $$df . pure ||]

  fromFunctionsAtomic ::
    Code (a -> (b , c))
    -> Code (AtomicDelta a -> c -> (Delta b, c))
    -> cat a b
  fromFunctionsAtomic f df =
    fromFunctions f [|| iterTr $$df ||]

  compile ::
    cat a b -> Code (a -> (b, Interaction (Delta a) (Delta b) ))








