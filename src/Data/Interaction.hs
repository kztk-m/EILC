{-# LANGUAGE ExistentialQuantification #-}
module Data.Interaction
  (
    Interaction(..), InteractionStep(..),

    iterations, toStep, repeatSteps
  ) where
import           Control.DeepSeq (NFData (..))

-- | @'Interaction' a b@ represents a process that repeatedly receives @a@ and returns @b@.
newtype Interaction a b = Interaction { runInteraction :: a -> (b, Interaction a b) }
instance NFData (Interaction a b) where
  rnf (Interaction f) = rnf f


iterations :: Interaction a b -> [a] -> [b]
iterations _ []       = []
iterations i (a : as) =
  let (b, i') = runInteraction i a
  in b : iterations i' as
{-# INLINABLE iterations #-}

-- | A non-recursive datatype isomorphic to 'Interaction', where
--   data carried by the interction is made explicit.
data InteractionStep a b = forall c. InteractionStep { iInit :: !c, iStep :: !(a -> c -> (b, c)) }

toStep :: Interaction a b -> InteractionStep a b
toStep i = InteractionStep i (flip runInteraction)

repeatSteps :: InteractionStep a b -> Interaction a b
repeatSteps (InteractionStep i step) =
  let int c = Interaction $ \a ->
                let (b, c') = step a c
                in (b, int c')
  in int i






