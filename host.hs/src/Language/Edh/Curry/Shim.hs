{-# LANGUAGE PolyKinds #-}

module Language.Edh.Curry.Shim
  ( pattern TypeRep,
    dynPerformIO,
    dynPerformSTM,
    dynContSTM,
  )
where

import Control.Concurrent.STM (STM)
import Data.Dynamic (Dynamic (..), Typeable)
import Type.Reflection
  ( TypeRep,
    eqTypeRep,
    typeRep,
    withTypeable,
    pattern App,
    type (:~~:) (HRefl),
  )
import Prelude

data TypeableInstance a where
  TypeableInstance :: Typeable a => TypeableInstance a

typeableInstance :: TypeRep a -> TypeableInstance a
typeableInstance tr = withTypeable tr TypeableInstance

{- ORMOLU_DISABLE -}

-- | Shim for the proposed one at:
--   https://gitlab.haskell.org/ghc/ghc/-/issues/19691
pattern TypeRep :: forall k (a :: k). () => Typeable a => TypeRep a
pattern TypeRep <- (typeableInstance -> TypeableInstance)
  where TypeRep = typeRep

{- ORMOLU_ENABLE -}

-- | Perform a polymorphic IO action which is wrapped in a 'Dynamic'
--
-- The specified 'naAlt' action will be performed instead, if the wrapped
-- computation is not applicable, i.e. not really an IO action.
dynPerformIO :: IO Dynamic -> Dynamic -> IO Dynamic
dynPerformIO naAlt (Dynamic trAct monotypedAct) = case trAct of
  App io TypeRep ->
    case io `eqTypeRep` typeRep @IO of
      Just HRefl -> Dynamic TypeRep <$> monotypedAct
      Nothing -> naAlt -- not an IO action
  _ -> naAlt -- not even a poly-type

-- | Perform a polymorphic STM action which is wrapped in a 'Dynamic'
--
-- The specified 'naAlt' action will be performed instead, if the wrapped
-- computation is not applicable, i.e. not really an STM action.
dynPerformSTM :: STM Dynamic -> Dynamic -> STM Dynamic
dynPerformSTM naAlt (Dynamic trAct monotypedAct) = case trAct of
  App io TypeRep ->
    case io `eqTypeRep` typeRep @STM of
      Just HRefl -> Dynamic TypeRep <$> monotypedAct
      Nothing -> naAlt -- not an STM action
  _ -> naAlt -- not even a poly-type

-- | Perform a polymorphic STM action which is wrapped in a 'Dynamic'
--
-- The specified 'naAlt' action will be performed instead, if the wrapped
-- computation is not applicable, i.e. not really an STM action.
dynContSTM :: STM () -> Dynamic -> (Dynamic -> STM ()) -> STM ()
dynContSTM naAlt (Dynamic trAct monotypedAct) !exit = case trAct of
  App io TypeRep ->
    case io `eqTypeRep` typeRep @STM of
      Just HRefl -> exit . Dynamic TypeRep =<< monotypedAct
      Nothing -> naAlt -- not an STM action
  _ -> naAlt -- not even a poly-type
