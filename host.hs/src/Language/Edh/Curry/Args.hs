{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.Curry.Args
  ( ScriptArg (..),
    Effective (..),
    scriptArgName,
    type (@:),
    type ($:),
    pattern ComputArg,
    appliedArg,
    effectfulArg,
  )
where

import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as T
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import Prelude

newtype ScriptArg (a :: Type) (name :: Symbol) = ScriptArg a

scriptArgName :: forall (name :: Symbol). KnownSymbol name => Text
scriptArgName = T.pack $ symbolVal (Proxy :: Proxy name)

data Effective a = InEffect !a | NonEffect

type name @: a = ScriptArg a name

type name $: a = ScriptArg (Effective a) name

pattern ComputArg :: a -> name @: a
pattern ComputArg a = ScriptArg a

{-# COMPLETE ComputArg #-}

appliedArg :: name @: a -> a
appliedArg (ScriptArg a) = a

effectfulArg :: name $: a -> Maybe a
effectfulArg (ScriptArg (InEffect a)) = Just a
effectfulArg (ScriptArg NonEffect) = Nothing
