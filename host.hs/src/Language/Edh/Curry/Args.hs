{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.Curry.Args
  ( ScriptArg (..),
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

newtype ScriptArg (t :: Type) (name :: Symbol) = ScriptArg t

scriptArgName :: forall (name :: Symbol). KnownSymbol name => Text
scriptArgName = T.pack $ symbolVal (Proxy :: Proxy name)

data Effected t = Effective !t | NonEffect

type name @: t = ScriptArg t name

type name $: t = ScriptArg (Effected t) name

pattern ComputArg :: t -> name @: t
pattern ComputArg t = ScriptArg t

{-# COMPLETE ComputArg #-}

appliedArg :: name @: t -> t
appliedArg (ScriptArg a) = a

effectfulArg :: name $: t -> Maybe t
effectfulArg (ScriptArg (Effective a)) = Just a
effectfulArg (ScriptArg NonEffect) = Nothing
