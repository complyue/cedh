module Language.Edh.Curry
  ( installCurryBatteries,
    withComputClass,
    -- TODO organize and doc the re-exports
    module Language.Edh.Curry.Comput,
    module Language.Edh.Curry.Shim,
  )
where

-- import           Debug.Trace

import Control.Monad
import Language.Edh.Curry.Comput
import Language.Edh.Curry.Shim
import Language.Edh.EHI
import Prelude

installCurryBatteries :: EdhWorld -> IO ()
installCurryBatteries !world =
  void $
    installEdhModule world "curry/RT" $ \ !ets exit -> do
      let !moduScope = contextScope $ edh'context ets

      !clsComput <- defineComputClass moduScope

      let !moduArts = [(AttrByName "Comput", EdhObject clsComput)]
      iopdUpdate moduArts $ edh'scope'entity moduScope
      prepareExpStore ets (edh'scope'this moduScope) $ \ !esExps ->
        iopdUpdate moduArts esExps

      exit

withComputClass :: (Object -> EdhTx) -> EdhTx
withComputClass !act = importEdhModule "curry/RT" $ \ !moduRT !ets ->
  lookupEdhObjAttr moduRT (AttrByName "Comput") >>= \case
    (_, EdhObject !clsComput) -> runEdhTx ets $ act clsComput
    _ -> error "bug: curry/RT provides no Comput class"
