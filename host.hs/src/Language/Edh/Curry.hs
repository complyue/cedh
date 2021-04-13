module Language.Edh.Curry
  ( installCurryBatteries,
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
    installEdhModule world "curry/Demo" $ \ !ets exit -> do
      let !moduScope = contextScope $ edh'context ets

      let !moduArts =
            []
      !artsDict <-
        EdhDict
          <$> createEdhDict [(EdhString k, v) | (k, v) <- moduArts]
      flip iopdUpdate (edh'scope'entity moduScope) $
        [(AttrByName k, v) | (k, v) <- moduArts]
          ++ [(AttrByName "__exports__", artsDict)]

      exit
