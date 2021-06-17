module Main where

-- import           Debug.Trace

import Language.Edh.Curry
import Language.Edh.EHI
import Language.Edh.Repl
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Prelude

main :: IO ()
main =
  getArgs >>= \case
    [] -> replWithModule "curry"
    [edhModu] -> replWithModule edhModu
    _ -> hPutStrLn stderr "Usage: cedh [ <edh-module> ]" >> exitFailure
  where
    replWithModule :: FilePath -> IO ()
    replWithModule = edhRepl defaultEdhConsoleSettings $
      \ !world -> do
        let !consoleOut = consoleIO (edh'world'console world) . ConsoleOut

        -- install all necessary batteries
        installEdhBatteries world
        installCurryBatteries world

        consoleOut $
          ">> Currying Đ (Edh) <<\n"
            <> "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:\n"
            <> "  https://github.com/e-wrks/tour\n"
