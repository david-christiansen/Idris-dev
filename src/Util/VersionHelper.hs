module Util.VersionHelper where

import Control.Exception
import System.Process
import Language.Haskell.TH

getHash :: ExpQ
getHash = do version <- runIO $ catch (readProcess "git" ["rev-parse", "HEAD"] "")
                                      (\e -> let e' = (e :: SomeException) in return "PRE")
             stringE (takeWhile (/= '\n')  version)
