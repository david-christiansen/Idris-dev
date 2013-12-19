{-# LANGUAGE TemplateHaskell, CPP #-}

module Util.Version (gitHash) where

#ifdef RELEASE

gitHash  :: String
gitHash = ""

#else
import Util.VersionHelper

gitHash :: String
gitHash = "-" ++ $(getHash)

#endif
