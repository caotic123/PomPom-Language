{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -Wno-missing-safe-haskell-mode #-}
module Paths_Kei2 (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/caotic/.cabal/bin"
libdir     = "/Users/caotic/.cabal/lib/x86_64-osx-ghc-8.10.4/Kei2-0.1.0.0-inplace-Kei2"
dynlibdir  = "/Users/caotic/.cabal/lib/x86_64-osx-ghc-8.10.4"
datadir    = "/Users/caotic/.cabal/share/x86_64-osx-ghc-8.10.4/Kei2-0.1.0.0"
libexecdir = "/Users/caotic/.cabal/libexec/x86_64-osx-ghc-8.10.4/Kei2-0.1.0.0"
sysconfdir = "/Users/caotic/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "Kei2_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "Kei2_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "Kei2_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "Kei2_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "Kei2_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "Kei2_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
