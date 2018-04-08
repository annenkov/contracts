{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -fno-warn-implicit-prelude #-}
module Paths_contracts_haskell (
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

bindir     = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/lts-11.3/8.2.2/bin"
libdir     = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/lts-11.3/8.2.2/lib/x86_64-linux-ghc-8.2.2/contracts-haskell-0.1.0.0-84FfExXNrqvLvr2z5Moug7-contracts-haskell"
dynlibdir  = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/lts-11.3/8.2.2/lib/x86_64-linux-ghc-8.2.2"
datadir    = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/lts-11.3/8.2.2/share/x86_64-linux-ghc-8.2.2/contracts-haskell-0.1.0.0"
libexecdir = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/lts-11.3/8.2.2/libexec/x86_64-linux-ghc-8.2.2/contracts-haskell-0.1.0.0"
sysconfdir = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/lts-11.3/8.2.2/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "contracts_haskell_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "contracts_haskell_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "contracts_haskell_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "contracts_haskell_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "contracts_haskell_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "contracts_haskell_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
