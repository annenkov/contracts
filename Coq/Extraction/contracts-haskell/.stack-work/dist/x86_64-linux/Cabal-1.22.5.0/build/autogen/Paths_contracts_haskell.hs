module Paths_contracts_haskell (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/ghc-7.10/7.10.3/bin"
libdir     = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/ghc-7.10/7.10.3/lib/x86_64-linux-ghc-7.10.3/contracts-haskell-0.1.0.0-HnfsBa16keB7WX7M5KBBGe"
datadir    = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/ghc-7.10/7.10.3/share/x86_64-linux-ghc-7.10.3/contracts-haskell-0.1.0.0"
libexecdir = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/ghc-7.10/7.10.3/libexec"
sysconfdir = "/home/danil/Projects/contracts/Coq/Extraction/contracts-haskell/.stack-work/install/x86_64-linux/ghc-7.10/7.10.3/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "contracts_haskell_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "contracts_haskell_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "contracts_haskell_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "contracts_haskell_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "contracts_haskell_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
