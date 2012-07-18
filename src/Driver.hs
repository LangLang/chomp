{-# LANGUAGE OverloadedStrings #-}
module Driver( driverMain ) where

{-                               DOCUMENTATION                              -}
{-
    Driver...
-}

{-                                 MODULES                                  -}
-- Standard
import qualified Data.ByteString.Char8 as BC8
import qualified Data.Attoparsec
import Control.Monad
import qualified System.Environment
import System.IO (stderr)
import qualified System.Exit
import qualified System.Directory
import System.FilePath ((</>))

-- Chomp
import SyntaxTree
import Parser
import OperationalSemantics

{-                              IMPLEMENTATION                              -}

driverMain :: IO ()
driverMain = do
  -- Read command line arguments
  args <- System.Environment.getArgs
  sourceFileContents <- if length args < 1
    then BC8.hPutStrLn stderr "No arguments supplied." >> printUsage >> (System.Exit.exitWith $ System.Exit.ExitFailure 1)
    else if head args == "--help"
      then printUsage >> System.Exit.exitSuccess
      else if length args > 1
        then BC8.hPutStrLn stderr "Too many arguments supplied." 
          >> printUsage 
          >> (System.Exit.exitWith $ System.Exit.ExitFailure 1)
        else loadSourceFile $ head args
  Data.Attoparsec.parseTest parseLangLang sourceFileContents
  where
    loadSourceFile path = do
      currentDirPath <- System.Directory.getCurrentDirectory
      BC8.readFile (currentDirPath </> path) -- (uses path directly if it is already absolute)

printUsage :: IO ()
printUsage = putStrLn "USAGE: chomp sourceFile"
