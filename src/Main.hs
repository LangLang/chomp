module Main( main ) where

{-                               DOCUMENTATION                              -}
{-
    Chomp: A brave new LangLang compiler
-}

{-                                 MODULES                                  -}
-- Standard
import qualified Data.ByteString as B (getContents)
import Data.Attoparsec (parse)
import Control.Monad

-- Chomp
import SyntaxTree
import Parser

{-                              IMPLEMENTATION                              -}

main :: IO ()
main = do
  putStrLn "Chomp v0.0.1 for LangLang"
  st <- (liftM $ parse parseLangLang) B.getContents
  print st
  return ()

