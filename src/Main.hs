module Main( main ) where

{-                               DOCUMENTATION                              -}
{-
    Chomp: A brave new LangLang compiler
-}

{-                                 MODULES                                  -}
-- Standard
import qualified Data.ByteString as B (getContents)
import Data.Attoparsec (parse, parseTest)
import Control.Monad

-- Chomp
import SyntaxTree
import Parser

{-                              IMPLEMENTATION                              -}

main :: IO ()
main = do
  putStrLn "Chomp v0.0.1 for LangLang"
  --result <- (liftM $ parse parseLangLang) B.getContents
  --print result
  return ()
  (parseTest parseLangLang) =<< B.getContents


