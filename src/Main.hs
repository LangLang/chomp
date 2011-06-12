module Main (
    main
) where

import qualified Data.ByteString.Lazy.Char8 as LC
import Data.Char
import Control.Monad

-- Syntax tree representation

type SymbolId    = Int
data Declare     = Atom SymbolId
                 | Arrow (SymbolId, Expression)
data EvalDeclare = AssertDecl Declare
                 | WitnessDecl Declare
data Query       = ConjunctSelect Declare SymbolId
data EvalQuery   = Assert Query
                 | Witness Query
type Set         = [Expression]
data Expression  = Query | Declare | Set

-- Parse input language

parseExpr :: (LC.ByteString, Set) -> (LC.ByteString, Set)
parseExpr (s, r) = (LC.dropWhile isSpace s, r)

parse :: LC.ByteString -> Set
parse s = snd $ parseExpr (s, [])

-- Main loop

main :: IO ()
main = do
  putStrLn "Chomp v0.0.1 for LangLang"
  liftM parse LC.getContents
  return ()

