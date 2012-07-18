module SyntaxTree where

{-                               DOCUMENTATION                              -}
{-
    Syntax tree representation for the language LangLang
-}

{-                                 MODULES                                  -}
-- Standard
import qualified Data.ByteString as B
import Data.ByteString.Char8 (pack)

{-                              IMPLEMENTATION                              -}
type Token      = B.ByteString

data Operator = Arrow           -- -> 
              | ArrowConjunct   -- ->.
              | Conjunct        -- .
              | Complement      -- \
              deriving (Eq)

data Expression = Symbol Token
                | Top
                | B Expressions Operator Expressions
                | L Expressions Operator
                | R Operator Expressions
                | N Operator
                deriving (Eq)
                
type Expressions = [Expression]  -- Technically Top should also be here 

instance Show Operator where
  show Arrow = "->"
  show ArrowConjunct = "->."
  show Conjunct = "."
  show Complement = "\\"

instance Show Expression where
  show (Symbol t)     = show t
  show Top            = "_"
  show (B l Arrow r) = (showExpr l) ++ " -> " ++ (showExpr r)
  show (B l ArrowConjunct r) = showExpr l ++ " ->. "  ++ showExpr r  
  show (B l op r) = showExpr l ++ show op ++ showExpr r
  show (L l Arrow) = showExpr l ++ " ->"
  show (L l ArrowConjunct) = showExpr l ++ " ->."
  show (L l op) = show l ++ show op
  show (R Arrow r) = "-> " ++ show r
  show (R ArrowConjunct r) = "->. " ++ showExpr r
  show (R op r) = show op ++ showExpr r
  show (N op) = show op

showExpr :: Expressions -> String    
showExpr []  = "()"
showExpr [e] = show e
showExpr (e:es) = "(" ++ (foldl (++) (show e) (map ((" " ++) . show) es)) ++ ")"
