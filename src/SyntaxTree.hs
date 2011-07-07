module SyntaxTree where

{-                               DOCUMENTATION                              -}
{-
    Syntax tree representation for the language LangLang
-}

{-                                 MODULES                                  -}
-- Standard
import qualified Data.ByteString as B

{-                              IMPLEMENTATION                              -}
type Token      = B.ByteString

data Query = Conjunct [Expression]             -- (.Q)
           | Complement [Expression]           -- (/Q)
           deriving (Eq)

data ExpressionSegment = Declare [Expression]  -- (R->)
                       | Assert Query          -- assert `dot` (.Q)   or    (:Q)
                       | Witness Query         -- (.Q)
                       deriving (Eq)

data Expression = Symbol Token
                | Top
                | Bottom
                | Eval ExpressionSegment [Expression]
                deriving (Eq)

instance Show Expression where
  show (Symbol t)     = show t
  show Top            = "_"
  show (Eval lhs rhs) =
    case lhs of
      Declare lhs            -> showExpr lhs ++ " -> " ++ showExpr rhs
      Assert (Conjunct lhs)  -> showExpr lhs ++ ":" ++ showExpr rhs
      Witness (Conjunct lhs) -> showExpr lhs ++ "." ++ showExpr rhs
      Assert (Complement lhs)  -> showExpr lhs ++ "\\\\" ++ showExpr rhs
      Witness (Complement lhs) -> showExpr lhs ++ "\\" ++ showExpr rhs
    where
      showExpr []     = "(ERROR: EMPTY EXPRESSION LIST)"
      showExpr (e:[]) = show e
      showExpr (e:es) = (foldl (++) ('(':(show e)) $ map show es) ++ ")"
