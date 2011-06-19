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

data ExpressionSegment = Declare [Expression]  -- (R->)
                       | Assert Query          -- assert `dot` (.Q)   or    (:Q)
                       | Witness Query         -- (.Q)

data Expression = Symbol Token
                | Top
                | Eval ExpressionSegment [Expression]

instance Show Expression where
  show (Symbol t)     = show t
  show Top            = "_"
  show (Eval lhs rhs) =
    case lhs of
      Declare lhs            -> showExpr lhs ++ " -> " ++ showExpr rhs
      Assert (Conjunct lhs)  -> showExpr lhs ++ ":" ++ showExpr rhs
      Witness (Conjunct lhs) -> showExpr lhs ++ "." ++ showExpr rhs
    where
      showExpr []     = "(ERROR: EMPTY EXPRESSION LIST)"
      showExpr (e:[]) = show e
      showExpr (e:es) = (foldl (++) ('(':(show e)) $ map show es) ++ ")"
