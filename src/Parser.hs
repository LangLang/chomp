module Parser ( parseLangLang ) where

{-                               DOCUMENTATION                              -}
{-
    Parse LangLang source code and output a ParseTree
-}

{-                                 MODULES                                  -}
-- Standard
import qualified Data.ByteString as B
import Data.ByteString.Char8 (pack)
import Data.Char
import Data.Maybe
import qualified Data.Attoparsec as A
import qualified Data.Attoparsec.Char8 as AC
import Data.Attoparsec.Combinator
import Control.Monad
import Control.Applicative hiding (many)

-- Chomp
import SyntaxTree

{-                              IMPLEMENTATION                              -}
-- Generic parsers

-- Make a parser recursive
-- Note that you might have to combine this with 'try' in some circumstances
-- Also note that 'sepBy' could also be used (probably in combination with 'liftM' in many
-- circumstances
fixParser :: (a -> A.Parser a) -> a -> A.Parser a
fixParser parser a = (parser a >>= fixParser parser) <|> return a

-- Make a parser that takes one parameter optional (in order to combine with monad bind)
possibly :: (a -> A.Parser a) -> a -> A.Parser a
possibly p a = p a <|> return a

-- Wrap the return value of a parser in a list
oneToMany :: ([a] -> A.Parser a) -> [a] -> A.Parser [a]
oneToMany p a = (:[]) <$> (p a)

-- Common parsing

skipComments :: A.Parser ()
skipComments = skipMany $
  AC.skipSpace *> AC.char '#' *> (A.skipWhile $ not . AC.isEndOfLine)

-- AST parsing

parseSymbol :: A.Parser Expression
parseSymbol =
  (AC.char '_' *> pure Top) <|> (Symbol <$> AC.takeWhile AC.isAlpha_ascii)

parseSelector :: A.Parser ([Expression] -> ExpressionSegment)
parseSelector =
  (AC.char ':' *> return (Assert . Conjunct)) <|> (AC.char '.' *> return (Witness . Conjunct))

parseArrow :: [Expression] -> A.Parser ExpressionSegment
parseArrow e =
  AC.string (pack "->") *> (return $ Declare e)

parseCollection :: A.Parser [Expression]
parseCollection =
  AC.char '(' *> ((concat <$>) . many1) (parseExpression <* skipComments) <* AC.char ')'

-- Parse the codomain segment of a query
-- 1.  Can optionally start with a selector ':' or '.'
-- 2.1 Followed by a collection e.g. '(a -> b c:d.e)'
-- 2.2 Or a symbol e.g. 'a'

parseQuerySegment :: A.Parser ExpressionSegment
parseQuerySegment =
  selector <*> (collection <|> symbol)
  where
    selector   = parseSelector <* skipComments
    collection = parseCollection
    symbol     = ((:[]) <$> parseSymbol)

-- Parse a query expression
-- 1.  Can optionally start with a selector ':' or '.'
-- 2.1 Followed by a collection e.g. '(a:b c -> d)'
-- 2.2 Or a simple Query expression e.g. 'a:b:(e -> f).c:(a:b c -> d)'
-- * No arrows outside of brackets

parseQuerySegmentWith :: [Expression] -> A.Parser [Expression]
parseQuerySegmentWith e =
  (:[]) <$> flip Eval e <$> parseQuerySegment

parseQueryExpr :: A.Parser [Expression]
parseQueryExpr =
  (segment <|> collection <|> symbol) >>= fixParser parseQuerySegmentWith
  where
    segment    = parseQuerySegmentWith [] :: A.Parser [Expression]
    collection = parseCollection          :: A.Parser [Expression]
    symbol     = ((:[]) <$> parseSymbol)  :: A.Parser [Expression]

parseRelationExpr :: [Expression] -> A.Parser Expression
parseRelationExpr e =
  segment <*> (collection <|> expression)
  where
    segment    = Eval <$> (skipComments *> parseArrow e)
    collection = parseCollection
    expression = parseExpression

parseExpression :: A.Parser [Expression]
parseExpression =
  skipComments *> (parseQueryExpr >>= possibly (oneToMany parseRelationExpr))

-- Main parser

parseLangLang :: A.Parser [Expression]
parseLangLang = concat <$> many parseExpression
