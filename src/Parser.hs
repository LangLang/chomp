{-# LANGUAGE OverloadedStrings #-}
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
{- Generic parsers

-- Make a parser recursive
-- Note that you might have to combine this with 'try' in some circumstances
-- Also note that 'sepBy' could also be used (probably in combination with 'liftM' in many
-- circumstances
fixParser :: (a -> A.Parser a) -> a -> A.Parser a
fixParser parser a = (parser a >>= fixParser parser) <|> pure a

-- Make a parser that takes one parameter optional (in order to combine with monad bind)
possibly :: (a -> A.Parser a) -> a -> A.Parser a
possibly p a = p a <|> return a

-- Wrap the return value of a parser in a list
oneToMany :: ([a] -> A.Parser a) -> [a] -> A.Parser [a]
oneToMany p a = (:[]) <$> (p a)
-}

-- Common parsing

skipCommentLine :: A.Parser ()
skipCommentLine = AC.char '#' *> (A.skipWhile $ not . AC.isEndOfLine) *> AC.atEnd *> return ()

skipComments :: A.Parser ()
skipComments = skipMany (AC.skipSpace *> skipCommentLine)

-- should this be "skip many spaces?"

-- AST parsing

symbol :: A.Parser Expression
symbol =
  (AC.char '_' *> pure Top) <|> (Symbol <$> AC.takeWhile AC.isAlpha_ascii)

operator :: A.Parser Operator
operator =
  (AC.try $ AC.string "->." *> pure ArrowConjunct) <|> 
  (AC.string "->" *> pure Arrow) <|> 
  (AC.char '.' *> pure Conjunct) <|>
  (AC.char '\\' *> pure Complement)

collection :: A.Parser Expressions
collection =
  --AC.char '(' *> ((concat <$>) . many) (parseExpression <* skipComments) <* AC.char ')'
  AC.char '(' *> ((:[]) <$> expression) <* AC.char ')'

expression :: A.Parser Expression
expression = 
  (N <$> operator) <|> 
  symbol

expressions :: A.Parser Expressions
expressions = collection <|> ((:[]) <$> expression)

-- Main parser
parseLangLang :: A.Parser Expressions
parseLangLang = expressions

-- Temporary example of the non-termination problem with end-of-input in attoparsec
-- (Will be removed)
{-
parseLangLang :: A.Parser [Char]
--parseLangLang = many $ AC.char 'c'
--parseLangLang = many $ (AC.char 'c' <* A.endOfInput)
--parseLangLang = (many $ AC.char 'c') <* A.endOfInput
--parseLangLang = many $ (AC.char 'c' <* skipMany AC.skipSpace)
--parseLangLang = many $ (AC.char 'c'  <* skipMany AC.skipSpace <* A.endOfInput)
parseLangLang = (many $ (AC.char 'c'  <* skipMany AC.skipSpace)) <* A.endOfInput
--}
