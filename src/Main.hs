module Main( main ) where

{-                               DOCUMENTATION                              -}
{-
    Chomp: A brave new LangLang compiler
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

{-                              IMPLEMENTATION                              -}
-- Syntax tree representation
{-
type Token       = B.ByteString
--type SymbolId  = Int
type Declare     = (Token, RelationSet)
data DeclareEval = AssertDecl Declare
                 | WitnessDecl Declare
data Query       = ConjunctSelect Declare Token
data QueryEval   = Assert Query
                 | Witness Query
--data Relation    = QueryRel QueryEval | DeclareRel DeclareEval
--type RelationSet = [Relation]

--data Relation = Declare Expression
--              | Query Expression

--data Declaration = Token
--                 | Relation Expression

--data Query = Expression Expression
--data Eval = Declaration | Query
-}



-- Parser functions

--type Parser = (LC.ByteString, RelationSet) -> Maybe (BC.ByteString, RelationSet)
--type Lex  = BC.ByteString -> Maybe (BC.ByteString, BC.ByteString)

-- Parse input language
--lexToken :: BC.ByteString -> Maybe (BC.ByteString, BC.ByteString)
--lexToken s =  if BC.length tok > 0 then Just (tok, s') else Nothing
--  where
--    (tok, s') = BC.span (not . isSpace) s
--
--lexArrow :: BC.ByteString -> Maybe BC.ByteString
--lexArrow s =  if BC.unpack tok == "->" then Just s' else Nothing
--  where
--    (tok, s') = BC.splitAt 2 s

--lexWhite :: BC.ByteString -> BC.ByteString
--lexWhite = BC.dropWhile isSpace

--parseRelation :: Parser
--parseRelation (s, r) = if isJust s'' then Just (fromJust s'', r) else Nothing
--  where
--    ts        = lexToken s
--    (tok, s') = (liftM fst $ ts, liftM snd $ ts)
--    s''       = s' >>= (lexArrow . lexWhite)


--parseExpr :: (BC.ByteString, RelationSet) -> (BC.ByteString, RelationSet)
--parseExpr (s, r) = (BC.dropWhile isSpace s, r)

--parse :: BC.ByteString -> RelationSet
--parse s = snd $ parseRelation (s, [])

--whitespace :: Parser ()
--whitespace = skipWhile Data.Attoparsec.Char8.isSpace

type Token      = B.ByteString
data Expression = Symbol Token
                | Top
                | Relation Statement [Statement]
                | QueryConjunct Statement [Statement]

data Statement  = Declare Expression
                | Assert Expression
                | Witness Expression

data Connective = Arrow | ArrowColon | ArrowDot | Colon | Dot

skipComment :: A.Parser ()
skipComment = skipMany $
  AC.skipSpace *> AC.char '#' *> (A.skipWhile $ not . AC.isEndOfLine)

parseConnective :: A.Parser Connective
parseConnective =
  (AC.string (pack "->:") *> (return $ ArrowColon))
    <|> (AC.string (pack "->.") *> (return $ ArrowDot))
    <|> (AC.string (pack "->") *> (return $ Arrow))
    <|> (AC.string (pack ":")  *> (return $ Colon))
    <|> (AC.string (pack ".")  *> (return $ Dot))

parseSymbol :: A.Parser Expression
parseSymbol =
  (AC.char '_' *> pure Top) <|> (Symbol <$> AC.takeWhile AC.isAlpha_ascii)

--parseExpression :: A.Parser Expression
--parseExpression =
--  parseSymbol

parseLHS :: A.Parser Statement
parseLHS = Declare <$> parseSymbol

parseRHS :: Connective -> A.Parser (Connective, Statement)
parseRHS c = ((,) c) <$> parseStatement

parseQuantifier :: A.Parser (Expression -> Statement)
parseQuantifier =
  (AC.char ':' *> return Assert) <|> (AC.char '.' *> return Witness) <|> return Declare

parseConnectedStatement :: A.Parser Statement
parseConnectedStatement = do
  lhs <- parseLHS
  connective <- optional (parseConnective >>= parseRHS)
  return $ case connective of
    Just (ArrowColon, s) -> Assert  $ Relation lhs [s]
    Just (ArrowDot,   s) -> Witness $ Relation lhs [s]
    Just (Arrow,      s) -> Declare $ Relation lhs [s]
    Just (Colon,      s) -> Assert  $ QueryConjunct lhs [s]
    Just (Dot,        s) -> Witness $ QueryConjunct lhs [s]
    Nothing              -> lhs

parseStatement :: A.Parser Statement
parseStatement = skipComment *>
  ((AC.char '(' *> parseStatement <* skipComment <* AC.char ')')
    <|> parseConnectedStatement)

{-
parseStatement :: A.Parser Statement
parseStatement = do
  id <- AC.takeWhile AC.isAlpha_ascii <|> AC.string (pack "_")
  AC.skipSpace
  connective <- (Just <$> parseConnective) <|> return Nothing
  return $ case connective of
    Just ArrowColon -> Declare Top
    Just ArrowDot   -> Declare Top
    Just Arrow      -> Declare $ Relation (Declare Symbol id) <$>
    Just Colon      -> Declare Top
    Just Dot        -> Declare Top
    Nothing         -> Declare Top
-}

parseLangLang :: A.Parser [Statement]
parseLangLang = many parseStatement

-- Main loop
main :: IO ()
main = do
  putStrLn "Chomp v0.0.1 for LangLang"
  (liftM $ A.parse parseLangLang) B.getContents
  return ()

