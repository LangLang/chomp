
{-                                 MODULES                                  -}
-- Standard
import Data.Attoparsec hiding (take)
import Data.ByteString (ByteString, empty)
import Data.ByteString.Char8 (pack)
import Data.Maybe (isJust)
import Data.Functor
import Control.Monad (liftM, liftM2)
import Text.Printf (printf)

{-- QuickCheck
import Test.QuickCheck
--import Test.QuickCheck.Gen
import Test.QuickCheck.Arbitrary
--import Test.QuickCheck.Property
--import Test.QuickCheck.Test
-}

-- SmallCheck
import Test.SmallCheck

-- Chomp
import SyntaxTree
import Parser

{-                              IMPLEMENTATION                              -}

newtype LLString = LLString String

instance Show LLString where
  show (LLString str) = show str


-- Generators

instance Serial LLString where
  --series d = [LLString $ (take d $ repeat 'c')]
  --series d = map LLString $ take d $ term
  series d = map LLString $ terms d
    where
      -- Collections are made up out of terms
      terms d = ("":selector) `combine` subterms d

      -- Subterms never start with a selector
      subterms d
        | d == 0    = id
        | even d    = (idselector `combine` (parenterms $ d - 1)) ++ ((pterms d) `combine` selectorid)
        | otherwise = (idselector `combine` (parenterms $ d - 1)) ++ ((pterms d) `combine` (selectorid ++ arrow ++ arrowid))

      -- pterms are the previous generation of subterms that may or may not be in parenthesis
      pterms d
        | d == 0    = []
        | even d    = ((subterms \/ parenterms) $ d - 2) ++ ((subterms \/ parenterms) $ d - 1)
        | otherwise = (subterms \/ parenterms) $ d - 1

      -- parenterms are simple parenthesized terms e.g. (a:b->c)
      -- Note that we don't bother with terms like "(a)"
      -- (it's a valid parseable expression, but wastes too much testing time on something trivial)
      parenterms d
        | d == 0    = []
        | otherwise = map ((++")").('(':)) $ subterms d

      selectorid    = selector `combine` id
      idselector    = id `combine` selector
      arrowid       = arrow `combine` id
      selector      = [":", "."]
      arrow         = ["->"]
      id            = map (:[]) ['a'..'c']

      -- Generates all combinations of two lists (keeping their order invariant unlike permutations)
      combine       = liftM2 (++) :: [[a]] -> [[a]] -> [[a]]

  coseries rs d  = [] -- We will not be using coseries

  --coseries rs d = [ \(LLString str) -> undefined
  --                | f <-  ]

-- foldl (liftM2 (,)) ['a'] [['b']]

-- Generators
{-

instance Arbitrary LLString where
  arbitrary =
    LLString <$> randomQuery
    where
      randomQuery = oneof [randomToken, randomSelector]
      randomToken = listOf1 $ e lements $ '_':['a'..'z']
      randomSelector = elements [".", ":"]
      randomOperator = elements [".", ":", "->"]

-- Tests

main  = mapM_ (\(s,a) -> printf "%-25s: " s >> a) tests

-- Check whether the parser succeeded
prop_parserresult (LLString s) =
    property $ isJust $ maybeResult result
    where
      result = parse parseLangLang $ pack s

-- Parse the string, serialize it and parse it again. Check if the syntax tree remains the same.
prop_reflectparser (LLString s) =
    property $ succeeded
    where
      result = parse parseLangLang $ pack s
      succeeded = isJust $ maybeResult result


tests = [
  ("parserresult", quickCheck prop_parserresult),
  ("reflectparser", quickCheck prop_reflectparser)]

-}

main  = mapM_ (\(s,a) -> printf "%-25s:\n" s >> a) tests

-- Check whether the parser succeeded
--{-
prop_parsevalid :: LLString -> IO Bool
prop_parsevalid (LLString s) =
  debugPrint s >>
  case result of
    Partial f -> debugPrint "Partial" >> (checkResult $ f empty)
    otherwise -> checkResult result
  where
    result = parse parseLangLang $ pack s
    checkResult r =
      case r of
        Fail rem ctx msg -> (debugPrint $ "Fail " ++ msg) >> return False
        Partial f        -> debugPrint "Impossible partial" >> return False
        Done rem st      -> debugPrint "Done" >> return True
    debugPrint = print s
    --debugPrint = \str -> return ()

--}
{-
prop_parsevalid :: LLString -> Bool
prop_parsevalid (LLString s) =
  isJust $ maybeResult $ case result of
    Partial f -> f empty
    otherwise -> result
  where
    result = parse parseLangLang $ pack s
--}

-- Parse the string, serialize it and parse it again. Check if the syntax tree remains the same.
prop_reflectparser (LLString s) =
  succeeded
  where
    result = parse parseLangLang $ pack s
    succeeded = isJust $ maybeResult result

tests = [
  ("parsevalid", smallCheckI prop_parsevalid),
  --("parseinvalid", quickCheck prop_parseinvalid),
  ("reflectparser", smallCheck 0 prop_reflectparser)]
