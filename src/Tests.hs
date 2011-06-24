
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
      terms 0       = selectorid ++ id
      terms d       = if even d
                        then (liftM2 (++)) ((terms $ d - 2) ++ (terms $ d - 1)) selectorid
                        else (liftM2 (++)) (terms $ d - 1) (selectorid ++ arrow ++ arrowid)
      selectorid    = (liftM2 (++)) selector id
      arrowid       = (liftM2 (++)) arrow id
      selector      = [":", "."]
      arrow         = ["->"]
      id            = map (:[]) ['a'..'d']

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

main  = mapM_ (\(s,a) -> printf "%-25s: " s >> a) tests

-- Check whether the parser succeeded
--{-
prop_parsevalid :: LLString -> IO Bool
prop_parsevalid (LLString s) =
  print s >>
  case result of
    Partial f -> print "Partial" >> (checkResult $ f empty)
    otherwise -> checkResult result
  where
    result = parse parseLangLang $ pack s
    checkResult r =
      case r of
        Fail rem ctx msg -> (print $ "Fail " ++ msg) >> return False
        Partial f        -> print "Impossible partial" >> return False
        Done rem st      -> print "Done" >> return True
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
