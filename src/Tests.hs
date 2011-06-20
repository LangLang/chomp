
{-                                 MODULES                                  -}
-- Standard
import Data.Attoparsec
import Data.ByteString (ByteString)
import Data.ByteString.Char8 (pack)
import Data.Maybe (isJust)
import Data.Functor
import Control.Monad (liftM)
import Text.Printf (printf)
import Test.QuickCheck
--import Test.QuickCheck.Gen
import Test.QuickCheck.Arbitrary
--import Test.QuickCheck.Property
--import Test.QuickCheck.Test

-- Chomp
import SyntaxTree
import Parser

{-                              IMPLEMENTATION                              -}

-- Generators
newtype LLString = LLString String deriving Show

instance Arbitrary LLString where
  arbitrary =
    LLString <$> randomQuery
    where
      randomQuery = oneof [randomToken, randomSelector]
      randomToken = listOf1 $ elements $ '_':['a'..'z']
      randomSelector = elements [".", ":"]
      randomOperator = elements [".", ":", "->"]

-- Tests

main  = mapM_ (\(s,a) -> printf "%-25s: " s >> a) tests

-- Check whether the parser succeeded
prop_parserresult (LLString s) =
    property $ isJust $ maybeResult result
    where
      result = parse parseLangLang $ pack s

-- reversing twice a finite list, is the same as identity
prop_reflectparser (LLString s) =
    property $ succeeded
    where
      result = parse parseLangLang $ pack s
      succeeded = isJust $ maybeResult result


tests = [
  ("parserresult", quickCheck prop_parserresult),
  ("reflectparser", quickCheck prop_reflectparser)]
