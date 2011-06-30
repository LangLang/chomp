
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
import OperationalSemantics

{-                              IMPLEMENTATION                              -}

newtype LLString = LLString String

instance Show LLString where
  show (LLString str) = show str

-- Unit testing definitions

data CheckResult = Success { arguments :: [String] }
                 | Failure { arguments :: [String] }
                 | NotSure { arguments :: [String] }

unitCheck :: a -> IO ()
unitCheck f = putStrLn "TODO"

-- Generators

instance Serial LLString where
  --series d = [LLString $ (take d $ repeat 'c')]
  --series d = map LLString $ take d $ term
  series d = map LLString $ terms d
  --series d = map LLString $ collectterms d
    where
      -- Full terms may contain collections
      --fullterms d = terms d ++ parenthesize (terms d `combine` terms d)

      -- collectterms are collections of terms
      collectterms d = terms d ++ parenthesize (terms d `combine` (map (' ':) $ terms d))

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

      -- cterms are collections of terms

      -- parenterms are simple parenthesized terms e.g. (a:b->c)
      -- Note that we don't bother with terms like "(a)"
      -- (it's a valid parseable expression, but wastes too much testing time on something trivial)
      parenterms d
        | d == 0    = []
        | otherwise = parenthesize $ subterms d

      parenthesize  = map ((++")").('(':))
      selectorid    = selector `combine` id
      idselector    = id `combine` selector
      arrowid       = arrow `combine` id
      selector      = [":", ".", "\\\\", "\\"]
      arrow         = ["->"]
      id            = map (:[]) ['a'..'c']

      -- Generates all combinations of two lists (keeping their order invariant unlike permutations)
      combine       = liftM2 (++) :: [[a]] -> [[a]] -> [[a]]

  coseries rs d  = [] -- We will not be using coseries

-- Parser tests

-- Check whether the parser succeeded
--{-
--prop_parsevalid :: LLString -> IO Bool
prop_parsevalid (LLString s) =
  output $ prepend (s ++ "   ") $
    case result of
      Partial f -> prepend "Partial-" $ checkResult $ f empty
      otherwise -> checkResult result
  where
    result           = parse parseLangLang $ pack s
    checkResult r    =
      case r of
        Fail rem ctx msg -> ("Fail " ++ msg, False)
        Partial f        -> ("Impossible partial", False)
        Done rem st      -> ("Done", True)
    prepend s (s',r) = (s ++ s', r)
    output (s,r)     = putStrLn s >> return r
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

-- Operational tests

{- TODO
prop_evalwithconjunct :: Context -> Expression -> Expression -> CheckResult
prop_evalwithconjunct ctx ex0@(Symbol t0) ex1@(Symbol t1) = NotSure $ map show [ctx, ex0, ex1]
prop_evalwithconjunct ctx ex0             ex1             = NotSure $ map show [ctx, ex0, ex1]
--}

-- Dispatcher

main  = mapM_ (\(s,a) -> putStrLn s >> a) tests

tests = [
  ("parsevalid", smallCheckI prop_parsevalid),
  --("parseinvalid", quickCheck prop_parseinvalid),
  ("parsereflect", smallCheck 0 prop_reflectparser)
  --("evalwithconjunct", unitCheck prop_evalwithconjunct),
  ]
