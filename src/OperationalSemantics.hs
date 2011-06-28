module OperationalSemantics where

{-                               DOCUMENTATION                              -}
{-
    Operational semantics expressed as haskell functions.

    Semantics are documented like they would be in a paper, using a style
    similar to natural deduction.

    The assumptions placed before the turnstile |- is exactly the context
    in which a computation takes place.
    Usually this will be written 'ctx |-', but sometimes we will use the
    notation '(cs -> c) |-' similar to (and corresponding, in the code, with)
    haskell's pattern matching '(c:cs)' notation.
    When written in this way, c refers to the head of a chain of arrows and
    may be selected from like a regular symbol e.g. 'c:exp'.

    For the purposes of documenting the semantics '^' is a special pseudo-
    operator looking up a variable in the context similar to how the
    standard '.' operator works, but recursively in the scope. (Thus the
    documentation for the semantics might have expressions like 'ctx ^ exp'.
-}

{-                                 MODULES                                  -}
-- Standard
import Control.Monad (foldM)

-- Chomp
import SyntaxTree

{-                              IMPLEMENTATION                              -}

-- Top level semantics

-- A context is the path (stack of arrow declarations) leading to the current computation
-- Note that the top of the stack is the head of the list
type Context = [[Expression]]

-- The result of a computation. Allows eval to return Error
-- type Result = Maybe [Expression]
data Result a = Success [a] | Error
type EvalResult = Result Expression

--instance Functor Result where
--  fmap _ Error          = Error
--  fmap f (Success exp)  = Success (f exp)
--instance Monad Result where
--  (Success exp) >>= f   = mapResult f exp
--  Error  >>= _          = Error
--  (Success _) >> r      = r
--  Error  >>  _          = Error
--  return                = Success . (:[])
--  fail _                = Error

-- Map a evaluation function over a set of expression and the fold the list into a Result
-- This function short-circuits as soon as an error is reached
foldEval :: (Expression -> EvalResult) -> [Expression] -> EvalResult
foldEval f (e:es) =
  case f e of
    (Success exp') -> case foldEval f es of
      (Success exp'') -> Success (exp' ++ exp'')
      Error       -> Error
    Error -> Error

-- Auxiliary functions

-- Match an element inside a collection and return all matching expressions
conjunctCollection :: [Expression] -> Expression -> [Expression]
conjunctCollection (e:es) exp = []

-- Find an expression in the given context and return all matching expressions
conjunctContext :: Context -> Expression -> [Expression]
conjunctContext [] exp = []
conjunctContext (c:[]) exp = conjunctCollection c exp
conjunctContext (c:cs) exp =
  if matches /= [] then matches else conjunctContext cs exp
  where
    matches = conjunctCollection c exp

conjunctContextAssert :: Context -> Expression -> EvalResult
conjunctContextAssert ctx exp =
  -- Note that exp can't be bottom, bottom can only be expressed as an empty list of expressions []
  if matches /= [] then Success matches else Error
  where
    matches = conjunctContext ctx exp

-- Evaluates the expression inside the stack of contexts given
eval :: Context -> Expression -> EvalResult

{-
ctx |- exp0 -> exp1
-------------------
ctx |- exp0 -> exp1
-}

eval ctx exp@(Eval (Declare exp0) exp1)
  | True = Success (exp:[])

{-
  (cs -> c) |- :exp1
  ------------------
       c:exp1
-}

eval ctx exp@(Eval (Assert (Conjunct exp1)) [])
  | True = foldEval (conjunctContextAssert ctx) exp1

{-
ctx |- exp1:exp2
-----------------
ctx |- .exp1:exp2
-----------------
(ctx `.` exp1):exp2
-}

eval ctx exp@(Eval (Witness (Conjunct exp1)) [])
  | True =  Success $ concat $ map (conjunctContext ctx) exp1

{-
ctx |- exp0 . exp1
------------------
ctx |- ????????

(Eval (Witness (Conjunct exp0) exp1)

ctx |- exp0 \ exp1
------------------
ctx |- ????????

(Eval (Assert  (Complement exp0) exp1)

ctx |- exp0 \\ exp1
------------------
ctx |- ????????

(Eval (Witness (Complement exp0) exp1)

-}

