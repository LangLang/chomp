--{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module OperationalSemantics where

{-                               DOCUMENTATION                              -}
{-
    Operational semantics expressed as haskell functions.
-}

{-                                 MODULES                                  -}
-- Standard

-- Chomp
import SyntaxTree

{-                              IMPLEMENTATION                              -}

-- A context is the path (stack of arrow declarations) along with the relevant expressions in scope
-- that leads to the current computation
-- Note that the top of the stack is the head of the list
type Context = [[Expression]]

-- A thunk contains the context (the outer or left-hand side context) and an expression to evaluate
-- inside that context.
type Thunk = (Context, Expression)

-- The result of a computation. Allows eval to return Error
-- type Result = Maybe [Expression]
data Result a = Success [a] | Error deriving Eq
type ResultExpression = Result Expression
type ResultThunk = Result Thunk

eval :: Thunk -> ResultThunk
eval ([], ex@(
    B [B [Symbol t0] Arrow [Symbol t1]] Conjunct [Symbol t2]  -- (t0 -> t1):t2
  )) 
  | t1 == t2 = Success [([[B [Symbol t0] Arrow [Symbol t1]]], Symbol t1)] -- (t0 -> t1) |- t1
  | otherwise = Success [] -- ()
