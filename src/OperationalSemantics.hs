module OperationalSemantics where

{-                               DOCUMENTATION                              -}
{-
    Operational semantics expressed as haskell functions
    These will be combined using a functional
-}

{-                                 MODULES                                  -}
-- Standard

-- Chomp
import SyntaxTree

{-                              IMPLEMENTATION                              -}

--type Reduction = Context -> Expression

{-

ctx |- exp0 -> exp1
-------------------
ctx |- exp0 -> exp1

(Eval (Declare exp0) exp1)

ctx |- exp0 : exp1
------------------
ctx |- ????????

(Eval (Assert  (Conjunct exp0) exp1)

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

