--{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module OperationalSemantics where

{-                               DOCUMENTATION                              -}
{-
    Operational semantics expressed as haskell functions.

    CONVENTIONS:
      Semantics are documented like they would be in a paper, using a style
      similar to natural deduction.

      The assumptions placed before the turnstile |- is exactly the context
      in which a computation takes place.
      Usually this will be written 'ctx |-', but sometimes we will use the
      notation '(cs |- c) |-' similar to (and corresponding in the code, with)
      haskell's pattern matching '(c:cs)' notation.
      When written in this way, c refers to the head of a chain of arrows that
      have been queried.

      |- implies a kind of lazy evaluate-by-need strategy... (TODO)






      There is one special consideration however, the context listed before
      the turnstile does not include the expression on the right of the
      turnstile itself! Hence, the implementation must be specifically
      exclude it from checks such as 'c:exp'.

      These functions may be affected
      * conjunctContextContaining
      * conjunctContext
      * conjunctCollection

      In addition, the following conventions are typically used for variable names:
      * ex            A single expression
      * exs@(e:es)    A list of expressions
      * ctx@(c:cs)    A context (given by a list of scopes)
      * r             A result
      * 'e'           A symbol (represented by the token "e")
      * <c>           The environment of a scope c
      * ^c^           The left-hand-side focus of a scope c (everything before the arrow)
      * a,b           An expression that is matched in more than one place (used for simple pattern
                      matching in the semantics)
      * ()            Bottom or "nothing" (implemented as an empty list of expressions)
      * _             Top or "anything" or "everything"

    BUGS:
      + (2011-06-28)
        Currently it's not too clear whether the matching code which must evaluate expressions
        in higher up contexts should perform error checking. Theoretically we want to check
        queries even when they do not return a result in order to build code like this
        '{ checkParameters result }:result' where checkParameters does not need to be evaluated
        for the result, but is necessary for proof code. However, exactly how this will work is not
        entirely certain for now - currently assuming that every context will be checked, but
        not checking context variables when doing a lookup in the scope (i.e. conjunctContext)
        in order to avoid double checking things. This is probably not correct though, it is
        more likely that results will have to be memoized to avoid repeating work.

        The main functions affected are
        * conjunctCollection
        * conjunctContext
        * evalWithConjunct
        * uncheckedEval

      + (2011-07-08)
        At the moment "Top" is treated almost like a regular symbol, however there are certain rules
        that should be implemented for performance reasons.
        For example a.(b _ c d) should really just evaluate a._
        On the other hand it might still be necessary to evaluate some sub-expressions for static
        checks, e.g. a.(b -> c b:c _ d) should still evaluate b:c and report a compiler error if it
        fails??? -- Actually, is this correct? After all "Top" matches all expressions.
        Probably the check for b:c is NOT necessary.

        However, what happens if we have the following:

        (a.(b -> c b:c) a._)

        This is not equivalent to either a.(b -> c b:c _) or (a.(b:c) a.(b -> c) a._) and might be
        indicative of further bugs in the implementation (although assertions have not yet
        been implemented, so technically this is not a problem yet)
-}

{-                                 MODULES                                  -}
-- Standard
import Control.Monad (foldM)

-- Chomp
import SyntaxTree

{-                              IMPLEMENTATION                              -}

-- Top level semantics

-- A scope is a collection of expressions where one expression is singled out as the "focus".
-- Scope variable will typically be used to construct a Context which is a stack of scopes.
-- Many operations must ignore the expression that has "focus", so the Scope type provides higher
-- order functions that eliminate the need to deal with the focus expression directly.
-- Scope is implemented using integer to index the focus and a list of expressions

type Scope = (Int, [Expression])

scopeFocus :: Scope -> Expression
scopeFocus (i,exs) = exs !! i

scopeFocusLHS :: Scope -> [Expression]
scopeFocusLHS s = lhs $ scopeFocus s
  where
    lhs (Eval (Declare lhsExs) rhs) = lhsExs
    lhs _ = error "IMPOSSIBLE ERROR: Only declarations can be the scope focus."

scopeEnv :: Scope -> [Expression]
scopeEnv (i,[])  = []
scopeEnv (i,exs) = take i exs ++ drop (i+1) exs

scopeMap :: (Expression -> b) -> Scope -> [b]
scopeMap f s = map f $ scopeEnv s

scopeEmpty :: Scope
scopeEmpty = (0,[])

-- A context is the path (stack of arrow declarations) leading to the current computation
-- The path consists of a list of scopes, each of which is a collection of expression plus a focus
-- Note that the top of the stack is the head of the list
type Context = [Scope]

contextEmpty :: Context
contextEmpty = [scopeEmpty]

--instance Show Context where
--  show c = ""

type Thunk = (Context, Expression)

-- The result of a computation. Allows eval to return Error
-- type Result = Maybe [Expression]
data Result a = Success [a] | Error
type EvalResult = Result Expression
type ThunkResult = Result Thunk

-- Auxiliary functions

-- Convert an empty list to an "error" result and a non-empty list to "success"
--listToResult :: [a] -> Result a
--listToResult [] = Error
--listToResult l  = Success l

-- Unwrap a result, converting an "error" value into an empty list
resultToList :: Result a -> [a]
resultToList (Success l) = l
resultToList Error       = []

-- Map a evaluation function over a set of expression and the fold the list into a Result
-- This function short-circuits as soon as an error is reached
foldEval :: (Expression -> EvalResult) -> [Expression] -> EvalResult
foldEval f (e:es) =
  case f e of
    (Success exs') -> case foldEval f es of
      (Success exs'') -> Success (exs' ++ exs'')
      Error       -> Error
    Error -> Error

-- Collect the results of two queries into one
-- (It is convenient to use this function infix similar to (++))
collect :: EvalResult -> EvalResult -> EvalResult
collect a b = Success $ resultToList a ++ resultToList b

-- Convert a collection into a result
assert :: [a] -> Result a
assert [] = Error
assert l  = Success l


{---------------------------- OLD

-- Attempt match an expression to the another expression inside the current context
-- Note that this is not just a simple equality test. There is a left-hand side expression and a
-- right-hand side expression and both may be queries themselves. Therefore both need to be
-- evaluated before they can be matched.
-- Furthermore (a -> b -> c) on the LHS will match (a -> b) on the RHS but (a -> b) on the LHS will
-- not match (a -> b -> c) on the RHS.
-- The function returns the result of the match as a new collection.

--matchExpression :: Context -> Expression -> Expression -> [Expression]
--matchExpression ctx  rhs =

-- Match an element inside a collection and return all matching expressions
-- TODO: NOT SURE IF THIS SHOULD RETURN A RESULT OR JUST A LIST OF EXPRESSIONS...
conjunctCollection :: Context -> [Expression] -> Expression -> [Expression]
conjunctCollection ctx []     ex = []
conjunctCollection ctx [e]    ex = evalWithConjunct ctx e ex
conjunctCollection ctx (e:es) ex = (evalWithConjunct ctx e ex) ++ (conjunctCollection ctx es ex)

-- Evaluate the left-hand side of a conjunct in order to match it to the right-hand side
-- TODO: This function almost certainly needs to be tested (possibly using smallcheck to generate
--       various contexts and then specific expression for the LHS and RHS... although it might not
--       be possible to match the expected result in this way, so might have to manually code
--       contexts and expected results)
-- TODO: NOT SURE IF THIS SHOULD RETURN A RESULT OR JUST A LIST OF EXPRESSIONS...

evalWithConjunct :: Context -> Expression -> Expression -> [Expression]
evalWithConjunct ctx _           (Eval (Assert _) [])     = error "IMPOSSIBLE ERROR: Not possible to have two selectors in succession."
evalWithConjunct ctx _           (Eval (Witness _) [])    = error "IMPOSSIBLE ERROR: Not possible to have two selectors in succession."
evalWithConjunct ctx _           (Eval (Assert _) ex1)    = error "IMPOSSIBLE ERROR: Right-hand query should have been evaluated before the left-hand query is evaluated."
evalWithConjunct ctx _           (Eval (Witness _) ex1)   = error "IMPOSSIBLE ERROR: Right-hand query should have been evaluated before the left-hand query is evaluated."
evalWithConjunct ctx ex0         Top                      = uncheckedEval ctx ex0
evalWithConjunct ctx (Symbol t0) ex1@(Symbol t1)          = if t0 == t1 then [ex1] else []
evalWithConjunct ctx (Symbol t0) ex1@(Eval (Declare _) _) = []
evalWithConjunct ctx Top         ex1                      = [ex1]
evalWithConjunct ctx Top         ex1                      = [ex1]


----------------- BUSY HERE: These are the more complicated cases...
evalWithConjunct ctx ex0@(Eval (Declare ex00) ex01) ex1   = error "TODO: ..... NOT SURE YET WHAT TO DO HERE"
--evalWithConjunct ctx ex0@(Eval _ _)                 ex1   = conjunctCollection (TODO: what context should be used here?) $ uncheckedEval ctx ex0 $ ex1


-- Find an expression in the given context and return all matching expressions
-- Note that the expression must not be stated in the same context that we are searching in (or it
-- will simply match itself, causing an infinite loop)
-- TODO: NOT SURE IF THIS SHOULD RETURN A RESULT OR JUST A LIST OF EXPRESSIONS...
conjunctContext :: Context -> Expression -> [Expression]
conjunctContext []         _  = []
conjunctContext [c]        ex = conjunctCollection contextEmpty (scopeEnv c) ex
conjunctContext ctx@(c:cs) ex = if matches /= [] then matches else conjunctContext cs ex
  where
    matches = conjunctCollection ctx (scopeEnv c) ex   -- TODO: IS THIS THE CORRECT CONTEXT TO PASS THROUGH?
                                                       --       POSSIBLY NEED TO LOOK AT THE CODE IN CONJUNCT
                                                       --       TO ENSURE CIRCULAR REFERENCES DO NOT TAKE PLACE

---------------------------}

-- Evaluates the expression inside the stack of contexts given
eval :: Context -> Expression -> EvalResult
context :: Context -> Expression -> [Context]
context c e = []

fullEval :: Context -> Expression -> ThunkResult
fullEval ctx ex =
  case evalResult of
    Success exs -> Success $ zip (context ctx ex) exs
    Error -> Error
  where
    evalResult = eval ctx ex

{- Evaluating a declaration has no effect
   --------------------------------------
   Only queries can be evaluated

   1.1) Evaluate a normal arrow

        (ctx |- exs0) -> exs1
        -------------------
        (ctx |- exs0) -> exs1

   1.2) Evaluate an 'inductive' arrow

        (ctx |- exs0) ->: exs1
        -------------------
        (ctx |- exs0) ->: exs1
-}

--eval ctx ex@(Eval (Declare exs0) exs1)
--  | True = Success [ex]


{-
  Evaluate conjunct queries outside of any context
  ------------------------------------------------

  Note) When assuming nothing / bottom (no context or scope given), we can rewrite the rule without
        a turnstile. (This is just a convenience that lets us make empty scope implicit, it has no
        effect on the actual operational semantics)

        (() |- exs0).exs1
        -----------------
            exs0.exs1

  2.1.1) Selecting any collection of expressions from Bottom produces Bottom, regardless of the
         context.

        ctx |- ().exs1
        --------------
             ()
-}

eval ctx@[] ex@(
    Eval
      (Witness (Conjunct exs1))
      []
  )
  | True = Success []

{-
  2.1.2) Selecting any collection of expressions from an atom produces Bottom (nothing).
         ('e0' is an atom/token and () is Bottom)

        'e0'.exs1
        ---------
           ()
-}

eval ctx@[] ex@(
    Eval
      (Witness (Conjunct exs1))
      [Symbol e0]
  )
  | True = Success []


{-
  2.1.3) Selecting any collection of expressions from Top simply returns the collection.

        _.exs1
        ------
         exs1
-}

eval ctx@[] ex@(
    Eval
      (Witness (Conjunct exs1))
      [Top]
  )
  | True = Success exs1


--context ctx@[] ex@(Eval (Witness (Conjunct exs1)) [(Symbol e0)])
--  | True = [[]]

{-
  2.2) Selecting a collection of expressions from another collection is equivalent to selecting the
       (right-hand side) collection from each element of the left-hand side collection.
       And vica versa...

           (e0 es0).exs1
        -------------------
        (e0.exs1  es0.exs1)

          ex0.(e1 es1)
        -----------------
        (ex0.e1  ex0.es1)
-}

eval ctx@[] ex@(
    Eval
      q'exs1@(Witness (Conjunct exs1))
      (e0:es0)
  )
  | True = eval [] (Eval q'exs1 [e0])
            `collect` eval [] (Eval q'exs1 es0)

--context ctx@[] ex@(Eval (Witness (Conjunct exs1)) (e0:es0))
--  | True = context [] (Eval (Witness (Conjunct exs1)) [e0])
--            ++ context [] (Eval (Witness (Conjunct exs1)) es0)

{-
  2.3) Selecting Top from a declaration returns the right-hand side of the arrow in the
     context of the left-hand side.

          (ex0 -> rhs0)._
        -------------------
        ex0 -> rhs0 |- rhs0
-}

-- TODO: add context
eval ctx@[] ex@(
    Eval
      (Witness (Conjunct [Top]))
      [Eval
        (Declare ex0)
        rhs0]
  )
  | True = Success rhs0

--context ctx@[] ex@(Eval (Witness (Conjunct [Top])) exs0@[(Eval (Declare ex0) rhs0)])
--  | True = [exs0]


{-
  2.4.1) Selecting from a chain does not heed bracketing
         Note: This definition should be used with care in the future when side effects are
               introduced.

        (ex0 -> (a -> rhs0)).(a -> rhs1)
        ---------------------------------
        (((ex0.a).rhs1) -> (a -> rhs1))._
-}



{-
  2.4.2) Selecting an expression from a declaration matches the right-hand side of the expression
         against the right-hand side of the declaration.
         (rhs can can either an atomic token like 'e' or a declaration like
         ('a' -> ('b' -> ('c' 'd')) -> 'e')).

        (ex0 -> a).a
        -------------
        ex0 -> a |- a

        (ex0 -> a).b
        ------------
             ()

            (ex0 -> (a -> rhs0)).a
        -------------------------------
        ex0 -> (a -> rhs0) |- a -> rhs0

        (ex0 -> (a -> rhs0)).b
        ----------------------
                  ()

  Note) It is possible formulate an alternative semantics using anonymous "closures" as follows:
        (This is nice for studying the semantics from a different view point but unnecessary for
        implementation) (TODO: but should there be context?).

        {exs0}._
        --------
          exs0

             {e0 es0}.exs1
        -----------------------
        ({e0}.exs1  {es0}.exs1)

           {e0}.(e1 es1)
        -------------------
        ({e0}.e1  {e0}.es1)

        {ex -> rhs}.ex
        --------------
          ex -> rhs

        {ex}.ex
        -------
          ex

        (ex0 -> rhs)._
        --------------
             rhs

        (ex0 -> rhs).exs1
        ----------------
           {rhs}.exs1


  Note Lemma) This works very simply for atomic tokens.

        {'e' -> rhs}.'e'
        ----------------
           'e' -> rhs

        {'e'}.'e'
        ---------
           'e'
-}

-- TODO: add contexts
eval ctx@[] ex@(
    Eval
      (Witness (Conjunct b))
      exs0@[Eval
        (Declare ex0)
        a]
  )
  | a == b    = Success exs0
  | otherwise = Success []

eval ctx@[] ex@(
    Eval
      (Witness (Conjunct b))
      [Eval
        (Declare ex0)
        exs'a@[Eval
          (Declare a)
          rhs0]]
  )
  | a == b    = Success exs'a
  | otherwise = Success []

{-
  2.5) When the right-hand side is a context-query it is equivalent to a query using the left-hand
       side (which we call the "context-domain" for convenience).
       Note that we don't write down a context at the bottom, because the query iteself (I.e. ex0.a
       should produce a context)

        (ex0 -> .a)._
        -------------
            ex0.a

        (ex0 -> .a).a
        -------------
            ex0.a

        (ex0 -> .a).b
        -------------
             ()
-}

eval ctx@[] ex@(
    Eval
      q'b@(Witness (Conjunct b))
      [Eval
        d'ex0@(Declare ex0)
        [Eval
          (Witness (Conjunct a))
          []]]
  )
  | b == [Top]  = eval [] (Eval q'b ex0)
  | a == b      = eval [] (Eval q'b ex0)
  | otherwise   = Success []

{-
  2.7) When the right-hand side is declaration from a context-query then it is equivalent to a
       declaration where the left-hand side is queried from the context-domain.

        (ex0 -> (.a -> rhs0))._
        -----------------------
             ex0.a -> rhs0

        (ex0 -> (.a -> rhs0)).a
        -----------------------
             ex0.a -> rhs0

        (ex0 -> (.a -> rhs0)).b
        -----------------------
                  ()
-}

eval ctx@[] ex@(
    Eval
      q'b@(Witness (Conjunct b))
      [Eval
        (Declare ex0)
        [Eval
          (Declare
            [Eval
              (Witness (Conjunct a))
              []])
          rhs0]]
  )
  | b == [Top]  = Success [Eval (Declare $ resultToList $ eval [] (Eval q'b ex0)) rhs0]
  | a == b      = Success [Eval (Declare $ resultToList $ eval [] (Eval q'b ex0)) rhs0]
  | otherwise   = Success []

{-
  2.8) When the context-query is a declaration only the first symbol in the chain needs to be
       matched.
       Note that selecting Top is handled by rule 2.5.

          (ex0 -> (.(a -> rhs0))).a
        ----------------------------
        (ex0 -> (ex0.(a -> rhs0))).a

        (ex0 -> (.(a -> rhs0))).b
        -------------------------
                   ()

        TODO: match chains....
-}

eval ctx@[] ex@(
    Eval
      q'b@(Witness (Conjunct b))
      [Eval
        (Declare ex0)
        [Eval
          (Declare
            [Eval
              (Witness (Conjunct a))
              []])
          rhs0]]
  )
  | b == [Top]  = Success [Eval (Declare $ resultToList $ eval [] (Eval q'b ex0)) rhs0]
  | a == b      = Success [Eval (Declare $ resultToList $ eval [] (Eval q'b ex0)) rhs0]
  | otherwise   = Success []

{-
  2.9) Selecting an expression from a declaration with multiple domains is equivalent to selecting
       from multiple declarations with a single domain.

              ((e0 es0) -> rhs0).exs1
        --------------------------------
        ((e0 -> rhs0).exs1 (es0 -> rhs0).exs1)

           (ex0 -> rhs0).(e1 es1)
        --------------------------------
        ((ex0 -> rhs0).e1 (ex0 -> rhs0).es1)
-}

eval ctx@[] ex@(
    Eval
      q'exs1@(Witness (Conjunct exs1))
      [Eval
        (Declare (e0:es0))
        rhs0]
  )
  | True = eval [] (Eval q'exs1 [Eval (Declare [e0]) rhs0])
            `collect` eval [] (Eval q'exs1 [Eval (Declare es0) rhs0])



{-
  Evaluate conjunct queries against a context
  -------------------------------------------
-}

{-
  3.1) Query against a single scope
       Note that {<c>}.exs1 will produce the original context c, but without .exs1 see rule 2.4.
       However, also note that simple lambdas (as in anonymous sets) can't be looked up in scope and
       thus this function (should) drop the first lambda from the resulting scope.

        c |- .exs1
        ----------
        {<c>}.exs1
-}

eval ctx@[c] ex@(
    Eval
      (Witness (Conjunct exs1))
      []
  )
  | True = eval [] (Eval (Witness (Conjunct exs1)) $ scopeEnv c)

{-
  3.3) Query against an arrow in a scope

        (cs1 |- (c0 -> exs1)).c0
        ------------------------
          cs1 |- (c0 |- .exs1)

-}

{-
  3.3) Query against two levels of scope

               cs1 |- (c0 |- .exs1)
        -------------------------------
        ({<c0>}.exs1 (cs1 |- ^c0^.exs1))

-}

eval ctx@(c:cs) ex@(
    Eval
      (Witness (Conjunct exs1))
      []
  )
  | True = eval ctx (Eval (Witness (Conjunct exs1)) $ scopeEnv c)
            `collect` eval cs (Eval (Witness (Conjunct exs1)) $ scopeFocusLHS c)

{-
  3.3) Query against a stack of scopes

                (cs |- (c1 |- (c0 |- .exs1))
        -------------------------------------------
        () |- (cs |- (c0 |- .exs1)  (c1 |- (c0 |- .exs1))


  Note) (c -> .exs)._
        -------------
          c |- .exs
-}



--        Success $
--          concat $ map (conjunctCollection ctx $ scopeEnv c) exs1
--            ++ uncheckedEval (cs

{-
  (cs |- c) |- :exs1
  ------------------
    cs |- c:exs1
-}

--eval ctx@(c:cs) ex@(Eval (Assert (Conjunct exs1)) [])
--  | True = assert $ uncheckedEval ctx ex

{-
ctx |- exs0.exs1
-----------------
?????ctx |- (exs0 |- .exs1)??
-}

--eval ctx ex@(Eval (Witness (Conjunct exs1)) exs0)
--  | True = Success $ concat $ map (conjunctContext ctx) exs0

{-
ctx |- exs0 . exs1
------------------
ctx |- ????????

(Eval (Witness (Conjunct exs0) exs1)

ctx |- exs0 \ exs1
------------------
ctx |- ????????

(Eval (Assert  (Complement exs0) exs1)

ctx |- exs0 \\ exs1
------------------
ctx |- ????????

(Eval (Witness (Complement exs0) exs1)

-}


-- Evaluates the expression exactly like eval, but ignoring any errors

--TODO: Just calling eval might not be correct, because it might only return a partial result
--      when it has an error... for now we're just assuming this is the correct implementation for
--      simplicity. Will come back to it later.
uncheckedEval :: Context -> Expression -> [Expression]
uncheckedEval ctx ex = resultToList $ eval ctx ex
