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
      * octx@(o:os)   The outer (or left-hand side) context
      * ictx@(i:is)   The inner (or right-hand side) context
      * s             The scope (environment and focus)
      * r             A result
      * 't'           A symbol (represented by the token "t")
      * <c>           The environment of a scope c
      * ^c^           The left-hand-side focus of a scope c (everything before the arrow)
      * a,b           An expression that is matched in more than one place (used for simple pattern
                      matching in the semantics)
      * as,bs         A collection that is matched in more than one place
      * ()            Bottom or "nothing" (implemented as an empty list of expressions)
      * _             Top or "anything" or "everything"
      * rhs           A collection of expressions on the right-hand side of a declaration


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

   TODO:
      + (2011-07-28)
        We are writing too much boilerplate with Success, Error results at the moment. It will be
        good to investigate a better interface for this in future.

      + (2011-07-31)
        Looking at evalConjunctMatch (in matches) and rules like octx |- (e00 e01 ... e0n).exs1 it
        seems like it MIGHT be more correct to make Context = [Thunk] as a sort of memoization
        mechanism.
        I.e. A thunk carries computational content inside its context.
        However, getting this to be perfomant/correct sounds like it might be challenging and will
        require some thought. I.e. we might want the the context to be modified in place using
        something like the State monad.
        I.e. In a way the context acts like the program "heap" (it is referentially transparent,
        but never-the-less we want to modify it in place in order to PARTIALLY memoize and avoid
        infinite loops. Should the domain at every level of the context stack be fully evaluated?
        Actually, since collections are conceptually evaluated simultaneously, using lightweight
        threads (sparks?) together with transactional memory might be the simplest implementation of
        this idea. Actually in a more optimized implementation we might use some specialized
        scheduling algorithm that partitions collections according to dependencies
        (using dataflow analysis?). In fact, it would be nice to create specialized data structures
        along the way (possibly transactional data structures).
-}

{-                                 MODULES                                  -}
-- Standard
import Control.Monad (foldM)

-- Chomp
import SyntaxTree

{-                              IMPLEMENTATION                              -}

-- Top level semantics

-- A scope is a collection of expressions where one expression is singled out as the "focus".
-- The scope is typically the last collection that acted as the domain for a query operation.
-- Passing along this scope separately from a context allows us to extract the codomain of a shared
-- parent domain and adding it to the context (as used in rule 2.2 currently)
-- Unlike context, scope cannot be modified or returned from an eval. It is used internally only.
--
-- TODO: Expand/clarify on the reasons why this is necessary once it becomes more clear...
--       Perhaps as follows:
--
-- Scope is only necessary in order to deal with collections - when the evaluator encounters a
-- composite operation that has a collection on the left-hand side, it needs to split up those
-- operations (divide & conquer) without loosing scope information (the other declarations in the
-- same collection. If collections were restricted to one expression only, then scope will always be
-- empty and can be removed.
--
-- The scope in a sense is used to pass along contextual information when the eval function cannot
-- immediately determine what information needs to go into the context and once it can that
-- information is already lost. Only one level of scope need to be passed along to any eval function
-- all other scoping information is captured in the context.
-- Thus the scope holds a kind of delayed context which is not refined immediately, only later on
-- when a base case is reached.
--
-- TODO: It is possible that in the future the scope may also be used to memoize the result of
--       queries directly inside the scope, avoiding duplicate computations and possibly simplifying
--       lookup into the context.
--
-- Scope is implemented using an integer to index the focus and a list of expressions.

type Scope = (Int, [Expression])

scopeFocus :: Scope -> Expression
scopeFocus (i,exs) = exs !! i

--scopeFocusLHS :: Scope -> [Expression]
--scopeFocusLHS s = lhs $ scopeFocus s
--  where
--    lhs (Eval (Declare lhsExs) rhs) = lhsExs
--    lhs _ = error "IMPOSSIBLE ERROR: Only declarations can be the scope focus."

--scopeFocusRHS :: Scope -> [Expression]
--scopeFocusRHS s =

scopeEnv :: Scope -> [Expression]
scopeEnv (i,[])  = []
scopeEnv (i,exs) = take i exs ++ drop (i+1) exs

scopeMap :: (Expression -> b) -> Scope -> [b]
scopeMap f s = map f $ scopeEnv s

scopeEmpty :: Scope
scopeEmpty = (0,[])

-- A context is the path (stack of arrow declarations) along with the relevant expressions in scope
-- that leads to the current computation
-- Note that the top of the stack is the head of the list
-- Note: It may (?) be more efficient to use a finger tree to store the various paths of a context,
--       however, we are more concerned with correctness and simplicity than efficiency at this
--       stage.
--type Context = [Scope]
type Context = [[Expression]]

--contextEmpty :: Context
--contextEmpty = [scopeEmpty]

--instance Show Context where
--  show c = ""

-- A thunk contains the context (the outer or left-hand side context) and an expression to evaluate
-- inside that context.
type Thunk = (Context, Expression)

-- The result of a computation. Allows eval to return Error
-- type Result = Maybe [Expression]
data Result a = Success [a] | Error deriving Eq
type ResultExpression = Result Expression
type ResultThunk = Result Thunk

-- Auxiliary functions
{-
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
foldEval :: (Expression -> ResultExpression) -> [Expression] -> ResultExpression
foldEval f (e:es) =
  case f e of
    (Success exs') -> case foldEval f es of
      (Success exs'') -> Success (exs' ++ exs'')
      Error       -> Error
    Error -> Error

-- Collect the results of two queries into one
-- (It is convenient to use this function infix similar to (++))
collect :: ResultExpression -> ResultExpression -> ResultExpression
collect a b = Success $ resultToList a ++ resultToList b

-- Convert a collection into a result
assert :: [a] -> Result a
assert [] = Error
assert l  = Success l
-}

mapResult :: (a -> Result b) -> [a] -> Result b
mapResult f []     = Success []
mapResult f [t]    = f t
mapResult f (t:ts) =
  case f t of
    Error -> Error
    Success t' -> case mapResult f ts of
      Error       -> Error
      Success ts' -> Success $ t' ++ ts'

mapResultResult :: (a -> Result b) -> Result a -> Result b
mapResultResult f (Success r) = mapResult f r
mapResultResult f Error       = Error

{-
mapEval :: [Thunk] -> ResultThunk
mapEval []     = Success []
mapEval [t]    = eval t
mapEval (t:ts) =
  case eval t of
    Error -> Error
    Success t' -> case mapEval ts of
      Error       -> Error
      Success ts' -> Success $ t' ++ ts'
-}

mapEval :: [Thunk] -> ResultThunk
mapEval = mapResult eval

-- Map eval over a new expression formed from an existing expression and context on the left-hand
-- side (I.e. the existing expression is an "outer" expression)
mapEvalOuter :: ([Expression] -> Expression) -> ResultThunk -> ResultThunk
mapEvalOuter f result =
  case result of
    Success r -> mapEval $ map (mapThunk $ f . (:[])) r
    Error     -> Error
  where
    mapThunk f (a,b) = (a,f b)

-- Map eval over a new expression formed from an existing expression on the right-hand side
-- (I.e. the existing expression is an "inner" expression)
mapEvalInner :: Context -> ([Expression] -> Expression) -> ResultThunk -> ResultThunk
mapEvalInner octx f result =
  case result of
    Success r -> mapEval $ map (mapThunk $ f . (:[])) r
    Error     -> Error
  where
    mapThunk f (_,b) = (octx, f b)

-- Map eval over a list of expressions with a single context
mapEvalWith :: Context -> [Expression] -> ResultThunk
mapEvalWith ctx exs = mapEval $ map ((,) ctx) exs

-- Evaluate two declarations in lock-step and
{-
evalConjunctLockStep :: [Expression] -> [Expression] -> [Expression] -> [Expression] -> Expression
evalConjunctLockStep lhsDomain lhsCodomain rhsDomain rhsCodomain =
    case matches lhsDomain rhsDomain of
      Error          -> Error
      Success domain ->
        case matches lhsCodomain rhsCodomain of
          Error             -> Error
          Success codomain  -> Success (Eval (Declare domain) codomain)
  where
    matches :: [Expression] -> [Expression] -> ResultThunk
    matches lhs rhs = liftM2 match lhs rhs
      where
        match :: Expression -> Expression -> ResultThunk
        match lhs rhs =
-}




-- Evaluates an expression against the left-hand side domain of a collection (usually the context)
-- and returns the right-hand side.
-- ctx |- lhs.rhs
{-
evalConjunctMatch :: Context -> Expression -> Expression -> ResultThunk
evalConjunctMatch ctx@(c:cs) lhs rhs =
  case mapResult (lhsMatches ctx) c of
    Success r ->
      case evalConjunctMatch cs lhs rhs of
        Success rs -> Success $ r ++ rs
        Error      -> Error
    Error     -> Error
  where
    evalCodomain codomain = mapEvalWith codomain

    lhsMatches :: Context -> Expression -> ResultThunk
    lhsMatches ctx Top        = Success [([], Top)]
    lhsMatches ctx (Symbol _) = Success []
    lhsMatches ctx (Eval (Declare domain) codomain) =
      if any (lhs ==) domain
        -- then Success $ (map ((,) ctx) codomain)
        then (mapResultResult $ (rhsMatches ctx) . snd) $ mapEvalWith (domain:ctx) codomain
        else mapResult (lhsMatches ctx) domain         -- TODO: $ mapEvalWith ctx domain?
    lhsMatches ctx (Eval (Assert _) _)  = error "Fatal Error (Pre-condition for evalConjunctMatch): In the current implementation the context domain must not have embedded queries."
    lhsMatches ctx (Eval (Witness _) _) = error "Fatal Error (Pre-condition for evalConjunctMatch): In the current implementation the context domain must not have embedded queries."
    lhsMatches ctx _                    = error "Fatal Error (Pre-condition for evalConjunctMatch): Unknown expression pattern."

    rhsMatches :: Context -> Expression -> ResultThunk
    rhsMatches ctx Top =
      Success [(ctx, rhs)]
    rhsMatches ctx ex@(Symbol t) =
      Success $ if rhs == ex || rhs == Top then [(ctx, ex)] else []
    rhsMatches ctx ex@(Eval (Declare domain) codomain) =
      if rhs == ex
        --then Success [(ctx, ex)]
        then
        else mapResult (rhsMatches ctx) domain
    rhsMatches ctx (Eval (Assert _) _)  = error "Fatal Error (Pre-condition for evalConjunctMatch): The context codomain should have been evaluated before rhsMatches is called."
    rhsMatches ctx (Eval (Witness _) _) = error "Fatal Error (Pre-condition for evalConjunctMatch): The context codomain should have been evaluated before rhsMatches is called."
    rhsMatches ctx _                    = error "Fatal Error (Pre-condition for evalConjunctMatch): Unknown expression pattern."
-}

-- Evaluates a thunk (and expression inside a context)
eval :: Thunk -> ResultThunk

{- Evaluating symbols
   ------------------
   ?) Evaluating any symbol has no effect

        octx |- 't'
        -----------
        octx |- 't'

        octx |- _
        ---------
        octx |- _

        octx |- ()    (This rule is implicit in mapEval)
        ----------
            ()
-}

eval thunk@(octx, ex@(
    Symbol t
  ))
  | True = Success [thunk]

eval thunk@(octx, ex@(
    Top
  ))
  | True = Success [thunk]

{- Evaluating a declarations
   -------------------------
   1.1) Evaluating a declaration simply returns the declaration itself, unless the domain of the
        arrow is Bottom (I.e. there are no symbols in the domain to attach an arrow to)
        Note that the domain needs to be evaluated to determine if it is empty.

        octx |- () -> exs1
        -------------------
                ()

        octx |- exs0 -> exs1
        -------------------
        octx |- exs0 -> exs1
-}

eval (octx, ex@(
    Eval
      (Declare [])
      exs1
  ))
  | True = Success []

eval thunk@(octx, ex@(
    Eval
      (Declare exs0)
      exs1
  ))
  | True = case mapEval $ map ((,) octx) exs0 of
      Success [] -> Success []
      Success _  -> Success [thunk]
      Error      -> Error

{-
   1.? Evaluate an 'inductive' arrow
       TODO: this might complicate rule 1.1

        ctx |- exs0 ->: exs1
        --------------------
        ctx |- exs0 ->: exs1
-}


{-
  Evaluate conjunct queries outside of any context
  ------------------------------------------------

  Note) When assuming nothing / bottom (no context or scope given), we can rewrite the rule without
        a turnstile. (This is just a convenience that lets us make empty scope implicit, it has no
        effect on the actual operational semantics)

        () |- exs0.exs1
        ---------------
           exs0.exs1

  2.1.1) Selecting any collection of expressions from Bottom produces Bottom, regardless of the
         context.

        octx |- ().exs1
        ---------------
              ()
-}

eval (_, ex@(
    Eval
      (Witness (Conjunct exs1))
      []
  ))
  | True = Success []

{-
  2.1.2) Selecting any collection of expressions from an atom outside of any context produces
         Bottom (nothing).

        't0'.exs1
        ---------
           ()
-}

eval (octx@[], ex@(
    Eval
      (Witness (Conjunct exs1))
      [Symbol t0]
  ))
  | True = Success []

{-
  2.1.3) Selecting any collection of expressions from Top simply returns the collection in the
         context of Top. This means that any query acting on the result of this computation will
         succeed, however the result can still be used on the right-hand side of another query to
         refine another codomain.

         octx |- _.exs1
         --------------
           _ |- exs1
-}

eval (octx, ex@(
    Eval
      (Witness (Conjunct exs1))
      [Top]
  ))
  | True =
    case mapEvalWith octx exs1 of
      Success r -> Success $ map (((,) [[Top]]) . snd) r
      Error     -> Error

{-
  2.1.4) First evaluate subqueries before evaluating the full query.

        In the first case the context returned from the left-hand subquery is carried over to the
        main query. Note that this also is the natural bracketing for a query of the form
        'exs0.qs0.exs1'. It can never happen that exs1 is the result of a query evaluated on the
        right-hand side because the left-hand side is always fully evaluated first (due to the order
        of the following two rules) - thus exs1 cannot have an internal context.

        octx |- (exs0.qs0).exs1
        -----------------------
        (octx |- exs0.qs0).exs1   with (octx |- exs0.qs0) evaluated first (this may be multiple
                                  expressions with multiple contexts)

        In the second case, note that the left-hand side collection does not affect the right-hand
        side subquery in any way, although the context passed in to this rule may affect either
        query.

            octx |- exs0.(exs1.qs1)
        -------------------------------
        octx |- exs0.(octx |- exs1.qs1)   with (octx |- exs1.q1) evaluated first (this may be
                                          multiple expressions but only the single outer context is
                                          used in the outer query.

        TODO: This rule could possibly be extended to all types of queries...
-}

eval (octx, ex@(
    Eval
      q'exs1@(Witness (Conjunct exs1))
      [ex'qs0@(Eval
        (Witness (Conjunct qs0))
        exs0)]
  ))
  | True = mapEvalOuter (Eval q'exs1) $ eval (octx, ex'qs0)


eval (octx, ex@(
    Eval
      (Witness (Conjunct
        [ex'qs1@(Eval
          (Witness (Conjunct qs1))
          exs1)]))
      exs0
  ))
  | True = mapEvalInner octx (\e -> Eval (Witness (Conjunct e)) exs0) $ eval (octx, ex'qs1)

{-
  2.2) Selecting a collection of expressions from another collection is equivalent to selecting each
       right-hand side element from the entire left-hand side collection and vica versa

                              octx |- (e00 e01 ... e0n).exs1
        ---------------------------------------------------------------------------------
        ((octx,(e00 e01 ... e0n) |- e00.exs1)  ...  (octx,(e00 e01 ... e0n) |- e0n.exs1))

          (Note: (e00 ... e0n) must be explicitly evaluated inside the context the collection
          provides)

                                octx |- ex0.(e10 e11 ... e1n)
        ---------------------------------------------------------------------------------------------------
        ((octx |- ex0.(octx,(e10 e11 ... e1n) |- e10))  ...  (octx |- ex0.(octx,(e10 e11 ... e1n) |- e1n)))

          (Note: (e10 ... e1n) must be explicitly evaluated inside the context the collection
          provides)

      TODO: This implementation is not quite correct. Each (e00/e10 ... e0n/e1n) must be evaluated
            yet the collection simultaneously requires itself as a context while it is being
            evaluated.
            See evalConjunctMatch: it currently requires each domain in the context to be fully
            memoized.
            We might need to create a specialized version of mapEvalWith to take this into account
            E.g. evalCollection
-}

eval (octx, ex@(
    Eval
      q'exs1@(Witness (Conjunct exs1))
      exs0@(e0:es0)
  ))
  | True = mapEvalOuter (\e0 -> Eval q'exs1 e0) eval'exs0
  where
    eval'exs0 = mapEvalWith (exs0:octx) exs0
    -- TODO: This version does not memoize exs0 in the context of eval'exs0, which may be
    --       problematic. I.e. we do not have
    --       eval'exs0 = mapEvalWith (eval'exs0:octx) exs0
    --       since eval'exs0 is being evaluated. We also can't substitute (eval'exs0:octx) on the
    --       outside because the context may also be modified by evaluating by exs0

eval (octx, ex@(
    Eval
      (Witness (Conjunct exs1@(e1:es1)))
      exs'ex0@[ex0]
  ))
  | True = mapEvalInner octx (\e1 -> Eval (Witness (Conjunct e1)) exs'ex0) eval'exs1
  where
    eval'exs1 = mapEvalWith (exs1:octx) exs1

{- 2.?) Query with a symbol on the left-hand side. This may return a different (smaller context as
        the query looks "up" in the context.

           c |- 't0'.ex1
        --------------------
        ({c}.('t0' -> _)).ex1

                       cs,c |- 't0'.ex1
        -------------------------------------------------
        ((cs |- 't0'.ex1)  (cs |- ({c}.('t0' -> _)).ex1))

        Note: The implementation might differ a bit from the semantics here simply for performance
        reasons

        (Lemmas:

                          cs,c |- 't0'._
          ---------------------------------------------
          ((cs |- 't0'._)  (cs |- ({c}.('t0' -> _))._))

                         cs,c |- 't0'.'t1'
          ------------------------------------------------------
          ((cs |- 't0'.'t1')  (cs |- ({c}.('t0' -> 't1')).'t1'))
        )
-}

eval ([c], ex@(
    Eval
      q'ex1@(Witness (Conjunct [ex1]))
      exs't0@[(Symbol t0)]
  ))
  | True = eval ([],
      Eval
        q'ex1
        [Eval
          (Witness (Conjunct [Eval (DeclareLambda Nothing) c]))
          [Eval (Declare exs't0) [Top]]])


eval (c:cs, ex@(
    Eval
      q'ex1@(Witness (Conjunct [ex1]))
      [ex't0@(Symbol t0)]
  ))
  | True = mapEvalWith cs [
      ex,
      Eval
        (Witness (Conjunct [Eval (DeclareLambda Nothing) c]))
        [Eval (Declare [Symbol t0]) [Top]]]

{- 2.?  Query with an arrow on the left-hand side

                 octx |- ('t0' -> r0 -> rs0).(ictx |- (e0 -> es0))
        ------------------------------------------
        octx |- ({octx}.(ex0 -> rhs0) {octx}.ex0).(ictx |- ex1)
-}

{- 2.?  Query with an arrow on the left-hand side

                 octx |- (ex0 -> rhs0).(ictx |- ex1)
        ------------------------------------------
        octx |- ({octx}.(ex0 -> rhs0) {octx}.ex0).(ictx |- ex1)
-}


{-
  2.3) Selecting Top from a declaration returns the right-hand side of the arrow in the
       context of the left-hand side, only if the left-hand side does not evaluate to Bottom.
       This holds regardless of the context.

        ctx |- (() -> rhs0)._
        ---------------------
                  ()

        ctx |- (exs0 -> _)._      (This rule would be implicit except that context can be discarded)
        --------------------
                  _

         ctx |- (exs0 -> rhs0)._
        -------------------------
        ctx, exs0 -> rhs0 |- rhs0
-}

eval (ctx, ex@(
    Eval
      (Witness (Conjunct [Top]))
      [ex'exs0@(Eval
        (Declare [])
        rhs0)]
  ))
  | True = Success []

eval (ctx, ex@(
    Eval
      (Witness (Conjunct [Top]))
      [ex'exs0@(Eval
        (Declare exs0)
        [Top])]
  ))
  | True = if mapEvalWith ctx exs0 == Error then Error else Success [([], Top)]

eval (ctx, ex@(
    Eval
      (Witness (Conjunct [Top]))
      exs'exs0@[Eval
        (Declare exs0)
        rhs0]
  ))
  | True =
    case mapEvalWith ctx exs0 of
      Success [] -> Success []
      Success _  -> Success $ map ((,) (exs'exs0:ctx)) rhs0
      Error      -> Error

{-
  2.?)
        ctx |- (exs0 -> 'a').'b'
        ------------------------
                  ()

        ctx |- (exs0 -> 'a').'a'
        ------------------------
         ctx,exs0 -> 'a' |- 'a'

        ctx |- (exs0 -> _).'a'
        ----------------------
        ctx,exs0 -> 'a' |- 'a'
-}

eval (octx, ex@(
    Eval
      q'exs1@(Witness (Conjunct
        [Symbol b]))
      exs'exs0@[Eval
        (Declare exs0)
        [ex'a@(Symbol a)]]
  ))
  | a == b    = if mapEvalWith octx exs0 == Error then Error else Success [(exs'exs0:octx, ex'a)]
  | otherwise = if mapEvalWith octx exs0 == Error then Error else Success []

eval (octx, ex@(
    Eval
      q'exs1@(Witness (Conjunct
        [ex'a@(Symbol a)]))
      exs'exs0@[Eval
        (Declare exs0)
        [Top]]
  ))
  | True      = if mapEvalWith octx exs0 == Error then Error else Success [(exs'exs0:octx, ex'a)]

{- Selecting multiple expression from a declaration is equivalent to selecting each expression
   individually, except for context...... TODO

               (ex0 -> rhs0).(e1 es1)
        ------------------------------------
        ((ex0 -> rhs0).e1 (ex0 -> rhs0).es1)

                    (ex0 -> rhs0).((e1 es1) -> rhs1)
        --------------------------------------------------------
        ((ex0 -> rhs0).(e1 -> rhs1) (ex0 -> rhs0).(es1 -> rhs1))
-}




{-
  2.4.1) Selecting an expression from a declaration matches the right-hand side of the expression
         against the right-hand side of the declaration.
         Note that ex0 can be complex expression like (d -> c -> f), so selecting
         ((d -> c -> f) -> a).a will still return a regardless of the structure of ex0.
         However, ex0 must not be Bottom, thus it needs to be evaluated first to determine whether
         it is enhabitted by any values.

        (ex0 -> a).a
        -------------
        ex0 -> a |- a

        (ex0 -> a).b
        --------------
              ()
-}

--eval ctx@[] ex@(
--    Eval
--      (Witness (Conjunct [b]))
--      exs0@[Eval
--        (Declare ex0)
--        [a]]
--  )
--  | a == b    = if eval ex0 not empty then Success exs0

{-
  2.4.2) Selecting from a chained expression matches against the first link in the chain (if the
         entire chain could not be matched)

            (ex0 -> (a -> rhs0)).a
        -------------------------------
        ex0 -> (a -> rhs0) |- a -> rhs0

        (ex0 -> (a -> rhs0)).b
        ----------------------
                   ()
-}
{-
eval ctx@[] ex@(
    Eval
      (Witness (Conjunct [b]))
      [Eval
        (Declare ex0)
        exs'a@[Eval
          (Declare [a])
          rhs0]]
  )
  | a == b    = Success exs'a
  -- | otherwise = Success []  (Handled in 2.10)
-}
{-
  2.4.3) Selecting from a chain does not heed bracketing
         Note: This definition should be used with care in the future when side effects are
               introduced.

            (ex0 -> (a -> rhs0)).(b -> rhs1)
        -----------------------------------------
        (ex0 -> a).b -> (ex0 -> (a -> rhs0)).b.rhs1

        (ex0 -> (a -> rhs0)).(b -> rhs1)
        --------------------------------
                       ()
-}
{-
eval ctx@[] ex@(
    Eval
      (Witness (Conjunct [Eval (Declare [b]) rhs1]))
      exs'a@[Eval
        (Declare ex0)
        [Eval
          (Declare [a])
          rhs0]]
  )
  | a == b    = eval [] (Eval
                          (Declare
                            [Eval
                              (Witness (Conjunct [b]))
                              [Eval (Declare ex0) [a]]])
                          [Eval
                            (Witness (Conjunct rhs1))
                            [Eval
                              (Witness (Conjunct [b]))
                              exs'a]])
  -- | otherwise = Success []  (Handled in 2.10)
-}
{-
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
{-
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
  -- | otherwise   = Success []
-}
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
{-
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
  -- | otherwise   = Success []
-}
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
{-
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
  -- | otherwise   = Success []
-}
{-
  2.10) Evaluate all queries with no context that has an empty result

  (2.4.1)
        (ex0 -> a).b
        ------------
             ()

  (2.4.2)
        (ex0 -> (a -> rhs0)).(b -> rhs1)
        --------------------------------
                       ()

  (2.4.3)
        (ex0 -> (a -> rhs0)).b
        ----------------------
                   ()

  (2.5)
        (ex0 -> .a).b
        -------------
             ()

  (2.7)
        (ex0 -> (.a -> rhs0)).b
        -----------------------
                  ()

  (2.8)
        (ex0 -> (.(a -> rhs0))).b
        -------------------------
                   ()

-}
{-
eval ctx@[] ex = Success []
-}


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
{-
eval ctx@[c] ex@(
    Eval
      (Witness (Conjunct exs1))
      []
  )
  | True = eval [] (Eval (Witness (Conjunct exs1)) $ scopeEnv c)
-}
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


        TODO: This isn't currently possible because the representation of cs1 |- (c0 |- ().exs1)
              is exactly the same.
              We'll probably need to match something like (a ->. b).c instead for this to work.

-

eval ctx@(c:cs) ex@(
    Eval
      (Witness (Conjunct exs1))
      []
  )
  | True = eval ctx (Eval (Witness (Conjunct exs1)) $ scopeEnv c)
            `collect` eval cs (Eval (Witness (Conjunct exs1)) $ scopeFocusLHS c)
--}

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
--uncheckedEval :: Context -> Expression -> [Expression]
--uncheckedEval ctx ex = resultToList $ eval (ctx, ex)
