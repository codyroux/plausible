import Lean.Expr
import Batteries
import Plausible.Chamelean.Utils
import Plausible.Chamelean.Schedules
import Plausible.Chamelean.UnificationMonad
import Plausible.Chamelean.MakeConstrainedProducerInstance
import Plausible.Chamelean.LazyList


open Lean Meta

-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newGenericLib.ml

/-- Extracts all the unique variable names that appear in a hypothesis of a constructor for an inductive relation
    (this looks underneath constructor applications).

    For example, given `typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)`,
    this function returns `[Γ, τ1, e, τ2]`.
 -/
partial def variablesInHypothesisTSyntax (term : TSyntax `term) : MetaM (List Name) :=
  match term with
  | `($id:ident) => return [id.getId.eraseMacroScopes]
  | `($_:ident $args:term*)
  | `(($_:ident $args*)) => do
    -- Note that we have to explicitly pattern match on parenthesized constructor applications,
    -- otherwise we won't be able to handle nested constructor applications, e.g. `typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)`
    let foo ← args.toList.flatMapM variablesInHypothesisTSyntax
    return (List.eraseDups foo)
  | _ => return []

/-- Extracts all the unique variable names that appear in a `ConstructorExpr`
    (this looks underneath constructor applications). -/
def variablesInConstructorExpr (ctorExpr : ConstructorExpr) : List Name :=
  match ctorExpr with
  | .Unknown u => [u]
  | .Ctor _ args | .FuncApp _ args => args.flatMap variablesInConstructorExpr

/-- Given a hypothesis `hyp`, along with `binding` (a list of variables that we are binding with a call to a generator), plus `recCall` (a pair contianing the name of the inductive and a list of output argument indices),
    this function checks whether the generator we're using is recursive.

    For example, if we're trying to produce a call to the generator [(e, tau) <- typing gamma _ _], then
    we would have `binding = [e,tau]` and `hyp = typing gamma e tau`. -/
def isRecCall (binding : List Name) (hyp : HypothesisExpr) (recCall : Name × List Nat) : MetaM Bool := do
  let (ctorName, args) := hyp
  -- An output position is a position where all vars contained are unbound
  -- if they are unbound, we include them in the list of output indices (`outputPositions`)
  let outputPositions ← filterMapMWithIndex (fun i arg => do
    let vars := variablesInConstructorExpr arg
    if vars.isEmpty then pure none
    else if List.all vars (. ∈ binding) then
      pure (some i)
    else if List.any vars (. ∈ binding) then do
      let v := List.find? (· ∈ binding) vars
      logError m!"error: {v} ∈ {binding} = binding"
      throwError m!"Arguments to hypothesis {hyp} contain both fixed and yet-to-be-bound variables (not allowed)"
    else pure none) args
  let (inductiveName, recCallOutputIdxes) := recCall

  return (ctorName == inductiveName && (recCallOutputIdxes.mergeSort) == (outputPositions.mergeSort))


/-- Given a list of `hypotheses`, creates an association list mapping each hypothesis to a list of variable names.
    This list is then sorted in ascending order based on the length of the variable name list.
    (This is a heuristic, since we would like to work w/ hypotheses that have fewer variables first (fewer generation options to deal with).) -/
def mkSortedHypothesesVariablesMap (hypotheses : List HypothesisExpr) : List (HypothesisExpr × List (List Name)) :=
  let hypVarMap := hypotheses.map (fun h@(_, ctorArgs) =>
    (h, ctorArgs.map variablesInConstructorExpr))
  List.mergeSort hypVarMap (le := fun (_, vars1) (_, vars2) => vars1.flatten.length <= vars2.flatten.length)

/-- Environment for the `ScheduleM` reader monad -/
structure ScheduleEnv where
  /-- List of variables which are universally-quantified in the constructor's type,
      along with the types of these variables -/
  vars : List (Name × Expr)

  /-- Hypotheses about the variables in `vars` -/
  sortedHypotheses : List (HypothesisExpr × List (List Name))

  /-- Determines whether we're deriving a checker/enumerator/generator -/
  deriveSort : DeriveSort

  /-- The sort of auxiliary producer (generators / enumerators) invoked by
      the function being derived. Note that if `deriveSort = Checker`, then
      `prodSort = Enumerator`, since checkers have to invoke enumerators
      as discussed in the Computing Correctly paper. -/
  prodSort : ProducerSort

  /-- A pair contianing the name of the inductive relation and a list of indices for output arguments -/
  recCall : Name × List Nat

  /-- A list of fixed variables (i.e. inputs to the inductive relation) -/
  fixed : List Name

/-- A monad for deriving generator schedules. Under the hood,
    `ScheduleM` is just a reader monad stacked on top of `MetaM`,
    with `ScheduleEnv` serving as the environment for the reader monad. -/
abbrev ScheduleM (α : Type) := ReaderT ScheduleEnv MetaM α

/-- After we generate some variables, look at the hypotheses and see if any of them only contain fixed variables
    (if yes, then we need to check that hypothesis)
    - `checkedHypotheses` contains the hypotheses that have been checked so far  -/
def collectCheckSteps (env : ScheduleEnv) (boundVars : List Name) (checkedHypotheses : List Nat) : List (Nat × Source) := do
  let (inductiveName, inputArgs) := env.recCall

  let checkSteps := filterMapWithIndex (fun i (hyp, vars) =>
    if i ∉ checkedHypotheses && List.all vars (List.all . (. ∈ boundVars)) then
      let (ctorName, ctorArgs) := hyp
      let src :=
        if env.deriveSort == .Checker && inputArgs.isEmpty && ctorName == inductiveName then
          Source.Rec `aux_dec ctorArgs
        else .NonRec hyp
      some (i, src)
    else none) env.sortedHypotheses

  checkSteps

/-- Determines whether inputs & outputs of a generator appear under the same constructor in a hypothesis `hyp`
    - Example: consider the `TApp` constructor for STLC (when we are generating `e` such that `typing Γ e τ` holds):
    ```
    | TApp: ∀ Γ e1 e2 τ1 τ2,
      typing Γ e2 τ1 →
      typing Γ e1 (.Fun τ1 τ2) →
      typing Γ (.App e1 e2) τ2
    ```
    The hypothesis `typing Γ e1 (.Fun τ1 τ2)` contains a term `.Fun τ1 τ2` where
    the existentially quantified variable `τ1` hasn't been generated yet,
    whereas `τ2` is an input to the generator (since it appears in the conclusion of `TApp`).
    Since `τ1, τ2` both appear under the same `.Fun` constructor,
    `outputInputNotUnderSameConstructor (.Fun τ1 τ2) [τ2]` returns `false`.  -/
def outputInputNotUnderSameConstructor (hyp : HypothesisExpr) (outputVars : List Name) : ScheduleM Bool := do
  let (_, args) := hyp
  let result ← not <$> args.anyM (fun arg => do
    let vars := variablesInConstructorExpr arg
    return List.any vars (. ∈ outputVars) && List.any vars (. ∉ outputVars))
  return result

/-- Determines whether the variables in `outputVars` are constrained by a function application in the hypothesis `hyp`.
    This function is necessary since we can't output something and then assert that it equals the output of a (non-constructor) function
    (since we don't have access to the function). -/
partial def outputsNotConstrainedByFunctionApplication (hyp : HypothesisExpr) (outputVars : List Name) : ScheduleM Bool :=
  let (_, args) := hyp
  not <$> args.anyM (fun arg => check false arg)
    where
      check (b : Bool) (arg : ConstructorExpr) : ScheduleM Bool :=
        match arg with
        | .Unknown u => return (b && u ∈ outputVars)
        | .Ctor _ args => args.anyM (check b)
        | .FuncApp _ args => args.anyM (check true)

/-- If we have a hypothesis that we're generating an argument for,
     and that argument is a constructor application where all of its args are outputs,
     then we just need to produce a backtracking check

     e.g. if we're trying to generate `TFun t1 t2 <- typing G e (TFun t1 t2)`,
     we have to do:
     ```
       v_t1t2 <- typing G e v_t1t2
       match v_t1t2 with
       | TFun t1 t2 => ...
       | _ => none
     ```
     assuming t1 and t2 are *unfixed* (not an input and not generated yet)

     The triple that is output consists of:
     - the list of pattern-matches that need to be produced
       (since TT can handle multiple outputs, each of which may need to be constrained by a pattern)
     - the updated thing we're generating for (e.g. `typing G e v_t1t2` in the example above), ie the RHS of the let-bind
     - the updated output list (e.g. `v_t1t2` in the example above), ie the LHS of the let-bind -/
def handleConstrainedOutputs (hyp : HypothesisExpr) (outputVars : List Name) : MetaM (List ScheduleStep × HypothesisExpr × List Name) := do
  let (ctorName, ctorArgs) := hyp

  let (patternMatches, args', newOutputs) ← splitThreeLists <$> ctorArgs.mapM (fun arg =>
    let vars := variablesInConstructorExpr arg
    match arg with
    | .Ctor _ _ =>
      if !vars.isEmpty && List.all vars (. ∈ outputVars) then do
        let localCtx ← getLCtx
        let newName := localCtx.getUnusedName (Name.mkStr1 ("v" ++ String.intercalate "_" (Name.getString! <$> vars)))
        match patternOfConstructorExpr arg with
        | none => throwError m!"ConstructorExpr {arg} fails to be converted to pattern in handleConstrainedOutputs"
        | some pat =>
          let newMatch := ScheduleStep.Match newName pat
          pure (some newMatch, .Unknown newName, some newName)
      else
        pure (none, arg, none)
    | .Unknown v =>
      if v ∈ outputVars then
        pure (none, arg, some v)
      else
        pure (none, arg, none)
    | .FuncApp _ _ =>
      pure (none, arg, none))

  return (patternMatches.filterMap id, (ctorName, args'), newOutputs.filterMap id)

/-- Converts a list of `ScheduleStep`s to *normal form* (i.e. all unconstrained generation
    occurs before constrained generation) -/
def normalizeSchedule (steps : List ScheduleStep) : List ScheduleStep :=
  -- `unconstrainedBlock` is a list of `ScheduleStep`s consisting only of unconstrianed generation
  -- (i.e. calls to `arbitrary`)
  let rec normalize (steps : List ScheduleStep) (unconstrainedBlock : List ScheduleStep) : List ScheduleStep :=
    match steps with
    | [] =>
      -- if we run out of steps, we can just sort the `unconstrainedBlock`
      -- according to the comparison function on `scheduleStep`s
      List.mergeSort (le := compareBlocks) unconstrainedBlock
    | step@(.Unconstrained _ _ _) :: steps =>
      -- If we encounter a step consisting of unconstrained generation,
      -- we cons it onto `unconstrainedBlock` & continue
      normalize steps (step::unconstrainedBlock)
    | step :: steps =>
      -- If we encounter any step that's not unconstrained generation,
      -- the current block of unconstrained generation is over,
      -- so we need to cons it (after sorting) to the head of the list of `step` and continue
      List.mergeSort (le := compareBlocks) unconstrainedBlock ++ step :: normalize steps []
  normalize steps []
    where
      -- Comparison function on blocks of `ScheduleSteps`
      compareBlocks b1 b2 := Ordering.isLE $ Ord.compare b1 b2

def subsets {α} (as : List α) : LazyList (List α × List α) :=
  match as with
  | [] => pure ([],[])
  | a :: as' => do
    let (subset,comp) <- subsets as'
    .lcons (subset,a :: comp) ⟨ λ _ => .lcons (a :: subset, comp) ⟨λ _ => .lnil⟩⟩

def subsetsSuchThat {α} (p : α -> Bool) (as : List α) : LazyList (List α × List α) :=
  match as with
  | [] => pure ([],[])
  | a :: as' => do
    let (subset,comp) <- subsetsSuchThat p as'
    if p a then
    .lcons (subset,a :: comp) ⟨ λ _ => .lcons (a :: subset, comp) ⟨λ _ => .lnil⟩⟩
    else
    .lcons (subset,a::comp) ⟨ λ _ => .lnil ⟩

/-
Find all variables which appear repeatedly
Filter out functions and add their
-/

def nonemptySubsetsSuchThat {α} (p : α -> Bool) (as : List α) :=
  LazyList.filter (λ (l,_) => not l.isEmpty) (subsetsSuchThat p as)

def nonemptySubsets {α} (as : List α) :=
  LazyList.filter (λ (l,_) => not l.isEmpty) (subsets as)

#eval (nonemptySubsetsSuchThat (fun x => x % 2 == 0) [1,2,3,4,5,6]).take 15

def select {α} (as : List α) : LazyList (α × List α) :=
  match as with
  | [] => .lnil
  | a :: as' =>
    .lcons (a, as') ⟨λ _ => LazyList.mapLazyList (λ (x,as'') => (x, a::as'')) (select as')⟩

theorem select_smaller : ∀ α (l : List α) a l', (a,l') ∈ select l -> l'.length < l.length := by
  intros α l
  induction l
  case nil =>
    intros a l' hmem
    simp [select, List.length] at *
    cases hmem
  case cons x xs xs_ih =>
    intros a l' hmem
    simp [select, List.length] at *
    cases hmem
    case InLHead =>
      simp
    case InLNext notit tl =>
      simp [Thunk.get] at tl
      sorry
















partial def permutations {α} (as : List α) : LazyList (List α) :=
  match as with
  | [] => pure []
  | as => do
    let ⟨ x,as' ⟩  <- select as
    LazyList.mapLazyList (λ l => x :: l) (permutations as')

inductive PreScheduleStep α v where
| Checks (hyps : List α)
| Produce (out : List v) (hyp : α)
| InstVars (var : List v)
deriving Repr

instance [Repr α] [Repr v] : Repr (List (PreScheduleStep α v)) where
  reprPrec steps _ :=
    let lines := steps.map fun step =>
      match step with
      | .InstVars vars => s!"{repr vars} <- arbitrary"
      | .Produce out hyp => s!"{repr out} <- {repr hyp}"
      | .Checks hyps => s!"check {repr hyps}"
    "do\n  " ++ String.intercalate "\n  " lines
#print ConstructorExpr

def collectRepeatedNames (lists : List (List Name)) : List Name :=
  let allNames := lists.flatten
  let counts := allNames.foldl (fun (acc : NameMap Nat) name => acc.alter name (fun opt => some ((opt.getD 0) + 1))) {}
  counts.toList.filterMap (fun (name, count) =>
    if count > 1 then some name else none)

partial def containsFunctionCall (ctrExpr : ConstructorExpr) : Bool :=
  match ctrExpr with
  | .Unknown _ => false
  | .Ctor _ args => List.any args (fun x => containsFunctionCall x)
  | .FuncApp _ _ => true

def constructHypothesis (hyp : HypothesisExpr × List (List Name)) : HypothesisExpr × List (List Name) × List Name :=
  let repeatedNames := collectRepeatedNames hyp.snd
  let hypIndices := List.zip hyp.fst.snd hyp.snd
  let (mustBind, allSafe) := hypIndices.partition (fun (ctrExpr, vars) =>
    containsFunctionCall ctrExpr || (vars.any (List.contains repeatedNames)))

  (hyp.fst, allSafe.map (fun x => x.snd), repeatedNames ++ mustBind.flatMap (fun x => x.snd))

def needs_checking {α v} [BEq v] (env : List v) (a_vars : α × List (List v) × List v) : Bool :=
  let (_, potentialIndices, alwaysBound) := a_vars
  alwaysBound.all (List.contains env) &&
  potentialIndices.all (fun idx => idx.all (List.contains env))

def prune_empties {α v} (schd : List (PreScheduleStep α v)) : List (PreScheduleStep α v) :=
  schd.foldr aux []
  where
    aux pss l :=
      match pss with
      | .Checks [] => l
      | .InstVars [] => l
      | _ => pss :: l

/- Variables in third elt of hyp should be disjoint from flatten of snd elt
   Assume that any hyp in hyps should have at least one thing it could generate
   Any hypothesis which lacks an index it can generate from should be checked
   in a prior step. The second element of hyps should contain only lists of unbound
   variables.

   The snd and third elements combined should equal the set vars(hyp.fst)
 -/
partial def enum_schedules {α v} [BEq v] (vars : List v) (hyps : List (α × List (List v) × List v)) (env : List v)
  : LazyList (List (PreScheduleStep α v)) :=
  match hyps with
  | [] => pure (prune_empties [.InstVars $ vars.removeAll env])
  | _ => do
    let ⟨ (hyp, potential_output_indices, always_bound_variables),hyps' ⟩  <- select hyps
    let (some_bound_output_indices, all_unbound_output_indices) := List.partition (List.any . (List.contains env)) potential_output_indices
    let (out,bound) <- nonemptySubsets all_unbound_output_indices
    let bound_vars := bound.flatten ++ (always_bound_variables ++ some_bound_output_indices.flatten).filter (not ∘ List.contains env)
    let env' := bound_vars ++ env
    let (prechecks,to_be_satisfied) := List.partition (needs_checking env') hyps'
    let out_vars := out.flatten
    let env'' := out_vars ++ env'
    let (postchecks,to_be_satisfied') := List.partition (needs_checking env'') to_be_satisfied


    LazyList.mapLazyList (λ l => prune_empties [.InstVars bound_vars
                              , .Checks (Prod.fst <$> prechecks)
                              , .Produce out_vars hyp
                              , .Checks (Prod.fst <$> postchecks)
                              ]
                              ++ l) (enum_schedules vars to_be_satisfied' env'')

#eval (permutations [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]).take 3
#eval (enum_schedules [1,2,3,4] [("A",[[1,2,3],[4]],[]), ("B",[[4]],[])] []).take 15

-- Simple test with 2 hypotheses
#eval (enum_schedules [1,2,3] [("A",[[1],[2]],[]), ("B",[[2],[3]],[])] []).take 3

-- Test with overlapping variables
#eval (enum_schedules [1,2,3,4,5] [("H1",[[1],[2],[3]],[]), ("H2",[[3],[4]],[]), ("H3",[[4],[5]],[])] []).take 5

-- Test with some variables already bound
#eval (enum_schedules [1,2,3] [("A",[[1],[2]],[]), ("B",[[2],[3]],[])] [1])

-- Larger example to test scalability
#eval (enum_schedules [1,2,3,4] [("P",[[1],[2]],[]), ("Q",[[2],[3]],[]), ("R",[[3],[4]],[]), ("S",[[1],[4]],[])] []).take 10

-- Lots of variables (10 variables in one hypothesis)
#eval (enum_schedules [1,2,3,4,5,6,7,8,9,10] [("BigHyp",[[1],[2],[3],[4],[5],[6],[7],[8],[9],[10]],[])] []).take 5

-- Lots of hypotheses (10 hypotheses with few variables each)
#eval (enum_schedules [1,2,3,4,5,6,7,8,9,10] [("H1",[[1]],[]), ("H2",[[2]],[]), ("H3",[[3]],[]), ("H4",[[4]],[]), ("H5",[[5]],[]),
                       ("H6",[[6]],[]), ("H7",[[7]],[]), ("H8",[[8]],[]), ("H9",[[9]],[]), ("H10",[[10]],[])] []).take 3

-- Both: many hypotheses with many variables each
#eval (enum_schedules (List.range 14) [("A",[[1],[2],[3],[4],[5]],[]), ("B",[[3],[4],[5],[6],[7]],[]), ("C",[[5],[6],[7],[8],[9]],[]),
                       ("D",[[7],[8],[9],[10],[11],[3],[1],[2]],[]), ("E",[[9],[10],[11],[12],[13]],[])] []).take 100

#print ScheduleEnv

#print ScheduleStep
#print DeriveSort

-- Determine the right name for the recursive function in the producer
def recursiveFunctionName deriveSort :=
  match deriveSort with
  | DeriveSort.Generator => `aux_arb
  | .Enumerator => `aux_enum
  | .Checker | .Theorem => `aux_dec

def preScheduleStepToScheduleStep (preStep : PreScheduleStep HypothesisExpr Name) : ScheduleM (List ScheduleStep) := do
  let env <- read
  match preStep with
  | .Checks hyps => return (hyps.map (fun hyp =>
    let src := if env.deriveSort == DeriveSort.Checker && env.recCall.fst == hyp.fst then
      Source.Rec (recursiveFunctionName env.deriveSort) hyp.snd
    else
      Source.NonRec hyp;
    ScheduleStep.Check src true))
  | .Produce outs hyp =>
    let (newMatches, hyp', newOutputs) ← handleConstrainedOutputs hyp outs
    let typedOutputs ← newOutputs.mapM
      (fun v => do
        match List.lookup v env.vars with
        | some tyExpr =>
          let constructorExpr ← exprToConstructorExpr tyExpr
          pure (v, constructorExpr)
        | none =>
          pure (v, .Unknown `_))
    let (_, hypArgs) := hyp'

    let constrainingRelation ←
      if (← isRecCall outs hyp env.recCall) then
        let inputArgs := filterWithIndex (fun i _ => i ∉ (Prod.snd env.recCall)) hypArgs
        pure (Source.Rec env.recCall.fst inputArgs)
      else
        pure (Source.NonRec hyp')
    return (ScheduleStep.SuchThat typedOutputs constrainingRelation env.prodSort :: newMatches)
  | .InstVars vars =>
    vars.mapM (fun v => do
    let ty ← Option.getDM (List.lookup v env.vars)
          (throwError m!"key {v} missing from association list {env.vars}")
        let (ctorName, ctorArgs) := ty.getAppFnArgs
        let src ←
          if ctorName == Prod.fst env.recCall
            then Source.Rec env.recCall.fst <$> ctorArgs.toList.mapM (fun foo => exprToConstructorExpr foo)
          else
            let hypothesisExpr ← exprToHypothesisExpr ty
            match hypothesisExpr with
            | none => throwError m!"DFS: unable to convert Expr {ty} to a HypothesisExpr"
            | some hypExpr => pure (Source.NonRec hypExpr)
    return ScheduleStep.Unconstrained v src env.prodSort
    )


def possible_schedules' : ScheduleM (LazyList (List ScheduleStep)) := do
  let env <- read




  /- For each permutation, for each of its hypotheses, select which of its
  unbound variables should be instantiated to satisfy it.
  Not all unbound variables are able to be instantiated by a hypothesis,
  so we must filter out those unbound mentioned in the hypothesis which
  are arguments to a function (1) and those which are under a constructor
  that contains a bound or invalid unbound variable (2) and those that
  appear nonlinearly (as they would require an unlikely equality check)(3).
  Here is an encompassing example:
  `H (C a (f b)) c (C₃ c) d (C₃ (C₂ e) C₄)`
  We can't instantiate `b` because it is under a function (1),
   `a` because it is under a constructor with an invalid variable `b` (2),
   `c` because it appears nonlinearly
  We *can* instantiate `d` and `e` because they satisfy all three conditions
  Note that despite e being stored under several constructors, there are no
  bound or invalid variables mixed in, so we can generate H's 5th argument
  and pattern match the result against `(C₃ (C₂ x) C₄)` and if it matches,
  `e` to the value `x`.

  The remainder of its unbound variables should be instantiated according
  to their type unconstrained by a hypothesis. These unconstrained instantiations
  should happen before the constrained instantiation. For each `2^|unbound ∩ valid|`
  choice, we prepend the unconstrained instantiations behind the constrained one
  and lazily cons that version of the schedule to our list.

  Finally, we fold through the list, tracking the set of variables bound, as soon
  as a constraint has had all its variables bound, a check for it
  should be inserted at that point in the schedule. Finally, return
  the schedules. -/
  return (.lnil)


/-- Depth-first enumeration of all possible schedules.

    The list of possible schedules boils down to taking a permutation of list of hypotheses -- what this function
    does is it comes up with the list of possible permutations of hypotheses.

    For `TyApp` in the STLC example, here are the possible permutations (output is e, the unbound vars are {e1, e2, t1}):

    (a.) `[typing Γ e1 (TFun 𝜏1 𝜏2), typing Γ e2 𝜏1]`
    (b.) `[typing Γ e2 𝜏1, typing Γ e1 (TFun 𝜏1 𝜏2)]`

    We first discuss permutation (a).

    For permutation (a), `t1` and `e1` are unbound, so we're generate the max no. of variables possible
      * `e1` is in an outputtable position (since its not under a constructor)
      * `t1` is *not* in an ouputtable position (since `t1` is under the `TFun` constructor, `type` is an input mode, and `t2` is also an input mode)
      * This means `t1` has to be generated first arbitrarily

    We have elaborated this step to:
    ```lean
      t1 <- type                      -- (this uses the `Arbitrary` instance for [type])
      e1 <- typing Γ ? (TFun t1 t2)    -- (this desugars to `arbitraryST (fun e1 => typing Γ e1 (TFun t1 t2))` )
    ```

    Now that we have generated `t1` and `e1`, the next hypothesis is `typing Γ e2 𝜏1`
    * `e2` is the only variable that's unbound
    * Thus, our only option is to do:
    ```lean
      e2 <- typing Γ ? t1
    ```

    + For permutation (b), the first thing we do is check what are the unbound (not generated & not fixed by inputs)
      variables that are constrained by the first hypothesis `typing Γ e2 𝜏1`
      * `e2` is unbound & can be output (since its in the output mode & not generated yet)
      * `t1` can also be output since its not been generated yet & not under a constructor
        * `Γ` is fixed already (bound) b/c its a top-level argument (input) to `aux_arb`
      * Here we have 3 possible choices:
        1. Arbitrary [t1], ArbitrarySuchThat [e2]
        2. Arbitrary [e2], ArbitrarySuchThat [t1]
        3. ArbitrarySuchThat [e2, t1]

      * For each choice, we can then elaborate the next `ScheduleStep` in our hypothesis permutation (i.e. `typing Γ e1 (TFun 𝜏1 𝜏2)`)
      + Rest of the logic for dealing with permutation (b) is similar to as the 1st permutation
-/
partial def dfs (boundVars : List Name) (remainingVars : List Name) (checkedHypotheses : List Nat) (scheduleSoFar : List ScheduleStep) : ScheduleM (List (List ScheduleStep)) := do
  match remainingVars with
  | [] =>
    return (pure (List.reverse scheduleSoFar))
  | _ => do
    -- Obtain environment variables via the underlying reader monad's `read` functino
    let env ← read

    -- Determine the right name for the recursive function in the producer
    let recursiveFunctionName :=
      match env.deriveSort with
      | .Generator => `aux_arb
      | .Enumerator => `aux_enum
      | .Checker | .Theorem => `aux_dec

    -- Enumerate all paths for unconstrained generation / enumeration
    -- Each unconstrained path is a choice to instantiate one of the unbound variables arbitrarily
    let unconstrainedProdPaths ←
      flatMapMWithContext remainingVars (fun v remainingVars' => do
        let (newCheckedIdxs, newCheckedHyps) := List.unzip $ collectCheckSteps env (v::boundVars) checkedHypotheses
        let ty ← Option.getDM (List.lookup v env.vars)
          (throwError m!"key {v} missing from association list {env.vars}")
        let (ctorName, ctorArgs) := ty.getAppFnArgs
        let src ←
          if ctorName == Prod.fst env.recCall
            then Source.Rec recursiveFunctionName <$> ctorArgs.toList.mapM (fun foo => exprToConstructorExpr foo)
          else
            let hypothesisExpr ← exprToHypothesisExpr ty
            match hypothesisExpr with
            | none => throwError m!"DFS: unable to convert Expr {ty} to a HypothesisExpr"
            | some hypExpr => pure (Source.NonRec hypExpr)
        let unconstrainedProdStep := ScheduleStep.Unconstrained v src env.prodSort
        -- TODO: handle negated propositions in `ScheduleStep.Check`
        let checks := List.reverse $ (ScheduleStep.Check . true) <$> newCheckedHyps
        dfs (v::boundVars) remainingVars'
          (newCheckedIdxs ++ checkedHypotheses)
          (checks ++ unconstrainedProdStep :: scheduleSoFar))

    let remainingHypotheses := filterMapWithIndex (fun i hyp => if i ∈ checkedHypotheses then none else some (i, hyp)) env.sortedHypotheses

    -- Enumerate all paths for constrained generation / enumeration, based on the remaining hypotheses.
    -- Each constrained path is a choice to satisfy a hypothesis and generate one or more variables that it constrains with `arbitrarySuchThat` / `enumSuchThat`
    -- In a constrained path, we always output as many variables as possible.
    let constrainedProdPaths ← remainingHypotheses.flatMapM (fun (i, hyp, hypVars) => do
      if (i ∈ checkedHypotheses) then
        pure []
      else
        let remainingVarsSet := NameSet.ofList remainingVars
        let hypVarsSet := NameSet.ofList hypVars.flatten
        let outputSet := remainingVarsSet ∩ hypVarsSet
        let remainingVars' := (remainingVarsSet \ outputSet).toList
        let outputVars := outputSet.toList

        -- If any of these 3 conditions are true, there are no possible constrained producer `ScheduleStep`s,
        -- so just return the empty list
        if outputVars.isEmpty
          || (← not <$> outputInputNotUnderSameConstructor hyp outputVars)
          || (← not <$> outputsNotConstrainedByFunctionApplication hyp outputVars) then
          pure []
        else
          let (newMatches, hyp', newOutputs) ← handleConstrainedOutputs hyp outputVars
          let typedOutputs ← newOutputs.mapM
            (fun v => do
              match List.lookup v env.vars with
              | some tyExpr =>
                let constructorExpr ← exprToConstructorExpr tyExpr
                pure (v, constructorExpr)
              | none =>
                pure (v, .Unknown `_))
          let (_, hypArgs) := hyp'

          let constrainingRelation ←
            if (← isRecCall outputVars hyp env.recCall) then
              let inputArgs := filterWithIndex (fun i _ => i ∉ (Prod.snd env.recCall)) hypArgs
              pure (Source.Rec recursiveFunctionName inputArgs)
            else
              pure (Source.NonRec hyp')
          let constrainedProdStep := ScheduleStep.SuchThat typedOutputs constrainingRelation env.prodSort

          let (newCheckedIdxs, newCheckedHyps) := List.unzip $ collectCheckSteps env (outputVars ++ boundVars) (i::checkedHypotheses)
          -- TODO: handle negated propositions in `ScheduleStep.Check`
          let checks := List.reverse $ (ScheduleStep.Check . true) <$> newCheckedHyps

          dfs (outputVars ++ boundVars) remainingVars'
            (i :: newCheckedIdxs ++ checkedHypotheses)
            (checks ++ newMatches ++ constrainedProdStep :: scheduleSoFar))

    return constrainedProdPaths ++ unconstrainedProdPaths

/-- Takes a `deriveSort` and returns the corresponding `ProducerSort`:
    - If we're deriving a `Checker` or a `Enumerator`, the corresponding `ProducerSort` is an `Enumerator`,
      since its more efficient to enumerate values when checking
    - If we're deriving a `Generator` or a function which generates inputs to a `Theorem`,
      the corresponding `ProducerSort` is a `Generator`, since we want to generate random inputs -/
def convertDeriveSortToProducerSort (deriveSort : DeriveSort) : ProducerSort :=
  match deriveSort with
  | .Checker | .Enumerator => ProducerSort.Enumerator
  | .Generator | .Theorem => ProducerSort.Generator

/-- Computes all possible schedules for a constructor
    (each candidate schedule is represented as a `List ScheduleStep`).

    Arguments:
    - `vars`: list of universally-quantified variables and their types
    - `hypotheses`: List of hypotheses about the variables in `vars`
    - `deriveSort` determines whether we're deriving a checker/enumerator/generator
    - `recCall`: a pair contianing the name of the inductive relation and a list of indices for output arguments
      + `recCall` represents what a recursive call to the function being derived looks like
    - `fixedVars`: A list of fixed variables (i.e. inputs to the inductive relation) -/
def possibleSchedules (vars : List (Name × Expr)) (hypotheses : List HypothesisExpr) (deriveSort : DeriveSort)
  (recCall : Name × List Nat) (fixedVars : List Name) : LazyList (MetaM (List ScheduleStep)) := do

  let sortedHypotheses := mkSortedHypothesesVariablesMap hypotheses

  let prodSort := convertDeriveSortToProducerSort deriveSort

  let scheduleEnv := ⟨ vars, sortedHypotheses, deriveSort, prodSort, recCall, fixedVars ⟩

  let remainingVars := List.filter (. ∉ fixedVars) (Prod.fst <$> vars)

  let (newCheckedIdxs, newCheckedHyps) := List.unzip $ (collectCheckSteps scheduleEnv fixedVars [])
  let firstChecks := List.reverse $ (ScheduleStep.Check . true) <$> newCheckedHyps

  let lazyPreSchedules := enum_schedules remainingVars (sortedHypotheses.map constructHypothesis) fixedVars

  let finalPreSchedules := lazyPreSchedules.filter (fun schd => schd.all (fun stp =>
    match stp with
    | .Produce [_] _ => true
    | .Produce (_ :: _) _ => false
    | _ => true))

  let lazySchedules := finalPreSchedules.mapLazyList ((ReaderT.run . scheduleEnv) ∘ ((firstChecks ++ .) <$> .) ∘ List.flatMapM preScheduleStepToScheduleStep)

  lazySchedules

  -- let schedules ← ReaderT.run (dfs fixedVars remainingVars newCheckedIdxs firstChecks) scheduleEnv

  -- let normalizedSchedules := List.eraseDups (normalizeSchedule <$> schedules)

  -- Keep only schedules where `SuchThat` steps only bind 1 output to the
  -- result of a call to a constrained generator
  -- (this is a simplification we make for now so we don't have to handle tupling multiple inputs to constrained generators)


  -- Sort the schedules in terms of increasing length (we prioritize shorter schedules over longer ones)
  -- return (List.mergeSort lazySchedules (le := fun s1 s2 => s1.length <= s2.length))
