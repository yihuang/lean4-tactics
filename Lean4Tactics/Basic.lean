/-
# Basic Tactics: `intro`, `apply`, `exact`, `refine`

These are the first tactics every Lean user encounters. They form the foundation
of interactive theorem proving — moving terms between the goal and the context.

Each example below is a self-contained theorem. Comments document the goal state
before and after each tactic application, so you can follow the proof step by step.
-/

/--
`intro`: introduces a hypothesis (the antecedent of an implication, or a universal
quantifier) into the local context.

Example: prove `P → P` (identity).
-/
theorem basic_intro (P : Prop) : P → P := by
  -- ⊢  `P → P`
  intro h
  -- `h : P`  (a hypothesis added to context)
  -- ⊢  `P`
  exact h

/--
`intro` with multiple arguments: chain `intro` calls or use `intros`.

Example: prove `P → Q → P` (first projection).
-/
theorem basic_intro_multi (P Q : Prop) : P → Q → P := by
  -- ⊢  `P → Q → P`
  intro hp
  -- `hp : P`
  -- ⊢  `Q → P`
  intro hq
  -- `hq : Q`, `hp : P`
  -- ⊢  `P`
  exact hp      -- we ignore `hq`

/--
`apply`: matches the goal's conclusion against the conclusion of a hypothesis
(or theorem), generating new subgoals for any missing premises.

Example: modus ponens — from `P` and `P → Q`, derive `Q`.
-/
theorem basic_apply (P Q : Prop) (hp : P) (h : P → Q) : Q := by
  -- ⊢  `Q`
  apply h
  -- New goal: `P`  (we need to supply the premise of `h`)
  exact hp

/--
`apply` can chain. Example: prove `R` given `P → Q → R`, `P`, `Q`.
-/
theorem basic_apply_chain (P Q R : Prop) (hp : P) (hq : Q) (h : P → Q → R) : R := by
  -- ⊢  `R`
  apply h
  -- Two new goals: `P` and `Q`
  · exact hp    -- first subgoal
  · exact hq    -- second subgoal

/--
`exact`: closes a goal when the given term has exactly the goal type.
It is the direct, no-frills way to finish a goal.
-/
theorem basic_exact (A : Type) (a : A) : a = a := by
  -- ⊢  `a = a`
  exact rfl

/--
`refine`: like `exact` but allows `_` placeholders for missing subterms.
Each `_` becomes a new subgoal. This is the most flexible way to build a proof
term incrementally.

Example: prove `P ∧ Q → Q ∧ P` using `refine`.
-/
theorem basic_refine_and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  -- ⊢  `P ∧ Q → Q ∧ P`
  intro h
  -- `h : P ∧ Q`
  -- ⊢  `Q ∧ P`
  refine And.intro ?_ ?_
  -- Two new subgoals: `Q` and `P`
  · exact h.right
  · exact h.left

/--
`refine` with `h : P ∧ Q`, pattern-match the constructor inline.
-/
theorem basic_refine_and_destructure (P Q : Prop) (h : P ∧ Q) : Q := by
  -- ⊢  `Q`
  -- `h : P ∧ Q`
  refine h.right

/--
Combining `intro`, `apply`, and `refine` in one proof.

Example: `(P → Q → R) → (P → Q) → P → R` (modus ponens with two premises).
-/
theorem basic_combined (P Q R : Prop) : (P → Q → R) → (P → Q) → P → R := by
  -- ⊢  `(P → Q → R) → (P → Q) → P → R`
  intro hpqr
  -- `hpqr : P → Q → R`
  -- ⊢  `(P → Q) → P → R`
  intro hpq
  -- `hpq : P → Q`, `hpqr : P → Q → R`
  -- ⊢  `P → R`
  intro hp
  -- `hp : P`, `hpq : P → Q`, `hpqr : P → Q → R`
  -- ⊢  `R`
  refine hpqr hp ?_
  -- Subgoal: `Q`
  exact hpq hp
