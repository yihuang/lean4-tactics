/-
# Propositional Reasoning: `exfalso`, `by_contra`, `by_cases`, `contradiction`

These tactics handle classical reasoning patterns: proof by contradiction,
case splitting on a proposition, and deriving conclusions from `False`.
-/

/--
`exfalso`: changes the goal to `False`. Use when you have a contradiction
in your hypotheses and want to derive anything.

Example: from `False`, derive `P`.
-/
theorem exfalso_basic (P : Prop) (h : False) : P := by
  -- ⊢ `P`
  -- `h : False`
  exfalso
  -- ⊢ `False`
  exact h

/--
`exfalso` is useful when hypotheses contradict each other.

Example: from `h₁ : P` and `h₂ : ¬ P`, prove any `Q`.
-/
theorem exfalso_from_contra (P Q : Prop) (h₁ : P) (h₂ : ¬ P) : Q := by
  -- ⊢ `Q`
  -- `h₁ : P`, `h₂ : ¬ P`
  exfalso
  -- ⊢ `False`
  apply h₂
  -- ⊢ `P`
  exact h₁

/--
`by_contra h`: assumes `¬ goal` and adds `h : ¬ goal` to context.
Then the goal becomes `False` (classical proof by contradiction).

Example: `P ∨ ¬ P` (law of excluded middle, classical).
-/
theorem by_contra_lem (P : Prop) : P ∨ ¬ P := by
  -- ⊢ `P ∨ ¬ P`
  apply Classical.byContradiction
  -- Goal becomes `¬ (P ∨ ¬ P) → False`
  intro h
  -- `h : ¬ (P ∨ ¬ P)`
  -- ⊢ `False`
  apply h
  -- ⊢ `P ∨ ¬ P` (which we were assuming false — now we prove it)
  right
  -- ⊢ `¬ P`
  intro hp
  -- `hp : P`
  -- ⊢ `False`
  apply h
  left
  exact hp

/--
`by_cases h : P`: case split on proposition `P`.
Generates two subgoals: one assuming `h : P`, one assuming `h : ¬ P`.

Example: case analysis on a proposition to prove `Q`.
-/
theorem by_cases_example (P Q : Prop) (h₁ : P → Q) (h₂ : ¬ P → Q) : Q := by
  -- ⊢ `Q`
  by_cases h : P
  -- Case 1: `h : P` → ⊢ `Q`
  · exact h₁ h
  -- Case 2: `h : ¬ P` → ⊢ `Q`
  · exact h₂ h

/--
`by_cases` on a numeric condition: case split on `a ≤ b`.

Example: express `a ≤ b` as `¬ b < a`.
-/
theorem by_cases_nat_le (a b : Nat) : (if a ≤ b then 0 else 1) = (if b < a then 1 else 0) := by
  by_cases h : a ≤ b
  · -- `h : a ≤ b`, so `b < a` is false
    have hn : ¬ b < a := Nat.not_lt.mpr h
    simp [h, hn]
  · -- `h : ¬ a ≤ b`, so `b < a` is true
    have h' : b < a := Nat.lt_of_not_ge h
    simp [h, h']

/--
`contradiction`: closes a goal when the context contains a pair of
contradictory hypotheses (`P` and `¬ P`, or `a = b` and `a ≠ b`).

Example: from `P` and `¬ P`, done.
-/
theorem contradiction_basic (P : Prop) (h₁ : P) (h₂ : ¬ P) : False := by
  -- ⊢ `False`
  contradiction

/--
`contradiction` also works with `a = b` vs `a ≠ b`.

Example: from `x = 0` and `x ≠ 0`, derive `False`.
-/
theorem contradiction_equality (x : Nat) (h₁ : x = 0) (h₂ : x ≠ 0) : False := by
  -- ⊢ `False`
  contradiction

/--
`exfalso` vs `contradiction`: `exfalso` changes the goal to `False` and leaves
you to produce the contradiction manually; `contradiction` does it all at once.

Example: from `P` and `¬ P`, prove any `Q` — using `exfalso` step by step.
-/
theorem exfalso_vs_contradiction (P Q : Prop) (h₁ : P) (h₂ : ¬ P) : Q := by
  -- Using `exfalso`:
  exfalso
  -- ⊢ `False`
  apply h₂
  exact h₁

/--
Combining `by_cases` with `by_contra`.

Example: `(P → Q) → (¬ P → Q) → Q` — a form of case analysis.
-/
theorem case_analysis_comb (P Q : Prop) : (P → Q) → (¬ P → Q) → Q := by
  -- ⊢ `(P → Q) → (¬ P → Q) → Q`
  intro hPQ
  intro hnPQ
  -- `hPQ : P → Q`, `hnPQ : ¬ P → Q`
  by_cases h : P
  · -- `h : P` → get `Q` via `hPQ`
    exact hPQ h
  · -- `h : ¬ P` → get `Q` via `hnPQ`
    exact hnPQ h

/--
`classical tacs`: runs `tacs` in a scope where `Classical.propDecidable` is
available as a local instance.  This enables `dec_trivial` and `by_cases`
for any proposition, and gives access to the law of excluded middle.

Example: `P ∨ ¬ P` is provable classically but not constructively.
+-/
theorem classical_lem (P : Prop) : P ∨ ¬ P := by
  -- ⊢ `P ∨ ¬ P`
  classical
  exact Classical.em P

/--
Within a `classical` block, `by_cases` works for any proposition
(not just decidable ones).

Example: case analysis on an arbitrary `P`.
+-/
theorem classical_by_cases (P Q : Prop) (h₁ : P → Q) (h₂ : ¬ P → Q) : Q := by
  -- ⊢ `Q`
  classical
  by_cases h : P
  · exact h₁ h
  · exact h₂ h
