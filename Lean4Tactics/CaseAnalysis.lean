/-
# Case Analysis & Induction: `cases`, `induction`, `injection`, `constructor`, `split`, `left`, `right`

These tactics break a goal into subgoals by analyzing the structure of a
datatype or proposition. `cases` and `induction` work on inductive types;
`constructor`/`split`/`left`/`right` work on logical connectives.
-/

/--
`cases` on `Bool`: generate a subgoal for each constructor (`true`, `false`).

Example: `not (not b) = b` for all booleans.
-/
theorem cases_bool (b : Bool) : !(!b) = b := by
  -- ⊢  `!(!b) = b`
  cases b
  -- Case `b = false`:
  -- ⊢  `!(!false) = false`
  · rfl
  -- Case `b = true`:
  -- ⊢  `!(!true) = true`
  · rfl

/--
`cases` on `Nat`: generate subgoals for `0` and `succ n`.

Example: `0 + n = n` by case analysis on `n`.
-/
theorem cases_nat (n : Nat) : 0 + n = n := by
  -- ⊢  `0 + n = n`
  cases n
  -- Case `n = 0`:
  -- ⊢  `0 + 0 = 0`
  · rfl
  -- Case `n = succ n`:
  -- `n : Nat` (the predecessor)
  -- ⊢  `0 + Nat.succ n = Nat.succ n`
  · simp

/--
`cases` with `:` naming: name each case for readability.

Example: `Nat.succ n ≠ 0`.
-/
theorem cases_named (n : Nat) : Nat.succ n ≠ 0 := by
  -- ⊢  `Nat.succ n ≠ 0`
  intro h
  -- `h : Nat.succ n = 0`
  -- We can `cases` the equality to see that it's impossible
  cases h

/--
`induction` on `Nat`: like `cases` but gives the induction hypothesis.

Example: `0 + n = n` by induction.
-/
theorem induction_nat_add_zero (n : Nat) : 0 + n = n := by
  -- ⊢  `0 + n = n`
  induction n with
  | zero =>
      -- Base case: `n = 0`
      -- ⊢  `0 + 0 = 0`
      rfl
  | succ n ih =>
      -- Inductive step: assume `ih : 0 + n = n`, prove for `succ n`
      -- ⊢  `0 + Nat.succ n = Nat.succ n`
      simp

/--
`induction` with `generalizing`: when the induction hypothesis needs to work
for all values of a polymorphic parameter.

Example: `Nat.succ` injection lemma via induction.
-/
theorem induction_generalizing (n m : Nat) (h : n = m) : Nat.succ n = Nat.succ m := by
  -- ⊢  `Nat.succ n = Nat.succ m`
  rw [h]

/--
`injection`: from an equality of two constructor applications, derive equalities
of the arguments. In Lean 4.30, `injection h` automatically closes the goal
by case analysis (`cases h`).

Example: if `succ n = succ m`, then `n = m`.
-/
theorem injection_example (n m : Nat) (h : Nat.succ n = Nat.succ m) : n = m := by
  -- ⊢ `n = m`
  -- `h : Nat.succ n = Nat.succ m`
  injection h

/--
`injection` works for any inductive type with distinguishable constructors.

Example: from `(a, b) = (c, d)` we get `a = c`.
-/
theorem injection_pair (a b c d : Nat) (h : (a, b) = (c, d)) : a = c := by
  -- ⊢ `a = c`
  -- `h : (a, b) = (c, d)`
  injection h

/--
`constructor`: for `∧` (And), breaks `P ∧ Q` into two goals `P` and `Q`.

Example: `P ∧ Q → Q ∧ P`.
-/
theorem constructor_and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  -- ⊢  `P ∧ Q → Q ∧ P`
  intro h
  -- `h : P ∧ Q`
  -- ⊢  `Q ∧ P`
  constructor
  -- First subgoal: `Q`
  · exact h.right
  -- Second subgoal: `P`
  · exact h.left

/--
`split` (also `constructor`): for `↔` (Iff), breaks into `→` and `←`.

Example: `P ∧ Q ↔ Q ∧ P`.
-/
theorem split_iff_and_comm (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  -- ⊢  `(P ∧ Q) ↔ (Q ∧ P)`
  constructor
  -- Subgoal 1: `(P ∧ Q) → (Q ∧ P)`
  · intro h
    constructor
    · exact h.right
    · exact h.left
  -- Subgoal 2: `(Q ∧ P) → (P ∧ Q)`
  · intro h
    constructor
    · exact h.right
    · exact h.left

/--
`left` / `right`: pick which side of a disjunction (`Or`) to prove.

Example: `P → P ∨ Q`.
-/
theorem left_or_intro (P Q : Prop) (hp : P) : P ∨ Q := by
  -- ⊢  `P ∨ Q`
  left
  -- ⊢  `P`
  exact hp

/--
`right`: pick the right side.

Example: `Q → P ∨ Q`.
-/
theorem right_or_intro (P Q : Prop) (hq : Q) : P ∨ Q := by
  -- ⊢  `P ∨ Q`
  right
  -- ⊢  `Q`
  exact hq

/--
Case analysis on `Or` using `cases`.

Example: `P ∨ Q → Q ∨ P`.
-/
theorem cases_or_comm (P Q : Prop) : P ∨ Q → Q ∨ P := by
  -- ⊢  `P ∨ Q → Q ∨ P`
  intro h
  -- `h : P ∨ Q`
  -- ⊢  `Q ∨ P`
  cases h with
  | inl hp =>
      -- `hp : P`
      -- ⊢  `Q ∨ P`
      right
      exact hp
  | inr hq =>
      -- `hq : Q`
      -- ⊢  `Q ∨ P`
      left
      exact hq

/--
`split` for `∃`: also called `constructor`. Breaks `∃ x, P x` into `x` and `P x`.

Example: `∃ n, n = 0`.
-/
theorem exists_example : ∃ n : Nat, n = 0 := by
  -- ⊢  `∃ n, n = 0`
  refine ⟨0, ?_⟩
  -- Subgoal: `0 = 0`
  rfl
