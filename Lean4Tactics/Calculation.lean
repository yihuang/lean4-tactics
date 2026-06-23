/-
# Calculation & Automation: `calc`, `omega`, `decide`, `native_decide`

These tactics automate arithmetic reasoning and chain equations elegantly.
`calc` structures multi-step equality/inequality proofs.
`omega` solves linear arithmetic over Nat/Int.
`decide` and `native_decide` decide decidable propositions by computation.
-/

/--
`calc` chains relations (equality `=`, inequality `≤`, `≥`, etc.) in a readable
vertical format. Each step must be justified by a proof block.

Example: `(a + b) + c = a + (b + c)` via associativity.
-/
theorem calc_basic (a b c : Nat) : (a + b) + c = a + (b + c) := by
  -- ⊢ `(a + b) + c = a + (b + c)`
  calc
    (a + b) + c = a + (b + c) := by rw [Nat.add_assoc]

/--
`calc` with multiple steps: show the distributive law `(a + b) * 2 = 2*a + 2*b`.
-/
theorem calc_multi (a b : Nat) : (a + b) * 2 = 2*a + 2*b := by
  -- ⊢ `(a + b) * 2 = 2*a + 2*b`
  calc
    (a + b) * 2 = (a + b) + (a + b) := by omega
    _ = (a + a) + (b + b) := by omega
    _ = 2*a + 2*b := by omega

/--
`calc` also works with `≤` and other transitive relations.

Example: `a ≤ a + 1`, trivial by `omega`.
-/
theorem calc_inequality (a : Nat) : a ≤ a + 1 := by
  -- ⊢ `a ≤ a + 1`
  omega

/--
`calc` with `:=` syntax for a multi-line chain.

Example: `(a + b) + c = a + b + c` (parens elided).
-/
theorem calc_chain (a b c : Nat) : (a + b) + c = a + b + c := by
  -- ⊢ `(a + b) + c = a + b + c`
  calc
    (a + b) + c = a + (b + c) := by rw [Nat.add_assoc]
    _ = a + b + c := by simp [Nat.add_assoc]

/--
`omega`: fully automated Presburger arithmetic solver for `Nat` and `Int`.
Handles linear equations, inequalities, and divisibility by constants.

Example: simple addition identity.
-/
theorem omega_basic (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  -- ⊢ `a + 1 = b + 1`
  omega

/--
`omega` can handle multiple hypotheses and complex linear constraints.

Example: `a ≤ b` and `b ≤ a` implies `a = b`.
-/
theorem omega_le_antisymm (a b : Nat) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  -- ⊢ `a = b`
  omega

/--
`omega` solves multiplicative by constant (e.g. `2*a`) but not general multiplication.

Example: `2*a < 2*b` implies `a < b`.
-/
theorem omega_mul_const (a b : Nat) (h : 2*a < 2*b) : a < b := by
  -- ⊢ `a < b`
  omega

/--
`omega` with integer arithmetic: works on `Int` too.

Example: `x + 1 > x` for integers.
-/
theorem omega_int (x : Int) : x + 1 > x := by
  -- ⊢ `x + 1 > x`
  omega

/--
`decide`: solves decidable propositions by computation. Works on `Nat`, `Int`,
`Bool`, `Fin`, `List`, etc.

Example: a concrete numeric equality.
-/
theorem decide_basic : 12345 + 67890 = 80235 := by
  -- ⊢ `12345 + 67890 = 80235`
  decide

/--
`decide` handles inequalities and boolean expressions.

Example: `3 < 5` and `¬ (10 ≤ 7)`.
-/
theorem decide_inequality : (3 < 5) ∧ ¬ (10 ≤ 7) := by
  -- ⊢ `3 < 5 ∧ ¬ 10 ≤ 7`
  decide

/--
`decide` works on `List` membership and other decidable predicates.

Example: `1 ∈ [1, 2, 3]`.
-/
theorem decide_list : 1 ∈ [1, 2, 3] := by
  -- ⊢ `1 ∈ [1, 2, 3]`
  decide

/--
`native_decide`: like `decide`, but compiles the decision procedure to native code.
Faster for large computations, but has a small compilation overhead.

Example: large factorial computation.
-/
theorem native_decide_basic : 10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1 = 3628800 := by
  -- ⊢ `10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1 = 3628800`
  native_decide

/--
`native_decide` handles more complex decidable constraints.

Example: `a^2 ≥ 0` for all `a : Nat` up to a bound — but this is a `∀`,
which `native_decide` cannot handle directly. Use a concrete case.

Example: verify solution to a small linear equation.
-/
theorem native_decide_equation : ∃ x : Nat, x + 5 = 10 := by
  -- ⊢ `∃ x, x + 5 = 10`
  refine ⟨5, ?_⟩
  native_decide
