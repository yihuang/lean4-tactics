/-
# Relations: `symm`, `apply_assumption`, `ac_rfl`

These tactics work with symmetric relations, proof search via assumption,
and associative-commutative equality.
-/

/--
`symm`: applies symmetry to a relation. If the goal is `a ~ b` and `~` has a
`@[symm]` lemma, `symm` changes it to `b ~ a`.  Also works at a hypothesis
with `symm at h`.

Example: equality is symmetric.
-/
theorem symm_basic (a b : Nat) (h : a = b) : b = a := by
  -- ⊢ `b = a`
  symm
  -- ⊢ `a = b`
  exact h

/--
`symm` also works on hypotheses via `symm at h`.

Example: from `h : a = b`, get `h : b = a` in place.
-/
theorem symm_at_hyp (a b : Nat) (h : a = b) : a = b := by
  -- `h : a = b`
  symm at h
  -- `h : b = a`
  symm at h
  -- `h : a = b`
  exact h

/--
`symm` works for any relation with a `@[symm]` lemma, not just equality.
For example, `Nat` inequality `≤` is not symmetric, so `symm` fails on it.
But `a = b` and `a ↔ b` both support `symm`.

Example: `P ↔ Q` is symmetric.
-/
theorem symm_iff (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := by
  -- ⊢ `(P ↔ Q) → (Q ↔ P)`
  intro h
  -- `h : P ↔ Q`
  symm
  -- ⊢ `P ↔ Q`
  exact h

/--
`apply_assumption`: searches the context for a hypothesis whose conclusion
matches the goal (using `apply`), and applies it.  If the hypothesis has
premises, they become new subgoals (`apply_assumption` also calls
`assumption` on each new subgoal automatically).

Example: direct match — a hypothesis `hp : P` matches the goal `P`.
-/
theorem apply_assumption_direct (P : Prop) (hp : P) : P := by
  -- ⊢ `P`
  apply_assumption

/--
`apply_assumption` works through `→` as well: it applies `h : P → Q` to goal
`Q`, leaving `P` as a subgoal.  Use `apply_assumption; assumption` or pair
it with `apply_assumption` which also tries `assumption` on the premises.

Example: from `h : P → Q` and `hp : P`, prove `Q`.
-/
theorem apply_assumption_imp (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- ⊢ `Q`
  apply_assumption
  -- The premise `P` is left as a subgoal
  -- ⊢ `P`
  assumption

/--
`ac_rfl`: proves equalities up to associativity and commutativity of
operators marked with `Std.Associative` and `Std.Commutative`.
`Nat.add` and `Nat.mul` are already annotated.

Example: `(a + b) + c = (c + a) + b` using only AC reasoning.
-/
theorem ac_rfl_basic (a b c : Nat) : (a + b) + c = (c + a) + b := by
  -- ⊢ `(a + b) + c = (c + a) + b`
  ac_rfl

/--
`ac_rfl` works for multiplication as well.

Example: `(a * b) * c = (c * a) * b`.
-/
theorem ac_rfl_mul (a b c : Nat) : (a * b) * c = (c * a) * b := by
  -- ⊢ `(a * b) * c = (c * a) * b`
  ac_rfl

/--
`ac_rfl` handles mixed AC operators separately.

Example: a more complex AC rearrangement.
-/
theorem ac_rfl_complex (a b c d : Nat) : a + (b + c) + d = (c + a) + (b + d) := by
  -- ⊢ `a + (b + c) + d = (c + a) + (b + d)`
  ac_rfl
