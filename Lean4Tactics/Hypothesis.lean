/-
# Hypothesis Management: `have`, `let`, `generalize`, `revert`, `clear`, `subst`, `specialize`

These tactics manipulate the local context — introducing intermediate results,
renaming, removing, or specializing hypotheses.
-/

/--
`have h : P := expr`: introduces a new hypothesis `h : P` proved by `expr`.
Useful for breaking complex proofs into smaller steps.

Example: transitivity of equality.
-/
theorem have_basic (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  -- ⊢ `a = c`
  have ha_eq_b : a = b := h₁
  have hb_eq_c : b = c := h₂
  rw [ha_eq_b, hb_eq_c]

/--
`have h : P` without a proof term: creates a new subgoal `P`.

Example: prove `(a + b) + c = a + (b + c)` via associativity.
-/
theorem have_subgoal (a b c : Nat) : (a + b) + c = a + (b + c) := by
  -- ⊢ `(a + b) + c = a + (b + c)`
  have h : (a + b) + c = a + (b + c) := by
    -- Subgoal: `(a + b) + c = a + (b + c)`
    rw [Nat.add_assoc]
  exact h

/--
`have` with `:=` names intermediate results. Combine with `calc` or `omega`.

Example: `(a + a) + (b + b) = 2 * (a + b)`.
-/
theorem have_naming (a b : Nat) : (a + a) + (b + b) = 2 * (a + b) := by
  -- ⊢ `(a + a) + (b + b) = 2 * (a + b)`
  have ha2 : a + a = 2 * a := by omega
  have hb2 : b + b = 2 * b := by omega
  calc
    (a + a) + (b + b) = (2 * a) + (2 * b) := by rw [ha2, hb2]
    _ = 2 * (a + b) := by omega

/--
`let x := expr`: defines a local abbreviation. Unlike `have`, `let` is a
definitional abbreviation — `x` unfolds to `expr` during definitional reduction.

Example: naming `a + b` for reuse.
-/
theorem let_basic (a b : Nat) : (a + b) * 2 = (a + b) + (a + b) := by
  -- ⊢ `(a + b) * 2 = (a + b) + (a + b)`
  let s := a + b
  -- adds `s : Nat := a + b` to the context; the goal is UNCHANGED — `let` does
  -- not fold existing `a + b` occurrences into `s` (use Mathlib's `set` for that)
  -- ⊢ `(a + b) * 2 = (a + b) + (a + b)`
  omega

/--
`revert h`: undoes `intro h`, moving `h` back into the goal as an implication.
Useful when you want to apply a lemma that expects a different goal shape.

Example: from `P`, `Q`, prove `P`, using `revert` to temporarily drop `Q`.
-/
theorem revert_basic (P Q : Prop) (hp : P) (_hq : Q) : P := by
  -- ⊢ `P`
  -- `hp : P`, `_hq : Q`
  revert _hq; intro _
  -- ⊢ `P`
  exact hp

/--
`revert` is often used before `apply` when the goal doesn't match.

Example: from `h₁ : P → Q`, `h₂ : Q → R`, and `hp : P`, prove `R`.
-/
theorem revert_apply (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (hp : P) : R := by
  -- ⊢ `R`
  revert hp
  -- ⊢ `P → R`
  intro hp
  -- `hp : P`, ⊢ `R`
  apply h₂
  -- ⊢ `Q`
  apply h₁
  -- ⊢ `P`
  exact hp

/--
`clear h`: removes hypothesis `h` from the context. Useful when a hypothesis
is no longer needed.

Example: from `P` and `Q`, prove `P`, then clear `Q`.
-/
theorem clear_basic (P Q : Prop) (hp : P) (_hq : Q) : P := by
  -- ⊢ `P`
  -- `hp : P`, `_hq : Q`
  clear _hq
  -- `_hq` removed; ⊢ `P`
  exact hp

/--
`clear` can remove multiple hypotheses at once.

Example: `P → P`, clearing unused `Q` and `R`.
-/
theorem clear_multi (P Q R : Prop) (hp : P) (_hq : Q) (_hr : R) : P := by
  -- ⊢ `P`
  clear _hq _hr
  exact hp

/--
`rename_i` renames the most recent binder with an auto-generated name
(e.g. from `cases` or `induction`). Not to be confused with `rename`
(also a core tactic), which renames by *type* rather than by binder position.

Example: after `induction` without naming, rename the auto-generated variable.
-/
theorem rename_i_example (n : Nat) : n + 0 = n := by
  -- ⊢ `n + 0 = n`
  induction n
  · simp
  · -- The predecessor has an auto-generated name
    rename_i m ih
    -- Now the predecessor is `m` and the induction hypothesis is `ih : m + 0 = m`
    -- ⊢ `Nat.succ m + 0 = Nat.succ m`
    simp
/--
`subst h`: substitutes `h : x = t` or `h : t = x`, replacing `x` with `t`
everywhere and removing `h`.

Example: from `h : a = b`, prove `a + c = b + c`.
-/
theorem subst_basic (a b c : Nat) (h : a = b) : a + c = b + c := by
  -- ⊢ `a + c = b + c`
  -- `h : a = b`
  subst h
  -- `a` replaced by `b` everywhere; `h` removed
  -- ⊢ `b + c = b + c`
  rfl

/--
`subst h` also works when the equation is `h : t = x` (variable on the right).

Example: from `h : 0 = a`, prove `a = 0`.
-/
theorem subst_reverse (a : Nat) (h : 0 = a) : a = 0 := by
  -- ⊢ `a = 0`
  -- `h : 0 = a`
  subst h
  -- ⊢ `0 = 0`
  rfl

/--
`specialize h x`: if `h : ∀ x, P x`, replaces `h` with `h x : P x`.

Example: from `h : ∀ x : Nat, x = x` and `a : Nat`, prove `a = a`.
-/
theorem specialize_basic (h : ∀ x : Nat, x = x) (a : Nat) : a = a := by
  -- ⊢ `a = a`
  -- `h : ∀ x, x = x`
  specialize h a
  -- `h : a = a`
  exact h

/--
`specialize h a b`: specializes a multi-parameter `∀`.

Example: from `h : ∀ x y, x + y = y + x`, prove `a + b = b + a`.
-/
theorem specialize_multi (h : ∀ (x y : Nat), x + y = y + x) (a b : Nat) : a + b = b + a := by
  -- ⊢ `a + b = b + a`
  specialize h a b
  -- `h : a + b = b + a`
  exact h

/--
`generalize h : expr = x`: replaces all occurrences of `expr` with a fresh
variable `x` and introduces `h : expr = x`. Useful when you want to reason
about a subexpression abstractly.

Example: generalize `a + b` to study multiplication by zero.
-/
theorem generalize_basic (a b : Nat) : (a + b) * 0 = 0 := by
  -- ⊢ `(a + b) * 0 = 0`
  generalize h : a + b = s
  -- `h : a + b = s`
  -- ⊢ `s * 0 = 0`
  simp

/--
`rename` renames the most recent hypothesis whose *type* matches the given
pattern.  This is different from `rename_i`, which renames by binder position.

Example: rename a hypothesis of type `P` to `myP`.
-/
theorem rename_by_type (P Q : Prop) (hp : P) (_hq : Q) : P := by
  -- ⊢ `P`
  -- `hp : P`, `_hq : Q`
  rename P => myP
  -- `myP : P` (hp is now named myP)
  exact myP

/--
`rename` can disambiguate when multiple hypotheses have the same type;
it always targets the most recent one whose type matches the pattern.

Example: rename a hypothesis of type `P → Q`.
-/
theorem rename_function_type (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- ⊢ `Q`
  rename P → Q => himpl
  -- `himpl : P → Q`
  exact himpl hp

/--
`subst_vars`: applies `subst` to every hypothesis of the form `h : x = t`
or `h : t = x`, eliminating all such equations at once.
Useful for cleaning up a context full of equalities.

Example: from `h₁ : a = 5`, `h₂ : b = 3`, prove `a + b = 8`.
-/
theorem subst_vars_basic (a b : Nat) (h₁ : a = 5) (h₂ : b = 3) : a + b = 8 := by
  -- ⊢ `a + b = 8`
  subst_vars
  -- `a` replaced by `5`, `b` replaced by `3` everywhere
  -- ⊢ `5 + 3 = 8`
  rfl

/--
`subst_vars` avoids naming each equation individually.  It substitutes
all matching hypotheses at once.

Example: with multiple equations, all are substituted.
-/
theorem subst_vars_multi (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  -- ⊢ `a = c`
  subst_vars
  -- `a = b` and `b = c` are both substituted
  -- After substitution, `a` and `b` are replaced by `c`:
  -- ⊢ `c = c`
  rfl
