/-
# Advanced Tactics: `unfold`, `change`, `show`, `match`

These tactics give you fine-grained control over the shape of the goal.
`unfold` expands definitions, `change` replaces with definitionally equal terms,
`show` restates the goal for readability, and `match` performs pattern matching
in tactic mode.
-/

/--
`unfold` replaces a defined symbol by its definition. Unlike `dsimp` (which
only reduces definitionally), `unfold` works for any `def` or `theorem`.

Example: unfold a custom `triple` function.
-/
def triple (x : Nat) : Nat := x + x + x

theorem unfold_basic (x : Nat) : triple x = 3 * x := by
  -- ⊢ `triple x = 3 * x`
  unfold triple
  -- `triple x` becomes `x + x + x`
  -- ⊢ `x + x + x = 3 * x`
  omega

/--
`unfold` can unfold multiple definitions at once.

Example: unfold `triple` and `sq`.
-/
def sq (x : Nat) : Nat := x * x

theorem unfold_multi (x : Nat) : triple (sq x) = 3 * (x * x) := by
  -- ⊢ `triple (sq x) = 3 * (x * x)`
  unfold triple
  -- ⊢ `sq x + sq x + sq x = 3 * (x * x)`
  unfold sq
  -- ⊢ `(x * x) + (x * x) + (x * x) = 3 * (x * x)`
  omega

/--
`unfold` at a hypothesis: unfold a definition in `h` rather than the goal.

Example: unfold `triple` in hypothesis.
-/
theorem unfold_at_hyp (x : Nat) (h : triple x = 0) : x + x + x = 0 := by
  -- ⊢ `x + x + x = 0`
  -- `h : triple x = 0`
  unfold triple at h
  -- `h : x + x + x = 0`
  exact h

/--
`change` replaces the goal with a definitionally equal term. Unlike `unfold`,
`change` doesn't need to know the definition — it just checks definitional
equality between the current goal and the new expression.

Example: `2 + 3` is definitionally `5`.
-/
theorem change_basic : 2 + 3 = 5 := by
  -- ⊢ `2 + 3 = 5`
  change 5 = 5
  -- `2 + 3` reduces to `5` definitionally
  rfl

/--
`change` can be used to rewrite the goal to a more convenient form,
as long as the two forms are definitionally equal.

Example: change `a + 0` to `a`.
-/
theorem change_add_zero (a : Nat) : a + 0 = a := by
  -- ⊢ `a + 0 = a`
  -- `a + 0` is NOT definitionally `a` (Nat addition is defined by recursion on the first arg)
  -- So `change a = a` would fail here. Use `simp` or `Nat.add_zero`.
  simp

/--
`change` at a hypothesis: works like `change` but in a hypothesis.

Example: from `h : 2 + 3 = 5`, change to `h : 5 = 5`.
-/
theorem change_hyp (h : 2 + 3 = 5) : 5 = 5 := by
  -- ⊢ `5 = 5`
  -- `h : 2 + 3 = 5`
  change 5 = 5 at h
  -- `h : 5 = 5`
  exact h

/--
`show` restates the goal. Unlike `change`, it doesn't require definitional
equality — it just asserts what the goal type is (and verifies it matches).

Useful for documentation: making the current subgoal explicit.

Example: proving `P ∧ Q` with `show` to document each subgoal.
-/
theorem show_basic (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  -- ⊢ `P ∧ Q`
  constructor
  · show P
    exact hp
  · show Q
    exact hq

/--
`show` can change the goal to a syntactically different but definitionally
equal form. This is useful when the goal display is confusing.

Example: `show` with `calc`.
-/
theorem show_with_calc (a b : Nat) : (a + b) * 0 = 0 := by
  -- ⊢ `(a + b) * 0 = 0`
  show (a + b) * 0 = 0
  simp

/--
`match` in tactic mode: pattern matching on an expression to do case analysis.
Similar to `cases` but with syntax closer to term-level `match`.

Example: match on a `Nat` to see if it's `0` or `succ n`.
-/
theorem match_nat (n : Nat) : n = n := by
  -- ⊢ `n = n`
  match n with
  | 0 => rfl
  | m + 1 => rfl

/--
`match` on `List` with case analysis.

Example: `length (x :: xs) > 0`.
-/
theorem match_list (α : Type) (x : α) (xs : List α) : (x :: xs).length > 0 := by
  -- ⊢ `(x :: xs).length > 0`
  simp

/--
`match` can be used with `h :` to name the case hypothesis.

Example: `Nat.succ_pred_eq_of_pos`-like proof with match.
-/
theorem match_succ (n : Nat) (h : n ≠ 0) : n = Nat.succ (n - 1) := by
  -- ⊢ `n = Nat.succ (n - 1)`
  match n with
  | 0 => contradiction   -- `h : 0 ≠ 0`
  | m + 1 =>
      -- ⊢ `m + 1 = Nat.succ ((m + 1) - 1)`
      simp
