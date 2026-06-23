/-
# Tactic Control: `all_goals`, `first`, `try`, `repeat`, `focus`, `case`, `any_goals`

These tactics control how other tactics are applied across multiple subgoals.
They are essential for structuring complex proofs.
-/

/--
`all_goals` applies a tactic to every open goal simultaneously.

Example: prove `P ∧ P` by using `all_goals` to apply `exact hp` to both subgoals.
-/
theorem all_goals_basic (P : Prop) (hp : P) : P ∧ P := by
  -- ⊢ `P ∧ P`
  constructor
  all_goals
    -- ⊢ `P`
    exact hp

/--
`all_goals` with multiple tactics: uses `all_goals` to run `simp` on all goals.

Example: `a = a` and `b = b` in one shot.
-/
theorem all_goals_simp (a b : Nat) : a = a ∧ b = b := by
  -- ⊢ `a = a ∧ b = b`
  constructor
  all_goals
    rfl

/--
`any_goals` applies a tactic to at least one open goal. Unlike `all_goals`,
it succeeds even if some goals don't match.

Example: two goals, `simp` works on both.
-/
theorem any_goals_basic (a b : Nat) : (0 + a = a) ∧ (b + 0 = b) := by
  -- ⊢ `(0 + a = a) ∧ (b + 0 = b)`
  constructor
  any_goals simp

/--
`first` tries tactics in order and uses the first one that succeeds.

Example: try `rfl`, then `simp`, then `omega`.
-/
theorem first_tactics (a b : Nat) (h : a = b) : a + 0 = b := by
  -- ⊢ `a + 0 = b`
  first
  | exact h    -- `a = b` does not match `a + 0 = b`
  | rw [h]     -- this succeeds: rewrites `a` to `b`
  | simp

/--
`first` is useful for fallback logic: try a fast tactic, fall back to a slower one.

Example: fallback chain.
-/
theorem first_fallback (n : Nat) : 0 + n = n := by
  -- ⊢ `0 + n = n`
  first
  | rfl       -- `0 + n` is NOT definitionally `n` (Nat addition is defined by recursion on the first arg)
  | simp      -- `simp` works
  | omega

/--
`try` attempts a tactic and continues even if it fails. Essential when you
want to apply a tactic that may or may not match.

Example: try `simp` on each goal, don't stop if one goal doesn't simplify.
-/
theorem try_basic (a b : Nat) : (a + 0 = a) ∧ (0 + b = b) := by
  -- ⊢ `(a + 0 = a) ∧ (0 + b = b)`
  constructor
  · simp          -- `simp` works: `a + 0 = a`
  · simp          -- `simp` works: `0 + b = b`

/--
`try` with a failing tactic: `try` absorbs the failure.

Example: `try` `rfl` first (may fail), then `simp`.
-/
theorem try_fallback (a b : Nat) (h : a = b) : a + a = b + b := by
  -- ⊢ `a + a = b + b`
  try rfl
  -- `rfl` fails (not definitionally equal), but `try` absorbs the failure
  rw [h]

/--
`repeat` applies a tactic repeatedly until it fails. Useful for eliminating
a stack of implications.

Example: `P → Q → R → P` — use `repeat` to `intro` all at once.
-/
theorem repeat_intro (P Q R : Prop) : P → Q → R → P := by
  -- ⊢ `P → Q → R → P`
  repeat intro
  -- After `repeat intro`, all antecedents are introduced
  -- `a✝ : P`, `a✝¹ : Q`, `a✝² : R`
  -- ⊢ `P`
  assumption

/--
`repeat` can apply any tactic, not just `intro`.

Example: rewrite all occurrences of `a` to `b` using `h : a = b`.
-/
theorem repeat_rw (a b : Nat) (h : a = b) : (a + a) + a = (b + b) + b := by
  -- ⊢ `(a + a) + a = (b + b) + b`
  repeat rw [h]
  -- All `a`s are rewritten to `b`
  -- The goal `(b + b) + b = (b + b) + b` is closed by `repeat rw`
/--
`focus` temporarily isolates the current goal; other goals are suspended.
Useful when you want to work on one goal without seeing others.

-/
theorem focus_basic (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  -- ⊢ `P ∧ Q`
  constructor
  · -- ⊢ `P`
    focus
    exact hp
  · -- ⊢ `Q`
    exact hq

/--
`case` names a case from `cases` or `induction` and focuses it.
Makes the proof self-documenting by naming each branch.

Example: case analysis on `Bool` with named cases.
-/
theorem case_bool (b : Bool) : !(!b) = b := by
  -- ⊢ `!(!b) = b`
  cases b
  case false =>
    -- ⊢ `!(!false) = false`
    rfl
  case true =>
    -- ⊢ `!(!true) = true`
    rfl

/--
`case` with constructor names from `induction`.

Example: `Nat` induction with named cases.
-/
theorem case_induction (n : Nat) : 0 + n = n := by
  -- ⊢ `0 + n = n`
  induction n
  case zero =>
    -- ⊢ `0 + 0 = 0`
    rfl
  case succ n ih =>
    -- `n : Nat`, `ih : 0 + n = n`
    -- ⊢ `0 + Nat.succ n = Nat.succ n`
    simp

/--
`case` can also rename the introduced variables with `case succ n ih =>`.
-/
theorem case_rename (n : Nat) : n + 0 = n := by
  -- ⊢ `n + 0 = n`
  induction n
  case zero =>
    rfl
  case succ m ih =>
    -- `m` replaces the auto-generated name `n`
    -- `ih : m + 0 = m`
    -- ⊢ `Nat.succ m + 0 = Nat.succ m`
    simp

/--
`done`: succeeds only when there are no remaining goals.  Useful as a
sanity check at the end of a branch.

Example: after `exact`, assert that the goal is closed.
+-/
theorem done_basic (P : Prop) (hp : P) : P := by
  -- ⊢ `P`
  exact hp
  done

/--
`skip`: does nothing (no-op).  Useful as a placeholder or when a branch
was already closed by a previous tactic.

Example: `skip` doesn't change the goal.
+-/
theorem skip_basic (P : Prop) (hp : P) : P := by
  -- ⊢ `P`
  skip
  -- still ⊢ `P`
  exact hp

/--
`next` is like `case _ =>` but works without naming the case.
It focuses the next goal and optionally renames auto-generated binders.

Example: prove a conjunction without naming the goals.
+-/
theorem next_basic (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  -- ⊢ `P ∧ Q`
  constructor
  -- Two subgoals: `P` and `Q`
  next => exact hp
  next => exact hq

/--
`rotate_left n` moves the first `n` goals to the back.
`rotate_right n` moves the last `n` goals to the front.
The default for `n` is `1`.

Example: with three subgoals, bring the third one forward.
+-/
theorem rotate_basic (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : P ∧ Q ∧ R := by
  -- ⊢ `P ∧ Q ∧ R`
  constructor
  · exact hp
  · constructor
    · exact hq
    · exact hr

/--
`rotate_left 1` (default) moves the first subgoal to the back.

Example: `P ∧ Q ∧ R` — rotate the goals so `Q` comes first.
+-/
theorem rotate_left_example (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : P ∧ (Q ∧ R) := by
  -- ⊢ `P ∧ (Q ∧ R)`
  constructor
  · exact hp
  · constructor
    rotate_left 1
    · exact hr
    · exact hq
