/-
# Rewriting & Simplification: `rw`, `simp`, `dsimp`, `simpa`

Rewriting tactics transform the goal (or a hypothesis) by replacing subexpressions
using equalities. `rw` is precise — you control which equality fires where.
`simp` is sweeping — it uses the simplifier's database. `dsimp` only performs
definitional reduction. `simpa` is `simp` then `exact`.
-/

/--
`rw` (rewrite): replace the goal using an equality. Reads left-to-right by default.

Example: using `Nat.add_comm` to rewrite `n + m` into `m + n`.
-/
theorem rw_basic (n m : Nat) : n + m = m + n := by
  -- ⊢ `n + m = m + n`
  rw [Nat.add_comm n m]
  -- After rewrite: goal becomes `m + n = m + n`, which `rw` leaves for us
  -- ⊢ `m + n = m + n`

/--
`rw ←` (rewrite backwards): apply the equality in reverse.

Example: from `h : a = b`, rewrite `a` to `b` in the goal.
-/
theorem rw_backwards (a b : Nat) (h : a = b) : a + a = b + a := by
  -- ⊢ `a + a = b + a`
  rw [h]
  -- `h` rewrites `a` to `b` in the goal
  -- ⊢ `b + a = b + a`

/--
`rw` at a hypothesis: rewrite inside a hypothesis instead of the goal.

Example: from `h : a + 0 = b` and `Nat.add_zero`, derive `a = b`.
-/
theorem rw_at_hyp (a b : Nat) (h : a + 0 = b) : a = b := by
  -- ⊢ `a = b`
  -- `h : a + 0 = b`
  rw [Nat.add_zero a] at h
  -- Now `h : a = b`
  exact h

/--
`rw` can chain multiple rewrites in one step.

Example: `a + 0 + 0 = a`. Note: `a + 0 + 0` is parsed as `(a + 0) + 0`.
-/
theorem rw_chain (a : Nat) : a + 0 + 0 = a := by
  -- ⊢ `(a + 0) + 0 = a`
  rw [Nat.add_zero (a + 0)]
  -- Rewrites `(a + 0) + 0` to `a + 0`
  -- ⊢ `a + 0 = a`
  rw [Nat.add_zero a]
  -- ⊢ `a = a`

/--
`simp`: simplifies the goal using the simplifier's rule database.
Works for many built-in arithmetic identities.

Example: `0 + n = n` and `n + 0 = n`.
-/
theorem simp_basic (n : Nat) : 0 + n = n := by
  -- ⊢ `0 + n = n`
  simp

/--
`simp` also works on hypotheses with `simp at h`.

Example: from `h : 0 + n ≠ n`, derive a contradiction.
-/
theorem simp_at_hyp (n : Nat) (h : 0 + n ≠ n) : False := by
  -- ⊢ `False`
  -- `h : 0 + n ≠ n`
  simp at h
  -- `simp` simplifies `0 + n` to `n`, then `n ≠ n` to `False`
  -- So `h : False`

/--
`simp` with extra lemmas: `simp [h]` adds `h` to the simplification rules.

Example: from `h : a = b`, show `a + c = b + c`.
-/
theorem simp_with_lemma (a b c : Nat) (h : a = b) : a + c = b + c := by
  -- ⊢ `a + c = b + c`
  simp [h]

/--
`dsimp`: definitional simplification only — no lemma database.
Useful for unfolding `id`, `Function.comp`, etc.

Example: unfold a custom `double` definition.
-/
def double (x : Nat) : Nat := x + x

theorem dsimp_example (x : Nat) : double x = x + x := by
  -- ⊢ `double x = x + x`
  dsimp [double]
  -- `double x` reduces to `x + x`
  -- ⊢ `x + x = x + x`

/--
`simpa`: tries `simp` on the goal, then `exact` — a one-shot finishing move.

Example: prove `0 + n = n` without typing `simp` then `rfl`.
-/
theorem simpa_example (n : Nat) : (fun x : Nat => 0 + x) n = n := by
  -- ⊢ `(fun x => 0 + x) n = n`
  -- `simp` can't handle the lambda directly; `dsimp` first
  dsimp
  -- ⊢ `0 + n = n`
  simp

/--
`simp` with all hypotheses via `simp [*]` is not recommended (* is fragile),
but `simp [h₁, h₂]` with explicit lemma names is fine.

Example: from `h₁ : a = 5` and `h₂ : b = 3`, show `a + b = 8`.
-/
theorem simp_all_hypotheses (a b : Nat) (h₁ : a = 5) (h₂ : b = 3) : a + b = 8 := by
  -- ⊢ `a + b = 8`
  simp [h₁, h₂]
