/-
# Natural Number Game (All Levels)

A complete transcription of the [Natural Number Game (NNG4)](
https://adam.math.hhu.de/#/g/leanprover-community/nng4) into a single
self-contained file. Each level teaches one or two tactics by proving
a theorem about natural numbers.

Instead of playing through the interactive game, open this file in VS Code
and step through each `by` block with the Lean infoview to see how every
tactic changes the goal.

## How to use

1. Place your cursor inside any `by` block.
2. Execute one tactic at a time.
3. Watch the goal update in the infoview.
4. Read the doc comment above each theorem — it explains the tactic and
   shows the goal state before and after.

## Note

The original NNG uses a custom `MyNat` type and defines `a ≤ b` as
`∃ c, b = a + c`. This file uses Lean's built-in `Nat` and its native
`Nat.le`, so some proofs differ slightly from the game's canonical solutions.

**Lean 4.30 limitation**: `apply h at h1` is not supported. Use `apply h`
(to the goal) or `have := h h1; exact this` instead.
-/

set_option pp.unicode.fun true
set_option linter.unusedVariables false


/-!
## Helper definitions and lemmas

These correspond to theorems the NNG game awards after completing levels.
-/

namespace NNG

/-- Numeral abbreviations from the game. -/
theorem one_eq_succ_zero : (1 : Nat) = Nat.succ 0 := by decide
theorem two_eq_succ_one  : (2 : Nat) = Nat.succ 1 := by decide
theorem three_eq_succ_two : (3 : Nat) = Nat.succ 2 := by decide
theorem four_eq_succ_three : (4 : Nat) = Nat.succ 3 := by decide

/-- The predecessor function (used to prove `succ_inj` in Algorithm World). -/
def pred (n : Nat) : Nat :=
  match n with | 0 => 37 | Nat.succ n' => n'

theorem pred_succ (n : Nat) : pred (Nat.succ n) = n := by rfl

/-- `is_zero` predicate: true only for `0`. -/
def is_zero : Nat → Prop
  | 0 => True
  | Nat.succ _ => False

theorem is_zero_zero : is_zero 0 = True := by rfl
theorem is_zero_succ (a : Nat) : is_zero (Nat.succ a) = False := by rfl

/-- `succ_inj a b h : Nat.succ a = Nat.succ b → a = b`. -/
theorem succ_inj (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b :=
  (Nat.succ_inj (a := a) (b := b)).mp h

/-- `zero_ne_succ n : 0 ≠ Nat.succ n`. -/
theorem zero_ne_succ (n : Nat) : (0 : Nat) ≠ Nat.succ n := by
  intro h; exact Nat.succ_ne_zero n h.symm

/-- `succ_ne_zero a : Nat.succ a ≠ 0`. -/
theorem succ_ne_zero (a : Nat) : Nat.succ a ≠ 0 := Nat.succ_ne_zero a

/-- `succ_eq_add_one n : Nat.succ n = n + 1`. -/
theorem succ_eq_add_one (n : Nat) : Nat.succ n = n + 1 := Nat.succ_eq_add_one n

/-- A custom tactic that normalises additive expressions by commuting
and reassociating. -/
macro "simp_add" : tactic => `(tactic|(
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]))

/-!
## Addition World (core theorems, placed here so later worlds can use them)
-/

/-- `zero_add n : 0 + n = n`. Proved by induction on `n`. -/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rw [Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, hd]

/-- `succ_add a b : Nat.succ a + b = Nat.succ (a + b)`. Induction on `b`. -/
theorem succ_add (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, Nat.add_succ, hd]

/-- `add_comm a b : a + b = b + a`. Induction on `b`. -/
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction b with
  | zero => rw [Nat.add_zero, zero_add]
  | succ d hd => rw [Nat.add_succ, succ_add, hd]

/-- `add_assoc a b c : (a + b) + c = a + (b + c)`. Induction on `c`. -/
theorem add_assoc (a b c : Nat) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, Nat.add_succ, hd, Nat.add_succ]

/-- `add_right_comm a b c : (a + b) + c = (a + c) + b`. -/
theorem add_right_comm (a b c : Nat) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b, add_assoc]

/-!
## Multiplication World (core theorems)
-/

/-- `mul_one m : m * 1 = m`. -/
theorem mul_one (m : Nat) : m * 1 = m := by
  rw [one_eq_succ_zero, Nat.mul_succ, Nat.mul_zero, zero_add]

/-- `zero_mul m : 0 * m = 0`. Induction on `m`. -/
theorem zero_mul (m : Nat) : 0 * m = 0 := by
  induction m with
  | zero => rw [Nat.mul_zero]
  | succ d hd => rw [Nat.mul_succ, hd, Nat.add_zero]

/-- `succ_mul a b : Nat.succ a * b = a * b + b`. Uses `Nat.succ_mul`. -/
theorem succ_mul (a b : Nat) : Nat.succ a * b = a * b + b :=
  Nat.succ_mul a b

/-- `mul_comm a b : a * b = b * a`. Induction on `b`. -/
theorem mul_comm (a b : Nat) : a * b = b * a := by
  induction b with
  | zero => rw [zero_mul, Nat.mul_zero]
  | succ d hd => rw [Nat.mul_succ, succ_mul, hd]

/-- `one_mul m : 1 * m = m`. Derived from `mul_comm` and `mul_one`. -/
theorem one_mul (m : Nat) : 1 * m = m := by rw [mul_comm, mul_one]

/-- `two_mul m : 2 * m = m + m`. -/
theorem two_mul (m : Nat) : 2 * m = m + m := by
  rw [two_eq_succ_one, succ_mul, one_mul]

/-- `mul_add a b c : a * (b + c) = a * b + a * c`. Induction on `c`. -/
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, Nat.mul_succ, hd, Nat.mul_succ, add_assoc]

/-- `add_mul a b c : (a + b) * c = a * c + b * c`. Derived from `mul_comm`, `mul_add`. -/
theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c, mul_comm c]

/-- `mul_assoc a b c : (a * b) * c = a * (b * c)`. Induction on `c`. -/
theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ d hd => rw [Nat.mul_succ, Nat.mul_succ, hd, mul_add]

/-!
## Power World (core theorems)
-/

/-- `pow_one a : a ^ 1 = a`. -/
theorem pow_one (a : Nat) : a ^ 1 = a := by
  rw [one_eq_succ_zero, Nat.pow_succ, Nat.pow_zero, one_mul]

/-- `one_pow m : 1 ^ m = 1`. Induction on `m`. -/
theorem one_pow (m : Nat) : (1 : Nat) ^ m = 1 := by
  induction m with
  | zero => rw [Nat.pow_zero]
  | succ t ht => rw [Nat.pow_succ, ht, Nat.mul_one]

/-- `pow_two a : a ^ 2 = a * a`. -/
theorem pow_two (a : Nat) : a ^ 2 = a * a := by
  rw [two_eq_succ_one, Nat.pow_succ, pow_one]

/-- `pow_add a m n : a ^ (m + n) = a ^ m * a ^ n`. Induction on `n`. -/
theorem pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ t ht => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ht, mul_assoc]

/-- `mul_pow a b n : (a * b) ^ n = a ^ n * b ^ n`. Induction on `n`. -/
theorem mul_pow (a b n : Nat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero, Nat.mul_one]
  | succ t ht =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ht]
      simp [mul_assoc, mul_comm, Nat.mul_left_comm]

/-- `pow_pow a m n : (a ^ m) ^ n = a ^ (m * n)`. Induction on `n`. -/
theorem pow_pow (a m n : Nat) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ t ht => rw [Nat.pow_succ, ht, Nat.mul_succ, pow_add]

/-- `add_sq a b : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b`. -/
theorem add_sq (a b : Nat) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [pow_two, pow_two, pow_two]
  rw [add_right_comm]
  rw [mul_add, add_mul, add_mul]
  rw [two_mul, add_mul]
  rw [mul_comm b a]
  rw [← add_assoc, ← add_assoc]

end NNG


/-! # 1. Tutorial World

Basic tactics: `rfl`, `rw`, `nth_rewrite`, `simp`.
-/

namespace Tutorial
open NNG

/-- `rfl` proves `X = X` when both sides are syntactically identical.
It is the reflexivity of equality.

Goal before: `37*x + q = 37*x + q`
Goal after:  (none — closed by `rfl`)
-/
theorem level1 (x q : Nat) : 37 * x + q = 37 * x + q := by
  rfl

/--
`rw [h]` replaces every `X` with `Y` in the goal, where `h : X = Y`.
`rw [← h]` goes the other way (`Y` → `X`).

Here `h : y = x + 7`, so rewriting `y` with `x + 7` gives `2*(x+7) = 2*(x+7)`.
-/
theorem level2 (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- ⊢ `2 * y = 2 * (x + 7)`
  rw [h]
  -- ⊢ `2 * (x + 7) = 2 * (x + 7)`

/-- Rewriting with the numeral definitions `two_eq_succ_one` and
`one_eq_succ_zero` to reveal the Peano structure. -/
theorem level3 : (2 : Nat) = Nat.succ (Nat.succ 0) := by
  rw [two_eq_succ_one, one_eq_succ_zero]

/-- Using `←` to rewrite backwards. -/
theorem level4 : (2 : Nat) = Nat.succ (Nat.succ 0) := by
  rw [← one_eq_succ_zero, ← two_eq_succ_one]

/-- `simp` can close simple arithmetic goals automatically. -/
theorem level5 (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  simp

/-- Giving an explicit argument to a rewrite lemma targets only that occurrence.
`Nat.add_zero c` rewrites `c + 0` to `c`. -/
theorem level6 (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [Nat.add_zero c, Nat.add_zero b]

/-- `Nat.add_succ a d : a + Nat.succ d = Nat.succ (a + d)`.

Prove `Nat.succ n = n + 1` by unfolding `1` into `Nat.succ 0`.
-/
theorem level7_succ_eq_add_one (n : Nat) : Nat.succ n = n + 1 := by
  rw [one_eq_succ_zero, Nat.add_succ, Nat.add_zero]

/-- `2 + 2 = 4`, now trivial with `decide`. -/
theorem level8 : (2 : Nat) + 2 = 4 := by
  decide

end Tutorial


/-! # 2. Addition World

Core technique: `induction` (structural induction on `Nat`).
All theorems are proved here; the NNG namespace already contains them
so later worlds can use them without re-proving.
-/

namespace Addition
open NNG

theorem zero_add (n : Nat) : 0 + n = n := NNG.zero_add n
theorem succ_add (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := NNG.succ_add a b
theorem add_comm (a b : Nat) : a + b = b + a := NNG.add_comm a b
theorem add_assoc (a b c : Nat) : a + b + c = a + (b + c) := NNG.add_assoc a b c
theorem add_right_comm (a b c : Nat) : a + b + c = a + c + b := NNG.add_right_comm a b c

end Addition


/-! # 3. Multiplication World -/

namespace Multiplication
open NNG

theorem mul_one (m : Nat) : m * 1 = m := NNG.mul_one m
theorem zero_mul (m : Nat) : 0 * m = 0 := NNG.zero_mul m
theorem succ_mul (a b : Nat) : Nat.succ a * b = a * b + b := NNG.succ_mul a b
theorem mul_comm (a b : Nat) : a * b = b * a := NNG.mul_comm a b
theorem one_mul (m : Nat) : 1 * m = m := NNG.one_mul m
theorem two_mul (m : Nat) : 2 * m = m + m := NNG.two_mul m
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := NNG.mul_add a b c
theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := NNG.add_mul a b c
theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := NNG.mul_assoc a b c

end Multiplication


/-! # 4. Implication World

Tactics: `exact`, `apply`, `intro`, `symm`.
Logical symbols: `→` (implies), `≠` (defined as `a = b → False`).

**Note**: `apply h at h1` is not available in Lean 4.30. Use `apply h`
(to the goal) or `have := h h1`.
-/

namespace Implication
open NNG

/-- `exact h` closes a goal when `h` has exactly the goal type. -/
theorem level1 (x y z : Nat) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  -- ⊢ `x + y = 37`
  exact h1

/-- Combine `rw` on a hypothesis with `exact`. -/
theorem level2 (x y : Nat) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  rw [zero_add] at h   -- `h : x = 0 + y + 2`
  rw [zero_add] at h   -- `h : x = y + 2`
  exact h

/-- `apply` uses an implication to change the goal.
If `h2 : x = 37 → y = 42` and the goal is `y = 42`,
then `apply h2` changes the goal to `x = 37`. -/
theorem level3 (x y : Nat) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- ⊢ `y = 42`
  apply h2
  -- ⊢ `x = 37`
  exact h1

/-- `succ_inj a b : Nat.succ a = Nat.succ b → a = b`.

Here we rewrite `4` to `Nat.succ 3`, then `x+1` to `Nat.succ x`,
then apply `succ_inj`. -/
theorem level4 (x : Nat) (h : x + 1 = 4) : x = 3 := by
  rw [four_eq_succ_three] at h
  rw [← succ_eq_add_one] at h
  exact succ_inj _ _ h

/-- Same proof, but arguing backwards: apply `succ_inj` to the goal first. -/
theorem level5 (x : Nat) (h : x + 1 = 4) : x = 3 := by
  -- ⊢ `x = 3`
  apply succ_inj
  -- ⊢ `Nat.succ x = Nat.succ 3`
  rw [succ_eq_add_one, ← four_eq_succ_three]
  exact h

/-- `intro h` assumes the antecedent of an implication. -/
theorem level6 (x : Nat) : x = 37 → x = 37 := by
  intro h
  exact h

/-- `intro` followed by rewriting and `succ_inj`. -/
theorem level7 (x y : Nat) : x + 1 = y + 1 → x = y := by
  intro h
  repeat rw [← succ_eq_add_one] at h
  exact succ_inj _ _ h

/-- `a ≠ b` is notation for `a = b → False`. -/
theorem level8 (x y : Nat) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2
  exact h1

/-- `zero_ne_succ n : 0 ≠ Nat.succ n`. -/
theorem zero_ne_one : (0 : Nat) ≠ 1 := by
  intro h
  rw [one_eq_succ_zero] at h
  exact zero_ne_succ 0 h

/-- `symm` swaps the two sides of an equality. -/
theorem one_ne_zero : (1 : Nat) ≠ 0 := by
  symm
  exact zero_ne_one

/-- `2 + 2 ≠ 5`, proved by repeatedly stripping `Nat.succ` via `succ_inj`. -/
theorem level11 : Nat.succ (Nat.succ 0) + Nat.succ (Nat.succ 0) ≠
                 Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := by
  intro h
  rw [Nat.add_succ, Nat.add_succ, Nat.add_zero] at h
  have h4 := succ_inj _ _ (succ_inj _ _ (succ_inj _ _ (succ_inj _ _ h)))
  -- h4 : 0 = 1
  rw [one_eq_succ_zero] at h4
  exact zero_ne_succ 0 h4

end Implication


/-! # 5. Power World -/

namespace Power
open NNG

theorem zero_pow_zero : (0 : Nat) ^ 0 = 1 := by rw [Nat.pow_zero]
theorem zero_pow_succ (m : Nat) : (0 : Nat) ^ (Nat.succ m) = 0 := by rw [Nat.pow_succ, Nat.mul_zero]
theorem pow_one (a : Nat) : a ^ 1 = a := NNG.pow_one a
theorem one_pow (m : Nat) : (1 : Nat) ^ m = 1 := NNG.one_pow m
theorem pow_two (a : Nat) : a ^ 2 = a * a := NNG.pow_two a
theorem pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := NNG.pow_add a m n
theorem mul_pow (a b n : Nat) : (a * b) ^ n = a ^ n * b ^ n := NNG.mul_pow a b n
theorem pow_pow (a m n : Nat) : (a ^ m) ^ n = a ^ (m * n) := NNG.pow_pow a m n
theorem add_sq (a b : Nat) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := NNG.add_sq a b

/-- Fermat's Last Theorem — NNG's final "boss" joke level. It is a true theorem
(Wiles, 1995) but its proof is out of reach here, so we record only its
*statement* as a `Prop`, rather than fake a proof with `sorry`. Every actual
level in this file is fully proved. -/
def FLT : Prop := ∀ a b c n : Nat,
  (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3)

end Power


/-! # 6. Advanced Addition World

Cancellation laws and consequences of `a + b = 0`.
-/

namespace AdvAddition
open NNG

/-- `add_right_cancel a b n : a + n = b + n → a = b`.
Induction on `n`. -/
theorem add_right_cancel (a b n : Nat) : a + n = b + n → a = b := by
  induction n with
  | zero =>
      intro h
      -- ⊢ `a = b`, but `h : a + 0 = b + 0`
      rw [Nat.add_zero, Nat.add_zero] at h
      exact h
  | succ d hd =>
      intro h
      rw [Nat.add_succ, Nat.add_succ] at h
      apply hd
      exact succ_inj _ _ h

/-- `add_left_cancel a b n : n + a = n + b → a = b`.
Reduces to `add_right_cancel` via commutativity. -/
theorem add_left_cancel (a b n : Nat) : n + a = n + b → a = b := by
  rw [add_comm n a, add_comm n b]
  exact add_right_cancel a b n

/-- `add_left_eq_self x y : x + y = y → x = 0`. -/
theorem add_left_eq_self (x y : Nat) : x + y = y → x = 0 := by
  intro h
  have h' : x + y = 0 + y := by rw [zero_add y]; exact h
  exact add_right_cancel x 0 y h'

/-- `add_right_eq_self x y : x + y = x → y = 0`.
Uses `add_comm` and `add_left_eq_self`. -/
theorem add_right_eq_self (x y : Nat) : x + y = x → y = 0 := by
  rw [add_comm]; exact add_left_eq_self y x

/-- `add_right_eq_zero a b : a + b = 0 → a = 0`.
Case analysis on `b`: if `b = 0`, trivial; if `b = Nat.succ d`, impossible. -/
theorem add_right_eq_zero (a b : Nat) : a + b = 0 → a = 0 := by
  cases b with
  | zero => intro h; rw [Nat.add_zero] at h; exact h
  | succ d =>
      intro h; rw [Nat.add_succ] at h
      exact absurd h (Nat.succ_ne_zero (a + d))

/-- `add_left_eq_zero a b : a + b = 0 → b = 0`. Uses `add_comm` and `add_right_eq_zero`. -/
theorem add_left_eq_zero (a b : Nat) : a + b = 0 → b = 0 := by
  rw [add_comm]; exact add_right_eq_zero b a

end AdvAddition


/-! # 7. ≤ World

Uses core `Nat.le` rather than NNG's `∃ c, b = a + c` definition.
-/

namespace LessOrEqual

theorem le_refl (x : Nat) : x ≤ x := Nat.le_refl x
theorem zero_le (x : Nat) : 0 ≤ x := Nat.zero_le x
theorem le_succ_self (x : Nat) : x ≤ Nat.succ x := Nat.le_succ x
theorem le_trans (x y z : Nat) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := Nat.le_trans hxy hyz
theorem le_zero (x : Nat) (hx : x ≤ 0) : x = 0 := Nat.eq_zero_of_le_zero hx
theorem le_antisymm (x y : Nat) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := Nat.le_antisymm hxy hyx

/-- `left`/`right` choose a disjunct when the goal is `P ∨ Q`. -/
theorem level7 (x y : Nat) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  rcases h with (hx | hy)
  · right; exact hx
  · left; exact hy

theorem le_total (x y : Nat) : x ≤ y ∨ y ≤ x := Nat.le_total x y

/-- `Nat.succ x ≤ Nat.succ y → x ≤ y`. -/
theorem succ_le_succ (x y : Nat) (hx : Nat.succ x ≤ Nat.succ y) : x ≤ y :=
  (Nat.succ_le_succ_iff.mp hx)

/-- `x ≤ 1 → x = 0 ∨ x = 1`. Cases on `x`. -/
theorem le_one (x : Nat) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with
  | zero => left; rfl
  | succ x' =>
      cases x' with
      | zero => right; rfl
      | succ _ => exfalso; omega

/-- `x ≤ 2 → x = 0 ∨ x = 1 ∨ x = 2`. -/
theorem le_two (x : Nat) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  cases x with
  | zero => left; rfl
  | succ x' =>
      cases x' with
      | zero => right; left; rfl
      | succ x'' =>
          cases x'' with
          | zero => right; right; rfl
          | succ _ => exfalso; omega

end LessOrEqual


/-! # 8. Advanced Multiplication World

Cancellation and zero-divisor facts, proved with core `Nat` lemmas
(`Nat.eq_of_mul_eq_mul_left`, `Nat.succ_mul`) and case analysis.
-/

namespace AdvMultiplication
open NNG

/-- `a ≤ b → a*t ≤ b*t`. -/
theorem mul_le_mul_right (a b t : Nat) (h : a ≤ b) : a * t ≤ b * t :=
  Nat.mul_le_mul_right t h

/-- `a ≠ 0 → ∃ d, a = Nat.succ d`. Cases on `a`. -/
theorem eq_succ_of_ne_zero (a : Nat) (h : a ≠ 0) : ∃ d, a = Nat.succ d := by
  cases a with
  | zero => exfalso; exact h rfl
  | succ d => exact ⟨d, rfl⟩

/-- `a ≠ 0 → 1 ≤ a`. -/
theorem one_le_of_ne_zero (a : Nat) (h : a ≠ 0) : 1 ≤ a :=
  Nat.one_le_of_lt (Nat.pos_of_ne_zero h)

/-- `a ≠ 0 → b ≤ a * b`. Writing `a = succ d`, `a * b = d*b + b ≥ b`. -/
theorem le_mul_right (a b : Nat) (h : a ≠ 0) : b ≤ a * b := by
  obtain ⟨d, rfl⟩ := eq_succ_of_ne_zero a h
  rw [Nat.succ_mul]
  exact Nat.le_add_left b (d * b)

/-- `a ≠ 0 → a * b = a → b = 1`. Rewrite `a` as `a * 1`, then cancel `a`. -/
theorem mul_right_eq_one (a b : Nat) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  have h' : a * b = a * 1 := by rw [Nat.mul_one]; exact h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) h'

theorem mul_ne_zero (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  Nat.mul_ne_zero ha hb

/-- `a * b = 0 → a = 0 ∨ b = 0`.
Core Lean does not have this lemma; we prove it by case analysis. -/
theorem mul_eq_zero (a b : Nat) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  cases a with
  | zero => left; rfl
  | succ a' =>
      cases b with
      | zero => right; rfl
      | succ b' =>
          exfalso
          have hpos : (Nat.succ a') * (Nat.succ b') > 0 :=
            Nat.mul_pos (Nat.succ_pos a') (Nat.succ_pos b')
          rw [h] at hpos; exact Nat.lt_irrefl 0 hpos

/-- `a ≠ 0 → a * b = a * c → b = c`. Left cancellation via `Nat.eq_of_mul_eq_mul_left`. -/
theorem mul_left_cancel (a b c : Nat) (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) h

end AdvMultiplication


/-! # 9. Algorithm World

Custom tactics, `simp`, `decide`.
Core technique: define `pred` and `is_zero` to prove `succ_inj` and `succ_ne_zero`.
-/

namespace Algorithm
open NNG

/-- `add_left_comm a b c : a + (b + c) = b + (a + c)`.
Derived from `add_assoc` and `add_comm`. -/
theorem add_left_comm (a b c : Nat) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

/-- Using commutativity and associativity to rearrange terms manually. -/
theorem level2 (a b c d : Nat) : a + b + (c + d) = a + c + d + b := by
  omega

/-- `simp` with `add_left_comm` and `add_comm` can handle arbitrary additive
permutations automatically. -/
theorem level3 (a b c d e f g h : Nat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_left_comm, add_comm]

/-- The custom `simp_add` macro does the same. -/
theorem level4 (a b c d e f g h : Nat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add

/-- Proving `succ_inj` using `pred`. -/
theorem level5_succ_inj (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b := by
  calc
    a = pred (Nat.succ a) := by rw [pred_succ]
    _ = pred (Nat.succ b) := by rw [h]
    _ = b := by rw [pred_succ]

/-- Proving `succ_ne_zero` using `is_zero`. -/
theorem level6_succ_ne_zero (a : Nat) : Nat.succ a ≠ 0 := by
  intro h
  rw [← is_zero_succ a, h, is_zero_zero]; trivial

/-- `m ≠ n → Nat.succ m ≠ Nat.succ n`. -/
theorem succ_ne_succ (m n : Nat) (h : m ≠ n) : Nat.succ m ≠ Nat.succ n := by
  intro hsucc; apply h; exact succ_inj _ _ hsucc

/-- `decide` automates decidable propositions about `Nat`. -/
theorem level8 : (20 : Nat) + 20 = 40 := by
  decide

theorem level9 : (2 : Nat) + 2 ≠ 5 := by
  decide

end Algorithm
