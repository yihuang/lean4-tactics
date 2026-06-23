/-
# Software Formal Verification Examples

This module demonstrates how Lean tactics are used in practice to verify
software properties: loop invariants, arithmetic safety, functional correctness,
and data structure invariants.
-/

/-! ## Functional Correctness -/

/-- Recursive factorial: `fact n = n!` -/
def fact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | m + 1 => (m + 1) * fact m

/-- `fact n` is always positive.  Uses `induction` and `omega`. -/
theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp [fact]
    omega

/-! ## Arithmetic Safety -/

/-- `safe_div` checks for zero before dividing. -/
theorem safe_div_pos (a b : Nat) (_h : b > 0) : safe_div a b = some (a / b) := by
  if h : b > 0 then some (a / b) else none

/-- `safe_div` returns `some` iff the divisor is positive. -/
theorem safe_div_pos (a b : Nat) (h : b > 0) : safe_div a b = some (a / b) := by
  unfold safe_div; simp [h]

/-- `safe_div` returns `none` when divisor is zero. -/
theorem safe_div_zero (a : Nat) : safe_div a 0 = none := by
  unfold safe_div; simp

/-! ## List Properties -/

/-- `reverse` is involutive: `reverse (reverse xs) = xs`. -/
theorem reverse_reverse (xs : List Nat) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- `map` distributes over `++`. -/
theorem map_append (f : Nat → Nat) (xs ys : List Nat) :
    (xs ++ ys).map f = xs.map f ++ ys.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- `length (xs ++ ys) = length xs + length ys`. -/
theorem length_append (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

/-! ## Termination & Structural Recursion -/

/-- A recursive function that sums only even numbers in a list. -/
def sumEven : List Nat → Nat
  | [] => 0
  | x :: xs => (if x % 2 = 0 then x else 0) + sumEven xs

/-- `sumEven` never exceeds the sum of all elements. -/
theorem sumEven_le_sum (xs : List Nat) : sumEven xs ≤ xs.sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp [sumEven, List.sum_cons]
    by_cases h : x % 2 = 0
    · simp [h]; omega
    · simp [h]; omega

/-! ## Function Contract Pattern -/

/-- `longestPrefix p xs` returns the length of the longest prefix where `p` holds. -/
def longestPrefix (p : Nat → Bool) (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs' => if p x then 1 + longestPrefix p xs' else 0

/-- If `p` holds for every element, `longestPrefix` returns the full length. -/
theorem longestPrefix_all (p : Nat → Bool) (xs : List Nat) (hall : ∀ x ∈ xs, p x) :
    longestPrefix p xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x := hall x (by simp)
    have hrest : ∀ y ∈ xs, p y := by
      intro y hy; exact hall y (by simp [hy])
    simp [longestPrefix, hx, ih hrest]; omega

/-! ## State Machine: Counter -/

structure Counter where
  value : Nat

def counter_inc (c : Counter) : Counter :=
  { c with value := c.value + 1 }

def counter_dec (c : Counter) : Counter :=
  { c with value := c.value - 1 }

theorem longestPrefix_all (p : Nat → Bool) (xs : List Nat) (_hall : ∀ x ∈ xs, p x) :

/-- `inc` then `dec` is identity when `value > 0`. -/
theorem inc_dec_identity (c : Counter) (h : c.value > 0) :
    counter_read (counter_dec (counter_inc c)) = counter_read c := by
  unfold counter_read counter_inc counter_dec
  rw [Nat.add_sub_cancel]

/-! ## Invariant: Accumulator Pattern -/

/-- `sumTo n = 0 + 1 + ... + n` using a tail-recursive helper. -/
def sumTo (n : Nat) : Nat :=
  go n 0
where
  go (k : Nat) (acc : Nat) : Nat :=
    match k with
    | 0 => acc
    | m + 1 => go m (acc + m + 1)

/-- The invariant `sumTo.go k acc = acc + sumTo k`. -/
theorem sumTo_go_inv (k acc : Nat) : sumTo.go k acc = acc + sumTo k := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    calc
      sumTo.go (Nat.succ k) acc = sumTo.go k (acc + k + 1) := rfl
      _ = (acc + k + 1) + sumTo k := by rw [ih]
      _ = acc + ((k+1) + sumTo k) := by omega
      _ = acc + sumTo (Nat.succ k) := by
        have h : sumTo (Nat.succ k) = (k+1) + sumTo k := by
          unfold sumTo
          simp [sumTo.go]
          rw [ih (k+1), ih 0]
          omega
        rw [h]

/-- Concrete check: `sumTo 5 = 15`. -/
theorem sumTo_5 : sumTo 5 = 15 := by
  native_decide
