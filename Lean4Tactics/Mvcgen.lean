/-
# Monadic Verification: `mvcgen`

`mvcgen` (monadic verification condition generator) proves properties of
imperative programs written with Lean's `do` notation.  It breaks a goal
involving a monadic program into smaller *verification conditions* (VCs)
that are sufficient to prove the original goal.

Requires `import Std.Tactic.Do` and `open Std.Do`.

The typical workflow:
1. `generalize h : prog arg = result` to name the result.
2. `apply Id.of_wp_run_eq h` to switch to weakest-precondition form.
3. `mvcgen` to break down into VCs (requires a loop invariant).
4. `invariants` to provide loop invariants, then `with grind` to close VCs.
-/

import Std.Tactic.Do
open Std.Do

/--
A simple imperative function: compute the sum of an array using a `for` loop.
`Id.run` lets us use `do` notation for pure computation.
-/
def arraySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

/--
Verify that `arraySum` equals `Array.sum`.  This demonstrates the full
`mvcgen` workflow: weakest-precondition transformation, VC generation,
loop invariant, and final automation.

The loop invariant states: at every iteration, `out` equals the sum of
the already-visited prefix of the list.
-/
theorem mvcgen_array_sum (l : Array Nat) : arraySum l = l.sum := by
  -- ⊢ `arraySum l = l.sum`
  -- Name the result of the function
  generalize h : arraySum l = x
  -- `x` is the result; we need `x = l.sum`
  -- Switch to weakest-precondition form for `Id`
  apply Id.of_wp_run_eq h
  -- Generate verification conditions
  mvcgen
  -- Provide the loop invariant: `out` = sum of the visited prefix
  invariants
  · ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  with grind

/--
A function with `Array.push` inside the loop.

`multiplyByTwo` doubles every element of an array.
-/
def multiplyByTwo (l : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  for x in l do
    out := out.push (2 * x)
  return out

/--
Verify that `multiplyByTwo` equals `Array.map (· * 2)`.
The loop invariant: `out` contains the doubled prefix.
-/
theorem mvcgen_multiply_by_two (l : Array Nat) : multiplyByTwo l = l.map (· * 2) := by
  -- ⊢ `multiplyByTwo l = l.map (· * 2)`
  generalize h : multiplyByTwo l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · ⇓⟨xs, out⟩ => ⌜out = (xs.prefix.map (· * 2)).toArray⌝
  with grind

/--
A simple function using only assignment (no loop).

`addOne` increments a value using the `State` monad (via `Id.run`).
This example shows that `mvcgen` also works for loop-free programs.
-/
def addOne (x : Nat) : Nat := Id.run do
  let mut v := x
  v := v + 1
  return v

/--
Proof that `addOne x = x + 1`.  No loop invariant is needed because there
is no loop — `mvcgen` generates no VCs and the goal closes immediately.
-/
theorem mvcgen_add_one (x : Nat) : addOne x = x + 1 := by
  -- ⊢ `addOne x = x + 1`
  generalize h : addOne x = r
  apply Id.of_wp_run_eq h
  mvcgen
