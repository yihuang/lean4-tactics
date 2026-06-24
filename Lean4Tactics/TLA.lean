/-
# TLA+‑Style State Transition Verification

Peterson's mutual exclusion algorithm for two threads, specified in TLA+.

## TLA+ specification

```tla
------------------------------ MODULE Peterson ------------------------------
CONSTANT Thread  ≜ {t0, t1}
VARIABLES pc, flag, turn, x

Init ≜ ∧ pc   = [t ∈ Thread ↦ "idle"]
        ∧ flag = [t ∈ Thread ↦ FALSE]
        ∧ turn = t0
        ∧ x    = 0

flip(t) ≜ IF t = t0 THEN t1 ELSE t0

EnterWait(t) ≜ ∧ pc[t]   = "idle"
                ∧ flag[t] = FALSE
                ∧ flag'   = [flag EXCEPT ![t] = TRUE]
                ∧ turn'   = flip(t)
                ∧ pc'     = [pc EXCEPT ![t] = "wait"]
                ∧ UNCHANGED ⟨x⟩

EnterCrit(t) ≜ ∧ pc[t]   = "wait"
                ∧ (flag[flip(t)] = FALSE ∨ turn = t)
                ∧ pc'     = [pc EXCEPT ![t] = "crit"]
                ∧ UNCHANGED ⟨flag, turn, x⟩

Exit(t) ≜ ∧ pc[t]   = "crit"
           ∧ flag'   = [flag EXCEPT ![t] = FALSE]
           ∧ pc'     = [pc EXCEPT ![t] = "idle"]
           ∧ x'      = x + 1
           ∧ UNCHANGED ⟨turn⟩

Next ≜ ∨ ∃ t ∈ Thread : EnterWait(t)
        ∨ ∃ t ∈ Thread : EnterCrit(t)
        ∨ ∃ t ∈ Thread : Exit(t)
        ∨ UNCHANGED ⟨pc, flag, turn, x⟩

=============================================================================
```

The **safety property** (`MutualExclusion`) is verified by inductive
invariant.  The **liveness property** (starvation freedom) is stated using
the LTL module and requires weak fairness of each `EnterCrit(t)` action.
-/

import Lean4Tactics.LTL
namespace TLA

inductive Tid : Type  | t0 | t1  deriving DecidableEq, Repr
open Tid
inductive Loc : Type  | idle | wait | crit  deriving DecidableEq, Repr
open Loc

structure State where
  loc  : Tid → Loc
  flag : Tid → Bool
  turn : Tid
  x    : Nat

@[ext] theorem State.ext {a b : State} (h1 : a.loc = b.loc) (h2 : a.flag = b.flag) (h3 : a.turn = b.turn) (h4 : a.x = b.x) : a = b := by
  cases a; cases b; simp at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

def flip (t : Tid) : Tid := match t with | t0 => t1 | t1 => t0
@[simp] theorem flip_t0 : flip t0 = t1 := rfl
@[simp] theorem flip_t1 : flip t1 = t0 := rfl

/-! ## Actions -/

def aEnterWait (t : Tid) : State → State → Prop := λ s s' =>
  s.loc t = idle ∧ s.flag t = false ∧
  s' = { loc  := λ t' => if t' = t then wait else s.loc t'
       , flag := λ t' => if t' = t then true  else s.flag t'
       , turn := flip t, x := s.x }

def aEnterCrit (t : Tid) : State → State → Prop := λ s s' =>
  s.loc t = wait ∧ (s.flag (flip t) = false ∨ s.turn = t) ∧
  s' = { loc := λ t' => if t' = t then crit else s.loc t'
       , flag := s.flag, turn := s.turn, x := s.x }

def aExit (t : Tid) : State → State → Prop := λ s s' =>
  s.loc t = crit ∧
  s' = { loc  := λ t' => if t' = t then idle else s.loc t'
       , flag := λ t' => if t' = t then false else s.flag t'
       , turn := s.turn, x := s.x + 1 }

def Next (s s' : State) : Prop :=
  aEnterWait t0 s s' ∨ aEnterWait t1 s s' ∨
  aEnterCrit t0 s s' ∨ aEnterCrit t1 s s' ∨
  aExit t0 s s' ∨ aExit t1 s s' ∨
  s = s'

/-! ## Invariant -/

def Inv (s : State) : Prop :=
  (∀ t, s.loc t = crit → s.flag t = true) ∧
  (∀ t, s.loc t = wait → s.flag t = true) ∧
  ¬(s.loc t0 = crit ∧ s.loc t1 = crit) ∧
  (s.loc t0 = crit ∧ s.loc t1 = wait → s.turn = t0) ∧
  (s.loc t1 = crit ∧ s.loc t0 = wait → s.turn = t1)

def MutualExclusion (s : State) : Prop := ¬(s.loc t0 = crit ∧ s.loc t1 = crit)
def init : State := { loc := λ _ => idle, flag := λ _ => false, turn := t0, x := 0 }

theorem inv_init : Inv init := by unfold Inv init; simp
theorem inv_implies_mutex (s : State) (h : Inv s) : MutualExclusion s := by
  rcases h with ⟨_, _, h3, _, _⟩; exact h3

/-! ## Invariant preservation -/

theorem inv_preserved_enterWait (t : Tid) (s s' : State) (hInv : Inv s) (hAct : aEnterWait t s s') : Inv s' := by
  rcases hInv with ⟨hCrit, hWait, hMutex, hD, hE⟩
  rcases hAct with ⟨hLoc, hFlag, hEq⟩; subst s'
  rcases t with (t0|t1)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t' h
      cases t' with
      | t0 => simp
      | t1 => simp; simp [hCrit t1 (by simpa using h)]
    · intro t' h
      cases t' with
      | t0 => simp
      | t1 => simp; simp [hWait t1 (by simpa using h)]
    · simp
    · intro h; simp at h
    · simp
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t' h
      cases t' with
      | t0 => simp; simp [hCrit t0 (by simpa using h)]
      | t1 => simp
    · intro t' h
      cases t' with
      | t0 => simp; simp [hWait t0 (by simpa using h)]
      | t1 => simp
    · simp
    · simp
    · intro h; simp at h
theorem inv_preserved_enterCrit (t : Tid) (s s' : State) (hInv : Inv s) (hAct : aEnterCrit t s s') : Inv s' := by
  rcases hInv with ⟨hCrit, hWait, hMutex, hD, hE⟩
  rcases hAct with ⟨hLoc, hGuard, hEq⟩; subst s'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; simp; exact hWait t hLoc
    · simp [h] at ht'; simp; exact hCrit t' ht'
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; simp at ht'
    · simp [h] at ht'; simp; exact hWait t' ht'
  · intro hBoth
    rcases hBoth with ⟨h0', h1'⟩
    by_cases h0t : t0 = t
    · subst h0t
      have h1 : s.loc t1 = crit := by simpa using h1'
      rcases hGuard with (hflag | hturn)
      · have hflag' : s.flag t1 = false := by simpa using hflag
        have : s.flag t1 = true := hCrit t1 h1; rw [hflag'] at this; simp at this
      · have : s.turn = t1 := hE ⟨h1, hLoc⟩; exact (by decide : t0 ≠ t1) (hturn.symm ▸ this)
    · by_cases h1t : t1 = t
      · subst h1t
        have h0 : s.loc t0 = crit := by simpa using h0'
        rcases hGuard with (hflag | hturn)
        · have hflag' : s.flag t0 = false := by simpa using hflag
          have : s.flag t0 = true := hCrit t0 h0; rw [hflag'] at this; simp at this
        · have : s.turn = t0 := hD ⟨h0, hLoc⟩; exact (by decide : t1 ≠ t0) (hturn.symm ▸ this)
      · have h0 : s.loc t0 = crit := by simpa [h0t] using h0'
        have h1 : s.loc t1 = crit := by simpa [h1t] using h1'
        exact hMutex ⟨h0, h1⟩
  · intro ⟨h0c, h1w⟩
    cases t with
    | t0 =>
      have flagT1 : s.flag t1 = true := hWait t1 (by simpa using h1w)
      rcases hGuard with (hflag | hturn)
      · have hflag' : s.flag t1 = false := by simpa using hflag
        have : s.flag t1 = true := flagT1; rw [hflag'] at this; simp at this
      · exact hturn
    | t1 =>
      have h0cs : s.loc t0 = crit := by simpa using h0c
      exact hD ⟨h0cs, hLoc⟩
  · intro ⟨h1c, h0w⟩
    cases t with
    | t0 =>
      have h1cs : s.loc t1 = crit := by simpa using h1c
      exact hE ⟨h1cs, hLoc⟩
    | t1 =>
      have flagT0 : s.flag t0 = true := hWait t0 (by simpa using h0w)
      rcases hGuard with (hflag | hturn)
      · have hflag' : s.flag t0 = false := by simpa using hflag
        have : s.flag t0 = true := flagT0; rw [hflag'] at this; simp at this
      · exact hturn

theorem inv_preserved_exit (t : Tid) (s s' : State) (hInv : Inv s) (hAct : aExit t s s') : Inv s' := by
  rcases hInv with ⟨hCrit, hWait, hMutex, hD, hE⟩
  rcases hAct with ⟨hLoc, hEq⟩; subst s'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; simp at ht'
    · simp [h] at ht'; simp [h]; exact hCrit t' ht'
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; simp at ht'
    · simp [h] at ht'; simp [h]; exact hWait t' ht'
  · intro hBoth
    rcases hBoth with ⟨h0', h1'⟩
    have h0 : s.loc t0 = crit := by
      by_cases h0t : t0 = t
      · subst h0t; exact hLoc
      · simpa [h0t] using h0'
    have h1 : s.loc t1 = crit := by
      by_cases h1t : t1 = t
      · subst h1t; exact hLoc
      · simpa [h1t] using h1'
    exact hMutex ⟨h0, h1⟩
  · intro ⟨h0c, h1w⟩
    have h0s : s.loc t0 = crit := by
      by_cases h0t : t0 = t
      · subst h0t; exact hLoc
      · simpa [h0t] using h0c
    have h1s : s.loc t1 = wait := by
      by_cases h1t : t1 = t
      · subst h1t; simp at h1w
      · simpa [h1t] using h1w
    exact hD ⟨h0s, h1s⟩
  · intro ⟨h1c, h0w⟩
    have h1s : s.loc t1 = crit := by
      by_cases h1t : t1 = t
      · subst h1t; exact hLoc
      · simpa [h1t] using h1c
    have h0s : s.loc t0 = wait := by
      by_cases h0t : t0 = t
      · subst h0t; simp at h0w
      · simpa [h0t] using h0w
    exact hE ⟨h1s, h0s⟩

theorem next_preserves_inv (s s' : State) (hInv : Inv s) (hNext : Next s s') : Inv s' := by
  rcases hNext with (h|h|h|h|h|h|h)
  · exact inv_preserved_enterWait t0 s s' hInv h
  · exact inv_preserved_enterWait t1 s s' hInv h
  · exact inv_preserved_enterCrit t0 s s' hInv h
  · exact inv_preserved_enterCrit t1 s s' hInv h
  · exact inv_preserved_exit t0 s s' hInv h
  · exact inv_preserved_exit t1 s s' hInv h
  · subst h; exact hInv

inductive Reachable : State → Prop
  | init : Reachable init
  | step (s s' : State) : Reachable s → Next s s' → Reachable s'

theorem all_reachable_inv (s : State) (h : Reachable s) : Inv s := by
  induction h with | init => exact inv_init | step _ _ hPrev hNext ih => exact next_preserves_inv _ _ ih hNext

theorem mutual_exclusion_holds (s : State) (h : Reachable s) : MutualExclusion s :=
  inv_implies_mutex s (all_reachable_inv s h)

/-! ## Trace -/

def s1 : State := { loc := fun | t0 => wait | t1 => idle, flag := fun | t0 => true | t1 => false, turn := t1, x := 0 }
def s2 : State := { loc := fun | t0 => wait | t1 => wait, flag := fun | t0 => true | t1 => true, turn := t0, x := 0 }
def s3 : State := { loc := fun | t0 => crit | t1 => wait, flag := fun | t0 => true | t1 => true, turn := t0, x := 0 }
def s4 : State := { loc := fun | t0 => idle | t1 => wait, flag := fun | t0 => false | t1 => true, turn := t0, x := 1 }
def s5 : State := { loc := fun | t0 => idle | t1 => crit, flag := fun | t0 => false | t1 => true, turn := t0, x := 1 }
def s6 : State := { loc := fun | t0 => idle | t1 => idle, flag := fun | t0 => false | t1 => false, turn := t0, x := 2 }

theorem init_to_s1 : Next init s1 := by
  refine Or.inl ?_; unfold aEnterWait; refine ⟨by decide, by decide, ?_⟩
  apply State.ext
  · ext x; cases x <;> simp [s1, init]
  · ext x; cases x <;> simp [s1, init]
  · simp [s1]
  · simp [s1, init]

theorem s1_to_s2 : Next s1 s2 := by
  refine Or.inr (Or.inl ?_); unfold aEnterWait; refine ⟨by decide, by decide, ?_⟩
  apply State.ext
  · ext x; cases x <;> simp [s1, s2]
  · ext x; cases x <;> simp [s1, s2]
  · simp [s2]
  · simp [s1, s2]

theorem s2_to_s3 : Next s2 s3 := by
  refine Or.inr (Or.inr (Or.inl ?_)); unfold aEnterCrit; refine ⟨by decide, Or.inr ?_, ?_⟩
  · simp [s2]
  · apply State.ext
    · ext x; cases x <;> simp [s2, s3]
    · simp [s2, s3]
    · simp [s2, s3]
    · simp [s2, s3]

theorem s3_to_s4 : Next s3 s4 := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); unfold aExit; refine ⟨by decide, ?_⟩
  apply State.ext
  · ext x; cases x <;> simp [s3, s4]
  · ext x; cases x <;> simp [s3, s4]
  · simp [s3, s4]
  · simp [s3, s4]

theorem s4_to_s5 : Next s4 s5 := by
  refine Or.inr (Or.inr (Or.inr (Or.inl ?_))); unfold aEnterCrit; refine ⟨by decide, Or.inl ?_, ?_⟩
  · simp [s4]
  · apply State.ext
    · ext x; cases x <;> simp [s4, s5]
    · simp [s4, s5]
    · simp [s4, s5]
    · simp [s4, s5]

theorem s5_to_s6 : Next s5 s6 := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))); unfold aExit; refine ⟨by decide, ?_⟩
  apply State.ext
  · ext x; cases x <;> simp [s5, s6]
  · ext x; cases x <;> simp [s5, s6]
  · simp [s5, s6]
  · simp [s5, s6]

open Reachable
theorem trace_complete : Reachable s6 :=
  step s5 s6 (step s4 s5 (step s3 s4 (step s2 s3 (step s1 s2 (step init s1 Reachable.init init_to_s1) s1_to_s2) s2_to_s3) s3_to_s4) s4_to_s5) s5_to_s6

theorem trace_mutex : MutualExclusion s6 := mutual_exclusion_holds s6 trace_complete

/-! ## Liveness demo (uses LTL) -/

open LTL

def waiting (t : Tid) (s : State) : Prop := s.loc t = Loc.wait
def inCrit (t : Tid) (s : State) : Prop := s.loc t = Loc.crit
def starvationFree (t : Tid) (σ : LTL.Trace State) : Prop :=
  always σ (λ s => waiting t s → eventually σ (inCrit t))
def rank (t : Tid) (s : State) : Nat × Nat × Nat :=
  (if s.turn = t then 0 else 1,
   match s.loc t with | Loc.crit => 0 | Loc.wait => 1 | Loc.idle => 2,
   match s.loc (flip t) with | Loc.crit => 0 | Loc.wait => 1 | Loc.idle => 2)

theorem starvation_free (t : Tid) (σ : LTL.Trace State)
    (hValid : isValid Next σ) (hWF : WF (aEnterCrit t) σ) : starvationFree t σ := by
  sorry

def σ_demo (n : Nat) : State := match n with
  | 0 => init | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | 5 => s5 | 6 => s6 | _ => s6

theorem σ_demo_large (n : Nat) (hn : 6 ≤ n) : σ_demo n = s6 := by
  unfold σ_demo; match n with | 0|1|2|3|4|5 => omega | 6 => rfl | n+7 => rfl

theorem trace_valid : isValid Next σ_demo := by
  unfold isValid; intro n
  by_cases h : n < 6
  · match n with
    | 0 => simpa [σ_demo] using init_to_s1
    | 1 => simpa [σ_demo] using s1_to_s2
    | 2 => simpa [σ_demo] using s2_to_s3
    | 3 => simpa [σ_demo] using s3_to_s4
    | 4 => simpa [σ_demo] using s4_to_s5
    | 5 => simpa [σ_demo] using s5_to_s6
  · have hn : 6 ≤ n := by omega
    have h_eq1 : σ_demo n = s6 := σ_demo_large n hn
    have h_eq2 : σ_demo (n + 1) = s6 := σ_demo_large (n + 1) (by omega)
    have h_next : Next s6 s6 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rfl))))))
    simpa [h_eq1, h_eq2]

theorem t0_waits_then_enters : starvationFree (Tid.t0) σ_demo := by
  unfold starvationFree always; intro n hwait; unfold waiting at hwait
  by_cases h : n < 3
  · match n with
    | 0 => simp [init, σ_demo] at hwait
    | 1 => unfold eventually inCrit; refine ⟨3, ?_⟩; simp [σ_demo, s3]
    | 2 => unfold eventually inCrit; refine ⟨3, ?_⟩; simp [σ_demo, s3]
  · have h_ge : 3 ≤ n := by omega
    have h_not_waiting : ∀ m, 3 ≤ m → (σ_demo m).loc (Tid.t0) ≠ Loc.wait := by
      intro m hm; have h_cases : m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ 7 ≤ m := by omega
      rcases h_cases with (hm3|hm4|hm5|hm6|hm7)
      · subst hm3; simp [σ_demo, s3]
      · subst hm4; simp [σ_demo, s4]
      · subst hm5; simp [σ_demo, s5]
      · subst hm6; simp [σ_demo, s6]
      · have : σ_demo m = s6 := σ_demo_large m (by omega); simp [this, s6]
    exfalso; exact h_not_waiting n h_ge hwait

end TLA
