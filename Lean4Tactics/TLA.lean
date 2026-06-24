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
  (∀ t, s.flag t = true → (s.loc t = wait ∨ s.loc t = crit)) ∧
  ¬(s.loc t0 = crit ∧ s.loc t1 = crit) ∧
  (s.loc t0 = crit ∧ s.loc t1 = wait → s.turn = t0) ∧
  (s.loc t1 = crit ∧ s.loc t0 = wait → s.turn = t1)

def MutualExclusion (s : State) : Prop := ¬(s.loc t0 = crit ∧ s.loc t1 = crit)
def init : State := { loc := λ _ => idle, flag := λ _ => false, turn := t0, x := 0 }
theorem inv_init : Inv init := by unfold Inv init; simp

theorem inv_implies_mutex (s : State) (h : Inv s) : MutualExclusion s := by
  rcases h with ⟨_, _, _, h4, _, _⟩; exact h4

/-! ## Invariant preservation -/

theorem inv_preserved_enterWait (t : Tid) (s s' : State) (hInv : Inv s) (hAct : aEnterWait t s s') : Inv s' := by
  rcases hInv with ⟨hCrit, hWait, hFlagLoc, hMutex, hD, hE⟩
  rcases hAct with ⟨hLoc, hFlag, hEq⟩; subst s'
  rcases t with (t0|t1)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t' h
      cases t' with
      | t0 => simp
      | t1 => simp; simp [hCrit t1 (by simpa using h)]
    · intro t' h
      cases t' with
      | t0 => simp
      | t1 => simp; simp [hWait t1 (by simpa using h)]
    · intro t' hflag
      cases t' with
      | t0 => simp
      | t1 =>
        simp at hflag
        have hloct1 := hFlagLoc t1 hflag
        rcases hloct1 with (h | h)
        · simp; left; exact h
        · simp; right; exact h
    · simp
    · intro h; simp at h
    · simp
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t' h
      cases t' with
      | t0 => simp; simp [hCrit t0 (by simpa using h)]
      | t1 => simp
    · intro t' h
      cases t' with
      | t0 => simp; simp [hWait t0 (by simpa using h)]
      | t1 => simp
    · intro t' hflag
      cases t' with
      | t0 =>
        simp at hflag
        have hloct0 := hFlagLoc t0 hflag
        rcases hloct0 with (h | h)
        · simp; left; exact h
        · simp; right; exact h
      | t1 => simp
    · simp
    · simp
    · intro h; simp at h
theorem inv_preserved_enterCrit (t : Tid) (s s' : State) (hInv : Inv s) (hAct : aEnterCrit t s s') : Inv s' := by
  rcases hInv with ⟨hCrit, hWait, hFlagLoc, hMutex, hD, hE⟩
  rcases hAct with ⟨hLoc, hGuard, hEq⟩; subst s'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; simp; exact hWait t hLoc
    · simp [h] at ht'; simp; exact hCrit t' ht'
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; simp at ht'
    · simp [h] at ht'; simp; exact hWait t' ht'
  · intro t' hflag
    by_cases h : t' = t
    · subst h; simp
    · have hloc' := hFlagLoc t' hflag
      rcases hloc' with (h' | h')
      · simp [h]; left; exact h'
      · simp [h]; right; exact h'
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
  rcases hInv with ⟨hCrit, hWait, hFlagLoc, hMutex, hD, hE⟩
  rcases hAct with ⟨hLoc, hEq⟩; subst s'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; simp at ht'
    · simp [h] at ht'; simp [h]; exact hCrit t' ht'
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; simp at ht'
    · simp [h] at ht'; simp [h]; exact hWait t' ht'
  · intro t' hflag
    by_cases h : t' = t
    · subst h; simp at hflag
    · simp [h] at hflag; have hloc' := hFlagLoc t' hflag
      rcases hloc' with (h' | h')
      · simp [h]; left; exact h'
      · simp [h]; right; exact h'
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
  refine Or.inl ?_
  unfold aEnterWait; refine ⟨by decide, by decide, ?_⟩
  apply State.ext
  · ext x; cases x <;> simp [s1, init]
  · ext x; cases x <;> simp [s1, init]
  · simp [s1]
  · simp [s1, init]

theorem s1_to_s2 : Next s1 s2 := by
  refine Or.inr (Or.inl ?_)
  unfold aEnterWait; refine ⟨by decide, by decide, ?_⟩
  apply State.ext
  · ext x; cases x <;> simp [s1, s2]
  · ext x; cases x <;> simp [s1, s2]
  · simp [s2]
  · simp [s1, s2]

theorem s2_to_s3 : Next s2 s3 := by
  refine Or.inr (Or.inr (Or.inl ?_))
  unfold aEnterCrit; refine ⟨by decide, Or.inr ?_, ?_⟩
  · simp [s2]
  · apply State.ext
    · ext x; cases x <;> simp [s2, s3]
    · simp [s2, s3]
    · simp [s2, s3]
    · simp [s2, s3]

theorem s3_to_s4 : Next s3 s4 := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
  unfold aExit; refine ⟨by decide, ?_⟩
  apply State.ext
  · ext x; cases x <;> simp [s3, s4]
  · ext x; cases x <;> simp [s3, s4]
  · simp [s3, s4]
  · simp [s3, s4]

theorem s4_to_s5 : Next s4 s5 := by
  refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
  unfold aEnterCrit; refine ⟨by decide, Or.inl ?_, ?_⟩
  · simp [s4]
  · apply State.ext
    · ext x; cases x <;> simp [s4, s5]
    · simp [s4, s5]
    · simp [s4, s5]
    · simp [s4, s5]

theorem s5_to_s6 : Next s5 s6 := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
  unfold aExit; refine ⟨by decide, ?_⟩
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

/-! ## Starvation freedom -/

theorem not_enabled_enterCrit_imp (t : Tid) (s : State) (h : s.loc t = wait) (hne : ¬ enabled (aEnterCrit t) s) :
    s.flag (flip t) = true ∧ s.turn = flip t := by
  have h_not_guard : ¬ (s.flag (flip t) = false ∨ s.turn = t) := by
    intro h_guard
    apply hne
    unfold enabled aEnterCrit
    refine ⟨{ loc := λ t' => if t' = t then crit else s.loc t'
            , flag := s.flag, turn := s.turn, x := s.x }, h, h_guard, ?_⟩
    rfl
  rcases not_or.mp h_not_guard with ⟨hflag_ne_false, hturn_ne_t⟩
  have hflag_true : s.flag (flip t) = true := by
    have h_cases : s.flag (flip t) = false ∨ s.flag (flip t) = true := by
      cases s.flag (flip t) <;> simp
    rcases h_cases with (h | h)
    · exact (hflag_ne_false h).elim
    · exact h
  have hturn_flip : s.turn = flip t := by
    have h_cases : s.turn = t ∨ s.turn = flip t := by
      cases s.turn <;> cases t <;> simp
    rcases h_cases with (h | h)
    · exact (hturn_ne_t h).elim
    · exact h
  exact ⟨hflag_true, hturn_flip⟩

theorem next_loc_t_stays_wait (t : Tid) (s s' : State) (h : Next s s') (hloc : s.loc t = wait)
    (h_not_enter : ¬ aEnterCrit t s s') : s'.loc t = wait := by
  rcases h with (h|h|h|h|h|h|h)
  · rcases h with ⟨hLoc, hFlag, hEq⟩
    subst hEq; simp
    by_cases h' : t = t0
    · subst h'; simp
    · simp [h', hloc]
  · rcases h with ⟨hLoc, hFlag, hEq⟩
    subst hEq; simp
    by_cases h' : t = t1
    · subst h'; simp
    · simp [h', hloc]
  · rcases h with ⟨hLoc, hGuard, hEq⟩
    subst hEq; simp
    by_cases h' : t = t0
    · subst h'; exfalso; exact h_not_enter ⟨hLoc, hGuard, rfl⟩
    · simp [h']; exact hloc
  · rcases h with ⟨hLoc, hGuard, hEq⟩
    subst hEq; simp
    by_cases h' : t = t1
    · subst h'; exfalso; exact h_not_enter ⟨hLoc, hGuard, rfl⟩
    · simp [h']; exact hloc
  · rcases h with ⟨hLoc, hEq⟩
    subst hEq; simp
    by_cases h' : t = t0
    · subst h'; exfalso; exact (by decide : wait ≠ crit) (hloc.symm ▸ hLoc)
    · simp [h']; exact hloc
  · rcases h with ⟨hLoc, hEq⟩
    subst hEq; simp
    by_cases h' : t = t1
    · subst h'; exfalso; exact (by decide : wait ≠ crit) (hloc.symm ▸ hLoc)
    · simp [h']; exact hloc
  · subst h; exact hloc

/-!
Starvation freedom for Peterson's algorithm under weak fairness of both
threads' enter-critical-section actions and the other thread's exit action.

Proof structure:
1. If t is waiting and never enters crit, then `aEnterCrit t` is never taken
   and therefore (by WF) is only finitely often enabled.
2. Beyond the last enabling point, `flag(flip t) = true` and `turn = flip t`
   forever (otherwise `aEnterCrit t` would be enabled).
3. By the invariant, `loc(flip t)` is either `wait` or `crit`.
4. The other thread cannot stay in `wait`: `aEnterCrit(flip t)` is enabled
   there (`turn = flip t`), and by its WF must be taken, moving it to `crit`.
5. The other thread cannot stay in `crit`: `aExit(flip t)` is enabled, and by
   its WF must be taken, setting `flag(flip t) = false`.
6. Here `aEnterCrit t` is enabled (`flag(flip t) = false`), and by its WF must
   be taken — contradicting the "never enters crit" assumption.
-/
theorem starvation_free (t : Tid) (σ : LTL.Trace State)
    (hValid : isValid Next σ) (hWF : WF (aEnterCrit t) σ)
    (hWF_other_enter : WF (aEnterCrit (flip t)) σ)
    (hWF_other_exit : WF (aExit (flip t)) σ)
    (hInitInv : Inv (σ 0)) : starvationFree t σ := by
  have hInv_all : ∀ n, Inv (σ n) := by
    intro n; induction n with
    | zero => exact hInitInv
    | succ k ih => exact next_preserves_inv _ _ ih (hValid k)
  unfold starvationFree always
  intro n hwait
  unfold waiting at hwait
  have hloc_wait : (σ n).loc t = wait := hwait
  by_cases h_enters : eventually σ (inCrit t)
  · exact h_enters
  · -- t never enters the critical section; derive contradiction
    have h_never_crit : ∀ m, (σ m).loc t ≠ crit := by
      intro m hm; apply h_enters; exact ⟨m, hm⟩
    have h_never_taken : ∀ m ≥ n, ¬ takenAt (aEnterCrit t) σ m := by
      intro m hm htaken
      rcases htaken with ⟨hLoc, hGuard, hEq⟩
      have hcrit : (σ (m+1)).loc t = crit := by
        simp [hEq]
      exact h_never_crit (m+1) hcrit
    have h_not_inf_enabled : ¬ infOftenEnabled (aEnterCrit t) σ := by
      intro h_inf
      have h_inf_taken : infOftenTaken (aEnterCrit t) σ := hWF h_inf
      rcases h_inf_taken n with ⟨m, hm, h_taken⟩
      exact h_never_taken m hm h_taken
    have h_exists_N : ∃ N, ∀ m ≥ N, ¬ enabled (aEnterCrit t) (σ m) := by
      rw [infOftenEnabled] at h_not_inf_enabled
      by_cases h : ∃ N, ∀ m ≥ N, ¬ enabled (aEnterCrit t) (σ m)
      · exact h
      · exfalso
        apply h_not_inf_enabled
        intro n
        by_cases h_ex : ∃ m, m ≥ n ∧ enabled (aEnterCrit t) (σ m)
        · exact h_ex
        · exfalso
          apply h
          refine ⟨n, λ m hm hm_en => h_ex ?_⟩
          exact ⟨m, hm, hm_en⟩
    rcases h_exists_N with ⟨N, hN⟩
    let M := max n N
    have hM_ge_n : M ≥ n := Nat.le_max_left _ _
    have hM_range : ∀ m ≥ M, ¬ enabled (aEnterCrit t) (σ m) := by
      intro m hm; apply hN m; exact Nat.le_trans (Nat.le_max_right _ _) hm
    have h_always_wait : ∀ m, n ≤ m → (σ m).loc t = wait := by
      intro m hm
      induction hm with
      | refl => exact hloc_wait
      | step h ih =>
        rename_i k
        have hstep : Next (σ k) (σ (k+1)) := hValid k
        have h_not_enter : ¬ aEnterCrit t (σ k) (σ (k+1)) := by
          intro h_enter
          apply h_never_taken k h
          exact h_enter
        exact next_loc_t_stays_wait t (σ k) (σ (k+1)) hstep ih h_not_enter
    have h_flag_turn : ∀ m ≥ M, (σ m).flag (flip t) = true ∧ (σ m).turn = flip t := by
      intro m hm
      have h_wait : (σ m).loc t = wait := h_always_wait m (Nat.le_trans hM_ge_n hm)
      have h_disabled : ¬ enabled (aEnterCrit t) (σ m) := hM_range m hm
      exact not_enabled_enterCrit_imp t (σ m) h_wait h_disabled
    have h_flag : ∀ m ≥ M, (σ m).flag (flip t) = true :=
      λ m hm => (h_flag_turn m hm).1
    have h_turn : ∀ m ≥ M, (σ m).turn = flip t :=
      λ m hm => (h_flag_turn m hm).2
    have h_loc_other : ∀ m ≥ M, (σ m).loc (flip t) = wait ∨ (σ m).loc (flip t) = crit := by
      intro m hm
      rcases hInv_all m with ⟨_, _, hFlagLoc, _, _, _⟩
      have hflag : (σ m).flag (flip t) = true := h_flag m hm
      exact hFlagLoc (flip t) hflag
    -- Case analysis on flip t's location
    by_cases h_crit_ever : ∃ m ≥ M, (σ m).loc (flip t) = crit
    · rcases h_crit_ever with ⟨m0, hm0, h_crit⟩
      have h_wait_m0 : (σ m0).loc t = wait := h_always_wait m0 (Nat.le_trans hM_ge_n hm0)
      -- flip t is in crit at m0; aExit(flip t) is enabled there
      have h_exit_enabled_m0 : enabled (aExit (flip t)) (σ m0) := by
        unfold enabled aExit
        refine ⟨{ loc := λ t' => if t' = flip t then idle else (σ m0).loc t'
                , flag := λ t' => if t' = flip t then false else (σ m0).flag t'
                , turn := (σ m0).turn, x := (σ m0).x + 1 }, h_crit, ?_⟩
        rfl
      -- Lemma: if flip t is in crit at σ(k) and aExit(flip t) is NOT taken at step k, then it stays in crit at σ(k+1)
      have crit_persists_lemma : ∀ (s s' : State), Next s s' → s.loc (flip t) = crit → ¬ aExit (flip t) s s' → s'.loc (flip t) = crit := by
        intro s s' hNext hCrit hNotExit
        rcases hNext with (h|h|h|h|h|h|h)
        · rcases h with ⟨hLoc, hFlag, hEq⟩; subst hEq; simp
          by_cases h' : flip t = t0
          · rw [h'] at hCrit; rw [hLoc] at hCrit; simp at hCrit
          · simp [h', hCrit]
        · rcases h with ⟨hLoc, hFlag, hEq⟩; subst hEq; simp
          by_cases h' : flip t = t1
          · rw [h'] at hCrit; rw [hLoc] at hCrit; simp at hCrit
          · simp [h', hCrit]
        · rcases h with ⟨hLoc, hGuard, hEq⟩; subst hEq; simp
          by_cases h' : flip t = t0
          · rw [h']; simp
          · simp [h']; exact hCrit
        · rcases h with ⟨hLoc, hGuard, hEq⟩; subst hEq; simp
          by_cases h' : flip t = t1
          · rw [h']; simp
          · simp [h']; exact hCrit
        · rcases h with ⟨hLoc, hEq⟩; subst hEq; simp
          by_cases h' : flip t = t0
          · rw [h'] at hNotExit; unfold aExit at hNotExit; simp at hNotExit
            exfalso; exact hNotExit hLoc
          · simp [h']; exact hCrit
        · rcases h with ⟨hLoc, hEq⟩; subst hEq; simp
          by_cases h' : flip t = t1
          · rw [h'] at hNotExit; unfold aExit at hNotExit; simp at hNotExit
            exfalso; exact hNotExit hLoc
          · simp [h']; exact hCrit
        · subst h; exact hCrit
      -- If aExit(flip t) is never taken from m0 onward, then (σ k).loc (flip t) = crit for all k ≥ m0
      by_cases h_exit_never : ∀ j ≥ m0, ¬ takenAt (aExit (flip t)) σ j
      · have h_all_crit : ∀ k ≥ m0, (σ k).loc (flip t) = crit := by
          intro k hk
          induction hk with
          | refl => exact h_crit
          | step hj ih =>
            rename_i j
            have hstep : Next (σ j) (σ (j+1)) := hValid j
            have hcrit_j : (σ j).loc (flip t) = crit := ih
            have h_not_exit_j : ¬ aExit (flip t) (σ j) (σ (j+1)) := h_exit_never j hj
            exact crit_persists_lemma (σ j) (σ (j+1)) hstep hcrit_j h_not_exit_j
        -- So aExit(flip t) is enabled at all k ≥ m0 (since loc = crit)
        have h_enabled_all : ∀ k ≥ m0, enabled (aExit (flip t)) (σ k) := by
          intro k hk
          have hcrit_k : (σ k).loc (flip t) = crit := h_all_crit k hk
          unfold enabled aExit
          refine ⟨{ loc := λ t' => if t' = flip t then idle else (σ k).loc t'
                  , flag := λ t' => if t' = flip t then false else (σ k).flag t'
                  , turn := (σ k).turn, x := (σ k).x + 1 }, hcrit_k, ?_⟩
          rfl
        have h_inf_enabled_exit : infOftenEnabled (aExit (flip t)) σ := by
          intro p
          let k := max p m0
          have hk_ge_m0 : k ≥ m0 := Nat.le_max_right _ _
          refine ⟨k, Nat.le_max_left _ _, h_enabled_all k hk_ge_m0⟩
        have h_inf_taken_exit : infOftenTaken (aExit (flip t)) σ := hWF_other_exit h_inf_enabled_exit
        rcases h_inf_taken_exit m0 with ⟨k, hk, h_taken⟩
        exfalso; exact h_exit_never k hk h_taken
      · -- aExit(flip t) IS taken at some step k ≥ m0
        have h_exit_exists : ∃ j ≥ m0, takenAt (aExit (flip t)) σ j := by
          by_cases h_ex : ∃ j ≥ m0, takenAt (aExit (flip t)) σ j
          · exact h_ex
          · exfalso
            apply h_exit_never
            intro j hj
            by_cases h_taken : takenAt (aExit (flip t)) σ j
            · exfalso; exact h_ex ⟨j, hj, h_taken⟩
            · exact h_taken
        rcases h_exit_exists with ⟨k, hk, h_taken_k⟩
        rcases h_taken_k with ⟨hLoc_exit, hEq_exit⟩
        -- After the exit, flag(flip t) = false, so aEnterCrit t becomes enabled
        have h_flag_other_false : (σ (k+1)).flag (flip t) = false := by
          simp [hEq_exit]
        have h_wait_after : (σ (k+1)).loc t = wait :=
          h_always_wait (k+1) (Nat.le_trans (Nat.le_trans hM_ge_n hm0) (Nat.le_trans hk (by omega)))
        have h_enter_enabled : enabled (aEnterCrit t) (σ (k+1)) := by
          unfold enabled aEnterCrit
          refine ⟨{ loc := λ t' => if t' = t then crit else (σ (k+1)).loc t'
                  , flag := (σ (k+1)).flag, turn := (σ (k+1)).turn, x := (σ (k+1)).x },
                  h_wait_after, Or.inl h_flag_other_false, ?_⟩
          rfl
        -- But k+1 ≥ M, contradicting hM_range
        have hk1_ge_M : k+1 ≥ M := Nat.le_trans (Nat.le_trans hm0 hk) (by omega)
        exfalso; exact hM_range (k+1) hk1_ge_M h_enter_enabled
    · -- flip t is never in crit after M; so always in wait
      have h_all_wait : ∀ m ≥ M, (σ m).loc (flip t) = wait := by
        intro m hm
        rcases h_loc_other m hm with (h | h)
        · exact h
        · exfalso; exact h_crit_ever ⟨m, hm, h⟩
      -- aEnterCrit(flip t) is always enabled (loc = wait, turn = flip t)
      have h_enter_other_enabled : ∀ m ≥ M, enabled (aEnterCrit (flip t)) (σ m) := by
        intro m hm
        have h_wait_other : (σ m).loc (flip t) = wait := h_all_wait m hm
        have h_turn_flip : (σ m).turn = flip t := h_turn m hm
        unfold enabled aEnterCrit
        refine ⟨{ loc := λ t' => if t' = flip t then crit else (σ m).loc t'
                , flag := (σ m).flag, turn := (σ m).turn, x := (σ m).x },
                h_wait_other, Or.inr h_turn_flip, ?_⟩
        rfl
      have h_inf_enabled_other : infOftenEnabled (aEnterCrit (flip t)) σ := by
        intro p
        let k := max p M
        have hk_ge_M : k ≥ M := Nat.le_max_right _ _
        refine ⟨k, Nat.le_max_left _ _, h_enter_other_enabled k hk_ge_M⟩
      have h_inf_taken_other : infOftenTaken (aEnterCrit (flip t)) σ := hWF_other_enter h_inf_enabled_other
      rcases h_inf_taken_other M with ⟨k, hk, h_taken_other⟩
      rcases h_taken_other with ⟨hLocOther, hGuardOther, hEqOther⟩
      -- flip t just entered crit; contradiction via h_crit_ever
      have h_crit_after : (σ (k+1)).loc (flip t) = crit := by
        simp [hEqOther]
      have hk1_ge_M : k+1 ≥ M := Nat.le_trans hk (by omega)
      exfalso; exact h_crit_ever ⟨k+1, hk1_ge_M, h_crit_after⟩


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
      intro m hm
      have h_cases : m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ 7 ≤ m := by omega
      rcases h_cases with (hm3|hm4|hm5|hm6|hm7)
      · subst hm3; simp [σ_demo, s3]
      · subst hm4; simp [σ_demo, s4]
      · subst hm5; simp [σ_demo, s5]
      · subst hm6; simp [σ_demo, s6]
      · have : σ_demo m = s6 := σ_demo_large m (by omega); simp [this, s6]
    exfalso; exact h_not_waiting n h_ge hwait

end TLA
