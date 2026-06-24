/-
# TLA+‑Style State Transition Verification

A formal specification and verification of Peterson's mutual exclusion
algorithm for two threads, modeled in TLA+ style.

**Key concepts:**

- **State** as an algebraic data type with named variables
- **Init** predicate defining legal starting states
- **Actions** as binary state relations (one per atomic step)
- **Next** relation as the disjunction of all actions
  (cf. TLA+'s `Next == ∨ action₁ ∨ action₂ ∨ … ∨ UNCHANGED vars`)
- **Stuttering** steps that leave the state unchanged
- **Inductive invariant** — a predicate over states that
  1. holds in `init`
  2. is preserved by every action
- **Safety property** (`MutualExclusion`) derived from the invariant,
  proving the system is race‑condition free under arbitrary interleaving
- **Proof by invariant preservation** — the standard TLA+ verification technique
-/

set_option linter.unusedVariables false

namespace TLA

/-!
## Thread and Location Types
-/

/-- Two thread identifiers. -/
inductive Tid : Type
  | t0 | t1
  deriving DecidableEq, Repr

open Tid

/-- Per‑thread program location in Peterson's protocol.

    `idle` — not trying to enter the critical section (flag = false)
    `wait` — trying but waiting in the Peterson loop (flag = true, turn set to other)
    `crit` — inside the critical section (flag = true)
-/
inductive Loc : Type
  | idle | wait | crit
  deriving DecidableEq, Repr

open Loc

/-!
## System State

Each state captures the program counter of both threads, the shared
`flag` and `turn` variables of Peterson's algorithm, and a shared
counter `x` that threads increment inside the critical section.
-/

structure State where
  loc  : Tid → Loc
  flag : Tid → Bool
  turn : Tid
  x    : Nat

/-- The initial state: both threads idle, no flags raised, counter at 0. -/
def init : State :=
  { loc  := λ _ => idle
  , flag := λ _ => false
  , turn := t0
  , x    := 0
  }

/-- The other thread (`flip` is an involution). -/
def flip (t : Tid) : Tid :=
  match t with | t0 => t1 | t1 => t0

@[simp] theorem flip_t0 : flip t0 = t1 := rfl
@[simp] theorem flip_t1 : flip t1 = t0 := rfl

@[simp] theorem flip_inv (t : Tid) : flip (flip t) = t := by
  cases t <;> rfl

@[simp] theorem t0_ne_t1 : t0 ≠ t1 := by decide
@[simp] theorem t1_ne_t0 : t1 ≠ t0 := by decide

/-!
## Actions

Each action is a binary relation `State → State → Prop`.  They model one
atomic step of Peterson's protocol under arbitrary interleaving.
-/

/-- Peterson step 1: thread `t` raises its flag and defers to the other thread.

    flag[t] := true
    turn    := other
    loc[t]  := wait          (idle → wait)
-/
def actEnterWait (t : Tid) (s s' : State) : Prop :=
  s.loc t = idle ∧ s.flag t = false ∧
  s'.flag t = true ∧ s'.turn = flip t ∧
  s'.loc t = wait ∧
  s'.loc (flip t) = s.loc (flip t) ∧
  s'.flag (flip t) = s.flag (flip t) ∧
  s'.x = s.x

/-- Thread `t` enters the critical section.

    guard: flag[other] = false ∨ turn = t
    loc[t] := crit           (wait → crit)
-/
def actEnterCrit (t : Tid) (s s' : State) : Prop :=
  s.loc t = wait ∧ (s.flag (flip t) = false ∨ s.turn = t) ∧
  s'.loc t = crit ∧
  s'.loc (flip t) = s.loc (flip t) ∧
  s'.flag = s.flag ∧ s'.turn = s.turn ∧
  s'.x = s.x

/-- Thread `t` leaves the critical section, resetting its flag and incrementing `x`.

    flag[t] := false
    loc[t]  := idle           (crit → idle)
    x       := x + 1
-/
def actExit (t : Tid) (s s' : State) : Prop :=
  s.loc t = crit ∧
  s'.loc t = idle ∧ s'.flag t = false ∧
  s'.loc (flip t) = s.loc (flip t) ∧
  s'.flag (flip t) = s.flag (flip t) ∧
  s'.turn = s.turn ∧
  s'.x = s.x + 1

/-- TLA+ stuttering step: the state does not change. -/
def actStutter (s s' : State) : Prop :=
  s = s'

/-- The **Next** relation: disjunction of all atomic actions plus stuttering.

    Cf. `Next == ∨ actEnterWait(self) ∨ actEnterCrit(self) ∨ actExit(self) ∨ UNCHANGED vars`
    In Lean, `∨` is right‑associative: `A ∨ B ∨ C ∨ D = A ∨ (B ∨ (C ∨ D))`.
-/
def Next (s s' : State) : Prop :=
  (∃ t, actEnterWait t s s') ∨
  (∃ t, actEnterCrit t s s') ∨
  (∃ t, actExit t s s') ∨
  actStutter s s'

/-!
## Inductive Invariant

The invariant captures all properties that must hold in every reachable state.
It is designed to be **preserved by every action** — the core TLA+ proof
technique.

    Inv(s) ≜
      ∧ ∀ t, loc[t] = crit → flag[t]
      ∧ ∀ t, loc[t] = wait  → flag[t]
      ∧ ¬(loc[t0] = crit  ∧  loc[t1] = crit)
      ∧ (loc[t0] = crit   ∧  loc[t1] = wait → turn = t0)
      ∧ (loc[t1] = crit   ∧  loc[t0] = wait → turn = t1)
-/

def Inv (s : State) : Prop :=
  (∀ t, s.loc t = crit → s.flag t = true) ∧
  (∀ t, s.loc t = wait → s.flag t = true) ∧
  ¬(s.loc t0 = crit ∧ s.loc t1 = crit) ∧
  (s.loc t0 = crit ∧ s.loc t1 = wait → s.turn = t0) ∧
  (s.loc t1 = crit ∧ s.loc t0 = wait → s.turn = t1)

/-!
## Safety Property

Mutual exclusion: no two threads are ever simultaneously in the critical
section.  This is the race‑condition freedom we set out to prove.
-/

def MutualExclusion (s : State) : Prop :=
  ¬(s.loc t0 = crit ∧ s.loc t1 = crit)

/-- The invariant implies mutual exclusion (immediate from clause 3 of `Inv`). -/
theorem inv_implies_mutex (s : State) (h : Inv s) : MutualExclusion s := by
  rcases h with ⟨_, _, h3, _, _⟩
  exact h3

/-!
## Proof: `Inv` holds in `init`
-/

theorem inv_init : Inv init := by
  unfold Inv init
  simp

/-!
## Helper: when `t' ≠ t` in a two‑element type, `t' = flip t`.
-/
theorem ne_implies_flip {t' t : Tid} (h : t' ≠ t) : t' = flip t := by
  cases t <;> cases t' <;> simp at h <;> simp

/-!
## Proof: every action preserves `Inv`

We prove one lemma per action, then combine them into `next_preserves_inv`.
-/

/-! ### `actEnterWait` preserves `Inv`

Only thread `t` changes (idle → wait, flag becomes true, turn set to `flip t`).
Everything about the other thread (`flip t`) is inherited from `s`.
-/

theorem inv_preserved_enterWait (t : Tid) (s s' : State) (hInv : Inv s) (hAct : actEnterWait t s s') :
    Inv s' := by
  rcases hInv with ⟨hCrit, hWait, hMutex, hD, hE⟩
  rcases hAct with ⟨hLoc, hFlag, hFlag', hTurn', hLoc', hLocOther, hFlagOther, hX⟩
  have hTurnVal : s'.turn = flip t := hTurn'
  have hLocFlip : s'.loc (flip t) = s.loc (flip t) := hLocOther
  have hFlagFlip : s'.flag (flip t) = s.flag (flip t) := hFlagOther
  cases t with
  | t0 =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t' ht'
      cases t' with
      | t0 => simp [hLoc'] at ht'
      | t1 =>
        have htmp : s'.loc t1 = s.loc t1 := by simpa using hLocFlip
        have hloc : s.loc t1 = crit := htmp.symm ▸ ht'
        have hflag : s.flag t1 = true := hCrit t1 hloc
        have htmp2 : s'.flag t1 = s.flag t1 := by
          calc s'.flag t1 = s'.flag (flip t0) := by simp
            _ = s.flag (flip t0) := hFlagFlip
            _ = s.flag t1 := by simp
        rw [htmp2]; exact hflag
    · intro t' ht'
      cases t' with
      | t0 => simpa [hLoc', hFlag'] using ht'
      | t1 =>
        have htmp : s'.loc t1 = s.loc t1 := by simpa using hLocFlip
        have hloc : s.loc t1 = wait := htmp.symm ▸ ht'
        have hflag : s.flag t1 = true := hWait t1 hloc
        have htmp2 : s'.flag t1 = s.flag t1 := by
          calc s'.flag t1 = s'.flag (flip t0) := by simp
            _ = s.flag (flip t0) := hFlagFlip
            _ = s.flag t1 := by simp
        rw [htmp2]; exact hflag
    · simp [hLoc', hLocFlip]
    · intro h; simp [hLoc'] at h
    · intro h; rw [hTurnVal, flip_t0]
  | t1 =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t' ht'
      cases t' with
      | t0 =>
        have htmp : s'.loc t0 = s.loc t0 := by simpa using hLocFlip
        have hloc : s.loc t0 = crit := htmp.symm ▸ ht'
        have hflag : s.flag t0 = true := hCrit t0 hloc
        have htmp2 : s'.flag t0 = s.flag t0 := by
          calc s'.flag t0 = s'.flag (flip t1) := by simp
            _ = s.flag (flip t1) := hFlagFlip
            _ = s.flag t0 := by simp
        rw [htmp2]; exact hflag
      | t1 => simp [hLoc'] at ht'
    · intro t' ht'
      cases t' with
      | t0 =>
        have htmp : s'.loc t0 = s.loc t0 := by simpa using hLocFlip
        have hloc : s.loc t0 = wait := htmp.symm ▸ ht'
        have hflag : s.flag t0 = true := hWait t0 hloc
        have htmp2 : s'.flag t0 = s.flag t0 := by
          calc s'.flag t0 = s'.flag (flip t1) := by simp
            _ = s.flag (flip t1) := hFlagFlip
            _ = s.flag t0 := by simp
        rw [htmp2]; exact hflag
      | t1 => simpa [hLoc', hFlag'] using ht'
    · simp [hLoc', hLocFlip]
    · intro h; rw [hTurnVal, flip_t1]
    · intro h; simp [hLoc'] at h

/-! ### `actEnterCrit` preserves `Inv`

Only thread `t` changes (wait → crit).  The guard condition ensures the
other thread is not currently in crit, so mutual exclusion is preserved.
-/

theorem inv_preserved_enterCrit (t : Tid) (s s' : State) (hInv : Inv s) (hAct : actEnterCrit t s s') :
    Inv s' := by
  rcases hInv with ⟨hCrit, hWait, hMutex, hD, hE⟩
  rcases hAct with ⟨hLoc, hGuard, hLoc', hLocOther, hFlagSame, hTurnSame, hX⟩
  have hFlagSame' (t' : Tid) : s'.flag t' = s.flag t' := by
    simpa using congrArg (λ f : Tid → Bool => f t') hFlagSame
  have hLocOther' (t' : Tid) (hne : t' ≠ t) : s'.loc t' = s.loc t' := by
    have hflip : t' = flip t := ne_implies_flip hne
    subst hflip; exact hLocOther
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; rw [hFlagSame' t]; exact hWait t hLoc
    · rw [hFlagSame' t']; apply hCrit t'; exact hLocOther' t' h ▸ ht'
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; rw [hLoc'] at ht'; simp at ht'
    · rw [hFlagSame' t']; apply hWait t'; exact hLocOther' t' h ▸ ht'
  · intro hBoth
    rcases hBoth with ⟨h0', h1'⟩
    by_cases ht0 : t0 = t
    · subst ht0
      have h1 : s.loc t1 = crit := hLocOther' t1 (by decide) ▸ h1'
      rcases hGuard with (hflag | hturn)
      · have hflag' : s.flag t1 = false := by simpa [flip_t0] using hflag
        have htrue : s.flag t1 = true := hCrit t1 h1
        rw [hflag'] at htrue; simp at htrue
      · have ht1 : s.turn = t1 := hE ⟨h1, hLoc⟩
        have : t0 ≠ t1 := by decide
        exact this (hturn.symm ▸ ht1)
    · by_cases ht1 : t1 = t
      · subst ht1
        have h0 : s.loc t0 = crit := hLocOther' t0 (by decide) ▸ h0'
        rcases hGuard with (hflag | hturn)
        · have hflag' : s.flag t0 = false := by simpa [flip_t1] using hflag
          have htrue : s.flag t0 = true := hCrit t0 h0
          rw [hflag'] at htrue; simp at htrue
        · have ht0 : s.turn = t0 := hD ⟨h0, hLoc⟩
          have : t1 ≠ t0 := by decide
          exact this (hturn.symm ▸ ht0)
      · have h0 : s.loc t0 = crit := hLocOther' t0 ht0 ▸ h0'
        have h1 : s.loc t1 = crit := hLocOther' t1 ht1 ▸ h1'
        exact hMutex ⟨h0, h1⟩
  · intro ⟨h0c, h1w⟩
    rw [hTurnSame]
    cases t with
    | t0 =>
      have flagT1 : s.flag t1 = true := hWait t1 (hLocOther' t1 (by decide) ▸ h1w)
      rcases hGuard with (hflag | hturn)
      · have hflag' : s.flag t1 = false := by simpa [flip_t0] using hflag
        simp [hflag'] at flagT1
      · exact hturn
    | t1 =>
      have h0cs : s.loc t0 = crit := hLocOther' t0 (by decide) ▸ h0c
      exact hD ⟨h0cs, hLoc⟩
  · intro ⟨h1c, h0w⟩
    rw [hTurnSame]
    cases t with
    | t0 =>
      have h1cs : s.loc t1 = crit := hLocOther' t1 (by decide) ▸ h1c
      exact hE ⟨h1cs, hLoc⟩
    | t1 =>
      have flagT0 : s.flag t0 = true := hWait t0 (hLocOther' t0 (by decide) ▸ h0w)
      rcases hGuard with (hflag | hturn)
      · have hflag' : s.flag t0 = false := by simpa [flip_t1] using hflag
        simp [hflag'] at flagT0
      · exact hturn
/-! ### `actExit` preserves `Inv`

Only thread `t` changes (crit → idle, flag reset, x incremented).
Everything else inherits from `s`.
-/

theorem inv_preserved_exit (t : Tid) (s s' : State) (hInv : Inv s) (hAct : actExit t s s') :
    Inv s' := by
  rcases hInv with ⟨hCrit, hWait, hMutex, hD, hE⟩
  rcases hAct with ⟨hLoc, hLoc', hFlag', hLocOther, hFlagOther, hTurnSame, hX⟩
  have hLocOther' (t' : Tid) (hne : t' ≠ t) : s'.loc t' = s.loc t' := by
    have hflip : t' = flip t := ne_implies_flip hne
    subst hflip; exact hLocOther
  have hFlagOther' (t' : Tid) (hne : t' ≠ t) : s'.flag t' = s.flag t' := by
    have hflip : t' = flip t := ne_implies_flip hne
    subst hflip; exact hFlagOther
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; rw [hLoc'] at ht'; simp at ht'
    · rw [hFlagOther' t' h]; apply hCrit t'; exact hLocOther' t' h ▸ ht'
  · intro t' ht'
    by_cases h : t' = t
    · subst t'; rw [hLoc'] at ht'; simp at ht'
    · rw [hFlagOther' t' h]; apply hWait t'; exact hLocOther' t' h ▸ ht'
  · intro hBoth
    rcases hBoth with ⟨h0', h1'⟩
    have h0 : s.loc t0 = crit := by
      by_cases h0t : t0 = t
      · subst h0t; exact hLoc
      · exact hLocOther' t0 h0t ▸ h0'
    have h1 : s.loc t1 = crit := by
      by_cases h1t : t1 = t
      · subst h1t; exact hLoc
      · exact hLocOther' t1 h1t ▸ h1'
    exact hMutex ⟨h0, h1⟩
  · intro ⟨h0c, h1w⟩
    rw [hTurnSame]
    have h0s : s.loc t0 = crit := by
      by_cases h0t : t0 = t
      · subst h0t; exact hLoc
      · exact hLocOther' t0 h0t ▸ h0c
    have h1s : s.loc t1 = wait := by
      by_cases h1t : t1 = t
      · subst h1t; rw [hLoc'] at h1w; simp at h1w
      · exact hLocOther' t1 h1t ▸ h1w
    exact hD ⟨h0s, h1s⟩
  · intro ⟨h1c, h0w⟩
    rw [hTurnSame]
    have h1s : s.loc t1 = crit := by
      by_cases h1t : t1 = t
      · subst h1t; exact hLoc
      · exact hLocOther' t1 h1t ▸ h1c
    have h0s : s.loc t0 = wait := by
      by_cases h0t : t0 = t
      · subst h0t; rw [hLoc'] at h0w; simp at h0w
      · exact hLocOther' t0 h0t ▸ h0w
    exact hE ⟨h1s, h0s⟩

/-! ### Stuttering preserves `Inv` -/

theorem inv_preserved_stutter (s s' : State) (hInv : Inv s) (hAct : actStutter s s') : Inv s' := by
  subst s'
  exact hInv

/-!
## Combined theorem
-/

/-- Every `Next` step preserves `Inv`.  This is the inductive step of the TLA+
    invariance proof. -/
theorem next_preserves_inv (s s' : State) (hInv : Inv s) (hNext : Next s s') : Inv s' := by
  rcases hNext with (⟨t, h⟩ | ⟨t, h⟩ | ⟨t, h⟩ | h)
  · exact inv_preserved_enterWait t s s' hInv h
  · exact inv_preserved_enterCrit t s s' hInv h
  · exact inv_preserved_exit t s s' hInv h
  · exact inv_preserved_stutter s s' hInv h

/-!
## Inductive reachability

A formal definition of reachable states: the reflexive‑transitive closure
of `Next` from `init`.
-/

inductive Reachable : State → Prop
  | init    : Reachable init
  | step    (s s' : State) : Reachable s → Next s s' → Reachable s'

/-- Every reachable state satisfies `Inv`, hence mutual exclusion. -/
theorem all_reachable_inv (s : State) (h : Reachable s) : Inv s := by
  induction h with
  | init => exact inv_init
  | step _ _ hPrev hNext ih => exact next_preserves_inv _ _ ih hNext

/-- **Main theorem**: Mutual exclusion holds for every reachable state. -/
theorem mutual_exclusion_holds (s : State) (h : Reachable s) : MutualExclusion s :=
  inv_implies_mutex s (all_reachable_inv s h)

/-!
## Concrete Execution Trace

A concrete interleaving to illustrate the model at work: both threads
run to completion without ever being simultaneously in the critical section.
-/

/-- The state after t0 enters `wait`. -/
def s1 : State :=
  { loc  := fun | t0 => wait | t1 => idle
  , flag := fun | t0 => true | t1 => false
  , turn := t1, x := 0 }

/-- The state after t1 enters `wait`. -/
def s2 : State :=
  { loc  := fun | t0 => wait | t1 => wait
  , flag := fun | t0 => true | t1 => true
  , turn := t0, x := 0 }

/-- The state after t0 enters `crit`. -/
def s3 : State :=
  { loc  := fun | t0 => crit | t1 => wait
  , flag := fun | t0 => true | t1 => true
  , turn := t0, x := 0 }

/-- The state after t0 exits `crit` (and increments x). -/
def s4 : State :=
  { loc  := fun | t0 => idle | t1 => wait
  , flag := fun | t0 => false | t1 => true
  , turn := t0, x := 1 }

/-- The state after t1 enters `crit`. -/
def s5 : State :=
  { loc  := fun | t0 => idle | t1 => crit
  , flag := fun | t0 => false | t1 => true
  , turn := t0, x := 1 }

/-- The state after t1 exits `crit` (and increments x). -/
def s6 : State :=
  { loc  := fun | t0 => idle | t1 => idle
  , flag := fun | t0 => false | t1 => false
  , turn := t0, x := 2 }

theorem init_to_s1 : Next init s1 := by
  refine Or.inl ⟨t0, ?_⟩
  unfold actEnterWait; simp [s1, init]

theorem s1_to_s2 : Next s1 s2 := by
  refine Or.inl ⟨t1, ?_⟩
  unfold actEnterWait; simp [s1, s2]

theorem s2_to_s3 : Next s2 s3 := by
  refine Or.inr (Or.inl ⟨t0, ?_⟩)
  unfold actEnterCrit; simp [s2, s3]

theorem s3_to_s4 : Next s3 s4 := by
  refine Or.inr (Or.inr (Or.inl ⟨t0, ?_⟩))
  unfold actExit; simp [s3, s4]

theorem s4_to_s5 : Next s4 s5 := by
  refine Or.inr (Or.inl ⟨t1, ?_⟩)
  unfold actEnterCrit; simp [s4, s5]

theorem s5_to_s6 : Next s5 s6 := by
  refine Or.inr (Or.inr (Or.inl ⟨t1, ?_⟩))
  unfold actExit; simp [s5, s6]

/-- The trace from `init` to `s6` is valid. -/
theorem trace_complete : Reachable s6 := by
  apply Reachable.step s5 s6
  · apply Reachable.step s4 s5
    · apply Reachable.step s3 s4
      · apply Reachable.step s2 s3
        · apply Reachable.step s1 s2
          · apply Reachable.step init s1
            · exact Reachable.init
            · exact init_to_s1
          · exact s1_to_s2
        · exact s2_to_s3
      · exact s3_to_s4
    · exact s4_to_s5
  · exact s5_to_s6

/-- Verify mutual exclusion on the final state of the concrete trace. -/
theorem trace_mutex : MutualExclusion s6 :=
  mutual_exclusion_holds s6 trace_complete

end TLA
