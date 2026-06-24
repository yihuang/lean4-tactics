/-
# Linear Temporal Logic (LTL) — Generic Library

LTL operators defined generically over infinite traces (`Nat → α`).

| Symbol | Operator     | Meaning                         |
|--------|--------------|----------------------------------|
| `○ p`  | `next`       | p holds at the next step         |
| `□ p`  | `always`     | p holds at every step            |
| `◇ p`  | `eventually` | p holds at some future step      |
| `p 𝒰 q`| `strUntil`   | p holds strictly until q holds   |
-/


namespace LTL

/-! ## Infinite traces -/

def Trace (α : Type) : Type := Nat → α
def drop {α} (σ : Trace α) (n : Nat) : Trace α := λ k => σ (n + k)

/-! ## LTL operators -/

variable {α : Type} (σ : Trace α)

def next (p : α → Prop) : Prop := p (σ 1)
def always (p : α → Prop) : Prop := ∀ n, p (σ n)
def eventually (p : α → Prop) : Prop := ∃ n, p (σ n)
def strUntil (p q : α → Prop) : Prop := ∃ n, q (σ n) ∧ ∀ m < n, p (σ m)
def weakUntil (p q : α → Prop) : Prop := always σ p ∨ strUntil σ p q

theorem not_always (p : α → Prop) : ¬(always σ p) ↔ eventually σ (λ s => ¬ p s) := by
  unfold always eventually; simp

theorem not_eventually (p : α → Prop) : ¬(eventually σ p) ↔ always σ (λ s => ¬ p s) := by
  unfold always eventually; simp

/-! ## Transition system validity -/

def isValid (Next : α → α → Prop) (σ : Trace α) : Prop := ∀ n, Next (σ n) (σ (n + 1))

/-! ## Fairness -/

def enabled (A : α → α → Prop) (s : α) : Prop := ∃ s', A s s'
def takenAt (A : α → α → Prop) (σ : Trace α) (n : Nat) : Prop := A (σ n) (σ (n + 1))
def infOftenEnabled (A : α → α → Prop) (σ : Trace α) : Prop := ∀ n, ∃ m ≥ n, enabled A (σ m)
def infOftenTaken (A : α → α → Prop) (σ : Trace α) : Prop := ∀ n, ∃ m ≥ n, takenAt A σ m
def WF (A : α → α → Prop) (σ : Trace α) : Prop := infOftenEnabled A σ → infOftenTaken A σ
def SF (A : α → α → Prop) (σ : Trace α) : Prop :=
  (∃ n, ∀ m ≥ n, enabled A (σ m)) → infOftenTaken A σ

end LTL
