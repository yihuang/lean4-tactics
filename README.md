# Lean4 Tactics

Interactive, executable documentation for Lean 4 tactics.

## What this is

Each tactic is demonstrated by **self-contained theorems** with **line-by-line
context comments** showing the goal state (`⊢`) before and after every step.
Open any file, place your cursor on a tactic, and watch the goal transform in
the Lean infoview.

## Core tactic modules

| Module | Tactics |
|---|---|
| `Basic` | `intro`, `apply`, `exact`, `refine`, `infer_instance` |
| `Rewriting` | `rw`, `simp`, `dsimp`, `simpa` |
| `CaseAnalysis` | `cases`, `induction`, `injection`, `constructor`, `split`, `left`, `right` |
| `Propositional` | `exfalso`, `Classical.byContradiction`, `by_cases`, `contradiction`, `classical` |
| `Hypothesis` | `have`, `let`, `revert`, `clear`, `rename_i`, `rename`, `subst`, `subst_vars`, `specialize`, `generalize` |
| `Calculation` | `calc`, `omega`, `decide`, `native_decide` |
| `Control` | `all_goals`, `any_goals`, `first`, `try`, `repeat`, `focus`, `case`, `done`, `skip`, `next`, `rotate_left`, `rotate_right` |
| `Advanced` | `unfold`, `change`, `show`, `match` |
| `Grind` | `grind` (SMT automation: congruence closure, arithmetic, E‑matching) |
| `Mvcgen` | `mvcgen` (monadic verification condition generator) |
| `Relation` | `symm`, `apply_assumption`, `ac_rfl` |
| `Verification` | software verification patterns: `induction`, `omega`, `calc`, `native_decide`, `simp`, `by_cases` |

## Advanced demos

Larger, self-contained formalisation projects (under `Lean4Tactics/Demos/`) that
apply the tactics above to non-trivial artefacts.

| Demo | Description |
|---|---|
| `Compiler` | Compiler correctness for arithmetic expressions (`Expr` → stack VM). Structural induction, big-step semantics. |
| `SmallStep` | λ-calculus with de Bruijn indices compiled to a pure stack VM. Small-step (`VMStep`/`VMExec`) and big-step (`Eval`) semantics, equivalence proof. |
| `NaturalNumberGame` | Transcription of the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) — 9 worlds, ~110 theorems on addition, multiplication, exponentiation, inequalities, and cancellation laws, all fully proved. NNG's `FLT` joke boss is recorded as a `Prop` statement only (it is Fermat's Last Theorem). |
| `TLA` | TLA+-style state-transition verification: Peterson's two-thread mutual-exclusion algorithm, with the mutual-exclusion safety invariant and a liveness proof. |
| `LTL` | A generic Linear Temporal Logic library over infinite traces (`Nat → α`): the `○`/`□`/`◇`/`𝒰` operators and their laws. |

## How to use

```bash
git clone <this-repo>
cd lean4-tactics
lake build
```

Then open any `.lean` file in VS Code with the [lean4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) extension.
Place the cursor on a tactic line — the infoview shows the goal before and after.
Every theorem compiles and is fully proved standalone — no external dependencies, no `sorry`.

## Annotation style

Each step is annotated with the goal state and context changes:

```
-- ⊢ P → Q              (goal before the tactic)
intro h
-- h : P                 (new hypothesis)
-- ⊢ Q                  (updated goal after the tactic)

refine And.intro ?_ ?_
-- ⊢ P                  (subgoal inside the first branch)
· exact hp
-- ⊢ Q                  (subgoal inside the second branch)
· exact hq
```

## Requirements

- [elan](https://github.com/leanprover/elan) (Lean version manager, includes `lake`)
- Lean 4 (toolchain: `leanprover/lean4:v4.30.0-rc1`)
- VSCode + [lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

## Reference links

| Source | URL |
|---|---|
| Lean reference — tactic reference | <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/> |
| Lean reference — `grind` | <https://lean-lang.org/doc/reference/latest/The--grind--tactic/> |
| Lean reference — `mvcgen` | <https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/> |
| Lean tutorial — `mvcgen` imperative verification | <https://lean-lang.org/doc/tutorials/latest/mvcgen/> |
| Core tactic source (`Init/Tactics.lean`) | <https://github.com/leanprover/lean4/blob/master/src/Init/Tactics.lean> |
| `Init.Tactics` API docs | <https://physlib.io/docs/Init/Tactics.html> |
| Lean release notes | <https://lean-lang.org/doc/reference/latest/releases/> |
