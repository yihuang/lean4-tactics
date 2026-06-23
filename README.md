# Lean4 Tactics

Interactive, executable documentation for Lean 4 tactics.

## What this is

Each tactic is demonstrated by **self-contained theorems** with **line-by-line
context comments** showing the goal state (`⊢`) before and after every step.
Open any file, place your cursor on a tactic, and watch the goal transform in
the Lean infoview.

## Modules

| Module | Tactics |
|---|---|
| `Basic` | `intro`, `apply`, `exact`, `refine` |
| `Rewriting` | `rw`, `simp`, `dsimp`, `simpa` |
| `CaseAnalysis` | `cases`, `induction`, `injection`, `constructor`, `split`, `left`, `right` |
| `Propositional` | `exfalso`, `by_contra`, `by_cases`, `contradiction` |
| `Hypothesis` | `have`, `let`, `revert`, `clear`, `rename_i`, `subst`, `specialize`, `generalize` |
| `Calculation` | `calc`, `omega`, `decide`, `native_decide` |
| `Control` | `all_goals`, `any_goals`, `first`, `try`, `repeat`, `focus`, `case` |
| `Advanced` | `unfold`, `change`, `show`, `match` |

## How to use

```bash
git clone <this-repo>
cd lean4-tactics
lake build
```

Then open any `.lean` file in VS Code with the [lean4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) extension.
Place the cursor on a tactic line — the infoview shows the goal before and after.
Every theorem compiles and runs standalone; no external dependencies.

## Goal comments

All files use a consistent annotation style:

```
-- ⊢  current goal         (target type)
-- h₁ : P                   (new hypothesis added by the tactic)
-- two subgoals: `P` and `Q`  (new goals generated)
```

## Requirements

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Lean 4 (toolchain: `leanprover/lean4:v4.30.0-rc1`)
- VSCode + [lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
