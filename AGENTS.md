# lean4-tactics

Tactic documentation with executable examples and line-by-line context comments.

Each theorem is self-contained. Comments annotate the goal state before and after
every tactic application — clone the repo, open in VS Code, and step through with
the Lean LSP infoview.

## Architecture

- `Lean4Tactics/` — one file per tactic category (Basic, Rewriting, CaseAnalysis, …)
- Every theorem is `by`-block with `-- ⊢` markers documenting the current target
- All examples compile on `lake build` with no mathlib dependency
