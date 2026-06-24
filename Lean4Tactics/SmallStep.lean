/-
# Compiler Correctness: Lambda Calculus → Pure Stack VM

## Small-Step Semantics

**Small-step semantics** describe computation as a sequence of atomic transitions
between machine states. Each step is indivisible (a single instruction), and
execution proceeds one step at a time until no further step is possible.

This contrasts with **big-step semantics** (the `Eval` relation in this file),
which describes the *final result* of evaluating a term in a single judgment.
Big-step is "what you get"; small-step is "how you get there, step by step."

| Aspect | Big-Step (`Eval`) | Small-Step (`VMStep` / `VMExec`) |
|--------|-------------------|----------------------------------|
| Granularity | Whole term at once | One VM instruction at a time |
| Intermediate states | None | Every `State` (code, stack, env, dump) |
| Relation | `Eval env t v` (term → value) | `VMStep s t` (state → next state) |
| Closure | `VMExec s t` = reflexive-transitive closure of `VMStep` |

## This File

A λ-calculus with de Bruijn indices is compiled to a pure stack VM.
The key theorem `compile_sim` proves a **simulation** between the two levels:
if `Eval env t v` (big-step), then the compiled code reaches the same value
via small-step VM transitions.

No `Term` references at runtime — all compilation is done at compile time.
-/

namespace Lambda

inductive Term : Type
  | lit : Nat → Term | var : Nat → Term | lam : Term → Term
  | app : Term → Term → Term | add : Term → Term → Term
  deriving Repr
open Term

inductive Instr : Type
  | push : Nat → Instr
  | iadd : Instr
  | load : Nat → Instr
  | mkclo : List Instr → Instr
  | call : Instr
  | ret : Instr
  | slide : Nat → Instr
  deriving Repr
open Instr

abbrev Prog := List Instr

inductive Val : Type
  | num : Nat → Val
  | clo : Prog → List Val → Val
  deriving Repr
open Val

abbrev Env := List Val

def compile (t : Term) : Prog :=
  match t with
  | lit n   => [push n]
  | var i   => [load i]
  | lam b   => [mkclo (compile b ++ [ret])]
  | app f a => compile a ++ compile f ++ [call, slide 1]
  | add a b => compile b ++ compile a ++ [iadd]

inductive Eval : Env → Term → Val → Prop
  | lit {env n} : Eval env (lit n) (num n)
  | var {env i} (h : i < env.length) : Eval env (var i) (env.get ⟨i, h⟩)
  | lam {env body} : Eval env (lam body) (clo (compile body ++ [ret]) env)
  | app {env fn arg body env' va v}
      (hf : Eval env fn (clo (compile body ++ [ret]) env'))
      (ha : Eval env arg va)
      (hbody : Eval (va :: env') body v) : Eval env (app fn arg) v
  | iadd {env a b va vb}
      (ha : Eval env a (num va)) (hb : Eval env b (num vb)) : Eval env (add a b) (num (va + vb))

structure State where
  code  : Prog
  stack : List Val
  env   : Env
  dump  : List (Prog × Env)
  deriving Repr

inductive VMStep : State → State → Prop
  | push (n : Nat) (r : Prog) (st : List Val) (env : Env) (d : List (Prog × Env)) :
      VMStep (State.mk (push n :: r) st env d) (State.mk r (num n :: st) env d)
  | iadd (a b : Nat) (r : Prog) (st : List Val) (env : Env) (d : List (Prog × Env)) :
      VMStep (State.mk (iadd :: r) (num a :: num b :: st) env d) (State.mk r (num (a + b) :: st) env d)
  | load (i : Nat) (r : Prog) (st : List Val) (env : Env) (d : List (Prog × Env)) (h : i < env.length) :
      VMStep (State.mk (load i :: r) st env d) (State.mk r (env.get ⟨i, h⟩ :: st) env d)
  | mkclo (code : Prog) (r : Prog) (st : List Val) (env : Env) (d : List (Prog × Env)) :
      VMStep (State.mk (mkclo code :: r) st env d) (State.mk r (clo code env :: st) env d)
  | call (code : Prog) (env' : Env) (v : Val) (r : Prog) (st : List Val) (env : Env) (d : List (Prog × Env)) :
      VMStep (State.mk (call :: r) (clo code env' :: v :: st) env d)
             (State.mk code (v :: st) (v :: env') ((r, env) :: d))
  | ret (st : List Val) (env : Env) (k : Prog) (env_k : Env) (d : List (Prog × Env)) :
      VMStep (State.mk [ret] st env ((k, env_k) :: d)) (State.mk k st env_k d)
  | slide (n : Nat) (v : Val) (st : List Val) (r : Prog) (env : Env) (d : List (Prog × Env)) :
      VMStep (State.mk (slide n :: r) (v :: st) env d) (State.mk r (v :: st.drop n) env d)

inductive VMExec : State → State → Prop
  | refl (s : State) : VMExec s s
  | step (s t u : State) (h : VMStep s t) (hrest : VMExec t u) : VMExec s u

/--
`VMExec` is the reflexive-transitive closure of `VMStep`.
This lemma proves it is transitive: if `s` reaches `t` and `t` reaches `u`,
then `s` reaches `u`.

**Proof**: induction on the derivation of `hst : VMExec s t`.
- `refl` case: `s = t`, so `htu : VMExec t u` is the goal.
- `step` case: `VMExec.step s t' u h (ih htu)` extends the first step `h`
  with the induction hypothesis `ih` applied to the remaining steps.
-/
theorem VMExec_trans {s t u : State} (hst : VMExec s t) (htu : VMExec t u) : VMExec s u := by
  induction hst with
  | refl =>
    -- `hst = refl s` ⇒ `t = s`. The goal becomes `VMExec s u`, which is `htu`.
    exact htu
  | step s t' _ h hrest ih =>
    -- `ih : VMExec t u → VMExec s u`. Apply `step` to extend by `h`.
    exact VMExec.step s t' u h (ih htu)

/--
After a function call returns, the `ret` instruction restores the caller's
continuation and environment from the dump, and `slide 1` removes the
argument from the stack (keeping the result on top).

This lemma composes the two VM steps into a single `VMExec` transition.
-/
theorem ret_slide1 (v w : Val) (st : List Val) (env env' : Env) (k : Prog) (dump : List (Prog × Env)) :
    VMExec (State.mk [ret] (v :: w :: st) (w :: env') ((slide 1 :: k, env) :: dump))
           (State.mk k (v :: st) env dump) := by
  -- ⊢ `VMExec (State.mk [ret] …) (State.mk k (v :: st) env dump)`
  refine VMExec.step _ _ _ (VMStep.ret (v :: w :: st) (w :: env') (slide 1 :: k) env dump) ?_
  -- ⊢ `VMExec (State.mk (slide 1 :: k) (v :: w :: st) env dump) (State.mk k (v :: st) env dump)`
  refine VMExec.step _ _ _ (VMStep.slide 1 v (w :: st) k env dump) ?_
  -- ⊢ `VMExec (State.mk k (v :: st) env dump) (State.mk k (v :: st) env dump)`
  exact VMExec.refl _

/--
The core **simulation lemma**: running the compiled code of a term `t`
(from any continuation `k`, stack `st`, environment `env`, and dump `dump`)
produces the same result as the big-step `Eval` semantics.

Formally, if `Eval env t v` then for any `k`, `st`, `dump`:
  `VMExec (State.mk (compile t ++ k) st env dump) (State.mk k (v :: st) env dump)`

**Proof**: induction on the `Eval` derivation `h`.

| Case | Compilation | VM behavior |
|------|-------------|-------------|
| `lit` | `push n` → pushes `num n` | Single step. |
| `var` | `load i` → loads from env | Single step. |
| `lam` | `mkclo (body ++ [ret])` → pushes closure | Single step. |
| `iadd` | `b` then `a` then `iadd` | Simulate `b` (`num vb` on stack), then `a` (`num va` on top), then `iadd` computes `va + vb`. |
| `app` | `arg`, then `fn`, then `call; slide 1` | Simulate `arg` → `va`, then `fn` → closure. `call` pushes a frame and jumps to the closure body. Simulate body → `v`. `ret` + `slide 1` (via `ret_slide1`) restore caller state with `v` on top. |
-/
theorem compile_sim (t : Term) (env : Env) (k : Prog) (st : List Val) (dump : List (Prog × Env))
    (v : Val) (h : Eval env t v) :
    VMExec (State.mk (compile t ++ k) st env dump) (State.mk k (v :: st) env dump) := by
  induction h generalizing k st dump
  case lit env n =>
    -- ⊢ `VMExec (State.mk (push n :: k) st env dump) (State.mk k (num n :: st) env dump)`
    exact VMExec.step _ _ _ (VMStep.push n k st env dump) (VMExec.refl _)
  case var env i h =>
    -- `h : i < env.length`
    -- ⊢ `VMExec (State.mk (load i :: k) st env dump) (State.mk k (env.get ⟨i, h⟩ :: st) env dump)`
    exact VMExec.step _ _ _ (VMStep.load i k st env dump h) (VMExec.refl _)
  case lam env body =>
    -- ⊢ `VMExec (State.mk (mkclo (compile body ++ [ret]) :: k) st env dump) (State.mk k (clo (compile body ++ [ret]) env :: st) env dump)`
    exact VMExec.step _ _ _ (VMStep.mkclo (compile body ++ [ret]) k st env dump) (VMExec.refl _)
  case iadd env a b va vb ha hb iha ihb =>
    unfold compile
    -- ⊢ `VMExec (State.mk (compile b ++ compile a ++ [iadd] ++ k) st env dump) (State.mk k (num (va + vb) :: st) env dump)`
    refine VMExec_trans (by simpa [List.append_assoc] using ihb (compile a ++ [iadd] ++ k) st dump) ?_
    -- ⊢ `VMExec (State.mk (compile a ++ [iadd] ++ k) (num vb :: st) env dump) (State.mk k (num (va + vb) :: st) env dump)`
    refine VMExec_trans (by simpa using iha (iadd :: k) (num vb :: st) dump) ?_
    -- ⊢ `VMExec (State.mk (iadd :: k) (num va :: num vb :: st) env dump) (State.mk k (num (va + vb) :: st) env dump)`
    exact VMExec.step _ _ _ (VMStep.iadd va vb k st env dump) (VMExec.refl _)
  case app env fn arg body env' va v hf ha hbody ihf iha ihbody =>
    unfold compile
    -- ⊢ `VMExec (State.mk (compile arg ++ compile fn ++ [call, slide 1] ++ k) st env dump) (State.mk k (v :: st) env dump)`
    refine VMExec_trans (by simpa [List.append_assoc] using iha (compile fn ++ (call :: slide 1 :: k)) st dump) ?_
    -- ⊢ `VMExec (State.mk (compile fn ++ (call :: slide 1 :: k)) (va :: st) env dump) (State.mk k (v :: st) env dump)`
    refine VMExec_trans (by simpa using ihf (call :: slide 1 :: k) (va :: st) dump) ?_
    -- ⊢ `VMExec (State.mk (call :: slide 1 :: k) (clo (compile body ++ [ret]) env' :: va :: st) env dump) (State.mk k (v :: st) env dump)`
    refine VMExec.step _ _ _ (VMStep.call (compile body ++ [ret]) env' va (slide 1 :: k) st env dump) ?_
    -- ⊢ `VMExec (State.mk (compile body ++ [ret]) (va :: st) (va :: env') ((slide 1 :: k, env) :: dump)) (State.mk k (v :: st) env dump)`
    exact VMExec_trans (ihbody [ret] (va :: st) ((slide 1 :: k, env) :: dump))
                       (ret_slide1 v va st env env' k dump)

/--
Top-level compiler correctness: evaluating a closed term `t` in environment
`env` to value `v` means the compiled program starting in the empty stack
and dump ends with `[v]` on the stack.

This is `compile_sim` specialized to `k = []`, `st = []`, `dump = []`.
-/
theorem compile_correct (t : Term) (env : Env) (v : Val) (h : Eval env t v) :
    VMExec (State.mk (compile t) [] env []) (State.mk [] [v] env []) := by
  -- ⊢ `VMExec (State.mk (compile t) [] env []) (State.mk [] [v] env [])`
  simpa using compile_sim t env [] [] [] v h

def exampleTerm : Term := app (lam (add (var 0) (lit 1))) (lit 5)

#eval compile exampleTerm

/--
The example term `(λx. x + 1) 5` evaluates to `6` under the big-step `Eval` semantics.
The `apply` steps use `Eval.app` (the argument `5` is a literal, and `fn` evaluates
to a closure), then `Eval.iadd` with `var 0` (the bound variable, value `5`) and `lit 1`.
-/
theorem example_eval : Eval [] exampleTerm (num 6) := by
  -- ⊢ `Eval [] exampleTerm (num 6)`
  apply Eval.app (Eval.lam) (Eval.lit)
  -- ⊢ `Eval (num 5 :: []) (add (var 0) (lit 1)) (num 6)`
  apply Eval.iadd (Eval.var (by decide)) (Eval.lit)

/--
Compiler correctness for the example term: compiling `(λx. x + 1) 5` and running
it on the VM produces `[6]` on the stack, confirming the end-to-end result.
This is an instance of `compile_correct`.
-/
theorem example_correct : VMExec (State.mk (compile exampleTerm) [] [] [])
                                 (State.mk [] [num 6] [] []) := by
  -- ⊢ `VMExec (State.mk (compile exampleTerm) [] [] []) (State.mk [] [num 6] [] [])`
  exact compile_correct exampleTerm [] (num 6) example_eval

end Lambda
