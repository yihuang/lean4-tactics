/-
# Compiler Correctness: Lambda Calculus → Pure Stack VM

A λ-calculus with de Bruijn indices, compiled to a pure stack machine.
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

theorem VMExec_trans {s t u : State} (hst : VMExec s t) (htu : VMExec t u) : VMExec s u := by
  induction hst with
  | refl => exact htu
  | step s t' _ h hrest ih => exact VMExec.step s t' u h (ih htu)

theorem ret_slide1 (v w : Val) (st : List Val) (env env' : Env) (k : Prog) (dump : List (Prog × Env)) :
    VMExec (State.mk [ret] (v :: w :: st) (w :: env') ((slide 1 :: k, env) :: dump))
           (State.mk k (v :: st) env dump) :=
  VMExec.step _ _ _ (VMStep.ret (v :: w :: st) (w :: env') (slide 1 :: k) env dump) <|
  VMExec.step _ _ _ (VMStep.slide 1 v (w :: st) k env dump) (VMExec.refl _)

theorem compile_sim (t : Term) (env : Env) (k : Prog) (st : List Val) (dump : List (Prog × Env))
    (v : Val) (h : Eval env t v) :
    VMExec (State.mk (compile t ++ k) st env dump) (State.mk k (v :: st) env dump) := by
  induction h generalizing k st dump
  case lit env n => exact VMExec.step _ _ _ (VMStep.push n k st env dump) (VMExec.refl _)
  case var env i h => exact VMExec.step _ _ _ (VMStep.load i k st env dump h) (VMExec.refl _)
  case lam env body => exact VMExec.step _ _ _ (VMStep.mkclo (compile body ++ [ret]) k st env dump) (VMExec.refl _)
  case iadd env a b va vb ha hb iha ihb =>
    unfold compile
    refine VMExec_trans (by simpa [List.append_assoc] using ihb (compile a ++ [iadd] ++ k) st dump) ?_
    refine VMExec_trans (by simpa using iha (iadd :: k) (num vb :: st) dump) ?_
    exact VMExec.step _ _ _ (VMStep.iadd va vb k st env dump) (VMExec.refl _)
  case app env fn arg body env' va v hf ha hbody ihf iha ihbody =>
    unfold compile
    refine VMExec_trans (by simpa [List.append_assoc] using iha (compile fn ++ (call :: slide 1 :: k)) st dump) ?_
    refine VMExec_trans (by simpa using ihf (call :: slide 1 :: k) (va :: st) dump) ?_
    refine VMExec.step _ _ _ (VMStep.call (compile body ++ [ret]) env' va (slide 1 :: k) st env dump) ?_
    exact VMExec_trans (ihbody [ret] (va :: st) ((slide 1 :: k, env) :: dump))
                       (ret_slide1 v va st env env' k dump)

theorem compile_correct (t : Term) (env : Env) (v : Val) (h : Eval env t v) :
    VMExec (State.mk (compile t) [] env []) (State.mk [] [v] env []) := by
  simpa using compile_sim t env [] [] [] v h

def exampleTerm : Term := app (lam (add (var 0) (lit 1))) (lit 5)

#eval compile exampleTerm

theorem example_eval : Eval [] exampleTerm (num 6) := by
  apply Eval.app (Eval.lam) (Eval.lit)
  apply Eval.iadd (Eval.var (by decide)) (Eval.lit)

theorem example_correct : VMExec (State.mk (compile exampleTerm) [] [] [])
                                 (State.mk [] [num 6] [] []) :=
  compile_correct exampleTerm [] (num 6) example_eval

end Lambda
