set_option linter.unusedSimpArgs false

/-
# Compiler Correctness: Arithmetic Expressions → Stack VM

A complete, self-contained compiler verification example:

1. **Source**: arithmetic expressions with de Bruijn-indexed variables
2. **Target**: a stack-based VM
3. **Compiler**: translates source to VM instructions
4. **Proof**: structural induction — compiled code matches the interpreter
-/

set_option linter.unusedVariables false

/-! ## Source -/

inductive Expr : Type
  | num : Nat → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  deriving Repr

open Expr

def Store := List Nat

def lookup (env : Store) (i : Nat) : Nat :=
  match env with
  | [] => 0
  | x :: xs => if i = 0 then x else lookup xs (i - 1)

def denote (env : Store) (e : Expr) : Nat :=
  match e with
  | num n   => n
  | var i   => lookup env i
  | add a b => denote env a + denote env b
  | sub a b => denote env a - denote env b

/-! ## Target: Stack VM -/

inductive Instr : Type
  | push : Nat → Instr
  | load : Nat → Instr
  | iadd : Instr
  | isub : Instr
  deriving Repr

open Instr

abbrev Prog := List Instr

def exec (p : Prog) (store : Store) (stack : List Nat) : List Nat :=
  match p with
  | [] => stack
  | push n :: rest => exec rest store (n :: stack)
  | load i :: rest => exec rest store (lookup store i :: stack)
  | iadd :: rest =>
      match stack with
      | a :: b :: st => exec rest store ((b + a) :: st)
      | _ => stack
  | isub :: rest =>
      match stack with
      | a :: b :: st => exec rest store ((b - a) :: st)
      | _ => stack

/-! ## Compiler -/

def compile (e : Expr) : Prog :=
  match e with
  | num n   => [push n]
  | var i   => [load i]
  | add a b => compile a ++ compile b ++ [iadd]
  | sub a b => compile a ++ compile b ++ [isub]

/-! ## Correctness Proof -/

theorem compile_sim (e : Expr) (env : Store) (k : Prog) (st : List Nat) :
    exec (compile e ++ k) env st = exec k env (denote env e :: st) := by
  induction e generalizing k st with
  | num n => simp [compile, exec, denote]
  | var i => simp [compile, exec, denote, lookup]
  | add a b iha ihb =>
    calc
      exec (compile a ++ compile b ++ [iadd] ++ k) env st
          = exec (compile b ++ [iadd] ++ k) env (denote env a :: st) := by
            simpa [List.append_assoc] using iha (compile b ++ [iadd] ++ k) st
      _ = exec ([iadd] ++ k) env (denote env b :: denote env a :: st) := by
            simpa [List.append_assoc] using ihb ([iadd] ++ k) (denote env a :: st)
      _ = exec k env ((denote env a + denote env b) :: st) := by simp [exec]
      _ = exec k env (denote env (add a b) :: st) := rfl
  | sub a b iha ihb =>
    calc
      exec (compile a ++ compile b ++ [isub] ++ k) env st
          = exec (compile b ++ [isub] ++ k) env (denote env a :: st) := by
            simpa [List.append_assoc] using iha (compile b ++ [isub] ++ k) st
      _ = exec ([isub] ++ k) env (denote env b :: denote env a :: st) := by
            simpa [List.append_assoc] using ihb ([isub] ++ k) (denote env a :: st)
      _ = exec k env ((denote env a - denote env b) :: st) := by simp [exec]
      _ = exec k env (denote env (sub a b) :: st) := rfl

theorem compile_correct (e : Expr) (env : Store) :
    exec (compile e) env [] = [denote env e] := by
  have h := compile_sim e env [] []
  simpa using h

/-! ## Example -/

def myExpr : Expr := sub (add (num 3) (num 4)) (num 2)

#eval denote [] myExpr
#eval exec (compile myExpr) [] []
