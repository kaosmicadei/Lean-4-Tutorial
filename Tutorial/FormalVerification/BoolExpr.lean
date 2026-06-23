import Std

/-!
From L. de Moura and S Ullrich, "The Lean 4 Theorem Prover and Programming
Language" https://link.springer.com/chapter/10.1007/978-3-030-79876-5_37

The goal of this file is to show how to use Lean to define a simple symbolic
language and a simplification procedure for it, and to prove that the
simplification procedure preserves the meaning of expressions.
-/

inductive BoolExpr where
  | var (name : String) : BoolExpr
  | val (b : Bool) : BoolExpr
  | or  (p q : BoolExpr) : BoolExpr
  | not (p : BoolExpr) : BoolExpr

def simplify : BoolExpr → BoolExpr
  | .or p q => mkOr (simplify p) (simplify q)
  | .not p => mkNot (simplify p)
  | e => e
  where
    mkOr : BoolExpr → BoolExpr → BoolExpr
      | .val true, _ => .val true
      | .val false, q => q
      | _, .val true => .val true
      | p, .val false => p
      | p, q => .or p q

    mkNot : BoolExpr → BoolExpr
      | .val b => .val (!b)
      | p => .not p

abbrev Context := Std.HashMap String Bool

def denote (ctx : Context) : BoolExpr → Bool
  | .val b => b
  | .not p => !(denote ctx p)
  | .or p q => denote ctx p || denote ctx q
  | .var x => if let some b := ctx.get? x then b else false

@[simp] theorem denote_mkOr (ctx : Context) (p q : BoolExpr) :
  denote ctx (simplify.mkOr p q) = denote ctx (p.or q) := by
  cases p with
  | val b =>
    simp [simplify.mkOr, denote]
    cases b
    . simp
    . simp [denote]
  | _ =>
    simp [simplify.mkOr, denote]
    cases q with
    | val b =>
      simp [denote]
      cases b
      . simp [denote]
      . simp [denote]
    | _ =>
      simp [denote]


@[simp] theorem denote_mkNot (ctx : Context) (p : BoolExpr) :
  denote ctx (simplify.mkNot p) = denote ctx (p.not) := by
  cases p <;> simp [simplify.mkNot, denote]

theorem denote_simplify (ctx : Context) (p : BoolExpr) :
  denote ctx (simplify p) = denote ctx p := by
  induction p with
  | or p q ihp ihq =>
    rw [simplify, denote_mkOr, denote, ihp, ihq, denote]
  | not p ihp =>
    rw [simplify, denote_mkNot, denote, ihp, denote]
  | _ => rfl
