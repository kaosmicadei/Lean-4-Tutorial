inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

def Vect.get? (v : Vect α n) (i : Nat) : Option α :=
  match v, i with
  | .nil, _ => none
  | .cons x xs, 0 => some x
  | .cons _ xs, j + 1 => get? xs j

def v : Vect Nat 2 := Vect.cons 1 (Vect.cons 2 Vect.nil)
#eval v.get? 0  -- some 1
#eval v.get? 1  -- some 2
#eval v.get? 2  -- none

structure Finite (n : Nat) where
  val : Nat
  isLt : val < n

def impossible (n : Finite 0) : α := nomatch n

def Vect.get (v : Vect α n) (i : Finite n) : α :=
  match v, i with
  | .nil, j => impossible j
  | .cons x _, ⟨0, _⟩ => x
  | .cons _ xs, ⟨j + 1, h⟩ => get xs ⟨j, (by simp at h; exact h)⟩

#eval v.get ⟨0, by decide⟩  -- 1
#eval v.get ⟨1, by decide⟩  -- 2
-- #eval v.get ⟨2, by decide⟩  -- error: `decide` proved that the proposition is false
