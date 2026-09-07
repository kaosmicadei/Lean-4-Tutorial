inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

def Vect.get? : Vect α n → Nat → Option α
  | .nil, _ => none
  | .cons x xs, 0 => some x
  | .cons _ xs, i + 1 => get? xs i

structure Finite (n : Nat) where
  val : Nat
  isLt : val < n

#eval (⟨2, (by trivial)⟩ : Finite 3)

def impossible (n : Finite 0) : α := nomatch n

def Vect.get : Vect α n → Finite n → α
  | .nil, i => nomatch i
  | .cons x xs, ⟨0, _⟩ => x
  | .cons x xs, ⟨i + 1, h⟩ => get xs ⟨i, (by simp at h; assumption)⟩

def test : Vect String 3 := Vect.cons "apple" (Vect.cons "banana" (Vect.cons "cherry" Vect.nil))
#eval test
#eval test.get ⟨2, by decide⟩

--#eval Vect.nil.get ⟨2, by decide⟩
