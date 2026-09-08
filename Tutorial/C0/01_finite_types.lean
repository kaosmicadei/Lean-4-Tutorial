/-
In proves involving finite sets, it is often useful to have a type that represents the set of
natural numbers less than `n`, or simply `Fin n`. Those are called finite types.

To given an idea why shuch types are useful, consider the definition of a vector (fixed size list).
-/

inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)


/-
If we want to recover a particular element of a vector of length `n`, we can define a `get?` method that takes a vector and an index `i : Nat` and returns an `Option α` type.
-/

def Vect.get? (v : Vect α n) (i : Nat) : Option α :=
  match v, i with
  | .nil, _ => none
  | .cons x xs, 0 => some x
  | .cons _ xs, j + 1 => get? xs j

/-
The `Option` type is necessary because the index `i` may be out of bounds so we need a way to
represent that case. That means we are not checking if the index is in bounds, we are just short-circuiting the computation and returning `none` if the index is out of bounds.
-/

def v : Vect Nat 2 := Vect.cons 1 (Vect.cons 2 Vect.nil)
#eval v.get? 0  -- some 1
#eval v.get? 1  -- some 2
#eval v.get? 2  -- none


/-
We could, of course, add an `if` condition to check if the index is in bounds and return an error if it is not. But that would be a runtime check.

For purpose of proving theorems, we need to be able to check bounds at compile time. That is where finite types come in. A finite type `Fin n` is a pair that holds a natural number `i` and a proof that `i < n`. The compiler can use that proof to ensure the index is in bounds at compile time.
-/

structure Finite (n : Nat) where
  val : Nat
  isLt : val < n

/-
A particular interesting case is when we have `Fin 0`. That's because `Fin 0` represents an empty set of natural numbers, meaning there are no valid indices. We cannot populate a `Fin 0` because there is no index `i` that satisfies `i < 0`.
-/

def impossible (n : Finite 0) : α := nomatch n

/-
`nomatch` is the exact opposite of `match`. While `match` breaks a value down into its possible
constructors, `nomatch` asserts that there are no possible constructors for the given value.

Using `Finite n`, we can define a method `Vect.get` that always returns a valid element of the
vector, because the index is guaranteed to be in bounds at compile time. The `Finite 0` guarantees
that no value can be recovered from a dimension-zero vector.
-/

def Vect.get (v : Vect α n) (i : Finite n) : α :=
  match v, i with
  | .nil, j => impossible j
  | .cons x _, ⟨0, _⟩ => x
  | .cons _ xs, ⟨j + 1, h⟩ => get xs ⟨j, (by simp at h; exact h)⟩

/-
`Vect α n` and `Finite n` have the same length `n`. This means that for every element in the
vector, there is a corresponding valid index in the finite type, and vice versa. If we try to
access any index out of bounds using `Vect.get`, instead of the function returning an
`Option` or raising an error, it will be the proof of the proposition `i < n` that fails to be
constructed, resulting in a compile-time error.
-/

#eval v.get ⟨0, by decide⟩  -- 1
#eval v.get ⟨1, by decide⟩  -- 2
-- #eval v.get ⟨2, by decide⟩  -- error: `decide` proved that the proposition `2 < 2` is false

/-
Because the finite type as a useful type, Lean already implements it as `Fin n`, and provides
various utility functions and theorems for working with it.
-/
