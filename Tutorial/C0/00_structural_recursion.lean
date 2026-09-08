section RecursionAndTermination
/-
Since Lean is a functional programming language, we cannot use loops to define functions and we
need to use recursion instead.

The basic example of recursion is the Fibonacci function, which is defined as follows:
-/

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-
The Fibonacci function is an example of structural recursion. That means the compiler can verify the
termination by checking that the argument in the recursive is in fact reducing. In this case, the
argument is `n` and the recursive calls are `fib n` and `fib (n + 1)`, which are both smaller than
`n + 2`.

In Lean, when a recursive termination is not obvious for the compiler, we have to prove the
termination ourselves indication which arguments are decreasing and how.

One example of non-structural recursion is the Euclidean algorithm for computing the greatest
common divisor (gcd) of two natural numbers. The gcd is defined as follows:
-/

def gcd (a b : Nat) : Nat :=
  if _h : b = 0 then
    a
  else
    gcd b (a % b)
termination_by b
decreasing_by
  -- if b≠0 then a % b < b
  have h1 : 0 < b := Nat.pos_of_ne_zero _h  -- non-zero naturals are positive
  have h2 : a % b < b := Nat.mod_lt a h1    -- the modulus is strictly smaller than the divisor
  exact h2

/-
Here, the termination is associated with the second argument `b`, which must to decrease in the
recursive call. The proof of termination is done by showing that `a % b` is strictly smaller than
`b` when `b ≠ 0`.

For a human, such condition is obvious, but the Lean compiler needs to be convinced by a formal
proof to accept the definition of `gcd` will in fact terminate.
-/
end RecursionAndTermination


section Vectors
/-
Another example of structural recursion in Lean are lists and vectors. A vector is a list with a
fixed legnth. Because Lean is a type dependent language, the length of a vector can be encoded in
its type. For example, a vector of length 3 of natural numbers has the type `Vect Nat 3`. The
definition of vectors is as follows:
-/

inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

/-
A `Vect.nil` corresponds to a vector of dimension zero. The `Vect.cons` constructor, prepends an
element of type `α` to a vector of dimension `n`, producing a vector of dimension `n + 1`.
-/

#check (Vect.nil : Vect Nat _)  -- will be inferred as `Vect Nat 0`

def v : Vect Nat 2 := Vect.cons 1 (Vect.cons 2 Vect.nil)
#check Vect.cons 3 v  -- will be inferred as `Vect Nat 3`

/-
One of the main advantages of using vectors instead of lists is that we can define functions that
are guaranteed to be well-defined by the type system, which simplifies its implementation. For
example, the inner product of two vectors is only defined when both vectors have the same
dimension. By coercing the dimension in the type, we can define a inner product for arbitrary
dimensions without having to worry about mismatched lengths. We can do that using structural
recursion on the vector type, as follows:
-/

def inner_prod (u v : Vect Nat n) : Nat :=
  match u, v with
  | .nil, .nil => 0
  | .cons x xs, .cons y ys => x * y + inner_prod xs ys

/-
There is no need to implement the cases of `u = cons x xs` and `v = nil` or the other way around
because those cases will produce a mismatched dimensions right at the type level.
-/

def v0 : Vect Nat 2 := Vect.cons 1 (Vect.cons 2 Vect.nil)
def v1 : Vect Nat 3 := Vect.cons 1 (Vect.cons 2 (Vect.cons 3 Vect.nil))
def v2 : Vect Nat 3 := Vect.cons 4 (Vect.cons 5 (Vect.cons 6 Vect.nil))

--#eval inner_prod v0 v1  -- error: mismatched dimensions
#eval inner_prod v1 v2

/-
The definition of the inner product as done is limited to vectors of natural numbers. But we can
generalise it to vectors of different types by ensuring the types used have:
* a multiplication operation,
* an addition operation, and
* a zero element.

Such generalisation is done by adding typeclass constraints to the definition of the function, as
follows:
-/

def inner_prod' [Mul α] [Add α] [Zero α] (u v : Vect α n) : α :=
  match u, v with
  | .nil, .nil => 0
  | .cons x xs, .cons y ys => x * y + inner_prod' xs ys

def u1 : Vect Float 3 := Vect.cons 1.0 (Vect.cons 2.0 (Vect.cons 3.0 Vect.nil))
def u2 : Vect Float 3 := Vect.cons 4.0 (Vect.cons 5.0 (Vect.cons 6.0 Vect.nil))

#eval inner_prod' u1 u2
--#eval inner_prod' v1 u1  -- error: mismatched types
end Vectors


section ListManipulation
/-
Our final example of structural recursion is the manipulation of lists.

The most basic list operation is the `map` function, which applies a function `f` to each element
of a list `xs`, mapping a list of type `List α` to a list of type `List β`.
-/

def map (f : α → β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x :: xs => f x :: map f xs

/-
Here, the compiler can verify the termination of the `map` function because the recursive call is
done on the tail of the list, which is strictly smaller than the original list.

The `map` function has several properties that can be proved by structural induction on the list `
xs`. A few examples are:
* Length: `(map f xs).length = xs.length`
* Identity: `map id xs = xs`
* Associativity: `map f (xs ++ ys) = map f xs ++ map f ys`
* Composition: `map g (map f xs) = map (g ∘ f) xs`
-/

theorem map_length (f : α → β) (xs : List α) : (map f xs).length = xs.length := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>  -- ih : induction hypothesis
    simp [map]
    rw [ih]

theorem map_id (xs : List α) : map id xs = xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    simp [map]
    rw [ih]

theorem map_associative (f : α → β) (xs ys : List α) : map f (xs ++ ys) = map f xs ++ map f ys := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    simp [map]
    rw [ih]

theorem map_comp (f : α → β) (g : β → γ) (xs : List α) : map g (map f xs) = map (g ∘ f) xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    simp [map]
    rw [ih]

/-
Those theorems are more powerful that regular unit tests because they test the logic of the
function regardless the inputs.

For example, the `map_comp` theorem proves that the composition of two maps is equivalent to a
single map with the composition of the two functions, for any list `xs`. Because that proves is
valid for any two functions `f` and `g` with no side effects, and any list `xs`, a compiler can use
it to optimise the code by replacing two maps with a single map with the composition of the two
functions (as long as the functions have no side effects).

Another interesting list operation is the `fold` function, which projects a list of type `List α`
into a single value of type `β` by applying a binary function `f : β → α → β` recursively to each
element of the list, starting with an initial value `acc : β`.
-/

def fold (f : β → α → β) (acc : β) (xs : List α) : β :=
  match xs with
  | [] => acc
  | x :: xs => fold f (f acc x) xs

/-
Again, the compiler uses structural recursion of the list to verify the termination of the `fold` function. The `fold` function has several properties that can be proved by structural induction on the list `xs`. A few examples are:
* Neutral element: if `f e x = x` for all `x`, then `fold f e (x::xs) = fold f x xs`
* Associativity: `fold f z (xs ++ ys) = fold f (fold f z xs) ys`
* Map composition: `fold f z (map g xs) = fold (λ acc x => f acc (g x)) z xs`
-/

theorem fold_neutral (f : α → α → α) (e x : α) (xs : List α) :
  f e x = x → fold f e (x::xs) = fold f x xs := by
  intro h
  simp [fold]
  rw [h]

theorem fold_associative (f : β → α → β) (acc : β) (xs ys : List α) :
  fold f acc (xs ++ ys) = fold f (fold f acc xs) ys := by
  induction xs generalizing acc with
  | nil => trivial
  | cons x xs ih =>
    simp [fold]
    specialize ih (f acc x)
    exact ih

theorem fold_map (f : α → β) (g : γ → β → γ) (acc : γ) (xs : List α) :
  fold g acc (map f xs) = fold (fun a x => g a (f x)) acc xs := by
  induction xs generalizing acc with
  | nil => trivial
  | cons x xs ih =>
    simp [map, fold]
    rw [ih]

/-
Because `fold` can receive any binary function `f`, the inductive proofs of its properties require the use of `generalizing` to allow the induction hypothesis to be applied to any accumulator value `acc`, which includes the result of the function `f` applied to the head of the list and the accumulator. Those generalisations can be manually replaced using the `specialize` tactic, which allows to apply the induction hypothesis to a specific value of `acc`, or they can be automatically inferred by the compiler when using `rw` to replace the goal with the induction hypothesis.
-/

end ListManipulation
