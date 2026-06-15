/-
The goal of this file is to show how formal verification can be used to
prove code optimisation techniques, such as fusion and deforestation. We
will define two common higher-order functions, `map` and `fold`, and then
prove that they can be fused together to eliminate repeat traversals of
the list.

We want to prove two theorems:
1. Fusion: A sequence of `map` operations can be fused into a single `map`
   with a composed function.
2. Deforestation: A `map` followed by a `fold` can be fused into a single
   `fold` with a composed function.
-/

/--
The `map` function takes a function `f : α → β` and a list of type `α`,
and applies `f` to each element of the list, returning a new list of type
`β`.

The `map` function has the following invariants:
* It preserves the length of the list: `length (map f xs) = length xs`.
* It preserves the order of the elements:
  `map f (xs ++ ys) = map f xs ++ map f ys`.
* It is composable: `map g (map f xs) = map (g ∘ f) xs`.

The composability invariant is particularly important because it allows
us to create complex transformations by composing simpler ones.
-/
def map (f : α → β) : List α → List β
  | [] => []
  | a::as => f a :: map f as

/--
Fold (or reduce) is a common operation for aggregation. It takes a binary
function `f : β → α → β`, an initial accumulator value `acc : β`, and a
list of type `α`, and processes the list from left to right, applying `f`
to the accumulator and each element of the list, returning a result of
type `β`.

The `fold` function has the following invariants:
* It is associative: `fold f acc (xs ++ ys) = fold f (fold f acc xs) ys`.
* It has an identity element: if there exists an element `e` such that
  `f e x = x` for all `x`, then `fold f e (x::xs) = fold f x xs`.
* It is composable with
  `map`: `fold f acc (map g xs) = fold (λa ↦ (f a) ∘ g) acc xs`.

The composability with `map` invariant is crucial for deforestation, as
it allows us to fuse `map` and `fold` together, eliminating intermediate
lists and reducing the number of traversals of the list.
-/
def fold (f : β → α → β) (acc : β) : List α → β
  | [] => acc
  | x :: xs => fold f (f acc x) xs

-- Let's see some examples.
#eval map (fun x => x + 1) [1, 2, 3]
#eval fold (fun acc x => acc + x) 0 [1, 2, 3]

/--
Two functions `f : α → β` and `g : β → γ` are composable if they don't
have side effects.

If `f` and `g` are composable, then mapping `f` over a list `xs : List α`
and then mapping `g` over the result is the same as mapping the composition
`g ∘ f` over `xs`.
-/
theorem fusion (f : α → β) (g : β → γ) (xs : List α) :
  map g (map f xs) = map (g ∘ f) xs := by
  induction xs with
  | nil => trivial     -- mapping over an empty list must return an empty list
  | cons a as ih =>    -- ih : induction hypothesis for the tail of the list
     simp [map] at *
     rw [ih]

/--
Two functions `f : α → β` and `g : γ → β → γ` are composable if they don't
have side effects.

If `f : α → β` and `g : γ → β → γ` are composable functions, given an
initial value `acc : γ` and a list `xs : List α`, folding `g` over the
result of mapping `f` is the same as folding a function `λa.λx. g a (f x)`
over `xs` with the same initial value `acc`.
-/
theorem deforastation (f : α → β) (g : γ → β → γ) (acc : γ) (xs : List α) :
  fold g acc (map f xs) = fold (fun a x => g a (f x)) acc xs := by
  induction xs generalizing acc with  -- acc can be results from previous iterations
  | nil => trivial   -- operations over an empty list must return the initial value
  | cons a as ih =>  -- ih : induction hypothesis for the tail of the list
     simp [map, fold] at *
     rw [ih]

/-
This concludes our goal. We have successfully proved that mapping and
folding composable functions can be merged into a single traversal
operation.

Fusion and deforestation are two of the reasons that make iterators so
powerful. They allow us to express complex transformations by composing
simple ones, while also allowing the compiler to optimize the code by
eliminating intermediate data structures and reducing the number of
traversals of the list.
-/
