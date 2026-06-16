/-!
The goal of this file is to explain what are monads and how they work.

For that, we will implement a `Result` type that can be used to represent
the success or failure of a computation. Then we will turn it into a monad
by adding specific transformations to its contents.
-/

/--
`Result` is a type called "sum type" (also "tagged union" or "inductive
type") that allows to represent different scenarios of a computation via
its variants. For that reason, those types are are sometimes referred to
as "computational contexts".

In the case of `Result`, there are two variants:
* `Err` which represents a failure and contains an error value of type `ε`.
* `Ok` which represents a success and contains a value of type `α`.
-/
inductive Result (ε : Type) (α : Type) where
  | Err : ε → Result ε α
  | Ok : α → Result ε α

/--
`map` allows you to transform the value inside a computational context
without changing the variant.

If the value is `Ok a`, `map` applies a function `f : α → β` to `a`
and returns `Ok (f a)`. If the value is `Err e`, it returns `Err e`
unchanged.
-/
def Result.map (f : α → β) : Result ε α → Result ε β
  | .Err e => .Err e
  | .Ok a => .Ok (f a)

/--
`seq` allows us to apply a function inside a computational context to a
value inside the same context.

Suppose we have a function `f : α → β → γ` and two values: `x : Result ε α`
and `y : Result ε β`.

Because functions in FP are curried, `f` can be seen as producing a
function `β → γ` after applying `α`. So, appling `map f x` will result
in a `Result ε (β → γ)`. This means we now have a function inside the
`Result` context.

`seq` is used to apply this function-in-a-context to `y`, producing a
`Result ε γ`.

If either `x` or `y` is `Err`, the computation short-circuits and the
first `Err` is returned.
-/
def Result.seq (f : Result ε (α → β)) (x : Unit → Result ε α) : Result ε β :=
  match f, x () with
  | .Err e, _ => .Err e
  | _, .Err e => .Err e
  | .Ok g, .Ok a => .Ok (g a)

/-
`bind` is the operation that allows chaining computations inside a
computational context.

It takes a value `x : Result ε α` and a function `f : α → Result ε β`.

If `x` is `Ok a`, it applies `f` to `a`, producing a new `Result` that
can be either an `Ok` or an `Err`.

If `x` is `Err e`, it returns `Err e` immediately.

This is what allows computations to depend on previous results while
preserving the failure-handling context.
-/
def Result.bind (x : Result ε α) (f : α → Result ε β) : Result ε β :=
  match x with
  | .Err e => .Err e
  | .Ok a => f a

/-
Functor is a class (in the sense of equivalence class) of computational
contexts that have a `map` function that allows us to transform the
values inside the context without changing the context variant itself.

The `map` function takes a function `f : α → β` and a value of type `F α`
and returns a value of type `F β` satisfying the following laws:
* Identity: `map id = id`
* Composition: `map g ∘ map f = map (g ∘ f)`
-/
instance : Functor (Result ε) where
  map := Result.map
namespace Result
theorem map_id (x : Result ε α) : map id x = x := by
  rcases x <;> rfl

theorem map_comp (f : α → β) (g : β → γ) (x : Result ε α) :
  map g (map f x) = map (g ∘ f) x := by
  rcases x <;> rfl
end Result

/-
Applicative is a class (in the sense of equivalence class) of computational
contexts that have two main operations: `pure` and `seq`. These operations
allow us to lift values and functions into the context and apply them to
values in the same context variant.

Because FP is curried, a function `f : α → β → γ` can be seen as a function
`α → (β → γ)`. This means that if we map `f` over a value `x : F α`, we
get a value of type `F (β → γ)`. To apply this function to another value
`y : F β`, we use the `seq` operation, which takes a function from
`F (β → γ)` and applies it to the value in `F β`, producing a value of
type `F γ`.

To lift a value into the context, we use the `pure` operation, which takes
a value of type `α` and returns a value of type `F α` in the context.

`pure` and `seq` must satisfy the following laws:
* Identity: `seq (pure id) x = x`
* Homomorphism: `seq (pure f) (pure x) = pure (f x)`
* Interchange: `seq u (pure y) = seq (pure (fun f => f y)) u`
* Composition: `seq (seq (seq (pure comp) u) v) w = seq u (seq v w)`
Where `comp` is the function composition operator.
-/
instance : Applicative (Result ε) where
  pure := Result.Ok
  seq := Result.seq

theorem seq_pure_id (x : Result ε α) : (pure id) <*> x = x := by
  rcases x <;> rfl

theorem seq_pure_hom (f : α → β) (x : α) :
  (pure f) <*> (pure x) = (pure (f x) : Result ε β) := by
  rfl

theorem seq_pure_interchange (u : Result ε (α → β)) (y : α) :
  u <*> (pure y) = (pure (fun f => f y)) <*> u := by
  rcases u <;> rfl

theorem seq_comp (u : Result ε (β → γ)) (v : Result ε (α → β)) (w : Result ε α) :
  (pure (· ∘ ·) <*> u <*> v <*> w) = (u <*> (v <*> w)) := by
  rcases u <;> rcases v <;> rcases w <;> rfl

/-
Monad is a class (in the sense of equivalence class) of computational
contexts that have a `bind` operation that allows us to chain computations
and change internal structures without leaving the context.

`bind` takes a value `x : F α` and applies a function `f : α → F β` to
its content producing a new value of type `F β`. This new value can be
the same variant as `x` or a different one, depending on the result of
the function `f`.

`bind` must satisfy the following laws:
* Left identity: `pure a >>= f = f a`
* Right identity: `m >>= pure = m`
* Associativity: `(m >>= f) >>= g = m >>= (fun x => f x >>= g)`
-/
instance : Monad (Result ε) where
  bind := Result.bind

theorem bind_left_id (a : α) (f : α → Result ε β) :
  (pure a >>= f) = f a := by
  rfl

theorem bind_right_id (m : Result ε α) :
  (m >>= pure) = m := by
  rcases m <;> rfl

theorem bind_assoc (m : Result ε α) (f : α → Result ε β) (g : β → Result ε γ) :
  ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  rcases m <;> rfl

/-
As a functor, `Result` allows us to transform the value inside the context
without changing the context variant itself. So,
-/
#eval (· + 1) <$> (.Ok 1 : Result String Nat)

/-
As an applicative, `Result` allows us to combine multiple arguments inside
the context.
-/
#eval .Ok (· + ·) <*> .Ok 1 <*> (.Ok 2 : Result String Nat)

/-
As a monad, `Result` allows us to chain computations. As each step
succeeds, the bind operation moves to the next step. If any step fails,
the computation short-circuits and returns the error immediately.
-/
#eval (.Ok 1 : Result String Nat) >>= (fun _ => .Err "failed") >>= (fun x => .Ok (x + 1))

/-
In summary, this is how modern functional programming languages handles
error with no side effects. The `Result` context allows to keep the
computation chain predictable, only two possible outcomes can emerge,
which outcome will depend on the input values.
-/
