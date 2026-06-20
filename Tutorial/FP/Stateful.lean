/-!
The goal of this file is to show how monads can be used to model mutability
in FP. We will define the what is known as state monad and use it to
implement a toy-model stack-based virtual machine.
-/

/--
A stateful computation, shorted as `State`, is a structure that holds a
function that takes an initial state of type `σ` and produces a pair
composed by a returning value of type `α` and a new state of type `σ`.
-/
structure State (σ : Type) (α : Type) where
  run : σ → (α × σ)

namespace State
/--
`map` applies a function `f` to the returning value of a stateful
computation `s` leaving the returned state unchanged.
-/
def map (f : α → β) (s : State σ α) : State σ β :=
  ⟨fun s' => Prod.map f id (s.run s')⟩

/--
`pure` creates a stateful computation that returns a given value `x`
without modifying the initial state.
-/
def pure (x : α) : State σ α :=
  ⟨fun s => (x, s)⟩

/--
`seq` applies a function returned by a stateful computation `f` to the
returning value of another stateful computation `x`, threading the state
through both computations.
-/
def seq (f : State σ (α → β)) (x : Unit → State σ α) : State σ β :=
  ⟨fun s =>
    let (g, s') := f.run s
    let (a, s'') := (x ()).run s'
    (g a, s'')⟩

/--
`bind` allows to chain stateful computations by using the returning value
of the previous computation as input for the next one, threading the state
through both computations.
-/
def bind (x : State σ α) (f : α → State σ β) : State σ β :=
  ⟨fun s =>
    let (a, s') := x.run s
    (f a).run s'⟩
end State

/-
Functor is a class (in the sense of equivalence class) of computational
contexts that have a `map` function that allows us to transform the
values inside the context without changing the context variant itself.

The `map` function takes a function `f : α → β` and a value of type `F α`
and returns a value of type `F β` satisfying the following laws:
* Identity: `map id = id`
* Composition: `map g ∘ map f = map (g ∘ f)`
-/
instance : Functor (State σ) where
  map := State.map

theorem map_id (x : State σ α) : State.map id x = x := by
  cases x <;> rfl

theorem map_comp (f : α → β) (g : β → γ) (x : State σ α) :
    State.map g (State.map f x) = State.map (g ∘ f) x := by
  cases x <;> rfl

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
instance : Applicative (State σ) where
  pure := State.pure
  seq := State.seq

theorem seq_id (x : State σ α) : (pure id) <*> x = x := by
  cases x <;> rfl

theorem seq_hom (f : α → β) (x : α) :
  (pure f : State σ (α → β)) <*> (pure x) = pure (f x) := by
  rfl

theorem seq_inter (u : State σ (α → β)) (y : α) :
  u <*> (pure y) = (pure fun f => f y) <*> u := by
  cases u <;> rfl

theorem seq_comp (u : State σ (β → γ)) (v : State σ (α → β)) (w : State σ α) :
  ((pure (· ∘ ·)) <*> u <*> v <*> w) = (u <*> (v <*> w)) := by
  cases u <;> cases v <;> cases w <;> rfl

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
instance : Monad (State σ) where
  bind := State.bind

theorem bind_left_id (a : α) (f : α → State σ β) :
  (pure a >>= f) = f a := by
  rfl

theorem bind_right_id (m : State σ α) :
  (m >>= pure) = m := by
  cases m <;> rfl

theorem bind_assoc (m : State σ α) (f : α → State σ β) (g : β → State σ γ) :
  ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  cases m <;> rfl

/-
With that, we have two ways to chain stateful computations, using `seq`
-/
#eval ((· + ·) <$> (pure 1) <*> (pure 1 : State Unit Nat)).run ()
/-
or using `bind`
-/
#eval ((pure 1 : State Unit Nat) >>= (fun x => pure 1 >>= fun y => pure (x + y))).run ()
/-
But none of them are practical.

In fact, the main advantage of monads is the do-notation which allows to
write chained computations in a more readable way.
-/
def computation_example : State Unit Nat := do
  let x ← pure 1
  let y ← pure 1
  pure (x + y)

#eval computation_example.run ()
/-
This version looks much better and closer to what people would write in
an imperative language. I also looks like the stack-based computation.
-/


/--
A stack is a stateful computation that holds a list of values to be
consumed by the computation. That allows us to chain computations with
different number of arguments.
-/
abbrev Stack α := State (List α)

/--
`put` pushes a value `x` to the top of the stack leaving the return value
empty.
-/
def put (x : α) : Stack α Unit :=
  ⟨λs ↦ ((), x :: s)⟩

/--
`get` moves the top value of the the stack to the return value leaving
the rest of the stack unchanged.
-/
def get [Inhabited α] : Stack α α :=
  ⟨λs ↦ (s.head!, s.tail)⟩

theorem put_get [Inhabited α] (x : α) : (put x >>= λ_ ↦ get) = pure x := by
  rfl

namespace VirtualMachine
/-
We can use the `Stack` monad to model a stack-based virtual machine. For
example, we can define a program that pushes two numbers to the stack,
retrieves them and returns their sum.
-/

def program1 : Stack Nat Nat := do
  put 1
  put 2
  let a ← get
  let b ← get
  pure (a + b)

#eval program1.run []

/-
To make the program more modular, we can define a function `add` that
retrieves two numbers from the stack and returns their sum. Then we can
define a new program that pushes two numbers to the stack, calls `add`
and returns the result.
-/

/-
We define two helper functions `call` and `ret` to make the code closer
to what we would write in an assembly language. `call` takes a stackful
computation and executes it, while `ret` takes a value and returns it
as the result of the computation.
-/
def call : Stack α β → Stack α β := id
def ret (x : α) : Stack α α := pure x

def add : Stack Nat Nat := do
  let a ← get
  let b ← get
  ret (a + b)

def program2 : Stack Nat Nat := do
  put 1
  put 2
  let r ← call add
  ret r

#eval program2.run []

/--
We can prove that `program1` and `program2` are equivalent by showing that
they produce the same result for any initial stack.
-/
theorem program1_eq_program2 : program1 = program2 := by
  rfl
end VirtualMachine
