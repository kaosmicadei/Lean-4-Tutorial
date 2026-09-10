/-
I think a good way to learn Lean is by creating your own version of the natural numbers. This gives
a good view on: inductive types, constructors, pattern matching, recursion, and allows to explore
basics of theorem proving with proves that forces you to think step by step.

This file goes shows a basic construction of the natural numbers, explains the use of pattern matching and recursion to implement addition and multiplication, and some unnecessarily verbose
step-by-step proofs so the reader can follows the reasoning process.

A good reminder is that Lean is designed to be used interactively, that means the proves here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.

# Definition of Natural Numbers
Inductive types are types with more than one constructor. If you are coming from programming
languages like C++, you will be familiar with the concept. If you are coming from languages like
Python, it basically means your class have multiple `__init__` methods, each one creating a
different instance of the same class.

So, with that in mind, let's get it started!

According to Peano's axioms, the natural type has two constructors: zero and the successor function.
-/

inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ

/-
By definition, `zero` and `succ` produces different objects of type `ℕ`. And we can use this
structural difference to prove one of the Peano's axioms:

> Zero is not the successor of any natural number.
-/

theorem ℕ.zero_ne_succ (n : ℕ) : ℕ.zero ≠ ℕ.succ n := by
  dsimp          -- expands definitions, in this case the definition of ≠
  unfold Not     -- replaces ¬ with its definition
  intro h        -- moves the proposition `ℕ.zero = ℕ.succ n` to the context under the name `h`
  contradiction  -- verifies the structural contradiction of `ℕ.zero` and `ℕ.succ`

/-
The proof above is too verbose on purpose, to show the step-by-step reasoning in Lean. In practice,
Lean's compiler is way more powerful and could infer the structural contradiction automatically
during simplification. That would look like this:

    theorem ℕ.zero_ne_succ' (n : ℕ) : ℕ.zero ≠ ℕ.succ n := by simp

But, for someone learning, it's nice to see the mechanics behind the magic. Even if all the
compiler details are still hidden from the user.

We can also use the structural difference of the constructors to prove another Peano's axiom:

> If the successor of m is equal to the successor of n, then m is equal to n.
-/

theorem ℕ.succ_injective (m n : ℕ) (h: ℕ.succ m = ℕ.succ n) : m = n := by
  injection h

/-
If different constructors produce different objects, the same constructor applied to different
arguments can only produce the same object if the arguments themselves are equal. This can be
formally captured by the `injection` tactic.

# Addition between Natural Numbers
The addition between two natural numbers has two rules:
* `0 + n = n`
* `succ m + n = succ (m + n)`

Because Lean is a functional programming language, we can abuse of pattern matching and recursion
to define `add(m, n)`. Think of pattern matching as a more descriptive if-else list that uses deconstructor statements, and recursion as a structural way to perform loops.
-/

def ℕ.add (m n : ℕ) : ℕ :=
  match m with
  | .zero => n
  | .succ m' => .succ (ℕ.add m' n)

/-
Now that we had defined the addition function for natural numbers, it's conventient to instantiate
our `ℕ` type to the `Add` typeclass. That will allow us to use the `+` notation for addition and
write `m + n` instead of `ℕ.add m n`.

In functional programming languages like Lean, typeclasses allow to create polymorphism by defining generic interfaces that can be implemented for different types. `Add`, for example, allows to any
type implementing some sort of addition operation to use the `+` operator with the only constraint
being the addition must be a monoid, `+ : A × A → A`.
-/

instance : Add ℕ where
  add := ℕ.add

/-
The definition of a function can be used by the Lean's compiler to simplify expressions and prove theorems automatically. But they cannot be used as propositions directly. And be able to be used as
a proposition is important so we can rewrite expressions.

In order to use the definition of addition as propositions, we need to define the cases as separated
theorems. Think about theorems in Lean as functions that return propositions.
-/

theorem ℕ.zero_add (n : ℕ) : .zero + n = n := by trivial
theorem ℕ.succ_add (m n : ℕ) : .succ m + n = .succ (m + n) := by trivial

/-
Because this propositions can be derived directly from the definitions, we can be trivially proven using the `trivial` tactic.

To name the theorems, I'm using the Mathlib convention where we name the mathematical fact and name
the main objects. In this case, when we have `0 + n`, the main object is zero and the mathematical
fact is the addition, so we name the theorem `zero_add`. The order also have a utility here, it
serves to show which one appears first in the expression.

## Properties of Addition


### Associativity of addition
-/

theorem ℕ.add_assoc (m n k : ℕ) : (m + n) + k = m + (n + k) := by
  induction m with
  | zero => rw [ℕ.zero_add, ℕ.zero_add]  -- by definition, `trivial` would also work here
  | succ m' ih => rw [ℕ.succ_add, ℕ.succ_add, ℕ.succ_add, ih]

/-
### Commutativity of addition
-/

theorem ℕ.add_zero (n : ℕ) : n + .zero = n := by
  induction n with
  | zero => rw [ℕ.zero_add]  -- by definition, `trivial` would also work here
  | succ n' ih => rw [ℕ.succ_add, ih]

theorem ℕ.add_succ (m n : ℕ) : m + .succ n = .succ (m + n) := by
  induction m with
  | zero => rw [ℕ.zero_add, ℕ.zero_add]  -- by definition, `trivial` would also work here
  | succ m' ih => rw [ℕ.succ_add, ℕ.succ_add, ih]

theorem ℕ.add_comm (m n : ℕ) : m + n = n + m := by
  induction m with
  | zero => rw [ℕ.zero_add, ℕ.add_zero]
  | succ m' ih => rw [ℕ.succ_add, ℕ.add_succ, ih]

/-
# Multiplication of Natural Numbers
-/

def ℕ.mul (m n : ℕ) : ℕ :=
  match m with
  | .zero => .zero
  | .succ m' => n + ℕ.mul m' n

instance : Mul ℕ where
  mul := ℕ.mul

theorem ℕ.zero_mul (n : ℕ) : .zero * n = .zero := by trivial
theorem ℕ.succ_mul (m n : ℕ) : .succ m * n = n + (m * n) := by trivial

-- Commutativity of multiplication
theorem ℕ.mul_zero (n : ℕ) : n * .zero = .zero := by
  induction n with
  | zero => trivial
  | succ n' ih => rw [ℕ.succ_mul, ih, ℕ.add_zero]

theorem ℕ.mul_succ (m n : ℕ) : m * .succ n = m * n + m := by
  induction m with
  | zero => trivial
  | succ m' ih => rw [ℕ.succ_mul, ℕ.succ_mul, ih, ℕ.succ_add, ℕ.add_succ, ℕ.add_assoc]

theorem ℕ.mul_comm (m n : ℕ) : m * n = n * m := by
  induction m with
  | zero => rw [ℕ.zero_mul, ℕ.mul_zero]
  | succ m' ih => rw [ℕ.succ_mul, ih, ℕ.mul_succ, ℕ.add_comm]

-- Distrubutive
theorem ℕ.mul_add (m n k : ℕ) : m * (n + k) = m * n + m * k := by
  induction m with
  | zero => trivial
  | succ m' ih =>
    rw [ℕ.succ_mul, ℕ.succ_mul, ℕ.succ_mul, ih]
    rw [ℕ.add_comm k, ℕ.add_assoc, ℕ.add_comm k]
    rw [← ℕ.add_assoc, ← ℕ.add_assoc, ← ℕ.add_assoc]

theorem ℕ.add_mul (m n k : ℕ) : (m + n) * k = m * k + n * k := by
  induction m with
  | zero => trivial
  | succ m' ih => rw [ℕ.succ_add, ℕ.succ_mul, ℕ.succ_mul, ih, ← ℕ.add_assoc]

-- Associativity of multiplication
theorem ℕ.mul_assoc (m n k : ℕ) : (m * n) * k = m * (n * k) := by
  induction m with
  | zero => trivial
  | succ m' ih => rw [ℕ.succ_mul, ℕ.succ_mul, ℕ.add_mul, ih]
