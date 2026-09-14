/-
> 🚨*Disclaimer*🚨 This file was written following the literal programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

If writing your own natural number types is a good way to start to learn Lean, then learning about
how to use logical operations and existential quantifiers is the best way to learn more about
tactics and proof strategies in Lean.

This file shows a few examples of logical statements and their proofs before diving into some proofs
involving quantifiers (∃ and ∀) and natural numbers.

As a reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.

# Logical operations

## Implication
In the Lean syntax, when we are defining functions, `A → B` represents a map from `A` to `B`.

However, thanks to the Curry-Howard correspondence, a function `P → Q` can be interpreted as a logical implication `P → Q` because it can be read as:

> Taking a proof of `P` and applying the function `P → Q` to it, we obtain a proof of `Q`.

A simple example is the identity function.
-/

example (P : Prop) : P → P := by
  exact id

/-
The `id` function takes an input value and returns the same value as output. When this value is a
proof to the proposition `P`, it returns the same proof as output.

## Negation
`Not P` or `¬P` represents the negation of a proposition `P`. Since Lean uses constructive logic, `¬P` requires to construct a proof that `P` is false. That means, `¬P` takes a proposition `P` and
returns a proof of `False`. Or in other words, `¬P` is defined as `P → False`.

Now, here is the catch. `False` is an empty type. That means, there is no valid construction of a value of type `False`. So, an implication `P → False` holds only if `P` cannot be constructed either.

For example, think about the case in the natural numbers where `0 ≠ succ n`. Since zero and the
successor are two distinct constructors of the natural numbers, there is no valid construction such
that `0 = succ n`. Therefore, `0 = succ n` cannot be constructed. Therefore, `0 = succ n` implies `False`.

The Lean compiler, however, is way more powerful than that. It can handle more abstract reasoning
like working with opaque propositions. That is the case of the contrapositive.
-/

theorem contrapositive (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  intro h1
  unfold Not at *
  intro p
  have q := h p
  exact h1 q

/-
In the `contrapositive` example, we have two hypotheses: `h : P → Q` and `h1 : Q → False`. And we
want to show that `P → False`. The proposition `P` is introduced to the context as the variable
`p`. We recover the proposition `Q` by applying the hypothesis `h` to `p`, obtaining `q := h p`.
Finally, we apply `h1` to `q` to derive `False`.

## Conjunction and Disjunction
Together with implication and negation, conjunction (`∧`, "and") and disjunction (`∨`, "or") are
the building blocks of propositional logic.

In Lean, conjunction and disjunction are represented using two types of data structures:
* a "pair type" or product type for conjunction ("A and B"),
* a "sum type" or coproduct type for disjunction ("A or B").

The difference between them is that a product type is like a tuple and holds both values at the
same time. A sum type, on the other hand, is separated in cases where each case holds one of the possible values.

To give a practical example, let's look at the commutativity of conjunction and disjunction.
-/

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨p, q⟩ := h
  exact And.intro q p

/-
Here we have used `obtain` to break down the hypothesis `h : P ∧ Q` into its components `p : P` and
`q : Q`. The angle brackets `⟨ ⟩` (`\<` and `\>`) are used to pattern match on the components of  a
structure.

Now, let's see the difference when proving the commutativity of disjunction.
-/

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl p => exact Or.inr p
  | inr q => exact Or.inl q

/-
Here we have used `cases ... with` to split the hypothesis `h : P ∨ Q` into its possible cases.
The `inl` constructor (`intro left`) corresponds to the case where `P` holds, and the `inr`
constructor (`intro right`) corresponds to the case where `Q` holds.

Let's see an example where both logical operators appear. Let's prove the distributivity of conjunction over disjunction.
-/

example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  intro abc
  obtain ⟨a, bc⟩ := abc
  cases bc with
  | inl b => exact Or.inl (And.intro a b)
  | inr c => exact Or.inr (And.intro a c)

/-
Here, the first hypothesis, `abc : A ∧ (B ∨ C)` is a conjunction of `A` and `B ∨ C`. We use
`obtain ⟨a, bc⟩ := abc` to break it down into `a : A` and `bc : B ∨ C`. Then, we use
`cases bc with` to handle the cases where `B` and `C` hold separately. That way, we can prove
either `A ∧ B` or `A ∧ C`.

Now, let's see an example of proof that mixes logical operators with natural numbers.
-/

example (n m : Nat) : m * n = 0 → m = 0 ∨ n = 0 := by
  intro h
  cases m with
  | zero =>
    left
    trivial
  | succ m' =>
    right
    rw [Nat.add_mul, Nat.one_mul, Nat.add_eq_zero_iff] at h
    exact h.right

/-
Here, the first thing that we notice is that we don't need to use `induction`. That is because we
can use the fact that zero is not a successor of any natural number to conclude, in the second
case, that `n = 0`.

The key part here are the tactics `left` and `right`. They allow us to specify which side of the
goal we want to follow.

In the first case, `m = 0`, so we follow the left side of the disjunction, while in the second
case, `m = succ m'` and therefore `n` must be zero. So we follow the right side of the disjunction.


## Existential Quantifier
-/

-- Introduces the existential quantifier (∃).
-- Nonzero natural numbers have a predecessor
example (n : Nat) : n ≠ 0 → ∃ k : Nat, n = k + 1 := by
  intro h
  cases n with
  | zero => contradiction
  | succ n' => exists n'

-- Shows how to combine existential quantifiers with conjunctions.
-- Divisibility property for natural numbers
example (a b c : Nat) : a ∣ b ∧ a ∣ c → a ∣ (b + c) := by
  intro h
  obtain ⟨hab, hac⟩ := h
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hac
  rw [hk, hl, ← Nat.mul_add]
  exists (k + l)

-- Definition of even and odd numbers using existential quantifiers.
def Even (n : Nat) := ∃ k : Nat, n = 2*k
def Odd (n : Nat) := ∃ k : Nat, n = 2*k + 1

theorem succ_even_to_odd (n : Nat) : Even n → Odd (n + 1) := by
  intro h
  unfold Even at h
  obtain ⟨k, hn⟩ := h
  rw [hn]
  unfold Odd
  exists k

theorem succ_odd_to_even (n : Nat) : Odd n → Even (n + 1) := by
  intro h
  unfold Odd at h
  obtain ⟨k, hn⟩ := h
  rw [hn]
  unfold Even
  exists (k + 1)

/-
## Universal Quantifier
-/

-- Introducing the universal quantifier (∀)
-- Every natural number is either even or odd
example : ∀ (n : Nat), Even n ∨ Odd n := by
  intro n
  induction n with
  | zero =>
    left
    exists 0
  | succ n' ih =>
    cases ih with
    | inl h =>
      right
      exact succ_even_to_odd n' h
    | inr h =>
      left
      exact succ_odd_to_even n' h

-- No natural number is both even and odd
example : ∀ (n : Nat), ¬(Even n ∧ Odd n) := by
  intro n
  unfold Not
  intro h
  obtain ⟨he, ho⟩ := h
  unfold Even at he
  unfold Odd at ho
  obtain ⟨k, hk⟩ := he
  obtain ⟨l, hl⟩ := ho
  have h1 : n % 2 = 0 := by
    rw [hk, Nat.mul_mod_right]
  have h2 : n % 2 = 1 := by
    rw [hl, Nat.add_mod, Nat.mul_mod_right, Nat.one_mod]
  have h3 : 0 = 1 := by
    rw [← h1, ← h2]
  contradiction

-- Sum of two odd numbers is even
example (m n : Nat) : Odd m ∧ Odd n → Even (m + n) := by
  intro h
  obtain ⟨hm, hn⟩ := h
  unfold Odd at hm hn
  obtain ⟨k, hk⟩ := hm
  obtain ⟨l, hl⟩ := hn
  rw [hk, hl]
  unfold Even
  exists (k + l + 1)
  rw [Nat.add_assoc, Nat.add_comm 1, Nat.add_assoc]
  rw [← Nat.add_assoc, Nat.mul_add, Nat.mul_add]
