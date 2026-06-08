/-
The goal of this file is to show how formal verification can be used to prove the
correctness of a simple compiler. We will define a toy expression language and
a minimal stack machine, and then prove that the compiler correctly translates
expressions into instructions for that machine.

For simplicity, our stack machine will only support natural numbers and two
instructions: `push n` and `add`. The `push n` instruction will push a natural
number `n` onto the stack, and the `add` instruction will pop the top two
elements of the stack, add them together, and push the result back onto the
stack. Our expression language will mirror those operations having
_constant numbers_ and _addition operation_.

We then define three main functions:
* `eval` which evaluates an expression to a natural number.
* `compile` which compiles an expression into a list of instructions for our
  stack machine.
* `run` which executes a list of instructions on a stack and returns the resulting
  stack.

The main theorem we want to prove is that running the compiled code on an empty
stack will yield a stack with a single element which is the result of evaluating
the expression. In other words, we want to prove the following invariant:

> For all expressions `e` and stacks `s`, running the compiled code of `e` on `s`
> should yield a stack with a single element which is the result of evaluating
> `e` on `s`.
-/

section StackMachine
/-
We start by defining our stack machine which is composed of:
* A `Stack` data structure.
* A set of instructions (in our case, `push` and `add`).
* A `run` function that executes a list of instructions on a stack.
-/

/--
A stack is a simple data structure that allows adding and removing elements
in a last-in, first-out (LIFO) manner. It has two main operations:
* `push` which adds an element to the top of the stack.
* `pop` which removes the top element of the stack and returns it along with the
  rest of the stack.

Those two operations hold the following invariant:
> Pushing an element and then popping it should return the original stack and the
> pushed element.

In formal terms:
> ∀ a : α, ∀ s : Stack α, pop (push a s) = some ⟨a, s⟩.
-/
structure Stack α where
  data : List α

/--
It is convenient to define an easy way to initialise an empty stack.
-/
def emptyStack : Stack α := ⟨[]⟩

/--
The `push` function adds an element of type `α` on top of a stack `s`.
-/
def Stack.push (a : α) (s : Stack α) : Stack α := ⟨a::s.data⟩

/--
The `pop` function removes the top element of the stack and returns it along
with the rest of the stack, which can be used later. If the stack is empty,
it returns `none`.
-/
def Stack.pop (s : Stack α) : Option (α × Stack α) :=
  match s.data with
  | [] => none
  | a::rest => some ⟨a, ⟨rest⟩⟩

/--
Pushing an element to a stack and then popping it must return the original stack
and the pushed element.
-/
theorem Stack.pop_push (a : α) (s : Stack α) : (s.push a).pop = some ⟨a, s⟩ := by
  rw [Stack.push, Stack.pop]   -- Expand the definition of `push` and `pop` and simplify.

/--
Our stack machine has two instructions:
* `push n` which pushes a natural number `n` on the stack
* `add` which pops the top two elements of the stack, adds them and pushes the
  result back on the stack.

Internally, they use the `push` and `pop` operations we defined above.

To execute our instructions, we define two functions:
* `exec` which executes a single instruction on a stack.
* `run` which executes a list of instructions on a stack.
-/
inductive Instr where
  | push : Nat → Instr
  | add  : Instr

/--
Executes a single instruction on a stack. It also makes convenient to reasoning
about the `run` function later in the proof of the main theorem.
-/
def exec (i : Instr) (s : Stack Nat) : Stack Nat :=
  match i with
  | .push n => s.push n
  | .add =>
    match s.pop with
    | none => s
    | some ⟨a, s'⟩ =>
      match s'.pop with
      | none => s
      | some ⟨b, s''⟩ => s''.push (a + b)

/--
Executes a list of instructions on a stack returning the resulting stack.
-/
def run (is : List Instr) (s : Stack Nat) : Stack Nat :=
  match is with
  | [] => s
  | i::is => run is (exec i s)

-- Let's see some examples of how our stack machine works.
#eval run [Instr.push 2, Instr.push 3, Instr.add] emptyStack

/-
This concludes the definition of our stack machine. We have defined:
* A simple stack data structure.
* A set of instructions.
* A way to execute those instructions on a stack.
-/
end StackMachine

section ExpressionLanguage
/-
Next, we will define:
* Our expression language.
* An `eval` function that evaluates expressions to natural numbers.
* The `compile` function that translates expressions into instructions.
-/

/--
A language is a set of rules that defines how to construct valid sentences. In
the case of computational languages, rules that allow us to construct syntax
trees.

Here, we will define a simple language that allows us to express the addition of
natural numbers.

Our expression language will have two constructs:
* `const n` which represents a constant natural number `n`.
* `add lhs rhs` which represents the addition of two expressions `lhs` and `rhs`.

The main invariant here is that:
> Evaluating an expression should yield the same result as running the compiled
> code on an empty stack.

In formal terms:
> ∀ e : Expr, run (compile e) emptyStack = push (eval e) emptyStack.
-/
inductive Expr where
 | const : Nat → Expr
 | add   : Expr → Expr → Expr

/--
Evaluates an expression returns a natural number when the expression is a
constant, and the sum of two expressions when it is an addition.
-/
def eval : Expr → Nat
  | Expr.const n => n
  | Expr.add lhs rhs => eval lhs + eval rhs

/--
The compile function connects our expression language to our stack machine. It
translates an expression into a list of instructions that, when successfully
executed on an empty stack, will yield a stack with a single element which is
the result of evaluating the expression.
-/
def compile : Expr → List Instr
  | Expr.const n => [Instr.push n]
  | Expr.add lhs rhs => compile lhs ++ compile rhs ++ [Instr.add]

-- Let's see some examples
def test_expr := Expr.add (Expr.add (Expr.const 2) (Expr.const 3)) (Expr.const 4)
#eval eval test_expr
#eval run (compile test_expr) emptyStack

/-
This concludes the definition of our expression language and the compilation
process. We have defined:
* A simple expression language with constants and addition.
* An evaluation function that computes the value of an expression.
* A compilation function that translates expressions into instructions for our
  stack machine.
-/
end ExpressionLanguage

section CompilerCorrectness
/-
Finally, we can now prove the main theorem that connects our expression language
and our stack machine. We cannot jump straight to the main theorem. We will need
some auxiliary lemmas to help us in the proof. We will need to prove:
* Running a combination of two lists of instructions is the same as running the
  first list and then running the second list on the resulting stack.
* Running a compiled expression on a general stack is the same as pushing the
  result of evaluating the expression on that stack.
-/

/--
We will prove that running a combination of two lists of instructions is the same
as running the first list and then running the second list on the resulting stack.

In formal terms:
> ∀ is1 is2 : List Instr, ∀ s : Stack Nat, run (is1 ++ is2) s = run is2 (run is1 s).

This is necessary because the `compile` function uses list concatenation of
instructions for addition, and we need to be able to reason about that result.
-/
theorem run_append (is1 is2 : List Instr) (s : Stack Nat) :
  run (is1 ++ is2) s = run is2 (run is1 s) := by
  induction is1 generalizing s with
  | nil => simp [run]  -- uses the definition of `run` to simplify the equality
  | cons i is ih =>    -- ih : induction hypothesis for the tail of the list
    simp [run]
    exact ih (exec i s)

/--
We will prove that running a compiled expression on a general stack is the same as
pushing the result of evaluating the expression on that stack.

In formal terms:
> ∀ e : Expr, ∀ s : Stack Nat, run (compile e) s = push (eval e) s.

This is necessary because the `run_append` lemma produces a `run is2 (run is1 s)`,
and we need to be able to reason about the inner `run is1 s` as a valid stack.
-/
theorem compile_correct_stack (e : Expr) (s : Stack Nat) :
  run (compile e) s = s.push (eval e) := by
  induction e generalizing s with    -- s can be results from previous operations
  | const n => simp [compile, eval, run, exec]
  | add lhs rhs ihl ihr =>
    simp [compile, eval]
    rw [run_append, run_append, ihl, ihr, run, exec]
    simp [run]
    simp [Stack.pop, Stack.push]
    rw [Nat.add_comm]

/--
The `compile` function is correct if running the compiled code on an empty stack
returns a stack with a single element which is the result of evaluating the
expression.
-/
theorem compile_correct (e : Expr) :
  run (compile e) emptyStack = emptyStack.push (eval e) := by
  exact compile_correct_stack e emptyStack

/-
This concludes our goal. We have successfully proved that our compiler correctly
translates expressions into instructions for our stack machine.

Any change on the instruction set, the expression language, the evaluation
function or the compilation function that breaks the invariant will cause the
proof of `compile_correct` to fail.

Making extensible instruction sets means that we can add new instructions without
touching existing code.

The formal verification ensures that the new instructions are not only correct
but also don't break the correctness of the existing logic.
-/
end CompilerCorrectness
