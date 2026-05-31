import Tutorial.Basic
import Tutorial.NaturalNumber.Definition

open ℕ

-- 1. Prove the following properties of addition of natural numbers writing the
-- necessary lemmas to support your proves.
section Addition
section Basic
lemma ℕ.add_zero (n : ℕ) : n + zero = n := by sorry
lemma ℕ.add_succ (m n : ℕ) : m + succ n = succ (m + n) := by sorry
end Basic

section Commutativity
theorem ℕ.add_comm (m n : ℕ) : m + n = n + m := by sorry
end Commutativity

section Associativity
theorem ℕ.add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by sorry
end Associativity
end Addition

-- 2. Prove the following properties of multiplication of natural numbers
-- writing the necessary lemmas to support your proves.
section Multiplication
section Basic
lemma ℕ.mul_zero (n : ℕ) : n * zero = zero := by sorry
lemma ℕ.mul_succ (m n : ℕ) : m * succ n = m + (m * n) := by sorry
end Basic

section Commutativity
theorem ℕ.mul_comm (m n : ℕ) : m * n = n * m := by sorry
end Commutativity

section Distributivity
theorem ℕ.mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by sorry
theorem ℕ.add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by sorry
end Distributivity

section Associativity
theorem ℕ.mul_assoc (a b c : ℕ) : a * b * c = a * (b * c) := by sorry
end Associativity
end Multiplication

-- 3. Prove the following properties of even and odd numbers writing the
-- necessary lemmas to support your proves.
section Logic
def Even (n : ℕ) : Prop := ∃ k : ℕ, n = k + k
def Odd (n : ℕ) : Prop := ∃ k : ℕ, n = succ (k + k)

theorem ℕ.zero_not_succ (n : ℕ) : zero ≠ succ n := by sorry
theorem ℕ.succ_injective (m n : ℕ) (h : succ m = succ n) : m = n := by sorry
theorem ℕ.zero_or_succ (n : ℕ) : zero = n ∨ ∃ m : ℕ, n = succ m := by sorry
theorem ℕ.even_or_odd (n : ℕ) : Even n ∨ Odd n := by sorry
theorem ℕ.odd_plus_odd (m n : ℕ) (h: Odd m ∧ Odd n) : Even (m + n) := by sorry
end Logic
