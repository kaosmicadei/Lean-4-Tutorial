inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ

namespace ℕ
section Addition
def add : ℕ → ℕ → ℕ
  | m, zero => m
  | m, succ n => succ (add m n)

instance : Add ℕ where
  add := add
end Addition

section Multiplication
def mul : ℕ → ℕ → ℕ
  | _, zero => zero
  | m, succ n => m + (mul m n)

instance : Mul ℕ where
  mul := mul
end Multiplication
end ℕ
