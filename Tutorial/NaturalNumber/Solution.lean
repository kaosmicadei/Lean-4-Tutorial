import Tutorial.Basic
import Tutorial.NaturalNumber.Definition

open ℕ

-- 1. Prove the following properties of addition of natural numbers writing the
-- necessary lemmas to support your proves.
section Addition
section Basic
lemma ℕ.add_zero (n : ℕ) : n + zero = n := by trivial
lemma ℕ.add_succ (m n : ℕ) : m + succ n = succ (m + n) := by trivial
end Basic

section Commutativity
-- first: addition commutes with zero
lemma ℕ.zero_add (n : ℕ) : zero + n = n := by
  induction n with
  | zero => trivial
  | succ n h => rw [add_succ, h]
-- then: addition commutes with successor
lemma ℕ.succ_add (m n : ℕ) : succ m + n = succ (m + n) := by
  induction n with
  | zero => trivial
  | succ n h => rw [add_succ, add_succ, h]
-- finally: addition is commutative
theorem ℕ.add_comm (m n : ℕ) : m + n = n + m := by
  induction m with
  | zero => rw [add_zero]; exact zero_add n
  | succ m h => rw [add_succ, ← h]; exact succ_add m n
end Commutativity

section Associativity
theorem ℕ.add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => trivial
  | succ k h =>
    repeat rw [add_succ]
    rw [h]
end Associativity
end Addition

-- 2. Prove the following properties of multiplication of natural numbers
-- writing the necessary lemmas to support your proves.
section Multiplication
section Basic
lemma ℕ.mul_zero (n : ℕ) : n * zero = zero := by trivial
lemma ℕ.mul_succ (m n : ℕ) : m * succ n = m + (m * n) := by trivial
end Basic

section Commutativity
-- first: multiplication commutes with zero
lemma ℕ.zero_mul (n : ℕ) : zero * n = zero := by
  induction n with
  | zero => trivial
  | succ n h => rw [mul_succ, h, add_zero]
-- then: multiplication commutes with successor
lemma ℕ.succ_mul (m n : ℕ) : succ m * n = n + (m * n) := by
  induction n with
  | zero => trivial
  | succ n h =>
  rw [mul_succ, h, mul_succ, ← add_assoc, ← add_assoc, succ_add, succ_add]
  rw [succ_add, succ_add, add_comm m n]
-- finally: multiplication is commutative
theorem ℕ.mul_comm (m n : ℕ) : m * n = n * m := by
  induction m with
  | zero => rw [mul_zero]; exact zero_mul n
  | succ k h => rw [mul_succ, ← h]; exact succ_mul k n
end Commutativity

section Distributivity
theorem ℕ.mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => trivial
  | succ n h =>
    rw [add_succ, mul_succ, h, mul_succ, ← add_assoc, add_comm a, ← add_assoc]

theorem ℕ.add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  repeat rw [mul_comm _ c]
  exact mul_add c a b
end Distributivity

section Associativity
theorem ℕ.mul_assoc (a b c : ℕ) : a * b * c = a * (b * c) := by
  induction c with
  | zero => trivial
  | succ c h =>
    repeat rw [mul_succ]
    rw [mul_add, h]
end Associativity
end Multiplication

-- 3. Prove the following properties of even and odd numbers writing the
-- necessary lemmas to support your proves.
section Logic
def Even (n : ℕ) : Prop := ∃ k : ℕ, n = k + k
def Odd (n : ℕ) : Prop := ∃ k : ℕ, n = succ (k + k)

theorem ℕ.zero_not_succ (n : ℕ) : zero ≠ succ n := by
  intro h
  contradiction  -- anything can be proved from False

theorem ℕ.succ_injective (m n : ℕ) (h : succ m = succ n) : m = n := by
  injection h

theorem ℕ.zero_or_succ (n : ℕ) : zero = n ∨ ∃ m : ℕ, n = succ m := by
  induction n with
  | zero => left; trivial
  | succ n h =>
    cases h with
    | inl hl =>
      right
      rw [← hl]
      exists zero
    | inr hr =>
      cases hr with
      | intro k hk =>
        right
        rw [hk]
        exists (succ k)

theorem ℕ.even_or_odd (n : ℕ) : Even n ∨ Odd n := by
  induction n with
  | zero =>
    left
    unfold Even
    exists zero
  | succ k h =>
    cases h with
    | inl k_even =>
      cases k_even with
      | intro a ha =>
        right
        unfold Odd
        rw [ha]
        exists a
    | inr k_odd =>
      cases k_odd with
      | intro b hb =>
        left
        unfold Even
        rw [hb]
        exists (succ b)
        rw [add_succ, succ_add]

theorem ℕ.odd_plus_odd (m n : ℕ) (h: Odd m ∧ Odd n) : Even (m + n) := by
  cases h with
  | intro hm hn =>
    cases hm with
    | intro a ha =>
    cases hn with
    | intro b hb =>
      unfold Even
      rw [ha, hb]
      rw [← succ_add, ← add_succ, add_assoc, add_comm a, ← add_assoc, ← add_assoc]
      rw [succ_add, add_assoc, add_comm b.succ, add_succ]
      exists succ (a + b)
end Logic
