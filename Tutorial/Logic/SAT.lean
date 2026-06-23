theorem even_iff (n : Nat) (h : n ≤ 3) : n % 2 = 0 ↔ n = 0 ∨ n = 2 := by
  constructor
  . -- n is even
    intro h1
    cases n with
    | zero =>
      left
      rfl
    | succ k =>
      cases k with
      | zero => contradiction
      | succ l =>
        rw [Nat.add_assoc] at h1
        simp at *
        have h2 : l < 2 := by
          have h3 : l ≤ 2 := Nat.le_trans h (by decide)
          have h4 := Nat.lt_or_eq_of_le h3
          cases h4 with
          | inl h5 => exact h5
          | inr h5 =>
            rw [h5] at h
            contradiction
        rw [Nat.mod_eq_of_lt h2] at h1
        exact h1
  . -- n is 0 or 2
    intro h1
    cases h1 with
    | inl h2 => rw [h2]
    | inr h2 => rw [h2]

theorem xor_eq_false_iff_even (A B C: Bool) :
  A ^^ (B ^^ C) = false ↔ (A.toNat + B.toNat + C.toNat) % 2 = 0 := by
  constructor
  . decide +revert
  . decide +revert
