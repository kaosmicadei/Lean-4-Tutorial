/-
Prove that, if a natural number is divisible by 2 and its half is also
divisible by 2, then the original number is divisible by 4.
-/
theorem div_two_mod_2_dvd_by_four
  (n : Nat) (h1 : 2 ∣ n) (h2 : 2 ∣ n/2) : 4 ∣ n := by
  cases h2 with
  | intro k hk =>
    have l1 := Nat.mod_eq_zero_of_dvd h1
    have l2 : n = 2*(n/2) := by
      have l3 := Nat.mod_add_div n 2
      rw [l1, Nat.zero_add] at l3
      rw [l3]
    rw [hk, ← Nat.mul_assoc] at l2
    simp at l2
    apply Nat.dvd_of_mod_eq_zero
    rw [l2, Nat.mul_mod, Nat.mod_self, Nat.zero_mul]
