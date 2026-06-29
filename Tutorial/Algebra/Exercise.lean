example (a b : Nat) : (a + b) * (a - b) = a*a - b*b := by
  rw [Nat.mul_sub, Nat.add_mul, Nat.add_mul, Nat.add_comm (a*b)]
  rw [Nat.mul_comm b a, Nat.add_sub_add_right]

example (a b : Nat) : (a + b) * (a + b) = a*a + b*b + 2*a*b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a]
  rw [Nat.add_assoc, Nat.add_comm (a*b), Nat.add_comm (a*b)]
  rw [Nat.add_assoc (b*b)]
  rw [← Nat.mul_add, ← Nat.mul_one b]
  rw [← Nat.mul_add]
  simp
  rw [Nat.mul_comm b 2, ← Nat.mul_assoc, Nat.mul_comm a 2]
  rw [← Nat.add_assoc]
