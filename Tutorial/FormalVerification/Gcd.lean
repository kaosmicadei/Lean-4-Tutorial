partial def gcd' : Nat → Nat → Nat
  | 0, b => b
  | a, b => gcd' (b % a) a

#eval gcd' 48 18

def gcd (a b : Nat) : Nat :=
  if h : a = 0 then
    b
  else
    gcd (b % a) a
termination_by a
decreasing_by
  have h1 := Nat.pos_of_ne_zero h
  have h2 := Nat.mod_lt b h1
  exact h2

theorem gcd_zero_left (b : Nat) : gcd 0 b = b := by simp [gcd]

theorem gcd_zero_right (a : Nat) : gcd a 0 = a := by
  rw [gcd, Nat.zero_mod]
  cases a with
  | zero => simp
  | succ n =>
    simp
    exact gcd_zero_left (n + 1)

theorem gcd_one_left (b : Nat) : gcd 1 b = 1 := by
  rw [gcd]
  simp
  rw [Nat.mod_one]
  exact gcd_zero_left 1

theorem gcd_one_right (a : Nat) : gcd a 1 = 1 := by
  cases a with
  | zero => exact gcd_zero_left 1
  | succ n =>
    rw [gcd]
    simp
    cases n with
    | zero =>
      simp
      exact gcd_zero_left 1
    | succ k =>
      simp
      exact gcd_one_left (k + 1 + 1)

theorem gcd_succ (a b : Nat) : gcd (a + 1) b = gcd (b % (a + 1)) (a + 1) := by
  cases b with
  | zero =>
    simp
    rw [gcd_zero_right, gcd_zero_left]
  | succ n =>
    rw [gcd]
    simp

theorem gcd_self (a : Nat) : gcd a a = a := by
  cases a with
  | zero => simp [gcd]
  | succ n =>
    rw [gcd]
    simp
    exact gcd_zero_left (n + 1)

theorem gcd_rec (a b : Nat) : gcd a b = gcd (b % a) a := by
  cases a with
  | zero => simp [gcd]
  | succ n =>
    rw [gcd]
    simp

@[elab_as_elim] theorem gcd_induction {P : Nat → Nat → Prop} (m n : Nat)
    (H0 : ∀n, P 0 n) (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) : P m n :=
  Nat.strongRecOn (motive := fun m => ∀ n, P m n) m
    (fun
    | 0, _ => H0
    | _+1, IH => fun _ => H1 _ _ (Nat.succ_pos _) (IH _ (Nat.mod_lt _ (Nat.succ_pos _)) _) )
    n

theorem gcd_dvd (a b : Nat) : gcd a b ∣ a ∧ gcd a b ∣ b := by
  induction a, b using gcd_induction with
  | H0 n =>
    rw [gcd_zero_left]
    have h1 := Nat.dvd_zero n
    have h2 := Nat.dvd_refl n
    exact ⟨h1, h2⟩
  | H1 m n h IH =>
    rw [← gcd_rec m n] at IH
    have h1 := IH.right
    have h2 := (Nat.dvd_mod_iff IH.right).mp IH.left
    exact ⟨h1, h2⟩

theorem gcd_comm (a b : Nat) : gcd a b = gcd b a := by
  induction a, b using gcd_induction with
  | H0 n => rw [gcd_zero_left, gcd_zero_right]
  | H1 m n h IH =>
    rw [← gcd_rec m n] at IH
    rw [IH]
    cases n with
    | zero =>
      simp
      rw [gcd_zero_right, gcd_zero_left]
    | succ k =>
      rw [gcd_succ]
      sorry

#check Nat.gcd
