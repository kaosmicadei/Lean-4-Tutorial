/-
> 🚨*Disclaimer*🚨 This file was written following the literal programming style. That means it is
> supposed to be read as a prose rather than a regular source code.

A good reminder is that Lean is designed to be used interactively, that means the proofs here assume
the reader is using VS Code with the Lean extension. That way, one can put the cursor in a
particular part of the proof and see how the context changes in the Lean InfoView tab in real time.
Also, hovering the mouse over expression and tactics can show additional information that are really
insightful to understand Lean's internal workings.
-/

example (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  intro h1
  unfold Not at *
  intro p
  have q := h p
  exact h1 q

example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  intro abc
  obtain ⟨a, bc⟩ := abc
  cases bc with
  | inl b => exact Or.inl (And.intro a b)
  | inr c => exact Or.inr (And.intro a c)

example (n m : Nat) : m * n = 0 → m = 0 ∨ n = 0 := by
  intro h
  cases m with
  | zero =>
    left
    rfl
  | succ m' =>
    right
    rw [Nat.add_mul, Nat.one_mul, Nat.add_eq_zero_iff] at h
    exact h.right

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

example (a b c : Nat) : a ∣ b ∧ a ∣ c → a ∣ (b + c) := by
  intro h
  obtain ⟨hab, hac⟩ := h
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hac
  rw [hk, hl, ← Nat.mul_add]
  exists (k + l)

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
  simp
  rw [← Nat.add_assoc, Nat.mul_add, Nat.mul_add]

example (n : Nat) : n ≠ 0 → ∃ k : Nat, n = k + 1 := by
  intro h
  cases n with
  | zero => contradiction
  | succ k => exists k
