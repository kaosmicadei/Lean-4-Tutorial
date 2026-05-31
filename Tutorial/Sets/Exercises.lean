import Mathlib.Data.Set.Basic

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2


theorem compl_compl (A : Set U) : Aᶜᶜ = A := by
  apply subset_antisymm
  . intro x h
    rw [Set.mem_compl_iff] at h
    rw [Set.mem_compl_iff] at h
    push Not at h
    exact h
  . intro x h
    rw [Set.mem_compl_iff]
    rw [Set.mem_compl_iff]
    push Not
    exact h
