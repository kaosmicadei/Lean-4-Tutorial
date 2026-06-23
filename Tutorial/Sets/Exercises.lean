import Mathlib.Data.Set.Basic

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2


theorem compl_compl (A : Set U) : Aᶜᶜ = A := by
  apply subset_antisymm
  · intro x h
    rw [Set.mem_compl_iff] at h
    rw [Set.mem_compl_iff] at h
    push Not at h
    exact h
  · intro x h
    rw [Set.mem_compl_iff]
    rw [Set.mem_compl_iff]
    push Not
    exact h

theorem compl_subset_compl_of_subset {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x h
  rw [Set.mem_compl_iff] at h
  rw [Set.mem_compl_iff]
  by_contra h2
  have h3 := h1 h2
  apply h
  exact h3

theorem inter_distrib_left (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · intro h
    rw [Set.mem_union, Set.mem_inter_iff, Set.mem_inter_iff]
    cases h with
    | intro ha hbc =>
      rw [Set.mem_union] at hbc
      cases hbc with
      | inl hb => left; exact ⟨ha, hb⟩
      | inr hc => right; exact ⟨ha, hc⟩
  · intro h
    rw [Set.mem_inter_iff, Set.mem_union]
    rw [Set.mem_union, Set.mem_inter_iff, Set.mem_inter_iff] at h
    cases h with
    | inl hab => exact ⟨hab.left, Or.inl hab.right⟩
    | inr hac => exact ⟨hac.left, Or.inr hac.right⟩
