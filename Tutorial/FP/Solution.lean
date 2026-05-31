import Tutorial.FP.Definition

theorem fusion (f : α → β) (g : β → γ) : (map g) ∘ (map f) = map (g ∘ f) := by
  funext xs
  induction xs with
  | nil => trivial
  | cons a as h =>
    simp? [map] at *
    rw [h]

theorem deforastation (f : α → β) (g : γ → β → γ) (acc : γ) :
  (fold g acc) ∘ (map f) = fold (λa ↦ (g a) ∘ f) acc := by
  funext xs
  induction xs generalizing acc with
  | nil => trivial
  | cons a as h =>
    simp? [map, fold] at *
    rw [h]
