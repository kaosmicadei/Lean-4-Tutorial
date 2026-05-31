import Tutorial.FormalVerification.Definition

theorem fusion (f : α → β) (g : β → γ) : (map g) ∘ (map f) = map (g ∘ f) := by sorry

theorem deforastation (f : α → β) (g : γ → β → γ) (acc : γ) :
  (fold g acc) ∘ (map f) = fold (λa ↦ (g a) ∘ f) acc := by sorry
