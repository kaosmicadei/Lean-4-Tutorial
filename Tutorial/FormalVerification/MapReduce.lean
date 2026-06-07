section Map
def map (f : α → β) : List α → List β
  | [] => []
  | a::as => f a :: map f as

#eval map (fun x => x + 1) [1, 2, 3]

theorem fusion (f : α → β) (g : β → γ) : (map g) ∘ (map f) = map (g ∘ f) := by
  funext xs
  induction xs with
  | nil => trivial
  | cons a as h =>
    simp? [map] at *
    rw [h]
end Map

section Reduce
def fold (f : β → α → β) (acc : β) : List α → β
  | [] => acc
  | x :: xs => fold f (f acc x) xs

#eval fold (fun acc x => acc + x) 0 [1, 2, 3]

theorem deforastation (f : α → β) (g : γ → β → γ) (acc : γ) :
  (fold g acc) ∘ (map f) = fold (λa ↦ (g a) ∘ f) acc := by
  funext xs
  induction xs generalizing acc with
  | nil => trivial
  | cons a as h =>
    simp? [map, fold] at *
    rw [h]
end Reduce
