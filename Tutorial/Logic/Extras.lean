/-!
Proof that:
* OR is associative: `(P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R)`
* AND distributes over OR on the left and on the right:
  `P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)` and `(P ∧ Q) ∨ R ↔ (P ∨ R) ∧ (Q ∨ R)`
* OR distributes over AND on the left and on the right:
  `P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R)` and `(P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R)`

Then, use these properties to show that the following is a tautology:
  `((P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S)) = ((P ∨ Q) ∧ (R ∨ S))`
-/

theorem or_assoc' (P Q R : Prop) : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  constructor
  . intro h
    cases h with
    | inl pq =>
      cases pq with
      | inl p => exact Or.inl p
      | inr q => exact Or.inr (Or.inl q)
    | inr r => exact Or.inr (Or.inr r)
  . intro h
    cases h with
    | inl p => exact Or.inl (Or.inl p)
    | inr qr =>
      cases qr with
      | inl q => exact Or.inl (Or.inr q)
      | inr r => exact Or.inr r

theorem and_or_left' (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  . intro h
    cases h with
    | intro p qr =>
      cases qr with
      | inl q => exact Or.inl ⟨p, q⟩
      | inr r => exact Or.inr ⟨p, r⟩
  . intro h
    cases h with
    | inl pq => exact ⟨pq.left, Or.inl pq.right⟩
    | inr pr => exact ⟨pr.left, Or.inr pr.right⟩

theorem and_or_right' (P Q R : Prop) : (P ∧ Q) ∨ R ↔ (P ∨ R) ∧ (Q ∨ R) := by
  constructor
  . intro h
    cases h with
    | inl pq => exact ⟨Or.inl pq.left, Or.inl pq.right⟩
    | inr r => exact ⟨Or.inr r, Or.inr r⟩
  . intro h
    cases h with
    | intro pr qr =>
      cases pr with
      | inl p =>
        cases qr with
        | inl q => exact Or.inl ⟨p, q⟩
        | inr r => exact Or.inr r
      | inr r => exact Or.inr r

theorem or_and_left' (P Q R : Prop) : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  constructor
  . intro h
    cases h with
    | inl p => exact ⟨Or.inl p, Or.inl p⟩
    | inr qr => exact ⟨Or.inr qr.left, Or.inr qr.right⟩
  . intro h
    cases h with
    | intro pq pr =>
      cases pq with
      | inl p => exact Or.inl p
      | inr q =>
        cases pr with
        | inl p => exact Or.inl p
        | inr r => exact Or.inr ⟨q, r⟩

theorem or_and_right' (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  . intro h
    cases h with
    | intro pq r =>
      cases pq with
      | inl p => exact Or.inl ⟨p, r⟩
      | inr q => exact Or.inr ⟨q, r⟩
  . intro h
    cases h with
    | inl pr => exact ⟨Or.inl pr.left, pr.right⟩
    | inr qr => exact ⟨Or.inr qr.left, qr.right⟩


example (P Q R : Prop) :
  ((P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S)) = ((P ∨ Q) ∧ (R ∨ S)) := by
  rw [← or_assoc']
  repeat rw [← and_or_left']
  rw [← or_and_right']
