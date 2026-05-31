import Tutorial.Basic

namespace Implication
theorem identity (P : Prop) : P → P := by
  exact λp ↦ p

theorem impl_trans (P Q R: Prop) (h1 : P → Q) (h2 : Q → R) : (P → R) := by
  exact h2 ∘ h1
end Implication

namespace Conjunction
theorem left_impl (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left

theorem right_impl (P Q : Prop) : P ∧ Q → Q := by
  intro h
  exact h.right

theorem and_comm' (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨h.right, h.left⟩

theorem and_assoc' (P Q R : Prop) : P ∧ Q ∧ R → (P ∧ Q) ∧ R := by sorry

theorem impl_and (P Q R : Prop) : (P → Q ∧ R) → (P → Q) ∧ (P → R) := by sorry
theorem and_impl (P Q R : Prop) : (P → Q) ∧ (P → R) → (P → Q ∧ R) := by sorry
corollary (P Q R : Prop) : (P → Q) ∧ (P → R) ↔ (P → Q ∧ R) := by sorry
end Conjunction

namespace Disjunction
theorem left_impl (P Q : Prop) : P → P ∨ Q := by sorry
theorem right_impl (P Q : Prop) : Q → P ∨ Q := by sorry

theorem or_comm (P Q : Prop) : P ∨ Q → Q ∨ P := by sorry
theorem or_assoc (P Q R : Prop) : P ∨ Q ∨ R → (P ∨ Q) ∨ R := by sorry

theorem impl_or (P Q R : Prop) : (P → Q ∨ R) → (P → Q) ∨ (P → R) := by sorry
theorem or_impl (P Q R : Prop) : (P → Q) ∨ (P → R) → (P → Q ∨ R) := by sorry
corollary (P Q R : Prop) : (P → Q) ∨ (P → R) ↔ (P → Q ∨ R) := by sorry
end Disjunction

namespace Negation
example (P : Prop) : P → ¬¬P := by
  intro p np
  contradiction

theorem not_impl (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro pq nq p
  apply nq
  apply pq
  assumption

section MorganLaw
-- Morgan's law is not fully constructively provable, but there is a workaround
-- using double negation
lemma not_or (P Q : Prop) : ¬(P ∨ Q) → (¬P ∧ ¬Q) := by
  intro npq
  constructor
  . intro p
    apply npq
    left
    assumption
  . intro q
    apply npq
    right
    assumption

lemma and_not (P Q : Prop) : (¬P ∧ ¬Q) → ¬(P ∨ Q) := by
  intro npnq
  intro pq
  cases pq with
  | inl p =>
    apply npnq.left
    assumption
  | inr q =>
    apply npnq.right
    assumption

theorem not_or_and_not (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  . apply not_or
  . apply and_not

theorem or_not_not_and (P Q : Prop) : (¬P ∨ ¬Q) → ¬(P ∧ Q) := by
  intro npnq
  intro pq
  cases npnq with
  | inl np =>
    apply np
    exact pq.left
  | inr nq =>
    apply nq
    exact pq.right

theorem not_and_alt (P Q : Prop) : ¬(P ∧ Q) → ¬¬(¬P ∨ ¬Q) := by
  intro npq
  intro h
  apply npq
  constructor
  . false_or_by_contra
    apply h
    left
    assumption
  . false_or_by_contra
    apply h
    right
    assumption
end MorganLaw
end Negation
