import Tutorial.Basic

namespace Implication
theorem identity (P : Prop) : P → P := by sorry
theorem impl_trans (P Q R: Prop) (h1 : P → Q) (h2 : Q → R) : (P → R) := by sorry
end Implication

namespace Conjunction
theorem left_impl (P Q : Prop) : P ∧ Q → P := by sorry
theorem right_impl (P Q : Prop) : P ∧ Q → Q := by sorry

theorem and_comm' (P Q : Prop) : P ∧ Q → Q ∧ P := by sorry
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
example (P : Prop) : P → ¬¬P := by sorry

theorem not_impl (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by sorry

section MorganLaw
-- Morgan's law is not fully constructively provable, but there is a workaround
-- using double negation
theorem not_or_and_not (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by sorry
theorem or_not_not_and (P Q : Prop) : (¬P ∨ ¬Q) → ¬(P ∧ Q) := by sorry
theorem not_and_alt (P Q : Prop) : ¬(P ∧ Q) → ¬¬(¬P ∨ ¬Q) := by sorry
end MorganLaw
end Negation
