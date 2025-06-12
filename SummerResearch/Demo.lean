/-
Demo file for Summer Research
-/

import Mathlib

-- The rewrite tactic `rw` is used to rewrite the goal using a lemma or theorem.

#check mul_comm

--Enter ℝ by `slash R space`
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

-- P is a quantifier, Q and R are propositions
variable {α : Type*} (P : α → Prop) (Q R: Prop)

example (h : Q → R) (hQ : Q) : R := by
  apply h
  exact hQ

--De Morgan's laws:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x
  intro h'
  apply h
  use x
--push_neg at h
--exact h

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro h'
  rcases h' with ⟨x, hx⟩
  apply h x
  exact hx
--push_neg
--exact h

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  apply h'
  use x
--push_neg at h
--exact h

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, hx⟩
  apply hx
  exact h' x
--push_neg
--exact h
