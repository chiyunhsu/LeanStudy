import Mathlib

-- P is a quantifier
variable {α : Type*} (P : α → Prop) (Q : Prop)

--To prove `¬ P`, use the tactic `intro h` to introduce the hypothesis `h: P`. Then the goal becomes `False`.
--To prove `P → Q`, use the tactic `intro h` to introduce the hypothesis `h: P`. Then the goal becomes `Q`.
--To prove `P ∧ Q`, use the tactic `constructor` to split the goal into two subgoals: `P` and `Q`.
--To prove `P ∨ Q`, use the tactic `left` or `right` to choose which disjunct to prove. Then the goal becomes `P` or `Q`.
--To use `h: ¬ P`, use `apply h` to a goal which is `False`. then the goal becomes `P`.
--To use `h: P → Q`, use `apply h` to a goal which is `Q`. Then the goal becomes `P`.
--To use `h: P ∧ Q`, use `h.1: P` and `h.2: Q`
--To use `h: P ∨ Q`, use `rcases h with h1 | h2` to destruct the disjunction. Then use `h1 : P` or `h2 : Q` to refer to the left or right disjunct.


--To prove `∀ x, P x`, use the tactic `intro x` to introduce the variable `x`. Then the goal becomes `P x`.
--To prove `∃ x, P x`, use the tactic `use x` to introduce the witness `x`. Then the goal becomes `P x`.
--To use `h: ∀ x, P x`, use `h x` to apply the hypothesis to the variable `x`.
--To use `h: ∃ x, P x`, use `rcases h with ⟨x, hx⟩` to destruct the existential quantifier. Then you can use `hx` to refer to the witness `x`.

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

-- `by_contra` is a tactic that allows you to prove a goal by contradiction.
-- It assumes the negation of the goal and tries to derive a contradiction.
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


/- Rules of Inference -/
variable (P : Prop) (Q : Prop) (R : Prop)

-- Modus Ponens
example (h₁ : P → Q) (h₂ : P) : Q := h₁ h₂
-- Modus Tollens
example (h₁ : P → Q) (h₂ : ¬Q) : ¬P := mt h₁ h₂
-- Addition
example (h : P) : P ∨ Q := Or.inl h
-- Simplification
example (h : P ∧ Q) : P := h.1
-- Conjunction
example (h₁ : P) (h₂ : Q) : P ∧ Q := ⟨h₁, h₂⟩ -- And.intro h₁ h₂
-- Disjunctive Syllogism
example (h₁ : P ∨ Q) (h₂ : ¬P) : Q := by
  rcases h₁ with hp | hq
  · exact absurd hp h₂
  · exact hq
-- Hypothetical Syllogism
example (h₁ : P → Q) (h₂ : Q → R) : (P → R) := by
  intro hp
  have hq : Q := h₁ hp
  exact h₂ hq
-- Resolution
example (h₁ : P ∨ Q) (h₂ : ¬P ∨ R) : Q ∨ R := by
  rcases h₁ with hp | hq
  · rcases h₂ with hnp | hr
    · exact absurd hp hnp
    · exact Or.inr hr
  · exact Or.inl hq

/- Rules of Inference with Quantifiers -/
variable {α : Type*} (P : α → Prop) (Q : Prop) (R : Prop)
-- Universal Instantiation
example (c : α) (h : ∀ x, P x) : P c := h c
-- Existential Generalization
example (c : α) (h : P c) : ∃ x, P x := Exists.intro c h
