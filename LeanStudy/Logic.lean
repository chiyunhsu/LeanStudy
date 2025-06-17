import mathlib

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
