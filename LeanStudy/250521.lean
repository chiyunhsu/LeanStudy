import Mathlib

variable (a b : ℝ)
variable (f: ℝ → ℝ)

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  have ngoal: ¬x > 0 := by
    intro h'
    have x_lt_x: x < x := h x h'
    apply lt_irrefl x x_lt_x
  apply le_of_not_gt ngoal

variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x h'
  have h'': ∃ x, P x := by
    use x
  apply h h''

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro h'
  rcases h' with ⟨x, hx⟩
  apply h x hx

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, hx⟩
  apply hx
  apply h' x

example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h h'

example (h : Q) : ¬¬Q := by
  intro h'
  apply h' h

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction
