import mathlib

variable (a b : ℝ)
variable (f: ℝ → ℝ)

example (a b : ℝ)(h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

example : ¬FnHasUb fun x ↦ x := by
  intro h
  rcases h with ⟨a, fnuba⟩
  have : (a+1) ≤ a := fnuba (a+1)
  linarith


example (h : Monotone f) (h' : f a < f b) : a < b := by
  have ngoal: ¬ a ≥ b := by
    intro h''
    have : f a ≥ f b := h h''
    linarith
  apply lt_of_not_ge ngoal


example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  have : f a ≤ f b := by
    apply h'' h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intros x y hxy
    exact le_refl 0
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ (0 : ℝ) := h monof h'
  linarith
