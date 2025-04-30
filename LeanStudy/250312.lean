import Mathlib

example (a b : ℝ): 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

example (a b : ℝ): 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith


#check abs_le'.mpr

example (a b : ℝ) : |a*b| ≤ (a^2 + b^2) / 2 := by
  apply abs_le'.mpr
  constructor
  · have h₁: 0 ≤ (a^2 + b^2) - 2*a*b
    calc
      (a^2 + b^2)- 2*a*b = (a - b)^2  := by ring
      _ ≥ 0 := by apply pow_two_nonneg
    linarith[h₁]
  · have h₂: 0 ≤ (a^2 + b^2) + 2*a*b
    calc
      (a^2 + b^2) + 2*a*b = (a + b)^2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
    linarith[h₂]







/-
    calc
      (a^2 + b^2) / 2 + a * b = (a - b)^2 / 2 : by ring
      _ ≥ 0 : by apply pow_two_nonneg
    linarith
  apply abs_le'.mpr[h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · exact h₀
  intro h
  apply h₁
  rw [h]
-/
