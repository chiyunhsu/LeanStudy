import Mathlib

variable (x y : ℝ)
variable (f: ℝ → ℝ)

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    apply add_le_add
    exact le_abs_self x
    exact le_abs_self y
  · rw [abs_of_neg h]
    rw[neg_add]
    apply add_le_add
    exact neg_le_abs_self x
    exact neg_le_abs_self y
/-
  rcases le_or_gt 0 x with h | h
  · rcases le_or_gt 0 y with h' | h'
    · rw [abs_of_nonneg h, abs_of_nonneg h']
      have hxy: 0 ≤ x + y := by
        apply add_nonneg h h'
      rw [abs_of_nonneg hxy]
    · rw [abs_of_nonneg h, abs_of_neg h']
      rcases le_or_gt 0 (x + y) with h'' | h''
      · rw [abs_of_nonneg h'']
        linarith
      · rw [abs_of_neg h'']
        linarith
  · rcases le_or_gt 0 y with h' | h'
    · rw [abs_of_neg h, abs_of_nonneg h']
      rcases le_or_gt 0 (x + y) with h'' | h''
      · rw [abs_of_nonneg h'']
        linarith
      · rw [abs_of_neg h'']
        linarith
    · rw [abs_o
      f_neg h, abs_of_neg h']
      have hxy: 0 > x + y := by
        apply add_neg h h'
      rw [abs_of_neg hxy]
      linarith
-/

theorem lt_abs (x y : ℝ) : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy] at h
      left; exact h
    · rw [abs_of_neg hy] at h
      right; exact h
  · intro h
    rcases h with h1 | h2
    · have: y ≤ |y| := le_abs_self y
      linarith
    · have: -y ≤ |y| := neg_le_abs_self y
      linarith


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with hx | hx
  · rw[abs_of_nonneg hx]
    constructor
    · intro h
      constructor
      · have : -y ≤ 0 := by linarith
        linarith
      · exact h
    · intro h
      exact h.2
  · rw[abs_of_neg hx]
    constructor
    · intro h
      constructor
      · linarith
      · linarith
    · intro h
      have : - (- y) > - x := neg_lt_neg h.1
      simp at this
      exact this
end MyAbs
