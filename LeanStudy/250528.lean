import Mathlib

variable (a b : ℝ)
variable (f: ℝ → ℝ)

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨h1,h2⟩
  constructor
  exact h1
  intro h'
  apply h2
  apply dvd_antisymm h1 h'

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · exact h1
    · intro h'
      apply h2
      linarith
  · rintro ⟨h3,h4⟩
    constructor
    · exact h3
    · intro h'
      apply h4
      linarith

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    have h1 : x ^ 2 ≥ 0 := pow_two_nonneg x
    have h2 : x ^ 2 = - y ^ 2 := by linarith
    have h3 : y ^ 2 ≥ 0 := pow_two_nonneg y
    have h4 : x ^ 2 ≤ 0 := by
      rw[h2]
      linarith
    linarith
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h' : y ^ 2 + x ^ 2 = 0 := by linarith
    constructor
    · exact aux h
    · exact aux h'
  · intro ⟨h1,h2⟩
    rw[h1,h2]
    linarith
