import Mathlib

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
--rcases h with ⟨a, ha⟩ | ⟨b, hb⟩
--· rw [ha, mul_assoc]
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩; positivity; positivity

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h': (x - 1) * (x + 1) = 0 := by
    linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h1 | h2
  · left; linarith
  · right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x - y) * (x + y) = 0 := by
    linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h1 | h2
  · left; linarith
  · right; linarith

variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^2 - 1 := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h1 | h2
  · left;
    calc
      x = (x - 1) + 1 := by ring
      _ = 1 := by rw[h1]; ring
  · right;
      calc
      x = (x + 1) - 1 := by ring
      _ = -1 := by rw[h2]; ring

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x - y) * (x + y) = 0 := by
    calc
      (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
      _ = 0 := by rw [h]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h1 | h2
  · left;
    calc
      x = (x - y) + y := by ring
      _ = y := by rw[h1]; ring
  · right;
      calc
      x = (x + y) - y := by ring
      _ = -y := by rw[h2]; ring
