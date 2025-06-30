import Mathlib


/- 5.2 Induction and recursion -/

#check Nat

/-
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-/

example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right

#check pow_succ
-- Exercise
theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  · induction' n with n ih
    · repeat rw [fac]
      simp
    · rw [fac]
      simp at ih
      simp
      have h : 2 ≤ n + 2 := by linarith
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n
        _ ≤ 2 * fac (n + 1)  := by simp [ih]
        _ ≤ (n + 2) * fac (n + 1) := (mul_le_mul_right (fac_pos (n + 1))).2 h
        _ = fac (n + 2) := by simp [fac]
