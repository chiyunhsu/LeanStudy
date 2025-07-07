import Mathlib

/- 3.6 Sequences and Convergence -/
/- 25/6/23, 25/07/07 -/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

set_option linter.unusedVariables false
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  simp  --rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have n_ge_Ns : n ≥ Ns := le_trans (le_max_left Ns Nt) hn
  have n_ge_Nt : n ≥ Nt := le_trans (le_max_right Ns Nt) hn
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr; linarith
    _ ≤ |s n - a| + |t n - b| := by apply abs_add
    _ < ε / 2 + ε / 2 := by linarith [hs n n_ge_Ns, ht n n_ge_Nt]
    _ = ε := by linarith

  theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    · rw [h]
      ring
  · have acpos : 0 < |c| := abs_pos.mpr h
    intro ε epos
    have ecpos : 0 < ε / |c| := by simp [epos, acpos]
    rcases cs (ε / |c|) ecpos with ⟨N, hs⟩
    use N
    intro n hn
    calc
      |(fun n ↦ c * s n) n - c * a| = |c * s n - c * a| := by dsimp
      _ = |c * (s n - a)| := by congr; linarith
      _ = |c| * |s n - a| := abs_mul c (s n - a)
      _ < |c| * (ε / |c|) := by
        apply (mul_lt_mul_left acpos).2
        exact hs n hn
      _ = ε := by field_simp

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc
    |s n| = |a + (s n - a)| := by congr; linarith
    _ ≤ |a| + |s n - a|  := abs_add a (s n - a)
    _ < |a| + 1 := by linarith [h n hn]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  have hn0 : n ≥ N₀ := le_trans (le_max_left N₀ N₁) (hn)
  have hn1 : n ≥ N₁ := le_trans (le_max_right N₀ N₁) (hn)
  calc
    |s n * t n - 0| = |s n * (t n - 0)| := by congr; linarith!
    _ = |s n| * |t n - 0| := by apply abs_mul
    _ < B * (ε / B) := mul_lt_mul'' (h₀ n hn0) (h₁ n hn1) (abs_nonneg _) (abs_nonneg _)
    _ = ε := by field_simp

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring
