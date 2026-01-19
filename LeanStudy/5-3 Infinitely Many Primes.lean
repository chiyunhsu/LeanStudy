import MathLib

def P := { p : ℕ | Nat.Prime p }

theorem PrimesInfinite : ¬ Set.Finite P := by
  intro hfin
  let P_Finset := Set.Finite.toFinset hfin
  let N := P_Finset.prod id + 1
  have N_ne_one : N ≠ 1 := by
    by_contra N_eq_one
    simp [N] at N_eq_one
    rw [Finset.prod_eq_zero_iff] at N_eq_one
    rcases N_eq_one with ⟨p, p_mem, p_eq_zero⟩
    simp [P_Finset, P] at p_mem
    have p_ne_zero := Nat.Prime.ne_zero p_mem
    contradiction
  have h := Nat.exists_prime_and_dvd N_ne_one
  rcases h with ⟨p, p_prime, p_dvd_N⟩
  apply Nat.Prime.not_dvd_one p_prime
  have p_dvd_prod : p ∣ P_Finset.prod id := by
    apply Finset.dvd_prod_of_mem
    rw [Set.Finite.mem_toFinset, P, Set.mem_setOf_eq]
    exact p_prime
  convert (Nat.dvd_sub p_dvd_N p_dvd_prod)
  simp [P_Finset, N]

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial n + 1 := by
    apply two_le
    · apply Nat.succ_ne_zero
    · linarith [Nat.factorial_pos n]
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial n := by
    apply Nat.dvd_factorial
    apply Nat.pos_iff_ne_zero.mpr
    exact Nat.Prime.ne_zero pp
    exact ple
  have : p ∣ 1 := by
    convert (Nat.dvd_sub pdvd this)
    simp
  show False
  exact Nat.Prime.not_dvd_one pp this
