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
  have this := Nat.dvd_sub p_dvd_N p_dvd_prod
  simp only [id_eq, add_tsub_cancel_left, N] at this
  exact this

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le
