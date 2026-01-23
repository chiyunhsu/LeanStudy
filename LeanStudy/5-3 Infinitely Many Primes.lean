import MathLib

def P := { p : ℕ | Nat.Prime p }

/- My own proof of the infinitude of primes -/
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

open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i ∈ s, i :=
  Finset.dvd_prod_of_mem _ h

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  have p_ne_one : ¬ p = 1 := Nat.Prime.ne_one prime_p
  have : p = 1 ∨ p = q := Nat.Prime.eq_one_or_self_of_dvd prime_q p h
  tauto

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  rcases h₁ with h_dvd_a | h_dvd_prod
  left; exact Nat.Prime.eq_of_dvd_of_prime prime_p h₀.1 h_dvd_a
  right; exact ih h₀.2 h_dvd_prod

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
    have : 1 ≤ ∏ i ∈ s', i := by
      apply Finset.one_le_prod'
      intro i hi
      exact Nat.Prime.one_le (mem_s'.mp hi)
    linarith
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
    apply Finset.dvd_prod_of_mem _
    exact mem_s'.mpr pp
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  show False
  exact Nat.Prime.not_dvd_one pp this

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k
