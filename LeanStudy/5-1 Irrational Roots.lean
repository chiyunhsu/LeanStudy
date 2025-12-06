import MathLib

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have two_dvd_m : 2 ∣ m := by
    apply even_of_even_sqr
    use n ^ 2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp two_dvd_m
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := (mul_right_inj' two_ne_zero).mp this
  have two_dvd_n : 2 ∣ n := by
    apply even_of_even_sqr
    use k ^ 2
    rw [← this]
  have : 2 ∣ m.gcd n := Nat.dvd_gcd two_dvd_m two_dvd_n
  have : 2 ∣ 1 := by
    rwa [← coprime_mn]
  norm_num at this

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have p_dvd_m : p ∣ m := by
    apply Nat.Prime.dvd_of_dvd_pow (n := 2) prime_p
    use n ^ 2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp p_dvd_m
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := (mul_right_inj' (Nat.Prime.ne_zero prime_p)).mp this
  have p_dvd_n : p ∣ n :=
    Nat.Prime.dvd_of_dvd_pow prime_p (Dvd.intro (k ^ 2) this)
  have : p ∣ m.gcd n := Nat.dvd_gcd p_dvd_m p_dvd_n
  have p_dvd_one : p ∣ 1 := by
    rwa [← coprime_mn]
  have : 2 ≤ p := Nat.Prime.two_le prime_p
  have : p ≤ 1 := Nat.le_of_dvd zero_lt_one p_dvd_one
  linarith
