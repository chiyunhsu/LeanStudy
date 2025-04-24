import Mathlib.Topology.Basic

#check 2 + 2

def f (x : ℕ ) :=
  x + 3

#check f

def FermatLastTheorem :=
  ∀ x y z n : Nat, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem

theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

/-
theorem hard : FermatLastTheorem :=
  sorry

#check hard
-/

/-
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩
-/
