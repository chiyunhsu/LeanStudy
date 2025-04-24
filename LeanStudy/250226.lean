import Mathlib

variable (R : Type*) [CommRing R]
variable (a b c d : R)

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))

example : c * b * a = b * (a * c) := by ring

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← zero_add b, ← add_right_neg a, add_comm a, add_assoc, h, ← add_assoc, neg_add_cancel, zero_add]


--theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
-- sorry

end MyRing
