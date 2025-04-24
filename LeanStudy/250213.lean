import Mathlib

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
  calc
    a * (b * c) = a * b * c := by
      rw [← mul_assoc]
    _ = b * a * c := by
      rw [mul_comm a]
    _ = b * (a * c) := by
      rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [mul_assoc a e]
  rw [h]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [mul_comm] at hyp
  rw [hyp]
  rw [hyp']
  rw [sub_self]

section
variable (a b c : ℝ)
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = a * (c + d) + b * (c + d) := by
      rw [add_mul]
    _ = a * c + a * d + b * (c + d) := by
      rw [mul_add]
    _ = a * c + a * d + (b * c + b * d) := by
      rw [mul_add]
    _ = a * c + a * d + b * c + b * d := by
      rw [← add_assoc]
end
