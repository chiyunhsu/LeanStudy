import Mathlib

example (a b : ℝ): min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example (a b : ℝ): min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h


example (a b c: ℝ): min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · show min (min a b) c ≤ a
      apply le_trans
      --· min (min a b) c ≤ (min a b);
      apply min_le_left (min a b) c
      --· min (a b) ≤ a
      apply min_le_left a b
    · show min (min a b) c ≤ min b c
      apply le_min
      · show min (min a b) c ≤ b
        apply le_trans
        apply min_le_left (min a b) c
        apply min_le_right a b
      · show min (min a b) c ≤ c
        apply min_le_right (min a b) c
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · show min a (min b c) ≤ min a b
      apply le_min
      apply min_le_left a (min b c)
      apply le_trans
      apply min_le_right a (min b c)
      apply min_le_left b c
    · show min a (min b c) ≤ c
      apply le_trans
      apply min_le_right a (min b c)
      apply min_le_right b c
