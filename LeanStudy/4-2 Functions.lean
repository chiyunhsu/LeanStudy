import Mathlib

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, h⟩
    · left
      use x, xs, h
    · right
      use x, xt, h
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    show f x ∈ v
    apply h
    use x, xs
    --have : f x ∈ f '' s := by use x, xs
    --exact h this
  · rintro h y ⟨x, xs, rfl⟩
    show x ∈ f ⁻¹' v
    exact h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨x', x's, feq⟩
  rw [h feq] at x's
  exact x's

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xu, rfl⟩
  exact xu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y yu
  unfold Surjective at h
  obtain ⟨x, rfl⟩ := h y
  use x, yu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, rfl⟩
  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x hx
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x; constructor
  · rintro (xu | xv)
    left; exact xu
    exact Or.inr xv
  · rintro (xu | xv)
    exact Or.inl xu
    exact Or.inr xv

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry
