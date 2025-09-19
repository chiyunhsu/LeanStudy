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
    right; exact xv
  · rintro (xu | xv)
    exact Or.inl xu
    exact Or.inr xv

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  constructor

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor <;> use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨ys, yt⟩
  obtain ⟨x1, x1s, hx1⟩ := ys
  rw [← hx1]
  obtain ⟨x2, x2t, hx2⟩ := yt
  unfold Injective at h
  rw [← hx2] at hx1
  have heq := h hx1
  rw [← heq] at x2t
  use x1, ⟨x1s, x2t⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨ys, ynt⟩
  obtain ⟨x, xs, rfl⟩ := ys
  have xnt : x ∉ t := by
    intro xt
    apply ynt
    use x, xt
  use x, ⟨xs, xnt⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨xu, xnv⟩
  use xu, xnv

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨ys, yv⟩
    obtain ⟨x, xs, rfl⟩ := ys
    have xv : x ∈ f ⁻¹' v := by
      show f x ∈ v
      exact yv
    use x, ⟨xs, xv⟩
  · rintro ⟨x, ⟨xs, xv⟩, rfl⟩
    constructor
    · use x, xs
    · exact xv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, xv⟩, rfl⟩
  constructor
  · use x, xs
  · exact xv

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, xu⟩
  constructor
  · use x, xs
  · exact xu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | xu)
  · exact Or.inl ⟨x, xs, rfl⟩
  · exact Or.inr xu
