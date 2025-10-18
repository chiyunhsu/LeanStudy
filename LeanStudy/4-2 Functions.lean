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

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨i, xAi⟩
    use i, x, xAi
  · rintro ⟨i, x, xAi, rfl⟩
    use x, ⟨i, xAi⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  simp
  intro i x hx
  show f x ∈ f '' A i
  simp at hx
  use x, hx i

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y hy
  simp at *
  rcases (hy i) with ⟨x, xAi, rfl⟩
  use x
  constructor
  intro j
  rcases (hy j) with ⟨x', x'Aj, h⟩
  have heq : x' = x := injf h
  rw [← heq]
  exact x'Aj
  rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]

example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnn y ynn sqeq
  rw [← sq_sqrt xnn, ← sq_sqrt ynn, sqeq]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnn y ynn eq
  simp at eq
  rw [← sqrt_sq xnn, ← sqrt_sq ynn, eq]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  simp
  constructor
  · rintro ⟨x, xnn, rfl⟩
    apply sqrt_nonneg
  · intro ynn
    use y ^ 2, sq_nonneg y, sqrt_sq ynn

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  simp
  constructor
  · rintro ⟨x, rfl⟩
    exact sq_nonneg x
  · intro ynn
    use sqrt y, sq_sqrt ynn

variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse]
  rw [dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

#print LeftInverse

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · rintro f_inj x
    let x' := inverse f (f x)
    have h : f x' = f x := inverse_spec (f x) ⟨x, rfl⟩
    exact f_inj h
  · intro h x1 x2 feq
    have h1 : inverse f (f x1) = x1 := h x1
    have h2 : inverse f (f x2) = x2 := h x2
    rw [← h1, ← h2, feq]

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry
