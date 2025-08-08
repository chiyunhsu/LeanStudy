import Mathlib

/- 4.1 Sets -/
/- 25/07/24, 25/07/31 -/

variable {α : Type*}
variable (s t u : Set α)
open Set

-- intersection
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

-- union
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · constructor
    exact xs
    left; exact xt
  · constructor
    exact xs
    right; exact xu

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · exact ⟨xs, Or.inl xt⟩
  · exact ⟨xs, Or.inr xu⟩

-- set difference
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  have xnt : x ∉ t := by
    intro xt
    apply xntu
    left; exact xt
  have xnu : x ∉ u := by
    intro xu
    apply xntu
    right; exact xu
  exact ⟨⟨xs, xnt⟩, xnu⟩

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  exact ⟨⟨xs, xntu ∘ Or.inl⟩, xntu ∘ Or.inr⟩

example (P Q : Prop) (h : ¬ (P ∨ Q)) : ¬ P :=
  h ∘ Or.inl

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _ ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun _ ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) (fun _ ⟨xs, xt⟩ ↦ ⟨xt, xs⟩)

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  · rintro ⟨xs, xsut⟩; exact xs
  · intro xs; exact ⟨xs, Or.inl xs⟩

example : s ∩ (s ∪ t) = s :=
  Set.ext fun _ ↦ ⟨fun ⟨xs, _⟩ ↦ xs, fun xs ↦ ⟨xs, Or.inl xs⟩⟩

example : s ∪ s ∩ t = s := by
  ext x
  constructor
  · rintro (xs | ⟨xs, xt⟩) <;> exact xs
  · intro xs; exact Or.inl xs

example : s ∪ s ∩ t = s :=
  Set.ext fun _ ↦ ⟨fun h ↦ match h with
    | Or.inl xs => xs
    | Or.inr ⟨xs, _⟩ => xs,
    fun xs => Or.inl xs⟩

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · rintro (⟨xs, xnt⟩ | xt)
    exact Or.inl xs
    exact Or.inr xt
  · rintro (xs | xt)
    by_cases xt : x ∈ t
    · right; exact xt
    · left; exact ⟨xs, xt⟩
    right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt,xns⟩)
    constructor
    · exact Or.inl xs
    · rintro ⟨xs, xt⟩
      contradiction
    constructor
    · exact Or.inr xt
    · rintro xst
      have xs : x ∈ s := xst.1
      contradiction
  · rintro ⟨xs | xt, xnst⟩
    constructor
    · constructor
      · exact xs
      · intro xt
        have xst : x ∈ s ∩ t := ⟨xs, xt⟩
        contradiction
    · right
      constructor
      · exact xt
      · intro xs
        have xst : x ∈ s ∩ t := ⟨xs, xt⟩
        contradiction

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro hprime hgt_two
  rcases Nat.Prime.eq_two_or_odd hprime with htwo | hodd
  · have hneq_two : n ≠ 2 := ne_of_gt hgt_two
    contradiction
  · exact Nat.odd_iff.2 hodd

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h
