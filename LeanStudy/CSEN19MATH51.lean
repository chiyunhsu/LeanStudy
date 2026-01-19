import Mathlib.Logic.Basic

/- Laws of Propositional Logic -/
lemma AndIdempotent {p : Prop} : p ∧ p ↔ p := by
  apply Iff.intro
  · intro h
    exact h.1
  · intro hp
    exact And.intro hp hp

lemma OrIdempotent {p : Prop} :  p ∨ p ↔ p := by
  apply Iff.intro
  · intro h
    rcases h with hp | hp
    <;> exact hp
  · intro hp
    exact Or.inl hp

lemma AndAssociative {p q r : Prop} :  p ∧ (q ∧ r) ↔ (p ∧ q) ∧ r := by
  apply Iff.intro
  · intro h
    exact And.intro (And.intro h.1 h.2.1) h.2.2
  · intro h
    exact And.intro h.1.1 (And.intro h.1.2 h.2)

lemma OrAssociative {p q r : Prop} :  p ∨ (q ∨ r) ↔ (p ∨ q) ∨ r := by
  apply Iff.intro
  · intro h
    rcases h with hp | hqr
    · exact Or.inl (Or.inl hp)
    · rcases hqr with hq | hr
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hr
  · intro h
    rcases h with hpq | hr
    · rcases hpq with hp | hq
      · exact Or.inl hp
      · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr hr)

lemma AndCommutative {p q : Prop}: p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · intro h
    exact And.intro h.2 h.1
  · intro h
    exact And.intro h.2 h.1

lemma OrCommutative {p q : Prop} : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  · intro h
    rcases h with hp | hq
    · exact Or.inr hp
    · exact Or.inl hq
  · intro h
    rcases h with hq | hp
    · exact Or.inr hq
    · exact Or.inl hp

lemma OrAndDistributive {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro h
    rcases h with hp | hqr
    · exact And.intro (Or.inl hp) (Or.inl hp)
    · exact And.intro (Or.inr hqr.1) (Or.inr hqr.2)
  · intro h
    rcases h with ⟨hpq, hpr⟩
    rcases hpq with hp | hq
    · exact Or.inl hp
    · rcases hpr with hp | hr
      · exact Or.inl hp
      · exact Or.inr (And.intro hq hr)

lemma AndOrDistributive {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    rcases h.2 with hq | hr
    · exact Or.inl (And.intro h.1 hq)
    · exact Or.inr (And.intro h.1 hr)
  · intro h
    rcases h with hpq | hpr
    · exact And.intro hpq.1 (Or.inl hpq.2)
    · exact And.intro hpr.1 (Or.inr hpr.2)

lemma AndIdentity {p : Prop} : p ∧ True ↔ p := by
  apply Iff.intro
  · intro h
    exact h.1
  · intro hp
    exact And.intro hp True.intro

lemma OrIdentity {p : Prop} : p ∨ False ↔ p := by
  apply Iff.intro
  · intro h
    rcases h with hp | hfalse
    · exact hp
    · exact False.elim hfalse
  · intro hp
    exact Or.inl hp

lemma AddDomination {p : Prop} : p ∨ True ↔ True := by
  apply Iff.intro
  · intro h
    exact True.intro
  · intro h
    exact Or.inr h

lemma OrDomination {p : Prop} : p ∧ False ↔ False := by
  apply Iff.intro
  · intro h
    exact False.elim h.2
  · intro h
    exact And.intro (False.elim h) h

lemma AndComplement {p : Prop} : p ∧ ¬p ↔ False := by
  apply Iff.intro
  · intro h
    exact absurd h.1 h.2
  · intro h
    exact False.elim h

lemma OrComplement {p : Prop} : p ∨ ¬p ↔ True := by
  apply Iff.intro
  · intro h
    exact True.intro
  · intro h
    by_cases hp : p
    · exact Or.inl hp
    · exact Or.inr hp

lemma AndDeMorgan {p q : Prop} : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  apply Iff.intro
  · intro h
    by_cases hp : p
    · by_cases hq : q
      · exact False.elim (h (And.intro hp hq))
      · exact Or.inr hq
    · exact Or.inl hp
  · intro h
    rcases h with hnp | hnq
    · intro hpq
      exact absurd hpq.1 hnp
    · intro hpq
      exact absurd hpq.2 hnq

lemma OrDeMorgan {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  · intro h
    exact And.intro (mt Or.inl h) (mt Or.inr h)
  · intro h
    rcases h with ⟨hnp, hnq⟩
    intro hpq
    rcases hpq with hp | hq
    · exact absurd hp hnp
    · exact absurd hq hnq

lemma OrAndAbsorption {p q : Prop} : p ∨ (p ∧ q) ↔ p := by
  apply Iff.intro
  · intro h
    rcases h with hp | hpq
    · exact hp
    · exact hpq.1
  · intro hp
    exact Or.inl hp

lemma AndOrAbsorption {p q : Prop} : p ∧ (p ∨ q) ↔ p := by
  apply Iff.intro
  · intro h
    exact h.1
  · intro hp
    exact And.intro hp (Or.inl hp)

lemma ConditionalIdentity {p q : Prop} : (p → q) ↔ (¬p ∨ q) := by
  apply Iff.intro
  · intro h
    by_cases hp : p
    · exact Or.inr (h hp)
    · exact Or.inl hp
  · intro h
    rcases h with hnp | hq
    · intro hp
      exact absurd hp hnp
    · intro hp
      exact hq

/- Rules of Inference -/
lemma ModusPonens {p q : Prop} (h₁ : p → q) (h₂ : p) : q := h₁ h₂

lemma ModusTollens {p q : Prop} (h₁ : p → q) (h₂ : ¬q) : ¬p := mt h₁ h₂

lemma Addition {p q : Prop} (h : p) : p ∨ q := Or.inl h

lemma Simplification {p q : Prop} (h : p ∧ q) : p := h.1

lemma Conjunction {p q : Prop} (h₁ : p) (h₂ : q) : p ∧ q := And.intro h₁ h₂

lemma DisjunctiveSyllogism {p q : Prop} (h₁ : p ∨ q) (h₂ : ¬p) : q := by
  rcases h₁ with hp | hq
  · exact absurd hp h₂
  · exact hq

lemma HypotheticalSyllogism {p q r : Prop} (h₁ : p → q) (h₂ : q → r) : (p → r) := by
  intro hp
  have hq : q := h₁ hp
  exact h₂ hq

lemma Resolution {p q r : Prop} (h₁ : p ∨ q) (h₂ : ¬p ∨ r) : q ∨ r := by
  rcases h₁ with hp | hq
  · rcases h₂ with hnp | hr
    · exact absurd hp hnp
    · exact Or.inr hr
  · exact Or.inl hq

/- Examples -/
example {p q r : Prop} (h1 : p) (h2 : p ∧ ¬r) (h3 : ¬r → q) : p ∧ q := by
  have h4 : ¬r ∧ p := AndCommutative.mp h2
  have h5 : ¬r := Simplification h4
  have h6 : q := ModusPonens h3 h5
  have h7 : p ∧ q := Conjunction h1 h6
  exact h7

example {p q r : Prop} (h1 : p ∧ ¬q) (h2 : r → q) : ¬r := by
  sorry

example {p q r : Prop} (h1 : p ∨ q) (h2 : ¬p ∨ r) (h3 : ¬r) : q := by
  sorry

/- Rules of Inference with Quantifiers -/
variable {α : Type*}
-- Universal Instantiation
lemma UnivInst {p : α → Prop} (h : ∀ x, p x) (c : α) : p c := h c

-- Existential Generalization
lemma ExistGen {p : α → Prop} (c : α) (h : p c) : ∃ x, p x := Exists.intro c h

/- Examples with Quantifiers -/

example {p q : α → Prop} (c : α) (h1 : ∀ x, p x → q x) (h2 : p c) : q c := by
  sorry

example {p q : α → Prop} (c : α) (h : p c ∧ q c) : ∃ x, p x := by
  sorry

example {p q : α → Prop} (h1 : ∃ x, p x) (h2 : ∀ x, p x → q x) : ∃ x, q x := by
  sorry
