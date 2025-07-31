import Mathlib

open Finset Multiset Nat List

open PowerSeries
--open Theorems100




variable {α : Type*}


open Finset Multiset Nat List YoungDiagram


#check rowLen_eq_card

lemma lemma1 {d : YoungDiagram} :
    d.rowLens.sum = d.cells.card:= by
    unfold rowLens
    simp



--The sum of the lengths of all rows (rowLens) in a Young diagram equals the total number of cells (cells.card) in the diagram.
lemma young_diagram_rowLens_sum {d : YoungDiagram} :
    d.rowLens.sum = d.cells.card:= by
  obtain h':= YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := d)
  have : Sorted (fun x1 x2 => x1 ≥ x2) d.rowLens := by
    rw [YoungDiagram.rowLens]
    obtain h := d.isLowerSet
    obtain := YoungDiagram.rowLens_sorted d
    have h1 : d.rowLens= (List.map d.rowLen (List.range (d.colLen 0))) := by
      rw [YoungDiagram.rowLens]
    rw [← h1]
    omega
  have : (YoungDiagram.ofRowLens d.rowLens this).card = d.rowLens.sum := by
    conv_rhs => rw [YoungDiagram.rowLens]
    rw [YoungDiagram.ofRowLens_to_rowLens_eq_self]
    sorry
  rw [← this]
  rw [card_eq_of_equiv]
  simp only [mem_cells]
  rw [YoungDiagram.ofRowLens_to_rowLens_eq_self]





#check List.map
#check List.range
#check List.map



lemma young_diagram_transpos_card {d : YoungDiagram} :
    d.transpose.card = d.card := by
  apply Finset.card_eq_of_equiv
  simp only [YoungDiagram.mem_cells]
  refine ⟨
    fun ⟨x, hx⟩ => ⟨x.swap, YoungDiagram.mem_transpose.mp hx⟩,
    fun ⟨x, hx⟩ => ⟨x.swap, by simp [YoungDiagram.mem_transpose, hx]⟩,
    fun _ => by simp,
    fun _ => by simp ⟩


-- the YoungDiagram of Partition n
def young_diagram_of_partition {n : ℕ} (p : Partition n) : YoungDiagram where
  cells := (Finset.range n ×ˢ Finset.range n).filter (fun ⟨c, v⟩ =>
    c < (p.parts.filter (fun x => x > v)).card)
  isLowerSet := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ ⟨ha, hb⟩ h_a_in
    simp at ha hb h_a_in ⊢
    obtain ⟨h1, h2⟩ := h_a_in
    constructor
    . omega
    . refine GCongr.gt_imp_gt ?_ ha h2
      apply Multiset.card_le_card
      apply Multiset.monotone_filter_right
      omega



-- the sum of YoungDiagram from Partition n equals n
lemma young_diagram_of_partition_sum {n : ℕ} (p : Partition n) :
    (young_diagram_of_partition p).cells.card = n := by
  --have h_sum := p.parts_sum
  simp only [young_diagram_of_partition, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_product_right]
  simp
  rw [Finset.sum_eq_card_nsmul (b := 1)]
  . simp
  . intro x hx
    rw [Finset.card_eq_one]
    generalize hk : (Multiset.filter (fun x₂ => x < x₂) p.parts).card = k
    use 0
    induction' x with n hn
    . simp_all
      sorry


    . obtain hn := hn
      simp at hn




    -- use (Multiset.filter (fun x₂ => x < x₂) p.parts).card
    -- generalize hk : (Multiset.filter (fun x₂ => x < x₂) p.parts).card = k

    -- ext i
    -- simp
    -- constructor
    -- intro hx
    -- have : k = 1 := by
    --   rw [← hk]
    --   have hpos : ∀ (i : ℕ), i ∈ p.parts → 0 < i := by
    --     intro i hi
    --     exact p.parts_pos hi
    --   have :  ∀ (i : ℕ), i ∈ p.parts →  i ≤ n := by omega






-- the Partition n of  YoungDiagram
def partition_of_young_diagram {n : ℕ} {d : YoungDiagram}
    (hd_sum : d.cells.card = n) : Partition n where
  parts := Multiset.ofList d.rowLens
  parts_pos := fun {i} a ↦ YoungDiagram.pos_of_mem_rowLens d i a
  parts_sum := by
    simp only [sum_coe, young_diagram_rowLens_sum, hd_sum]



def partition_conjugate {n : ℕ} (p : Partition n) : Partition n :=
  let d := young_diagram_of_partition p
  have : d.transpose.cells.card = n := by
    simp only [young_diagram_transpos_card, ← young_diagram_of_partition_sum p, d]
  partition_of_young_diagram this


def Partition.self_conjugate (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun c => partition_conjugate c = c





------------------------------------------------------------
--Translate the partition of distinct odd numbers into self-conjugate partitions
def young_diagram_of_trans {n : ℕ} (p : Partition n) (hp : p ∈ Partition.oddDistincts n) : YoungDiagram where
  cells := ((Finset.range n) ×ˢ (Finset.range n)).filter fun ⟨x, y⟩ =>
    let m := min x y
    let sorted_list := p.parts.sort GE.ge
    m < sorted_list.length ∧ |(x : ℤ) - y| ≤ (sorted_list.getD m 0) / 2
  isLowerSet := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ ⟨ha, hb⟩ h_a_in
    simp at ha hb h_a_in ⊢
    obtain ⟨h1, h2⟩ := h_a_in
    constructor
    . omega
    . constructor
      . omega
      . sorry





--prove their sum are equal
lemma sum_young_diagram_of_trans {n : ℕ} (p : Partition n) (hp : p ∈ Partition.oddDistincts n) :
  (young_diagram_of_trans p hp).cells.card = n := by
  unfold young_diagram_of_trans
  simp

  sorry



-- Translate the partition of self-conjugate partitions into distinct odd numbers.
def young_diagram_of_anti_trans {n : ℕ} (p : Partition n) (hp : p ∈ Partition.self_conjugate n) : YoungDiagram where
  cells := ((Finset.range n) ×ˢ (Finset.range n)).filter fun ⟨x, y⟩ =>
    let cnt := (young_diagram_of_partition p).cells.filter (fun ⟨i, j⟩ => (min i j) = x) |>.card
    y < cnt
  isLowerSet := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ ⟨ha, hb⟩ h_a_in
    simp at ha hb h_a_in ⊢
    constructor
    . omega
    . obtain ⟨h1, h2⟩ := h_a_in
      sorry


--Translate the partition of distinct odd numbers into self-conjugate partitions
lemma sum_young_diagram_of_anti_trans {n : ℕ} (p : Partition n) (hp : p ∈ Partition.self_conjugate n) :
  (young_diagram_of_anti_trans p hp).cells.card = n := by
  --unfold young_diagram_of_anti_trans
  --simp
  unfold Partition.self_conjugate partition_conjugate at hp
  simp at hp
  sorry





/-To prove that the number of partitions into distinct odd numbers is equal to the number of
self-conjugate partitions via a bijective mapping-/

theorem equiv_of_oddDistincts_self_conjugate (n : ℕ) :
    (Partition.oddDistincts n).card = (Partition.self_conjugate n).card := by
  let f : Partition.oddDistincts n → Partition.self_conjugate n :=
  fun π =>
    have : π.val ∈ Partition.oddDistincts n := by simp
    let parts' := (partition_of_young_diagram (sum_young_diagram_of_trans π.val this)).parts
    have total : π.val.parts.sum = n := π.val.parts_sum
    have hsum : parts'.sum = n := by
      exact (partition_of_young_diagram (sum_young_diagram_of_trans π.val this)).parts_sum
    have hpos : ∀ (i : ℕ), i ∈ parts' → 0 < i := by
      intro i hi
      unfold parts' at hi
      exact ((partition_of_young_diagram (sum_young_diagram_of_trans π.val this))).parts_pos hi
    have hpos' : ∀ i ∈ parts', 0 < i := by
      intro i hi
      exact hpos i hi
    have hcon : (partition_of_young_diagram (sum_young_diagram_of_trans π.val this)) ∈ (Partition.self_conjugate n)  := by
       sorry
    ⟨{ parts := parts', parts_sum := hsum, parts_pos := by
        intros i hi
        exact hpos' i hi
     }, hcon ⟩
  let g : Partition.self_conjugate n → Partition.oddDistincts n :=
  fun π =>
    have : π.val ∈ Partition.self_conjugate n := by simp
    let parts' := (partition_of_young_diagram (sum_young_diagram_of_anti_trans π.val this)).parts
    have total : π.val.parts.sum = n := π.val.parts_sum
    have hsum : parts'.sum = n := by
      exact (partition_of_young_diagram (sum_young_diagram_of_anti_trans π.val this)).parts_sum
    have hpos : ∀ (i : ℕ), i ∈ parts' → 0 < i := by
      intro i hi
      unfold parts' at hi
      exact ((partition_of_young_diagram (sum_young_diagram_of_anti_trans π.val this))).parts_pos hi
    have hpos' : ∀ i ∈ parts', 0 < i := by
      intro i hi
      exact hpos i hi
    have hcon : (partition_of_young_diagram (sum_young_diagram_of_anti_trans π.val this)) ∈ (Partition.oddDistincts n)  := by
       sorry
    ⟨{ parts := parts', parts_sum := hsum, parts_pos := by
        intros i hi
        exact hpos' i hi
     }, hcon ⟩
  have fg_id : ∀ (π : Partition.oddDistincts n), g (f π) = π := by
    intro π
    apply Subtype.ext
    rw [Nat.Partition.ext_iff]

    obtain h := f π
    obtain h' := g h

    exact Nat.Partition.ext_iff.mpr
    rw []
    sorry
  have gf_id : ∀ (π :Partition.self_conjugate n), f (g π) = π := by
    intro π
    let parts := (partition_conjugate π.val).parts
    sorry
  have e : Partition.oddDistincts n ≃ Partition.self_conjugate n :=
    { toFun := f, invFun := g, left_inv := fg_id, right_inv := gf_id }
  exact Finset.card_eq_of_equiv e
