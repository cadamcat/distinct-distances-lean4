import DistinctDistances.TrackC.RichLineUniformity
import DistinctDistances.TrackC.PairIncidence

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Two-rich points are finite because each belongs to an intersection of distinct listed lines. -/
theorem richPoints_finite (d : ℕ) (L : Finset (Line d)) (k : ℕ) (hk : 2 ≤ k) :
    (richPoints L k).Finite := by
  let A : Line d × Line d → Set (E d) := fun ll => (ll.1.1:Set (E d)) ∩ (ll.2.1:Set (E d))
  have hfinite : (⋃ ll ∈ L.offDiag,A ll).Finite := L.offDiag.finite_toSet.biUnion (fun ll hll =>
    (affine_lines_intersection_bound d ll.1 ll.2 (Finset.mem_offDiag.mp hll).2.2).1)
  apply hfinite.subset
  intro x hx
  have hc : 1 < (L.filter (fun l => x ∈ l.1)).card := by
    change k ≤ (L.filter (fun l => x ∈ l.1)).card at hx
    omega
  obtain ⟨l,hl,l',hl',hne⟩ := Finset.one_lt_card.mp hc
  exact Set.mem_iUnion.mpr ⟨(l,l'),Set.mem_iUnion.mpr
    ⟨Finset.mem_offDiag.mpr ⟨(Finset.mem_filter.mp hl).1,(Finset.mem_filter.mp hl').1,hne⟩,
     (Finset.mem_filter.mp hl).2,(Finset.mem_filter.mp hl').2⟩⟩

/-- Sum uniform multiplicity classes by a finite doubling induction. -/
theorem rich_line_tail_bound (C : ℝ) (hC : 0 < C) (L : Finset (Line 3)) (B : ℝ)
    (hB : 0 ≤ B)
    (hUniform : ∀ (S : Finset (E 3)) (j : ℕ),3 ≤ j →
      (∀ x ∈ S,j ≤ lineMultiplicity L x ∧ lineMultiplicity L x ≤ 2*j) →
      (S.card:ℝ) ≤ C*richLineBudget L.card B j) (k : ℕ) (hk : 3 ≤ k) :
    FiniteCardBound (richPoints L k) (2*C*richLineBudget L.card B k) := by
  have hall : ∀ n : ℕ,∀ j : ℕ,L.card+1-j = n → 3 ≤ j →
      ((richPoints L j).ncard:ℝ) ≤ 2*C*richLineBudget L.card B j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hjn hj
      have hjpos : (0:ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      by_cases hlarge : L.card < j
      · have hempty : richPoints L j = ∅ := by
          ext x
          simp only [richPoints,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
          intro hx
          have hc : lineMultiplicity L x ≤ L.card := Finset.card_filter_le _ _
          omega
        rw [hempty]
        simpa using mul_nonneg (by positivity : 0 ≤ 2*C)
          (richLineBudget_nonneg L.card B j (Nat.cast_nonneg _) hB hjpos.le)
      · have hf := richPoints_finite 3 L j (by omega)
        have hf₂ := richPoints_finite 3 L (2*j) (by omega)
        let U := hf.toFinset
        let S := U.filter (fun x => lineMultiplicity L x < 2*j)
        let V := U.filter (fun x => ¬lineMultiplicity L x < 2*j)
        have hV : V = hf₂.toFinset := by
          ext x
          constructor
          · intro hx
            have hxnot : ¬lineMultiplicity L x < 2*j := (Finset.mem_filter.mp hx).2
            apply hf₂.mem_toFinset.mpr
            exact Nat.le_of_not_gt hxnot
          · intro hx
            have hx₂ : 2*j ≤ lineMultiplicity L x := hf₂.mem_toFinset.mp hx
            have hx₁ : j ≤ lineMultiplicity L x := by omega
            exact Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr hx₁,by omega⟩
        have hsplit : S.card+V.card = U.card :=
          Finset.card_filter_add_card_filter_not (s := U) (fun x => lineMultiplicity L x < 2*j)
        have hS : (S.card:ℝ) ≤ C*richLineBudget L.card B j := by
          apply hUniform S j hj
          intro x hx
          have hxU := (Finset.mem_filter.mp hx).1
          have hxR : x ∈ richPoints L j := hf.mem_toFinset.mp hxU
          exact ⟨hxR,Nat.le_of_lt (Finset.mem_filter.mp hx).2⟩
        have hnext : L.card+1-2*j < n := by omega
        have htail := ih (L.card+1-2*j) hnext (2*j) rfl (by omega)
        have hVcard : (V.card:ℝ) ≤ 2*C*richLineBudget L.card B (2*j) := by
          rw [hV,← Set.ncard_eq_toFinset_card (richPoints L (2*j)) hf₂]
          simpa only [Nat.cast_mul,Nat.cast_ofNat] using htail
        have hcontract := richLineBudget_double L.card B j (Nat.cast_nonneg _) hB hjpos
        have hVbound : (V.card:ℝ) ≤ C*richLineBudget L.card B j := by
          apply hVcard.trans
          calc
            _ ≤ 2*C*(richLineBudget L.card B j/2) := by gcongr
            _ = _ := by ring
        have hcount : (U.card:ℝ) = (S.card:ℝ)+(V.card:ℝ) := by exact_mod_cast hsplit.symm
        rw [Set.ncard_eq_toFinset_card (richPoints L j) hf]
        change (U.card:ℝ) ≤ _
        linarith
  exact ⟨richPoints_finite 3 L k (by omega),hall (L.card+1-k) k rfl hk⟩

end DistinctDistances.TrackC
