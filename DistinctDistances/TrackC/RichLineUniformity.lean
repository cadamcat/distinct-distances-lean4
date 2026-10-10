import DistinctDistances.TrackC.RichLinePruning

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Remove the supporting-line uniformity condition by induction on the line count. -/
theorem rich_line_uniformity_remove (C : ℝ) (hC : 0 < C)
    (hUniform : ∀ (L : Finset (Line 3)) (S : Finset (E 3)) (B : ℝ) (k : ℕ),
      L.Nonempty → 0 ≤ B → planeCap L B → 3 ≤ k →
      (∀ x ∈ S,k ≤ lineMultiplicity L x ∧ lineMultiplicity L x ≤ 2*k) →
      (L.card:ℝ)/100 ≤ ((L.filter (fun l => (S.card:ℝ)*k/(100*(L.card:ℝ)) ≤
        (pointsOn S l).card)).card:ℝ) →
      (S.card:ℝ) ≤ C*richLineBudget L.card B k) :
    ∀ (L : Finset (Line 3)) (S : Finset (E 3)) (B : ℝ) (k : ℕ),
      0 ≤ B → planeCap L B → 3 ≤ k →
      (∀ x ∈ S,k ≤ lineMultiplicity L x ∧ lineMultiplicity L x ≤ 2*k) →
      (S.card:ℝ) ≤ C*richLineBudget L.card B k := by
  have hall : ∀ n : ℕ,∀ (L : Finset (Line 3)),L.card = n →
      ∀ (S : Finset (E 3)) (B : ℝ) (k : ℕ),0 ≤ B → planeCap L B → 3 ≤ k →
        (∀ x ∈ S,k ≤ lineMultiplicity L x ∧ lineMultiplicity L x ≤ 2*k) →
        (S.card:ℝ) ≤ C*richLineBudget L.card B k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L hLn S B k hB hcap hk hS
      have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      by_cases hSempty : S = ∅
      · subst S
        simpa using mul_nonneg hC.le (richLineBudget_nonneg L.card B k (Nat.cast_nonneg _) hB hkpos.le)
      by_cases hLempty : L = ∅
      · obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
        have hxk := (hS x hx).1
        simp [hLempty,lineMultiplicity] at hxk
        omega
      have hL : L.Nonempty := Finset.nonempty_iff_ne_empty.mpr hLempty
      let L₁ := L.filter (fun l => (S.card:ℝ)*k/(100*(L.card:ℝ)) ≤ (pointsOn S l).card)
      by_cases hlarge : (L.card:ℝ)/100 ≤ (L₁.card:ℝ)
      · exact hUniform L S B k hL hB hcap hk hS hlarge
      · have hsmall : (L₁.card:ℝ) < (L.card:ℝ)/100 := lt_of_not_ge hlarge
        have hsmaller : L₁.card < n := by
          have hr : (L₁.card:ℝ) < L.card := hsmall.trans_le (div_le_self (Nat.cast_nonneg _) (by norm_num))
          rw [← hLn]
          exact_mod_cast hr
        have hsub : L₁ ⊆ L := Finset.filter_subset _ _
        have hcap₁ : planeCap L₁ B := by
          intro H
          apply (show ((L₁.filter (fun l => l.1 ≤ H.1)).card:ℝ) ≤
              ((L.filter (fun l => l.1 ≤ H.1)).card:ℝ) from Nat.cast_le.mpr ?_).trans (hcap H)
          apply Finset.card_le_card
          intro l hl
          exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp hl).1,(Finset.mem_filter.mp hl).2⟩
        obtain ⟨S',k',hS'sub,hk'3,hk'k,hkhalf,hS',hsize⟩ :=
          sparse_line_uniformity_selection L S k hL hk hS L₁ rfl hsmall
        have hbound := ih L₁.card hsmaller L₁ rfl S' B k' hB hcap₁ hk'3 hS'
        have hcontract := richLineBudget_sparse L.card L₁.card B k k'
          (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsmall.le hB hkpos hkhalf
        calc
          _ ≤ 4*(S'.card:ℝ) := hsize
          _ ≤ 4*(C*richLineBudget L₁.card B k') := mul_le_mul_of_nonneg_left hbound (by norm_num)
          _ ≤ 4*(C*(richLineBudget L.card B k/4)) := by gcongr
          _ = _ := by ring
  intro L S B k hB hcap hk hS
  exact hall L.card L rfl S B k hB hcap hk hS

end DistinctDistances.TrackC
