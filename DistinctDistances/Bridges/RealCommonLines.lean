import DistinctDistances.Bridges.CommonLineComponents
import DistinctDistances.Bridges.BezoutComponents

/-! Track A's refined Bézout theorem supplies track C's real common-line bound. -/

namespace DistinctDistances.Bridges

noncomputable section

theorem real_totalDegree_map (f : TrackC.Poly 3) :
    (MvPolynomial.map (algebraMap ℝ ℂ) f).totalDegree = f.totalDegree := by
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective f (f := algebraMap ℝ ℂ) Complex.ofReal_injective]

theorem coprime_common_lines_real (f g : TrackC.Poly 3) (hf : f ≠ 0) (hg : g ≠ 0)
    (hcop : IsRelPrime f g) :
    TrackC.FiniteCardBound {l : TrackC.Line 3 | TrackC.onPolynomial f l ∧ TrackC.onPolynomial g l}
      ((f.totalDegree : ℝ) * g.totalDegree) := by
  classical
  let S : Set (TrackC.Line 3) := {l | TrackC.onPolynomial f l ∧ TrackC.onPolynomial g l}
  by_cases hS : S.Nonempty
  · obtain ⟨lift, hinj, hlift⟩ := real_common_line_components f g hf hg hcop
    obtain ⟨l₀, hl₀⟩ := hS
    let fc := MvPolynomial.map (algebraMap ℝ ℂ) f
    let gc := MvPolynomial.map (algebraMap ℝ ℂ) g
    have hmapinj : Function.Injective
        (MvPolynomial.map (algebraMap ℝ ℂ) : TrackC.Poly 3 → Poly 3) :=
      MvPolynomial.map_injective _ Complex.ofReal_injective
    have hfc : fc ≠ 0 := fun hz => hf (hmapinj (hz.trans (map_zero _).symm))
    have hgc : gc ≠ 0 := fun hz => hg (hmapinj (hz.trans (map_zero _).symm))
    have hcomp₀ := (hlift l₀ hl₀.1 hl₀.2).1
    have hfc_mem : fc ∈ (lift l₀).ideal := hcomp₀.le (Ideal.subset_span (by simp [fc]))
    have hgc_mem : gc ∈ (lift l₀).ideal := hcomp₀.le (Ideal.subset_span (by simp [gc]))
    have hfc_unit : ¬ IsUnit fc := fun hu => hcomp₀.isPrime.ne_top
      ((lift l₀).ideal.eq_top_of_isUnit_mem hfc_mem hu)
    have hgc_unit : ¬ IsUnit gc := fun hu => hcomp₀.isPrime.ne_top
      ((lift l₀).ideal.eq_top_of_isUnit_mem hgc_mem hu)
    have hfcdeg : 1 ≤ fc.totalDegree :=
      Nat.succ_le_of_lt (totalDegree_pos_of_not_isUnit fc hfc hfc_unit)
    have hgcdeg : 1 ≤ gc.totalDegree :=
      Nat.succ_le_of_lt (totalDegree_pos_of_not_isUnit gc hgc hgc_unit)
    have hfinitebound (L : Finset (TrackC.Line 3)) (hL : (L : Set (TrackC.Line 3)) ⊆ S) :
        (L.card : ℝ) ≤ (f.totalDegree : ℝ) * g.totalDegree := by
      let F := L.image lift
      have hF : AffineFamily.IsPure F 1 := by
        intro V hV
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hV
        have hdata := hlift l (hL hl).1 (hL hl).2
        exact ⟨hdata.1.isPrime, hdata.2.1⟩
      have hcomponents : ∀ V ∈ F, V.IsComponentOf (Ideal.span {fc, gc}) := by
        intro V hV
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hV
        exact (hlift l (hL hl).1 (hL hl).2).1
      have hdegree : ∀ V ∈ F, V.degree = 1 := by
        intro V hV
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hV
        exact (hlift l (hL hl).1 (hL hl).2).2.2
      have hb := card_degree_one_components fc gc hfcdeg hgcdeg F hF hcomponents hdegree
      have hcard : F.card = L.card := Finset.card_image_of_injective L hinj
      rw [hcard, real_totalDegree_map f, real_totalDegree_map g] at hb
      exact_mod_cast hb
    have hfinite : S.Finite := by
      by_contra hinfinite
      obtain ⟨L, hL, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite
        (f.totalDegree * g.totalDegree + 1)
      have hb : L.card ≤ f.totalDegree * g.totalDegree := by
        exact_mod_cast hfinitebound L hL
      omega
    refine ⟨hfinite, ?_⟩
    rw [Set.ncard_eq_toFinset_card S hfinite]
    exact hfinitebound hfinite.toFinset (fun l hl => hfinite.mem_toFinset.mp hl)
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have hfinite : S.Finite := by
      rw [he]
      exact Set.finite_empty
    refine ⟨hfinite, ?_⟩
    change (S.ncard : ℝ) ≤ (f.totalDegree : ℝ) * g.totalDegree
    rw [he, Set.ncard_empty, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end
end DistinctDistances.Bridges
