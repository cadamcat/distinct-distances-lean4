import DistinctDistances.TrackE.GlobalConcentration
import DistinctDistances.TrackE.RequestsRank
import DistinctDistances.TrackA.Hilbert
import DistinctDistances.Bridges.AffineRank

/-! Finitary scalar and counting inputs for `eq:global-rank-lower`. -/

namespace DistinctDistances.Reduction
open scoped BigOperators Classical
noncomputable section

/-- Degree D=floor A is positive and at least A/2 when A≥1, reduction.tex:476. -/
theorem global_rank_degree_scale (A : ℝ) (hA : 1 ≤ A) :
    1 ≤ ⌊A⌋₊ ∧ A ≤ 2 * (⌊A⌋₊ : ℝ) := by
  have hfloor : 1 ≤ ⌊A⌋₊ := by
    have h := Nat.floor_mono hA
    simpa using h
  have hupper : A < (⌊A⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one A
  constructor
  · exact hfloor
  · have hfloorR : (1 : ℝ) ≤ (⌊A⌋₊ : ℝ) := by exact_mod_cast hfloor
    linarith

/-- Compare the complete weighted sums at A and the integer defining degree D.
Consumer: reduction.tex:474–481; the ambient dimension bounds the loss by 2^n. -/
theorem global_rank_weighted_compare {n : ℕ} (F : AffineFamily.Family n)
    (A : ℝ) (hA : 1 ≤ A) (D : ℕ) (hD : 1 ≤ D) (hAD : A ≤ 2 * (D : ℝ))
    (hF : ∀ V ∈ F, V.IsIrreducible ∧ V.dimension ≤ n) :
    (∑ V ∈ F, (V.degree : ℝ) * A ^ V.dimension) ≤
      (2 : ℝ) ^ n * (TrackA.affineWeightedDegree F D : ℝ) := by
  have hterm (V : AffineVariety n) (hV : V ∈ F) :
      (V.degree : ℝ) * A ^ V.dimension ≤
        (2 : ℝ) ^ n * ((V.degree : ℝ) * (D : ℝ) ^ V.dimension) := by
    obtain ⟨hVi, hdim⟩ := hF V hV
    have hdegreeQ : 1 ≤ V.degree := AffineVariety.one_le_degree V hVi.ne_top
    have hdegree : 0 ≤ (V.degree : ℝ) := by
      have hdegreeQ0 : (0 : ℚ) ≤ V.degree := le_trans (by norm_num) hdegreeQ
      exact_mod_cast hdegreeQ0
    have hpow : A ^ V.dimension ≤ (2 : ℝ) ^ n * (D : ℝ) ^ V.dimension := by
      calc
        A ^ V.dimension ≤ (2 * (D : ℝ)) ^ V.dimension :=
          pow_le_pow_left₀ (by linarith [hA]) hAD _
        _ = (2 : ℝ) ^ V.dimension * (D : ℝ) ^ V.dimension := by rw [mul_pow]
        _ ≤ (2 : ℝ) ^ n * (D : ℝ) ^ V.dimension := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hdim)
            (by positivity)
    calc
      (V.degree : ℝ) * A ^ V.dimension ≤
          (V.degree : ℝ) * ((2 : ℝ) ^ n * (D : ℝ) ^ V.dimension) :=
        mul_le_mul_of_nonneg_left hpow hdegree
      _ = (2 : ℝ) ^ n * ((V.degree : ℝ) * (D : ℝ) ^ V.dimension) := by ring
  have hsum :
      (∑ V ∈ F, (V.degree : ℝ) * A ^ V.dimension) ≤
        (2 : ℝ) ^ n * ∑ V ∈ F, (V.degree : ℝ) * (D : ℝ) ^ V.dimension := by
    calc
      (∑ V ∈ F, (V.degree : ℝ) * A ^ V.dimension) ≤
          ∑ V ∈ F, (2 : ℝ) ^ n * ((V.degree : ℝ) * (D : ℝ) ^ V.dimension) := by
        apply Finset.sum_le_sum
        intro V hV
        exact hterm V hV
      _ = (2 : ℝ) ^ n * ∑ V ∈ F, (V.degree : ℝ) * (D : ℝ) ^ V.dimension := by
        rw [Finset.mul_sum]
  have hcast :
      (TrackA.affineWeightedDegree F D : ℝ) =
        ∑ V ∈ F, (V.degree : ℝ) * (D : ℝ) ^ V.dimension := by
    simp [TrackA.affineWeightedDegree]
  simpa only [hcast] using hsum

/-- Sum global concentration over the components containing actual pair flats.
The count uses only components of dimension at least C(d,2), then adds the
nonnegative weights of the remaining components, reduction.tex:467–473. -/
theorem global_rank_weighted_count {d : ℕ} (W : Finset (RPoint d × RPoint d))
    (F : AffineFamily.Family (Fintype.card (SkewIdx (d + 1))))
    (C A : ℝ) (hC : 0 < C) (hA : 1 ≤ A) (hF : ∀ V ∈ F, V.IsIrreducible)
    (hcover : ∀ x ∈ W, ∃ V ∈ F,
      skewToPoint '' pairFlat x.1 x.2 ⊆ V.points ∧ Nat.choose d 2 ≤ V.dimension)
    (hcount : ∀ V ∈ F, Nat.choose d 2 ≤ V.dimension →
      ((W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card : ℝ) ≤
        C * (V.degree : ℝ) * A ^ (V.dimension - Nat.choose d 2)) :
    (W.card : ℝ) * A ^ Nat.choose d 2 ≤
      C * ∑ V ∈ F, (V.degree : ℝ) * A ^ V.dimension := by
  classical
  let s := Nat.choose d 2
  let G := F.filter fun V => s ≤ V.dimension
  have hcover' : W ⊆ G.biUnion fun V =>
      W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points := by
    intro x hx
    obtain ⟨V, hV, hcontain, hdim⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr
      ⟨V, Finset.mem_filter.mpr ⟨hV, hdim⟩,
        Finset.mem_filter.mpr ⟨hx, hcontain⟩⟩
  have hcard : (W.card : ℝ) ≤
      ∑ V ∈ G, ((W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card : ℝ) := by
    have hnat : W.card ≤ (G.biUnion fun V =>
        W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card :=
      Finset.card_le_card hcover'
    have hsumNat : (G.biUnion fun V =>
        W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card ≤
        ∑ V ∈ G, (W.filter fun x =>
          skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card := Finset.card_biUnion_le
    exact_mod_cast hnat.trans hsumNat
  have hpowNonneg : 0 ≤ A ^ s := pow_nonneg (le_trans (by norm_num) hA) _
  have hbase := mul_le_mul_of_nonneg_right hcard hpowNonneg
  have hterm (V : AffineVariety (Fintype.card (SkewIdx (d + 1)))) (hV : V ∈ G) :
      ((W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card : ℝ) * A ^ s ≤
        C * (V.degree : ℝ) * A ^ V.dimension := by
    have hVF : V ∈ F := (Finset.mem_filter.mp hV).1
    have hdim : s ≤ V.dimension := (Finset.mem_filter.mp hV).2
    have hc := hcount V hVF hdim
    calc
      _ = A ^ s * ((W.filter fun x =>
          skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card : ℝ) := by ring
      _ ≤ A ^ s * (C * (V.degree : ℝ) * A ^ (V.dimension - s)) :=
        mul_le_mul_of_nonneg_left hc hpowNonneg
      _ = C * (V.degree : ℝ) * (A ^ s * A ^ (V.dimension - s)) := by ring
      _ = C * (V.degree : ℝ) * A ^ V.dimension := by
        have hexp : s + (V.dimension - s) = V.dimension := by omega
        rw [← pow_add, hexp]
  have hsumterm :
      (∑ V ∈ G, ((W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card : ℝ)) * A ^ s ≤
        ∑ V ∈ G, C * (V.degree : ℝ) * A ^ V.dimension := by
    calc
      _ = ∑ V ∈ G, ((W.filter fun x =>
          skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card : ℝ) * A ^ s := by
        rw [Finset.sum_mul]
      _ ≤ ∑ V ∈ G, C * (V.degree : ℝ) * A ^ V.dimension := by
        exact Finset.sum_le_sum fun V hV => hterm V hV
  have hdegreeNonneg (V : AffineVariety (Fintype.card (SkewIdx (d + 1))))
      (hV : V ∈ F) : 0 ≤ (V.degree : ℝ) := by
    have hdeg := AffineVariety.one_le_degree V (hF V hV).ne_top
    have hdeg0 : (0 : ℚ) ≤ V.degree := le_trans (by norm_num) hdeg
    exact_mod_cast hdeg0
  have hsumSubset :
      (∑ V ∈ G, (V.degree : ℝ) * A ^ V.dimension) ≤
        ∑ V ∈ F, (V.degree : ℝ) * A ^ V.dimension :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun V hV _ =>
      mul_nonneg (hdegreeNonneg V hV) (pow_nonneg (le_trans (by norm_num) hA) _)
  calc
    (W.card : ℝ) * A ^ s ≤
        (∑ V ∈ G, ((W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card : ℝ)) * A ^ s := hbase
    _ ≤ ∑ V ∈ G, C * (V.degree : ℝ) * A ^ V.dimension := hsumterm
    _ = C * ∑ V ∈ G, (V.degree : ℝ) * A ^ V.dimension := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro V hV
      ring
    _ ≤ C * ∑ V ∈ F, (V.degree : ℝ) * A ^ V.dimension :=
      mul_le_mul_of_nonneg_left hsumSubset (le_of_lt hC)

/-- The component family at the defining degree has exactly the original
restriction rank, using envelope_hilbert and the proved finite-coordinate bridge.
Consumer: reduction.tex:474–481. -/
theorem global_rank_envelope_hilbert {d : ℕ} (W : Finset (RPoint d × RPoint d)) (D : ℕ)
    (F : AffineFamily.Family (Fintype.card (SkewIdx (d + 1))))
    (hF : AffineFamily.locus F = envelope (skewToPoint '' (⋃ x ∈ W, pairFlat x.1 x.2)) D) :
    AffineFamily.hilbert F D = restrictionRank (⋃ x ∈ W, pairFlat x.1 x.2) D := by
  rw [AffineFamily.hilbert, hF, envelope_hilbert]
  have hskew : skewToPoint (e := d + 1) =
      (fun z : SkewIdx (d + 1) → ℂ =>
        fun i => z ((Fintype.equivFin (SkewIdx (d + 1))).symm i)) := rfl
  rw [hskew]
  exact (Bridges.restrictionRank_eq_hilbertOfSet
    (Fintype.equivFin (SkewIdx (d + 1))) (⋃ x ∈ W, pairFlat x.1 x.2) D).symm

end
end DistinctDistances.Reduction
