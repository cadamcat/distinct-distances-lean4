import OAI.AlgebraicGeometry.PlaneCurves.Factorization
import DistinctDistances.TrackA.RadialGenericDegreeSupport
import DistinctDistances.TrackA.DepthHypotheses
import DistinctDistances.TrackA.SylvesterMatrixSupport
import DistinctDistances.TrackA.GcdSpecializationSupport
import DistinctDistances.TrackA.SimultaneousRadialFiberSupport
import DistinctDistances.TrackA.NarrowRootBoundSupport
import DistinctDistances.TrackA.ComponentSeparatorAux

namespace DistinctDistances.TrackA
noncomputable section
open Filter
open scoped BigOperators Classical Topology

/-- `dep:projection-degree-exists`, depth.tex:108–125.
An irreducible dimension-preserving radial image has genuine generic finite degree. -/
theorem dep_radial_degree_exists {d : ℕ} (Y : AffineVariety d) (hY : Y.IsIrreducible)
    (l : ℕ) (hl : 1 ≤ l) (hdim : Y.dimension = l) (p : Point d)
    (himage : (radialImage p Y).dimension = l) :
    GenericallyFiniteRadialDegree p Y (radialMapDegree p Y) := by
  have hex := radial_generic_degree_exists Y hY hl hdim p himage
  simpa only [radialMapDegree, dif_pos hex] using hex.choose_spec

/-- `dep:depth-to-degree`, depth.tex:120–137. Images are pooled exactly once. -/
theorem dep_depth_to_degree {d : ℕ} (J : AffineFamily.Family d) (l : ℕ)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l) (p : Point d) (R : ℚ)
    (himages : ∀ Y ∈ J, (radialImage p Y).dimension = l)
    (hmult : ∀ Y ∈ J, Y.multiplicity p ≤ Y.degree / 2)
    (hdepth : ∀ Y ∈ J, (groupDepth p J Y : ℚ) ≤ R) :
    AffineFamily.degree J ≤ 2 * R * ProjectiveFamily.degree (projectedFamily p J) := by
  classical
  let F : ProjectiveFamily.Family d := projectedFamily p J
  have himageDegreeNonneg (Y : AffineVariety d) : 0 ≤ (radialImage p Y).degree := by
    unfold ProjectiveVariety.degree
    exact OAI.PiExponentJets.W22.actualMultiplicity_nonneg _ _ _ (le_rfl)
  have hcarrierBound (Y : AffineVariety d) (hY : Y ∈ J) :
      Y.degree ≤ 2 * (radialMapDegree p Y : ℚ) * (radialImage p Y).degree := by
    obtain ⟨hYirr, hYdim⟩ := hJ Y hY
    have hfinite := dep_radial_degree_exists Y hYirr l hl hYdim p (himages Y hY)
    have hformula := poly_projection_radial Y hYirr l hl hYdim p (himages Y hY)
      (radialMapDegree p Y) hfinite
    linarith [hmult Y hY]
  have hfiberBound (Y : AffineVariety d) (hY : Y ∈ J) :
      (∑ Z ∈ J.filter (fun Z => radialImage p Z = radialImage p Y), Z.degree) ≤
        2 * (groupDepth p J Y : ℚ) * (radialImage p Y).degree := by
    let fiber := J.filter (fun Z => radialImage p Z = radialImage p Y)
    calc
      (∑ Z ∈ fiber, Z.degree) ≤
          ∑ Z ∈ fiber, 2 * (radialMapDegree p Z : ℚ) * (radialImage p Y).degree := by
        apply Finset.sum_le_sum
        intro Z hZ
        obtain ⟨hZJ, hZimage⟩ := Finset.mem_filter.mp hZ
        have hZbound := hcarrierBound Z hZJ
        rw [hZimage] at hZbound
        exact hZbound
      _ = (∑ Z ∈ fiber, (radialMapDegree p Z : ℚ)) *
          (2 * (radialImage p Y).degree) := by
        calc
          (∑ Z ∈ fiber, 2 * (radialMapDegree p Z : ℚ) * (radialImage p Y).degree) =
              ∑ Z ∈ fiber, (radialMapDegree p Z : ℚ) *
                (2 * (radialImage p Y).degree) := by
            apply Finset.sum_congr rfl
            intro Z hZ
            ring
          _ = (∑ Z ∈ fiber, (radialMapDegree p Z : ℚ)) *
              (2 * (radialImage p Y).degree) := (Finset.sum_mul ..).symm
      _ = 2 * (groupDepth p J Y : ℚ) * (radialImage p Y).degree := by
        simp [fiber, groupDepth, Nat.cast_sum]
        ring
  have hgroupBound (W : ProjectiveVariety d) (hW : W ∈ F) :
      (∑ Z ∈ J.filter (fun Z => radialImage p Z = W), Z.degree) ≤ 2 * R * W.degree := by
    obtain ⟨Y₀, hY₀, hY₀W⟩ := Finset.mem_image.mp hW
    have hfiber := hfiberBound Y₀ hY₀
    rw [← hY₀W]
    calc
      (∑ Z ∈ J.filter (fun Z => radialImage p Z = radialImage p Y₀), Z.degree) ≤
          2 * (groupDepth p J Y₀ : ℚ) * (radialImage p Y₀).degree := hfiber
      _ ≤ 2 * R * (radialImage p Y₀).degree := by
        calc
          2 * (groupDepth p J Y₀ : ℚ) * (radialImage p Y₀).degree =
              2 * ((groupDepth p J Y₀ : ℚ) * (radialImage p Y₀).degree) := by ring
          _ ≤ 2 * (R * (radialImage p Y₀).degree) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hdepth Y₀ hY₀) (himageDegreeNonneg Y₀)) (by norm_num)
          _ = 2 * R * (radialImage p Y₀).degree := by ring
  have hfilterImage : J.filter (fun Y => radialImage p Y ∈ F) = J := by
    apply Finset.filter_eq_self.mpr
    intro Y hY
    exact Finset.mem_image.mpr ⟨Y, hY, rfl⟩
  have hpartition :
      (∑ Y ∈ J, Y.degree) =
        ∑ W ∈ F, ∑ Y ∈ J.filter (fun Y => radialImage p Y = W), Y.degree := by
    calc
      (∑ Y ∈ J, Y.degree) =
          ∑ Y ∈ J.filter (fun Y => radialImage p Y ∈ F), Y.degree := by rw [hfilterImage]
      _ = ∑ W ∈ F, ∑ Y ∈ J.filter (fun Y => radialImage p Y = W), Y.degree :=
        (Finset.sum_fiberwise_eq_sum_filter J F (radialImage p) (fun Y => Y.degree)).symm
  change (∑ Y ∈ J, Y.degree) ≤ 2 * R * (∑ W ∈ F, W.degree)
  calc
    (∑ Y ∈ J, Y.degree) =
        ∑ W ∈ F, ∑ Y ∈ J.filter (fun Y => radialImage p Y = W), Y.degree := hpartition
    _ ≤ ∑ W ∈ F, 2 * R * W.degree := Finset.sum_le_sum fun W hW => hgroupBound W hW
    _ = 2 * R * (∑ W ∈ F, W.degree) := by rw [Finset.mul_sum]

/-- `dep:row-deletion`, depth.tex:139–144. Grade impl: weighted finite Markov. -/
theorem dep_row_deletion {d : ℕ} (centers : Finset (Point d))
    (J : AffineFamily.Family d) (mass : AffineVariety d → ℕ)
    (hcenters : 1 ≤ centers.card) (hmass : 1 ≤ ∑ Y ∈ J, mass Y)
    (bad : Finset (Point d × AffineVariety d)) (hbad : bad ⊆ centers.product J) :
    let total : ℝ := ∑ Y ∈ J, (mass Y : ℝ)
    let α : ℝ := (∑ a ∈ bad, (mass a.2 : ℝ)) / ((centers.card : ℝ) * total)
    ∃ badCenters : Finset (Point d), badCenters ⊆ centers ∧
      (badCenters.card : ℝ) ≤ (centers.card : ℝ) * Real.sqrt α ∧
      ∀ p ∈ centers, p ∉ badCenters →
        (∑ Y ∈ J.filter (fun Y => (p,Y) ∈ bad), (mass Y : ℝ)) ≤ total * Real.sqrt α := by
  classical
  dsimp only
  let total : ℝ := ∑ Y ∈ J, (mass Y : ℝ)
  let badMass : ℝ := ∑ a ∈ bad, (mass a.2 : ℝ)
  let α : ℝ := badMass / ((centers.card : ℝ) * total)
  change ∃ badCenters : Finset (Point d), badCenters ⊆ centers ∧
    (badCenters.card : ℝ) ≤ (centers.card : ℝ) * Real.sqrt α ∧
    ∀ p ∈ centers, p ∉ badCenters →
      (∑ Y ∈ J.filter (fun Y => (p,Y) ∈ bad), (mass Y : ℝ)) ≤ total * Real.sqrt α
  have hcentersPos : 0 < (centers.card : ℝ) := by
    have h : 0 < centers.card := by omega
    exact_mod_cast h
  have htotalPos : 0 < total := by
    dsimp [total]
    have h : 0 < ∑ Y ∈ J, mass Y := by omega
    exact_mod_cast h
  have hdenPos : 0 < (centers.card : ℝ) * total := mul_pos hcentersPos htotalPos
  have hbadMassNonneg : 0 ≤ badMass := by
    dsimp [badMass]
    exact Finset.sum_nonneg fun a ha => Nat.cast_nonneg (mass a.2)
  have hαNonneg : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg hbadMassNonneg hdenPos.le
  have hrootNonneg : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hrootSq : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hαNonneg
  have hbalance : badMass = α * (centers.card : ℝ) * total := by
    dsimp [α]
    field_simp [ne_of_gt hdenPos]
  let rowMass : Point d → ℝ := fun p =>
    ∑ Y ∈ J.filter (fun Y => (p,Y) ∈ bad), (mass Y : ℝ)
  have hrowNonneg (p : Point d) : 0 ≤ rowMass p := by
    dsimp [rowMass]
    exact Finset.sum_nonneg fun Y hY => Nat.cast_nonneg (mass Y)
  have hrowSum : (∑ p ∈ centers, rowMass p) = badMass := by
    dsimp [rowMass, badMass]
    simp only [Finset.sum_filter]
    change (∑ p ∈ centers, ∑ Y ∈ J,
      (fun a : Point d × AffineVariety d =>
        if a ∈ bad then (mass a.2 : ℝ) else 0) (p,Y)) = _
    rw [← Finset.sum_product']
    change (∑ a ∈ centers.product J,
      if a ∈ bad then (mass a.2 : ℝ) else 0) = _
    rw [← Finset.sum_filter]
    have hfilter : (centers.product J).filter (fun a => a ∈ bad) = bad := by
      apply Finset.ext
      intro a
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro ha
        exact ⟨hbad ha, ha⟩
    rw [hfilter]
  let threshold : ℝ := total * Real.sqrt α
  let badCenters : Finset (Point d) := centers.filter (fun p => threshold < rowMass p)
  have hbadCentersSubset : badCenters ⊆ centers := Finset.filter_subset _ _
  have hrowThreshold (p : Point d) (hp : p ∈ centers) (hpnot : p ∉ badCenters) :
      rowMass p ≤ threshold := by
    apply le_of_not_gt
    intro hlarge
    exact hpnot (Finset.mem_filter.mpr ⟨hp, hlarge⟩)
  have hbadRowsLower : (badCenters.card : ℝ) * threshold ≤
      ∑ p ∈ badCenters, rowMass p := by
    calc
      (badCenters.card : ℝ) * threshold = ∑ _p ∈ badCenters, threshold := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ badCenters, rowMass p :=
        Finset.sum_le_sum fun p hp => le_of_lt (Finset.mem_filter.mp hp).2
  have hbadRowsUpper : (∑ p ∈ badCenters, rowMass p) ≤ badMass := by
    calc
      (∑ p ∈ badCenters, rowMass p) ≤ ∑ p ∈ centers, rowMass p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hbadCentersSubset
        intro p hp hpn
        exact hrowNonneg p
      _ = badMass := hrowSum
  refine ⟨badCenters, hbadCentersSubset, ?_, ?_⟩
  · by_cases hrootZero : Real.sqrt α = 0
    · have hαZero : α = 0 := by rw [← hrootSq, hrootZero]; simp
      have hbadMassZero : badMass = 0 := by rw [hbalance, hαZero]; ring
      have hrowLeBadMass (p : Point d) (hp : p ∈ centers) : rowMass p ≤ badMass := by
        calc
          rowMass p ≤ ∑ q ∈ centers, rowMass q := by
            have hsingle : ({p} : Finset (Point d)) ⊆ centers := by simp [hp]
            have hs := Finset.sum_le_sum_of_subset_of_nonneg hsingle
              (fun q hq hqnot => hrowNonneg q)
            simpa using hs
          _ = badMass := hrowSum
      have hbadCentersEmpty : badCenters = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hlarge := (Finset.mem_filter.mp hp).2
        have hrowzero : rowMass p ≤ 0 := by
          simpa [hbadMassZero] using hrowLeBadMass p (Finset.mem_filter.mp hp).1
        have hthresholdZero : threshold = 0 := by simp [threshold, hrootZero]
        linarith
      simp [hbadCentersEmpty, hrootZero]
    · have hrootPos : 0 < Real.sqrt α :=
        lt_of_le_of_ne hrootNonneg (Ne.symm hrootZero)
      by_contra hlarge
      have hcount : (centers.card : ℝ) * Real.sqrt α < (badCenters.card : ℝ) :=
        lt_of_not_ge hlarge
      have hcountMul := mul_lt_mul_of_pos_right hcount (mul_pos htotalPos hrootPos)
      have hbalanceRoot :
          (centers.card : ℝ) * Real.sqrt α * (total * Real.sqrt α) =
            α * (centers.card : ℝ) * total := by
        calc
          (centers.card : ℝ) * Real.sqrt α * (total * Real.sqrt α) =
              (Real.sqrt α) ^ 2 * (centers.card : ℝ) * total := by ring
          _ = α * (centers.card : ℝ) * total := by rw [hrootSq]
      have hbadRowsUpper' : (badCenters.card : ℝ) * threshold ≤
          α * (centers.card : ℝ) * total := by
        calc
          (badCenters.card : ℝ) * threshold ≤ ∑ p ∈ badCenters, rowMass p := hbadRowsLower
          _ ≤ badMass := hbadRowsUpper
          _ = α * (centers.card : ℝ) * total := hbalance
      dsimp [threshold] at hcountMul hbadRowsUpper'
      rw [hbalanceRoot] at hcountMul
      linarith
  · intro p hp hpnot
    simpa [rowMass, threshold] using hrowThreshold p hp hpnot

/-- `dep:first-cut-depth`, depth.tex:146–168. A proper ray section counts all groups. -/
theorem dep_first_cut_depth {d : ℕ} (J : AffineFamily.Family d) (l : ℕ)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l) (Y : AffineVariety d) (hY : Y ∈ J)
    (p : Point d) (himage : (radialImage p Y).dimension = l)
    (f : Poly d) (L : ℕ) (hf : f.totalDegree ≤ L)
    (hzero : ∀ Z ∈ J, f ∈ Z.ideal)
    (hproper : ∃ y ∈ Y.points, ∃ t : ℂ, MvPolynomial.eval (p + t • (y-p)) f ≠ 0) :
    groupDepth p J Y ≤ L := by
  let G := J.filter (fun Z => radialImage p Z = radialImage p Y)
  have hGJ : G ⊆ J := Finset.filter_subset _ _
  have hG : AffineFamily.IsPure G l := fun Z hZ => hJ Z (hGJ hZ)
  have hYG : Y ∈ G := Finset.mem_filter.mpr ⟨hY, rfl⟩
  have himages : ∀ Z ∈ G, radialImage p Z = radialImage p Y :=
    fun Z hZ => (Finset.mem_filter.mp hZ).2
  have hgeneric : ∀ Z ∈ G, GenericallyFiniteRadialDegree p Z (radialMapDegree p Z) := by
    intro Z hZ
    exact dep_radial_degree_exists Z (hG Z hZ).1 l hl (hG Z hZ).2 p
      (by rw [himages Z hZ]; exact himage)
  obtain ⟨z, hz, hQne, hfibers, hdisjoint⟩ := simultaneous_radial_fibers G hl hG Y hYG p
    himage himages (radialMapDegree p) hgeneric f (hzero Y hY) hproper
  have hcount := radial_fiber_sum_le_ray_degree G p z f
    (fun Z hZ => hzero Z (hGJ hZ)) (fun Z hZ => (hfibers Z hZ).1) hdisjoint hQne
  have hsum : (∑ Z ∈ G, (radialFiber p Z z).ncard) = ∑ Z ∈ G, radialMapDegree p Z :=
    Finset.sum_congr rfl (fun Z hZ => (hfibers Z hZ).2)
  change (∑ Z ∈ G, radialMapDegree p Z) ≤ L
  rw [← hsum]
  exact hcount.trans hf

/-- `dep:narrow-root-count`, depth.tex:170–204. Isolated centers and moving roots. -/
theorem dep_narrow_root_count (d : ℕ) :
    ∃ C : ℚ, 0 < C ∧ ∀ (J : AffineFamily.Family d) (l : ℕ),
      1 ≤ l → AffineFamily.IsPure J l → ∀ (Y : AffineVariety d), Y ∈ J →
      ∀ (S : Finset (Point d)) (E : Set (Poly d)) (L : ℕ),
      1 ≤ L → (∀ f ∈ E, f.totalDegree ≤ L) → IsolatedPoints E S →
      (∀ p ∈ S, (radialImage p Y).dimension = l) →
      (∑ p ∈ S, ((groupDepth p J Y - 1 : ℕ) : ℚ)) ≤
        C * AffineFamily.degree J * (L : ℚ)^(l+1) := by
  refine ⟨((d+1 : ℕ) : ℚ) * (2 : ℚ)^(d+1), by positivity, ?_⟩
  intro J l hl hJ Y hY S E L hL hE hS himage
  exact narrow_root_count_bound J hl hJ Y hY S E L hL hE hS himage

/-- `dep:sylvester-rank`, depth.tex:363–374. Includes exactly-one-zero specialization. -/
theorem dep_sylvester_rank {F : Type*} [Field F] (L : ℕ) (hL : 1 ≤ L)
    (f g : MvPolynomial (Fin 2) F) (hf : f.IsHomogeneous L) (hg : g.IsHomogeneous L)
    (hnonzero : f ≠ 0 ∨ g ≠ 0) :
    Matrix.rank (sylvesterMatrix L f g) = 2*L - (binaryGcd f g).totalDegree := by
  exact sylvester_rank_core L hL f g hf hg hnonzero

/-- `dep:gcd-specialization`, depth.tex:382–401. Full divisor length at singular centers. -/
theorem dep_gcd_specialization {d : ℕ} (X : AffineVariety d) (hX : X.IsIrreducible)
    (F G : BinaryForm d) (L : ℕ) (hF : F.IsHomogeneous L) (hG : G.IsHomogeneous L)
    (p : Point d) (hp : p ∈ X.points) :
    ∃ H : Poly 2, H ≠ 0 ∧ H.IsHomogeneous (genericGcdDegree X hX F G) ∧
      H ∣ specializeBinary F p ∧ H ∣ specializeBinary G p := by
  letI : X.ideal.IsPrime := hX
  let R := Poly d ⧸ X.ideal
  let K := FractionRing R
  let η : Poly d →+* K := (algebraMap R K).comp (Ideal.Quotient.mk X.ideal)
  let f := MvPolynomial.map η F
  let g := MvPolynomial.map η G
  let f₀ := specializeBinary F p
  let g₀ := specializeBinary G p
  let h := genericGcdDegree X hX F G
  have hh : h = (binaryGcd f g).totalDegree := rfl
  have hf : f.IsHomogeneous L := hF.map η
  have hg : g.IsHomogeneous L := hG.map η
  have hf₀ : f₀.IsHomogeneous L := hF.map (MvPolynomial.eval p)
  have hg₀ : g₀.IsHomogeneous L := hG.map (MvPolynomial.eval p)
  have hhL : h ≤ L := hh ▸ binary_gcd_degree_le f g L hf hg
  by_cases hL : L = 0
  · have h0 : h = 0 := by omega
    refine ⟨1, one_ne_zero, ?_, one_dvd _, one_dvd _⟩
    change (1 : Poly 2).IsHomogeneous h
    rw [h0]
    exact MvPolynomial.isHomogeneous_one _ _
  by_cases hzero : f₀ = 0 ∧ g₀ = 0
  · refine ⟨MvPolynomial.X 0 ^ h, pow_ne_zero _ (MvPolynomial.X_ne_zero _), ?_, ?_, ?_⟩
    · simpa only [one_mul] using (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).pow h
    · change MvPolynomial.X 0 ^ h ∣ f₀
      rw [hzero.1]
      exact dvd_zero _
    · change MvPolynomial.X 0 ^ h ∣ g₀
      rw [hzero.2]
      exact dvd_zero _
  have hnonzero₀ : f₀ ≠ 0 ∨ g₀ ≠ 0 := by tauto
  have hnonzero : f ≠ 0 ∨ g ≠ 0 := by
    rcases hnonzero₀ with hf0 | hg0
    · exact Or.inl (fun hz => hf0 (generic_binary_zero_specializes X hX F p hp hz))
    · exact Or.inr (fun hz => hg0 (generic_binary_zero_specializes X hX G p hp hz))
  have hrank := sylvester_rank_specialization X hX F G L p hp
  have hgeneric := dep_sylvester_rank L (by omega) f g hf hg hnonzero
  have hspecial := dep_sylvester_rank L (by omega) f₀ g₀ hf₀ hg₀ hnonzero₀
  change (sylvesterMatrix L f₀ g₀).rank ≤ (sylvesterMatrix L f g).rank at hrank
  rw [hgeneric, hspecial, ← hh] at hrank
  have hspecialL := binary_gcd_degree_le f₀ g₀ L hf₀ hg₀
  have hle : h ≤ (binaryGcd f₀ g₀).totalDegree := by omega
  exact binary_common_divisor_of_degree f₀ g₀ L h hf₀ hg₀ hnonzero₀ hle

/-- `dep:wide-rank-loss`, depth.tex:301–438. The generic list bound controls
only the supported distinguished roots of the limiting gcd; omitted components remain in E. -/
theorem dep_wide_rank_loss {d : ℕ} (X : AffineVariety d) (hX : X.IsIrreducible)
    (J : AffineFamily.Family d) (l : ℕ) (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l)
    (Y : AffineVariety d) (hY : Y ∈ J) (E : Set (Poly d)) (L q r : ℕ)
    (hL : 1 ≤ L) (hrL : r ≤ L) (hgap : 2*q+8 ≤ r)
    (hE : ∀ f ∈ E, f.totalDegree ≤ L)
    (hcomponents : ∀ Z ∈ J, Z.IsComponentOf (Ideal.span E))
    (hgeneric : GenericMovingRootBound X Y J q)
    (S : Finset (Point d)) (hS : ∀ p ∈ S, p ∈ X.points)
    (himages : ∀ p ∈ S, (radialImage p Y).dimension = l) :
    ∃ (A : Matrix (Fin (2*L)) (Fin (2*L)) (Poly d)) (ρ : ℕ),
      L ≤ ρ ∧ ρ ≤ 2*L ∧ (∀ i j, (A i j).totalDegree ≤ L) ∧ GenericMatrixRank X A ρ ∧
      ∀ p ∈ S, r < groupDepth p J Y →
        Matrix.rank (fun i j => MvPolynomial.eval p (A i j)) ≤ ρ-r/2 := by
  have hsylvester : A2SylvesterRank := by
    intro K instK B hB f g hf hg hnonzero
    exact dep_sylvester_rank B hB f g hf hg hnonzero
  exact a2_wide_rank_loss_package hsylvester X hX J l hl hJ Y hY E L q r
    hL hrL hgap hE hcomponents hgeneric S hS himages

/-- `dep:wide-proper-test`, depth.tex:439–458. Compression detects actual centers. -/
theorem dep_wide_proper_test {d : ℕ} (X : AffineVariety d) (hX : X.IsIrreducible)
    (J : AffineFamily.Family d) (l : ℕ) (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l)
    (Y : AffineVariety d) (hY : Y ∈ J) (E : Set (Poly d)) (L q r : ℕ)
    (hL : 1 ≤ L) (hrL : r ≤ L) (hgap : 2*q+8 ≤ r)
    (hE : ∀ f ∈ E, f.totalDegree ≤ L)
    (hcomponents : ∀ Z ∈ J, Z.IsComponentOf (Ideal.span E))
    (hgeneric : GenericMovingRootBound X Y J q)
    (S : Finset (Point d)) (hS : ∀ p ∈ S, p ∈ X.points)
    (himages : ∀ p ∈ S, (radialImage p Y).dimension = l) :
    ∃ g : Poly d, g ∉ X.ideal ∧ (r/2) * g.totalDegree ≤ (d+1) * (2*L^2) ∧
      ∀ p ∈ S, r < groupDepth p J Y → MvPolynomial.eval p g = 0 := by
  classical
  obtain ⟨A, ρ, hρLower, hρUpper, hAdegree, hGenericRank, hRankDrop⟩ :=
    dep_wide_rank_loss X hX J l hl hJ Y hY E L q r hL hrL hgap hE hcomponents
      hgeneric S hS himages
  rcases hGenericRank with ⟨_, rows, cols, hminorNot⟩
  let Q : Poly d := Matrix.det (A.submatrix rows cols)
  have hdetDegree (B : Matrix (Fin ρ) (Fin ρ) (Poly d))
      (hB : ∀ i j, (B i j).totalDegree ≤ L) :
      B.det.totalDegree ≤ ρ * L := by
    rw [Matrix.det_apply]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro σ hσ
    calc
      (Equiv.Perm.sign σ • ∏ i : Fin ρ, B (σ i) i).totalDegree ≤
          (∏ i : Fin ρ, B (σ i) i).totalDegree :=
        MvPolynomial.totalDegree_smul_le _ _
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin ρ)), (B (σ i) i).totalDegree := by
        simpa using MvPolynomial.totalDegree_finsetProd
          (Finset.univ : Finset (Fin ρ)) (fun i => B (σ i) i)
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin ρ)), L := by
        apply Finset.sum_le_sum
        intro i hi
        exact hB (σ i) i
      _ = ρ * L := by simp
  have hQdegree : Q.totalDegree ≤ 2 * L^2 := by
    calc
      Q.totalDegree ≤ ρ * L := by
        simpa [Q] using hdetDegree (A.submatrix rows cols)
          (fun i j => hAdegree (rows i) (cols j))
      _ ≤ (2 * L) * L := Nat.mul_le_mul_right L hρUpper
      _ = 2 * L^2 := by ring
  have hQnotVan : Q ∉ MvPolynomial.vanishingIdeal ℂ X.points := by
    simpa [Q, AffineVariety.vanishingIdeal_points] using hminorNot
  have hQnotAll : ¬ ∀ x ∈ X.points, MvPolynomial.eval x Q = 0 := by
    simpa only [MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.aeval_eq_eval]
      using hQnotVan
  push_neg at hQnotAll
  obtain ⟨x, hx, hQx⟩ := hQnotAll
  have hhalfPos : 1 ≤ r/2 := by omega
  have hhalfLe : r/2 ≤ ρ := by omega
  let highS := S.filter (fun p => r < groupDepth p J Y)
  obtain ⟨g, hdegree, hzero, htest⟩ :=
    poly_matrix_multiplicity_compression A highS x rows cols hhalfPos hhalfLe
      (2 * L^2) (by simpa [Q] using hQdegree)
      (by
        intro p hp
        exact hRankDrop p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2) hQx
  have hgnot : g ∉ X.ideal := by
    intro hg
    have heval := (MvPolynomial.mem_zeroLocus_iff.mp hx) g hg
    apply htest
    simpa only [MvPolynomial.aeval_eq_eval] using heval
  refine ⟨g, hgnot, hdegree, ?_⟩
  intro p hp hdepth
  exact hzero p (Finset.mem_filter.mpr ⟨hp, hdepth⟩)

end
end DistinctDistances.TrackA
