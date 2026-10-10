import DistinctDistances.TrackE.CommonCarrierData
import DistinctDistances.TrackE.CommonPhysicalData
import DistinctDistances.TrackE.CommonProfiles
import DistinctDistances.TrackE.SelectionSequence
import DistinctDistances.TrackE.WideAssignments
import DistinctDistances.TrackD.Profiles.Defs
import DistinctDistances.TrackD.Profiles.Partition
import DistinctDistances.TrackD.Profiles.PoolFamilies
import DistinctDistances.TrackD.Profiles.Regularity
import DistinctDistances.TrackD.Profiles.RegularityMass
import DistinctDistances.TrackE.NarrowScale
import DistinctDistances.TrackE.RequestsWideFlat
import DistinctDistances.Framework.Asymptotics

/-! Helpers for m-e-carrier leaves 133, 135, 138. -/
namespace DistinctDistances.SparseCones.MECarrierAux
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Real nonneg sums over a biUnion are bounded by the double sum. -/
theorem sum_biUnion_le_aux {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ)
    (hf : ∀ y ∈ s.biUnion t, 0 ≤ f y) :
    ∑ y ∈ s.biUnion t, f y ≤ ∑ x ∈ s, ∑ y ∈ t x, f y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hf_s : ∀ y ∈ s.biUnion t, 0 ≤ f y := by
      intro y hy
      obtain ⟨X, hX, hyX⟩ := Finset.mem_biUnion.mp hy
      exact hf y (Finset.mem_biUnion.mpr ⟨X, Finset.mem_insert_of_mem hX, hyX⟩)
    have ih' := ih hf_s
    have h_union_le : ∑ y ∈ t a ∪ s.biUnion t, f y ≤
        (∑ y ∈ t a, f y) + (∑ y ∈ s.biUnion t, f y) := by
      have h_eq : t a ∪ s.biUnion t = t a ∪ ((s.biUnion t) \ t a) := by
        ext y
        simp only [Finset.mem_union, Finset.mem_sdiff]
        tauto
      have h_disj : Disjoint (t a) ((s.biUnion t) \ t a) :=
        Finset.sdiff_disjoint.symm
      rw [h_eq, Finset.sum_union h_disj]
      have h_sub : (s.biUnion t) \ t a ⊆ s.biUnion t := Finset.sdiff_subset
      have h_le : ∑ y ∈ (s.biUnion t) \ t a, f y ≤ ∑ y ∈ s.biUnion t, f y :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun y hy _ => hf_s y hy)
      linarith
    exact h_union_le.trans (add_le_add le_rfl ih')

/-- 133: fibers partition the set. -/
theorem owner_family_mass_aux (S : Finset (RPoint d))
    (α : RPoint d → AffineVariety d) :
    TrackD.famMass (commonOwnerFamily S α) (commonOwnerFiber S α) = (S.card : ℝ) := by
  classical
  simp only [TrackD.famMass, commonOwnerFamily, commonOwnerFiber]
  have h := Finset.sum_card_fiberwise_eq_card_filter S (S.image α) α
  have hfilter : S.filter (fun q => α q ∈ S.image α) = S := by
    apply Finset.filter_true_of_mem
    intro q hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hNat : ∑ Z ∈ S.image α, (S.filter (fun q => α q = Z)).card = S.card := by
    rw [h, hfilter]
  calc ∑ Z ∈ S.image α, (((S.filter (fun q => α q = Z)).card : ℕ) : ℝ)
      = (((∑ Z ∈ S.image α, (S.filter (fun q => α q = Z)).card) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
    _ = (S.card : ℝ) := by rw [hNat]

/-- Per-factor cut bound. -/
theorem cutScale_le_aux (B s : ℝ) (t b : Fin d → ℝ) (ρ : ℝ)
    (hB : 0 < B) (hs : 0 ≤ s)
    (hclose : ∀ a, |t a - b a| ≤ ρ) (a : Fin d) :
    TrackD.cutScale B s t a ≤ TrackD.cutScale B s b a * Real.exp (ρ * s) := by
  unfold TrackD.cutScale TrackD.testDeg
  have habs := hclose a
  have hle1 : t a - b a ≤ ρ := (abs_le.mp habs).2
  have hle : t a * s ≤ b a * s + ρ * s := by
    have h2 : (t a - b a) * s ≤ ρ * s :=
      mul_le_mul_of_nonneg_right hle1 hs
    linarith
  have hexp_le : Real.exp (t a * s) ≤ Real.exp (b a * s + ρ * s) :=
    Real.exp_le_exp.mpr hle
  calc B * Real.exp (t a * s)
      ≤ B * Real.exp (b a * s + ρ * s) :=
        mul_le_mul_of_nonneg_left hexp_le hB.le
    _ = (B * Real.exp (b a * s)) * Real.exp (ρ * s) := by
        rw [Real.exp_add]
        ring

theorem cutScale_pos_aux (B s : ℝ) (t : Fin d → ℝ) (hB : 0 < B) (a : Fin d) :
    0 < TrackD.cutScale B s t a := by
  unfold TrackD.cutScale TrackD.testDeg
  exact mul_pos hB (Real.exp_pos _)

theorem eScale_pos_aux (B s : ℝ) (t : Fin d → ℝ) (hB : 0 < B) (j : ℕ) :
    0 < TrackD.eScale B s t j := by
  unfold TrackD.eScale
  apply Finset.prod_pos
  intro i _
  exact cutScale_pos_aux B s t hB i

/-- 135: scale closeness. -/
theorem scale_closeness_aux (B N s ρ : ℝ) (b t : Fin d → ℝ)
    (hB : 0 < B) (hs : 0 ≤ s) (hρ : 0 ≤ ρ)
    (hb : ∑ a, b a = 0) (hBN : B ^ d = N)
    (hclose : ∀ a, |t a - b a| ≤ ρ) (j : ℕ) :
    TrackD.eScale B s t j ≤
      TrackD.eScale B s b j * Real.exp ((d : ℝ) * ρ * s) ∧
    TrackD.tailScale B s t j ≤
      (N / TrackD.eScale B s b j) * Real.exp ((d : ℝ) * ρ * s) := by
  classical
  have hcut : ∀ a, TrackD.cutScale B s t a ≤
      TrackD.cutScale B s b a * Real.exp (ρ * s) :=
    fun a => cutScale_le_aux B s t b ρ hB hs hclose a
  have hcut_nn : ∀ a, 0 ≤ TrackD.cutScale B s t a := fun a =>
    (cutScale_pos_aux B s t hB a).le
  have hcut_b_nn : ∀ a, 0 ≤ TrackD.cutScale B s b a := fun a =>
    (cutScale_pos_aux B s b hB a).le
  have hρs_nn : 0 ≤ ρ * s := mul_nonneg hρ hs
  have hexp1 : (1 : ℝ) ≤ Real.exp (ρ * s) :=
    Real.one_le_exp_iff.mpr hρs_nn
  have hexp_pow_eq : Real.exp ((d : ℝ) * ρ * s) = (Real.exp (ρ * s)) ^ d := by
    have h1 : (d : ℝ) * ρ * s = (d : ℝ) * (ρ * s) := by ring
    rw [h1, Real.exp_nat_mul]
  have he_pre : TrackD.eScale B s t j ≤
      TrackD.eScale B s b j * Real.exp ((d : ℝ) * ρ * s) := by
    unfold TrackD.eScale
    have hcard_le : (Finset.univ.filter (fun i : Fin d => i.val < j)).card ≤ d := by
      calc (Finset.univ.filter (fun i : Fin d => i.val < j)).card
          ≤ Fintype.card (Fin d) := Finset.card_le_univ _
        _ = d := Fintype.card_fin d
    have hpow_le : (Real.exp (ρ * s)) ^
        (Finset.univ.filter (fun i : Fin d => i.val < j)).card ≤
        Real.exp ((d : ℝ) * ρ * s) := by
      rw [hexp_pow_eq]
      exact pow_le_pow_right₀ hexp1 hcard_le
    have hprod_le : (∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
        TrackD.cutScale B s t i) ≤
        ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
          (TrackD.cutScale B s b i * Real.exp (ρ * s)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hcut_nn i
      · intro i hi
        exact hcut i
    have hprod_eq : (∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
        (TrackD.cutScale B s b i * Real.exp (ρ * s))) =
        (∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
          TrackD.cutScale B s b i) * ((Real.exp (ρ * s)) ^
            (Finset.univ.filter (fun i : Fin d => i.val < j)).card) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    calc ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
          TrackD.cutScale B s t i
        ≤ (∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
            TrackD.cutScale B s b i) *
          ((Real.exp (ρ * s)) ^
            (Finset.univ.filter (fun i : Fin d => i.val < j)).card) := by
          rw [← hprod_eq]
          exact hprod_le
      _ ≤ (∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
            TrackD.cutScale B s b i) * Real.exp ((d : ℝ) * ρ * s) := by
          apply mul_le_mul_of_nonneg_left hpow_le
          apply Finset.prod_nonneg
          intro i hi
          exact hcut_b_nn i
  have htail_le : TrackD.tailScale B s t j ≤
      TrackD.tailScale B s b j * Real.exp ((d : ℝ) * ρ * s) := by
    unfold TrackD.tailScale
    have hcard_le : (Finset.univ.filter (fun i : Fin d => j ≤ i.val)).card ≤ d := by
      calc (Finset.univ.filter (fun i : Fin d => j ≤ i.val)).card
          ≤ Fintype.card (Fin d) := Finset.card_le_univ _
        _ = d := Fintype.card_fin d
    have hpow_le : (Real.exp (ρ * s)) ^
        (Finset.univ.filter (fun i : Fin d => j ≤ i.val)).card ≤
        Real.exp ((d : ℝ) * ρ * s) := by
      rw [hexp_pow_eq]
      exact pow_le_pow_right₀ hexp1 hcard_le
    have hprod_le : (∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val),
        TrackD.cutScale B s t i) ≤
        ∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val),
          (TrackD.cutScale B s b i * Real.exp (ρ * s)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hcut_nn i
      · intro i hi
        exact hcut i
    have hprod_eq : (∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val),
        (TrackD.cutScale B s b i * Real.exp (ρ * s))) =
        (∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val),
          TrackD.cutScale B s b i) * ((Real.exp (ρ * s)) ^
            (Finset.univ.filter (fun i : Fin d => j ≤ i.val)).card) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    calc ∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val),
          TrackD.cutScale B s t i
        ≤ (∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val),
            TrackD.cutScale B s b i) *
          ((Real.exp (ρ * s)) ^
            (Finset.univ.filter (fun i : Fin d => j ≤ i.val)).card) := by
          rw [← hprod_eq]
          exact hprod_le
      _ ≤ (∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val),
            TrackD.cutScale B s b i) * Real.exp ((d : ℝ) * ρ * s) := by
          apply mul_le_mul_of_nonneg_left hpow_le
          apply Finset.prod_nonneg
          intro i hi
          exact hcut_b_nn i
  have heScale_b_pos : 0 < TrackD.eScale B s b j := eScale_pos_aux B s b hB j
  have hprod_eq : TrackD.eScale B s b j * TrackD.tailScale B s b j = N := by
    have hreg := TrackD.regularity_scale_product B s b j
    rw [hb] at hreg
    simp only [zero_mul, Real.exp_zero, mul_one] at hreg
    rw [hBN] at hreg
    exact hreg
  have htail_eq_div : TrackD.tailScale B s b j = N / TrackD.eScale B s b j := by
    rw [eq_div_iff (ne_of_gt heScale_b_pos), mul_comm]
    exact hprod_eq
  constructor
  · exact he_pre
  · rw [← htail_eq_div]
    exact htail_le

/-- 138: flat budgets. -/
theorem flat_budget_aux (𝒳 : AffineFamily.Family d)
    (S : AffineVariety d → Finset (RPoint d))
    (hpure : ∀ X ∈ 𝒳, X.IsIrreducible) (e m c : ℝ)
    (he : 0 < e) (hm : 0 ≤ m) (hc : 0 ≤ c)
    (hdegree : (∑ X ∈ 𝒳, (X.degree : ℝ)) ≤ e * c)
    (hweight : ∀ X ∈ 𝒳, ((S X).card : ℝ) ≤ m * (X.degree : ℝ) / e * c) :
    ((𝒳.filter TrackD.IsFlat).card : ℝ) ≤ e * c ∧
    ∀ X ∈ 𝒳, TrackD.IsFlat X → ((S X).card : ℝ) ≤ m * e⁻¹ * c := by
  classical
  have hdeg_nonneg : ∀ X ∈ 𝒳, 0 ≤ (X.degree : ℝ) := by
    intro X hX
    have hirr := hpure X hX
    have hne : X.ideal ≠ ⊤ := hirr.ne_top
    have h1 : (1 : ℚ) ≤ X.degree := AffineVariety.one_le_degree X hne
    have h0 : (0 : ℚ) ≤ X.degree := zero_le_one.trans h1
    exact_mod_cast h0
  have hdeg1 : ∀ X ∈ 𝒳, TrackD.IsFlat X → (X.degree : ℝ) = 1 := by
    intro X hX hflat
    have hirr := hpure X hX
    have heq : X.degree = 1 :=
      DistinctDistances.Request.affine_flat_degree_one X hirr hflat
    have hcast : ((X.degree : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by rw [heq]
    simpa using hcast
  have hsum_eq : (∑ X ∈ 𝒳.filter TrackD.IsFlat, (X.degree : ℝ)) =
      ((𝒳.filter TrackD.IsFlat).card : ℝ) := by
    calc ∑ X ∈ 𝒳.filter TrackD.IsFlat, (X.degree : ℝ)
        = ∑ X ∈ 𝒳.filter TrackD.IsFlat, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro X hX
          obtain ⟨hXmem, hflat⟩ := Finset.mem_filter.mp hX
          exact hdeg1 X hXmem hflat
      _ = ((𝒳.filter TrackD.IsFlat).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : 𝒳.filter TrackD.IsFlat ⊆ 𝒳 := Finset.filter_subset _ _
  have hle : (∑ X ∈ 𝒳.filter TrackD.IsFlat, (X.degree : ℝ)) ≤
      (∑ X ∈ 𝒳, (X.degree : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun X hX _ => hdeg_nonneg X hX)
  have hfirst : ((𝒳.filter TrackD.IsFlat).card : ℝ) ≤ e * c := by
    calc ((𝒳.filter TrackD.IsFlat).card : ℝ)
        = (∑ X ∈ 𝒳.filter TrackD.IsFlat, (X.degree : ℝ)) := hsum_eq.symm
      _ ≤ (∑ X ∈ 𝒳, (X.degree : ℝ)) := hle
      _ ≤ e * c := hdegree
  constructor
  · exact hfirst
  · intro X hX hflat
    have hle0 := hweight X hX
    have h1 := hdeg1 X hX hflat
    rw [h1] at hle0
    have heq : m * (1 : ℝ) / e * c = m * e⁻¹ * c := by
      rw [div_eq_mul_inv, mul_one]
    rw [heq] at hle0
    exact hle0

/-- 136: pooled owner bounds. -/
theorem owner_pooled_bounds_aux (pl : Finset (TrackD.Piece d))
    (S : Finset (RPoint d)) (α : RPoint d → AffineVariety d) (j : ℕ)
    (hS : S ⊆ TrackD.poolPts pl) (hα : TrackD.CarrierAssignment pl j α)
    (hpure : ∀ X ∈ pl, ∀ Z ∈ TrackD.pieceCarrierFamily X j, Z.IsIrreducible)
    (a v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v)
    (hdegree : ∀ X ∈ pl,
      (∑ Z ∈ TrackD.pieceCarrierFamily X j, (Z.degree : ℝ)) ≤ a)
    (hmass : ∀ X ∈ pl, ∀ Z, X.path.IsCarrier j Z →
      (∃ q ∈ X.pts, TrackD.toC q ∈ Z) →
      ((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℝ) ≤ (Z.degree : ℝ) * v) :
    (∑ Z ∈ commonOwnerFamily S α, (Z.degree : ℝ)) ≤ (pl.card : ℝ) * a ∧
    ∀ Z ∈ commonOwnerFamily S α,
      ((commonOwnerFiber S α Z).card : ℝ) ≤ (pl.card : ℝ) * (Z.degree : ℝ) * v := by
  classical
  -- owner image is covered by piece families
  have hsub : commonOwnerFamily S α ⊆
      pl.biUnion (fun X => TrackD.pieceCarrierFamily X j) := by
    intro Z hZ
    simp only [commonOwnerFamily] at hZ
    obtain ⟨q, hqS, hqeq⟩ := Finset.mem_image.mp hZ
    have hqpool : q ∈ TrackD.poolPts pl := hS hqS
    obtain ⟨X, hX, hqX⟩ := Finset.mem_biUnion.mp hqpool
    obtain ⟨hcarrier, hpoint⟩ := hα X hX q hqX
    have hmem : α q ∈ TrackD.pieceCarrierFamily X j := by
      rw [TrackD.mem_pieceCarrierFamily]
      exact ⟨hcarrier, q, hqX, hpoint⟩
    rw [hqeq] at hmem
    exact Finset.mem_biUnion.mpr ⟨X, hX, hmem⟩
  have hdeg_nn_U : ∀ Z ∈ pl.biUnion (fun X => TrackD.pieceCarrierFamily X j),
      0 ≤ (Z.degree : ℝ) := by
    intro Z hZ
    obtain ⟨X, hX, hZX⟩ := Finset.mem_biUnion.mp hZ
    have hirr := hpure X hX Z hZX
    have hne : Z.ideal ≠ ⊤ := hirr.ne_top
    have h1 : (1 : ℚ) ≤ Z.degree := AffineVariety.one_le_degree Z hne
    have h0 : (0 : ℚ) ≤ Z.degree := zero_le_one.trans h1
    exact_mod_cast h0
  have hle_owner_union : (∑ Z ∈ commonOwnerFamily S α, (Z.degree : ℝ)) ≤
      (∑ Z ∈ pl.biUnion (fun X => TrackD.pieceCarrierFamily X j), (Z.degree : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun Z hZU _ => hdeg_nn_U Z hZU)
  have hle_union_sum : (∑ Z ∈ pl.biUnion (fun X => TrackD.pieceCarrierFamily X j),
      (Z.degree : ℝ)) ≤
      ∑ X ∈ pl, ∑ Z ∈ TrackD.pieceCarrierFamily X j, (Z.degree : ℝ) :=
    sum_biUnion_le_aux pl (fun X => TrackD.pieceCarrierFamily X j)
      (fun Z => (Z.degree : ℝ)) hdeg_nn_U
  have hle_sum_a : (∑ X ∈ pl, ∑ Z ∈ TrackD.pieceCarrierFamily X j, (Z.degree : ℝ)) ≤
      (pl.card : ℝ) * a := by
    calc ∑ X ∈ pl, ∑ Z ∈ TrackD.pieceCarrierFamily X j, (Z.degree : ℝ)
        ≤ ∑ X ∈ pl, a := Finset.sum_le_sum (fun X hX => hdegree X hX)
      _ = (pl.card : ℝ) * a := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hfirst : (∑ Z ∈ commonOwnerFamily S α, (Z.degree : ℝ)) ≤ (pl.card : ℝ) * a :=
    (hle_owner_union.trans hle_union_sum).trans hle_sum_a
  constructor
  · exact hfirst
  · intro Z hZ
    simp only [commonOwnerFamily] at hZ
    obtain ⟨q0, hq0S, hq0eq⟩ := Finset.mem_image.mp hZ
    -- Z is irreducible via its witness piece
    have hq0pool : q0 ∈ TrackD.poolPts pl := hS hq0S
    obtain ⟨X0, hX0, hq0X⟩ := Finset.mem_biUnion.mp hq0pool
    obtain ⟨hcarr0, hpt0⟩ := hα X0 hX0 q0 hq0X
    have hmem0 : α q0 ∈ TrackD.pieceCarrierFamily X0 j := by
      rw [TrackD.mem_pieceCarrierFamily]
      exact ⟨hcarr0, q0, hq0X, hpt0⟩
    rw [hq0eq] at hmem0
    have hirrZ : Z.IsIrreducible := hpure X0 hX0 Z hmem0
    have hneZ : Z.ideal ≠ ⊤ := hirrZ.ne_top
    have h1Z : (1 : ℚ) ≤ Z.degree := AffineVariety.one_le_degree Z hneZ
    have h0Z : (0 : ℚ) ≤ Z.degree := zero_le_one.trans h1Z
    have hdeg_nn : 0 ≤ (Z.degree : ℝ) := by exact_mod_cast h0Z
    -- pieces that can supply Z
    set plZ : Finset (TrackD.Piece d) :=
      pl.filter (fun X => Z ∈ TrackD.pieceCarrierFamily X j) with hplZ
    have hplZ_sub : plZ ⊆ pl := Finset.filter_subset _ _
    have hcard_le : (plZ.card : ℝ) ≤ (pl.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hplZ_sub
    have hcover : commonOwnerFiber S α Z ⊆
        plZ.biUnion (fun X => X.pts.filter (fun q => TrackD.toC q ∈ Z)) := by
      intro q hq
      simp only [commonOwnerFiber, Finset.mem_filter] at hq
      obtain ⟨hqS, hqeq⟩ := hq
      have hqp : q ∈ TrackD.poolPts pl := hS hqS
      obtain ⟨X, hX, hqX⟩ := Finset.mem_biUnion.mp hqp
      obtain ⟨hcarr, hpt⟩ := hα X hX q hqX
      have hmem : Z ∈ TrackD.pieceCarrierFamily X j := by
        have hmemα : α q ∈ TrackD.pieceCarrierFamily X j := by
          rw [TrackD.mem_pieceCarrierFamily]
          exact ⟨hcarr, q, hqX, hpt⟩
        rw [hqeq] at hmemα
        exact hmemα
      have hXplZ : X ∈ plZ := Finset.mem_filter.mpr ⟨hX, hmem⟩
      have hptZ : TrackD.toC q ∈ Z := by
        rw [← hqeq]
        exact hpt
      exact Finset.mem_biUnion.mpr ⟨X, hXplZ, Finset.mem_filter.mpr ⟨hqX, hptZ⟩⟩
    have hcard_nat : (commonOwnerFiber S α Z).card ≤
        ∑ X ∈ plZ, (X.pts.filter (fun q => TrackD.toC q ∈ Z)).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have hcard_real : ((commonOwnerFiber S α Z).card : ℝ) ≤
        ∑ X ∈ plZ, (((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℕ) : ℝ) := by
      calc ((commonOwnerFiber S α Z).card : ℝ)
          ≤ (((∑ X ∈ plZ, (X.pts.filter (fun q => TrackD.toC q ∈ Z)).card) : ℕ) : ℝ) :=
            Nat.cast_le.mpr hcard_nat
        _ = ∑ X ∈ plZ, (((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℕ) : ℝ) := by
            rw [Nat.cast_sum]
    have hmass_real : ∀ X ∈ plZ,
        (((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℕ) : ℝ) ≤
          (Z.degree : ℝ) * v := by
      intro X hX
      obtain ⟨hXpl, hZX⟩ := Finset.mem_filter.mp hX
      obtain ⟨hcarr, hex⟩ := (TrackD.mem_pieceCarrierFamily X j Z).mp hZX
      exact hmass X hXpl Z hcarr hex
    have hsum_le : (∑ X ∈ plZ, (((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℕ) : ℝ)) ≤
        (plZ.card : ℝ) * ((Z.degree : ℝ) * v) := by
      calc ∑ X ∈ plZ, (((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℕ) : ℝ)
          ≤ ∑ X ∈ plZ, ((Z.degree : ℝ) * v) :=
            Finset.sum_le_sum (fun X hX => hmass_real X hX)
        _ = (plZ.card : ℝ) * ((Z.degree : ℝ) * v) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hle_pl : (plZ.card : ℝ) * ((Z.degree : ℝ) * v) ≤
        (pl.card : ℝ) * ((Z.degree : ℝ) * v) := by
      apply mul_le_mul_of_nonneg_right hcard_le
      exact mul_nonneg hdeg_nn hv
    calc ((commonOwnerFiber S α Z).card : ℝ)
        ≤ ∑ X ∈ plZ, (((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℕ) : ℝ) :=
          hcard_real
      _ ≤ (plZ.card : ℝ) * ((Z.degree : ℝ) * v) := hsum_le
      _ ≤ (pl.card : ℝ) * ((Z.degree : ℝ) * v) := hle_pl
      _ = (pl.card : ℝ) * (Z.degree : ℝ) * v := by ring

/-- 137: retained mass lower bounds. -/
theorem retained_mass_lower_aux {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ} (W : CommonPhysicalSequence T M j τ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      regime.N i * Real.exp (-η * M.s i) ≤ ((W.sources i).card : ℝ) ∧
      regime.N i * Real.exp (-η * M.s i) ≤ ((W.targets i).card : ℝ) := by
  classical
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsrc_o := W.source_omissions.def hhalf
  have htgt_o := W.target_omissions.def hhalf
  have hsrc_exp := M.source_size.1 (η / 2) hη2
  have htgt_exp := M.target_size.1 (η / 2) hη2
  have hs_large : ∀ᶠ i in atTop, (2 * Real.log 2) / η ≤ M.s i :=
    M.width_grows.eventually_ge_atTop _
  filter_upwards [hsrc_o, htgt_o, hsrc_exp, htgt_exp, hs_large] with i
    hsrc_o htgt_o hsrc_exp htgt_exp hs_large
  have hNnn : 0 ≤ regime.N i := (regime.N_pos i).le
  have hlog2pos : (0 : ℝ) < 2 := by norm_num
  have hexp_half : Real.exp (-(η / 2) * M.s i) ≤ 1 / 2 := by
    have hmul : (η / 2) * M.s i ≥ Real.log 2 := by
      have h1 : (η / 2) * ((2 * Real.log 2) / η) = Real.log 2 := by
        field_simp
      calc Real.log 2 = (η / 2) * ((2 * Real.log 2) / η) := h1.symm
        _ ≤ (η / 2) * M.s i :=
          mul_le_mul_of_nonneg_left hs_large hη2.le
    have hneg : -(η / 2) * M.s i ≤ -Real.log 2 := by linarith
    have hle := Real.exp_le_exp.mpr hneg
    have hlog2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log hlog2pos]
      norm_num
    rwa [hlog2] at hle
  have hexp_factor : Real.exp (-η * M.s i) =
      Real.exp (-(η / 2) * M.s i) * Real.exp (-(η / 2) * M.s i) := by
    have hfactor : -η * M.s i = -(η / 2) * M.s i + (-(η / 2) * M.s i) := by ring
    rw [hfactor, Real.exp_add]
  have hexp_le : Real.exp (-η * M.s i) ≤
      (1 / 2) * Real.exp (-(η / 2) * M.s i) := by
    rw [hexp_factor]
    exact mul_le_mul_of_nonneg_right hexp_half (Real.exp_pos _).le
  have hN_exp_le : regime.N i * Real.exp (-η * M.s i) ≤
      (1 / 2) * (regime.N i * Real.exp (-(η / 2) * M.s i)) := by
    calc regime.N i * Real.exp (-η * M.s i)
        ≤ regime.N i * ((1 / 2) * Real.exp (-(η / 2) * M.s i)) :=
          mul_le_mul_of_nonneg_left hexp_le hNnn
      _ = (1 / 2) * (regime.N i * Real.exp (-(η / 2) * M.s i)) := by ring
  -- source side
  have hsrc_pool : regime.N i * Real.exp (-(η / 2) * M.s i) ≤
      ((TrackD.poolPts (T.sources i)).card : ℝ) := by
    have h := hsrc_exp ()
    simpa using h
  have hsrc_omit_nn : 0 ≤ ((((TrackD.poolPts (T.sources i)) \
      retainedCommonPool (T.sources i) (T.sources i ∪ T.targets i) j
        (W.equations i) (W.minor i) (W.owner i)).card : ℕ) : ℝ) := by
    positivity
  have hsrc_pool_nn : 0 ≤ (((TrackD.poolPts (T.sources i)).card : ℕ) : ℝ) := by
    positivity
  have hnorm_src_omit : ‖((((TrackD.poolPts (T.sources i)) \
      retainedCommonPool (T.sources i) (T.sources i ∪ T.targets i) j
        (W.equations i) (W.minor i) (W.owner i)).card : ℕ) : ℝ)‖ =
      ((((TrackD.poolPts (T.sources i)) \
      retainedCommonPool (T.sources i) (T.sources i ∪ T.targets i) j
        (W.equations i) (W.minor i) (W.owner i)).card : ℕ) : ℝ) :=
    Real.norm_of_nonneg hsrc_omit_nn
  have hnorm_src_pool : ‖((((TrackD.poolPts (T.sources i)).card : ℕ)) : ℝ)‖ =
      ((((TrackD.poolPts (T.sources i)).card : ℕ)) : ℝ) :=
    Real.norm_of_nonneg hsrc_pool_nn
  rw [hnorm_src_omit, hnorm_src_pool] at hsrc_o
  have hsrc_sub : W.sources i ⊆ TrackD.poolPts (T.sources i) :=
    Finset.filter_subset _ _
  have hsrc_eq : ((TrackD.poolPts (T.sources i)).card : ℝ) =
      ((W.sources i).card : ℝ) +
        ((((TrackD.poolPts (T.sources i)) \ W.sources i).card : ℕ) : ℝ) := by
    have hnat : (TrackD.poolPts (T.sources i)).card =
        (W.sources i).card + (((TrackD.poolPts (T.sources i)) \ W.sources i).card) := by
      have h := Finset.card_sdiff_add_card_eq_card hsrc_sub
      linarith
    rw [hnat, Nat.cast_add]
  have hsrc_omit_eq : (TrackD.poolPts (T.sources i) \ W.sources i).card =
      (TrackD.poolPts (T.sources i) \
        retainedCommonPool (T.sources i) (T.sources i ∪ T.targets i) j
          (W.equations i) (W.minor i) (W.owner i)).card := by
    rfl
  have hsrc_half : (1 / 2) * (((TrackD.poolPts (T.sources i)).card : ℕ) : ℝ) ≤
      ((W.sources i).card : ℝ) := by
    have h_omit : ((((TrackD.poolPts (T.sources i)) \ W.sources i).card : ℕ) : ℝ) ≤
        (1 / 2) * ((((TrackD.poolPts (T.sources i)).card : ℕ)) : ℝ) := by
      rw [hsrc_omit_eq]
      exact hsrc_o
    linarith [hsrc_eq]
  have hsrc_final : regime.N i * Real.exp (-η * M.s i) ≤ ((W.sources i).card : ℝ) := by
    calc regime.N i * Real.exp (-η * M.s i)
        ≤ (1 / 2) * (regime.N i * Real.exp (-(η / 2) * M.s i)) := hN_exp_le
      _ ≤ (1 / 2) * ((((TrackD.poolPts (T.sources i)).card : ℕ)) : ℝ) :=
          mul_le_mul_of_nonneg_left hsrc_pool (by norm_num)
      _ ≤ ((W.sources i).card : ℝ) := hsrc_half
  -- target side (symmetric)
  have htgt_pool : regime.N i * Real.exp (-(η / 2) * M.s i) ≤
      ((TrackD.poolPts (T.targets i)).card : ℝ) := by
    have h := htgt_exp ()
    simpa using h
  have htgt_omit_nn : 0 ≤ ((((TrackD.poolPts (T.targets i)) \
      retainedCommonPool (T.targets i) (T.sources i ∪ T.targets i) j
        (W.equations i) (W.minor i) (W.owner i)).card : ℕ) : ℝ) := by
    positivity
  have htgt_pool_nn : 0 ≤ (((TrackD.poolPts (T.targets i)).card : ℕ) : ℝ) := by
    positivity
  have hnorm_tgt_omit : ‖((((TrackD.poolPts (T.targets i)) \
      retainedCommonPool (T.targets i) (T.sources i ∪ T.targets i) j
        (W.equations i) (W.minor i) (W.owner i)).card : ℕ) : ℝ)‖ =
      ((((TrackD.poolPts (T.targets i)) \
      retainedCommonPool (T.targets i) (T.sources i ∪ T.targets i) j
        (W.equations i) (W.minor i) (W.owner i)).card : ℕ) : ℝ) :=
    Real.norm_of_nonneg htgt_omit_nn
  have hnorm_tgt_pool : ‖((((TrackD.poolPts (T.targets i)).card : ℕ)) : ℝ)‖ =
      ((((TrackD.poolPts (T.targets i)).card : ℕ)) : ℝ) :=
    Real.norm_of_nonneg htgt_pool_nn
  rw [hnorm_tgt_omit, hnorm_tgt_pool] at htgt_o
  have htgt_sub : W.targets i ⊆ TrackD.poolPts (T.targets i) :=
    Finset.filter_subset _ _
  have htgt_eq : ((TrackD.poolPts (T.targets i)).card : ℝ) =
      ((W.targets i).card : ℝ) +
        ((((TrackD.poolPts (T.targets i)) \ W.targets i).card : ℕ) : ℝ) := by
    have hnat : (TrackD.poolPts (T.targets i)).card =
        (W.targets i).card + (((TrackD.poolPts (T.targets i)) \ W.targets i).card) := by
      have h := Finset.card_sdiff_add_card_eq_card htgt_sub
      linarith
    rw [hnat, Nat.cast_add]
  have htgt_omit_eq : (TrackD.poolPts (T.targets i) \ W.targets i).card =
      (TrackD.poolPts (T.targets i) \
        retainedCommonPool (T.targets i) (T.sources i ∪ T.targets i) j
          (W.equations i) (W.minor i) (W.owner i)).card := by
    rfl
  have htgt_half : (1 / 2) * (((TrackD.poolPts (T.targets i)).card : ℕ) : ℝ) ≤
      ((W.targets i).card : ℝ) := by
    have h_omit : ((((TrackD.poolPts (T.targets i)) \ W.targets i).card : ℕ) : ℝ) ≤
        (1 / 2) * ((((TrackD.poolPts (T.targets i)).card : ℕ)) : ℝ) := by
      rw [htgt_omit_eq]
      exact htgt_o
    linarith [htgt_eq]
  have htgt_final : regime.N i * Real.exp (-η * M.s i) ≤ ((W.targets i).card : ℝ) := by
    calc regime.N i * Real.exp (-η * M.s i)
        ≤ (1 / 2) * (regime.N i * Real.exp (-(η / 2) * M.s i)) := hN_exp_le
      _ ≤ (1 / 2) * ((((TrackD.poolPts (T.targets i)).card : ℕ)) : ℝ) :=
          mul_le_mul_of_nonneg_left htgt_pool (by norm_num)
      _ ≤ ((W.targets i).card : ℝ) := htgt_half
  exact ⟨hsrc_final, htgt_final⟩

/-- 134: retained carrier structure. -/
theorem retained_carrier_structure_aux {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) (hj : j ≤ d) (i : ℕ) :
    AffineFamily.IsPure (W.sourceCarriers i) (d - j) ∧
    AffineFamily.IsPure (W.targetCarriers i) (d - j) ∧
    TrackD.Assignment (regime.P i) (W.sourceCarriers i) (W.sourceAssigned i) ∧
    TrackD.Assignment (regime.P i) (W.targetCarriers i) (W.targetAssigned i) ∧
    (∀ Z ∈ W.sourceCarriers i ∪ W.targetCarriers i,
      TrackD.IsFlat Z → TrackD.IsRealFlat Z) := by
  classical
  have hmem_pieces : ∀ X ∈ T.sources i ∪ T.targets i,
      X ∈ (T.partition i).pieces := by
    intro X hX
    rcases Finset.mem_union.mp hX with h | h
    · exact (T.certificate i).sources_subset h
    · exact (T.certificate i).targets_subset h
  have hpiece : ∀ X ∈ T.sources i ∪ T.targets i,
      TrackD.PieceGood (regime.P i)
        (selectionTolerance (T.precision i)) (selectionTolerance (T.precision i))
        (selectionScale (T.precision i)) X := by
    intro X hX
    exact ((T.certificate i).good.pieces_good X (hmem_pieces X hX)).1
  have hsubset : ∀ X ∈ T.sources i ∪ T.targets i, X.pts ⊆ regime.P i := by
    intro X hX
    exact (hpiece X hX).subset
  have hvanish : ∀ X ∈ T.sources i ∪ T.targets i, ∀ q ∈ X.pts, ∀ k : Fin d,
      MvPolynomial.eval (TrackD.toC q) (X.path.cut k) = 0 := by
    intro X hX q hq k
    exact (hpiece X hX).vanish q hq k
  have hproper : ∀ X ∈ T.sources i ∪ T.targets i, ∀ q ∈ X.pts,
      X.path.ProperAt (TrackD.toC q) := by
    intro X hX q hq
    exact (hpiece X hX).proper q hq
  have hsrc_pool_sub : W.sources i ⊆ TrackD.poolPts (T.sources i) :=
    Finset.filter_subset _ _
  have htgt_pool_sub : W.targets i ⊆ TrackD.poolPts (T.targets i) :=
    Finset.filter_subset _ _
  have hpool_src_sub : TrackD.poolPts (T.sources i) ⊆ regime.P i := by
    intro q hq
    obtain ⟨X, hX, hqX⟩ := Finset.mem_biUnion.mp hq
    exact hsubset X (Finset.mem_union_left _ hX) hqX
  have hpool_tgt_sub : TrackD.poolPts (T.targets i) ⊆ regime.P i := by
    intro q hq
    obtain ⟨X, hX, hqX⟩ := Finset.mem_biUnion.mp hq
    exact hsubset X (Finset.mem_union_right _ hX) hqX
  -- purity for either role
  have hpure_of : ∀ (pl : Finset (TrackD.Piece d)) (S : Finset (RPoint d)),
      S ⊆ TrackD.poolPts pl → pl ⊆ T.sources i ∪ T.targets i →
      ∀ Z ∈ commonOwnerFamily S (W.owner i), Z.IsIrreducible ∧ Z.dimension = d - j := by
    intro pl S hSsub hplsub Z hZ
    simp only [commonOwnerFamily] at hZ
    obtain ⟨q, hqS, hqeq⟩ := Finset.mem_image.mp hZ
    have hqpool : q ∈ TrackD.poolPts pl := hSsub hqS
    obtain ⟨X, hX, hqX⟩ := Finset.mem_biUnion.mp hqpool
    have hXunion : X ∈ T.sources i ∪ T.targets i := hplsub hX
    obtain ⟨hcarr, hpt⟩ := W.supported i X hXunion q hqX
    have hcarrierZ : X.path.IsCarrier j Z := hqeq ▸ hcarr
    have hpointZ : TrackD.toC q ∈ Z := hqeq ▸ hpt
    have hlocal : Z ∈ X.path.localCarriers j (TrackD.toC q) :=
      ⟨hcarrierZ, hpointZ⟩
    exact TrackD.prof_partition_pure X q hqX
      (hvanish X hXunion q hqX) (hproper X hXunion q hqX) j hj Z hlocal
  have hpure_src : AffineFamily.IsPure (W.sourceCarriers i) (d - j) := by
    intro Z hZ
    have hZ : Z ∈ commonOwnerFamily (W.sources i) (W.owner i) := by
      simpa only [CommonPhysicalSequence.sourceCarriers] using hZ
    exact hpure_of (T.sources i) (W.sources i) hsrc_pool_sub
      Finset.subset_union_left Z hZ
  have hpure_tgt : AffineFamily.IsPure (W.targetCarriers i) (d - j) := by
    intro Z hZ
    have hZ : Z ∈ commonOwnerFamily (W.targets i) (W.owner i) := by
      simpa only [CommonPhysicalSequence.targetCarriers] using hZ
    exact hpure_of (T.targets i) (W.targets i) htgt_pool_sub
      Finset.subset_union_right Z hZ
  -- assignment for either role
  have hassign_of : ∀ (pl : Finset (TrackD.Piece d)) (S : Finset (RPoint d)),
      S ⊆ TrackD.poolPts pl → pl ⊆ T.sources i ∪ T.targets i →
      S ⊆ regime.P i →
      TrackD.Assignment (regime.P i) (commonOwnerFamily S (W.owner i))
        (commonOwnerFiber S (W.owner i)) := by
    intro pl S hSsub hplsub hSP
    refine ⟨?_, ?_, ?_⟩
    · intro Y hY q hq
      simp only [commonOwnerFiber, Finset.mem_filter] at hq
      obtain ⟨hqS, _⟩ := hq
      exact hSP hqS
    · intro Y hY q hq
      simp only [commonOwnerFiber, Finset.mem_filter] at hq
      obtain ⟨hqS, hqeq⟩ := hq
      have hqpool : q ∈ TrackD.poolPts pl := hSsub hqS
      obtain ⟨X, hX, hqX⟩ := Finset.mem_biUnion.mp hqpool
      have hXunion : X ∈ T.sources i ∪ T.targets i := hplsub hX
      obtain ⟨hcarr, hpt⟩ := W.supported i X hXunion q hqX
      have hptY : TrackD.toC q ∈ Y := hqeq ▸ hpt
      exact hptY
    · intro X hX Y hY hne
      apply Finset.disjoint_left.mpr
      intro q hq1 hq2
      simp only [commonOwnerFiber, Finset.mem_filter] at hq1 hq2
      obtain ⟨_, h1⟩ := hq1
      obtain ⟨_, h2⟩ := hq2
      exact hne (h1.symm.trans h2)
  have hSP_src : W.sources i ⊆ regime.P i :=
    hsrc_pool_sub.trans hpool_src_sub
  have hSP_tgt : W.targets i ⊆ regime.P i :=
    htgt_pool_sub.trans hpool_tgt_sub
  have hass_src : TrackD.Assignment (regime.P i) (W.sourceCarriers i)
      (W.sourceAssigned i) := by
    have h := hassign_of (T.sources i) (W.sources i) hsrc_pool_sub
      Finset.subset_union_left hSP_src
    simpa only [CommonPhysicalSequence.sourceCarriers,
      CommonPhysicalSequence.sourceAssigned] using h
  have hass_tgt : TrackD.Assignment (regime.P i) (W.targetCarriers i)
      (W.targetAssigned i) := by
    have h := hassign_of (T.targets i) (W.targets i) htgt_pool_sub
      Finset.subset_union_right hSP_tgt
    simpa only [CommonPhysicalSequence.targetCarriers,
      CommonPhysicalSequence.targetAssigned] using h
  have hreal : ∀ Z ∈ W.sourceCarriers i ∪ W.targetCarriers i,
      TrackD.IsFlat Z → TrackD.IsRealFlat Z := by
    intro Z hZ hflat
    rcases Finset.mem_union.mp hZ with hsrc | htgt
    · have hZim : Z ∈ commonOwnerFamily (W.sources i) (W.owner i) := by
        simpa only [CommonPhysicalSequence.sourceCarriers] using hsrc
      simp only [commonOwnerFamily] at hZim
      obtain ⟨q, hqS, hqeq⟩ := Finset.mem_image.mp hZim
      simp only [CommonPhysicalSequence.sources, retainedCommonPool,
        Finset.mem_filter] at hqS
      obtain ⟨_, _, hkeep⟩ := hqS
      have hkeepZ : keepRealCarrier Z := hqeq ▸ hkeep
      exact hkeepZ hflat
    · have hZim : Z ∈ commonOwnerFamily (W.targets i) (W.owner i) := by
        simpa only [CommonPhysicalSequence.targetCarriers] using htgt
      simp only [commonOwnerFamily] at hZim
      obtain ⟨q, hqS, hqeq⟩ := Finset.mem_image.mp hZim
      simp only [CommonPhysicalSequence.targets, retainedCommonPool,
        Finset.mem_filter] at hqS
      obtain ⟨_, _, hkeep⟩ := hqS
      have hkeepZ : keepRealCarrier Z := hqeq ▸ hkeep
      exact hkeepZ hflat
  exact ⟨hpure_src, hpure_tgt, hass_src, hass_tgt, hreal⟩

end
end DistinctDistances.SparseCones.MECarrierAux
