import DistinctDistances.TrackE.CommonSourceSections
import DistinctDistances.TrackE.CommonProjectionBudgets
import DistinctDistances.TrackE.CommonLiftingInputs
import DistinctDistances.TrackE.MReqAux
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Literal finite-normalization and original-intersection inputs,
`sc:retained-products.family`, sparse-cones.tex:194–207. -/
namespace DistinctDistances.Request
noncomputable section

/-- Request to A: injection of the linear equations on the original tangent
isolates a point of the WHOLE equation ideal, allowing components elsewhere. -/
theorem common_linear_section_isolated {d k : ℕ}
    (Z : AffineVariety (d + d)) (hZ : Z.IsIrreducible)
    (E : Fin (2 * k) → Poly (d + d)) (hlin : ∀ i, (E i).totalDegree ≤ 1)
    (z : Point (d + d)) (hz : z ∈ Z)
    (hzero : ∀ i, MvPolynomial.eval z (E i) = 0)
    (hinj : Function.Injective ((LinearMap.pi (fun i => differential (E i) z)).domRestrict
      (Z.tangentSpace z))) :
    pointIdeal z ∈ (Z.ideal ⊔ Ideal.span (Set.range E)).minimalPrimes := by
  exact MReqAux.linear_section_isolated_of_tangent_inj Z hZ E hlin z hz hzero hinj

end
end DistinctDistances.Request

namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

theorem common_affine_projection_rational_point {d k : ℕ}
    (φ : AffineProjection d k) (x : Point d) :
    TrackD.rationalPoint (fun i => φ.pullback (MvPolynomial.X i)) 1 x = φ.apply x := by
  funext i
  simp only [TrackD.rationalPoint]
  have h1 : MvPolynomial.eval x (1 : Poly d) = 1 := by simp
  rw [h1, div_one]
  have h := φ.eval_pullback x (MvPolynomial.X i)
  simp only [MvPolynomial.aeval_X] at h
  simpa using h

theorem common_affine_projection_rational_image {d k : ℕ}
    (X : AffineVariety d) (φ : AffineProjection d k) :
    TrackD.rationalImage X (fun i => φ.pullback (MvPolynomial.X i)) 1 = φ.image X := by
  have hpt : ∀ x : Point d,
      TrackD.rationalPoint (fun i => φ.pullback (MvPolynomial.X i)) 1 x = φ.apply x :=
    fun x => common_affine_projection_rational_point φ x
  have hset : {y | ∃ x ∈ X, MvPolynomial.eval x (1 : Poly d) ≠ 0 ∧
      TrackD.rationalPoint (fun i => φ.pullback (MvPolynomial.X i)) 1 x = y} =
      φ.apply '' X.points := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hx, _, rfl⟩
      exact ⟨x, hx, (hpt x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp, hpt x⟩
  have himg : TrackD.rationalImage X (fun i => φ.pullback (MvPolynomial.X i)) 1 =
      AffineVariety.closure (φ.apply '' X.points) := by
    unfold TrackD.rationalImage
    rw [hset]
  rw [himg, ← φ.image_eq_closure]

theorem common_affine_projection_rational_differential {d k : ℕ}
    (φ : AffineProjection d k) (x : Point d) :
    TrackD.rationalDifferential (fun i => φ.pullback (MvPolynomial.X i)) 1 x = φ.linear := by
  have h1 : MvPolynomial.eval x (1 : Poly d) = 1 := by simp
  have hdiff1 : differential (1 : Poly d) x = 0 := by simp [differential]
  have hpull : ∀ i : Fin k, φ.pullback (MvPolynomial.X i) =
      linearCoordinate φ.linear i + MvPolynomial.C (φ.offset i) := fun i => by
    simp [AffineProjection.pullback]
  have hadd : ∀ (f g : Poly d) (v : Point d),
      differential (f + g) x v = differential f x v + differential g x v := by
    intro f g v
    simp [differential, LinearMap.sum_apply, LinearMap.smul_apply, add_mul,
      Finset.sum_add_distrib]
  have hC : ∀ (c : ℂ), differential (MvPolynomial.C c) x = 0 := fun c => by
    simp [differential]
  have hlin : ∀ (j : Fin k) (v : Point d),
      differential (linearCoordinate φ.linear j) x v = φ.linear v j := by
    intro j v
    simp only [linearCoordinate, differential, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
    have hsum : ∀ k0 : Fin d, MvPolynomial.aeval x
        (MvPolynomial.pderiv k0 (∑ i : Fin d,
          MvPolynomial.C (φ.linear (Pi.single i 1) j) * MvPolynomial.X i)) =
        φ.linear (Pi.single k0 1) j := by
      intro k0
      rw [map_sum]
      simp only [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X]
      simp only [map_mul, MvPolynomial.aeval_C, Pi.single_apply, apply_ite,
        Algebra.algebraMap_self, RingHom.id_apply, map_one, map_zero,
        mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq, Finset.mem_univ]
    simp_rw [hsum]
    have hx : v = ∑ i : Fin d, v i • (Pi.single i (1 : ℂ) : Point d) := by
      simpa using ((Pi.basisFun ℂ (Fin d)).sum_repr v).symm
    have hlin2 : φ.linear v j = ∑ i : Fin d, v i * φ.linear (Pi.single i (1 : ℂ)) j := by
      have h := congrFun (congrArg φ.linear hx) j
      rw [map_sum] at h
      simpa [map_smul, Pi.smul_apply, smul_eq_mul] using h
    calc (∑ i : Fin d, φ.linear (Pi.single i 1) j * v i)
        = ∑ i : Fin d, v i * φ.linear (Pi.single i 1) j := by
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = φ.linear v j := hlin2.symm
  have hpull_diff : ∀ i : Fin k, differential (φ.pullback (MvPolynomial.X i)) x =
      (LinearMap.proj i).comp φ.linear := by
    intro i
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [hpull i, hadd, hC]
    simpa using hlin i v
  have hrw : TrackD.rationalDifferential (fun i => φ.pullback (MvPolynomial.X i)) 1 x =
      LinearMap.pi (fun i => differential (φ.pullback (MvPolynomial.X i)) x) := by
    unfold TrackD.rationalDifferential
    congr 1
    funext i
    rw [h1, hdiff1]
    simp [inv_one, one_smul, smul_zero, sub_zero]
  rw [hrw]
  apply LinearMap.ext
  intro v
  funext i
  simp only [LinearMap.pi_apply, hpull_diff, LinearMap.comp_apply, LinearMap.proj_apply]

theorem common_zero_ideal_tangent_space {k : ℕ} (V : AffineVariety k)
    (hV : V.ideal = ⊥) (x : Point k) : V.tangentSpace x = ⊤ := by
  apply eq_top_iff.mpr
  intro v _
  simp only [AffineVariety.tangentSpace, Submodule.mem_iInf]
  intro f
  have hf0 : (f.val : Poly k) = 0 := by
    have hmem : f.val ∈ (⊥ : Ideal (Poly k)) := hV ▸ f.property
    exact Ideal.mem_bot.mp hmem
  rw [hf0]
  simp only [LinearMap.mem_ker]
  have hdiff : differential (0 : Poly k) x = 0 := by
    simp [differential]
  rw [hdiff]
  simp

theorem common_eval_tail_rename {d : ℕ} (q : Point (d + 1)) (a : Poly d) :
    MvPolynomial.aeval q (commonTailRename a) = MvPolynomial.eval (Fin.tail q) a := by
  have h : (commonTailRename (n := d) a) = MvPolynomial.rename Fin.succ a := rfl
  rw [h, MvPolynomial.aeval_rename]
  have hcomp : q ∘ Fin.succ = Fin.tail q := by
    funext i
    rfl
  rw [hcomp]
  rfl

/-- A SINGLE base value selects the whole fiber of every original indexed
slice. Index-dependent proper cuts are retained, even for duplicated slices. -/
theorem common_simultaneous_normalization_sections_in_open
    {d k : ℕ} {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (V : ι → AffineVariety d)
    (hV : ∀ i ∈ I, (V i).IsIrreducible ∧ (V i).dimension = k)
    (φ : AffineProjection d k)
    (hnorm : ∀ i ∈ I, TrackA.FiniteAffineProjection φ (V i) ∧ ∃ r : ℕ,
      (r : ℚ) = (V i).degree ∧ φ.GenericallyFiniteOfDegree (V i) r)
    (g : ι → Poly d) (hg : ∀ i ∈ I, g i ∉ (V i).ideal) :
    ∃ t : Point k, ∃ S : ι → Finset (Point d), ∀ i ∈ I,
      ((S i).card : ℚ) = (V i).degree ∧
      (∀ x, x ∈ S i ↔ x ∈ V i ∧ φ.apply x = t) ∧
      ∀ x ∈ S i, MvPolynomial.eval x (g i) ≠ 0 := by
  classical
  by_cases hI : I.Nonempty
  · obtain ⟨i0, hi0⟩ := hI
    have hget : ∀ j : ↥I, ∃ b : Poly k, ∃ c : Poly k, ∃ r : ℕ,
        b ∉ (φ.image (V j.val)).ideal ∧
        c ∉ (φ.image (V j.val)).ideal ∧
        (r : ℚ) = (V j.val).degree ∧
        (∀ t ∈ (φ.image (V j.val)).points, MvPolynomial.aeval t c ≠ 0 →
          (φ.fiber (V j.val) t).Finite ∧ (φ.fiber (V j.val) t).ncard = r) ∧
        (∀ x ∈ (V j.val), MvPolynomial.eval (φ.apply x) b ≠ 0 →
          MvPolynomial.eval x (g j.val) ≠ 0) := by
      intro j
      have hi := j.property
      obtain ⟨hirr, hdim⟩ := hV j.val hi
      obtain ⟨hfin, r, hrdeg, hgen⟩ := hnorm j.val hi
      obtain ⟨b, hb, havoid⟩ :=
        common_finite_cut_base_open (V j.val) hirr hdim φ hfin (g j.val) (hg j.val hi)
      obtain ⟨_, c, hc, hcount⟩ := hgen
      exact ⟨b, c, r, hb, hc, hrdeg, hcount, havoid⟩
    choose b c r hr using hget
    have hb : ∀ j : ↥I, b j ∉ (φ.image (V j.val)).ideal := fun j => (hr j).1
    have hc : ∀ j : ↥I, c j ∉ (φ.image (V j.val)).ideal := fun j => (hr j).2.1
    have hrdeg : ∀ j : ↥I, ((r j : ℕ) : ℚ) = (V j.val).degree := fun j => (hr j).2.2.1
    have hcount : ∀ j : ↥I, ∀ t ∈ (φ.image (V j.val)).points,
        MvPolynomial.aeval t (c j) ≠ 0 →
          (φ.fiber (V j.val) t).Finite ∧ (φ.fiber (V j.val) t).ncard = r j :=
      fun j => (hr j).2.2.2.1
    have havoid : ∀ j : ↥I, ∀ x ∈ (V j.val),
        MvPolynomial.eval (φ.apply x) (b j) ≠ 0 →
          MvPolynomial.eval x (g j.val) ≠ 0 :=
      fun j => (hr j).2.2.2.2
    have hbot : ∀ j : ↥I, (φ.image (V j.val)).ideal = ⊥ := by
      intro j
      have hi := j.property
      obtain ⟨hirr, hdim⟩ := hV j.val hi
      obtain ⟨hfin, _, _, _⟩ := hnorm j.val hi
      exact TrackA.finite_affine_projection_image_ideal_bot (V j.val) hirr hdim φ hfin
    have hbne : ∀ j : ↥I, b j ≠ 0 := fun j hzero =>
      hb j (hzero ▸ Ideal.zero_mem _)
    have hcne : ∀ j : ↥I, c j ≠ 0 := fun j hzero =>
      hc j (hzero ▸ Ideal.zero_mem _)
    have hBne : (∏ j : ↥I, (b j * c j)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j _
      exact mul_ne_zero (hbne j) (hcne j)
    have hBmem : (∏ j : ↥I, (b j * c j)) ∉ (φ.image (V i0)).ideal := by
      intro hmem
      have hbot0 := hbot ⟨i0, hi0⟩
      have hzero : (∏ j : ↥I, (b j * c j)) = 0 :=
        Ideal.mem_bot.mp (hbot0 ▸ hmem)
      exact hBne hzero
    obtain ⟨t, htmem, htB⟩ := GenericFiber.exists_point_of_not_mem
      (φ.image (V i0)) (∏ j : ↥I, (b j * c j)) hBmem
    have hBt : MvPolynomial.aeval t (∏ j : ↥I, (b j * c j)) ≠ 0 := htB
    have hprod_eq : MvPolynomial.aeval t (∏ j : ↥I, (b j * c j)) =
        ∏ j : ↥I, (MvPolynomial.aeval t (b j) * MvPolynomial.aeval t (c j)) := by
      simp [map_prod, map_mul]
    have hne_all : ∀ j : ↥I, MvPolynomial.aeval t (b j) ≠ 0 ∧
        MvPolynomial.aeval t (c j) ≠ 0 := by
      rw [hprod_eq] at hBt
      rw [Finset.prod_ne_zero_iff] at hBt
      intro j
      have hj := hBt j (Finset.mem_univ j)
      exact mul_ne_zero_iff.mp hj
    have ht_mem : ∀ (i : ι) (hi : i ∈ I), t ∈ (φ.image (V i)).points := by
      intro i hi
      simp only [AffineVariety.points, MvPolynomial.mem_zeroLocus_iff, hbot ⟨i, hi⟩,
        Ideal.mem_bot]
      intro f hf
      rw [hf]
      simp
    refine ⟨t, fun i => if hi : i ∈ I then
      (hcount ⟨i, hi⟩ t (ht_mem i hi) (hne_all ⟨i, hi⟩).2).1.toFinset else ∅, fun i hi => ?_⟩
    simp only [dif_pos hi]
    have hcnt := hcount ⟨i, hi⟩ t (ht_mem i hi) (hne_all ⟨i, hi⟩).2
    have hdeg := hrdeg ⟨i, hi⟩
    have hav := havoid ⟨i, hi⟩
    have hb_ne : MvPolynomial.eval t (b ⟨i, hi⟩) ≠ 0 := (hne_all ⟨i, hi⟩).1
    refine ⟨?_, ?_, ?_⟩
    · have hn : (hcnt.1.toFinset.card : ℚ) = (r ⟨i, hi⟩ : ℚ) := by
        have hcard : hcnt.1.toFinset.card = r ⟨i, hi⟩ := by
          rw [← Set.ncard_eq_toFinset_card _ hcnt.1]
          exact hcnt.2
        rw [hcard]
      rw [hn, hdeg]
    · intro x
      exact hcnt.1.mem_toFinset
    · intro x hx
      have hfib := (hcnt.1.mem_toFinset.mp hx)
      have hbx : MvPolynomial.eval (φ.apply x) (b ⟨i, hi⟩) ≠ 0 := by
        have heq : φ.apply x = t := hfib.2
        rw [heq]
        exact hb_ne
      exact hav x hfib.1 hbx
  · refine ⟨0, fun _ => ∅, fun i hi => False.elim (hI ⟨i, hi⟩)⟩

/-- The literal two blocks of linear equations on the full label space. -/
def commonBlockLinearMap {d k : ℕ} (φ ψ : LinearProjection d k) :
    Point (d + d) →ₗ[ℂ] Point (k + k) :=
  (TrackD.productLinearEquiv (d := k)).toLinearMap.comp
    ((φ.prodMap ψ).comp (TrackD.productLinearEquiv (d := d)).symm.toLinearMap)

theorem common_block_linear_map_product {d k : ℕ} (φ ψ : LinearProjection d k)
    (x v : Point d) :
    commonBlockLinearMap φ ψ (TrackD.productPoint x v) =
      TrackD.productPoint (φ x) (ψ v) := by
  unfold commonBlockLinearMap
  simp only [LinearMap.comp_apply]
  have hbase : (TrackD.productLinearEquiv (d := d)).symm (TrackD.productPoint x v)
      = (x, v) := by
    have h := (TrackD.productLinearEquiv (d := d)).left_inv (x, v)
    simpa [TrackD.productLinearEquiv] using h
  have hsym : (TrackD.productLinearEquiv (d := d)).symm.toLinearMap
      (TrackD.productPoint x v) = (x, v) := hbase
  rw [hsym]
  simp only [LinearMap.prodMap_apply]
  rfl

/-- Both tangent certificates belong to the ORIGINAL complete product image
and complete radial slice at the literal actual pair. -/
def commonTangentPair {d : ℕ} (i₀ : Fin d) (X Y : AffineVariety d)
    (p y : Point d) : Prop :=
  (y - p) i₀ ≠ 0 ∧
  ((TrackD.productVariety X Y).tangentSpace (TrackD.productPoint p y)).map
    (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) (TrackD.productPoint p y)) =
    (commonProductImage i₀ X Y).tangentSpace
      (TrackD.productPoint p (TrackD.dirChart (LinearMap.proj i₀) (y - p))) ∧
  (Y.tangentSpace y).map (TrackD.dirChartDeriv (LinearMap.proj i₀) (y - p)) =
    (TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀)).tangentSpace
      (TrackD.dirChart (LinearMap.proj i₀) (y - p))

end
end DistinctDistances.SparseCones
