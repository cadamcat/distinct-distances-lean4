import DistinctDistances.TrackE.MReqAux
import DistinctDistances.Bridges.DirectionSections
import DistinctDistances.Bridges.ProjectiveEnvelope
import DistinctDistances.TrackA.RadialFiberSupport
import DistinctDistances.TrackA.RelativePointIsolationSupport
import DistinctDistances.TrackA.Intersections
import DistinctDistances.Foundations.Projection
import DistinctDistances.Foundations.Projective
import DistinctDistances.Foundations.Affine
import DistinctDistances.TrackE.DirectionFibers

namespace DistinctDistances.SparseCones.MOLiftAux

open scoped BigOperators Classical

noncomputable section

variable {d : ℕ}

/-- Projective subvariety inclusion from points inclusion. -/
theorem projectiveSubvariety_of_points_subset
    (W V : ProjectiveVariety d) (h : W.points ⊆ V.points) :
    W.Subvariety V := by
  have hrep : ProjectiveVariety.nonzeroRepresentatives W.points ⊆
      ProjectiveVariety.nonzeroRepresentatives V.points := by
    intro v hv
    obtain ⟨hv0, hmem⟩ := hv
    exact ⟨hv0, h hmem⟩
  have hvan : MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives V.points) ≤
      MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives W.points) :=
    MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) hrep
  have hW : MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives W.points) = W.ideal :=
    ProjectiveVariety.vanishingIdeal_points W
  have hV : MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives V.points) = V.ideal :=
    ProjectiveVariety.vanishingIdeal_points V
  rw [hV, hW] at hvan
  exact hvan

/-- Singleton affine variety has dimension zero. -/
theorem affine_singleton_dimension_zero (C : AffineVariety d) (x : Point d)
    (hpts : C.points = {x}) : C.dimension = 0 := by
  have Hideal : C.ideal = pointIdeal x := by
    have h1 : C.ideal = MvPolynomial.vanishingIdeal ℂ C.points := by
      rw [AffineVariety.vanishingIdeal_points]
    rw [h1, hpts]
    rfl
  have hdim : OAI.QuarticPowerFree.affineDimension C.ideal = 0 := by
    rw [Hideal]
    exact TrackA.pointIdeal_affineDimension_zero x
  exact hdim

/-- A coordinate separating two distinct points. -/
theorem exists_coord_ne_of_ne {x1 x2 : Point d} (hne : x1 ≠ x2) :
    ∃ i : Fin d, x1 i ≠ x2 i := by
  by_contra hcon
  push Not at hcon
  apply hne
  funext i
  exact hcon i

/-- A finite affine variety containing two distinct points is reducible. -/
theorem affine_finite_not_prime_of_two_points (C : AffineVariety d)
    (x1 x2 : Point d) (h1 : x1 ∈ C.points) (h2 : x2 ∈ C.points) (hne : x1 ≠ x2)
    (hfin : C.points.Finite) : ¬ C.IsIrreducible := by
  classical
  intro hirr
  obtain ⟨i0, hi0⟩ := exists_coord_ne_of_ne (d := d) hne
  let f1 : Poly d := MvPolynomial.X i0 - MvPolynomial.C (x1 i0)
  have hf1x1 : MvPolynomial.aeval x1 f1 = 0 := by simp [f1]
  have hf1x2 : MvPolynomial.aeval x2 f1 ≠ 0 := by
    simp only [f1, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    exact sub_ne_zero.mpr (Ne.symm hi0)
  have hcoord : ∀ y : Point d, y ∈ C.points → y ≠ x1 → ∃ j : Fin d, y j ≠ x1 j := by
    intro y _ hy
    exact exists_coord_ne_of_ne hy
  choose j hj using hcoord
  let S := hfin.toFinset.filter (fun y => y ≠ x1)
  have hS : ∀ y ∈ S, y ∈ C.points ∧ y ≠ x1 := by
    intro y hy
    have hmem : y ∈ hfin.toFinset := Finset.mem_of_mem_filter y hy
    have hne' : y ≠ x1 := (Finset.mem_filter.mp hy).2
    exact ⟨hfin.mem_toFinset.mp hmem, hne'⟩
  let g : Point d → Poly d := fun y =>
    if hy : y ∈ S then
      MvPolynomial.X (j y (hS y hy).1 (hS y hy).2) -
        MvPolynomial.C (y (j y (hS y hy).1 (hS y hy).2))
    else 1
  have hg_zero : ∀ y ∈ S, MvPolynomial.aeval y (g y) = 0 := by
    intro y hy
    have heq : g y =
        MvPolynomial.X (j y (hS y hy).1 (hS y hy).2) -
          MvPolynomial.C (y (j y (hS y hy).1 (hS y hy).2)) := by
      simp only [g, dif_pos hy]
    rw [heq]
    simp
  have hg_ne : ∀ y ∈ S, MvPolynomial.aeval x1 (g y) ≠ 0 := by
    intro y hy
    have heq : g y =
        MvPolynomial.X (j y (hS y hy).1 (hS y hy).2) -
          MvPolynomial.C (y (j y (hS y hy).1 (hS y hy).2)) := by
      simp only [g, dif_pos hy]
    rw [heq]
    simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    exact sub_ne_zero.mpr (Ne.symm (hj y (hS y hy).1 (hS y hy).2))
  let f2 : Poly d := ∏ y ∈ S, g y
  have hf2_zero : ∀ y ∈ S, MvPolynomial.aeval y f2 = 0 := by
    intro y hy
    have hprod : MvPolynomial.aeval y f2 = ∏ w ∈ S, MvPolynomial.aeval y (g w) := by
      simp [f2, map_prod]
    rw [hprod]
    exact Finset.prod_eq_zero hy (hg_zero y hy)
  have hf2_ne : MvPolynomial.aeval x1 f2 ≠ 0 := by
    have hprod : MvPolynomial.aeval x1 f2 = ∏ w ∈ S, MvPolynomial.aeval x1 (g w) := by
      simp [f2, map_prod]
    rw [hprod, Finset.prod_ne_zero_iff]
    intro y hy
    exact hg_ne y hy
  have hprod_mem : f1 * f2 ∈ C.ideal := by
    rw [← AffineVariety.vanishingIdeal_points C]
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    by_cases hzx1 : z = x1
    · rw [hzx1, map_mul, hf1x1, zero_mul]
    · have hzS : z ∈ S := by
        simp only [S, Finset.mem_filter]
        exact ⟨hfin.mem_toFinset.mpr hz, hzx1⟩
      rw [map_mul]
      exact mul_eq_zero_of_right _ (hf2_zero z hzS)
  have hf1_notmem : f1 ∉ C.ideal := by
    intro hmem
    have hz := MvPolynomial.mem_zeroLocus_iff.mp h2 f1 hmem
    exact hf1x2 hz
  have hf2_notmem : f2 ∉ C.ideal := by
    intro hmem
    have hz := MvPolynomial.mem_zeroLocus_iff.mp h1 f2 hmem
    exact hf2_ne hz
  exact (hirr.mem_or_mem hprod_mem).elim hf1_notmem hf2_notmem

/-- 187h: a curve projecting into an irreducible curve with generic degree
has image of dimension one and degree at most that of the target. -/
theorem outer_projection_image_bounds_aux (p : Point d) (C : AffineVariety d)
    (γ : ProjectiveVariety d)
    (hC : C.IsIrreducible ∧ C.dimension = 1)
    (hγ : γ.IsIrreducible ∧ γ.dimension = 1)
    (hproj : (radialImage p C).points ⊆ γ.points)
    (r : ℕ) (hdeg : GenericallyFiniteRadialDegree p C r) :
    (radialImage p C).dimension = 1 ∧ (radialImage p C).degree ≤ γ.degree := by
  obtain ⟨hCirr, hCdim⟩ := hC
  obtain ⟨hγirr, hγdim⟩ := hγ
  have hx0 : ∃ x ∈ C.points, x ≠ p := TrackA.radial_actual_of_generic C p hdeg
  obtain ⟨x0, hx0C, hx0ne⟩ := hx0
  obtain ⟨_, g, D, hhom, hgnot, hfib⟩ := hdeg
  have hWirr : (radialImage p C).IsIrreducible :=
    radialImage_irreducible p C hCirr ⟨x0, hx0C, hx0ne⟩
  have hsub : (radialImage p C).Subvariety γ :=
    projectiveSubvariety_of_points_subset _ _ hproj
  have hWne : (radialImage p C).points.Nonempty := by
    refine ⟨_, ProjectiveVariety.subset_closure _ ⟨x0, hx0C, hx0ne, rfl⟩⟩
  have hγne : γ.points.Nonempty :=
    ProjectiveFamily.irreducible_points_nonempty γ hγirr
  have hdim_le : (radialImage p C).dimension ≤ 1 := by
    have hmono := DistinctDistances.MReqAux.projective_cone_dimension_mono
      γ (radialImage p C) hsub
    rw [ProjectiveVariety.dimension_cone _ hWne,
      ProjectiveVariety.dimension_cone _ hγne, hγdim] at hmono
    omega
  have hdim_ne0 : (radialImage p C).dimension ≠ 0 := by
    intro h0
    obtain ⟨pt, hpt⟩ :=
      DistinctDistances.Bridges.projective_zero_dim_singleton _ hWirr h0
    have hgne_eval : MvPolynomial.eval pt.rep g ≠ 0 := by
      by_contra hcon
      apply hgnot
      have hWideal : (radialImage p C).ideal =
          ProjectiveVariety.vanishingIdeal {pt} := by
        rw [← hpt, ProjectiveVariety.vanishingIdeal_points]
      rw [hWideal]
      show g ∈ MvPolynomial.vanishingIdeal ℂ
        (ProjectiveVariety.nonzeroRepresentatives {pt})
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro v hv
      obtain ⟨hv0, hmem⟩ := hv
      have hmem' : Projectivization.mk ℂ v hv0 = pt :=
        Set.mem_singleton_iff.mp hmem
      have hmem'' : Projectivization.mk ℂ v hv0 =
          Projectivization.mk ℂ pt.rep pt.rep_nonzero :=
        hmem'.trans (Projectivization.mk_rep pt).symm
      obtain ⟨c, hc⟩ :=
        (Projectivization.mk_eq_mk_iff' ℂ v pt.rep hv0 pt.rep_nonzero).mp hmem''
      have hsmul := DistinctDistances.Bridges.homogeneous_eval_smul g hhom c pt.rep
      have hc_eq : v = c • pt.rep := hc.symm
      simp only [MvPolynomial.aeval_eq_eval] at *
      rw [hc_eq, hsmul, hcon, mul_zero]
    have hgne : MvPolynomial.aeval pt.rep g ≠ 0 := by
      simpa [MvPolynomial.aeval_eq_eval] using hgne_eval
    have hptmem : pt ∈ (radialImage p C).points := by
      rw [hpt]; exact Set.mem_singleton pt
    obtain ⟨hfin, _⟩ := hfib pt hptmem hgne
    have hfiber_eq : radialFiber p C pt = {x | x ∈ C.points ∧ x ≠ p} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxc, hxne, _⟩ := hx
        exact ⟨hxc, hxne⟩
      · intro hx
        obtain ⟨hxc, hxne⟩ := hx
        refine ⟨hxc, hxne, ?_⟩
        have hmem : radialProjection p x hxne ∈ (radialImage p C).points :=
          ProjectiveVariety.subset_closure _ ⟨x, hxc, hxne, rfl⟩
        rw [hpt] at hmem
        exact Set.mem_singleton_iff.mp hmem
    have hCfin : C.points.Finite := by
      have hsub2 : C.points ⊆ radialFiber p C pt ∪ {p} := by
        intro x hxc
        by_cases hxne : x = p
        · exact Or.inr (Set.mem_singleton_iff.mpr hxne)
        · exact Or.inl (hfiber_eq ▸ ⟨hxc, hxne⟩)
      exact (hfin.union (Set.finite_singleton p)).subset hsub2
    by_cases hpC : p ∈ C.points
    · exact affine_finite_not_prime_of_two_points C p x0 hpC hx0C
        (Ne.symm hx0ne) hCfin hCirr
    · have hCeq : C.points = radialFiber p C pt := by
        ext x
        constructor
        · intro hxc
          have hxne : x ≠ p := fun heq => hpC (heq ▸ hxc)
          exact hfiber_eq ▸ ⟨hxc, hxne⟩
        · intro hxf
          exact (hfiber_eq ▸ hxf).1
      by_cases hsing : C.points = {x0}
      · have hdim0 : C.dimension = 0 := affine_singleton_dimension_zero C x0 hsing
        omega
      · have hex : ∃ x1 ∈ C.points, x1 ≠ x0 := by
          by_contra hcon
          push Not at hcon
          have hsub3 : C.points ⊆ {x0} := fun x hxc =>
            Set.mem_singleton_iff.mpr (hcon x hxc)
          have heq3 : C.points = {x0} :=
            Set.Subset.antisymm hsub3 (Set.singleton_subset_iff.mpr hx0C)
          exact hsing heq3
        obtain ⟨x1, hx1C, hx1ne⟩ := hex
        exact affine_finite_not_prime_of_two_points C x0 x1 hx0C hx1C
          (Ne.symm hx1ne) hCfin hCirr
  have hdim_eq : (radialImage p C).dimension = 1 := by omega
  have hcone_eq : (radialImage p C).affineCone.dimension =
      γ.affineCone.dimension := by
    rw [ProjectiveVariety.dimension_cone _ hWne,
      ProjectiveVariety.dimension_cone _ hγne, hdim_eq, hγdim]
  have hideal_eq : (radialImage p C).ideal = γ.ideal := by
    have heq := DistinctDistances.MReqAux.projective_ideal_eq_of_cone_dim_eq
      γ (radialImage p C) hγirr hWirr hsub hcone_eq
    exact heq.symm
  have heq : radialImage p C = γ := ProjectiveVariety.ext hideal_eq
  exact ⟨hdim_eq, heq ▸ le_rfl⟩

/-- Chart homogenization exponent: pad with the chart variable to total degree. -/
def chartHomogenizeExponent (D : ℕ) (i₀ : Fin d) (s : Fin d →₀ ℕ) : Fin d →₀ ℕ :=
  s + Finsupp.single i₀ (D - s.degree)

theorem chartHomogenizeExponent_degree (D : ℕ) (i₀ : Fin d) (s : Fin d →₀ ℕ)
    (hD : s.degree ≤ D) : (chartHomogenizeExponent D i₀ s).degree = D := by
  have hadd : (s + Finsupp.single i₀ (D - s.degree)).degree =
      s.degree + (Finsupp.single i₀ (D - s.degree)).degree := map_add _ _ _
  have hsingle : (Finsupp.single i₀ (D - s.degree) : Fin d →₀ ℕ).degree =
      D - s.degree := Finsupp.degree_single _ _
  simp only [chartHomogenizeExponent, hadd, hsingle]
  omega

/-- Homogenize a polynomial in the chart `X_{i₀} ≠ 0` to its total degree. -/
def chartHomogenize (H : Poly d) (i₀ : Fin d) : Poly d :=
  ∑ s ∈ H.support, MvPolynomial.monomial (chartHomogenizeExponent H.totalDegree i₀ s) (H.coeff s)

theorem chartHomogenize_homogeneous (H : Poly d) (i₀ : Fin d) :
    (chartHomogenize H i₀).IsHomogeneous H.totalDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro s hs
  apply MvPolynomial.isHomogeneous_monomial
  exact chartHomogenizeExponent_degree H.totalDegree i₀ s (MvPolynomial.le_totalDegree hs)

theorem chartHomogenize_totalDegree_le (H : Poly d) (i₀ : Fin d) :
    (chartHomogenize H i₀).totalDegree ≤ H.totalDegree := by
  classical
  by_cases hH : H = 0
  · simp [chartHomogenize, hH]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro s hs
    -- monomial of degree D has totalDegree ≤ D
    have hle : (MvPolynomial.monomial (chartHomogenizeExponent H.totalDegree i₀ s)
        (H.coeff s)).totalDegree ≤ H.totalDegree := by
      by_cases hc : H.coeff s = 0
      · simp [hc]
      · have hdeg := chartHomogenizeExponent_degree H.totalDegree i₀ s
          (MvPolynomial.le_totalDegree hs)
        have hmono : (MvPolynomial.monomial (chartHomogenizeExponent H.totalDegree i₀ s)
            (H.coeff s)).totalDegree ≤
            (chartHomogenizeExponent H.totalDegree i₀ s).degree := by
          exact MvPolynomial.totalDegree_monomial_le _ _
        rw [hdeg] at hmono
        exact hmono
    exact hle

/-- Evaluation of a monomial exponent. -/
theorem eval_chartHomogenizeExponent (w : Point d) (i₀ : Fin d)
    (s : Fin d →₀ ℕ) (D : ℕ) :
    MvPolynomial.eval w
      (MvPolynomial.monomial (chartHomogenizeExponent D i₀ s) (1 : ℂ)) =
      s.prod (fun i e => w i ^ e) * w i₀ ^ (D - s.degree) := by
  classical
  have heval : MvPolynomial.eval w
      (MvPolynomial.monomial (chartHomogenizeExponent D i₀ s) (1 : ℂ)) =
      (chartHomogenizeExponent D i₀ s).prod (fun i e => w i ^ e) := by
    rw [MvPolynomial.eval_monomial]
    simp
  rw [heval]
  simp only [chartHomogenizeExponent]
  have hsplit : (s + Finsupp.single i₀ (D - s.degree)).prod (fun i e => w i ^ e) =
      s.prod (fun i e => w i ^ e) *
        (Finsupp.single i₀ (D - s.degree)).prod (fun i e => w i ^ e) := by
    apply Finsupp.prod_add_index
    · intro a _
      exact pow_zero _
    · intro a _ b1 b2
      exact pow_add _ _ _
  rw [hsplit]
  have hsingle : (Finsupp.single i₀ (D - s.degree)).prod (fun i e => w i ^ e) =
      w i₀ ^ (D - s.degree) :=
    Finsupp.prod_single_index (pow_zero _)
  rw [hsingle]

/-- Product form of the chart-homogenization exponent. -/
theorem chartHomogenizeExponent_prod (w : Point d) (i₀ : Fin d)
    (s : Fin d →₀ ℕ) (D : ℕ) :
    (chartHomogenizeExponent D i₀ s).prod (fun i e => w i ^ e) =
      s.prod (fun i e => w i ^ e) * w i₀ ^ (D - s.degree) := by
  classical
  simp only [chartHomogenizeExponent]
  have hsplit : (s + Finsupp.single i₀ (D - s.degree)).prod (fun i e => w i ^ e) =
      s.prod (fun i e => w i ^ e) *
        (Finsupp.single i₀ (D - s.degree)).prod (fun i e => w i ^ e) := by
    apply Finsupp.prod_add_index
    · intro a _
      exact pow_zero _
    · intro a _ b1 b2
      exact pow_add _ _ _
  rw [hsplit]
  have hsingle : (Finsupp.single i₀ (D - s.degree)).prod (fun i e => w i ^ e) =
      w i₀ ^ (D - s.degree) :=
    Finsupp.prod_single_index (pow_zero _)
  rw [hsingle]

/-- Evaluation of a scaled monomial splits off the scaling power. -/
theorem smul_monomial_prod (w : Point d) (s : Fin d →₀ ℕ) (c : ℂ) :
    s.prod (fun i e => ((c • w) i) ^ e) = c ^ s.degree * s.prod (fun i e => w i ^ e) := by
  classical
  have hpt : ∀ i : Fin d, ∀ e : ℕ, ((c • w) i) ^ e = c ^ e * w i ^ e := by
    intro i e
    simp [Pi.smul_apply, smul_eq_mul, mul_pow]
  have hsplit : s.prod (fun i e => ((c • w) i) ^ e) =
      s.prod (fun i e => c ^ e) * s.prod (fun i e => w i ^ e) := by
    simp_rw [hpt]
    simp only [Finsupp.prod, Finset.prod_mul_distrib]
  rw [hsplit]
  congr 1
  simp only [Finsupp.prod, Finsupp.degree_apply]
  exact Finset.prod_pow_eq_pow_sum s.support (fun i => s i) c

/-- Cancelling a chart power against its inverse. -/
theorem chart_pow_mul_inv_pow (w0 : ℂ) (hw0 : w0 ≠ 0) (D : ℕ) (e : ℕ) (hle : e ≤ D) :
    w0 ^ D * ((w0⁻¹) ^ e) = w0 ^ (D - e) := by
  have hDeq : D = e + (D - e) := (Nat.add_sub_cancel' hle).symm
  conv_lhs => rw [hDeq, pow_add]
  rw [mul_comm (w0 ^ e) (w0 ^ (D - e)), mul_assoc, ← mul_pow, mul_inv_cancel₀ hw0,
    one_pow, mul_one]

/-- Full chart-homogenization evaluation formula. -/
theorem chartHomogenize_eval (H : Poly d) (i₀ : Fin d) (w : Point d)
    (hw : w i₀ ≠ 0) :
    MvPolynomial.eval w (chartHomogenize H i₀) =
      w i₀ ^ H.totalDegree *
        MvPolynomial.eval ((w i₀)⁻¹ • w) H := by
  classical
  set D := H.totalDegree with hDdef
  have hHas : H = ∑ s ∈ H.support, MvPolynomial.monomial s (H.coeff s) :=
    MvPolynomial.as_sum H
  simp only [chartHomogenize, ← hDdef]
  rw [MvPolynomial.eval_sum]
  conv_rhs => rw [hHas, MvPolynomial.eval_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hle : s.degree ≤ D := by
    rw [hDdef]
    exact MvPolynomial.le_totalDegree hs
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
    smul_monomial_prod w s (((w i₀))⁻¹),
    chartHomogenizeExponent_prod w i₀ s D]
  have hpc : (w i₀) ^ D * (((w i₀))⁻¹ ^ s.degree) = (w i₀) ^ (D - s.degree) :=
    chart_pow_mul_inv_pow (w i₀) hw D s.degree hle
  calc H.coeff s * (s.prod (fun i e => w i ^ e) * (w i₀) ^ (D - s.degree))
      = H.coeff s * s.prod (fun i e => w i ^ e) *
        ((w i₀) ^ D * ((w i₀))⁻¹ ^ s.degree) := by rw [← hpc]; ring
    _ = (w i₀) ^ D * (H.coeff s * (((w i₀))⁻¹ ^ s.degree * s.prod (fun i e => w i ^ e))) := by
        ring

/-- Specializing a pair monomial at the source does not increase degree. -/
theorem pairFixLeft_monomial_totalDegree_le (s : Fin d ⊕ Fin d →₀ ℕ) (c : ℂ)
    (p : Point d) :
    (TrackD.pairFixLeft (MvPolynomial.monomial s c) p).totalDegree ≤ s.degree := by
  classical
  simp only [TrackD.pairFixLeft]
  rw [MvPolynomial.aeval_monomial]
  have hC : (algebraMap ℂ (Poly d)) c = MvPolynomial.C c := by simp
  rw [hC]
  have hprod_le : (s.prod (fun i k =>
      (Sum.elim (fun j => MvPolynomial.C (p j)) MvPolynomial.X i) ^ k)).totalDegree ≤
      s.degree := by
    have heq : s.prod (fun i k =>
        (Sum.elim (fun j => MvPolynomial.C (p j)) MvPolynomial.X i) ^ k) =
        ∏ i ∈ s.support,
          (Sum.elim (fun j => MvPolynomial.C (p j)) MvPolynomial.X i) ^ (s i) := rfl
    rw [heq, Finsupp.degree_apply]
    apply le_trans (MvPolynomial.totalDegree_finsetProd s.support _)
    apply Finset.sum_le_sum
    intro i _
    cases i with
    | inl k =>
      simp only [Sum.elim_inl]
      calc ((MvPolynomial.C (p k) ^ s (Sum.inl k)) : Poly d).totalDegree
          ≤ s (Sum.inl k) * (MvPolynomial.C (p k)).totalDegree :=
            MvPolynomial.totalDegree_pow _ _
        _ = s (Sum.inl k) * 0 := by rw [MvPolynomial.totalDegree_C]
        _ = 0 := Nat.mul_zero _
        _ ≤ s (Sum.inl k) := Nat.zero_le _
    | inr k =>
      simp only [Sum.elim_inr]
      calc ((MvPolynomial.X k ^ s (Sum.inr k)) : Poly d).totalDegree
          ≤ s (Sum.inr k) * (MvPolynomial.X k).totalDegree :=
            MvPolynomial.totalDegree_pow _ _
        _ = s (Sum.inr k) * 1 := by rw [MvPolynomial.totalDegree_X]
        _ = s (Sum.inr k) := Nat.mul_one _
  calc (MvPolynomial.C c * s.prod (fun i k =>
        (Sum.elim (fun j => MvPolynomial.C (p j)) MvPolynomial.X i) ^ k)).totalDegree
      ≤ (MvPolynomial.C c).totalDegree + (s.prod (fun i k =>
        (Sum.elim (fun j => MvPolynomial.C (p j)) MvPolynomial.X i) ^ k)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ = 0 + (s.prod (fun i k =>
        (Sum.elim (fun j => MvPolynomial.C (p j)) MvPolynomial.X i) ^ k)).totalDegree := by
        rw [MvPolynomial.totalDegree_C]
    _ = (s.prod (fun i k =>
        (Sum.elim (fun j => MvPolynomial.C (p j)) MvPolynomial.X i) ^ k)).totalDegree :=
        Nat.zero_add _
    _ ≤ s.degree := hprod_le

/-- Specializing a pair polynomial at the source does not increase degree. -/
theorem pairFixLeft_totalDegree_le (G : TrackD.PairPoly d) (p : Point d) :
    (TrackD.pairFixLeft G p).totalDegree ≤ G.totalDegree := by
  classical
  by_cases hG : G = 0
  · simp [hG, TrackD.pairFixLeft]
  · have hAs : G = ∑ s ∈ G.support, MvPolynomial.monomial s (G.coeff s) :=
      MvPolynomial.as_sum G
    have hmap : TrackD.pairFixLeft G p =
        ∑ s ∈ G.support, TrackD.pairFixLeft (MvPolynomial.monomial s (G.coeff s)) p := by
      conv_lhs => rw [hAs]
      simp only [TrackD.pairFixLeft, MvPolynomial.aeval_sum]
    rw [hmap]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro s hs
    exact le_trans (pairFixLeft_monomial_totalDegree_le s (G.coeff s) p)
      (MvPolynomial.le_totalDegree hs)

/-- A chart witness keeps the homogenization off the component ideal. -/
theorem chartHomogenize_not_mem_of_witness (H : Poly d) (i₀ : Fin d)
    (γ : ProjectiveVariety d) (z : ProjectivePoint d)
    (hz : z ∈ γ.points) (hw : z.rep i₀ ≠ 0)
    (hH : MvPolynomial.eval (((z.rep i₀)⁻¹) • z.rep) H ≠ 0) :
    chartHomogenize H i₀ ∉ γ.ideal := by
  intro hmem
  have hvan : chartHomogenize H i₀ ∈ ProjectiveVariety.vanishingIdeal γ.points := by
    rw [ProjectiveVariety.vanishingIdeal_points]
    exact hmem
  have hrep : z.rep ∈ ProjectiveVariety.nonzeroRepresentatives γ.points := by
    refine ⟨z.rep_nonzero, ?_⟩
    have hmk : Projectivization.mk ℂ z.rep z.rep_nonzero = z :=
      Projectivization.mk_rep z
    rw [hmk]
    exact hz
  have hzero := (MvPolynomial.mem_vanishingIdeal_iff.mp hvan) z.rep hrep
  rw [MvPolynomial.aeval_eq_eval] at hzero
  have heval := chartHomogenize_eval H i₀ z.rep hw
  rw [heval] at hzero
  exact (mul_ne_zero (pow_ne_zero _ hw) hH) hzero

/-- Specialized vanishing is homogenized vanishing in the chart. -/
theorem outerGammaInEqs_vanishing_iff (i₀ : Fin d) (G : TrackD.PairPoly d)
    (p : Point d) (z : ProjectivePoint d) (hw : z.rep i₀ ≠ 0) :
    (MvPolynomial.eval (TrackD.pairPt p (((z.rep i₀)⁻¹) • z.rep)) G = 0 ↔
      MvPolynomial.eval z.rep
        (chartHomogenize (TrackD.pairFixLeft G p) i₀) = 0) := by
  have heval := chartHomogenize_eval (TrackD.pairFixLeft G p) i₀ z.rep hw
  have hspec : MvPolynomial.eval (((z.rep i₀)⁻¹) • z.rep)
      (TrackD.pairFixLeft G p) =
      MvPolynomial.eval (TrackD.pairPt p (((z.rep i₀)⁻¹) • z.rep)) G :=
    TrackD.eval_pairFixLeft G p _
  rw [heval, hspec]
  have hpow : (z.rep i₀) ^ (TrackD.pairFixLeft G p).totalDegree ≠ 0 :=
    pow_ne_zero _ hw
  constructor
  · intro h0
    rw [h0, mul_zero]
  · intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hpow
    · exact h

/-- Bad directions across a family are bounded by the family degree times `Bdeg`. -/
theorem badDirections_card_le_of_gamma_bounds
    (CfP : ProjectiveFamily.Family d) (E Bdeg : ℝ)
    (hB : 0 ≤ Bdeg)
    (hE : ((ProjectiveFamily.degree CfP : ℚ) : ℝ) ≤ E)
    (F : ProjectiveVariety d → Finset (ProjectivePoint d))
    (hF : ∀ γ ∈ CfP, ((F γ).card : ℝ) ≤ (((γ.degree : ℚ) : ℝ)) * Bdeg) :
    (((CfP.biUnion F).card : ℝ)) ≤ E * Bdeg := by
  classical
  calc (((CfP.biUnion F).card : ℝ))
      ≤ ∑ γ ∈ CfP, (((F γ).card : ℝ)) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ γ ∈ CfP, (((γ.degree : ℚ) : ℝ) * Bdeg) :=
        Finset.sum_le_sum hF
    _ = (∑ γ ∈ CfP, (((γ.degree : ℚ) : ℝ))) * Bdeg := by
        rw [Finset.sum_mul]
    _ ≤ E * Bdeg := by
        have hsum : (∑ γ ∈ CfP, (((γ.degree : ℚ) : ℝ))) =
            (((ProjectiveFamily.degree CfP : ℚ) : ℝ)) := by
          simp [ProjectiveFamily.degree]
        rw [hsum]
        exact mul_le_mul_of_nonneg_right hE hB

/-- Row targets over bad directions are bounded by the cap times the direction bound. -/
theorem discard_row_bound_of_gamma_bounds
    (P T : Finset (RPoint d)) (p : RPoint d)
    (CfP : ProjectiveFamily.Family d) (E Bdeg cap : ℝ)
    (hcap : 0 ≤ cap) (hB : 0 ≤ Bdeg)
    (hE : ((ProjectiveFamily.degree CfP : ℚ) : ℝ) ≤ E)
    (F : ProjectiveVariety d → Finset (ProjectivePoint d))
    (hF : ∀ γ ∈ CfP, ((F γ).card : ℝ) ≤ (((γ.degree : ℚ) : ℝ)) * Bdeg)
    (hT : T ⊆ P)
    (hlight : ∀ q ∈ T, ((P.filter (· ∈ affineSpan ℝ {p, q})).card : ℝ) ≤ cap)
    (hcover : ∀ q ∈ T, ∃ h : cplx q ≠ cplx p,
      radialProjection (cplx p) (cplx q) h ∈ CfP.biUnion F) :
    ((T.card : ℝ)) ≤ cap * (E * Bdeg) := by
  classical
  have hUnion : (((CfP.biUnion F).card : ℝ)) ≤ E * Bdeg :=
    badDirections_card_le_of_gamma_bounds CfP E Bdeg hB hE F hF
  have hcount : ((T.card : ℝ)) ≤ cap * (((CfP.biUnion F).card : ℝ)) :=
    DistinctDistances.Reduction.card_partners_on_finite_directions_le
      P T p (CfP.biUnion F) cap hcap hT hlight hcover
  calc ((T.card : ℝ)) ≤ cap * (((CfP.biUnion F).card : ℝ)) := hcount
    _ ≤ cap * (E * Bdeg) := mul_le_mul_of_nonneg_left hUnion hcap

/-- Row sums over a pool are bounded by the `hsmall` product budget. -/
theorem discard_global_bound_of_row_sums
    (S : Finset (RPoint d)) (row : RPoint d → ℕ)
    (cap E Bdeg ρ' : ℝ)
    (hsmall : E * Bdeg * cap ≤ ρ' * ((S.card : ℝ)))
    (hrow : ∀ p ∈ S, (((row p : ℕ)) : ℝ) ≤ cap * (E * Bdeg)) :
    ((((∑ p ∈ S, row p : ℕ)) : ℝ)) ≤ ρ' * (((S.card : ℝ))) ^ 2 := by
  classical
  have hSnonneg : (0 : ℝ) ≤ ((S.card : ℝ)) := Nat.cast_nonneg _
  have hcast : ((((∑ p ∈ S, row p : ℕ)) : ℝ)) = ∑ p ∈ S, ((((row p : ℕ))) : ℝ) :=
    Nat.cast_sum S row
  rw [hcast]
  calc ∑ p ∈ S, ((((row p : ℕ))) : ℝ)
      ≤ ∑ _p ∈ S, (cap * (E * Bdeg)) := Finset.sum_le_sum hrow
    _ = (((S.card : ℝ))) * (cap * (E * Bdeg)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (((S.card : ℝ))) * (E * Bdeg * cap) := by ring
    _ ≤ (((S.card : ℝ))) * (ρ' * (((S.card : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsmall hSnonneg
    _ = ρ' * (((S.card : ℝ))) ^ 2 := by ring

/-- A homogenized zero transfers across reps of one projective point. -/
theorem homogenized_zero_of_rep_eq_of_vector_zero (H : Poly d) (i₀ : Fin d)
    (v : Point d) (hv0 : v ≠ 0) (z : ProjectivePoint d)
    (hmk : Projectivization.mk ℂ v hv0 = z)
    (hH : MvPolynomial.eval v (chartHomogenize H i₀) = 0) :
    MvPolynomial.eval z.rep (chartHomogenize H i₀) = 0 := by
  classical
  have hrep_eq : Projectivization.mk ℂ z.rep z.rep_nonzero = z :=
    Projectivization.mk_rep z
  have hmem : Projectivization.mk ℂ v hv0 =
      Projectivization.mk ℂ z.rep z.rep_nonzero := hmk.trans hrep_eq.symm
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ v z.rep hv0 z.rep_nonzero).mp hmem
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    exact hv0 hc.symm
  have hsmul := DistinctDistances.Bridges.homogeneous_eval_smul
    (chartHomogenize H i₀) (chartHomogenize_homogeneous H i₀) c z.rep
  have hpow : c ^ H.totalDegree ≠ 0 := pow_ne_zero _ hc0
  have hzero : c ^ H.totalDegree * MvPolynomial.eval z.rep (chartHomogenize H i₀) = 0 := by
    rw [← hsmul, hc]
    exact hH
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hpow
  · exact h

/-- Deleted pairs split by source point into row fibers. -/
theorem discard_pair_card_eq_fiber_sum
    (S : Finset (RPoint d)) (D : Finset (RPoint d × RPoint d))
    (hfirst : ∀ pq ∈ D, pq.1 ∈ S) :
    D.card = ∑ p ∈ S, (D.filter (fun pq => pq.1 = p)).card := by
  classical
  have hdisj : (S : Set (RPoint d)).PairwiseDisjoint
      (fun p => D.filter (fun pq : RPoint d × RPoint d => pq.1 = p)) := by
    intro p _ p' _ hne
    apply Finset.disjoint_left.mpr
    rintro pq hpq hpq'
    have h1 : pq.1 = p := (Finset.mem_filter.mp hpq).2
    have h2 : pq.1 = p' := (Finset.mem_filter.mp hpq').2
    exact hne (h1.symm.trans h2)
  have heq : D = S.biUnion (fun p => D.filter (fun pq : RPoint d × RPoint d => pq.1 = p)) := by
    apply Finset.Subset.antisymm
    · intro pq hpq
      exact Finset.mem_biUnion.mpr
        ⟨pq.1, hfirst pq hpq, Finset.mem_filter.mpr ⟨hpq, rfl⟩⟩
    · intro pq hpq
      obtain ⟨_, _, hmem⟩ := Finset.mem_biUnion.mp hpq
      exact Finset.mem_of_mem_filter pq hmem
  conv_lhs => rw [heq]
  rw [Finset.card_biUnion hdisj]

open DistinctDistances.TrackA
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A proper homogeneous cut has a pure projective component family, with
its actual minimal-prime evidence retained for Bézout. -/
theorem projective_homogeneous_cut_family {n : ℕ} (F : ProjectiveFamily.Family n)
    (k : ℕ) (hF : ProjectiveFamily.IsPure F (k+1))
    (ℓ : Poly n) (D : ℕ) (hℓ : ℓ.IsHomogeneous D) (havoid : ∀ V ∈ F, ℓ ∉ V.ideal) :
    ∃ W : ProjectiveFamily.Family n,
      ProjectiveFamily.IsPure W k ∧
      (ProjectiveFamily.locus W).Subvariety (ProjectiveFamily.locus F) ∧
      (∀ p, p ∈ (ProjectiveFamily.locus W).points ↔
        p ∈ (ProjectiveFamily.locus F).points ∧ MvPolynomial.eval p.rep ℓ = 0) ∧
      ℓ ∈ (ProjectiveFamily.locus W).ideal ∧
      (∀ U ∈ W, U.ideal ∈ ((ProjectiveFamily.locus F).ideal ⊔ Ideal.span {ℓ}).minimalPrimes) := by
  let J := (ProjectiveFamily.locus F).ideal ⊔ Ideal.span {ℓ}
  have hspan : (Ideal.span {ℓ}).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
    apply Ideal.homogeneous_span
    rintro f (rfl : f = ℓ)
    exact ⟨D, hℓ⟩
  have hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) :=
    (ProjectiveFamily.locus F).isHomogeneous.sup hspan
  let Qs := {Q : Ideal (Poly n) // Q ∈ J.minimalPrimes}
  letI : Fintype Qs := (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n) J).fintype
  have hdim (Q : Qs) : OAI.QuarticPowerFree.affineDimension Q.val = k+1 :=
    projective_linear_cut_minimal_prime_dimension F k hF ℓ havoid Q.val Q.property
  let φ : Qs → ProjectiveVariety n := fun Q =>
    projectiveVarietyOfHomogeneousPrime Q.val Q.property.isPrime
      (homogeneous_minimal_prime J Q.val hJ Q.property)
      (prime_coordinate_not_mem_of_positive_dimension Q.val Q.property.isPrime (by rw [hdim Q]; omega))
  let W := Finset.univ.image φ
  have hφ (Q : Qs) : (φ Q).IsIrreducible ∧ (φ Q).dimension = k := by
    have hirr : (φ Q).IsIrreducible := Q.property.isPrime
    refine ⟨hirr, ?_⟩
    have heq := (φ Q).dimension_cone (ProjectiveFamily.irreducible_points_nonempty (φ Q) hirr)
    change OAI.QuarticPowerFree.affineDimension Q.val = (φ Q).dimension+1 at heq
    rw [hdim Q] at heq
    omega
  have hrep (U : ProjectiveVariety n) (p : ProjectivePoint n) :
      p ∈ U.points ↔ p.rep ∈ U.affineCone.points := by
    simpa only [Projectivization.mk_rep] using
      ProjectiveVariety.mem_points_mk_iff U p.rep p.rep_nonzero
  have hzero (p : ProjectivePoint n) :
      p ∈ (ProjectiveFamily.locus W).points ↔ p.rep ∈ MvPolynomial.zeroLocus ℂ J := by
    rw [ProjectiveFamily.points_locus]
    constructor
    · intro hp
      obtain ⟨U, hU⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hUW, hpU⟩ := Set.mem_iUnion.mp hU
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hUW
      have hxQ := (hrep (φ Q) p).1 hpU
      exact fun f hf => hxQ f (Q.property.le hf)
    · intro hp
      let P := MvPolynomial.vanishingIdeal ℂ ({p.rep} : Set (Point n))
      have hJP : J ≤ P := by
        intro f hf
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff p.rep f).2 (hp f hf)
      obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hJP
      let c : Qs := ⟨Q,hQ⟩
      have hpφ : p ∈ (φ c).points := by
        apply (hrep (φ c) p).2
        intro f hf
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff p.rep f).1 (hQP hf)
      exact Set.mem_iUnion.mpr ⟨φ c, Set.mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, hpφ⟩⟩
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hU
    exact hφ Q
  · intro f hf
    apply (chart_projective_family_mem W f).2
    intro U hU
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hU
    exact Q.property.le (Ideal.mem_sup_left hf)
  · intro p
    rw [hzero p]
    constructor
    · intro hp
      refine ⟨(hrep (ProjectiveFamily.locus F) p).2 (fun f hf => hp f (Ideal.mem_sup_left hf)), ?_⟩
      simpa only [MvPolynomial.aeval_eq_eval] using
        hp ℓ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton ℓ)))
    · rintro ⟨hpF, hpℓ⟩
      have hker : J ≤ RingHom.ker (MvPolynomial.aeval p.rep).toRingHom := by
        apply sup_le
        · exact fun f hf => (hrep (ProjectiveFamily.locus F) p).1 hpF f hf
        · apply Ideal.span_le.mpr
          rintro f (rfl : f = ℓ)
          exact hpℓ
      exact fun f hf => hker hf
  · constructor
    · apply (chart_projective_family_mem W ℓ).2
      intro U hU
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hU
      exact Q.property.le (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton ℓ)))
    · intro U hU
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hU
      exact Q.property


/-- Bézout gives a finite set containing precisely the zeros of a proper
homogeneous polynomial on an irreducible projective curve. -/
theorem projective_curve_zero_finset (V : ProjectiveVariety d)
    (hV : V.IsIrreducible) (hdim : V.dimension = 1)
    (f : Poly d) (D : ℕ) (hhom : f.IsHomogeneous D) (hf : f ∉ V.ideal) :
    ∃ Z : Finset (ProjectivePoint d),
      (∀ z, z ∈ Z ↔ z ∈ V.points ∧ MvPolynomial.eval z.rep f = 0) ∧
      (Z.card : ℝ) ≤ (D : ℝ) * (V.degree : ℝ) := by
  have hpure : ProjectiveFamily.IsPure ({V} : ProjectiveFamily.Family d) (0+1) := by
    intro U hU
    have heq := Finset.mem_singleton.mp hU
    subst U
    exact ⟨hV, hdim⟩
  have havoid : ∀ U ∈ ({V} : ProjectiveFamily.Family d), f ∉ U.ideal := by
    intro U hU
    simpa only [Finset.mem_singleton.mp hU] using hf
  obtain ⟨W, hW, hsub, hpoints, hmem, hprimes⟩ :=
    projective_homogeneous_cut_family {V} 0 hpure f D hhom havoid
  have hlocus : ProjectiveFamily.locus ({V} : ProjectiveFamily.Family d) = V :=
    Bridges.projective_singleton_locus V
  rw [hlocus] at hpoints hprimes
  have hdeg := (TrackA.fa_bezout_projective_cut V hV f D hhom hf 0 hdim W hprimes).2
  let pt : W → ProjectivePoint d := fun U =>
    Classical.choose (Bridges.projective_zero_dim_singleton U.val
      (hW U.val U.property).1 (hW U.val U.property).2)
  have hpt (U : W) : U.val.points = {pt U} :=
    Classical.choose_spec (Bridges.projective_zero_dim_singleton U.val
      (hW U.val U.property).1 (hW U.val U.property).2)
  let Z := Finset.univ.image pt
  have hZ (z : ProjectivePoint d) : z ∈ Z ↔ z ∈ (ProjectiveFamily.locus W).points := by
    rw [ProjectiveFamily.points_locus]
    constructor
    · intro hz
      obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hz
      exact Set.mem_iUnion.mpr ⟨U.val, Set.mem_iUnion.mpr
        ⟨U.property, by rw [hpt U]; exact Set.mem_singleton _⟩⟩
    · intro hz
      obtain ⟨U, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hUW, hzU⟩ := Set.mem_iUnion.mp hz
      have heq : z = pt ⟨U, hUW⟩ := by
        rw [hpt ⟨U, hUW⟩] at hzU
        exact Set.mem_singleton_iff.mp hzU
      exact Finset.mem_image.mpr ⟨⟨U, hUW⟩, Finset.mem_univ _, heq.symm⟩
  have hcard : Z.card ≤ W.card := by
    calc
      Z.card ≤ (Finset.univ : Finset W).card := Finset.card_image_le
      _ = W.card := by rw [Finset.card_univ]; exact Fintype.card_coe W
  have hWcard : (W.card : ℚ) ≤ ProjectiveFamily.degree W := by
    unfold ProjectiveFamily.degree
    calc
      (W.card : ℚ) = ∑ U ∈ W, (1 : ℚ) := by simp
      _ ≤ ∑ U ∈ W, U.degree := by
        apply Finset.sum_le_sum
        intro U hU
        rw [← U.degree_cone]
        exact U.affineCone.one_le_degree (hW U hU).1.ne_top
  refine ⟨Z, fun z => (hZ z).trans (hpoints z), ?_⟩
  have hrat : (Z.card : ℚ) ≤ (D : ℚ) * V.degree :=
    (by exact_mod_cast hcard : (Z.card : ℚ) ≤ (W.card : ℚ)).trans (hWcard.trans hdeg)
  exact_mod_cast hrat

/-- Projective degrees are nonnegative, including the empty variety. -/
theorem projective_degree_nonneg (V : ProjectiveVariety d) : (0 : ℝ) ≤ (V.degree : ℝ) := by
  have hrat : (0 : ℚ) ≤ V.degree := by
    rw [← V.degree_cone]
    change 0 ≤ OAI.QuarticPowerFree.affineDegree V.ideal
    unfold OAI.QuarticPowerFree.affineDegree
    exact mul_nonneg (Nat.cast_nonneg _)
      (TrackA.affine_hilbert_coefficient_nonneg V.ideal _ le_rfl)
  exact_mod_cast hrat

end

end DistinctDistances.SparseCones.MOLiftAux
