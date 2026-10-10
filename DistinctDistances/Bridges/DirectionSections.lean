import DistinctDistances.Bridges.AmbientHilbert
import DistinctDistances.TrackA.Intersections
import DistinctDistances.TrackA.ProjectiveChartSupport
import DistinctDistances.TrackA.ProjectiveCutFamilySupport
import DistinctDistances.TrackE.Directional
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
Direction sections for track E's projective requests.

An irreducible projective variety has positive degree and dimension below the
number of coordinates. A zero-dimensional one is a single point. A proper
linear cut has irreducible components of dimension one less, of total degree
at most the original degree, and those components cover the cut.
-/

namespace DistinctDistances.Bridges

noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

def linearForm (c : Point n) : Poly n :=
  ∑ i : Fin n, MvPolynomial.C (c i) * MvPolynomial.X i

theorem linearForm_homogeneous (c : Point n) : (linearForm c).IsHomogeneous 1 := by
  unfold linearForm
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact (MvPolynomial.isHomogeneous_C (Fin n) (c i)).mul (MvPolynomial.isHomogeneous_X ℂ i)

theorem eval_linearForm (c x : Point n) :
    MvPolynomial.eval x (linearForm c) = ∑ i, c i * x i := by
  unfold linearForm
  rw [← MvPolynomial.aeval_eq_eval, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [map_mul, MvPolynomial.aeval_X]

theorem linearMap_eq_sum (φ : Point n →ₗ[ℂ] ℂ) (x : Point n) :
    φ x = ∑ i, x i * φ (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Point n) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    φ x = φ (∑ i, x i • (Pi.single i 1 : Point n)) := congrArg φ hx
    _ = ∑ i, φ (x i • (Pi.single i 1 : Point n)) := by rw [map_sum]
    _ = ∑ i, x i * φ (Pi.single i 1) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul, smul_eq_mul]

def rayAlgHom (v : Point n) : Poly n →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X)

def rayVariety (v : Point n) : AffineVariety n where
  ideal := RingHom.ker (rayAlgHom v)
  isRadical := (RingHom.ker_isPrime (rayAlgHom v)).isRadical

theorem rayVariety_irreducible (v : Point n) : (rayVariety v).IsIrreducible :=
  RingHom.ker_isPrime (rayAlgHom v)

theorem rayAlgHom_linearForm (v c : Point n) :
    rayAlgHom v (linearForm c) = Polynomial.C (∑ i, c i * v i) * Polynomial.X := by
  calc
    rayAlgHom v (linearForm c)
        = ∑ i, rayAlgHom v (MvPolynomial.C (c i) * MvPolynomial.X i) := by
          simp only [linearForm, map_sum]
    _ = ∑ i, Polynomial.C (c i) * (Polynomial.C (v i) * Polynomial.X) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp only [rayAlgHom, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
            Polynomial.algebraMap_eq]
    _ = ∑ i, Polynomial.C (c i * v i) * Polynomial.X := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [← mul_assoc, ← Polynomial.C_mul]
    _ = (∑ i, Polynomial.C (c i * v i)) * Polynomial.X := by
          rw [← Finset.sum_mul]
    _ = Polynomial.C (∑ i, c i * v i) * Polynomial.X := by
          rw [← map_sum (Polynomial.C)]

theorem ray_eval (v : Point n) (c : ℂ) (f : Poly n) :
    MvPolynomial.aeval (c • v) f = Polynomial.eval c (rayAlgHom v f) := by
  refine MvPolynomial.hom_eq_hom (MvPolynomial.aeval (c • v)).toRingHom
    ((Polynomial.evalRingHom c).comp (rayAlgHom v).toRingHom) ?_ ?_ f
  · ext a
    simp [rayAlgHom]
  · intro i
    rw [RingHom.comp_apply]
    change MvPolynomial.aeval (c • v) (MvPolynomial.X i) =
      Polynomial.eval c (rayAlgHom v (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X, rayAlgHom, MvPolynomial.aeval_X, Pi.smul_apply, smul_eq_mul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring

theorem rayVariety_points (v : Point n) :
    (rayVariety v).points = {x | ∃ c : ℂ, x = c • v} := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    have hspan : x ∉ Submodule.span ℂ {v} := by
      intro hxspan
      apply hnot
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxspan
      exact ⟨c, hc.symm⟩
    obtain ⟨φ, hφx, hmap⟩ :=
      (Submodule.span ℂ {v}).exists_dual_map_eq_bot_of_notMem hspan inferInstance
    have hvanish : ∀ y ∈ Submodule.span ℂ {v}, φ y = 0 := by
      intro y hy
      have hm : φ y ∈ (Submodule.span ℂ {v}).map φ :=
        Submodule.mem_map.mpr ⟨y, hy, rfl⟩
      simpa [hmap] using hm
    let c : Point n := fun i => φ (Pi.single i 1)
    have hker : linearForm c ∈ RingHom.ker (rayAlgHom v) := by
      rw [RingHom.mem_ker, rayAlgHom_linearForm]
      have hφv : φ v = 0 := hvanish v (Submodule.subset_span (Set.mem_singleton v))
      have hcoeff : ∑ i, c i * v i = 0 := by
        have hswap : ∑ i, c i * v i = ∑ i, v i * c i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [mul_comm]
        rw [hswap]
        simpa [c] using (linearMap_eq_sum φ v).symm.trans hφv
      rw [hcoeff, map_zero, zero_mul]
    have hx0 : MvPolynomial.aeval x (linearForm c) = 0 := hx _ hker
    rw [MvPolynomial.aeval_eq_eval, eval_linearForm] at hx0
    have hxφ : φ x = ∑ i, x i * c i := linearMap_eq_sum φ x
    have : φ x = 0 := by
      rw [hxφ]
      simpa [mul_comm] using hx0
    exact hφx this
  · rintro ⟨c, rfl⟩
    intro f hf
    rw [ray_eval]
    have hf0 : rayAlgHom v f = 0 := by
      simpa [rayVariety] using hf
    simp [hf0]

theorem rayVariety_dimension {v : Point n} (hv : v ≠ 0) : (rayVariety v).dimension = 1 := by
  let I := (rayVariety v).ideal
  have hI : I = RingHom.ker (rayAlgHom v) := rfl
  have : I.IsPrime := by
    rw [hI]
    exact RingHom.ker_isPrime (rayAlgHom v)
  have htrdeg : Algebra.trdeg ℂ (Poly n ⧸ I) ≤ 1 := by
    calc
      Algebra.trdeg ℂ (Poly n ⧸ I) ≤ Algebra.trdeg ℂ (Polynomial ℂ) := by
        rw [hI]
        exact trdeg_le_of_injective
          (Ideal.kerLiftAlg (rayAlgHom v))
          (Ideal.kerLiftAlg_injective (rayAlgHom v))
      _ = 1 := Polynomial.trdeg_of_isDomain
  have hdim := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg I
    (OAI.QuarticPowerFree.coordinateHilbert I)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually I)
  have hle : (rayVariety v).dimension ≤ 1 := by
    have hcard : ((rayVariety v).dimension : Cardinal) ≤ 1 := by
      change ((OAI.QuarticPowerFree.coordinateHilbert I).natDegree : Cardinal) ≤ 1
      rw [hdim]
      exact htrdeg
    exact_mod_cast hcard
  have hne : (rayVariety v).dimension ≠ 0 := by
    intro hdim0
    obtain ⟨x, hx, _⟩ := TrackA.zeroDim_irreducible_data (rayVariety v)
      (rayVariety_irreducible v) hdim0
    have hzero : (0 : Point n) ∈ (rayVariety v).points := by
      rw [rayVariety_points]
      exact ⟨0, by simp⟩
    have hvmem : v ∈ (rayVariety v).points := by
      rw [rayVariety_points]
      exact ⟨1, by simp⟩
    rw [hx] at hzero hvmem
    have h0x : (0 : Point n) = x := Set.mem_singleton_iff.mp hzero
    have hvx : v = x := Set.mem_singleton_iff.mp hvmem
    exact hv (h0x.trans hvx.symm).symm
  omega

private theorem irreducible_dimension_mono (V W : AffineVariety n)
    (hV : V.IsIrreducible) (hW : W.IsIrreducible) (hVW : V.Subvariety W) :
    V.dimension ≤ W.dimension := by
  have : V.ideal.IsPrime := hV
  have : W.ideal.IsPrime := hW
  exact OAI.QuarticPowerFree.affineDimension_antitone W.ideal V.ideal hVW

private theorem irreducible_subvariety_eq (V W : AffineVariety n)
    (hV : V.IsIrreducible) (hW : W.IsIrreducible) (hVW : V.Subvariety W)
    (hpos : 0 < W.dimension) (hdim : V.dimension = W.dimension) : V = W := by
  have : V.ideal.IsPrime := hV
  by_contra hne
  have hstrict : W.ideal < V.ideal := lt_of_le_of_ne hVW (by
    intro heq
    exact hne (AffineVariety.ext heq.symm))
  obtain ⟨f, hfV, hfW⟩ := SetLike.exists_of_lt hstrict
  have hcut : W.ideal ⊔ Ideal.span {f} ≤ V.ideal := by
    apply sup_le hVW
    apply Ideal.span_le.mpr
    intro a ha
    have heq : a = f := Set.mem_singleton_iff.mp ha
    change a ∈ V.ideal
    rw [heq]
    exact hfV
  obtain ⟨J, hJ, hJV⟩ := Ideal.exists_minimalPrimes_le hcut
  let Z : AffineVariety n := ⟨J, hJ.isPrime.isRadical⟩
  have hcomp : Z.IsComponentOf (W.ideal ⊔ Ideal.span {f}) := hJ
  have hZd : Z.dimension = W.dimension - 1 :=
    TrackA.fa_bezout_proper_dimension W Z hW f hfW hcomp (W.dimension - 1) (by omega)
  have hle : V.dimension ≤ Z.dimension :=
    irreducible_dimension_mono V Z hV hJ.isPrime hJV
  omega

theorem projective_singleton_locus (V : ProjectiveVariety n) :
    ProjectiveFamily.locus {V} = V := by
  apply ProjectiveVariety.ext
  have hset : (⋃ W ∈ ({V} : ProjectiveFamily.Family n), W.points) = V.points := by
    ext z
    simp
  change ProjectiveVariety.vanishingIdeal
    (⋃ W ∈ ({V} : ProjectiveFamily.Family n), W.points) = V.ideal
  rw [hset]
  exact V.vanishingIdeal_points

theorem projective_zero_dim_singleton (Y : ProjectiveVariety n) (hY : Y.IsIrreducible)
    (hdim : Y.dimension = 0) : ∃ p : ProjectivePoint n, Y.points = {p} := by
  obtain ⟨p, hp⟩ := ProjectiveFamily.irreducible_points_nonempty Y hY
  let R := rayVariety p.rep
  have hRne : p.rep ≠ 0 := p.rep_nonzero
  have hRdim : R.dimension = 1 := rayVariety_dimension hRne
  have hcone : Y.affineCone.dimension = 1 := by
    rw [Y.dimension_cone ⟨p, hp⟩, hdim]
  have hsub : R.points ⊆ Y.affineCone.points := by
    intro x hx
    rw [rayVariety_points] at hx
    obtain ⟨c, rfl⟩ := hx
    exact TrackA.cone_smul_mem Y p.rep
      ((Y.mem_points_mk_iff p.rep p.rep_nonzero).1 (by simpa using hp)) c
  have hRsub : R.Subvariety Y.affineCone :=
    (AffineVariety.subvariety_iff_points_subset R Y.affineCone).2 hsub
  have heq : R = Y.affineCone :=
    irreducible_subvariety_eq R Y.affineCone (rayVariety_irreducible p.rep) hY hRsub
      (by rw [hcone]; exact Nat.one_pos) (hRdim.trans hcone.symm)
  refine ⟨p, ?_⟩
  ext q
  constructor
  · intro hq
    have hqrep : q.rep ∈ Y.affineCone.points :=
      (Y.mem_points_mk_iff q.rep q.rep_nonzero).1 (by simpa using hq)
    rw [← heq, rayVariety_points] at hqrep
    obtain ⟨c, hc⟩ := hqrep
    have hc0 : c ≠ 0 := by
      intro hz
      apply q.rep_nonzero
      simp [hc, hz]
    rw [← Projectivization.mk_rep q, ← Projectivization.mk_rep p]
    exact (Projectivization.mk_eq_mk_iff' ℂ q.rep p.rep q.rep_nonzero p.rep_nonzero).2
      ⟨c, hc.symm⟩
  · intro hq
    have hq' : q = p := Set.mem_singleton_iff.mp hq
    simpa [hq'] using hp

/-- Components of one proper homogeneous linear cut, with the degree budget of
`FA.bezout` and set-theoretic coverage of the cut. -/
theorem projective_proper_linear_section (Y : ProjectiveVariety n) (hY : Y.IsIrreducible)
    (m : ℕ) (hm : Y.dimension = m + 1) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hnot : ℓ ∉ Y.ideal) :
    ∃ F : ProjectiveFamily.Family n,
      (∀ V ∈ F, V.IsIrreducible ∧ V.dimension = m ∧
        V.ideal ∈ (Y.ideal ⊔ Ideal.span {ℓ}).minimalPrimes) ∧
      ProjectiveFamily.degree F ≤ Y.degree ∧
      ∀ z : ProjectivePoint n, z ∈ Y.points → MvPolynomial.eval z.rep ℓ = 0 →
        ∃ V ∈ F, z ∈ V.points := by
  let F0 : ProjectiveFamily.Family n := {Y}
  have hlocus : ProjectiveFamily.locus F0 = Y := projective_singleton_locus Y
  have hpure : ProjectiveFamily.IsPure F0 (m + 1) := by
    intro V hV
    have hV' : V = Y := Finset.mem_singleton.mp hV
    subst hV'
    exact ⟨hY, hm⟩
  have havoid : ∀ V ∈ F0, ℓ ∉ V.ideal := by
    intro V hV
    have hV' : V = Y := Finset.mem_singleton.mp hV
    simpa [hV'] using hnot
  let J := Y.ideal ⊔ Ideal.span {ℓ}
  have hspan : (Ideal.span {ℓ}).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
    apply Ideal.homogeneous_span
    rintro f (rfl : f = ℓ)
    exact ⟨1, hℓ⟩
  have hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) :=
    Y.isHomogeneous.sup hspan
  let Qs := {Q : Ideal (Poly n) // Q ∈ J.minimalPrimes}
  let : Fintype Qs := (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n) J).fintype
  have hJeq : (ProjectiveFamily.locus F0).ideal ⊔ Ideal.span {ℓ} = J := by
    rw [hlocus]
  have hAff (Q : Qs) : OAI.QuarticPowerFree.affineDimension Q.val = m + 1 := by
    have hmem : Q.val ∈ ((ProjectiveFamily.locus F0).ideal ⊔ Ideal.span {ℓ}).minimalPrimes := by
      simpa [hJeq] using Q.property
    exact TrackA.projective_linear_cut_minimal_prime_dimension F0 m hpure ℓ havoid
      Q.val hmem
  let φ : Qs → ProjectiveVariety n := fun Q =>
    TrackA.projectiveVarietyOfHomogeneousPrime Q.val Q.property.isPrime
      (TrackA.homogeneous_minimal_prime J Q.val hJ Q.property)
      (TrackA.prime_coordinate_not_mem_of_positive_dimension Q.val Q.property.isPrime
        (by rw [hAff Q]; omega))
  let F := Finset.univ.image φ
  have hmemF (Q : Qs) : φ Q ∈ F := Finset.mem_image.mpr ⟨Q, Finset.mem_univ _, rfl⟩
  have hF : ∀ V ∈ F, V.IsIrreducible ∧ V.dimension = m ∧
      V.ideal ∈ J.minimalPrimes := by
    intro V hV
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hV
    refine ⟨Q.property.isPrime, ?_, Q.property⟩
    have hne := ProjectiveFamily.irreducible_points_nonempty (φ Q) Q.property.isPrime
    have hcone := (φ Q).dimension_cone hne
    change OAI.QuarticPowerFree.affineDimension Q.val = (φ Q).dimension + 1 at hcone
    rw [hAff Q] at hcone
    omega
  have hdegree : ProjectiveFamily.degree F ≤ Y.degree := by
    have hcut := TrackA.fa_bezout_projective_cut Y hY ℓ 1 hℓ hnot m hm F (by
      intro V hV
      exact (hF V hV).2.2)
    calc
      ProjectiveFamily.degree F ≤ (1 : ℚ) * Y.degree := hcut.2
      _ = Y.degree := one_mul _
  have hcover : ∀ z : ProjectivePoint n, z ∈ Y.points → MvPolynomial.eval z.rep ℓ = 0 →
      ∃ V ∈ F, z ∈ V.points := by
    intro z hzY heval
    have hzcone : z.rep ∈ Y.affineCone.points :=
      (Y.mem_points_mk_iff z.rep z.rep_nonzero).1 (by simpa using hzY)
    let P := MvPolynomial.vanishingIdeal ℂ ({z.rep} : Set (Point n))
    have hYP : Y.ideal ≤ P := by
      intro g hg
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff z.rep g).2 (hzcone g hg)
    have hℓP : Ideal.span {ℓ} ≤ P := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff z.rep ℓ).2 <| by
        rw [MvPolynomial.aeval_eq_eval]
        exact heval
    have hJP : J ≤ P := sup_le hYP hℓP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hJP
    let c : Qs := ⟨Q, hQ⟩
    refine ⟨φ c, hmemF c, ?_⟩
    rw [← Projectivization.mk_rep z, ProjectiveVariety.mem_points_mk_iff]
    intro f hf
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff z.rep f).1 (hQP hf)
  exact ⟨F, hF, hdegree, hcover⟩

theorem direction_variety_basics (d : ℕ) :
    ∀ Y : ProjectiveVariety d, Y.IsIrreducible →
      1 ≤ (Y.degree : ℝ) ∧ Y.dimension < d := by
  intro Y hY
  constructor
  · have hdeg : (1 : ℚ) ≤ Y.degree := by
      rw [← Y.degree_cone]
      exact Y.affineCone.one_le_degree hY.ne_top
    exact_mod_cast hdeg
  · have hne := ProjectiveFamily.irreducible_points_nonempty Y hY
    have hcone := Y.dimension_cone hne
    have hle := affine_dimension_le Y.affineCone
    omega

theorem zero_dim_direction_locus (d : ℕ) :
    ∀ Y : ProjectiveVariety d, Y.IsIrreducible → Y.dimension = 0 →
      ∃ F : Finset (ProjectivePoint d), Y.points ⊆ (F : Set (ProjectivePoint d)) ∧
        (F.card : ℝ) ≤ (Y.degree : ℝ) := by
  intro Y hY hdim
  obtain ⟨p, hp⟩ := projective_zero_dim_singleton Y hY hdim
  refine ⟨{p}, ?_, ?_⟩
  · rw [hp, Finset.coe_singleton]
  · have hdeg : (1 : ℚ) ≤ Y.degree := by
      rw [← Y.degree_cone]
      exact Y.affineCone.one_le_degree hY.ne_top
    have hcard : ({p} : Finset (ProjectivePoint d)).card = 1 := by simp
    rw [hcard]
    exact_mod_cast hdeg

theorem sum_cplx_mul {d : ℕ} (a b : RPoint d) :
    ∑ i, cplx a i * cplx b i = ((inner ℝ a b : ℝ) : ℂ) := by
  simp only [cplx, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem direction_hyperplane_sections (d : ℕ) :
    ∀ Y : ProjectiveVariety d, Y.IsIrreducible → 1 ≤ Y.dimension →
      ∀ n : RPoint d, (∃ v ∈ Y.affineCone.points, ∑ i, v i * cplx n i ≠ 0) →
        ∃ F : ProjectiveFamily.Family d,
          (∀ V ∈ F, V.IsIrreducible ∧ V.dimension + 1 = Y.dimension) ∧
          (∑ V ∈ F, (V.degree : ℝ)) ≤ (Y.degree : ℝ) ∧
          ∀ p q : RPoint d, DirMem Y p q → inner ℝ (q - p) n = 0 →
            ∃ V ∈ F, DirMem V p q := by
  intro Y hY hdim n hv
  let ℓ : Poly d := linearForm (cplx n)
  have hℓ : ℓ.IsHomogeneous 1 := linearForm_homogeneous (cplx n)
  have hnot : ℓ ∉ Y.ideal := by
    intro hℓY
    obtain ⟨v, hvY, hvn⟩ := hv
    have hzero : MvPolynomial.aeval v ℓ = 0 := hvY ℓ hℓY
    rw [MvPolynomial.aeval_eq_eval, eval_linearForm] at hzero
    apply hvn
    simpa [mul_comm] using hzero
  have hm : Y.dimension = (Y.dimension - 1) + 1 := by omega
  obtain ⟨F, hF, hdegree, hcover⟩ :=
    projective_proper_linear_section Y hY (Y.dimension - 1) hm ℓ hℓ hnot
  refine ⟨F, ?_, ?_, ?_⟩
  · intro V hV
    rcases hF V hV with ⟨hirr, hVdim, _⟩
    exact ⟨hirr, by omega⟩
  · have hsum : (∑ V ∈ F, (V.degree : ℝ)) = ((ProjectiveFamily.degree F : ℚ) : ℝ) := by
      simp [ProjectiveFamily.degree]
    rw [hsum]
    exact_mod_cast hdegree
  · intro p q hdir hinner
    rcases hdir with ⟨hq, hz⟩
    let z := radialProjection (cplx p) (cplx q) hq
    have hzY : z ∈ Y.points := hz
    have hdisp : cplx q - cplx p = cplx (q - p) := by
      ext i
      simp [cplx]
    have heval0 : MvPolynomial.eval (cplx q - cplx p) ℓ = 0 := by
      rw [eval_linearForm, hdisp, sum_cplx_mul, real_inner_comm]
      exact congrArg (fun t : ℝ => (t : ℂ)) hinner
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (cplx q - cplx p)
      (sub_ne_zero.mpr hq)
    have hunit : z.rep = a • (cplx q - cplx p) := by
      simpa [z, radialProjection] using ha.symm
    have hrep : z.rep = (a : ℂ) • (cplx q - cplx p) := by
      rw [hunit, Units.smul_def]
    have hevalRep : MvPolynomial.eval z.rep ℓ = 0 := by
      rw [hrep, homogeneous_eval_smul ℓ hℓ (a : ℂ) (cplx q - cplx p), heval0]
      simp
    obtain ⟨V, hV, hzV⟩ := hcover z hzY hevalRep
    exact ⟨V, hV, ⟨hq, by simpa [z] using hzV⟩⟩

theorem curve_linear_sections (d : ℕ) :
    ∀ Y : ProjectiveVariety d, Y.IsIrreducible → Y.dimension = 1 →
      ∀ W : Submodule ℂ (Point d), Module.finrank ℂ W ≤ 3 →
        (∀ z ∈ Y.points, z.submodule ≤ W) ∨
        ∃ F : Finset (ProjectivePoint d), (F.card : ℝ) ≤ (Y.degree : ℝ) ∧
          ∀ z ∈ Y.points, z.submodule ≤ W → z ∈ F := by
  intro Y hY hdim W _hW
  by_cases hcontain : ∀ z ∈ Y.points, z.submodule ≤ W
  · exact Or.inl hcontain
  · right
    push Not at hcontain
    obtain ⟨z0, hz0Y, hz0W⟩ := hcontain
    have hrep : z0.rep ∉ W := by
      intro hmem
      apply hz0W
      rw [Projectivization.submodule_eq]
      exact (Submodule.span_singleton_le_iff_mem z0.rep W).2 hmem
    obtain ⟨φ, hφ, hmap⟩ := W.exists_dual_map_eq_bot_of_notMem hrep inferInstance
    have hvanish : ∀ u ∈ W, φ u = 0 := by
      intro u hu
      have hm : φ u ∈ W.map φ := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
      simpa [hmap] using hm
    let c : Point d := fun i => φ (Pi.single i 1)
    let ℓ : Poly d := linearForm c
    have hℓ : ℓ.IsHomogeneous 1 := linearForm_homogeneous c
    have hnot : ℓ ∉ Y.ideal := by
      intro hℓY
      have hzero : MvPolynomial.aeval z0.rep ℓ = 0 :=
        ((Y.mem_points_mk_iff z0.rep z0.rep_nonzero).1 (by simpa using hz0Y)) ℓ hℓY
      rw [MvPolynomial.aeval_eq_eval, eval_linearForm] at hzero
      have hφ0 : φ z0.rep = 0 := by
        rw [linearMap_eq_sum]
        simpa [c, mul_comm] using hzero
      exact hφ hφ0
    have hm : Y.dimension = 0 + 1 := by simp [hdim]
    obtain ⟨G, hG, hdegree, hcover⟩ :=
      projective_proper_linear_section Y hY 0 hm ℓ hℓ hnot
    let S := {V : ProjectiveVariety d // V ∈ G}
    let pt : S → ProjectivePoint d := fun V =>
      Classical.choose (projective_zero_dim_singleton V.val (hG V.val V.property).1
        (hG V.val V.property).2.1)
    have hpt (V : S) : V.val.points = {pt V} :=
      Classical.choose_spec (projective_zero_dim_singleton V.val (hG V.val V.property).1
        (hG V.val V.property).2.1)
    let F : Finset (ProjectivePoint d) := Finset.univ.image pt
    have hcardNat : F.card ≤ G.card := by
      have hle : F.card ≤ (Finset.univ : Finset S).card := by
        simpa [F] using Finset.card_image_le (s := (Finset.univ : Finset S)) (f := pt)
      have hS : (Finset.univ : Finset S).card = G.card := by
        rw [Finset.card_univ]
        exact Fintype.card_coe G
      exact hle.trans_eq hS
    have hGcard : (G.card : ℚ) ≤ ProjectiveFamily.degree G := by
      unfold ProjectiveFamily.degree
      calc
        (G.card : ℚ) = ∑ V ∈ G, (1 : ℚ) := by simp
        _ ≤ ∑ V ∈ G, V.degree := by
          apply Finset.sum_le_sum
          intro V hV
          rw [← (V.degree_cone)]
          exact V.affineCone.one_le_degree (hG V hV).1.ne_top
    have hcard : (F.card : ℝ) ≤ (Y.degree : ℝ) := by
      have hrat : (F.card : ℚ) ≤ Y.degree := by
        calc
          (F.card : ℚ) ≤ (G.card : ℚ) := by exact_mod_cast hcardNat
          _ ≤ ProjectiveFamily.degree G := hGcard
          _ ≤ Y.degree := hdegree
      exact_mod_cast hrat
    refine ⟨F, hcard, ?_⟩
    intro z hzY hzW
    have hrepW : z.rep ∈ W := by
      rw [Projectivization.submodule_eq] at hzW
      exact (Submodule.span_singleton_le_iff_mem z.rep W).1 hzW
    have heval : MvPolynomial.eval z.rep ℓ = 0 := by
      rw [eval_linearForm]
      have hφ0 : φ z.rep = 0 := hvanish z.rep hrepW
      rw [linearMap_eq_sum] at hφ0
      simpa [c, ℓ, mul_comm] using hφ0
    obtain ⟨V, hV, hzV⟩ := hcover z hzY heval
    have hzpt : z = pt ⟨V, hV⟩ := by
      have : z ∈ ({pt ⟨V, hV⟩} : Set (ProjectivePoint d)) := by
        rw [← hpt ⟨V, hV⟩]
        exact hzV
      exact Set.mem_singleton_iff.mp this
    exact Finset.mem_image.mpr ⟨⟨V, hV⟩, Finset.mem_univ _, hzpt.symm⟩

end
end DistinctDistances.Bridges
