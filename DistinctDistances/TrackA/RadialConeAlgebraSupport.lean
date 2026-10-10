import DistinctDistances.TrackA.AlgebraicFieldFiberSupport
import DistinctDistances.Foundations.GenericFiber

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

def radialCoordinate {n : ℕ} (p : Point n) (i : Fin n) : Poly n :=
  MvPolynomial.X i - MvPolynomial.C (p i)

theorem radialCoordinate_eval {n : ℕ} (p x : Point n) :
    (fun i => MvPolynomial.aeval x (radialCoordinate p i)) = x - p := by
  funext i
  simp [radialCoordinate]

/-- The literal radial cone pullback retains the original source quotient
and one scalar variable, sending target coordinates to t(x-p). -/
def radialConePullback {n : ℕ} (V : AffineVariety n) (p : Point n) :
    Poly n →ₐ[ℂ] Polynomial (Poly n ⧸ V.ideal) :=
  GenericFiber.conePullback V.ideal (radialCoordinate p)

theorem radialConePullback_X {n : ℕ} (V : AffineVariety n) (p : Point n) (i : Fin n) :
    radialConePullback V p (MvPolynomial.X i) =
      Polynomial.X * Polynomial.C (Ideal.Quotient.mk V.ideal (radialCoordinate p i)) :=
  GenericFiber.conePullback_X V.ideal (radialCoordinate p) i

/-- A kernel element vanishes on every literal nonzero representative of
the radial image, including points outside a chosen source chart. -/
theorem radialCone_ker_le_image_ideal {n : ℕ} (V : AffineVariety n) (p : Point n) :
    RingHom.ker (radialConePullback V p) ≤ (radialImage p V).ideal := by
  intro f hf
  rw [RingHom.mem_ker] at hf
  change GenericFiber.conePullback V.ideal (radialCoordinate p) f = 0 at hf
  rw [GenericFiber.conePullback_eq_map] at hf
  change f ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives
    {z | ∃ x ∈ V.points, ∃ hx : x ≠ p, radialProjection p x hx = z})
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro w ⟨hw, x, hx, hxne, he⟩
  have hcoeff (k : ℕ) : (GenericFiber.scalarPullback (radialCoordinate p) f).coeff k ∈ V.ideal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg (fun Q : Polynomial (Poly n ⧸ V.ideal) => Q.coeff k) hf
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using h
  have hQ : (GenericFiber.scalarPullback (radialCoordinate p) f).map
      (MvPolynomial.aeval x).toRingHom = 0 := by
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact hx _ (hcoeff k)
  have he' : Projectivization.mk ℂ w hw =
      Projectivization.mk ℂ (x-p) (sub_ne_zero.mpr hxne) := he.symm
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he'
  have h := congrArg (Polynomial.eval t) hQ
  rw [GenericFiber.eval_scalarPullback, radialCoordinate_eval] at h
  simpa only [Polynomial.eval_zero, ← ht] using h

/-- The original radial image ideal is exactly the kernel of its scalar
cone pullback. A source principal open proves the difficult inclusion. -/
theorem radialImage_ideal_eq_cone_ker {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (p : Point n) (hactual : ∃ x ∈ V.points, x ≠ p) :
    (radialImage p V).ideal = RingHom.ker (radialConePullback V p) := by
  obtain ⟨x0, hx0, hx0ne⟩ := hactual
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x0 i ≠ p i := by
    by_contra h
    push_neg at h
    exact hx0ne (funext h)
  let g := radialCoordinate p i
  have hg : g ∉ V.ideal := by
    intro h
    have hz := hx0 g h
    simp only [g, radialCoordinate, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply] at hz
    exact hi (sub_eq_zero.mp hz)
  have hF (x : Point n) (hx : x ∈ V.points) (hxg : MvPolynomial.aeval x g ≠ 0) :
      (fun j => MvPolynomial.aeval x (radialCoordinate p j)) ≠ 0 := by
    intro hz
    exact hxg (congrFun hz i)
  have hker := GenericFiber.image_vanishingIdeal_eq_ker V hV g hg (radialCoordinate p) hF
  apply le_antisymm
  · intro f hf
    change f ∈ RingHom.ker (GenericFiber.conePullback V.ideal (radialCoordinate p))
    rw [← hker]
    change f ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives (GenericFiber.image V g (radialCoordinate p)))
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro w ⟨hw, x, hx, hxg, hcoords, he⟩
    have hxne : x ≠ p := by
      intro heq
      have hz : (fun j => MvPolynomial.aeval x (radialCoordinate p j)) = 0 := by
        rw [radialCoordinate_eval, heq, sub_self]
      exact hcoords hz
    change f ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives
      {z | ∃ x ∈ V.points, ∃ hx : x ≠ p, radialProjection p x hx = z}) at hf
    apply hf w
    refine ⟨hw, x, hx, hxne, ?_⟩
    simpa only [radialProjection, radialCoordinate_eval] using he
  · exact radialCone_ker_le_image_ideal V p

abbrev RadialConeBase {n : ℕ} (V : AffineVariety n) (p : Point n) :=
  Poly n ⧸ RingHom.ker (radialConePullback V p)

def radialConeInclusion {n : ℕ} (V : AffineVariety n) (p : Point n) :
    RadialConeBase V p →ₐ[ℂ] Polynomial (Poly n ⧸ V.ideal) :=
  Ideal.kerLiftAlg (radialConePullback V p)

theorem radialConeInclusion_injective {n : ℕ} (V : AffineVariety n) (p : Point n) :
    Function.Injective (radialConeInclusion V p) :=
  Ideal.kerLiftAlg_injective (radialConePullback V p)

@[instance_reducible]
def radialConeAlgebra {n : ℕ} (V : AffineVariety n) (p : Point n) :
    Algebra (RadialConeBase V p) (Polynomial (Poly n ⧸ V.ideal)) := by
  with_unfolding_all
    exact RingHom.toAlgebra (R := RadialConeBase V p)
      (S := Polynomial (Poly n ⧸ V.ideal)) (radialConeInclusion V p).toRingHom

/-- The actual dimension-preserving radial cone inclusion is algebraic;
its source and target use the original coordinate ideals and scalar map. -/
theorem radialConeInclusion_algebraic {n l : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension = l) (p : Point n)
    (hactual : ∃ x ∈ V.points, x ≠ p) (himage : (radialImage p V).dimension = l) :
    letI := radialConeAlgebra V p
    Algebra.IsAlgebraic (RadialConeBase V p) (Polynomial (Poly n ⧸ V.ideal)) := by
  letI : V.ideal.IsPrime := hV
  let R := RadialConeBase V p
  let B := Polynomial (Poly n ⧸ V.ideal)
  letI : (RingHom.ker (radialConePullback V p)).IsPrime := RingHom.ker_isPrime _
  letI := radialConeAlgebra V p
  letI : SMul ℂ R := (inferInstance : Algebra ℂ R).toSMul
  haveI : IsScalarTower ℂ R B := by
    refine IsScalarTower.of_algebraMap_eq (R := ℂ) (S := R) (A := B) ?_
    intro c
    change algebraMap ℂ B c = radialConeInclusion V p (algebraMap ℂ R c)
    exact (radialConeInclusion V p).commutes c |>.symm
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr
    (radialConeInclusion_injective V p)
  obtain ⟨x0, hx0, hx0ne⟩ := hactual
  have hpoints : (radialImage p V).points.Nonempty :=
    ⟨radialProjection p x0 hx0ne, ProjectiveVariety.subset_closure _ ⟨x0, hx0, hx0ne, rfl⟩⟩
  have hR : Algebra.trdeg ℂ R = ((l+1 : ℕ) : Cardinal) := by
    rw [← GenericFiber.affineDimension_eq_trdeg, ← radialImage_ideal_eq_cone_ker V hV p
      ⟨x0, hx0, hx0ne⟩]
    change ((radialImage p V).affineCone.dimension : Cardinal) = _
    rw [ProjectiveVariety.dimension_cone _ hpoints, himage]
  have hB : Algebra.trdeg ℂ B = ((l+1 : ℕ) : Cardinal) := by
    rw [GenericFiber.trdeg_polynomial_quotient]
    change (V.dimension : Cardinal) + 1 = _
    rw [hd, Nat.cast_add, Nat.cast_one]
  exact algebraic_of_equal_finite_trdeg ℂ R B (l+1) hR hB

/-- The actual original radial cone map has positive constant field Hom
fibers above a nonzero original target-cone polynomial class. -/
theorem radialCone_generic_field_hom_count {n l : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension = l) (p : Point n)
    (hactual : ∃ x ∈ V.points, x ≠ p) (himage : (radialImage p V).dimension = l) :
    letI := radialConeAlgebra V p
    ∃ g : RadialConeBase V p, g ≠ 0 ∧ ∃ r : ℕ, 0 < r ∧
      ∀ (K : Type*) [Field K] [Algebra (RadialConeBase V p) K] [IsAlgClosed K],
        algebraMap (RadialConeBase V p) K g ≠ 0 →
          Finite (Polynomial (Poly n ⧸ V.ideal) →ₐ[RadialConeBase V p] K) ∧
          Nat.card (Polynomial (Poly n ⧸ V.ideal) →ₐ[RadialConeBase V p] K) = r := by
  letI : V.ideal.IsPrime := hV
  let R := RadialConeBase V p
  let B := Polynomial (Poly n ⧸ V.ideal)
  letI : (RingHom.ker (radialConePullback V p)).IsPrime := RingHom.ker_isPrime _
  letI := radialConeAlgebra V p
  letI : SMul ℂ R := (inferInstance : Algebra ℂ R).toSMul
  haveI : IsScalarTower ℂ R B := by
    refine IsScalarTower.of_algebraMap_eq (R := ℂ) (S := R) (A := B) ?_
    intro c
    change algebraMap ℂ B c = radialConeInclusion V p (algebraMap ℂ R c)
    exact (radialConeInclusion V p).commutes c |>.symm
  haveI : Module.IsTorsionFree R B := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    change Function.Injective (radialConeInclusion V p)
    exact radialConeInclusion_injective V p
  haveI : Algebra.FiniteType R B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R B
  haveI : Algebra.IsAlgebraic R B := radialConeInclusion_algebraic V hV hd p hactual himage
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℂ R).injective
  exact algebraic_finiteType_field_hom_fibers R B

/-- A positive-dimensional irreducible source has an actual radial point
away from every center. This discharges the cone construction's premise. -/
theorem radial_actual_of_positive_dimension {n l : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hl : 1 ≤ l) (hd : V.dimension = l) (p : Point n) :
    ∃ x ∈ V.points, x ≠ p := by
  letI : V.ideal.IsPrime := hV
  by_contra h
  push Not at h
  obtain ⟨x0, hx0⟩ := V.points_nonempty_of_isIrreducible hV
  have hp : p ∈ V.points := (h x0 hx0) ▸ hx0
  have hpts : V.points = {p} := by
    ext x
    exact ⟨fun hx => Set.mem_singleton_iff.mpr (h x hx), fun hx =>
      (Set.mem_singleton_iff.mp hx) ▸ hp⟩
  let ev : Poly n →ₐ[ℂ] ℂ := MvPolynomial.aeval p
  have hI : V.ideal = RingHom.ker ev := by
    rw [← V.vanishingIdeal_points, hpts]
    ext f
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, RingHom.mem_ker]
  have hev : Function.Surjective ev := fun c => ⟨MvPolynomial.C c, by simp [ev]⟩
  let e : (Poly n ⧸ RingHom.ker ev) ≃ₐ[ℂ] ℂ := Ideal.quotientKerAlgEquivOfSurjective hev
  have hQ : Algebra.trdeg ℂ (Poly n ⧸ V.ideal) = 0 := by
    rw [hI, e.trdeg_eq, trdeg_eq_zero]
  have hdim : (V.dimension : Cardinal) = 0 := (GenericFiber.affineDimension_eq_trdeg V.ideal).trans hQ
  have hzero : V.dimension = 0 := by exact_mod_cast hdim
  omega

end
end DistinctDistances.TrackA
