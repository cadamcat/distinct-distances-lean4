import DistinctDistances.Foundations.Projective
import DistinctDistances.Foundations.Local

/-!
Linear projections are genuine complex linear maps. Affine images are
defined by contraction of ideals along polynomial pullback, and projective
and radial images by projective Zariski closure. Generic projection degree
is the cardinality of fibers on a nonempty principal open subset of the
reduced image (characteristic zero). No degree-loss identity is included
as a structure field or a projection hypothesis.
-/

namespace DistinctDistances

open scoped BigOperators
noncomputable section

abbrev LinearProjection (n m : ℕ) := Point n →ₗ[ℂ] Point m

def linearCoordinate {n m : ℕ} (φ : LinearProjection n m) (j : Fin m) : Poly n :=
  ∑ i : Fin n, MvPolynomial.C (φ (Pi.single i 1) j) * MvPolynomial.X i

def linearPullback {n m : ℕ} (φ : LinearProjection n m) : Poly m →ₐ[ℂ] Poly n :=
  MvPolynomial.aeval (linearCoordinate φ)

structure AffineProjection (n m : ℕ) where
  linear : LinearProjection n m
  offset : Point m

namespace AffineProjection

variable {n m : ℕ}

private theorem linearCoordinate_eval (ψ : LinearProjection n m) (x : Point n) (j : Fin m) :
    MvPolynomial.aeval x (linearCoordinate ψ j) = ψ x j := by
  have hx : x = ∑ i : Fin n, x i • (Pi.single i (1 : ℂ) : Point n) := by
    simpa using ((Pi.basisFun ℂ (Fin n)).sum_repr x).symm
  have hlin : ψ x j = ∑ i : Fin n, x i * ψ (Pi.single i (1 : ℂ)) j := by
    have h := congrFun (congrArg ψ hx) j
    rw [map_sum] at h
    simpa [map_smul, Pi.smul_apply, smul_eq_mul] using h
  rw [linearCoordinate]
  calc
    MvPolynomial.aeval x
        (∑ i : Fin n, MvPolynomial.C (ψ (Pi.single i 1) j) * MvPolynomial.X i) =
      ∑ i : Fin n, ψ (Pi.single i 1) j * x i := by simp
    _ = ∑ i : Fin n, x i * ψ (Pi.single i 1) j := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ψ x j := hlin.symm

def apply (φ : AffineProjection n m) (x : Point n) : Point m := φ.linear x + φ.offset

def pullback (φ : AffineProjection n m) : Poly m →ₐ[ℂ] Poly n :=
  MvPolynomial.aeval (fun j => linearCoordinate φ.linear j + MvPolynomial.C (φ.offset j))

def image (φ : AffineProjection n m) (V : AffineVariety n) : AffineVariety m :=
  ⟨V.ideal.comap φ.pullback.toRingHom,
    Ideal.IsRadical.comap φ.pullback.toRingHom V.isRadical⟩

def fiber (φ : AffineProjection n m) (V : AffineVariety n) (y : Point m) : Set (Point n) :=
  {x | x ∈ V ∧ φ.apply x = y}

/-- A geometric generic degree, without asserting the difficult projection estimates. -/
def GenericallyFiniteOfDegree (φ : AffineProjection n m) (V : AffineVariety n) (r : ℕ) : Prop :=
  0 < r ∧ ∃ g : Poly m, g ∉ (φ.image V).ideal ∧
    ∀ y ∈ (φ.image V).points, MvPolynomial.aeval y g ≠ 0 →
      (φ.fiber V y).Finite ∧ (φ.fiber V y).ncard = r

theorem eval_pullback (φ : AffineProjection n m) (x : Point n) (f : Poly m) :
    MvPolynomial.aeval x (φ.pullback f) = MvPolynomial.aeval (φ.apply x) f := by
  change MvPolynomial.aeval x
    (MvPolynomial.aeval
      (fun j => linearCoordinate φ.linear j + MvPolynomial.C (φ.offset j)) f) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : Fin m → ℂ => MvPolynomial.aeval g f)
  funext j
  change MvPolynomial.aeval x
    (linearCoordinate φ.linear j + MvPolynomial.C (φ.offset j)) =
      φ.linear x j + φ.offset j
  rw [map_add, linearCoordinate_eval, MvPolynomial.aeval_C]
  simp

theorem image_eq_closure (φ : AffineProjection n m) (V : AffineVariety n) :
    φ.image V = AffineVariety.closure (φ.apply '' V.points) := by
  apply AffineVariety.ext
  change V.ideal.comap φ.pullback.toRingHom =
    MvPolynomial.vanishingIdeal ℂ (φ.apply '' V.points)
  ext f
  rw [Ideal.mem_comap, MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro hf y hy
    have hvan : φ.pullback f ∈ MvPolynomial.vanishingIdeal ℂ V.points := by
      rw [AffineVariety.vanishingIdeal_points]
      exact hf
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← eval_pullback]
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hvan) x hx
  · intro hf
    rw [← AffineVariety.vanishingIdeal_points]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro x hx
    change MvPolynomial.aeval x (φ.pullback f) = 0
    rw [eval_pullback]
    exact hf (φ.apply x) ⟨x, hx, rfl⟩

theorem image_irreducible (φ : AffineProjection n m) (V : AffineVariety n)
    (hV : V.IsIrreducible) : (φ.image V).IsIrreducible := by
  letI : V.ideal.IsPrime := hV
  exact Ideal.IsPrime.comap φ.pullback.toRingHom

end AffineProjection

def projectiveImage {n m : ℕ} (φ : LinearProjection n m) (V : ProjectiveVariety n) :
    ProjectiveVariety m :=
  ProjectiveVariety.closure {p | ∃ v : Point n, ∃ hv : v ≠ 0,
    Projectivization.mk ℂ v hv ∈ V ∧ ∃ hφ : φ v ≠ 0, Projectivization.mk ℂ (φ v) hφ = p}

/-- Radial projection, defined on `x ≠ p`, including singular centers on a carrier. -/
def radialProjection {n : ℕ} (p x : Point n) (hx : x ≠ p) : ProjectivePoint n :=
  Projectivization.mk ℂ (x-p) (sub_ne_zero.mpr hx)

def radialImage {n : ℕ} (p : Point n) (V : AffineVariety n) : ProjectiveVariety n :=
  ProjectiveVariety.closure {z | ∃ x ∈ V.points, ∃ hx : x ≠ p, radialProjection p x hx = z}

def radialFiber {n : ℕ} (p : Point n) (V : AffineVariety n) (z : ProjectivePoint n) :
    Set (Point n) :=
  {x | x ∈ V.points ∧ ∃ hx : x ≠ p, radialProjection p x hx = z}

/-- Principal opens are homogeneous, so their nonvanishing is scale independent. -/
def GenericallyFiniteRadialDegree {n : ℕ} (p : Point n) (V : AffineVariety n) (r : ℕ) : Prop :=
  0 < r ∧ ∃ (g : Poly n) (D : ℕ), g.IsHomogeneous D ∧ g ∉ (radialImage p V).ideal ∧
    ∀ z ∈ (radialImage p V).points, MvPolynomial.aeval z.rep g ≠ 0 →
      (radialFiber p V z).Finite ∧ (radialFiber p V z).ncard = r

private def radialParameter {n : ℕ} (p : Point n) : Poly n →ₐ[ℂ] Polynomial (Poly n) :=
  MvPolynomial.aeval (fun i => Polynomial.X * Polynomial.C
    (MvPolynomial.X i - MvPolynomial.C (p i)))

private theorem radialParameter_eval {n : ℕ} (p x : Point n) (f : Poly n) (c : ℂ) :
    ((radialParameter p f).map (MvPolynomial.aeval x).toRingHom).eval c =
      MvPolynomial.aeval (fun i => c * (x i - p i)) f := by
  let e : Poly n →+* ℂ := (MvPolynomial.aeval x).toRingHom
  let ρ : Polynomial (Poly n) →+* ℂ :=
    (Polynomial.evalRingHom c).comp (Polynomial.mapRingHom e)
  have h : ρ.comp (radialParameter p).toRingHom =
      (MvPolynomial.aeval (fun i => c * (x i - p i))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ, e, radialParameter]
    · intro i
      simp [ρ, e, radialParameter]
  change ρ (radialParameter p f) = _
  exact congrArg (fun F : Poly n →+* ℂ => F f) h

private theorem radialParameter_coeff_eval {n : ℕ} (p x : Point n) (f : Poly n) (k : ℕ) :
    MvPolynomial.aeval x ((radialParameter p f).coeff k) =
      ((radialParameter p f).map (MvPolynomial.aeval x).toRingHom).coeff k := by
  simp [Polynomial.coeff_map]

private theorem radial_not_mem_witness {n : ℕ} (p : Point n) (V : AffineVariety n)
    (f : Poly n) (hf : f ∉ (radialImage p V).ideal) :
    ∃ x ∈ V.points, ∃ hx : x ≠ p, ∃ c : ℂ, c ≠ 0 ∧
      ((radialParameter p f).map (MvPolynomial.aeval x).toRingHom).eval c ≠ 0 := by
  change f ∉ ProjectiveVariety.vanishingIdeal
    {z | ∃ x ∈ V.points, ∃ hx : x ≠ p, radialProjection p x hx = z} at hf
  change f ∉ MvPolynomial.vanishingIdeal ℂ
    (ProjectiveVariety.nonzeroRepresentatives
      {z | ∃ x ∈ V.points, ∃ hx : x ≠ p, radialProjection p x hx = z}) at hf
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hf
  push Not at hf
  obtain ⟨v, hv, hvf⟩ := hf
  obtain ⟨hv0, hpv⟩ := hv
  obtain ⟨x, hxV, hxne, hxz⟩ := hpv
  have hproj : Projectivization.mk ℂ v hv0 =
      Projectivization.mk ℂ (x-p) (sub_ne_zero.mpr hxne) := hxz.symm
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ v (x-p) hv0 (sub_ne_zero.mpr hxne)).mp hproj
  have hc0 : c ≠ 0 := by
    intro hc'
    have hvz : v = 0 := by simpa [hc'] using hc.symm
    exact hv0 hvz
  have hvf' : MvPolynomial.aeval (c • (x-p)) f ≠ 0 := by
    rw [hc]
    exact hvf
  have hargs : c • (x-p) = fun i => c * (x i - p i) := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  refine ⟨x, hxV, hxne, c, hc0, ?_⟩
  rw [hargs] at hvf'
  rw [radialParameter_eval]
  exact hvf'

theorem radialImage_irreducible {n : ℕ} (p : Point n) (V : AffineVariety n)
    (hV : V.IsIrreducible) (hx : ∃ x ∈ V.points, x ≠ p) :
    (radialImage p V).IsIrreducible := by
  classical
  let T : Set (ProjectivePoint n) :=
    {z | ∃ x ∈ V.points, ∃ hx : x ≠ p, radialProjection p x hx = z}
  change (ProjectiveVariety.vanishingIdeal T).IsPrime
  rw [Ideal.isPrime_iff]
  constructor
  · intro htop
    obtain ⟨x, hxV, hxne⟩ := hx
    have hrep0 : x-p ≠ 0 := sub_ne_zero.mpr hxne
    have hrep : x-p ∈ ProjectiveVariety.nonzeroRepresentatives T := by
      refine ⟨hrep0, ?_⟩
      exact ⟨x, hxV, hxne, rfl⟩
    have hone : (1 : Poly n) ∈ ProjectiveVariety.vanishingIdeal T := by
      rw [htop]
      simp
    have hzero := (MvPolynomial.mem_vanishingIdeal_iff.mp hone) (x-p) hrep
    have hbad : (1 : ℂ) = 0 := by simpa using hzero
    exact one_ne_zero hbad
  · intro f g hfg
    by_contra h
    push Not at h
    obtain ⟨hfnot, hgnot⟩ := h
    have hfgvan : f * g ∈ MvPolynomial.vanishingIdeal ℂ
        (ProjectiveVariety.nonzeroRepresentatives T) := hfg
    obtain ⟨xf, hxfV, hxfne, cf, hcf, hfeval⟩ :=
      radial_not_mem_witness p V f hfnot
    obtain ⟨xg, hxgV, hxgne, cg, hcg, hgeval⟩ :=
      radial_not_mem_witness p V g hgnot
    let Qf := (radialParameter p f).map (MvPolynomial.aeval xf).toRingHom
    let Qg := (radialParameter p g).map (MvPolynomial.aeval xg).toRingHom
    have hQfne : Qf ≠ 0 := by
      intro hzero
      have heval : Qf.eval cf = 0 := by simp [hzero]
      exact hfeval heval
    have hQg_ne : Qg ≠ 0 := by
      intro hzero
      have heval : Qg.eval cg = 0 := by simp [hzero]
      exact hgeval heval
    obtain ⟨kf, hkf⟩ : ∃ k, Qf.coeff k ≠ 0 := by
      by_contra hno
      have hcoeff : ∀ k, Qf.coeff k = 0 := by
        intro k
        by_contra hne
        exact hno ⟨k, hne⟩
      have hzero : Qf = 0 := by
        ext k
        exact hcoeff k
      exact hQfne hzero
    obtain ⟨kg, hkg⟩ : ∃ k, Qg.coeff k ≠ 0 := by
      by_contra hno
      have hcoeff : ∀ k, Qg.coeff k = 0 := by
        intro k
        by_contra hne
        exact hno ⟨k, hne⟩
      have hzero : Qg = 0 := by
        ext k
        exact hcoeff k
      exact hQg_ne hzero
    let af := (radialParameter p f).coeff kf
    let ag := (radialParameter p g).coeff kg
    have hafV : af ∉ V.ideal := by
      intro hmem
      have hzero := MvPolynomial.mem_zeroLocus_iff.mp hxfV af hmem
      change MvPolynomial.aeval xf ((radialParameter p f).coeff kf) = 0 at hzero
      have hcoeff : Qf.coeff kf = 0 := by
        rw [← radialParameter_coeff_eval p xf f kf]
        exact hzero
      exact hkf hcoeff
    have hagV : ag ∉ V.ideal := by
      intro hmem
      have hzero := MvPolynomial.mem_zeroLocus_iff.mp hxgV ag hmem
      change MvPolynomial.aeval xg ((radialParameter p g).coeff kg) = 0 at hzero
      have hcoeff : Qg.coeff kg = 0 := by
        rw [← radialParameter_coeff_eval p xg g kg]
        exact hzero
      exact hkg hcoeff
    obtain ⟨w, hwV, hwne⟩ := hx
    obtain ⟨i, hi⟩ : ∃ i : Fin n, w i ≠ p i := by
      by_contra hno
      apply hwne
      funext i
      by_contra hne
      exact hno ⟨i, hne⟩
    let ℓ : Poly n := MvPolynomial.X i - MvPolynomial.C (p i)
    have hℓw : MvPolynomial.aeval w ℓ ≠ 0 := by
      simpa [ℓ] using (sub_ne_zero.mpr hi)
    have hℓV : ℓ ∉ V.ideal := by
      intro hmem
      exact hℓw (MvPolynomial.mem_zeroLocus_iff.mp hwV ℓ hmem)
    have hprodV : af * ag * ℓ ∉ V.ideal := by
      intro hmem
      rcases hV.mem_or_mem hmem with hpair | hℓ
      · rcases hV.mem_or_mem hpair with haf | hag
        · exact hafV haf
        · exact hagV hag
      · exact hℓV hℓ
    have hprodNotVan : af * ag * ℓ ∉ MvPolynomial.vanishingIdeal ℂ V.points := by
      simpa [AffineVariety.vanishingIdeal_points] using hprodV
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hprodNotVan
    push Not at hprodNotVan
    obtain ⟨y, hyV, hyprod⟩ := hprodNotVan
    have hEvalProd : MvPolynomial.aeval y af * MvPolynomial.aeval y ag *
        MvPolynomial.aeval y ℓ ≠ 0 := by
      simpa only [map_mul] using hyprod
    have hafY : MvPolynomial.aeval y af ≠ 0 := by
      intro hy
      apply hEvalProd
      simp [hy]
    have hagY : MvPolynomial.aeval y ag ≠ 0 := by
      intro hy
      apply hEvalProd
      simp [hy]
    have hℓY : MvPolynomial.aeval y ℓ ≠ 0 := by
      intro hy
      apply hEvalProd
      simp [hy]
    have hyne : y ≠ p := by
      intro hEq
      subst y
      exact hℓY (by simp [ℓ])
    let QfY := (radialParameter p f).map (MvPolynomial.aeval y).toRingHom
    let QgY := (radialParameter p g).map (MvPolynomial.aeval y).toRingHom
    have hQfYcoeff : QfY.coeff kf ≠ 0 := by
      have heval := radialParameter_coeff_eval p y f kf
      change MvPolynomial.aeval y af = QfY.coeff kf at heval
      rw [← heval]
      exact hafY
    have hQgYcoeff : QgY.coeff kg ≠ 0 := by
      have heval := radialParameter_coeff_eval p y g kg
      change MvPolynomial.aeval y ag = QgY.coeff kg at heval
      rw [← heval]
      exact hagY
    have hQfY : QfY ≠ 0 := by
      intro hzero
      exact hQfYcoeff (by simp [hzero])
    have hQgY : QgY ≠ 0 := by
      intro hzero
      exact hQgYcoeff (by simp [hzero])
    let Q := (radialParameter p (f*g)).map (MvPolynomial.aeval y).toRingHom
    have hQ : Q = QfY * QgY := by
      simp [Q, QfY, QgY, radialParameter]
    have hroot : ∀ c : ℂ, c ≠ 0 → Q.eval c = 0 := by
      intro c hc
      have hcy0 : c • (y-p) ≠ 0 := smul_ne_zero hc (sub_ne_zero.mpr hyne)
      have hcy : c • (y-p) ∈ ProjectiveVariety.nonzeroRepresentatives T := by
        refine ⟨hcy0, ?_⟩
        refine ⟨y, hyV, hyne, ?_⟩
        exact ((Projectivization.mk_eq_mk_iff' ℂ (c • (y-p)) (y-p) hcy0
          (sub_ne_zero.mpr hyne)).2 ⟨c, rfl⟩).symm
      have hz := (MvPolynomial.mem_vanishingIdeal_iff.mp hfgvan) (c • (y-p)) hcy
      have hparam := radialParameter_eval p y (f*g) c
      change Q.eval c = _ at hparam
      have hargs : c • (y-p) = fun i => c * (y i - p i) := by
        funext i
        simp [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      rw [hargs] at hz
      rw [hparam]
      exact hz
    have hroots : Set.Infinite {c : ℂ | Q.eval c = 0} := by
      have hcompl : ({(0 : ℂ)} : Set ℂ)ᶜ ⊆ {c : ℂ | Q.eval c = 0} := by
        intro c hc
        have hc0 : c ≠ 0 := by simpa using hc
        exact hroot c hc0
      exact Set.Infinite.mono hcompl (Set.finite_singleton (0 : ℂ)).infinite_compl
    have hQzero : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      simpa only [Polynomial.IsRoot, Set.mem_setOf_eq] using hroots
    rw [hQ] at hQzero
    exact (mul_eq_zero.mp hQzero).elim hQfY hQgY

end

end DistinctDistances
