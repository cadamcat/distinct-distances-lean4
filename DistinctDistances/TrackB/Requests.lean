import DistinctDistances.Foundations
import DistinctDistances.TrackB.PolynomialImageSupport
import DistinctDistances.TrackB.Compactification
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.FractionRing
import DistinctDistances.Foundations.GenericFiber
import DistinctDistances.TrackB.BridgesBAux

namespace DistinctDistances.TrackB.Request

/-- Request to track A, supplying conc:description-product (concentration.tex:1057–1058).
Expose the existing private AffineFamily.prime_same_dimension_eq proof from
Foundations/Affine.lean:343–424, so refinement can conclude that V stays a component. -/
theorem affine_prime_same_dimension_eq {n k : ℕ}
    (I J : Ideal (Poly n)) [I.IsPrime] [J.IsPrime] (hIJ : I ≤ J)
    (hI : OAI.QuarticPowerFree.affineDimension I = k)
    (hJ : OAI.QuarticPowerFree.affineDimension J = k) : I = J := by
  classical
  by_contra hne
  have hlt : I < J := lt_of_le_of_ne hIJ hne
  obtain ⟨p, hpJ, hpI⟩ := SetLike.exists_of_lt hlt
  have hcut : I ⊔ Ideal.span {p} ≤ J :=
    sup_le hIJ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpJ))
  let P := OAI.QuarticPowerFree.coordinateHilbert I
  let Q := OAI.QuarticPowerFree.coordinateHilbert (I ⊔ Ideal.span {p})
  have hP : ∀ᶠ T : ℕ in Filter.atTop,
      P.eval (T : ℚ) =
        (Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace T).map
          (Ideal.Quotient.mkₐ ℂ I).toLinearMap) : ℚ) := by
    exact (OAI.QuarticPowerFree.coordinateHilbert_eventually I).mono
      (fun _ h => h.symm)
  have hQ : ∀ᶠ T : ℕ in Filter.atTop,
      Q.eval (T : ℚ) =
        (Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace T).map
          (Ideal.Quotient.mkₐ ℂ (I ⊔ Ideal.span {p})).toLinearMap) : ℚ) := by
    exact (OAI.QuarticPowerFree.coordinateHilbert_eventually _).mono
      (fun _ h => h.symm)
  have hI' : P.natDegree = k := by
    simpa [P, OAI.QuarticPowerFree.affineDimension] using hI
  by_cases hk : k = 0
  · have hcutInfo := OAI.QuarticPowerFree.proper_cut_hilbert_polynomial
      I p hpI P Q hP hQ 0 (by rw [hI', hk]; omega)
    have hcoeffP : P.coeff 1 = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hI', hk]
      omega
    have hcoeffQ : Q.coeff 0 ≤ 0 := by
      simpa [hcoeffP] using hcutInfo.2
    have hcutDim : OAI.QuarticPowerFree.affineDimension
        (I ⊔ Ideal.span {p}) = 0 := by
      have hQdim : Q.natDegree = 0 := Nat.eq_zero_of_le_zero hcutInfo.1
      simpa [Q, OAI.QuarticPowerFree.affineDimension] using hQdim
    have hcutProper : I ⊔ Ideal.span {p} ≠ ⊤ := by
      intro htop
      have htopJ : (⊤ : Ideal (Poly n)) ≤ J := htop ▸ hcut
      exact Ideal.IsPrime.ne_top' (top_le_iff.mp htopJ)
    have hdegreeQ : OAI.QuarticPowerFree.affineDegree
        (I ⊔ Ideal.span {p}) = Q.coeff 0 := by
      simp [OAI.QuarticPowerFree.affineDegree, Q, hcutDim]
    have hpositive := OAI.QuarticPowerFree.one_le_affineDegree
      (I ⊔ Ideal.span {p}) hcutProper
    rw [hdegreeQ] at hpositive
    have : (1 : ℚ) ≤ 0 := hpositive.trans hcoeffQ
    norm_num at this
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let d := k - 1
    have hdegP : P.natDegree ≤ d + 1 := by
      rw [hI']
      omega
    have hcutInfo := OAI.QuarticPowerFree.proper_cut_hilbert_polynomial
      I p hpI P Q hP hQ d hdegP
    have hnon : ∀ᶠ T : ℕ in Filter.atTop,
        0 ≤ (OAI.QuarticPowerFree.coordinateHilbert J).eval (T : ℚ) := by
      filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually J] with T hT
      rw [← hT]
      positivity
    have hle : ∀ᶠ T : ℕ in Filter.atTop,
        (OAI.QuarticPowerFree.coordinateHilbert J).eval (T : ℚ) ≤ Q.eval (T : ℚ) := by
      filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually J,
        OAI.QuarticPowerFree.coordinateHilbert_eventually (I ⊔ Ideal.span {p})]
        with T hJT hQT
      rw [← hJT, ← hQT]
      exact_mod_cast OAI.QuarticPowerFree.quotient_hilbert_le
        (I ⊔ Ideal.span {p}) J hcut T
    have hdimJ : (OAI.QuarticPowerFree.coordinateHilbert J).natDegree ≤ d := by
      exact (OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _
        hnon hle).trans hcutInfo.1
    have hJ' : (OAI.QuarticPowerFree.coordinateHilbert J).natDegree = k := by
      simpa [OAI.QuarticPowerFree.affineDimension] using hJ
    have : k ≤ d := by omega
    dsimp [d] at this
    omega

/-- Request to track A: the constant-fiber form of the image-dimension theorem,
supplying `conc:degree.dimension` (concentration.tex:519–522). All dimensions are
the shared Hilbert dimensions, and fibers are actual inverse images on a principal
open. The source and image may be singular. This request is reusable independently
of skew forms, ruling incidences, and the parameter compactification. -/
theorem polynomial_projective_image_dimension {n m d : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (g : Poly n) (hg : g ∉ X.ideal)
    (F : Fin m → Poly n)
    (hF : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 →
      (fun i => MvPolynomial.aeval x (F i)) ≠ 0)
    (hfib : ∀ p ∈ polynomialProjectiveImage X g F,
      (AffineVariety.closure (polynomialProjectiveFiber X g F p)).dimension = d) :
    X.dimension = (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).dimension + d :=
  GenericFiber.polynomial_projective_image_dimension X hX g hg F hF hfib

/-- Request to track A: Hilbert dimension of a nonempty principal open of an
affine linear space. This supplies the constant fiber input to conc:degree.dimension,
concentration.tex:519–522, and uses the existing affine Hilbert dimension. -/
theorem affine_linear_principal_open_dimension {n d : ℕ}
    (b : Point n) (φ : Point d →ₗ[ℂ] Point n) (hφ : Function.Injective φ)
    (g : Poly n) (t0 : Point d) (ht0 : MvPolynomial.aeval (b + φ t0) g ≠ 0) :
    (AffineVariety.closure {x | ∃ t : Point d, x = b + φ t ∧ MvPolynomial.aeval x g ≠ 0}).dimension = d :=
  GenericFiber.affine_linear_principal_open_dimension b φ hφ g t0 ht0

/-- Request to track A: the point-set form of proper projection from a closed
Segre subvariety, supplying conc:deg-dense-incidence (concentration.tex:644–648).
It asserts only image closedness, with no dimension or degree conclusion. -/
theorem projective_segre_projection_closed {n m : ℕ} (Y : ProjectiveVariety (n * m))
    (hY : ∀ b ∈ Y.points, ∃ p : ProjectivePoint n, ∃ q : ProjectivePoint m,
      segrePoint p q = b) :
    {q : ProjectivePoint m | ∃ p : ProjectivePoint n, segrePoint p q ∈ Y.points} =
      (ProjectiveVariety.closure
        {q : ProjectivePoint m | ∃ p : ProjectivePoint n, segrePoint p q ∈ Y.points}).points := by
  apply Set.Subset.antisymm (ProjectiveVariety.subset_closure _)
  intro q hq
  exact BridgesB.segre_projection_closed Y q hq

/-- Request to track A: separating actual coordinate functions with commuting
partial derivations in the coordinate fraction field. This supplies the generic
chart in conc:deg-null-local-rigidity, concentration.tex:966–981. No quadratic
form, tangent-null hypothesis, or linearity conclusion is assumed. -/
theorem affine_separating_coordinate_derivations {n r : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (hdim : X.dimension = r)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (Poly n ⧸ X.ideal) K]
    [IsScalarTower ℂ (Poly n ⧸ X.ideal) K] [IsFractionRing (Poly n ⧸ X.ideal) K] :
    ∃ ι : Fin r → Fin n, ∃ δ : Fin r → Derivation ℂ K K,
      (∀ i j, δ i (algebraMap (Poly n ⧸ X.ideal) K
        (Ideal.Quotient.mk X.ideal (MvPolynomial.X (ι j)))) = if i = j then 1 else 0) ∧
      (∀ i j x, δ i (δ j x) = δ j (δ i x)) ∧
      (∀ x : K, (∀ i, δ i x = 0) → ∃ c : ℂ, algebraMap ℂ K c = x) :=
  BridgesB.affine_separating_coordinate_derivations X hX hdim K

/-- Request to track A: a dominant polynomial map has an image containing a
homogeneous principal open of its actual projective closure. This is the
constructible-image input of conc:deg-skew-pencil (concentration.tex:824–843),
independent of tangent ranks or skew-pencil singularity. -/
theorem polynomial_projective_image_contains_open {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (g : Poly n) (hg : g ∉ X.ideal)
    (F : Fin m → Poly n)
    (hF : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 →
      (fun i => MvPolynomial.aeval x (F i)) ≠ 0) :
    ∃ (G : Poly m) (D : ℕ), G.IsHomogeneous D ∧
      G ∉ (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal ∧
      ∀ p ∈ (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).points,
        MvPolynomial.aeval p.rep G ≠ 0 → p ∈ polynomialProjectiveImage X g F :=
  BridgesB.polynomial_projective_image_contains_open X hX g hg F hF

end DistinctDistances.TrackB.Request
