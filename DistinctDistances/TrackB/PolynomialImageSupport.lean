import DistinctDistances.Foundations
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots

namespace DistinctDistances.TrackB
noncomputable section

/-- The image of a polynomial map to projective space on a principal affine open. -/
def polynomialProjectiveImage {n m : ℕ} (X : AffineVariety n) (g : Poly n)
    (F : Fin m → Poly n) : Set (ProjectivePoint m) :=
  {p | ∃ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 ∧
    ∃ hF : (fun i => MvPolynomial.aeval x (F i)) ≠ 0,
      Projectivization.mk ℂ (fun i => MvPolynomial.aeval x (F i)) hF = p}

def polynomialProjectiveFiber {n m : ℕ} (X : AffineVariety n) (g : Poly n)
    (F : Fin m → Poly n) (p : ProjectivePoint m) : Set (Point n) :=
  {x | x ∈ X.points ∧ MvPolynomial.aeval x g ≠ 0 ∧
    ∃ hF : (fun i => MvPolynomial.aeval x (F i)) ≠ 0,
      Projectivization.mk ℂ (fun i => MvPolynomial.aeval x (F i)) hF = p}

/-- Pull back after multiplying every image coordinate by an independent scalar. -/
def scalarPolynomialPullback {n m : ℕ} (F : Fin m → Poly n) :
    Poly m →ₐ[ℂ] Polynomial (Poly n) :=
  MvPolynomial.aeval (fun i => Polynomial.X * Polynomial.C (F i))

theorem eval_scalarPolynomialPullback {n m : ℕ} (F : Fin m → Poly n)
    (x : Point n) (t : ℂ) (f : Poly m) :
    ((scalarPolynomialPullback F f).map (MvPolynomial.aeval x).toRingHom).eval t =
      MvPolynomial.aeval (t • (fun i => MvPolynomial.aeval x (F i))) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [scalarPolynomialPullback]
  | add f h hf hh => simp only [map_add, Polynomial.map_add, Polynomial.eval_add, hf, hh]
  | mul_X f i hf =>
      rw [map_mul, Polynomial.map_mul, Polynomial.eval_mul, hf]
      simp only [scalarPolynomialPullback, MvPolynomial.aeval_X, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C, map_mul, MvPolynomial.aeval_X, Pi.smul_apply, smul_eq_mul,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] <;> ring

/-- Vanishing on a nonempty principal open of a reduced irreducible variety is
vanishing on the whole variety. This is the only open-density fact needed here. -/
theorem principal_open_vanishing {n : ℕ} (X : AffineVariety n)
    (hX : X.IsIrreducible) (g f : Poly n) (hg : g ∉ X.ideal)
    (hf : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 → MvPolynomial.aeval x f = 0) :
    f ∈ X.ideal := by
  have hgf : g * f ∈ X.ideal := by
    rw [← X.vanishingIdeal_points]
    intro x hx
    rw [map_mul]
    by_cases hzero : MvPolynomial.aeval x g = 0
    · rw [hzero, zero_mul]
    · rw [hf x hx hzero, mul_zero]
  exact (hX.mem_or_mem hgf).resolve_left hg

/-- `conc:degree.image-irreducible`, concentration.tex:519–522,633–638.
The image ideal is the kernel of a map into a polynomial ring over the domain
coordinate ring of X. No smoothness or normality hypothesis is required. -/
theorem polynomialProjectiveImage_irreducible {n m : ℕ} (X : AffineVariety n)
    (hX : X.IsIrreducible) (g : Poly n) (hg : g ∉ X.ideal)
    (F : Fin m → Poly n)
    (hF : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 →
      (fun i => MvPolynomial.aeval x (F i)) ≠ 0) :
    (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).IsIrreducible := by
  letI : X.ideal.IsPrime := hX
  let q : Poly n →+* Poly n ⧸ X.ideal := Ideal.Quotient.mk X.ideal
  let ψ : Poly m →+* Polynomial (Poly n ⧸ X.ideal) :=
    (Polynomial.mapRingHom q).comp (scalarPolynomialPullback F).toRingHom
  have hmem (f : Poly m) :
      f ∈ ProjectiveVariety.vanishingIdeal (polynomialProjectiveImage X g F) ↔ ψ f = 0 := by
    constructor
    · intro hf
      have hcoeff (k : ℕ) : (scalarPolynomialPullback F f).coeff k ∈ X.ideal := by
        apply principal_open_vanishing X hX g _ hg
        intro x hx hxg
        let P : Polynomial ℂ :=
          (scalarPolynomialPullback F f).map (MvPolynomial.aeval x).toRingHom
        have hP : P = 0 := by
          apply Polynomial.eq_zero_of_infinite_isRoot
          apply Set.Infinite.mono (s := ({(0 : ℂ)} : Set ℂ)ᶜ)
            ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
          intro t ht
          have ht0 : t ≠ 0 := by simpa using ht
          let w : Point m := fun i => MvPolynomial.aeval x (F i)
          have hw : w ≠ 0 := hF x hx hxg
          have htw : t • w ≠ 0 := smul_ne_zero ht0 hw
          have heq : Projectivization.mk ℂ (t • w) htw = Projectivization.mk ℂ w hw :=
            (Projectivization.mk_eq_mk_iff' ℂ (t • w) w htw hw).2 ⟨t, rfl⟩
          have hp : Projectivization.mk ℂ w hw ∈ polynomialProjectiveImage X g F :=
            ⟨x, hx, hxg, hw, rfl⟩
          change P.eval t = 0
          rw [eval_scalarPolynomialPullback]
          exact hf (t • w) ⟨htw, heq.symm ▸ hp⟩
        have hz := congrArg (fun Q : Polynomial ℂ => Q.coeff k) hP
        simpa [P] using hz
      apply Polynomial.ext
      intro k
      rw [Polynomial.coeff_zero]
      change ((scalarPolynomialPullback F f).map q).coeff k = 0
      rw [Polynomial.coeff_map]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcoeff k)
    · intro hf
      rintro w ⟨hw, hp⟩
      obtain ⟨x, hx, hxg, hv, he⟩ := hp
      let v : Point m := fun i => MvPolynomial.aeval x (F i)
      have hcoeff (k : ℕ) : (scalarPolynomialPullback F f).coeff k ∈ X.ideal := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hz := congrArg (fun Q : Polynomial (Poly n ⧸ X.ideal) => Q.coeff k) hf
        simpa [ψ, q] using hz
      have hP : (scalarPolynomialPullback F f).map (MvPolynomial.aeval x).toRingHom = 0 := by
        apply Polynomial.ext
        intro k
        rw [Polynomial.coeff_map, Polynomial.coeff_zero]
        exact hx _ (hcoeff k)
      have he' : Projectivization.mk ℂ w hw = Projectivization.mk ℂ v hv := he.symm
      obtain ⟨t, ht⟩ :=
        (Projectivization.mk_eq_mk_iff' ℂ w v hw hv).mp he'
      have hz := congrArg (Polynomial.eval t) hP
      simpa only [eval_scalarPolynomialPullback, Polynomial.eval_zero, ← ht] using hz
  have hker : ProjectiveVariety.vanishingIdeal (polynomialProjectiveImage X g F) =
      RingHom.ker ψ := by
    ext f
    exact hmem f
  change (ProjectiveVariety.vanishingIdeal (polynomialProjectiveImage X g F)).IsPrime
  rw [hker]
  exact RingHom.ker_isPrime ψ

#print axioms polynomialProjectiveImage_irreducible
end
end DistinctDistances.TrackB
