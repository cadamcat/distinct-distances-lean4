import DistinctDistances.TrackD.RationalContainment
import DistinctDistances.TrackD.GenericCotangent

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- Polynomial pullback to the source function field on a rational chart. -/
def rationalFieldPullback {n m : ℕ} (K : Type*) [Field K] [Algebra ℂ K]
    (φ : Poly n →ₐ[ℂ] K) (f : Fin m → Poly n) (g : Poly n) : Poly m →ₐ[ℂ] K :=
  MvPolynomial.aeval (fun i => φ (f i) / φ g)

private theorem aeval_homogeneous_scaled {σ : Type*} (K : Type*) [CommRing K]
    [Algebra ℂ K] (q : MvPolynomial σ ℂ) (D : ℕ) (hq : q.IsHomogeneous D)
    (c : K) (y : σ → K) :
    MvPolynomial.aeval (fun i => c * y i) q =
      c ^ D * MvPolynomial.aeval y q := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdegree : D = ∑ i ∈ e.support, e i := hq.degree_eq_sum_deg_support he
  have hprod :
      (∏ i ∈ e.support, (c * y i) ^ e i) =
        c ^ D * ∏ i ∈ e.support, (y i) ^ e i := by
    calc
      (∏ i ∈ e.support, (c * y i) ^ e i) =
          ∏ i ∈ e.support, c ^ e i * (y i) ^ e i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [mul_pow]
      _ = (∏ i ∈ e.support, c ^ e i) *
          ∏ i ∈ e.support, (y i) ^ e i := by rw [Finset.prod_mul_distrib]
      _ = c ^ D * ∏ i ∈ e.support, (y i) ^ e i := by
        rw [Finset.prod_pow_eq_pow_sum, hdegree]
  simp only [hprod]
  ring

private theorem aeval_homogenize_one {m : ℕ} (K : Type*) [CommRing K]
    [Algebra ℂ K] (q : Poly m) (y : Fin m → K) :
  MvPolynomial.aeval (fun o : Option (Fin m) => o.elim 1 y)
        (OAI.PiExponentJets.W22.homogenize q) = MvPolynomial.aeval y q := by
  let ρ : MvPolynomial (Option (Fin m)) ℂ →ₐ[ℂ] K :=
    MvPolynomial.aeval (fun o : Option (Fin m) => o.elim 1 y)
  let δ : MvPolynomial (Option (Fin m)) ℂ →ₐ[ℂ] Poly m :=
    { OAI.PiExponentJets.W22.dehomogenize with
      commutes' := by intro a; simp [OAI.PiExponentJets.W22.dehomogenize] }
  have hρ : ρ = (MvPolynomial.aeval y).comp δ := by
    ext i
    cases i <;> simp [ρ, δ, OAI.PiExponentJets.W22.dehomogenize]
  calc
    _ = ρ (OAI.PiExponentJets.W22.homogenize q) := rfl
    _ = ((MvPolynomial.aeval y).comp δ)
        (OAI.PiExponentJets.W22.homogenize q) := by rw [hρ]
    _ = MvPolynomial.aeval y
        (OAI.PiExponentJets.W22.dehomogenize
          (OAI.PiExponentJets.W22.homogenize q)) := rfl
    _ = MvPolynomial.aeval y q := by
      rw [OAI.PiExponentJets.W22.dehomogenize_homogenize]

private theorem rationalNumerator_field_eval {n m : ℕ}
    (X : AffineVariety n) (K : Type*) [Field K] [Algebra ℂ K]
    [Algebra (Poly n ⧸ X.ideal) K] [IsScalarTower ℂ (Poly n ⧸ X.ideal) K]
    [IsFractionRing (Poly n ⧸ X.ideal) K]
    (f : Fin m → Poly n) (g : Poly n) (hg : g ∉ X.ideal) (q : Poly m) :
    coordinateFieldMap X.ideal K (rationalNumerator f g q) =
      coordinateFieldMap X.ideal K g ^ q.totalDegree *
        rationalFieldPullback K (coordinateFieldMap X.ideal K) f g q := by
  let φ := coordinateFieldMap X.ideal K
  let y : Fin m → K := fun i => φ (f i) / φ g
  have hφg : φ g ≠ 0 := by
    intro hzero
    apply hg
    rw [← coordinateFieldMap_kernel X.ideal K]
    exact RingHom.mem_ker.mpr hzero
  have hcoords :
      (fun o : Option (Fin m) => φ (o.elim g f)) =
        (fun o : Option (Fin m) => φ g * o.elim 1 y) := by
    funext o
    cases o with
    | none => simp
    | some i =>
      change φ (f i) = φ g * (φ (f i) / φ g)
      calc
        φ (f i) = φ (f i) / φ g * φ g := (div_mul_cancel₀ _ hφg).symm
        _ = φ g * (φ (f i) / φ g) := by ring
  change φ (MvPolynomial.aeval (fun o : Option (Fin m) => o.elim g f)
    (OAI.PiExponentJets.W22.homogenize q)) = _
  rw [MvPolynomial.comp_aeval_apply, hcoords]
  have hscale := aeval_homogeneous_scaled K
    (OAI.PiExponentJets.W22.homogenize q) q.totalDegree
    (OAI.PiExponentJets.W22.homogenize_isHomogeneous q) (φ g)
    (fun o : Option (Fin m) => o.elim 1 y)
  rw [aeval_homogenize_one K q y] at hscale
  calc
    _ = φ g ^ q.totalDegree * MvPolynomial.aeval y q := hscale
    _ = φ g ^ q.totalDegree *
        rationalFieldPullback K φ f g q := by
      congr 1

/-- `FA.model`, `secants.tex:63–69`. The ideal of the genuine rational-image
closure is the kernel of the pullback to the source coordinate function field.
Implementation package: homogenized denominator clearing, with no dimension argument. -/
theorem rationalFieldPullback_kernel {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (Poly n ⧸ X.ideal) K]
    [IsScalarTower ℂ (Poly n ⧸ X.ideal) K] [IsFractionRing (Poly n ⧸ X.ideal) K]
    (f : Fin m → Poly n) (g : Poly n) (hg : g ∉ X.ideal) :
    RingHom.ker (rationalFieldPullback K (coordinateFieldMap X.ideal K) f g) =
      (rationalImage X f g).ideal := by
  let φ := coordinateFieldMap X.ideal K
  have hkerφ : RingHom.ker φ = X.ideal := coordinateFieldMap_kernel X.ideal K
  have hφg : φ g ≠ 0 := by
    intro h
    apply hg
    rw [← hkerφ]
    exact RingHom.mem_ker.mpr h
  ext q
  change rationalFieldPullback K φ f g q = 0 ↔ q ∈ (rationalImage X f g).ideal
  constructor
  · intro hq
    have hnumK : φ (rationalNumerator f g q) = 0 := by
      rw [rationalNumerator_field_eval X K f g hg q, hq, mul_zero]
    have hnumI : rationalNumerator f g q ∈ X.ideal := by
      rw [← hkerφ]
      exact RingHom.mem_ker.mpr hnumK
    have hnumEval := (mem_ideal_iff_eval_zero X (rationalNumerator f g q)).mp hnumI
    change q ∈ MvPolynomial.vanishingIdeal ℂ
      {y | ∃ x ∈ X, MvPolynomial.eval x g ≠ 0 ∧ rationalPoint f g x = y}
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro y ⟨x, hx, hgx, rfl⟩
    have h := hnumEval x hx
    rw [rationalNumerator_eval f g q x hgx] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hgx)
  · intro hq
    have hopen : ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0 ∧
        MvPolynomial.eval x (rationalNumerator f g q) = 0) := by
      have hgopen : ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0) := by
        obtain ⟨x, hx, hxg⟩ : ∃ x ∈ X, MvPolynomial.eval x g ≠ 0 := by
          by_contra h
          apply hg
          apply (mem_ideal_iff_eval_zero X g).mpr
          intro x hx
          by_contra hxg
          exact h ⟨x, hx, hxg⟩
        exact ⟨g, ⟨x, hx, hxg⟩, fun _ _ h => h⟩
      refine hgopen.mono ?_
      intro x hx hxg
      refine ⟨hxg, ?_⟩
      have hqEval : MvPolynomial.eval (rationalPoint f g x) q = 0 := by
        change q ∈ MvPolynomial.vanishingIdeal ℂ
          {y | ∃ x ∈ X, MvPolynomial.eval x g ≠ 0 ∧ rationalPoint f g x = y} at hq
        exact (MvPolynomial.mem_vanishingIdeal_iff.mp hq)
          (rationalPoint f g x) ⟨x, hx, hxg, rfl⟩
      rw [rationalNumerator_eval f g q x hxg, hqEval, mul_zero]
    have hnumAll : ∀ x ∈ X, MvPolynomial.eval x (rationalNumerator f g q) = 0 :=
      ForGeneralPoint.eval_zero hX _ (hopen.mono fun _ _ h => h.2)
    have hnumI : rationalNumerator f g q ∈ X.ideal :=
      (mem_ideal_iff_eval_zero X _).mpr hnumAll
    have hnumK : φ (rationalNumerator f g q) = 0 := by
      exact RingHom.mem_ker.mp (hkerφ ▸ hnumI)
    rw [rationalNumerator_field_eval X K f g hg q] at hnumK
    exact (mul_eq_zero.mp hnumK).resolve_left (pow_ne_zero _ hφg)

end
end DistinctDistances.TrackD
