import DistinctDistances.TrackD.Genericity
import DistinctDistances.TrackA.Regularity
import Mathlib.RingTheory.Kaehler.Polynomial

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

@[simp] theorem locus_singleton (X : AffineVariety d) :
    AffineFamily.locus ({X} : AffineFamily.Family d) = X := by
  apply AffineVariety.ext
  simp [AffineFamily.locus, AffineVariety.ofIdeal, X.isRadical.radical]

@[simp] theorem degree_singleton (X : AffineVariety d) :
    AffineFamily.degree ({X} : AffineFamily.Family d) = X.degree := by
  simp [AffineFamily.degree]

/-- OAI's independent-coordinate description bounds the shared Hilbert dimension by
the ambient number of coordinates. -/
theorem dimension_le_ambient (X : AffineVariety d) (hX : X.IsIrreducible) : X.dimension ≤ d := by
  obtain ⟨P, j, hj, _, _, N, hN⟩ :=
    OAI.QuarticPowerFree.coordinate_hilbert_degree_independent X.ideal hX.ne_top
  have hP : P = OAI.QuarticPowerFree.coordinateHilbert X.ideal := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, hN⟩,
      OAI.QuarticPowerFree.coordinateHilbert_eventually X.ideal] with T hp hq
    exact hp.symm.trans hq
  have hc := Fintype.card_le_of_injective j hj
  simp only [Fintype.card_fin] at hc
  change (OAI.QuarticPowerFree.coordinateHilbert X.ideal).natDegree ≤ d
  rwa [← hP]

theorem mk_derivation_sum (K : Type*) [CommRing K] [Algebra ℂ K]
    [Algebra (Poly d) K] [IsScalarTower ℂ (Poly d) K] (v : Fin d → K) (f : Poly d) :
    MvPolynomial.mkDerivation ℂ v f = ∑ i : Fin d, MvPolynomial.pderiv i f • v i := by
  let δ := MvPolynomial.mkDerivation ℂ v
  have hs := (KaehlerDifferential.mvPolynomialBasis ℂ (Fin d)).sum_repr
    (KaehlerDifferential.D ℂ (Poly d) f)
  have he := congrArg δ.liftKaehlerDifferential hs
  simp only [map_sum, map_smul, KaehlerDifferential.mvPolynomialBasis_repr_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    Derivation.liftKaehlerDifferential_comp_D, MvPolynomial.mkDerivation_X] at he
  simpa only [δ, MvPolynomial.mkDerivation_X] using he.symm

/-- Bounded equations already give every tangent equation once they include an ideal
generating set. This argument uses the derivation product rule at points of the variety. -/
theorem bounded_kernel_eq_tangent (X : AffineVariety d) (E : Finset (Poly d))
    (hE : Ideal.span (E : Set (Poly d)) = X.ideal) (D : ℕ)
    (hdeg : ∀ f ∈ E, f.totalDegree ≤ D) (x : Point d) (hx : x ∈ X) :
    TrackA.boundedJacobianKernel ({X} : AffineFamily.Family d) D x = X.tangentSpace x := by
  have hloc : (AffineFamily.locus ({X} : AffineFamily.Family d)).ideal = X.ideal :=
    congrArg AffineVariety.ideal (locus_singleton X)
  apply le_antisymm
  · intro v hv
    let φ : Poly d →ₐ[ℂ] ℂ := MvPolynomial.aeval x
    letI : Algebra (Poly d) ℂ := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ (Poly d) ℂ := IsScalarTower.of_algHom φ
    let δ := MvPolynomial.mkDerivation ℂ v
    have hδ : ∀ f : Poly d, δ f = differential f x v := by
      intro f
      have hs := mk_derivation_sum ℂ v f
      simp only [Algebra.smul_def] at hs
      change δ f = ∑ i : Fin d, MvPolynomial.eval x (MvPolynomial.pderiv i f) * v i at hs
      simpa [differential, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, smul_eq_mul] using hs
    have hzero : ∀ f ∈ Ideal.span (E : Set (Poly d)), φ f = 0 ∧ δ f = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        have hfI : f ∈ X.ideal := hE ▸ Ideal.subset_span hf
        have hf0 : φ f = 0 := (mem_ideal_iff_eval_zero X f).mp hfI x hx
        have hfb : f ∈ (AffineFamily.locus ({X} : AffineFamily.Family d)).ideal := by
          rwa [hloc]
        have hvf := (Submodule.mem_iInf _).mp hv ⟨f, hfb, hdeg f hf⟩
        exact ⟨hf0, by simpa only [hδ, LinearMap.mem_ker] using hvf⟩
      | zero => simp
      | add f g hf hg ihf ihg => simp [map_add, ihf, ihg]
      | smul r f hf ih =>
        change φ (r * f) = 0 ∧ δ (r * f) = 0
        have hφf : algebraMap (Poly d) ℂ f = 0 := by
          change φ f = 0
          exact ih.1
        simp [map_mul, δ.leibniz, Algebra.smul_def, ih, hφf]
    simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    intro f
    have hf : f.val ∈ Ideal.span (E : Set (Poly d)) := by
      rw [hE]
      exact f.property
    simpa only [hδ] using (hzero f.val hf).2
  · intro v hv
    simp only [TrackA.boundedJacobianKernel, Submodule.mem_iInf, LinearMap.mem_ker]
    intro f
    have hf : f.val ∈ X.ideal := by simpa only [hloc] using f.property.1
    exact (Submodule.mem_iInf _).mp hv ⟨f.val, hf⟩

theorem singleton_from_generators (X : AffineVariety d) (hX : X.IsIrreducible)
    (E : Finset (Poly d)) (hE : Ideal.span (E : Set (Poly d)) = X.ideal)
    (L : ℕ) (hL : 1 ≤ L) (hdeg : ∀ f ∈ E, f.totalDegree ≤ L) :
    TrackA.FromAffineLists ({X} : AffineFamily.Family d) L := by
  letI : X.ideal.IsPrime := hX
  refine ⟨1, fun _ => {X}, fun _ => L, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hL, (⟨(E : Set (Poly d)), hdeg, ?_⟩ :
      AffineFamily.ComponentsDefinedInDegree {X} L)⟩
    intro V hV
    have hVX := Finset.mem_singleton.mp hV
    subst V
    change X.ideal ∈ (Ideal.span (E : Set (Poly d))).minimalPrimes
    rw [hE, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  · intro V
    constructor
    · intro hV
      exact ⟨0, hV⟩
    · rintro ⟨i, hV⟩
      exact hV
  · simp

/-- Generic tangent dimension, derived from the frozen singleton-family regularity
statement. No new smoothness assertion is used as an axiom or input. -/
theorem general_tangent_finrank (X : AffineVariety d) (hX : X.IsIrreducible) :
    ForGeneralPoint X (fun x => Module.finrank ℂ (X.tangentSpace x) = X.dimension) := by
  obtain ⟨E, hE⟩ := X.ideal.fg_of_isNoetherianRing
  let L := 1 + E.sup MvPolynomial.totalDegree
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hdeg : ∀ f ∈ E, f.totalDegree ≤ L := by
    intro f hf
    have hsup := Finset.le_sup (f := MvPolynomial.totalDegree) hf
    dsimp [L]
    omega
  have hF : AffineFamily.IsPure ({X} : AffineFamily.Family d) X.dimension := by
    intro V hV
    have hVX := Finset.mem_singleton.mp hV
    subst V
    exact ⟨hX, rfl⟩
  obtain ⟨C, hC, hreg⟩ := TrackA.poly_regularity_exceptional_degree d
  let D := (C + 1) * L
  have hCD : C * L ≤ D := by dsimp [D]; nlinarith
  have hLD : L ≤ D := by dsimp [D]; nlinarith
  have hD : 0 < (D : ℚ) := by
    have : 0 < D := by dsimp [D]; nlinarith
    exact_mod_cast this
  have hXpos : (0 : ℚ) < X.degree :=
    lt_of_lt_of_le zero_lt_one (X.one_le_degree hX.ne_top)
  have hlpos : (0 : ℚ) < L := by exact_mod_cast (show 0 < L by omega)
  have hsmall : (C : ℚ) * X.degree * (L : ℚ) / (D : ℚ) < X.degree := by
    apply (div_lt_iff₀ hD).mpr
    simp only [D, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_pos hXpos hlpos]
  obtain ⟨bad, hsub, hbad, hrank⟩ := hreg {X} X.dimension L D
    (dimension_le_ambient X hX) hF hL (singleton_from_generators X hX E hE L hL hdeg) hCD
  have hgood : X ∉ bad := by
    intro hmem
    have heq : bad = {X} := le_antisymm hsub (Finset.singleton_subset_iff.mpr hmem)
    simp only [heq, degree_singleton] at hbad
    exact (not_lt_of_ge hbad) hsmall
  obtain ⟨g, hg, hgRank⟩ := hrank X (Finset.mem_singleton_self X) hgood
  have hgnz : ∃ x ∈ X, MvPolynomial.eval x g ≠ 0 := by
    by_contra h
    push Not at h
    exact hg ((mem_ideal_iff_eval_zero X g).mpr h)
  refine ⟨g, hgnz, ?_⟩
  intro x hx hn
  have hker := bounded_kernel_eq_tangent X E hE D
    (fun f hf => (hdeg f hf).trans hLD) x hx
  calc
    Module.finrank ℂ (X.tangentSpace x) =
        Module.finrank ℂ (TrackA.boundedJacobianKernel ({X} : AffineFamily.Family d) D x) :=
      (congrArg (fun W : Submodule ℂ (Point d) => Module.finrank ℂ W) hker).symm
    _ = X.dimension := hgRank x hx hn

end
end DistinctDistances.TrackD
