import DistinctDistances.TrackA.NormalizationRankSupport
import DistinctDistances.Foundations.GenericFiber
import Mathlib.FieldTheory.Minpoly.Basic

/-! Actual complex source sections in the prescribed open, for the mixed
section in `sc:retained-products.family`, sparse-cones.tex:194–207. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

/-- A proper cut on the irreducible source of a finite normalization
has no points over one nonempty principal open in the original base. -/
theorem common_finite_cut_base_open {d k : ℕ}
    (X : AffineVariety d) (hX : X.IsIrreducible) (hd : X.dimension = k)
    (φ : AffineProjection d k) (hfinite : TrackA.FiniteAffineProjection φ X)
    (g : Poly d) (hg : g ∉ X.ideal) :
    ∃ b : Poly k, b ∉ (φ.image X).ideal ∧
      ∀ x ∈ X, MvPolynomial.eval (φ.apply x) b ≠ 0 →
        MvPolynomial.eval x g ≠ 0 := by
  letI : X.ideal.IsPrime := hX
  let A := Poly d ⧸ X.ideal
  let ρ : Poly k →ₐ[ℂ] A := (Ideal.Quotient.mkₐ ℂ X.ideal).comp φ.pullback
  letI : Algebra (Poly k) A := ρ.toRingHom.toAlgebra
  letI : Module (Poly k) A := ρ.toRingHom.toAlgebra.toModule
  have hρfinite : ρ.toRingHom.Finite := hfinite
  let u : A := Ideal.Quotient.mk X.ideal g
  have hu : u ≠ 0 := by
    exact fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hint : IsIntegral (Poly k) u := hρfinite.to_isIntegral u
  let f := minpoly (Poly k) u
  have hf : f.Monic := minpoly.monic hint
  have hfroot : Polynomial.aeval u f = 0 := minpoly.aeval (Poly k) u
  have hb : f.coeff 0 ≠ 0 := by
    intro hc
    have hfactor : Polynomial.X * f.divX = f := by
      simpa only [hc, Polynomial.C_0, add_zero] using Polynomial.X_mul_divX_add f
    have hmonic : f.divX.Monic := Polynomial.monic_X.of_mul_monic_left
      (hfactor.symm ▸ hf)
    have he := congrArg (Polynomial.aeval u) hfactor
    have hproduct : u * Polynomial.aeval u f.divX = 0 := by
      simpa only [map_mul, Polynomial.aeval_X, hfroot] using he
    have hdivroot : Polynomial.aeval u f.divX = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hu
    exact (Polynomial.degree_divX_lt hf.ne_zero).not_ge
      (minpoly.min (Poly k) u hmonic hdivroot)
  let b : Poly k := f.coeff 0
  have hrel : u * Polynomial.aeval u f.divX + ρ b = 0 := by
    have he := congrArg (Polynomial.aeval u) (Polynomial.X_mul_divX_add f)
    have hbase : (algebraMap (Poly k) A) (f.coeff 0) = ρ b := rfl
    simpa only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      hfroot, hbase] using he
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (Polynomial.aeval u f.divX)
  have hcut : g * v + φ.pullback b ∈ X.ideal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_add, map_mul]
    change u * Ideal.Quotient.mk X.ideal v + ρ b = 0
    rw [hv]
    exact hrel
  refine ⟨b, ?_, ?_⟩
  · rw [TrackA.finite_affine_projection_image_ideal_bot X hX hd φ hfinite]
    simpa only [Ideal.mem_bot] using hb
  · intro x hx hxbase hxg
    have he := MvPolynomial.mem_zeroLocus_iff.mp hx (g * v + φ.pullback b) hcut
    have hxg' : MvPolynomial.aeval x g = 0 := hxg
    rw [map_add, map_mul, hxg', zero_mul, zero_add, φ.eval_pullback] at he
    exact hxbase he

/-- A complete degree-sized complex linear fiber can be chosen inside
any prescribed proper source open. The finite fiber is the literal
fiber of the original projection, with no sheets discarded. -/
theorem common_normalization_section_in_open {d k : ℕ}
    (X : AffineVariety d) (hX : X.IsIrreducible) (hd : X.dimension = k)
    (φ : AffineProjection d k) (hφ : Function.Surjective φ.linear)
    (hfinite : TrackA.FiniteAffineProjection φ X) (r : ℕ)
    (hr : φ.GenericallyFiniteOfDegree X r) (hdegree : (r : ℚ) = X.degree)
    (g : Poly d) (hg : g ∉ X.ideal) :
    ∃ t ∈ (φ.image X).points, ∃ S : Finset (Point d),
      (S.card : ℚ) = X.degree ∧
      (∀ x, x ∈ S ↔ x ∈ X ∧ φ.apply x = t) ∧
      ∀ x ∈ S, MvPolynomial.eval x g ≠ 0 := by
  obtain ⟨b, hb, havoid⟩ := common_finite_cut_base_open X hX hd φ hfinite g hg
  obtain ⟨_, c, hc, hcount⟩ := hr
  have hprime := φ.image_irreducible X hX
  have hbc : b * c ∉ (φ.image X).ideal := by
    intro hm
    exact (hprime.mem_or_mem hm).elim hb hc
  obtain ⟨t, ht, htbc⟩ := GenericFiber.exists_point_of_not_mem (φ.image X) (b * c) hbc
  have htb : MvPolynomial.aeval t b ≠ 0 := by
    intro hz
    exact htbc (by simp only [map_mul, hz, zero_mul])
  have htc : MvPolynomial.aeval t c ≠ 0 := by
    intro hz
    exact htbc (by simp only [map_mul, hz, mul_zero])
  obtain ⟨hfin, hcard⟩ := hcount t ht htc
  refine ⟨t, ht, hfin.toFinset, ?_, ?_, ?_⟩
  · have hn : hfin.toFinset.card = r := by
      rw [← Set.ncard_eq_toFinset_card (φ.fiber X t) hfin]
      exact hcard
    rw [hn]
    exact hdegree
  · intro x
    exact hfin.mem_toFinset
  · intro x hx
    have hfiber : x ∈ X ∧ φ.apply x = t := hfin.mem_toFinset.mp hx
    apply havoid x hfiber.1
    rw [hfiber.2]
    exact htb

end
end DistinctDistances.SparseCones
