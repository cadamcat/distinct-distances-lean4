import DistinctDistances.TrackD.TangentRankSpecialization
import DistinctDistances.TrackD.GenericTangent
import DistinctDistances.TrackA.ADepthAux
import DistinctDistances.TrackE.MOZtdAux

/-! Isolation inside the WHOLE original equation ideal, allowing other
components away from the counted point. `sc:retained-products.family`,
sparse-cones.tex:150–155,194–207. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_zero_tangent_dimension {d : ℕ}
    (V : AffineVariety (d + d)) (hV : V.IsIrreducible)
    (p : Point (d + d)) (hp : p ∈ V) (hT : V.tangentSpace p = ⊥) :
    V.dimension = 0 := by
  classical
  have hle := DistinctDistances.TrackD.tangent_finrank_ge_dimension V hV p hp
  rw [hT] at hle
  have hfr0 : Module.finrank ℂ ↥(⊥ : Submodule ℂ (Point (d + d))) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hfr0] at hle
  exact Nat.le_zero.mp hle

theorem common_quadratic_section_isolated {d k : ℕ}
    (V : AffineVariety (d + d)) (hV : V.IsIrreducible)
    (E : Fin (2 * k) → Poly (d + d)) (hdegree : ∀ a, (E a).totalDegree ≤ 2)
    (p : Point (d + d)) (hp : p ∈ V)
    (hzero : ∀ a, MvPolynomial.eval p (E a) = 0)
    (hinj : Function.Injective
      ((LinearMap.pi (fun a => differential (E a) p)).domRestrict
        (V.tangentSpace p))) :
    pointIdeal p ∈ (V.ideal ⊔ Ideal.span (Set.range E)).minimalPrimes := by
  classical
  -- The combined ideal vanishes at `p`.
  have hJle : V.ideal ⊔ Ideal.span (Set.range E) ≤ pointIdeal p := by
    apply sup_le
    · intro f hf
      have hpPoints : p ∈ V.points := hp
      have hvan : (MvPolynomial.aeval p) f = 0 :=
        (MvPolynomial.mem_zeroLocus_iff.mp hpPoints) f hf
      show f ∈ MvPolynomial.vanishingIdeal ℂ ({p} : Set (Point (d + d)))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact hvan
    · apply Ideal.span_le.mpr
      rintro f ⟨a, rfl⟩
      show E a ∈ MvPolynomial.vanishingIdeal ℂ ({p} : Set (Point (d + d)))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simpa [MvPolynomial.aeval_eq_eval] using hzero a
  haveI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le hJle
  have hVP : V.ideal ≤ P := le_sup_left.trans hPmin.le
  have hEP : Ideal.span (Set.range E) ≤ P := le_sup_right.trans hPmin.le
  let W : AffineVariety (d + d) := ⟨P, hPmin.isPrime.isRadical⟩
  have hWideal : W.ideal = P := rfl
  have hWirr : W.IsIrreducible := hPmin.isPrime
  have hpW : p ∈ W := by
    show p ∈ W.points
    show p ∈ MvPolynomial.zeroLocus ℂ P
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro f hf
    have hmem : f ∈ pointIdeal p := hPle hf
    have hvan := (MvPolynomial.mem_vanishingIdeal_singleton_iff p f).mp hmem
    simpa using hvan
  have hT : W.tangentSpace p = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hvV : v ∈ V.tangentSpace p := by
      simp only [AffineVariety.tangentSpace, Submodule.mem_iInf,
        LinearMap.mem_ker] at hv ⊢
      intro f
      have hfP : f.val ∈ P := hVP f.property
      have hmem := hv ⟨f.val, hfP⟩
      simpa only [LinearMap.mem_ker] using hmem
    have hEvan : ∀ a, differential (E a) p v = 0 := by
      intro a
      have hEaP : E a ∈ P := hEP (Ideal.subset_span ⟨a, rfl⟩)
      have hmem := (Submodule.mem_iInf _).mp hv ⟨E a, hEaP⟩
      simpa only [LinearMap.mem_ker] using hmem
    have hpi : (LinearMap.pi (fun a => differential (E a) p)) v = 0 := by
      funext a
      simp only [LinearMap.pi_apply, hEvan, Pi.zero_apply]
    have hdom : ((LinearMap.pi (fun a => differential (E a) p)).domRestrict
        (V.tangentSpace p)) ⟨v, hvV⟩ =
        ((LinearMap.pi (fun a => differential (E a) p)).domRestrict
          (V.tangentSpace p)) ⟨0, Submodule.zero_mem _⟩ := by
      simp only [LinearMap.domRestrict_apply, hpi, map_zero]
    have heq := hinj hdom
    exact congrArg Subtype.val heq
  have hdim : W.dimension = 0 := common_zero_tangent_dimension W hWirr p hpW hT
  haveI : P.IsPrime := hPmin.isPrime
  have hPdim : OAI.QuarticPowerFree.affineDimension P = 0 := by
    simpa [hWideal, AffineVariety.dimension] using hdim
  have hPmax : P.IsMaximal := OAI.QuarticPowerFree.zeroDim_isMaximal P hPdim
  have hPeq : P = pointIdeal p :=
    hPmax.eq_of_le (pointIdeal_isMaximal p).ne_top hPle
  rw [← hPeq]
  exact hPmin

end
end DistinctDistances.SparseCones
