import DistinctDistances.Bridges.RealCoprimality
import DistinctDistances.Bridges.RealLineLift
import DistinctDistances.Bridges.CurveComponents
import DistinctDistances.Bridges.Hypersurfaces

/-! A real common line becomes a minimal-prime component of the complex intersection. -/

namespace DistinctDistances.Bridges

open UniqueFactorizationMonoid
noncomputable section

theorem prime_divisor_mem (P : Ideal (Poly 3)) (hP : P.IsPrime) (f : Poly 3)
    (hf : f ≠ 0) (hmem : f ∈ P) : ∃ p : Poly 3, Prime p ∧ p ∣ f ∧ p ∈ P := by
  classical
  let : StrongNormalizationMonoid (Poly 3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  have hprod : (normalizedFactors f).prod ∈ P :=
    P.mem_of_dvd (prod_normalizedFactors hf).symm.dvd hmem
  obtain ⟨p, hpf, hpP⟩ := (hP.multiset_prod_mem_iff_exists_mem (normalizedFactors f)).mp hprod
  exact ⟨p, prime_of_normalized_factor p hpf, dvd_of_mem_normalizedFactors hpf, hpP⟩

theorem complex_common_line_component (f g : Poly 3) (hf : f ≠ 0)
    (hcop : IsRelPrime f g) (l : TrackC.Line 3)
    (hfl : f ∈ (realLineLift l).ideal) (hgl : g ∈ (realLineLift l).ideal) :
    (realLineLift l).IsComponentOf (Ideal.span {f, g}) := by
  classical
  let V := realLineLift l
  let : V.ideal.IsPrime := realLineLift_irreducible l
  have hIV : Ideal.span ({f, g} : Set (Poly 3)) ≤ V.ideal :=
    Ideal.span_le.mpr (Set.pair_subset_iff.mpr ⟨hfl, hgl⟩)
  obtain ⟨R, hR, hRV⟩ := Ideal.exists_minimalPrimes_le hIV
  let : R.IsPrime := hR.isPrime
  have hfR : f ∈ R := hR.le (Ideal.subset_span (by simp))
  have hgR : g ∈ R := hR.le (Ideal.subset_span (by simp))
  obtain ⟨p, hp, hpf, hpR⟩ := prime_divisor_mem R hR.isPrime f hf hfR
  let hpideal : (Ideal.span {p}).IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  let X := primeHypersurface p hpideal
  have hX : X.IsIrreducible := hpideal
  have hXdim : X.dimension = 2 := primeHypersurface_dimension p hpideal hp.ne_zero
    (totalDegree_pos_of_not_isUnit p hp.ne_zero hp.not_isUnit)
  have hgX : g ∉ X.ideal := by
    intro hgP
    exact hp.not_isUnit (hcop hpf (Ideal.mem_span_singleton.mp hgP))
  have hcutR : X.ideal ⊔ Ideal.span {g} ≤ R :=
    sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpR))
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgR))
  obtain ⟨Q, hQ, hQR⟩ := Ideal.exists_minimalPrimes_le hcutR
  let Y : AffineVariety 3 := ⟨Q, hQ.isPrime.isRadical⟩
  have hY : Y.IsIrreducible := hQ.isPrime
  have hYdim : Y.dimension = 1 :=
    TrackA.fa_bezout_proper_dimension X Y hX g hgX hQ 1 hXdim
  have hYV : Y = V := curve_eq_of_infinite_subvariety Y V hY hYdim
    (realLineLift_irreducible l) (hQR.trans hRV) (realLineLift_points_infinite l)
  have hQV : Q = V.ideal := congrArg AffineVariety.ideal hYV
  have hRVeq : R = V.ideal := le_antisymm hRV (hQV ▸ hQR)
  change V.ideal ∈ (Ideal.span {f, g}).minimalPrimes
  rw [← hRVeq]
  exact hR

theorem real_common_line_components (f g : TrackC.Poly 3) (hf : f ≠ 0) (_hg : g ≠ 0)
    (hcop : IsRelPrime f g) :
    ∃ lift : TrackC.Line 3 → AffineVariety 3, Function.Injective lift ∧
      ∀ l : TrackC.Line 3, TrackC.onPolynomial f l → TrackC.onPolynomial g l →
        (lift l).IsComponentOf (Ideal.span
          {MvPolynomial.map (algebraMap ℝ ℂ) f, MvPolynomial.map (algebraMap ℝ ℂ) g}) ∧
        (lift l).dimension = 1 ∧ (lift l).degree = 1 := by
  refine ⟨realLineLift, realLineLift_injective, ?_⟩
  intro l hfl hgl
  have hmapinj : Function.Injective
      (MvPolynomial.map (algebraMap ℝ ℂ) : TrackC.Poly 3 → Poly 3) :=
    MvPolynomial.map_injective _ Complex.ofReal_injective
  have hfmap : MvPolynomial.map (algebraMap ℝ ℂ) f ≠ 0 :=
    fun hz => hf (hmapinj (hz.trans (map_zero _).symm))
  exact ⟨complex_common_line_component _ _ hfmap (real_coprimality f g hcop) l
      (realLineLift_onPolynomial l f hfl) (realLineLift_onPolynomial l g hgl),
    realLineLift_dimension_degree l⟩

end
end DistinctDistances.Bridges
