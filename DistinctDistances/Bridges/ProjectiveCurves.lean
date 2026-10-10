import DistinctDistances.Bridges.Homogenization
import DistinctDistances.Bridges.CurveInvariants
import Mathlib.RingTheory.GradedAlgebra.Radical

/-! The distinguished affine chart of projective closure preserves curve multiplicity. -/

namespace DistinctDistances.Bridges
open scoped Classical
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

 theorem affineVector_ne_zero {n : ℕ} (x : Point n) : Fin.cons 1 x ≠ (0 : Point (n+1)) := by
  intro hz
  have h := congrFun hz 0
  simpa using h

 theorem affineEmbedding_injective {n : ℕ} :
    Function.Injective (affineEmbedding : Point n → ProjectivePoint (n+1)) := by
  intro x y h
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _
    (affineVector_ne_zero x) (affineVector_ne_zero y)).mp h
  change (c : ℂ) • Fin.cons 1 y = Fin.cons 1 x at hc
  have h0 := congrFun hc 0
  have hc1 : (c : ℂ) = 1 := by simpa using h0
  funext i
  have hi := congrFun hc i.succ
  simpa [hc1] using hi.symm

 theorem affineEmbedding_rep_zero_ne {n : ℕ} (x : Point n) :
    (affineEmbedding x).rep 0 ≠ 0 := by
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (Fin.cons 1 x : Point (n+1)) (affineVector_ne_zero x)
  change (c : ℂ) • Fin.cons 1 x = (affineEmbedding x).rep at hc
  have he : (affineEmbedding x).rep 0 = (c : ℂ) := by
    rw [← hc]
    simp
  rw [he]
  exact Units.ne_zero c

 theorem chartCoordinates_affineEmbedding {n : ℕ} (x : Point n) :
    chartCoordinates 0 (affineEmbedding x) = x := by
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (Fin.cons 1 x : Point (n+1)) (affineVector_ne_zero x)
  change (c : ℂ) • Fin.cons 1 x = (affineEmbedding x).rep at hc
  funext i
  simp [chartCoordinates, ← hc, Units.ne_zero c]

 theorem homogeneous_mem_projectiveClosure_iff {n D : ℕ} (Y : AffineVariety n)
    (f : Poly (n+1)) (hf : f.IsHomogeneous D) :
    f ∈ (projectiveClosure Y).ideal ↔ chartPullback 0 f ∈ Y.ideal := by
  rw [← Y.vanishingIdeal_points]
  constructor
  · intro h x hx
    change MvPolynomial.eval x (chartPullback 0 f) = 0
    rw [eval_chartPullback_zero]
    exact h (Fin.cons 1 x) ⟨affineVector_ne_zero x, x,hx,rfl⟩
  · intro h v hv
    obtain ⟨hv,x,hx,he⟩ := hv
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ hv
      (affineVector_ne_zero x)).mp he.symm
    change (c : ℂ) • Fin.cons 1 x = v at hc
    have hz : MvPolynomial.eval (Fin.cons 1 x) f = 0 := by
      rw [← eval_chartPullback_zero]
      exact h x hx
    change MvPolynomial.eval v f = 0
    rw [← hc, homogeneous_eval_smul f hf, hz, mul_zero]

 theorem projectiveClosure_chart_zero {n : ℕ} (Y : AffineVariety n) :
    (projectiveClosure Y).affineChart 0 = Y := by
  have hi : (projectiveClosure Y).ideal.map (chartPullback 0).toRingHom = Y.ideal := by
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      intro f hf
      rw [← Y.vanishingIdeal_points]
      intro x hx
      change MvPolynomial.eval x (chartPullback 0 f) = 0
      rw [eval_chartPullback_zero]
      exact hf (Fin.cons 1 x) ⟨affineVector_ne_zero x,x,hx,rfl⟩
    · intro f hf
      rw [← chartPullback_homogenize f]
      apply Ideal.mem_map_of_mem
      exact (homogeneous_mem_projectiveClosure_iff Y (homogenize f)
        (homogenize_homogeneous f)).mpr (by rw [chartPullback_homogenize]; exact hf)
  apply AffineVariety.ext
  change ((projectiveClosure Y).ideal.map (chartPullback 0).toRingHom).radical = Y.ideal
  rw [hi, Y.isRadical.radical]

 theorem projectiveClosure_irreducible {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) : (projectiveClosure Y).IsIrreducible := by
  apply (projectiveClosure Y).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
  · intro htop
    have hchart : (projectiveClosure Y).affineChart 0 = AffineVariety.empty := by
      apply AffineVariety.ext
      simp [ProjectiveVariety.affineChart, AffineVariety.ofIdeal, htop,
        AffineVariety.empty, Ideal.map_top, Ideal.radical_top]
    have he : Y.ideal = ⊤ := by
      rw [projectiveClosure_chart_zero] at hchart
      have hi := congrArg AffineVariety.ideal hchart
      simpa [AffineVariety.empty, AffineVariety.ofIdeal, Ideal.radical_top] using hi
    exact hY.ne_top he
  · rintro f g ⟨D,hf⟩ ⟨E,hg⟩ hfg
    have hfg' : chartPullback 0 f * chartPullback 0 g ∈ Y.ideal := by
      rw [← map_mul]
      exact (homogeneous_mem_projectiveClosure_iff Y (f*g) (hf.mul hg)).mp hfg
    rcases hY.mem_or_mem hfg' with h | h
    · exact Or.inl ((homogeneous_mem_projectiveClosure_iff Y f hf).mpr h)
    · exact Or.inr ((homogeneous_mem_projectiveClosure_iff Y g hg).mpr h)

 theorem projective_irreducible_isPure {n : ℕ} (Y : ProjectiveVariety n)
    (hY : Y.IsIrreducible) : Y.IsPure Y.dimension := by
  letI : Y.ideal.IsPrime := hY
  intro W
  have hi : W.val.ideal = Y.ideal := by
    have hw := W.property
    change W.val.ideal ∈ Y.ideal.minimalPrimes at hw
    simpa only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
      using hw
  rw [ProjectiveVariety.ext hi]

 theorem projectiveClosure_multiplicity {n : ℕ} (Y : AffineVariety n) (p : Point n) :
    (projectiveClosure Y).multiplicity (affineEmbedding p) = Y.multiplicity p := by
  rw [(projectiveClosure Y).multiplicity_chart (affineEmbedding p) 0
    (affineEmbedding_rep_zero_ne p), projectiveClosure_chart_zero,
    chartCoordinates_affineEmbedding]

end
end DistinctDistances.Bridges
