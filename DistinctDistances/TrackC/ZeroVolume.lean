import DistinctDistances.TrackC.Basic

open MeasureTheory
open scoped BigOperators

namespace DistinctDistances.TrackC

/-- The coordinate-product form of CI:113–115. -/
theorem polynomial_pi_zero_volume (d : ℕ) (f : Poly d) (hf : f ≠ 0) :
    volume {x : Fin d → ℝ | MvPolynomial.eval x f = 0} = 0 := by
  classical
  induction d with
  | zero =>
    have hconst := MvPolynomial.eq_C_of_isEmpty f
    have hc : f.coeff 0 ≠ 0 := by
      intro h
      apply hf
      rw [hconst, h]
      simp
    have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x f = 0} = ∅ := by
      ext x
      change MvPolynomial.eval x f = 0 ↔ False
      rw [hconst, MvPolynomial.eval_C]
      exact iff_false_intro hc
    rw [hempty]
    simp
  | succ d ih =>
    let p := MvPolynomial.finSuccEquiv ℝ d f
    have hp : p ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℝ d).injective (by simpa [p] using h)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, p.coeff k ≠ 0 := by
      by_contra! h
      apply hp
      apply Polynomial.ext
      intro i
      simpa only [Polynomial.coeff_zero] using h i
    have hae : ∀ᵐ x : Fin d → ℝ ∂volume, MvPolynomial.eval x (p.coeff k) ≠ 0 := by
      apply ae_iff.mpr
      simpa using ih (p.coeff k) hk
    let S : Set ((Fin d → ℝ) × ℝ) :=
      {u | MvPolynomial.eval (Fin.cons u.2 u.1) f = 0}
    have hcont : Continuous (fun u : (Fin d → ℝ) × ℝ =>
        MvPolynomial.eval (Fin.cons u.2 u.1) f) := by
      apply (MvPolynomial.continuous_eval f).comp
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_snd
      · simpa only [Fin.cons_succ, Function.comp_def] using
          (continuous_apply j).comp continuous_fst
    have hSm : MeasurableSet S := (isClosed_eq hcont continuous_const).measurableSet
    have hS : volume S = 0 := by
      apply Measure.measure_prod_null_of_ae_null hSm
      filter_upwards [hae] with x hx
      let q : Polynomial ℝ := Polynomial.map (MvPolynomial.eval x) p
      have hq : q ≠ 0 := by
        intro h
        have he := congrArg (fun r : Polynomial ℝ => r.coeff k) h
        apply hx
        simpa [q, Polynomial.coeff_map] using he
      have hsection : Prod.mk x ⁻¹' S = {t : ℝ | q.eval t = 0} := by
        ext t
        simp [S, q, p, MvPolynomial.eval_eq_eval_mv_eval']
      rw [hsection]
      exact (Polynomial.finite_setOfPred_isRoot hq).measure_zero volume
    have hsplit := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have hswap : MeasurePreserving (Prod.swap : ℝ × (Fin d → ℝ) → (Fin d → ℝ) × ℝ) :=
      Measure.measurePreserving_swap
    have hnull := (hswap.comp hsplit).quasiMeasurePreserving.preimage_null hS
    simpa [S, MeasurableEquiv.piFinSuccAbove] using hnull

/-- Transfer coordinate-product volume to the Euclidean norm model. -/
theorem polynomial_euclidean_zero_volume (d : ℕ) (f : Poly d) (hf : f ≠ 0) :
    volume (zeroSet f) = 0 := by
  have h := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.preimage_null
    (polynomial_pi_zero_volume d f hf)
  simpa [zeroSet, evalR] using h

end DistinctDistances.TrackC
