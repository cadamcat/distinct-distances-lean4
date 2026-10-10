import DistinctDistances.TrackA.PolarAlgebraSupport
import DistinctDistances.TrackA.DerivationOrderSupport
import DistinctDistances.OAIInterface.ChartGradients

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

theorem chartPullback_pderiv (i : Fin 3) (f : Poly 3) (j : Fin 2) :
    chartPullback i (MvPolynomial.pderiv (i.succAbove j) f) =
      MvPolynomial.pderiv j (chartPullback i f) := by
  simpa only [chartPullback, MvPolynomial.aeval_def, OAI.Nagata.W27.directChartHom,
    MvPolynomial.algebraMap_eq, MvPolynomial.coe_eval₂Hom, map_one]
    using (OAI.Nagata.Workers.W25.pderiv_directChartHom i f j).symm

/-- Euler's identity handles the omitted chart partial; surviving partials
are ordinary derivatives and lose at most one order. -/
theorem firstPolar_chart_order (f : Poly 3) (d : ℕ) (hf : f.IsHomogeneous d)
    (w : Fin 3 → ℂ) (i : Fin 3) (p : Point 2) (r : ℕ)
    (horder : OrderAtLeast (chartPullback i f) p r) :
    OrderAtLeast (chartPullback i (firstPolar f w)) p (r-1) := by
  cases r with
  | zero => simp [OrderAtLeast]
  | succ r =>
    let I := pointIdealOver p ^ r
    have hsurviving (j : Fin 2) :
        chartPullback i (MvPolynomial.pderiv (i.succAbove j) f) ∈ I := by
      rw [chartPullback_pderiv]
      exact pderiv_order_drop _ p (r+1) horder j
    have hEuler := congrArg (chartPullback i) hf.sum_X_mul_pderiv
    simp only [map_sum, map_mul, map_nsmul] at hEuler
    rw [Fin.sum_univ_succAbove _ i] at hEuler
    have hX : chartPullback i (MvPolynomial.X i) = 1 := by simp [chartPullback]
    rw [hX, one_mul] at hEuler
    have hsum : (∑ j : Fin 2, chartPullback i (MvPolynomial.X (i.succAbove j)) *
        chartPullback i (MvPolynomial.pderiv (i.succAbove j) f)) ∈ I := by
      exact Ideal.sum_mem _ (fun j hj => Ideal.mul_mem_left _ _ (hsurviving j))
    have hfmem : chartPullback i f ∈ I :=
      Ideal.pow_le_pow_right (Nat.le_succ r) horder
    have homitted : chartPullback i (MvPolynomial.pderiv i f) ∈ I := by
      have htotal : chartPullback i (MvPolynomial.pderiv i f) +
          (∑ j : Fin 2, chartPullback i (MvPolynomial.X (i.succAbove j)) *
            chartPullback i (MvPolynomial.pderiv (i.succAbove j) f)) ∈ I := by
        rw [hEuler]
        exact I.nsmul_mem hfmem d
      have hdiff := I.sub_mem htotal hsum
      simpa only [add_sub_cancel_right] using hdiff
    change chartPullback i (∑ j, w j • MvPolynomial.pderiv j f) ∈ I
    rw [map_sum]
    apply Ideal.sum_mem
    intro j hj
    rw [map_smul]
    apply (I.restrictScalars ℂ).smul_mem
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
    · exact homitted
    · exact hsurviving a

end
end DistinctDistances.TrackA
