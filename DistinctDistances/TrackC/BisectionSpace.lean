import DistinctDistances.TrackC.Basic
import OAI.NumberTheory.PowerFree.HilbertGrowth

namespace DistinctDistances.TrackC

/-- The coefficient sphere needed for simultaneous bisection embeds in the
bounded-degree polynomial space. Degree count is imported from OAI. -/
theorem bisection_polynomial_embedding (d m D : ℕ) (h : m < Nat.choose (D+d) d) :
    ∃ F : E (m+1) →ₗ[ℝ] Poly d, Function.Injective F ∧
      ∀ c : E (m+1), (F c).totalDegree ≤ D := by
  classical
  let V := OAI.QuarticPowerFree.totalSpace (σ := Fin d) (K := ℝ) D
  letI : Module.Finite ℝ V := OAI.QuarticPowerFree.totalSpace_finite D
  have hV : Module.finrank ℝ V = Nat.choose (D+d) d :=
    OAI.QuarticPowerFree.totalSpace_finrank D
  have hdim : Module.finrank ℝ (E (m+1)) ≤ Module.finrank ℝ V := by
    rw [hV]
    simpa using Nat.succ_le_of_lt h
  obtain ⟨F, hF⟩ := (finrank_le_iff_exists_linearMap.mp hdim)
  refine ⟨V.subtype.comp F, Subtype.val_injective.comp hF, ?_⟩
  intro c
  exact OAI.QuarticPowerFree.mem_totalSpace.mp (F c).property

end DistinctDistances.TrackC
