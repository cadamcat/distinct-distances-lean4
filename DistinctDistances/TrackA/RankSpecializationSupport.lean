import DistinctDistances.TrackA.Definitions

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- A matrix over an integral carrier has at least as much rank at its
generic point as at any complex point. The residue point can be singular. -/
theorem rank_at_point_le_generic {R K : Type*} [CommRing R] [Field K]
    [Algebra ℂ R] [Algebra ℂ K] (φ : R →ₐ[ℂ] ℂ) (ψ : R →ₐ[ℂ] K)
    (hψ : Function.Injective ψ) {a : ℕ} (M : Matrix (Fin a) (Fin a) R) :
    (M.map φ).rank ≤ (M.map ψ).rank := by
  obtain ⟨V, U, e, _, _, hnormal⟩ := Matrix.exists_rank_normal_form (M.map φ)
  let r := (M.map φ).rank
  let rows : Fin r → Fin a := fun i => e.symm (Sum.inl i)
  let N : Matrix (Fin a) (Fin a) R :=
    V.map (algebraMap ℂ R) * M * U.map (algebraMap ℂ R)
  let P : Matrix (Fin r) (Fin r) R := N.submatrix rows rows
  have hV : (V.map (algebraMap ℂ R)).map φ = V := by
    ext i j
    simp [Matrix.map_apply, φ.commutes]
  have hU : (U.map (algebraMap ℂ R)).map φ = U := by
    ext i j
    simp [Matrix.map_apply, φ.commutes]
  have hN : N.map φ = V * M.map φ * U := by
    simp only [N, Matrix.map_mul, hV, hU]
  have hP : P.map φ = 1 := by
    change (N.map φ).submatrix rows rows = 1
    rw [hN, hnormal]
    ext i j
    simp [rows, Matrix.submatrix, Matrix.fromBlocks, Matrix.one_apply]
  have hdet : φ P.det = 1 := by
    change φ.toRingHom P.det = 1
    rw [RingHom.map_det φ.toRingHom P]
    change (P.map φ).det = 1
    rw [hP, Matrix.det_one]
  have hP0 : P.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdet
    exact zero_ne_one hdet
  have hψP : (P.map ψ).det ≠ 0 := by
    change (ψ.toRingHom.mapMatrix P).det ≠ 0
    rw [← RingHom.map_det]
    exact fun h => hP0 (hψ (h.trans (map_zero ψ).symm))
  calc
    (M.map φ).rank = (P.map ψ).rank := by
      rw [Matrix.rank_of_det_ne_zero hψP, Fintype.card_fin]
    _ ≤ (N.map ψ).rank := Matrix.rank_submatrix_le (N.map ψ) rows rows
    _ ≤ (M.map ψ).rank := by
      simp only [N, Matrix.map_mul]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end
end DistinctDistances.TrackA
