import DistinctDistances.TrackE.RequestsStar
import DistinctDistances.TrackE.MReqAux

/-! Shared-model containment and dimension rigidity consumed by
`sc:separated-rank`, sparse-cones.tex:732–751. -/
namespace DistinctDistances.Request
open scoped Classical
noncomputable section

/-- Track A, `FA.model`: an irreducible subvariety of a finite irreducible
cover lies in one member. Inclusion preserves dimension, and equality of
dimensions forces equality of these two irreducible varieties. -/
theorem projective_irreducible_container {d : ℕ} (V : ProjectiveVariety d)
    (F : ProjectiveFamily.Family d) (hF : ∀ C ∈ F, C.IsIrreducible)
    (hlocus : ProjectiveFamily.locus F = V) (W : ProjectiveVariety d)
    (hW : W.IsIrreducible) (hWV : W.Subvariety V) :
    ∃ C ∈ F, W.Subvariety C ∧ W.dimension ≤ C.dimension ∧
      (W.dimension = C.dimension → W = C) := by
  classical
  have hWV' : V.ideal ≤ W.ideal := hWV
  have hInfV : (⨅ C ∈ F, C.ideal) ≤ V.ideal := by
    rw [← hlocus]
    exact MReqAux.projective_biInf_le_locus F
  have hInfW : (⨅ C ∈ F, C.ideal) ≤ W.ideal := hInfV.trans hWV'
  obtain ⟨C, hCF, hCW⟩ := MReqAux.exists_projective_ideal_le_of_biInf_le F W hW hInfW
  have hWC : W.Subvariety C := hCW
  have hCne := ProjectiveFamily.irreducible_points_nonempty C (hF C hCF)
  have hWne := ProjectiveFamily.irreducible_points_nonempty W hW
  have hconeW := ProjectiveVariety.dimension_cone W hWne
  have hconeC := ProjectiveVariety.dimension_cone C hCne
  have hmono := MReqAux.projective_cone_dimension_mono C W hCW
  have hdim : W.dimension ≤ C.dimension := by omega
  refine ⟨C, hCF, hWC, hdim, ?_⟩
  intro heq
  have hcone_eq : (W.affineCone).dimension = (C.affineCone).dimension := by omega
  have hI := MReqAux.projective_ideal_eq_of_cone_dim_eq C W (hF C hCF) hW hCW hcone_eq
  exact ProjectiveVariety.ext hI.symm

end
end DistinctDistances.Request
