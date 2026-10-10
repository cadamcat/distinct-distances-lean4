import DistinctDistances.TrackB.UniformCompletion
import DistinctDistances.TrackB.AffineFlatGeometry
import DistinctDistances.Bridges.AmbientHilbert
import Mathlib.Algebra.MvPolynomial.Funext

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

theorem contained_count_components_le {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (hP : ∀ p ∈ P, p ∈ affineParameters e)
    (V : AffineVariety (skewDim e)) :
    containedFlatCount C P V ≤ ∑ W : V.Component, containedFlatCount C P W.variety := by
  classical
  let F : V.Component → Finset (ProjectivePoint (e + e)) :=
    fun W => P.filter (fun p => evaluationFlat C p ⊆ W.variety.points)
  have hsub : (P.filter (fun p => evaluationFlat C p ⊆ V.points)) ⊆
      Finset.univ.biUnion F := by
    intro p hp
    obtain ⟨hpP, hpV⟩ := Finset.mem_filter.mp hp
    obtain ⟨W, hW⟩ := evaluationFlat_in_component C p (hP p hpP) V hpV
    exact Finset.mem_biUnion.mpr ⟨W, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hpP, hW⟩⟩
  have hcard (S : Finset V.Component) : (S.biUnion F).card ≤ ∑ W ∈ S, (F W).card := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert W S hWS ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hWS]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)
  exact (Finset.card_le_card hsub).trans (hcard Finset.univ)


#print axioms evaluationFlat_vanishingIdeal_prime
#print axioms contained_count_components_le
end
end DistinctDistances.TrackB
