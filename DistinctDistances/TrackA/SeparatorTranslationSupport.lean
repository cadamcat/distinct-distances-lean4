import DistinctDistances.Foundations.PointLocal
import DistinctDistances.OAIInterface.PointParameters

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
open MvPolynomial OAI.PiExponent.WeightedBezout

theorem separator_translation_eval {F : Type*} [Field F] {c : ℕ}
    (z y : FieldPoint c F) (p : FieldPoly c F) :
    eval y (translationEquiv z p) = eval (z+y) p := by
  have h : (eval y).comp (translationEquiv z).toRingHom = eval (z+y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change eval y (translationEquiv z (C a)) = eval (z+y) (C a)
      simp [translationEquiv, translation]
    · intro i
      change eval y (translationEquiv z (X i)) = eval (z+y) (X i)
      simp [translationEquiv, translation, Pi.add_apply]
  exact RingHom.congr_fun h p

theorem separator_translation_degree {F : Type*} [Field F] {c : ℕ}
    (z : FieldPoint c F) (p : FieldPoly c F) :
    (translationEquiv z p).totalDegree ≤ p.totalDegree := by
  have hg (i : Fin c) : (C (z i)+X i : FieldPoly c F).totalDegree ≤ 1 := by
    simpa only [totalDegree_C, totalDegree_X, Nat.zero_max] using totalDegree_add (C (z i)) (X i)
  simpa only [translationEquiv, AlgEquiv.ofAlgHom_apply, translation, weightedTotalDegree_one]
    using totalDegree_aeval_le_weighted (1 : Fin c → ℕ) (fun i => C (z i)+X i) hg p

theorem separator_translation_pointIdeal {F : Type*} [Field F] {c : ℕ}
    (z : FieldPoint c F) :
    (pointIdealOver z).map (translationEquiv z).toRingHom = pointIdealOver (0 : FieldPoint c F) := by
  have hcomap : (pointIdealOver (0 : FieldPoint c F)).comap
      (translationEquiv z).toRingHom = pointIdealOver z := by
    ext p
    simp only [Ideal.mem_comap, pointIdealOver, mem_vanishingIdeal_singleton_iff]
    simp only [MvPolynomial.aeval_eq_eval]
    change eval 0 (translationEquiv z p) = 0 ↔ eval z p = 0
    rw [separator_translation_eval, add_zero]
  rw [← hcomap]
  have hsurj : Function.Surjective (translationEquiv z).toRingHom := (translationEquiv z).surjective
  exact Ideal.map_comap_of_surjective (translationEquiv z).toRingHom hsurj _

theorem separator_translation_minimal {F : Type*} [Field F] {c : ℕ}
    (z : FieldPoint c F) (E : Set (FieldPoly c F))
    (hmin : pointIdealOver z ∈ (Ideal.span E).minimalPrimes) :
    pointIdealOver (0 : FieldPoint c F) ∈
      (Ideal.span ((translationEquiv z) '' E)).minimalPrimes := by
  rw [← separator_translation_pointIdeal z, ← Ideal.map_span]
  change (pointIdealOver z).map (translationEquiv z).toRingHom ∈
    ((Ideal.span E).map (translationEquiv z).toRingHom).minimalPrimes
  have hsurj : Function.Surjective (translationEquiv z).toRingHom := (translationEquiv z).surjective
  rw [Ideal.minimalPrimes_map_of_surjective hsurj]
  have hker : RingHom.ker (translationEquiv z).toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot (translationEquiv z).toRingHom).mp (translationEquiv z).injective
  simp only [hker, sup_bot_eq]
  exact Set.mem_image_of_mem _ hmin

end
end DistinctDistances.TrackA
