import DistinctDistances.OAIInterface.DistanceEnergy
import DistinctDistances.TrackE.Basic

/-!
# Radius-class collision energy, including a zero distance

`reduction.tex:155–160`. OAI's energy theorem counts nonzero physical distances.
Erase a possible copy of the center from the representative set, apply that theorem,
and put the diagonal back explicitly. The resulting bound uses the paper's
`M = 1 + count` convention and counts ordered distinct pairs.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

open Classical in
def pointDistancePairs (Z : Finset (RPoint d)) (q : RPoint d) :
    Finset (RPoint d × RPoint d) :=
  Z.offDiag.filter fun e => dist q e.1 = dist q e.2

/-- Arithmetic for the one possible zero-distance representative. -/
theorem collision_bound_of_energy_with_one_missing (L K E M : ℝ)
    (hM : 1 < M) (hL : 2 * M ≤ L) (hK₀ : 0 ≤ K)
    (hK : L - 1 ≤ K) (hKL : K ≤ L)
    (henergy : K ^ 2 ≤ (M - 1) * (E + K)) :
    L ^ 2 / (2 * M) ≤ E := by
  have hL₀ : 0 ≤ L - 1 := by linarith
  have hfirst : (L - 1) ^ 2 ≤ (M - 1) * (E + L) := by
    calc
      _ ≤ K ^ 2 := (sq_le_sq₀ hL₀ hK₀).mpr hK
      _ ≤ (M - 1) * (E + K) := henergy
      _ ≤ (M - 1) * (E + L) :=
        mul_le_mul_of_nonneg_left (by linarith : E + K ≤ E + L) (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hfirst (by linarith : 0 ≤ 2 * M)
  have hshift : 0 ≤ (M + 1) * L * (L - 2 * M) := by
    apply mul_nonneg
    · apply mul_nonneg <;> linarith
    · linarith
  apply (div_le_iff₀ (by linarith : 0 < 2 * M)).mpr
  apply (mul_le_mul_iff_left₀ (by linarith : 0 < M - 1)).mp
  nlinarith [hscaled, hshift]

open Classical in
/-- Erasing the center leaves all ordered distinct equal-distance pairs unchanged. -/
theorem pointDistancePairs_erase (Z : Finset (RPoint d)) (q : RPoint d) :
    pointDistancePairs (Z.erase q) q = pointDistancePairs Z q := by
  classical
  ext e
  simp only [pointDistancePairs, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_erase]
  constructor
  · tauto
  · rintro ⟨⟨h₁, h₂, hne⟩, heq⟩
    have h₁q : e.1 ≠ q := by
      intro h
      have hz : dist q e.2 = 0 := by simpa [h] using heq.symm
      exact hne (h.trans (dist_eq_zero.mp hz))
    have h₂q : e.2 ≠ q := by
      intro h
      have hz : dist q e.1 = 0 := by simpa [h] using heq
      exact hne ((dist_eq_zero.mp hz).symm.trans h.symm)
    exact ⟨⟨⟨h₁q, h₁⟩, ⟨h₂q, h₂⟩, hne⟩, heq⟩

open Classical in
/-- Reindex OAI's equal-length energy for pairs `(q,z)` by their second coordinates,
then separate the diagonal. -/
theorem equalLengthPairs_star_card (Z : Finset (RPoint d)) (q : RPoint d) :
    (OAI.ErdosDistinctDistances.equalLengthPairs ((Z.erase q).image fun z => (q, z))).card =
      (pointDistancePairs Z q).card + (Z.erase q).card := by
  classical
  let U := Z.erase q
  let F := (U ×ˢ U).filter fun e => dist q e.1 = dist q e.2
  have himage : OAI.ErdosDistinctDistances.equalLengthPairs (U.image fun z => (q, z)) =
      F.image (fun e => ((q, e.1), (q, e.2))) := by
    ext e
    simp only [OAI.ErdosDistinctDistances.equalLengthPairs, F, Finset.mem_filter,
      Finset.mem_product, Finset.mem_image]
    aesop
  have hinj : Function.Injective (fun e : RPoint d × RPoint d => ((q, e.1), (q, e.2))) := by
    intro e e' h
    exact Prod.ext (congrArg (fun a => a.1.2) h) (congrArg (fun a => a.2.2) h)
  have hneq : (F.filter fun e => e.1 ≠ e.2) = pointDistancePairs U q := by
    ext e
    simp only [F, pointDistancePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
    tauto
  have heq : (F.filter fun e => ¬ e.1 ≠ e.2) = U.diag := by
    ext e
    simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_diag, not_not]
    aesop
  rw [himage, Finset.card_image_of_injective _ hinj]
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun e => e.1 ≠ e.2)
  rw [hneq, heq, Finset.diag_card, pointDistancePairs_erase] at hsplit
  exact hsplit.symm

open Classical in
/-- `red:directions.energy` (`reduction.tex:155–160`): an `L ≥ 2M`-point representative
set supplies at least `L²/(2M)` equal-distance ordered distinct pairs for every sample point. -/
theorem pointDistancePairs_lower_bound (P Z : Finset (RPoint d)) (q : RPoint d)
    (hZ : Z ⊆ P) (hq : q ∈ P) (hlarge : 2 * Mcount P ≤ (Z.card : ℝ)) :
    (Z.card : ℝ) ^ 2 / (2 * Mcount P) ≤ (pointDistancePairs Z q).card := by
  classical
  let S := (Z.erase q).image fun z => (q, z)
  have hS : S ⊆ P.offDiag := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hzq, hzZ⟩ := Finset.mem_erase.mp hz
    exact Finset.mem_offDiag.mpr ⟨hq, hZ hzZ, hzq.symm⟩
  have hcardS : S.card = (Z.erase q).card := by
    exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
  have hOAI := OAI.ErdosDistinctDistances.equalLengthPairs_lower_bound S hS
  have hdist : OAI.ErdosDistinctDistances.distances P = distanceSet P := rfl
  rw [hdist, hcardS, equalLengthPairs_star_card] at hOAI
  have henergy : ((Z.erase q).card : ℝ) ^ 2 ≤
      (Mcount P - 1) * ((pointDistancePairs Z q).card + (Z.erase q).card) := by
    have h := Nat.cast_le (α := ℝ).mpr hOAI
    simpa [Mcount, distinctDistances] using h
  have hM₁ : 1 ≤ Mcount P := by
    dsimp [Mcount]
    have h := Nat.cast_nonneg (α := ℝ) (distinctDistances P)
    linarith
  have hZ₂ : 2 ≤ Z.card := by
    have : (2 : ℝ) ≤ Z.card := by linarith
    exact_mod_cast this
  have hP₂ : 2 ≤ P.card := hZ₂.trans (Finset.card_le_card hZ)
  have hdist₁ := OAI.ErdosDistinctDistances.one_le_card_distances hP₂
  rw [hdist] at hdist₁
  have hM : 1 < Mcount P := by
    have h : (1 : ℝ) ≤ distinctDistances P := by exact_mod_cast hdist₁
    dsimp [Mcount]
    linarith
  have hKL : ((Z.erase q).card : ℝ) ≤ Z.card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.erase_subset _ _))
  have hK : (Z.card : ℝ) - 1 ≤ (Z.erase q).card := by
    by_cases hqZ : q ∈ Z
    · have h := Z.card_erase_add_one hqZ
      have hr : ((Z.erase q).card : ℝ) + 1 = Z.card := by exact_mod_cast h
      linarith
    · have heq : Z.erase q = Z := by
        ext z
        simp only [Finset.mem_erase]
        constructor
        · tauto
        · intro hz
          exact ⟨fun h => hqZ (h ▸ hz), hz⟩
      rw [heq]
      linarith
  exact collision_bound_of_energy_with_one_missing _ _ _ _ hM hlarge
    (Nat.cast_nonneg _) hK hKL henergy

end Reduction

end

end DistinctDistances
