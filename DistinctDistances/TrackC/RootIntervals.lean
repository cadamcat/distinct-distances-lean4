import DistinctDistances.TrackC.Basic

namespace DistinctDistances.TrackC

/-- Roots in disjoint successive sample intervals force a degree lower bound. -/
theorem polynomial_root_intervals_bound (p : Polynomial ℝ) (hp : p ≠ 0) (n : ℕ)
    (t : Fin (n+1) → ℝ) (ht : StrictMono t)
    (hroot : ∀ i : Fin n, ∃ u : ℝ, t i.castSucc < u ∧ u < t i.succ ∧ p.IsRoot u) :
    n ≤ p.natDegree := by
  classical
  choose u hul hur hup using hroot
  have hu : StrictMono u := by
    intro i j hij
    calc
      u i < t i.succ := hur i
      _ ≤ t j.castSucc := ht.monotone (by change i.val+1 ≤ j.val; exact Nat.succ_le_of_lt hij)
      _ < u j := hul j
  let Z : Finset ℝ := Finset.univ.image u
  have hcard : Z.card = n := by
    rw [Finset.card_image_of_injective _ hu.injective, Finset.card_univ, Fintype.card_fin]
  have hsubset : Z.val ⊆ p.roots := by
    intro z hz
    change z ∈ Finset.univ.image u at hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact (Polynomial.mem_roots hp).mpr (hup i)
  rw [← hcard]
  exact Polynomial.card_le_degree_of_subset_roots hsubset

/-- Any distinct ordered sample pair forcing a root gives at most degree+1 samples. -/
theorem polynomial_sign_sample_bound (p : Polynomial ℝ) (hp : p ≠ 0) (T : Finset ℝ)
    (hroot : ∀ a ∈ T, ∀ b ∈ T, a < b → ∃ u : ℝ, a < u ∧ u < b ∧ p.IsRoot u) :
    T.card ≤ p.natDegree+1 := by
  classical
  cases hT : T.card with
  | zero => omega
  | succ n =>
    let t := T.orderEmbOfFin hT
    have ht : StrictMono t := t.strictMono
    have hmem (i : Fin (n+1)) : t i ∈ T := T.orderEmbOfFin_mem hT i
    have h := polynomial_root_intervals_bound p hp n t ht (fun i =>
      hroot _ (hmem i.castSucc) _ (hmem i.succ) (ht (by change i.val < i.val+1; omega)))
    omega

end DistinctDistances.TrackC
