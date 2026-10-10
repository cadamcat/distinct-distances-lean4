import DistinctDistances.TrackD.Profiles.PartitionGreedy

/-! Attaching a greedy capture certificate to its path, `profiles.tex:141–149`.
The point set shrinks, while every preceding carrier system is retained. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem partition_prefix_system_eq (π π' : CutPath d) (j : ℕ)
    (hcuts : ∀ i : Fin d, i.val < j → π.cut i = π'.cut i) :
    π.system j = π'.system j := by
  unfold CutPath.system
  congr 1
  ext f
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (hcuts i hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, hcuts i hi⟩

theorem partition_prefix_carriers_eq (π π' : CutPath d) (j : ℕ)
    (hcuts : ∀ i : Fin d, i.val < j → π.cut i = π'.cut i) (x : Point d) :
    π.localCarriers j x = π'.localCarriers j x := by
  unfold CutPath.localCarriers CutPath.IsCarrier
  rw [partition_prefix_system_eq π π' j hcuts]

theorem partition_prefix_captured_eq (π π' : CutPath d) (j : ℕ)
    (hcuts : ∀ i : Fin d, i.val < j → π.cut i = π'.cut i)
    (S : Finset (Pt d)) (g : Poly d) :
    π.captured j S g = π'.captured j S g := by
  classical
  unfold CutPath.captured
  congr 1
  funext x
  rw [partition_prefix_carriers_eq π π' j hcuts]

/-- Attaching one proper capture increases the completed prefix by one.
The earlier cut systems, vanishing, properness and recorded times persist. -/
theorem partition_extend_prefix (π : CutPath d) (j : ℕ) (hj : j < d)
    (S T : Finset (Pt d)) (g : Poly d) (b : ℝ)
    (hcap : T ⊆ π.captured j S g)
    (hvan : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      MvPolynomial.eval (toC x) (π.cut i) = 0)
    (hproper : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      ∀ Z ∈ π.localCarriers i.val (toC x), π.cut i ∉ Z.ideal)
    (hmono : ∀ i k : Fin d, i.val < j → k.val < j → i ≤ k → π.time i ≤ π.time k)
    (hfinal : ∀ i : Fin d, i.val < j → π.time i ≤ b) :
    ∃ π' : CutPath d,
      (∀ i : Fin d, i.val < j → π'.cut i = π.cut i ∧ π'.time i = π.time i) ∧
      π'.cut ⟨j, hj⟩ = g ∧ π'.time ⟨j, hj⟩ = b ∧
      (∀ x ∈ T, ∀ i : Fin d, i.val < j + 1 →
        MvPolynomial.eval (toC x) (π'.cut i) = 0) ∧
      (∀ x ∈ T, ∀ i : Fin d, i.val < j + 1 →
        ∀ Z ∈ π'.localCarriers i.val (toC x), π'.cut i ∉ Z.ideal) ∧
      (∀ i k : Fin d, i.val < j + 1 → k.val < j + 1 → i ≤ k →
        π'.time i ≤ π'.time k) ∧
      ∀ i : Fin d, i.val < j + 1 → π'.time i ≤ b := by
  classical
  let index : Fin d := ⟨j, hj⟩
  let π' : CutPath d := ⟨Function.update π.cut index g, Function.update π.time index b⟩
  have hprefix : ∀ i : Fin d, i.val < j → π'.cut i = π.cut i ∧ π'.time i = π.time i := by
    intro i hi
    have hne : i ≠ index := by intro h; have := congrArg Fin.val h; dsimp [index] at this; omega
    simp [π', hne]
  have hcut : π'.cut index = g := by simp [π']
  have htime : π'.time index = b := by simp [π']
  have hsys : ∀ k ≤ j, ∀ x : Point d, π'.localCarriers k x = π.localCarriers k x := by
    intro k hk x
    exact partition_prefix_carriers_eq π' π k (fun i hi => (hprefix i (by omega)).1) x
  have hpoint : ∀ x ∈ T, x ∈ S ∧ MvPolynomial.eval (toC x) g = 0 ∧
      ∀ Z ∈ π.localCarriers j (toC x), g ∉ Z.ideal := by
    intro x hx
    exact Finset.mem_filter.mp (hcap hx)
  refine ⟨π', hprefix, hcut, htime, ?_, ?_, ?_, ?_⟩
  · intro x hx i hi
    by_cases hij : i.val < j
    · rw [(hprefix i hij).1]
      exact hvan x (hpoint x hx).1 i hij
    · have hieq : i = index := Fin.ext (by dsimp [index]; omega)
      rw [hieq, hcut]
      exact (hpoint x hx).2.1
  · intro x hx i hi Z hZ
    by_cases hij : i.val < j
    · rw [(hprefix i hij).1]
      exact hproper x (hpoint x hx).1 i hij Z ((hsys i.val (by omega) (toC x)) ▸ hZ)
    · have hieq : i = index := Fin.ext (by dsimp [index]; omega)
      rw [hieq, hcut]
      have hZj : Z ∈ π.localCarriers j (toC x) := by
        rw [hieq] at hZ
        exact (hsys j le_rfl (toC x)) ▸ hZ
      exact (hpoint x hx).2.2 Z hZj
  · intro i k hi hk hik
    by_cases hkj : k.val < j
    · have hij : i.val < j := by change i.val ≤ k.val at hik; omega
      rw [(hprefix i hij).2, (hprefix k hkj).2]
      exact hmono i k hij hkj hik
    · have hkeq : k = index := Fin.ext (by dsimp [index]; omega)
      rw [hkeq, htime]
      by_cases hij : i.val < j
      · rw [(hprefix i hij).2]
        exact hfinal i hij
      · have hieq : i = index := Fin.ext (by dsimp [index]; omega)
        rw [hieq, htime]
  · intro i hi
    by_cases hij : i.val < j
    · rw [(hprefix i hij).2]
      exact hfinal i hij
    · have hieq : i = index := Fin.ext (by dsimp [index]; omega)
      rw [hieq, htime]

end
end DistinctDistances.TrackD
