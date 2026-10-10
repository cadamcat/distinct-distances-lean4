import DistinctDistances.Defs

/-!
# Probes of the target's definitions (statement fidelity)

Kernel-checked evaluations of the copied Formal Conjectures definitions on small cases.
-/

-- The distance set of an empty set is empty: there are no off-diagonal pairs.
example (X : Type*) [MetricSpace X] : distanceSet (∅ : Finset X) = ∅ := by
  simp [distanceSet]

-- The distance set of a singleton is empty.
example (X : Type*) [MetricSpace X] (x : X) : distanceSet ({x} : Finset X) = ∅ := by
  simp [distanceSet]

-- Hence the empty set and singletons determine zero distances.
example (X : Type*) [MetricSpace X] : distinctDistances (∅ : Finset X) = 0 := by
  simp [distinctDistances, distanceSet]

example (X : Type*) [MetricSpace X] (x : X) :
    distinctDistances ({x} : Finset X) = 0 := by
  simp [distinctDistances, distanceSet]

-- Ordered-pair count: the off-diagonal has |P| * (|P| - 1) pairs.
example (X : Type*) [MetricSpace X] (P : Finset X) :
    P.offDiag.card = P.card * P.card - P.card :=
  Finset.offDiag_card P

-- A two-point set determines exactly one distance: both ordered pairs give the same
-- distance by symmetry of `dist`.
theorem distinctDistances_pair (X : Type*) [MetricSpace X] [DecidableEq X] (a b : X)
    (h : a ≠ b) :
    distinctDistances ({a, b} : Finset X) = 1 := by
  classical
  have hoff : Finset.offDiag ({a, b} : Finset X) = {(a, b), (b, a)} := by
    rw [Finset.offDiag_insert (by simpa using h), Finset.offDiag_singleton,
      Finset.singleton_product_singleton, Finset.singleton_product_singleton]
    simp
  have himg : (Finset.offDiag ({a, b} : Finset X)).image
      (fun pair : X × X => dist pair.1 pair.2) = {dist a b} := by
    rw [hoff]
    ext r
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with rfl | rfl <;> simp [dist_comm]
    · intro hr
      exact ⟨(a, b), Or.inl rfl, hr.symm⟩
  unfold distinctDistances distanceSet
  rw [himg, Finset.card_singleton]

-- Every set with at least two points determines at least one distance, so the lower-bound
-- clause of the target is not vacuous.
theorem one_le_distinctDistances (X : Type*) [MetricSpace X] (P : Finset X)
    (hP : 2 ≤ P.card) : 1 ≤ distinctDistances P := by
  classical
  obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  have hmem : dist a b ∈ distanceSet P := by
    rw [distanceSet, Finset.mem_image]
    exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩, rfl⟩
  rw [distinctDistances]
  exact Finset.card_pos.mpr ⟨dist a b, hmem⟩
