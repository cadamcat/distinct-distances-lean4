import DistinctDistances.Defs

open scoped Finset

/-!
# Independent restatement of the target (statement-fidelity probe)

`Indep` restates the target `DistinctDistances.jsp_000900` without the copied Formal
Conjectures definitions: the distance set is written out as an off-diagonal image and the
count as its cardinality. `fc_iff_indep` proves the two formulations equivalent. The
boundary examples distinguish readings of the definitions: empty and singleton sets give
zero distances, two-point sets give exactly one, and ordered pairs contribute one distance
per unordered pair by symmetry of `dist`.
-/

namespace FidelityProbe

/-- The target statement, typed exactly as in `Challenge.lean`. -/
def FCStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card →
        c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (distinctDistances P : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
        (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)))

/-- The same statement with the distance count written out explicitly. -/
def Indep : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card →
        c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤
          ((#((P.offDiag.image fun pair :
            EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
              dist pair.1 pair.2)) : ℕ) : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
        ((#((P.offDiag.image fun pair :
            EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
              dist pair.1 pair.2)) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)))

theorem fc_to_indep (h : FCStatement) : Indep := h

theorem indep_to_fc (h : Indep) : FCStatement := h

theorem fc_iff_indep : FCStatement ↔ Indep := ⟨fc_to_indep, indep_to_fc⟩

/-- Unfolding `FCStatement` gives back the statement exactly as `Challenge.lean` types it. -/
example : FCStatement = (∀ d : ℕ, 3 ≤ d →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card →
        c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (distinctDistances P : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
        (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)))) := rfl

/-- Unfolding `distanceSet` gives the off-diagonal image. -/
example (X : Type*) [MetricSpace X] (P : Finset X) :
    distanceSet P = P.offDiag.image fun pair : X × X => dist pair.1 pair.2 := rfl

-- Boundary witnesses distinguishing readings of the definitions.
-- Empty and singleton sets determine no distances (no off-diagonal pairs).
example (X : Type*) [MetricSpace X] : distanceSet (∅ : Finset X) = ∅ := by
  simp [distanceSet]

example (X : Type*) [MetricSpace X] (x : X) :
    distinctDistances ({x} : Finset X) = 0 := by
  simp [distinctDistances, distanceSet]

-- Two-point sets determine exactly one distance (ordered pairs agree by `dist_comm`).
example (X : Type*) [MetricSpace X] [DecidableEq X] (a b : X) (h : a ≠ b) :
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

end FidelityProbe

#print axioms FidelityProbe.fc_iff_indep
