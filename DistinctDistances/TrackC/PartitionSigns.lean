import DistinctDistances.TrackC.PolynomialCalculus

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- Internal copy of the frozen signCell formula, avoiding a cyclic import of
Polynomial.lean; the public partition wrapper identifies them definitionally. -/
def factorSignCell {d : ℕ} (fs : List (Poly d)) (σ : Fin fs.length → Bool) : Set (E d) :=
  {x | ∀ i : Fin fs.length, if σ i then 0 < evalR (fs.get i) x else evalR (fs.get i) x < 0}

@[simp] theorem factorSignCell_nil {d : ℕ} (σ : Fin 0 → Bool) :
    factorSignCell ([] : List (Poly d)) σ = Set.univ := by
  ext x
  simp [factorSignCell]

theorem factorSignCell_cons {d : ℕ} (f : Poly d) (fs : List (Poly d))
    (σ : Fin (f::fs).length → Bool) :
    factorSignCell (f::fs) σ =
      {x | if σ 0 then 0 < evalR f x else evalR f x < 0} ∩
        factorSignCell fs (fun i => σ i.succ) := by
  ext x
  simp [factorSignCell, Fin.forall_fin_succ]

theorem factorSignCell_open {d : ℕ} (fs : List (Poly d)) (σ : Fin fs.length → Bool) :
    IsOpen (factorSignCell fs σ) := by
  have heq : factorSignCell fs σ = ⋂ i : Fin fs.length,
      {x : E d | if σ i then 0 < evalR (fs.get i) x else evalR (fs.get i) x < 0} := by
    ext x
    simp [factorSignCell]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  cases h : σ i
  · simpa [h] using isOpen_lt (polynomial_contDiff d (fs.get i) 0).continuous continuous_const
  · simpa [h] using isOpen_lt continuous_const (polynomial_contDiff d (fs.get i) 0).continuous

theorem factorSignCell_disjoint {d : ℕ} (fs : List (Poly d))
    (σ τ : Fin fs.length → Bool) (hστ : σ ≠ τ) :
    Disjoint (factorSignCell fs σ) (factorSignCell fs τ) := by
  apply Set.disjoint_left.mpr
  intro x hx hxt
  apply hστ
  funext i
  have hp := hx i
  have hq := hxt i
  cases hσ : σ i <;> cases hτ : τ i
  · rfl
  · simp [hσ, hτ] at hp hq
    linarith
  · simp [hσ, hτ] at hp hq
    linarith
  · rfl

theorem eval_product_ne_zero_iff {d : ℕ} (fs : List (Poly d)) (x : E d) :
    evalR fs.prod x ≠ 0 ↔ ∀ i : Fin fs.length, evalR (fs.get i) x ≠ 0 := by
  induction fs with
  | nil => simp [evalR]
  | cons f fs ih =>
    have he : evalR (f::fs).prod x = evalR f x * evalR fs.prod x := by simp [evalR]
    rw [he, mul_ne_zero_iff, ih]
    simp [Fin.forall_fin_succ]

/-- The full finite family of strict sign cells. -/
noncomputable def factorSignCells {d : ℕ} (fs : List (Poly d)) : Finset (Set (E d)) :=
  Finset.univ.image (factorSignCell fs)

theorem factorSignCells_card {d : ℕ} (fs : List (Poly d)) :
    (factorSignCells fs).card ≤ 2^fs.length := by
  exact (Finset.card_image_le).trans (by simp)

theorem factorSignCells_cover {d : ℕ} (fs : List (Poly d)) :
    (⋃ R ∈ factorSignCells fs, R) = (zeroSet fs.prod)ᶜ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hR
    change evalR fs.prod x ≠ 0
    apply (eval_product_ne_zero_iff fs x).mpr
    intro i
    have h := hxR i
    cases hσi : σ i
    · exact ne_of_lt (by simpa [hσi] using h)
    · exact ne_of_gt (by simpa [hσi] using h)
  · intro hx
    have hn := (eval_product_ne_zero_iff fs x).mp hx
    let σ : Fin fs.length → Bool := fun i => decide (0 < evalR (fs.get i) x)
    apply Set.mem_iUnion₂.mpr
    refine ⟨factorSignCell fs σ, Finset.mem_image.mpr ⟨σ, Finset.mem_univ σ, rfl⟩, ?_⟩
    intro i
    dsimp [σ]
    split_ifs with hp
    · exact of_decide_eq_true hp
    · exact lt_of_le_of_ne (le_of_not_gt (by simpa using hp)) (hn i)

end DistinctDistances.TrackC
