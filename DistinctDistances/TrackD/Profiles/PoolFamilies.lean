import DistinctDistances.TrackD.Profiles.JacobianGeometry

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

def pieceCarrierFamily (X : Piece d) (j : ℕ) : AffineFamily.Family d :=
  (pathComponents X.path j).filter (fun Z => ∃ x ∈ X.pts, toC x ∈ Z)

def poolCarrierFamily (pl : Finset (Piece d)) (j : ℕ) : AffineFamily.Family d :=
  pl.biUnion (fun X => pieceCarrierFamily X j)

theorem mem_pieceCarrierFamily (X : Piece d) (j : ℕ) (Z : AffineVariety d) :
    Z ∈ pieceCarrierFamily X j ↔ X.path.IsCarrier j Z ∧ ∃ x ∈ X.pts, toC x ∈ Z := by
  simp only [pieceCarrierFamily, Finset.mem_filter, mem_pathComponents_iff]

theorem mem_poolCarrierFamily (pl : Finset (Piece d)) (j : ℕ) (Z : AffineVariety d) :
    Z ∈ poolCarrierFamily pl j ↔ PoolCarrier pl j Z := by
  simp only [poolCarrierFamily, Finset.mem_biUnion, mem_pieceCarrierFamily, PoolCarrier]

theorem poolCarrierFamily_pure (P : Finset (Pt d)) (pl : Finset (Piece d))
    (θ ξ K : ℝ) (hpl : ∀ X ∈ pl, PieceGood P θ ξ K X) (j : ℕ) (hj : j ≤ d) :
    AffineFamily.IsPure (poolCarrierFamily pl j) (d - j) := by
  intro Z hZ
  obtain ⟨X, hX, hZ, x, hx, hxZ⟩ := (mem_poolCarrierFamily pl j Z).mp hZ
  exact prof_partition_pure X x hx ((hpl X hX).vanish x hx) ((hpl X hX).proper x hx)
    j hj Z ⟨hZ, hxZ⟩

/-- Each pool member contributes its own defining system. The effective degree is
the sum of system bounds, independent of overlaps between component families. -/
theorem poolCarrierFamily_from_lists (pl : Finset (Piece d)) (j : ℕ)
    (L : Piece d → ℕ) (hL : ∀ X ∈ pl, 1 ≤ L X)
    (hdegree : ∀ X ∈ pl, ∀ i : Fin d, i.val < j → (X.path.cut i).totalDegree ≤ L X) :
    TrackA.FromAffineLists (poolCarrierFamily pl j) (∑ X ∈ pl, L X) := by
  let e : pl ≃ Fin pl.card := Fintype.equivFinOfCardEq (by simp)
  refine ⟨pl.card, (fun i => pieceCarrierFamily (e.symm i).val j),
    (fun i => L (e.symm i).val), ?_, ?_, ?_⟩
  · intro i
    refine ⟨hL (e.symm i).val (e.symm i).property, ?_⟩
    refine ⟨{f | ∃ k : Fin d, k.val < j ∧ (e.symm i).val.path.cut k = f}, ?_, ?_⟩
    · rintro f ⟨k, hk, rfl⟩
      exact hdegree (e.symm i).val (e.symm i).property k hk
    · intro Z hZ
      exact ((mem_pieceCarrierFamily (e.symm i).val j Z).mp hZ).1
  · intro Z
    constructor
    · intro hZ
      obtain ⟨X, hX, hZX⟩ := Finset.mem_biUnion.mp hZ
      refine ⟨e ⟨X, hX⟩, ?_⟩
      simpa using hZX
    · rintro ⟨i, hZi⟩
      exact Finset.mem_biUnion.mpr ⟨(e.symm i).val, (e.symm i).property, hZi⟩
  · symm
    calc
      (∑ i : Fin pl.card, L (e.symm i).val) = ∑ X : pl, L X.val :=
        Equiv.sum_comp e.symm (fun X : pl => L X.val)
      _ = ∑ X ∈ pl, L X := by simpa only [Finset.sum_coe_sort] using Finset.sum_attach pl L

theorem pool_family_equations (pl : Finset (Piece d)) (j : ℕ)
    (E : List (Poly d))
    (hE : ∀ f ∈ E, f ∈ (AffineFamily.locus (poolCarrierFamily pl j)).ideal) :
    ∀ Z, PoolCarrier pl j Z → ∀ f ∈ E, f ∈ Z.ideal := by
  intro Z hZ f hf
  apply (mem_ideal_iff_eval_zero Z f).mpr
  intro x hx
  have hxF : x ∈ (AffineFamily.locus (poolCarrierFamily pl j)).points := by
    rw [AffineFamily.points_locus]
    exact Set.mem_iUnion₂.mpr ⟨Z, (mem_poolCarrierFamily pl j Z).mpr hZ, hx⟩
  exact (mem_ideal_iff_eval_zero (AffineFamily.locus (poolCarrierFamily pl j)) f).mp (hE f hf) x hxF

end
end DistinctDistances.TrackD
