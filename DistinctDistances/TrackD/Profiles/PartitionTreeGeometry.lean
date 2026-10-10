import DistinctDistances.TrackD.Profiles.PartitionPrefixes
import DistinctDistances.TrackD.Profiles.PartitionThresholds

/-! Path invariants and saturated-residual inheritance in the regularization
tree, `profiles.tex:141–170`. These declarations do not assume that such a
tree has been constructed. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

/-- Geometry of a nonempty terminal descendant, measured against one original
node and its already completed cut prefix. -/
structure PartitionGridLeaf (grid : Fin G → ℝ) (L : Fin G → ℕ) (r : Fin G)
    (π : CutPath d) (j : ℕ) (S : Finset (Pt d)) (s : ℝ) (X : Piece d) : Prop where
  subset : X.pts ⊆ S
  nonempty : X.pts.Nonempty
  width : X.width = s
  prefix_eq : ∀ i : Fin d, i.val < j → X.path.cut i = π.cut i ∧ X.path.time i = π.time i
  newcuts : ∀ i : Fin d, j ≤ i.val → ∃ k : Fin G,
    r ≤ k ∧ (X.path.cut i).totalDegree ≤ L k ∧ X.path.time i = grid k
  mono : Monotone X.path.time
  vanish : ∀ x ∈ X.pts, ∀ i, MvPolynomial.eval (toC x) (X.path.cut i) = 0
  proper : ∀ x ∈ X.pts, X.path.ProperAt (toC x)

/-- A descendant retains the older prefix when an intermediate node is
forgotten. New cuts of that intermediate node keep their original grid and
degree certificates. -/
theorem PartitionGridLeaf.compose (grid : Fin G → ℝ) (L : Fin G → ℕ)
    (r r' : Fin G) (π π' : CutPath d) (j j' : ℕ) (S S' : Finset (Pt d)) (s : ℝ)
    (X : Piece d) (hX : PartitionGridLeaf grid L r' π' j' S' s X)
    (hsubset : S' ⊆ S) (hindex : j ≤ j') (hr : r ≤ r')
    (hprefix : ∀ i : Fin d, i.val < j → π'.cut i = π.cut i ∧ π'.time i = π.time i)
    (hnew : ∀ i : Fin d, j ≤ i.val → i.val < j' →
      ∃ k : Fin G, r ≤ k ∧ (π'.cut i).totalDegree ≤ L k ∧ π'.time i = grid k) :
    PartitionGridLeaf grid L r π j S s X := by
  refine ⟨hX.subset.trans hsubset, hX.nonempty, hX.width, ?_, ?_,
    hX.mono, hX.vanish, hX.proper⟩
  · intro i hi
    obtain ⟨hc, ht⟩ := hX.prefix_eq i (by omega)
    exact ⟨hc.trans (hprefix i hi).1, ht.trans (hprefix i hi).2⟩
  · intro i hi
    by_cases hij : i.val < j'
    · obtain ⟨k, hrk, hdeg, htime⟩ := hnew i hi hij
      obtain ⟨hc, ht⟩ := hX.prefix_eq i hij
      exact ⟨k, hrk, hc ▸ hdeg, ht.trans htime⟩
    · obtain ⟨k, hrk, hdeg, htime⟩ := hX.newcuts i (by omega)
      exact ⟨k, hr.trans hrk, hdeg, htime⟩

/-- At a grid time skipped by a residual, the terminal path still has exactly
the original prefix: its future cuts are at later grid times. -/
theorem PartitionGridLeaf.skipped_index_eq (grid : Fin G → ℝ) (L : Fin G → ℕ)
    (hgrid : StrictMono grid) (r r' : Fin G) (hrr' : r < r')
    (π : CutPath d) (j : ℕ) (R : Finset (Pt d)) (s : ℝ) (X : Piece d)
    (hX : PartitionGridLeaf grid L r' π j R s X)
    (hprefix : ∀ i : Fin d, i.val < j → π.time i ≤ grid r)
    (ℓ : ℕ) (hℓ : ℓ < d)
    (hplateau : ∀ i : Fin d, (i.val < ℓ → X.path.time i ≤ grid r) ∧
      (ℓ ≤ i.val → grid r < X.path.time i)) : ℓ = j := by
  have hnotbefore : ¬ ℓ < j := by
    intro h
    let i : Fin d := ⟨ℓ, hℓ⟩
    have hpi := (hX.prefix_eq i (by dsimp [i]; omega)).2
    have hupper := hprefix i (by dsimp [i]; omega)
    have hlower := (hplateau i).2 (by dsimp [i]; omega)
    rw [hpi] at hlower
    linarith
  have hnotafter : ¬ j < ℓ := by
    intro h
    let i : Fin d := ⟨j, by omega⟩
    obtain ⟨k, hrk, hdeg, htime⟩ := hX.newcuts i (by dsimp [i]; omega)
    have hupper := (hplateau i).1 (by dsimp [i]; omega)
    have hlower : grid r < grid k := hgrid (hrr'.trans_le hrk)
    rw [htime] at hupper
    linarith
  omega

/-- The saturated node threshold becomes a uniform bound on every surviving
terminal descendant. Carrier and cut assignments stay those of the original
node throughout the restriction. -/
theorem PartitionGridLeaf.residual_capture_bound (grid : Fin G → ℝ) (L : Fin G → ℕ)
    (hgrid : StrictMono grid) (r r' : Fin G) (hrr' : r < r')
    (π : CutPath d) (j : ℕ) (R : Finset (Pt d)) (s : ℝ) (X : Piece d)
    (hX : PartitionGridLeaf grid L r' π j R s X)
    (hprefix : ∀ i : Fin d, i.val < j → π.time i ≤ grid r)
    (m a tail u : ℝ) (hu : u ≤ a) (htail : tail ≤ a / 9)
    (hsize : m * Real.exp (-a / 2 - tail) ≤ X.pts.card)
    (hsaturated : ∀ g : Poly d, g.totalDegree ≤ L r →
      ((π.captured j R g).card : ℝ) ≤ m * Real.exp (-a)) :
    ∀ ℓ < d,
      (∀ i : Fin d, (i.val < ℓ → X.path.time i ≤ grid r) ∧
        (ℓ ≤ i.val → grid r < X.path.time i)) →
      ∀ g : Poly d, g.totalDegree ≤ L r →
        ((X.path.captured ℓ X.pts g).card : ℝ) ≤
          Real.exp (-7 * u / 18) * X.pts.card := by
  intro ℓ hℓ hplateau g hg
  have heq := hX.skipped_index_eq grid L hgrid r r' hrr' π j R s X hprefix ℓ hℓ hplateau
  subst ℓ
  have hcap : ((X.path.captured j X.pts g).card : ℝ) ≤ m * Real.exp (-a) := by
    rw [partition_prefix_captured_eq X.path π j (fun i hi => (hX.prefix_eq i hi).1)]
    have hsub := partition_capture_subset π j R X.pts hX.subset g
    exact (show ((π.captured j X.pts g).card : ℝ) ≤ (π.captured j R g).card by
      exact_mod_cast Finset.card_le_card hsub).trans (hsaturated g hg)
  simpa only [mul_comm (Real.exp _)] using partition_fragmentation_uniform
    m (X.pts.card : ℝ) ((X.path.captured j X.pts g).card : ℝ) a tail u
    (by positivity) hu htail hsize hcap

end
end DistinctDistances.TrackD
