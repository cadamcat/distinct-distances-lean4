import DistinctDistances.TrackD.Profiles.PartitionTreeGeometry
import DistinctDistances.TrackD.Profiles.PartitionEventBudgets
import DistinctDistances.TrackD.Profiles.PartitionForest
import DistinctDistances.TrackD.Profiles.PartitionPackages
import DistinctDistances.TrackD.Profiles.PartitionTreeConstruction

/-! The constructive finite regularization tree, `profiles.tex:121–185`.
The tree uses finite event recursion and the separate algebraic finishing
package. The multiscale window assembly is a further step. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

/-- All grid and threshold data are supplied before the point set and its
prefix. Every branch retains its original node mass and carrier system. -/
theorem partition_regularize_grid (grid : Fin G → ℝ) (hgrid : StrictMono grid)
    (L : Fin G → ℕ) (s u : ℝ) (hu : 0 < u) (a : Fin (G * d) → ℝ)
    (ha : ∀ i, u ≤ a i)
    (htail : ∀ i, (∑ k ∈ Finset.univ.filter (fun k : Fin (G * d) => i < k), a k) ≤ a i / 9)
    (r : Fin G) (S S₀ : Finset (Pt d)) (hsubset : S ⊆ S₀)
    (E : Set (Poly d))
    (hdegree : ∀ f ∈ E, f.totalDegree ≤ L ⟨G - 1, by have := r.isLt; omega⟩)
    (hisolate : MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (S₀ : Set (Pt d)))
    (π : CutPath d) (j : ℕ) (hj : j ≤ d)
    (hvan : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      MvPolynomial.eval (toC x) (π.cut i) = 0)
    (hproper : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      ∀ Z ∈ π.localCarriers i.val (toC x), π.cut i ∉ Z.ideal)
    (hmono : ∀ i k : Fin d, i.val < j → k.val < j → i ≤ k → π.time i ≤ π.time k)
    (hfinal : ∀ i : Fin d, i.val < j → π.time i ≤ grid r) :
    ∃ pl : Finset (Piece d),
      (∀ X ∈ pl, PartitionGridLeaf grid L r π j S s X ∧
        (S.card : ℝ) * Real.exp (-partitionEventTail a (r.val * d + j)) ≤ X.pts.card ∧
        ∀ k : Fin G, r ≤ k → ∀ ℓ < d,
          (∀ i : Fin d, (i.val < ℓ → X.path.time i ≤ grid k) ∧
            (ℓ ≤ i.val → grid k < X.path.time i)) →
          ∀ g : Poly d, g.totalDegree ≤ L k →
            ((X.path.captured ℓ X.pts g).card : ℝ) ≤
              Real.exp (-7 * u / 18) * X.pts.card) ∧
      (pl : Set (Piece d)).PairwiseDisjoint Piece.pts ∧
      (S.card : ℝ) - (∑ X ∈ pl, (X.pts.card : ℝ)) ≤
        S.card * partitionEventTail (fun i => Real.exp (-a i / 2)) (r.val * d + j) := by
  obtain ⟨f⟩ := partition_grid_forest_exists grid hgrid L s u hu a ha htail r S S₀ hsubset
    E hdegree hisolate π j hj hvan hproper hmono hfinal
  exact ⟨f.pieces, f.leaf, f.disjoint, f.discard⟩

end
end DistinctDistances.TrackD
