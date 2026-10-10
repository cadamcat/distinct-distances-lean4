import DistinctDistances.TrackC.PartitionConstruction
import DistinctDistances.TrackC.PartitionLineCrossing

open Classical

namespace DistinctDistances.TrackC

/-- Dimension-parametric strict-sign polynomial partition, including line crossing. -/
theorem partition_dimension_construct (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset (E d)) (r : ℕ), 1 ≤ r →
      ∃ (fs : List (Poly d)) (cells : Finset (Set (E d))),
        fs.prod ≠ 0 ∧ (fs.prod.totalDegree : ℝ) ≤ C*r ∧
        (cells.card : ℝ) ≤ C*(r : ℝ)^d ∧
        (∀ R ∈ cells, (∃ σ, R = factorSignCell fs σ) ∧ IsOpen R ∧
          ((pointsIn S R).card : ℝ) ≤ C*S.card/(r : ℝ)^d) ∧
        (∀ R ∈ cells, ∀ R' ∈ cells, R ≠ R' → Disjoint R R') ∧
        (⋃ R ∈ cells, R) = (zeroSet fs.prod)ᶜ ∧
        (∀ l : Line d, ¬ onPolynomial fs.prod l →
          (cells.filter (fun R => (R ∩ (l.1 : Set (E d))).Nonempty)).card ≤
            fs.prod.totalDegree+1) := by
  obtain ⟨C, hC, hpartition⟩ := sign_partition_construction d hd
  refine ⟨C, hC, ?_⟩
  intro S r hr
  obtain ⟨fs, cells, hf0, hdegree, hcard, hcells, hdisj, hcover⟩ := hpartition S r hr
  refine ⟨fs, cells, hf0, hdegree, hcard, hcells, hdisj, hcover, ?_⟩
  intro l hn
  exact partition_line_crossing d fs cells (fun R hR => (hcells R hR).1) hdisj l hn

end DistinctDistances.TrackC
