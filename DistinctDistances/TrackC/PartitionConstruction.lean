import DistinctDistances.TrackC.PartitionIteration
import DistinctDistances.TrackC.PartitionSeries
import DistinctDistances.TrackC.PartitionScale

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- The complete degree, cardinality, occupancy and sign-cell partition budget.
Line crossing is added separately by the univariate restriction argument. -/
theorem sign_partition_construction (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset (E d)) (r : ℕ), 1 ≤ r →
      ∃ (fs : List (Poly d)) (cells : Finset (Set (E d))),
        fs.prod ≠ 0 ∧ (fs.prod.totalDegree : ℝ) ≤ C*r ∧
        (cells.card : ℝ) ≤ C*(r : ℝ)^d ∧
        (∀ R ∈ cells, (∃ σ, R = factorSignCell fs σ) ∧ IsOpen R ∧
          ((pointsIn S R).card : ℝ) ≤ C*S.card/(r : ℝ)^d) ∧
        (∀ R ∈ cells, ∀ R' ∈ cells, R ≠ R' → Disjoint R R') ∧
        (⋃ R ∈ cells, R) = (zeroSet fs.prod)ᶜ := by
  classical
  let C : ℝ := 8*(d : ℝ)^2
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hC : 0 < C := by dsimp [C]; positivity
  have hC2 : (2 : ℝ) ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro S r hr
  let J := partitionLevelCount d r
  obtain ⟨fs, hlen, hf0, hdegree, hcount⟩ := iterated_sign_bisection d hd S J
  have hscale := partitionLevelCount_bounds d r hd hr
  let cells := factorSignCells fs
  have hdegnat : fs.prod.totalDegree ≤ 8*d^2*r := by
    have hsum := bisection_degree_sum_bound d J hd
    have hpow : 2^(J/d) ≤ 2*r := hscale.2.2
    have h := hdegree.trans (hsum.trans (Nat.mul_le_mul_left (4*d^2) hpow))
    have heq : 4*d^2*(2*r) = 8*d^2*r := by ring
    simpa only [heq] using h
  have hdeg : (fs.prod.totalDegree : ℝ) ≤ C*r := by
    dsimp [C]
    exact_mod_cast hdegnat
  have hcellnat : cells.card ≤ 2*r^d :=
    (factorSignCells_card fs).trans (by simpa [hlen] using hscale.2.1)
  have hcells : (cells.card : ℝ) ≤ C*(r : ℝ)^d := by
    have hsmall : (cells.card : ℝ) ≤ 2*(r : ℝ)^d := by exact_mod_cast hcellnat
    exact hsmall.trans (mul_le_mul_of_nonneg_right hC2 (by positivity))
  refine ⟨fs, cells, hf0, hdeg, hcells, ?_, ?_, factorSignCells_cover fs⟩
  · intro R hR
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hR
    refine ⟨⟨σ, rfl⟩, factorSignCell_open fs σ, ?_⟩
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hden : (r : ℝ)^d ≤ (2 : ℝ)^J := by exact_mod_cast hscale.1.le
    have hsmall : (S.card : ℝ)/(2 : ℝ)^J ≤ (S.card : ℝ)/(r : ℝ)^d :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have hbig : (S.card : ℝ)/(r : ℝ)^d ≤ C*S.card/(r : ℝ)^d := by
      have hc1 : (1 : ℝ) ≤ C := by linarith
      have h := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ S.card/(r : ℝ)^d) hc1
      simpa only [mul_div_assoc] using h
    exact (hcount σ).trans (hsmall.trans hbig)
  · intro R hR R' hR' hne
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hR'
    apply factorSignCell_disjoint
    intro hστ
    exact hne (congrArg (factorSignCell fs) hστ)

end DistinctDistances.TrackC
