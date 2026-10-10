import DistinctDistances.TrackD.Profiles.PartitionChain
import DistinctDistances.TrackD.Profiles.PartitionDyadic
import DistinctDistances.TrackD.Profiles.PartitionPackages

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- The finite chain gives the original partition conclusions once its
terminal core and total fractional loss have been bounded. -/
theorem partition_chain_partition (P : Finset (Pt d)) (n L : ℕ)
    (remaining : ℕ → Finset (Pt d)) (pieces : ℕ → Finset (Piece d))
    (error : ℕ → ℝ) (δ θ ξ K s₀ : ℝ) (hN : 0 < cfgN P)
    (hstart : remaining 0 = P)
    (hnested : ∀ i < n, remaining (i + 1) ⊆ remaining i)
    (hgood : ∀ i < n, ∀ X ∈ pieces i,
      PieceGood P θ ξ K X ∧ s₀ ≤ X.width ∧ X.pts ⊆ remaining i)
    (hdisjoint : ∀ i < n, (pieces i : Set (Piece d)).PairwiseDisjoint Piece.pts)
    (hnext : ∀ i < n, ∀ X ∈ pieces i, Disjoint X.pts (remaining (i + 1)))
    (hcore : CoreIsolated (remaining n) L)
    (hdegree : δ * cfgN P / cfgA P * (L : ℝ) ^ 2 ≤ θ * cfgN P)
    (hstep : ∀ i < n,
      ((remaining i).card : ℝ) - (remaining (i + 1)).card -
        (∑ X ∈ pieces i, (X.pts.card : ℝ)) ≤ cfgN P * error i)
    (herror : (∑ i ∈ Finset.range n, error i) ≤ θ) :
    ∃ Q : Partition d, Q.Good P δ θ ξ K s₀ := by
  classical
  have hnonempty : ∀ i < n, ∀ X ∈ pieces i, X.pts.Nonempty := by
    intro i hi X hX
    have hmass := (hgood i hi X hX).1.size
    have hpos : (0 : ℝ) < X.pts.card :=
      lt_of_lt_of_le (mul_pos hN (Real.exp_pos _)) hmass
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  obtain ⟨hdisj, hsum, hcoreDisj⟩ := partition_chain_join n remaining pieces Piece.pts
    hnested (fun i hi X hX => (hgood i hi X hX).2.2) hdisjoint hnext hnonempty
  let allPieces : Finset (Piece d) := (Finset.range n).biUnion pieces
  refine ⟨⟨remaining n, L, allPieces⟩, ?_, hcore, hdegree, ?_, hdisj, ?_, ?_⟩
  · have hsub : ∀ i ≤ n, remaining i ⊆ P := by
      intro i
      induction i with
      | zero => intro hi; rw [hstart]
      | succ i ih =>
          intro hi
          exact (hnested i (by omega)).trans (ih (by omega))
    exact hsub n le_rfl
  · intro X hX
    obtain ⟨i, hi, hXi⟩ := Finset.mem_biUnion.mp hX
    have h := hgood i (Finset.mem_range.mp hi) X hXi
    exact ⟨h.1, h.2.1⟩
  · intro X hX
    exact (hcoreDisj X hX).symm
  · change cfgN P - (remaining n).card - (∑ X ∈ allPieces, (X.pts.card : ℝ)) ≤ _
    dsimp only [allPieces]
    rw [hsum]
    have hmass := partition_window_mass_ledger n
      (fun i => ((remaining i).card : ℝ))
      (fun i => ∑ X ∈ pieces i, (X.pts.card : ℝ))
      (fun i => cfgN P * error i) hstep
    rw [hstart, ← Finset.mul_sum] at hmass
    exact hmass.trans (by simpa only [mul_comm θ] using
      mul_le_mul_of_nonneg_left herror hN.le)

end
end DistinctDistances.TrackD
