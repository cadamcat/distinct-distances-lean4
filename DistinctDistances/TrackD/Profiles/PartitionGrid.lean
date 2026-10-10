import DistinctDistances.TrackD.Profiles.RankCore

/-! The finite-grid bridge from saturated regularization events to all
interior polynomial tests, `profiles.tex:164–170`. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

/-- A fixed degree multiplier is absorbed by a later testing time. -/
theorem partition_degree_absorption (B s a b ξ K : ℝ)
    (hB : 0 ≤ B) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hgap : a + ξ / 4 ≤ b) (hlarge : Real.log K ≤ ξ / 4 * s) :
    K * testDeg B s a ≤ testDeg B s b := by
  rw [RankCore.testDeg_shift B s a b]
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hfactor : K ≤ Real.exp ((b - a) * s) := by
    rw [← Real.exp_log hKpos]
    apply Real.exp_le_exp.mpr
    exact hlarge.trans (mul_le_mul_of_nonneg_right (by linarith) hs)
  have hT : 0 ≤ testDeg B s a := mul_nonneg hB (Real.exp_nonneg _)
  simpa only [mul_comm K] using mul_le_mul_of_nonneg_left hfactor hT

/-- Before the first grid time, or at a grid time strictly inside the same
plateau, every test has a fixed positive amount of degree slack. -/
theorem partition_grid_interior (hG : 0 < G) (grid : Fin G → ℝ)
    (ξ : ℝ) (hξ : 0 < ξ)
    (hmesh : ∀ k : Fin G, ∀ hk : k.val + 1 < G,
      grid ⟨k.val + 1, hk⟩ - grid k ≤ ξ / 4)
    (t : Fin d → ℝ) (htimes : ∀ i, ∃ k, t i = grid k)
    (j : ℕ) (hj : j < d) (b : ℝ) (hb : OnPlateau t j ξ b) :
    b + ξ / 4 ≤ grid ⟨0, hG⟩ ∨
      ∃ k : Fin G, b + ξ / 4 ≤ grid k ∧ grid k < b + ξ / 2 ∧
        ∀ i : Fin d, (i.val < j → t i ≤ grid k) ∧
          (j ≤ i.val → grid k < t i) := by
  classical
  by_cases hfirst : b + ξ / 4 ≤ grid ⟨0, hG⟩
  · exact Or.inl hfirst
  right
  let eligible := Finset.univ.filter (fun k : Fin G => b + ξ / 4 ≤ grid k)
  have hne : eligible.Nonempty := by
    obtain ⟨k, hk⟩ := htimes ⟨j, hj⟩
    have hnext := (hb ⟨j, hj⟩).2 le_rfl
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hk] at hnext
    linarith
  let k := eligible.min' hne
  have hk : k ∈ eligible := Finset.min'_mem eligible hne
  have hlower : b + ξ / 4 ≤ grid k := (Finset.mem_filter.mp hk).2
  have hkpos : 0 < k.val := by
    by_contra hn
    have hkzero : k = ⟨0, hG⟩ := Fin.ext (by change k.val = 0; omega)
    exact hfirst (by simpa only [hkzero] using hlower)
  let prev : Fin G := ⟨k.val - 1, by omega⟩
  have hprev : prev ∉ eligible := by
    intro hp
    have hle : k ≤ prev := Finset.min'_le eligible prev hp
    change k.val ≤ k.val - 1 at hle
    omega
  have hprevlt : grid prev < b + ξ / 4 := by
    apply lt_of_not_ge
    intro h
    exact hprev (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hpnext : prev.val + 1 < G := by dsimp [prev]; omega
  have hpkeq : (⟨prev.val + 1, hpnext⟩ : Fin G) = k := by
    apply Fin.ext
    dsimp [prev]
    omega
  have hgap := hmesh prev hpnext
  rw [hpkeq] at hgap
  have hupper : grid k < b + ξ / 2 := by linarith
  refine ⟨k, hlower, hupper, ?_⟩
  intro i
  constructor
  · intro hi
    have h := (hb i).1 hi
    linarith
  · intro hi
    have h := (hb i).2 hi
    linarith

/-- The grid and its lower boundary control every polynomial test on an
interior plateau. All constants and the grid are fixed before the point set. -/
theorem partition_no_capture_of_grid (π : CutPath d) (S : Finset (Pt d))
    (hG : 0 < G) (grid : Fin G → ℝ) (hgrid : Monotone grid)
    (ξ K B s ε : ℝ) (hξ : 0 < ξ) (hK : 1 ≤ K) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hlarge : Real.log K ≤ ξ / 4 * s)
    (hmesh : ∀ k : Fin G, ∀ hk : k.val + 1 < G,
      grid ⟨k.val + 1, hk⟩ - grid k ≤ ξ / 4)
    (htimes : ∀ i, ∃ k, π.time i = grid k)
    (hboundary : ∀ b : ℝ, b + ξ / 4 ≤ grid ⟨0, hG⟩ →
      ∀ g : Poly d, (g.totalDegree : ℝ) ≤ K * testDeg B s b →
        ((π.captured 0 S g).card : ℝ) ≤ ε * S.card)
    (hregular : ∀ k : Fin G, ∀ j < d,
      (∀ i : Fin d, (i.val < j → π.time i ≤ grid k) ∧
        (j ≤ i.val → grid k < π.time i)) →
      ∀ g : Poly d, (g.totalDegree : ℝ) ≤ testDeg B s (grid k) →
        ((π.captured j S g).card : ℝ) ≤ ε * S.card) :
    ∀ j < d, ∀ b : ℝ, OnPlateau π.time j ξ b →
      ∀ g : Poly d, (g.totalDegree : ℝ) ≤ K * testDeg B s b →
        ((π.captured j S g).card : ℝ) ≤ ε * S.card := by
  intro j hj b hb g hg
  rcases partition_grid_interior hG grid ξ hξ hmesh π.time htimes j hj b hb with
    hfirst | ⟨k, hlower, hupper, hplateau⟩
  · have hjzero : j = 0 := by
      by_contra hn
      have hjpos : 0 < j := by omega
      let i : Fin d := ⟨0, by omega⟩
      obtain ⟨k, hk⟩ := htimes i
      have hmin : grid ⟨0, hG⟩ ≤ π.time i := by
        rw [hk]
        exact hgrid (show (⟨0, hG⟩ : Fin G) ≤ k by change 0 ≤ k.val; omega)
      have hbefore := (hb i).1 (by dsimp [i]; omega)
      linarith
    subst j
    exact hboundary b hfirst g hg
  · exact hregular k j hj hplateau g (hg.trans (partition_degree_absorption B s b
      (grid k) ξ K hB hs hK hlower hlarge))

end
end DistinctDistances.TrackD
