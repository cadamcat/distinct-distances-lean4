import DistinctDistances.TrackD.Profiles.PartitionPieceGood

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

/-- Before the first cut the only carrier is the whole affine space. -/
theorem partition_initial_capture_eq (π : CutPath d) (S : Finset (Pt d))
    (g : Poly d) (hg : g ≠ 0) :
    π.captured 0 S g = S.filter (fun x => MvPolynomial.eval (toC x) g = 0) := by
  classical
  have hsys : π.system 0 = ⊥ := by simp [CutPath.system]
  ext x
  simp only [CutPath.captured, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    refine ⟨h.1, h.2, ?_⟩
    intro Z hZ
    have hmin : Z.ideal ∈ (π.system 0).minimalPrimes := hZ.1
    rw [hsys, Ideal.minimalPrimes_eq_subsingleton_self] at hmin
    have hZzero : Z.ideal = ⊥ := by simpa using hmin
    rw [hZzero]
    exact fun hmem => hg (Ideal.mem_bot.mp hmem)

/-- A first-type batch cannot retain its defining polynomial without an
early cut: otherwise that polynomial captures its entire nonempty leaf at
an internal grid event. The output plateau margin does not enter this bound. -/
theorem partition_first_type_imbalance (hd : 0 < d) (grid : Fin G → ℝ) (L : Fin G → ℕ)
    (r k : Fin G) (hrk : r ≤ k) (s u θ : ℝ) (hu : 0 < u)
    (π : CutPath d) (S : Finset (Pt d)) (X : Piece d)
    (hX : PartitionGridLeaf grid L r π 0 S s X)
    (htests : PartitionGridTests grid L r u X)
    (g : Poly d) (hg : g ≠ 0) (hdegree : g.totalDegree ≤ L k)
    (hvan : ∀ x ∈ S, MvPolynomial.eval (toC x) g = 0)
    (htime : grid k ≤ -1 / 2 + θ) :
    ∃ i : Fin d, 1 / 2 - θ ≤ |X.path.time i| := by
  classical
  have hearly : ∃ i : Fin d, X.path.time i ≤ grid k := by
    by_contra hn
    have hfuture : ∀ i : Fin d, grid k < X.path.time i := by
      intro i
      apply lt_of_not_ge
      intro hi
      exact hn ⟨i, hi⟩
    have hplateau : ∀ i : Fin d, (i.val < 0 → X.path.time i ≤ grid k) ∧
        (0 ≤ i.val → grid k < X.path.time i) := by
      intro i
      exact ⟨fun hi => (by omega), fun _ => hfuture i⟩
    have hcount := htests k hrk 0 hd hplateau g hdegree
    have hcaptured : X.path.captured 0 X.pts g = X.pts := by
      rw [partition_initial_capture_eq X.path X.pts g hg]
      apply Finset.filter_eq_self.mpr
      intro x hx
      exact hvan x (hX.subset hx)
    rw [hcaptured] at hcount
    have hε : Real.exp (-7 * u / 18) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hmass : (0 : ℝ) < X.pts.card := by exact_mod_cast Finset.card_pos.mpr hX.nonempty
    have hstrict := mul_lt_mul_of_pos_right hε hmass
    linarith
  obtain ⟨i, hi⟩ := hearly
  refine ⟨i, ?_⟩
  have habs := neg_le_abs (X.path.time i)
  linarith

end
end DistinctDistances.TrackD
