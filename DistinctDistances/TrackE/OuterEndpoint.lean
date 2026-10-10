import DistinctDistances.TrackE.CommonEndpoint
import DistinctDistances.TrackE.OuterRows

/-! The outermost-pool endpoint, sparse-cones.tex:340–651. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:u-outer-lift (sparse-cones.tex:340–651): the outermost pool, used in
both physical roles at width `s = log B` and with mass at least `N √δ`, is
impossible. `outer_profile_last_eq_one` already gives `b_last = 1`; the
remaining argument is outer regularity (426–561), the discarded components
(564–578) and the algebraic lift with its root and degree count (580–651). -/
theorem outer_profile_contradiction {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (houter : ∀ i, T.IsOuter i) (hs : ∀ i, M.s i = Real.log (regime.B i)) :
    False := by
  have hsparse := outer_rows_sparse T M houter hs (1 / 16) (by norm_num)
  have htol : ∀ᶠ i in atTop, selectionTolerance (T.precision i) ≤ 1 / 8 :=
    (selection_tolerance_tendsto_zero T.precision T.precision_grows).eventually
      (Iic_mem_nhds (by norm_num))
  obtain ⟨i, ⟨Γ, hΓ, hdel, hrow⟩, hti⟩ := (hsparse.and htol).exists
  set S := TrackD.poolPts (T.sources i) with hSdef
  have htargets : T.targets i = T.sources i := (houter i).1.symm
  -- the selected graph is dense
  have hsel := (T.certificate i).selected
  rw [htargets] at hsel
  have hG : (outerSelectedGraph T i).card =
      ((S ×ˢ S).filter (fun pq => TrackD.SelectedIncidence (regime.P i) (F.family i)
        (T.terminal i) (selectionTolerance (T.precision i)) pq.1 pq.2)).card := by
    simp only [outerSelectedGraph, htargets, hSdef]
  -- the pool is nonempty
  have hnpos : (0 : ℝ) < S.card := by
    have hmass := (houter i).2.2
    have hN := regime.N_pos i
    have hδ := Real.sqrt_pos.mpr (F.delta_pos i)
    exact lt_of_lt_of_le (mul_pos hN hδ) hmass
  -- the rows of `Γ` partition it
  have hΓS : ∀ pq ∈ Γ, pq.1 ∈ S := by
    intro pq hpq
    have h := hΓ hpq
    simp only [outerSelectedGraph, Finset.mem_filter, Finset.mem_product] at h
    exact h.1.1
  have hΓcard : (Γ.card : ℝ) ≤ S.card * ((1 / 16) * S.card) := by
    rw [Finset.card_eq_sum_card_fiberwise hΓS]
    push_cast
    calc (∑ p ∈ S, ((Γ.filter (fun pq => pq.1 = p)).card : ℝ))
        ≤ ∑ _p ∈ S, (1 / 16) * (S.card : ℝ) := Finset.sum_le_sum (fun p _ => hrow p)
      _ = S.card * ((1 / 16) * S.card) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit : ((outerSelectedGraph T i).card : ℝ) ≤
      ((outerSelectedGraph T i \ Γ).card : ℝ) + Γ.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := outerSelectedGraph T i) (t := Γ)
    exact_mod_cast h
  rw [hG] at hsplit
  nlinarith

end
end DistinctDistances.SparseCones
