import DistinctDistances.TrackC.Incidence

/-! Adapters from track C's nonempty line subtype to finite families of affine lines. -/

namespace DistinctDistances.Bridges

open scoped BigOperators Classical
noncomputable section

theorem flat_nonempty_of_positive_rank {d k : ℕ}
    (H : AffineSubspace ℝ (TrackC.E d)) (hk : 0 < k)
    (hH : Module.finrank ℝ H.direction = k) : (H : Set (TrackC.E d)).Nonempty := by
  apply (AffineSubspace.nonempty_iff_ne_bot H).mpr
  intro he
  rw [he, AffineSubspace.direction_bot] at hH
  have hzero : Module.finrank ℝ (⊥ : Submodule ℝ (TrackC.E d)) = 0 := by simp
  rw [hzero] at hH
  omega

/-- The supplier's incidence count agrees with the consumer's product-filter count. -/
theorem ci_st_affine : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (Q : Finset (TrackC.E d))
      (L : Finset (AffineSubspace ℝ (TrackC.E d))),
      (∀ l ∈ L, Module.finrank ℝ l.direction = 1) →
      (((Q ×ˢ L).filter (fun x => x.1 ∈ x.2)).card : ℝ) ≤
        C * (((Q.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + Q.card + L.card) := by
  obtain ⟨C, hC, h⟩ := TrackC.ci_st
  refine ⟨C, hC, ?_⟩
  intro d Q L hL
  let pack : {F // F ∈ L} → TrackC.Line d := fun F =>
    ⟨F.val, flat_nonempty_of_positive_rank F.val (by norm_num) (hL F.val F.property),
      hL F.val F.property⟩
  let L' : Finset (TrackC.Line d) := L.attach.image pack
  have hpack : Function.Injective pack := by
    intro F G he
    apply Subtype.ext
    exact congrArg (fun H : TrackC.Line d => H.val) he
  have hcard : L'.card = L.card := by
    dsimp [L']
    rw [Finset.card_image_of_injective _ hpack, Finset.card_attach]
  have hcount (x : TrackC.E d) :
      TrackC.lineMultiplicity L' x = (L.filter (fun l => x ∈ l)).card := by
    unfold TrackC.lineMultiplicity
    symm
    apply Finset.card_bij (fun l hl => pack ⟨l, (Finset.mem_filter.mp hl).1⟩)
    · intro l hl
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨⟨l, (Finset.mem_filter.mp hl).1⟩,
          Finset.mem_attach _ _, rfl⟩, (Finset.mem_filter.mp hl).2⟩
    · intro l hl l' hl' he
      exact congrArg (fun H : TrackC.Line d => H.val) he
    · intro l hl
      obtain ⟨G, hG, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hl).1
      refine ⟨G.val, Finset.mem_filter.mpr ⟨G.property, ?_⟩, he⟩
      simpa only [← he] using (Finset.mem_filter.mp hl).2
  have hinc : TrackC.incidences Q L' =
      ((Q ×ˢ L).filter (fun x => x.1 ∈ x.2)).card := by
    simp only [TrackC.incidences, hcount, Finset.card_eq_sum_ones,
      Finset.sum_filter, Finset.sum_product]
  have hbound := h d Q L'
  rw [hinc, hcard, ← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hbound
  exact hbound

/-- Taking the ceiling transfers the natural rich-line threshold to a real threshold. -/
theorem ci_st_rich_real (m : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (Q : Finset (TrackC.E m)) (L : Finset (AffineSubspace ℝ (TrackC.E m))) (t : ℝ),
      2 ≤ t → (∀ l ∈ L, Module.finrank ℝ l.direction = 1 ∧
        t ≤ ((Q.filter (· ∈ l)).card : ℝ)) →
      (L.card : ℝ) ≤ C * ((Q.card : ℝ) ^ 2 / t ^ 3 + Q.card / t) := by
  obtain ⟨C, hC, h⟩ := TrackC.ci_st_rich
  refine ⟨C, hC, ?_⟩
  intro Q L t ht hL
  let k : ℕ := ⌈t⌉₊
  have htpos : 0 < t := by linarith
  have htk : t ≤ (k : ℝ) := Nat.le_ceil t
  have hk2 : 2 ≤ k := by exact_mod_cast (ht.trans htk)
  obtain ⟨hf, hb⟩ := (h m Q ∅ k hk2).2
  let pack : {F // F ∈ L} → TrackC.Line m := fun F =>
    ⟨F.val, flat_nonempty_of_positive_rank F.val (by norm_num) (hL F.val F.property).1,
      (hL F.val F.property).1⟩
  let L' : Finset (TrackC.Line m) := L.attach.image pack
  have hpack : Function.Injective pack := by
    intro F G he
    apply Subtype.ext
    exact congrArg (fun H : TrackC.Line m => H.val) he
  have hcard : L'.card = L.card := by
    dsimp [L']
    rw [Finset.card_image_of_injective _ hpack, Finset.card_attach]
  have hsub : L' ⊆ hf.toFinset := by
    intro F hF
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
    apply hf.mem_toFinset.mpr
    change (k : ℝ) ≤ (TrackC.pointsOn Q (pack G)).card
    have hocc : ⌈t⌉₊ ≤ (Q.filter (· ∈ G.val)).card :=
      Nat.ceil_le.mpr (hL G.val G.property).2
    exact_mod_cast hocc
  have hcardbound : (L.card : ℝ) ≤ ((TrackC.richLines Q k).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hf, ← hcard]
    exact_mod_cast Finset.card_le_card hsub
  apply hcardbound.trans
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply add_le_add
  · exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (pow_le_pow_left₀ htpos.le htk 3)
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) htpos htk

end
end DistinctDistances.Bridges
