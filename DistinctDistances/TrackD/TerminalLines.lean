import DistinctDistances.TrackD.GenericDepth
import DistinctDistances.TrackD.LinesCore
import DistinctDistances.TrackD.GeoLinesGroups
import DistinctDistances.TrackD.GeoLinePlaneScalar
import DistinctDistances.TrackD.GeoSlice

/-!
# `geo:terminal`, assigned lines (`secants.tex:254–331`)

The abstract line case is purely real: lines and planes of `ℝ^d`, sample occupancies and the
distance count `M`. The translation from projective containment `closure(π_p Y) ⊆ C_p` to a
plane through `p` (`secants.tex:255–258`) is `geo_terminal_lines`.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical
open Finset

noncomputable section

/-- Incidence bound between real lines and real planes of `ℝ^d` (`ℓ ⊆ H`), the form used at
`secants.tex:300–306` after a generic slice. -/
def LinePlaneIncidence (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (L 𝓗 : Finset (AffineSubspace ℝ (Pt d))),
    (∀ ℓ ∈ L, IsRealLine ℓ) → (∀ H ∈ 𝓗, IsRealPlane H) →
      (((L ×ˢ 𝓗).filter (fun x => x.1 ≤ x.2)).card : ℝ) ≤
        C * (((L.card : ℝ) * 𝓗.card) ^ ((2 : ℝ) / 3) + L.card + 𝓗.card)

/-- `geo:terminal.slice` (`secants.tex:300–303`, an instance of `FW.generic`): a generic real
hyperplane turns lines into points and planes into lines of `ℝ^{d-1}`, preserving and reflecting
containment, so the point–line bound in `ℝ^{d-1}` gives the line–plane bound in `ℝ^d`. -/
theorem terminal_slice (d : ℕ) (hd : 3 ≤ d) (hST : STIncidence (d - 1)) :
    LinePlaneIncidence d := by
  exact GeoSlice.slice_incidence d hd hST

/-- `geo:terminal.lineplane` (`secants.tex:270–292`, eq. `geo:line-plane-product`): a real line
`ℓ` in a real plane `H` satisfies `|P ∩ ℓ| · |P ∩ H| ≤ C M^2`. Parabolic lift
`(x₁, x₂) ↦ (x₁, x₁² + x₂²)` and the planar point–line bound; two-circle bound for bounded
`|P ∩ ℓ|`. -/
theorem terminal_lineplane (d : ℕ) (hST : STIncidence 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (Pt d)) (ℓ H : AffineSubspace ℝ (Pt d)),
      IsRealLine ℓ → IsRealPlane H → ℓ ≤ H →
        (occ P ℓ : ℝ) * occ P H ≤ C * cfgM P ^ 2 := by
  exact GeoLinePlane.lineplane d hST

/-- Every real line of `ℝ^d`, `d ≥ 3`, lies in a real plane. -/
lemma exists_plane_of_line {d : ℕ} (hd : 3 ≤ d) (ℓ : AffineSubspace ℝ (Pt d))
    (hℓ : IsRealLine ℓ) : ∃ H : AffineSubspace ℝ (Pt d), IsRealPlane H ∧ ℓ ≤ H := by
  unfold IsRealLine at hℓ
  have hns : ¬ (ℓ : Set (Pt d)).Subsingleton := by
    intro hs
    have h0 := AffineSubspace.direction_eq_bot_iff.mpr hs
    rw [h0, finrank_bot] at hℓ
    exact absurd hℓ (by norm_num)
  obtain ⟨x, hx⟩ : (ℓ : Set (Pt d)).Nonempty := by
    by_contra hne
    exact hns (Set.not_nonempty_iff_eq_empty.mp hne ▸ Set.subsingleton_empty)
  have hlt : ℓ.direction ≠ ⊤ := by
    intro htop
    have h1 := congrArg (fun V : Submodule ℝ (Pt d) => Module.finrank ℝ V) htop
    simp only [finrank_top, finrank_euclideanSpace, Fintype.card_fin] at h1
    omega
  obtain ⟨w, -, hw⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hlt)
  have hw0 : w ≠ 0 := fun h => hw (h ▸ ℓ.direction.zero_mem)
  have hdisj : ℓ.direction ⊓ (ℝ ∙ w) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv2
    by_cases hc : c = 0
    · simp [hc]
    · exfalso; apply hw
      have := ℓ.direction.smul_mem c⁻¹ hv1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  refine ⟨AffineSubspace.mk' x (ℓ.direction ⊔ ℝ ∙ w), ?_, ?_⟩
  · unfold IsRealPlane
    rw [AffineSubspace.direction_mk']
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq ℓ.direction (ℝ ∙ w)
    rw [hdisj, finrank_bot, finrank_span_singleton hw0] at h2
    omega
  · calc ℓ = AffineSubspace.mk' x ℓ.direction := (AffineSubspace.mk'_eq hx).symm
      _ ≤ _ := (AffineSubspace.mk'_le_mk'_iff x).mpr le_sup_left

/-- Some real plane exists in `ℝ^d`, `d ≥ 3`. -/
lemma exists_plane {d : ℕ} (hd : 3 ≤ d) : ∃ H : AffineSubspace ℝ (Pt d), IsRealPlane H := by
  have hv : (EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ) : Pt d) ≠ 0 := by
    intro h
    have := congrArg (fun v : Pt d => v ⟨0, by omega⟩) h
    simp at this
  obtain ⟨H, hH, -⟩ := exists_plane_of_line hd (AffineSubspace.mk' 0 (ℝ ∙ _)) (by
    unfold IsRealLine; rw [AffineSubspace.direction_mk']; exact finrank_span_singleton hv)
  exact ⟨H, hH⟩

lemma occ_mono {m : ℕ} (P : Finset (Pt m)) {F G : AffineSubspace ℝ (Pt m)} (h : F ≤ G) :
    occ P F ≤ occ P G := by
  unfold occ
  exact card_le_card (fun x hx => by
    simp only [mem_filter] at hx ⊢; exact ⟨hx.1, h hx.2⟩)


/-- The ordered pairs counted in the line case: `q` is assigned to a line `ℓ`, and either the
center `p` is on `ℓ` or the plane spanned by `p` and `ℓ` is one of the at most `E` planes recorded
at `p` (the planes over the line components of `C_p`). -/
def linePairs {d : ℕ} (P : Finset (Pt d)) (L : Finset (AffineSubspace ℝ (Pt d)))
    (S : AffineSubspace ℝ (Pt d) → Finset (Pt d))
    (𝓗 : Pt d → Finset (AffineSubspace ℝ (Pt d))) : Finset (Pt d × Pt d) :=
  (P ×ˢ P).filter (fun pq => ∃ ℓ ∈ L, pq.2 ∈ S ℓ ∧
    (pq.1 ∈ ℓ ∨ affineSpan ℝ (insert pq.1 (ℓ : Set (Pt d))) ∈ 𝓗 pq.1))

/-- `geo:terminal.lines-core` (`secants.tex:254–331`), abstract and explicit. Given the
line–plane incidence bound and the line–plane occupancy bound `|P∩ℓ|·|P∩H| ≤ C_LP M^2`, there are
`K, C` (depending only on the two input constants) such that whenever `K M ≤ A`, every plane holds
at most `h` points and at most `E` real planes are recorded at each center,
`#linePairs ≤ AEN + C (MN + N h (1 + log N)^2 + N^2 M^2 / A^2)`. -/
theorem terminal_lines_core (d : ℕ) (hd : 3 ≤ d) (hLP : LinePlaneIncidence d) (CLP : ℝ)
    (hocc : ∀ (P : Finset (Pt d)) (ℓ H : AffineSubspace ℝ (Pt d)),
      IsRealLine ℓ → IsRealPlane H → ℓ ≤ H → (occ P ℓ : ℝ) * occ P H ≤ CLP * cfgM P ^ 2) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ (P : Finset (Pt d)) (A E h : ℝ),
      0 < A → K * cfgM P ≤ A → 0 ≤ E →
      (∀ H : AffineSubspace ℝ (Pt d), IsRealPlane H → (occ P H : ℝ) ≤ h) →
      ∀ (L : Finset (AffineSubspace ℝ (Pt d))) (S : AffineSubspace ℝ (Pt d) → Finset (Pt d)),
        (∀ ℓ ∈ L, IsRealLine ℓ) → (∀ ℓ ∈ L, S ℓ ⊆ P.filter (· ∈ ℓ)) →
        (L : Set (AffineSubspace ℝ (Pt d))).PairwiseDisjoint S →
        ∀ 𝓗 : Pt d → Finset (AffineSubspace ℝ (Pt d)),
          (∀ p ∈ P, ((𝓗 p).card : ℝ) ≤ E ∧ ∀ H ∈ 𝓗 p, IsRealPlane H) →
          ((linePairs P L S 𝓗).card : ℝ) ≤
            A * E * cfgN P +
              C * (cfgM P * cfgN P + cfgN P * h * (1 + Real.log (cfgN P)) ^ 2 +
                cfgN P ^ 2 * cfgM P ^ 2 / A ^ 2) := by
  obtain ⟨C₁, hC₁, hinc⟩ := hLP
  set C₀ : ℝ := max CLP 1 with hC₀def
  have hC₀ : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCLP : CLP ≤ C₀ := le_max_left _ _
  refine ⟨Real.sqrt (2 * C₁ * C₀) + 1, Real.sqrt C₀ + 4 * C₁ + 2048 * C₀ * C₁ ^ 3,
    by positivity, by positivity, ?_⟩
  intro P A E h hA hKM hE hh L S hL hS hdisj 𝓗 h𝓗
  set N := cfgN P with hNdef
  set M := cfgM P with hMdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hM1 : 1 ≤ M := by
    have : (0 : ℝ) ≤ (distinctDistances P : ℝ) := Nat.cast_nonneg _
    simp only [hMdef, cfgM]; linarith
  set n : AffineSubspace ℝ (Pt d) → ℕ := fun ℓ => (S ℓ).card with hndef
  obtain ⟨H₀, hH₀⟩ := exists_plane hd
  have hh0 : 0 ≤ h := le_trans (Nat.cast_nonneg _) (hh H₀ hH₀)
  -- occupancies and masses
  have hnocc : ∀ ℓ ∈ L, n ℓ ≤ occ P ℓ := fun ℓ hℓ => card_le_card (hS ℓ hℓ)
  have hmassN : ∑ ℓ ∈ L, n ℓ ≤ P.card := by
    rw [← card_biUnion hdisj]
    apply card_le_card
    intro q hq
    obtain ⟨ℓ, hℓ, hqℓ⟩ := mem_biUnion.mp hq
    exact (mem_filter.mp (hS ℓ hℓ hqℓ)).1
  have hmass : ∑ ℓ ∈ L, (n ℓ : ℝ) ≤ N := by
    simp only [hNdef, cfgN]; exact_mod_cast hmassN
  have hsig_occ : ∀ H : AffineSubspace ℝ (Pt d),
      LinesCore.sig (fun ℓ H => ℓ ≤ H) L n H ≤ (occ P H : ℝ) := by
    intro H
    unfold LinesCore.sig
    have hd' : ((L.filter (fun ℓ => ℓ ≤ H)) : Set (AffineSubspace ℝ (Pt d))).PairwiseDisjoint S :=
      hdisj.subset (by intro x hx; exact (mem_filter.mp hx).1)
    have : ∑ ℓ ∈ L.filter (fun ℓ => ℓ ≤ H), n ℓ ≤ occ P H := by
      rw [← card_biUnion hd']
      apply card_le_card
      intro q hq
      obtain ⟨ℓ, hℓ, hqℓ⟩ := mem_biUnion.mp hq
      obtain ⟨hℓL, hℓH⟩ := mem_filter.mp hℓ
      obtain ⟨hqP, hqℓ'⟩ := mem_filter.mp (hS ℓ hℓL hqℓ)
      exact mem_filter.mpr ⟨hqP, hℓH hqℓ'⟩
    exact_mod_cast this
  -- line occupancy
  have hline : ∀ ℓ ∈ L, (occ P ℓ : ℝ) ≤ Real.sqrt C₀ * M := by
    intro ℓ hℓ
    obtain ⟨H, hH, hℓH⟩ := exists_plane_of_line hd ℓ (hL ℓ hℓ)
    have h1 := hocc P ℓ H (hL ℓ hℓ) hH hℓH
    have h2 : (occ P ℓ : ℝ) ≤ occ P H := by exact_mod_cast occ_mono P hℓH
    have h3 : (occ P ℓ : ℝ) ^ 2 ≤ C₀ * M ^ 2 := by
      have h0 : (0 : ℝ) ≤ occ P ℓ := Nat.cast_nonneg _
      have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
      nlinarith
    have h4 : Real.sqrt (C₀ * M ^ 2) = Real.sqrt C₀ * M := by
      rw [Real.sqrt_mul hC₀.le, Real.sqrt_sq (by linarith)]
    rw [← h4]
    exact Real.le_sqrt_of_sq_le h3
  -- decomposition of the counted pairs
  set A1 := (P ×ˢ P).filter (fun pq => ∃ ℓ ∈ L, pq.2 ∈ S ℓ ∧ pq.1 ∈ ℓ) with hA1
  set A2 := (P ×ˢ P).filter
    (fun pq => ∃ ℓ ∈ L, pq.2 ∈ S ℓ ∧ ∃ H ∈ 𝓗 pq.1, ℓ ≤ H ∧ pq.1 ∈ H) with hA2
  have hsplit : linePairs P L S 𝓗 ⊆ A1 ∪ A2 := by
    intro pq hpq
    obtain ⟨hpqP, ℓ, hℓ, hq, hor⟩ := mem_filter.mp hpq
    rcases hor with hp | hspan
    · exact mem_union_left _ (mem_filter.mpr ⟨hpqP, ℓ, hℓ, hq, hp⟩)
    · refine mem_union_right _ (mem_filter.mpr ⟨hpqP, ℓ, hℓ, hq, _, hspan, ?_, ?_⟩)
      · intro x hx
        exact subset_affineSpan ℝ _ (Set.mem_insert_of_mem _ hx)
      · exact mem_affineSpan ℝ (Set.mem_insert _ _)
  -- bound on A1
  have hA1card : (A1.card : ℝ) ≤ Real.sqrt C₀ * M * N := by
    have hsub : A1 ⊆ L.biUnion (fun ℓ => (P.filter (· ∈ ℓ)) ×ˢ S ℓ) := by
      intro pq hpq
      obtain ⟨hpqP, ℓ, hℓ, hq, hp⟩ := mem_filter.mp hpq
      exact mem_biUnion.mpr ⟨ℓ, hℓ, mem_product.mpr
        ⟨mem_filter.mpr ⟨(mem_product.mp hpqP).1, hp⟩, hq⟩⟩
    have h1 : A1.card ≤ ∑ ℓ ∈ L, occ P ℓ * n ℓ := by
      refine (card_le_card hsub).trans (card_biUnion_le.trans (le_of_eq ?_))
      apply sum_congr rfl; intro ℓ _; rw [card_product]; rfl
    calc (A1.card : ℝ) ≤ ∑ ℓ ∈ L, (occ P ℓ : ℝ) * n ℓ := by exact_mod_cast h1
      _ ≤ ∑ ℓ ∈ L, Real.sqrt C₀ * M * n ℓ :=
          sum_le_sum fun ℓ hℓ => mul_le_mul_of_nonneg_right (hline ℓ hℓ) (Nat.cast_nonneg _)
      _ = Real.sqrt C₀ * M * ∑ ℓ ∈ L, (n ℓ : ℝ) := by rw [mul_sum]
      _ ≤ Real.sqrt C₀ * M * N :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
  -- the plane family with `σ(H) ≥ A`
  set σ : AffineSubspace ℝ (Pt d) → ℝ := LinesCore.sig (fun ℓ H => ℓ ≤ H) L n with hσdef
  set Gs := (P.biUnion 𝓗).filter (fun H => A ≤ σ H) with hGs
  have hGs_plane : ∀ H ∈ Gs, IsRealPlane H := by
    intro H hH
    obtain ⟨p, hp, hHp⟩ := mem_biUnion.mp (mem_filter.mp hH).1
    exact (h𝓗 p hp).2 H hHp
  have hσ0 : ∀ H, 0 ≤ σ H := fun H => sum_nonneg fun ℓ _ => Nat.cast_nonneg _
  -- bound on A2
  have hA2card : (A2.card : ℝ) ≤ N * E * A + ∑ H ∈ Gs, (occ P H : ℝ) * σ H := by
    have hsub : A2 ⊆ P.biUnion (fun p => ((𝓗 p).filter (fun H => p ∈ H)).biUnion
        (fun H => ((L.filter (fun ℓ => ℓ ≤ H)).biUnion S).image (fun q => (p, q)))) := by
      intro pq hpq
      obtain ⟨hpqP, ℓ, hℓ, hq, H, hH, hℓH, hpH⟩ := mem_filter.mp hpq
      refine mem_biUnion.mpr ⟨pq.1, (mem_product.mp hpqP).1, mem_biUnion.mpr
        ⟨H, mem_filter.mpr ⟨hH, hpH⟩, mem_image.mpr ⟨pq.2, mem_biUnion.mpr
          ⟨ℓ, mem_filter.mpr ⟨hℓ, hℓH⟩, hq⟩, rfl⟩⟩⟩
    have h1 : (A2.card : ℝ) ≤ ∑ p ∈ P, ∑ H ∈ (𝓗 p).filter (fun H => p ∈ H), σ H := by
      have hnat : A2.card ≤ ∑ p ∈ P, ∑ H ∈ (𝓗 p).filter (fun H => p ∈ H),
          ∑ ℓ ∈ L.filter (fun ℓ => ℓ ≤ H), n ℓ := by
        refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun p _ => ?_))
        refine card_biUnion_le.trans (sum_le_sum fun H _ => ?_)
        exact card_image_le.trans card_biUnion_le
      have : (A2.card : ℝ) ≤ ∑ p ∈ P, ∑ H ∈ (𝓗 p).filter (fun H => p ∈ H),
          ∑ ℓ ∈ L.filter (fun ℓ => ℓ ≤ H), (n ℓ : ℝ) := by exact_mod_cast hnat
      exact this
    have h2 : ∀ p ∈ P, ∑ H ∈ (𝓗 p).filter (fun H => p ∈ H), σ H ≤
        E * A + ∑ H ∈ Gs.filter (fun H => p ∈ H), σ H := by
      intro p hp
      rw [← sum_filter_add_sum_filter_not ((𝓗 p).filter (fun H => p ∈ H)) (fun H => A ≤ σ H)]
      rw [add_comm (E * A) _]
      apply add_le_add
      · apply sum_le_sum_of_subset_of_nonneg
        · intro H hH
          obtain ⟨hH1, hAσ⟩ := mem_filter.mp hH
          obtain ⟨hH𝓗, hpH⟩ := mem_filter.mp hH1
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_biUnion.mpr ⟨p, hp, hH𝓗⟩, hAσ⟩, hpH⟩
        · intro H _ _; exact hσ0 H
      · calc ∑ H ∈ ((𝓗 p).filter (fun H => p ∈ H)).filter (fun H => ¬ A ≤ σ H), σ H
            ≤ ∑ _H ∈ ((𝓗 p).filter (fun H => p ∈ H)).filter (fun H => ¬ A ≤ σ H), A :=
              sum_le_sum fun H hH => le_of_lt (not_le.mp (mem_filter.mp hH).2)
          _ ≤ ∑ _H ∈ 𝓗 p, A := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro H hH; exact (mem_filter.mp (mem_filter.mp hH).1).1
              · intro _ _ _; exact hA.le
          _ = (𝓗 p).card * A := by rw [sum_const, nsmul_eq_mul]
          _ ≤ E * A := mul_le_mul_of_nonneg_right (h𝓗 p hp).1 hA.le
    have h3 : ∑ p ∈ P, ∑ H ∈ Gs.filter (fun H => p ∈ H), σ H =
        ∑ H ∈ Gs, (occ P H : ℝ) * σ H := by
      simp only [sum_filter]
      rw [sum_comm]
      apply sum_congr rfl; intro H _
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      rfl
    calc (A2.card : ℝ) ≤ ∑ p ∈ P, ∑ H ∈ (𝓗 p).filter (fun H => p ∈ H), σ H := h1
      _ ≤ ∑ p ∈ P, (E * A + ∑ H ∈ Gs.filter (fun H => p ∈ H), σ H) := sum_le_sum h2
      _ = N * E * A + ∑ H ∈ Gs, (occ P H : ℝ) * σ H := by
          rw [sum_add_distrib, h3, sum_const, nsmul_eq_mul]; simp only [hNdef, cfgN]; ring
  -- the abstract layer-cake bound
  have habs : 2 * C₁ * C₀ * M ^ 2 ≤ A ^ 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * C₁ * C₀ by positivity)
    have hs0 := Real.sqrt_nonneg (2 * C₁ * C₀)
    have hKM' : 0 ≤ (Real.sqrt (2 * C₁ * C₀) + 1) * M := by positivity
    nlinarith
  have hcore := LinesCore.planes_weighted_sum (fun ℓ H => ℓ ≤ H) L Gs n (occ P) C₀ C₁ M N A
    ⌊h⌋₊ hC₀ hC₁ hA hN0
    (fun L' hL' G' hG' => hinc L' G' (fun ℓ hℓ => hL ℓ (hL' hℓ))
      (fun H hH => hGs_plane H (hG' hH)))
    (fun ℓ hℓ H hH hℓH => by
      have h1 := hocc P ℓ H (hL ℓ hℓ) (hGs_plane H hH) hℓH
      have h2 : (n ℓ : ℝ) ≤ occ P ℓ := by exact_mod_cast hnocc ℓ hℓ
      have h3 : (0 : ℝ) ≤ occ P H := Nat.cast_nonneg _
      have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
      nlinarith)
    hmass
    (fun H hH => (mem_filter.mp hH).2)
    (fun H _ => hsig_occ H)
    (fun H hH => Nat.le_floor (hh H (hGs_plane H hH)))
    habs
  -- assemble
  have hfloor : ((⌊h⌋₊ : ℕ) : ℝ) ≤ h := Nat.floor_le hh0
  have hlog : 1 ≤ (1 + Real.log N) ^ 2 := by
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg _
    nlinarith
  have hcard := card_le_card hsplit
  have hcardU : ((linePairs P L S 𝓗).card : ℝ) ≤ A1.card + A2.card := by
    exact_mod_cast hcard.trans (card_union_le A1 A2)
  set Cc := Real.sqrt C₀ + 4 * C₁ + 2048 * C₀ * C₁ ^ 3 with hCc
  have hp1 : 0 ≤ 2048 * C₀ * C₁ ^ 3 := by positivity
  have hp2 : 0 ≤ Real.sqrt C₀ := Real.sqrt_nonneg C₀
  have hNh : 0 ≤ N * h := mul_nonneg hN0 hh0
  have hMN : 0 ≤ M * N := by positivity
  have hX : 0 ≤ N ^ 2 * M ^ 2 / A ^ 2 := by positivity
  have e1 : Real.sqrt C₀ * M * N ≤ Cc * (M * N) := by
    have : Real.sqrt C₀ ≤ Cc := by rw [hCc]; linarith
    nlinarith
  have e2 : 4 * C₁ * N * (⌊h⌋₊ : ℝ) ≤ Cc * (N * h * (1 + Real.log N) ^ 2) := by
    have h4 : 4 * C₁ ≤ Cc := by rw [hCc]; linarith
    have : 4 * C₁ * N * (⌊h⌋₊ : ℝ) ≤ 4 * C₁ * (N * h) := by
      have := mul_le_mul_of_nonneg_left hfloor (show 0 ≤ 4 * C₁ * N by positivity)
      linarith
    calc 4 * C₁ * N * (⌊h⌋₊ : ℝ) ≤ 4 * C₁ * (N * h) := this
      _ ≤ Cc * (N * h) := mul_le_mul_of_nonneg_right h4 hNh
      _ ≤ Cc * (N * h * (1 + Real.log N) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
  have e3 : 2048 * C₀ * C₁ ^ 3 * M ^ 2 * N ^ 2 / A ^ 2 ≤ Cc * (N ^ 2 * M ^ 2 / A ^ 2) := by
    have h5 : 2048 * C₀ * C₁ ^ 3 ≤ Cc := by rw [hCc]; linarith
    have : 2048 * C₀ * C₁ ^ 3 * M ^ 2 * N ^ 2 / A ^ 2 =
        2048 * C₀ * C₁ ^ 3 * (N ^ 2 * M ^ 2 / A ^ 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right h5 hX
  calc ((linePairs P L S 𝓗).card : ℝ) ≤ A1.card + A2.card := hcardU
    _ ≤ Real.sqrt C₀ * M * N + (N * E * A + (4 * C₁ * N * ⌊h⌋₊ +
          2048 * C₀ * C₁ ^ 3 * M ^ 2 * N ^ 2 / A ^ 2)) := by
        have hcore' : ∑ H ∈ Gs, (occ P H : ℝ) * σ H ≤
            4 * C₁ * N * ⌊h⌋₊ + 2048 * C₀ * C₁ ^ 3 * M ^ 2 * N ^ 2 / A ^ 2 := hcore
        linarith
    _ ≤ A * E * N + Cc * (M * N + N * h * (1 + Real.log N) ^ 2 + N ^ 2 * M ^ 2 / A ^ 2) := by
        nlinarith

/-- `geo:terminal.lines` (`secants.tex:254–331`): the line case of `geo:terminal` in the shared
model. Directional families of degree at most `E`, any partial assignment to distinct complex
lines that are real. -/
theorem geo_terminal_lines (d : ℕ) (hd : 3 ≤ d) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ (P : Finset (Pt d)) (A E h : ℝ),
      0 < A → K * cfgM P ≤ A → 0 ≤ E →
      (∀ H : AffineSubspace ℝ (Pt d), IsRealPlane H → (occ P H : ℝ) ≤ h) →
      ∀ Cf : Pt d → ProjectiveFamily.Family d,
        (∀ p ∈ P, IsDirectionalFamily (Cf p) ∧ (ProjectiveFamily.degree (Cf p) : ℝ) ≤ E) →
      ∀ (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d)),
        Assignment P 𝒴 S → (∀ Y ∈ 𝒴, IsLine Y → IsRealFlat Y) →
        (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
            ∃ Y ∈ 𝒴, IsLine Y ∧ pq.2 ∈ S Y ∧ ProjectsInto (Cf pq.1) pq.1 Y)).card : ℝ) ≤
          A * E * cfgN P +
            C * (cfgM P * cfgN P + cfgN P * h * (1 + Real.log (cfgN P)) ^ 2 +
              cfgN P ^ 2 * cfgM P ^ 2 / A ^ 2) := by
  have hLP := terminal_slice d hd (ci_st_incidence (d-1))
  obtain ⟨CLP, hCLP, hocc⟩ := terminal_lineplane d (ci_st_incidence 2)
  obtain ⟨K, C, hK, hC, hcore⟩ := terminal_lines_core d hd hLP CLP hocc
  refine ⟨K, C, hK, hC, ?_⟩
  intro P A E h hA hKM hE hh Cf hCf 𝒴 S hS hreal
  let L := GeoLines.realLines 𝒴
  let S' := GeoLines.realAssignment 𝒴 S
  let ℋ := GeoLines.recordedPlanes 𝒴 Cf
  have hL : ∀ ℓ ∈ L, IsRealLine ℓ := GeoLines.realLines_are_lines 𝒴 hreal
  have hS' : ∀ ℓ ∈ L, S' ℓ ⊆ P.filter (· ∈ ℓ) :=
    GeoLines.realAssignment_subset P 𝒴 S hS hreal
  have hdisj : (L : Set (AffineSubspace ℝ (Pt d))).PairwiseDisjoint S' :=
    GeoLines.realAssignment_disjoint P 𝒴 S hS
  have hℋ : ∀ p ∈ P, ((ℋ p).card : ℝ) ≤ E ∧ ∀ H ∈ ℋ p, IsRealPlane H := by
    intro p hp
    refine ⟨?_, GeoLines.recordedPlanes_are_planes 𝒴 hreal Cf p⟩
    have hcard : ((ℋ p).card : ℝ) ≤ (Cf p).card := by
      exact_mod_cast GeoLines.recordedPlanes_card 𝒴 Cf p
    exact hcard.trans ((GeoLines.family_card_le_degree (Cf p) (hCf p hp).1).trans (hCf p hp).2)
  have hbound := hcore P A E h hA hKM hE hh L S' hL hS' hdisj ℋ hℋ
  have hsub : (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
      ∃ Y ∈ 𝒴, IsLine Y ∧ pq.2 ∈ S Y ∧ ProjectsInto (Cf pq.1) pq.1 Y) ⊆ linePairs P L S' ℋ := by
    intro pq hpq
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_filter.mp hpq).1,
      GeoLines.selected_pair_cover P Cf (fun p hp => (hCf p hp).1) 𝒴 S hreal pq hpq⟩
  have hcard : (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
      ∃ Y ∈ 𝒴, IsLine Y ∧ pq.2 ∈ S Y ∧ ProjectsInto (Cf pq.1) pq.1 Y)).card : ℝ) ≤
      (linePairs P L S' ℋ).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hbound

end

end TrackD
end DistinctDistances
