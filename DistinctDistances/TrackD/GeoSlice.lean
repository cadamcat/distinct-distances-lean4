import DistinctDistances.TrackD.GeoSliceArrangement

/-! Transfer of real line–plane containments to point–line incidences after a generic slice. -/

namespace DistinctDistances.TrackD.GeoSlice
open scoped Classical
open Finset
noncomputable section

theorem slice_incidence (d : ℕ) (hd : 3 ≤ d) (hST : STIncidence (d-1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L H : Finset (AffineSubspace ℝ (Pt d))),
      (∀ F ∈ L, IsRealLine F) → (∀ F ∈ H, IsRealPlane F) →
      (((L ×ˢ H).filter (fun FG => FG.1 ≤ FG.2)).card : ℝ) ≤
        C * (((L.card : ℝ)*H.card)^((2 : ℝ)/3)+L.card+H.card) := by
  obtain ⟨C, hC, hST⟩ := hST
  refine ⟨C, hC, ?_⟩
  intro L H hL hH
  by_cases hLne : L.Nonempty
  swap
  · have hLe : L = ∅ := not_nonempty_iff_eq_empty.mp hLne
    have hzero : ((L ×ˢ H).filter (fun FG => FG.1 ≤ FG.2)).card = 0 := by simp [hLe]
    rw [hzero, Nat.cast_zero]
    positivity
  obtain ⟨F₀, hF₀⟩ := hLne
  obtain ⟨φ, hφL, hφH, hφI⟩ := good_functional L H
  have hLT : ∀ F ∈ L, ∃ v ∈ F.direction, φ v ≠ 0 := by
    intro F hF
    exact hφL F hF (direction_ne_bot_of_rank F 1 (by omega) (hL F hF))
  have hHT : ∀ F ∈ H, ∃ v ∈ F.direction, φ v ≠ 0 := by
    intro F hF
    exact hφH F hF (direction_ne_bot_of_rank F 2 (by omega) (hH F hF))
  have hφ : φ ≠ 0 := by
    intro he
    obtain ⟨v, -, hv⟩ := hLT F₀ hF₀
    apply hv
    rw [he]; rfl
  obtain ⟨u, hu⟩ := LinearMap.surjective hφ (1 : ℝ)
  obtain ⟨t, ht⟩ := (badOffsets φ L).exists_notMem
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  have hedim : Module.finrank ℝ (LinearMap.ker φ) = Module.finrank ℝ (Pt (d-1)) := by
    simp only [Pt, finrank_euclideanSpace, Fintype.card_fin] at hdim ⊢
    omega
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hedim
  let g := coords φ u hu e
  let a : AffineSubspace ℝ (Pt d) → Pt (d-1) := fun F => g (point (F ⊓ level φ t u))
  let b : AffineSubspace ℝ (Pt d) → AffineSubspace ℝ (Pt (d-1)) :=
    fun F => (F ⊓ level φ t u).map g.toAffineMap
  have hpoints := slice_points_injective φ t u hu L hL hLT ht
  have hplanes := slice_planes_injective φ t u hu H hH hHT hφI
  have hglevel := coords_injective_level φ t u hu e
  have ha : Set.InjOn a (L : Set (AffineSubspace ℝ (Pt d))) := by
    intro F hF G hG he
    apply hpoints hF hG
    exact hglevel (slice_point_mem φ t u hu F (hL F hF) (hLT F hF)).2
      (slice_point_mem φ t u hu G (hL G hG) (hLT G hG)).2 he
  have hb : Set.InjOn b (H : Set (AffineSubspace ℝ (Pt d))) := by
    intro F hF G hG he
    apply hplanes hF hG
    exact map_injective_on_level φ t u hu e (F ⊓ level φ t u) (G ⊓ level φ t u)
      inf_le_right inf_le_right he
  have hline : ∀ F ∈ H, IsRealLine (b F) := by
    intro F hF
    have hr := slice_plane_rank φ t u hu F (hH F hF) (hHT F hF)
    have hW : (F ⊓ level φ t u).direction ≤ LinearMap.ker φ := by
      have h := AffineSubspace.direction_le (show F ⊓ level φ t u ≤ level φ t u from inf_le_right)
      rwa [level_direction] at h
    have hi : Set.InjOn g ((F ⊓ level φ t u).direction : Set (Pt d)) :=
      (coords_injective_ker φ u hu e).mono hW
    unfold IsRealLine
    dsimp only [b]
    rw [AffineSubspace.map_direction, LinearMap.toAffineMap_linear, rank_map g _ hi]
    exact hr
  let Q := L.image a
  let T := H.image b
  let I := (Q ×ˢ T).filter (fun z => z.1 ∈ z.2)
  let S := (L ×ˢ H).filter (fun FG => FG.1 ≤ FG.2)
  let f : AffineSubspace ℝ (Pt d) × AffineSubspace ℝ (Pt d) →
      Pt (d-1) × AffineSubspace ℝ (Pt (d-1)) := fun FG => (a FG.1,b FG.2)
  have hf : Set.MapsTo f (S : Set _) (I : Set _) := by
    intro FG hFG
    obtain ⟨hFG, hle⟩ := mem_filter.mp hFG
    obtain ⟨hF, hG⟩ := mem_product.mp hFG
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_image_of_mem _ hF,mem_image_of_mem _ hG⟩, ?_⟩
    have hp := slice_point_mem φ t u hu FG.1 (hL FG.1 hF) (hLT FG.1 hF)
    exact AffineSubspace.mem_map_of_mem g.toAffineMap ⟨hle hp.1,hp.2⟩
  have hfi : Set.InjOn f (S : Set _) := by
    intro FG hFG F'G' hF'G' he
    have hFG' := mem_product.mp (mem_filter.mp hFG).1
    have hF'G'' := mem_product.mp (mem_filter.mp hF'G').1
    exact Prod.ext (ha hFG'.1 hF'G''.1 (congrArg Prod.fst he))
      (hb hFG'.2 hF'G''.2 (congrArg Prod.snd he))
  have hcount := card_le_card_of_injOn f hf hfi
  have hcount' : (S.card : ℝ) ≤ I.card := by exact_mod_cast hcount
  have hinc := hST Q T (by
    intro F hF
    obtain ⟨G, hG, rfl⟩ := mem_image.mp hF
    exact hline G hG)
  have hQcard : Q.card = L.card := card_image_of_injOn ha
  have hTcard : T.card = H.card := card_image_of_injOn hb
  rw [hQcard,hTcard] at hinc
  exact hcount'.trans hinc

end
end DistinctDistances.TrackD.GeoSlice
