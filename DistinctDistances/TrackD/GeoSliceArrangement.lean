import DistinctDistances.TrackD.GeoSliceLinear

/-! A single hyperplane preserves distinct lines and planes in a finite arrangement. -/

namespace DistinctDistances.TrackD.GeoSlice
open scoped Classical
open Finset
noncomputable section
variable {d : ℕ}

theorem direction_ne_bot_of_rank (F : AffineSubspace ℝ (Pt d)) (r : ℕ)
    (hr : 0 < r) (hF : Module.finrank ℝ F.direction = r) : F.direction ≠ ⊥ := by
  intro he
  rw [he, finrank_bot] at hF
  omega

theorem good_functional (L H : Finset (AffineSubspace ℝ (Pt d))) :
    ∃ φ : Module.Dual ℝ (Pt d),
      (∀ F ∈ L, F.direction ≠ ⊥ → ∃ v ∈ F.direction, φ v ≠ 0) ∧
      (∀ F ∈ H, F.direction ≠ ⊥ → ∃ v ∈ F.direction, φ v ≠ 0) ∧
      (∀ F ∈ H, ∀ G ∈ H, F ≠ G → (F ⊓ G).direction ≠ ⊥ →
        ∃ v ∈ (F ⊓ G).direction, φ v ≠ 0) := by
  let S := (L.image AffineSubspace.direction ∪ H.image AffineSubspace.direction) ∪
    (((H ×ˢ H).filter (fun FG => FG.1 ≠ FG.2)).image (fun FG => (FG.1 ⊓ FG.2).direction))
  obtain ⟨φ, hφ⟩ := finite_functional S
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro F hF
    apply hφ
    exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ hF))
  · intro F hF
    apply hφ
    exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hF))
  · intro F hF G hG hFG
    apply hφ
    exact mem_union_right _ (mem_image.mpr ⟨(F,G), mem_filter.mpr
      ⟨mem_product.mpr ⟨hF,hG⟩,hFG⟩, rfl⟩)

def point (F : AffineSubspace ℝ (Pt d)) : Pt d :=
  if h : (F : Set (Pt d)).Nonempty then h.choose else 0

theorem point_mem (F : AffineSubspace ℝ (Pt d)) (h : (F : Set (Pt d)).Nonempty) : point F ∈ F := by
  simp only [point, dif_pos h]
  exact h.choose_spec

def badOffsets (φ : Module.Dual ℝ (Pt d)) (L : Finset (AffineSubspace ℝ (Pt d))) : Finset ℝ :=
  ((L ×ˢ L).filter (fun FG => FG.1 ≠ FG.2 ∧
    ((FG.1 ⊓ FG.2) : Set (Pt d)).Nonempty)).image (fun FG => φ (point (FG.1 ⊓ FG.2)))

theorem offset_avoids_intersection (φ : Module.Dual ℝ (Pt d)) (t : ℝ)
    (L : Finset (AffineSubspace ℝ (Pt d))) (hL : ∀ F ∈ L, IsRealLine F)
    (ht : t ∉ badOffsets φ L) (F G : AffineSubspace ℝ (Pt d)) (hF : F ∈ L) (hG : G ∈ L)
    (hFG : F ≠ G) (x : Pt d) (hxF : x ∈ F) (hxG : x ∈ G) : φ x ≠ t := by
  intro he
  have hx : x ∈ F ⊓ G := ⟨hxF,hxG⟩
  have hne : ((F ⊓ G) : Set (Pt d)).Nonempty := ⟨x,hx⟩
  have hpoint : point (F ⊓ G) = x :=
    line_intersection_subsingleton F G (hL F hF) (hL G hG) hFG (point_mem (F ⊓ G) hne) hx
  apply ht
  exact mem_image.mpr ⟨(F,G), mem_filter.mpr ⟨mem_product.mpr ⟨hF,hG⟩,hFG,hne⟩,
    by rw [hpoint, he]⟩

theorem slice_point_mem (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) (hu : φ u = 1)
    (F : AffineSubspace ℝ (Pt d)) (hF : IsRealLine F)
    (hw : ∃ v ∈ F.direction, φ v ≠ 0) :
    point (F ⊓ level φ t u) ∈ F ∧ point (F ⊓ level φ t u) ∈ level φ t u := by
  have hne := slice_nonempty φ t u hu F
    (affine_nonempty F (direction_ne_bot_of_rank F 1 (by omega) hF)) hw
  exact point_mem (F ⊓ level φ t u) hne

theorem slice_points_injective (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) (hu : φ u = 1)
    (L : Finset (AffineSubspace ℝ (Pt d))) (hL : ∀ F ∈ L, IsRealLine F)
    (hw : ∀ F ∈ L, ∃ v ∈ F.direction, φ v ≠ 0) (ht : t ∉ badOffsets φ L) :
    Set.InjOn (fun F => point (F ⊓ level φ t u)) (L : Set (AffineSubspace ℝ (Pt d))) := by
  intro F hF G hG he
  change point (F ⊓ level φ t u) = point (G ⊓ level φ t u) at he
  by_contra hFG
  have hpF := slice_point_mem φ t u hu F (hL F hF) (hw F hF)
  have hpG := slice_point_mem φ t u hu G (hL G hG) (hw G hG)
  have hz := offset_avoids_intersection φ t L hL ht F G hF hG hFG
    (point (F ⊓ level φ t u)) hpF.1 (he.symm ▸ hpG.1)
  exact hz ((level_mem φ t u hu _).mp hpF.2)

theorem slice_plane_rank (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) (hu : φ u = 1)
    (F : AffineSubspace ℝ (Pt d)) (hF : IsRealPlane F)
    (hw : ∃ v ∈ F.direction, φ v ≠ 0) : IsRealLine (F ⊓ level φ t u) := by
  have hne := slice_nonempty φ t u hu F
    (affine_nonempty F (direction_ne_bot_of_rank F 2 (by omega) hF)) hw
  unfold IsRealLine
  rw [slice_direction φ t u F hne]
  have hr := inf_ker_rank φ F.direction hw
  change Module.finrank ℝ F.direction = 2 at hF
  omega

theorem slice_planes_injective (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) (hu : φ u = 1)
    (H : Finset (AffineSubspace ℝ (Pt d))) (hH : ∀ F ∈ H, IsRealPlane F)
    (hw : ∀ F ∈ H, ∃ v ∈ F.direction, φ v ≠ 0)
    (hi : ∀ F ∈ H, ∀ G ∈ H, F ≠ G → (F ⊓ G).direction ≠ ⊥ →
      ∃ v ∈ (F ⊓ G).direction, φ v ≠ 0) :
    Set.InjOn (fun F => F ⊓ level φ t u) (H : Set (AffineSubspace ℝ (Pt d))) := by
  intro F hF G hG he
  change F ⊓ level φ t u = G ⊓ level φ t u at he
  by_contra hFG
  have hr := intersection_rank_lt F G 2 (by omega) (hH F hF) (hH G hG) hFG
  have hk := inf_ker_bot φ (F ⊓ G).direction (by omega) (hi F hF G hG hFG)
  have hle : F ⊓ level φ t u ≤ F ⊓ G := le_inf inf_le_left (by rw [he]; exact inf_le_left)
  have hd : (F ⊓ level φ t u).direction ≤ (F ⊓ G).direction ⊓ LinearMap.ker φ := by
    refine le_inf (AffineSubspace.direction_le hle) ?_
    have h := AffineSubspace.direction_le (show F ⊓ level φ t u ≤ level φ t u from inf_le_right)
    rwa [level_direction] at h
  rw [hk] at hd
  have hzero : (F ⊓ level φ t u).direction = ⊥ := eq_bot_iff.mpr hd
  have hrank := slice_plane_rank φ t u hu F (hH F hF) (hw F hF)
  unfold IsRealLine at hrank
  rw [hzero, finrank_bot] at hrank
  omega

end
end DistinctDistances.TrackD.GeoSlice
