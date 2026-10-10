import DistinctDistances.TrackD.Inputs
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Finite transversality, affine level sets and coordinates for a generic slice. -/

namespace DistinctDistances.TrackD.GeoSlice
open scoped Classical
open Finset
noncomputable section
variable {d m : ℕ}

theorem affine_nonempty (F : AffineSubspace ℝ (Pt d)) (hF : F.direction ≠ ⊥) :
    (F : Set (Pt d)).Nonempty := by
  by_contra hn
  apply hF
  apply AffineSubspace.direction_eq_bot_iff.mpr
  rw [Set.not_nonempty_iff_eq_empty.mp hn]
  exact Set.subsingleton_empty

theorem intersection_rank_lt (F G : AffineSubspace ℝ (Pt d)) (r : ℕ) (hr : 0 < r)
    (hF : Module.finrank ℝ F.direction = r) (hG : Module.finrank ℝ G.direction = r)
    (hFG : F ≠ G) : Module.finrank ℝ (F ⊓ G).direction < r := by
  by_cases hne : ((F ⊓ G) : Set (Pt d)).Nonempty
  · have hleF : (F ⊓ G).direction ≤ F.direction := AffineSubspace.direction_le inf_le_left
    have hleG : (F ⊓ G).direction ≤ G.direction := AffineSubspace.direction_le inf_le_right
    have hle := Submodule.finrank_mono hleF
    rw [hF] at hle
    by_contra! hn
    have he : Module.finrank ℝ (F ⊓ G).direction = r := le_antisymm hle hn
    have heF := Submodule.eq_of_le_of_finrank_eq hleF (he.trans hF.symm)
    have heG := Submodule.eq_of_le_of_finrank_eq hleG (he.trans hG.symm)
    have hIF := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le heF hne inf_le_left
    have hIG := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le heG hne inf_le_right
    exact hFG (hIF.symm.trans hIG)
  · have hs : ((F ⊓ G) : Set (Pt d)).Subsingleton := by
      rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact Set.subsingleton_empty
    rw [AffineSubspace.direction_eq_bot_iff.mpr hs, finrank_bot]
    exact hr

theorem line_intersection_subsingleton (F G : AffineSubspace ℝ (Pt d))
    (hF : IsRealLine F) (hG : IsRealLine G) (hFG : F ≠ G) :
    ((F ⊓ G) : Set (Pt d)).Subsingleton := by
  have hr := intersection_rank_lt F G 1 (by omega) hF hG hFG
  have hd : (F ⊓ G).direction = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  exact AffineSubspace.direction_eq_bot_iff.mp hd

theorem finite_functional (S : Finset (Submodule ℝ (Pt d))) :
    ∃ φ : Module.Dual ℝ (Pt d), ∀ W ∈ S, W ≠ ⊥ → ∃ v ∈ W, φ v ≠ 0 := by
  let T := S.filter (· ≠ ⊥)
  have hex : ∀ W : T, ∃ v ∈ (W.val : Submodule ℝ (Pt d)), v ≠ 0 := by
    intro W
    exact (Submodule.ne_bot_iff W.val).mp (mem_filter.mp W.property).2
  let v : T → Pt d := fun W => (hex W).choose
  have hv : ∀ W : T, v W ≠ 0 := fun W => (hex W).choose_spec.2
  obtain ⟨φ, hφ⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) v hv
  refine ⟨φ, ?_⟩
  intro W hW hW0
  let w : T := ⟨W, mem_filter.mpr ⟨hW, hW0⟩⟩
  exact ⟨v w, (hex w).choose_spec.1, hφ w⟩

theorem inf_ker_rank (φ : Module.Dual ℝ (Pt d)) (W : Submodule ℝ (Pt d))
    (hw : ∃ v ∈ W, φ v ≠ 0) :
    Module.finrank ℝ ↥(W ⊓ LinearMap.ker φ) + 1 = Module.finrank ℝ W := by
  have hf : φ.domRestrict W ≠ 0 := by
    intro he
    obtain ⟨v, hv, hφ⟩ := hw
    have hz := congrArg (fun f : W →ₗ[ℝ] ℝ => f ⟨v,hv⟩) he
    exact hφ hz
  have hr := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have he : Module.finrank ℝ ↥(W ⊓ LinearMap.ker φ) =
      Module.finrank ℝ (LinearMap.ker (φ.domRestrict W)) := by
    change Module.finrank ℝ ↥(W ⊓ LinearMap.ker φ) =
      Module.finrank ℝ ((LinearMap.ker φ).comap W.subtype)
    rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  rw [he]
  exact hr

theorem inf_ker_bot (φ : Module.Dual ℝ (Pt d)) (W : Submodule ℝ (Pt d))
    (hr : Module.finrank ℝ W ≤ 1) (hw : W ≠ ⊥ → ∃ v ∈ W, φ v ≠ 0) :
    W ⊓ LinearMap.ker φ = ⊥ := by
  by_cases hW : W = ⊥
  · simp [hW]
  · apply Submodule.finrank_eq_zero.mp
    have h := inf_ker_rank φ W (hw hW)
    omega

def level (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) : AffineSubspace ℝ (Pt d) :=
  AffineSubspace.mk' (t • u) (LinearMap.ker φ)

theorem level_mem (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) (hu : φ u = 1) (x : Pt d) :
    x ∈ level φ t u ↔ φ x = t := by
  simp only [level, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker,
    map_sub, map_smul, smul_eq_mul, hu, mul_one, sub_eq_zero]

theorem level_direction (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) :
    (level φ t u).direction = LinearMap.ker φ := AffineSubspace.direction_mk' _ _

theorem slice_nonempty (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) (hu : φ u = 1)
    (F : AffineSubspace ℝ (Pt d)) (hF : (F : Set (Pt d)).Nonempty)
    (hw : ∃ v ∈ F.direction, φ v ≠ 0) : ((F ⊓ level φ t u) : Set (Pt d)).Nonempty := by
  obtain ⟨a, ha⟩ := hF
  obtain ⟨v, hv, hφ⟩ := hw
  refine ⟨((t-φ a)/φ v) • v + a, ?_⟩
  apply (AffineSubspace.mem_inf_iff _ _ _).mpr
  refine ⟨AffineSubspace.vadd_mem_of_mem_direction (F.direction.smul_mem _ hv) ha, ?_⟩
  rw [level_mem φ t u hu]
  simp only [map_add, map_smul, smul_eq_mul]
  field_simp
  ring

theorem slice_direction (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d)
    (F : AffineSubspace ℝ (Pt d)) (hne : ((F ⊓ level φ t u) : Set (Pt d)).Nonempty) :
    (F ⊓ level φ t u).direction = F.direction ⊓ LinearMap.ker φ := by
  obtain ⟨a, ha⟩ := hne
  rw [AffineSubspace.direction_inf_of_mem_inf ha, level_direction]

def projection (φ : Module.Dual ℝ (Pt d)) (u : Pt d) (hu : φ u = 1) :
    Pt d →ₗ[ℝ] LinearMap.ker φ where
  toFun x := ⟨x - φ x • u, by simp [LinearMap.mem_ker, hu]⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [map_add, add_smul, Submodule.coe_add]
    abel
  map_smul' s x := by
    apply Subtype.ext
    simp only [map_smul, smul_eq_mul, Submodule.coe_smul, smul_sub, smul_smul, RingHom.id_apply]

def coords (φ : Module.Dual ℝ (Pt d)) (u : Pt d) (hu : φ u = 1)
    (e : LinearMap.ker φ ≃ₗ[ℝ] Pt m) : Pt d →ₗ[ℝ] Pt m :=
  e.toLinearMap.comp (projection φ u hu)

theorem coords_injective_level (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) (hu : φ u = 1)
    (e : LinearMap.ker φ ≃ₗ[ℝ] Pt m) :
    Set.InjOn (coords φ u hu e) (level φ t u : Set (Pt d)) := by
  intro x hx y hy h
  have he := congrArg Subtype.val (e.injective h)
  change x-φ x • u = y-φ y • u at he
  rw [(level_mem φ t u hu x).mp hx, (level_mem φ t u hu y).mp hy] at he
  exact (sub_left_inj).mp he

theorem coords_injective_ker (φ : Module.Dual ℝ (Pt d)) (u : Pt d) (hu : φ u = 1)
    (e : LinearMap.ker φ ≃ₗ[ℝ] Pt m) :
    Set.InjOn (coords φ u hu e) (LinearMap.ker φ : Set (Pt d)) := by
  intro x hx y hy h
  have he := congrArg Subtype.val (e.injective h)
  change x-φ x • u = y-φ y • u at he
  rw [LinearMap.mem_ker.mp hx, LinearMap.mem_ker.mp hy] at he
  simpa using he

theorem rank_map (f : Pt d →ₗ[ℝ] Pt m) (W : Submodule ℝ (Pt d))
    (hf : Set.InjOn f (W : Set (Pt d))) :
    Module.finrank ℝ (W.map f) = Module.finrank ℝ W := by
  have hi : Function.Injective (f.domRestrict W) := by
    intro x y he
    exact Subtype.ext (hf x.property y.property he)
  have he : LinearMap.range (f.domRestrict W) = W.map f := by
    ext y
    simp only [LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x,hx⟩, rfl⟩
  rw [← he]
  exact LinearMap.finrank_range_of_inj hi

theorem map_injective_on_level (φ : Module.Dual ℝ (Pt d)) (t : ℝ) (u : Pt d) (hu : φ u = 1)
    (e : LinearMap.ker φ ≃ₗ[ℝ] Pt m) (F G : AffineSubspace ℝ (Pt d))
    (hF : F ≤ level φ t u) (hG : G ≤ level φ t u)
    (h : F.map (coords φ u hu e).toAffineMap = G.map (coords φ u hu e).toAffineMap) : F = G := by
  have hi := coords_injective_level φ t u hu e
  apply le_antisymm
  · intro x hx
    have hm : coords φ u hu e x ∈ G.map (coords φ u hu e).toAffineMap :=
      h ▸ AffineSubspace.mem_map_of_mem (coords φ u hu e).toAffineMap hx
    obtain ⟨y, hy, he⟩ := AffineSubspace.mem_map.mp hm
    have he' : y = x := hi (hG hy) (hF hx) he
    exact he' ▸ hy
  · intro x hx
    have hm : coords φ u hu e x ∈ F.map (coords φ u hu e).toAffineMap :=
      h.symm ▸ AffineSubspace.mem_map_of_mem (coords φ u hu e).toAffineMap hx
    obtain ⟨y, hy, he⟩ := AffineSubspace.mem_map.mp hm
    have he' : y = x := hi (hF hy) (hG hx) he
    exact he' ▸ hy

end
end DistinctDistances.TrackD.GeoSlice
