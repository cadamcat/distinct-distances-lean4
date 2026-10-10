import DistinctDistances.TrackD.Inputs
import Mathlib.Geometry.Euclidean.Basic

/-! Distance fibers and a paraboloid lift without choosing plane coordinates. -/

namespace DistinctDistances.TrackD.GeoLinePlane
open scoped BigOperators Classical
open Finset
noncomputable section
variable {d : ℕ}

theorem card_two {α : Type*} [DecidableEq α] (s : Finset α)
    (h : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → z = x ∨ z = y) : s.card ≤ 2 := by
  by_contra! hn
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := two_lt_card_iff.mp hn
  exact (h x hx y hy z hz hxy).elim (fun he => hxz he.symm) (fun he => hyz he.symm)

theorem line_params (ℓ : AffineSubspace ℝ (Pt d)) (hℓ : IsRealLine ℓ)
    (a : Pt d) (ha : a ∈ ℓ) :
    ∃ v : Pt d, v ≠ 0 ∧ ∀ x : Pt d, x ∈ ℓ ↔ ∃ t : ℝ, x = a + t • v := by
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one
    (R := ℝ) (M := ℓ.direction) hℓ
  let w : ℓ.direction := e 1
  have hw : w ≠ 0 := by
    intro hz
    exact one_ne_zero (e.injective (hz.trans e.map_zero.symm))
  refine ⟨w.val, fun hz => hw (Subtype.ext hz), ?_⟩
  intro x
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem ha x]
  change (x - a ∈ ℓ.direction) ↔ ∃ t : ℝ, x = a + t • w.val
  constructor
  · intro hx
    let u : ℓ.direction := ⟨x-a, hx⟩
    have ht : e.symm u • w = u := by
      dsimp only [w]
      rw [← e.map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]
    refine ⟨e.symm u, ?_⟩
    have he := congrArg Subtype.val ht
    change e.symm u • w.val = x-a at he
    rw [he]; abel
  · rintro ⟨t, rfl⟩
    rw [add_sub_cancel_left]
    exact ℓ.direction.smul_mem t w.property

theorem line_nonempty (ℓ : AffineSubspace ℝ (Pt d)) (hℓ : IsRealLine ℓ) :
    (ℓ : Set (Pt d)).Nonempty := by
  by_contra hn
  have hs : (ℓ : Set (Pt d)).Subsingleton := by
    rw [Set.not_nonempty_iff_eq_empty.mp hn]; exact Set.subsingleton_empty
  have he := AffineSubspace.direction_eq_bot_iff.mpr hs
  unfold IsRealLine at hℓ
  rw [he, finrank_bot] at hℓ
  omega

theorem param_injective (a v : Pt d) (hv : v ≠ 0) :
    Function.Injective (fun t : ℝ => a + t • v) := by
  intro s t h
  have hs : s • v = t • v := add_left_cancel h
  exact (smul_left_injective ℝ hv) hs

theorem line_distance_fiber (s : Finset (Pt d)) (ℓ : AffineSubspace ℝ (Pt d))
    (hℓ : IsRealLine ℓ) (hs : ∀ x ∈ s, x ∈ ℓ) (c : Pt d) (r : ℝ) :
    (s.filter (fun x => dist x c = r)).card ≤ 2 := by
  apply card_two
  intro x hx y hy z hz hxy
  obtain ⟨hxS, hxD⟩ := mem_filter.mp hx
  obtain ⟨hyS, hyD⟩ := mem_filter.mp hy
  obtain ⟨hzS, hzD⟩ := mem_filter.mp hz
  obtain ⟨v, hv, hp⟩ := line_params ℓ hℓ x (hs x hxS)
  obtain ⟨t, rfl⟩ := (hp y).mp (hs y hyS)
  obtain ⟨u, rfl⟩ := (hp z).mp (hs z hzS)
  have ht : t ≠ 0 := by intro he; simp [he] at hxy
  have hd (k : ℝ) : dist (x+k • v) c = dist x c ↔
      k = 0 ∨ k = -2 * inner ℝ v (x-c) / inner ℝ v v := by
    simpa only [vadd_eq_add, vsub_eq_sub, add_comm] using
      EuclideanGeometry.dist_smul_vadd_eq_dist x c hv k
  have ht' := ((hd t).mp (hyD.trans hxD.symm)).resolve_left ht
  rcases (hd u).mp (hzD.trans hxD.symm) with hu | hu
  · left; simp [hu]
  · right; rw [hu, ht']

theorem plane_distance_fiber (s : Finset (Pt d)) (H : AffineSubspace ℝ (Pt d))
    (hH : IsRealPlane H) (hs : ∀ x ∈ s, x ∈ H) (a b : Pt d)
    (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) (r t : ℝ) :
    (s.filter (fun x => dist x a = r ∧ dist x b = t)).card ≤ 2 := by
  apply card_two
  intro x hx y hy z hz hxy
  obtain ⟨hxS, hxD, hxE⟩ := mem_filter.mp hx
  obtain ⟨hyS, hyD, hyE⟩ := mem_filter.mp hy
  obtain ⟨hzS, hzD, hzE⟩ := mem_filter.mp hz
  exact EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two
    hH ha hb (hs x hxS) (hs y hyS) (hs z hzS) hab hxy hxD hyD hzD hxE hyE hzE

def distances (P : Finset (Pt d)) : Finset ℝ := insert 0 (distanceSet P)

theorem mem_distances (P : Finset (Pt d)) {x y : Pt d} (hx : x ∈ P) (hy : y ∈ P) :
    dist x y ∈ distances P := by
  by_cases h : x = y
  · simp [distances, h]
  · exact mem_insert_of_mem (mem_image.mpr ⟨(x,y), mem_offDiag.mpr ⟨hx, hy, h⟩, rfl⟩)

theorem distances_card (P : Finset (Pt d)) : (distances P).card = distinctDistances P + 1 := by
  apply card_insert_of_notMem
  rintro h
  obtain ⟨⟨x,y⟩, hxy, he⟩ := mem_image.mp h
  exact (mem_offDiag.mp hxy).2.2 (dist_eq_zero.mp he)

theorem distances_card_real (P : Finset (Pt d)) : ((distances P).card : ℝ) = cfgM P := by
  rw [distances_card, Nat.cast_add, Nat.cast_one]; rfl

theorem distances_nonneg (P : Finset (Pt d)) {r : ℝ} (hr : r ∈ distances P) : 0 ≤ r := by
  rcases mem_insert.mp hr with he | hr
  · rw [he]
  · obtain ⟨x, -, rfl⟩ := mem_image.mp hr; exact dist_nonneg

theorem line_card (P : Finset (Pt d)) (ℓ : AffineSubspace ℝ (Pt d)) (hℓ : IsRealLine ℓ) :
    (occ P ℓ : ℝ) ≤ 2 * cfgM P := by
  let A := P.filter (· ∈ ℓ)
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    have hn : A.card ≤ 2 * (distances P).card :=
      card_le_mul_card_image_of_maps_to
        (fun x hx => mem_distances P (mem_filter.mp hx).1 (mem_filter.mp ha).1) 2
        (fun r _ => line_distance_fiber A ℓ hℓ (fun x hx => (mem_filter.mp hx).2) a r)
    have hr : (A.card : ℝ) ≤ 2 * ((distances P).card : ℝ) := by exact_mod_cast hn
    change (A.card : ℝ) ≤ _
    simpa only [distances_card_real] using hr
  · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    change (A.card : ℝ) ≤ _
    rw [he, card_empty, Nat.cast_zero]
    have hM : 0 ≤ cfgM P := by unfold cfgM; positivity
    positivity

theorem plane_card (P : Finset (Pt d)) (H : AffineSubspace ℝ (Pt d)) (hH : IsRealPlane H) :
    (occ P H : ℝ) ≤ 2 * cfgM P ^ 2 := by
  let Q := P.filter (· ∈ H)
  by_cases hQ : Q.card ≤ 1
  · have hM : 1 ≤ cfgM P := by
      unfold cfgM
      have := Nat.cast_nonneg (α := ℝ) (distinctDistances P)
      linarith
    have hn : (Q.card : ℝ) ≤ 1 := by exact_mod_cast hQ
    change (Q.card : ℝ) ≤ _
    nlinarith
  · obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (lt_of_not_ge hQ)
    have hn : Q.card ≤ 2 * ((distances P) ×ˢ (distances P)).card := by
      apply card_le_mul_card_image_of_maps_to (f := fun x => (dist x a, dist x b))
        (fun x hx => mem_product.mpr ⟨mem_distances P (mem_filter.mp hx).1 (mem_filter.mp ha).1,
          mem_distances P (mem_filter.mp hx).1 (mem_filter.mp hb).1⟩) 2
      intro rt _
      rcases rt with ⟨r,t⟩
      simpa only [Prod.mk.injEq] using plane_distance_fiber Q H hH
        (fun x hx => (mem_filter.mp hx).2) a b (mem_filter.mp ha).2 (mem_filter.mp hb).2
        hab r t
    rw [card_product] at hn
    have hr : (Q.card : ℝ) ≤ 2 * ((distances P).card : ℝ) ^ 2 := by
      exact_mod_cast (by simpa only [pow_two] using hn)
    change (Q.card : ℝ) ≤ _
    simpa only [distances_card_real] using hr

def vec (u v : ℝ) : Pt 2 := WithLp.toLp 2 ![u,v]

def lift (a v x : Pt d) : Pt 2 := vec (inner ℝ v (x-a)) (dist x a ^ 2)

theorem dist_param (a v x : Pt d) (t : ℝ) :
    dist x (a+t • v) ^ 2 = dist x a ^ 2 - 2*t*inner ℝ v (x-a) + t^2*‖v‖^2 := by
  have he : x-(a+t • v) = (x-a)-t • v := by abel
  rw [dist_eq_norm, he, norm_sub_sq_real, dist_eq_norm, inner_smul_right,
    real_inner_comm (x-a) v, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

def liftedLine (t k : ℝ) : AffineSubspace ℝ (Pt 2) :=
  AffineSubspace.mk' (vec 0 k) (ℝ ∙ vec 1 (2*t))

theorem liftedLine_mem (t k : ℝ) (z : Pt 2) :
    z ∈ liftedLine t k ↔ z 1 - 2*t*z 0 = k := by
  simp only [liftedLine, AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨s, hs⟩
    have h0 := congrArg (fun z : Pt 2 => z 0) hs
    have h1 := congrArg (fun z : Pt 2 => z 1) hs
    simp [vec] at h0 h1
    rw [h0] at h1
    nlinarith
  · intro hz
    refine ⟨z 0, ?_⟩
    ext i
    fin_cases i <;> simp [vec] <;> linarith

theorem liftedLine_line (t k : ℝ) : IsRealLine (liftedLine t k) := by
  unfold IsRealLine liftedLine
  rw [AffineSubspace.direction_mk']
  apply finrank_span_singleton
  intro hz
  have h := congrArg (fun z : Pt 2 => z 0) hz
  simp [vec] at h

theorem liftedLine_injective {t k u l : ℝ} (h : liftedLine t k = liftedLine u l) : t = u ∧ k = l := by
  have h0 : vec 0 k ∈ liftedLine u l := by
    rw [← h]; exact AffineSubspace.self_mem_mk' _ _
  have h1 : vec 1 (k+2*t) ∈ liftedLine u l := by
    rw [← h, liftedLine_mem]; simp [vec]
  rw [liftedLine_mem] at h0 h1
  simp [vec] at h0 h1
  constructor <;> linarith

theorem lift_incidence (a v x : Pt d) (t : ℝ) :
    lift a v x ∈ liftedLine t (dist x (a+t • v)^2-t^2*‖v‖^2) := by
  rw [liftedLine_mem, dist_param]
  simp [lift, vec]

theorem lift_eq_dist (a v x y : Pt d) (h : lift a v x = lift a v y) (t : ℝ) :
    dist x (a+t • v) = dist y (a+t • v) := by
  have h0 := congrArg (fun z : Pt 2 => z 0) h
  have h1 := congrArg (fun z : Pt 2 => z 1) h
  change inner ℝ v (x-a) = inner ℝ v (y-a) at h0
  change dist x a ^ 2 = dist y a ^ 2 at h1
  have he : dist x (a+t • v)^2 = dist y (a+t • v)^2 := by rw [dist_param, dist_param, h0, h1]
  nlinarith [dist_nonneg (x := x) (y := a+t • v), dist_nonneg (x := y) (y := a+t • v)]

theorem lift_fiber (Q : Finset (Pt d)) (H : AffineSubspace ℝ (Pt d)) (hH : IsRealPlane H)
    (hQ : ∀ x ∈ Q, x ∈ H) (a v : Pt d) (ha : a ∈ H) (hb : a+v ∈ H) (hv : v ≠ 0)
    (z : Pt 2) : (Q.filter (fun x => lift a v x = z)).card ≤ 2 := by
  apply card_two
  intro x hx y hy w hw hxy
  obtain ⟨hxQ, hxZ⟩ := mem_filter.mp hx
  obtain ⟨hyQ, hyZ⟩ := mem_filter.mp hy
  obtain ⟨hwQ, hwZ⟩ := mem_filter.mp hw
  have hya := lift_eq_dist a v y x (hyZ.trans hxZ.symm) 0
  have hwa := lift_eq_dist a v w x (hwZ.trans hxZ.symm) 0
  have hyb := lift_eq_dist a v y x (hyZ.trans hxZ.symm) 1
  have hwb := lift_eq_dist a v w x (hwZ.trans hxZ.symm) 1
  simp only [zero_smul, add_zero, one_smul] at hya hwa hyb hwb
  exact EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two
    hH ha hb (hQ x hxQ) (hQ y hyQ) (hQ w hwQ)
    (by intro he; apply hv; have := add_left_cancel (he.symm.trans (add_zero a).symm); exact this)
    hxy rfl hya hwa rfl hyb hwb

end
end DistinctDistances.TrackD.GeoLinePlane
