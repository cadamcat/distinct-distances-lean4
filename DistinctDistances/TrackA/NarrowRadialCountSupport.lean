import DistinctDistances.TrackA.CommonRadialSourceOpenSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- Literal union of fibers in the original equal-image group. -/
def groupRadialFiber {n : ℕ} (J : AffineFamily.Family n) (p : Point n)
    (Y : AffineVariety n) (z : ProjectivePoint n) : Set (Point n) :=
  ⋃ V : J.filter (fun V => radialImage p V = radialImage p Y), radialFiber p V.val z

/-- The original fixed root is omitted exactly once. -/
def groupMovingFiber {n : ℕ} (J : AffineFamily.Family n) (p : Point n)
    (Y : AffineVariety n) (z : ProjectivePoint n) (y : Point n) : Set (Point n) :=
  groupRadialFiber J p Y z \ {y}

theorem groupRadialFiber_count {n : ℕ} (J : AffineFamily.Family n) (p : Point n)
    (Y : AffineVariety n) (z : ProjectivePoint n) (r : AffineVariety n → ℕ)
    (hcount : ∀ V ∈ J, radialImage p V = radialImage p Y →
      (radialFiber p V z).Finite ∧ (radialFiber p V z).ncard = r V)
    (hdisj : ∀ V ∈ J, radialImage p V = radialImage p Y →
      ∀ W ∈ J, V ≠ W → Disjoint (radialFiber p V z) (radialFiber p W z)) :
    (groupRadialFiber J p Y z).Finite ∧ (groupRadialFiber J p Y z).ncard =
      ∑ V ∈ J.filter (fun V => radialImage p V = radialImage p Y), r V := by
  let G := J.filter (fun V => radialImage p V = radialImage p Y)
  have hg (V : G) : V.val ∈ J ∧ radialImage p V.val = radialImage p Y := Finset.mem_filter.mp V.property
  have hf (V : G) : (radialFiber p V.val z).Finite := (hcount V.val (hg V).1 (hg V).2).1
  have hd : Pairwise (fun V W : G => Disjoint (radialFiber p V.val z) (radialFiber p W.val z)) := by
    intro V W hne
    exact hdisj V.val (hg V).1 (hg V).2 W.val (hg W).1
      (fun he => hne (Subtype.ext he))
  refine ⟨Set.finite_iUnion hf, ?_⟩
  change (⋃ V : G, radialFiber p V.val z).ncard = _
  rw [Set.ncard_iUnion_of_finite hf hd, finsum_eq_sum_of_fintype]
  calc
    (∑ V : G, (radialFiber p V.val z).ncard) = ∑ V : G, r V.val :=
      Finset.sum_congr rfl (fun V _ => (hcount V.val (hg V).1 (hg V).2).2)
    _ = ∑ V ∈ G, r V := Finset.sum_coe_sort G r

/-- Counts on the full original group lose precisely one fixed root. -/
theorem groupMovingFiber_count {n : ℕ} (J : AffineFamily.Family n) (p y : Point n)
    (Y : AffineVariety n) (hY : Y ∈ J) (hy : y ∈ Y.points) (hpy : y ≠ p)
    (r : AffineVariety n → ℕ)
    (hcount : ∀ V ∈ J, radialImage p V = radialImage p Y →
      (radialFiber p V (radialProjection p y hpy)).Finite ∧
      (radialFiber p V (radialProjection p y hpy)).ncard = r V)
    (hdisj : ∀ V ∈ J, radialImage p V = radialImage p Y →
      ∀ W ∈ J, V ≠ W → Disjoint (radialFiber p V (radialProjection p y hpy))
        (radialFiber p W (radialProjection p y hpy))) :
    (groupMovingFiber J p Y (radialProjection p y hpy) y).Finite ∧
      (groupMovingFiber J p Y (radialProjection p y hpy) y).ncard =
        (∑ V ∈ J.filter (fun V => radialImage p V = radialImage p Y), r V) - 1 := by
  obtain ⟨hf, hc⟩ := groupRadialFiber_count J p Y (radialProjection p y hpy) r hcount hdisj
  have hymem : y ∈ groupRadialFiber J p Y (radialProjection p y hpy) := by
    apply Set.mem_iUnion.mpr
    exact ⟨⟨Y, Finset.mem_filter.mpr ⟨hY, rfl⟩⟩, hy, hpy, rfl⟩
  exact ⟨hf.sdiff, (Set.ncard_sdiff_singleton_of_mem hymem).trans (congrArg (fun c => c-1) hc)⟩

/-- A counted source point lies on just one member of the entire original
carrier family, including members outside its equal-image group. -/
theorem radial_fiber_unique_original_carrier {n : ℕ} (J : AffineFamily.Family n)
    (p : Point n) (V : AffineVariety n) (hV : V ∈ J) (z : ProjectivePoint n)
    (hdisj : ∀ W ∈ J, V ≠ W → Disjoint (radialFiber p V z) (radialFiber p W z))
    (x : Point n) (hx : x ∈ radialFiber p V z) :
    ∀ W ∈ J, x ∈ W.points → W = V := by
  intro W hW hxW
  by_contra hne
  have hw : x ∈ radialFiber p W z := ⟨hxW, hx.2⟩
  exact Set.disjoint_left.mp (hdisj W hW (fun he => hne he.symm)) hx hw

/-- A moving radial root determines one literal source-times-line
parameter sending it back to the original center. -/
theorem radial_moving_root_parameter {n : ℕ} (p y x : Point n)
    (hpy : y ≠ p) (hxp : x ≠ p) (hxy : x ≠ y)
    (he : radialProjection p x hxp = radialProjection p y hpy) :
    ∃! t : ℂ, p = y + t • (x-y) := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ (x-p) (y-p)
    (sub_ne_zero.mpr hxp) (sub_ne_zero.mpr hpy)).mp he
  have ha1 : a-1 ≠ 0 := by
    intro h
    have heq : a = 1 := sub_eq_zero.mp h
    rw [heq, one_smul] at ha
    exact hxy (by simpa only [sub_left_inj] using ha.symm)
  have hline : x-y = (a-1) • (y-p) := by
    rw [sub_smul, one_smul, ha]
    abel
  refine ⟨-(a-1)⁻¹, ?_, ?_⟩
  · change p = y + (-(a-1)⁻¹) • (x-y)
    rw [hline, smul_smul, neg_mul, inv_mul_cancel₀ ha1, neg_one_smul]
    abel
  · intro t ht
    apply smul_left_injective ℂ (sub_ne_zero.mpr hxy)
    change t • (x-y) = -(a-1)⁻¹ • (x-y)
    apply add_left_cancel (a := y)
    rw [← ht, hline, smul_smul, neg_mul, inv_mul_cancel₀ ha1, neg_one_smul]
    abel

/-- All counted solutions avoid both fixed endpoints. -/
theorem radial_moving_parameter_endpoints {n : ℕ} (p y x : Point n)
    (hpy : y ≠ p) (hxp : x ≠ p) (t : ℂ) (ht : p = y + t • (x-y)) :
    t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · intro he
    rw [he, zero_smul, add_zero] at ht
    exact hpy ht.symm
  · intro he
    rw [he, one_smul, add_sub_cancel] at ht
    exact hxp ht.symm

end
end DistinctDistances.TrackA
