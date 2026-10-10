import DistinctDistances.TrackE.FlatCaps
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

/-!
# The sparse-projection alternative in `red:directions.count`

`reduction.tex:180–192`: partition first by radius and then by orthogonal projection.
Each joint fiber is a sphere in an affine translate of the orthogonal complement.
In complement dimension at most one it has at most two points.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

open Classical in
/-- Real-valued version of the finite fiber-cardinality bound. -/
theorem card_le_image_card_mul_of_real_fiber_bound {α β : Type*}
    (S : Finset α) (f : α → β) (K : ℝ)
    (hfiber : ∀ b ∈ S.image f, ((S.filter fun a => f a = b).card : ℝ) ≤ K) :
    (S.card : ℝ) ≤ (S.image f).card * K := by
  classical
  calc
    (S.card : ℝ) = ∑ b ∈ S.image f, ((S.filter fun a => f a = b).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image f S
    _ ≤ ∑ _ ∈ S.image f, K := Finset.sum_le_sum hfiber
    _ = (S.image f).card * K := by simp

open Classical in
/-- Two successive partitions: at most `M` first labels, at most `2M` second labels
in each first fiber, and joint fibers of cardinality at most `K`. -/
theorem card_le_two_mul_sq_mul_of_sparse_projections {α β γ : Type*}
    (S : Finset α) (f : α → β) (g : α → γ) (M K : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hfirst : ((S.image f).card : ℝ) ≤ M)
    (hsecond : ∀ b ∈ S.image f, (((S.filter fun a => f a = b).image g).card : ℝ) ≤ 2 * M)
    (hjoint : ∀ b ∈ S.image f, ∀ c,
      ((S.filter fun a => f a = b ∧ g a = c).card : ℝ) ≤ K) :
    (S.card : ℝ) ≤ 2 * M ^ 2 * K := by
  classical
  have hfiber : ∀ b ∈ S.image f, ((S.filter fun a => f a = b).card : ℝ) ≤ 2 * M * K := by
    intro b hb
    have h := card_le_image_card_mul_of_real_fiber_bound (S.filter fun a => f a = b) g K (by
      intro c _
      have heq : ((S.filter fun a => f a = b).filter fun a => g a = c) =
          (S.filter fun a => f a = b ∧ g a = c) := by
        ext a
        simp only [Finset.mem_filter]
        tauto
      rw [heq]
      exact hjoint b hb c)
    exact h.trans (mul_le_mul_of_nonneg_right (hsecond b hb) hK)
  calc
    (S.card : ℝ) ≤ (S.image f).card * (2 * M * K) :=
      card_le_image_card_mul_of_real_fiber_bound S f (2 * M * K) hfiber
    _ ≤ M * (2 * M * K) := by gcongr
    _ = 2 * M ^ 2 * K := by ring

open Classical in
/-- A sample point as center gives at most `M = 1 + count` radius values, including zero. -/
theorem card_radius_values_le (P : Finset (RPoint d)) (p : RPoint d) (hp : p ∈ P) :
    ((P.image fun z => dist z p).card : ℝ) ≤ Mcount P := by
  classical
  have hsubset : (P.image fun z => dist z p) ⊆ insert 0 (distanceSet P) := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    by_cases hzp : z = p
    · simp [hzp]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨(z, p), Finset.mem_offDiag.mpr ⟨hz, hp, hzp⟩, rfl⟩
  have hcard : (P.image fun z => dist z p).card ≤ (distanceSet P).card + 1 :=
    (Finset.card_le_card hsubset).trans (Finset.card_insert_le _ _)
  simpa only [Mcount, distinctDistances, Nat.cast_add, Nat.cast_one] using
    (Nat.cast_le.mpr hcard : ((P.image fun z => dist z p).card : ℝ) ≤
      ((distanceSet P).card + 1 : ℕ))

open Classical in
/-- A joint fiber records its actual radius and actual projection. -/
def radiusProjectionFiber (P : Finset (RPoint d)) (p : RPoint d)
    (U : Submodule ℝ (RPoint d)) (r : ℝ) (v : U) : Finset (RPoint d) :=
  P.filter fun z => dist z p = r ∧ U.orthogonalProjectionOnto z = v

open Classical in
/-- Each nonempty joint fiber is contained in a sphere centered in the appropriate
affine translate of `Uᗮ`. Choosing a point from the fiber avoids any square-root convention. -/
theorem radiusProjectionFiber_sphere (P : Finset (RPoint d)) (p : RPoint d)
    (U : Submodule ℝ (RPoint d)) (r : ℝ) (v : U)
    (hne : (radiusProjectionFiber P p U r v).Nonempty) :
    ∃ (F : AffineSubspace ℝ (RPoint d)) (c : RPoint d) (s : ℝ),
      F.direction = Uᗮ ∧ c ∈ F ∧
      radiusProjectionFiber P p U r v ⊆ P.filter fun z => z ∈ F ∧ dist z c = s := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨_, hrad₀, hproj₀⟩ := Finset.mem_filter.mp hz₀
  let F := AffineSubspace.mk' z₀ Uᗮ
  let c : RPoint d := EuclideanGeometry.orthogonalProjection F p
  have hz₀F : z₀ ∈ F := AffineSubspace.self_mem_mk' _ _
  have hmem : ∀ z ∈ radiusProjectionFiber P p U r v, z ∈ F := by
    intro z hz
    obtain ⟨_, _, hproj⟩ := Finset.mem_filter.mp hz
    apply AffineSubspace.mem_mk'.mpr
    change z - z₀ ∈ Uᗮ
    apply U.orthogonalProjectionOnto_eq_zero_iff.mp
    rw [map_sub, hproj, hproj₀, sub_self]
  refine ⟨F, c, dist z₀ c, AffineSubspace.direction_mk' _ _,
    (EuclideanGeometry.orthogonalProjection F p).property, ?_⟩
  intro z hz
  obtain ⟨hzP, hrad, _⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨hzP, hmem z hz, ?_⟩
  have h₀ := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    p hz₀F
  have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    p (hmem z hz)
  change dist z₀ p * dist z₀ p = dist z₀ c * dist z₀ c + dist p c * dist p c at h₀
  change dist z p * dist z p = dist z c * dist z c + dist p c * dist p c at h
  have heq : dist z c ^ 2 = dist z₀ c ^ 2 := by rw [hrad₀] at h₀; rw [hrad] at h; nlinarith
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp heq

open Classical in
/-- A sphere meets a real affine flat of dimension at most one in at most two points,
including the degenerate dimension-zero and radius-zero cases. -/
theorem card_sphere_inter_flat_le_two (P : Finset (RPoint d))
    (F : AffineSubspace ℝ (RPoint d)) (p : RPoint d) (r : ℝ)
    (hF : Module.finrank ℝ F.direction ≤ 1) :
    (P.filter fun z => z ∈ F ∧ dist z p = r).card ≤ 2 := by
  classical
  let T := P.filter fun z => z ∈ F ∧ dist z p = r
  by_cases hT : T.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hT
    obtain ⟨_, hz₀F, hz₀r⟩ := Finset.mem_filter.mp hz₀
    obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := ℝ) (V := F.direction)).mp hF
    let sphere : EuclideanGeometry.Sphere (RPoint d) := ⟨p, r⟩
    have hz₀s : z₀ ∈ sphere := by
      simpa [EuclideanGeometry.mem_sphere, sphere, dist_comm] using hz₀r
    have hsubset : T ⊆ {z₀, sphere.secondInter z₀ (v : RPoint d)} := by
      intro z hz
      obtain ⟨_, hzF, hzr⟩ := Finset.mem_filter.mp hz
      have hdiff : z - z₀ ∈ F.direction := by
        simpa only [vsub_eq_sub] using F.vsub_mem_direction hzF hz₀F
      obtain ⟨t, ht⟩ := hv ⟨z - z₀, hdiff⟩
      have hzline : z ∈ AffineSubspace.mk' z₀ (ℝ ∙ (v : RPoint d)) := by
        apply AffineSubspace.mem_mk'.mpr
        change z - z₀ ∈ ℝ ∙ (v : RPoint d)
        exact Submodule.mem_span_singleton.mpr ⟨t, congrArg Subtype.val ht⟩
      have hzs : z ∈ sphere := by
        simpa [EuclideanGeometry.mem_sphere, sphere, dist_comm] using hzr
      have heq := (sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hz₀s hzline).mpr hzs
      simpa only [Finset.mem_insert, Finset.mem_singleton] using heq
    exact (Finset.card_le_card hsubset).trans (by simp only [Finset.card_le_two])
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ 2
    rw [hempty, Finset.card_empty]
    omega

open Classical in
/-- Joint radius/projection fibers in complement dimension at most one have at most
two points (`reduction.tex:189`). -/
theorem card_radiusProjectionFiber_le_two (P : Finset (RPoint d)) (p : RPoint d)
    (U : Submodule ℝ (RPoint d)) (r : ℝ) (v : U)
    (hU : Module.finrank ℝ Uᗮ ≤ 1) :
    (radiusProjectionFiber P p U r v).card ≤ 2 := by
  classical
  by_cases hne : (radiusProjectionFiber P p U r v).Nonempty
  · obtain ⟨F, c, s, hdir, _, hsubset⟩ := radiusProjectionFiber_sphere P p U r v hne
    exact (Finset.card_le_card hsubset).trans
      (card_sphere_inter_flat_le_two P F c s (by rw [hdir]; exact hU))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    omega

open Classical in
/-- The complement-dimension-two case is exactly the circle occupancy input. -/
theorem card_radiusProjectionFiber_le_circle (P : Finset (RPoint d)) (p : RPoint d)
    (U : Submodule ℝ (RPoint d)) (r : ℝ) (v : U)
    (hU : Module.finrank ℝ Uᗮ = 2) :
    ((radiusProjectionFiber P p U r v).card : ℝ) ≤ 2 * Mcount P - 1 := by
  classical
  by_cases hne : (radiusProjectionFiber P p U r v).Nonempty
  · obtain ⟨F, c, s, hdir, hc, hsubset⟩ := radiusProjectionFiber_sphere P p U r v hne
    exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans
      (card_inter_circle_le P F (by rw [hdir]; exact hU) c hc s)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    dsimp [Mcount]
    have h := Nat.cast_nonneg (α := ℝ) (distinctDistances P)
    linarith

open Classical in
/-- `red:directions.fibers` (`reduction.tex:183–192`): uniform over all span dimensions
at least four, each joint radius/projection fiber has size at most
`C M^(d/2-2)`. Lower-dimensional induction handles complement dimension at least three;
the circle input and the proved two-point lemma handle the remaining dimensions. -/
theorem exists_radiusProjectionFiber_bound (hIH : IH d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (RPoint d)) (p : RPoint d)
      (U : Submodule ℝ (RPoint d)), 4 ≤ Module.finrank ℝ U → ∀ (r : ℝ) (v : U),
        ((radiusProjectionFiber P p U r v).card : ℝ) ≤
          C * Mcount P ^ ((d : ℝ) / 2 - 2) := by
  classical
  let constant : Fin d → ℝ := fun i => if h : 3 ≤ i.val then
    (card_inter_flat_le_of_IH hIH i.val h i.isLt).choose else 2
  have hpositive : ∀ i : Fin d, 0 < constant i := by
    intro i
    dsimp [constant]
    split_ifs with hi
    · exact (card_inter_flat_le_of_IH hIH i.val hi i.isLt).choose_spec.1
    · norm_num
  have hlocal : ∀ i : Fin d, 3 ≤ i.val →
      ∀ (P : Finset (RPoint d)) (F : AffineSubspace ℝ (RPoint d)),
        Module.finrank ℝ F.direction = i.val →
        ((P.filter (· ∈ F)).card : ℝ) ≤ constant i * Mcount P ^ ((i.val : ℝ) / 2) := by
    intro i hi P F hF
    simpa only [constant, dif_pos hi] using
      (card_inter_flat_le_of_IH hIH i.val hi i.isLt).choose_spec.2 P F hF
  let C : ℝ := 2 + ∑ i : Fin d, constant i
  have hsum : 0 ≤ ∑ i : Fin d, constant i :=
    Finset.sum_nonneg fun i _ => (hpositive i).le
  have hC2 : 2 ≤ C := by dsimp [C]; linarith
  have hCi : ∀ i : Fin d, constant i ≤ C := by
    intro i
    have hi : constant i ≤ ∑ j : Fin d, constant j :=
      Finset.single_le_sum (fun j _ => (hpositive j).le) (Finset.mem_univ i)
    dsimp [C]
    linarith
  refine ⟨C, by linarith, ?_⟩
  intro P p U hU r v
  let u := Module.finrank ℝ Uᗮ
  have hdim : Module.finrank ℝ U + u = d := by
    simpa only [u, RPoint, finrank_euclideanSpace_fin] using U.finrank_add_finrank_orthogonal
  have hdimR : (Module.finrank ℝ U : ℝ) + (u : ℝ) = (d : ℝ) := by exact_mod_cast hdim
  have hUR : (4 : ℝ) ≤ Module.finrank ℝ U := by exact_mod_cast hU
  have hM : 1 ≤ Mcount P := by
    dsimp [Mcount]
    have h := Nat.cast_nonneg (α := ℝ) (distinctDistances P)
    linarith
  have hM0 : 0 < Mcount P := by linarith
  have hexp0 : 0 ≤ (d : ℝ) / 2 - 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) u]
  by_cases hu1 : u ≤ 1
  · have hfiber : ((radiusProjectionFiber P p U r v).card : ℝ) ≤ 2 := by
      exact_mod_cast card_radiusProjectionFiber_le_two P p U r v hu1
    have hpow := Real.one_le_rpow hM hexp0
    calc
      _ ≤ 2 := hfiber
      _ ≤ 2 * Mcount P ^ ((d : ℝ) / 2 - 2) := by linarith
      _ ≤ C * Mcount P ^ ((d : ℝ) / 2 - 2) :=
        mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hM0.le _)
  · by_cases hu2 : u = 2
    · have huR : (u : ℝ) = 2 := by exact_mod_cast hu2
      have hexp1 : 1 ≤ (d : ℝ) / 2 - 2 := by linarith
      calc
        _ ≤ 2 * Mcount P - 1 := card_radiusProjectionFiber_le_circle P p U r v hu2
        _ ≤ 2 * Mcount P := by linarith
        _ = 2 * Mcount P ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ 2 * Mcount P ^ ((d : ℝ) / 2 - 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM hexp1) (by norm_num)
        _ ≤ C * Mcount P ^ ((d : ℝ) / 2 - 2) :=
          mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hM0.le _)
    · have hu3 : 3 ≤ u := by omega
      have hud : u < d := by omega
      have hexp : (u : ℝ) / 2 ≤ (d : ℝ) / 2 - 2 := by linarith
      by_cases hne : (radiusProjectionFiber P p U r v).Nonempty
      · obtain ⟨F, c, s, hdir, _, hsubset⟩ := radiusProjectionFiber_sphere P p U r v hne
        have hflat : radiusProjectionFiber P p U r v ⊆ P.filter (· ∈ F) := by
          intro z hz
          obtain ⟨hzP, hzF, _⟩ := Finset.mem_filter.mp (hsubset hz)
          exact Finset.mem_filter.mpr ⟨hzP, hzF⟩
        calc
          _ ≤ ((P.filter (· ∈ F)).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hflat)
          _ ≤ constant ⟨u, hud⟩ * Mcount P ^ ((u : ℝ) / 2) :=
            hlocal ⟨u, hud⟩ hu3 P F (by rw [hdir])
          _ ≤ C * Mcount P ^ ((d : ℝ) / 2 - 2) :=
            mul_le_mul (hCi ⟨u, hud⟩)
              (Real.rpow_le_rpow_of_exponent_le hM hexp)
              (Real.rpow_nonneg hM0.le _) (by linarith)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
        positivity

open Classical in
/-- If the sample exceeds the sparse-fiber bound, one radius class has at least `2M`
distinct projections. This is the rich-radius alternative consumed by the dimension induction. -/
theorem exists_rich_radius_of_large_card (hIH : IH d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (RPoint d)) (p : RPoint d), p ∈ P →
      ∀ U : Submodule ℝ (RPoint d), 4 ≤ Module.finrank ℝ U →
      2 * C * Mcount P ^ ((d : ℝ) / 2) < P.card →
      ∃ r ∈ P.image (fun z => dist z p),
        2 * Mcount P ≤ (((P.filter fun z => dist z p = r).image
          U.orthogonalProjectionOnto).card : ℝ) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_radiusProjectionFiber_bound hIH
  refine ⟨C, hC, ?_⟩
  intro P p hp U hU hcard
  by_contra! hsparse
  have hM : 0 < Mcount P := by
    dsimp [Mcount]
    positivity
  have h := card_le_two_mul_sq_mul_of_sparse_projections P (fun z => dist z p)
    U.orthogonalProjectionOnto (Mcount P) (C * Mcount P ^ ((d : ℝ) / 2 - 2))
    hM.le (by positivity) (card_radius_values_le P p hp)
    (fun r hr => by
      convert (hsparse r hr).le using 1
      congr 2
      ext w
      simp only [Finset.mem_image, Finset.mem_filter])
    (fun r _ v => by
      convert hbound P p U hU r v using 1
      unfold radiusProjectionFiber
      congr 2
      ext z
      simp only [Finset.mem_filter])
  have hpow : Mcount P ^ (2 : ℕ) * Mcount P ^ ((d : ℝ) / 2 - 2) =
      Mcount P ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hM]
    congr 1
    push_cast
    ring
  have hupper : (P.card : ℝ) ≤ 2 * C * Mcount P ^ ((d : ℝ) / 2) := by
    calc
      _ ≤ 2 * Mcount P ^ 2 * (C * Mcount P ^ ((d : ℝ) / 2 - 2)) := h
      _ = 2 * C * (Mcount P ^ 2 * Mcount P ^ ((d : ℝ) / 2 - 2)) := by ring
      _ = _ := by rw [hpow]
  exact not_lt_of_ge hupper hcard

/-- An explicit small ratio excludes the sparse-fiber bound, uniformly over nonempty
samples. The powers are real powers after casting; no natural division is used. -/
theorem exists_small_ratio_for_radius_bound (hd : 3 ≤ d) (C : ℝ) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P : Finset (RPoint d), 0 < P.card →
      Mcount P ≤ ε * Ascale d P.card →
        2 * C * Mcount P ^ ((d : ℝ) / 2) < P.card := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have he : (2 : ℝ) / d * ((d : ℝ) / 2) = 1 := by
    field_simp [ne_of_gt hd0]
  let ε : ℝ := (1 / (4 * C)) ^ ((2 : ℝ) / d)
  have hε : 0 < ε := Real.rpow_pos_of_pos (by positivity) _
  have hεpow : ε ^ ((d : ℝ) / 2) = 1 / (4 * C) := by
    dsimp [ε]
    rw [← Real.rpow_mul (by positivity), he, Real.rpow_one]
  refine ⟨ε, hε, ?_⟩
  intro P hP hMP
  have hN : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hA : 0 < Ascale d P.card := Real.rpow_pos_of_pos hN _
  have hApow : Ascale d P.card ^ ((d : ℝ) / 2) = (P.card : ℝ) := by
    dsimp [Ascale]
    rw [← Real.rpow_mul hN.le, he, Real.rpow_one]
  have hM : 0 < Mcount P := by dsimp [Mcount]; positivity
  calc
    _ ≤ 2 * C * (ε * Ascale d P.card) ^ ((d : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow hM.le hMP (by positivity)
    _ = (P.card : ℝ) / 2 := by
      rw [Real.mul_rpow hε.le hA.le, hεpow, hApow]
      field_simp [ne_of_gt hC] <;> ring
    _ < (P.card : ℝ) := by linarith

open Classical in
/-- `red:directions.rich-radius-exists`: in the small-`M/A` regime, every counted span
of dimension at least four has a radius class with at least `2M` distinct projections. -/
theorem exists_rich_radius_of_small_ratio (hd : 3 ≤ d) (hIH : IH d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (P : Finset (RPoint d)) (p : RPoint d), p ∈ P →
      Mcount P ≤ ε * Ascale d P.card →
      ∀ U : Submodule ℝ (RPoint d), 4 ≤ Module.finrank ℝ U →
      ∃ r ∈ P.image (fun z => dist z p),
        2 * Mcount P ≤ (((P.filter fun z => dist z p = r).image
          U.orthogonalProjectionOnto).card : ℝ) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_rich_radius_of_large_card hIH
  obtain ⟨ε, hε, hsmall⟩ := exists_small_ratio_for_radius_bound hd C hC
  refine ⟨ε, hε, ?_⟩
  intro P p hp hMP U hU
  exact hbound P p hp U hU (hsmall P (Finset.card_pos.mpr ⟨p, hp⟩) hMP)

end Reduction

end

end DistinctDistances
