import DistinctDistances.TrackD.PerspectiveGroup
import DistinctDistances.TrackD.PerspectiveCentersGeometry
import DistinctDistances.TrackD.GeoSpan
import DistinctDistances.TrackA.ProjectiveChartRankSupport
import DistinctDistances.TrackA.RadialProjectionSupport

namespace DistinctDistances.TrackD.PerspectiveTransport

set_option maxHeartbeats 800000

open scoped Classical BigOperators
noncomputable section

variable {n m : ℕ}

/-- Points of a variety map to points of its reduced affine image. -/
theorem image_mem (φ : AffineProjection n m) (V : AffineVariety n)
    (x : Point n) (hx : x ∈ V.points) : φ.apply x ∈ (φ.image V).points := by
  intro f hf
  rw [← AffineProjection.eval_pullback]
  exact hx _ hf

/-- An affine inverse on the source remains an inverse on the reduced image. -/
theorem inverse_on_image (φ : AffineProjection n m) (ψ : AffineProjection m n)
    (V : AffineVariety n) (hinv : ∀ x ∈ V.points, ψ.apply (φ.apply x) = x)
    (y : Point m) (hy : y ∈ (φ.image V).points) :
    ψ.apply y ∈ V.points ∧ φ.apply (ψ.apply y) = y := by
  have hpull (f : Poly n) (hf : f ∈ V.ideal) : ψ.pullback f ∈ (φ.image V).ideal := by
    change φ.pullback (ψ.pullback f) ∈ V.ideal
    rw [← V.vanishingIdeal_points]
    intro x hx
    rw [φ.eval_pullback, ψ.eval_pullback, hinv x hx]
    exact hx f hf
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [← ψ.eval_pullback]
    exact hy _ (hpull f hf)
  · ext j
    let F : Poly m := ψ.pullback (φ.pullback (MvPolynomial.X j)) - MvPolynomial.X j
    have hF : F ∈ (φ.image V).ideal := by
      change φ.pullback F ∈ V.ideal
      rw [← V.vanishingIdeal_points]
      intro x hx
      simp only [φ.eval_pullback, F, map_sub, ψ.eval_pullback, hinv x hx,
        MvPolynomial.aeval_X, sub_self]
    have hz := hy F hF
    simpa only [F, map_sub, ψ.eval_pullback, φ.eval_pullback,
      MvPolynomial.aeval_X, sub_eq_zero] using hz

theorem image_points (φ : AffineProjection n m) (ψ : AffineProjection m n)
    (V : AffineVariety n) (hinv : ∀ x ∈ V.points, ψ.apply (φ.apply x) = x) :
    (φ.image V).points = φ.apply '' V.points := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨hψ, heq⟩ := inverse_on_image φ ψ V hinv y hy
    exact ⟨ψ.apply y, hψ, heq⟩
  · rintro y ⟨x, hx, rfl⟩
    exact image_mem φ V x hx

theorem inverse_image (φ : AffineProjection n m) (ψ : AffineProjection m n)
    (V : AffineVariety n) (hinv : ∀ x ∈ V.points, ψ.apply (φ.apply x) = x) :
    ψ.image (φ.image V) = V := by
  rw [ψ.image_eq_closure, image_points φ ψ V hinv]
  have hset : ψ.apply '' (φ.apply '' V.points) = V.points := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hinv z hz]
    · intro hx
      exact ⟨φ.apply x, ⟨x, hx, rfl⟩, hinv x hx⟩
  rw [hset]
  apply AffineVariety.ext
  exact V.vanishingIdeal_points

/-- Degree-one pullback embeds every filtered restriction space. -/
theorem image_hilbert_le (φ : AffineProjection n m) (V : AffineVariety n) (D : ℕ) :
    (φ.image V).hilbert D ≤ V.hilbert D := by
  let a : Fin m → Poly n := fun j => linearCoordinate φ.linear j + MvPolynomial.C (φ.offset j)
  have ha (j) : (a j).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    exact max_le (TrackA.linearCoordinate_homogeneous φ.linear j).totalDegree_le (by simp)
  have h := OAI.QuarticPowerFree.polynomial_projection_hilbert_le V.ideal
    (φ.image V).ideal a 1 ha (fun f => by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rfl) D
  change (φ.image V).hilbert D ≤ V.hilbert (1 * D) at h
  simpa only [Nat.one_mul] using h

theorem image_hilbert (φ : AffineProjection n m) (ψ : AffineProjection m n)
    (V : AffineVariety n) (hinv : ∀ x ∈ V.points, ψ.apply (φ.apply x) = x) (D : ℕ) :
    (φ.image V).hilbert D = V.hilbert D := by
  apply Nat.le_antisymm (image_hilbert_le φ V D)
  have h := image_hilbert_le ψ (φ.image V) D
  rwa [inverse_image φ ψ V hinv] at h

theorem image_hilbertPolynomial (φ : AffineProjection n m) (ψ : AffineProjection m n)
    (V : AffineVariety n) (hinv : ∀ x ∈ V.points, ψ.apply (φ.apply x) = x) :
    (φ.image V).hilbertPolynomial = V.hilbertPolynomial := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  filter_upwards [(φ.image V).hilbert_eventually, V.hilbert_eventually] with D hφ hV
  rw [← hφ, ← hV, image_hilbert φ ψ V hinv]

theorem image_dimension (φ : AffineProjection n m) (ψ : AffineProjection m n)
    (V : AffineVariety n) (hinv : ∀ x ∈ V.points, ψ.apply (φ.apply x) = x) :
    (φ.image V).dimension = V.dimension := by
  change (φ.image V).hilbertPolynomial.natDegree = V.hilbertPolynomial.natDegree
  rw [image_hilbertPolynomial φ ψ V hinv]

theorem image_degree (φ : AffineProjection n m) (ψ : AffineProjection m n)
    (V : AffineVariety n) (hinv : ∀ x ∈ V.points, ψ.apply (φ.apply x) = x) :
    (φ.image V).degree = V.degree := by
  change ((φ.image V).dimension.factorial : ℚ) *
      (φ.image V).hilbertPolynomial.coeff (φ.image V).dimension =
    (V.dimension.factorial : ℚ) * V.hilbertPolynomial.coeff V.dimension
  rw [image_dimension φ ψ V hinv, image_hilbertPolynomial φ ψ V hinv]

/-- Every finite-dimensional affine flat has affine coordinates extending to
its ambient space, with an affine inverse defined on the entire coordinate space. -/
theorem affine_coordinates (Pl : AffineSubspace ℂ (Point n)) (r : ℕ)
    (hr : Module.finrank ℂ Pl.direction = r) (a : Point n) (ha : a ∈ Pl) :
    ∃ (φ : AffineProjection n r) (ψ : AffineProjection r n),
      (∀ x ∈ Pl, ψ.apply (φ.apply x) = x) ∧
      (∀ y, φ.apply (ψ.apply y) = y) ∧ (∀ y, ψ.apply y ∈ Pl) := by
  let e : Point r ≃ₗ[ℂ] Pl.direction := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi]
    simpa using hr.symm)
  let i : Point r →ₗ[ℂ] Point n := Pl.direction.subtype.comp e.toLinearMap
  have hi : Function.Injective i := Pl.direction.subtype_injective.comp e.injective
  obtain ⟨L, hL⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  have hLi (y : Point r) : L (i y) = y := LinearMap.congr_fun hL y
  let φ : AffineProjection n r := ⟨L, -L a⟩
  let ψ : AffineProjection r n := ⟨i, a⟩
  have hφ (x : Point n) : φ.apply x = L (x-a) := by
    simp [φ, AffineProjection.apply, map_sub, sub_eq_add_neg]
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · intro x hx
    have hxa : x-a ∈ Pl.direction := by
      simpa only [vsub_eq_sub] using Pl.vsub_mem_direction hx ha
    obtain ⟨y, hy⟩ : ∃ y : Point r, i y = x-a := by
      refine ⟨e.symm ⟨x-a, hxa⟩, ?_⟩
      simp [i]
    rw [hφ, ← hy, hLi]
    change i y + a = x
    rw [hy]
    abel
  · intro y
    rw [hφ]
    simp only [ψ, AffineProjection.apply, add_sub_cancel_right, hLi]
  · intro y
    change i y + a ∈ Pl
    exact Pl.vadd_mem_of_mem_direction (e y).property ha

/-- The polynomial representing a complex linear functional. -/
def linear_form (ℓ : Point n →ₗ[ℂ] ℂ) : Poly n :=
  linearCoordinate (LinearMap.pi fun _ : Fin 1 => ℓ) 0

@[simp] theorem linear_form_eval (ℓ : Point n →ₗ[ℂ] ℂ) (x : Point n) :
    MvPolynomial.aeval x (linear_form ℓ) = ℓ x :=
  TrackA.linearCoordinate_eval _ _ _

theorem linear_form_homogeneous (ℓ : Point n →ₗ[ℂ] ℂ) :
    (linear_form ℓ).IsHomogeneous 1 := TrackA.linearCoordinate_homogeneous _ _

/-- Linear subspaces are closed, expressed directly through their separating forms. -/
theorem closure_subset_submodule (T : Set (Point n)) (S : Submodule ℂ (Point n))
    (hTS : T ⊆ S) : (AffineVariety.closure T).points ⊆ S := by
  intro x hx
  by_contra hxS
  obtain ⟨ℓ, hℓx, hℓS⟩ := S.exists_le_ker_of_notMem hxS
  have hf : linear_form ℓ ∈ (AffineVariety.closure T).ideal := by
    intro y hy
    rw [linear_form_eval]
    exact hℓS (hTS hy)
  exact hℓx (by simpa using hx _ hf)

/-- Taking cones commutes with reduced linear image when the projective
image is nonempty. -/
theorem projective_image_cone (V : ProjectiveVariety n) (φ : LinearProjection n m)
    (hne : ∃ v ∈ V.affineCone.points, φ v ≠ 0) :
    (projectiveImage φ V).affineCone =
      (⟨φ, 0⟩ : AffineProjection n m).image V.affineCone := by
  let W := projectiveImage φ V
  let π : AffineProjection n m := ⟨φ, 0⟩
  have hφ (v : Point n) : π.apply v = φ v := by simp [π, AffineProjection.apply]
  have hmem (v : Point n) (hv : v ∈ V.affineCone.points) (hφv : φ v ≠ 0) :
      φ v ∈ W.affineCone.points := by
    have hv0 : v ≠ 0 := by intro h; simpa [h] using hφv
    apply (W.mem_points_mk_iff _ hφv).mp
    exact ProjectiveVariety.subset_closure _
      ⟨v, hv0, (V.mem_points_mk_iff v hv0).mpr hv, hφv, rfl⟩
  obtain ⟨v₀, hv₀, hφ₀⟩ := hne
  have hzero : (0 : Point m) ∈ W.affineCone.points := by
    simpa using TrackA.cone_smul_mem W (φ v₀) (hmem v₀ hv₀ hφ₀) 0
  apply AffineVariety.ext
  apply le_antisymm
  · intro F hF
    change π.pullback F ∈ V.ideal
    change π.pullback F ∈ V.affineCone.ideal
    rw [← V.affineCone.vanishingIdeal_points]
    intro v hv
    rw [π.eval_pullback, hφ]
    by_cases hφv : φ v = 0
    · rw [hφv]
      exact hzero F hF
    · exact hmem v hv hφv F hF
  · intro F hF
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro w ⟨hw, v, hv, hvV, hφv, heq⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ w (φ v) hw hφv).mp heq.symm
    have hcv : c • v ∈ V.affineCone.points :=
      TrackA.cone_smul_mem V v ((V.mem_points_mk_iff v hv).mp hvV) c
    have hz := hcv _ hF
    change MvPolynomial.aeval (c • v) (π.pullback F) = 0 at hz
    rw [π.eval_pullback, hφ, map_smul, hc] at hz
    exact hz

/-- The radial image cone is the affine linear image of the source cone. -/
theorem radial_image_cone (V : AffineVariety n) (p : Point n)
    (hne : ∃ x ∈ V.points, x ≠ p) :
    (radialImage p V).affineCone =
      (⟨TrackA.radialLinearProjection p, 0⟩ : AffineProjection (n+1) n).image
        (projectiveClosure V).affineCone := by
  rw [← TrackA.radial_projective_image V p hne]
  apply projective_image_cone
  obtain ⟨x, hx, hxp⟩ := hne
  have hv : Fin.cons (α := fun _ => ℂ) 1 x ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa using h0
  refine ⟨Fin.cons 1 x, ?_, ?_⟩
  · apply ((projectiveClosure V).mem_points_mk_iff _ hv).mp
    exact (TrackA.affineEmbedding_mem_closure V x).mpr hx
  · simpa only [TrackA.radialLinearProjection_cons] using sub_ne_zero.mpr hxp

/-- The source cone remains in any linear space containing its affine generators. -/
theorem projective_closure_cone_subset (V : AffineVariety n)
    (S : Submodule ℂ (Point (n+1)))
    (hS : ∀ x ∈ V.points, Fin.cons (α := fun _ => ℂ) 1 x ∈ S) :
    (projectiveClosure V).affineCone.points ⊆ S := by
  intro v hv
  by_contra hvS
  obtain ⟨ℓ, hℓv, hℓS⟩ := S.exists_le_ker_of_notMem hvS
  have hF : linear_form ℓ ∈ (projectiveClosure V).ideal := by
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro w ⟨hw, x, hx, hpx⟩
    have hx0 : Fin.cons (α := fun _ => ℂ) 1 x ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simpa using h0
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ w
      (Fin.cons 1 x) hw hx0).mp hpx.symm
    rw [linear_form_eval, ← hc, map_smul]
    change c * ℓ (Fin.cons 1 x) = 0
    rw [show ℓ (Fin.cons 1 x) = 0 from hℓS (hS x hx), mul_zero]
  exact hℓv (by simpa using hv _ hF)

/-- The homogeneous span of an affine plane, independent of any chosen origin. -/
def homogeneous_plane (Pl : AffineSubspace ℂ (Point n)) : Submodule ℂ (Point (n+1)) :=
  Submodule.span ℂ ((fun x : Point n => Fin.cons (α := fun _ => ℂ) 1 x) '' (Pl : Set (Point n)))

def plane_lift (a : Point n) (S : Submodule ℂ (Point n)) :
    (ℂ × S) →ₗ[ℂ] Point (n+1) where
  toFun v := Fin.cons v.1 (v.1 • a + v.2.val)
  map_add' v w := by
    ext j
    cases j using Fin.cases <;> simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' c v := by
    ext j
    cases j using Fin.cases <;> simp [smul_add, smul_smul] <;> ring

theorem plane_lift_injective (a : Point n) (S : Submodule ℂ (Point n)) :
    Function.Injective (plane_lift a S) := by
  intro v w h
  have h0 : v.1 = w.1 := by simpa [plane_lift] using congrFun h 0
  apply Prod.ext h0
  apply Subtype.ext
  ext j
  have hj := congrFun h j.succ
  simpa [plane_lift, h0] using hj

theorem homogeneous_plane_range (Pl : AffineSubspace ℂ (Point n))
    (a : Point n) (ha : a ∈ Pl) :
    homogeneous_plane Pl = LinearMap.range (plane_lift a Pl.direction) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨x, hx, rfl⟩
    refine ⟨(1, ⟨x-a, ?_⟩), ?_⟩
    · simpa only [vsub_eq_sub] using Pl.vsub_mem_direction hx ha
    · ext j
      cases j using Fin.cases <;> simp [plane_lift, sub_eq_add_neg]
  · rintro v ⟨⟨t, u⟩, rfl⟩
    have haH : Fin.cons (α := fun _ => ℂ) 1 a ∈ homogeneous_plane Pl :=
      Submodule.subset_span ⟨a, ha, rfl⟩
    have huH : Fin.cons (α := fun _ => ℂ) 1 (u.val+a) ∈ homogeneous_plane Pl :=
      Submodule.subset_span ⟨u.val+a, Pl.vadd_mem_of_mem_direction u.property ha, rfl⟩
    have hform : plane_lift a Pl.direction (t, u) =
        t • Fin.cons (α := fun _ => ℂ) 1 a +
          (Fin.cons (α := fun _ => ℂ) 1 (u.val+a) - Fin.cons 1 a) := by
      ext j
      cases j using Fin.cases <;> simp [plane_lift] <;> ring
    rw [hform]
    exact (homogeneous_plane Pl).add_mem ((homogeneous_plane Pl).smul_mem t haH)
      ((homogeneous_plane Pl).sub_mem huH haH)

theorem homogeneous_plane_finrank (Pl : AffineSubspace ℂ (Point n))
    (a : Point n) (ha : a ∈ Pl) :
    Module.finrank ℂ (homogeneous_plane Pl) = 1 + Module.finrank ℂ Pl.direction := by
  rw [homogeneous_plane_range Pl a ha,
    LinearMap.finrank_range_of_inj (plane_lift_injective a Pl.direction), Module.finrank_prod]
  simp

@[simp] theorem homogeneous_plane_cons_mem (Pl : AffineSubspace ℂ (Point n))
    (a : Point n) (ha : a ∈ Pl) (x : Point n) :
    Fin.cons (α := fun _ => ℂ) 1 x ∈ homogeneous_plane Pl ↔ x ∈ Pl := by
  rw [homogeneous_plane_range Pl a ha]
  constructor
  · rintro ⟨⟨t, u⟩, hu⟩
    have ht : t = 1 := by simpa [plane_lift] using congrFun hu 0
    have hx : u.val+a = x := by
      ext j
      have hj := congrFun hu j.succ
      simpa [plane_lift, ht, add_comm] using hj
    rw [← hx]
    exact Pl.vadd_mem_of_mem_direction u.property ha
  · intro hx
    refine ⟨(1, ⟨x-a, ?_⟩), ?_⟩
    · simpa only [vsub_eq_sub] using Pl.vsub_mem_direction hx ha
    · ext j
      cases j using Fin.cases <;> simp [plane_lift, sub_eq_add_neg]

theorem curve_affine_span_eq (Y : AffineVariety n) (hY : IsCurve Y)
    (hnl : ¬ IsLine Y) (Pl : AffineSubspace ℂ (Point n))
    (hPl : Module.finrank ℂ Pl.direction = 2) (hYP : Y.points ⊆ Pl) :
    affineSpan ℂ Y.points = Pl := by
  have hle : affineSpan ℂ Y.points ≤ Pl := affineSpan_le.mpr hYP
  have hdir := AffineSubspace.direction_le hle
  have hdim : Module.finrank ℂ (affineSpan ℂ Y.points).direction =
      Module.finrank ℂ Pl.direction := by
    have hlo := GeoRadial.nonlinear_span_ge_two Y hY hnl
    have hhi := Submodule.finrank_mono hdir
    change 2 ≤ Module.finrank ℂ (affineSpan ℂ Y.points).direction at hlo
    omega
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq hdir hdim)
    ((Y.points_nonempty_of_isIrreducible hY.1).mono (subset_affineSpan ℂ _)) hle

/-- Nonlinear planar curves span the full homogeneous plane. -/
theorem curve_cone_span (Y : AffineVariety n) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (Pl : AffineSubspace ℂ (Point n)) (hPl : Module.finrank ℂ Pl.direction = 2)
    (hYP : Y.points ⊆ Pl) :
    Submodule.span ℂ (projectiveClosure Y).affineCone.points = homogeneous_plane Pl := by
  have hcone : (projectiveClosure Y).affineCone.points ⊆ homogeneous_plane Pl :=
    projective_closure_cone_subset Y _ (fun x hx => Submodule.subset_span ⟨x, hYP hx, rfl⟩)
  apply le_antisymm (Submodule.span_le.mpr hcone)
  apply Submodule.span_le.mpr
  rintro v ⟨x, hx, rfl⟩
  have hxspan : x ∈ affineSpan ℂ Y.points := by
    rwa [curve_affine_span_eq Y hY hnl Pl hPl hYP]
  refine affineSpan_induction hxspan ?_ ?_
  · intro x hx
    apply Submodule.subset_span
    have hv : Fin.cons (α := fun _ => ℂ) 1 x ≠ 0 := by
      intro hz
      have h0 := congrFun hz 0
      simpa using h0
    exact ((projectiveClosure Y).mem_points_mk_iff _ hv).mp
      ((TrackA.affineEmbedding_mem_closure Y x).mpr hx)
  · intro c u v w hu hv hw
    have heq : Fin.cons (α := fun _ => ℂ) 1 (c • (u -ᵥ v) +ᵥ w) =
        c • (Fin.cons (α := fun _ => ℂ) 1 u - Fin.cons 1 v) + Fin.cons 1 w := by
      ext j
      cases j using Fin.cases <;> simp [vsub_eq_sub, vadd_eq_add, smul_eq_mul] <;> ring
    change Fin.cons (α := fun _ => ℂ) 1 (c • (u -ᵥ v) +ᵥ w) ∈
      Submodule.span ℂ (projectiveClosure Y).affineCone.points
    rw [heq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ c (Submodule.sub_mem _ hu hv)) hw

/-- An injective restriction of a linear projection has a linear inverse extending
from its image to the whole ambient target. -/
theorem linear_inverse_on_submodule (S : Submodule ℂ (Point n))
    (φ : LinearProjection n m) (hdisj : Disjoint S (LinearMap.ker φ)) :
    ∃ ρ : LinearProjection m n, ∀ x ∈ S, ρ (φ x) = x := by
  let f := φ.comp S.subtype
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro x hx
      have hzero : x.val = 0 := by
        apply (Submodule.disjoint_def.mp hdisj) x.val x.property
        exact hx
      exact Subtype.ext hzero
    · exact bot_le
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  refine ⟨S.subtype.comp g, ?_⟩
  intro x hx
  exact congrArg Subtype.val (LinearMap.congr_fun hg ⟨x, hx⟩)

theorem plane_radial_inverse (Pl : AffineSubspace ℂ (Point n))
    (a : Point n) (ha : a ∈ Pl) (p : Point n) (hp : p ∉ Pl) :
    ∃ ρ : LinearProjection n (n+1),
      ∀ v ∈ homogeneous_plane Pl, ρ (TrackA.radialLinearProjection p v) = v := by
  apply linear_inverse_on_submodule
  rw [TrackA.radialLinearProjection_kernel, affineEmbedding,
    Projectivization.submodule_mk]
  apply Submodule.disjoint_span_singleton_of_notMem
  simpa only [homogeneous_plane_cons_mem Pl a ha p] using hp

theorem radial_cone_points (Y : AffineVariety n) (Pl : AffineSubspace ℂ (Point n))
    (hYP : Y.points ⊆ Pl) (a : Point n) (ha : a ∈ Pl) (p : Point n)
    (hp : p ∉ Pl) (hYne : Y.points.Nonempty) :
    (radialImage p Y).affineCone.points =
      TrackA.radialLinearProjection p '' (projectiveClosure Y).affineCone.points := by
  obtain ⟨ρ, hρ⟩ := plane_radial_inverse Pl a ha p hp
  have hcone : (projectiveClosure Y).affineCone.points ⊆ homogeneous_plane Pl :=
    projective_closure_cone_subset Y _ (fun x hx => Submodule.subset_span ⟨x, hYP hx, rfl⟩)
  have hactual : ∃ x ∈ Y.points, x ≠ p := by
    obtain ⟨x, hx⟩ := hYne
    exact ⟨x, hx, fun h => hp (h ▸ hYP hx)⟩
  rw [radial_image_cone Y p hactual]
  have h := image_points (⟨TrackA.radialLinearProjection p, 0⟩ : AffineProjection (n+1) n)
    (⟨ρ, 0⟩ : AffineProjection n (n+1)) (projectiveClosure Y).affineCone
    (by intro v hv; simpa [AffineProjection.apply] using hρ v (hcone hv))
  have happ : (⟨TrackA.radialLinearProjection p, 0⟩ : AffineProjection (n+1) n).apply =
      TrackA.radialLinearProjection p := by
    funext v
    simp [AffineProjection.apply]
  rwa [happ] at h

theorem radial_cone_span (Y : AffineVariety n) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (Pl : AffineSubspace ℂ (Point n)) (hPl : Module.finrank ℂ Pl.direction = 2)
    (hYP : Y.points ⊆ Pl) (a : Point n) (ha : a ∈ Pl) (p : Point n) (hp : p ∉ Pl) :
    Submodule.span ℂ (radialImage p Y).affineCone.points =
      (homogeneous_plane Pl).map (TrackA.radialLinearProjection p) := by
  rw [radial_cone_points Y Pl hYP a ha p hp (Y.points_nonempty_of_isIrreducible hY.1),
    Submodule.span_image, curve_cone_span Y hY hnl Pl hPl hYP]

/-- Equal projected planes determine the three-space containing their centre. -/
theorem sup_eq_sup_center (A B : Submodule ℂ (Point n)) (P : Point n)
    (φ : LinearProjection n m) (hker : LinearMap.ker φ = ℂ ∙ P)
    (hmap : A.map φ = B.map φ) (hBA : ¬ B ≤ A) : A ⊔ B = A ⊔ ℂ ∙ P := by
  have hB : B ≤ A ⊔ ℂ ∙ P := by
    intro b hb
    have hm : φ b ∈ A.map φ := by rw [hmap]; exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hea⟩ := Submodule.mem_map.mp hm
    have hd : b-a ∈ ℂ ∙ P := by
      rw [← hker, LinearMap.mem_ker, map_sub, hea, sub_self]
    have hb' := (A ⊔ ℂ ∙ P).add_mem (show a ∈ A ⊔ ℂ ∙ P from Submodule.mem_sup_left ha)
      (show b-a ∈ A ⊔ ℂ ∙ P from Submodule.mem_sup_right hd)
    have heq : a + (b-a) = b := by abel
    rwa [heq] at hb'
  have hPU : P ∈ A ⊔ B := by
    obtain ⟨b, hb, hbA⟩ := SetLike.not_le_iff_exists.mp hBA
    have hm : φ b ∈ A.map φ := by rw [hmap]; exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hea⟩ := Submodule.mem_map.mp hm
    have hd : b-a ∈ ℂ ∙ P := by
      rw [← hker, LinearMap.mem_ker, map_sub, hea, sub_self]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hd
    have ht0 : t ≠ 0 := by
      intro hz
      have hba : b = a := sub_eq_zero.mp (by simpa [hz] using ht.symm)
      apply hbA
      rw [hba]
      exact ha
    have hdU : b-a ∈ A ⊔ B :=
      (A ⊔ B).sub_mem (Submodule.mem_sup_right hb) (Submodule.mem_sup_left ha)
    have h := (A ⊔ B).smul_mem t⁻¹ hdU
    rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul] at h
    exact h
  apply le_antisymm (sup_le le_sup_left hB)
  exact sup_le le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hPU))

/-- If both curves occupy the same plane, exterior radial projection is faithful
on their closed homogeneous cones and therefore on their affine varieties. -/
theorem equal_curves_of_equal_plane_radial (Y Y' : AffineVariety n)
    (Pl Pl' : AffineSubspace ℂ (Point n)) (hYP : Y.points ⊆ Pl) (hYP' : Y'.points ⊆ Pl')
    (ha : (Pl : Set (Point n)).Nonempty) (p : Point n) (hp : p ∉ Pl)
    (hYne : Y.points.Nonempty) (hY'ne : Y'.points.Nonempty)
    (hAB : homogeneous_plane Pl = homogeneous_plane Pl')
    (hrad : radialImage p Y = radialImage p Y') : Y = Y' := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨ρ, hρ⟩ := plane_radial_inverse Pl a ha p hp
  let π : AffineProjection (n+1) n := ⟨TrackA.radialLinearProjection p, 0⟩
  let ψ : AffineProjection n (n+1) := ⟨ρ, 0⟩
  have hcone (V : AffineVariety n) (hV : V.points ⊆ Pl) :
      ∀ v ∈ (projectiveClosure V).affineCone.points, ψ.apply (π.apply v) = v := by
    intro v hv
    have hvH := projective_closure_cone_subset V (homogeneous_plane Pl)
      (fun x hx => Submodule.subset_span ⟨x, hV hx, rfl⟩) hv
    simpa [ψ, π, AffineProjection.apply] using hρ v hvH
  have hcone' : ∀ v ∈ (projectiveClosure Y').affineCone.points, ψ.apply (π.apply v) = v := by
    intro v hv
    have hvH := projective_closure_cone_subset Y' (homogeneous_plane Pl')
      (fun x hx => Submodule.subset_span ⟨x, hYP' hx, rfl⟩) hv
    rw [← hAB] at hvH
    simpa [ψ, π, AffineProjection.apply] using hρ v hvH
  have hactual : ∃ x ∈ Y.points, x ≠ p := by
    obtain ⟨x, hx⟩ := hYne
    exact ⟨x, hx, fun h => hp (h ▸ hYP hx)⟩
  have hp' : p ∉ Pl' := by
    intro hp'
    apply hp
    apply (homogeneous_plane_cons_mem Pl a ha p).mp
    rw [hAB]
    exact Submodule.subset_span ⟨p, hp', rfl⟩
  have hactual' : ∃ x ∈ Y'.points, x ≠ p := by
    obtain ⟨x, hx⟩ := hY'ne
    exact ⟨x, hx, fun h => hp' (h ▸ hYP' hx)⟩
  have hconeeq : (projectiveClosure Y).affineCone = (projectiveClosure Y').affineCone := by
    rw [← inverse_image π ψ _ (hcone Y hYP), ← inverse_image π ψ _ hcone']
    change ψ.image ((⟨TrackA.radialLinearProjection p, 0⟩ : AffineProjection (n+1) n).image
      (projectiveClosure Y).affineCone) = ψ.image
      ((⟨TrackA.radialLinearProjection p, 0⟩ : AffineProjection (n+1) n).image
        (projectiveClosure Y').affineCone)
    rw [← radial_image_cone Y p hactual, ← radial_image_cone Y' p hactual', hrad]
  apply (AffineVariety.points_eq_iff Y Y').mp
  ext x
  have hv : Fin.cons (α := fun _ => ℂ) 1 x ≠ 0 := by
    intro hz
    have h0 := congrFun hz 0
    simpa using h0
  rw [← TrackA.affineEmbedding_mem_closure Y x, ← TrackA.affineEmbedding_mem_closure Y' x]
  change Projectivization.mk ℂ (Fin.cons 1 x) hv ∈ (projectiveClosure Y).points ↔
    Projectivization.mk ℂ (Fin.cons 1 x) hv ∈ (projectiveClosure Y').points
  rw [ProjectiveVariety.mem_points_mk_iff, ProjectiveVariety.mem_points_mk_iff, hconeeq]

theorem normalized_separating_form (S : Submodule ℂ (Point n))
    (P : Point n) (hP : P ∉ S) :
    ∃ ℓ : Point n →ₗ[ℂ] ℂ, ℓ P = 1 ∧ S ≤ LinearMap.ker ℓ := by
  obtain ⟨ℓ, hℓS, hℓP⟩ := LinearMap.exists_extend_of_notMem
    (0 : S →ₗ[ℂ] ℂ) hP (1 : ℂ)
  refine ⟨ℓ, hℓP, ?_⟩
  intro x hx
  exact LinearMap.congr_fun hℓS ⟨x, hx⟩

theorem subtract_form_center_mem (S : Submodule ℂ (Point n)) (P : Point n)
    (ℓ : Point n →ₗ[ℂ] ℂ) (hℓP : ℓ P = 1) (hℓS : S ≤ LinearMap.ker ℓ)
    (x : Point n) (hx : x ∈ S ⊔ ℂ ∙ P) : x - ℓ x • P ∈ S := by
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
  have hℓs : ℓ s = 0 := hℓS hs
  simpa [map_add, map_smul, hℓs, hℓP] using hs

theorem form_zero_iff_mem (S : Submodule ℂ (Point n)) (P : Point n)
    (ℓ : Point n →ₗ[ℂ] ℂ) (hℓP : ℓ P = 1) (hℓS : S ≤ LinearMap.ker ℓ)
    (x : Point n) (hx : x ∈ S ⊔ ℂ ∙ P) : ℓ x = 0 ↔ x ∈ S := by
  constructor
  · intro hzero
    simpa [hzero] using subtract_form_center_mem S P ℓ hℓP hℓS x hx
  · exact fun hxS => hℓS hxS

theorem cone_smul_mem_iff (V : ProjectiveVariety n) (c : ℂ) (hc : c ≠ 0)
    (x : Point n) : c • x ∈ V.affineCone.points ↔ x ∈ V.affineCone.points := by
  constructor
  · intro hx
    have h := TrackA.cone_smul_mem V (c • x) hx c⁻¹
    simpa [smul_smul, hc] using h
  · exact fun hx => TrackA.cone_smul_mem V x hx c

/-- The closed radial-image correspondence is pointwise on the two exterior planes. -/
theorem cone_correspondence (Y Y' : AffineVariety n)
    (Pl Pl' : AffineSubspace ℂ (Point n)) (hYP : Y.points ⊆ Pl) (hYP' : Y'.points ⊆ Pl')
    (a a' : Point n) (ha : a ∈ Pl) (ha' : a' ∈ Pl')
    (hYne : Y.points.Nonempty) (hY'ne : Y'.points.Nonempty)
    (p : Point n) (hp : p ∉ Pl) (hp' : p ∉ Pl')
    (hrad : radialImage p Y = radialImage p Y') (u v : Point (n+1))
    (hu : u ∈ homogeneous_plane Pl) (hv : v ∈ homogeneous_plane Pl')
    (heq : TrackA.radialLinearProjection p u = TrackA.radialLinearProjection p v) :
    u ∈ (projectiveClosure Y).affineCone.points ↔
      v ∈ (projectiveClosure Y').affineCone.points := by
  have hforward (V W : AffineVariety n) (F G : AffineSubspace ℂ (Point n))
      (hVF : V.points ⊆ F) (hWG : W.points ⊆ G)
      (b b' : Point n) (hb : b ∈ F) (hb' : b' ∈ G)
      (hVne : V.points.Nonempty) (hWne : W.points.Nonempty)
      (hpF : p ∉ F) (hpG : p ∉ G) (hVW : radialImage p V = radialImage p W)
      (z z' : Point (n+1)) (hz' : z' ∈ homogeneous_plane G)
      (hzEq : TrackA.radialLinearProjection p z = TrackA.radialLinearProjection p z')
      (hzV : z ∈ (projectiveClosure V).affineCone.points) :
      z' ∈ (projectiveClosure W).affineCone.points := by
    have hzrad : TrackA.radialLinearProjection p z ∈ (radialImage p V).affineCone.points := by
      rw [radial_cone_points V F hVF b hb p hpF hVne]
      exact ⟨z, hzV, rfl⟩
    rw [hVW, radial_cone_points W G hWG b' hb' p hpG hWne] at hzrad
    obtain ⟨w, hw, hweq⟩ := hzrad
    obtain ⟨ρ, hρ⟩ := plane_radial_inverse G b' hb' p hpG
    have hwG := projective_closure_cone_subset W (homogeneous_plane G)
      (fun x hx => Submodule.subset_span ⟨x, hWG hx, rfl⟩) hw
    have hww : w = z' := by
      rw [← hρ w hwG, ← hρ z' hz', hweq, hzEq]
    rwa [← hww]
  exact ⟨hforward Y Y' Pl Pl' hYP hYP' a a' ha ha' hYne hY'ne hp hp' hrad
      u v hv heq,
    hforward Y' Y Pl' Pl hYP' hYP a' a ha' ha hY'ne hYne hp' hp hrad.symm
      v u hu heq.symm⟩

theorem slice_direction_finrank (A : Submodule ℂ (Point n))
    (hA : Module.finrank ℂ A = 3) (ℓ : Point n →ₗ[ℂ] ℂ)
    (a : Point n) (ha : a ∈ A) (hℓa : ℓ a = 1) :
    Module.finrank ℂ ↥(A ⊓ LinearMap.ker ℓ) = 2 := by
  let f : A →ₗ[ℂ] ℂ := ℓ.comp A.subtype
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨c • ⟨a, ha⟩, ?_⟩
    simp [f, hℓa]
  have hker : Module.finrank ℂ (LinearMap.ker f) = 2 := by
    have h := f.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, hA] at h
    omega
  let i : LinearMap.ker f →ₗ[ℂ] Point n := A.subtype.comp (LinearMap.ker f).subtype
  have hi : Function.Injective i := A.subtype_injective.comp (LinearMap.ker f).subtype_injective
  have hrange : LinearMap.range i = A ⊓ LinearMap.ker ℓ := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val.property, v.property⟩
    · rintro ⟨hxA, hxℓ⟩
      exact ⟨⟨⟨x, hxA⟩, hxℓ⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hi, hker]

/-- A reduced irreducible curve contained in a line has degree one. -/
theorem curve_in_line_degree (Y : AffineVariety n) (hY : IsCurve Y)
    (L : AffineSubspace ℂ (Point n)) (hL : Module.finrank ℂ L.direction = 1)
    (hYL : Y.points ⊆ L) : Y.degree = 1 := by
  obtain ⟨a, ha⟩ := Y.points_nonempty_of_isIrreducible hY.1
  have haL := hYL ha
  have hpts : Y.points = (L : Set (Point n)) := by
    have h := GeoCommon.span_eq_of_dim_eq Y 1 hY.1 hY.2 ⟨a, ha⟩ a L.direction
      (by rwa [AffineSubspace.mk'_eq haL]) 1 hL rfl
    simpa only [AffineSubspace.mk'_eq haL] using h
  obtain ⟨v, hv⟩ : ∃ v : L.direction, v ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hL]; norm_num)
  have hv0 : (v : Point n) ≠ 0 := fun h => hv (Subtype.ext h)
  obtain ⟨j, hj⟩ := GeoRadial.exists_coord v.val hv0
  have hline : Y = Bridges.complexLine a v.val := by
    apply (AffineVariety.points_eq_iff _ _).mp
    rw [hpts, Bridges.complexLine_points a v.val j hj]
    ext x
    constructor
    · intro hx
      have hd : x-a ∈ L.direction := by simpa only [vsub_eq_sub] using L.vsub_mem_direction hx haL
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hL hv ⟨x-a, hd⟩
      refine ⟨c, ?_⟩
      have hcv : c • v.val = x-a := congrArg Subtype.val hc
      rw [hcv]
      abel
    · rintro ⟨c, rfl⟩
      have h := L.vadd_mem_of_mem_direction (L.direction.smul_mem c v.property) haL
      simpa [vadd_eq_add, add_comm] using h
  rw [hline, Bridges.complexLine_degree a v.val j hj]

/-- The two plane equations and a reference centre used to compare perspectives. -/
structure PlaneComparison (A B : Submodule ℂ (Point (n+1))) (S : Set (Point n)) where
  reference : Point n
  reference_mem : reference ∈ S
  mu : Point (n+1) →ₗ[ℂ] ℂ
  eta : Point (n+1) →ₗ[ℂ] ℂ
  mu_reference : mu (Fin.cons 1 reference) = 1
  eta_reference : eta (Fin.cons 1 reference) = 1
  mu_target : B ≤ LinearMap.ker mu
  eta_source : A ≤ LinearMap.ker eta
  source_union : A ⊔ B = A ⊔ ℂ ∙ Fin.cons 1 reference
  target_union : A ⊔ B = B ⊔ ℂ ∙ Fin.cons 1 reference
  mu_source_nonzero : ¬ A ≤ LinearMap.ker mu
  centres : ∀ p ∈ S, Fin.cons (α := fun _ => ℂ) 1 p ∈ A ⊔ B ∧
    mu (Fin.cons 1 p) ≠ 0 ∧ eta (Fin.cons 1 p) ≠ 0

theorem perspective_plane_data (Y Y' : AffineVariety n)
    (Pl Pl' : AffineSubspace ℂ (Point n))
    (hY : IsCurve Y) (hY' : IsCurve Y') (hnl : ¬ IsLine Y) (hnl' : ¬ IsLine Y')
    (hneY : Y ≠ Y') (hPl : Module.finrank ℂ Pl.direction = 2)
    (hPl' : Module.finrank ℂ Pl'.direction = 2) (hYP : Y.points ⊆ Pl) (hYP' : Y'.points ⊆ Pl')
    (S : Set (Point n)) (hS : ∀ p ∈ S, p ∉ Pl ∧ p ∉ Pl' ∧ radialImage p Y = radialImage p Y')
    (hne : S.Nonempty) : Nonempty (PlaneComparison (homogeneous_plane Pl) (homogeneous_plane Pl') S) := by
  let A := homogeneous_plane Pl
  let B := homogeneous_plane Pl'
  obtain ⟨a, haY⟩ := Y.points_nonempty_of_isIrreducible hY.1
  obtain ⟨a', haY'⟩ := Y'.points_nonempty_of_isIrreducible hY'.1
  have ha := hYP haY
  have ha' := hYP' haY'
  have hA : Module.finrank ℂ A = 3 := by
    rw [homogeneous_plane_finrank Pl a ha, hPl]
  have hB : Module.finrank ℂ B = 3 := by
    rw [homogeneous_plane_finrank Pl' a' ha', hPl']
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨hp₀P, hp₀P', hr₀⟩ := hS p₀ hp₀
  have hAB : A ≠ B := by
    intro heq
    exact hneY (equal_curves_of_equal_plane_radial Y Y' Pl Pl' hYP hYP' ⟨a, ha⟩
      p₀ hp₀P ⟨a, haY⟩ ⟨a', haY'⟩ heq hr₀)
  have hBA : ¬ B ≤ A := by
    intro hle
    exact hAB (Submodule.eq_of_le_of_finrank_eq hle (hB.trans hA.symm)).symm
  have hABle : ¬ A ≤ B := by
    intro hle
    exact hAB (Submodule.eq_of_le_of_finrank_eq hle (hA.trans hB.symm))
  have hmaps (p : Point n) (hp : p ∈ S) :
      A.map (TrackA.radialLinearProjection p) = B.map (TrackA.radialLinearProjection p) := by
    obtain ⟨hpP, hpP', hr⟩ := hS p hp
    rw [← radial_cone_span Y hY hnl Pl hPl hYP a ha p hpP,
      ← radial_cone_span Y' hY' hnl' Pl' hPl' hYP' a' ha' p hpP', hr]
  have hunion (p : Point n) (hp : p ∈ S) :
      A ⊔ B = A ⊔ ℂ ∙ Fin.cons 1 p ∧ A ⊔ B = B ⊔ ℂ ∙ Fin.cons 1 p := by
    have hker : LinearMap.ker (TrackA.radialLinearProjection p) = ℂ ∙ Fin.cons 1 p := by
      rw [TrackA.radialLinearProjection_kernel, affineEmbedding, Projectivization.submodule_mk]
    exact ⟨sup_eq_sup_center A B _ _ hker (hmaps p hp) hBA,
      (by rw [sup_comm]; exact sup_eq_sup_center B A _ _ hker (hmaps p hp).symm hABle)⟩
  have hP₀A : Fin.cons (α := fun _ => ℂ) 1 p₀ ∉ A := by
    change Fin.cons (α := fun _ => ℂ) 1 p₀ ∉ homogeneous_plane Pl
    simpa only [homogeneous_plane_cons_mem Pl a ha p₀] using hp₀P
  have hP₀B : Fin.cons (α := fun _ => ℂ) 1 p₀ ∉ B := by
    change Fin.cons (α := fun _ => ℂ) 1 p₀ ∉ homogeneous_plane Pl'
    simpa only [homogeneous_plane_cons_mem Pl' a' ha' p₀] using hp₀P'
  obtain ⟨mu, hmu0, hmuB⟩ := normalized_separating_form B (Fin.cons 1 p₀) hP₀B
  obtain ⟨eta, heta0, hetaA⟩ := normalized_separating_form A (Fin.cons 1 p₀) hP₀A
  obtain ⟨hUA, hUB⟩ := hunion p₀ hp₀
  have hmuA : ¬ A ≤ LinearMap.ker mu := by
    intro hzero
    apply hABle
    intro v hv
    apply (form_zero_iff_mem B (Fin.cons 1 p₀) mu hmu0 hmuB v ?_).mp (hzero hv)
    rw [← hUB]
    exact Submodule.mem_sup_left hv
  refine ⟨⟨p₀, hp₀, mu, eta, hmu0, heta0, hmuB, hetaA, hUA, hUB, hmuA, ?_⟩⟩
  intro p hp
  obtain ⟨hpP, hpP', _⟩ := hS p hp
  have hPU : Fin.cons (α := fun _ => ℂ) 1 p ∈ A ⊔ B := by
    rw [(hunion p hp).1]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  refine ⟨hPU, ?_, ?_⟩
  · intro hz
    have hpB : Fin.cons (α := fun _ => ℂ) 1 p ∈ B :=
      (form_zero_iff_mem B (Fin.cons 1 p₀) mu hmu0 hmuB _ (hUB ▸ hPU)).mp hz
    exact hpP' ((homogeneous_plane_cons_mem Pl' a' ha' p).mp hpB)
  · intro hz
    have hpA : Fin.cons (α := fun _ => ℂ) 1 p ∈ A :=
      (form_zero_iff_mem A (Fin.cons 1 p₀) eta heta0 hetaA _ (hUA ▸ hPU)).mp hz
    exact hpP ((homogeneous_plane_cons_mem Pl a ha p).mp hpA)

namespace PlaneComparison

variable {A B : Submodule ℂ (Point (n+1))} {S : Set (Point n)}

def scalar (D : PlaneComparison A B S) (p : S) : ℂ :=
  D.mu (Fin.cons 1 p.val) / D.eta (Fin.cons 1 p.val)

def offset (D : PlaneComparison A B S) (p : S) : Point (n+1) :=
  Fin.cons 1 D.reference - (D.eta (Fin.cons 1 p.val))⁻¹ • Fin.cons 1 p.val

def act (D : PlaneComparison A B S) (p : S) (x : Point (n+1)) : Point (n+1) :=
  D.scalar p • x + D.offset p

theorem scalar_ne_zero (D : PlaneComparison A B S) (p : S) : D.scalar p ≠ 0 :=
  div_ne_zero (D.centres p.val p.property).2.1 (D.centres p.val p.property).2.2

/-- Normalized comparisons preserve the source plane and its chart equation. -/
theorem act_plane (D : PlaneComparison A B S) (p : S) (x : Point (n+1))
    (hxA : x ∈ A) (hmux : D.mu x = 1) :
    D.act p x ∈ A ∧ D.mu (D.act p x) = 1 := by
  have hP := D.centres p.val p.property
  have hP₀ : Fin.cons (α := fun _ => ℂ) 1 D.reference ∈ A ⊔ B := by
    rw [D.source_union]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hU : D.act p x ∈ A ⊔ B :=
    (A ⊔ B).add_mem ((A ⊔ B).smul_mem _ (Submodule.mem_sup_left hxA))
      ((A ⊔ B).sub_mem hP₀ ((A ⊔ B).smul_mem _ hP.1))
  have heta_x : D.eta x = 0 := D.eta_source hxA
  have heta : D.eta (D.act p x) = 0 := by
    simp [act, offset, map_add, map_sub, map_smul, heta_x,
      D.eta_reference, hP.2.2]
  refine ⟨(form_zero_iff_mem A _ D.eta D.eta_reference D.eta_source _
      (D.source_union ▸ hU)).mp heta, ?_⟩
  simp only [act, offset, scalar, map_add, map_sub, map_smul, hmux,
    smul_eq_mul, mul_one, D.mu_reference, div_eq_mul_inv]
  ring

end PlaneComparison

theorem slice_points (V : ProjectiveVariety n) (ℓ : Point n →ₗ[ℂ] ℂ) (x : Point n) :
    x ∈ (TrackA.projectiveLinearSlice V (linear_form ℓ)).points ↔
      x ∈ V.affineCone.points ∧ ℓ x = 1 := by
  simpa only [← MvPolynomial.aeval_eq_eval, linear_form_eval] using
    TrackA.linearSlice_points V (linear_form ℓ) x

theorem chart_plane_mem (A : Submodule ℂ (Point n)) (ℓ : Point n →ₗ[ℂ] ℂ)
    (a : Point n) (ha : a ∈ A) (hℓa : ℓ a = 1) (x : Point n) :
    x ∈ AffineSubspace.mk' a (A ⊓ LinearMap.ker ℓ) ↔ x ∈ A ∧ ℓ x = 1 := by
  rw [AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_inf]
  constructor
  · rintro ⟨hxA, hxℓ⟩
    have hx : x ∈ A := by simpa using A.add_mem hxA ha
    have hzero : ℓ x - ℓ a = 0 := by simpa [LinearMap.mem_ker, map_sub] using hxℓ
    exact ⟨hx, (sub_eq_zero.mp hzero).trans hℓa⟩
  · rintro ⟨hxA, hxℓ⟩
    exact ⟨A.sub_mem hxA ha, by simp [LinearMap.mem_ker, map_sub, hxℓ, hℓa]⟩

theorem normalized_comparison_cone (Y Y' : AffineVariety n)
    (Pl Pl' : AffineSubspace ℂ (Point n)) (hYP : Y.points ⊆ Pl) (hYP' : Y'.points ⊆ Pl')
    (a a' : Point n) (ha : a ∈ Pl) (ha' : a' ∈ Pl')
    (hYne : Y.points.Nonempty) (hY'ne : Y'.points.Nonempty)
    (S : Set (Point n)) (hS : ∀ p ∈ S, p ∉ Pl ∧ p ∉ Pl' ∧ radialImage p Y = radialImage p Y')
    (D : PlaneComparison (homogeneous_plane Pl) (homogeneous_plane Pl') S)
    (p : S) (x : Point (n+1)) (hxA : x ∈ homogeneous_plane Pl) (hmux : D.mu x = 1) :
    D.act p x ∈ (projectiveClosure Y).affineCone.points ↔
      x ∈ (projectiveClosure Y).affineCone.points := by
  let A := homogeneous_plane Pl
  let B := homogeneous_plane Pl'
  let P : Point (n+1) := Fin.cons 1 p.val
  let P₀ : Point (n+1) := Fin.cons 1 D.reference
  let t : Point (n+1) := x - (D.mu P)⁻¹ • P
  have hP := D.centres p.val p.property
  have hP₀ : P₀ ∈ A ⊔ B := by
    rw [D.source_union]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have htU : t ∈ A ⊔ B :=
    (A ⊔ B).sub_mem (Submodule.mem_sup_left hxA) ((A ⊔ B).smul_mem _ hP.1)
  have hmut : D.mu t = 0 := by
    simp [t, map_sub, map_smul, hmux, hP.2.1, P]
  have htB : t ∈ B :=
    (form_zero_iff_mem B P₀ D.mu D.mu_reference D.mu_target t
      (D.target_union ▸ htU)).mp hmut
  obtain ⟨hHA, _⟩ := D.act_plane p x hxA hmux
  have hpt : TrackA.radialLinearProjection p.val x = TrackA.radialLinearProjection p.val t := by
    simp [t, P, map_sub, map_smul, TrackA.radialLinearProjection_cons]
  have hcoef : D.scalar p * (D.mu P)⁻¹ = (D.eta P)⁻¹ := by
    dsimp [PlaneComparison.scalar, P]
    field_simp [(D.centres p.val p.property).2.1, (D.centres p.val p.property).2.2]
  have hqP₀ : TrackA.radialLinearProjection D.reference P₀ = 0 := by
    simp [P₀, TrackA.radialLinearProjection_cons]
  have hreference : TrackA.radialLinearProjection D.reference (D.act p x) =
      TrackA.radialLinearProjection D.reference (D.scalar p • t) := by
    change TrackA.radialLinearProjection D.reference
      (D.scalar p • x + (P₀ - (D.eta P)⁻¹ • P)) = _
    simp only [t, map_add, map_sub, map_smul, hqP₀, zero_sub,
      smul_sub, smul_smul, hcoef] <;> simp only [sub_eq_add_neg]
  obtain ⟨hpP, hpP', hrp⟩ := hS p.val p.property
  obtain ⟨h₀P, h₀P', hr₀⟩ := hS D.reference D.reference_mem
  have hc₀ := cone_correspondence Y Y' Pl Pl' hYP hYP' a a' ha ha' hYne hY'ne
    D.reference h₀P h₀P' hr₀ (D.act p x) (D.scalar p • t) hHA
      (B.smul_mem _ htB) hreference
  have hcp := cone_correspondence Y Y' Pl Pl' hYP hYP' a a' ha ha' hYne hY'ne
    p.val hpP hpP' hrp x t hxA htB hpt
  exact hc₀.trans ((cone_smul_mem_iff (projectiveClosure Y') (D.scalar p)
    (D.scalar_ne_zero p) t).trans hcp.symm)

theorem normalized_comparison_slice (Y Y' : AffineVariety n)
    (Pl Pl' : AffineSubspace ℂ (Point n)) (hYP : Y.points ⊆ Pl) (hYP' : Y'.points ⊆ Pl')
    (a a' : Point n) (ha : a ∈ Pl) (ha' : a' ∈ Pl')
    (hYne : Y.points.Nonempty) (hY'ne : Y'.points.Nonempty)
    (S : Set (Point n)) (hS : ∀ p ∈ S, p ∉ Pl ∧ p ∉ Pl' ∧ radialImage p Y = radialImage p Y')
    (D : PlaneComparison (homogeneous_plane Pl) (homogeneous_plane Pl') S)
    (p : S) (x : Point (n+1)) (hxA : x ∈ homogeneous_plane Pl) (hmux : D.mu x = 1) :
    D.act p x ∈ (TrackA.projectiveLinearSlice (projectiveClosure Y) (linear_form D.mu)).points ↔
      x ∈ (TrackA.projectiveLinearSlice (projectiveClosure Y) (linear_form D.mu)).points := by
  rw [slice_points, slice_points, normalized_comparison_cone Y Y' Pl Pl' hYP hYP'
    a a' ha ha' hYne hY'ne S hS D p x hxA hmux, (D.act_plane p x hxA hmux).2, hmux]

/-- Conjugation of a scalar-affine map by affine coordinates has the same scalar. -/
theorem affine_conjugation (φ : AffineProjection n m) (c : ℂ) (b x : Point n) :
    φ.apply (c • x + b) = c • φ.apply x +
      (φ.linear b + (1-c) • φ.offset) := by
  ext j
  simp [AffineProjection.apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem image_mem_iff_inverse (φ : AffineProjection n m) (ψ : AffineProjection m n)
    (V : AffineVariety n) (hinv : ∀ x ∈ V.points, ψ.apply (φ.apply x) = x)
    (hrinv : ∀ y, φ.apply (ψ.apply y) = y) (y : Point m) :
    y ∈ (φ.image V).points ↔ ψ.apply y ∈ V.points := by
  constructor
  · exact fun hy => (inverse_on_image φ ψ V hinv y hy).1
  · intro hy
    have h := image_mem φ V (ψ.apply y) hy
    rwa [hrinv] at h

/-- Explicit chart transport and the faithful scalar-affine comparison action. -/
theorem chart_stabilizer_embedding
    (Y Y' : AffineVariety n) (Pl Pl' : AffineSubspace ℂ (Point n))
    (hY : IsCurve Y) (hY' : IsCurve Y') (hnl : ¬ IsLine Y) (hnl' : ¬ IsLine Y')
    (hneY : Y ≠ Y') (hPl : Module.finrank ℂ Pl.direction = 2)
    (hPl' : Module.finrank ℂ Pl'.direction = 2) (hYP : Y.points ⊆ Pl) (hYP' : Y'.points ⊆ Pl')
    (S : Set (Point n)) (hS : ∀ p ∈ S, p ∉ Pl ∧ p ∉ Pl' ∧ radialImage p Y = radialImage p Y')
    (hne : S.Nonempty) :
    ∃ Z : AffineVariety 2, IsCurve Z ∧ Z.points.Nonempty ∧
      (∀ L : AffineSubspace ℂ (Point 2), Module.finrank ℂ L.direction = 1 → ¬ Z.points ⊆ L) ∧
      Z.degree ≤ Y.degree ∧ ∃ f : S → ScalarAffine.stabilizer Z, Function.Injective f := by
  obtain ⟨D⟩ := perspective_plane_data Y Y' Pl Pl' hY hY' hnl hnl' hneY hPl hPl' hYP hYP' S hS hne
  let A := homogeneous_plane Pl
  let V := projectiveClosure Y
  let W := TrackA.projectiveLinearSlice V (linear_form D.mu)
  have hYne := Y.points_nonempty_of_isIrreducible hY.1
  have hY'ne := Y'.points_nonempty_of_isIrreducible hY'.1
  have hV : V.IsIrreducible := projectiveClosure_isIrreducible Y hY.1
  have hmu : linear_form D.mu ∉ V.ideal := by
    intro hf
    apply D.mu_source_nonzero
    have hle : Submodule.span ℂ (projectiveClosure Y).affineCone.points ≤ LinearMap.ker D.mu := by
      apply Submodule.span_le.mpr
      intro x hx
      have hz := hx _ hf
      change D.mu x = 0
      simpa only [linear_form_eval] using hz
    intro x hx
    apply hle
    rw [curve_cone_span Y hY hnl Pl hPl hYP]
    exact hx
  have hW : IsCurve W := ⟨TrackA.linearSlice_irreducible V hV _
    (linear_form_homogeneous D.mu) hmu, by
      rw [TrackA.linearSlice_dimension V hV _ (linear_form_homogeneous D.mu) hmu,
        projectiveClosure_dimension Y hYne, hY.2]⟩
  have hWdeg : W.degree = Y.degree := by
    rw [TrackA.linearSlice_degree V hV _ (linear_form_homogeneous D.mu) hmu,
      projectiveClosure_degree Y]
  obtain ⟨z₀, hz₀⟩ := W.points_nonempty_of_isIrreducible hW.1
  have hcone : V.affineCone.points ⊆ A := projective_closure_cone_subset Y A
    (fun x hx => Submodule.subset_span ⟨x, hYP hx, rfl⟩)
  obtain ⟨hz₀V, hmuz₀⟩ := (slice_points V D.mu z₀).mp hz₀
  have hz₀A := hcone hz₀V
  let F := AffineSubspace.mk' z₀ (A ⊓ LinearMap.ker D.mu)
  have hF : Module.finrank ℂ F.direction = 2 := by
    rw [AffineSubspace.direction_mk']
    obtain ⟨a, ha⟩ := hYne
    apply slice_direction_finrank A _ D.mu z₀ hz₀A hmuz₀
    rw [homogeneous_plane_finrank Pl a (hYP ha), hPl]
  have hWF : W.points ⊆ F := by
    intro x hx
    obtain ⟨hxV, hmux⟩ := (slice_points V D.mu x).mp hx
    exact (chart_plane_mem A D.mu z₀ hz₀A hmuz₀ x).mpr ⟨hcone hxV, hmux⟩
  obtain ⟨φ, ψ, hinvF, hrinv, hψF⟩ := affine_coordinates F 2 hF z₀ (AffineSubspace.self_mem_mk' _ _)
  have hinvW : ∀ x ∈ W.points, ψ.apply (φ.apply x) = x := fun x hx => hinvF x (hWF hx)
  let Z := φ.image W
  have hZ : IsCurve Z := ⟨φ.image_irreducible W hW.1, by
    rw [image_dimension φ ψ W hinvW, hW.2]⟩
  have hZdeg : Z.degree = Y.degree := (image_degree φ ψ W hinvW).trans hWdeg
  have hZne : Z.points.Nonempty := ⟨φ.apply z₀, image_mem φ W z₀ hz₀⟩
  have hYdeg : Y.degree ≠ 1 := fun he => hnl (Bridges.degree_one_curve_line Y hY.1 hY.2 he)
  have hZline : ∀ L : AffineSubspace ℂ (Point 2), Module.finrank ℂ L.direction = 1 → ¬ Z.points ⊆ L := by
    intro L hL hZL
    exact hYdeg (hZdeg.symm.trans (curve_in_line_degree Z hZ L hL hZL))
  let g : S → ScalarAffine := fun p =>
    ⟨Units.mk0 (D.scalar p) (D.scalar_ne_zero p),
      φ.linear (D.offset p) + (1-D.scalar p) • φ.offset⟩
  have hact (p : S) (x : Point 2) :
      ψ.apply (ScalarAffine.act (g p) x) = D.act p (ψ.apply x) := by
    have hx := (chart_plane_mem A D.mu z₀ hz₀A hmuz₀ (ψ.apply x)).mp (hψF x)
    have hHx := D.act_plane p (ψ.apply x) hx.1 hx.2
    have hHF : D.act p (ψ.apply x) ∈ F :=
      (chart_plane_mem A D.mu z₀ hz₀A hmuz₀ _).mpr hHx
    have hφH : φ.apply (D.act p (ψ.apply x)) = ScalarAffine.act (g p) x := by
      rw [PlaneComparison.act, affine_conjugation, hrinv]
      rfl
    rw [← hφH, hinvF _ hHF]
  obtain ⟨a, haY⟩ := hYne
  obtain ⟨a', haY'⟩ := hY'ne
  have hg (p : S) : g p ∈ ScalarAffine.stabilizer Z := by
    intro x
    have hx := (chart_plane_mem A D.mu z₀ hz₀A hmuz₀ (ψ.apply x)).mp (hψF x)
    change ScalarAffine.act (g p) x ∈ Z.points ↔ x ∈ Z.points
    rw [image_mem_iff_inverse φ ψ W hinvW hrinv, hact]
    exact (normalized_comparison_slice Y Y' Pl Pl' hYP hYP' a a' (hYP haY) (hYP' haY')
      ⟨a, haY⟩ ⟨a', haY'⟩ S hS D p (ψ.apply x) hx.1 hx.2).trans
        (image_mem_iff_inverse φ ψ W hinvW hrinv x).symm
  let f : S → ScalarAffine.stabilizer Z := fun p => ⟨g p, hg p⟩
  refine ⟨Z, hZ, hZne, hZline, hZdeg.le, f, ?_⟩
  intro p q hpq
  have hgEq : g p = g q := congrArg Subtype.val hpq
  have hs : D.scalar p = D.scalar q := by
    have h := congrArg (fun k : ScalarAffine => (k.scalar : ℂ)) hgEq
    exact h
  have hacts : D.act p (ψ.apply 0) = D.act q (ψ.apply 0) := by
    rw [← hact, ← hact, hgEq]
  have hb : D.offset p = D.offset q := by
    simp only [PlaneComparison.act, hs] at hacts
    exact add_left_cancel hacts
  have hscaled : (D.eta (Fin.cons 1 p.val))⁻¹ • Fin.cons (α := fun _ => ℂ) 1 p.val =
      (D.eta (Fin.cons 1 q.val))⁻¹ • Fin.cons (α := fun _ => ℂ) 1 q.val := by
    exact sub_right_injective hb
  have hinv : (D.eta (Fin.cons 1 p.val))⁻¹ = (D.eta (Fin.cons 1 q.val))⁻¹ := by
    simpa only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero, mul_one] using congrFun hscaled 0
  apply Subtype.ext
  ext j
  have h := congrFun hscaled j.succ
  simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ, hinv] at h
  exact mul_left_cancel₀ (inv_ne_zero (D.centres q.val q.property).2.2) h

end
end DistinctDistances.TrackD.PerspectiveTransport
