import DistinctDistances.TrackA.ProjectionSourceSupport
import OAI.NumberTheory.PowerFree.ProjectionDegrees

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

def radialLinearProjection {n : ℕ} (p : Point n) : LinearProjection (n+1) n where
  toFun v j := v j.succ - v 0 * p j
  map_add' v w := by ext j; simp only [Pi.add_apply]; ring
  map_smul' c v := by ext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem radialLinearProjection_cons {n : ℕ} (p x : Point n) :
    radialLinearProjection p (Fin.cons 1 x) = x-p := by
  ext j
  simp [radialLinearProjection]

theorem radialLinearProjection_surjective {n : ℕ} (p : Point n) :
    Function.Surjective (radialLinearProjection p) := by
  intro x
  refine ⟨Fin.cons 0 x, ?_⟩
  ext j
  simp [radialLinearProjection]

theorem radialLinearProjection_kernel {n : ℕ} (p : Point n) :
    LinearMap.ker (radialLinearProjection p) = (affineEmbedding p).submodule := by
  rw [affineEmbedding, Projectivization.submodule_mk]
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨v 0, ?_⟩
    ext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
      have h := congrFun hv j
      exact (sub_eq_zero.mp h).symm
  · rintro ⟨c, rfl⟩
    ext j
    simp [radialLinearProjection, Pi.smul_apply, smul_eq_mul]

theorem linearPullback_eval {n m : ℕ} (φ : LinearProjection n m) (F : Poly m) (v : Point n) :
    MvPolynomial.eval v (linearPullback φ F) = MvPolynomial.eval (φ v) F := by
  change MvPolynomial.aeval v (MvPolynomial.aeval (linearCoordinate φ) F) = _
  rw [MvPolynomial.comp_aeval_apply]
  have hcoords : (fun j => MvPolynomial.aeval v (linearCoordinate φ j)) = φ v := by
    funext j
    exact linearCoordinate_eval φ v j
  rw [hcoords, MvPolynomial.aeval_eq_eval]

theorem affineEmbedding_mem_closure {n : ℕ} (X : AffineVariety n) (x : Point n) :
    affineEmbedding x ∈ (projectiveClosure X).points ↔ x ∈ X.points := by
  change affineEmbedding x ∈ projectiveClosure X ↔ x ∈ X
  rw [← (projectiveClosure X).chart_mem_iff (affineEmbedding x) 0
    (chartCoordinates_affineEmbedding x).2, projectiveClosure_chart_zero,
    (chartCoordinates_affineEmbedding x).1]

theorem affineEmbedding_injective {n : ℕ} :
    Function.Injective (affineEmbedding (n := n)) := by
  intro x y h
  have hh := congrArg (chartCoordinates 0) h
  simpa only [(chartCoordinates_affineEmbedding x).1,
    (chartCoordinates_affineEmbedding y).1] using hh

theorem affineEmbedding_chartCoordinates {n : ℕ} (q : ProjectivePoint (n+1))
    (hq : q.rep 0 ≠ 0) : affineEmbedding (chartCoordinates 0 q) = q := by
  rw [← Projectivization.mk_rep q]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(q.rep 0)⁻¹, ?_⟩
  ext j
  cases j using Fin.cases with
  | zero => simp [Pi.smul_apply, smul_eq_mul, hq]
  | succ j => simp [chartCoordinates, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem radialLinearProjection_embedding_nonzero {n : ℕ} (p x : Point n) :
    radialLinearProjection p (affineEmbedding x).rep ≠ 0 ↔ x ≠ p := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (Fin.cons (α := fun _ => ℂ) (1 : ℂ) x) (by
      intro hz
      have h0 := congrFun hz (0 : Fin (n+1))
      exact one_ne_zero (by simpa only [Fin.cons_zero, Pi.zero_apply] using h0))
  change (u : ℂ) • Fin.cons (1 : ℂ) x = (affineEmbedding x).rep at hu
  rw [← hu, map_smul, radialLinearProjection_cons]
  simp [Units.ne_zero u, sub_ne_zero]

theorem projectiveMap_radial {n : ℕ} (p x : Point n) (hx : x ≠ p)
    (hφ : radialLinearProjection p (affineEmbedding x).rep ≠ 0) :
    projectiveMap (radialLinearProjection p) (affineEmbedding x) hφ = radialProjection p x hx := by
  obtain ⟨hv, he⟩ := projectiveMap_embedding_data (radialLinearProjection p) x hφ
  simpa only [radialLinearProjection_cons, radialProjection] using he

/-- Closing the affine source before radial projection does not change its image. -/
theorem radial_projective_image {n : ℕ} (X : AffineVariety n) (p : Point n)
    (hactual : ∃ x ∈ X.points, x ≠ p) :
    projectiveImage (radialLinearProjection p) (projectiveClosure X) = radialImage p X := by
  let φ := radialLinearProjection p
  let Y := radialImage p X
  let T : Set (ProjectivePoint n) :=
    {z | ∃ v : Point (n+1), ∃ hv : v ≠ 0,
      Projectivization.mk ℂ v hv ∈ projectiveClosure X ∧
      ∃ hφ : φ v ≠ 0, Projectivization.mk ℂ (φ v) hφ = z}
  have hrad : {z | ∃ x ∈ X.points, ∃ hx : x ≠ p, radialProjection p x hx = z} ⊆ T := by
    rintro z ⟨x, hx, hxne, rfl⟩
    have hv : Fin.cons (α := fun _ => ℂ) (1 : ℂ) x ≠ 0 := by
      intro hz
      have h0 := congrFun hz (0 : Fin (n+1))
      exact one_ne_zero (by simpa only [Fin.cons_zero, Pi.zero_apply] using h0)
    refine ⟨Fin.cons 1 x, hv, (affineEmbedding_mem_closure X x).mpr hx,
      by simpa only [φ, radialLinearProjection_cons] using sub_ne_zero.mpr hxne, ?_⟩
    simp only [φ, radialLinearProjection_cons, radialProjection]
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hactual
  have hY0 : (0 : Point n) ∈ Y.affineCone.points := by
    have hz : radialProjection p x₀ hx₀ne ∈ Y.points :=
      ProjectiveVariety.subset_closure _ ⟨x₀, hx₀, hx₀ne, rfl⟩
    have hvec : x₀-p ∈ Y.affineCone.points :=
      (Y.mem_points_mk_iff _ (sub_ne_zero.mpr hx₀ne)).mp hz
    simpa using cone_smul_mem Y (x₀-p) hvec 0
  have hpull (G : Poly n) (d : ℕ) (hG : G.IsHomogeneous d) (hGY : G ∈ Y.ideal) :
      linearPullback φ G ∈ (projectiveClosure X).ideal := by
    have hhom : (linearPullback φ G).IsHomogeneous d := by
      change (MvPolynomial.aeval (linearCoordinate φ) G).IsHomogeneous d
      simpa only [one_mul] using hG.aeval (linearCoordinate φ) (linearCoordinate_homogeneous φ)
    apply (projectiveClosure_homogeneous_mem X _ hhom).mpr
    rw [← X.vanishingIdeal_points]
    intro x hx
    change MvPolynomial.aeval x
      (MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) (linearPullback φ G)) = 0
    rw [MvPolynomial.comp_aeval_apply]
    have hcoords : (fun j => MvPolynomial.aeval x
        (Fin.cons (α := fun _ => Poly n) 1 MvPolynomial.X j)) = Fin.cons (1 : ℂ) x := by
      funext j
      cases j using Fin.cases <;> simp
    rw [hcoords, MvPolynomial.aeval_eq_eval, linearPullback_eval]
    change MvPolynomial.eval (radialLinearProjection p (Fin.cons 1 x)) G = 0
    rw [radialLinearProjection_cons]
    by_cases hxne : x = p
    · subst x
      simpa using hY0 G hGY
    · have hz : radialProjection p x hxne ∈ Y.points :=
        ProjectiveVariety.subset_closure _ ⟨x, hx, hxne, rfl⟩
      exact hz (x-p) (sub_ne_zero.mpr hxne) rfl G hGY
  have hT : T ⊆ Y.points := by
    rintro z ⟨v, hv, hvX, hφ, rfl⟩
    apply (Y.mem_points_mk_iff _ hφ).mpr
    intro F hF
    rw [← MvPolynomial.sum_homogeneousComponent F]
    simp only [map_sum, MvPolynomial.aeval_eq_eval]
    apply Finset.sum_eq_zero
    intro d hd
    have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem Y.isHomogeneous hF d
    have hmem := hpull _ d (MvPolynomial.homogeneousComponent_isHomogeneous d F) hcomp
    have hz := hvX v hv rfl (linearPullback φ (MvPolynomial.homogeneousComponent d F)) hmem
    simpa only [MvPolynomial.aeval_eq_eval, linearPullback_eval] using hz
  apply ProjectiveVariety.ext
  apply le_antisymm
  · exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) (by
      intro v hv
      exact ⟨hv.1, hrad hv.2⟩)
  · change Y.ideal ≤ ProjectiveVariety.vanishingIdeal T
    rw [← Y.vanishingIdeal_points]
    exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) (by
      intro v hv
      exact ⟨hv.1, hT hv.2⟩)

end
end DistinctDistances.TrackA
