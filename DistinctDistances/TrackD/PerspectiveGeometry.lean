import DistinctDistances.TrackD.PerspectiveTranslation
import DistinctDistances.TrackD.Requests

namespace DistinctDistances.TrackD.PerspectiveCore

open scoped Classical
noncomputable section

variable {G : Type*} [Group G]

/-- The algebraic stabilizer step of `secants.tex:351–367`, after passing to the affine
plane chart. The Bézout line-section bound is the explicit track-A input. -/
theorem planar_stabilizer_bound (Y : AffineVariety 2) (hY : IsCurve Y)
    (hne : Y.points.Nonempty)
    (hproper : ∀ L : AffineSubspace ℂ (Point 2), Module.finrank ℂ L.direction = 1 →
      ¬ Y.points ⊆ L)
    (χ : G →* ℂˣ) (b : G → Point 2)
    (hcomp : ∀ g h, b (g * h) = (χ g : ℂ) • b h + b g)
    (hfaithful : ∀ g, χ g = 1 → b g = 0 → g = 1)
    (hpreserve : ∀ g p, p ∈ Y → orbit χ b p g ∈ Y) :
    (Set.univ : Set G).Finite ∧ ((Set.univ : Set G).ncard : ℝ) ≤ (Y.degree : ℝ) := by
  obtain ⟨p₀, hp₀⟩ := hne
  have htranslation : ∀ g, χ g = 1 → b g = 0 := by
    intro g hg
    by_contra hb
    let L := AffineSubspace.mk' p₀ (ℂ ∙ b g)
    have hL : Module.finrank ℂ L.direction = 1 := by
      rw [AffineSubspace.direction_mk']
      exact finrank_span_singleton hb
    obtain ⟨hT, _⟩ := request_planar_curve_line_intersection Y hY L hL (hproper L hL)
    apply hb
    apply translation_zero_of_finite_orbit χ b hcomp g hg p₀
      (Y.points ∩ (L : Set (Point 2))) hT
    intro n
    refine ⟨hpreserve (g ^ n) p₀ hp₀, ?_⟩
    rw [translation_orbit_form χ b hcomp g hg p₀]
    apply AffineSubspace.mem_mk'.mpr
    change p₀ + n • b g - p₀ ∈ (ℂ ∙ b g : Submodule ℂ (Point 2))
    rw [add_sub_cancel_left]
    have hm : (n : ℂ) • b g ∈ (ℂ ∙ b g : Submodule ℂ (Point 2)) :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (b g))
    simpa only [Nat.cast_smul_eq_nsmul] using hm
  have hinj := scalar_injective χ b hfaithful htranslation
  obtain ⟨c, hcenter⟩ := center_exists χ b hinj hcomp
  let v : Point 2 := Pi.single (0 : Fin 2) (1 : ℂ)
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h (0 : Fin 2)
    simpa [v] using this
  let L₀ := AffineSubspace.mk' c (ℂ ∙ v)
  have hL₀ : Module.finrank ℂ L₀.direction = 1 := by
    rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton hv
  obtain ⟨p, hp, hpL₀⟩ := Set.not_subset.mp (hproper L₀ hL₀)
  have hpc : p ≠ c := by
    rintro rfl
    exact hpL₀ (AffineSubspace.self_mem_mk' _ _)
  let L := AffineSubspace.mk' c (ℂ ∙ (p - c))
  have hL : Module.finrank ℂ L.direction = 1 := orbit_line_dimension c p hpc
  obtain ⟨hT, hdeg⟩ := request_planar_curve_line_intersection Y hY L hL (hproper L hL)
  obtain ⟨hfin, hcard⟩ := stabilizer_bound χ b c p hinj hcenter hpc
    (Y.points ∩ (L : Set (Point 2))) hT
    (fun g => ⟨hpreserve g p hp, orbit_on_line χ b c p hcenter g⟩)
  refine ⟨hfin, ?_⟩
  have hcardR : ((Set.univ : Set G).ncard : ℝ) ≤
      ((Y.points ∩ (L : Set (Point 2))).ncard : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans hdeg

end
end DistinctDistances.TrackD.PerspectiveCore
