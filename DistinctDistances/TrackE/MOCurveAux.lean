import DistinctDistances.TrackA.ProjectiveChartSupport
import DistinctDistances.TrackA.ProjectiveChartRankSupport
import DistinctDistances.Foundations.Projection
import DistinctDistances.Foundations.Projective
import DistinctDistances.Foundations.Affine
import DistinctDistances.Bridges.DirectionSections
import DistinctDistances.TrackE.MReqAux

namespace DistinctDistances.SparseCones.MOCurveAux

open scoped BigOperators Classical
noncomputable section

variable {n : ℕ}

/-- Projective subvariety inclusion from points inclusion. -/
theorem projectiveSubvariety_of_points_subset
    (W V : ProjectiveVariety n) (h : W.points ⊆ V.points) :
    W.Subvariety V := by
  have hrep : ProjectiveVariety.nonzeroRepresentatives W.points ⊆
      ProjectiveVariety.nonzeroRepresentatives V.points := by
    intro v hv
    obtain ⟨hv0, hmem⟩ := hv
    exact ⟨hv0, h hmem⟩
  have hvan : MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives V.points) ≤
      MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives W.points) :=
    MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) hrep
  have hW : MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives W.points) = W.ideal :=
    ProjectiveVariety.vanishingIdeal_points W
  have hV : MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives V.points) = V.ideal :=
    ProjectiveVariety.vanishingIdeal_points V
  rw [hV, hW] at hvan
  exact hvan

/-- Closure of a point set inside a projective variety stays inside it. -/
theorem projective_closure_points_subset_of_subset
    (S : Set (ProjectivePoint n)) (V : ProjectiveVariety n)
    (hS : S ⊆ V.points) :
    (ProjectiveVariety.closure S).points ⊆ V.points := by
  intro z hz
  -- unfold membership in the closure
  have hz' : ∀ (v : Point n) (hv : v ≠ 0),
      Projectivization.mk ℂ v hv = z →
      v ∈ MvPolynomial.zeroLocus ℂ (ProjectiveVariety.vanishingIdeal S) := by
    intro v hv he
    exact hz v hv he
  intro v hv he
  -- it suffices to show every equation of V vanishes at v
  intro f hf
  have hfV : f ∈ ProjectiveVariety.vanishingIdeal V.points := by
    rw [ProjectiveVariety.vanishingIdeal_points]
    exact hf
  have hfS : f ∈ ProjectiveVariety.vanishingIdeal S := by
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro w ⟨hw0, hwS⟩
    have hwV : Projectivization.mk ℂ w hw0 ∈ V.points := hS hwS
    have hwCone : w ∈ V.affineCone.points :=
      (ProjectiveVariety.mem_points_mk_iff V w hw0).mp hwV
    exact MvPolynomial.mem_zeroLocus_iff.mp hwCone f hf
  have hmem := hz' v hv he f hfS
  simpa [MvPolynomial.aeval_eq_eval] using hmem

/-- Translation identity for cone equations (cf. `SparseCones.eval_translate`;
duplicated here to avoid a forward reference from the radial-image leaves). -/
theorem mo_eval_translate (p x : Point n) (g : Poly n) :
    MvPolynomial.eval x
        (MvPolynomial.aeval (fun a => (MvPolynomial.X a -
          MvPolynomial.C (p a) : Poly n)) g) =
      MvPolynomial.eval (x - p) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | mul_X f i hf =>
    rw [map_mul, map_mul, hf, map_mul]
    simp

theorem mo_eval_translate_aeval (p x : Point n) (g : Poly n) :
    (MvPolynomial.aeval x
        (MvPolynomial.aeval (fun a => (MvPolynomial.X a -
          MvPolynomial.C (p a) : Poly n)) g)) =
      (MvPolynomial.aeval (x - p) g) :=
  mo_eval_translate p x g

end

end DistinctDistances.SparseCones.MOCurveAux
