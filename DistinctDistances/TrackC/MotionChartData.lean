import DistinctDistances.TrackC.AxisFrame
import DistinctDistances.TrackC.CanonicalPhysical
import DistinctDistances.TrackC.AxisAvoidanceTransport
import DistinctDistances.TrackC.CanonicalCayley
import DistinctDistances.TrackC.CanonicalModelRange
import DistinctDistances.TrackC.CanonicalChartIntrinsic
import DistinctDistances.TrackC.CanonicalPairProjection

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- A full reversing graph in one proper orthonormal axis frame. -/
structure MotionChartData (g : Motion 3) where
  frame : E 3 ≃ₗᵢ[ℝ] E 3
  proper : LinearMap.det frame.toLinearMap = 1
  s : ℝ
  omega : ℝ
  d₀ : ℝ
  d₁ : ℝ
  graph : ∀ x : E 3, ((x+motionConjugate frame g x) 2)/2 = s ∧
    ((x-motionConjugate frame g x) 0)/2 = d₀-omega*((x+motionConjugate frame g x) 1)/2 ∧
    ((x-motionConjugate frame g x) 1)/2 = d₁+omega*((x+motionConjugate frame g x) 0)/2

def MotionChartData.parameterSet {g : Motion 3} (c : MotionChartData g) : Set (E 6) :=
  sixRotate c.frame.symm '' Set.range (canonicalMotionParameter c.s c.omega c.d₀ c.d₁)

theorem MotionChartData.intrinsic_graph {g : Motion 3} (c : MotionChartData g) :
    ∀ x : E 3, inner ℝ (motionChartAxis c.frame) (x+g x) = 2*c.s ∧
      motionOrthogonalPart (motionChartAxis c.frame) (x-g x) =
        c.omega • cross3 (motionChartAxis c.frame) (x+g x)+2 • motionChartOffset c.frame c.d₀ c.d₁ :=
  canonical_graph_intrinsic c.frame c.proper g c.s c.omega c.d₀ c.d₁ c.graph

theorem MotionChartData.intrinsic_flat {g : Motion 3} (c : MotionChartData g) :
    c.parameterSet = {z : E 6 | inner ℝ (motionChartAxis c.frame) (wCoord z) = c.omega ∧
      motionOrthogonalPart (motionChartAxis c.frame) (cCoord z) =
        motionChartOffset c.frame c.d₀ c.d₁+c.s • cross3 (motionChartAxis c.frame) (wCoord z)} :=
  canonical_flat_intrinsic c.frame c.proper c.s c.omega c.d₀ c.d₁

theorem MotionChartData.w_projection {g : Motion 3} (c : MotionChartData g) :
    wCoord '' c.parameterSet = {w : E 3 | inner ℝ (motionChartAxis c.frame) w = c.omega} :=
  canonical_rotated_w_projection c.frame c.s c.omega c.d₀ c.d₁

theorem MotionChartData.pair_w_projection {g : Motion 3} (c : MotionChartData g)
    (x y : E 3) (hxy : g x = y) :
    wCoord '' (pairFlatSet x y ∩ c.parameterSet) =
      {w : E 3 | inner ℝ (motionChartAxis c.frame) w = c.omega} := by
  apply rotated_pair_w_projection c.frame c.proper x y c.s c.omega c.d₀ c.d₁
  have h := c.graph (c.frame x)
  simpa only [motionConjugate_apply,c.frame.symm_apply_apply,hxy] using h

/-- A single normalized motion, retaining both the canonical flat set and its
graph-dual model, motions.tex:298–346. -/
theorem normalized_single_motion (g : Motion 3) (S : Finset (E 3))
    (hrev : reverseMotion g) (haxis : Module.finrank ℝ (axis g) = 1)
    (havoid : axisAvoidsTriples g S) :
    ∃ (c : MotionChartData g) (F : Flat 6 3),
      (F.1 : Set (E 6)) = c.parameterSet ∧ MotionFlatModel g S F := by
  obtain ⟨R,hR,hRAxis⟩ := spatial_axis_frame (axis g) haxis
  let gr := motionConjugate R g
  have hrrev : reverseMotion gr := reverse_motion_conjugate R hR g hrev
  have hraxis : axis gr = Submodule.span ℝ {EuclideanSpace.single (2 : Fin 3) (1 : ℝ)} := by
    rw [axis_motionConjugate]
    exact hRAxis
  obtain ⟨s,ω,d₀,d₁,hgraph⟩ := canonical_reversing_graph gr hrrev hraxis
  let c : MotionChartData g := ⟨R,hR,s,ω,d₀,d₁,hgraph⟩
  obtain ⟨T,hT⟩ := canonical_physical_equiv gr hraxis
  have havoidR : axisAvoidsTriples gr (S.image R) := axis_avoidance_conjugate R g S havoid
  have hproj := canonical_projection_triples gr (S.image R) hraxis havoidR
  obtain ⟨Fc,hFc,hFcModel⟩ := canonical_motion_flat_model_with_range gr (S.image R) s ω d₀ d₁ T
    (fun x hx => by simpa only [canonicalPhysicalPoint] using hT x)
    (fun x hx => hgraph x)
    (by
      intro x hx y hy z hz htri
      simpa only [hT] using hproj x hx y hy z hz htri)
  obtain ⟨F,hF,hFModel⟩ := motion_flat_model_rotate R.symm (proper_rotation_symm R hR)
    gr (S.image R) Fc hFcModel
  refine ⟨c,F,?_,?_⟩
  · rw [hF,hFc]
    rfl
  · simpa [gr,Finset.image_image,Function.comp_def] using hFModel

end DistinctDistances.TrackC
