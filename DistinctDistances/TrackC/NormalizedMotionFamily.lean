import DistinctDistances.TrackC.MotionChartWholeDistinctness

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Assemble the canonical-chart constructions in the common parameter space,
motions.tex:298–372. This has the original normalized_motion_flats interface. -/
theorem normalized_motion_flats_construct (X Y : Finset (E 3)) (G : Finset (Motion 3))
    (hG : ∀ g ∈ G, reverseMotion g ∧ Module.finrank ℝ (axis g) = 1 ∧
      axisAvoidsTriples g (matchPoints X Y g)) :
    ∃ F : Motion 3 → Flat 6 3,
      Set.InjOn F (G : Set (Motion 3)) ∧
      (∀ g ∈ G, MotionFlatModel g (matchPoints X Y g) (F g)) ∧
      (∀ x ∈ X, ∀ y ∈ Y, ∀ g ∈ G, ∀ g' ∈ G,
        g x = y → g' x = y → g ≠ g' →
          pairFlatSet x y ∩ ((F g).1 : Set (E 6)) ≠
            pairFlatSet x y ∩ ((F g').1 : Set (E 6))) := by
  have hex (g : Motion 3) (hg : g ∈ G) :
      ∃ (c : MotionChartData g) (F : Flat 6 3),
        (F.1 : Set (E 6)) = c.parameterSet ∧ MotionFlatModel g (matchPoints X Y g) F :=
    normalized_single_motion g (matchPoints X Y g) (hG g hg).1 (hG g hg).2.1 (hG g hg).2.2
  choose chart flat hflat hmodel using hex
  obtain ⟨F₀,hF₀,hnull₀⟩ := canonical_motion_null_flat 0 0 0 0
  let F : Motion 3 → Flat 6 3 := fun g => if hg : g ∈ G then flat g hg else F₀
  have hF (g : Motion 3) (hg : g ∈ G) : F g = flat g hg := by simp only [F,dif_pos hg]
  have hFset (g : Motion 3) (hg : g ∈ G) : ((F g).1 : Set (E 6)) = (chart g hg).parameterSet := by
    rw [hF g hg]
    exact hflat g hg
  refine ⟨F,?_,?_,?_⟩
  · intro g hg h hh heq
    have hsets : (chart g hg).parameterSet = (chart h hh).parameterSet := by
      rw [← hFset g hg,← hFset h hh]
      exact congrArg (fun Q : Flat 6 3 => (Q.1 : Set (E 6))) heq
    exact (chart g hg).same_motion_of_parameterSet (chart h hh) hsets
  · intro g hg
    rw [hF g hg]
    exact hmodel g hg
  · intro x hx y hy g hg h hh hxy hxy' hne hsections
    rw [hFset g hg,hFset h hh] at hsections
    exact hne ((chart g hg).same_motion_of_pair_section (chart h hh) x y hxy hxy' hsections)

end DistinctDistances.TrackC
