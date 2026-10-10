import DistinctDistances.Foundations.Projection
import DistinctDistances.TrackE.MReqAux

/-! Track A's actual radial-map pullback, consumed by the proper-cut step
at sparse-cones.tex:721–732. No rank, mass or no-capture conclusion is an input. -/
namespace DistinctDistances.Request
noncomputable section

/-- Pull back a homogeneous equation along y ↦ [y-p]. Its physical numerator
has degree at most L and is proper on Y whenever the equation is proper on
the complete radial image of Y. Supplier: FA.model / poly:projection. -/
theorem bounded_radial_pullback {d L : ℕ} (p : Point d) (Y : AffineVariety d)
    (f : Poly d) (hf : f.IsHomogeneous L) :
    ∃ g : Poly d, g.totalDegree ≤ L ∧
      (f ∉ (radialImage p Y).ideal → g ∉ Y.ideal) ∧
      ∀ x : Point d, MvPolynomial.eval x g = MvPolynomial.eval (x - p) f := by
  refine ⟨TrackA.radialDirectionPullback p f, ?_, ?_, ?_⟩
  · calc (TrackA.radialDirectionPullback p f).totalDegree ≤ f.totalDegree :=
          MReqAux.radialDirectionPullback_totalDegree_le p f
      _ ≤ L := hf.totalDegree_le
  · intro hnot
    exact TrackA.radialDirectionPullback_not_mem Y p f hf hnot
  · intro x
    exact TrackA.radialDirectionPullback_eval p x f

end
end DistinctDistances.Request
