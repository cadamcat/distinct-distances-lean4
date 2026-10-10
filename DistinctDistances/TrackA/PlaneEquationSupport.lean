import DistinctDistances.TrackA.Definitions
import OAI.NumberTheory.PowerFree.SurfaceCounting

namespace DistinctDistances.TrackA
noncomputable section

/-- Once a projective equation is supplied, positivity, squarefreeness and
its actual Hilbert degree follow from the shared model and original OAI API. -/
theorem projective_equation_invariants {n : ℕ} (C : ProjectiveVariety (n+1))
    (hne : C.points.Nonempty) (f : Poly (n+1)) (hf : f ≠ 0)
    (hC : C.ideal = Ideal.span {f}) :
    1 ≤ f.totalDegree ∧ (f.totalDegree : ℚ) = C.degree ∧ Squarefree f := by
  obtain ⟨p, hp⟩ := hne
  have heval : MvPolynomial.eval p.rep f = 0 := by
    have hrep := hp p.rep p.rep_nonzero (Projectivization.mk_rep p)
    have hmem : f ∈ C.ideal := by rw [hC]; exact Ideal.subset_span rfl
    simpa only [MvPolynomial.aeval_eq_eval] using hrep f hmem
  have hpos : 0 < f.totalDegree := by
    by_contra hnot
    have hzero : f.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
    have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
    rw [hconstant, MvPolynomial.eval_C] at heval
    apply hf
    rw [hconstant, heval, map_zero]
  refine ⟨hpos, ?_, ?_⟩
  · rw [← C.degree_cone]
    change (f.totalDegree : ℚ) = OAI.QuarticPowerFree.affineDegree C.ideal
    rw [hC, OAI.QuarticPowerFree.affineDegree_hypersurface f hf hpos]
  · apply (isRadical_iff_squarefree_of_ne_zero hf).mp
    apply isRadical_iff_span_singleton.mpr
    rw [← hC]
    exact C.isRadical

end
end DistinctDistances.TrackA
