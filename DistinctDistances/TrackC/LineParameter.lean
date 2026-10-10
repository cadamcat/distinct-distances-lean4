import DistinctDistances.TrackC.LinePolynomial

namespace DistinctDistances.TrackC

/-- An affine line admits an injective real vector parameter. -/
theorem affine_line_parameter (d : ℕ) (l : Line d) :
    ∃ x v : E d, v ≠ 0 ∧ Set.range (fun t : ℝ => x + t • v) = (l.1 : Set (E d)) ∧
      Function.Injective (fun t : ℝ => x + t • v) := by
  classical
  obtain ⟨x, hx⟩ := l.2.1
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp l.2.2
  have hv0 : (v : E d) ≠ 0 := by
    intro h
    apply hv
    exact Subtype.ext h
  refine ⟨x, v, hv0, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨t, rfl⟩
      change x + t • (v : E d) ∈ l.1
      apply (l.1.vsub_right_mem_direction_iff_mem hx (x + t • (v : E d))).mp
      change (x + t • (v : E d)) - x ∈ l.1.direction
      simpa only [add_sub_cancel_left] using l.1.direction.smul_mem t v.property
    · intro hy
      let w : l.1.direction := ⟨y-x, l.1.vsub_mem_direction hy hx⟩
      obtain ⟨t, ht⟩ := hspan w
      refine ⟨t, ?_⟩
      have h := congrArg (fun q : l.1.direction => (q : E d)) ht
      change t • (v : E d) = y-x at h
      change x + t • (v : E d) = y
      rw [h]
      simp
  · intro a b hab
    have h : a • (v : E d) = b • (v : E d) := add_left_cancel hab
    exact smul_left_injective ℝ hv0 h

/-- A noncontained line has a nonzero restriction polynomial. -/
theorem linePolynomial_ne_zero_of_range (d : ℕ) (f : Poly d) (l : Line d) (x v : E d)
    (hrange : Set.range (fun t : ℝ => x+t • v) = (l.1 : Set (E d)))
    (hn : ¬ onPolynomial f l) : linePolynomial d f x v ≠ 0 := by
  intro hp
  apply hn
  intro y hy
  have hyrange : y ∈ Set.range (fun t : ℝ => x+t • v) := hrange.symm ▸ hy
  obtain ⟨t, rfl⟩ := hyrange
  have h := linePolynomial_eval d f x v t
  rw [hp] at h
  simpa using h.symm

end DistinctDistances.TrackC
