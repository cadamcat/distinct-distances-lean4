import DistinctDistances.TrackA.SeparatorAlgebraSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPolynomial

/-- A determinant in a local parameter quotient separates the origin
from every other common zero. Nilpotents in the quotient are retained. -/
theorem separator_from_divided_matrix {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    (c B : ℕ) (f : Fin c → FieldPoly c F) (u t : Fin c → R)
    (Q : Matrix (Fin c) (Fin c) (MvPolynomial (Fin c) R))
    (hdegree : ∀ i j, (Q i j).totalDegree ≤ B)
    (hdiv : ∀ i, MvPolynomial.map (algebraMap F R) (f i) - C (u i) =
      ∑ j, Q i j * (X j-C (t j)))
    (hsocle : (Q.map (eval (0 : Fin c → R))).det ∉ Ideal.span (Set.range u))
    (hunit : ∀ y : FieldPoint c F, y ≠ 0 → ∃ j, IsUnit (algebraMap F R (y j)-t j)) :
    ∃ s : FieldPoly c F, s.totalDegree ≤ c*B ∧ eval 0 s = 1 ∧
      ∀ y : FieldPoint c F, (∀ i, eval y (f i) = 0) → y ≠ 0 → eval y s = 0 := by
  let J := Ideal.span (Set.range u)
  let A := R ⧸ J
  let δ : MvPolynomial (Fin c) A := MvPolynomial.map (Ideal.Quotient.mk J) Q.det
  have hmapdeg : δ.totalDegree ≤ Q.det.totalDegree :=
    Finset.sup_mono (support_map_subset ..)
  have hδdeg : δ.totalDegree ≤ c*B :=
    hmapdeg.trans (polynomial_matrix_det_degree_le Q B hdegree)
  have hδeval (y : FieldPoint c F) :
      eval (fun i => algebraMap F A (y i)) δ =
        (Ideal.Quotient.mk J) (eval (fun i => algebraMap F R (y i)) Q.det) := by
    have hh := MvPolynomial.map_eval (Ideal.Quotient.mk J)
      (fun i => algebraMap F R (y i)) Q.det
    exact hh.symm
  have hzero : eval (fun i => algebraMap F A ((0 : FieldPoint c F) i)) δ ≠ 0 := by
    rw [hδeval]
    simp only [Pi.zero_apply, map_zero]
    rw [RingHom.map_det]
    exact fun hh => hsocle (Ideal.Quotient.eq_zero_iff_mem.mp hh)
  have hvanish (y : FieldPoint c F) (hy : ∀ i, eval y (f i) = 0) (hne : y ≠ 0) :
      eval (fun i => algebraMap F A (y i)) δ = 0 := by
    let ey : MvPolynomial (Fin c) R →+* R := eval (fun i => algebraMap F R (y i))
    let M : Matrix (Fin c) (Fin c) A := (Q.map ey).map (Ideal.Quotient.mk J)
    let v : Fin c → A := fun j => (Ideal.Quotient.mk J) (algebraMap F R (y j)-t j)
    have hu (i : Fin c) : (Ideal.Quotient.mk J) (u i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
    have hf (i : Fin c) : ey (MvPolynomial.map (algebraMap F R) (f i)) = 0 := by
      change eval ((algebraMap F R) ∘ y) (MvPolynomial.map (algebraMap F R) (f i)) = 0
      rw [← MvPolynomial.map_eval, hy i, map_zero]
    have hM : Matrix.mulVec M v = 0 := by
      funext i
      have hh := congrArg (fun p => (Ideal.Quotient.mk J) (ey p)) (hdiv i)
      simp only [map_sub, map_sum, map_mul] at hh
      simp only [hf, ey, eval_X, eval_C, hu, map_zero, sub_self] at hh
      change (∑ j, (Ideal.Quotient.mk J) (ey (Q i j)) *
        (Ideal.Quotient.mk J) (algebraMap F R (y j)-t j)) = 0
      simpa only [map_sub, ey] using hh.symm
    obtain ⟨j, hj⟩ := hunit y hne
    have hv : v j ∈ nonZeroDivisors A :=
      (hj.map (Ideal.Quotient.mk J)).mem_nonZeroDivisors
    have hdet := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hM hv
    rw [hδeval, RingHom.map_det ey Q, RingHom.map_det]
    exact hdet
  obtain ⟨s, hsdeg, hsval, hszero⟩ := scalar_separator_from_algebra δ (c*B) hδdeg
    0 hzero {y : FieldPoint c F | ∀ i, eval y (f i) = 0}
      (fun y hy hne => hvanish y hy hne)
  exact ⟨s, hsdeg, hsval, fun y hy hne => hszero y hy hne⟩

end
end DistinctDistances.TrackA
