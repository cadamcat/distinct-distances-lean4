import DistinctDistances.TrackA.SeparatorMatrixSupport
import DistinctDistances.TrackA.SeparatorParametersSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPolynomial

theorem origin_isolated_separator {F : Type*} [Field F] [IsAlgClosed F]
    (c L : ℕ) (E : Set (FieldPoly c F)) (hE : ∀ f ∈ E, f.totalDegree ≤ L)
    (hmin : pointIdealOver (0 : FieldPoint c F) ∈ (Ideal.span E).minimalPrimes)
    (hsocle : ∀ (f : Fin c → OriginLocalRing c F)
      (Q : Matrix (Fin c) (Fin c) (OriginLocalRing c F)),
      Module.length (OriginLocalRing c F)
        (OriginLocalRing c F ⧸ Ideal.span (Set.range f)) < ⊤ →
      (∀ i, f i = ∑ j, Q i j *
        algebraMap (FieldPoly c F) (OriginLocalRing c F) (X j)) →
      Q.det ∉ Ideal.span (Set.range f)) :
    ∃ s : FieldPoly c F, s.totalDegree ≤ c*(L-1) ∧ eval 0 s = 1 ∧
      ∀ y ∈ zeroLocus F (Ideal.span E), y ≠ 0 → eval y s = 0 := by
  let R := OriginLocalRing c F
  letI : CommRing R :=
    { __ := (inferInstance : Ring R)
      mul_comm := fun a b => mul_comm a b }
  let t : Fin c → R := fun j => algebraMap (FieldPoly c F) R (X j)
  obtain ⟨f, hf, hfinite⟩ := origin_bounded_parameters c L E hE hmin
  let u : Fin c → R := fun i => algebraMap (FieldPoly c F) R (f i)
  have heval : aeval t = IsScalarTower.toAlgHom F (FieldPoly c F) R := by
    ext i
    simp [t]
  have hfi0 (i : Fin c) : eval (0 : FieldPoint c F) (f i) = 0 := by
    have hh := hmin.le (hf i).2
    have hzero := (MvPolynomial.mem_vanishingIdeal_singleton_iff 0 (f i)).mp hh
    simpa only [MvPolynomial.aeval_eq_eval] using hzero
  choose Q hdegree hdiff using fun i => divided_difference_exists (f i) t
  have hQdegree : ∀ i j, (Q i j).totalDegree ≤ L-1 := by
    intro i j
    rcases hdegree i j with hh | hh
    · simp [hh]
    · have hh' := (hf i).1
      omega
  have hdiv (i : Fin c) : MvPolynomial.map (algebraMap F R) (f i)-C (u i) =
      ∑ j, Q i j*(X j-C (t j)) := by
    simpa only [heval, IsScalarTower.toAlgHom_apply, u] using hdiff i
  let Q₀ : Matrix (Fin c) (Fin c) R := fun i j => eval (0 : Fin c → R) (Q i j)
  have hfmap (i : Fin c) : eval (0 : Fin c → R) (MvPolynomial.map (algebraMap F R) (f i)) = 0 := by
    have hh := MvPolynomial.map_eval (algebraMap F R) (0 : FieldPoint c F) (f i)
    rw [hfi0 i, map_zero] at hh
    have hfunc : (algebraMap F R) ∘ (0 : FieldPoint c F) = (0 : Fin c → R) := by
      funext i
      simp
    rw [hfunc] at hh
    exact hh.symm
  have hQ₀ (i : Fin c) : u i = ∑ j, Q₀ i j * t j := by
    have hh := congrArg (eval (0 : Fin c → R)) (hdiv i)
    simp only [map_sub, map_sum, map_mul, eval_C, eval_X, Pi.zero_apply,
      hfmap, zero_sub] at hh
    have hh' : -u i = -(∑ j, Q₀ i j * t j) := by
      calc
        -u i = ∑ j, eval (0 : Fin c → R) (Q i j) * -t j := hh
        _ = -(∑ j, Q₀ i j * t j) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          exact mul_neg _ _
    exact neg_injective hh'
  have hdet := hsocle u Q₀ hfinite hQ₀
  have hunit : ∀ y : FieldPoint c F, y ≠ 0 → ∃ j, IsUnit (algebraMap F R (y j)-t j) := by
    intro y hy
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra hh
      apply hy
      funext j
      exact not_not.mp (fun hj => hh ⟨j, hj⟩)
    have hraw : (C (y j)-X j : FieldPoly c F) ∉ pointIdealOver (0 : FieldPoint c F) := by
      rw [pointIdealOver, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simpa using hj
    have hmap : algebraMap (FieldPoly c F) R (C (y j)-X j) = algebraMap F R (y j)-t j := by
      rw [map_sub]
      rfl
    refine ⟨j, ?_⟩
    rw [← hmap]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff R
      (pointIdealOver (0 : FieldPoint c F)) _).mpr hraw
  obtain ⟨s, hsdegree, hsvalue, hszero⟩ := separator_from_divided_matrix
    c (L-1) f u t Q hQdegree hdiv hdet hunit
  refine ⟨s, hsdegree, hsvalue, ?_⟩
  intro y hy hne
  apply hszero y _ hne
  intro i
  exact (MvPolynomial.aeval_eq_eval y ▸ hy (f i) (hf i).2)

end
end DistinctDistances.TrackA
