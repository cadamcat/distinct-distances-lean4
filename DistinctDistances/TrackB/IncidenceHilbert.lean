import DistinctDistances.TrackB.SegreCoefficients
import DistinctDistances.TrackB.IncidenceMoments
import DistinctDistances.TrackB.IncidenceBinomial
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Monad

/-!
The finite polynomial identity in DESIGN.md's alternative for conc:deg-projective-bundle.
This is B13.4, the algebraic coefficient-extraction step. To use it geometrically one must
prove B13.1–B13.3: the regular incidence embedding, its Koszul resolution, and equality
of the actual multigraded Hilbert polynomial with this transform. No geometry or degree
model is defined here, and that equality is not a hypothesis hidden in a variety structure.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false

open scoped BigOperators

abbrev BaseHilbertPolynomial := MvPolynomial (Fin 2) ℚ
abbrev IncidenceHilbertPolynomial := MvPolynomial (Fin 3) ℚ

/-- Substitute signed line-bundle twists into the two base variables, then add the
point-coordinate variable. The variables are `(a, ell, xi)`, in that order. -/
noncomputable def shiftedBaseHilbert (H : BaseHilbertPolynomial) (da dell : ℤ) :
    IncidenceHilbertPolynomial :=
  MvPolynomial.bind₁ (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X (0 : Fin 3) + MvPolynomial.C (da : ℚ)
    else MvPolynomial.X (1 : Fin 3) + MvPolynomial.C (dell : ℚ)) H

/-- The rational polynomial `choose(v-m+n,n)`. All shifts are rational subtraction,
not natural subtraction inside a cast. -/
noncomputable def shiftedProjectiveHilbert (n m : ℕ) : IncidenceHilbertPolynomial :=
  MvPolynomial.C ((n.factorial : ℚ)⁻¹) *
    ∏ k ∈ Finset.range n,
      (MvPolynomial.X (2 : Fin 3) + MvPolynomial.C ((n : ℚ) - (m : ℚ) - (k : ℚ)))

/-- Coefficient of `z^m` in the exterior-power expression
`(1+z)(1+A⁻¹z)^e / ((1+A⁻²z)(1+Bz))`, applied to H, with b=ell-a.
The four indices are delta, k, l, beta from DESIGN.md. -/
noncomputable def exteriorHilbertTerm (e m : ℕ) (H : BaseHilbertPolynomial) :
    IncidenceHilbertPolynomial :=
  ∑ delta ∈ Finset.range 2,
    ∑ k ∈ Finset.range (e + 1),
      ∑ l ∈ Finset.range (m + 1),
        ∑ beta ∈ Finset.range (m + 1),
          if delta + k + l + beta = m then
            MvPolynomial.C ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)) *
              shiftedBaseHilbert H
                (-((k : ℤ) + 2 * (l : ℤ) + (beta : ℤ))) (beta : ℤ)
          else 0

/-- The polynomial computed by the explicit regular Koszul resolution. The actual
incidence's Hilbert polynomial must be proved equal to this expression (B13.3). -/
noncomputable def koszulIncidenceHilbert (e : ℕ) (H : BaseHilbertPolynomial) :
    IncidenceHilbertPolynomial :=
  ∑ m ∈ Finset.range e,
    MvPolynomial.C ((-1 : ℚ) ^ m) *
      exteriorHilbertTerm e m H * shiftedProjectiveHilbert (e.choose 2) m

/-- A mixed top-degree coefficient of the base polynomial, with its factorial normalization. -/
noncomputable def mixedHilbertCoefficient (H : BaseHilbertPolynomial) (p q : ℕ) : ℚ :=
  (p.factorial : ℚ) * (q.factorial : ℚ) *
    H.coeff (Finsupp.single (0 : Fin 2) p + Finsupp.single (1 : Fin 2) q)

/-- The point/parameter mixed coefficient of the incidence polynomial. The missing
variable a has exponent zero. This is an ordinary rational coefficient, not a degree definition. -/
noncomputable def pointParameterCoefficient
    (H : IncidenceHilbertPolynomial) (pointExp parameterExp : ℕ) : ℚ :=
  (pointExp.factorial : ℚ) * (parameterExp.factorial : ℚ) *
    H.coeff
      (Finsupp.single (1 : Fin 3) parameterExp + Finsupp.single (2 : Fin 3) pointExp)

namespace IncidenceBinomial

theorem coeff_toMvPolynomial {σ : Type*} (P : Polynomial ℚ) (i : σ) (K : ℕ) :
    (P.toMvPolynomial i).coeff (Finsupp.single i K) = P.coeff K := by
  classical
  rw [Polynomial.toMvPolynomial_eq_rename_comp]
  change (MvPolynomial.rename (fun _ : Unit => i)
    ((MvPolynomial.uniqueAlgEquiv ℚ Unit).symm P)).coeff _ = _
  have h := MvPolynomial.coeff_rename_mapDomain (fun _ : Unit => i)
    (fun _ _ _ => rfl) ((MvPolynomial.uniqueAlgEquiv ℚ Unit).symm P)
    (Finsupp.single () K)
  simpa only [Finsupp.mapDomain_single, MvPolynomial.coeff_uniqueAlgEquiv_symm,
    Finsupp.single_eq_same] using h

theorem pointBinomial_toMvPolynomial (n m : ℕ) :
    (pointBinomial n (m : ℚ)).toMvPolynomial (2 : Fin 3) = shiftedProjectiveHilbert n m := by
  unfold pointBinomial shiftedProjectiveHilbert
  simp only [map_mul, map_prod, map_add, Polynomial.toMvPolynomial_C,
    Polynomial.toMvPolynomial_X]

theorem shiftedProjectiveHilbert_pascal (n m : ℕ) :
    shiftedProjectiveHilbert (n + 1) m - shiftedProjectiveHilbert (n + 1) (m + 1) =
      shiftedProjectiveHilbert n m := by
  rw [← pointBinomial_toMvPolynomial, ← pointBinomial_toMvPolynomial,
    ← pointBinomial_toMvPolynomial, ← map_sub]
  congr 1
  simpa only [Nat.cast_add, Nat.cast_one] using pointBinomial_pascal n (m : ℚ)

theorem shiftedProjectiveHilbert_coefficient (n K m : ℕ) :
    (shiftedProjectiveHilbert n m).coeff (Finsupp.single (2 : Fin 3) K) =
      (pointCoefficientPolynomial n K).eval (m : ℚ) := by
  rw [← pointBinomial_toMvPolynomial, coeff_toMvPolynomial,
    pointCoefficientPolynomial_eval]

/-- The exact shift-polynomial degree and top coefficient used by B13.4. -/
theorem incidence_point_coefficient_polynomial (e h : ℕ) (he : 3 ≤ e)
    (hh : h + 2 ≤ e) :
    ∃ F : Polynomial ℚ, F.natDegree ≤ e - 2 - h ∧
      F.coeff (e - 2 - h) = (-1 : ℚ) ^ (e - 2 - h) /
        ((((e - 1).choose 2 + h).factorial : ℚ) * ((e - 2 - h).factorial : ℚ)) ∧
      ∀ m : ℕ, (shiftedProjectiveHilbert (e.choose 2 - 1) m).coeff
        (Finsupp.single (2 : Fin 3) ((e - 1).choose 2 + h)) = F.eval (m : ℚ) := by
  have hc : e.choose 2 = (e - 1).choose 2 + (e - 1) := by
    conv_lhs => rw [show e = (e - 1) + 1 by omega]
    rw [Nat.choose_succ_succ']
    simp [Nat.choose_one_right, Nat.add_comm]
  have hK : (e - 1).choose 2 + h ≤ e.choose 2 - 1 := by omega
  have hd : e.choose 2 - 1 - ((e - 1).choose 2 + h) = e - 2 - h := by omega
  refine ⟨pointCoefficientPolynomial (e.choose 2 - 1) ((e - 1).choose 2 + h), ?_, ?_, ?_⟩
  · rw [pointCoefficientPolynomial_degree, hd]
  · simpa only [hd] using pointCoefficientPolynomial_top (e.choose 2 - 1)
      ((e - 1).choose 2 + h) hK
  · exact fun m => shiftedProjectiveHilbert_coefficient _ _ _

#print axioms shiftedProjectiveHilbert_pascal
#print axioms shiftedProjectiveHilbert_coefficient
#print axioms incidence_point_coefficient_polynomial


theorem finSuccEquiv_toMvPolynomial (n : ℕ) (i : Fin n) (P : Polynomial ℚ) :
    MvPolynomial.finSuccEquiv ℚ n (P.toMvPolynomial i.succ) =
      Polynomial.C (P.toMvPolynomial i) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp only [map_add, hp, hq]
  | monomial k c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    have hc : MvPolynomial.finSuccEquiv ℚ n (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) := (MvPolynomial.finSuccEquiv ℚ n).commutes c
    simp only [map_mul, map_pow, Polynomial.toMvPolynomial_C,
      Polynomial.toMvPolynomial_X, MvPolynomial.finSuccEquiv_X_succ, hc]

/-- Extract exactly a^0 ell^j xi^K in the frozen order of variables. -/
noncomputable def pointCoefficient (P : IncidenceHilbertPolynomial) (j K : ℕ) : ℚ :=
  ((((MvPolynomial.finSuccEquiv ℚ 1)
    (((MvPolynomial.finSuccEquiv ℚ 2) P).coeff 0)).coeff j).coeff
      (Finsupp.single (0 : Fin 1) K))

theorem pointCoefficient_eq (P : IncidenceHilbertPolynomial) (j K : ℕ) :
    pointCoefficient P j K = P.coeff
      (Finsupp.single (1 : Fin 3) j + Finsupp.single (2 : Fin 3) K) := by
  unfold pointCoefficient
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.finSuccEquiv_coeff_coeff]
  congr 1
  ext i
  cases i using Fin.cases with
  | zero => norm_num [Finsupp.cons_zero, Finsupp.single_apply]
  | succ i =>
    simp only [Finsupp.cons_succ, Finsupp.add_apply]
    cases i using Fin.cases with
    | zero =>
      simp only [Finsupp.cons_zero]
      norm_num [Finsupp.single_apply, Fin.ext_iff]
    | succ i =>
      simp only [Finsupp.cons_succ]
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      norm_num [Finsupp.single_apply, Fin.ext_iff]

theorem shifted_monomial_point_coefficient (p q n m j K : ℕ) (da dell : ℤ) :
    (shiftedBaseHilbert
        (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q)
        da dell * shiftedProjectiveHilbert n m).coeff
      (Finsupp.single (1 : Fin 3) j + Finsupp.single (2 : Fin 3) K) =
      (da : ℚ) ^ p * (q.choose j : ℚ) * (dell : ℚ) ^ (q - j) *
        (pointBinomial n (m : ℚ)).coeff K := by
  rw [← pointCoefficient_eq, ← pointBinomial_toMvPolynomial]
  unfold pointCoefficient shiftedBaseHilbert
  simp only [map_mul, map_pow, MvPolynomial.bind₁_X_right, ite_true,
    if_neg (by decide : (1 : Fin 2) ≠ 0)]
  have h0 : MvPolynomial.finSuccEquiv ℚ 2 (MvPolynomial.X (0 : Fin 3) + MvPolynomial.C (da : ℚ)) =
      Polynomial.X + Polynomial.C (MvPolynomial.C (da : ℚ)) := by
    simp only [map_add, MvPolynomial.finSuccEquiv_X_zero]
    congr 1
    exact (MvPolynomial.finSuccEquiv ℚ 2).commutes (da : ℚ)
  have h1 : MvPolynomial.finSuccEquiv ℚ 2 (MvPolynomial.X (1 : Fin 3) + MvPolynomial.C (dell : ℚ)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 2) + MvPolynomial.C (dell : ℚ)) := by
    simp only [map_add]
    change MvPolynomial.finSuccEquiv ℚ 2 (MvPolynomial.X (0 : Fin 2).succ) + _ = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    congr 1
    exact (MvPolynomial.finSuccEquiv ℚ 2).commutes (dell : ℚ)
  have hp2 : MvPolynomial.finSuccEquiv ℚ 2
      ((pointBinomial n (m : ℚ)).toMvPolynomial (2 : Fin 3)) =
      Polynomial.C ((pointBinomial n (m : ℚ)).toMvPolynomial (1 : Fin 2)) := by
    simpa only [show (1 : Fin 2).succ = (2 : Fin 3) by decide] using
      finSuccEquiv_toMvPolynomial 2 (1 : Fin 2) (pointBinomial n (m : ℚ))
  rw [h0, h1, hp2]
  rw [← map_pow (Polynomial.C : MvPolynomial (Fin 2) ℚ →+* _), mul_assoc,
    ← map_mul (Polynomial.C : MvPolynomial (Fin 2) ℚ →+* _)]
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_add_C_pow]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
    map_mul, map_pow, map_one, mul_one]
  have h2 : MvPolynomial.finSuccEquiv ℚ 1 (MvPolynomial.C (da : ℚ)) =
      Polynomial.C (MvPolynomial.C (da : ℚ)) := by
    exact (MvPolynomial.finSuccEquiv ℚ 1).commutes (da : ℚ)
  have h3 : MvPolynomial.finSuccEquiv ℚ 1 (MvPolynomial.X (0 : Fin 2) + MvPolynomial.C (dell : ℚ)) =
      Polynomial.X + Polynomial.C (MvPolynomial.C (dell : ℚ)) := by
    simp only [map_add, MvPolynomial.finSuccEquiv_X_zero]
    congr 1
    exact (MvPolynomial.finSuccEquiv ℚ 1).commutes (dell : ℚ)
  have hp1 : MvPolynomial.finSuccEquiv ℚ 1
      ((pointBinomial n (m : ℚ)).toMvPolynomial (1 : Fin 2)) =
      Polynomial.C ((pointBinomial n (m : ℚ)).toMvPolynomial (0 : Fin 1)) := by
    simpa only [show (0 : Fin 1).succ = (1 : Fin 2) by decide] using
      finSuccEquiv_toMvPolynomial 1 (0 : Fin 1) (pointBinomial n (m : ℚ))
  rw [h2, h3, hp1]
  simp only [← map_pow, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
    Polynomial.coeff_X_add_C_pow, MvPolynomial.coeff_C_mul,
    MvPolynomial.C_1, map_one, mul_one, one_mul]
  rw [mul_assoc, MvPolynomial.coeff_C_mul]
  have hcast : (q.choose j : MvPolynomial (Fin 1) ℚ) = MvPolynomial.C (q.choose j : ℚ) :=
    (map_natCast (MvPolynomial.C : ℚ →+* MvPolynomial (Fin 1) ℚ) (q.choose j)).symm
  rw [hcast, MvPolynomial.coeff_C_mul, coeff_toMvPolynomial]
  ring

#print axioms shifted_monomial_point_coefficient

open IncidenceMoments

/-- Expand coefficients of the actual frozen Koszul delta/k/l/beta sum. -/
theorem koszul_monomial_coefficient_expansion (e p q j K : ℕ) :
    (koszulIncidenceHilbert e
        (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q)).coeff
      (Finsupp.single (1 : Fin 3) j + Finsupp.single (2 : Fin 3) K) =
      (q.choose j : ℚ) * ∑ m ∈ Finset.range e,
        (∑ delta ∈ Finset.range 2, signedExteriorSlice e m delta p (q - j)) *
          (pointBinomial (e.choose 2) (m : ℚ)).coeff K := by
  unfold koszulIncidenceHilbert exteriorHilbertTerm signedExteriorSlice
  simp only [Finset.mul_sum, Finset.sum_mul, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro delta _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro beta _
  split_ifs with hc
  · rw [mul_assoc, MvPolynomial.coeff_C_mul, mul_assoc, MvPolynomial.coeff_C_mul,
      shifted_monomial_point_coefficient]
    simp only [Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
    have hsign : (-1 : ℚ) ^ m * (-1 : ℚ) ^ (l + beta) = (-1 : ℚ) ^ (delta + k) := by
      rw [← pow_add, show m + (l + beta) = (delta + k) + 2 * (l + beta) by omega,
        pow_add, pow_mul]
      norm_num
    calc
      _ = (q.choose j : ℚ) * ((-1 : ℚ) ^ m * (-1 : ℚ) ^ (l + beta)) *
          (e.choose k : ℚ) * (-((k : ℚ) + 2 * (l : ℚ) + (beta : ℚ))) ^ p *
            (beta : ℚ) ^ (q - j) * (pointBinomial (e.choose 2) (m : ℚ)).coeff K := by ring
      _ = _ := by rw [hsign]; ring
  · simp

theorem koszul_monomial_coefficient_slices (e p q j K : ℕ) :
    (koszulIncidenceHilbert e
        (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q)).coeff
      (Finsupp.single (1 : Fin 3) j + Finsupp.single (2 : Fin 3) K) =
      (q.choose j : ℚ) * ∑ m ∈ Finset.range e,
        (shiftedSliceMoment e p (q - j) m -
          if m = 0 then 0 else shiftedSliceMoment e p (q - j) (m - 1)) *
            (pointBinomial (e.choose 2) (m : ℚ)).coeff K := by
  rw [koszul_monomial_coefficient_expansion]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m ≤ e := (Finset.mem_range.mp hm).le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [signedExteriorSlice_pair e m p (q - j) hm']

#print axioms koszul_monomial_coefficient_expansion
#print axioms koszul_monomial_coefficient_slices


/-- Discrete summation by parts applies Pascal to the actual point-polynomial factor. -/
theorem koszul_monomial_coefficient_reduction (e p q j K : ℕ) (he : 3 ≤ e)
    (hbound : p + (q - j) + 2 ≤ e) :
    (koszulIncidenceHilbert e
        (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q)).coeff
      (Finsupp.single (1 : Fin 3) j + Finsupp.single (2 : Fin 3) K) =
      (q.choose j : ℚ) * shiftedSlicePolynomial e p (q - j)
        (pointCoefficientPolynomial (e.choose 2 - 1) K) := by
  have hc : e.choose 2 = (e - 1).choose 2 + (e - 1) := by
    conv_lhs => rw [show e = (e - 1) + 1 by omega]
    rw [Nat.choose_succ_succ']
    simp [Nat.choose_one_right, Nat.add_comm]
  have hn : e.choose 2 - 1 + 1 = e.choose 2 := by omega
  have hpas : ∀ m : ℕ,
      (pointBinomial (e.choose 2) (m : ℚ)).coeff K -
        (pointBinomial (e.choose 2) ((m + 1 : ℕ) : ℚ)).coeff K =
          (pointCoefficientPolynomial (e.choose 2 - 1) K).eval (m : ℚ) := by
    intro m
    rw [pointCoefficientPolynomial_eval]
    have hh := congrArg (fun P : Polynomial ℚ => P.coeff K)
      (pointBinomial_pascal (e.choose 2 - 1) (m : ℚ))
    simpa only [Polynomial.coeff_sub, hn, Nat.cast_add, Nat.cast_one] using hh
  rw [koszul_monomial_coefficient_slices, slice_summation_parts e (by omega),
    shiftedSliceMoment_boundary_zero e p (q - j) (e - 1) hbound le_rfl,
    zero_mul, add_zero]
  congr 1
  unfold shiftedSlicePolynomial
  apply Finset.sum_congr rfl
  intro m _
  rw [hpas]

#print axioms koszul_monomial_coefficient_reduction


noncomputable def shiftedBaseLinearMap (da dell : ℤ) : BaseHilbertPolynomial →ₗ[ℚ] IncidenceHilbertPolynomial where
  toFun H := shiftedBaseHilbert H da dell
  map_add' H G := by unfold shiftedBaseHilbert; exact map_add _ _ _
  map_smul' c H := by unfold shiftedBaseHilbert; exact map_smul _ _ _

noncomputable def exteriorHilbertLinearMap (e m : ℕ) : BaseHilbertPolynomial →ₗ[ℚ] IncidenceHilbertPolynomial :=
  ∑ delta ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
    ∑ l ∈ Finset.range (m + 1), ∑ beta ∈ Finset.range (m + 1),
      if delta + k + l + beta = m then
        (LinearMap.mulLeft ℚ (MvPolynomial.C ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)))).comp
          (shiftedBaseLinearMap (-((k : ℤ) + 2 * (l : ℤ) + (beta : ℤ))) (beta : ℤ))
      else 0

theorem exteriorHilbertLinearMap_apply (e m : ℕ) (H : BaseHilbertPolynomial) :
    exteriorHilbertLinearMap e m H = exteriorHilbertTerm e m H := by
  unfold exteriorHilbertLinearMap exteriorHilbertTerm
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro delta _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro beta _
  split_ifs <;> rfl

noncomputable def koszulHilbertLinearMap (e : ℕ) : BaseHilbertPolynomial →ₗ[ℚ] IncidenceHilbertPolynomial :=
  ∑ m ∈ Finset.range e,
    (LinearMap.mulRight ℚ (shiftedProjectiveHilbert (e.choose 2) m)).comp
      ((LinearMap.mulLeft ℚ (MvPolynomial.C ((-1 : ℚ) ^ m))).comp (exteriorHilbertLinearMap e m))

theorem koszulHilbertLinearMap_apply (e : ℕ) (H : BaseHilbertPolynomial) :
    koszulHilbertLinearMap e H = koszulIncidenceHilbert e H := by
  unfold koszulHilbertLinearMap koszulIncidenceHilbert
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, exteriorHilbertLinearMap_apply]
  rfl

noncomputable def pointParameterLinearMap (K j : ℕ) : IncidenceHilbertPolynomial →ₗ[ℚ] ℚ :=
  ((K.factorial : ℚ) * (j.factorial : ℚ)) •
    MvPolynomial.lcoeff ℚ (Finsupp.single (1 : Fin 3) j + Finsupp.single (2 : Fin 3) K)

theorem pointParameterLinearMap_apply (K j : ℕ) (H : IncidenceHilbertPolynomial) :
    pointParameterLinearMap K j H = pointParameterCoefficient H K j := rfl

noncomputable def mixedHilbertLinearMap (p q : ℕ) : BaseHilbertPolynomial →ₗ[ℚ] ℚ :=
  ((p.factorial : ℚ) * (q.factorial : ℚ)) •
    MvPolynomial.lcoeff ℚ (Finsupp.single (0 : Fin 2) p + Finsupp.single (1 : Fin 2) q)

theorem mixedHilbertLinearMap_apply (p q : ℕ) (H : BaseHilbertPolynomial) :
    mixedHilbertLinearMap p q H = mixedHilbertCoefficient H p q := rfl

noncomputable def segreCombinationLinearMap (e h j : ℕ) : BaseHilbertPolynomial →ₗ[ℚ] ℚ :=
  ∑ i ∈ Finset.range (h + 1),
    (segreCoeff (e - 1 - i) (h - i) : ℚ) • mixedHilbertLinearMap (h - i) (i + j)

theorem segreCombinationLinearMap_apply (e h j : ℕ) (H : BaseHilbertPolynomial) :
    segreCombinationLinearMap e h j H = ∑ i ∈ Finset.range (h + 1),
      (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedHilbertCoefficient H (h - i) (i + j) := by
  simp only [segreCombinationLinearMap, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, mixedHilbertLinearMap_apply]

#print axioms koszulHilbertLinearMap_apply
#print axioms segreCombinationLinearMap_apply

theorem base_exponents_eq (p q r s : ℕ) :
    (Finsupp.single (0 : Fin 2) p + Finsupp.single (1 : Fin 2) q =
      Finsupp.single (0 : Fin 2) r + Finsupp.single (1 : Fin 2) s) ↔ p = r ∧ q = s := by
  constructor
  · intro h
    have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
    simpa using And.intro h0 h1
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mixed_monomial_coefficient (p q r s : ℕ) :
    mixedHilbertCoefficient
      (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q) r s =
      if p = r ∧ q = s then (r.factorial : ℚ) * (s.factorial : ℚ) else 0 := by
  simp [mixedHilbertCoefficient, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.coeff_monomial, base_exponents_eq]

/-- B13.4 for a base monomial, including cancellation below its top total degree. -/
theorem koszul_monomial_point_coefficient (e h j p q : ℕ) (he : 3 ≤ e)
    (hh : h + 2 ≤ e) (hdegree : p + q ≤ h + j) :
    pointParameterCoefficient (koszulIncidenceHilbert e
        (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q))
      ((e - 1).choose 2 + h) j =
      ∑ i ∈ Finset.range (h + 1), (segreCoeff (e - 1 - i) (h - i) : ℚ) *
        mixedHilbertCoefficient
          (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q)
          (h - i) (i + j) := by
  by_cases hq : q < j
  · have hlhs : pointParameterCoefficient (koszulIncidenceHilbert e
        (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q))
          ((e - 1).choose 2 + h) j = 0 := by
      unfold pointParameterCoefficient
      rw [koszul_monomial_coefficient_slices, Nat.choose_eq_zero_of_lt hq,
        Nat.cast_zero, zero_mul, mul_zero]
    rw [hlhs]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [mixed_monomial_coefficient, if_neg (by omega : ¬ (p = h - i ∧ q = i + j)), mul_zero]
  · have hq' : j ≤ q := by omega
    let t := q - j
    let d := e - 2 - h
    let K := (e - 1).choose 2 + h
    let F := pointCoefficientPolynomial (e.choose 2 - 1) K
    have hqt : t + j = q := by dsimp [t]; omega
    have hpt : p + t ≤ h := by dsimp [t]; omega
    have hbound : p + t + 2 ≤ e := by omega
    have hc : e.choose 2 = (e - 1).choose 2 + (e - 1) := by
      conv_lhs => rw [show e = (e - 1) + 1 by omega]
      rw [Nat.choose_succ_succ']
      simp [Nat.choose_one_right, Nat.add_comm]
    have hK : K ≤ e.choose 2 - 1 := by dsimp [K]; omega
    have hd : e.choose 2 - 1 - K = d := by dsimp [K, d]; omega
    have hF : F.natDegree ≤ d := by
      dsimp [F]
      rw [pointCoefficientPolynomial_degree, hd]
    have hFtop : F.coeff d = (-1 : ℚ) ^ d / ((K.factorial : ℚ) * (d.factorial : ℚ)) := by
      simpa only [hd] using pointCoefficientPolynomial_top (e.choose 2 - 1) K hK
    have hreduce : pointParameterCoefficient (koszulIncidenceHilbert e
        (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q)) K j =
        (K.factorial : ℚ) * (j.factorial : ℚ) * (q.choose j : ℚ) *
          shiftedSlicePolynomial e p t F := by
      unfold pointParameterCoefficient
      rw [koszul_monomial_coefficient_reduction e p q j K he hbound]
      ring
    by_cases htop : p + t = h
    · have hsum : p + t + d + 2 = e := by dsimp [d]; omega
      have hindex : d + p + 1 = e - 1 - t := by dsimp [d]; omega
      have hlhs : pointParameterCoefficient (koszulIncidenceHilbert e
          (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q)) K j =
          (p.factorial : ℚ) * (q.factorial : ℚ) * (segreCoeff (e - 1 - t) p : ℚ) := by
        rw [hreduce]
        simpa only [hqt, hindex] using normalized_shiftedSlicePolynomial_top
          e p t d K j F hsum hF hFtop
      change pointParameterCoefficient _ K j = _
      rw [hlhs, Finset.sum_eq_single t]
      · rw [mixed_monomial_coefficient, if_pos (by omega : p = h - t ∧ q = t + j)]
        rw [show h - t = p by omega, hqt]
        ring
      · intro i _ hit
        rw [mixed_monomial_coefficient,
          if_neg (by omega : ¬ (p = h - i ∧ q = i + j)), mul_zero]
      · intro ht
        exfalso
        apply ht
        exact Finset.mem_range.mpr (by omega)
    · have hsum : p + t + d + 2 < e := by dsimp [d]; omega
      have hlhs : pointParameterCoefficient (koszulIncidenceHilbert e
          (MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q)) K j = 0 := by
        rw [hreduce, shiftedSlicePolynomial_zero e p t d F hsum hF, mul_zero]
      change pointParameterCoefficient _ K j = _
      rw [hlhs]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i ≤ h := by have := Finset.mem_range.mp hi; omega
      rw [mixed_monomial_coefficient,
        if_neg (by omega : ¬ (p = h - i ∧ q = i + j)), mul_zero]

#print axioms koszul_monomial_point_coefficient


theorem monomial_as_base (s : Fin 2 →₀ ℕ) (c : ℚ) :
    MvPolynomial.monomial s c = c •
      (MvPolynomial.X (0 : Fin 2) ^ (s 0) * MvPolynomial.X (1 : Fin 2) ^ (s 1)) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]

/-- B13.4 by linearity over the actual support; only the support's total degree is used. -/
theorem koszul_coefficient_of_degree (e h j : ℕ) (he : 3 ≤ e) (hh : h + 2 ≤ e)
    (H : BaseHilbertPolynomial) (hH : H.totalDegree ≤ h + j) :
    pointParameterCoefficient (koszulIncidenceHilbert e H) ((e - 1).choose 2 + h) j =
      ∑ i ∈ Finset.range (h + 1),
        (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedHilbertCoefficient H (h - i) (i + j) := by
  let L : BaseHilbertPolynomial →ₗ[ℚ] ℚ :=
    (pointParameterLinearMap ((e - 1).choose 2 + h) j).comp (koszulHilbertLinearMap e)
  let R : BaseHilbertPolynomial →ₗ[ℚ] ℚ := segreCombinationLinearMap e h j
  have hmono : ∀ s ∈ H.support, L (MvPolynomial.monomial s (H.coeff s)) =
      R (MvPolynomial.monomial s (H.coeff s)) := by
    intro s hs
    have hsdegree := (MvPolynomial.le_totalDegree hs).trans hH
    have htotal : s.sum (fun _ n => n) = s 0 + s 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    have hbound : s 0 + s 1 ≤ h + j := by rw [htotal] at hsdegree; exact hsdegree
    simp only [monomial_as_base, map_smul]
    apply congrArg (fun x : ℚ => (H.coeff s) • x)
    dsimp [L, R]
    simpa only [LinearMap.comp_apply, koszulHilbertLinearMap_apply,
      pointParameterLinearMap_apply, segreCombinationLinearMap_apply] using
        koszul_monomial_point_coefficient e h j (s 0) (s 1) he hh hbound
  have hlinear : L H = R H := by
    calc
      L H = L (∑ s ∈ H.support, MvPolynomial.monomial s (H.coeff s)) := congrArg L H.as_sum
      _ = ∑ s ∈ H.support, L (MvPolynomial.monomial s (H.coeff s)) := map_sum L _ _
      _ = ∑ s ∈ H.support, R (MvPolynomial.monomial s (H.coeff s)) := Finset.sum_congr rfl hmono
      _ = R (∑ s ∈ H.support, MvPolynomial.monomial s (H.coeff s)) := (map_sum R _ _).symm
      _ = R H := congrArg R H.as_sum.symm
  simpa only [L, R, LinearMap.comp_apply, koszulHilbertLinearMap_apply,
    pointParameterLinearMap_apply, segreCombinationLinearMap_apply] using hlinear

#print axioms koszul_coefficient_of_degree

end IncidenceBinomial

/-- B13.4: the finite-difference calculation that would replace the singular-base
projective-bundle pushforward after the actual geometric Hilbert identity is established.
It includes lower-degree terms of H, which must cancel out of the top coefficient. -/
theorem koszulIncidenceHilbert_point_coefficient (e h j : ℕ)
    (he : 3 ≤ e) (hh : h + 2 ≤ e) (hj : j ≤ 1)
    (H : BaseHilbertPolynomial) (hH : H.totalDegree ≤ h + j) :
    pointParameterCoefficient (koszulIncidenceHilbert e H) ((e - 1).choose 2 + h) j =
      ∑ i ∈ Finset.range (h + 1),
        (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedHilbertCoefficient H (h - i) (i + j) := by
  exact IncidenceBinomial.koszul_coefficient_of_degree e h j he hh H hH

#print axioms koszulIncidenceHilbert_point_coefficient

end DistinctDistances.TrackB
