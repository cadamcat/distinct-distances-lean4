import DistinctDistances.TrackA.Definitions
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection

/-! Support for `poly_socle` (polynomial.tex:121–162).

Instead of the Koszul/Ext comparison of the paper, the determinant is tracked through an
induction that trades one parameter `f_last` for one generic linear form `ℓ` in the
coordinates at a time. With `J` the ideal of the other parameters, the adjugate row gives
`± det Q'' * f_last ≡ det Q' * ℓ (mod J)`; since `f_last` is regular modulo `J`, a relation
`det Q' ∈ J + (f_last)` would force `det Q'' ∈ J + (ℓ)`. The only Cohen–Macaulay input is
OpenAI's `polynomialLocal_regular_prefix_maximal_not_associated` (a regular sequence shorter
than the height leaves the maximal ideal unassociated) and its constant regular parameter
selection. -/

namespace DistinctDistances.TrackA.Socle

noncomputable section
open scoped BigOperators
open IsLocalRing RingTheory.Sequence Matrix

section Abstract

variable {R : Type*} [CommRing R]

lemma ideal_smul_top (I : Ideal R) : (I • (⊤ : Submodule R R)) = I := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

lemma isRegular_iff_ideal (rs : List R) :
    IsRegular R rs ↔ IsWeaklyRegular R rs ∧ Ideal.ofList rs ≠ ⊤ := by
  rw [isRegular_iff, ideal_smul_top, ne_comm]

lemma isRegular_of_append {rs ss : List R} (h : IsRegular R (rs ++ ss)) : IsRegular R rs := by
  rw [isRegular_iff_ideal] at h ⊢
  refine ⟨((isWeaklyRegular_append_iff R rs ss).mp h.1).1, fun htop => h.2 ?_⟩
  rw [Ideal.ofList_append, htop, top_sup_eq]

lemma mem_of_mul_mem_of_isRegular {rs : List R} {x a : R} (h : IsRegular R (rs ++ [x]))
    (ha : x * a ∈ Ideal.ofList rs) : a ∈ Ideal.ofList rs := by
  have h1 := ((isWeaklyRegular_append_iff R rs [x]).mp h.toIsWeaklyRegular).2
  rw [isWeaklyRegular_singleton_iff] at h1
  have h2 := mem_of_isSMulRegular_quotient_of_smul_mem h1 (x := a)
    (by rw [ideal_smul_top, smul_eq_mul]; exact ha)
  rwa [ideal_smul_top] at h2

lemma mulVec_mem_span {m n : Type*} [Fintype n] (M : Matrix m n R) (w : n → R) (i : m) :
    (M *ᵥ w) i ∈ Ideal.span (Set.range w) := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

lemma radical_le_maximalIdeal [IsLocalRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R) :
    I.radical ≤ maximalIdeal R :=
  (maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr hI

lemma mem_minimalPrimes_of_radical_eq [IsLocalRing R] {I : Ideal R}
    (h : I.radical = maximalIdeal R) : maximalIdeal R ∈ I.minimalPrimes := by
  refine ⟨⟨(maximalIdeal.isMaximal R).isPrime, h ▸ Ideal.le_radical⟩, ?_⟩
  rintro q ⟨hq, hIq⟩ -
  rw [← h]
  exact hq.radical_le_iff.mpr hIq

/-- Generic choice of one coordinate form: if `x` is a parameter modulo `J`, a general
`F`-combination of the coordinates `z` is one too. Uses Krull's principal ideal theorem
to see that the primes containing `J` below the maximal ideal are minimal over `J`. -/
lemma exists_generic_param [IsNoetherianRing R] [IsLocalRing R]
    {F : Type*} [Field F] [Infinite F] [Algebra F R] {k : ℕ}
    (J : Ideal R) (x : R) (z : Fin (k+1) → R)
    (hJx : (J ⊔ Ideal.span {x}).radical = maximalIdeal R)
    (hzm : ∀ j, z j ∈ maximalIdeal R)
    (hz : maximalIdeal R ≤ J ⊔ Ideal.span (Set.range z)) :
    ∃ μ : Fin (k+1) → F, μ ≠ 0 ∧
      (J ⊔ Ideal.span {∑ j, algebraMap F R (μ j) * z j}).radical = maximalIdeal R := by
  classical
  let φ : (Fin (k+1) → F) →ₗ[F] R := Fintype.linearCombination F z
  have hφ : ∀ μ, φ μ = ∑ j, algebraMap F R (μ j) * z j := by
    intro μ
    simp [φ, Fintype.linearCombination_apply, Algebra.smul_def]
  let S : Set (Ideal R) := J.minimalPrimes \ {maximalIdeal R}
  have hSfin : S.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing R J).sdiff
  let U : Ideal R → Submodule F (Fin (k+1) → F) := fun p => (p.restrictScalars F).comap φ
  let s : Finset (Submodule F (Fin (k+1) → F)) := insert ⊥ (hSfin.toFinset.image U)
  have hJm : J ≤ maximalIdeal R := le_sup_left.trans (hJx ▸ Ideal.le_radical)
  have htop : ⊤ ∉ s := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact bot_ne_top h.symm
    · obtain ⟨p, hp, hpU⟩ := Finset.mem_image.mp h
      rw [Set.Finite.mem_toFinset] at hp
      obtain ⟨hpmin, hpm⟩ := hp
      have hpprime : p.IsPrime := hpmin.1.1
      have hzp : ∀ j, z j ∈ p := by
        intro j
        have h1 : Pi.single j 1 ∈ U p := by rw [hpU]; trivial
        have h2 : φ (Pi.single j 1) ∈ p := h1
        simpa [hφ, Pi.single_apply] using h2
      have hmp : maximalIdeal R ≤ p := hz.trans
        (sup_le hpmin.1.2 (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hzp j)))
      exact hpm (Set.mem_singleton_iff.mpr
        (le_antisymm (IsLocalRing.le_maximalIdeal hpprime.ne_top) hmp))
  obtain ⟨μ, hμ⟩ := (Set.ne_univ_iff_exists_notMem _).mp
    (Subspace.biUnion_ne_univ_of_top_notMem htop)
  simp only [Set.mem_iUnion, not_exists] at hμ
  have hμbot : μ ≠ 0 := fun h0 => hμ ⊥ (Finset.mem_insert_self _ _) (by simp [h0])
  have hμp : ∀ p ∈ S, φ μ ∉ p := fun p hp hmem =>
    hμ (U p) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨p, hSfin.mem_toFinset.mpr hp, rfl⟩)) hmem
  refine ⟨μ, hμbot, ?_⟩
  rw [← hφ]
  apply le_antisymm
  · apply radical_le_maximalIdeal
    refine sup_le hJm ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hφ]
    exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _ (hzm j))
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hle, hp⟩
    by_contra hmp
    have hpm : p ≠ maximalIdeal R := fun h => hmp (h ▸ le_rfl)
    have hlt : p < maximalIdeal R :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) hpm
    have hm : maximalIdeal R ∈ (Ideal.span (insert x (J : Set R))).minimalPrimes := by
      apply mem_minimalPrimes_of_radical_eq
      rw [Ideal.span_insert, Ideal.span_eq, sup_comm]
      exact hJx
    have hpmin := Ideal.mem_minimalPrimes_span_of_mem_minimalPrimes_span_insert hlt x
      (J : Set R) hm (J : Set R) (fun y hy => hle (Ideal.mem_sup_left hy))
      (fun y hy => Ideal.le_radical (Ideal.subset_span (Set.mem_insert_of_mem _ hy)))
    rw [Ideal.span_eq] at hpmin
    exact hμp p ⟨hpmin, hpm⟩ (le_sup_right.trans hle (Ideal.mem_span_singleton_self _))

/-- The determinant induction. `hL` is the Cohen–Macaulay input: a regular sequence of
length `< n` followed by a parameter stays regular. -/
theorem socle_induction [IsNoetherianRing R] [IsLocalRing R]
    {F : Type*} [Field F] [Infinite F] [Algebra F R] (n : ℕ)
    (hL : ∀ (t : List R) (x : R), IsRegular R t → t.length < n →
      (Ideal.ofList (t ++ [x])).radical = maximalIdeal R → IsRegular R (t ++ [x])) :
    ∀ (k : ℕ) (ys : List R) (z f : Fin k → R) (Q : Matrix (Fin k) (Fin k) R),
      ys.length + k = n →
      (∀ i, f i - (Q *ᵥ z) i ∈ Ideal.ofList ys) →
      (∀ j, z j ∈ maximalIdeal R) →
      maximalIdeal R ≤ Ideal.ofList ys ⊔ Ideal.span (Set.range z) →
      IsRegular R (ys ++ List.ofFn f) →
      (Ideal.ofList (ys ++ List.ofFn f)).radical = maximalIdeal R →
      Q.det ∉ Ideal.ofList (ys ++ List.ofFn f) := by
  intro k
  induction k with
  | zero =>
    intro ys z f Q _ _ _ _ _ hrad hdet
    rw [Matrix.det_isEmpty] at hdet
    have htop : Ideal.ofList (ys ++ List.ofFn f) = ⊤ := (Ideal.eq_top_iff_one _).mpr hdet
    rw [htop, Ideal.radical_top] at hrad
    exact (maximalIdeal.isMaximal R).ne_top hrad.symm
  | succ k ih =>
    intro ys z f Q hlen hQ hzm hz hreg hrad hdet
    classical
    set t : List R := ys ++ List.ofFn (fun i : Fin k => f i.castSucc) with ht
    set J : Ideal R := Ideal.ofList t with hJ
    have hsplit : ys ++ List.ofFn f = t ++ [f (Fin.last k)] := by
      rw [List.ofFn_succ', List.concat_eq_append, List.append_assoc]
    rw [hsplit] at hreg hrad hdet
    have hJx : (J ⊔ Ideal.span {f (Fin.last k)}).radical = maximalIdeal R := by
      rw [← Ideal.ofList_singleton, ← Ideal.ofList_append]
      exact hrad
    have hys : Ideal.ofList ys ≤ J := by
      rw [hJ, ht, Ideal.ofList_append]
      exact le_sup_left
    have hfJ : ∀ i : Fin k, f i.castSucc ∈ J := fun i =>
      Ideal.subset_span (List.mem_append_right ys (List.mem_ofFn.mpr ⟨i, rfl⟩))
    obtain ⟨μ, hμ, hrad'⟩ := exists_generic_param (F := F) J (f (Fin.last k)) z hJx hzm
      (hz.trans (sup_le_sup_right hys _))
    set ℓ := ∑ j, algebraMap F R (μ j) * z j with hℓ
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hμ
    -- change of coordinates putting `ℓ` at position `j0`
    let v : Fin (k+1) → R := fun j => algebraMap F R (μ j)
    let D : Matrix (Fin (k+1)) (Fin (k+1)) R := (1 : Matrix _ _ R).updateRow j0 v
    have hDdet : D.det = algebraMap F R (μ j0) := by
      have hv : (∑ m, v m • (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) m) = v := by
        ext j
        simp [Matrix.one_apply]
      have h := Matrix.det_updateRow_sum (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) j0 v
      rw [hv, Matrix.det_one, smul_eq_mul, mul_one] at h
      exact h
    have hDunit : IsUnit D.det := by
      rw [hDdet]
      exact (isUnit_iff_ne_zero.mpr (by simpa using hj0)).map (algebraMap F R)
    let z' : Fin (k+1) → R := D *ᵥ z
    have hz'0 : z' j0 = ℓ := by
      simp [z', D, v, hℓ, Matrix.mulVec, dotProduct, Matrix.updateRow_self]
    have hzz' : z = D⁻¹ *ᵥ z' := by
      simp only [z', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D hDunit, Matrix.one_mulVec]
    let Q' : Matrix (Fin (k+1)) (Fin (k+1)) R := Q * D⁻¹
    have hQz' : Q' *ᵥ z' = Q *ᵥ z := by
      simp only [Q', z', Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul D hDunit, Matrix.mul_one]
    let Q'' : Matrix (Fin k) (Fin k) R := Q'.submatrix Fin.castSucc j0.succAbove
    have hz'm : ∀ j, z' j ∈ maximalIdeal R := fun j =>
      (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hzm i)) (mulVec_mem_span D z j)
    -- the induction hypothesis for `ℓ :: ys`, the coordinates other than `j0`,
    -- and the parameters other than the last
    have hIH1 : (ℓ :: ys).length + k = n := by
      simp only [List.length_cons]
      omega
    have hIH2 : ∀ i : Fin k, f i.castSucc - (Q'' *ᵥ fun j => z' (j0.succAbove j)) i ∈
        Ideal.ofList (ℓ :: ys) := by
      intro i
      have h1 := hQ i.castSucc
      rw [← hQz'] at h1
      simp only [Matrix.mulVec, dotProduct] at h1 ⊢
      rw [Fin.sum_univ_succAbove _ j0] at h1
      have e : f i.castSucc - ∑ j : Fin k, Q'' i j * z' (j0.succAbove j) =
          (f i.castSucc - (Q' i.castSucc j0 * z' j0 +
            ∑ j : Fin k, Q' i.castSucc (j0.succAbove j) * z' (j0.succAbove j))) +
          Q' i.castSucc j0 * ℓ := by
        rw [hz'0]
        simp only [Q'', Matrix.submatrix_apply]
        ring
      rw [e, Ideal.ofList_cons]
      exact Ideal.add_mem _ (Ideal.mem_sup_right h1)
        (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    have hIH4 : maximalIdeal R ≤ Ideal.ofList (ℓ :: ys) ⊔
        Ideal.span (Set.range fun j => z' (j0.succAbove j)) := by
      have hspan : Ideal.span (Set.range z') ≤ Ideal.ofList (ℓ :: ys) ⊔
          Ideal.span (Set.range fun j => z' (j0.succAbove j)) := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        rw [Ideal.ofList_cons]
        by_cases hi : i = j0
        · rw [hi, hz'0]
          exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
        · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
          exact Ideal.mem_sup_right (Ideal.subset_span ⟨i', rfl⟩)
      have hzspan : Ideal.span (Set.range z) ≤ Ideal.span (Set.range z') := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        rw [hzz']
        exact mulVec_mem_span _ _ _
      have hys' : Ideal.ofList ys ≤ Ideal.ofList (ℓ :: ys) := by
        rw [Ideal.ofList_cons]
        exact le_sup_right
      refine hz.trans (sup_le (hys'.trans le_sup_left) (hzspan.trans hspan))
    have hreg' : IsRegular R (ℓ :: t) := by
      have h1 := hL t ℓ (isRegular_of_append hreg)
        (by rw [ht, List.length_append, List.length_ofFn]; omega)
        (by rw [Ideal.ofList_append, Ideal.ofList_singleton]; exact hrad')
      exact IsLocalRing.isRegular_of_perm h1 List.perm_append_comm
    have hrad'' : (Ideal.ofList (ℓ :: t)).radical = maximalIdeal R := by
      rw [Ideal.ofList_cons, sup_comm]
      exact hrad'
    have hIH := ih (ℓ :: ys) (fun j => z' (j0.succAbove j)) (fun i => f i.castSucc) Q''
      hIH1 hIH2 (fun j => hz'm _) hIH4 hreg' hrad''
    -- the adjugate row `j0`
    have hadj : ∑ i, Q'.adjugate j0 i * (Q' *ᵥ z') i = Q'.det * ℓ := by
      have h : Q'.adjugate *ᵥ (Q' *ᵥ z') = Q'.det • z' := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
          Matrix.one_mulVec]
      have h' := congrFun h j0
      rw [Pi.smul_apply, smul_eq_mul, hz'0] at h'
      exact h'
    have hcs : ∀ i : Fin k, (Q' *ᵥ z') i.castSucc ∈ J := by
      intro i
      have h1 : f i.castSucc - (Q' *ᵥ z') i.castSucc ∈ J := by
        rw [hQz']
        exact hys (hQ _)
      have e : (Q' *ᵥ z') i.castSucc =
          f i.castSucc - (f i.castSucc - (Q' *ᵥ z') i.castSucc) := by ring
      rw [e]
      exact J.sub_mem (hfJ i) h1
    have hlast : f (Fin.last k) - (Q' *ᵥ z') (Fin.last k) ∈ J := by
      rw [hQz']
      exact hys (hQ _)
    set a := Q'.adjugate j0 (Fin.last k) with ha
    have hmem : a * f (Fin.last k) - Q'.det * ℓ ∈ J := by
      rw [← hadj, Fin.sum_univ_castSucc]
      have e : a * f (Fin.last k) - (∑ i : Fin k, Q'.adjugate j0 i.castSucc *
            (Q' *ᵥ z') i.castSucc + Q'.adjugate j0 (Fin.last k) * (Q' *ᵥ z') (Fin.last k)) =
          a * (f (Fin.last k) - (Q' *ᵥ z') (Fin.last k)) -
            ∑ i : Fin k, Q'.adjugate j0 i.castSucc * (Q' *ᵥ z') i.castSucc := by
        rw [ha]
        ring
      rw [e]
      exact J.sub_mem (J.mul_mem_left _ hlast) (J.sum_mem fun i _ => J.mul_mem_left _ (hcs i))
    -- conclusion
    have hdet' : Q'.det ∈ Ideal.ofList (t ++ [f (Fin.last k)]) := by
      rw [Matrix.det_mul]
      exact Ideal.mul_mem_right _ _ hdet
    rw [Ideal.ofList_append, Ideal.ofList_singleton] at hdet'
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp hdet'
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    have hprod : f (Fin.last k) * (a - w * ℓ) ∈ J := by
      have e : f (Fin.last k) * (a - w * ℓ) =
          (a * f (Fin.last k) - Q'.det * ℓ) + b * ℓ := by
        rw [← hbc]
        ring
      rw [e]
      exact J.add_mem hmem (J.mul_mem_right _ hb)
    have haJ : a - w * ℓ ∈ J := mem_of_mul_mem_of_isRegular hreg hprod
    have haℓ : a ∈ Ideal.ofList (ℓ :: t) := by
      rw [Ideal.ofList_cons]
      have e : a = (a - w * ℓ) + w * ℓ := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_right haJ)
        (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    apply hIH
    change Q''.det ∈ Ideal.ofList (ℓ :: t)
    have hsign : Q''.det =
        (-1) ^ ((Fin.last k : ℕ) + (j0 : ℕ)) * a := by
      rw [ha, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, ← mul_assoc,
        ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    rw [hsign]
    exact Ideal.mul_mem_left _ _ haℓ

end Abstract

section FiniteLength

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A proper ideal of finite colength in a local ring has the maximal ideal as radical. -/
lemma radical_eq_maximalIdeal_of_length_lt_top (I : Ideal R) (hI : I ≤ maximalIdeal R)
    (hlen : Module.length R (R ⧸ I) < ⊤) : I.radical = maximalIdeal R := by
  apply le_antisymm (radical_le_maximalIdeal hI)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro p ⟨hIp, hp⟩
  have hfin : IsFiniteLength R (R ⧸ I) := Module.length_ne_top_iff.mp hlen.ne
  have hart : IsArtinian R (R ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  have hart' : IsArtinian R (R ⧸ p) :=
    isArtinian_of_surjective _ (Submodule.factor hIp) (Submodule.factor_surjective hIp)
  have : IsArtinianRing (R ⧸ p) := isArtinian_of_tower R hart'
  have hfield : IsField (R ⧸ p) := IsArtinianRing.isField_of_isDomain (R ⧸ p)
  have hmax : p.IsMaximal := Ideal.Quotient.maximal_of_isField p hfield
  exact (IsLocalRing.eq_maximalIdeal hmax).ge

end FiniteLength

section Origin

variable {F : Type*} [Field F]

lemma X_mem_maximalIdeal (c : ℕ) (j : Fin c) :
    algebraMap (FieldPoly c F) (OriginLocalRing c F) (MvPolynomial.X j) ∈
      maximalIdeal (OriginLocalRing c F) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  apply Ideal.mem_map_of_mem
  change MvPolynomial.X j ∈ MvPolynomial.vanishingIdeal F {(0 : Fin c → F)}
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  simp

lemma maximalIdeal_le_span_X (c : ℕ) :
    maximalIdeal (OriginLocalRing c F) ≤ Ideal.span (Set.range fun j : Fin c =>
      algebraMap (FieldPoly c F) (OriginLocalRing c F) (MvPolynomial.X j)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
  intro p hp
  change p ∈ MvPolynomial.vanishingIdeal F {(0 : Fin c → F)} at hp
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hp
  have hp' : p ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin c))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push Not at h
    have hm0 : m = 0 := by
      ext i
      exact h i (Set.mem_univ i)
    subst hm0
    have h0 : p.coeff 0 = 0 := by
      rw [MvPolynomial.aeval_zero] at hp
      simpa [MvPolynomial.constantCoeff_eq] using hp
    exact (MvPolynomial.mem_support_iff.mp hm) h0
  rw [Set.image_univ] at hp'
  rw [Ideal.mem_comap]
  have := Ideal.mem_map_of_mem (algebraMap (FieldPoly c F) (OriginLocalRing c F)) hp'
  rwa [Ideal.map_span, ← Set.range_comp] at this

/-- The Cohen–Macaulay input at the origin: a regular sequence of length `< c` followed by a
parameter is regular, by OpenAI's `polynomialLocal_regular_prefix_maximal_not_associated`. -/
lemma origin_regular_append (c : ℕ) (t : List (OriginLocalRing c F)) (x : OriginLocalRing c F)
    (ht : IsRegular (OriginLocalRing c F) t) (hlen : t.length < c)
    (hrad : (Ideal.ofList (t ++ [x])).radical = maximalIdeal (OriginLocalRing c F)) :
    IsRegular (OriginLocalRing c F) (t ++ [x]) := by
  let P := pointIdealOver (0 : FieldPoint c F)
  have hheight : P.height = (c : ℕ∞) := OAI.QuarticPowerFree.mvPolynomial_maximal_height c P
  have hnot := OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated
    F c P t ht (by rw [hheight]; exact_mod_cast hlen)
  have hsmul : IsSMulRegular (OriginLocalRing c F ⧸ Ideal.ofList t) x := by
    by_contra hx
    have hx' : x ∈ ⋃ p ∈ associatedPrimes (OriginLocalRing c F)
        (OriginLocalRing c F ⧸ Ideal.ofList t), (p : Set (OriginLocalRing c F)) := by
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨p, hp, hxp⟩ := hx'
    have hp' : IsAssociatedPrime p (OriginLocalRing c F ⧸ Ideal.ofList t) := hp
    have hle : Ideal.ofList t ≤ p := by
      have h := hp'.annihilator_le
      rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at h
    have hmp : maximalIdeal (OriginLocalRing c F) ≤ p := by
      rw [← hrad]
      refine hp'.isPrime.radical_le_iff.mpr ?_
      rw [Ideal.ofList_append, Ideal.ofList_singleton]
      exact sup_le hle (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxp))
    have hpm : p = maximalIdeal (OriginLocalRing c F) :=
      le_antisymm (IsLocalRing.le_maximalIdeal hp'.isPrime.ne_top) hmp
    exact hnot (hpm ▸ hp')
  rw [isRegular_iff_ideal]
  refine ⟨(isWeaklyRegular_append_iff (OriginLocalRing c F) t [x]).mpr
    ⟨ht.toIsWeaklyRegular, ?_⟩, ?_⟩
  · rw [isWeaklyRegular_singleton_iff, ideal_smul_top]
    exact hsmul
  · intro htop
    rw [htop, Ideal.radical_top] at hrad
    exact (maximalIdeal.isMaximal (OriginLocalRing c F)).ne_top hrad.symm

end Origin

/-- `poly_socle`, proved by the determinant induction after a constant change of the
parameters into a regular sequence. -/
theorem origin_det_not_mem {F : Type*} [Field F] [IsAlgClosed F] (c : ℕ)
    (f : Fin c → OriginLocalRing c F) (Q : Matrix (Fin c) (Fin c) (OriginLocalRing c F))
    (hfinite : Module.length (OriginLocalRing c F)
      (OriginLocalRing c F ⧸ Ideal.span (Set.range f)) < ⊤)
    (hQ : ∀ i, f i = ∑ j, Q i j *
      algebraMap (FieldPoly c F) (OriginLocalRing c F) (MvPolynomial.X j)) :
    Matrix.det Q ∉ Ideal.span (Set.range f) := by
  classical
  let P := pointIdealOver (0 : FieldPoint c F)
  have hheight : P.height = (c : ℕ∞) := OAI.QuarticPowerFree.mvPolynomial_maximal_height c P
  let Z : Fin c → OriginLocalRing c F := fun j =>
    algebraMap (FieldPoly c F) (OriginLocalRing c F) (MvPolynomial.X j)
  have hZm : ∀ j, Z j ∈ maximalIdeal (OriginLocalRing c F) := X_mem_maximalIdeal c
  have hfZ : f = Q *ᵥ Z := funext hQ
  have hfm : Ideal.span (Set.range f) ≤ maximalIdeal (OriginLocalRing c F) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [hfZ]
    exact (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hZm j)) (mulVec_mem_span Q Z i)
  have hrad := radical_eq_maximalIdeal_of_length_lt_top _ hfm hfinite
  obtain ⟨cs, hlen, hreg, -, hrad'⟩ :=
    OAI.PiExponentSiegel.W58.polynomialLocal_exists_constant_regular_parameters
      F c P f hrad c hheight
  let AR : Matrix (Fin c) (Fin c) (OriginLocalRing c F) := fun i j =>
    algebraMap F _ (cs.get (Fin.cast hlen.symm i) j)
  let g : Fin c → OriginLocalRing c F := AR *ᵥ f
  have hg : List.ofFn g = cs.map (Finsupp.linearCombination F f) := by
    apply List.ext_get
    · simp [hlen]
    · intro n h1 h2
      simp [g, AR, Matrix.mulVec, dotProduct,
        Finsupp.linearCombination_apply, Finsupp.sum_fintype, Algebra.smul_def]
  have key := socle_induction (R := OriginLocalRing c F) (F := F) c
    (fun t x ht hl hr => origin_regular_append c t x ht hl hr) c [] Z g (AR * Q) (by simp)
    (fun i => by simp [g, hfZ, Matrix.mulVec_mulVec]) hZm
    (by simpa using maximalIdeal_le_span_X c)
    (by simpa [hg] using hreg) (by simpa [hg] using hrad')
  intro hdet
  apply key
  rw [Matrix.det_mul]
  have hspan : Ideal.ofList ([] ++ List.ofFn g) = Ideal.span (Set.range g) := by
    rw [List.nil_append]
    exact congrArg Ideal.span (Set.ext fun r => List.mem_ofFn' g r)
  have hcramer : ∀ j, AR.det * f j ∈ Ideal.ofList ([] ++ List.ofFn g) := by
    intro j
    have h : AR.adjugate *ᵥ g = AR.det • f := by
      simp only [g, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    have h' := congrFun h j
    rw [Pi.smul_apply, smul_eq_mul] at h'
    rw [← h', hspan]
    exact mulVec_mem_span _ _ _
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hdet
  rw [← ha, Finset.mul_sum]
  exact Ideal.sum_mem _ fun j _ => by
    rw [mul_left_comm]
    exact Ideal.mul_mem_left _ _ (hcramer j)

end

end DistinctDistances.TrackA.Socle
