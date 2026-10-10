import DistinctDistances.Foundations.GradedEvaluation
import DistinctDistances.Foundations
import OAI.NumberTheory.PowerFree.GenericCuts
import OAI.NumberTheory.PowerFree.PointInterpolation
import OAI.NumberTheory.PowerFree.PatchBounds

/-!
Generic-fibre dimension facts in the shared Hilbert model. For a prime ideal the shared
affine Hilbert dimension is the transcendence degree of the coordinate ring
(OAI `hilbert_natDegree_eq_trdeg`); everything here is reduced to that identity.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace GenericFiber

/-- The shared Hilbert dimension of a prime ideal is its transcendence degree. -/
theorem affineDimension_eq_trdeg {n : ℕ} (I : Ideal (Poly n)) [I.IsPrime] :
    (OAI.QuarticPowerFree.affineDimension I : Cardinal) = Algebra.trdeg ℂ (Poly n ⧸ I) :=
  OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg I _
    (OAI.QuarticPowerFree.coordinateHilbert_eventually I)

/-- A prime with polynomial-ring quotient has the number of variables as dimension. -/
theorem affineDimension_of_quotient_equiv {n d : ℕ} (I : Ideal (Poly n)) [I.IsPrime]
    (e : (Poly n ⧸ I) ≃ₐ[ℂ] Poly d) : OAI.QuarticPowerFree.affineDimension I = d := by
  have h := affineDimension_eq_trdeg I
  rw [e.trdeg_eq, MvPolynomial.trdeg_of_isDomain] at h
  simpa using h

/-- Affine-linear substitution `f ↦ f(b + φ t)`. -/
def affineSubst {n d : ℕ} (b : Point n) (φ : Point d →ₗ[ℂ] Point n) : Poly n →ₐ[ℂ] Poly d :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (b i) +
    ∑ k : Fin d, MvPolynomial.C (φ (Pi.single k 1) i) * MvPolynomial.X k)

theorem eval_affineSubst {n d : ℕ} (b : Point n) (φ : Point d →ₗ[ℂ] Point n)
    (t : Point d) (f : Poly n) :
    MvPolynomial.eval t (affineSubst b φ f) = MvPolynomial.aeval (b + φ t) f := by
  have hcomp := MvPolynomial.comp_aeval (R := ℂ) (S₁ := Poly d)
    (fun i => MvPolynomial.C (b i) +
      ∑ k : Fin d, MvPolynomial.C (φ (Pi.single k 1) i) * MvPolynomial.X k)
    (MvPolynomial.aeval t : Poly d →ₐ[ℂ] ℂ)
  have h := congrArg (fun F : Poly n →ₐ[ℂ] ℂ => F f) hcomp
  simp only [AlgHom.comp_apply] at h
  rw [← MvPolynomial.coe_aeval_eq_eval]
  change (MvPolynomial.aeval t) (affineSubst b φ f) = _
  rw [affineSubst, h]
  refine congrArg (fun x : Point n => MvPolynomial.aeval x f) ?_
  funext i
  have ht : φ t = ∑ k : Fin d, t k • φ (Pi.single k 1) := by
    conv_lhs => rw [show t = ∑ k : Fin d, t k • (Pi.single k (1 : ℂ) : Point d) by
      simpa using ((Pi.basisFun ℂ (Fin d)).sum_repr t).symm]
    simp [map_sum, map_smul]
  simp only [map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply, Pi.add_apply, ht, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem affineSubst_surjective {n d : ℕ} (b : Point n) (φ : Point d →ₗ[ℂ] Point n)
    (hφ : Function.Injective φ) : Function.Surjective (affineSubst b φ) := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective φ (LinearMap.ker_eq_bot.mpr hφ)
  have hX : ∀ k : Fin d, MvPolynomial.X k ∈ (affineSubst b φ).range := by
    intro k
    refine ⟨∑ i : Fin n, MvPolynomial.C (L (Pi.single i 1) k) *
      (MvPolynomial.X i - MvPolynomial.C (b i)), ?_⟩
    change affineSubst b φ _ = MvPolynomial.X k
    apply MvPolynomial.funext
    intro t
    rw [eval_affineSubst]
    simp only [map_sum, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply, Pi.add_apply, MvPolynomial.eval_X,
      add_sub_cancel_left]
    have hLt : L (φ t) = t := by
      simpa using congrArg (fun F : Point d →ₗ[ℂ] Point d => F t) hL
    have hsum : L (φ t) = ∑ i : Fin n, (φ t) i • L (Pi.single i 1) := by
      conv_lhs => rw [show φ t = ∑ i : Fin n, (φ t) i • (Pi.single i (1 : ℂ) : Point n) by
        simpa using ((Pi.basisFun ℂ (Fin n)).sum_repr (φ t)).symm]
      simp [map_sum, map_smul]
    have hk := congrArg (fun v : Point d => v k) (hsum.symm.trans hLt)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
    rw [← hk]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrange : (affineSubst b φ).range = ⊤ := by
    rw [eq_top_iff, ← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    exact hX k
  intro y
  have hy : y ∈ (affineSubst b φ).range := hrange ▸ Algebra.mem_top
  exact hy

/-- The Hilbert dimension of a nonempty principal open of an affine-linear space. -/
theorem affine_linear_principal_open_dimension {n d : ℕ}
    (b : Point n) (φ : Point d →ₗ[ℂ] Point n) (hφ : Function.Injective φ)
    (g : Poly n) (t0 : Point d) (ht0 : MvPolynomial.aeval (b + φ t0) g ≠ 0) :
    (AffineVariety.closure
      {x | ∃ t : Point d, x = b + φ t ∧ MvPolynomial.aeval x g ≠ 0}).dimension = d := by
  classical
  set S : Set (Point n) := {x | ∃ t : Point d, x = b + φ t ∧ MvPolynomial.aeval x g ≠ 0}
  have hker : MvPolynomial.vanishingIdeal ℂ S = RingHom.ker (affineSubst b φ) := by
    ext f
    rw [RingHom.mem_ker, MvPolynomial.mem_vanishingIdeal_iff]
    constructor
    · intro hf
      have hgf : affineSubst b φ g * affineSubst b φ f = 0 := by
        apply MvPolynomial.funext
        intro t
        rw [map_mul, eval_affineSubst, eval_affineSubst, map_zero]
        by_cases hgt : MvPolynomial.aeval (b + φ t) g = 0
        · rw [hgt, zero_mul]
        · rw [hf _ ⟨t, rfl, hgt⟩, mul_zero]
      have hg : affineSubst b φ g ≠ 0 := by
        intro hz
        apply ht0
        rw [← eval_affineSubst, hz, map_zero]
      exact (mul_eq_zero.mp hgf).resolve_left hg
    · rintro hf x ⟨t, rfl, _⟩
      rw [← eval_affineSubst, hf, map_zero]
  change OAI.QuarticPowerFree.affineDimension (MvPolynomial.vanishingIdeal ℂ S) = d
  rw [hker]
  have : (RingHom.ker (affineSubst b φ)).IsPrime := RingHom.ker_isPrime _
  exact affineDimension_of_quotient_equiv _
    (Ideal.quotientKerAlgEquivOfSurjective (affineSubst_surjective b φ hφ))


/-! ### Graded evaluation and coefficient bookkeeping -/


section Split

variable {ι κ : Type*}

theorem aeval_sumElim_X_C (z : κ → ℂ) (Φ : MvPolynomial (ι ⊕ κ) ℂ) :
    MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun b => MvPolynomial.C (z b))) Φ =
      MvPolynomial.map (MvPolynomial.aeval (R := ℂ) z).toRingHom
        (MvPolynomial.sumAlgEquiv ℂ ι κ Φ) := by
  have hhom : (MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun b => MvPolynomial.C (z b))) :
      MvPolynomial (ι ⊕ κ) ℂ →ₐ[ℂ] MvPolynomial ι ℂ) =
      (MvPolynomial.mapAlgHom (MvPolynomial.aeval z)).comp
        (MvPolynomial.sumAlgEquiv ℂ ι κ).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro s
    cases s with
    | inl i => simp
    | inr b => simp
  exact congrArg (fun F : MvPolynomial (ι ⊕ κ) ℂ →ₐ[ℂ] MvPolynomial ι ℂ => F Φ) hhom

theorem sumAlgEquiv_monomial [Fintype ι] [Fintype κ] (s : ι ⊕ κ →₀ ℕ) (c : ℂ) :
    MvPolynomial.sumAlgEquiv ℂ ι κ (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (Finsupp.sumFinsuppAddEquivProdFinsupp s).1
        (MvPolynomial.monomial (Finsupp.sumFinsuppAddEquivProdFinsupp s).2 c) := by
  classical
  rw [MvPolynomial.monomial_eq, MvPolynomial.monomial_eq, MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_prod, map_pow, Fintype.prod_sum_type,
    MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr,
    MvPolynomial.sumAlgEquiv_C_inl,
    Finsupp.fst_sumFinsuppAddEquivProdFinsupp, Finsupp.snd_sumFinsuppAddEquivProdFinsupp]
  ring

theorem coeff_coeff_sumAlgEquiv [Fintype ι] [Fintype κ] (Φ : MvPolynomial (ι ⊕ κ) ℂ)
    (β : ι →₀ ℕ) (γ : κ →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv ℂ ι κ Φ).coeff β).coeff γ =
      Φ.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (β, γ)) := by
  classical
  induction Φ using MvPolynomial.induction_on' with
  | monomial s c =>
      rw [sumAlgEquiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      by_cases hs : s = Finsupp.sumFinsuppAddEquivProdFinsupp.symm (β, γ)
      · subst hs
        simp
      · rw [if_neg (fun h => hs h)]
        have hne : Finsupp.sumFinsuppAddEquivProdFinsupp s ≠ (β, γ) := by
          intro h
          apply hs
          rw [← h, AddEquiv.symm_apply_apply]
        by_cases h1 : (Finsupp.sumFinsuppAddEquivProdFinsupp s).1 = β
        · rw [if_pos h1, MvPolynomial.coeff_monomial, if_neg]
          intro h2
          exact hne (Prod.ext h1 h2)
        · rw [if_neg h1]
          simp
  | add p q hp hq =>
      rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq,
        MvPolynomial.coeff_add]

theorem weight_sumFinsupp_symm [Fintype ι] [Fintype κ] (w₁ : ι → ℕ) (w₂ : κ → ℕ)
    (β : ι →₀ ℕ) (γ : κ →₀ ℕ) :
    Finsupp.weight (Sum.elim w₁ w₂) (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (β, γ)) =
      Finsupp.weight w₁ β + Finsupp.weight w₂ γ := by
  classical
  simp only [Finsupp.weight_apply, smul_eq_mul]
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Finsupp.sum_fintype _ _ (fun _ => zero_mul _),
    Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Fintype.sum_sum_type]
  simp [Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inl,
    Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inr]

end Split

/-- The generic coefficient lemma. A dependence among graded elements of `A[t]`, whose
`κ`-part is independent, has a nonzero coefficient polynomial in the `κ`-variables which is
homogeneous and does not vanish at `f`. -/
theorem exists_generic_coefficient {A : Type*} [CommRing A] [IsDomain A] [Algebra ℂ A]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (wι : ι → ℕ) (a : ι → A) (f : κ → A)
    (hf : AlgebraicIndependent ℂ
      (fun b => (Polynomial.X * Polynomial.C (f b) : Polynomial A)))
    (hdep : ¬ AlgebraicIndependent ℂ (Sum.elim
      (fun i => (Polynomial.X ^ wι i * Polynomial.C (a i) : Polynomial A))
      (fun b => (Polynomial.X * Polynomial.C (f b) : Polynomial A)))) :
    ∃ (Φ : MvPolynomial (ι ⊕ κ) ℂ) (D : ℕ),
      Φ.IsWeightedHomogeneous (Sum.elim wι (fun _ => 1)) D ∧
      MvPolynomial.aeval (Sum.elim a f) Φ = 0 ∧
      ∃ (β : ι →₀ ℕ) (D' : ℕ),
        ((MvPolynomial.sumAlgEquiv ℂ ι κ Φ).coeff β).IsHomogeneous D' ∧
        MvPolynomial.aeval f ((MvPolynomial.sumAlgEquiv ℂ ι κ Φ).coeff β) ≠ 0 := by
  classical
  let w : ι ⊕ κ → ℕ := Sum.elim wι (fun _ => 1)
  have hv : (Sum.elim
      (fun i => (Polynomial.X ^ wι i * Polynomial.C (a i) : Polynomial A))
      (fun b => (Polynomial.X * Polynomial.C (f b) : Polynomial A))) =
      fun s => (Polynomial.X ^ w s * Polynomial.C (Sum.elim a f s) : Polynomial A) := by
    funext s
    cases s with
    | inl i => rfl
    | inr b => simp [w]
  rw [hv, algebraicIndependent_iff] at hdep
  push_neg at hdep
  obtain ⟨Φ0, hΦ0, hne0⟩ := hdep
  have hcomp : ∀ D, MvPolynomial.aeval (Sum.elim a f)
      (MvPolynomial.weightedHomogeneousComponent w D Φ0) = 0 := by
    intro D
    rw [← coeff_aeval_graded, hΦ0, Polynomial.coeff_zero]
  obtain ⟨d, hd⟩ : ∃ d, Φ0.coeff d ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne0 (MvPolynomial.ext _ _ (fun d => by simp [h d]))
  let D := Finsupp.weight w d
  let Φ := MvPolynomial.weightedHomogeneousComponent w D Φ0
  have hΦne : Φ ≠ 0 := by
    intro h
    apply hd
    have := congrArg (fun q : MvPolynomial (ι ⊕ κ) ℂ => q.coeff d) h
    simp only [Φ, MvPolynomial.coeff_weightedHomogeneousComponent] at this
    simpa [D] using this
  have hΦhom : Φ.IsWeightedHomogeneous w D :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous D Φ0
  let Ψ := MvPolynomial.sumAlgEquiv ℂ ι κ Φ
  have hΨ : Ψ ≠ 0 := by
    intro h
    apply hΦne
    have := congrArg (MvPolynomial.sumAlgEquiv ℂ ι κ).symm h
    simpa [Ψ] using this
  obtain ⟨β, hβ⟩ : ∃ β, Ψ.coeff β ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΨ (MvPolynomial.ext _ _ (fun β => by simp [h β]))
  have hhom : (Ψ.coeff β).IsHomogeneous (D - Finsupp.weight wι β) := by
    intro γ hγ
    rw [coeff_coeff_sumAlgEquiv] at hγ
    have h : Finsupp.weight (Sum.elim wι (fun _ : κ => (1 : ℕ)))
        (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (β, γ)) = D := hΦhom hγ
    rw [weight_sumFinsupp_symm] at h
    have h2 : Finsupp.weight (1 : κ → ℕ) γ = Finsupp.weight (fun _ : κ => (1 : ℕ)) γ := rfl
    change Finsupp.weight 1 γ = D - Finsupp.weight wι β
    omega
  refine ⟨Φ, D, hΦhom, hcomp D, β, D - Finsupp.weight wι β, hhom, ?_⟩
  intro hzero
  have hgraded := aeval_graded_of_isWeightedHomogeneous (R := A) hhom f
  have hone : (fun b : κ => (Polynomial.X ^ (1 : κ → ℕ) b * Polynomial.C (f b) : Polynomial A)) =
      fun b => Polynomial.X * Polynomial.C (f b) := by
    funext b
    simp
  rw [hone, hzero, map_zero, zero_mul] at hgraded
  exact hβ ((algebraicIndependent_iff.mp hf) _ hgraded)

/-! ### Dimension bookkeeping in the shared Hilbert model -/

theorem affineDimension_mono {n : ℕ} {I J : Ideal (Poly n)} (h : I ≤ J) :
    OAI.QuarticPowerFree.affineDimension J ≤ OAI.QuarticPowerFree.affineDimension I := by
  apply OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
  · filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually J] with T hT
    rw [← hT]
    positivity
  · filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually J,
      OAI.QuarticPowerFree.coordinateHilbert_eventually I] with T hJ hI
    rw [← hJ, ← hI]
    exact_mod_cast OAI.QuarticPowerFree.quotient_hilbert_le I J h T

/-- The dimension of a reduced variety is at most the maximum over its components. -/
theorem dimension_le_of_components {n : ℕ} (V : AffineVariety n) (k : ℕ)
    (h : ∀ W : V.Component, W.variety.dimension ≤ k) : V.dimension ≤ k := by
  classical
  let F : AffineFamily.Family n := Finset.univ.image (fun W : V.Component => W.variety)
  have hinf : (⨅ W ∈ F, W.ideal) = V.ideal := by
    apply le_antisymm
    · intro f hf
      rw [← V.isRadical.radical, ← Ideal.sInf_minimalPrimes]
      rw [Ideal.mem_sInf]
      intro Q hQ
      have hmem : AffineVariety.Component.variety (⟨Q, hQ⟩ : V.Component) ∈ F :=
        Finset.mem_image.mpr ⟨⟨Q, hQ⟩, Finset.mem_univ _, rfl⟩
      simp only [Submodule.mem_iInf] at hf
      exact hf _ hmem
    · apply le_iInf₂
      intro W hW
      obtain ⟨W', _, rfl⟩ := Finset.mem_image.mp hW
      exact W'.property.1.2
  have hlocus : AffineFamily.locus F = V := by
    apply AffineVariety.ext
    change (⨅ W ∈ F, W.ideal).radical = V.ideal
    rw [hinf, V.isRadical.radical]
  have hle : ∀ D, V.hilbert D ≤ ∑ W ∈ F, W.hilbert D := by
    intro D
    have := AffineFamily.hilbert_le_sum F D
    rwa [AffineFamily.hilbert, hlocus] at this
  have hsum : (∑ W ∈ F, W.hilbertPolynomial).natDegree ≤ k := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro W hW
    obtain ⟨W', _, rfl⟩ := Finset.mem_image.mp hW
    exact h W'
  refine le_trans ?_ hsum
  apply OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
  · filter_upwards [V.hilbert_eventually] with T hT
    rw [← hT]
    positivity
  · have hall : ∀ᶠ T : ℕ in Filter.atTop, ∀ W ∈ F,
        (W.hilbert T : ℚ) = W.hilbertPolynomial.eval (T : ℚ) :=
      (Filter.eventually_all_finset F).mpr (fun W _ => W.hilbert_eventually)
    filter_upwards [V.hilbert_eventually, hall] with T hT hW
    rw [← hT, Polynomial.eval_finset_sum]
    rw [← Finset.sum_congr rfl hW]
    exact_mod_cast hle T

/-- A polynomial nonvanishing on a set lies in no minimal prime of its vanishing ideal. -/
theorem not_mem_minimalPrimes_of_ne_zero {n : ℕ} (T : Set (Point n)) (h : Poly n)
    (hT : ∀ y ∈ T, MvPolynomial.aeval y h ≠ 0) (Q : Ideal (Poly n))
    (hQ : Q ∈ (MvPolynomial.vanishingIdeal ℂ T).minimalPrimes) : h ∉ Q := by
  classical
  intro hhQ
  let I := MvPolynomial.vanishingIdeal ℂ T
  let M := (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n) I).toFinset
  let P : M → Ideal (Poly n) := fun q => q.val
  have hP : ∀ q, P q ∈ I.minimalPrimes := fun q => (Set.Finite.mem_toFinset _).mp q.property
  obtain ⟨b, hb, hsep⟩ := OAI.QuarticPowerFree.minimal_prime_separators I P hP
    Subtype.val_injective
  let q0 : M := ⟨Q, (Set.Finite.mem_toFinset _).mpr hQ⟩
  have hbh : b q0 * h ∈ I := by
    have hrad : I.radical = I := (AffineVariety.vanishingIdeal_isRadical T).radical
    rw [← hrad, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro R hR
    let qR : M := ⟨R, (Set.Finite.mem_toFinset _).mpr hR⟩
    by_cases hq : qR = q0
    · have hRQ : R = Q := congrArg Subtype.val hq
      rw [hRQ]
      exact Ideal.mul_mem_left _ _ hhQ
    · exact Ideal.mul_mem_right _ _ (hsep q0 qR (fun h => hq h.symm))
  have hbI : b q0 ∈ I := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    have := (MvPolynomial.mem_vanishingIdeal_iff.mp hbh) y hy
    rw [map_mul] at this
    exact (mul_eq_zero.mp this).resolve_right (hT y hy)
  exact hb q0 (hQ.1.2 hbI)

/-- Successive cuts through a point lose at most one dimension each. -/
theorem exists_prime_cut {n : ℕ} (x : Point n) :
    ∀ (r : ℕ) (f : Fin r → Poly n) (P0 : Ideal (Poly n)), P0.IsPrime →
      x ∈ MvPolynomial.zeroLocus ℂ P0 → (∀ a, MvPolynomial.aeval x (f a) = 0) →
      ∃ Z : Ideal (Poly n), Z.IsPrime ∧ P0 ≤ Z ∧ (∀ a, f a ∈ Z) ∧
        x ∈ MvPolynomial.zeroLocus ℂ Z ∧
        OAI.QuarticPowerFree.affineDimension P0 ≤ OAI.QuarticPowerFree.affineDimension Z + r := by
  intro r
  induction r with
  | zero =>
      intro f P0 hP0 hx _
      exact ⟨P0, hP0, le_rfl, fun a => a.elim0, hx, by omega⟩
  | succ r ih =>
      intro f P0 hP0 hx hf
      -- one cut by `f 0`
      have hstep : ∃ Z1 : Ideal (Poly n), Z1.IsPrime ∧ P0 ≤ Z1 ∧ f 0 ∈ Z1 ∧
          x ∈ MvPolynomial.zeroLocus ℂ Z1 ∧
          OAI.QuarticPowerFree.affineDimension P0 ≤
            OAI.QuarticPowerFree.affineDimension Z1 + 1 := by
        by_cases hmem : f 0 ∈ P0
        · exact ⟨P0, hP0, le_rfl, hmem, hx, by omega⟩
        · let mx : Ideal (Poly n) := RingHom.ker (MvPolynomial.aeval x : Poly n →ₐ[ℂ] ℂ)
          have hmx : mx.IsPrime := RingHom.ker_isPrime _
          have hle : P0 ⊔ Ideal.span {f 0} ≤ mx := by
            apply sup_le
            · intro q hq
              exact (MvPolynomial.mem_zeroLocus_iff.mp hx) q hq
            · rw [Ideal.span_le, Set.singleton_subset_iff]
              exact hf 0
          obtain ⟨Z1, hZ1, hZ1mx⟩ := Ideal.exists_minimalPrimes_le hle
          have hZ1p : Z1.IsPrime := hZ1.isPrime
          refine ⟨Z1, hZ1p, le_trans le_sup_left hZ1.1.2,
            hZ1.1.2 (le_sup_right (a := P0) (Ideal.mem_span_singleton_self _)), ?_, ?_⟩
          · rw [MvPolynomial.mem_zeroLocus_iff]
            intro q hq
            exact hZ1mx hq
          · rcases Nat.eq_zero_or_eq_succ_pred (OAI.QuarticPowerFree.affineDimension P0)
              with h0 | hs
            · omega
            · have := OAI.QuarticPowerFree.proper_cut_component_dimension P0 Z1 (f 0) hmem hZ1 hs
              omega
      obtain ⟨Z1, hZ1p, hPZ1, hf0, hxZ1, hdim1⟩ := hstep
      obtain ⟨Z, hZp, hZ1Z, hfZ, hxZ, hdim⟩ :=
        ih (fun a => f a.succ) Z1 hZ1p hxZ1 (fun a => hf a.succ)
      refine ⟨Z, hZp, le_trans hPZ1 hZ1Z, ?_, hxZ, by omega⟩
      intro a
      refine Fin.cases ?_ (fun b => ?_) a
      · exact hZ1Z hf0
      · exact hfZ b

/-- The shared dimension of `A[t]`, `A` the coordinate ring of a prime. -/
theorem trdeg_polynomial_quotient {n : ℕ} (P : Ideal (Poly n)) [P.IsPrime] :
    Algebra.trdeg ℂ (Polynomial (Poly n ⧸ P)) =
      (OAI.QuarticPowerFree.affineDimension P : Cardinal) + 1 := by
  have h1 : FaithfulSMul ℂ (Poly n ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective ℂ (Poly n ⧸ P)).mpr (algebraMap ℂ _).injective
  have h2 : FaithfulSMul (Poly n ⧸ P) (Polynomial (Poly n ⧸ P)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Polynomial.C_injective
  have h := trdeg_add_eq ℂ (Poly n ⧸ P) (A := Polynomial (Poly n ⧸ P))
  rw [Polynomial.trdeg_of_isDomain] at h
  rw [← h, ← OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg P _
    (OAI.QuarticPowerFree.coordinateHilbert_eventually P)]
  rfl

theorem finite_roots_of_ne_zero (Θ : MvPolynomial Unit ℂ) (hΘ : Θ ≠ 0) :
    {τ : ℂ | MvPolynomial.aeval (fun _ : Unit => τ) Θ = 0}.Finite := by
  let P : Polynomial ℂ := MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial ℂ)) Θ
  have hP : ∀ τ, P.eval τ = MvPolynomial.aeval (fun _ : Unit => τ) Θ := by
    intro τ
    rw [eval_aeval_polynomial]
    simp
  have hPne : P ≠ 0 := by
    intro h0
    apply hΘ
    apply MvPolynomial.funext
    intro y
    have hy : y = fun _ : Unit => y () := by
      funext u
      rfl
    have := hP (y ())
    rw [h0, Polynomial.eval_zero] at this
    rw [map_zero, ← MvPolynomial.coe_aeval_eq_eval, hy]
    exact this.symm
  apply (Polynomial.finite_setOf_isRoot hPne).subset
  intro τ hτ
  change P.IsRoot τ
  rw [Polynomial.IsRoot, hP]
  exact hτ


theorem alg_aeval {σ B C : Type*} [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]
    (φ : B →ₐ[ℂ] C) (v : σ → B) (q : MvPolynomial σ ℂ) :
    φ (MvPolynomial.aeval v q) = MvPolynomial.aeval (fun s => φ (v s)) q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]

theorem mk_aeval {k : ℕ} {σ : Type*} (I : Ideal (Poly k)) (v : σ → Poly k)
    (q : MvPolynomial σ ℂ) :
    Ideal.Quotient.mk I (MvPolynomial.aeval v q) =
      MvPolynomial.aeval (fun s => Ideal.Quotient.mk I (v s)) q := by
  have := alg_aeval (Ideal.Quotient.mkₐ ℂ I) v q
  simpa only [Ideal.Quotient.mkₐ_eq_mk] using this

theorem eval_aeval {k : ℕ} {σ : Type*} (y : Point k) (v : σ → Poly k) (q : MvPolynomial σ ℂ) :
    MvPolynomial.aeval y (MvPolynomial.aeval v q) =
      MvPolynomial.aeval (fun s => MvPolynomial.aeval y (v s)) q :=
  alg_aeval (MvPolynomial.aeval y) v q

/-- Vanishing on the zero locus of a prime is membership. -/
theorem mem_of_vanishes_on_zeroLocus {k : ℕ} (Z : Ideal (Poly k)) [Z.IsPrime] (q : Poly k)
    (hq : ∀ y ∈ MvPolynomial.zeroLocus ℂ Z, MvPolynomial.aeval y q = 0) : q ∈ Z := by
  have hrad : Z.radical = Z := (Ideal.IsPrime.isRadical inferInstance).radical
  rw [← hrad, ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  exact MvPolynomial.mem_vanishingIdeal_iff.mpr hq

/-! ### Polynomial maps to projective space -/

section Image

variable {n m : ℕ}

/-- The image of a polynomial map to projective space on a principal affine open. -/
def image (X : AffineVariety n) (g : Poly n) (F : Fin m → Poly n) : Set (ProjectivePoint m) :=
  {p | ∃ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 ∧
    ∃ hF : (fun i => MvPolynomial.aeval x (F i)) ≠ 0,
      Projectivization.mk ℂ (fun i => MvPolynomial.aeval x (F i)) hF = p}

/-- The literal fibre over a projective point. -/
def fiber (X : AffineVariety n) (g : Poly n) (F : Fin m → Poly n) (p : ProjectivePoint m) :
    Set (Point n) :=
  {x | x ∈ X.points ∧ MvPolynomial.aeval x g ≠ 0 ∧
    ∃ hF : (fun i => MvPolynomial.aeval x (F i)) ≠ 0,
      Projectivization.mk ℂ (fun i => MvPolynomial.aeval x (F i)) hF = p}

/-- `f ↦ f(t F)` with coefficients in `Poly n`. -/
def scalarPullback (F : Fin m → Poly n) : Poly m →ₐ[ℂ] Polynomial (Poly n) :=
  MvPolynomial.aeval (fun i => Polynomial.X * Polynomial.C (F i))

theorem eval_scalarPullback (F : Fin m → Poly n) (x : Point n) (t : ℂ) (f : Poly m) :
    ((scalarPullback F f).map (MvPolynomial.aeval x).toRingHom).eval t =
      MvPolynomial.aeval (t • (fun i => MvPolynomial.aeval x (F i))) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [scalarPullback]
  | add f h hf hh => simp only [map_add, Polynomial.map_add, Polynomial.eval_add, hf, hh]
  | mul_X f i hf =>
      rw [map_mul, Polynomial.map_mul, Polynomial.eval_mul, hf]
      simp only [scalarPullback, MvPolynomial.aeval_X, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C, map_mul, MvPolynomial.aeval_X, Pi.smul_apply, smul_eq_mul,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] <;> ring

/-- The cone pullback `f ↦ f(t F)` into `(Poly n ⧸ P)[t]`. -/
def conePullback (P : Ideal (Poly n)) (F : Fin m → Poly n) :
    Poly m →ₐ[ℂ] Polynomial (Poly n ⧸ P) :=
  MvPolynomial.aeval (fun i => Polynomial.X * Polynomial.C (Ideal.Quotient.mk P (F i)))

theorem conePullback_eq_map (P : Ideal (Poly n)) (F : Fin m → Poly n) (f : Poly m) :
    conePullback P F f = (scalarPullback F f).map (Ideal.Quotient.mk P) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      simp only [conePullback, scalarPullback, MvPolynomial.aeval_C, Polynomial.algebraMap_apply,
        Polynomial.map_C]
      rfl
  | add f h hf hh => simp only [map_add, Polynomial.map_add, hf, hh]
  | mul_X f i hf =>
      rw [map_mul, map_mul, Polynomial.map_mul, hf]
      simp [conePullback, scalarPullback]

theorem conePullback_X (P : Ideal (Poly n)) (F : Fin m → Poly n) (i : Fin m) :
    conePullback P F (MvPolynomial.X i) =
      Polynomial.X * Polynomial.C (Ideal.Quotient.mk P (F i)) := by
  simp [conePullback]

/-- The homogeneous vanishing ideal of the image is the kernel of the cone pullback. -/
theorem image_vanishingIdeal_eq_ker (X : AffineVariety n) (hX : X.IsIrreducible)
    (g : Poly n) (hg : g ∉ X.ideal) (F : Fin m → Poly n)
    (hF : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 →
      (fun i => MvPolynomial.aeval x (F i)) ≠ 0) :
    ProjectiveVariety.vanishingIdeal (image X g F) = RingHom.ker (conePullback X.ideal F) := by
  ext f
  rw [RingHom.mem_ker, conePullback_eq_map]
  constructor
  · intro hf
    have hcoeff (k : ℕ) : (scalarPullback F f).coeff k ∈ X.ideal := by
      have hgc : g * (scalarPullback F f).coeff k ∈ X.ideal := by
        rw [← X.vanishingIdeal_points]
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        intro x hx
        rw [map_mul]
        by_cases hxg : MvPolynomial.aeval x g = 0
        · rw [hxg, zero_mul]
        · let Pc : Polynomial ℂ :=
            (scalarPullback F f).map (MvPolynomial.aeval x).toRingHom
          have hP : Pc = 0 := by
            apply Polynomial.eq_zero_of_infinite_isRoot
            apply Set.Infinite.mono (s := ({(0 : ℂ)} : Set ℂ)ᶜ)
              ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
            intro t ht
            have ht0 : t ≠ 0 := by simpa using ht
            let w : Point m := fun i => MvPolynomial.aeval x (F i)
            have hw : w ≠ 0 := hF x hx hxg
            have htw : t • w ≠ 0 := smul_ne_zero ht0 hw
            have heq : Projectivization.mk ℂ (t • w) htw = Projectivization.mk ℂ w hw :=
              (Projectivization.mk_eq_mk_iff' ℂ (t • w) w htw hw).2 ⟨t, rfl⟩
            have hp : Projectivization.mk ℂ w hw ∈ image X g F :=
              ⟨x, hx, hxg, hw, rfl⟩
            change Pc.eval t = 0
            rw [eval_scalarPullback]
            exact hf (t • w) ⟨htw, heq.symm ▸ hp⟩
          have hz := congrArg (fun Q : Polynomial ℂ => Q.coeff k) hP
          simp only [Pc, Polynomial.coeff_map, Polynomial.coeff_zero] at hz
          rw [show MvPolynomial.aeval x ((scalarPullback F f).coeff k) = 0 from hz, mul_zero]
      exact (hX.mem_or_mem hgc).resolve_left hg
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcoeff k)
  · intro hf
    rintro w ⟨hw, hp⟩
    obtain ⟨x, hx, hxg, hv, he⟩ := hp
    let v : Point m := fun i => MvPolynomial.aeval x (F i)
    have hcoeff (k : ℕ) : (scalarPullback F f).coeff k ∈ X.ideal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hz := congrArg (fun Q : Polynomial (Poly n ⧸ X.ideal) => Q.coeff k) hf
      simpa using hz
    have hP : (scalarPullback F f).map (MvPolynomial.aeval x).toRingHom = 0 := by
      apply Polynomial.ext
      intro k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      exact hx _ (hcoeff k)
    have he' : Projectivization.mk ℂ w hw = Projectivization.mk ℂ v hv := he.symm
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ w v hw hv).mp he'
    have hz := congrArg (Polynomial.eval t) hP
    simpa only [eval_scalarPullback, Polynomial.eval_zero, ← ht] using hz

theorem exists_point_of_not_mem (X : AffineVariety n) (q : Poly n) (hq : q ∉ X.ideal) :
    ∃ x ∈ X.points, MvPolynomial.aeval x q ≠ 0 := by
  by_contra h
  push_neg at h
  apply hq
  rw [← X.vanishingIdeal_points]
  exact MvPolynomial.mem_vanishingIdeal_iff.mpr h

theorem fiber_proportional (X : AffineVariety n) (g : Poly n) (F : Fin m → Poly n)
    (v : Point m) (hv : v ≠ 0) (y : Point n) (hy : y ∈ fiber X g F (Projectivization.mk ℂ v hv)) :
    ∃ c : ℂ, c ≠ 0 ∧ (fun i => MvPolynomial.aeval y (F i)) = c • v := by
  obtain ⟨_, _, hyF, hmk⟩ := hy
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ hyF hv).mp hmk
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  apply hyF
  rw [← hc, zero_smul]

/-- Generic upper bound: some image point has fibre dimension at most `dim X - r`. -/
theorem fiber_upper_bound (X : AffineVariety n) (hX : X.IsIrreducible) (g : Poly n)
    (hg : g ∉ X.ideal) (F : Fin m → Poly n) (r : ℕ) (j : Fin (r + 1) → Fin m)
    (hj : AlgebraicIndependent ℂ (fun a => (Polynomial.X *
      Polynomial.C (Ideal.Quotient.mk X.ideal (F (j a))) : Polynomial (Poly n ⧸ X.ideal)))) :
    ∃ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 ∧
      ∃ hx : (fun i => MvPolynomial.aeval x (F i)) ≠ 0,
        (AffineVariety.closure (fiber X g F (Projectivization.mk ℂ _ hx))).dimension + r ≤
          X.dimension := by
  classical
  haveI : X.ideal.IsPrime := hX
  set P := X.ideal with hPdef
  set N := X.dimension with hNdef
  have hT : Algebra.trdeg ℂ (Polynomial (Poly n ⧸ P)) = (N : Cardinal) + 1 :=
    trdeg_polynomial_quotient P
  have hrN : r ≤ N := by
    have h := hj.cardinalMk_le_trdeg
    rw [hT, Cardinal.mk_fintype, Fintype.card_fin] at h
    have h' : ((r + 1 : ℕ) : Cardinal) ≤ ((N + 1 : ℕ) : Cardinal) := by
      rw [Nat.cast_add N 1, Nat.cast_one]
      exact h
    have := Nat.cast_le.mp h'
    omega
  set k := N - r with hk
  have hdep : ∀ E : Fin (k + 1) ↪ Fin n, ¬ AlgebraicIndependent ℂ (Sum.elim
      (fun b => (Polynomial.X ^ (fun _ : Fin (k + 1) => (0 : ℕ)) b *
        Polynomial.C (Ideal.Quotient.mk P (MvPolynomial.X (E b))) : Polynomial (Poly n ⧸ P)))
      (fun a => (Polynomial.X * Polynomial.C (Ideal.Quotient.mk P (F (j a))) :
        Polynomial (Poly n ⧸ P)))) := by
    intro E hind
    have h := hind.cardinalMk_le_trdeg
    rw [hT, Cardinal.mk_fintype, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
    have h' : ((k + 1 + (r + 1) : ℕ) : Cardinal) ≤ ((N + 1 : ℕ) : Cardinal) := by
      rw [Nat.cast_add N 1, Nat.cast_one]
      exact h
    have := Nat.cast_le.mp h'
    omega
  choose Φ D hΦhom hΦrel β D' he hene using fun E : Fin (k + 1) ↪ Fin n =>
    exists_generic_coefficient (fun _ : Fin (k + 1) => (0 : ℕ))
      (fun b => Ideal.Quotient.mk P (MvPolynomial.X (E b)))
      (fun a => Ideal.Quotient.mk P (F (j a))) hj (hdep E)
  let e : (Fin (k + 1) ↪ Fin n) → MvPolynomial (Fin (r + 1)) ℂ := fun E =>
    (MvPolynomial.sumAlgEquiv ℂ (Fin (k + 1)) (Fin (r + 1)) (Φ E)).coeff (β E)
  let eP : (Fin (k + 1) ↪ Fin n) → Poly n := fun E =>
    MvPolynomial.aeval (fun a => F (j a)) (e E)
  have heP : ∀ E, eP E ∉ P := by
    intro E hmem
    apply hene E
    have h0 : Ideal.Quotient.mk P (eP E) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [mk_aeval] at h0
    exact h0
  have hj0 : F (j 0) ∉ P := by
    intro hmem
    have h0 := hj.ne_zero 0
    apply h0
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
  let G : Poly n := g * F (j 0) * ∏ E, eP E
  have hG : G ∉ P := by
    intro hmem
    rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h1 | h1
    · rcases Ideal.IsPrime.mem_or_mem inferInstance h1 with h2 | h2
      · exact hg h2
      · exact hj0 h2
    · obtain ⟨E, _, hE⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact heP E hE
  obtain ⟨x, hxX, hxG⟩ := exists_point_of_not_mem X G hG
  simp only [G, map_mul, map_prod] at hxG
  have hxg : MvPolynomial.aeval x g ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hxG)
  have hxj0 : MvPolynomial.aeval x (F (j 0)) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hxG)
  have hxE : ∀ E, MvPolynomial.aeval x (eP E) ≠ 0 := by
    intro E
    exact (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hxG)) E (Finset.mem_univ _)
  set v : Point m := fun i => MvPolynomial.aeval x (F i) with hvdef
  have hv : v ≠ 0 := fun h => hxj0 (congrFun h (j 0))
  refine ⟨x, hxX, hxg, hv, ?_⟩
  change (AffineVariety.closure (fiber X g F (Projectivization.mk ℂ v hv))).dimension + r ≤ N
  suffices hdimk : (AffineVariety.closure (fiber X g F (Projectivization.mk ℂ v hv))).dimension ≤ k by
    omega
  apply dimension_le_of_components
  intro W
  by_contra hW
  push_neg at hW
  set Q := W.val with hQdef
  have hQmin : Q ∈ (MvPolynomial.vanishingIdeal ℂ
      (fiber X g F (Projectivization.mk ℂ v hv))).minimalPrimes := W.property
  haveI hQp : Q.IsPrime := hQmin.isPrime
  have hPQ : P ≤ Q := by
    calc P = MvPolynomial.vanishingIdeal ℂ X.points := X.vanishingIdeal_points.symm
      _ ≤ MvPolynomial.vanishingIdeal ℂ (fiber X g F (Projectivization.mk ℂ v hv)) :=
          MvPolynomial.vanishingIdeal_anti_mono (fun y hy => hy.1)
      _ ≤ Q := hQmin.1.2
  have hj0Q : F (j 0) ∉ Q := by
    apply not_mem_minimalPrimes_of_ne_zero _ _ _ Q hQmin
    intro y hy
    obtain ⟨c, hc, hcv⟩ := fiber_proportional X g F v hv y hy
    have h1 := congrFun hcv (j 0)
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]
    exact mul_ne_zero hc hxj0
  have hlin : ∀ l, MvPolynomial.C (v (j 0)) * F l - MvPolynomial.C (v l) * F (j 0) ∈ Q := by
    intro l
    apply hQmin.1.2
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    obtain ⟨c, _, hcv⟩ := fiber_proportional X g F v hv y hy
    have h1 := congrFun hcv l
    have h2 := congrFun hcv (j 0)
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
    simp only [map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, h1, h2]
    ring
  obtain ⟨J, hJinj, hJind⟩ :=
    OAI.QuarticPowerFree.affineDimension_independent_coordinates Q hQp.ne_top
  have hk1 : k + 1 ≤ OAI.QuarticPowerFree.affineDimension Q := hW
  let E : Fin (k + 1) ↪ Fin n :=
    ⟨fun b => J (Fin.castLE hk1 b), hJinj.comp (Fin.castLE_injective hk1)⟩
  have hEind : AlgebraicIndependent ℂ
      (fun b => Ideal.Quotient.mk Q (MvPolynomial.X (E b))) :=
    hJind.comp _ (Fin.castLE_injective hk1)
  let π : (Poly n ⧸ P) →ₐ[ℂ] Poly n ⧸ Q := Ideal.Quotient.factorₐ ℂ hPQ
  have hrelQ := congrArg π (hΦrel E)
  rw [map_zero, alg_aeval] at hrelQ
  set c : Poly n ⧸ Q := Ideal.Quotient.mk Q (F (j 0)) with hcdef
  have hc : c ≠ 0 := fun h => hj0Q (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hv0 : v (j 0) ≠ 0 := hxj0
  let z : Fin (r + 1) → ℂ := fun a => v (j a) / v (j 0)
  have hFja : ∀ a, Ideal.Quotient.mk Q (F (j a)) = c * algebraMap ℂ (Poly n ⧸ Q) (z a) := by
    intro a
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hlin (j a))
    simp only [map_sub, map_mul, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      at h
    calc Ideal.Quotient.mk Q (F (j a))
        = algebraMap ℂ (Poly n ⧸ Q) ((v (j 0))⁻¹ * v (j 0)) * Ideal.Quotient.mk Q (F (j a)) := by
          rw [inv_mul_cancel₀ hv0, map_one, one_mul]
      _ = algebraMap ℂ (Poly n ⧸ Q) (v (j 0))⁻¹ *
          (algebraMap ℂ (Poly n ⧸ Q) (v (j 0)) * Ideal.Quotient.mk Q (F (j a))) := by
          rw [map_mul, mul_assoc]
      _ = algebraMap ℂ (Poly n ⧸ Q) (v (j 0))⁻¹ *
          (algebraMap ℂ (Poly n ⧸ Q) (v (j a)) * c) := by
          rw [sub_eq_zero.mp h]
      _ = c * algebraMap ℂ (Poly n ⧸ Q) (z a) := by
          simp only [z, div_eq_mul_inv, map_mul]
          ring
  have hfam : (fun s => π (Sum.elim (fun b => Ideal.Quotient.mk P (MvPolynomial.X (E b)))
      (fun a => Ideal.Quotient.mk P (F (j a))) s)) =
      fun s => c ^ (Sum.elim (fun _ : Fin (k + 1) => (0 : ℕ)) (fun _ : Fin (r + 1) => (1 : ℕ)) s) *
        Sum.elim (fun b => Ideal.Quotient.mk Q (MvPolynomial.X (E b)))
          (fun a => algebraMap ℂ (Poly n ⧸ Q) (z a)) s := by
    funext s
    cases s with
    | inl b => simp [π]
    | inr a =>
        simp only [Sum.elim_inr, pow_one]
        rw [← hFja a]
        rfl
  rw [hfam, aeval_scale_of_isWeightedHomogeneous (hΦhom E)] at hrelQ
  have hrel2 := (mul_eq_zero.mp hrelQ).resolve_left (pow_ne_zero _ hc)
  have hfactor : MvPolynomial.aeval (Sum.elim (fun b => Ideal.Quotient.mk Q (MvPolynomial.X (E b)))
      (fun a => algebraMap ℂ (Poly n ⧸ Q) (z a))) (Φ E) =
      MvPolynomial.aeval (fun b => Ideal.Quotient.mk Q (MvPolynomial.X (E b)))
        (MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun a => MvPolynomial.C (z a))) (Φ E)) := by
    rw [alg_aeval]
    refine congrArg (fun φ => MvPolynomial.aeval φ (Φ E)) ?_
    funext s
    cases s with
    | inl b => simp
    | inr a => simp
  rw [hfactor] at hrel2
  have hT0 := (algebraicIndependent_iff.mp hEind) _ hrel2
  rw [aeval_sumElim_X_C] at hT0
  have hcoef := congrArg (fun q : MvPolynomial (Fin (k + 1)) ℂ => q.coeff (β E)) hT0
  simp only [MvPolynomial.coeff_map] at hcoef
  apply hxE E
  have hvj : (fun a => MvPolynomial.aeval x (F (j a))) =
      fun a => (v (j 0)) ^ ((1 : Fin (r + 1) → ℕ) a) * z a := by
    funext a
    simp only [Pi.one_apply, pow_one, z]
    show v (j a) = v (j 0) * (v (j a) / v (j 0))
    field_simp
  change MvPolynomial.aeval x (MvPolynomial.aeval (fun a => F (j a)) (e E)) = 0
  rw [eval_aeval, hvj, aeval_scale_of_isWeightedHomogeneous (he E)]
  have hz0 : MvPolynomial.aeval z (e E) = 0 := by
    simpa [e] using hcoef
  rw [hz0, mul_zero]


/-- Lower bound: some image point has fibre dimension at least `dim X - r`. -/
theorem fiber_lower_bound (X : AffineVariety n) (hX : X.IsIrreducible) (g : Poly n)
    (hg : g ∉ X.ideal) (F : Fin m → Poly n) (r : ℕ) (j : Fin (r + 1) → Fin m)
    (hj : AlgebraicIndependent ℂ (fun a => (Polynomial.X *
      Polynomial.C (Ideal.Quotient.mk X.ideal (F (j a))) : Polynomial (Poly n ⧸ X.ideal))))
    (hdep : ∀ i : Fin m, ¬ AlgebraicIndependent ℂ (Sum.elim
      (fun u : Unit => (Polynomial.X ^ (fun _ : Unit => (1 : ℕ)) u *
        Polynomial.C (Ideal.Quotient.mk X.ideal (F i)) : Polynomial (Poly n ⧸ X.ideal)))
      (fun a => (Polynomial.X * Polynomial.C (Ideal.Quotient.mk X.ideal (F (j a))) :
        Polynomial (Poly n ⧸ X.ideal))))) :
    ∃ p ∈ image X g F,
      X.dimension ≤ (AffineVariety.closure (fiber X g F p)).dimension + r := by
  classical
  haveI : X.ideal.IsPrime := hX
  set P := X.ideal with hPdef
  choose Φ D hΦhom hΦrel β D' he hene using fun i : Fin m =>
    exists_generic_coefficient (fun _ : Unit => (1 : ℕ))
      (fun _ => Ideal.Quotient.mk P (F i))
      (fun a => Ideal.Quotient.mk P (F (j a))) hj (hdep i)
  let e : Fin m → MvPolynomial (Fin (r + 1)) ℂ := fun i =>
    (MvPolynomial.sumAlgEquiv ℂ Unit (Fin (r + 1)) (Φ i)).coeff (β i)
  let eP : Fin m → Poly n := fun i => MvPolynomial.aeval (fun a => F (j a)) (e i)
  have heP : ∀ i, eP i ∉ P := by
    intro i hmem
    apply hene i
    have h0 : Ideal.Quotient.mk P (eP i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [mk_aeval] at h0
    exact h0
  have hj0 : F (j 0) ∉ P := by
    intro hmem
    have h0 := hj.ne_zero 0
    apply h0
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
  let G : Poly n := g * F (j 0) * ∏ i, eP i
  have hG : G ∉ P := by
    intro hmem
    rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h1 | h1
    · rcases Ideal.IsPrime.mem_or_mem inferInstance h1 with h2 | h2
      · exact hg h2
      · exact hj0 h2
    · obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact heP i hi
  obtain ⟨x, hxX, hxG⟩ := exists_point_of_not_mem X G hG
  simp only [G, map_mul, map_prod] at hxG
  have hxg : MvPolynomial.aeval x g ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hxG)
  have hxj0 : MvPolynomial.aeval x (F (j 0)) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hxG)
  have hxE : ∀ i, MvPolynomial.aeval x (eP i) ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hxG)) i (Finset.mem_univ _)
  set v : Point m := fun i => MvPolynomial.aeval x (F i) with hvdef
  have hv : v ≠ 0 := fun h => hxj0 (congrFun h (j 0))
  have hv0 : v (j 0) ≠ 0 := hxj0
  let z : Fin (r + 1) → ℂ := fun a => v (j a) / v (j 0)
  have hz0 : z 0 = 1 := div_self hv0
  -- the cuts
  let f : Fin r → Poly n := fun b =>
    MvPolynomial.C (v (j 0)) * F (j b.succ) - MvPolynomial.C (v (j b.succ)) * F (j 0)
  have hfx : ∀ b, MvPolynomial.aeval x (f b) = 0 := by
    intro b
    simp only [f, map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, v]
    ring
  obtain ⟨Z, hZp, hPZ, hfZ, hxZ, hdimZ⟩ :=
    exists_prime_cut x r f P inferInstance hxX hfx
  haveI : Z.IsPrime := hZp
  -- coefficients do not vanish at the generic normalised point
  have hez : ∀ i, MvPolynomial.aeval z (e i) ≠ 0 := by
    intro i hzero
    apply hxE i
    have hvj : (fun a => MvPolynomial.aeval x (F (j a))) =
        fun a => (v (j 0)) ^ ((1 : Fin (r + 1) → ℕ) a) * z a := by
      funext a
      simp only [Pi.one_apply, pow_one, z]
      show v (j a) = v (j 0) * (v (j a) / v (j 0))
      field_simp
    change MvPolynomial.aeval x (MvPolynomial.aeval (fun a => F (j a)) (e i)) = 0
    rw [eval_aeval, hvj, aeval_scale_of_isWeightedHomogeneous (he i), hzero, mul_zero]
  -- the univariate root sets
  let Θ : Fin m → MvPolynomial Unit ℂ := fun i =>
    MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun a => MvPolynomial.C (z a))) (Φ i)
  have hΘ : ∀ i, Θ i ≠ 0 := by
    intro i h0
    apply hez i
    have hc := congrArg (fun q : MvPolynomial Unit ℂ => q.coeff (β i)) h0
    simp only [Θ, aeval_sumElim_X_C, MvPolynomial.coeff_map] at hc
    simpa [e] using hc
  let Rt : Fin m → Set ℂ := fun i => {τ | MvPolynomial.aeval (fun _ : Unit => τ) (Θ i) = 0}
  have hRt : ∀ i, (Rt i).Finite := fun i => finite_roots_of_ne_zero (Θ i) (hΘ i)
  have hΘeval : ∀ i τ, MvPolynomial.aeval (fun _ : Unit => τ) (Θ i) =
      MvPolynomial.aeval (Sum.elim (fun _ : Unit => τ) z) (Φ i) := by
    intro i τ
    simp only [Θ]
    rw [alg_aeval]
    refine congrArg (fun φ => MvPolynomial.aeval φ (Φ i)) ?_
    funext s
    cases s with
    | inl u => simp
    | inr a => simp
  -- points of the cut map into a finite set of image points
  let pick : Point m → ProjectivePoint m := fun ζ =>
    if h : ζ = 0 then Projectivization.mk ℂ v hv else Projectivization.mk ℂ ζ h
  let Pset : Set (ProjectivePoint m) := pick '' (Set.univ.pi Rt)
  have hPsetfin : Pset.Finite := (Set.Finite.pi (fun i => hRt i)).image pick
  have hyX : ∀ y ∈ MvPolynomial.zeroLocus ℂ Z, y ∈ X.points := by
    intro y hy
    exact MvPolynomial.zeroLocus_anti_mono hPZ hy
  have hPset : ∀ y ∈ MvPolynomial.zeroLocus ℂ Z, MvPolynomial.aeval y (F (j 0)) ≠ 0 →
      ∀ hw : (fun i => MvPolynomial.aeval y (F i)) ≠ 0,
        Projectivization.mk ℂ (fun i => MvPolynomial.aeval y (F i)) hw ∈ Pset := by
    intro y hy hyj hw
    set w : Point m := fun i => MvPolynomial.aeval y (F i) with hwdef
    have hw0 : w (j 0) ≠ 0 := hyj
    let ζ : Point m := (w (j 0))⁻¹ • w
    have hζ0 : ζ (j 0) = 1 := by
      simp only [ζ, Pi.smul_apply, smul_eq_mul]
      exact inv_mul_cancel₀ hw0
    have hζne : ζ ≠ 0 := fun h => by
      have := congrFun h (j 0)
      rw [hζ0] at this
      exact one_ne_zero this
    have hwj : ∀ a, w (j a) = w (j 0) * z a := by
      intro a
      refine Fin.cases ?_ (fun b => ?_) a
      · rw [hz0, mul_one]
      · have hb := (MvPolynomial.mem_zeroLocus_iff.mp hy) _ (hfZ b)
        simp only [f, map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self,
          RingHom.id_apply] at hb
        simp only [z]
        field_simp
        linear_combination hb
    have hwi : ∀ i, w i = w (j 0) * ζ i := by
      intro i
      simp only [ζ, Pi.smul_apply, smul_eq_mul]
      field_simp
    have hroot : ∀ i, ζ i ∈ Rt i := by
      intro i
      change MvPolynomial.aeval (fun _ : Unit => ζ i) (Θ i) = 0
      rw [hΘeval]
      have hrel : MvPolynomial.aeval y
          (MvPolynomial.aeval (Sum.elim (fun _ : Unit => F i) (fun a => F (j a))) (Φ i)) = 0 := by
        apply hyX y hy
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [mk_aeval]
        have hfun : (fun s => Ideal.Quotient.mk X.ideal
            (Sum.elim (fun _ : Unit => F i) (fun a => F (j a)) s)) =
            Sum.elim (fun _ : Unit => Ideal.Quotient.mk P (F i))
              (fun a => Ideal.Quotient.mk P (F (j a))) := by
          funext s
          cases s with
          | inl u => rfl
          | inr a => rfl
        rw [hfun]
        exact hΦrel i
      rw [eval_aeval] at hrel
      have hfam : (fun s => MvPolynomial.aeval y
          (Sum.elim (fun _ : Unit => F i) (fun a => F (j a)) s)) =
          fun s => (w (j 0)) ^ (Sum.elim (fun _ : Unit => (1 : ℕ)) (fun _ : Fin (r + 1) => (1 : ℕ)) s) *
            Sum.elim (fun _ : Unit => ζ i) z s := by
        funext s
        cases s with
        | inl u =>
            simp only [Sum.elim_inl, pow_one]
            exact hwi i
        | inr a =>
            simp only [Sum.elim_inr, pow_one]
            exact hwj a
      rw [hfam, aeval_scale_of_isWeightedHomogeneous (hΦhom i)] at hrel
      exact (mul_eq_zero.mp hrel).resolve_left (pow_ne_zero _ hw0)
    refine ⟨ζ, fun i _ => hroot i, ?_⟩
    simp only [pick, dif_neg hζne]
    apply (Projectivization.mk_eq_mk_iff' ℂ ζ w hζne hw).mpr
    exact ⟨(w (j 0))⁻¹, rfl⟩
  have hgZ : g ∉ Z := fun h => hxg ((MvPolynomial.mem_zeroLocus_iff.mp hxZ) g h)
  have hj0Z : F (j 0) ∉ Z := fun h => hxj0 ((MvPolynomial.mem_zeroLocus_iff.mp hxZ) _ h)
  -- prime avoidance: the cut meets a single fibre
  obtain ⟨p', hp'⟩ : ∃ p' : ProjectivePoint m, ∀ y ∈ MvPolynomial.zeroLocus ℂ Z,
      MvPolynomial.aeval y g ≠ 0 → MvPolynomial.aeval y (F (j 0)) ≠ 0 →
      ∀ hw : (fun i => MvPolynomial.aeval y (F i)) ≠ 0,
        Projectivization.mk ℂ (fun i => MvPolynomial.aeval y (F i)) hw = p' := by
    by_contra hcon
    push_neg at hcon
    let hp : ProjectivePoint m → Fin m → Poly n := fun p' l =>
      MvPolynomial.C (p'.rep (j 0)) * F l - MvPolynomial.C (p'.rep l) * F (j 0)
    have hl : ∀ p' : ProjectivePoint m, ∃ l, hp p' l ∉ Z := by
      intro p'
      obtain ⟨y, hyZ, hyg, hyj, hw, hne⟩ := hcon p'
      by_contra hall
      push_neg at hall
      apply hne
      have hyl : ∀ l, p'.rep (j 0) * MvPolynomial.aeval y (F l) =
          p'.rep l * MvPolynomial.aeval y (F (j 0)) := by
        intro l
        have := (MvPolynomial.mem_zeroLocus_iff.mp hyZ) _ (hall l)
        simp only [hp, map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self,
          RingHom.id_apply] at this
        exact sub_eq_zero.mp this
      have hr0 : p'.rep (j 0) ≠ 0 := by
        intro h0
        apply p'.rep_nonzero
        funext l
        have := hyl l
        rw [h0, zero_mul] at this
        exact (mul_eq_zero.mp this.symm).resolve_right hyj
      conv_rhs => rw [← Projectivization.mk_rep p']
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hw p'.rep_nonzero).mpr
      refine ⟨MvPolynomial.aeval y (F (j 0)) / p'.rep (j 0), ?_⟩
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_eq_iff hr0]
      linear_combination (hyl l).symm
    choose l hl using hl
    let H : Poly n := g * F (j 0) * ∏ p' ∈ hPsetfin.toFinset, hp p' (l p')
    have hHZ : H ∉ Z := by
      intro hmem
      rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h1 | h1
      · rcases Ideal.IsPrime.mem_or_mem inferInstance h1 with h2 | h2
        · exact hgZ h2
        · exact hj0Z h2
      · obtain ⟨p', _, hp'⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
        exact hl p' hp'
    apply hHZ
    apply mem_of_vanishes_on_zeroLocus
    intro y hy
    simp only [H, map_mul, map_prod]
    by_cases hyg : MvPolynomial.aeval y g = 0
    · rw [hyg, zero_mul, zero_mul]
    by_cases hyj : MvPolynomial.aeval y (F (j 0)) = 0
    · rw [hyj, mul_zero, zero_mul]
    have hw : (fun i => MvPolynomial.aeval y (F i)) ≠ 0 := fun h => hyj (congrFun h (j 0))
    have hmemPset := hPset y hy hyj hw
    set q := Projectivization.mk ℂ (fun i => MvPolynomial.aeval y (F i)) hw with hqdef
    have hfac : MvPolynomial.aeval y (hp q (l q)) = 0 := by
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ q.rep
        (fun i => MvPolynomial.aeval y (F i)) q.rep_nonzero hw).mp (by
          rw [Projectivization.mk_rep])
      simp only [hp, map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self,
        RingHom.id_apply]
      rw [← hc]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.prod_eq_zero (hPsetfin.mem_toFinset.mpr hmemPset) hfac, mul_zero]
  -- the chosen fibre
  have hxp' : Projectivization.mk ℂ v hv = p' := hp' x hxZ hxg hxj0 hv
  refine ⟨p', ⟨x, hxX, hxg, hv, hxp'⟩, ?_⟩
  have hIZ : MvPolynomial.vanishingIdeal ℂ (fiber X g F p') ≤ Z := by
    intro q hq
    have hprod : q * (g * F (j 0)) ∈ Z := by
      apply mem_of_vanishes_on_zeroLocus
      intro y hy
      rw [map_mul, map_mul]
      by_cases hyg : MvPolynomial.aeval y g = 0
      · rw [hyg, zero_mul, mul_zero]
      by_cases hyj : MvPolynomial.aeval y (F (j 0)) = 0
      · rw [hyj, mul_zero, mul_zero]
      have hw : (fun i => MvPolynomial.aeval y (F i)) ≠ 0 := fun h => hyj (congrFun h (j 0))
      have hyfib : y ∈ fiber X g F p' := ⟨hyX y hy, hyg, hw, hp' y hy hyg hyj hw⟩
      rw [(MvPolynomial.mem_vanishingIdeal_iff.mp hq) y hyfib, zero_mul]
    rcases Ideal.IsPrime.mem_or_mem inferInstance hprod with h1 | h1
    · exact h1
    · rcases Ideal.IsPrime.mem_or_mem inferInstance h1 with h2 | h2
      · exact absurd h2 hgZ
      · exact absurd h2 hj0Z
  have hmono := affineDimension_mono hIZ
  have hXP : X.dimension = OAI.QuarticPowerFree.affineDimension P := rfl
  change X.dimension ≤ OAI.QuarticPowerFree.affineDimension
    (MvPolynomial.vanishingIdeal ℂ (fiber X g F p')) + r
  omega

/-- Constant-fibre image dimension formula for a polynomial map to projective space. -/
theorem polynomial_projective_image_dimension {d : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (g : Poly n) (hg : g ∉ X.ideal)
    (F : Fin m → Poly n)
    (hF : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 →
      (fun i => MvPolynomial.aeval x (F i)) ≠ 0)
    (hfib : ∀ p ∈ image X g F, (AffineVariety.closure (fiber X g F p)).dimension = d) :
    X.dimension = (ProjectiveVariety.closure (image X g F)).dimension + d := by
  classical
  haveI : X.ideal.IsPrime := hX
  set P := X.ideal with hPdef
  set ψ := conePullback P F with hψdef
  have hker := image_vanishingIdeal_eq_ker X hX g hg F hF
  obtain ⟨x0, hx0X, hx0g⟩ := exists_point_of_not_mem X g hg
  have hS : (image X g F).Nonempty := ⟨_, x0, hx0X, hx0g, hF x0 hx0X hx0g, rfl⟩
  set Y := ProjectiveVariety.closure (image X g F) with hYdef
  have hYne : Y.points.Nonempty := hS.mono (ProjectiveVariety.subset_closure _)
  have hcone := ProjectiveVariety.dimension_cone Y hYne
  have hdimQ : OAI.QuarticPowerFree.affineDimension (RingHom.ker ψ) = Y.dimension + 1 := by
    rw [← hker]
    exact hcone
  set r := Y.dimension with hrdef
  haveI hQp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨j1, _, hj1ind⟩ :=
    OAI.QuarticPowerFree.affineDimension_independent_coordinates (RingHom.ker ψ) hQp.ne_top
  let j : Fin (r + 1) → Fin m := fun a => j1 (Fin.cast hdimQ.symm a)
  have hjind0 : AlgebraicIndependent ℂ
      (fun a => Ideal.Quotient.mk (RingHom.ker ψ) (MvPolynomial.X (j a))) :=
    hj1ind.comp _ (Fin.cast_injective _)
  have hψX : ∀ i, ψ (MvPolynomial.X i) =
      Polynomial.X * Polynomial.C (Ideal.Quotient.mk P (F i)) := fun i => conePullback_X P F i
  have hj : AlgebraicIndependent ℂ (fun a => (Polynomial.X *
      Polynomial.C (Ideal.Quotient.mk P (F (j a))) : Polynomial (Poly n ⧸ P))) := by
    rw [algebraicIndependent_iff]
    intro q hq
    apply (algebraicIndependent_iff.mp hjind0) q
    rw [← mk_aeval]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [RingHom.mem_ker]
    change ψ (MvPolynomial.aeval (fun a => MvPolynomial.X (j a)) q) = 0
    rw [alg_aeval (B := Poly m) (C := Polynomial (Poly n ⧸ P)) ψ]
    simpa only [hψX] using hq
  have hdep : ∀ i : Fin m, ¬ AlgebraicIndependent ℂ (Sum.elim
      (fun u : Unit => (Polynomial.X ^ (fun _ : Unit => (1 : ℕ)) u *
        Polynomial.C (Ideal.Quotient.mk P (F i)) : Polynomial (Poly n ⧸ P)))
      (fun a => (Polynomial.X * Polynomial.C (Ideal.Quotient.mk P (F (j a))) :
        Polynomial (Poly n ⧸ P)))) := by
    intro i hind
    have hpre : AlgebraicIndependent ℂ (Sum.elim
        (fun _ : Unit => Ideal.Quotient.mk (RingHom.ker ψ) (MvPolynomial.X i))
        (fun a => Ideal.Quotient.mk (RingHom.ker ψ) (MvPolynomial.X (j a)))) := by
      rw [algebraicIndependent_iff]
      intro q hq
      apply (algebraicIndependent_iff.mp hind) q
      have hfam : (Sum.elim
          (fun _ : Unit => Ideal.Quotient.mk (RingHom.ker ψ) (MvPolynomial.X i))
          (fun a => Ideal.Quotient.mk (RingHom.ker ψ) (MvPolynomial.X (j a)))) =
          fun s => Ideal.Quotient.mk (RingHom.ker ψ)
            (Sum.elim (fun _ : Unit => (MvPolynomial.X i : Poly m))
              (fun a => MvPolynomial.X (j a)) s) := by
        funext s
        cases s with
        | inl u => rfl
        | inr a => rfl
      rw [hfam, ← mk_aeval, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker,
        alg_aeval (B := Poly m) (C := Polynomial (Poly n ⧸ P)) ψ] at hq
      have hfun2 : (fun s => ψ (Sum.elim (fun _ : Unit => (MvPolynomial.X i : Poly m))
          (fun a => MvPolynomial.X (j a)) s)) =
          Sum.elim (fun u : Unit => (Polynomial.X ^ (fun _ : Unit => (1 : ℕ)) u *
            Polynomial.C (Ideal.Quotient.mk P (F i)) : Polynomial (Poly n ⧸ P)))
            (fun a => Polynomial.X * Polynomial.C (Ideal.Quotient.mk P (F (j a)))) := by
        funext s
        cases s with
        | inl u => simp [hψX]
        | inr a => simp [hψX]
      rw [hfun2] at hq
      exact hq
    have h := hpre.cardinalMk_le_trdeg
    rw [← affineDimension_eq_trdeg, hdimQ, Cardinal.mk_fintype, Fintype.card_sum,
      Fintype.card_unit, Fintype.card_fin, Nat.cast_le] at h
    omega
  obtain ⟨x, hxX, hxg, hx, hup⟩ := fiber_upper_bound X hX g hg F r j hj
  obtain ⟨p, hp, hlow⟩ := fiber_lower_bound X hX g hg F r j hj hdep
  have hd1 := hfib _ ⟨x, hxX, hxg, hx, rfl⟩
  have hd2 := hfib p hp
  rw [hd1] at hup
  rw [hd2] at hlow
  omega

end Image

end GenericFiber

end

end DistinctDistances
