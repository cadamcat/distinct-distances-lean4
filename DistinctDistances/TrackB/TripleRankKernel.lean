import DistinctDistances.TrackB.TripleRankInfra

/-!
(P3) The kernel-bundle recursion via the `x0`-deformation `h_k = (ι_d z)_k − x0 c_k q`.
-/

namespace DistinctDistances.TrackB
namespace TripleRankRoute

set_option autoImplicit false
noncomputable section
open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

noncomputable local instance : AddRightCancelMonoid (Fin 3 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 3 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

section Generic

variable {e : ℕ}

/-- A generic linear form in the directions is a non-zero-divisor modulo the base. -/
theorem exists_generic_q (T : Set (ProjectivePoint e × ProjectivePoint (e + e))) :
    ∃ c : Fin e → ℂ, ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
          MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T) →
        g ∈ MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T) := by
  classical
  set I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T) with hIdef
  let A := Poly (e + (e + e))
  let M := A ⧸ I
  have hfin := associatedPrimes.finite A M
  haveI : Finite (associatedPrimes A M) := hfin.to_subtype
  let L : (Fin e → ℂ) →ₗ[ℂ] A :=
    Fintype.linearCombination ℂ (fun k : Fin e => (MvPolynomial.X (Fin.castAdd (e + e) k) : A))
  have hL : ∀ c : Fin e → ℂ, L c =
      ∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k) := by
    intro c
    simp only [L, Fintype.linearCombination_apply]
    apply Finset.sum_congr rfl
    intro k _
    exact MvPolynomial.smul_eq_C_mul _ _
  let bad : associatedPrimes A M → Submodule ℂ (Fin e → ℂ) :=
    fun P => (P.1.restrictScalars ℂ).comap L
  have hbad : ∀ P, bad P ≠ ⊤ := by
    intro P hP
    obtain ⟨hprime, x, hx⟩ := (isAssociatedPrime_iff).mp P.2
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hdk : ∀ k : Fin e, MvPolynomial.X (Fin.castAdd (e + e) k) * g ∈ I := by
      intro k
      have hk : (Pi.single k (1 : ℂ)) ∈ bad P := by rw [hP]; trivial
      change L (Pi.single k 1) ∈ P.1 at hk
      have hk' : (MvPolynomial.X (Fin.castAdd (e + e) k) : A) ∈ P.1 := by
        simpa [L, Fintype.linearCombination_apply, Pi.single_apply] using hk
      rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot] at hk'
      exact Ideal.Quotient.eq_zero_iff_mem.mp hk'
    have hg : g ∈ I := by
      rw [hIdef, MvPolynomial.mem_vanishingIdeal_iff]
      rintro w ⟨d, p, hd, hp, _, rfl⟩
      obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hd (funext hcon)
      have := MvPolynomial.mem_vanishingIdeal_iff.mp (hdk i) _ ⟨d, p, hd, hp, by assumption, rfl⟩
      rw [map_mul, MvPolynomial.aeval_X] at this
      have hdi : joinPoints d p (Fin.castAdd (e + e) i) = d i := by simp [joinPoints]
      rw [hdi] at this
      exact (mul_eq_zero.mp this).resolve_left hi
    have hzero : (Ideal.Quotient.mk I g : M) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hg
    rw [hzero] at hx
    apply hprime.ne_top
    rw [hx]
    ext r
    simp [Submodule.mem_colon_singleton]
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨c, fun g hg => ?_⟩
  rw [← hL] at hg
  by_contra hgI
  have hzd : L c ∈ {r : A | ∃ x : M, x ≠ 0 ∧ r • x = 0} := by
    refine ⟨Ideal.Quotient.mk I g, ?_, ?_⟩
    · intro h; exact hgI (Ideal.Quotient.eq_zero_iff_mem.mp h)
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr hg
  rw [← biUnion_associatedPrimes_eq_zero_divisors] at hzd
  obtain ⟨P, hP, hcP⟩ := Set.mem_iUnion₂.mp hzd
  exact hc ⟨P, hP⟩ hcP

end Generic


section Extension

theorem splitHom_rename (a c : ℕ) (g : Poly a) :
    splitHom a c (MvPolynomial.rename (Fin.castAdd c) g) = MvPolynomial.C g := by
  have h : (splitHom a c).comp (MvPolynomial.rename (Fin.castAdd c)) =
      IsScalarTower.toAlgHom ℂ (Poly a) (MvPolynomial (Fin c) (Poly a)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [splitHom]
  exact congrArg (fun φ : Poly a →ₐ[ℂ] MvPolynomial (Fin c) (Poly a) => φ g) h

theorem mem_map_rename_iff_split {a c : ℕ} (I : Ideal (Poly a)) (f : Poly (a + c)) :
    f ∈ Ideal.map (MvPolynomial.rename (Fin.castAdd c)) I ↔
      splitHom a c f ∈ Ideal.map (MvPolynomial.C : Poly a →+* MvPolynomial (Fin c) (Poly a)) I := by
  constructor
  · intro hf
    have hle : Ideal.map (MvPolynomial.rename (Fin.castAdd c)) I ≤
        (Ideal.map (MvPolynomial.C : Poly a →+* MvPolynomial (Fin c) (Poly a)) I).comap
          (splitHom a c) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp only [Ideal.mem_comap]
      rw [splitHom_rename]
      exact Ideal.mem_map_of_mem _ hg
    exact hle hf
  · intro hF
    rw [← joinHom_splitHom a c f]
    have hmap := Ideal.mem_map_of_mem (joinHom a c) hF
    rw [Ideal.map_map] at hmap
    have hcomp : (joinHom a c).comp (MvPolynomial.C : Poly a →+* MvPolynomial (Fin c) (Poly a)) =
        (MvPolynomial.rename (Fin.castAdd c)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [joinHom]
      · intro i; simp [joinHom]
    rw [hcomp] at hmap
    exact hmap

/-- A base non-zero-divisor stays one after extension. -/
theorem rename_mul_mem {a c : ℕ} (I : Ideal (Poly a)) (r : Poly a)
    (hr : ∀ g, r * g ∈ I → g ∈ I) (f : Poly (a + c))
    (hf : MvPolynomial.rename (Fin.castAdd c) r * f ∈ Ideal.map (MvPolynomial.rename (Fin.castAdd c)) I) :
    f ∈ Ideal.map (MvPolynomial.rename (Fin.castAdd c)) I := by
  rw [mem_map_rename_iff_split] at hf ⊢
  rw [map_mul, splitHom_rename, MvPolynomial.mem_map_C_iff] at hf
  rw [MvPolynomial.mem_map_C_iff]
  intro m
  have := hf m
  rw [MvPolynomial.coeff_C_mul] at this
  exact hr _ this

/-- A fiber variable is a non-zero-divisor modulo an extended ideal. -/
theorem X_mul_mem {a c : ℕ} (I : Ideal (Poly a)) (k : Fin c) (f : Poly (a + c))
    (hf : MvPolynomial.X (Fin.natAdd a k) * f ∈ Ideal.map (MvPolynomial.rename (Fin.castAdd c)) I) :
    f ∈ Ideal.map (MvPolynomial.rename (Fin.castAdd c)) I := by
  rw [mem_map_rename_iff_split] at hf ⊢
  rw [map_mul, MvPolynomial.mem_map_C_iff] at hf
  rw [MvPolynomial.mem_map_C_iff]
  intro m
  have h1 : splitHom a c (MvPolynomial.X (Fin.natAdd a k)) = MvPolynomial.X k := by
    simp [splitHom]
  have := hf (Finsupp.single k 1 + m)
  rw [h1, MvPolynomial.coeff_X_mul] at this
  exact this

end Extension

section Domain

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- Fiberwise restriction to a base point as a polynomial in the fiber coordinates. -/
def fiberAt (b : Point (e + (e + e))) : TPoly e →+* MvPolynomial (Fin (skewDim e + 1)) ℂ :=
  (MvPolynomial.map (MvPolynomial.aeval b).toRingHom).comp (splitHom (e + (e + e)) (skewDim e + 1)).toRingHom

theorem eval_fiberAt (b : Point (e + (e + e))) (ξ : Point (skewDim e + 1)) (f : TPoly e) :
    MvPolynomial.eval ξ (fiberAt b f) = MvPolynomial.aeval (joinPoints b ξ) f := by
  have := eval_split (e + (e + e)) (skewDim e + 1) b ξ f
  simp only [MvPolynomial.aeval_eq_eval] at this
  exact this

theorem fiberAt_eq_zero_iff (b : Point (e + (e + e))) (f : TPoly e) :
    fiberAt b f = 0 ↔ ∀ ξ, MvPolynomial.aeval (joinPoints b ξ) f = 0 := by
  constructor
  · intro h ξ
    rw [← eval_fiberAt, h, map_zero]
  · intro h
    apply MvPolynomial.funext
    intro ξ
    rw [eval_fiberAt, h, map_zero]

/-- Domain argument: if `ℓ · f` lies in the base and `ℓ` is fiberwise nonzero wherever `r ≠ 0`,
then `r · f` lies in the base. -/
theorem domain_mem (ℓ f r : TPoly e)
    (hℓ : ∀ b ∈ pairRepresentatives (liftedParameterBase C Γ H),
      (∃ ξ, MvPolynomial.aeval (joinPoints b ξ) r ≠ 0) → fiberAt b ℓ ≠ 0)
    (hr : ∀ b : Point (e + (e + e)), ∀ ξ ξ' : Point (skewDim e + 1),
      MvPolynomial.aeval (joinPoints b ξ) r = MvPolynomial.aeval (joinPoints b ξ') r)
    (hf : ℓ * f ∈ baseIdeal C Γ H) : r * f ∈ baseIdeal C Γ H := by
  rw [mem_baseIdeal_iff] at hf ⊢
  intro b hb ξ
  rw [map_mul]
  by_cases hr0 : MvPolynomial.aeval (joinPoints b ξ) r = 0
  · rw [hr0, zero_mul]
  · have hprod : fiberAt b ℓ * fiberAt b f = 0 := by
      rw [← map_mul]
      exact (fiberAt_eq_zero_iff b _).mpr (hf b hb)
    have hfz : fiberAt b f = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (hℓ b hb ⟨ξ, hr0⟩)
    rw [(fiberAt_eq_zero_iff b f).mp hfz ξ, mul_zero]

end Domain

section Deformation

variable {e : ℕ} (C : SkewCoordinates e)

/-- Generic direction linear form `q = Σ c_k d_k`, tridegree `(1,0,0)`. -/
def genQ (c : Fin e → ℂ) : TPoly e :=
  ∑ k, MvPolynomial.C (c k) * dirVar k

/-- Deformed kernel generators `h_k = D_k − x0 c_k q`, tridegree `(1,0,1)`. -/
def genH (c : Fin e → ℂ) (k : Fin e) : TPoly e :=
  dForm C k - ptVar 0 * MvPolynomial.C (c k) * genQ (e := e) c

/-- Chart fiber forms `W_k = (ι_{e_i} z)_k`, linear in `z` (degree `(0,0,1)`). -/
def chartW (i k : Fin e) : TPoly e :=
  ∑ kk : Fin (skewDim e), MvPolynomial.C
    ((((C.decode (Pi.single kk 1)).val (Pi.single i 1)) (Pi.single k 1))) *
    ptVar (Fin.succ kk)

theorem genQ_hom (c : Fin e → ℂ) :
    (genQ (e := e) c).IsWeightedHomogeneous (tw e) (HilbertMulti.tripleDegree 1 0 0) := by
  unfold genQ
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro k _
  have h := (MvPolynomial.isWeightedHomogeneous_C (R := ℂ) (tw e) (c k)).mul
    (dirVar_hom (e := e) k)
  simpa using h

theorem genH_hom (c : Fin e → ℂ) (k : Fin e) :
    (genH C c k).IsWeightedHomogeneous (tw e) (HilbertMulti.tripleDegree 1 0 1) := by
  unfold genH
  apply MvPolynomial.IsWeightedHomogeneous.sub
  · exact dForm_hom C k
  · have h01 : (ptVar (e := e) 0 * MvPolynomial.C (c k)).IsWeightedHomogeneous
        (tw e) (HilbertMulti.tripleDegree 0 0 1) := by
      have h := (ptVar_hom (e := e) 0).mul
        (MvPolynomial.isWeightedHomogeneous_C (R := ℂ) (tw e) (c k))
      simpa using h
    have h := h01.mul (genQ_hom (e := e) c)
    rw [tripleDegree_add] at h
    exact h

theorem chartW_hom (i k : Fin e) :
    (chartW C i k).IsWeightedHomogeneous (tw e) (HilbertMulti.tripleDegree 0 0 1) := by
  unfold chartW
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro kk _
  have h := (MvPolynomial.isWeightedHomogeneous_C (R := ℂ) (tw e)
    ((((C.decode (Pi.single kk 1)).val (Pi.single i 1)) (Pi.single k 1)))).mul
    (ptVar_hom (Fin.succ kk))
  rw [zero_add] at h
  simpa using h

/-- The deformed ideal `J_h = I_BS + (h)`. -/
def defJh (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (c : Fin e → ℂ) : Ideal (TPoly e) :=
  baseIdeal C Γ H ⊔ Ideal.span (Set.range (genH C c))

theorem defJh_hom (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (c : Fin e → ℂ) :
    (defJh C Γ H c).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) :=
  (baseIdeal_hom C Γ H).sup (span_hom (genH C c) _ (genH_hom C c))

/-- `Σ_k d_k D_k = 0` as polynomials (alternating `z(d,d) = 0`), via evaluations. -/
theorem sum_dir_dForm_eq_zero :
    (∑ k : Fin e, dirVar (e := e) k * dForm C k) = 0 := by
  apply MvPolynomial.funext
  intro w
  let b : Point (e + (e + e)) := fun j => w (Fin.castAdd (skewDim e + 1) j)
  let xi : Point (skewDim e + 1) := fun a => w (Fin.natAdd (e + (e + e)) a)
  let d : Point e := fun i => b (Fin.castAdd (e + e) i)
  let p : Point (e + e) := fun j => b (Fin.natAdd e j)
  have hw : w = tj d p xi := by
    funext a
    refine Fin.addCases (fun bl => ?_) (fun kr => ?_) a
    · refine Fin.addCases (fun dl => ?_) (fun pr => ?_) bl
      · simp [tj, joinPoints, d, b]
      · simp [tj, joinPoints, p, b]
    · simp [tj, joinPoints, xi]
  rw [hw]
  simp only [← MvPolynomial.aeval_eq_eval, map_sum, map_mul]
  simp only [eval_dirVar, eval_dForm]
  have hself : (C.decode (Fin.tail xi)).val d d = 0 :=
    (C.decode (Fin.tail xi)).2 d
  have hexp : (∑ k : Fin e, d k * (C.decode (Fin.tail xi)).val d (Pi.single k 1)) =
      (C.decode (Fin.tail xi)).val d d := by
    have hdeq : d = ∑ k : Fin e, d k • (Pi.single k (1 : ℂ) : Point e) := by
      simpa using ((Pi.basisFun ℂ (Fin e)).sum_repr d).symm
    have h1 : (C.decode (Fin.tail xi)).val d d =
        (C.decode (Fin.tail xi)).val d (∑ k : Fin e, d k • (Pi.single k (1 : ℂ) : Point e)) := by
      rw [← hdeq]
    rw [h1, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, smul_eq_mul]
  rw [hexp]
  exact hself

/-- `Σ_k d_k h_k = −x0 q²`. -/
theorem sum_dir_genH (c : Fin e → ℂ) :
    (∑ k : Fin e, dirVar (e := e) k * genH C c k) =
      -(ptVar (e := e) 0 * (genQ (e := e) c) ^ 2) := by
  have hsub : ∀ k : Fin e,
      dirVar (e := e) k * genH C c k =
        dirVar (e := e) k * dForm C k -
        dirVar (e := e) k * (ptVar (e := e) 0 * MvPolynomial.C (c k) * genQ (e := e) c) := by
    intro k
    unfold genH
    ring
  rw [Finset.sum_congr rfl (fun k _ => hsub k), Finset.sum_sub_distrib,
    sum_dir_dForm_eq_zero, zero_sub]
  congr 1
  have hfactor : (∑ k : Fin e,
        dirVar (e := e) k * (ptVar (e := e) 0 * MvPolynomial.C (c k) * genQ (e := e) c)) =
      ptVar (e := e) 0 * (genQ (e := e) c) *
        (∑ k : Fin e, MvPolynomial.C (c k) * dirVar (e := e) k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfactor]
  unfold genQ
  rw [sq]
  ring

/-- `x0 q² ∈ J_h`. -/
theorem x0_mul_qsq_mem (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (c : Fin e → ℂ) :
    ptVar (e := e) 0 * (genQ (e := e) c) ^ 2 ∈ defJh C Γ H c := by
  have hsum : (∑ k : Fin e, dirVar (e := e) k * genH C c k) ∈ defJh C Γ H c := by
    apply Ideal.sum_mem
    intro k _
    have hmem : genH C c k ∈ defJh C Γ H c :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    exact (defJh C Γ H c).mul_mem_left _ hmem
  rw [sum_dir_genH] at hsum
  simpa using hsum

/-- `J_h + (x0) = J_K` as ideals. -/
theorem defJh_add_x0_eq (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (c : Fin e → ℂ) :
    defJh C Γ H c ⊔ Ideal.span ({ptVar (e := e) 0} : Set (TPoly e)) =
      kernelIdeal C Γ H := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · exact le_sup_of_le_left le_sup_left
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        have hD : dForm C k ∈ kernelIdeal C Γ H :=
          Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
        have hx0 : ptVar (e := e) 0 ∈ kernelIdeal C Γ H :=
          Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span rfl))
        have h1 : ptVar (e := e) 0 * MvPolynomial.C (c k) ∈ kernelIdeal C Γ H :=
          (kernelIdeal C Γ H).mul_mem_right _ hx0
        have hterm : ptVar (e := e) 0 * MvPolynomial.C (c k) * genQ (e := e) c ∈
            kernelIdeal C Γ H :=
          (kernelIdeal C Γ H).mul_mem_right _ h1
        have heq : genH C c k = dForm C k - ptVar (e := e) 0 * MvPolynomial.C (c k) *
            genQ (e := e) c := rfl
        rw [heq]
        exact Ideal.sub_mem _ hD hterm
    · rw [Ideal.span_le]
      rintro _ rfl
      exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span rfl))
  · apply sup_le
    · apply sup_le
      · exact le_sup_of_le_left le_sup_left
      · rw [Ideal.span_le]
        rintro _ rfl
        exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      have hh : genH C c k ∈ defJh C Γ H c :=
        Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
      have hh' : genH C c k ∈
          defJh C Γ H c ⊔ Ideal.span ({ptVar (e := e) 0} : Set (TPoly e)) :=
        Ideal.mem_sup_left hh
      have hx0 : ptVar (e := e) 0 ∈
          defJh C Γ H c ⊔ Ideal.span ({ptVar (e := e) 0} : Set (TPoly e)) :=
        Ideal.mem_sup_right (Ideal.subset_span rfl)
      have hterm : ptVar (e := e) 0 * (MvPolynomial.C (c k) * genQ (e := e) c) ∈
          defJh C Γ H c ⊔ Ideal.span ({ptVar (e := e) 0} : Set (TPoly e)) :=
        ((defJh C Γ H c ⊔ Ideal.span ({ptVar (e := e) 0} : Set (TPoly e)))).mul_mem_right _ hx0
      have heq : dForm C k =
          genH C c k + ptVar (e := e) 0 * (MvPolynomial.C (c k) * genQ (e := e) c) := by
        unfold genH
        ring
      rw [heq]
      exact Ideal.add_mem _ hh' hterm

end Deformation

section ChartRanks

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- `J_h + (q²)` (colon target for T1). -/
def defJh2 (c : Fin e → ℂ) : Ideal (TPoly e) :=
  defJh C Γ H c ⊔ Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e))

/-- `J_K + (q²)` (for T2/T3). -/
def defJK2 (c : Fin e → ℂ) : Ideal (TPoly e) :=
  kernelIdeal C Γ H ⊔ Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e))

theorem genQ_sq_hom (c : Fin e → ℂ) :
    ((genQ (e := e) c) ^ 2).IsWeightedHomogeneous (tw e)
      (HilbertMulti.tripleDegree 2 0 0) := by
  rw [pow_two]
  have h := (genQ_hom (e := e) c).mul (genQ_hom (e := e) c)
  rw [tripleDegree_add] at h
  simpa using h

theorem defJh2_hom (c : Fin e → ℂ) :
    (defJh2 C Γ H c).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) := by
  have h0 : (Ideal.span (Set.range (fun _ : Unit => (genQ (e := e) c) ^ 2))).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) :=
    span_hom _ _ (fun _ => genQ_sq_hom (e := e) c)
  have heq : Ideal.span (Set.range (fun _ : Unit => (genQ (e := e) c) ^ 2)) =
      Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) := by
    congr 1
    ext x
    simp
  rw [heq] at h0
  exact (defJh_hom C Γ H c).sup h0

theorem defJK2_hom (c : Fin e → ℂ) :
    (defJK2 C Γ H c).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) := by
  have h0 : (Ideal.span (Set.range (fun _ : Unit => (genQ (e := e) c) ^ 2))).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) :=
    span_hom _ _ (fun _ => genQ_sq_hom (e := e) c)
  have heq : Ideal.span (Set.range (fun _ : Unit => (genQ (e := e) c) ^ 2)) =
      Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) := by
    congr 1
    ext x
    simp
  rw [heq] at h0
  exact (kernelIdeal_hom C Γ H).sup h0

/-- `J_h2 ≤ (J_h : x0)` (since `x0·q² ∈ J_h`). -/
theorem defJh2_le_colon (c : Fin e → ℂ) :
    defJh2 C Γ H c ≤ (defJh C Γ H c).colon {ptVar (e := e) 0} := by
  apply sup_le
  · exact OAI.PiExponentJets.W64.ideal_le_colon_singleton _ _
  · rw [Ideal.span_le]
    rintro _ rfl
    refine Submodule.mem_colon_singleton.mpr ?_
    rw [smul_eq_mul, mul_comm]
    exact x0_mul_qsq_mem C Γ H c

/-- Prefix ideals `J_{<j} = I_BS + (h_k, k<j)` for the CI iteration (T4). -/
def defJprefix (c : Fin e → ℂ) (j : Fin e) : Ideal (TPoly e) :=
  baseIdeal C Γ H ⊔ Ideal.span (genH C c '' {k : Fin e | k < j})

theorem defJprefix_hom (c : Fin e → ℂ) (j : Fin e) :
    (defJprefix C Γ H c j).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) := by
  apply Ideal.IsHomogeneous.sup (baseIdeal_hom C Γ H)
  apply Ideal.homogeneous_span
  rintro _ ⟨k, _, rfl⟩
  exact ⟨_, genH_hom C c k⟩

/-- Degree shift `(s,t,u)+(0,0,1) = (s,t,u+1)`. -/
theorem triple_shift_x0 (s t u : ℕ) :
    HilbertMulti.tripleDegree s t u + HilbertMulti.tripleDegree 0 0 1 =
      HilbertMulti.tripleDegree s t (u + 1) := by
  rw [tripleDegree_add]
  simp

/-- Degree shift `(s,t,u)+(2,0,0) = (s+2,t,u)`. -/
theorem triple_shift_qsq (s t u : ℕ) :
    HilbertMulti.tripleDegree s t u + HilbertMulti.tripleDegree 2 0 0 =
      HilbertMulti.tripleDegree (s + 2) t u := by
  rw [tripleDegree_add]
  simp

/-- Degree shift `(s,t,u)+(1,0,1) for the `h` steps. -/
theorem triple_shift_h (s t u : ℕ) :
    HilbertMulti.tripleDegree s t u + HilbertMulti.tripleDegree 1 0 1 =
      HilbertMulti.tripleDegree (s + 1) t (u + 1) := by
  rw [tripleDegree_add]
  simp

/-- `J_h2 + (x0) = J_K2`. -/
theorem defJh2_add_x0_eq (c : Fin e → ℂ) :
    defJh2 C Γ H c ⊔ Ideal.span ({ptVar (e := e) 0} : Set (TPoly e)) =
      defJK2 C Γ H c := by
  unfold defJh2 defJK2
  have h := defJh_add_x0_eq C Γ H c
  have heq : (defJh C Γ H c ⊔ Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e))) ⊔
      Ideal.span ({ptVar (e := e) 0} : Set (TPoly e)) =
      (defJh C Γ H c ⊔ Ideal.span ({ptVar (e := e) 0} : Set (TPoly e))) ⊔
        Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) := by
    ac_rfl
  rw [heq, h]

/-- `J_h` agrees with the base on point-degree-zero pieces (exact, piece-wise). -/
theorem mem_Jh_iff_base_zero (c : Fin e → ℂ) (s t : ℕ) (f : TPoly e)
    (hf : f ∈ piece e s t 0) : f ∈ defJh C Γ H c ↔ f ∈ baseIdeal C Γ H := by
  constructor
  · intro h
    have hvan : ∀ g ∈ defJh C Γ H c, ∀ b ∈ pairRepresentatives (liftedParameterBase C Γ H),
        MvPolynomial.aeval (joinPoints b (0 : Point (skewDim e + 1))) g = 0 := by
      intro g hg b hb
      have hle : defJh C Γ H c ≤ MvPolynomial.vanishingIdeal ℂ
          {w | ∃ b ∈ pairRepresentatives (liftedParameterBase C Γ H),
            w = joinPoints b (0 : Point (skewDim e + 1))} := by
        apply sup_le
        · intro g hg
          rw [MvPolynomial.mem_vanishingIdeal_iff]
          rintro _ ⟨b, hb, rfl⟩
          exact (mem_baseIdeal_iff C Γ H g).mp hg b hb 0
        · rw [Ideal.span_le]
          rintro _ ⟨k, rfl⟩
          rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_iff]
          rintro _ ⟨b, hb', rfl⟩
          obtain ⟨d, p, _, _, _, rfl⟩ := hb'
          change MvPolynomial.aeval (tj d p 0) (genH C c k) = 0
          unfold genH genQ
          simp only [map_sub, map_mul, map_sum, MvPolynomial.aeval_C,
            eval_ptVar, eval_dirVar, eval_dForm]
          have hx0 : (0 : Point (skewDim e + 1)) 0 = (0 : ℂ) := rfl
          rw [hx0, zero_mul, zero_mul, sub_zero]
          have htail : Fin.tail (0 : Point (skewDim e + 1)) = 0 := rfl
          rw [htail]
          simp
      exact MvPolynomial.mem_vanishingIdeal_iff.mp (hle hg) _ ⟨b, hb, rfl⟩
    rw [mem_baseIdeal_iff]
    intro b hb ξ
    rw [eval_ptdeg_zero f s t hf b ξ 0]
    exact hvan f h b hb
  · intro h
    exact Ideal.mem_sup_left h

/-- `J_h` agrees with the base on point-degree-zero pieces (exact). -/
theorem defJh_degree_zero (c : Fin e → ℂ) (s t : ℕ) :
    secRank (defJh C Γ H c) s t 0 = secRank (baseIdeal C Γ H) s t 0 := by
  symm
  apply secRank_eq_of_piece
  intro f hf
  exact (mem_Jh_iff_base_zero C Γ H c s t f hf).symm

/-- Nat-indexed prefix `J_{<m}`. -/
def defJprefixNat (c : Fin e → ℂ) (m : ℕ) : Ideal (TPoly e) :=
  baseIdeal C Γ H ⊔ Ideal.span (genH C c '' {k : Fin e | k.val < m})

theorem prefixNat_zero (c : Fin e → ℂ) :
    defJprefixNat C Γ H c 0 = baseIdeal C Γ H := by
  have hempty : {k : Fin e | k.val < 0} = ∅ := by
    ext k
    simp
  unfold defJprefixNat
  rw [hempty, Set.image_empty, Ideal.span_empty, sup_bot_eq]

theorem prefixNat_succ (c : Fin e → ℂ) (m : ℕ) (hm : m < e) :
    defJprefixNat C Γ H c (m + 1) =
      defJprefixNat C Γ H c m ⊔ Ideal.span ({genH C c ⟨m, hm⟩} : Set (TPoly e)) := by
  have hset : {k : Fin e | k.val < m + 1} = {k : Fin e | k.val < m} ∪ {⟨m, hm⟩} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases heq : k.val = m
      · right
        exact Fin.ext heq
      · left
        omega
    · rintro (h | rfl)
      · omega
      · exact Nat.lt_succ_self m
  unfold defJprefixNat
  rw [hset, Set.image_union, Set.image_singleton, Ideal.span_union]
  ac_rfl

theorem prefixNat_ge (c : Fin e → ℂ) (m : ℕ) (hm : e ≤ m) :
    defJprefixNat C Γ H c m = defJh C Γ H c := by
  have huniv : {k : Fin e | k.val < m} = Set.univ := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    calc k.val < e := k.isLt
      _ ≤ m := hm
  unfold defJprefixNat defJh
  rw [huniv, Set.image_univ]

theorem prefixNat_eq_FinPrefix (c : Fin e → ℂ) (j : Fin e) :
    defJprefixNat C Γ H c j.val = defJprefix C Γ H c j := by
  have hset : {k : Fin e | k.val < j.val} = {k : Fin e | k < j} := by
    ext k
    simp
  unfold defJprefixNat defJprefix
  rw [hset]

theorem defJprefixNat_hom (c : Fin e → ℂ) (m : ℕ) :
    (defJprefixNat C Γ H c m).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) := by
  apply Ideal.IsHomogeneous.sup (baseIdeal_hom C Γ H)
  apply Ideal.homogeneous_span
  rintro _ ⟨k, _, rfl⟩
  exact ⟨_, genH_hom C c k⟩

/-- All nat prefixes agree with the base at `u = 0` (exact, all `h` vanish on `x = 0`). -/
theorem prefixNat_degree_zero (c : Fin e → ℂ) (m : ℕ) (s t : ℕ) :
    secRank (defJprefixNat C Γ H c m) s t 0 = secRank (baseIdeal C Γ H) s t 0 := by
  symm
  apply secRank_eq_of_piece
  intro f hf
  constructor
  · intro h
    exact Ideal.mem_sup_left h
  · intro h
    have hvan : ∀ g ∈ defJprefixNat C Γ H c m,
        ∀ b ∈ pairRepresentatives (liftedParameterBase C Γ H),
        MvPolynomial.aeval (joinPoints b (0 : Point (skewDim e + 1))) g = 0 := by
      intro g hg b hb
      have hle : defJprefixNat C Γ H c m ≤ MvPolynomial.vanishingIdeal ℂ
          {w | ∃ b ∈ pairRepresentatives (liftedParameterBase C Γ H),
            w = joinPoints b (0 : Point (skewDim e + 1))} := by
        apply sup_le
        · intro g hg
          rw [MvPolynomial.mem_vanishingIdeal_iff]
          rintro _ ⟨b, hb, rfl⟩
          exact (mem_baseIdeal_iff C Γ H g).mp hg b hb 0
        · rw [Ideal.span_le]
          rintro _ ⟨k, _, rfl⟩
          rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_iff]
          rintro _ ⟨b, hb', rfl⟩
          obtain ⟨d, p, _, _, _, rfl⟩ := hb'
          change MvPolynomial.aeval (tj d p 0) (genH C c k) = 0
          unfold genH genQ
          simp only [map_sub, map_mul, map_sum, MvPolynomial.aeval_C,
            eval_ptVar, eval_dirVar, eval_dForm]
          have hx0 : (0 : Point (skewDim e + 1)) 0 = (0 : ℂ) := rfl
          rw [hx0, zero_mul, zero_mul, sub_zero]
          have htail : Fin.tail (0 : Point (skewDim e + 1)) = 0 := rfl
          rw [htail]
          simp
      exact MvPolynomial.mem_vanishingIdeal_iff.mp (hle hg) _ ⟨b, hb, rfl⟩
    rw [mem_baseIdeal_iff]
    intro b hb ξ
    rw [eval_ptdeg_zero f s t hf b ξ 0]
    exact hvan f h b hb

/-- Pair direction form `q₀` whose rename is `genQ`. -/
def pairQ0 (c : Fin e → ℂ) : Poly (e + (e + e)) :=
  ∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)

theorem rename_pairQ0 (c : Fin e → ℂ) :
    MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (pairQ0 (e := e) c) =
      genQ (e := e) c := by
  unfold pairQ0 genQ dirVar
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]

/-- `genQ` is a non-zero-divisor modulo the base (exact, via generic `c`). -/
theorem base_nzd_genQ (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)))
    (f : TPoly e)
    (hf : genQ (e := e) c * f ∈ baseIdeal C Γ H) :
    f ∈ baseIdeal C Γ H := by
  have hbase : baseIdeal C Γ H =
      Ideal.map (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)))
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H))) := rfl
  have hgen : genQ (e := e) c =
      MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (pairQ0 (e := e) c) := by
    rw [rename_pairQ0]
  rw [hbase, hgen] at hf
  have hr : ∀ g, pairQ0 (e := e) c * g ∈
      MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)) := by
    intro g hg
    have hg' : (∑ k, MvPolynomial.C (c k) *
        MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) := by
      unfold pairQ0 at hg
      exact hg
    exact hc g hg'
  exact rename_mul_mem _ _ hr _ hf

/-- `(base : q²) = base` exactly (via generic `q` nzd). -/
theorem base_colon_qsq_eq (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H))) :
    (baseIdeal C Γ H).colon {genQ (e := e) c ^ 2} = baseIdeal C Γ H := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hf
    have heq1 : genQ (e := e) c * (genQ (e := e) c * f) = f * (genQ (e := e) c ^ 2) := by
      ring
    have h1 : genQ (e := e) c * (genQ (e := e) c * f) ∈ baseIdeal C Γ H := by
      rw [heq1]
      exact hf
    have h_qf : genQ (e := e) c * f ∈ baseIdeal C Γ H :=
      base_nzd_genQ C Γ H c hc _ h1
    exact base_nzd_genQ C Γ H c hc _ h_qf
  · exact OAI.PiExponentJets.W64.ideal_le_colon_singleton _ _

/-- Exact rank step for `base+(q²)` (no torsion, `q` generic). -/
theorem base_add_qsq_rank (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)))
    (s t u : ℕ) :
    secRank (baseIdeal C Γ H ⊔ Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)))
      (s + 2) t u + secRank (baseIdeal C Γ H) s t u =
      secRank (baseIdeal C Γ H) (s + 2) t u := by
  have heq := triple_shift_qsq s t u
  have hstep := HilbertMulti.colon_rank_step (tw e) (baseIdeal C Γ H)
    (baseIdeal_hom C Γ H) ((genQ (e := e) c) ^ 2) (genQ_sq_hom (e := e) c)
    (HilbertMulti.tripleDegree s t u)
  rw [heq, base_colon_qsq_eq C Γ H c hc] at hstep
  have hJK : Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) ⊔ baseIdeal C Γ H =
      baseIdeal C Γ H ⊔ Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) := by
    rw [sup_comm]
  rw [hJK] at hstep
  simp only [secRank] at hstep ⊢
  exact hstep

/-- Pascal nat shift `s'+1-(k+1) = s'-k` (no truncation when `k+1 ≤ s'+1`). -/
theorem pascal_shift_succ_nat (s' k : ℕ) (hk : k + 1 ≤ s' + 1) :
    s' + 1 - (k + 1) = s' - k := by
  omega

/-- Pascal int shift `u'+1-(k+1) = u'-k` (ints, no truncation). -/
theorem pascal_shift_succ_int (u' k : ℕ) :
    (((u' + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ)) = (((u' : ℕ) : ℤ) - (k : ℤ)) := by
  push_cast
  ring

/-- Pascal choose `C(m+1,k+1) = C(m,k)+C(m,k+1)` (cast to ℤ). -/
theorem pascal_choose_succ (m k : ℕ) :
    (((m + 1).choose (k + 1) : ℕ) : ℤ) =
      ((m.choose k : ℕ) : ℤ) + ((m.choose (k + 1) : ℕ) : ℤ) := by
  have h := Nat.choose_succ_succ m k
  exact_mod_cast h

/-- Sign `(-1)^{k+1} = -(-1)^k`. -/
theorem pascal_neg_one_succ (k : ℕ) : (-1 : ℤ) ^ (k + 1) = -(-1 : ℤ) ^ k := by
  rw [pow_succ]
  ring

/-- Alternating Pascal recursion for `Σ (-1)^k C(m+1,k) F k`. -/
theorem alt_pascal (F : ℕ → ℤ) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1 + 1), (-1 : ℤ) ^ k * ((m + 1).choose k : ℤ) * F k) =
      (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (m.choose k : ℤ) * F k) -
      (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (m.choose k : ℤ) * F (k + 1)) := by
  have h1 : (∑ k ∈ Finset.range (m + 1 + 1), (-1 : ℤ) ^ k * ((m + 1).choose k : ℤ) * F k) =
      F 0 + ∑ k ∈ Finset.range (m + 1), ((-1 : ℤ) ^ (k + 1) * (m.choose k : ℤ) * F (k + 1) +
        (-1 : ℤ) ^ (k + 1) * (m.choose (k + 1) : ℤ) * F (k + 1)) := by
    rw [Finset.sum_range_succ', add_comm]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro k _
      rw [Nat.choose_succ_succ]
      push_cast
      ring
  have h2 : (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (m.choose k : ℤ) * F k) =
      F 0 + ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (k + 1) * (m.choose (k + 1) : ℤ) * F (k + 1) := by
    rw [Finset.sum_range_succ (fun k => (-1 : ℤ) ^ (k + 1) * (m.choose (k + 1) : ℤ) * F (k + 1)),
      Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [Finset.sum_range_succ', add_comm]
    simp
  rw [h1, h2, Finset.sum_add_distrib]
  have h3 : (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (k + 1) * (m.choose k : ℤ) * F (k + 1)) =
      -∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (m.choose k : ℤ) * F (k + 1) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h3]
  ring

/-- `J_h2` at `u = 0` equals `base+(q²)` at `u = 0` (exact, via `J_h`/`base` + `q²`). -/
theorem Jh2_degree_zero_eq (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)))
    (s t : ℕ) :
    secRank (defJh2 C Γ H c) s t 0 =
      secRank (baseIdeal C Γ H ⊔ Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e))) s t 0 := by
  by_cases hs : s < 2
  · -- `q²` (degree `(2,0,0)`) does not affect `s < 2` pieces
    have hle : ¬ HilbertMulti.tripleDegree 2 0 0 ≤ HilbertMulti.tripleDegree s t 0 := by
      intro hle
      have h0 : (HilbertMulti.tripleDegree 2 0 0 : Fin 3 →₀ ℕ) 0 ≤
          (HilbertMulti.tripleDegree s t 0 : Fin 3 →₀ ℕ) 0 := hle 0
      simp [HilbertMulti.tripleDegree] at h0
      omega
    have hJh2 : secRank (defJh2 C Γ H c) s t 0 = secRank (defJh C Γ H c) s t 0 := by
      have hstep := HilbertMulti.section_rank_step_of_not_le
        (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) (defJh C Γ H c)
        (defJh_hom C Γ H c) ((genQ (e := e) c) ^ 2) (genQ_sq_hom (e := e) c)
        (fun h => hle h)
      have heq : Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) ⊔ defJh C Γ H c =
          defJh2 C Γ H c := by
        unfold defJh2
        rw [sup_comm]
      rw [heq] at hstep
      simp only [secRank, tw] at hstep ⊢
      exact hstep
    have hbase : secRank (baseIdeal C Γ H ⊔
        Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e))) s t 0 =
        secRank (baseIdeal C Γ H) s t 0 := by
      have hstep := HilbertMulti.section_rank_step_of_not_le
        (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) (baseIdeal C Γ H)
        (baseIdeal_hom C Γ H) ((genQ (e := e) c) ^ 2) (genQ_sq_hom (e := e) c)
        (fun h => hle h)
      have heq : Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) ⊔ baseIdeal C Γ H =
          baseIdeal C Γ H ⊔ Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) := by
        rw [sup_comm]
      rw [heq] at hstep
      simp only [secRank, tw] at hstep ⊢
      exact hstep
    rw [hJh2, hbase, defJh_degree_zero]
  · -- `s ≥ 2`: both satisfy the same `q²` colon recurrence with matching base data
    push Not at hs
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
    have heq_shift := triple_shift_qsq s' t 0
    have hstepJh := HilbertMulti.colon_rank_step (tw e) (defJh C Γ H c)
      (defJh_hom C Γ H c) ((genQ (e := e) c) ^ 2) (genQ_sq_hom (e := e) c)
      (HilbertMulti.tripleDegree s' t 0)
    rw [heq_shift] at hstepJh
    have hJK_Jh : Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) ⊔ defJh C Γ H c =
        defJh2 C Γ H c := by
      unfold defJh2
      rw [sup_comm]
    rw [hJK_Jh] at hstepJh
    have hcolJh : secRank ((defJh C Γ H c).colon {genQ (e := e) c ^ 2}) s' t 0 =
        secRank (defJh C Γ H c) s' t 0 := by
      symm
      apply secRank_eq_of_piece
      intro f hf
      constructor
      · intro h
        exact OAI.PiExponentJets.W64.ideal_le_colon_singleton _ _ h
      · intro h
        rw [Submodule.mem_colon_singleton, smul_eq_mul] at h
        have hmem : f * (genQ (e := e) c ^ 2) ∈ baseIdeal C Γ H := by
          have hJh : f * (genQ (e := e) c ^ 2) ∈ defJh C Γ H c := h
          have hf' : f.IsWeightedHomogeneous (tw e) (HilbertMulti.tripleDegree s' t 0) := hf
          have hq := genQ_sq_hom (e := e) c
          have hmul := hf'.mul hq
          rw [triple_shift_qsq] at hmul
          have hpiece : f * (genQ (e := e) c ^ 2) ∈ piece e (s' + 2) t 0 := hmul
          exact (mem_Jh_iff_base_zero C Γ H c (s' + 2) t _ hpiece).mp hJh
        have hbase_mem : f ∈ baseIdeal C Γ H := by
          have hcol := base_colon_qsq_eq C Γ H c hc
          have hmem_colon : f ∈ (baseIdeal C Γ H).colon {genQ (e := e) c ^ 2} := by
            rw [Submodule.mem_colon_singleton, smul_eq_mul]
            exact hmem
          rw [hcol] at hmem_colon
          exact hmem_colon
        exact (mem_Jh_iff_base_zero C Γ H c s' t f hf).mpr hbase_mem
    have hstepBase := HilbertMulti.colon_rank_step (tw e) (baseIdeal C Γ H)
      (baseIdeal_hom C Γ H) ((genQ (e := e) c) ^ 2) (genQ_sq_hom (e := e) c)
      (HilbertMulti.tripleDegree s' t 0)
    rw [heq_shift, base_colon_qsq_eq C Γ H c hc] at hstepBase
    have hJK_base : Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) ⊔ baseIdeal C Γ H =
        baseIdeal C Γ H ⊔ Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) := by
      rw [sup_comm]
    rw [hJK_base] at hstepBase
    have hJh_eq : secRank (defJh C Γ H c) (s' + 2) t 0 = secRank (baseIdeal C Γ H) (s' + 2) t 0 :=
      defJh_degree_zero C Γ H c _ _
    have hJh_eq' : secRank (defJh C Γ H c) s' t 0 = secRank (baseIdeal C Γ H) s' t 0 :=
      defJh_degree_zero C Γ H c _ _
    simp only [secRank] at hstepJh hstepBase hcolJh hJh_eq hJh_eq' ⊢
    omega

end ChartRanks

end
end TripleRankRoute
end DistinctDistances.TrackB
