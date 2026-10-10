import DistinctDistances.TrackB.TripleRankKernel

/-!
Chart substitutions `ψ_K` for the `d_i`-torsion statements of (P3).

`ψ = psiHom c i K` fixes the base variables and sends `x0 ↦ d_i x0`,
`z ↦ d_i z − Σ_{k ∈ K} h_k · (e_i^* ∧ e_k^*)`.  It agrees with the `d_i`-scaling of the
point variables modulo `(h_k : k ∈ K)` and kills `h_k` for `k ∈ K`, `k ≠ i`.
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

section Chart

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- Pointwise value of `h_k`. -/
def hval (c : Fin e → ℂ) (d : Point e) (ξ : Point (skewDim e + 1)) (k : Fin e) : ℂ :=
  (C.decode (Fin.tail ξ)).val d (Pi.single k 1) - ξ 0 * c k * ∑ j, c j * d j

theorem eval_genH (c : Fin e → ℂ) (d : Point e) (p : Point (e + e))
    (ξ : Point (skewDim e + 1)) (k : Fin e) :
    MvPolynomial.aeval (tj d p ξ) (genH C c k) = hval C c d ξ k := by
  unfold genH genQ hval
  simp only [map_sub, map_mul, map_sum, MvPolynomial.aeval_C, eval_ptVar, eval_dirVar,
    eval_dForm, Algebra.algebraMap_self, RingHom.id_apply]

theorem eval_genQ (c : Fin e → ℂ) (d : Point e) (p : Point (e + e))
    (ξ : Point (skewDim e + 1)) :
    MvPolynomial.aeval (tj d p ξ) (genQ (e := e) c) = ∑ j, c j * d j := by
  unfold genQ
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, eval_dirVar, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem sum_hval (c : Fin e → ℂ) (d : Point e) (ξ : Point (skewDim e + 1)) :
    (∑ k, d k * hval C c d ξ k) = -(ξ 0 * (∑ j, c j * d j) ^ 2) := by
  have h := congrArg (MvPolynomial.aeval (tj d (0 : Point (e + e)) ξ)) (sum_dir_genH C c)
  simp only [map_sum, map_mul, map_neg, map_pow, eval_dirVar, eval_genH, eval_ptVar,
    eval_genQ] at h
  exact h

/-- Polynomial identity from pointwise identity at joined points. -/
theorem tpoly_ext (f g : TPoly e)
    (h : ∀ (d : Point e) (p : Point (e + e)) (ξ : Point (skewDim e + 1)),
      MvPolynomial.aeval (tj d p ξ) f = MvPolynomial.aeval (tj d p ξ) g) : f = g := by
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
  simp only [← MvPolynomial.aeval_eq_eval]
  exact h d p xi

/-- The chart substitution `ψ_K`. -/
def psiHom (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) : TPoly e →ₐ[ℂ] TPoly e :=
  MvPolynomial.aeval (fun a : Fin (e + (e + e) + (skewDim e + 1)) =>
    Fin.addCases (fun b => MvPolynomial.X (Fin.castAdd (skewDim e + 1) b))
      (fun k : Fin (skewDim e + 1) => Fin.cases (dirVar i * ptVar 0)
        (fun kk => dirVar i * ptVar (Fin.succ kk) -
          ∑ k' ∈ K, MvPolynomial.C (alphaC C i kk k') * genH C c k') k) a)

/-- The substituted fiber vector. -/
def psiVec (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) (d : Point e)
    (ξ : Point (skewDim e + 1)) : Point (skewDim e + 1) :=
  Fin.cons (d i * ξ 0) (d i • Fin.tail ξ - ∑ k' ∈ K, (hval C c d ξ k') •
    C.decode.symm (anchAlt (LinearMap.proj i) (LinearMap.proj k')))

theorem psi_eval (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) (d : Point e)
    (p : Point (e + e)) (ξ : Point (skewDim e + 1)) (f : TPoly e) :
    MvPolynomial.aeval (tj d p ξ) (psiHom C c i K f) =
      MvPolynomial.aeval (tj d p (psiVec C c i K d ξ)) f := by
  unfold psiHom
  rw [MvPolynomial.comp_aeval_apply]
  congr 1
  congr 1
  funext a
  refine Fin.addCases (fun b => ?_) (fun k => ?_) a
  · simp [tj, joinPoints]
  · refine Fin.cases ?_ (fun kk => ?_) k
    · simp only [Fin.addCases_right, Fin.cases_zero, map_mul, eval_dirVar, eval_ptVar]
      simp [tj, joinPoints, psiVec]
    · simp only [Fin.addCases_right, Fin.cases_succ, map_sub, map_mul, map_sum,
        MvPolynomial.aeval_C, eval_dirVar, eval_ptVar, eval_genH, Algebra.algebraMap_self,
        RingHom.id_apply]
      simp [tj, joinPoints, psiVec, alphaC, Fin.tail, Finset.sum_apply, mul_comm]

theorem hval_psiVec (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) (d : Point e)
    (ξ : Point (skewDim e + 1)) (k : Fin e) :
    hval C c d (psiVec C c i K d ξ) k = d i * hval C c d ξ k -
      ∑ k' ∈ K, hval C c d ξ k' *
        (d i * (if k' = k then 1 else 0) - d k' * (if i = k then 1 else 0)) := by
  have htail : Fin.tail (psiVec C c i K d ξ) = d i • Fin.tail ξ - ∑ k' ∈ K,
      (hval C c d ξ k') • C.decode.symm (anchAlt (LinearMap.proj i) (LinearMap.proj k')) := by
    funext k; simp [psiVec, Fin.tail]
  have h0 : psiVec C c i K d ξ 0 = d i * ξ 0 := by simp [psiVec]
  have hk : hval C c d ξ k = (C.decode (Fin.tail ξ)).val d (Pi.single k 1) -
      ξ 0 * c k * ∑ j, c j * d j := rfl
  rw [show hval C c d (psiVec C c i K d ξ) k =
      (C.decode (Fin.tail (psiVec C c i K d ξ))).val d (Pi.single k 1) -
        psiVec C c i K d ξ 0 * c k * ∑ j, c j * d j from rfl, htail, h0, hk]
  simp only [map_sub, map_smul, map_sum, LinearEquiv.apply_symm_apply, Submodule.coe_sub,
    Submodule.coe_smul, Submodule.coe_sum, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul]
  simp only [anchAlt, IncidenceLocal.anchoredForm, LinearMap.sub_apply,
    LinearMap.BilinForm.linMulLin_apply, LinearMap.proj_apply, Pi.single_apply]
  ring

theorem psi_genH_ne (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) (k : Fin e) (hk : k ≠ i) :
    psiHom C c i K (genH C c k) = if k ∈ K then 0 else dirVar i * genH C c k := by
  apply tpoly_ext
  intro d p ξ
  rw [psi_eval, eval_genH, hval_psiVec]
  have hs : (∑ k' ∈ K, hval C c d ξ k' *
      (d i * (if k' = k then 1 else 0) - d k' * (if i = k then 1 else 0))) =
      if k ∈ K then hval C c d ξ k * d i else 0 := by
    rw [← Finset.sum_ite_eq' K k (fun k' => hval C c d ξ k' * d i)]
    apply Finset.sum_congr rfl
    intro k' _
    have hik : ¬ i = k := fun h => hk h.symm
    simp only [hik, if_false, mul_zero, sub_zero]
    split_ifs <;> ring
  rw [hs]
  by_cases hkK : k ∈ K
  · simp only [hkK, if_true, map_zero]
    ring
  · simp only [hkK, if_false, map_mul, eval_dirVar, eval_genH]
    ring

theorem psi_genH_self (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) :
    psiHom C c i K (genH C c i) = ∑ l ∈ insert i K, dirVar l * genH C c l := by
  apply tpoly_ext
  intro d p ξ
  rw [psi_eval, eval_genH, hval_psiVec]
  simp only [map_sum, map_mul, eval_dirVar, eval_genH, ite_true, mul_one]
  have hs : (∑ k' ∈ K, hval C c d ξ k' *
      (d i * (if k' = i then 1 else 0) - d k')) =
      (if i ∈ K then hval C c d ξ i * d i else 0) - ∑ k' ∈ K, d k' * hval C c d ξ k' := by
    rw [← Finset.sum_ite_eq' K i (fun k' => hval C c d ξ k' * d i), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k' _
    split_ifs <;> ring
  rw [hs]
  by_cases hiK : i ∈ K
  · rw [Finset.insert_eq_of_mem hiK, if_pos hiK]
    ring
  · rw [Finset.sum_insert hiK, if_neg hiK]
    ring

theorem psi_genH_univ_self (c : Fin e → ℂ) (i : Fin e) :
    psiHom C c i Finset.univ (genH C c i) = -(ptVar (e := e) 0 * (genQ (e := e) c) ^ 2) := by
  rw [psi_genH_self, Finset.insert_eq_of_mem (Finset.mem_univ i), sum_dir_genH]

theorem psi_x0 (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) :
    psiHom C c i K (ptVar 0) = dirVar i * ptVar 0 := by
  simp [psiHom, ptVar]

/-- Algebra maps fixing the base variables preserve the base ideal. -/
theorem base_mem_of_fix (φ : TPoly e →ₐ[ℂ] TPoly e)
    (hφ : ∀ b : Fin (e + (e + e)), φ (MvPolynomial.X (Fin.castAdd (skewDim e + 1) b)) =
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) b))
    (f : TPoly e) (hf : f ∈ baseIdeal C Γ H) : φ f ∈ baseIdeal C Γ H := by
  have hcomp : φ.comp (MvPolynomial.rename (Fin.castAdd (skewDim e + 1))) =
      MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [hφ]
  have hle : baseIdeal C Γ H ≤ (baseIdeal C Γ H).comap φ := by
    unfold baseIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    simp only [Ideal.mem_comap]
    have := congrArg (fun χ : Poly (e + (e + e)) →ₐ[ℂ] TPoly e => χ g) hcomp
    simp only [AlgHom.comp_apply] at this
    rw [this]
    exact Ideal.mem_map_of_mem _ hg
  exact hle hf

theorem fix_genQ (φ : TPoly e →ₐ[ℂ] TPoly e)
    (hφ : ∀ b : Fin (e + (e + e)), φ (MvPolynomial.X (Fin.castAdd (skewDim e + 1) b)) =
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) b)) (c : Fin e → ℂ) :
    φ (genQ (e := e) c) = genQ (e := e) c := by
  unfold genQ dirVar
  simp only [map_sum, map_mul, MvPolynomial.algHom_C, hφ]
  rfl

theorem psi_fix (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) (b : Fin (e + (e + e))) :
    psiHom C c i K (MvPolynomial.X (Fin.castAdd (skewDim e + 1) b)) =
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) b) := by
  simp [psiHom]

theorem scale_fix (i : Fin e) (b : Fin (e + (e + e))) :
    scaleHom i (MvPolynomial.X (Fin.castAdd (skewDim e + 1) b)) =
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) b) := by
  simp [scaleHom]

theorem rho_fix (i : Fin e) (b : Fin (e + (e + e))) :
    rhoHom C i (MvPolynomial.X (Fin.castAdd (skewDim e + 1) b)) =
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) b) := by
  simp [rhoHom]

/-- `ψ_K` agrees with the `d_i`-scaling modulo `(h_k : k ∈ K)`. -/
theorem psi_scale_sub_mem (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) (f : TPoly e) :
    scaleHom i f - psiHom C c i K f ∈ Ideal.span (genH C c '' (K : Set (Fin e))) := by
  apply algHom_sub_mem
  intro a
  refine Fin.addCases (fun b => ?_) (fun k => ?_) a
  · simp [scaleHom, psiHom]
  · refine Fin.cases ?_ (fun kk => ?_) k
    · simp [scaleHom, psiHom, ptVar]
    · simp only [scaleHom, psiHom, MvPolynomial.aeval_X, Fin.addCases_right, Fin.cases_succ]
      have : dirVar i * MvPolynomial.X (Fin.natAdd (e + (e + e)) kk.succ) -
          (dirVar i * ptVar kk.succ -
            ∑ k' ∈ K, MvPolynomial.C (alphaC C i kk k') * genH C c k') =
          ∑ k' ∈ K, MvPolynomial.C (alphaC C i kk k') * genH C c k' := by
        simp [ptVar]
      rw [this]
      apply Ideal.sum_mem
      intro k' hk'
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k', hk', rfl⟩)

/-- Elementwise torsion from homogeneous pieces. -/
theorem torsion_of_pieces (J J' : Ideal (TPoly e))
    (hJ' : J'.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e))) (i : Fin e)
    (h : ∀ (s t u : ℕ) (f : TPoly e), f ∈ piece e s t u → f ∈ J' →
      ∃ N : ℕ, dirVar i ^ N * f ∈ J) :
    ∀ f ∈ J', ∃ N : ℕ, dirVar i ^ N * f ∈ J := by
  classical
  intro f hf
  let 𝒜 := MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)
  rw [← DirectSum.sum_support_decompose 𝒜 f]
  apply Finset.sum_induction _ (fun g => ∃ N : ℕ, dirVar i ^ N * g ∈ J)
  · rintro a b ⟨N1, h1⟩ ⟨N2, h2⟩
    refine ⟨N1 + N2, ?_⟩
    rw [mul_add, pow_add]
    apply J.add_mem
    · rw [mul_comm (dirVar i ^ N1), mul_assoc]
      exact J.mul_mem_left _ h1
    · rw [mul_assoc]
      exact J.mul_mem_left _ h2
  · exact ⟨0, by simp⟩
  · intro d _
    have hcomp : (DirectSum.decompose 𝒜 f d : TPoly e) ∈ J' :=
      (Ideal.IsHomogeneous.mem_iff 𝒜 hJ').mp hf d
    have hdeg : d = HilbertMulti.tripleDegree (d 0) (d 1) (d 2) := by
      apply Finsupp.ext; intro j; fin_cases j <;> simp [HilbertMulti.tripleDegree]
    have h𝒜 : 𝒜 d = piece e (d 0) (d 1) (d 2) := by
      show 𝒜 d = 𝒜 (HilbertMulti.tripleDegree (d 0) (d 1) (d 2))
      congr 1
    have hpiece : (DirectSum.decompose 𝒜 f d : TPoly e) ∈ piece e (d 0) (d 1) (d 2) :=
      h𝒜 ▸ (DirectSum.decompose 𝒜 f d).2
    exact h _ _ _ _ hpiece hcomp

/-- `ρ_i` maps the kernel-bundle ideal into the base. -/
theorem rho_kernel_le (i : Fin e) (g : TPoly e) (hg : g ∈ kernelIdeal C Γ H) :
    rhoHom C i g ∈ baseIdeal C Γ H := by
  rw [mem_baseIdeal_iff]
  intro b hb ξ
  obtain ⟨d, p, hd, hp, hB, rfl⟩ := hb
  have hpair : joinPoints d p ∈ pairRepresentatives (liftedParameterBase C Γ H) :=
    ⟨d, p, hd, hp, hB, rfl⟩
  change MvPolynomial.aeval (tj d p ξ) (rhoHom C i g) = 0
  rw [rho_eval]
  have hle : kernelIdeal C Γ H ≤ MvPolynomial.vanishingIdeal ℂ
      {w | ∃ ξ' : Point (skewDim e + 1), ξ' 0 = 0 ∧ (C.decode (Fin.tail ξ')).val d = 0 ∧
        w = tj d p ξ'} := by
    apply sup_le
    apply sup_le
    · intro g hg
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      rintro _ ⟨ξ', _, _, rfl⟩
      exact (mem_baseIdeal_iff C Γ H g).mp hg _ hpair ξ'
    · rw [Ideal.span_le]
      rintro _ rfl
      rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_iff]
      rintro _ ⟨ξ', h0, _, rfl⟩
      change MvPolynomial.aeval (tj d p ξ') (ptVar 0) = 0
      rw [eval_ptVar]
      exact h0
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_iff]
      rintro _ ⟨ξ', _, hk, rfl⟩
      change MvPolynomial.aeval (tj d p ξ') (dForm C k) = 0
      rw [eval_dForm, hk]
      rfl
  have := MvPolynomial.mem_vanishingIdeal_iff.mp (hle hg) _
    ⟨rhoVec C i d ξ, by simp [rhoVec], rho_kernel C i d ξ, rfl⟩
  exact this

/-- (T3-torsion) `(J_K : q²)` is `d_i`-torsion over `J_K` (generic `q`). -/
theorem torsion_JK_qsq' (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)))
    (f : TPoly e) (hf : f ∈ (kernelIdeal C Γ H).colon {genQ (e := e) c ^ 2}) (i : Fin e) :
    ∃ N : ℕ, dirVar (e := e) i ^ N * f ∈ kernelIdeal C Γ H := by
  refine torsion_of_pieces _ _ (HilbertMulti.homogeneous_colon (tw e) _
    (kernelIdeal_hom C Γ H) (genQ_sq_hom (e := e) c)) i ?_ f hf
  intro s t u f hpiece hf
  refine ⟨u, ?_⟩
  rw [← scaleHom_eq i f s t u hpiece]
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hf
  have h1 := rho_kernel_le C Γ H i _ hf
  rw [map_mul, map_pow, fix_genQ _ (rho_fix C i) c] at h1
  have hρ : rhoHom C i f ∈ baseIdeal C Γ H := by
    have hcol : rhoHom C i f ∈ (baseIdeal C Γ H).colon {genQ (e := e) c ^ 2} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      exact h1
    rwa [base_colon_qsq_eq C Γ H c hc] at hcol
  have hsplit : scaleHom i f = (scaleHom i f - rhoHom C i f) + rhoHom C i f := by ring
  rw [hsplit]
  apply Ideal.add_mem
  · have hle : Ideal.span {ptVar (e := e) 0} ⊔ Ideal.span (Set.range (dForm C)) ≤
        kernelIdeal C Γ H := sup_le (le_sup_of_le_left le_sup_right) le_sup_right
    exact hle (scale_sub_rho_mem C i f)
  · exact Ideal.mem_sup_left (Ideal.mem_sup_left hρ)

theorem span_genH_le_Jh2 (c : Fin e → ℂ) (K : Finset (Fin e)) :
    Ideal.span (genH C c '' (K : Set (Fin e))) ≤ defJh2 C Γ H c := by
  rw [Ideal.span_le]
  rintro _ ⟨k, _, rfl⟩
  exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))

/-- Final step shared by T1/T2: `d_i ψ f ∈ J_h2` gives `d_i^{u+1} f ∈ J_h2`. -/
theorem torsion_finish_Jh2 (c : Fin e → ℂ) (i : Fin e) (f : TPoly e) (s t u : ℕ)
    (hpiece : f ∈ piece e s t u)
    (h : dirVar i * psiHom C c i Finset.univ f ∈ defJh2 C Γ H c) :
    dirVar i ^ (u + 1) * f ∈ defJh2 C Γ H c := by
  have hsub : scaleHom i f - psiHom C c i Finset.univ f ∈ defJh2 C Γ H c :=
    span_genH_le_Jh2 C Γ H c Finset.univ (psi_scale_sub_mem C c i Finset.univ f)
  have heq : dirVar i ^ (u + 1) * f = dirVar i * (scaleHom i f - psiHom C c i Finset.univ f) +
      dirVar i * psiHom C c i Finset.univ f := by
    rw [scaleHom_eq i f s t u hpiece]
    ring
  rw [heq]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hsub) h

/-- (T1-torsion) `(J_h : x0)` is `d_i`-torsion over `J_h + (q²)`. -/
theorem torsion_Jh_colon_x0' (c : Fin e → ℂ) (f : TPoly e)
    (hf : f ∈ (defJh C Γ H c).colon {ptVar (e := e) 0}) (i : Fin e) :
    ∃ N : ℕ, dirVar (e := e) i ^ N * f ∈ defJh2 C Γ H c := by
  refine torsion_of_pieces _ _ (HilbertMulti.homogeneous_colon (tw e) _
    (defJh_hom C Γ H c) (ptVar_hom (e := e) 0)) i ?_ f hf
  intro s t u f hpiece hf
  refine ⟨u + 1, torsion_finish_Jh2 C Γ H c i f s t u hpiece ?_⟩
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hf
  have hle : defJh C Γ H c ≤ (baseIdeal C Γ H ⊔
      Ideal.span {ptVar (e := e) 0 * genQ (e := e) c ^ 2}).comap (psiHom C c i Finset.univ) := by
    apply sup_le
    · intro g hg
      exact Ideal.mem_sup_left (base_mem_of_fix C Γ H _ (psi_fix C c i _) g hg)
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]
      by_cases hk : k = i
      · subst hk
        rw [psi_genH_univ_self]
        exact neg_mem (Ideal.mem_sup_right (Ideal.subset_span rfl))
      · rw [psi_genH_ne C c i _ k hk, if_pos (Finset.mem_univ k)]
        exact zero_mem _
  have hx := hle hf
  rw [Ideal.mem_comap, map_mul, psi_x0] at hx
  obtain ⟨B, hB, G', hG', hsum⟩ := Submodule.mem_sup.mp hx
  obtain ⟨G, rfl⟩ := Ideal.mem_span_singleton'.mp hG'
  have hx0 : ptVar (e := e) 0 * (dirVar i * psiHom C c i Finset.univ f - G * genQ (e := e) c ^ 2) ∈
      baseIdeal C Γ H := by
    have : ptVar (e := e) 0 * (dirVar i * psiHom C c i Finset.univ f - G * genQ (e := e) c ^ 2) =
        B := by linear_combination -hsum
    rw [this]
    exact hB
  have hmem : dirVar i * psiHom C c i Finset.univ f - G * genQ (e := e) c ^ 2 ∈
      baseIdeal C Γ H :=
    X_mul_mem (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H)))
      (0 : Fin (skewDim e + 1)) _ hx0
  have heq : dirVar i * psiHom C c i Finset.univ f =
      (dirVar i * psiHom C c i Finset.univ f - G * genQ (e := e) c ^ 2) +
        G * genQ (e := e) c ^ 2 := by ring
  rw [heq]
  apply Ideal.add_mem
  · exact Ideal.mem_sup_left (Ideal.mem_sup_left hmem)
  · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

/-- (T2-torsion) `(J_h + (q²) : x0)` is `d_i`-torsion over `J_h + (q²)`. -/
theorem torsion_Jh2_colon_x0' (c : Fin e → ℂ) (f : TPoly e)
    (hf : f ∈ (defJh2 C Γ H c).colon {ptVar (e := e) 0}) (i : Fin e) :
    ∃ N : ℕ, dirVar (e := e) i ^ N * f ∈ defJh2 C Γ H c := by
  refine torsion_of_pieces _ _ (HilbertMulti.homogeneous_colon (tw e) _
    (defJh2_hom C Γ H c) (ptVar_hom (e := e) 0)) i ?_ f hf
  intro s t u f hpiece hf
  refine ⟨u + 1, torsion_finish_Jh2 C Γ H c i f s t u hpiece ?_⟩
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hf
  have hbase2 : baseIdeal C Γ H ⊔ Ideal.span {genQ (e := e) c ^ 2} =
      Ideal.map (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)))
        (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H)) ⊔
          Ideal.span {pairQ0 (e := e) c ^ 2}) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_pow, rename_pairQ0]
    rfl
  have hle : defJh2 C Γ H c ≤ (baseIdeal C Γ H ⊔
      Ideal.span {genQ (e := e) c ^ 2}).comap (psiHom C c i Finset.univ) := by
    apply sup_le
    · apply sup_le
      · intro g hg
        exact Ideal.mem_sup_left (base_mem_of_fix C Γ H _ (psi_fix C c i _) g hg)
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap]
        by_cases hk : k = i
        · subst hk
          rw [psi_genH_univ_self]
          exact neg_mem (Ideal.mem_sup_right
            (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
        · rw [psi_genH_ne C c i _ k hk, if_pos (Finset.mem_univ k)]
          exact zero_mem _
    · rw [Ideal.span_le]
      rintro _ rfl
      rw [SetLike.mem_coe, Ideal.mem_comap]
      rw [map_pow, fix_genQ _ (psi_fix C c i _) c]
      exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  have hx := hle hf
  rw [Ideal.mem_comap, map_mul, psi_x0, hbase2] at hx
  have hx0 : ptVar (e := e) 0 * (dirVar i * psiHom C c i Finset.univ f) ∈
      Ideal.map (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)))
        (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H)) ⊔
          Ideal.span {pairQ0 (e := e) c ^ 2}) := by
    have : ptVar (e := e) 0 * (dirVar i * psiHom C c i Finset.univ f) =
        psiHom C c i Finset.univ f * (dirVar i * ptVar 0) := by ring
    rw [this]
    exact hx
  have hmem := X_mul_mem _ (0 : Fin (skewDim e + 1)) _ hx0
  rw [← hbase2] at hmem
  have hle2 : baseIdeal C Γ H ⊔ Ideal.span {genQ (e := e) c ^ 2} ≤ defJh2 C Γ H c :=
    sup_le (le_sup_of_le_left le_sup_left) le_sup_right
  exact hle2 hmem

theorem hval_cons (c : Fin e → ℂ) (d : Point e) (a : ℂ) (ω : alternatingForms (U := Point e))
    (k : Fin e) :
    hval C c d (Fin.cons a (C.decode.symm ω)) k =
      ω.val d (Pi.single k 1) - a * c k * ∑ j, c j * d j := by
  unfold hval
  simp [Fin.tail_cons]

theorem anchAlt_apply (i l : Fin e) (d : Point e) (k : Fin e) :
    (anchAlt (LinearMap.proj i) (LinearMap.proj l)).val d (Pi.single k 1) =
      d i * (if l = k then 1 else 0) - d l * (if i = k then 1 else 0) := by
  simp only [anchAlt, IncidenceLocal.anchoredForm, LinearMap.sub_apply,
    LinearMap.BilinForm.linMulLin_apply, LinearMap.proj_apply, Pi.single_apply]

/-- (F1) `h_k` is fiberwise nonzero in chart `i ≠ k`. -/
theorem fiber_genH_ne (c : Fin e → ℂ) (i k : Fin e) (hk : k ≠ i) (d : Point e) (hdi : d i ≠ 0) :
    ∃ ξ : Point (skewDim e + 1), hval C c d ξ k ≠ 0 := by
  refine ⟨Fin.cons 0 (C.decode.symm (anchAlt (LinearMap.proj i) (LinearMap.proj k))), ?_⟩
  rw [hval_cons, anchAlt_apply]
  simp [Ne.symm hk, hdi]

/-- (F2) `Σ_{l ∈ K'} d_l h_l` is fiberwise nonzero when `i ∈ K'`, `d_i ≠ 0`, `q(d) ≠ 0`. -/
theorem fiber_sum_genH (c : Fin e → ℂ) (i : Fin e) (K' : Finset (Fin e)) (hiK : i ∈ K')
    (d : Point e) (hdi : d i ≠ 0) (hq : (∑ j, c j * d j) ≠ 0) :
    ∃ ξ : Point (skewDim e + 1), (∑ l ∈ K', d l * hval C c d ξ l) ≠ 0 := by
  classical
  by_cases hout : ∃ l, l ∉ K' ∧ d l ≠ 0
  · obtain ⟨l, hlK, hdl⟩ := hout
    refine ⟨Fin.cons 0 (C.decode.symm (anchAlt (LinearMap.proj i) (LinearMap.proj l))), ?_⟩
    have hterm : ∀ j ∈ K', d j * hval C c d
        (Fin.cons 0 (C.decode.symm (anchAlt (LinearMap.proj i) (LinearMap.proj l)))) j =
        if i = j then -(d l * d i) else 0 := by
      intro j hj
      rw [hval_cons, anchAlt_apply]
      have hlj : ¬ l = j := fun h => hlK (h ▸ hj)
      by_cases hij : i = j
      · subst hij; simp [hlj]; ring
      · simp [hlj, hij]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq K' i (fun _ => -(d l * d i)), if_pos hiK]
    exact neg_ne_zero.mpr (mul_ne_zero hdl hdi)
  · push Not at hout
    refine ⟨Fin.cons 1 (C.decode.symm 0), ?_⟩
    have hterm : ∀ j ∈ K', d j * hval C c d (Fin.cons 1 (C.decode.symm 0)) j =
        -((∑ j, c j * d j) * (c j * d j)) := by
      intro j _
      rw [hval_cons]
      simp
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.mul_sum]
    have hfull : (∑ j ∈ K', c j * d j) = ∑ j, c j * d j := by
      rw [← Finset.sum_subset (Finset.subset_univ K')]
      intro j _ hj
      rw [hout j hj, mul_zero]
    rw [hfull]
    exact neg_ne_zero.mpr (mul_ne_zero hq hq)

/-- Domain step in chart `i`: a fiberwise nonzero factor can be cancelled up to `d_i`. -/
theorem domain_step (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)))
    (i : Fin e) (ℓ g : TPoly e)
    (hℓ : ∀ (d : Point e) (p : Point (e + e)), d i ≠ 0 → (∑ j, c j * d j) ≠ 0 →
      ∃ ξ : Point (skewDim e + 1), MvPolynomial.aeval (tj d p ξ) ℓ ≠ 0)
    (hg : ℓ * g ∈ baseIdeal C Γ H) : dirVar i * g ∈ baseIdeal C Γ H := by
  have hr : ∀ b : Point (e + (e + e)), ∀ ξ ξ' : Point (skewDim e + 1),
      MvPolynomial.aeval (joinPoints b ξ) (dirVar i * genQ (e := e) c) =
        MvPolynomial.aeval (joinPoints b ξ') (dirVar i * genQ (e := e) c) := by
    intro b ξ ξ'
    simp [dirVar, genQ, joinPoints]
  have h1 := domain_mem C Γ H ℓ g (dirVar i * genQ (e := e) c) ?_ hr hg
  · have h2 : genQ (e := e) c * (dirVar i * g) ∈ baseIdeal C Γ H := by
      have : genQ (e := e) c * (dirVar i * g) = dirVar i * genQ (e := e) c * g := by ring
      rw [this]
      exact h1
    exact base_nzd_genQ C Γ H c hc _ h2
  · intro b hb hne
    obtain ⟨d, p, hd, hp, hB, rfl⟩ := hb
    obtain ⟨ξ, hξ⟩ := hne
    change MvPolynomial.aeval (tj d p ξ) (dirVar i * genQ (e := e) c) ≠ 0 at hξ
    rw [map_mul, eval_dirVar, eval_genQ] at hξ
    obtain ⟨ξ', hξ'⟩ := hℓ d p (left_ne_zero_of_mul hξ) (right_ne_zero_of_mul hξ)
    intro h0
    exact hξ' ((fiberAt_eq_zero_iff (joinPoints d p) ℓ).mp h0 ξ')

theorem scale_genH (c : Fin e → ℂ) (i k : Fin e) :
    scaleHom i (genH C c k) = dirVar i * genH C c k := by
  have h := scaleHom_eq i (genH C c k) 1 0 1
    ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr (genH_hom C c k))
  rw [h, pow_one]

theorem scale_psi_comm (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) (g : TPoly e) :
    scaleHom i (psiHom C c i K g) = psiHom C c i K (scaleHom i g) := by
  have h : (scaleHom i).comp (psiHom C c i K) = (psiHom C c i K).comp (scaleHom i) := by
    apply MvPolynomial.algHom_ext
    intro a
    refine Fin.addCases (fun b => ?_) (fun k => ?_) a
    · simp [scaleHom, psiHom]
    · refine Fin.cases ?_ (fun kk => ?_) k
      · simp [scaleHom, psiHom, ptVar, dirVar]
      · simp only [AlgHom.comp_apply]
        have hs : ∀ y, scaleHom i y = MvPolynomial.aeval (fun a : Fin (e + (e + e) + (skewDim e + 1)) =>
            Fin.addCases (fun b => MvPolynomial.X (Fin.castAdd (skewDim e + 1) b))
              (fun k => dirVar i * MvPolynomial.X (Fin.natAdd (e + (e + e)) k)) a) y := fun _ => rfl
        have hp : ∀ y, psiHom C c i K y = MvPolynomial.aeval (fun a : Fin (e + (e + e) + (skewDim e + 1)) =>
            Fin.addCases (fun b => MvPolynomial.X (Fin.castAdd (skewDim e + 1) b))
              (fun k : Fin (skewDim e + 1) => Fin.cases (dirVar i * ptVar 0)
                (fun kk => dirVar i * ptVar (Fin.succ kk) -
                  ∑ k' ∈ K, MvPolynomial.C (alphaC C i kk k') * genH C c k') k) a) y :=
          fun _ => rfl
        rw [hp (MvPolynomial.X _), MvPolynomial.aeval_X, Fin.addCases_right, Fin.cases_succ]
        rw [hs (MvPolynomial.X _), MvPolynomial.aeval_X, Fin.addCases_right]
        rw [map_sub, map_mul, map_sum]
        have hdi : scaleHom i (dirVar i) = dirVar i := scale_fix i _
        have hpi : psiHom C c i K (dirVar i) = dirVar i := psi_fix C c i K _
        have hz : scaleHom i (ptVar (e := e) kk.succ) =
            dirVar i * MvPolynomial.X (Fin.natAdd (e + (e + e)) kk.succ) := by
          simp [scaleHom, ptVar]
        have hz' : psiHom C c i K (MvPolynomial.X (Fin.natAdd (e + (e + e)) kk.succ)) =
            dirVar i * ptVar kk.succ -
              ∑ k' ∈ K, MvPolynomial.C (alphaC C i kk k') * genH C c k' := by
          simp [psiHom]
        rw [hdi, hz, map_mul, hpi, hz']
        simp only [map_mul, MvPolynomial.algHom_C, scale_genH, ptVar]
        rw [mul_sub, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k' _
        rw [MvPolynomial.algebraMap_eq]
        ring
  exact congrArg (fun χ : TPoly e →ₐ[ℂ] TPoly e => χ g) h

theorem scale_dirVar (i j : Fin e) : scaleHom i (dirVar (e := e) j) = dirVar j :=
  scale_fix i _

theorem psi_dirVar (c : Fin e → ℂ) (i : Fin e) (K : Finset (Fin e)) (j : Fin e) :
    psiHom C c i K (dirVar (e := e) j) = dirVar j :=
  psi_fix C c i K _

theorem kappa_ell0 (c : Fin e → ℂ) (i mm : Fin e) (S : Finset (Fin e)) (hiS : i ∈ S)
    (hmS : mm ∉ S) :
    psiHom C c i {mm} (∑ l ∈ S, dirVar l * genH C c l) =
      dirVar i * ∑ l ∈ insert mm S, dirVar l * genH C c l := by
  apply tpoly_ext
  intro d p ξ
  rw [psi_eval]
  simp only [map_sum, map_mul, eval_dirVar, eval_genH, hval_psiVec, Finset.sum_singleton]
  rw [Finset.sum_insert hmS]
  have hterm : ∀ l ∈ S, d l * (d i * hval C c d ξ l - hval C c d ξ mm *
      (d i * (if mm = l then 1 else 0) - d mm * (if i = l then 1 else 0))) =
      d i * (d l * hval C c d ξ l) + (if i = l then d i * (d mm * hval C c d ξ mm) else 0) := by
    intro l hl
    have hml : ¬ mm = l := fun h => hmS (h ▸ hl)
    by_cases hil : i = l
    · subst hil; simp [hml]; ring
    · simp [hml, hil]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq S i (fun _ => d i * (d mm * hval C c d ξ mm)), if_pos hiS]
  ring

/-- (T4-torsion) prefix colons `(J_{<m} : h_m)` are `d_i`-torsion over `J_{<m}`. -/
theorem torsion_prefixNat' (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)))
    (m : ℕ) (hm : m < e) (f : TPoly e)
    (hf : f ∈ (defJprefixNat C Γ H c m).colon {genH C c ⟨m, hm⟩}) (i : Fin e) :
    ∃ N : ℕ, dirVar (e := e) i ^ N * f ∈ defJprefixNat C Γ H c m := by
  classical
  refine torsion_of_pieces _ _ (HilbertMulti.homogeneous_colon (tw e) _
    (defJprefixNat_hom C Γ H c m) (genH_hom C c ⟨m, hm⟩)) i ?_ f hf
  intro s t u f hpiece hf
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hf
  set mm : Fin e := ⟨m, hm⟩ with hmm
  let S : Finset (Fin e) := Finset.univ.filter (fun k : Fin e => k.val < m)
  have hS : ((S : Finset (Fin e)) : Set (Fin e)) = {k : Fin e | k.val < m} := by
    ext k; simp [S]
  have hmS : mm ∉ S := by simp [S, mm]
  have hspanS : Ideal.span (genH C c '' (S : Set (Fin e))) ≤ defJprefixNat C Γ H c m := by
    rw [hS]; unfold defJprefixNat; exact le_sup_right
  have hbaseJ : baseIdeal C Γ H ≤ defJprefixNat C Γ H c m := by
    unfold defJprefixNat; exact le_sup_left
  have hscale : scaleHom i f = dirVar i ^ u * f := scaleHom_eq i f s t u hpiece
  have hsub : scaleHom i f - psiHom C c i S f ∈ defJprefixNat C Γ H c m :=
    hspanS (psi_scale_sub_mem C c i S f)
  by_cases hiS : i ∈ S
  · have hmi : mm ≠ i := fun h => hmS (h ▸ hiS)
    set ℓ0 := ∑ l ∈ S, dirVar (e := e) l * genH C c l with hℓ0
    have hψi : psiHom C c i S (genH C c i) = ℓ0 := by
      rw [psi_genH_self, Finset.insert_eq_of_mem hiS]
    have hℓ0J : ℓ0 ∈ defJprefixNat C Γ H c m := by
      apply Ideal.sum_mem
      intro l hl
      apply Ideal.mul_mem_left
      exact hspanS (Ideal.subset_span ⟨l, hl, rfl⟩)
    have hle : defJprefixNat C Γ H c m ≤
        (baseIdeal C Γ H ⊔ Ideal.span {ℓ0}).comap (psiHom C c i S) := by
      apply sup_le
      · intro g hg
        exact Ideal.mem_sup_left (base_mem_of_fix C Γ H _ (psi_fix C c i S) g hg)
      · rw [Ideal.span_le]
        rintro _ ⟨k, hk, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap]
        by_cases hki : k = i
        · subst hki
          rw [hψi]
          exact Ideal.mem_sup_right (Ideal.subset_span rfl)
        · have hkS : k ∈ S := by simpa [S] using hk
          rw [psi_genH_ne C c i S k hki, if_pos hkS]
          exact zero_mem _
    have hx := hle hf
    rw [Ideal.mem_comap, map_mul, psi_genH_ne C c i S mm hmi, if_neg hmS] at hx
    obtain ⟨B, hB, G', hG', hsum⟩ := Submodule.mem_sup.mp hx
    obtain ⟨G, rfl⟩ := Ideal.mem_span_singleton'.mp hG'
    have hκm : psiHom C c i {mm} (genH C c mm) = 0 := by
      rw [psi_genH_ne C c i {mm} mm hmi, if_pos (Finset.mem_singleton_self mm)]
    have hκℓ0 : psiHom C c i {mm} ℓ0 =
        dirVar i * ∑ l ∈ insert mm S, dirVar l * genH C c l :=
      kappa_ell0 C c i mm S hiS hmS
    have hκ1 : psiHom C c i {mm} ℓ0 * psiHom C c i {mm} G ∈ baseIdeal C Γ H := by
      have h := congrArg (psiHom C c i {mm}) hsum
      rw [map_add, map_mul, map_mul, map_mul, hκm, mul_zero, mul_zero] at h
      have : psiHom C c i {mm} ℓ0 * psiHom C c i {mm} G = -psiHom C c i {mm} B := by
        linear_combination h
      rw [this]
      exact neg_mem (base_mem_of_fix C Γ H _ (psi_fix C c i {mm}) B hB)
    have hκG : dirVar i * psiHom C c i {mm} G ∈ baseIdeal C Γ H := by
      apply domain_step C Γ H c hc i (psiHom C c i {mm} ℓ0) (psiHom C c i {mm} G) _ hκ1
      intro d p hdi hq
      obtain ⟨ξ, hξ⟩ := fiber_sum_genH C c i (insert mm S) (Finset.mem_insert_of_mem hiS)
        d hdi hq
      refine ⟨ξ, ?_⟩
      rw [hκℓ0]
      simp only [map_mul, map_sum, eval_dirVar, eval_genH]
      exact mul_ne_zero hdi hξ
    have hscB : scaleHom i B ∈ baseIdeal C Γ H := base_mem_of_fix C Γ H _ (scale_fix i) B hB
    have hscℓ0 : scaleHom i ℓ0 = dirVar i * ℓ0 := by
      rw [hℓ0, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [map_mul, scale_dirVar, scale_genH]
      ring
    have hscψ : scaleHom i (psiHom C c i S f) = dirVar i ^ u * psiHom C c i S f := by
      rw [scale_psi_comm, hscale, map_mul, map_pow, psi_dirVar]
    have hscm : scaleHom i (genH C c mm) = dirVar i * genH C c mm := scale_genH C c i mm
    have hR : scaleHom i B + scaleHom i G * (dirVar i * ℓ0) =
        dirVar i ^ u * psiHom C c i S f * (dirVar i * (dirVar i * genH C c mm)) := by
      have h := congrArg (scaleHom i) hsum
      rw [map_add, map_mul, map_mul, map_mul, hscℓ0, hscψ, hscm, scale_dirVar] at h
      exact h
    have hGsub := psi_scale_sub_mem C c i {mm} G
    rw [Finset.coe_singleton, Set.image_singleton] at hGsub
    obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton'.mp hGsub
    have hkey : genH C c mm * (dirVar i ^ (u + 3) * psiHom C c i S f - dirVar i ^ 2 * Q * ℓ0) ∈
        baseIdeal C Γ H := by
      have : genH C c mm * (dirVar i ^ (u + 3) * psiHom C c i S f - dirVar i ^ 2 * Q * ℓ0) =
          dirVar i * scaleHom i B + (dirVar i * psiHom C c i {mm} G) * (dirVar i * ℓ0) := by
        linear_combination (-dirVar i) * hR + (-(dirVar i ^ 2 * ℓ0)) * hQ
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hscB) (Ideal.mul_mem_right _ _ hκG)
    have hdom : dirVar i * (dirVar i ^ (u + 3) * psiHom C c i S f - dirVar i ^ 2 * Q * ℓ0) ∈
        baseIdeal C Γ H := by
      apply domain_step C Γ H c hc i (genH C c mm) _ _ hkey
      intro d p hdi _
      obtain ⟨ξ, hξ⟩ := fiber_genH_ne C c i mm hmi d hdi
      exact ⟨ξ, by rw [eval_genH]; exact hξ⟩
    have hψJ : dirVar i ^ (u + 4) * psiHom C c i S f ∈ defJprefixNat C Γ H c m := by
      have : dirVar i ^ (u + 4) * psiHom C c i S f =
          dirVar i * (dirVar i ^ (u + 3) * psiHom C c i S f - dirVar i ^ 2 * Q * ℓ0) +
            dirVar i ^ 3 * Q * ℓ0 := by ring
      rw [this]
      exact Ideal.add_mem _ (hbaseJ hdom) (Ideal.mul_mem_left _ _ hℓ0J)
    refine ⟨u + (u + 4), ?_⟩
    have : dirVar i ^ (u + (u + 4)) * f =
        dirVar i ^ (u + 4) * (scaleHom i f - psiHom C c i S f) +
          dirVar i ^ (u + 4) * psiHom C c i S f := by
      rw [hscale]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hsub) hψJ
  · have hle : defJprefixNat C Γ H c m ≤ (baseIdeal C Γ H).comap (psiHom C c i S) := by
      apply sup_le
      · intro g hg
        exact base_mem_of_fix C Γ H _ (psi_fix C c i S) g hg
      · rw [Ideal.span_le]
        rintro _ ⟨k, hk, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap]
        have hkS : k ∈ S := by simpa [S] using hk
        have hki : k ≠ i := fun h => hiS (h ▸ hkS)
        rw [psi_genH_ne C c i S k hki, if_pos hkS]
        exact zero_mem _
    have hx := hle hf
    rw [Ideal.mem_comap, map_mul] at hx
    have hdom : dirVar i * psiHom C c i S f ∈ baseIdeal C Γ H := by
      apply domain_step C Γ H c hc i (psiHom C c i S (genH C c mm)) _ _
        (by rw [mul_comm]; exact hx)
      intro d p hdi hq
      by_cases hmi : mm = i
      · rw [hmi, psi_genH_self]
        obtain ⟨ξ, hξ⟩ := fiber_sum_genH C c i (insert i S) (Finset.mem_insert_self i S) d hdi hq
        refine ⟨ξ, ?_⟩
        simp only [map_sum, map_mul, eval_dirVar, eval_genH]
        exact hξ
      · rw [psi_genH_ne C c i S mm hmi, if_neg hmS]
        obtain ⟨ξ, hξ⟩ := fiber_genH_ne C c i mm hmi d hdi
        refine ⟨ξ, ?_⟩
        rw [map_mul, eval_dirVar, eval_genH]
        exact mul_ne_zero hdi hξ
    refine ⟨u + 1, ?_⟩
    have : dirVar i ^ (u + 1) * f =
        dirVar i * (scaleHom i f - psiHom C c i S f) + dirVar i * psiHom C c i S f := by
      rw [hscale]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hsub) (hbaseJ hdom)

end Chart

end
end TripleRankRoute
end DistinctDistances.TrackB
