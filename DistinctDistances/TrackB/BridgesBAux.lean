import DistinctDistances.Foundations
import DistinctDistances.Foundations.GenericFiber
import DistinctDistances.TrackB.Compactification
import DistinctDistances.TrackB.SegreClosureSupport
import DistinctDistances.TrackB.PolynomialImageSupport
import DistinctDistances.Foundations.ImageOpen
import DistinctDistances.TrackB.TangentLineSupport
import DistinctDistances.TrackD.DifferentialConstants
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
Helpers for the track B inputs taken from track A.

The Segre elimination section is a namespaced port of the proved
`RulingMaps.segre_projection_closed` (TrackB/RulingMapsAux.lean:246–574), which cannot
be imported here because RulingMapsAux imports Requests.lean.
-/

namespace DistinctDistances.TrackB

namespace BridgesB

set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Elimination: projections from Segre products are closed -/

/-- Finitely many homogeneous generators of a homogeneous ideal. -/
theorem exists_homogeneous_generators {n : ℕ} (I : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ)) :
    ∃ (τ : Type) (_ : Fintype τ) (f : τ → Poly n) (δ : τ → ℕ),
      (∀ i, f i ∈ I) ∧ (∀ i, (f i).IsHomogeneous (δ i)) ∧ I ≤ Ideal.span (Set.range f) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  let τ := Σ g : s, Fin (g.1.totalDegree + 1)
  refine ⟨τ, inferInstance, fun i => MvPolynomial.homogeneousComponent i.2 i.1.1,
    fun i => i.2, ?_, ?_, ?_⟩
  · intro i
    have hg : i.1.1 ∈ I := by
      rw [← hs]
      exact Submodule.subset_span i.1.2
    exact MvPolynomial.homogeneousComponent_mem_of_mem hI hg _
  · intro i
    exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
  · rw [← hs]
    apply Submodule.span_le.mpr
    intro g hg
    rw [← MvPolynomial.sum_homogeneousComponent g]
    apply Ideal.sum_mem
    intro d hd
    apply Ideal.subset_span
    exact ⟨⟨⟨g, hg⟩, ⟨d, Finset.mem_range.mp hd⟩⟩, rfl⟩

theorem homogeneousComponent_mul_of_isHomogeneous {n : ℕ} {q : Poly n} {δ D : ℕ}
    (hq : q.IsHomogeneous δ) (hδ : δ ≤ D) (c : Poly n) :
    MvPolynomial.homogeneousComponent D (c * q) =
      MvPolynomial.homogeneousComponent (D - δ) c * q := by
  classical
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent c]
  rw [Finset.sum_mul, map_sum]
  have hterm : ∀ k, MvPolynomial.homogeneousComponent D
      (MvPolynomial.homogeneousComponent k c * q) =
      if k + δ = D then MvPolynomial.homogeneousComponent k c * q else 0 := by
    intro k
    have hmem : MvPolynomial.homogeneousComponent k c * q ∈
        MvPolynomial.homogeneousSubmodule (Fin n) ℂ (k + δ) :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        ((MvPolynomial.homogeneousComponent_isHomogeneous k c).mul hq)
    rw [MvPolynomial.homogeneousComponent_of_mem hmem]
    by_cases h : k + δ = D
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  by_cases hmem : D - δ ∈ Finset.range (c.totalDegree + 1)
  · rw [Finset.sum_eq_single (D - δ)]
    · intro k hk hne
      exact absurd (by have := (Finset.mem_filter.mp hk).2; omega) hne
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨hmem, by omega⟩) hnot
  · rw [Finset.sum_eq_zero]
    · have hz : MvPolynomial.homogeneousComponent (D - δ) c = 0 := by
        apply MvPolynomial.homogeneousComponent_eq_zero
        rw [Finset.mem_range] at hmem
        omega
      rw [hz, zero_mul]
    · intro k hk
      exfalso
      have h1 := (Finset.mem_filter.mp hk).2
      have h2 := (Finset.mem_filter.mp hk).1
      apply hmem
      rwa [show D - δ = k by omega]

/-- Substitution `Z_{(k1,k2)} ↦ x_{k2} Y_{k1}`. -/
def segreSlice {N1 N2 : ℕ} (x : Point N2) : Poly (N1 * N2) →ₐ[ℂ] Poly N1 :=
  MvPolynomial.aeval (fun k => MvPolynomial.C (x (finProdFinEquiv.symm k).2) *
    MvPolynomial.X (finProdFinEquiv.symm k).1)

theorem eval_segreSlice {N1 N2 : ℕ} (x : Point N2) (b : Point N1) (f : Poly (N1 * N2)) :
    MvPolynomial.aeval b (segreSlice x f) = MvPolynomial.aeval (segreVector b x) f := by
  rw [segreSlice, GenericFiber.eval_aeval]
  refine congrArg (fun φ => MvPolynomial.aeval φ f) ?_
  funext k
  simp [segreVector, mul_comm]

theorem segreSlice_isHomogeneous {N1 N2 : ℕ} (x : Point N2) {f : Poly (N1 * N2)} {δ : ℕ}
    (hf : f.IsHomogeneous δ) : (segreSlice (N1 := N1) x f).IsHomogeneous δ := by
  have h := hf.aeval (fun k => (MvPolynomial.C (x (finProdFinEquiv.symm k).2) *
    MvPolynomial.X (finProdFinEquiv.symm k).1 : Poly N1))
    (fun k => MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa [segreSlice] using h

/-- The symbolic version of `segreSlice`, with the second factor as indeterminates. -/
def segreSym {N1 N2 : ℕ} : Poly (N1 * N2) →ₐ[ℂ] MvPolynomial (Fin N1) (Poly N2) :=
  MvPolynomial.aeval (fun k => MvPolynomial.C (MvPolynomial.X (finProdFinEquiv.symm k).2) *
    MvPolynomial.X (finProdFinEquiv.symm k).1)

theorem map_segreSym {N1 N2 : ℕ} (x : Point N2) (f : Poly (N1 * N2)) :
    MvPolynomial.map (MvPolynomial.aeval x).toRingHom (segreSym (N1 := N1) f) =
      segreSlice x f := by
  have hhom : (MvPolynomial.mapAlgHom (MvPolynomial.aeval x)).comp (segreSym (N1 := N1)) =
      segreSlice x := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [segreSym, segreSlice]
  exact congrArg (fun F : Poly (N1 * N2) →ₐ[ℂ] Poly N1 => F f) hhom

theorem map_lift {N1 N2 : ℕ} (x : Point N2) (c : Poly N1) :
    MvPolynomial.map (MvPolynomial.aeval x).toRingHom
      (MvPolynomial.map (algebraMap ℂ (Poly N2)) c) = c := by
  rw [MvPolynomial.map_map]
  have : ((MvPolynomial.aeval x).toRingHom.comp (algebraMap ℂ (Poly N2))) = RingHom.id ℂ := by
    ext r
    simp
  rw [this, MvPolynomial.map_id]

/-- Exponents of total degree `D` in `N1` variables, as a finite set. -/
def degFinset (N1 D : ℕ) : Finset (Fin N1 →₀ ℕ) :=
  ((Finset.univ : Finset (Fin N1 → Fin (D + 1))).image
    (fun f => Finsupp.equivFunOnFinite.symm (fun i => (f i : ℕ)))).filter
      (fun α => α.degree = D)

theorem le_degree_of {N1 : ℕ} (α : Fin N1 →₀ ℕ) (i : Fin N1) : α i ≤ α.degree := by
  classical
  by_cases hi : i ∈ α.support
  · exact Finset.single_le_sum (f := fun j => α j) (fun j _ => Nat.zero_le _) hi
  · rw [Finsupp.notMem_support_iff.mp hi]
    exact Nat.zero_le _

theorem mem_degFinset {N1 D : ℕ} {α : Fin N1 →₀ ℕ} : α ∈ degFinset N1 D ↔ α.degree = D := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨fun i => ⟨α i, Nat.lt_succ_of_le (h ▸ le_degree_of α i)⟩, Finset.mem_univ _, ?_⟩, h⟩
    ext i
    simp

theorem degree_eq_sum_univ {N1 : ℕ} (α : Fin N1 →₀ ℕ) : α.degree = ∑ i, α i := by
  classical
  change ∑ i ∈ α.support, α i = _
  exact Finset.sum_subset (Finset.subset_univ _)
    (fun i _ hi => Finsupp.notMem_support_iff.mp hi)

theorem eval_homogeneous_sum {N1 D : ℕ} (P : Poly N1) (hP : P.IsHomogeneous D) (b : Point N1) :
    ∑ β : degFinset N1 D, P.coeff β.1 * ∏ k ∈ β.1.support, b k ^ β.1 k =
      MvPolynomial.aeval b P := by
  classical
  have hae : MvPolynomial.eval b P = MvPolynomial.aeval b P := by
    rw [← MvPolynomial.coe_aeval_eq_eval]
    rfl
  rw [← hae, MvPolynomial.eval_eq,
    Finset.sum_coe_sort (degFinset N1 D) (fun β => P.coeff β * ∏ k ∈ β.support, b k ^ β k)]
  symm
  apply Finset.sum_subset
  · intro d hd
    apply mem_degFinset.mpr
    have h := hP (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.degree_eq_weight_one]
    exact h
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul]

/-- Projective elimination: the projection to the second factor of a closed subset of a
Segre product is closed. The proof is the projective Nullstellensatz together with a
determinant certificate. -/
theorem segre_projection_closed {N1 N2 : ℕ} (K : ProjectiveVariety (N1 * N2))
    (x0 : ProjectivePoint N2)
    (hx0 : x0 ∈ (ProjectiveVariety.closure
      {x : ProjectivePoint N2 | ∃ b : ProjectivePoint N1, segrePoint b x ∈ K.points}).points) :
    ∃ b : ProjectivePoint N1, segrePoint b x0 ∈ K.points := by
  classical
  by_contra hno
  obtain ⟨τ, _, fg, δ, hfgK, hfgH, hspan⟩ := exists_homogeneous_generators K.ideal K.isHomogeneous
  let J : Ideal (Poly N1) := Ideal.span (Set.range (fun i => segreSlice x0.rep (fg i)))
  have hvanK : ∀ b : Point N1, (∀ i, MvPolynomial.aeval b (segreSlice x0.rep (fg i)) = 0) →
      ∀ f ∈ K.ideal, MvPolynomial.aeval (segreVector b x0.rep) f = 0 := by
    intro b hb f hf
    have hle : Ideal.span (Set.range fg) ≤
        RingHom.ker (MvPolynomial.aeval (segreVector b x0.rep) : Poly (N1 * N2) →ₐ[ℂ] ℂ) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, ← eval_segreSlice]
      exact hb i
    exact hle (hspan hf)
  have hzero : ∀ b ∈ MvPolynomial.zeroLocus ℂ J, b = 0 := by
    intro b hb
    by_contra hb0
    apply hno
    refine ⟨Projectivization.mk ℂ b hb0, ?_⟩
    have hseg : segrePoint (Projectivization.mk ℂ b hb0) x0 =
        Projectivization.mk ℂ (segreVector b x0.rep)
          (segreVector_ne_zero _ _ hb0 x0.rep_nonzero) := by
      conv_lhs => rw [← Projectivization.mk_rep x0]
      rw [segrePoint_mk]
    rw [hseg, ProjectiveVariety.mem_points_mk_iff]
    intro f hf
    exact hvanK b (fun i => hb _ (Ideal.subset_span ⟨i, rfl⟩)) f hf
  have hXrad : ∀ i : Fin N1, ∃ r : ℕ, (MvPolynomial.X i : Poly N1) ^ r ∈ J := by
    intro i
    have hmem : (MvPolynomial.X i : Poly N1) ∈ J.radical := by
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
        MvPolynomial.mem_vanishingIdeal_iff]
      intro b hb
      rw [hzero b hb]
      simp
    exact Ideal.mem_radical_iff.mp hmem
  choose rr hrr using hXrad
  let Nm : ℕ := (∑ i, rr i) + 1
  have hXNm : ∀ i, (MvPolynomial.X i : Poly N1) ^ Nm ∈ J := by
    intro i
    have hle : rr i ≤ Nm := by
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (rr j)) (Finset.mem_univ i)
      omega
    rw [show Nm = rr i + (Nm - rr i) by omega, pow_add]
    exact J.mul_mem_right _ (hrr i)
  let D : ℕ := N1 * Nm + (∑ i, δ i) + 1
  have hδD : ∀ i, δ i ≤ D := by
    intro i
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (δ j)) (Finset.mem_univ i)
    omega
  have hmono : ∀ α : Fin N1 →₀ ℕ, α.degree = D → MvPolynomial.monomial α (1 : ℂ) ∈ J := by
    intro α hα
    obtain ⟨i, hi⟩ : ∃ i, Nm ≤ α i := by
      by_contra hh
      push_neg at hh
      have h1 : α.degree ≤ N1 * (Nm - 1) := by
        rw [degree_eq_sum_univ]
        calc ∑ i, α i ≤ ∑ _i : Fin N1, (Nm - 1) :=
              Finset.sum_le_sum (fun i _ => by have := hh i; omega)
          _ = N1 * (Nm - 1) := by simp
      have h2 : N1 * (Nm - 1) ≤ N1 * Nm := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      omega
    have hsplit : MvPolynomial.monomial α (1 : ℂ) =
        (MvPolynomial.X i) ^ Nm * MvPolynomial.monomial (α - Finsupp.single i Nm) 1 := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
      congr 1
      rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)]
    rw [hsplit]
    exact J.mul_mem_right _ (hXNm i)
  have hcert : ∀ α : degFinset N1 D, ∃ c : τ → Poly N1,
      (∀ i, (c i).IsHomogeneous (D - δ i)) ∧
      MvPolynomial.monomial α.1 (1 : ℂ) = ∑ i, c i * segreSlice x0.rep (fg i) := by
    intro α
    have hmem := hmono α.1 (mem_degFinset.mp α.2)
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
    refine ⟨fun i => MvPolynomial.homogeneousComponent (D - δ i) (c i),
      fun i => MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩
    have h1 : MvPolynomial.homogeneousComponent D (MvPolynomial.monomial α.1 (1 : ℂ)) =
        MvPolynomial.monomial α.1 1 := by
      have hm : MvPolynomial.monomial α.1 (1 : ℂ) ∈ MvPolynomial.homogeneousSubmodule (Fin N1) ℂ D :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_monomial _ (mem_degFinset.mp α.2))
      rw [MvPolynomial.homogeneousComponent_of_mem hm, if_pos rfl]
    rw [← h1, ← hc, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact homogeneousComponent_mul_of_isHomogeneous
      (segreSlice_isHomogeneous x0.rep (hfgH i)) (hδD i) (c i)
  choose c hcH hcEq using hcert
  let Psym : degFinset N1 D → MvPolynomial (Fin N1) (Poly N2) := fun α =>
    ∑ i, MvPolynomial.map (algebraMap ℂ (Poly N2)) (c α i) * segreSym (fg i)
  let M : Matrix (degFinset N1 D) (degFinset N1 D) (Poly N2) := fun α β => (Psym α).coeff β.1
  have hspec : ∀ (x : Point N2) (α β : degFinset N1 D),
      MvPolynomial.aeval x (M α β) = (∑ i, c α i * segreSlice x (fg i)).coeff β.1 := by
    intro x α β
    have hmap : MvPolynomial.map (MvPolynomial.aeval x).toRingHom (Psym α) =
        ∑ i, c α i * segreSlice x (fg i) := by
      simp only [Psym, map_sum, map_mul, map_lift, map_segreSym]
    rw [← hmap, MvPolynomial.coeff_map]
    rfl
  have hdetx : ∀ x : Point N2, MvPolynomial.aeval x M.det =
      (Matrix.of fun α β : degFinset N1 D =>
        (∑ i, c α i * segreSlice x (fg i)).coeff β.1).det := by
    intro x
    rw [AlgHom.map_det]
    congr 1
    ext α β
    exact hspec x α β
  have hGvan : M.det ∈ (ProjectiveVariety.closure
      {x : ProjectivePoint N2 | ∃ b : ProjectivePoint N1, segrePoint b x ∈ K.points}).ideal := by
    change M.det ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives _)
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro v ⟨hv, b', hb'⟩
    have hseg : segrePoint b' (Projectivization.mk ℂ v hv) =
        Projectivization.mk ℂ (segreVector b'.rep v)
          (segreVector_ne_zero _ _ b'.rep_nonzero hv) := by
      conv_lhs => rw [← Projectivization.mk_rep b']
      rw [segrePoint_mk]
    rw [hseg] at hb'
    have hK : ∀ f ∈ K.ideal, MvPolynomial.aeval (segreVector b'.rep v) f = 0 :=
      fun f hf => hb' _ _ rfl f hf
    rw [hdetx, ← Matrix.exists_mulVec_eq_zero_iff]
    obtain ⟨k0, hk0⟩ : ∃ k0, b'.rep k0 ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact b'.rep_nonzero (funext hh)
    refine ⟨fun β => ∏ k ∈ β.1.support, b'.rep k ^ β.1 k, ?_, ?_⟩
    · intro h0
      have hβ0 : Finsupp.single k0 D ∈ degFinset N1 D := by
        apply mem_degFinset.mpr
        simp
      have := congrFun h0 ⟨Finsupp.single k0 D, hβ0⟩
      have hD0 : D ≠ 0 := by omega
      simp [Finsupp.support_single_ne_zero _ hD0] at this
      exact hk0 this
    · funext α
      show ∑ β : degFinset N1 D, (∑ i, c α i * segreSlice v (fg i)).coeff β.1 *
        ∏ k ∈ β.1.support, b'.rep k ^ β.1 k = 0
      have hPhom : (∑ i, c α i * segreSlice v (fg i)).IsHomogeneous D := by
        apply MvPolynomial.IsHomogeneous.sum
        intro i _
        have := (hcH α i).mul (segreSlice_isHomogeneous v (hfgH i))
        rwa [Nat.sub_add_cancel (hδD i)] at this
      rw [eval_homogeneous_sum _ hPhom, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_mul, eval_segreSlice, hK _ (hfgK i), mul_zero]
  have hG1 : MvPolynomial.aeval x0.rep M.det = 1 := by
    rw [hdetx]
    have hone : (Matrix.of fun α β : degFinset N1 D =>
        (∑ i, c α i * segreSlice x0.rep (fg i)).coeff β.1) = 1 := by
      ext α β
      rw [Matrix.of_apply, ← hcEq α, MvPolynomial.coeff_monomial, Matrix.one_apply]
      by_cases h : α = β
      · subst h
        simp
      · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg h]
    rw [hone, Matrix.det_one]
  have := hx0 x0.rep x0.rep_nonzero (Projectivization.mk_rep _) _ hGvan
  rw [hG1] at this
  exact one_ne_zero this


/-! ### Images of polynomial maps contain a homogeneous principal open -/

open MvPolynomial in
theorem aeval_smul_of_isHomogeneous {n D : ℕ} {f : Poly n} (hf : f.IsHomogeneous D) (c : ℂ)
    (x : Point n) : aeval (c • x) f = c ^ D * aeval x f := by
  have h := GenericFiber.aeval_scale_of_isWeightedHomogeneous (R := ℂ) (w := 1) hf x c
  have hfun : (fun s => c ^ (1 : Fin n → ℕ) s * x s) = c • x := by
    funext s
    simp
  rw [hfun] at h
  exact h

open MvPolynomial in
/-- A homogeneous component nonzero at `v` gives a nonzero scalar `c` with `h(c v) ≠ 0`. -/
theorem exists_scalar_eval_ne_zero {m : ℕ} (h : Poly m) (v : Point m) (d : ℕ)
    (hd : aeval v (homogeneousComponent d h) ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ aeval (c • v) h ≠ 0 := by
  classical
  let N := h.totalDegree
  let Pv : Polynomial ℂ := ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (aeval v (homogeneousComponent k h)) * Polynomial.X ^ k
  have heval : ∀ c : ℂ, Pv.eval c = aeval (c • v) h := by
    intro c
    conv_rhs => rw [← sum_homogeneousComponent h]
    rw [map_sum, Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous k h)]
    ring
  have hdN : d < N + 1 := by
    by_contra hlt
    apply hd
    rw [homogeneousComponent_eq_zero d h (by omega), map_zero]
  have hcoeff : Pv.coeff d = aeval v (homogeneousComponent d h) := by
    simp only [Pv, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hdN)]
  have hPv : Polynomial.X * Pv ≠ 0 := by
    refine mul_ne_zero Polynomial.X_ne_zero (fun h0 => hd ?_)
    rw [← hcoeff, h0, Polynomial.coeff_zero]
  by_contra hall
  push_neg at hall
  apply hPv
  apply Polynomial.funext
  intro c
  rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_zero]
  by_cases hc : c = 0
  · rw [hc, zero_mul]
  · rw [heval, hall c hc, mul_zero]

/-- The cone source map `(x, t) ↦ (x mod I, T)`, with `none` the scalar variable. -/
def coneSourceMap {n : ℕ} (I : Ideal (Poly n)) :
    MvPolynomial (Option (Fin n)) ℂ →ₐ[ℂ] Polynomial (Poly n ⧸ I) :=
  MvPolynomial.aeval (fun o => Option.elim o Polynomial.X
    (fun i => Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.X i))))

/-- The cone pullback `y_i ↦ t · F_i(x)`. -/
def conePullback {n m : ℕ} (F : Fin m → Poly n) :
    Poly m →ₐ[ℂ] MvPolynomial (Option (Fin n)) ℂ :=
  MvPolynomial.aeval (fun i => MvPolynomial.X none * MvPolynomial.rename some (F i))

theorem coneSourceMap_rename {n : ℕ} (I : Ideal (Poly n)) (f : Poly n) :
    coneSourceMap I (MvPolynomial.rename some f) = Polynomial.C (Ideal.Quotient.mk I f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      Polynomial.algebraMap_apply, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap]
  | add f h hf hh => rw [map_add, map_add, hf, hh, map_add, map_add]
  | mul_X f i hf =>
    rw [map_mul, map_mul, hf, MvPolynomial.rename_X, map_mul, map_mul]
    simp [coneSourceMap]

theorem coneSourceMap_conePullback {n m : ℕ} (I : Ideal (Poly n)) (F : Fin m → Poly n)
    (f : Poly m) :
    coneSourceMap I (conePullback F f) =
      (scalarPolynomialPullback F f).map (Ideal.Quotient.mk I) := by
  have hhom : (coneSourceMap I).comp (conePullback F) =
      (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ ℂ I)).comp (scalarPolynomialPullback F) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, conePullback, scalarPolynomialPullback, MvPolynomial.aeval_X,
      map_mul, coneSourceMap_rename]
    simp [coneSourceMap]
  exact congrArg (fun Φ : Poly m →ₐ[ℂ] Polynomial (Poly n ⧸ I) => Φ f) hhom

/-- The ideal of the closure of a polynomial projective image is the kernel of the
scalar pullback into the coordinate ring (the computation in
`polynomialProjectiveImage_irreducible`). -/
theorem closure_image_ideal_mem_iff {n m : ℕ} (X : AffineVariety n)
    (hX : X.IsIrreducible) (g : Poly n) (hg : g ∉ X.ideal)
    (F : Fin m → Poly n)
    (hF : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 →
      (fun i => MvPolynomial.aeval x (F i)) ≠ 0) (f : Poly m) :
    f ∈ (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal ↔
      (scalarPolynomialPullback F f).map (Ideal.Quotient.mk X.ideal) = 0 := by
  letI : X.ideal.IsPrime := hX
  let q : Poly n →+* Poly n ⧸ X.ideal := Ideal.Quotient.mk X.ideal
  change f ∈ ProjectiveVariety.vanishingIdeal (polynomialProjectiveImage X g F) ↔ _
  constructor
  · intro hf
    have hcoeff (k : ℕ) : (scalarPolynomialPullback F f).coeff k ∈ X.ideal := by
      apply principal_open_vanishing X hX g _ hg
      intro x hx hxg
      let P : Polynomial ℂ :=
        (scalarPolynomialPullback F f).map (MvPolynomial.aeval x).toRingHom
      have hP : P = 0 := by
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
        have hp : Projectivization.mk ℂ w hw ∈ polynomialProjectiveImage X g F :=
          ⟨x, hx, hxg, hw, rfl⟩
        change P.eval t = 0
        rw [eval_scalarPolynomialPullback]
        exact hf (t • w) ⟨htw, heq.symm ▸ hp⟩
      have hz := congrArg (fun Q : Polynomial ℂ => Q.coeff k) hP
      simpa [P] using hz
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero, Polynomial.coeff_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcoeff k)
  · intro hf
    rintro w ⟨hw, hp⟩
    obtain ⟨x, hx, hxg, hv, he⟩ := hp
    let v : Point m := fun i => MvPolynomial.aeval x (F i)
    have hcoeff (k : ℕ) : (scalarPolynomialPullback F f).coeff k ∈ X.ideal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hz := congrArg (fun Q : Polynomial (Poly n ⧸ X.ideal) => Q.coeff k) hf
      simpa [q] using hz
    have hP : (scalarPolynomialPullback F f).map (MvPolynomial.aeval x).toRingHom = 0 := by
      apply Polynomial.ext
      intro k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      exact hx _ (hcoeff k)
    have he' : Projectivization.mk ℂ w hw = Projectivization.mk ℂ v hv := he.symm
    obtain ⟨t, ht⟩ :=
      (Projectivization.mk_eq_mk_iff' ℂ w v hw hv).mp he'
    have hz := congrArg (Polynomial.eval t) hP
    simpa only [eval_scalarPolynomialPullback, Polynomial.eval_zero, ← ht] using hz

open MvPolynomial in
/-- `polynomial_projective_image_contains_open`, proved from the point-level Chevalley
theorem `ImageOpen.polynomial_point_image_contains_open` applied to the cone map
`(x, t) ↦ t · F(x)` on `X × 𝔸¹` with the open `t · g ≠ 0`. -/
theorem polynomial_projective_image_contains_open {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (g : Poly n) (hg : g ∉ X.ideal)
    (F : Fin m → Poly n)
    (hF : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 →
      (fun i => MvPolynomial.aeval x (F i)) ≠ 0) :
    ∃ (G : Poly m) (D : ℕ), G.IsHomogeneous D ∧
      G ∉ (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal ∧
      ∀ p ∈ (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).points,
        MvPolynomial.aeval p.rep G ≠ 0 → p ∈ polynomialProjectiveImage X g F := by
  classical
  letI : X.ideal.IsPrime := hX
  let J := (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal
  let θ := coneSourceMap X.ideal
  let φ := conePullback F
  let P : Ideal (MvPolynomial (Option (Fin n)) ℂ) := RingHom.ker θ
  haveI : P.IsPrime := RingHom.ker_isPrime θ
  let p : MvPolynomial (Option (Fin n)) ℂ := MvPolynomial.X none * rename some g
  have hp : p ∉ P := by
    change θ p ≠ 0
    simp only [p, θ, map_mul, coneSourceMap_rename]
    refine mul_ne_zero ?_ ?_
    · simp [coneSourceMap]
    · rw [Ne, Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  obtain ⟨h, hhQ, hhpt⟩ := ImageOpen.polynomial_point_image_contains_open φ P p hp
  have hQJ : ∀ f, f ∈ P.comap φ ↔ f ∈ J := by
    intro f
    rw [closure_image_ideal_mem_iff X hX g hg F hF f, ← coneSourceMap_conePullback]
    rfl
  obtain ⟨d, hd⟩ : ∃ d, homogeneousComponent d h ∉ J := by
    by_contra hall
    push_neg at hall
    apply hhQ
    rw [hQJ, ← sum_homogeneousComponent h]
    exact J.sum_mem (fun d _ => hall d)
  refine ⟨homogeneousComponent d h, d, homogeneousComponent_isHomogeneous d h, hd, ?_⟩
  intro q hq hGq
  obtain ⟨c, hc0, hc⟩ := exists_scalar_eval_ne_zero h q.rep d hGq
  have hcv : c • q.rep ≠ 0 := smul_ne_zero hc0 q.rep_nonzero
  have hmkc : Projectivization.mk ℂ (c • q.rep) hcv = q := by
    rw [(Projectivization.mk_eq_mk_iff' ℂ _ _ hcv q.rep_nonzero).2 ⟨c, rfl⟩,
      Projectivization.mk_rep]
  have hy : ∀ f ∈ P.comap φ, aeval (c • q.rep) f = 0 := by
    intro f hf
    rw [hQJ] at hf
    exact hq (c • q.rep) hcv hmkc f hf
  obtain ⟨x, hxP, hxp, hxy⟩ := hhpt _ hy hc
  let x' : Point n := fun i => x (some i)
  have hrename : ∀ f : Poly n, aeval x (rename some f) = aeval x' f := by
    intro f
    rw [aeval_rename]
    rfl
  have hx'X : x' ∈ X.points := by
    intro f hf
    have hfP : rename some f ∈ P := by
      change θ (rename some f) = 0
      rw [coneSourceMap_rename, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
    have := hxP _ hfP
    rwa [hrename] at this
  have hxp' : x none * aeval x' g ≠ 0 := by
    have := hxp
    simp only [p, map_mul, MvPolynomial.aeval_X, hrename] at this
    exact this
  have hxg : aeval x' g ≠ 0 := right_ne_zero_of_mul hxp'
  have ht : x none ≠ 0 := left_ne_zero_of_mul hxp'
  have hFx := hF x' hx'X hxg
  have hyeq : c • q.rep = x none • (fun i => aeval x' (F i)) := by
    funext i
    rw [← hxy i]
    simp only [φ, conePullback, aeval_X, map_mul, hrename, Pi.smul_apply, smul_eq_mul]
  refine ⟨x', hx'X, hxg, hFx, ?_⟩
  rw [← hmkc]
  symm
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hcv hFx).2
  exact ⟨x none, hyeq.symm⟩

/-! ### Homogenization at a coordinate and tangent comparison along lines -/

open MvPolynomial in
/-- Homogenization of `f` with respect to the coordinate `Y_a`, in the same variables:
`∑_d Y_a^(deg f - d) f_d`. It agrees with `f` on the hyperplane `Y_a = 1`. -/
def homogenizeAt {m : ℕ} (a : Fin m) (f : Poly m) : Poly m :=
  ∑ d ∈ Finset.range (f.totalDegree + 1),
    X a ^ (f.totalDegree - d) * homogeneousComponent d f

open MvPolynomial in
theorem homogenizeAt_isHomogeneous {m : ℕ} (a : Fin m) (f : Poly m) :
    (homogenizeAt a f).IsHomogeneous f.totalDegree := by
  apply IsHomogeneous.sum
  intro d hd
  have hdle : d ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  have h := (isHomogeneous_X_pow a (f.totalDegree - d)).mul
    (homogeneousComponent_isHomogeneous d f)
  rwa [Nat.sub_add_cancel hdle] at h

open MvPolynomial in
theorem aeval_homogenizeAt_of_eq_one {m : ℕ} (a : Fin m) (f : Poly m) (z : Point m)
    (hz : z a = 1) : aeval z (homogenizeAt a f) = aeval z f := by
  conv_rhs => rw [← sum_homogeneousComponent f]
  simp only [homogenizeAt, map_sum, map_mul, map_pow, aeval_X, hz, one_pow, one_mul]

/-- Two polynomials agreeing on the line `y + t w` have the same differential along `w`. -/
theorem differential_eq_of_line_eq {m : ℕ} (f f' : Poly m) (y w : Point m)
    (h : ∀ t : ℂ, MvPolynomial.aeval (y + t • w) f = MvPolynomial.aeval (y + t • w) f') :
    differential f y w = differential f' y w := by
  have hline : lineRestriction y w f = lineRestriction y w f' := by
    apply Polynomial.funext
    intro t
    rw [eval_lineRestriction, eval_lineRestriction]
    exact h t
  rw [← coeff_one_lineRestriction, ← coeff_one_lineRestriction, hline]

/-! ### Separating coordinate derivations -/

section Derivations

open KaehlerDifferential

/-- If `x` is algebraically independent and every element of the field `K` is algebraic over
the polynomial ring `ℂ[x]`, then the differentials `d x_i` form a `K`-basis of `Ω[K⁄ℂ]`. -/
theorem kaehler_basis_of_algebraic {r : ℕ} (K : Type*) [Field K] [Algebra ℂ K]
    (x : Fin r → K) (hind : AlgebraicIndependent ℂ x)
    (halg : ∀ z : K, ∃ q : Polynomial (MvPolynomial (Fin r) ℂ), q ≠ 0 ∧
      q.eval₂ (MvPolynomial.aeval x : MvPolynomial (Fin r) ℂ →ₐ[ℂ] K).toRingHom z = 0) :
    ∃ b : Module.Basis (Fin r) K (Ω[K⁄ℂ]), ∀ i, b i = D ℂ K (x i) := by
  classical
  let P := MvPolynomial (Fin r) ℂ
  let E := FractionRing P
  letI : Algebra P K := (MvPolynomial.aeval x : P →ₐ[ℂ] K).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ P K := IsScalarTower.of_algebraMap_eq
    (fun c => ((MvPolynomial.aeval x : P →ₐ[ℂ] K).commutes c).symm)
  have hinj : Function.Injective (algebraMap P K) :=
    algebraicIndependent_iff_injective_aeval.mp hind
  letI : Algebra E K := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower P E K := IsScalarTower.of_algebraMap_eq
    (fun p => (IsFractionRing.lift_algebraMap hinj p).symm)
  haveI : Algebra.IsAlgebraic E K := by
    constructor
    intro z
    obtain ⟨q, hq, hz⟩ := halg z
    have hP : IsAlgebraic P z := ⟨q, hq, hz⟩
    exact hP.extendScalars (IsFractionRing.injective P E)
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  haveI : Algebra.FormallyEtale P E := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  haveI : Algebra.FormallyEtale E K := Algebra.FormallyEtale.of_isSeparable E K
  haveI : Algebra.FormallyEtale P K := Algebra.FormallyEtale.comp P E K
  let e := tensorKaehlerEquivOfFormallyEtale ℂ P K
  let b0 := mvPolynomialBasis ℂ (Fin r)
  refine ⟨(b0.baseChange K).map e, fun i => ?_⟩
  have hb0 : b0 i = D ℂ P (MvPolynomial.X i) := by
    apply b0.repr.injective
    rw [Module.Basis.repr_self, mvPolynomialBasis_repr_D_X]
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb0]
  have h := tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap ℂ P K (MvPolynomial.X i)
  rw [← h, LinearEquiv.apply_symm_apply]
  congr 1
  change MvPolynomial.aeval x (MvPolynomial.X i) = x i
  exact MvPolynomial.aeval_X x i

/-- A transcendence basis of an affine coordinate domain made of coordinate functions, of
size the Hilbert dimension. -/
theorem exists_coordinate_transcendence_basis {n r : ℕ} (I : Ideal (Poly n)) [I.IsPrime]
    (hdim : OAI.QuarticPowerFree.affineDimension I = r) :
    ∃ ι : Fin r → Fin n,
      AlgebraicIndependent ℂ (fun k => Ideal.Quotient.mk I (MvPolynomial.X (ι k))) ∧
      ∀ a : Poly n ⧸ I, IsAlgebraic (Algebra.adjoin ℂ
        (Set.range (fun k => Ideal.Quotient.mk I (MvPolynomial.X (ι k))))) a := by
  classical
  let A := Poly n ⧸ I
  let c : Fin n → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X i)
  haveI : FaithfulSMul ℂ A :=
    (faithfulSMul_iff_algebraMap_injective ℂ A).mpr (algebraMap ℂ A).injective
  have htop : Algebra.adjoin ℂ (Set.range c) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    have hc : MvPolynomial.aeval c = Ideal.Quotient.mkₐ ℂ I := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X]
      show c i = _
      rfl
    rw [hc, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective ℂ I
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range c)) A := by
    constructor
    intro a
    have ha : a ∈ Algebra.adjoin ℂ (Set.range c) := htop ▸ Algebra.mem_top
    exact isAlgebraic_algebraMap (R := Algebra.adjoin ℂ (Set.range c)) (A := A) ⟨a, ha⟩
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range c)
  have hcard : Cardinal.mk t = r := by
    rw [ht.cardinalMk_eq_trdeg, ← GenericFiber.affineDimension_eq_trdeg, hdim]
  obtain ⟨e⟩ : Nonempty (t ≃ Fin r) := Cardinal.mk_eq_nat_iff.mp hcard
  have hsub : ∀ k : Fin r, ∃ i, c i = (e.symm k : A) := fun k => hts (e.symm k).2
  choose ι hι using hsub
  have hx : (fun k => Ideal.Quotient.mk I (MvPolynomial.X (ι k))) =
      ((↑) : t → A) ∘ e.symm := by
    funext k
    exact hι k
  refine ⟨ι, ?_, ?_⟩
  · rw [hx]
    exact ht.1.comp _ e.symm.injective
  · intro a
    have hrange : Set.range (fun k => Ideal.Quotient.mk I (MvPolynomial.X (ι k))) =
        Set.range ((↑) : t → A) := by
      rw [hx, EquivLike.range_comp]
    rw [hrange]
    exact ht.isAlgebraic.isAlgebraic a

/-- `affine_separating_coordinate_derivations`: coordinate derivations of the function field
of an irreducible affine variety along a coordinate transcendence basis. -/
theorem affine_separating_coordinate_derivations {n r : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (hdim : X.dimension = r)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (Poly n ⧸ X.ideal) K]
    [IsScalarTower ℂ (Poly n ⧸ X.ideal) K] [IsFractionRing (Poly n ⧸ X.ideal) K] :
    ∃ ι : Fin r → Fin n, ∃ δ : Fin r → Derivation ℂ K K,
      (∀ i j, δ i (algebraMap (Poly n ⧸ X.ideal) K
        (Ideal.Quotient.mk X.ideal (MvPolynomial.X (ι j)))) = if i = j then 1 else 0) ∧
      (∀ i j x, δ i (δ j x) = δ j (δ i x)) ∧
      (∀ x : K, (∀ i, δ i x = 0) → ∃ c : ℂ, algebraMap ℂ K c = x) := by
  classical
  letI : X.ideal.IsPrime := hX
  let A := Poly n ⧸ X.ideal
  let P := MvPolynomial (Fin r) ℂ
  obtain ⟨ι, hind, halgA⟩ := exists_coordinate_transcendence_basis X.ideal hdim
  let xA : Fin r → A := fun k => Ideal.Quotient.mk X.ideal (MvPolynomial.X (ι k))
  let x : Fin r → K := fun k => algebraMap A K (xA k)
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hindK : AlgebraicIndependent ℂ x := hind.map' (f := IsScalarTower.toAlgHom ℂ A K) hAK
  have haevalK : ∀ p : P, MvPolynomial.aeval x p = algebraMap A K (MvPolynomial.aeval xA p) := by
    intro p
    have hcomp : (IsScalarTower.toAlgHom ℂ A K).comp (MvPolynomial.aeval xA) =
        MvPolynomial.aeval x := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [x]
    rw [← hcomp]
    rfl
  letI : Algebra P K := (MvPolynomial.aeval x : P →ₐ[ℂ] K).toRingHom.toAlgebra
  have hA : ∀ a : A, IsAlgebraic P (algebraMap A K a) := by
    intro a
    obtain ⟨q', hq', hz'⟩ := halgA a
    let ε := hind.aevalEquiv
    refine ⟨q'.map (ε.symm : _ →+* P), (Polynomial.map_ne_zero_iff ε.symm.injective).mpr hq', ?_⟩
    change Polynomial.eval₂ (MvPolynomial.aeval x : P →ₐ[ℂ] K).toRingHom (algebraMap A K a)
      (q'.map (ε.symm : _ →+* P)) = 0
    rw [Polynomial.eval₂_map]
    have hring : ((MvPolynomial.aeval x : P →ₐ[ℂ] K).toRingHom.comp (ε.symm : _ →+* P)) =
        (algebraMap A K).comp (algebraMap (Algebra.adjoin ℂ (Set.range xA)) A) := by
      ext s
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [haevalK, ← hind.algebraMap_aevalEquiv]
      simp [ε]
    rw [hring, ← Polynomial.hom_eval₂]
    change algebraMap A K (Polynomial.aeval a q') = 0
    rw [hz', map_zero]
  have halgK : ∀ z : K, ∃ q : Polynomial P, q ≠ 0 ∧
      q.eval₂ (MvPolynomial.aeval x : P →ₐ[ℂ] K).toRingHom z = 0 := by
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    have hz : IsAlgebraic P (algebraMap A K a / algebraMap A K b) := by
      rw [div_eq_mul_inv]
      exact (hA a).mul (IsAlgebraic.inv_iff.mpr (hA b))
    exact hz
  obtain ⟨b, hb⟩ := kaehler_basis_of_algebraic K x hindK halgK
  let δ : Fin r → Derivation ℂ K K := fun i => (b.coord i).compDer (D ℂ K)
  have hδx : ∀ i j, δ i (x j) = if i = j then 1 else 0 := by
    intro i j
    change b.coord i (D ℂ K (x j)) = _
    rw [← hb j, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hzero : ∀ E : Derivation ℂ K K, (∀ k, E (x k) = 0) → ∀ y, E y = 0 := by
    intro E hE y
    have hl : E.liftKaehlerDifferential = 0 := by
      apply b.ext
      intro k
      rw [hb k, Derivation.liftKaehlerDifferential_comp_D, hE k, LinearMap.zero_apply]
    rw [← Derivation.liftKaehlerDifferential_comp_D E y, hl, LinearMap.zero_apply]
  refine ⟨ι, δ, fun i j => hδx i j, ?_, ?_⟩
  · intro i j y
    have hcomm := hzero ⁅δ i, δ j⁆ (fun k => by
      rw [Derivation.commutator_apply, hδx j k, hδx i k]
      split_ifs <;> simp [Derivation.map_one_eq_zero]) y
    rw [Derivation.commutator_apply] at hcomm
    exact sub_eq_zero.mp hcomm
  · intro y hy
    have hD : D ℂ K y = 0 := by
      apply b.ext_elem
      intro i
      rw [map_zero, Finsupp.zero_apply]
      exact hy i
    haveI : Algebra.EssFiniteType A K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors A)
    haveI : Algebra.EssFiniteType ℂ K := Algebra.EssFiniteType.comp ℂ A K
    obtain ⟨c, hc⟩ := TrackD.differential_zero_is_constant K y hD
    exact ⟨c, hc.symm⟩

end Derivations

end

end BridgesB

end DistinctDistances.TrackB
