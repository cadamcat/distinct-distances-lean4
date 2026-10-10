import DistinctDistances.Foundations.Affine
import DistinctDistances.OAIInterface.HomogeneousHilbert
import OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative

/-!
`ProjectivePoint n` is `ℙ(ℂ^n)`, so projective ambient dimension `d` uses
`n = d+1`. This convention also makes the directions of `ℂ^n` use the same
index `n`, without natural subtraction or a coordinate reindexing.
Ideals are radical, homogeneous, and saturated at the irrelevant ideal.
-/

namespace DistinctDistances

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section
open scoped BigOperators

abbrev ProjectivePoint (n : ℕ) := Projectivization ℂ (Point n)

/-- Saturation by the irrelevant ideal, expressed using its coordinate generators. -/
def IrrelevantSaturated {n : ℕ} (I : Ideal (Poly n)) : Prop :=
  ∀ f : Poly n, (∀ i : Fin n, ∃ r : ℕ, MvPolynomial.X i ^ r * f ∈ I) → f ∈ I

structure ProjectiveVariety (n : ℕ) where
  ideal : Ideal (Poly n)
  isRadical : ideal.IsRadical
  isHomogeneous : ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ)
  isSaturated : IrrelevantSaturated ideal

namespace ProjectiveVariety

variable {n : ℕ}

@[ext] theorem ext {V W : ProjectiveVariety n} (h : V.ideal = W.ideal) : V = W := by
  cases V
  cases W
  cases h
  rfl

/-- All representatives satisfy the equations; this avoids choosing a representative. -/
def points (V : ProjectiveVariety n) : Set (ProjectivePoint n) :=
  {p | ∀ (v : Point n) (hv : v ≠ 0), Projectivization.mk ℂ v hv = p →
    v ∈ MvPolynomial.zeroLocus ℂ V.ideal}

instance : Membership (ProjectivePoint n) (ProjectiveVariety n) := ⟨fun V p => p ∈ V.points⟩

def IsIrreducible (V : ProjectiveVariety n) : Prop := V.ideal.IsPrime

def Subvariety (V W : ProjectiveVariety n) : Prop := W.ideal ≤ V.ideal

noncomputable abbrev restrictionSpace (V : ProjectiveVariety n) (D : ℕ) :
    Submodule ℂ (Poly n ⧸ V.ideal) := OAI.PiExponentJets.W64.quotientSection V.ideal D

instance restrictionSpace_finite (V : ProjectiveVariety n) (D : ℕ) :
    Module.Finite ℂ (V.restrictionSpace D) := inferInstance

noncomputable def hilbert (V : ProjectiveVariety n) (D : ℕ) : ℕ :=
  Module.finrank ℂ (V.restrictionSpace D)

noncomputable abbrev hilbertPolynomial (V : ProjectiveVariety n) : Polynomial ℚ :=
  OAI.PiExponentJets.W22.actualHP V.ideal V.isHomogeneous

noncomputable def dimension (V : ProjectiveVariety n) : ℕ := V.hilbertPolynomial.natDegree

noncomputable def degree (V : ProjectiveVariety n) : ℚ :=
  OAI.PiExponentJets.W22.actualMultiplicity V.ideal V.isHomogeneous V.dimension

def affineCone (V : ProjectiveVariety n) : AffineVariety n := ⟨V.ideal, V.isRadical⟩

def nonzeroRepresentatives (T : Set (ProjectivePoint n)) : Set (Point n) :=
  {v | ∃ hv : v ≠ 0, Projectivization.mk ℂ v hv ∈ T}

/-- Canonical homogeneous ideal of a projective point set, with all degrees. -/
def vanishingIdeal (T : Set (ProjectivePoint n)) : Ideal (Poly n) :=
  MvPolynomial.vanishingIdeal ℂ (nonzeroRepresentatives T)

private theorem aeval_smul_of_isHomogeneous_root {n : ℕ} (c : ℂ) (v : Point n)
    (f : Poly n) (d : ℕ) (hf : f.IsHomogeneous d) :
    MvPolynomial.aeval (c • v) f = c ^ d * MvPolynomial.aeval v f := by
  simp only [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_eq, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdegree : e.degree = d := by
    have h := hf (Finsupp.mem_support_iff.mp he)
    have h' : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) e = d := by
      simpa only [Pi.one_def] using h
    rw [← Finsupp.degree_eq_weight_one] at h'
    exact h'
  have hprod :
      (∏ i ∈ e.support, (c * v i) ^ e i) =
        c ^ d * ∏ i ∈ e.support, v i ^ e i := by
    calc
      (∏ i ∈ e.support, (c * v i) ^ e i) =
          ∏ i ∈ e.support, c ^ e i * v i ^ e i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [mul_pow]
      _ = (∏ i ∈ e.support, c ^ e i) * ∏ i ∈ e.support, v i ^ e i := by
        rw [Finset.prod_mul_distrib]
      _ = c ^ d * ∏ i ∈ e.support, v i ^ e i := by
        rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hdegree]
  rw [hprod]
  ring

theorem vanishingIdeal_homogeneous (T : Set (ProjectivePoint n)) :
    (vanishingIdeal T).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
  classical
  rw [Ideal.isHomogeneous_iff_forall_subset]
  intro d f hf
  change GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) d f ∈
    vanishingIdeal T
  rw [GradedRing.proj_apply]
  change (MvPolynomial.decomposition.decompose' f d : Poly n) ∈ vanishingIdeal T
  rw [MvPolynomial.decomposition.decompose'_apply]
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  intro v hv
  obtain ⟨hv, hp⟩ := hv
  let P : Polynomial ℂ :=
    ∑ e ∈ Finset.range (f.totalDegree + 1),
      Polynomial.C (MvPolynomial.aeval v (MvPolynomial.homogeneousComponent e f)) *
        Polynomial.X ^ e
  have hEval (c : ℂ) : P.eval c = MvPolynomial.aeval (c • v) f := by
    calc
      P.eval c = ∑ e ∈ Finset.range (f.totalDegree + 1),
          MvPolynomial.aeval v (MvPolynomial.homogeneousComponent e f) * c ^ e := by
        simp [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
      _ = ∑ e ∈ Finset.range (f.totalDegree + 1),
          c ^ e * MvPolynomial.aeval v (MvPolynomial.homogeneousComponent e f) := by
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = ∑ e ∈ Finset.range (f.totalDegree + 1),
          MvPolynomial.aeval (c • v) (MvPolynomial.homogeneousComponent e f) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [aeval_smul_of_isHomogeneous_root c v
          (MvPolynomial.homogeneousComponent e f) e
          (MvPolynomial.homogeneousComponent_isHomogeneous e f)]
      _ = MvPolynomial.aeval (c • v) f := by
        conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent f]
        simp only [map_sum]
  have hroots : Set.Infinite {c : ℂ | P.eval c = 0} := by
    have hnonzero : ({(0 : ℂ)} : Set ℂ)ᶜ ⊆ {c : ℂ | P.eval c = 0} := by
      intro c hc
      have hc0 : c ≠ 0 := by simpa using hc
      have hcv : c • v ≠ 0 := smul_ne_zero hc0 hv
      have heq : Projectivization.mk ℂ (c • v) hcv = Projectivization.mk ℂ v hv :=
        (Projectivization.mk_eq_mk_iff' ℂ (c • v) v hcv hv).2 ⟨c, rfl⟩
      have hrep : c • v ∈ nonzeroRepresentatives T := ⟨hcv, heq.symm ▸ hp⟩
      change P.eval c = 0
      rw [hEval c]
      exact (MvPolynomial.mem_vanishingIdeal_iff.mp hf) (c • v) hrep
    exact Set.Infinite.mono hnonzero (Set.finite_singleton (0 : ℂ)).infinite_compl
  have hP : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    simpa only [Polynomial.IsRoot, Set.mem_setOf_eq] using hroots
  have hcoeff (d : ℕ) :
      P.coeff d = MvPolynomial.aeval v (MvPolynomial.homogeneousComponent d f) := by
    by_cases hd : d ≤ f.totalDegree
    · have hdmem : d ∈ Finset.range (f.totalDegree + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
      simp only [P]
      rw [Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single d]
      · simp [Polynomial.coeff_C_mul_X_pow]
      · intro e he hed
        rw [Polynomial.coeff_C_mul_X_pow]
        simp only [if_neg hed.symm]
      · intro hnot
        exact (hnot hdmem).elim
    · have hlt : f.totalDegree < d := Nat.lt_of_not_ge hd
      have hnot : d ∉ Finset.range (f.totalDegree + 1) := by
        simp only [Finset.mem_range]
        omega
      simp only [P]
      rw [Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_zero]
      · rw [MvPolynomial.homogeneousComponent_eq_zero d f hlt]
        simp
      · intro e he
        have he' : e ≤ f.totalDegree := Nat.le_of_lt_succ (Finset.mem_range.mp he)
        have hed : d ≠ e := ne_of_gt (lt_of_le_of_lt he' hlt)
        rw [Polynomial.coeff_C_mul_X_pow]
        simp only [if_neg hed]
  rw [← hcoeff d, hP]
  simp

theorem vanishingIdeal_saturated (T : Set (ProjectivePoint n)) :
    IrrelevantSaturated (vanishingIdeal T) := by
  intro f hf
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro v ⟨hv, hp⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin n, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    exact not_not.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨r, hr⟩ := hf i
  have hzero : MvPolynomial.aeval v (MvPolynomial.X i ^ r * f) = 0 :=
    (MvPolynomial.mem_vanishingIdeal_iff.mp hr) v ⟨hv, hp⟩
  have hzero' : (v i) ^ r * MvPolynomial.aeval v f = 0 := by
    simpa only [map_mul, map_pow, MvPolynomial.aeval_X] using hzero
  exact (mul_eq_zero.mp hzero').resolve_left (pow_ne_zero _ hi)

/-- Projective Zariski closure; no Hilbert or projection estimate is a field. -/
def closure (T : Set (ProjectivePoint n)) : ProjectiveVariety n :=
  ⟨vanishingIdeal T, AffineVariety.vanishingIdeal_isRadical _,
    vanishingIdeal_homogeneous T, vanishingIdeal_saturated T⟩

def IsComponentOf (V W : ProjectiveVariety n) : Prop := V.ideal ∈ W.ideal.minimalPrimes

abbrev Component (V : ProjectiveVariety n) := {W : ProjectiveVariety n // W.IsComponentOf V}

theorem finite_components (V : ProjectiveVariety n) :
    {W : ProjectiveVariety n | W.IsComponentOf V}.Finite := by
  have himage :
      (ProjectiveVariety.ideal '' {W : ProjectiveVariety n | W.IsComponentOf V}).Finite := by
    refine (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n) V.ideal).subset ?_
    rintro I ⟨W, hW, rfl⟩
    exact hW
  apply himage.of_finite_image
  intro W hW W' hW' h
  exact ProjectiveVariety.ext h

instance componentFinite (V : ProjectiveVariety n) : Fintype V.Component :=
  (finite_components V).fintype

def IsPure (V : ProjectiveVariety n) (k : ℕ) : Prop :=
  ∀ W : V.Component, W.val.dimension = k

private theorem aeval_smul_of_isHomogeneous {n : ℕ} (c : ℂ) (v : Point n)
    (f : Poly n) (d : ℕ) (hf : f.IsHomogeneous d) :
    MvPolynomial.aeval (c • v) f = c ^ d * MvPolynomial.aeval v f := by
  simp only [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_eq, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdegree : e.degree = d := by
    have h := hf (Finsupp.mem_support_iff.mp he)
    have h' : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) e = d := by
      simpa only [Pi.one_def] using h
    rw [← Finsupp.degree_eq_weight_one] at h'
    exact h'
  have hprod :
      (∏ i ∈ e.support, (c * v i) ^ e i) =
        c ^ d * ∏ i ∈ e.support, v i ^ e i := by
    calc
      (∏ i ∈ e.support, (c * v i) ^ e i) =
          ∏ i ∈ e.support, c ^ e i * v i ^ e i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [mul_pow]
      _ = (∏ i ∈ e.support, c ^ e i) * ∏ i ∈ e.support, v i ^ e i := by
        rw [Finset.prod_mul_distrib]
      _ = c ^ d * ∏ i ∈ e.support, v i ^ e i := by
        rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hdegree]
  rw [hprod]
  ring

theorem mem_points_mk_iff (V : ProjectiveVariety n) (v : Point n) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ V.points ↔ v ∈ V.affineCone.points := by
  constructor
  · intro hp
    exact hp v hv rfl
  · intro hcone w hw h f hf
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ w v hw hv).mp h
    have hcomp (d : ℕ) :
        MvPolynomial.aeval w (MvPolynomial.homogeneousComponent d f) = 0 := by
      rw [← hc, aeval_smul_of_isHomogeneous c v (MvPolynomial.homogeneousComponent d f) d
        (MvPolynomial.homogeneousComponent_isHomogeneous d f)]
      exact mul_eq_zero_of_right _ (hcone _
        (MvPolynomial.homogeneousComponent_mem_of_mem V.isHomogeneous hf d))
    rw [← MvPolynomial.sum_homogeneousComponent f]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    exact hcomp d

theorem vanishingIdeal_points (V : ProjectiveVariety n) :
    vanishingIdeal V.points = V.ideal := by
  ext f
  constructor
  · intro hf
    apply V.isSaturated
    intro i
    refine ⟨1, ?_⟩
    rw [pow_one]
    change MvPolynomial.X i * f ∈ V.affineCone.ideal
    rw [← AffineVariety.vanishingIdeal_points V.affineCone]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hp : Projectivization.mk ℂ x hx0 ∈ V.points :=
        (ProjectiveVariety.mem_points_mk_iff V x hx0).2 hx
      have hfx : MvPolynomial.aeval x f = 0 :=
        (MvPolynomial.mem_vanishingIdeal_iff.mp hf) x ⟨hx0, hp⟩
      rw [map_mul, MvPolynomial.aeval_X, hfx, mul_zero]
  · intro hf
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro v ⟨hv, hp⟩
    exact MvPolynomial.mem_zeroLocus_iff.mp (hp v hv rfl) f hf

theorem subset_closure (T : Set (ProjectivePoint n)) : T ⊆ (closure T).points := by
  intro p hp v hv he
  intro f hf
  exact hf v ⟨hv, he.symm ▸ hp⟩

theorem hilbert_eventually (V : ProjectiveVariety n) :
    ∃ N : ℕ, ∀ D : ℕ, N < D →
      (V.hilbert D : ℚ) = V.hilbertPolynomial.eval (D : ℚ) :=
  OAI.PiExponentJets.W22.actualHP_eventually V.ideal V.isHomogeneous

private theorem affineCone_hilbert_eq_cumulative (V : ProjectiveVariety n) (D : ℕ) :
    V.affineCone.hilbert D =
      ∑ j ∈ Finset.range (D + 1), V.hilbert j := by
  change Module.finrank ℂ
      ((OAI.QuarticPowerFree.totalSpace (K := ℂ) D).map
        (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap) = _
  have hspace : OAI.QuarticPowerFree.totalSpace (K := ℂ) D =
      MvPolynomial.restrictTotalDegree (Fin n) ℂ D := by
    ext f
    simp only [OAI.QuarticPowerFree.mem_totalSpace, MvPolynomial.mem_restrictTotalDegree]
  rw [hspace]
  change Module.finrank ℂ
    (OAI.PiExponentJets.W24.quotientDegreeFiltration V.ideal D) = _
  rw [OAI.PiExponentJets.W25.quotientDegreeFiltration_finrank_eq_sum
    V.ideal V.isHomogeneous D]
  rfl

theorem dimension_cone (V : ProjectiveVariety n) (hV : V.points.Nonempty) :
    V.affineCone.dimension = V.dimension + 1 := by
  classical
  obtain ⟨p, hp⟩ := hV
  have hcoord : ∃ i : Fin n, p.rep i ≠ 0 := by
    by_contra h
    apply p.rep_nonzero
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨i, hi⟩ := hcoord
  have hrep : p.rep ∈ MvPolynomial.zeroLocus ℂ V.ideal :=
    hp p.rep p.rep_nonzero (Projectivization.mk_rep p)
  have hsection_pos (D : ℕ) : 0 < V.hilbert D := by
    change 0 < Module.finrank ℂ (V.restrictionSpace D)
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    let x : V.restrictionSpace D :=
      ⟨Ideal.Quotient.mk V.ideal (MvPolynomial.X i ^ D),
        Submodule.mem_map.mpr ⟨MvPolynomial.X i ^ D,
          MvPolynomial.isHomogeneous_X_pow i D, rfl⟩⟩
    refine ⟨x, ?_⟩
    intro hx
    have hx0 : Ideal.Quotient.mk V.ideal (MvPolynomial.X i ^ D) = 0 :=
      congrArg Subtype.val hx
    have hmem : MvPolynomial.X i ^ D ∈ V.ideal :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx0
    have heval := MvPolynomial.mem_zeroLocus_iff.mp hrep _ hmem
    have heval' : (p.rep i) ^ D = 0 := by simpa using heval
    exact (pow_ne_zero D hi) heval'
  have hpoly_ne : V.hilbertPolynomial ≠ 0 := by
    intro hzero
    obtain ⟨N, hN⟩ := V.hilbert_eventually
    have heq := hN (N + 1) (by omega)
    rw [hzero, Polynomial.eval_zero] at heq
    have hpos : 0 < (V.hilbert (N + 1) : ℚ) := by exact_mod_cast hsection_pos (N + 1)
    rw [heq] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨N, hN⟩ := V.hilbert_eventually
  obtain ⟨q, hqdeg, hq⟩ :=
    OAI.PiExponentJets.W24.exists_eventual_cumulative_polynomial
      V.hilbert V.hilbertPolynomial hpoly_ne (N + 1) (by
        intro D hD
        exact (hN D (by omega)).symm)
  obtain ⟨NA, hA⟩ := Filter.eventually_atTop.mp V.affineCone.hilbert_eventually
  have hpoly := OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    V.affineCone.hilbertPolynomial q
    (Filter.eventually_atTop.mpr ⟨max NA (N + 1), by
      intro D hD
      have hDA : NA ≤ D := le_trans (le_max_left _ _) hD
      have hDN : N + 1 ≤ D := le_trans (le_max_right _ _) hD
      calc
        V.affineCone.hilbertPolynomial.eval (D : ℚ) =
            (V.affineCone.hilbert D : ℚ) := (hA D hDA).symm
        _ = ((∑ j ∈ Finset.range (D + 1), V.hilbert j : ℕ) : ℚ) := by
          rw [affineCone_hilbert_eq_cumulative]
        _ = q.eval (D : ℚ) := (hq D hDN).symm⟩)
  change V.affineCone.hilbertPolynomial.natDegree =
    V.hilbertPolynomial.natDegree + 1
  rw [hpoly]
  exact hqdeg

theorem degree_cone (V : ProjectiveVariety n) : V.affineCone.degree = V.degree := by
  classical
  by_cases hV : V.points.Nonempty
  · obtain ⟨p, hp⟩ := hV
    have hcoord : ∃ i : Fin n, p.rep i ≠ 0 := by
      by_contra h
      apply p.rep_nonzero
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    obtain ⟨i, hi⟩ := hcoord
    have hrep : p.rep ∈ MvPolynomial.zeroLocus ℂ V.ideal :=
      hp p.rep p.rep_nonzero (Projectivization.mk_rep p)
    have hsection_pos (D : ℕ) : 0 < V.hilbert D := by
      change 0 < Module.finrank ℂ (V.restrictionSpace D)
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      let x : V.restrictionSpace D :=
        ⟨Ideal.Quotient.mk V.ideal (MvPolynomial.X i ^ D),
          Submodule.mem_map.mpr ⟨MvPolynomial.X i ^ D,
            MvPolynomial.isHomogeneous_X_pow i D, rfl⟩⟩
      refine ⟨x, ?_⟩
      intro hx
      have hx0 : Ideal.Quotient.mk V.ideal (MvPolynomial.X i ^ D) = 0 :=
        congrArg Subtype.val hx
      have hmem : MvPolynomial.X i ^ D ∈ V.ideal :=
        Ideal.Quotient.eq_zero_iff_mem.mp hx0
      have heval := MvPolynomial.mem_zeroLocus_iff.mp hrep _ hmem
      have heval' : (p.rep i) ^ D = 0 := by simpa using heval
      exact (pow_ne_zero D hi) heval'
    have hpoly_ne : V.hilbertPolynomial ≠ 0 := by
      intro hzero
      obtain ⟨N, hN⟩ := V.hilbert_eventually
      have heq := hN (N + 1) (by omega)
      rw [hzero, Polynomial.eval_zero] at heq
      have hpos : 0 < (V.hilbert (N + 1) : ℚ) := by
        exact_mod_cast hsection_pos (N + 1)
      rw [heq] at hpos
      exact (lt_irrefl 0) hpos
    obtain ⟨N, hN⟩ := V.hilbert_eventually
    let M := N + 1
    let pref : Polynomial ℚ :=
      OAI.PiExponentJets.W24.polynomialPrefix V.hilbertPolynomial
    let c : ℚ :=
      (∑ j ∈ Finset.range M, (V.hilbert j : ℚ)) - pref.eval (M : ℚ)
    let q : Polynomial ℚ :=
      pref.comp (Polynomial.X + Polynomial.C 1) + Polynomial.C c
    have hsum (m : ℕ) (hm : M ≤ m) :
        pref.eval (m : ℚ) + c =
          ∑ j ∈ Finset.range m, (V.hilbert j : ℚ) := by
      induction m, hm using Nat.le_induction with
      | base =>
          simp [c]
      | succ m hm ih =>
          rw [OAI.PiExponentJets.W24.polynomialPrefix_eval,
            Finset.sum_range_succ,
            ← OAI.PiExponentJets.W24.polynomialPrefix_eval,
            (hN m (by omega)).symm,
            Finset.sum_range_succ]
          linarith
    have hq_eval (D : ℕ) (hD : M ≤ D) :
        q.eval (D : ℚ) =
          ((∑ j ∈ Finset.range (D + 1), V.hilbert j : ℕ) : ℚ) := by
      calc
        q.eval (D : ℚ) = pref.eval ((D + 1 : ℕ) : ℚ) + c := by
          simp [q, pref, Polynomial.eval_add, Polynomial.eval_comp,
            Polynomial.eval_X, Polynomial.eval_C, Nat.cast_add, Nat.cast_one]
        _ = ∑ j ∈ Finset.range (D + 1), (V.hilbert j : ℚ) :=
          hsum (D + 1) (by omega)
        _ = ((∑ j ∈ Finset.range (D + 1), V.hilbert j : ℕ) : ℚ) := by simp
    have hpref_deg : pref.natDegree = V.hilbertPolynomial.natDegree + 1 := by
      exact OAI.PiExponentJets.W24.polynomialPrefix_natDegree
        V.hilbertPolynomial hpoly_ne
    have hq_deg : q.natDegree = V.hilbertPolynomial.natDegree + 1 := by
      simp only [q, Polynomial.natDegree_add_C, Polynomial.natDegree_comp,
        Polynomial.natDegree_add_C, Polynomial.natDegree_X, mul_one]
      exact hpref_deg
    obtain ⟨NA, hA⟩ := Filter.eventually_atTop.mp V.affineCone.hilbert_eventually
    have hpoly : V.affineCone.hilbertPolynomial = q := by
      apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
      filter_upwards [Filter.eventually_atTop.mpr ⟨max NA M, by
        intro D hD
        have hDA : NA ≤ D := le_trans (le_max_left _ _) hD
        have hDM : M ≤ D := le_trans (le_max_right _ _) hD
        calc
          V.affineCone.hilbertPolynomial.eval (D : ℚ) =
              (V.affineCone.hilbert D : ℚ) := (hA D hDA).symm
          _ = ((∑ j ∈ Finset.range (D + 1), V.hilbert j : ℕ) : ℚ) := by
            exact_mod_cast affineCone_hilbert_eq_cumulative V D
          _ = q.eval (D : ℚ) := (hq_eval D hDM).symm⟩] with D hD
      exact hD
    have hpref0 : pref ≠ 0 := by
      intro hz
      have hnat := congrArg Polynomial.natDegree hz
      rw [hpref_deg, Polynomial.natDegree_zero] at hnat
      omega
    have hcomp0 : (pref.comp (Polynomial.X + Polynomial.C (1 : ℚ))) ≠ 0 := by
      apply (Polynomial.comp_X_add_C_ne_zero_iff).2
      exact hpref0
    have hcomp_degree :
        (pref.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree =
          ((V.hilbertPolynomial.natDegree + 1 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hcomp0, Polynomial.natDegree_comp,
        hpref_deg, Polynomial.natDegree_X_add_C, mul_one]
    have hconst_degree : (Polynomial.C c).degree <
        (pref.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree := by
      calc
        (Polynomial.C c).degree ≤ 0 := Polynomial.degree_C_le
        _ < ((V.hilbertPolynomial.natDegree + 1 : ℕ) : WithBot ℕ) :=
          WithBot.coe_lt_coe.mpr (Nat.zero_lt_succ _)
        _ = (pref.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree :=
          hcomp_degree.symm
    have hinner : (Polynomial.X + Polynomial.C (1 : ℚ)).natDegree ≠ 0 := by
      simp
    have hq_leading : q.leadingCoeff = pref.leadingCoeff := by
      dsimp [q]
      rw [Polynomial.leadingCoeff_add_of_degree_lt' hconst_degree,
        Polynomial.leadingCoeff_comp hinner,
        Polynomial.leadingCoeff_X_add_C]
      simp
    have hq_coeff : q.coeff (V.hilbertPolynomial.natDegree + 1) =
        V.hilbertPolynomial.leadingCoeff *
          ((V.hilbertPolynomial.natDegree + 1 : ℕ) : ℚ)⁻¹ := by
      have hpref_coeff : pref.leadingCoeff =
          V.hilbertPolynomial.leadingCoeff *
            ((V.hilbertPolynomial.natDegree + 1 : ℕ) : ℚ)⁻¹ := by
        calc
          pref.leadingCoeff = pref.coeff pref.natDegree := rfl
          _ = pref.coeff (V.hilbertPolynomial.natDegree + 1) := by
            rw [hpref_deg]
          _ = V.hilbertPolynomial.leadingCoeff *
              ((V.hilbertPolynomial.natDegree + 1 : ℕ) : ℚ)⁻¹ := by
            simpa only [pref, Nat.cast_add, Nat.cast_one] using
              OAI.PiExponentJets.W24.polynomialPrefix_top_coefficient
                V.hilbertPolynomial
      calc
        q.coeff (V.hilbertPolynomial.natDegree + 1) = q.coeff q.natDegree := by
          rw [hq_deg]
        _ = q.leadingCoeff := Polynomial.coeff_natDegree
        _ = pref.leadingCoeff := hq_leading
        _ = V.hilbertPolynomial.leadingCoeff *
            ((V.hilbertPolynomial.natDegree + 1 : ℕ) : ℚ)⁻¹ := hpref_coeff
    have hdim := ProjectiveVariety.dimension_cone V ⟨p, hp⟩
    have hleading : V.hilbertPolynomial.leadingCoeff =
        V.hilbertPolynomial.coeff V.dimension := by rfl
    change ((V.affineCone.dimension).factorial : ℚ) *
        V.affineCone.hilbertPolynomial.coeff V.affineCone.dimension =
      V.hilbertPolynomial.coeff V.dimension * (V.dimension.factorial : ℚ)
    rw [hdim, hpoly]
    have hq_coeff' : q.coeff (V.dimension + 1) =
        V.hilbertPolynomial.coeff V.dimension * ((V.dimension + 1 : ℕ) : ℚ)⁻¹ := by
      simpa only [ProjectiveVariety.dimension, hleading] using hq_coeff
    rw [hq_coeff', Nat.factorial_succ]
    push_cast
    field_simp
  · have hEmpty : V.points = ∅ := by
      ext p
      constructor
      · intro hp
        exact hV ⟨p, hp⟩
      · simp
    have hI : V.ideal = ⊤ := by
      rw [← V.vanishingIdeal_points]
      simp [ProjectiveVariety.vanishingIdeal,
        ProjectiveVariety.nonzeroRepresentatives, hEmpty,
        MvPolynomial.vanishingIdeal_empty]
    have hzeroRank (D : ℕ) : V.affineCone.hilbert D = 0 := by
      change Module.finrank ℂ
        ((OAI.QuarticPowerFree.totalSpace (K := ℂ) D).map
          (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap) = 0
      rw [hI]
      have hmk : (Ideal.Quotient.mkₐ ℂ (⊤ : Ideal (Poly n))).toLinearMap = 0 := by
        ext f
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)
      rw [hmk]
      simp
    have hpoly0 : V.affineCone.hilbertPolynomial = 0 := by
      apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
      filter_upwards [V.affineCone.hilbert_eventually] with D hD
      rw [hzeroRank D] at hD
      simpa using hD.symm
    have htopHom : (⊤ : Ideal (Poly n)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
      rw [← hI]
      exact V.isHomogeneous
    have hAffineDegree : V.affineCone.degree = 0 := by
      change OAI.QuarticPowerFree.affineDegree V.ideal = 0
      have hcoord0 : OAI.QuarticPowerFree.coordinateHilbert V.ideal = 0 := hpoly0
      simp [OAI.QuarticPowerFree.affineDegree,
        OAI.QuarticPowerFree.affineDimension, hcoord0]
    have hProjectiveDegree : V.degree = 0 := by
      change OAI.PiExponentJets.W22.actualMultiplicity
        V.ideal V.isHomogeneous V.dimension = 0
      rw [OAI.PiExponentJets.W22.actualMultiplicity_congr
        V.isHomogeneous htopHom hI,
        OAI.PiExponentJets.W22.actualMultiplicity_top htopHom]
    rw [hAffineDegree, hProjectiveDegree]

end ProjectiveVariety

namespace ProjectiveFamily

variable {n : ℕ}

abbrev Family (n : ℕ) := Finset (ProjectiveVariety n)

def IsPure (F : Family n) (k : ℕ) : Prop :=
  ∀ V ∈ F, V.IsIrreducible ∧ V.dimension = k

def degree (F : Family n) : ℚ := ∑ V ∈ F, V.degree

def locus (F : Family n) : ProjectiveVariety n :=
  ProjectiveVariety.closure (⋃ V ∈ F, V.points)

def hilbert (F : Family n) (D : ℕ) : ℕ := (locus F).hilbert D

def ComponentsDefinedInDegree (F : Family n) (L : ℕ) : Prop :=
  ∃ E : Set (Poly n), (∀ f ∈ E, ∃ d ≤ L, f.IsHomogeneous d) ∧
    ∀ V ∈ F, V.ideal ∈ (Ideal.span E).minimalPrimes

theorem points_locus (F : Family n) :
    (locus F).points = ⋃ V ∈ F, V.points := by
  classical
  ext p
  constructor
  · intro hp
    by_contra hnot
    have hnot' : ¬ ∃ V : ProjectiveVariety n, ∃ (_ : V ∈ F), p ∈ V.points := by
      simpa only [Set.mem_iUnion] using hnot
    have hchoose : ∀ V ∈ F, ∃ f : Poly n, f ∈ V.ideal ∧
        MvPolynomial.aeval p.rep f ≠ 0 := by
      intro V hV
      have hVnot : p ∉ V := by
        intro hpV
        exact hnot' ⟨V, ⟨hV, hpV⟩⟩
      have hnotforall : ¬ ∀ f, f ∈ V.ideal → MvPolynomial.aeval p.rep f = 0 := by
        intro hzero
        have hcone : p.rep ∈ V.affineCone.points := by
          change p.rep ∈ MvPolynomial.zeroLocus ℂ V.ideal
          exact MvPolynomial.mem_zeroLocus_iff.mpr hzero
        have hpV : Projectivization.mk ℂ p.rep p.rep_nonzero ∈ V :=
          (ProjectiveVariety.mem_points_mk_iff V p.rep p.rep_nonzero).2 hcone
        exact hVnot (by simpa using hpV)
      push Not at hnotforall
      exact hnotforall
    let g : ProjectiveVariety n → Poly n := fun V =>
      if hV : V ∈ F then Classical.choose (hchoose V hV) else 1
    have hg : ∀ V, V ∈ F → g V ∈ V.ideal ∧ MvPolynomial.aeval p.rep (g V) ≠ 0 := by
      intro V hV
      simpa [g, hV] using Classical.choose_spec (hchoose V hV)
    let q : Poly n := ∏ V ∈ F, g V
    have hq : q ∈ ProjectiveVariety.vanishingIdeal (⋃ V ∈ F, V.points) := by
      apply MvPolynomial.mem_vanishingIdeal_iff.mpr
      rintro v ⟨hv, hpv⟩
      simp only [Set.mem_iUnion] at hpv
      obtain ⟨W, hW, hpW⟩ := hpv
      have hzero : MvPolynomial.aeval v (g W) = 0 :=
        MvPolynomial.mem_zeroLocus_iff.mp (hpW v hv rfl) (g W) (hg W hW).1
      dsimp [q]
      rw [map_prod]
      exact Finset.prod_eq_zero hW hzero
    have hqzero : MvPolynomial.aeval p.rep q = 0 := by
      change p ∈ (ProjectiveVariety.closure (⋃ V ∈ F, V.points)).points at hp
      have hzero : p.rep ∈ MvPolynomial.zeroLocus ℂ
          (ProjectiveVariety.vanishingIdeal (⋃ V ∈ F, V.points)) :=
        hp p.rep p.rep_nonzero (Projectivization.mk_rep p)
      exact MvPolynomial.mem_zeroLocus_iff.mp hzero q hq
    have hqne : MvPolynomial.aeval p.rep q ≠ 0 := by
      dsimp [q]
      rw [map_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro V hV
      exact (hg V hV).2
    exact hqne hqzero
  · intro hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨V, hV, hpV⟩ := hp
    have hpUnion : p ∈ ⋃ W ∈ F, W.points := by
      simp only [Set.mem_iUnion]
      exact ⟨V, hV, hpV⟩
    simpa [locus] using ProjectiveVariety.subset_closure
      (⋃ W ∈ F, W.points) hpUnion

private theorem points_nonempty_of_isIrreducible (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) : V.points.Nonempty := by
  by_contra h
  have hEmpty : V.points = ∅ := by
    ext p
    constructor
    · intro hp
      exact h ⟨p, hp⟩
    · simp
  have htop : V.ideal = ⊤ := by
    rw [← V.vanishingIdeal_points]
    simp [ProjectiveVariety.vanishingIdeal,
      ProjectiveVariety.nonzeroRepresentatives, hEmpty,
      MvPolynomial.vanishingIdeal_empty]
  exact hV.ne_top htop

private theorem vanishingIdeal_iUnion_eq_iInf (F : ProjectiveFamily.Family n) :
    ProjectiveVariety.vanishingIdeal (⋃ V ∈ F, V.points) = ⨅ V ∈ F, V.ideal := by
  classical
  ext f
  constructor
  · intro hf
    change f ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives (⋃ V ∈ F, V.points)) at hf
    simp only [Ideal.mem_iInf]
    intro V hV
    have hfV : f ∈ ProjectiveVariety.vanishingIdeal V.points := by
      apply MvPolynomial.mem_vanishingIdeal_iff.mpr
      intro x hx
      rcases hx with ⟨hx0, hxV⟩
      have hxUnion : x ∈ ProjectiveVariety.nonzeroRepresentatives
          (⋃ W ∈ F, W.points) := by
        exact ⟨hx0, by
          simp only [Set.mem_iUnion]
          exact ⟨V, hV, hxV⟩⟩
      exact (MvPolynomial.mem_vanishingIdeal_iff.mp hf) x hxUnion
    rw [ProjectiveVariety.vanishingIdeal_points] at hfV
    exact hfV
  · intro hf
    change f ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives (⋃ V ∈ F, V.points))
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro x hx
    rcases hx with ⟨hx0, hxUnion⟩
    simp only [Set.mem_iUnion] at hxUnion
    obtain ⟨V, hV, hxV⟩ := hxUnion
    have hf' : ∀ V, V ∈ F → f ∈ V.ideal := by
      simpa only [Ideal.mem_iInf] using hf
    have hfV : f ∈ V.ideal := hf' V hV
    rw [← ProjectiveVariety.vanishingIdeal_points V] at hfV
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hfV) x ⟨hx0, hxV⟩

theorem irreducible_points_nonempty (V : ProjectiveVariety n) (hV : V.IsIrreducible) :
    V.points.Nonempty := points_nonempty_of_isIrreducible V hV

theorem degree_locus (F : Family n) (k : ℕ) (hF : IsPure F k) :
    (locus F).degree = degree F := by
  classical
  let G : AffineFamily.Family n := F.image ProjectiveVariety.affineCone
  have hcone_inj : Function.Injective (ProjectiveVariety.affineCone (n := n)) := by
    intro V W hVW
    apply ProjectiveVariety.ext
    exact congrArg AffineVariety.ideal hVW
  have hGpure : AffineFamily.IsPure G (k + 1) := by
    intro W hW
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp (by simpa [G] using hW)
    refine ⟨(hF V hV).1, ?_⟩
    rw [ProjectiveVariety.dimension_cone V
      (points_nonempty_of_isIrreducible V (hF V hV).1), (hF V hV).2]
  have hinf : (⨅ W ∈ G, W.ideal) = ⨅ V ∈ F, V.ideal := by
    ext f
    simp only [Ideal.mem_iInf]
    constructor
    · intro h V hV
      exact h (V.affineCone) (Finset.mem_image.mpr ⟨V, hV, rfl⟩)
    · intro h W hW
      obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp (by simpa [G] using hW)
      exact h V hV
  have hrad : (⨅ V ∈ F, V.ideal).IsRadical := by
    apply Ideal.isRadical_iInf
    intro V
    apply Ideal.isRadical_iInf
    intro _
    exact V.isRadical
  have hcone : (ProjectiveFamily.locus F).affineCone = AffineFamily.locus G := by
    apply AffineVariety.ext
    change ProjectiveVariety.vanishingIdeal (⋃ V ∈ F, V.points) =
      (⨅ W ∈ G, W.ideal).radical
    rw [vanishingIdeal_iUnion_eq_iInf F, hinf, hrad.radical]
  have hdegree_sum : AffineFamily.degree G = ProjectiveFamily.degree F := by
    change (∑ W ∈ F.image ProjectiveVariety.affineCone, W.degree) =
      ∑ V ∈ F, V.degree
    calc
      (∑ W ∈ F.image ProjectiveVariety.affineCone, W.degree) =
          ∑ V ∈ F, (V.affineCone).degree :=
        Finset.sum_image (fun V _ W _ h => hcone_inj h)
      _ = ∑ V ∈ F, V.degree := by
        apply Finset.sum_congr rfl
        intro V hV
        exact ProjectiveVariety.degree_cone V
  calc
    (locus F).degree = (locus F).affineCone.degree :=
      (ProjectiveVariety.degree_cone (locus F)).symm
    _ = (AffineFamily.locus G).degree := congrArg AffineVariety.degree hcone
    _ = AffineFamily.degree G := AffineFamily.degree_locus G (k + 1) hGpure
    _ = ProjectiveFamily.degree F := hdegree_sum

end ProjectiveFamily

/-- The usual chart embedding `x ↦ [1:x]`. -/
def affineEmbedding {n : ℕ} (x : Point n) : ProjectivePoint (n+1) :=
  Projectivization.mk ℂ (Fin.cons 1 x) (by
    intro hz
    have h := congrFun hz 0
    simpa using h)

def projectiveClosure {n : ℕ} (V : AffineVariety n) : ProjectiveVariety (n+1) :=
  ProjectiveVariety.closure (affineEmbedding '' V.points)

private def projectiveDehomogenize {n : ℕ} : Poly (n+1) →+* Poly n :=
  (Polynomial.evalRingHom (1 : Poly n)).comp (MvPolynomial.finSuccEquiv ℂ n).toRingHom

private theorem projectiveDehomogenize_eq_aeval {n : ℕ} (f : Poly (n+1)) :
    projectiveDehomogenize f =
      MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) f := by
  have h : projectiveDehomogenize =
      (MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [projectiveDehomogenize, Polynomial.evalRingHom, MvPolynomial.finSuccEquiv]
    · intro i
      cases i using Fin.cases with
      | zero => simp [projectiveDehomogenize, Polynomial.evalRingHom,
          MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
      | succ j => simp [projectiveDehomogenize, Polynomial.evalRingHom,
          MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (fun F : Poly (n+1) →+* Poly n => F f) h

private theorem projectiveDehomogenize_totalDegree_le {n : ℕ} {D : ℕ}
    {f : Poly (n+1)} (hf : f.IsHomogeneous D) :
    (projectiveDehomogenize f).totalDegree ≤ D := by
  let p := MvPolynomial.finSuccEquiv ℂ n f
  change (Polynomial.eval 1 p).totalDegree ≤ D
  have hnat : p.natDegree ≤ D := by
    dsimp [p]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree f 0).trans hf.totalDegree_le
  have hcoeff : ∀ i ∈ p.support, (p.coeff i).totalDegree ≤ D := by
    intro i hi
    have hiD : i ≤ D := (Polynomial.le_natDegree_of_mem_supp _ hi).trans hnat
    have hh := MvPolynomial.IsHomogeneous.finSuccEquiv_coeff_isHomogeneous hf i (D-i) (by omega)
    exact hh.totalDegree_le.trans (Nat.sub_le D i)
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [one_pow, mul_one]
  exact MvPolynomial.totalDegree_finsetSum_le (fun i hi => hcoeff i hi)

private theorem aeval_projectiveDehomogenize {n : ℕ} (x : Point n) (f : Poly (n+1)) :
    MvPolynomial.aeval x (projectiveDehomogenize f) =
      MvPolynomial.aeval (Fin.cons (1 : ℂ) x) f := by
  have h : ((MvPolynomial.aeval x).toRingHom).comp projectiveDehomogenize =
      (MvPolynomial.aeval (Fin.cons (1 : ℂ) x)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [projectiveDehomogenize, Polynomial.evalRingHom, MvPolynomial.finSuccEquiv]
    · intro i
      cases i using Fin.cases with
      | zero => simp [projectiveDehomogenize, Polynomial.evalRingHom, MvPolynomial.finSuccEquiv]
      | succ j => simp [projectiveDehomogenize, Polynomial.evalRingHom, MvPolynomial.finSuccEquiv]
  exact congrArg (fun F : Poly (n+1) →+* ℂ => F f) h

private theorem projectiveClosure_dehom_mem {n : ℕ} (V : AffineVariety n)
    {f : Poly (n+1)} (h : f ∈ (projectiveClosure V).ideal) :
    projectiveDehomogenize f ∈ V.ideal := by
  change f ∈ ProjectiveVariety.vanishingIdeal (affineEmbedding '' V.points) at h
  rw [← AffineVariety.vanishingIdeal_points V]
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  intro x hx
  let v : Point (n+1) := Fin.cons (1 : ℂ) x
  have hv : v ≠ 0 := by
    intro he
    have h0 := congrFun he 0
    norm_num [v] at h0
  have hzero : MvPolynomial.aeval v f = 0 := by
    apply (MvPolynomial.mem_vanishingIdeal_iff.mp h) v
    refine ⟨hv, ⟨x, hx, ?_⟩⟩
    simp [affineEmbedding, v]
  rw [aeval_projectiveDehomogenize x f]
  simpa [v] using hzero

private theorem projectiveClosure_dehom_mem_iff {n : ℕ} (V : AffineVariety n)
    {D : ℕ} {f : Poly (n+1)} (hf : f.IsHomogeneous D) :
    f ∈ (projectiveClosure V).ideal ↔ projectiveDehomogenize f ∈ V.ideal := by
  change f ∈ ProjectiveVariety.vanishingIdeal (affineEmbedding '' V.points) ↔
    projectiveDehomogenize f ∈ V.ideal
  constructor
  · intro h
    exact projectiveClosure_dehom_mem V h
  · intro h
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro v hv
    obtain ⟨hv0, hp⟩ := hv
    obtain ⟨x, hx, hpx⟩ := hp
    let w : Point (n+1) := Fin.cons (1 : ℂ) x
    have hw : w ≠ 0 := by
      intro he
      have h0 := congrFun he 0
      norm_num [w] at h0
    have hpEq : Projectivization.mk ℂ v hv0 = Projectivization.mk ℂ w hw := by
      simpa [affineEmbedding, w] using hpx.symm
    obtain ⟨c, hc⟩ :=
      (Projectivization.mk_eq_mk_iff' ℂ v w hv0 hw).mp hpEq
    have hxzero : MvPolynomial.aeval x (projectiveDehomogenize f) = 0 :=
      MvPolynomial.mem_zeroLocus_iff.mp hx (projectiveDehomogenize f) h
    rw [← hc, ProjectiveVariety.aeval_smul_of_isHomogeneous c w f D hf,
      ← aeval_projectiveDehomogenize x f, hxzero, mul_zero]

noncomputable def projectiveHomogenize {n : ℕ} (D : ℕ) (f : Poly n) : Poly (n+1) :=
  ∑ i ∈ Finset.range (D+1),
    MvPolynomial.X (0 : Fin (n+1)) ^ (D-i) * MvPolynomial.rename Fin.succ
      (MvPolynomial.homogeneousComponent i f)

private theorem projectiveHomogenize_isHomogeneous {n : ℕ} (D : ℕ) (f : Poly n) :
    (projectiveHomogenize D f).IsHomogeneous D := by
  unfold projectiveHomogenize
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have hiD : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hX :
      (MvPolynomial.X (0 : Fin (n+1)) ^ (D-i) : Poly (n+1)).IsHomogeneous (D-i) :=
    MvPolynomial.isHomogeneous_X_pow _ _
  have hf : (MvPolynomial.rename (Fin.succ : Fin n → Fin (n+1))
      (MvPolynomial.homogeneousComponent i f)).IsHomogeneous i :=
    (MvPolynomial.homogeneousComponent_isHomogeneous i f).rename_isHomogeneous
  convert hX.mul hf using 1 <;> omega

private theorem projectiveDehomogenize_projectiveHomogenize {n : ℕ} (D : ℕ)
    (f : Poly n) (hf : f.totalDegree ≤ D) :
    projectiveDehomogenize (projectiveHomogenize D f) = f := by
  rw [projectiveDehomogenize_eq_aeval]
  simp only [projectiveHomogenize, map_sum, map_mul, map_pow,
    MvPolynomial.aeval_X, MvPolynomial.aeval_rename, Function.comp_def,
    Fin.cons_zero, Fin.cons_succ]
  have hsum :
      (∑ i ∈ Finset.range (D+1), MvPolynomial.homogeneousComponent i f) = f := by
    calc
      _ = ∑ i ∈ Finset.range (f.totalDegree+1),
          MvPolynomial.homogeneousComponent i f := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hf))
        intro i hi hnot
        simp only [Finset.mem_range, not_lt] at hnot
        have hlt : f.totalDegree < i := by
          have hi' := Finset.mem_range.mp hi
          omega
        apply MvPolynomial.homogeneousComponent_eq_zero
        exact hlt
      _ = f := MvPolynomial.sum_homogeneousComponent f
  have hid : MvPolynomial.aeval (fun i : Fin n => MvPolynomial.X i) =
      AlgHom.id ℂ (Poly n) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [hid]
  simpa only [one_pow, one_mul, AlgHom.id_apply] using hsum

theorem projectiveClosure_hilbert {n : ℕ} (V : AffineVariety n) (D : ℕ) :
    (projectiveClosure V).hilbert D = V.hilbert D := by
  classical
  let J := (projectiveClosure V).ideal
  let S : Submodule ℂ (Poly (n+1) ⧸ J) :=
    (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D).map
      (Ideal.Quotient.mkₐ ℂ J).toLinearMap
  let T : Submodule ℂ (Poly n ⧸ V.ideal) := V.restrictionSpace D
  let ψ : Poly (n+1) →ₐ[ℂ] Poly n ⧸ V.ideal :=
    (Ideal.Quotient.mkₐ ℂ V.ideal).comp
      (MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X)
        : Poly (n+1) →ₐ[ℂ] Poly n)
  have hJ : ∀ f : Poly (n+1), f ∈ J → ψ f = 0 := by
    intro f hf
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hmem := projectiveClosure_dehom_mem V (by simpa [J] using hf)
    simpa [ψ, projectiveDehomogenize_eq_aeval] using hmem
  let Q : Poly (n+1) ⧸ J →ₐ[ℂ] Poly n ⧸ V.ideal :=
    Ideal.Quotient.liftₐ J ψ hJ
  let e : S →ₗ[ℂ] T :=
    { toFun := fun x => ⟨Q x.1, by
        have hxmem : x.1 ∈ (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D).map
            (Ideal.Quotient.mkₐ ℂ J).toLinearMap := x.2
        obtain ⟨f, hf, hxf⟩ := Submodule.mem_map.mp hxmem
        apply Submodule.mem_map.mpr
        refine ⟨projectiveDehomogenize f, ?_, ?_⟩
        · exact OAI.QuarticPowerFree.mem_totalSpace.mpr
            (projectiveDehomogenize_totalDegree_le hf)
        · change Ideal.Quotient.mk V.ideal (projectiveDehomogenize f) = Q x.1
          change Ideal.Quotient.mk J f = x.1 at hxf
          rw [← hxf]
          rw [projectiveDehomogenize_eq_aeval]
          change (Ideal.Quotient.mkₐ ℂ V.ideal)
              (MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) f) =
            (Ideal.Quotient.liftₐ J ψ hJ) (Ideal.Quotient.mk J f)
          rw [Ideal.Quotient.liftₐ_apply]
          rfl⟩
      map_add' x y := by
        apply Subtype.ext
        simp [Q]
      map_smul' c x := by
        apply Subtype.ext
        simp [Q] }
  have hzero : ∀ x : S, e x = 0 → x = 0 := by
    intro x hx
    have hxmem : x.1 ∈ (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D).map
        (Ideal.Quotient.mkₐ ℂ J).toLinearMap := x.2
    obtain ⟨f, hf, hxf⟩ := Submodule.mem_map.mp hxmem
    change Ideal.Quotient.mk J f = x.1 at hxf
    have hq0 : Q x.1 = 0 := congrArg Subtype.val hx
    have hq : Q (Ideal.Quotient.mk J f) = 0 := by
      rw [hxf]
      exact hq0
    have hψzero : ψ f = 0 := by
      change (Ideal.Quotient.liftₐ J ψ hJ) (Ideal.Quotient.mk J f) = 0 at hq
      rw [Ideal.Quotient.liftₐ_apply] at hq
      change ψ f = 0 at hq
      exact hq
    change (Ideal.Quotient.mk V.ideal)
      (MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) f) = 0 at hψzero
    have hdehom : projectiveDehomogenize f ∈ V.ideal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [projectiveDehomogenize_eq_aeval]
      exact hψzero
    have hfJ : f ∈ J := (projectiveClosure_dehom_mem_iff V hf).2 hdehom
    apply Subtype.ext
    rw [← hxf]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hfJ
  have hinj : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    have hsub : e (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz := hzero (x-y) hsub
    exact sub_eq_zero.mp (congrArg Subtype.val hz)
  have hsurj : Function.Surjective e := by
    intro y
    obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.mp y.2
    let g := projectiveHomogenize D f
    have hg : g.IsHomogeneous D := projectiveHomogenize_isHomogeneous D f
    let x : S := ⟨Ideal.Quotient.mk J g,
      Submodule.mem_map.mpr ⟨g, hg, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change Q (Ideal.Quotient.mk J g) = y.1
    calc
      Q (Ideal.Quotient.mk J g) = Ideal.Quotient.mk V.ideal
          (projectiveDehomogenize g) := by
        simp only [Q, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
          ψ, projectiveDehomogenize_eq_aeval]
        rfl
      _ = Ideal.Quotient.mk V.ideal f := by
        rw [projectiveDehomogenize_projectiveHomogenize D f
          (OAI.QuarticPowerFree.mem_totalSpace.mp hf)]
      _ = y.1 := hfy
  change Module.finrank ℂ S = Module.finrank ℂ T
  exact (LinearEquiv.ofBijective e ⟨hinj, hsurj⟩).finrank_eq

private theorem projectiveClosure_hilbertPolynomial_eq {n : ℕ} (V : AffineVariety n) :
    (projectiveClosure V).hilbertPolynomial = V.hilbertPolynomial := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  obtain ⟨NA, hA⟩ := Filter.eventually_atTop.mp V.hilbert_eventually
  obtain ⟨NP, hP⟩ := (projectiveClosure V).hilbert_eventually
  filter_upwards [Filter.eventually_atTop.mpr ⟨max NA NP + 1, by
    intro D hD
    have hDA : NA ≤ D := by omega
    have hDP : NP < D := by omega
    calc
      ((projectiveClosure V).hilbertPolynomial).eval (D : ℚ) =
          ((projectiveClosure V).hilbert D : ℚ) := (hP D hDP).symm
      _ = (V.hilbert D : ℚ) := by exact_mod_cast projectiveClosure_hilbert V D
      _ = V.hilbertPolynomial.eval (D : ℚ) := hA D hDA⟩] with D hD
  exact hD

theorem projectiveClosure_degree {n : ℕ} (V : AffineVariety n) :
    (projectiveClosure V).degree = V.degree := by
  have hpoly := projectiveClosure_hilbertPolynomial_eq V
  have hdim : (projectiveClosure V).dimension = V.dimension := by
    change (projectiveClosure V).hilbertPolynomial.natDegree =
      V.hilbertPolynomial.natDegree
    rw [hpoly]
  change
    ((projectiveClosure V).hilbertPolynomial).coeff ((projectiveClosure V).dimension) *
      (((projectiveClosure V).dimension).factorial : ℚ) =
    (((V.dimension).factorial : ℚ) * V.hilbertPolynomial.coeff V.dimension)
  rw [hdim, hpoly]
  ring

theorem projectiveClosure_dimension {n : ℕ} (V : AffineVariety n)
    (hV : V.points.Nonempty) : (projectiveClosure V).dimension = V.dimension := by
  have hpoly := projectiveClosure_hilbertPolynomial_eq V
  change (projectiveClosure V).hilbertPolynomial.natDegree =
    V.hilbertPolynomial.natDegree
  rw [hpoly]

/-- Homogeneous dehomogenization transports primality to the projective closure. -/
theorem projectiveClosure_isIrreducible {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) : (projectiveClosure V).IsIrreducible := by
  apply (projectiveClosure V).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
  · intro htop
    have hone : (1 : Poly (n+1)) ∈ (projectiveClosure V).ideal := by
      rw [htop]
      trivial
    have honeV := projectiveClosure_dehom_mem V hone
    exact hV.one_notMem (by simpa using honeV)
  · intro f g hf hg hfg
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    have hprod : projectiveDehomogenize f * projectiveDehomogenize g ∈ V.ideal := by
      simpa only [map_mul] using projectiveClosure_dehom_mem V hfg
    rcases hV.mem_or_mem hprod with h | h
    · exact Or.inl ((projectiveClosure_dehom_mem_iff V ha).2 h)
    · exact Or.inr ((projectiveClosure_dehom_mem_iff V hb).2 h)

@[simp] theorem ProjectiveFamily.locus_singleton {n : ℕ} (V : ProjectiveVariety n) :
    ProjectiveFamily.locus {V} = V := by
  apply ProjectiveVariety.ext
  change ProjectiveVariety.vanishingIdeal (⋃ W ∈ ({V} : Finset _), W.points) = V.ideal
  simpa using V.vanishingIdeal_points

/-- Homogenizing a source equation gives an equation of its projective closure. -/
theorem projectiveClosure_homogenize_mem {n : ℕ} (V : AffineVariety n)
    (g : Poly n) (hg : g ∈ V.ideal) :
    projectiveHomogenize g.totalDegree g ∈ (projectiveClosure V).ideal := by
  apply (projectiveClosure_dehom_mem_iff V
    (projectiveHomogenize_isHomogeneous g.totalDegree g)).mpr
  rwa [projectiveDehomogenize_projectiveHomogenize _ _ le_rfl]

theorem projectiveHomogenize_aeval {n : ℕ} (g : Poly n) :
    MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X)
      (projectiveHomogenize g.totalDegree g) = g := by
  rw [← projectiveDehomogenize_eq_aeval]
  exact projectiveDehomogenize_projectiveHomogenize _ _ le_rfl

theorem projectiveHomogenize_homogeneous {n : ℕ} (D : ℕ) (g : Poly n) :
    (projectiveHomogenize D g).IsHomogeneous D := projectiveHomogenize_isHomogeneous D g

theorem projectiveClosure_aeval_mem {n : ℕ} (V : AffineVariety n)
    (F : Poly (n+1)) (hF : F ∈ (projectiveClosure V).ideal) :
    MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) F ∈ V.ideal := by
  rw [← projectiveDehomogenize_eq_aeval]
  exact projectiveClosure_dehom_mem V hF

theorem projectiveClosure_homogeneous_mem {n D : ℕ} (V : AffineVariety n)
    (F : Poly (n+1)) (hF : F.IsHomogeneous D) :
    F ∈ (projectiveClosure V).ideal ↔
      MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) F ∈ V.ideal := by
  rw [← projectiveDehomogenize_eq_aeval]
  exact projectiveClosure_dehom_mem_iff V hF

end

end DistinctDistances
