import DistinctDistances.TrackB.PointIntegralSupport
import DistinctDistances.TrackB.IncidenceDensity
import DistinctDistances.TrackB.IncidenceLinearSupport
import DistinctDistances.TrackB.ParameterBaseGeometry
import DistinctDistances.OAIInterface.ReducedTensor
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.TensorProduct.Pi

/-!
Support for B12 `point_integral`, second part. The incidence Hilbert function is
compared with the Hilbert function of the ruling direction set
`{([v], ⋆, [1:z])}` through the ruling parametrization
`(z, v) ↦ ([v], [v : D_z v], [1:z])`.
-/

namespace DistinctDistances.TrackB.PointIntegral

set_option autoImplicit false
noncomputable section
open Polynomial

/-! ### Tridegree pieces: homogeneity and block scaling -/

/-- Tridegree-supported polynomials are weighted homogeneous in each block. -/
theorem triSet_homog {n m o s t u : ℕ} {G : Poly (n + m + o)}
    (hG : G ∈ MvPolynomial.restrictSupport ℂ (triSet n m o s t u)) :
    G.IsWeightedHomogeneous (xWeight n m o) s ∧ G.IsWeightedHomogeneous (yWeight n m o) t ∧
      G.IsWeightedHomogeneous (zWeight n m o) u := by
  rw [MvPolynomial.mem_restrictSupport_iff] at hG
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun d hd => ?_⟩
  · have h := hG (Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr hd))
    rw [xWeight_eq_sum]
    exact h.1
  · have h := hG (Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr hd))
    rw [yWeight_eq_sum]
    exact h.2.1
  · have h := hG (Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr hd))
    rw [zWeight_eq_sum, RulingMaps.degree_eq_sum_univ]
    simp only [zPart_apply]
    exact h.2.2

/-- Weighted homogeneity in the three blocks gives tridegree support. -/
theorem mem_triSet_of_homog {n m o s t u : ℕ} {G : Poly (n + m + o)}
    (hx : G.IsWeightedHomogeneous (xWeight n m o) s)
    (hy : G.IsWeightedHomogeneous (yWeight n m o) t)
    (hz : G.IsWeightedHomogeneous (zWeight n m o) u) :
    G ∈ MvPolynomial.restrictSupport ℂ (triSet n m o s t u) := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro d hd
  have hd' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hd)
  refine ⟨?_, ?_, ?_⟩
  · rw [← xWeight_eq_sum]
    exact hx hd'
  · rw [← yWeight_eq_sum]
    exact hy hd'
  · have h := hz hd'
    rw [zWeight_eq_sum, RulingMaps.degree_eq_sum_univ] at h
    simp only [zPart_apply] at h
    exact h

theorem joinPoints_smul_blocks {n m o : ℕ} (x : Point n) (y : Point m) (z : Point o)
    (c c' c'' : ℂ) :
    joinPoints (joinPoints (c • x) (c' • y)) (c'' • z) = fun i =>
      c ^ (xWeight n m o i) * (c' ^ (yWeight n m o i) *
        (c'' ^ (zWeight n m o i) * joinPoints (joinPoints x y) z i)) := by
  funext i
  rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
  · simp [joinPoints, xWeight, yWeight, zWeight, Fin.addCases_left]
  · simp [joinPoints, xWeight, yWeight, zWeight, Fin.addCases_left, Fin.addCases_right]
  · simp [joinPoints, xWeight, yWeight, zWeight, Fin.addCases_right]

/-- Block scaling of a tridegree-(s,t,u) polynomial. -/
theorem aeval_joinPoints_smul {n m o s t u : ℕ} {G : Poly (n + m + o)}
    (hG : G ∈ MvPolynomial.restrictSupport ℂ (triSet n m o s t u))
    (x : Point n) (y : Point m) (z : Point o) (c c' c'' : ℂ) :
    MvPolynomial.aeval (joinPoints (joinPoints (c • x) (c' • y)) (c'' • z)) G =
      c ^ s * c' ^ t * c'' ^ u * MvPolynomial.aeval (joinPoints (joinPoints x y) z) G := by
  obtain ⟨hx, hy, hz⟩ := triSet_homog hG
  rw [joinPoints_smul_blocks, GenericFiber.aeval_scale_of_isWeightedHomogeneous hx,
    GenericFiber.aeval_scale_of_isWeightedHomogeneous hy,
    GenericFiber.aeval_scale_of_isWeightedHomogeneous hz]
  ring

/-! ### The Segre substitution and its lift in diagonal tridegree -/

/-- Segre coordinates as products of one coordinate from each block. -/
def segreSubst (n m o : ℕ) : Poly ((n * m) * o) →ₐ[ℂ] Poly (n + m + o) :=
  MvPolynomial.aeval (fun k =>
    MvPolynomial.X (Fin.castAdd o (Fin.castAdd m
        (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).1)) *
      MvPolynomial.X (Fin.castAdd o (Fin.natAdd n
        (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).2)) *
      MvPolynomial.X (Fin.natAdd (n + m) (finProdFinEquiv.symm k).2))

theorem aeval_segreSubst {n m o : ℕ} (x : Point n) (y : Point m) (z : Point o)
    (F : Poly ((n * m) * o)) :
    MvPolynomial.aeval (joinPoints (joinPoints x y) z) (segreSubst n m o F) =
      MvPolynomial.aeval (segreVector (segreVector x y) z) F := by
  have h := congrArg (fun φ : Poly ((n * m) * o) →ₐ[ℂ] ℂ => φ F)
    (MvPolynomial.comp_aeval (R := ℂ)
      (fun k : Fin ((n * m) * o) =>
        MvPolynomial.X (Fin.castAdd o (Fin.castAdd m
            (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).1)) *
          MvPolynomial.X (Fin.castAdd o (Fin.natAdd n
            (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).2)) *
          MvPolynomial.X (Fin.natAdd (n + m) (finProdFinEquiv.symm k).2) :
          Fin ((n * m) * o) → Poly (n + m + o))
      (MvPolynomial.aeval (joinPoints (joinPoints x y) z)))
  simp only [AlgHom.comp_apply] at h
  rw [segreSubst, h]
  have hfun : (fun k : Fin ((n * m) * o) => MvPolynomial.aeval (joinPoints (joinPoints x y) z)
      (MvPolynomial.X (Fin.castAdd o (Fin.castAdd m
          (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).1)) *
        MvPolynomial.X (Fin.castAdd o (Fin.natAdd n
          (finProdFinEquiv.symm (finProdFinEquiv.symm k).1).2)) *
        MvPolynomial.X (Fin.natAdd (n + m) (finProdFinEquiv.symm k).2) : Poly (n + m + o)))
      = segreVector (segreVector x y) z := by
    funext k
    simp [joinPoints, segreVector, Fin.addCases_left, Fin.addCases_right]
  rw [hfun]

/-- Diagonal-tridegree monomials lift through the Segre substitution. -/
theorem segreSubst_lift_monomial (n m o : ℕ) :
    ∀ (D : ℕ) (d : Fin (n + m + o) →₀ ℕ), d ∈ triSet n m o D D D →
      ∃ F : Poly ((n * m) * o), segreSubst n m o F = MvPolynomial.monomial d 1 := by
  classical
  intro D
  induction D with
  | zero =>
    intro d hd
    refine ⟨1, ?_⟩
    have hd0 : d = 0 := by
      ext i
      rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
      · exact (Finset.sum_eq_zero_iff.mp hd.1) k (Finset.mem_univ _)
      · exact (Finset.sum_eq_zero_iff.mp hd.2.1) k (Finset.mem_univ _)
      · exact (Finset.sum_eq_zero_iff.mp hd.2.2) l (Finset.mem_univ _)
    rw [hd0, map_one]
    rfl
  | succ D ih =>
    intro d hd
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun i : Fin n => d (Fin.castAdd o (Fin.castAdd m i))) (by rw [hd.1]; omega)
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun j : Fin m => d (Fin.castAdd o (Fin.natAdd n j))) (by rw [hd.2.1]; omega)
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun l : Fin o => d (Fin.natAdd (n + m) l)) (by rw [hd.2.2]; omega)
    obtain ⟨A, hA⟩ : ∃ A : Fin (n + m + o), A = Fin.castAdd o (Fin.castAdd m i) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Fin (n + m + o), B = Fin.castAdd o (Fin.natAdd n j) := ⟨_, rfl⟩
    obtain ⟨Cc, hC⟩ : ∃ Cc : Fin (n + m + o), Cc = Fin.natAdd (n + m) l := ⟨_, rfl⟩
    rw [← hA] at hi
    rw [← hB] at hj
    rw [← hC] at hl
    have hAB : A ≠ B := by
      intro h
      have := congrArg Fin.val h
      simp [hA, hB] at this
      omega
    have hAC : A ≠ Cc := by
      intro h
      have := congrArg Fin.val h
      simp [hA, hC] at this
      omega
    have hBC : B ≠ Cc := by
      intro h
      have := congrArg Fin.val h
      simp [hB, hC] at this
      omega
    have xA : ∀ k : Fin n, A = Fin.castAdd o (Fin.castAdd m k) ↔ i = k := by
      intro k
      rw [hA]
      constructor
      · intro h
        have := congrArg Fin.val h
        simp at this
        exact Fin.ext this
      · rintro rfl
        rfl
    have xB : ∀ k : Fin n, B ≠ Fin.castAdd o (Fin.castAdd m k) := by
      intro k h
      have := congrArg Fin.val h
      simp [hB] at this
      omega
    have xC : ∀ k : Fin n, Cc ≠ Fin.castAdd o (Fin.castAdd m k) := by
      intro k h
      have := congrArg Fin.val h
      simp [hC] at this
      omega
    have yA : ∀ k : Fin m, A ≠ Fin.castAdd o (Fin.natAdd n k) := by
      intro k h
      have := congrArg Fin.val h
      simp [hA] at this
      omega
    have yB : ∀ k : Fin m, B = Fin.castAdd o (Fin.natAdd n k) ↔ j = k := by
      intro k
      rw [hB]
      constructor
      · intro h
        have := congrArg Fin.val h
        simp at this
        exact Fin.ext this
      · rintro rfl
        rfl
    have yC : ∀ k : Fin m, Cc ≠ Fin.castAdd o (Fin.natAdd n k) := by
      intro k h
      have := congrArg Fin.val h
      simp [hC] at this
      omega
    have zA : ∀ k : Fin o, A ≠ Fin.natAdd (n + m) k := by
      intro k h
      have := congrArg Fin.val h
      simp [hA] at this
      omega
    have zB : ∀ k : Fin o, B ≠ Fin.natAdd (n + m) k := by
      intro k h
      have := congrArg Fin.val h
      simp [hB] at this
      omega
    have zC : ∀ k : Fin o, Cc = Fin.natAdd (n + m) k ↔ l = k := by
      intro k
      rw [hC]
      constructor
      · intro h
        have := congrArg Fin.val h
        simp at this
        exact Fin.ext this
      · rintro rfl
        rfl
    set E : Fin (n + m + o) →₀ ℕ :=
      Finsupp.single A 1 + Finsupp.single B 1 + Finsupp.single Cc 1 with hE
    have hEle : E ≤ d := by
      intro k
      simp only [hE, Finsupp.add_apply, Finsupp.single_apply]
      by_cases hkA : A = k
      · subst hkA
        rw [if_pos rfl, if_neg (Ne.symm hAB), if_neg (Ne.symm hAC)]
        omega
      · by_cases hkB : B = k
        · subst hkB
          rw [if_neg hkA, if_pos rfl, if_neg (Ne.symm hBC)]
          omega
        · by_cases hkC : Cc = k
          · subst hkC
            rw [if_neg hkA, if_neg hkB, if_pos rfl]
            omega
          · rw [if_neg hkA, if_neg hkB, if_neg hkC]
            omega
    set d' := d - E with hd'
    have hdd : d = d' + E := (tsub_add_cancel_of_le hEle).symm
    have hEx : (∑ k : Fin n, E (Fin.castAdd o (Fin.castAdd m k))) = 1 := by
      simp [hE, Finsupp.single_apply, xA, xB, xC]
    have hEy : (∑ k : Fin m, E (Fin.castAdd o (Fin.natAdd n k))) = 1 := by
      simp [hE, Finsupp.single_apply, yA, yB, yC]
    have hEz : (∑ k : Fin o, E (Fin.natAdd (n + m) k)) = 1 := by
      simp [hE, Finsupp.single_apply, zA, zB, zC]
    have hd'mem : d' ∈ triSet n m o D D D := by
      have h1 := hd.1
      have h2 := hd.2.1
      have h3 := hd.2.2
      rw [hdd] at h1 h2 h3
      simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h1 h2 h3
      refine ⟨?_, ?_, ?_⟩ <;> omega
    obtain ⟨F', hF'⟩ := ih d' hd'mem
    refine ⟨MvPolynomial.X (finProdFinEquiv (finProdFinEquiv (i, j), l)) * F', ?_⟩
    rw [map_mul, hF']
    simp only [segreSubst, MvPolynomial.aeval_X, Equiv.symm_apply_apply]
    rw [← hA, ← hB, ← hC, hdd, hE]
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
    congr 1
    abel

/-- Diagonal-tridegree polynomials lift through the Segre substitution. -/
theorem segreSubst_lift {n m o D : ℕ} (G : Poly (n + m + o))
    (hG : G ∈ MvPolynomial.restrictSupport ℂ (triSet n m o D D D)) :
    ∃ F : Poly ((n * m) * o), segreSubst n m o F = G := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff] at hG
  have hlift : ∀ d ∈ G.support, ∃ F : Poly ((n * m) * o),
      segreSubst n m o F = MvPolynomial.monomial d 1 :=
    fun d hd => segreSubst_lift_monomial n m o D d (hG (Finset.mem_coe.mpr hd))
  choose F hF using hlift
  refine ⟨∑ d ∈ G.support.attach, MvPolynomial.C (G.coeff d.1) * F d.1 d.2, ?_⟩
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.as_sum G]
  rw [← Finset.sum_attach G.support]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_mul, hF, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_monomial,
    mul_one]

/-! ### Representatives -/

theorem eq_smul_rep_of_mk {n : ℕ} (P : ProjectivePoint n) (r : Point n) (hr : r ≠ 0)
    (h : Projectivization.mk ℂ r hr = P) : ∃ c : ℂ, c ≠ 0 ∧ r = c • P.rep := by
  subst h
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ r hr
  refine ⟨((a⁻¹ : ℂˣ) : ℂ), (a⁻¹).ne_zero, ?_⟩
  rw [← Units.smul_def, ← ha, inv_smul_smul]

theorem rep_eq_smul_of_mk {n : ℕ} (v : Point n) (hv : v ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ (Projectivization.mk ℂ v hv).rep = c • v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  exact ⟨(a : ℂ), a.ne_zero, by rw [← Units.smul_def, ha]⟩

theorem segreVector_smul_left {n m : ℕ} (c : ℂ) (x : Point n) (y : Point m) :
    segreVector (c • x) y = c • segreVector x y := by
  funext k
  simp [segreVector, mul_assoc]

theorem segreVector_smul_right {n m : ℕ} (c : ℂ) (x : Point n) (y : Point m) :
    segreVector x (c • y) = c • segreVector x y := by
  funext k
  simp [segreVector, mul_left_comm]

/-! ### The incidence ideal via the ruling parametrization -/

section Incidence

variable {e j N : ℕ} (C : SkewCoordinates e) (V : AffineVariety (skewDim e))
  (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) (a : Fin e)

/-- The ruling graph point `(v, (v, D_z v), (1, z))` as a triple representative. -/
def rulingGraphRep (z : Point (skewDim e)) (v : Point e) :
    Point (e + (e + e) + (skewDim e + 1)) :=
  joinPoints (joinPoints v (graphVector C z v)) (Fin.cons 1 z)

theorem rulingGraphRep_mem (z : Point (skewDim e)) (v : Point e)
    (hw : joinPoints z v ∈ rulingPoints Γ H) (hv : v ≠ 0) :
    rulingGraphRep C z v ∈ tripleRepresentatives (incidenceTriples C Γ H) := by
  refine ⟨v, graphVector C z v, Fin.cons 1 z, hv, graphVector_ne_zero C z v hv,
    consOne_ne_zero z, ⟨?_, ?_⟩, rfl⟩
  · exact ProjectiveVariety.subset_closure _
      ⟨Projectivization.mk ℂ v hv, graphParameter C z v hv, ⟨z, v, hw, hv, rfl, rfl⟩, rfl⟩
  · exact graph_incidenceCondition C z v hv

/-- The ruling graph in Segre coordinates. -/
def rulingSegreSet : Set (ProjectivePoint ((e * (e + e)) * (skewDim e + 1))) :=
  {q | ∃ z v, joinPoints z v ∈ rulingPoints Γ H ∧ ∃ hv : v ≠ 0,
    q = segrePoint (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv))
      (affineEmbedding z)}

/-- A tridegree polynomial lies in the incidence ideal iff it vanishes on the ruling graph. -/
theorem mem_incidenceIdeal_iff (R : IsRulingIncidence C V Γ H a j N) {s t u : ℕ}
    (G : Poly (e + (e + e) + (skewDim e + 1)))
    (hG : G ∈ MvPolynomial.restrictSupport ℂ (triSet e (e + e) (skewDim e + 1) s t u)) :
    G ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives (incidenceTriples C Γ H)) ↔
      ∀ z v, joinPoints z v ∈ rulingPoints Γ H → v ≠ 0 →
        MvPolynomial.aeval (rulingGraphRep C z v) G = 0 := by
  classical
  constructor
  · intro hmem z v hw hv
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hmem _ (rulingGraphRep_mem C Γ H z v hw hv)
  intro hvan
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro w ⟨x, y, zz, hx, hy, hz, hT, rfl⟩
  set px := Projectivization.mk ℂ x hx with hpx
  set py := Projectivization.mk ℂ y hy with hpy
  set pz := Projectivization.mk ℂ zz hz with hpz
  obtain ⟨cx, -, hcx⟩ := eq_smul_rep_of_mk px x hx rfl
  obtain ⟨cy, -, hcy⟩ := eq_smul_rep_of_mk py y hy rfl
  obtain ⟨cz, -, hcz⟩ := eq_smul_rep_of_mk pz zz hz rfl
  suffices hrep : MvPolynomial.aeval (joinPoints (joinPoints px.rep py.rep) pz.rep) G = 0 by
    rw [hcx, hcy, hcz, aeval_joinPoints_smul hG, hrep, mul_zero]
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate px
  obtain ⟨k, hk⟩ := exists_nonzero_coordinate py
  obtain ⟨l, hl⟩ := exists_nonzero_coordinate pz
  obtain ⟨hGx, hGy, hGz⟩ := triSet_homog hG
  set D := s + t + u with hD
  set Xi : Poly (e + (e + e) + (skewDim e + 1)) :=
    MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) with hXi
  set Xk : Poly (e + (e + e) + (skewDim e + 1)) :=
    MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e k)) with hXk
  set Xl : Poly (e + (e + e) + (skewDim e + 1)) :=
    MvPolynomial.X (Fin.natAdd (e + (e + e)) l) with hXl
  set G' := G * Xi ^ (D - s) * Xk ^ (D - t) * Xl ^ (D - u) with hG'def
  have hwX : ∀ (w : Fin (e + (e + e) + (skewDim e + 1)) → ℕ)
      (b : Fin (e + (e + e) + (skewDim e + 1))),
      (MvPolynomial.X b : Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous w (w b) :=
    fun w b => MvPolynomial.isWeightedHomogeneous_X ℂ w b
  have hG' : G' ∈ MvPolynomial.restrictSupport ℂ
      (triSet e (e + e) (skewDim e + 1) D D D) := by
    apply mem_triSet_of_homog
    · have h := ((hGx.mul ((hwX _ (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))).pow
        (D - s))).mul ((hwX _ (Fin.castAdd (skewDim e + 1) (Fin.natAdd e k))).pow (D - t))).mul
        ((hwX _ (Fin.natAdd (e + (e + e)) l)).pow (D - u))
      convert h using 1
      simp [xWeight, Fin.addCases_left, Fin.addCases_right]
      omega
    · have h := ((hGy.mul ((hwX _ (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))).pow
        (D - s))).mul ((hwX _ (Fin.castAdd (skewDim e + 1) (Fin.natAdd e k))).pow (D - t))).mul
        ((hwX _ (Fin.natAdd (e + (e + e)) l)).pow (D - u))
      convert h using 1
      simp [yWeight, Fin.addCases_left, Fin.addCases_right]
      omega
    · have h := ((hGz.mul ((hwX _ (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))).pow
        (D - s))).mul ((hwX _ (Fin.castAdd (skewDim e + 1) (Fin.natAdd e k))).pow (D - t))).mul
        ((hwX _ (Fin.natAdd (e + (e + e)) l)).pow (D - u))
      convert h using 1
      simp [zWeight, Fin.addCases_left, Fin.addCases_right]
      omega
  obtain ⟨F, hF⟩ := segreSubst_lift G' hG'
  have hG'eval : ∀ (p : Point e) (q : Point (e + e)) (r : Point (skewDim e + 1)),
      MvPolynomial.aeval (joinPoints (joinPoints p q) r) G' =
        MvPolynomial.aeval (joinPoints (joinPoints p q) r) G *
          p i ^ (D - s) * q k ^ (D - t) * r l ^ (D - u) := by
    intro p q r
    simp [hG'def, hXi, hXk, hXl, joinPoints, Fin.addCases_left, Fin.addCases_right]
  -- F vanishes on the ruling graph in Segre coordinates.
  have hFmem : F ∈ (ProjectiveVariety.closure (rulingSegreSet C Γ H)).ideal := by
    show F ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives (rulingSegreSet C Γ H))
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro r ⟨hr, z, v, hw, hv, hq⟩
    obtain ⟨c1, -, hc1⟩ := eq_smul_rep_of_mk _ r hr hq
    obtain ⟨c0, -, hc0⟩ := rep_eq_smul_of_mk
      (segreVector (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv)).rep
        (affineEmbedding z).rep)
      (segreVector_ne_zero _ _ (Projectivization.rep_nonzero _) (Projectivization.rep_nonzero _))
    obtain ⟨c2, -, hc2⟩ := rep_eq_smul_of_mk
      (segreVector (Projectivization.mk ℂ v hv).rep (graphParameter C z v hv).rep)
      (segreVector_ne_zero _ _ (Projectivization.rep_nonzero _) (Projectivization.rep_nonzero _))
    obtain ⟨c3, -, hc3⟩ := rep_eq_smul_of_mk v hv
    obtain ⟨c4, -, hc4⟩ := rep_eq_smul_of_mk (graphVector C z v) (graphVector_ne_zero C z v hv)
    obtain ⟨c5, -, hc5⟩ := rep_eq_smul_of_mk (Fin.cons 1 z : Point (skewDim e + 1))
      (consOne_ne_zero z)
    have hr' : r = segreVector (segreVector ((c1 * c0 * c2 * c3) • v) (c4 • graphVector C z v))
        (c5 • (Fin.cons 1 z : Point (skewDim e + 1))) := by
      rw [hc1]
      rw [show (segrePoint (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv))
          (affineEmbedding z)).rep = (Projectivization.mk ℂ
            (segreVector (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv)).rep
              (affineEmbedding z).rep)
            (segreVector_ne_zero _ _ (Projectivization.rep_nonzero _)
              (Projectivization.rep_nonzero _))).rep from rfl, hc0]
      rw [show (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv)).rep =
        (Projectivization.mk ℂ (segreVector (Projectivization.mk ℂ v hv).rep
          (graphParameter C z v hv).rep) (segreVector_ne_zero _ _
            (Projectivization.rep_nonzero _) (Projectivization.rep_nonzero _))).rep from rfl]
      rw [hc2, show (graphParameter C z v hv).rep = (Projectivization.mk ℂ (graphVector C z v)
        (graphVector_ne_zero C z v hv)).rep from rfl, hc4, hc3,
        show (affineEmbedding z).rep = (Projectivization.mk ℂ (Fin.cons 1 z : Point (skewDim e + 1))
          (consOne_ne_zero z)).rep from rfl, hc5]
      simp only [segreVector_smul_left, segreVector_smul_right, smul_smul]
      congr 1
      ring
    rw [hr', ← aeval_segreSubst, hF, aeval_joinPoints_smul hG', hG'eval]
    have h0 := hvan z v hw hv
    rw [rulingGraphRep] at h0
    rw [h0]
    ring
  -- The incidence point lies in the closure of the ruling graph.
  have hmemC : segrePoint (segrePoint px py) pz ∈ (compactIncidence C Γ H).points :=
    ProjectiveVariety.subset_closure _ ⟨px, py, pz, hT, rfl⟩
  have hS : segrePoint (segrePoint px py) pz ∈
      (ProjectiveVariety.closure (rulingSegreSet C Γ H)).points :=
    compact_incidence_subset_of_ruling_graph C V Γ H a R _
      (fun z v hw hv => ProjectiveVariety.subset_closure (rulingSegreSet C Γ H) ⟨z, v, hw, hv, rfl⟩)
      hmemC
  obtain ⟨c, hc0, hc⟩ := rep_eq_smul_of_mk (segreVector px.rep py.rep)
    (segreVector_ne_zero _ _ px.rep_nonzero py.rep_nonzero)
  have hnz : segreVector (segrePoint px py).rep pz.rep ≠ 0 :=
    segreVector_ne_zero _ _ (Projectivization.rep_nonzero _) pz.rep_nonzero
  have h0 := MvPolynomial.mem_zeroLocus_iff.mp (hS _ hnz rfl) F hFmem
  have hseg : segreVector (segrePoint px py).rep pz.rep =
      segreVector (segreVector (c • px.rep) py.rep) pz.rep := by
    rw [show (segrePoint px py).rep = (Projectivization.mk ℂ (segreVector px.rep py.rep)
      (segreVector_ne_zero _ _ px.rep_nonzero py.rep_nonzero)).rep from rfl, hc]
    simp only [segreVector_smul_left]
  rw [hseg, ← aeval_segreSubst, hF] at h0
  have h1 := aeval_joinPoints_smul hG' px.rep py.rep pz.rep c 1 1
  simp only [one_smul, one_pow, mul_one] at h1
  rw [h1, hG'eval] at h0
  have hcD : c ^ D ≠ 0 := pow_ne_zero _ hc0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hcD
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact absurd h (pow_ne_zero _ hi)
      · exact absurd h (pow_ne_zero _ hk)
    · exact absurd h (pow_ne_zero _ hl)

end Incidence

/-! ### The ruling direction set and evaluation maps -/

/-- The single point of `P^0`, represented by `1`. -/
def onePoint : Point 1 := fun _ => 1

theorem onePoint_ne_zero : onePoint ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [onePoint] at h0

section Direction

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- The ruling direction set `{([v], ⋆, [1:z])}`. -/
def rulingDirectionTriples :
    Set ((ProjectivePoint e × ProjectivePoint 1) × ProjectivePoint (skewDim e + 1)) :=
  {w | ∃ z v, joinPoints z v ∈ rulingPoints Γ H ∧ ∃ hv : v ≠ 0,
    w = ((Projectivization.mk ℂ v hv, Projectivization.mk ℂ onePoint onePoint_ne_zero),
      affineEmbedding z)}

/-- The direction representative `(v, 1, (1, z))`. -/
def directionRep (z : Point (skewDim e)) (v : Point e) : Point (e + 1 + (skewDim e + 1)) :=
  joinPoints (joinPoints v onePoint) (Fin.cons 1 z)

theorem directionTriples_snd_mem (V : AffineVariety (skewDim e))
    (hΓV : ∀ w ∈ Γ.points, firstPoint w ∈ V) :
    ∀ w ∈ rulingDirectionTriples Γ H, w.2 ∈ (projectiveClosure V).points := by
  rintro w ⟨z, v, hw, hv, rfl⟩
  apply ProjectiveVariety.subset_closure
  refine ⟨z, ?_, rfl⟩
  have h := hΓV _ hw.1
  rwa [RulingMaps.firstPoint_joinPoints] at h

/-- A tridegree polynomial vanishes on the direction set iff it vanishes on the ruling. -/
theorem mem_directionIdeal_iff {n t u : ℕ} (F : Poly (e + 1 + (skewDim e + 1)))
    (hF : F ∈ MvPolynomial.restrictSupport ℂ (triSet e 1 (skewDim e + 1) n t u)) :
    F ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives (rulingDirectionTriples Γ H)) ↔
      ∀ z v, joinPoints z v ∈ rulingPoints Γ H → v ≠ 0 →
        MvPolynomial.aeval (directionRep z v) F = 0 := by
  constructor
  · intro hmem z v hw hv
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hmem _
      ⟨v, onePoint, Fin.cons 1 z, hv, onePoint_ne_zero, consOne_ne_zero z,
        ⟨z, v, hw, hv, rfl⟩, rfl⟩
  · intro hvan
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro w ⟨x, y, zz, hx, hy, hz, ⟨z, v, hw, hv, heq⟩, rfl⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h1, h2⟩, h3⟩ := heq
    obtain ⟨a1, ha1⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h1
    obtain ⟨a2, ha2⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h2
    obtain ⟨a3, ha3⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h3
    rw [← ha1, ← ha2, ← ha3, Units.smul_def, Units.smul_def, Units.smul_def,
      aeval_joinPoints_smul hF]
    have h0 := hvan z v hw hv
    rw [directionRep] at h0
    rw [h0, mul_zero]

/-- Ruling points with nonzero direction, as an index type. -/
abbrev RulingIdx := {p : Point (skewDim e) × Point e //
  joinPoints p.1 p.2 ∈ rulingPoints Γ H ∧ p.2 ≠ 0}

/-- Evaluation of incidence polynomials along the ruling parametrization. -/
def evIncidence : Poly (e + (e + e) + (skewDim e + 1)) →ₗ[ℂ] (RulingIdx Γ H → ℂ) where
  toFun G w := MvPolynomial.aeval (rulingGraphRep C w.1.1 w.1.2) G
  map_add' G G' := by
    funext w
    simp
  map_smul' c G := by
    funext w
    simp

/-- Evaluation of direction polynomials along the ruling. -/
def evDirection : Poly (e + 1 + (skewDim e + 1)) →ₗ[ℂ] (RulingIdx Γ H → ℂ) where
  toFun F w := MvPolynomial.aeval (directionRep w.1.1 w.1.2) F
  map_add' F F' := by
    funext w
    simp
  map_smul' c F := by
    funext w
    simp

end Direction

theorem tripleSection_eq_range {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) (s t u : ℕ) :
    tripleSection T s t u = LinearMap.range
      ((Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))).toLinearMap
        ∘ₗ zComboHom n m o s t u) := by
  rw [LinearMap.range_comp, zComboHom_range]
  rfl

theorem zComboHom_mem {n m o s t u : ℕ}
    (x : bidegIndex n m s t → ↥(MvPolynomial.homogeneousSubmodule (Fin o) ℂ u)) :
    zComboHom n m o s t u x ∈ MvPolynomial.restrictSupport ℂ (triSet n m o s t u) := by
  rw [← zComboHom_range]
  exact ⟨x, rfl⟩

theorem finrank_range_eq_of_ker_eq {V W1 W2 : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W1] [Module ℂ W1] [AddCommGroup W2] [Module ℂ W2]
    (f : V →ₗ[ℂ] W1) (g : V →ₗ[ℂ] W2) (h : LinearMap.ker f = LinearMap.ker g) :
    Module.finrank ℂ (LinearMap.range f) = Module.finrank ℂ (LinearMap.range g) := by
  have h1 := f.finrank_range_add_finrank_ker
  have h2 := g.finrank_range_add_finrank_ker
  rw [h] at h1
  omega

section HilbertAsRank

variable {e j N : ℕ} (C : SkewCoordinates e) (V : AffineVariety (skewDim e))
  (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) (a : Fin e)

theorem tripleHilbert_incidence_eq (R : IsRulingIncidence C V Γ H a j N) (s t u : ℕ) :
    tripleHilbert (incidenceTriples C Γ H) s t u = Module.finrank ℂ
      (LinearMap.range (evIncidence C Γ H ∘ₗ zComboHom e (e + e) (skewDim e + 1) s t u)) := by
  unfold tripleHilbert
  rw [tripleSection_eq_range]
  apply finrank_range_eq_of_ker_eq
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
  change Ideal.Quotient.mk _ _ = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_incidenceIdeal_iff C V Γ H a R _ (zComboHom_mem x)]
  constructor
  · intro h
    funext w
    exact h _ _ w.2.1 w.2.2
  · intro h z v hw hv
    exact congrFun h ⟨(z, v), hw, hv⟩

theorem tripleHilbert_direction_eq (n t u : ℕ) :
    tripleHilbert (rulingDirectionTriples Γ H) n t u = Module.finrank ℂ
      (LinearMap.range (evDirection Γ H ∘ₗ zComboHom e 1 (skewDim e + 1) n t u)) := by
  unfold tripleHilbert
  rw [tripleSection_eq_range]
  apply finrank_range_eq_of_ker_eq
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
  change Ideal.Quotient.mk _ _ = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_directionIdeal_iff Γ H _ (zComboHom_mem x)]
  constructor
  · intro h
    funext w
    exact h _ _ w.2.1 w.2.2
  · intro h z v hw hv
    exact congrFun h ⟨(z, v), hw, hv⟩

end HilbertAsRank

/-! ### Sandwich: lower inclusion by splitting the degree -/

theorem aeval_join_zInclusion {n m o : ℕ} (w : Point (n + m)) (zz : Point o) (q : Poly o) :
    MvPolynomial.aeval (joinPoints w zz) (zInclusion n m o q) = MvPolynomial.aeval zz q := by
  have hf : (joinPoints w zz ∘ ⇑(embZ n m o)) = zz := by
    funext l
    show Fin.addCases w zz (Fin.natAdd (n + m) l) = zz l
    rw [Fin.addCases_right]
  rw [zInclusion, MvPolynomial.aeval_rename, hf]

theorem aeval_join_bidegMonomial {n m o s t : ℕ} (w : Point (n + m)) (zz : Point o)
    (β : bidegIndex n m s t) :
    MvPolynomial.aeval (joinPoints w zz) (bidegMonomial n m o s t β) = ∏ i, w i ^ β.1 i := by
  rw [bidegMonomial, MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_embDomain,
    Finsupp.prod_fintype]
  · apply Finset.prod_congr rfl
    intro i _
    rw [show (embXY n m o) i = Fin.castAdd o i from rfl]
    simp [joinPoints, Fin.addCases_left]
  · intro i
    simp

/-- Split a function with sum `s + t` into parts with sums `s` and `t`. -/
theorem split_sum_fun {k : ℕ} : ∀ (s t : ℕ) (μ : Fin k → ℕ), (∑ i, μ i) = s + t →
    ∃ μ1 μ2 : Fin k → ℕ, (∀ i, μ i = μ1 i + μ2 i) ∧ (∑ i, μ1 i) = s ∧ (∑ i, μ2 i) = t := by
  classical
  intro s
  induction s with
  | zero =>
    intro t μ h
    exact ⟨0, μ, fun i => by simp, by simp, by simpa using h⟩
  | succ s ih =>
    intro t μ h
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := μ)
      (by rw [h]; omega)
    set μ' := Function.update μ i (μ i - 1) with hμ'
    have hsum : (∑ k, μ' k) = s + t := by
      have e1 := Finset.sum_update_of_mem (Finset.mem_univ i) μ (μ i - 1)
      have e2 := Finset.add_sum_erase Finset.univ μ (Finset.mem_univ i)
      rw [← hμ'] at e1
      rw [e1]
      have e3 : (∑ x ∈ Finset.univ \ {i}, μ x) = ∑ x ∈ Finset.univ.erase i, μ x := by
        rw [Finset.sdiff_singleton_eq_erase]
      omega
    obtain ⟨μ1, μ2, hsplit, h1, h2⟩ := ih t μ' hsum
    refine ⟨Function.update μ1 i (μ1 i + 1), μ2, fun k => ?_, ?_, h2⟩
    · by_cases hk : k = i
      · subst hk
        have := hsplit k
        rw [hμ', Function.update_self] at this
        rw [Function.update_self]
        omega
      · have := hsplit k
        rw [hμ', Function.update_of_ne hk] at this
        rw [Function.update_of_ne hk]
        exact this
    · have e1 := Finset.sum_update_of_mem (Finset.mem_univ i) μ1 (μ1 i + 1)
      have e2 := Finset.add_sum_erase Finset.univ μ1 (Finset.mem_univ i)
      have e3 : (∑ x ∈ Finset.univ \ {i}, μ1 x) = ∑ x ∈ Finset.univ.erase i, μ1 x := by
        rw [Finset.sdiff_singleton_eq_erase]
      rw [e1]
      omega

section Sandwich

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

theorem zComboHom_single {n m o s t u : ℕ} (β : bidegIndex n m s t)
    (q : ↥(MvPolynomial.homogeneousSubmodule (Fin o) ℂ u)) :
    zComboHom n m o s t u (Pi.single β q) = bidegMonomial n m o s t β * zInclusion n m o q := by
  classical
  show zCombo n m o s t (fun γ => ((Pi.single β q : bidegIndex n m s t → _) γ : Poly o)) = _
  unfold zCombo
  rw [Finset.sum_eq_single β]
  · simp only [Pi.single_eq_same]
  · intro γ _ hγ
    simp only [Pi.single_eq_of_ne hγ, Submodule.coe_zero, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ β) h

theorem prod_incidence_split (z : Point (skewDim e)) (v : Point e)
    (δ : Fin (e + (e + e)) →₀ ℕ) (μ1 μ2 : Fin e → ℕ)
    (h1 : ∀ i, δ (Fin.castAdd (e + e) i) = μ1 i)
    (h2 : ∀ i, δ (Fin.natAdd e (Fin.castAdd e i)) = μ2 i)
    (h3 : ∀ i, δ (Fin.natAdd e (Fin.natAdd e i)) = 0) :
    (∏ i, joinPoints v (graphVector C z v) i ^ δ i) = ∏ i, v i ^ (μ1 i + μ2 i) := by
  rw [Fin.prod_univ_add, Fin.prod_univ_add]
  simp only [h1, h2, h3, pow_zero, Finset.prod_const_one, mul_one]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hv : joinPoints v (graphVector C z v) (Fin.castAdd (e + e) i) = v i := by
    simp [joinPoints]
  have hg : joinPoints v (graphVector C z v) (Fin.natAdd e (Fin.castAdd e i)) = v i := by
    simp [joinPoints, graphVector]
  rw [hv, hg, pow_add]

theorem prod_direction_eq (v : Point e) (β : Fin (e + 1) →₀ ℕ) :
    (∏ i, joinPoints v onePoint i ^ β i) =
      (∏ i : Fin e, v i ^ β (Fin.castAdd 1 i)) * onePoint 0 ^ β (Fin.natAdd e 0) := by
  rw [Fin.prod_univ_add]
  simp [joinPoints]

/-- Lower inclusion: direction sections of degree `s+t` come from incidence sections. -/
theorem range_direction_le_incidence (s t u : ℕ) :
    LinearMap.range (evDirection Γ H ∘ₗ zComboHom e 1 (skewDim e + 1) (s + t) 0 u) ≤
      LinearMap.range (evIncidence C Γ H ∘ₗ zComboHom e (e + e) (skewDim e + 1) s t u) := by
  classical
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.comp_apply]
  have hx : zComboHom e 1 (skewDim e + 1) (s + t) 0 u x =
      ∑ β, zComboHom e 1 (skewDim e + 1) (s + t) 0 u (Pi.single β (x β)) := by
    rw [← map_sum]
    congr 1
    exact (Finset.univ_sum_single x).symm
  rw [hx, map_sum]
  apply Submodule.sum_mem
  intro β _
  rw [zComboHom_single]
  obtain ⟨μ1, μ2, hsplit, h1, h2⟩ :=
    split_sum_fun s t (fun i => β.1 (Fin.castAdd 1 i)) β.2.1
  have hβy : β.1 (Fin.natAdd e 0) = 0 := by
    have h := β.2.2
    simpa using h
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin (e + (e + e)) →₀ ℕ,
      δ = Finsupp.equivFunOnFinite.symm (Fin.addCases μ1 (Fin.addCases μ2 (fun _ => 0))) :=
    ⟨_, rfl⟩
  have d1 : ∀ i, δ (Fin.castAdd (e + e) i) = μ1 i := by
    intro i
    simp [hδ]
  have d2 : ∀ i, δ (Fin.natAdd e (Fin.castAdd e i)) = μ2 i := by
    intro i
    simp [hδ]
  have d3 : ∀ i, δ (Fin.natAdd e (Fin.natAdd e i)) = 0 := by
    intro i
    subst hδ
    show Fin.addCases μ1 (Fin.addCases μ2 (fun _ => 0)) (Fin.natAdd e (Fin.natAdd e i)) = 0
    rw [Fin.addCases_right, Fin.addCases_right]
  have hδmem : (∑ i : Fin e, δ (Fin.castAdd (e + e) i)) = s ∧
      (∑ i : Fin (e + e), δ (Fin.natAdd e i)) = t := by
    constructor
    · simp only [d1]
      exact h1
    · rw [Fin.sum_univ_add]
      simp only [d2, d3, Finset.sum_const_zero, add_zero]
      exact h2
  refine ⟨Pi.single (⟨δ, hδmem⟩ : bidegIndex e (e + e) s t) (x β), ?_⟩
  rw [LinearMap.comp_apply, zComboHom_single]
  funext w
  change MvPolynomial.aeval (rulingGraphRep C w.1.1 w.1.2) _ =
    MvPolynomial.aeval (directionRep w.1.1 w.1.2) _
  rw [map_mul, map_mul, rulingGraphRep, directionRep, aeval_join_zInclusion,
    aeval_join_zInclusion, aeval_join_bidegMonomial, aeval_join_bidegMonomial,
    prod_incidence_split C w.1.1 w.1.2 δ μ1 μ2 d1 d2 d3, prod_direction_eq, hβy, pow_zero,
    mul_one]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hsplit i]

end Sandwich

/-! ### Sandwich: upper inclusion by substitution -/

/-- Image of a polynomial under a substitution whose variable images are weighted
homogeneous is weighted homogeneous when all monomials have the same image degree. -/
theorem aeval_isWeightedHomogeneous {N M : ℕ} (w' : Fin M → ℕ) (φ : Fin N → Poly M)
    (ω : Fin N → ℕ) (hφ : ∀ i, (φ i).IsWeightedHomogeneous w' (ω i)) (Φ : Poly N) (D : ℕ)
    (hΦ : ∀ d ∈ Φ.support, (∑ i, ω i * d i) = D) :
    (MvPolynomial.aeval φ Φ).IsWeightedHomogeneous w' D := by
  classical
  rw [MvPolynomial.as_sum Φ, map_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro d hd
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)]
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ (fun i => φ i ^ d i)
    (fun i => d i • ω i) (fun i _ => (hφ i).pow (d i))
  have hC : (algebraMap ℂ (Poly M) (Φ.coeff d)).IsWeightedHomogeneous w' 0 := by
    rw [MvPolynomial.algebraMap_eq]
    exact MvPolynomial.isWeightedHomogeneous_C w' _
  have h := hC.mul hprod
  convert h using 1
  rw [zero_add, ← hΦ d hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_eq_mul, mul_comm]

section Theta

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

theorem decode_expand (z : Point (skewDim e)) (v w : Point e) :
    (C.decode z).val v w = ∑ k, ∑ l, z k * v l *
      (C.decode (Pi.single k 1)).val (Pi.single l 1) w := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' z, pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The substitution `a ↦ v`, `b' ↦ x₀ v`, `b'' ↦ D_{x'} v`, `x ↦ x`. -/
def thetaImg : Fin (e + (e + e) + (skewDim e + 1)) → Poly (e + 1 + (skewDim e + 1)) :=
  Fin.addCases
    (Fin.addCases
      (fun i => MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 i)))
      (Fin.addCases
        (fun i => MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 i)) *
          MvPolynomial.X (Fin.natAdd (e + 1) (0 : Fin (skewDim e + 1))))
        (fun i => ∑ k : Fin (skewDim e), ∑ l : Fin e,
          MvPolynomial.C ((C.decode (Pi.single k 1)).val (Pi.single l 1) (Pi.single i 1)) *
            MvPolynomial.X (Fin.natAdd (e + 1) k.succ) *
            MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 l)))))
    (fun l => MvPolynomial.X (Fin.natAdd (e + 1) l))

theorem evDirection_theta (G : Poly (e + (e + e) + (skewDim e + 1))) :
    evDirection Γ H (MvPolynomial.aeval (thetaImg C) G) = evIncidence C Γ H G := by
  funext w
  change MvPolynomial.aeval (directionRep w.1.1 w.1.2) (MvPolynomial.aeval (thetaImg C) G) =
    MvPolynomial.aeval (rulingGraphRep C w.1.1 w.1.2) G
  have h := congrArg (fun φ : Poly (e + (e + e) + (skewDim e + 1)) →ₐ[ℂ] ℂ => φ G)
    (MvPolynomial.comp_aeval (R := ℂ) (thetaImg C)
      (MvPolynomial.aeval (directionRep w.1.1 w.1.2)))
  simp only [AlgHom.comp_apply] at h
  rw [h]
  have hfun : (fun i => MvPolynomial.aeval (directionRep w.1.1 w.1.2) (thetaImg C i))
      = rulingGraphRep C w.1.1 w.1.2 := by
    funext i
    refine Fin.addCases (fun i12 => ?_) (fun l => ?_) i
    · refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i12
      · simp [thetaImg, Fin.addCases_left, Fin.addCases_right, directionRep,
          rulingGraphRep, joinPoints, MvPolynomial.aeval_X]
      · refine Fin.addCases (fun i3 => ?_) (fun i4 => ?_) i2
        · simp [thetaImg, Fin.addCases_left, Fin.addCases_right, directionRep,
            rulingGraphRep, joinPoints, graphVector, onePoint, MvPolynomial.aeval_X]
        · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right, map_sum, map_mul,
            MvPolynomial.aeval_X, MvPolynomial.aeval_C, directionRep, rulingGraphRep, joinPoints,
            graphVector, pointOfCovector]
          rw [decode_expand]
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          simp only [Fin.cons_succ, Fin.addCases_left,
            MvPolynomial.algebraMap_eq, RingHom.id_apply]
          rw [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
          ring
    · simp [thetaImg, Fin.addCases_left, Fin.addCases_right, directionRep,
        rulingGraphRep, joinPoints, MvPolynomial.aeval_X]
  rw [hfun]

theorem thetaImg_homog_x (i : Fin (e + (e + e) + (skewDim e + 1))) :
    (thetaImg C i).IsWeightedHomogeneous (xWeight e 1 (skewDim e + 1))
      (xWeight e (e + e) (skewDim e + 1) i + yWeight e (e + e) (skewDim e + 1) i) := by
  have hX := fun b => MvPolynomial.isWeightedHomogeneous_X ℂ (xWeight e 1 (skewDim e + 1)) b
  have hC := fun (a : ℂ) => MvPolynomial.isWeightedHomogeneous_C (xWeight e 1 (skewDim e + 1)) a
  refine Fin.addCases (fun i12 => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i12
    · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
      simpa only [xWeight, yWeight, Fin.addCases_left, Fin.addCases_right] using
        hX (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 i1))
    · refine Fin.addCases (fun i3 => ?_) (fun i4 => ?_) i2
      · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
        simpa only [xWeight, yWeight, Fin.addCases_left, Fin.addCases_right] using
          (hX (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 i3))).mul
            (hX (Fin.natAdd (e + 1) (0 : Fin (skewDim e + 1))))
      · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
        apply MvPolynomial.IsWeightedHomogeneous.sum
        intro k _
        apply MvPolynomial.IsWeightedHomogeneous.sum
        intro l _
        simpa only [xWeight, yWeight, Fin.addCases_left, Fin.addCases_right] using
          ((hC ((C.decode (Pi.single k 1)).val (Pi.single l 1) (Pi.single i4 1))).mul
            (hX (Fin.natAdd (e + 1) k.succ))).mul
            (hX (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 l)))
  · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
    simpa only [xWeight, yWeight, Fin.addCases_left, Fin.addCases_right] using
      hX (Fin.natAdd (e + 1) l)

theorem thetaImg_homog_y (i : Fin (e + (e + e) + (skewDim e + 1))) :
    (thetaImg C i).IsWeightedHomogeneous (yWeight e 1 (skewDim e + 1)) 0 := by
  have hX := fun b => MvPolynomial.isWeightedHomogeneous_X ℂ (yWeight e 1 (skewDim e + 1)) b
  have hC := fun (a : ℂ) => MvPolynomial.isWeightedHomogeneous_C (yWeight e 1 (skewDim e + 1)) a
  refine Fin.addCases (fun i12 => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i12
    · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
      simpa only [yWeight, Fin.addCases_left, Fin.addCases_right] using
        hX (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 i1))
    · refine Fin.addCases (fun i3 => ?_) (fun i4 => ?_) i2
      · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
        simpa only [yWeight, Fin.addCases_left, Fin.addCases_right] using
          (hX (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 i3))).mul
            (hX (Fin.natAdd (e + 1) (0 : Fin (skewDim e + 1))))
      · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
        apply MvPolynomial.IsWeightedHomogeneous.sum
        intro k _
        apply MvPolynomial.IsWeightedHomogeneous.sum
        intro l _
        simpa only [yWeight, Fin.addCases_left, Fin.addCases_right] using
          ((hC ((C.decode (Pi.single k 1)).val (Pi.single l 1) (Pi.single i4 1))).mul
            (hX (Fin.natAdd (e + 1) k.succ))).mul
            (hX (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 l)))
  · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
    simpa only [yWeight, Fin.addCases_left, Fin.addCases_right] using
      hX (Fin.natAdd (e + 1) l)

theorem thetaImg_homog_z (i : Fin (e + (e + e) + (skewDim e + 1))) :
    (thetaImg C i).IsWeightedHomogeneous (zWeight e 1 (skewDim e + 1))
      (yWeight e (e + e) (skewDim e + 1) i + zWeight e (e + e) (skewDim e + 1) i) := by
  have hX := fun b => MvPolynomial.isWeightedHomogeneous_X ℂ (zWeight e 1 (skewDim e + 1)) b
  have hC := fun (a : ℂ) => MvPolynomial.isWeightedHomogeneous_C (zWeight e 1 (skewDim e + 1)) a
  refine Fin.addCases (fun i12 => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i12
    · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
      simpa only [yWeight, zWeight, Fin.addCases_left, Fin.addCases_right] using
        hX (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 i1))
    · refine Fin.addCases (fun i3 => ?_) (fun i4 => ?_) i2
      · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
        simpa only [yWeight, zWeight, Fin.addCases_left, Fin.addCases_right] using
          (hX (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 i3))).mul
            (hX (Fin.natAdd (e + 1) (0 : Fin (skewDim e + 1))))
      · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
        apply MvPolynomial.IsWeightedHomogeneous.sum
        intro k _
        apply MvPolynomial.IsWeightedHomogeneous.sum
        intro l _
        simpa only [yWeight, zWeight, Fin.addCases_left, Fin.addCases_right] using
          ((hC ((C.decode (Pi.single k 1)).val (Pi.single l 1) (Pi.single i4 1))).mul
            (hX (Fin.natAdd (e + 1) k.succ))).mul
            (hX (Fin.castAdd (skewDim e + 1) (Fin.castAdd 1 l)))
  · simp only [thetaImg, Fin.addCases_left, Fin.addCases_right]
    simpa only [yWeight, zWeight, Fin.addCases_left, Fin.addCases_right] using
      hX (Fin.natAdd (e + 1) l)

theorem theta_mem {s t u : ℕ} (G : Poly (e + (e + e) + (skewDim e + 1)))
    (hG : G ∈ MvPolynomial.restrictSupport ℂ (triSet e (e + e) (skewDim e + 1) s t u)) :
    MvPolynomial.aeval (thetaImg C) G ∈
      MvPolynomial.restrictSupport ℂ (triSet e 1 (skewDim e + 1) (s + t) 0 (u + t)) := by
  obtain ⟨hx, hy, hz⟩ := triSet_homog hG
  apply mem_triSet_of_homog
  · apply aeval_isWeightedHomogeneous _ _ _ (thetaImg_homog_x C)
    intro d hd
    have h1 := hx (MvPolynomial.mem_support_iff.mp hd)
    have h2 := hy (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_eq_sum] at h1 h2
    rw [← h1, ← h2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply aeval_isWeightedHomogeneous _ _ _ (thetaImg_homog_y C)
    intro d _
    simp
  · apply aeval_isWeightedHomogeneous _ _ _ (thetaImg_homog_z C)
    intro d hd
    have h2 := hy (MvPolynomial.mem_support_iff.mp hd)
    have h3 := hz (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_eq_sum] at h2 h3
    rw [add_comm u t, ← h2, ← h3, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Upper inclusion: incidence sections are direction sections of degree `(s+t, u+t)`. -/
theorem range_incidence_le_direction (s t u : ℕ) :
    LinearMap.range (evIncidence C Γ H ∘ₗ zComboHom e (e + e) (skewDim e + 1) s t u) ≤
      LinearMap.range (evDirection Γ H ∘ₗ zComboHom e 1 (skewDim e + 1) (s + t) 0 (u + t)) := by
  rintro _ ⟨x, rfl⟩
  have hmem := theta_mem C _ (zComboHom_mem x)
  rw [← zComboHom_range] at hmem
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hy]
  exact evDirection_theta C Γ H _

end Theta

/-- The incidence Hilbert function is sandwiched by the direction Hilbert function. -/
theorem tripleHilbert_sandwich {e j N : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (a : Fin e) (R : IsRulingIncidence C V Γ H a j N) (s t u : ℕ) :
    tripleHilbert (rulingDirectionTriples Γ H) (s + t) 0 u ≤
        tripleHilbert (incidenceTriples C Γ H) s t u ∧
      tripleHilbert (incidenceTriples C Γ H) s t u ≤
        tripleHilbert (rulingDirectionTriples Γ H) (s + t) 0 (u + t) := by
  rw [tripleHilbert_incidence_eq C V Γ H a R, tripleHilbert_direction_eq Γ H,
    tripleHilbert_direction_eq Γ H]
  exact ⟨Submodule.finrank_mono (range_direction_le_incidence C Γ H s t u),
    Submodule.finrank_mono (range_incidence_le_direction C Γ H s t u)⟩

/-! ### Slope uniqueness and transfer across the sandwich -/

/-- Uniqueness of the Hilbert slope over a positive-dimensional base: two slopes
approximating the same count function coincide. -/
theorem slope_unique {o : ℕ} (W : ProjectiveVariety o) (T : ℕ → ℕ) (r r' : ℕ)
    (C C' : ℚ) (M : ℕ) (hk : 1 ≤ W.dimension)
    (hpos : 0 < W.hilbertPolynomial.leadingCoeff)
    (h : ∀ u : ℕ, M ≤ u →
      |(T u : ℚ) - (r : ℚ) * (W.hilbert u : ℚ)| ≤ C * (u : ℚ) ^ (W.dimension - 1))
    (h' : ∀ u : ℕ, M ≤ u →
      |(T u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)| ≤ C' * (u : ℚ) ^ (W.dimension - 1)) :
    r = r' := by
  classical
  by_contra hne
  have hd1 : (1 : ℚ) ≤ |((r : ℚ) - (r' : ℚ))| := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hle : ((r : ℚ) - (r' : ℚ)) ≤ -1 := by
        have h1 : r + 1 ≤ r' := hlt
        have h2 : ((r : ℚ) + 1) ≤ (r' : ℚ) := by exact_mod_cast h1
        linarith
      rw [abs_of_nonpos (by linarith : ((r : ℚ) - (r' : ℚ)) ≤ 0)]
      linarith
    · have hle : (1 : ℚ) ≤ ((r : ℚ) - (r' : ℚ)) := by
        have h1 : r' + 1 ≤ r := hgt
        have h2 : ((r' : ℚ) + 1) ≤ (r : ℚ) := by exact_mod_cast h1
        linarith
      rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ ((r : ℚ) - (r' : ℚ)))]
      linarith
  have hcomb : ∀ u : ℕ, M ≤ u →
      |((r : ℚ) - (r' : ℚ))| * (W.hilbert u : ℚ)
        ≤ (|C| + |C'|) * (u : ℚ) ^ (W.dimension - 1) := by
    intro u hu
    have hGnn : (0 : ℚ) ≤ (W.hilbert u : ℚ) := by exact_mod_cast Nat.zero_le _
    have h1 := h u hu
    have h2 := h' u hu
    have e : ((r : ℚ) - (r' : ℚ)) * (W.hilbert u : ℚ) =
        (((T u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)))
          - (((T u : ℚ) - (r : ℚ) * (W.hilbert u : ℚ))) := by ring
    calc |((r : ℚ) - (r' : ℚ))| * (W.hilbert u : ℚ)
        = |((r : ℚ) - (r' : ℚ)) * (W.hilbert u : ℚ)| := by
          rw [abs_mul, abs_of_nonneg hGnn]
      _ = |(((T u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)))
          - (((T u : ℚ) - (r : ℚ) * (W.hilbert u : ℚ)))| := by rw [e]
      _ ≤ (|C| + |C'|) * (u : ℚ) ^ (W.dimension - 1) := by
          have g1 : |((T u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ))|
              ≤ |C'| * (u : ℚ) ^ (W.dimension - 1) :=
            le_trans h2 (mul_le_mul_of_nonneg_right (le_abs_self _)
              (pow_nonneg (by positivity) _))
          have g2 : |((T u : ℚ) - (r : ℚ) * (W.hilbert u : ℚ))|
              ≤ |C| * (u : ℚ) ^ (W.dimension - 1) :=
            le_trans h1 (mul_le_mul_of_nonneg_right (le_abs_self _)
              (pow_nonneg (by positivity) _))
          refine le_trans (abs_sub _ _) ?_
          rw [add_mul, add_comm (|C| * (u : ℚ) ^ (W.dimension - 1))]
          exact add_le_add g1 g2
  set S : Polynomial ℚ :=
    W.hilbertPolynomial - Polynomial.C (|C| + |C'|) * Polynomial.X ^ (W.dimension - 1)
    with hSdef
  have hSk : S.coeff W.dimension = W.hilbertPolynomial.leadingCoeff := by
    rw [hSdef, Polynomial.coeff_sub]
    have hz : (Polynomial.C (|C| + |C'|) * Polynomial.X ^ (W.dimension - 1) :
        Polynomial ℚ).coeff W.dimension = 0 := by
      rw [Polynomial.coeff_C_mul_X_pow]
      rw [if_neg (by omega)]
    rw [hz, sub_zero]
    rfl
  have hSdeg : S.natDegree = W.dimension := by
    apply le_antisymm
    · have hq : (Polynomial.C (|C| + |C'|) * Polynomial.X ^ (W.dimension - 1) :
          Polynomial ℚ).natDegree ≤ W.dimension - 1 := by
        calc (Polynomial.C (|C| + |C'|) * Polynomial.X ^ (W.dimension - 1) :
              Polynomial ℚ).natDegree
            ≤ (Polynomial.C (|C| + |C'|)).natDegree
              + (Polynomial.X ^ (W.dimension - 1) : Polynomial ℚ).natDegree :=
              Polynomial.natDegree_mul_le
          _ = 0 + (W.dimension - 1) := by
              rw [Polynomial.natDegree_C, Polynomial.natDegree_pow,
                Polynomial.natDegree_X, mul_one]
          _ = W.dimension - 1 := by omega
      have hqq : (Polynomial.C (|C| + |C'|) * Polynomial.X ^ (W.dimension - 1) :
          Polynomial ℚ).natDegree ≤ W.hilbertPolynomial.natDegree :=
        le_trans hq (by
          have : W.hilbertPolynomial.natDegree = W.dimension := rfl
          omega)
      calc S.natDegree
          ≤ max W.hilbertPolynomial.natDegree
            (Polynomial.C (|C| + |C'|) * Polynomial.X ^ (W.dimension - 1) :
              Polynomial ℚ).natDegree := by
            rw [hSdef]
            exact Polynomial.natDegree_sub_le _ _
        _ = W.hilbertPolynomial.natDegree := max_eq_left hqq
        _ = W.dimension := rfl
    · by_contra hlt
      push_neg at hlt
      have h0 : S.coeff W.dimension = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      rw [hSk] at h0
      exact (ne_of_gt hpos) h0
  have hSlc : S.leadingCoeff = W.hilbertPolynomial.leadingCoeff := by
    show S.coeff S.natDegree = _
    rw [hSdeg]
    exact hSk
  have hSne : S ≠ 0 := by
    intro h0
    rw [h0, Polynomial.leadingCoeff_zero] at hSlc
    exact (ne_of_gt hpos) hSlc.symm
  have hSdegpos : 0 < S.degree := by
    rw [Polynomial.degree_eq_natDegree hSne, hSdeg]
    exact_mod_cast hk
  have htend := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg S hSdegpos
    (by rw [hSlc]; exact le_of_lt hpos)
  have htendN : Filter.Tendsto (fun n : ℕ => S.eval ((n : ℕ) : ℚ))
      Filter.atTop Filter.atTop :=
    htend.comp tendsto_natCast_atTop_atTop
  obtain ⟨NW, hNW⟩ := W.hilbert_eventually
  obtain ⟨u, hu0, huB⟩ := (htendN.eventually (Filter.eventually_gt_atTop (0 : ℚ))).and
    (Filter.eventually_ge_atTop (max M (NW + 1))) |>.exists
  have huM : M ≤ u := le_trans (Nat.le_max_left _ _) huB
  have huNW : NW < u := by
    have h2 := Nat.le_max_right M (NW + 1)
    omega
  have hGu : ((W.hilbert u : ℕ) : ℚ) = W.hilbertPolynomial.eval ((u : ℕ) : ℚ) :=
    hNW u huNW
  have hGnn : (0 : ℚ) ≤ (W.hilbert u : ℚ) := by exact_mod_cast Nat.zero_le _
  have hKu : (W.hilbert u : ℚ) ≤ (|C| + |C'|) * (u : ℚ) ^ (W.dimension - 1) := by
    have h1 := hcomb u huM
    have h1' : |((r : ℚ) - (r' : ℚ)) * (W.hilbert u : ℚ)|
        ≤ (|C| + |C'|) * (u : ℚ) ^ (W.dimension - 1) := by
      rw [abs_mul, abs_of_nonneg hGnn]
      exact h1
    calc (W.hilbert u : ℚ) = 1 * (W.hilbert u : ℚ) := (one_mul _).symm
      _ ≤ |((r : ℚ) - (r' : ℚ)) * (W.hilbert u : ℚ)| := by
        rw [abs_mul, abs_of_nonneg hGnn]
        exact mul_le_mul_of_nonneg_right hd1 hGnn
      _ ≤ _ := h1'
  have hle : S.eval ((u : ℕ) : ℚ) ≤ 0 := by
    have e : S.eval ((u : ℕ) : ℚ) = W.hilbertPolynomial.eval ((u : ℕ) : ℚ)
        - (|C| + |C'|) * ((u : ℕ) : ℚ) ^ (W.dimension - 1) := by
      rw [hSdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
    rw [e, ← hGu]
    linarith [hKu]
  linarith [hu0, hle]

/-- The sandwich transfers the direction slope to the incidence count. -/
theorem sandwich_slope_transfer {o : ℕ} (W : ProjectiveVariety o) (T A : ℕ → ℕ)
    (r' t : ℕ) (C' C2 : ℚ) (M' M2 : ℕ)
    (hA : ∀ u : ℕ, M' ≤ u →
      |(A u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)| ≤ C' * (u : ℚ) ^ (W.dimension - 1))
    (hshift : ∀ u : ℕ, M2 ≤ u →
      |(W.hilbert (u + t) : ℚ) - (W.hilbert u : ℚ)|
        ≤ C2 * (u : ℚ) ^ (W.dimension - 1))
    (hsand : ∀ u : ℕ, A u ≤ T u ∧ T u ≤ A (u + t)) :
    ∃ K : ℚ, ∃ M : ℕ, ∀ u : ℕ, M ≤ u →
      |(T u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)|
        ≤ K * (u : ℚ) ^ (W.dimension - 1) := by
  classical
  refine ⟨|C'| * (1 + ((t : ℚ) + 1) ^ (W.dimension - 1)) + (r' : ℚ) * |C2|,
    max (max M' M2) 1, fun u hu => ?_⟩
  have huM' : M' ≤ u :=
    le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_left _ _) hu)
  have huM2 : M2 ≤ u :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_left _ _) hu)
  have hu1 : 1 ≤ u := le_trans (Nat.le_max_right _ _) hu
  have hu1c : (1 : ℚ) ≤ (u : ℚ) := by exact_mod_cast hu1
  have hunc : (0 : ℚ) ≤ (u : ℚ) := by linarith
  have hpow : ((u + t : ℕ) : ℚ) ^ (W.dimension - 1)
      ≤ (((t : ℚ) + 1) ^ (W.dimension - 1)) * (u : ℚ) ^ (W.dimension - 1) := by
    have hle : ((u + t : ℕ) : ℚ) ≤ ((t : ℚ) + 1) * (u : ℚ) := by
      have ht : (t : ℚ) ≤ (t : ℚ) * (u : ℚ) :=
        le_mul_of_one_le_right (by positivity) hu1c
      push_cast
      linarith
    calc ((u + t : ℕ) : ℚ) ^ (W.dimension - 1)
        ≤ (((t : ℚ) + 1) * (u : ℚ)) ^ (W.dimension - 1) :=
          pow_le_pow_left₀ (by positivity) hle _
      _ = (((t : ℚ) + 1) ^ (W.dimension - 1)) * (u : ℚ) ^ (W.dimension - 1) := by
          rw [mul_pow]
  have hAup := hA (u + t) (by omega)
  have hAlo := hA u huM'
  have hsh := hshift u huM2
  obtain ⟨hlo, hup⟩ := hsand u
  have h1a : |(A (u + t) : ℚ) - (r' : ℚ) * (W.hilbert (u + t) : ℚ)|
      ≤ |C'| * ((((t : ℚ) + 1) ^ (W.dimension - 1)) * (u : ℚ) ^ (W.dimension - 1)) :=
    le_trans hAup (by
      refine le_trans
        (mul_le_mul_of_nonneg_right (le_abs_self _)
          (pow_nonneg (by positivity) _)) ?_
      exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _))
  have h2a : |(r' : ℚ) * ((W.hilbert (u + t) : ℚ) - (W.hilbert u : ℚ))|
      ≤ (r' : ℚ) * (|C2| * (u : ℚ) ^ (W.dimension - 1)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (r' : ℚ))]
    exact mul_le_mul_of_nonneg_left
      (le_trans hsh (mul_le_mul_of_nonneg_right (le_abs_self _)
        (pow_nonneg hunc _))) (by positivity)
  have edecomp : (A (u + t) : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)
      = ((A (u + t) : ℚ) - (r' : ℚ) * (W.hilbert (u + t) : ℚ))
        + (r' : ℚ) * ((W.hilbert (u + t) : ℚ) - (W.hilbert u : ℚ)) := by ring
  have hsum : |(A (u + t) : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)|
      ≤ |C'| * ((((t : ℚ) + 1) ^ (W.dimension - 1)) * (u : ℚ) ^ (W.dimension - 1))
        + (r' : ℚ) * (|C2| * (u : ℚ) ^ (W.dimension - 1)) := by
    rw [edecomp]
    exact (abs_add_le _ _).trans (add_le_add h1a h2a)
  have e1 : |(A u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)|
      ≤ |C'| * (u : ℚ) ^ (W.dimension - 1) :=
    le_trans hAlo (mul_le_mul_of_nonneg_right (le_abs_self _)
      (pow_nonneg hunc _))
  have hn1 : (0 : ℚ) ≤ |C'| * (u : ℚ) ^ (W.dimension - 1) :=
    mul_nonneg (abs_nonneg _) (pow_nonneg hunc _)
  have hn2 : (0 : ℚ) ≤ |C'| * ((((t : ℚ) + 1) ^ (W.dimension - 1))
      * (u : ℚ) ^ (W.dimension - 1))
      + (r' : ℚ) * (|C2| * (u : ℚ) ^ (W.dimension - 1)) := by positivity
  have hlo' : (A u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)
      ≤ (T u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ) := by
    have hcc : (A u : ℚ) ≤ (T u : ℚ) := by exact_mod_cast hlo
    linarith
  have hup' : (T u : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ)
      ≤ (A (u + t) : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ) := by
    have hcc : (T u : ℚ) ≤ (A (u + t) : ℚ) := by exact_mod_cast hup
    linarith
  have hfold : (|C'| * (1 + ((t : ℚ) + 1) ^ (W.dimension - 1)) + (r' : ℚ) * |C2|)
        * (u : ℚ) ^ (W.dimension - 1)
      = |C'| * (u : ℚ) ^ (W.dimension - 1)
        + (|C'| * ((((t : ℚ) + 1) ^ (W.dimension - 1)) * (u : ℚ) ^ (W.dimension - 1))
          + (r' : ℚ) * (|C2| * (u : ℚ) ^ (W.dimension - 1))) := by ring
  rw [hfold, abs_le]
  constructor
  · have h1 := neg_le_of_abs_le e1
    linarith
  · have h2 := le_abs_self ((A (u + t) : ℚ) - (r' : ℚ) * (W.hilbert u : ℚ))
    linarith [hsum]

/-! ### Fibre Hilbert function of a radical fibre ideal -/

/-- Finrank of images of a submodule under two maps with the same kernel on it. -/
theorem finrank_map_eq_of_ker_iff {V W1 W2 : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W1] [Module ℂ W1] [AddCommGroup W2] [Module ℂ W2]
    (f : V →ₗ[ℂ] W1) (g : V →ₗ[ℂ] W2) (P : Submodule ℂ V)
    (h : ∀ x ∈ P, f x = 0 ↔ g x = 0) :
    Module.finrank ℂ (P.map f) = Module.finrank ℂ (P.map g) := by
  have hker : LinearMap.ker (f ∘ₗ P.subtype) = LinearMap.ker (g ∘ₗ P.subtype) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]
    exact h x.1 x.2
  have hf : P.map f = LinearMap.range (f ∘ₗ P.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hg : P.map g = LinearMap.range (g ∘ₗ P.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hf, hg]
  exact ((f ∘ₗ P.subtype).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      (g ∘ₗ P.subtype).quotKerEquivRange)).finrank_eq

/-- Bidegree scaling of a polynomial supported in bidegree `(s,t)`. -/
theorem aeval_joinPoints_smul_pair {n m s t : ℕ} {F : Poly (n + m)}
    (hF : F ∈ MvPolynomial.restrictSupport ℂ {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧ (∑ i : Fin m, d (Fin.natAdd n i)) = t})
    (x : Point n) (y : Point m) (c c' : ℂ) :
    MvPolynomial.aeval (joinPoints (c • x) (c' • y)) F =
      c ^ s * c' ^ t * MvPolynomial.aeval (joinPoints x y) F := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff] at hF
  rw [MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_eq_eval, MvPolynomial.eval_eq',
    MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hs, ht⟩ := hF (Finset.mem_coe.mpr hd)
  rw [Fin.prod_univ_add, Fin.prod_univ_add]
  simp only [joinPoints, Fin.addCases_left, Fin.addCases_right, Pi.smul_apply, smul_eq_mul,
    mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs, ht]
  ring

theorem aeval_fibreSpecialize {q o : ℕ} (z : Point o) (w : Point q) (F : Poly (q + (o + 1))) :
    MvPolynomial.aeval w (fibreSpecialize z F) =
      MvPolynomial.aeval (joinPoints w (Fin.cons 1 z)) F := by
  rw [fibreSpecialize, GenericFiber.eval_aeval]
  apply congrArg (fun f : Fin (q + (o + 1)) → ℂ => MvPolynomial.aeval f F)
  funext i
  refine Fin.addCases (fun i => ?_) (fun l => ?_) i
  · simp [joinPoints, Fin.append_left]
  · cases l using Fin.cases <;> simp [joinPoints, Fin.append_right]

theorem mem_zeroLocus_tripleFibreIdeal {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint (o + 1)))
    (z : Point o) (w : Point (n + m)) :
    w ∈ MvPolynomial.zeroLocus ℂ (tripleFibreIdeal T z) ↔
      ∀ F ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T),
        MvPolynomial.aeval (joinPoints w (Fin.cons 1 z)) F = 0 := by
  constructor
  · intro hw F hF
    rw [← aeval_fibreSpecialize]
    have h := (MvPolynomial.mem_zeroLocus_iff).mp hw _ (Ideal.mem_map_of_mem _ hF)
    simpa [MvPolynomial.aeval_def] using h
  · intro h
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    have hle : tripleFibreIdeal T z ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom := by
      unfold tripleFibreIdeal
      rw [Ideal.map_le_iff_le_comap]
      intro F hF
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change MvPolynomial.aeval w (fibreSpecialize z F) = 0
      rw [aeval_fibreSpecialize]
      exact h F hF
    have h2 := hle hp
    rw [RingHom.mem_ker] at h2
    simpa [MvPolynomial.aeval_def] using h2

/-- A projective point is `mk v` when `c v = t d.rep` with `c ≠ 0`. -/
theorem eq_mk_of_smul_eq {n : ℕ} (d : ProjectivePoint n) (v : Point n) (hv : v ≠ 0)
    (t c : ℂ) (hc : c ≠ 0) (h : c • v = t • d.rep) : d = Projectivization.mk ℂ v hv := by
  have ht : t ≠ 0 := by
    intro ht
    rw [ht, zero_smul] at h
    exact hv ((smul_eq_zero.mp h).resolve_left hc)
  rw [← Projectivization.mk_rep d]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨c / t, ?_⟩
  rw [div_eq_mul_inv, mul_comm, mul_smul, h, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- Block weights for a pair of variable blocks. -/
def wA (n m : ℕ) : Fin (n + m) → ℕ := Fin.addCases (fun _ => 1) (fun _ => 0)

def wB (n m : ℕ) : Fin (n + m) → ℕ := Fin.addCases (fun _ => 0) (fun _ => 1)

theorem weight_wA {n m : ℕ} (d : Fin (n + m) →₀ ℕ) :
    Finsupp.weight (wA n m) d = ∑ i : Fin n, d (Fin.castAdd m i) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_add]
  simp [wA]

theorem weight_wB {n m : ℕ} (d : Fin (n + m) →₀ ℕ) :
    Finsupp.weight (wB n m) d = ∑ i : Fin m, d (Fin.natAdd n i) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_add]
  simp [wB]

theorem mem_pairSet_of_homog {n m s t : ℕ} {P : Poly (n + m)}
    (hA : P.IsWeightedHomogeneous (wA n m) s) (hB : P.IsWeightedHomogeneous (wB n m) t) :
    P ∈ MvPolynomial.restrictSupport ℂ {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧ (∑ i : Fin m, d (Fin.natAdd n i)) = t} := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro d hd
  have hd' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hd)
  exact ⟨by rw [← weight_wA]; exact hA hd', by rw [← weight_wB]; exact hB hd'⟩

theorem sum_eq_of_mem_pairSet {n m s t : ℕ} {F : Poly (n + m)}
    (hF : F ∈ MvPolynomial.restrictSupport ℂ {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧ (∑ i : Fin m, d (Fin.natAdd n i)) = t})
    (d : Fin (n + m) →₀ ℕ) (hd : d ∈ F.support) : (∑ i, 1 * d i) = s + t := by
  rw [MvPolynomial.mem_restrictSupport_iff] at hF
  obtain ⟨h1, h2⟩ := hF (Finset.mem_coe.mpr hd)
  simp only [one_mul]
  rw [Fin.sum_univ_add, h1, h2]

section FibreFamilies

variable {e j N : ℕ} (C : SkewCoordinates e) (V : AffineVariety (skewDim e))
  (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) (a : Fin e)

/-- The parameter-closure equations, pulled back to the middle block. -/
def bLift (G : Poly (e + e)) : Poly (e + (e + e) + (skewDim e + 1)) :=
  MvPolynomial.rename (fun k : Fin (e + e) => Fin.castAdd (skewDim e + 1) (Fin.natAdd e k)) G

/-- The proportionality equations `a_i b_j - a_j b_i` (first half of `b`). -/
def propPoly (i j : Fin e) : Poly (e + (e + e) + (skewDim e + 1)) :=
  MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) *
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.castAdd e j))) -
    MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) j)) *
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.castAdd e i)))

/-- The evaluation-flat equations `x₀ b''_k - D_{x'}(b')_k`. -/
def flatPoly (k : Fin e) : Poly (e + (e + e) + (skewDim e + 1)) :=
  MvPolynomial.X (Fin.natAdd (e + (e + e)) (0 : Fin (skewDim e + 1))) *
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.natAdd e k))) -
    ∑ kk : Fin (skewDim e), ∑ l : Fin e,
      MvPolynomial.C ((C.decode (Pi.single kk 1)).val (Pi.single l 1) (Pi.single k 1)) *
        MvPolynomial.X (Fin.natAdd (e + (e + e)) kk.succ) *
        MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.castAdd e l)))

theorem aeval_bLift (x : Point e) (y : Point (e + e)) (zz : Point (skewDim e + 1))
    (G : Poly (e + e)) :
    MvPolynomial.aeval (joinPoints (joinPoints x y) zz) (bLift G) = MvPolynomial.aeval y G := by
  rw [bLift, MvPolynomial.aeval_rename]
  apply congrArg (fun f : Fin (e + e) → ℂ => MvPolynomial.aeval f G)
  funext k
  simp [joinPoints, Fin.addCases_left, Fin.addCases_right]

theorem aeval_propPoly (x : Point e) (y : Point (e + e)) (zz : Point (skewDim e + 1))
    (i j : Fin e) :
    MvPolynomial.aeval (joinPoints (joinPoints x y) zz) (propPoly i j) =
      x i * firstPoint y j - x j * firstPoint y i := by
  simp [propPoly, joinPoints, firstPoint, Fin.addCases_left, Fin.addCases_right]

theorem aeval_flatPoly (x : Point e) (y : Point (e + e)) (zz : Point (skewDim e + 1))
    (k : Fin e) :
    MvPolynomial.aeval (joinPoints (joinPoints x y) zz) (flatPoly C k) =
      zz 0 * secondPoint y k - (C.decode (Fin.tail zz)).val (firstPoint y) (Pi.single k 1) := by
  rw [decode_expand]
  simp only [flatPoly, map_sub, map_mul, map_sum, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  congr 1
  · simp [joinPoints, secondPoint, Fin.addCases_left, Fin.addCases_right]
  · apply Finset.sum_congr rfl
    intro kk _
    apply Finset.sum_congr rfl
    intro l _
    simp only [joinPoints, Fin.addCases_left, Fin.addCases_right, firstPoint, Fin.tail]
    rw [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
    ring

theorem bLift_mem (R : IsRulingIncidence C V Γ H a j N) (G : Poly (e + e))
    (hG : G ∈ (parameterClosure C Γ H).ideal) :
    bLift G ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives (incidenceTriples C Γ H)) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro w ⟨x, y, zz, hx, hy, hz, hT, rfl⟩
  have hp : Projectivization.mk ℂ y hy ∈ (parameterClosure C Γ H).points := by
    rw [← parameter_base_projection C V Γ H a R]
    exact ⟨_, hT.1⟩
  have hyz := hp y hy rfl
  rw [aeval_bLift]
  have := (MvPolynomial.mem_zeroLocus_iff).mp hyz G hG
  simpa [MvPolynomial.aeval_def] using this

theorem propPoly_mem (i j : Fin e) :
    propPoly i j ∈ MvPolynomial.vanishingIdeal ℂ
      (tripleRepresentatives (incidenceTriples C Γ H)) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro w ⟨x, y, zz, hx, hy, hz, hT, rfl⟩
  rw [aeval_propPoly]
  obtain ⟨t, ht1, -, -⟩ := hT.2
  obtain ⟨α, hα0, hα⟩ := rep_eq_smul_of_mk x hx
  obtain ⟨β, hβ0, hβ⟩ := rep_eq_smul_of_mk y hy
  rw [hα, hβ] at ht1
  have hcomp : ∀ l, β * firstPoint y l = t * α * x l := by
    intro l
    have h := congrFun ht1 l
    simp only [firstPoint, Pi.smul_apply, smul_eq_mul] at h ⊢
    linear_combination h
  have h0 : β * (x i * firstPoint y j - x j * firstPoint y i) = 0 := by
    linear_combination x i * hcomp j - x j * hcomp i
  exact (mul_eq_zero.mp h0).resolve_left hβ0

theorem covectorOfPoint_single (y : Point e) (k : Fin e) :
    covectorOfPoint y (Pi.single k 1) = y k := by
  simp [covectorOfPoint, Pi.single_apply]

theorem flatPoly_mem (k : Fin e) :
    flatPoly C k ∈ MvPolynomial.vanishingIdeal ℂ
      (tripleRepresentatives (incidenceTriples C Γ H)) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro w ⟨x, y, zz, hx, hy, hz, hT, rfl⟩
  rw [aeval_flatPoly]
  obtain ⟨t, ht1, -, hfib⟩ := hT.2
  obtain ⟨α, hα0, hα⟩ := rep_eq_smul_of_mk x hx
  obtain ⟨β, hβ0, hβ⟩ := rep_eq_smul_of_mk y hy
  obtain ⟨γ, hγ0, hγ⟩ := rep_eq_smul_of_mk zz hz
  change ((Projectivization.mk ℂ zz hz).rep 0,
      alternatingEvaluation (Projectivization.mk ℂ x hx).rep
        (C.decode (Fin.tail (Projectivization.mk ℂ zz hz).rep))) ∈
    Submodule.span ℂ {(t, covectorOfPoint (secondPoint (Projectivization.mk ℂ y hy).rep))}
    at hfib
  rw [Submodule.mem_span_singleton] at hfib
  obtain ⟨μ, hμ⟩ := hfib
  have hfst : μ * t = γ * zz 0 := by
    have h := congrArg Prod.fst hμ
    simp only [Prod.smul_mk, smul_eq_mul] at h
    rw [h, hγ]
    simp
  have hsnd : (C.decode (Fin.tail (Projectivization.mk ℂ zz hz).rep)).val
      (Projectivization.mk ℂ x hx).rep = μ • covectorOfPoint
        (secondPoint (Projectivization.mk ℂ y hy).rep) := by
    have h := congrArg Prod.snd hμ
    simp only [Prod.smul_mk] at h
    rw [h]
    rfl
  rw [hα, hβ, hγ] at hsnd
  rw [hα, hβ] at ht1
  have htail : Fin.tail (γ • zz) = γ • Fin.tail zz := by
    funext l
    simp [Fin.tail]
  have hfirst : firstPoint (β • y) = β • firstPoint y := by
    funext l
    simp [firstPoint]
  have hsecond : secondPoint (β • y) = β • secondPoint y := by
    funext l
    simp [secondPoint]
  rw [htail, hsecond, show C.decode (γ • Fin.tail zz) = γ • C.decode (Fin.tail zz) from
    C.decode.map_smul γ _, Submodule.coe_smul] at hsnd
  rw [hfirst] at ht1
  set D0 := (C.decode (Fin.tail zz)).val with hD0
  have hA : γ * (α * D0 x (Pi.single k 1)) = μ * (β * secondPoint y k) := by
    have h := congrArg (fun f : Module.Dual ℂ (Point e) => f (Pi.single k 1)) hsnd
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul] at h
    rw [covectorOfPoint_single] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    linear_combination h
  have hY : β * D0 (firstPoint y) (Pi.single k 1) = t * (α * D0 x (Pi.single k 1)) := by
    have h := congrArg (fun v : Point e => D0 v (Pi.single k 1)) ht1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact h
  have h0 : γ * β * (zz 0 * secondPoint y k - D0 (firstPoint y) (Pi.single k 1)) = 0 := by
    linear_combination (-γ) * hY + (-t) * hA + (-(β * secondPoint y k)) * hfst
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h (mul_ne_zero hγ0 hβ0)
  · exact h

/-- The literal point-parameter fibre over `z`. -/
def fibreParamSet (z : Point (skewDim e)) : Set (ProjectivePoint (e + e)) :=
  {p | p ∈ parameterClosure C Γ H ∧ z ∈ evaluationFlat C p}

theorem covectorOfPoint_smul (c : ℂ) (y : Point e) :
    covectorOfPoint (c • y) = c • covectorOfPoint y := by
  apply LinearMap.ext
  intro w
  simp [covectorOfPoint, Finset.mul_sum, mul_assoc]

theorem pointOfCovector_covectorOfPoint' (y : Point e) :
    pointOfCovector (covectorOfPoint y) = y := by
  funext i
  simp [pointOfCovector, covectorOfPoint, Pi.single_apply]

theorem covector_ext {f g : Module.Dual ℂ (Point e)}
    (h : ∀ k : Fin e, f (Pi.single k 1) = g (Pi.single k 1)) : f = g := by
  apply (Pi.basisFun ℂ (Fin e)).ext
  intro k
  rw [Pi.basisFun_apply]
  exact h k

theorem firstPoint_smul {n m : ℕ} (c : ℂ) (y : Point (n + m)) :
    firstPoint (c • y) = c • firstPoint y := by
  funext l
  simp [firstPoint]

theorem secondPoint_smul {n m : ℕ} (c : ℂ) (y : Point (n + m)) :
    secondPoint (c • y) = c • secondPoint y := by
  funext l
  simp [secondPoint]

theorem joinPoints_add {n m : ℕ} (x x' : Point n) (y y' : Point m) :
    joinPoints (x + x') (y + y') = joinPoints x y + joinPoints x' y' := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [joinPoints]

theorem joinPoints_smul {n m : ℕ} (c : ℂ) (x : Point n) (y : Point m) :
    joinPoints (c • x) (c • y) = c • joinPoints x y := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [joinPoints]

theorem joinPoints_zero {n m : ℕ} : joinPoints (0 : Point n) (0 : Point m) = 0 := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [joinPoints]

/-- Flat condition on a representative. -/
theorem mem_evaluationFlat_mk_iff (z : Point (skewDim e)) (b : Point (e + e)) (hb : b ≠ 0) :
    z ∈ evaluationFlat C (Projectivization.mk ℂ b hb) ↔
      (C.decode z).val (firstPoint b) = covectorOfPoint (secondPoint b) := by
  obtain ⟨β, hβ0, hβ⟩ := rep_eq_smul_of_mk b hb
  change (C.decode z).val (firstPoint (Projectivization.mk ℂ b hb).rep) =
    covectorOfPoint (secondPoint (Projectivization.mk ℂ b hb).rep) ↔ _
  rw [hβ, firstPoint_smul, secondPoint_smul, covectorOfPoint_smul, map_smul]
  constructor
  · intro h
    have h2 := congrArg (fun f => β⁻¹ • f) h
    simp only [smul_smul, inv_mul_cancel₀ hβ0, one_smul] at h2
    exact h2
  · intro h
    rw [h]

/-- On the flat, the first half of a nonzero vector is nonzero. -/
theorem firstPoint_ne_zero_of_flat (z : Point (skewDim e)) (b : Point (e + e)) (hb : b ≠ 0)
    (h : (C.decode z).val (firstPoint b) = covectorOfPoint (secondPoint b)) :
    firstPoint b ≠ 0 := by
  intro h0
  rw [h0, map_zero] at h
  have hs : secondPoint b = 0 := by
    rw [← pointOfCovector_covectorOfPoint' (secondPoint b), ← h]
    funext i
    simp [pointOfCovector]
  apply hb
  rw [← joinPoints_eta b, h0, hs, joinPoints_zero]

/-- Points of the fibre zero locus lie over the point-parameter fibre, with proportional
first block. -/
theorem zeroLocus_fibre_structure (R : IsRulingIncidence C V Γ H a j N)
    (z : Point (skewDim e)) (x : Point e) (b : Point (e + e)) (hb : b ≠ 0)
    (hw : joinPoints x b ∈ MvPolynomial.zeroLocus ℂ
      (tripleFibreIdeal (incidenceTriples C Γ H) z)) :
    Projectivization.mk ℂ b hb ∈ fibreParamSet C Γ H z ∧ ∃ c : ℂ, x = c • firstPoint b := by
  have hzero := (mem_zeroLocus_tripleFibreIdeal _ z _).mp hw
  have hpc : Projectivization.mk ℂ b hb ∈ (parameterClosure C Γ H).points := by
    rw [ProjectiveVariety.mem_points_mk_iff]
    change b ∈ MvPolynomial.zeroLocus ℂ (parameterClosure C Γ H).ideal
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro G hG
    have h := hzero _ (bLift_mem C V Γ H a R G hG)
    rw [aeval_bLift] at h
    simpa [MvPolynomial.aeval_def] using h
  have hflat : (C.decode z).val (firstPoint b) = covectorOfPoint (secondPoint b) := by
    apply covector_ext
    intro k
    have h := hzero _ (flatPoly_mem C Γ H k)
    rw [aeval_flatPoly, Fin.cons_zero, Fin.tail_cons, one_mul] at h
    rw [covectorOfPoint_single]
    linear_combination -h
  refine ⟨⟨hpc, (mem_evaluationFlat_mk_iff C z b hb).mpr hflat⟩, ?_⟩
  have hfb := firstPoint_ne_zero_of_flat C z b hb hflat
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hfb
  refine ⟨x j0 / firstPoint b j0, ?_⟩
  funext i
  have h := hzero _ (propPoly_mem C Γ H i j0)
  rw [aeval_propPoly] at h
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj0 ⊢
  field_simp
  linear_combination h

/-- Graph points over the point-parameter fibre lie in the fibre zero locus. -/
theorem graph_mem_zeroLocus (R : IsRulingIncidence C V Γ H a j N)
    (z : Point (skewDim e)) (y : Point (e + e)) (hy : y ≠ 0)
    (hp : Projectivization.mk ℂ y hy ∈ fibreParamSet C Γ H z) :
    joinPoints (firstPoint y) y ∈ MvPolynomial.zeroLocus ℂ
      (tripleFibreIdeal (incidenceTriples C Γ H) z) := by
  obtain ⟨hpc, hflat⟩ := hp
  rw [mem_evaluationFlat_mk_iff C z y hy] at hflat
  have hfy := firstPoint_ne_zero_of_flat C z y hy hflat
  obtain ⟨β, hβ0, hβ⟩ := rep_eq_smul_of_mk y hy
  have hgraph : graphVector C z (firstPoint y) = y := by
    rw [graphVector, hflat, pointOfCovector_covectorOfPoint', joinPoints_eta]
  have hfull : Projectivization.mk ℂ y hy ∈
      {p | ∃ d : ProjectivePoint e, incidenceCondition C d p (affineEmbedding z)} := by
    rw [full_point_fiber C z]
    refine ⟨firstPoint y, hfy, ?_⟩
    rw [graphParameter, Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, hgraph]⟩
  obtain ⟨d, hd⟩ := hfull
  have hdeq : d = Projectivization.mk ℂ (firstPoint y) hfy := by
    obtain ⟨t, ht, -, -⟩ := hd
    rw [hβ, firstPoint_smul] at ht
    exact eq_mk_of_smul_eq d _ hfy t β hβ0 ht
  have hbase : Projectivization.mk ℂ y hy ∈
      {p | ∃ d : ProjectivePoint e, (d, p) ∈ liftedParameterBase C Γ H} := by
    rw [parameter_base_projection C V Γ H a R]
    exact hpc
  obtain ⟨d', hd'⟩ := hbase
  have hd'eq : d' = Projectivization.mk ℂ (firstPoint y) hfy := by
    obtain ⟨t, ht, -⟩ := parameter_base_resolution C V Γ H a R hd'
    change firstPoint (Projectivization.mk ℂ y hy).rep = t • d'.rep at ht
    rw [hβ, firstPoint_smul] at ht
    exact eq_mk_of_smul_eq d' _ hfy t β hβ0 ht
  rw [hdeq] at hd
  rw [hd'eq] at hd'
  rw [mem_zeroLocus_tripleFibreIdeal]
  intro F hF
  have h := (MvPolynomial.mem_vanishingIdeal_iff.mp hF) _
    ⟨firstPoint y, y, Fin.cons 1 z, hfy, hy, consOne_ne_zero z, ⟨hd', hd⟩, rfl⟩
  simpa [MvPolynomial.aeval_def] using h

theorem graphVector_first_eq (z : Point (skewDim e)) (y : Point (e + e)) (hy : y ≠ 0)
    (hp : Projectivization.mk ℂ y hy ∈ fibreParamSet C Γ H z) :
    graphVector C z (firstPoint y) = y := by
  have hflat := (mem_evaluationFlat_mk_iff C z y hy).mp hp.2
  rw [graphVector, hflat, pointOfCovector_covectorOfPoint', joinPoints_eta]

theorem pointOfCovector_add (f g : Module.Dual ℂ (Point e)) :
    pointOfCovector (f + g) = pointOfCovector f + pointOfCovector g := by
  funext i
  simp [pointOfCovector]

theorem pointOfCovector_smul (c : ℂ) (f : Module.Dual ℂ (Point e)) :
    pointOfCovector (c • f) = c • pointOfCovector f := by
  funext i
  simp [pointOfCovector]

/-- The graph map `v ↦ (v, D_z v)` as a linear map. -/
def graphLin (z : Point (skewDim e)) : Point e →ₗ[ℂ] Point (e + e) where
  toFun v := graphVector C z v
  map_add' v w := by
    simp only [graphVector, map_add, pointOfCovector_add, joinPoints_add]
  map_smul' c v := by
    simp only [graphVector, map_smul, RingHom.id_apply, pointOfCovector_smul, joinPoints_smul]

theorem graphVector_expand (z : Point (skewDim e)) (v : Point e) (k : Fin (e + e)) :
    graphVector C z v k = ∑ i : Fin e, graphVector C z (Pi.single i 1) k * v i := by
  have h := (graphLin C z).pi_apply_eq_sum_univ v
  have hk := congrFun h k
  change graphVector C z v k = _ at hk
  rw [hk, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hsingle : (fun j => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  congr 2
  change graphVector C z _ k = _
  rw [hsingle]

/-- Substitution of the graph into the first block: `y ↦ (a, D_z a)`. -/
def graphSubst (z : Point (skewDim e)) : Poly (e + e) →ₐ[ℂ] Poly (e + (e + e)) :=
  MvPolynomial.aeval (fun k => ∑ i : Fin e,
    MvPolynomial.C (graphVector C z (Pi.single i 1) k) * MvPolynomial.X (Fin.castAdd (e + e) i))

/-- Inclusion of the second block. -/
def secondSubst : Poly (e + e) →ₐ[ℂ] Poly (e + (e + e)) :=
  MvPolynomial.aeval (fun k => MvPolynomial.X (Fin.natAdd e k))

theorem aeval_graphSubst (z : Point (skewDim e)) (x : Point e) (y : Point (e + e))
    (P : Poly (e + e)) :
    MvPolynomial.aeval (joinPoints x y) (graphSubst C z P) =
      MvPolynomial.aeval (graphVector C z x) P := by
  rw [graphSubst, GenericFiber.eval_aeval]
  apply congrArg (fun f : Fin (e + e) → ℂ => MvPolynomial.aeval f P)
  funext k
  rw [graphVector_expand]
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  apply Finset.sum_congr rfl
  intro i _
  simp [joinPoints, Fin.addCases_left]

theorem aeval_secondSubst (x : Point e) (y : Point (e + e)) (P : Poly (e + e)) :
    MvPolynomial.aeval (joinPoints x y) (secondSubst P) = MvPolynomial.aeval y P := by
  rw [secondSubst, GenericFiber.eval_aeval]
  apply congrArg (fun f : Fin (e + e) → ℂ => MvPolynomial.aeval f P)
  funext k
  simp [joinPoints, Fin.addCases_right]

theorem graphSubst_homog (z : Point (skewDim e)) {P : Poly (e + e)} {D : ℕ}
    (hP : P.IsHomogeneous D) :
    (graphSubst C z P).IsWeightedHomogeneous (wA e (e + e)) D ∧
      (graphSubst C z P).IsWeightedHomogeneous (wB e (e + e)) 0 := by
  have hdeg : ∀ d ∈ P.support, (∑ i, 1 * d i) = D := by
    intro d hd
    have h := hP (MvPolynomial.mem_support_iff.mp hd)
    simp only [one_mul]
    rw [← RulingMaps.degree_eq_sum_univ, Finsupp.degree_eq_weight_one]
    exact h
  constructor
  · apply aeval_isWeightedHomogeneous _ _ (fun _ => 1) _ P D hdeg
    intro k
    apply Submodule.sum_mem (MvPolynomial.weightedHomogeneousSubmodule ℂ (wA e (e + e)) 1)
    intro i _
    have hX : (MvPolynomial.X (Fin.castAdd (e + e) i) : Poly (e + (e + e))).IsWeightedHomogeneous
        (wA e (e + e)) 1 := by
      have := MvPolynomial.isWeightedHomogeneous_X ℂ (wA e (e + e)) (Fin.castAdd (e + e) i)
      simpa [wA] using this
    have := (MvPolynomial.isWeightedHomogeneous_C (wA e (e + e))
      (graphVector C z (Pi.single i 1) k)).mul hX
    simpa using this
  · apply aeval_isWeightedHomogeneous _ _ (fun _ => 0) _ P 0 (by intro d _; simp)
    intro k
    apply Submodule.sum_mem (MvPolynomial.weightedHomogeneousSubmodule ℂ (wB e (e + e)) 0)
    intro i _
    have hX : (MvPolynomial.X (Fin.castAdd (e + e) i) : Poly (e + (e + e))).IsWeightedHomogeneous
        (wB e (e + e)) 0 := by
      have := MvPolynomial.isWeightedHomogeneous_X ℂ (wB e (e + e)) (Fin.castAdd (e + e) i)
      simpa [wB] using this
    have := (MvPolynomial.isWeightedHomogeneous_C (wB e (e + e))
      (graphVector C z (Pi.single i 1) k)).mul hX
    simpa using this

theorem secondSubst_homog {P : Poly (e + e)} {D : ℕ} (hP : P.IsHomogeneous D) :
    (secondSubst P).IsWeightedHomogeneous (wA e (e + e)) 0 ∧
      (secondSubst P).IsWeightedHomogeneous (wB e (e + e)) D := by
  have hdeg : ∀ d ∈ P.support, (∑ i, 1 * d i) = D := by
    intro d hd
    have h := hP (MvPolynomial.mem_support_iff.mp hd)
    simp only [one_mul]
    rw [← RulingMaps.degree_eq_sum_univ, Finsupp.degree_eq_weight_one]
    exact h
  constructor
  · apply aeval_isWeightedHomogeneous _ _ (fun _ => 0) _ P 0 (by intro d _; simp)
    intro k
    have := MvPolynomial.isWeightedHomogeneous_X ℂ (wA e (e + e)) (Fin.natAdd e k)
    simpa [wA] using this
  · apply aeval_isWeightedHomogeneous _ _ (fun _ => 1) _ P D hdeg
    intro k
    have := MvPolynomial.isWeightedHomogeneous_X ℂ (wB e (e + e)) (Fin.natAdd e k)
    simpa [wB] using this

/-- Every form of degree `s+t` agrees on graph points with a bidegree-`(s,t)` polynomial. -/
theorem exists_pair_lift (z : Point (skewDim e)) (s t : ℕ) (G : Poly (e + e))
    (hG : G.IsHomogeneous (s + t)) :
    ∃ F ∈ MvPolynomial.restrictSupport ℂ {d : Fin (e + (e + e)) →₀ ℕ |
        (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t},
      ∀ y : Point (e + e), graphVector C z (firstPoint y) = y →
        MvPolynomial.aeval (joinPoints (firstPoint y) y) F = MvPolynomial.aeval y G := by
  classical
  have hsplit : ∀ d ∈ G.support, ∃ d1 d2 : Fin (e + e) →₀ ℕ,
      d = d1 + d2 ∧ d1.degree = s ∧ d2.degree = t := by
    intro d hd
    have h : d.degree = s + t := by
      rw [Finsupp.degree_eq_weight_one]
      exact hG (MvPolynomial.mem_support_iff.mp hd)
    rw [RulingMaps.degree_eq_sum_univ] at h
    obtain ⟨μ1, μ2, hμ, h1, h2⟩ := split_sum_fun s t (⇑d) h
    refine ⟨Finsupp.equivFunOnFinite.symm μ1, Finsupp.equivFunOnFinite.symm μ2, ?_, ?_, ?_⟩
    · ext i
      simp [hμ i]
    · rw [RulingMaps.degree_eq_sum_univ]
      simpa using h1
    · rw [RulingMaps.degree_eq_sum_univ]
      simpa using h2
  choose! d1 d2 hd12 hd1 hd2 using hsplit
  refine ⟨∑ d ∈ G.support, MvPolynomial.C (G.coeff d) *
      graphSubst C z (MvPolynomial.monomial (d1 d) 1) *
      secondSubst (MvPolynomial.monomial (d2 d) 1), ?_, ?_⟩
  · apply Submodule.sum_mem
    intro d hd
    obtain ⟨hA1, hB1⟩ := graphSubst_homog C z
      (MvPolynomial.isHomogeneous_monomial (1 : ℂ) (hd1 d hd))
    obtain ⟨hA2, hB2⟩ := secondSubst_homog
      (MvPolynomial.isHomogeneous_monomial (1 : ℂ) (hd2 d hd))
    apply mem_pairSet_of_homog
    · have := ((MvPolynomial.isWeightedHomogeneous_C (wA e (e + e)) (G.coeff d)).mul hA1).mul hA2
      simpa using this
    · have := ((MvPolynomial.isWeightedHomogeneous_C (wB e (e + e)) (G.coeff d)).mul hB1).mul hB2
      simpa using this
  · intro y hy
    calc MvPolynomial.aeval (joinPoints (firstPoint y) y) (∑ d ∈ G.support,
          MvPolynomial.C (G.coeff d) * graphSubst C z (MvPolynomial.monomial (d1 d) 1) *
            secondSubst (MvPolynomial.monomial (d2 d) 1))
        = ∑ d ∈ G.support, MvPolynomial.aeval y (MvPolynomial.C (G.coeff d) *
            MvPolynomial.monomial (d1 d) 1 * MvPolynomial.monomial (d2 d) 1) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro d _
          rw [map_mul, map_mul, aeval_graphSubst, aeval_secondSubst, hy, map_mul, map_mul,
            MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      _ = ∑ d ∈ G.support, MvPolynomial.aeval y (MvPolynomial.monomial d (G.coeff d)) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial, ← hd12 d hd, mul_one,
            mul_one]
      _ = MvPolynomial.aeval y G := by
          rw [← map_sum, ← MvPolynomial.as_sum]

/-- Collapse `(a, b) ↦ (b', b)`: the first block becomes the first half of `b`. -/
def pairCollapse : Poly (e + (e + e)) →ₐ[ℂ] Poly (e + e) :=
  MvPolynomial.aeval (Fin.append (fun i : Fin e => MvPolynomial.X (Fin.castAdd e i))
    (fun k : Fin (e + e) => MvPolynomial.X k))

theorem aeval_pairCollapse (y : Point (e + e)) (F : Poly (e + (e + e))) :
    MvPolynomial.aeval y (pairCollapse F) = MvPolynomial.aeval (joinPoints (firstPoint y) y) F := by
  rw [pairCollapse, GenericFiber.eval_aeval]
  apply congrArg (fun f : Fin (e + (e + e)) → ℂ => MvPolynomial.aeval f F)
  funext i
  refine Fin.addCases (fun i => ?_) (fun k => ?_) i
  · simp [joinPoints, firstPoint, Fin.append_left]
  · simp [joinPoints, Fin.append_right]

theorem pairCollapse_homog {s t : ℕ} {F : Poly (e + (e + e))}
    (hF : F ∈ MvPolynomial.restrictSupport ℂ {d : Fin (e + (e + e)) →₀ ℕ |
      (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
        (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) :
    (pairCollapse F).IsHomogeneous (s + t) := by
  apply aeval_isWeightedHomogeneous 1 _ (fun _ => 1) _ F (s + t)
    (sum_eq_of_mem_pairSet hF)
  intro i
  refine Fin.addCases (fun i => ?_) (fun k => ?_) i
  · simpa [Fin.append_left] using MvPolynomial.isWeightedHomogeneous_X ℂ
      (1 : Fin (e + e) → ℕ) (Fin.castAdd e i)
  · simpa [Fin.append_right] using MvPolynomial.isWeightedHomogeneous_X ℂ
      (1 : Fin (e + e) → ℕ) k

/-- Nonzero representatives of the point-parameter fibre, as an index type. -/
abbrev FibreRep (z : Point (skewDim e)) :=
  {y : Point (e + e) // y ∈ ProjectiveVariety.nonzeroRepresentatives (fibreParamSet C Γ H z)}

def evPair (z : Point (skewDim e)) : Poly (e + (e + e)) →ₗ[ℂ] (FibreRep C Γ H z → ℂ) where
  toFun F y := MvPolynomial.aeval (joinPoints (firstPoint y.1) y.1) F
  map_add' F F' := by
    funext y
    simp
  map_smul' c F := by
    funext y
    simp

def evFibre (z : Point (skewDim e)) : Poly (e + e) →ₗ[ℂ] (FibreRep C Γ H z → ℂ) where
  toFun G y := MvPolynomial.aeval y.1 G
  map_add' G G' := by
    funext y
    simp
  map_smul' c G := by
    funext y
    simp

/-- The Hilbert bridge: a radical fibre ideal has bigraded Hilbert function `HF_Y(s+t)`,
`Y` the closure of the point-parameter fibre. -/
theorem fibre_hilbert_eq_closure (R : IsRulingIncidence C V Γ H a j N)
    (z : Point (skewDim e))
    (hrad : (tripleFibreIdeal (incidenceTriples C Γ H) z).IsRadical)
    (s t : ℕ) (_hs : 1 ≤ s) (ht : 1 ≤ t) :
    idealPairHilbert (tripleFibreIdeal (incidenceTriples C Γ H) z) s t =
      (ProjectiveVariety.closure (fibreParamSet C Γ H z)).hilbert (s + t) := by
  classical
  set J := tripleFibreIdeal (incidenceTriples C Γ H) z with hJ
  set RS := MvPolynomial.restrictSupport ℂ {d : Fin (e + (e + e)) →₀ ℕ |
    (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
      (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t} with hRS
  have h1 : idealPairHilbert J s t = Module.finrank ℂ (RS.map (evPair C Γ H z)) := by
    unfold idealPairHilbert idealPairSection
    apply finrank_map_eq_of_ker_iff
    intro F hF
    rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hFJ
      funext y
      obtain ⟨hy0, hy⟩ := y.2
      have hw := graph_mem_zeroLocus C V Γ H a R z y.1 hy0 hy
      have h := (MvPolynomial.mem_zeroLocus_iff.mp hw) F hFJ
      simpa [evPair, MvPolynomial.aeval_def] using h
    · intro hev
      have hJrad : J = MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J) := by
        rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hrad.radical]
      rw [hJrad, MvPolynomial.mem_vanishingIdeal_iff]
      intro w hw
      rw [← joinPoints_eta w]
      rw [← joinPoints_eta w] at hw
      by_cases hb : secondPoint w = 0
      · have h := aeval_joinPoints_smul_pair hF (firstPoint w) (secondPoint w) 1 0
        rw [one_smul, zero_smul, ← hb, zero_pow (by omega), mul_zero, zero_mul] at h
        exact h
      · obtain ⟨hp, c, hc⟩ := zeroLocus_fibre_structure C V Γ H a R z (firstPoint w)
          (secondPoint w) hb hw
        have h := aeval_joinPoints_smul_pair hF (firstPoint (secondPoint w)) (secondPoint w) c 1
        rw [one_smul, ← hc] at h
        rw [h]
        have hev' := congrFun hev ⟨secondPoint w, hb, hp⟩
        change MvPolynomial.aeval (joinPoints (firstPoint (secondPoint w)) (secondPoint w)) F
          = 0 at hev'
        rw [hev', mul_zero]
  have h2 : RS.map (evPair C Γ H z) =
      (MvPolynomial.homogeneousSubmodule (Fin (e + e)) ℂ (s + t)).map (evFibre C Γ H z) := by
    apply le_antisymm
    · rintro _ ⟨F, hF, rfl⟩
      refine ⟨pairCollapse F, ?_, ?_⟩
      · rw [SetLike.mem_coe, MvPolynomial.mem_homogeneousSubmodule]
        exact pairCollapse_homog hF
      · funext y
        change MvPolynomial.aeval y.1 (pairCollapse F) = _
        rw [aeval_pairCollapse]
        rfl
    · rintro _ ⟨G, hG, rfl⟩
      rw [SetLike.mem_coe, MvPolynomial.mem_homogeneousSubmodule] at hG
      obtain ⟨F, hF, hFG⟩ := exists_pair_lift C z s t G hG
      refine ⟨F, hF, ?_⟩
      funext y
      exact hFG y.1 (graphVector_first_eq C Γ H z y.1 y.2.1 y.2.2)
  have h3 : (ProjectiveVariety.closure (fibreParamSet C Γ H z)).hilbert (s + t) =
      Module.finrank ℂ ((MvPolynomial.homogeneousSubmodule (Fin (e + e)) ℂ (s + t)).map
        (evFibre C Γ H z)) := by
    unfold ProjectiveVariety.hilbert
    change Module.finrank ℂ ((MvPolynomial.homogeneousSubmodule (Fin (e + e)) ℂ (s + t)).map
      (Ideal.Quotient.mkₐ ℂ (ProjectiveVariety.closure (fibreParamSet C Γ H z)).ideal).toLinearMap)
      = _
    apply finrank_map_eq_of_ker_iff
    intro G _
    rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    change G ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives (fibreParamSet C Γ H z)) ↔ _
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    constructor
    · intro h
      funext y
      have := h y.1 y.2
      simpa [evFibre, MvPolynomial.aeval_def] using this
    · intro h y hy
      have := congrFun h ⟨y, hy⟩
      simpa [evFibre, MvPolynomial.aeval_def] using this
  rw [h1, h2, h3]

end FibreFamilies

/-! ### Generic reducedness in characteristic zero -/

section CharZeroReduced
open scoped TensorProduct
set_option linter.style.haveILetI false

/-- Characteristic zero: a finitely generated domain stays reduced after any field base
change. Noether normalization plus OAI's finite flat domain tensor lemma. -/
theorem isReduced_tensor_fg_domain (L E D : Type) [Field L] [CharZero L] [Field E]
    [Algebra L E] [CommRing D] [IsDomain D] [Algebra L D] [Algebra.FiniteType L D] :
    IsReduced (E ⊗[L] D) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg L D
  let R := MvPolynomial (Fin s) L
  letI : Algebra R D := g.toRingHom.toAlgebra
  haveI : IsScalarTower L R D := IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  haveI : Module.Finite R D := hfin
  haveI : FaithfulSMul R D := (faithfulSMul_iff_algebraMap_injective R D).mpr hg
  haveI : IsDomain (R ⊗[L] E) := by
    let e1 := Algebra.TensorProduct.comm L R E
    let e2 := MvPolynomial.algebraTensorAlgEquiv (σ := Fin s) L E
    let f : R ⊗[L] E ≃+* MvPolynomial (Fin s) E := e1.toRingEquiv.trans e2.toRingEquiv
    exact Function.Injective.isDomain f.toRingHom f.injective
  haveI : FaithfulSMul R (R ⊗[L] E) := (faithfulSMul_iff_algebraMap_injective R _).mpr
    (Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap L E).injective)
  have hred : IsReduced ((R ⊗[L] E) ⊗[R] D) :=
    OAI.BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness.reduced_flat_domain_tensor
      (R := R) (A := R ⊗[L] E) (S := D)
  let e3 := Algebra.TensorProduct.comm R (R ⊗[L] E) D
  let e4 := Algebra.TensorProduct.cancelBaseChange L R R D E
  let e5 := Algebra.TensorProduct.comm L D E
  let eall : E ⊗[L] D ≃+* (R ⊗[L] E) ⊗[R] D :=
    (e5.symm.toRingEquiv.trans e4.symm.toRingEquiv).trans e3.symm.toRingEquiv
  exact isReduced_of_injective eall eall.injective

/-- Characteristic zero: a reduced algebra stays reduced after any field base change. -/
theorem isReduced_tensor_charZero (L E B : Type) [Field L] [CharZero L] [Field E]
    [Algebra L E] [CommRing B] [Algebra L B] [IsReduced B] : IsReduced (E ⊗[L] B) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B' hB'
  classical
  haveI : Algebra.FiniteType L B' := (Subalgebra.fg_iff_finiteType B').mp hB'
  haveI : IsReduced B' := isReduced_of_injective B'.val Subtype.val_injective
  haveI : IsNoetherianRing B' := Algebra.FiniteType.isNoetherianRing L B'
  have hfin := minimalPrimes.finite_of_isNoetherianRing B'
  haveI : Fintype (minimalPrimes B') := hfin.fintype
  let φ : B' →ₐ[L] ((p : minimalPrimes B') → B' ⧸ (p : Ideal B')) :=
    AlgHom.pi (fun p => Ideal.Quotient.mkₐ L (p : Ideal B'))
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hmem : x ∈ sInf (minimalPrimes B') := by
      rw [Submodule.mem_sInf]
      intro p hp
      have h := congrFun hx ⟨p, hp⟩
      change Ideal.Quotient.mk p x = 0 at h
      exact Ideal.Quotient.eq_zero_iff_mem.mp h
    rw [Ideal.sInf_minimalPrimes] at hmem
    obtain ⟨n, hn⟩ := hmem
    exact IsReduced.eq_zero x ⟨n, Ideal.mem_bot.mp hn⟩
  let ψ : E ⊗[L] B' →ₐ[L] E ⊗[L] ((p : minimalPrimes B') → B' ⧸ (p : Ideal B')) :=
    Algebra.TensorProduct.map (AlgHom.id L E) φ
  have hψ : Function.Injective ψ :=
    Module.Flat.lTensor_preserves_injective_linearMap φ.toLinearMap hφ
  let χ := Algebra.TensorProduct.piRight L L E (fun p : minimalPrimes B' => B' ⧸ (p : Ideal B'))
  haveI hq : ∀ p : minimalPrimes B', IsReduced (E ⊗[L] (B' ⧸ (p : Ideal B'))) := by
    intro p
    haveI : (p : Ideal B').IsPrime := Ideal.IsMinimalPrime.isPrime p.2
    haveI : Algebra.FiniteType L (B' ⧸ (p : Ideal B')) := inferInstance
    exact isReduced_tensor_fg_domain L E _
  haveI : IsReduced ((p : minimalPrimes B') → E ⊗[L] (B' ⧸ (p : Ideal B'))) := by
    constructor
    intro x hx
    funext p
    obtain ⟨n, hn⟩ := hx
    exact IsReduced.eq_zero (x p) ⟨n, by have h := congrFun hn p; rwa [Pi.pow_apply] at h⟩
  exact isReduced_of_injective (χ.toAlgHom.comp ψ) (χ.injective.comp hψ)

section GenericSpecialization

variable {q N : ℕ} (k : Subfield ℂ)

/-- Specialize the last `N` variables at `ξ`. -/
def specX (ξ : Fin N → ℂ) : MvPolynomial (Fin (q + N)) ℂ →ₐ[ℂ] MvPolynomial (Fin q) ℂ :=
  MvPolynomial.aeval (Fin.append (fun i => MvPolynomial.X i) (fun l => MvPolynomial.C (ξ l)))

/-- Coefficient inclusion from the subfield `k`. -/
abbrev kIncl (n : ℕ) : MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) ℂ :=
  MvPolynomial.map k.subtype

theorem specX_kIncl_rename (ξ : Fin N → ℂ) (f : MvPolynomial (Fin N) k) :
    specX ξ (kIncl k (q + N) (MvPolynomial.rename (Fin.natAdd q) f)) =
      MvPolynomial.C (MvPolynomial.eval₂ k.subtype ξ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [specX, kIncl]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg, MvPolynomial.eval₂_add, map_add]
  | mul_X f l hf =>
      simp only [map_mul, hf, MvPolynomial.rename_X, MvPolynomial.map_X, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X]
      simp [specX, Fin.append_right]


set_option maxHeartbeats 1000000 in
/-- Core of generic reducedness: if every `k`-rational `x`-polynomial vanishing at `ξ` lies in
the radical ideal `P`, and `P` is generated by `k`-rational elements, then the specialization
of `P` at `ξ` is radical. -/
theorem isRadical_specX (P : Ideal (MvPolynomial (Fin (q + N)) ℂ)) (hP : P.IsRadical)
    (hgen : P ≤ Ideal.span (kIncl k (q + N) '' (P.comap (kIncl k (q + N)))))
    (ξ : Fin N → ℂ)
    (hstar : ∀ f : MvPolynomial (Fin N) k, MvPolynomial.eval₂ k.subtype ξ f = 0 →
      kIncl k (q + N) (MvPolynomial.rename (Fin.natAdd q) f) ∈ P) :
    (P.map (specX ξ)).IsRadical := by
  classical
  set ι := kIncl k (q + N) with hι
  set P0 := P.comap ι with hP0
  let B0 := MvPolynomial (Fin (q + N)) k ⧸ P0
  letI : CommRing B0 := Ideal.Quotient.commRing P0
  have hP0rad : P0.IsRadical := hP.comap ι
  haveI : IsReduced B0 := (Ideal.isRadical_iff_quotient_reduced P0).mp hP0rad
  let evξ : MvPolynomial (Fin N) k →+* ℂ := MvPolynomial.eval₂Hom k.subtype ξ
  let Abar := MvPolynomial (Fin N) k ⧸ RingHom.ker evξ
  letI : CommRing Abar := Ideal.Quotient.commRing _
  haveI : (RingHom.ker evξ).IsPrime := RingHom.ker_isPrime evξ
  haveI : IsDomain Abar := Ideal.Quotient.isDomain _
  let L := FractionRing Abar
  have hφ0 : Function.Injective (RingHom.kerLift evξ) := RingHom.kerLift_injective evξ
  let φ : L →+* ℂ := IsFractionRing.lift (A := Abar) (K := L) (g := RingHom.kerLift evξ) hφ0
  -- `B0` as an `Abar`-algebra through the `x`-variables
  letI instR : Algebra (MvPolynomial (Fin N) k) (MvPolynomial (Fin (q + N)) k) :=
    (MvPolynomial.rename (Fin.natAdd q)).toRingHom.toAlgebra
  have hle : RingHom.ker evξ ≤ P0.comap (algebraMap (MvPolynomial (Fin N) k)
      (MvPolynomial (Fin (q + N)) k)) := by
    intro f hf
    rw [RingHom.mem_ker] at hf
    exact hstar f hf
  letI instAB : Algebra Abar B0 := Ideal.Quotient.algebraQuotientOfLEComap hle
  let M : Submonoid B0 := Algebra.algebraMapSubmonoid B0 (nonZeroDivisors Abar)
  let T0 := Localization M
  have hM : nonZeroDivisors Abar ≤ M.comap (algebraMap Abar B0) := by
    intro a ha
    exact Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, ha⟩ : nonZeroDivisors Abar)
  haveI hT0 : IsLocalization M T0 := Localization.isLocalization
  haveI : IsReduced T0 := inferInstance
  letI instLT : Algebra L T0 :=
    (IsLocalization.map T0 (algebraMap Abar B0) hM : L →+* T0).toAlgebra
  letI instLC : Algebra L ℂ := φ.toAlgebra
  haveI : CharZero L := RingHom.charZero φ
  haveI : IsReduced (ℂ ⊗[L] T0) := isReduced_tensor_charZero L ℂ T0
  have hLT : ∀ ℓ : L, algebraMap L T0 ℓ = IsLocalization.map T0 (algebraMap Abar B0) hM ℓ :=
    fun _ => rfl
  have hBA : ∀ a : Abar, algebraMap B0 T0 (algebraMap Abar B0 a) =
      algebraMap L T0 (algebraMap Abar L a) := by
    intro a
    rw [hLT, IsLocalization.map_eq]
  have hφA : ∀ a : Abar, φ (algebraMap Abar L a) = RingHom.kerLift evξ a := by
    intro a
    exact IsFractionRing.lift_algebraMap _ _
  have hAmk : ∀ f : MvPolynomial (Fin N) k,
      algebraMap Abar B0 (Ideal.Quotient.mk _ f) =
        Ideal.Quotient.mk P0 (MvPolynomial.rename (Fin.natAdd q) f) := fun _ => rfl
  -- the comparison map from the fibre ring
  let Φ : MvPolynomial (Fin q) ℂ →ₐ[ℂ] ℂ ⊗[L] T0 := MvPolynomial.aeval
    (fun i => (1 : ℂ) ⊗ₜ[L] algebraMap B0 T0
      (Ideal.Quotient.mk P0 (MvPolynomial.X (Fin.castAdd N i))))
  have hscalar : ∀ a : Abar, (1 : ℂ) ⊗ₜ[L] algebraMap B0 T0 (algebraMap Abar B0 a) =
      algebraMap ℂ (ℂ ⊗[L] T0) (RingHom.kerLift evξ a) := by
    intro a
    rw [hBA, ← Algebra.TensorProduct.tmul_one_eq_one_tmul, Algebra.TensorProduct.algebraMap_apply]
    congr 1
    change φ (algebraMap Abar L a) = _
    exact hφA a
  have hkey : ∀ F0 : MvPolynomial (Fin (q + N)) k, Φ (specX ξ (ι F0)) =
      (1 : ℂ) ⊗ₜ[L] algebraMap B0 T0 (Ideal.Quotient.mk P0 F0) := by
    intro F0
    change ((Φ.toRingHom.comp (specX ξ).toRingHom).comp ι) F0 =
      ((Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap B0 T0)).comp
        (Ideal.Quotient.mk P0)) F0
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      have h := hscalar (Ideal.Quotient.mk _ (MvPolynomial.C r))
      rw [hAmk, MvPolynomial.rename_C] at h
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.includeRight_apply]
      rw [h]
      simp [ι, specX, Φ, evξ]
    · intro j
      refine Fin.addCases (fun i => ?_) (fun l => ?_) j
      · simp [ι, specX, Φ, Fin.append_left]
      · have h := hscalar (Ideal.Quotient.mk _ (MvPolynomial.X l))
        rw [hAmk, MvPolynomial.rename_X] at h
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply]
        rw [h]
        simp [ι, specX, Φ, evξ, Fin.append_right]
  set J := P.map (specX ξ) with hJ
  have hJΦ : ∀ F ∈ J, Φ F = 0 := by
    intro F hF
    have hle : J ≤ RingHom.ker (Φ : MvPolynomial (Fin q) ℂ →+* ℂ ⊗[L] T0) := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      refine hgen.trans ?_
      rw [Ideal.span_le]
      rintro _ ⟨F0, hF0, rfl⟩
      change Φ (specX ξ (ι F0)) = 0
      rw [hkey, (Ideal.Quotient.eq_zero_iff_mem).mpr hF0, map_zero, TensorProduct.tmul_zero]
    exact hle hF
  let Φbar := Ideal.Quotient.liftₐ J Φ hJΦ
  -- the inverse direction
  let C := MvPolynomial (Fin q) ℂ ⧸ J
  letI instLC' : Algebra L C := Algebra.compHom C φ
  let β0 : MvPolynomial (Fin (q + N)) k →+* C :=
    (Ideal.Quotient.mk J).comp ((specX ξ).toRingHom.comp ι)
  have hβ0 : ∀ F0 ∈ P0, β0 F0 = 0 := by
    intro F0 hF0
    change Ideal.Quotient.mk J (specX ξ (ι F0)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hF0
  let β1 : B0 →+* C := Ideal.Quotient.lift P0 β0 hβ0
  have hβA : ∀ a : Abar, β1 (algebraMap Abar B0 a) = algebraMap ℂ C (RingHom.kerLift evξ a) := by
    intro a
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hAmk]
    change Ideal.Quotient.mk J (specX ξ (ι (MvPolynomial.rename (Fin.natAdd q) f))) = _
    rw [specX_kIncl_rename]
    rfl
  have hβunit : ∀ m : M, IsUnit (β1 m) := by
    rintro ⟨m, a, ha, rfl⟩
    change IsUnit (β1 (algebraMap Abar B0 a))
    rw [hβA]
    apply IsUnit.map
    apply IsUnit.mk0
    intro h0
    apply nonZeroDivisors.coe_ne_zero (⟨a, ha⟩ : nonZeroDivisors Abar)
    exact hφ0 (h0.trans (map_zero _).symm)
  let g0 : T0 →+* C := IsLocalization.lift hβunit
  have hLC : ∀ ℓ : L, algebraMap L C ℓ = algebraMap ℂ C (φ ℓ) := fun _ => rfl
  have hg0A : (g0.comp (algebraMap L T0)).comp (algebraMap Abar L) =
      ((algebraMap ℂ C).comp φ).comp (algebraMap Abar L) := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply]
    rw [← hBA, IsLocalization.lift_eq, hβA, hφA]
  have hg0 : ∀ ℓ : L, g0 (algebraMap L T0 ℓ) = algebraMap L C ℓ := by
    intro ℓ
    have h := IsLocalization.ringHom_ext (nonZeroDivisors Abar) hg0A
    rw [hLC]
    exact congrArg (fun f => f ℓ) h
  let g1 : T0 →ₐ[L] C := { g0 with commutes' := hg0 }
  let fC : ℂ →ₐ[L] C := { algebraMap ℂ C with commutes' := fun _ => rfl }
  let Ψ : ℂ ⊗[L] T0 →ₐ[L] C := Algebra.TensorProduct.productLeftAlgHom fC g1
  have hleft : Function.LeftInverse Ψ Φbar := by
    intro x
    change ((Ψ : ℂ ⊗[L] T0 →+* C).comp (Φbar : C →+* ℂ ⊗[L] T0)) x = RingHom.id C x
    congr 1
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, RingHom.id_apply, RingHom.coe_coe]
      change Ψ (Φ (MvPolynomial.C c)) = _
      rw [MvPolynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply]
      simp only [Ψ, Algebra.TensorProduct.productLeftAlgHom, Algebra.TensorProduct.lift_tmul,
        map_one, mul_one]
      rfl
    · intro i
      simp only [RingHom.comp_apply, RingHom.id_apply, RingHom.coe_coe]
      change Ψ (Φ (MvPolynomial.X i)) = _
      simp only [Φ, MvPolynomial.aeval_X, Ψ, Algebra.TensorProduct.productLeftAlgHom,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      change g0 (algebraMap B0 T0 _) = _
      rw [IsLocalization.lift_eq]
      change Ideal.Quotient.mk J (specX ξ (ι (MvPolynomial.X (Fin.castAdd N i)))) = _
      simp [ι, specX, Fin.append_left]
  haveI : IsReduced C := isReduced_of_injective Φbar hleft.injective
  exact (Ideal.isRadical_iff_quotient_reduced J).mpr this

end GenericSpecialization

end CharZeroReduced

/-! ### Generic reducedness of the incidence fibres -/

section ApplyGeneric

theorem fibreSpecialize_eq_specX {q o : ℕ} (z : Point o) :
    (fibreSpecialize z : Poly (q + (o + 1)) →ₐ[ℂ] Poly q) = specX (Fin.cons 1 z) := by
  unfold fibreSpecialize specX
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun l => ?_) i
  · simp [Fin.append_left]
  · cases l using Fin.cases <;> simp [Fin.append_right]

/-- Second-block weight on `Fin (q + N)`. -/
def wX (q N : ℕ) : Fin (q + N) → ℕ := Fin.addCases (fun _ => 0) (fun _ => 1)

theorem specX_smul_of_homog {q N D : ℕ} {F : Poly (q + N)}
    (hF : F.IsWeightedHomogeneous (wX q N) D) (v : Fin N → ℂ) (c : ℂ) :
    specX (c • v) F = MvPolynomial.C c ^ D * specX v F := by
  have h := GenericFiber.aeval_scale_of_isWeightedHomogeneous hF
    (Fin.append (fun i => (MvPolynomial.X i : Poly q)) (fun l => MvPolynomial.C (v l)))
    (MvPolynomial.C c)
  rw [specX, specX, ← h]
  apply congrArg (fun f : Fin (q + N) → Poly q => MvPolynomial.aeval f F)
  funext s
  refine Fin.addCases (fun i => ?_) (fun l => ?_) s
  · simp [wX, Fin.append_left]
  · simp [wX, Fin.append_right]

theorem specX_mem_map_smul {q N : ℕ} (P : Ideal (Poly (q + N)))
    (hP : ∀ F ∈ P, ∀ D, MvPolynomial.weightedHomogeneousComponent (wX q N) D F ∈ P)
    (v : Fin N → ℂ) (c : ℂ) :
    P.map (specX (c • v)) ≤ P.map (specX v) := by
  classical
  rw [Ideal.map_le_iff_le_comap]
  intro F hF
  rw [Ideal.mem_comap]
  have hfin := MvPolynomial.weightedHomogeneousComponent_finsupp (w := wX q N) F
  have hsum := MvPolynomial.sum_weightedHomogeneousComponent (wX q N) F
  rw [finsum_eq_sum _ hfin] at hsum
  rw [← hsum, map_sum]
  apply Submodule.sum_mem
  intro D _
  rw [specX_smul_of_homog
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous D F) v c]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hP F hF D))

theorem map_specX_smul {q N : ℕ} (P : Ideal (Poly (q + N)))
    (hP : ∀ F ∈ P, ∀ D, MvPolynomial.weightedHomogeneousComponent (wX q N) D F ∈ P)
    (v : Fin N → ℂ) {c : ℂ} (hc : c ≠ 0) :
    P.map (specX (c • v)) = P.map (specX v) := by
  apply le_antisymm (specX_mem_map_smul P hP v c)
  have h := specX_mem_map_smul P hP (c • v) c⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

/-- Generic reducedness of the fibres of a triple set over an affine base (characteristic
zero): off countably many hypersurfaces of `V`, the scheme-theoretic fibre ideal is radical. -/
theorem tripleFibreIdeal_isRadical_very_general {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint (o + 1)))
    (V : AffineVariety o) (hV : V.ideal ≠ ⊤)
    (hTW : ∀ w ∈ T, w.2 ∈ (projectiveClosure V).points) :
    ∃ g : ℕ → Poly o, (∀ i, g i ∉ V.ideal) ∧ ∀ z : Point o,
      (∀ i, MvPolynomial.aeval z (g i) ≠ 0) → (tripleFibreIdeal T z).IsRadical := by
  classical
  set W := projectiveClosure V with hWdef
  set P := MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) with hPdef
  have hPrad : P.IsRadical := AffineVariety.vanishingIdeal_isRadical _
  have hPhom : ∀ F ∈ P, ∀ D,
      MvPolynomial.weightedHomogeneousComponent (wX (n + m) (o + 1)) D F ∈ P :=
    fun F hF D => tripleIx_mem_whc_z T hF D
  -- a countable field of definition
  obtain ⟨G, hG⟩ : P.FG := IsNoetherian.noetherian P
  let S0 : Set ℂ := ⋃ g ∈ G, (g.coeffs : Set ℂ)
  have hS0 : S0.Countable :=
    G.countable_toSet.biUnion (fun g _ => g.coeffs.countable_toSet)
  let k := Subfield.closure S0
  haveI hkc : Countable k := by
    have h1 := Subfield.cardinalMk_closure_le_max S0
    have h2 : Cardinal.mk S0 ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hS0.to_subtype
    exact Cardinal.mk_le_aleph0_iff.mp (h1.trans (max_le h2 le_rfl))
  set ι := kIncl k (n + m + (o + 1)) with hι
  have hGk : ∀ g ∈ G, ∃ g0, ι g0 = g := by
    intro g hg
    have : g ∈ Set.range (MvPolynomial.map k.subtype) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro a ha
      exact ⟨⟨a, Subfield.subset_closure (Set.mem_biUnion hg ha)⟩, rfl⟩
    exact this
  have hgen : P ≤ Ideal.span (ι '' (P.comap ι)) := by
    calc P = Ideal.span (G : Set (Poly (n + m + (o + 1)))) := hG.symm
      _ ≤ _ := by
        apply Ideal.span_mono
        intro g hg
        obtain ⟨g0, hg0⟩ := hGk g hg
        refine ⟨g0, ?_, hg0⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, hg0, ← hG]
        exact Ideal.subset_span hg
  -- the countable family
  let ι' := kIncl k (o + 1)
  obtain ⟨enum, henum⟩ := exists_surjective_nat (MvPolynomial (Fin (o + 1)) k)
  let good : MvPolynomial (Fin (o + 1)) k → Prop := fun f =>
    (∃ D, (ι' f).IsHomogeneous D) ∧ ι' f ∉ W.ideal
  let g : ℕ → Poly o := fun i => if good (enum i) then
    MvPolynomial.aeval (Fin.cons (1 : Poly o) MvPolynomial.X) (ι' (enum i)) else 1
  refine ⟨g, ?_, ?_⟩
  · intro i
    by_cases hgi : good (enum i)
    · simp only [g, if_pos hgi]
      obtain ⟨⟨D, hD⟩, hW⟩ := hgi
      rwa [← projectiveClosure_homogeneous_mem V _ hD]
    · simp only [g, if_neg hgi]
      intro h1
      exact hV ((Ideal.eq_top_iff_one _).mpr h1)
  intro z hz
  have hdehom : ∀ F : Poly (o + 1), MvPolynomial.aeval z
      (MvPolynomial.aeval (Fin.cons (1 : Poly o) MvPolynomial.X) F) =
        MvPolynomial.aeval (Fin.cons 1 z : Point (o + 1)) F := by
    intro F
    rw [GenericFiber.eval_aeval]
    apply congrArg (fun f : Fin (o + 1) → ℂ => MvPolynomial.aeval f F)
    funext s
    cases s using Fin.cases <;> simp
  have hss : ∀ f : MvPolynomial (Fin (o + 1)) k, (∃ D, (ι' f).IsHomogeneous D) →
      MvPolynomial.aeval (Fin.cons 1 z : Point (o + 1)) (ι' f) = 0 → ι' f ∈ W.ideal := by
    intro f hhom hzero
    by_contra hW
    obtain ⟨i, rfl⟩ := henum f
    have h := hz i
    simp only [g, if_pos (show good (enum i) from ⟨hhom, hW⟩)] at h
    exact h (by rw [hdehom]; exact hzero)
  -- choose the scaling `c`
  let pf : MvPolynomial (Fin (o + 1)) k → Polynomial ℂ := fun f =>
    ∑ u ∈ Finset.range (f.totalDegree + 1), Polynomial.C (MvPolynomial.aeval
      (Fin.cons 1 z : Point (o + 1)) (ι' (MvPolynomial.homogeneousComponent u f))) *
        Polynomial.X ^ u
  let bad : Set ℂ := {0} ∪ ⋃ f : MvPolynomial (Fin (o + 1)) k,
    {c | pf f ≠ 0 ∧ (pf f).IsRoot c}
  have hbad : bad.Countable := by
    apply (Set.countable_singleton 0).union
    apply Set.countable_iUnion
    intro f
    by_cases hf : pf f = 0
    · simp [hf]
    · exact (Polynomial.finite_setOf_isRoot hf).countable.mono (fun c hc => hc.2)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ∉ bad := by
    by_contra hall
    push_neg at hall
    exact not_countable_complex (hbad.mono (fun c _ => hall c))
  have hc0 : c ≠ 0 := fun h => hc (Or.inl h)
  have hcroot : ∀ f, pf f ≠ 0 → ¬ (pf f).IsRoot c :=
    fun f hf hr => hc (Or.inr (Set.mem_iUnion.mpr ⟨f, hf, hr⟩))
  have heval : ∀ f : MvPolynomial (Fin (o + 1)) k,
      MvPolynomial.eval₂ k.subtype (c • (Fin.cons 1 z : Point (o + 1))) f = (pf f).eval c := by
    intro f
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent f]
    rw [MvPolynomial.eval₂_sum, Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      ← MvPolynomial.eval_map]
    have hh := ((MvPolynomial.homogeneousComponent_isHomogeneous u f).map k.subtype)
    have hs := GenericFiber.aeval_scale_of_isWeightedHomogeneous hh
      (Fin.cons 1 z : Point (o + 1)) c
    have e1 : MvPolynomial.eval (c • (Fin.cons 1 z : Point (o + 1)))
        (MvPolynomial.map k.subtype (MvPolynomial.homogeneousComponent u f)) =
        MvPolynomial.aeval (fun s => c ^ (1 : Fin (o + 1) → ℕ) s *
          (Fin.cons 1 z : Point (o + 1)) s)
          (MvPolynomial.map k.subtype (MvPolynomial.homogeneousComponent u f)) := by
      show MvPolynomial.aeval _ _ = _
      apply congrArg (fun x : Fin (o + 1) → ℂ => MvPolynomial.aeval x
        (MvPolynomial.map k.subtype (MvPolynomial.homogeneousComponent u f)))
      funext s
      simp
    rw [e1, hs, mul_comm]
  have hstar : ∀ f : MvPolynomial (Fin (o + 1)) k,
      MvPolynomial.eval₂ k.subtype (c • (Fin.cons 1 z : Point (o + 1))) f = 0 →
        ι (MvPolynomial.rename (Fin.natAdd (n + m)) f) ∈ P := by
    intro f hf
    rw [heval] at hf
    have hpf : pf f = 0 := by
      by_contra h
      exact hcroot f h hf
    have hcomp : ∀ u, MvPolynomial.aeval (Fin.cons 1 z : Point (o + 1))
        (ι' (MvPolynomial.homogeneousComponent u f)) = 0 := by
      intro u
      by_cases hu : u < f.totalDegree + 1
      · have h := congrArg (fun p : Polynomial ℂ => p.coeff u) hpf
        simp only [pf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
          Polynomial.coeff_zero] at h
        rw [Finset.sum_eq_single u (fun b _ hb => if_neg (Ne.symm hb))
          (fun hu' => absurd (Finset.mem_range.mpr hu) hu'), if_pos rfl] at h
        exact h
      · rw [MvPolynomial.homogeneousComponent_eq_zero u f (by omega), map_zero, map_zero]
    have hW : ∀ u, ι' (MvPolynomial.homogeneousComponent u f) ∈ W.ideal := fun u =>
      hss _ ⟨u, (MvPolynomial.homogeneousComponent_isHomogeneous u f).map _⟩ (hcomp u)
    have hmap : ι (MvPolynomial.rename (Fin.natAdd (n + m)) f) =
        zInclusion n m (o + 1) (ι' f) := by
      simp only [zInclusion, ι, ι', kIncl]
      rw [MvPolynomial.map_rename]
      rfl
    rw [hmap, ← MvPolynomial.sum_homogeneousComponent f, map_sum, map_sum]
    apply Submodule.sum_mem
    intro u _
    exact zInclusion_mem_tripleIdeal T W hTW _ (hW u)
  have hrad := isRadical_specX k P hPrad hgen (c • (Fin.cons 1 z : Point (o + 1))) hstar
  unfold tripleFibreIdeal
  rw [fibreSpecialize_eq_specX, ← map_specX_smul P hPhom _ hc0]
  exact hrad

end ApplyGeneric

end
end DistinctDistances.TrackB.PointIntegral
