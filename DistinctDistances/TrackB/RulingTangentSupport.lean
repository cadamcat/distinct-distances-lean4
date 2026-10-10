import DistinctDistances.TrackB.TangentQuotientSupport
import DistinctDistances.TrackD.Requests
import DistinctDistances.TrackB.BFlatAux

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

set_option linter.unusedSimpArgs false

/-- a constant affine coordinate has zero tangent derivative. -/
theorem normalized_coordinate_tangent {n : ℕ} (X : AffineVariety n)
    (a : Fin n) (c : ℂ) (hnorm : ∀ x ∈ X.points, x a = c)
    (x : Point n) (hx : x ∈ X.points) (u : Point n) (hu : u ∈ X.tangentSpace x) :
    u a = 0 := by
  let f : Poly n := MvPolynomial.X a - MvPolynomial.C c
  have hf : f ∈ X.ideal := by
    rw [← X.vanishingIdeal_points]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro y hy
    simp only [f, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply, hnorm y hy, sub_self]
  have hu_ker : u ∈ LinearMap.ker (differential f x) := by
    have htan : X.tangentSpace x ≤ LinearMap.ker (differential f x) :=
      iInf_le (fun (g : X.ideal) => LinearMap.ker (differential g.val x)) ⟨f, hf⟩
    exact htan hu
  have hdiff : differential f x u = 0 := hu_ker
  rw [bflat_differential_X_sub_C_apply] at hdiff
  exact hdiff

/-- the quotient rule with denominator one is the polynomial differential. -/
theorem rationalDifferential_one {n m : ℕ} (F : Fin m → Poly n) (x : Point n) :
    TrackD.rationalDifferential F 1 x = LinearMap.pi (fun i => differential (F i) x) := by
  have hdiff1 : differential (1 : Poly n) x = 0 := by
    have hC1 : (1 : Poly n) = MvPolynomial.C 1 := (map_one MvPolynomial.C).symm
    rw [hC1]
    exact bflat_differential_C 1 x
  apply LinearMap.ext
  intro u
  ext i
  simp only [TrackD.rationalDifferential, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_one, inv_one, one_smul, hdiff1,
    LinearMap.zero_apply, smul_zero, sub_zero]

/-- ruling dominance on H != 0 pulls back every nonzero base polynomial. -/
theorem ruling_base_polynomial_not_mem {e j N : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (R : IsRulingIncidence C V Γ H a j N)
    (g : Poly (skewDim e)) (hg : g ∉ V.ideal) :
    rulingOpenPolynomial g ∉ Γ.ideal := by
  intro hΓ
  have hvan : ∀ w ∈ Γ.points, MvPolynomial.aeval w (rulingOpenPolynomial g) = 0 := by
    rw [← Γ.vanishingIdeal_points] at hΓ
    exact fun w hw => MvPolynomial.mem_vanishingIdeal_iff.mp hΓ w hw
  have hvan_first : ∀ w ∈ Γ.points, MvPolynomial.aeval (firstPoint w) g = 0 := by
    intro w hw
    have h := hvan w hw
    rw [eval_rulingOpenPolynomial] at h
    exact h
  have hvan_work : ∀ z ∈ workingPoints V H, MvPolynomial.aeval z g = 0 := by
    intro z hz
    obtain ⟨v, hv⟩ := R.dominant z hz
    have hw : joinPoints z v ∈ Γ.points := hv
    have hfirst : firstPoint (joinPoints z v) = z := by
      ext i; simp [firstPoint, joinPoints]
    have h := hvan_first (joinPoints z v) hw
    rwa [hfirst] at h
  have hHg_van : ∀ z ∈ V.points, MvPolynomial.aeval z (H * g) = 0 := by
    intro z hz
    by_cases hHz : MvPolynomial.aeval z H = 0
    · rw [map_mul, hHz, zero_mul]
    · have hwork : z ∈ workingPoints V H := ⟨hz, hHz⟩
      rw [map_mul, hvan_work z hwork, mul_zero]
  have hHg_ideal : H * g ∈ V.ideal := by
    rw [← V.vanishingIdeal_points]
    exact MvPolynomial.mem_vanishingIdeal_iff.mpr hHg_van
  have hprime : V.ideal.IsPrime := R.variety_irreducible
  cases hprime.mem_or_mem hHg_ideal with
  | inl hH => exact R.nonzero_section hH
  | inr hg_mem => exact hg hg_mem

/-- normalization identifies directions in equal graph parameters. -/
theorem normalized_graph_parameter_direction {e : ℕ} (C : SkewCoordinates e)
    (a : Fin e) (z z' : Point (skewDim e)) (v v' : Point e)
    (hv : v ≠ 0) (hv' : v' ≠ 0) (hva : v a = 1) (hva' : v' a = 1)
    (hp : graphParameter C z v hv = graphParameter C z' v' hv') :
    v = v' := by
  unfold graphParameter at hp
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hp
  have hfirst : firstPoint (graphVector C z v) = v := by
    ext i
    simp [firstPoint, graphVector, joinPoints]
  have hfirst' : firstPoint (graphVector C z' v') = v' := by
    ext i
    simp [firstPoint, graphVector, joinPoints]
  have hsmul : firstPoint (c • graphVector C z' v') =
      c • firstPoint (graphVector C z' v') := by
    ext i
    simp [firstPoint, Pi.smul_apply]
  have hv_eq : c • v' = v := by
    have h := congrArg firstPoint hc
    rw [hsmul, hfirst', hfirst] at h
    exact h
  have hc1 : c = 1 := by
    have h := congrFun hv_eq a
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [hva, hva'] at h
    simpa using h
  subst hc1
  simpa using hv_eq.symm

/-- remove representative units from the actual evaluation equation. -/
theorem evaluationFlat_graphParameter_iff {e : ℕ} (C : SkewCoordinates e)
    (z z0 : Point (skewDim e)) (v : Point e) (hv : v ≠ 0) :
    z0 ∈ evaluationFlat C (graphParameter C z v hv) ↔
      (C.decode z0).val v = (C.decode z).val v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (graphVector C z v)
    (graphVector_ne_zero C z v hv)
  have hfirst : firstPoint (graphParameter C z v hv).rep = (a : ℂ) • v := by
    rw [graphParameter, ← ha, Units.smul_def]
    funext i
    simp [firstPoint, graphVector, joinPoints, Pi.smul_apply]
  have hsecond : secondPoint (graphParameter C z v hv).rep =
      (a : ℂ) • pointOfCovector ((C.decode z).val v) := by
    rw [graphParameter, ← ha, Units.smul_def]
    funext i
    simp only [secondPoint, graphVector, joinPoints, Pi.smul_apply, smul_eq_mul,
      Fin.addCases_right]
  change (C.decode z0).val (firstPoint (graphParameter C z v hv).rep) =
    covectorOfPoint (secondPoint (graphParameter C z v hv).rep) ↔ _
  rw [hfirst, hsecond]
  have hcov : covectorOfPoint ((a : ℂ) • pointOfCovector ((C.decode z).val v)) =
      (a : ℂ) • (C.decode z).val v := by
    rw [← pointOfCovector_smul, covector_point_inverse]
  have hlin : (C.decode z0).val ((a : ℂ) • v) = (a : ℂ) • (C.decode z0).val v := by
    simp
  rw [hcov, hlin]
  constructor
  · intro h
    have h' := congrArg (a⁻¹ • ·) h
    simpa [Units.smul_def, smul_smul] using h'
  · intro h
    rw [h]

/-- the entire affine evaluation fiber with H != 0 has the same
normalized direction in the actual ruling incidence. -/
theorem ruling_normalized_flat_fiber {e j N : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (R : IsRulingIncidence C V Γ H a j N)
    (z : Point (skewDim e)) (v : Point e) (hw : joinPoints z v ∈ rulingPoints Γ H)
    (hv : v ≠ 0) (z' : Point (skewDim e))
    (hflat : z' ∈ evaluationFlat C (graphParameter C z v hv))
    (hH : MvPolynomial.aeval z' H ≠ 0) :
    joinPoints z' v ∈ rulingPoints Γ H := by
  have hz'V : z' ∈ V.points := by
    have hsub := R.actual_flats z v hw hv
    exact hsub hflat
  have hwork' : z' ∈ workingPoints V H := ⟨hz'V, hH⟩
  let p := graphParameter C z v hv
  have hp_mem : p ∈ parameterImage C Γ H := ⟨z, v, hw, hv, rfl⟩
  have hfiber := (R.full_parameter_fibers p hp_mem z' hwork').mp hflat
  obtain ⟨v', hw', hv', hp'⟩ := hfiber
  have hna : v a = 1 := by
    have h := R.normalized (joinPoints z v) hw.1
    have hsec : secondPoint (joinPoints z v) = v := by
      ext i; simp [secondPoint, joinPoints]
    rwa [hsec] at h
  have hna' : v' a = 1 := by
    have h := R.normalized (joinPoints z' v') hw'.1
    have hsec : secondPoint (joinPoints z' v') = v' := by
      ext i; simp [secondPoint, joinPoints]
    rwa [hsec] at h
  have hvv' : v = v' := by
    apply normalized_graph_parameter_direction C a z z' v v' hv hv' hna hna'
    exact hp'.symm
  subst hvv'
  exact hw'

/-- whole affine flats in V give all evaluation-kernel tangent
vectors, directly from lines, without a source tangent dimension argument. -/
theorem ruling_evaluation_kernel_tangent {e j N : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (R : IsRulingIncidence C V Γ H a j N)
    (z : Point (skewDim e)) (v : Point e) (hw : joinPoints z v ∈ rulingPoints Γ H)
    (hv : v ≠ 0) (dz : Point (skewDim e)) (hker : (C.decode dz).val v = 0) :
    dz ∈ V.tangentSpace z := by
  apply line_direction_mem_tangent V z dz
  intro t
  have hsub := R.actual_flats z v hw hv
  apply hsub
  rw [evaluationFlat_graphParameter_iff]
  have hlin : (C.decode (z + t • dz)).val v = (C.decode z).val v + t • (C.decode dz).val v := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_smul]
  rw [hlin, hker, smul_zero, add_zero]

/-- Helper: the quotient section differs from its representative only in the span. -/
theorem bflat_sec_sub_mem {e : ℕ} (v : Point e) (x : Point e) :
    directionQuotientSection v ((Submodule.span ℂ {v}).mkQ x) - x ∈
      Submodule.span ℂ {v} := by
  let S := Submodule.span ℂ {v}
  have hq : S.mkQ (directionQuotientSection v (S.mkQ x) - x) = 0 := by
    rw [map_sub]
    have h := congrArg (fun L : Point e ⧸ S →ₗ[ℂ] Point e ⧸ S => L (S.mkQ x))
      (directionQuotientSection_rightInverse v)
    apply sub_eq_zero.mpr
    simpa only [S, LinearMap.comp_apply, LinearMap.id_apply] using h
  have hk : directionQuotientSection v (S.mkQ x) - x ∈ LinearMap.ker S.mkQ :=
    LinearMap.mem_ker.mpr hq
  simpa only [Submodule.ker_mkQ] using hk

/-- Helper: a kernel alternating form vanishes on the spanned direction (left). -/
theorem bflat_ker_vanish_left {e : ℕ} (D : LinearMap.BilinForm ℂ (Point e))
    (v : Point e) (h0 : D v = 0) (s : Point e)
    (hs : s ∈ Submodule.span ℂ {v}) (y : Point e) : D s y = 0 := by
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hs
  simp only [map_smul, LinearMap.smul_apply, h0, LinearMap.zero_apply, smul_zero]

/-- Helper: a kernel alternating form vanishes on the spanned direction (right). -/
theorem bflat_ker_vanish_right {e : ℕ} (D : LinearMap.BilinForm ℂ (Point e))
    (hD : D.IsAlt) (v : Point e) (h0 : D v = 0) (y s : Point e)
    (hs : s ∈ Submodule.span ℂ {v}) : D y s = 0 := by
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hs
  have f1 : D (t • v) y = 0 := by
    simp only [map_smul, LinearMap.smul_apply, h0, LinearMap.zero_apply, smul_zero]
  have hneg : D y (t • v) = - D (t • v) y := (hD.neg_eq _ _).symm
  rw [hneg, f1, neg_zero]

/-- Helper: shifting both arguments by span elements does not change the value. -/
theorem bflat_bilin_shift {e : ℕ} (D : LinearMap.BilinForm ℂ (Point e))
    (hD : D.IsAlt) (v : Point e) (h0 : D v = 0)
    (x s1 w s2 : Point e) (hs1 : s1 ∈ Submodule.span ℂ {v})
    (hs2 : s2 ∈ Submodule.span ℂ {v}) :
    D (x + s1) (w + s2) = D x w := by
  have r1 : D (x + s1) = D x + D s1 := map_add _ _ _
  have r2a : (D x) (w + s2) = D x w + D x s2 := map_add _ _ _
  have r2b : (D s1) (w + s2) = D s1 w + D s1 s2 := map_add _ _ _
  have z1 : D x s2 = 0 := bflat_ker_vanish_right _ hD _ h0 _ _ hs2
  have z2 : D s1 w = 0 := bflat_ker_vanish_left _ _ h0 _ hs1 _
  have z3 : D s1 s2 = 0 := bflat_ker_vanish_left _ _ h0 _ hs1 _
  calc D (x + s1) (w + s2) = (D x + D s1) (w + s2) := by rw [r1]
    _ = D x (w + s2) + D s1 (w + s2) := LinearMap.add_apply _ _ _
    _ = (D x w + D x s2) + (D s1 w + D s1 s2) := by rw [r2a, r2b]
    _ = D x w := by rw [z1, z2, z3]; simp

/-- Helper: restriction of a kernel form along the quotient section. -/
def bflat_ker_restrict {e : ℕ} (v : Point e) :
    LinearMap.ker (alternatingEvaluation (U := Point e) v) →ₗ[ℂ]
      alternatingForms (U := Point e ⧸ Submodule.span ℂ {v}) where
  toFun k :=
    ⟨k.1.1.comp (directionQuotientSection v) (directionQuotientSection v), fun q => by
      rw [LinearMap.BilinForm.comp_apply]
      exact k.1.2 _⟩
  map_add' a b := by
    apply Subtype.ext
    show (a.1.1 + b.1.1).comp (directionQuotientSection v)
        (directionQuotientSection v) =
      (a.1.1.comp (directionQuotientSection v) (directionQuotientSection v)) +
        (b.1.1.comp (directionQuotientSection v) (directionQuotientSection v))
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.BilinForm.comp_apply, LinearMap.add_apply]
  map_smul' a b := by
    apply Subtype.ext
    show (a • b.1.1).comp (directionQuotientSection v)
        (directionQuotientSection v) =
      a • (b.1.1.comp (directionQuotientSection v) (directionQuotientSection v))
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.BilinForm.comp_apply, LinearMap.smul_apply, smul_eq_mul]

/-- Helper: applying the restriction is evaluation at section lifts. -/
theorem bflat_ker_restrict_apply {e : ℕ} (v : Point e)
    (k : LinearMap.ker (alternatingEvaluation (U := Point e) v))
    (a b : Point e ⧸ Submodule.span ℂ {v}) :
    (bflat_ker_restrict v k).1 a b =
      k.1.1 (directionQuotientSection v a) (directionQuotientSection v b) := rfl

/-- Helper: the restriction agrees with the kernel form on representatives. -/
theorem bflat_restrict_agree {e : ℕ} (v : Point e)
    (k : LinearMap.ker (alternatingEvaluation (U := Point e) v))
    (x w : Point e) :
    k.1.1 x w = (bflat_ker_restrict v k).1
      ((Submodule.span ℂ {v}).mkQ x) ((Submodule.span ℂ {v}).mkQ w) := by
  rw [bflat_ker_restrict_apply]
  have hm1 := bflat_sec_sub_mem v x
  have hm2 := bflat_sec_sub_mem v w
  have h0 : k.1.1 v = 0 := LinearMap.mem_ker.mp k.2
  have e1 : directionQuotientSection v ((Submodule.span ℂ {v}).mkQ x) =
      x + (directionQuotientSection v ((Submodule.span ℂ {v}).mkQ x) - x) := by abel
  have e2 : directionQuotientSection v ((Submodule.span ℂ {v}).mkQ w) =
      w + (directionQuotientSection v ((Submodule.span ℂ {v}).mkQ w) - w) := by abel
  rw [e1, e2]
  exact (bflat_bilin_shift _ k.1.2 _ h0 _ _ _ _ hm1 hm2).symm

/-- Helper: every quotient alternating form is a restriction of a kernel form. -/
theorem bflat_restrict_surjective {e : ℕ} (v : Point e) :
    Function.Surjective (bflat_ker_restrict (e := e) v) := by
  intro Q0
  have hmv : (Submodule.span ℂ {v}).mkQ v = 0 := by
    have hmem : (Submodule.span ℂ {v}).mkQ v ∈
        Submodule.map (Submodule.span ℂ {v}).mkQ (Submodule.span ℂ {v}) :=
      Submodule.mem_map.mpr ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
    rw [Submodule.mkQ_map_self] at hmem
    simpa using hmem
  have halt : (Q0.1.comp (Submodule.span ℂ {v}).mkQ
      (Submodule.span ℂ {v}).mkQ).IsAlt := by
    intro q
    rw [LinearMap.BilinForm.comp_apply]
    exact Q0.2 _
  have hker0 : alternatingEvaluation (U := Point e) v
      ⟨Q0.1.comp (Submodule.span ℂ {v}).mkQ (Submodule.span ℂ {v}).mkQ, halt⟩ = 0 := by
    apply LinearMap.ext
    intro y
    show (Q0.1.comp (Submodule.span ℂ {v}).mkQ (Submodule.span ℂ {v}).mkQ) v y = 0
    rw [LinearMap.BilinForm.comp_apply, hmv]
    simp
  refine ⟨⟨⟨Q0.1.comp (Submodule.span ℂ {v}).mkQ (Submodule.span ℂ {v}).mkQ, halt⟩,
    hker0⟩, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro q1
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q1
  apply LinearMap.ext
  intro q2
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ q2
  have hsec : ∀ q : Point e ⧸ Submodule.span ℂ {v},
      (Submodule.span ℂ {v}).mkQ (directionQuotientSection v q) = q := by
    intro q
    have h := congrArg (fun L : (Point e ⧸ Submodule.span ℂ {v}) →ₗ[ℂ]
        Point e ⧸ Submodule.span ℂ {v} => L q)
      (directionQuotientSection_rightInverse v)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  show ((Q0.1.comp (Submodule.span ℂ {v}).mkQ (Submodule.span ℂ {v}).mkQ).comp
    (directionQuotientSection v) (directionQuotientSection v)) _ _ = Q0.1 _ _
  simp only [LinearMap.BilinForm.comp_apply, hsec]

/-- finite linear coordinates on the actual evaluation kernel,
with a surjective descended alternating-form map on the direction quotient. -/
theorem alternating_kernel_quotient_coordinates {e : ℕ} (v : Point e) (hv : v ≠ 0) :
    ∃ ψ : Point (flatDim e) ≃ₗ[ℂ] LinearMap.ker (alternatingEvaluation v),
      ∃ φ : Point (flatDim e) →ₗ[ℂ] alternatingForms (U := Point e ⧸ Submodule.span ℂ {v}),
        Function.Surjective φ ∧ ∀ t : Point (flatDim e), ∀ x w : Point e,
          (ψ t).val.val x w = (φ t).val ((Submodule.span ℂ {v}).mkQ x)
            ((Submodule.span ℂ {v}).mkQ w) := by
  have hPe : Module.finrank ℂ (Point e) = e := Module.finrank_fin_fun ℂ
  have hker : Module.finrank ℂ
      ↥(LinearMap.ker (alternatingEvaluation (U := Point e) v)) = flatDim e := by
    rw [alternatingEvaluation_kernel_finrank v hv, hPe]
    rfl
  have hdom : Module.finrank ℂ (Point (flatDim e)) = flatDim e :=
    Module.finrank_fin_fun ℂ
  letI : AddCommGroup ↥(alternatingForms (U := Point e)) := inferInstance
  letI : AddCommGroup ↥(LinearMap.ker (alternatingEvaluation (U := Point e) v)) :=
    inferInstance
  let ψ : Point (flatDim e) ≃ₗ[ℂ]
      ↥(LinearMap.ker (alternatingEvaluation (U := Point e) v)) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hdom, hker])
  let φ : Point (flatDim e) →ₗ[ℂ]
      alternatingForms (U := Point e ⧸ Submodule.span ℂ {v}) :=
    (bflat_ker_restrict v).comp ψ.toLinearMap
  refine ⟨ψ, φ, ?_, ?_⟩
  · intro Q
    obtain ⟨k, hk⟩ := bflat_restrict_surjective v Q
    obtain ⟨t, rfl⟩ := ψ.surjective k
    exact ⟨t, hk⟩
  · intro t x w
    exact bflat_restrict_agree v (ψ t) x w

end
end DistinctDistances.TrackB
