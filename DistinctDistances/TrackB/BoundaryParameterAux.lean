import DistinctDistances.TrackB.GenericPointFiberSupport

/-!
Boundary parameters for B11 (`conc:deg-fiber-degree`, concentration.tex:662–688).

Chevalley's request puts `Λ̄ ∩ {G ≠ 0}` in the actual parameter image. Over the boundary
`Λ̄ ∩ {G = 0}` every flat through `z` is parametrized, chart by chart, by a polynomial map in the
normalized boundary representative and `flatDim e` free coordinates. Boundary primes lose two
dimensions, so for `j = 0` the boundary flats miss a general point of `V`, and for `j = 1` only
finitely many boundary flats pass through a general point.
-/

namespace DistinctDistances.TrackB.B11

noncomputable section
open scoped BigOperators
open LinearMap (BilinForm)
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Charts of the evaluation flats -/

section Chart

variable {e : ℕ} (C : SkewCoordinates e) (i : Fin e)

theorem wedge_apply (y v w : Point e) :
    ((C.decode (coordinateWedge C i y)).val v) w =
      v i * covectorOfPoint y w - covectorOfPoint y v * w i := by
  have h : C.decode (coordinateWedge C i y) = coordinateWedgeForm i
      (covectorOfPoint y) := by
    simp [coordinateWedge, pointCovectorLinear]
  have hval := congrArg Subtype.val h
  have happly := congrArg (fun B : BilinForm ℂ (Point e) => B v w) hval
  simpa [coordinateWedgeForm, BilinForm.linMulLin_apply,
    LinearMap.proj_apply] using happly

/-- Forms with `e_i` in their kernel. -/
def chartKernel : Submodule ℂ (Point (skewDim e)) :=
  LinearMap.ker ((alternatingEvaluation (Pi.single i (1 : ℂ) : Point e)).comp
    C.decode.toLinearMap)

theorem chartKernel_finrank : Module.finrank ℂ (chartKernel C i) = flatDim e := by
  have hv : (Pi.single i (1 : ℂ) : Point e) ≠ 0 := by
    intro h
    have := congrFun h i
    simp at this
  have hEq := (C.decode.ofSubmodule' (LinearMap.ker
    (alternatingEvaluation (Pi.single i (1 : ℂ) : Point e)))).finrank_eq
  change Module.finrank ℂ (chartKernel C i) =
    Module.finrank ℂ (LinearMap.ker (alternatingEvaluation (Pi.single i (1 : ℂ) : Point e)))
    at hEq
  rw [hEq, alternatingEvaluation_kernel_finrank _ hv, Module.finrank_fin_fun]
  rfl

/-- The chart map: `z'` corrected so that its form sends `first x` to `second x`. -/
def zOf (x : Point (e + e)) (z' : Point (skewDim e)) : Point (skewDim e) :=
  z' + coordinateWedge C i (secondPoint x) -
    coordinateWedge C i (pointOfCovector ((C.decode z').val (firstPoint x)))

theorem chart_repr (x : Point (e + e)) (hxi : firstPoint x i = 1) (z : Point (skewDim e))
    (hz : (C.decode z).val (firstPoint x) = covectorOfPoint (secondPoint x)) :
    ∃ z' ∈ chartKernel C i, z = zOf C i x z' := by
  let ε : Point e := Pi.single i 1
  let z' := z - coordinateWedge C i (pointOfCovector ((C.decode z).val ε))
  have hεi : ε i = 1 := by simp [ε]
  have hDεε : (C.decode z).val ε ε = 0 := (C.decode z).2.self_eq_zero ε
  refine ⟨z', ?_, ?_⟩
  · change (C.decode z').val ε = 0
    apply LinearMap.ext
    intro w
    simp only [z', map_sub, Submodule.coe_sub, LinearMap.sub_apply, wedge_apply,
      covector_point_inverse, hεi, hDεε, LinearMap.zero_apply]
    ring
  · apply C.decode.injective
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    have hz' : ∀ q, covectorOfPoint (secondPoint x) q = (C.decode z).val (firstPoint x) q :=
      fun q => by rw [hz]
    simp only [zOf, z', map_sub, map_add, Submodule.coe_sub, Submodule.coe_add,
      LinearMap.sub_apply, LinearMap.add_apply, wedge_apply, covector_point_inverse, hz', hxi,
      hεi, hDεε]
    ring

/-- An injective parametrization of the chart kernel. -/
theorem chartKernel_parametrization :
    ∃ ψ : Point (flatDim e) →ₗ[ℂ] Point (skewDim e), Function.Injective ψ ∧
      ∀ z' ∈ chartKernel C i, ∃ t, z' = ψ t := by
  let b : Module.Basis (Fin (flatDim e)) ℂ (chartKernel C i) :=
    (Module.finBasis ℂ (chartKernel C i)).reindex (finCongr (chartKernel_finrank C i))
  let ψ : Point (flatDim e) →ₗ[ℂ] Point (skewDim e) :=
    (chartKernel C i).subtype.comp b.equivFun.symm.toLinearMap
  refine ⟨ψ, Subtype.val_injective.comp b.equivFun.symm.injective, ?_⟩
  intro z' hz'
  refine ⟨b.equivFun ⟨z', hz'⟩, ?_⟩
  simp [ψ]

/-! Polynomial coordinates of the chart map. -/

def xPart (n f : ℕ) : Point (n + f) →ₗ[ℂ] Point n :=
  LinearMap.pi (fun k => LinearMap.proj (Fin.castAdd f k))

def tPart (n f : ℕ) : Point (n + f) →ₗ[ℂ] Point f :=
  LinearMap.pi (fun k => LinearMap.proj (Fin.natAdd n k))

theorem xPart_append {n f : ℕ} (x : Point n) (t : Point f) :
    xPart n f (Fin.append x t) = x := by
  funext k
  simp [xPart]

theorem tPart_append {n f : ℕ} (x : Point n) (t : Point f) :
    tPart n f (Fin.append x t) = t := by
  funext k
  simp [tPart]

variable (ψ : Point (flatDim e) →ₗ[ℂ] Point (skewDim e))

/-- `u ↦ wedge(D_{z'} u)` is linear. -/
def wedgeEval (z' : Point (skewDim e)) : Point e →ₗ[ℂ] Point (skewDim e) :=
  (coordinateWedge C i).comp ((covectorPointLinear e).comp (C.decode z').val)

def chartPoly (m : Fin (skewDim e)) : Poly ((e + e) + flatDim e) :=
  dualPoly ((LinearMap.proj m).comp (ψ.comp (tPart (e + e) (flatDim e)))) +
    dualPoly ((LinearMap.proj m).comp ((coordinateWedge C i).comp
      ((secondBlockLinear e).comp (xPart (e + e) (flatDim e))))) -
    ∑ l : Fin e, MvPolynomial.X (Fin.castAdd (flatDim e) (Fin.castAdd e l)) *
      dualPoly ((LinearMap.proj m).comp ((coordinateWedge C i).comp
        ((covectorPointLinear e).comp
          ((alternatingEvaluation (Pi.single l (1 : ℂ) : Point e)).comp
            (C.decode.toLinearMap.comp (ψ.comp (tPart (e + e) (flatDim e))))))))

theorem eval_chartPoly (x : Point (e + e)) (t : Point (flatDim e)) (m : Fin (skewDim e)) :
    MvPolynomial.aeval (Fin.append x t) (chartPoly C i ψ m) = zOf C i x (ψ t) m := by
  have hu : firstPoint x = ∑ l : Fin e, firstPoint x l • (Pi.single l (1 : ℂ) : Point e) := by
    simpa using ((Pi.basisFun ℂ (Fin e)).sum_repr (firstPoint x)).symm
  have hlin : coordinateWedge C i (pointOfCovector ((C.decode (ψ t)).val (firstPoint x))) =
      ∑ l : Fin e, firstPoint x l • wedgeEval C i (ψ t) (Pi.single l 1) := by
    change wedgeEval C i (ψ t) (firstPoint x) = _
    conv_lhs => rw [hu]
    rw [map_sum]
    simp only [map_smul]
  simp only [chartPoly, map_sub, map_add, map_sum, map_mul, aeval_dualPoly, MvPolynomial.aeval_X,
    LinearMap.comp_apply, xPart_append, tPart_append, LinearMap.proj_apply,
    secondBlockLinear_apply]
  rw [zOf, Pi.sub_apply, Pi.add_apply, hlin, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  simp only [Pi.smul_apply, smul_eq_mul, wedgeEval, LinearMap.comp_apply]
  rw [Fin.append_left]
  rfl

end Chart

/-! ### Boundary primes lose two dimensions -/

theorem prime_dim_lt {n : ℕ} {I J : Ideal (Poly n)} [I.IsPrime] [J.IsPrime] (h : I < J) :
    OAI.QuarticPowerFree.affineDimension J < OAI.QuarticPowerFree.affineDimension I := by
  rcases lt_or_eq_of_le (GenericFiber.affineDimension_mono h.le) with hlt | heq
  · exact hlt
  · exact absurd (Request.affine_prime_same_dimension_eq I J h.le rfl heq) h.ne

theorem chart_prime_dim {n : ℕ} (P : Ideal (Poly n)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (G : Poly n) (D : ℕ) (hG : G.IsHomogeneous D) (hGP : G ∉ P) (c : Fin n)
    (N : Ideal (Poly n)) [hN : N.IsPrime]
    (hle : P ⊔ Ideal.span {G} ⊔ Ideal.span {MvPolynomial.X c - 1} ≤ N) :
    OAI.QuarticPowerFree.affineDimension N + 2 ≤ OAI.QuarticPowerFree.affineDimension P := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin n) ℂ
  let N0 : Ideal (Poly n) := (N.homogeneousCore 𝒜).toIdeal
  haveI : N0.IsPrime := hN.homogeneousCore
  have hPN : P ≤ N := le_trans le_sup_left (le_trans le_sup_left hle)
  have hGN : G ∈ N := hle (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self G)))
  have hXN : MvPolynomial.X c - 1 ∈ N :=
    hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hPN0 : P ≤ N0 := by
    have h := Ideal.homogeneousCore_mono 𝒜 hPN
    rw [← hP.toIdeal_homogeneousCore_eq_self]
    exact h
  have hGN0 : G ∈ N0 :=
    Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨D, (MvPolynomial.mem_homogeneousSubmodule D G).mpr hG⟩ hGN
  have hXN0 : MvPolynomial.X c - 1 ∉ N0 := by
    intro h
    have h0 := MvPolynomial.homogeneousComponent_mem_of_mem
      (N.homogeneousCore 𝒜).isHomogeneous h 0
    rw [MvPolynomial.homogeneousComponent_zero] at h0
    have hcoeff : (MvPolynomial.X c - 1 : Poly n).coeff 0 = -1 := by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_zero_X, MvPolynomial.coeff_zero_one]
      ring
    rw [hcoeff] at h0
    apply (inferInstance : N0.IsPrime).ne_top
    rw [Ideal.eq_top_iff_one]
    have := N0.mul_mem_left (MvPolynomial.C (-1 : ℂ)) h0
    simpa [← map_mul] using this
  have h1 : P < N0 := lt_of_le_of_ne hPN0 (fun h => hGP (h ▸ hGN0))
  have h2 : N0 < N := lt_of_le_of_ne (Ideal.toIdeal_homogeneousCore_le 𝒜 N)
    (fun h => hXN0 (h ▸ hXN))
  have d1 := prime_dim_lt h1
  have d2 := prime_dim_lt h2
  omega

/-! ### Boundary flats through a general point -/

section Boundary

variable {e : ℕ} (C : SkewCoordinates e)

/-- The ideal of the chart-`i` boundary: cone, `G = 0`, `x_{first,i} = 1`. -/
def boundaryChartIdeal (Λ : ProjectiveVariety (e + e)) (G : Poly (e + e)) (i : Fin e) :
    Ideal (Poly (e + e)) :=
  Λ.ideal ⊔ Ideal.span {G} ⊔ Ideal.span {MvPolynomial.X (Fin.castAdd e i) - 1}

theorem boundary_normalized (Λ : ProjectiveVariety (e + e)) (G : Poly (e + e)) (D : ℕ)
    (hG : G.IsHomogeneous D) (p : ProjectivePoint (e + e)) (hp : p ∈ Λ.points)
    (hpG : MvPolynomial.aeval p.rep G = 0) (z : Point (skewDim e))
    (hz : z ∈ evaluationFlat C p) :
    ∃ i : Fin e, ∃ x : Point (e + e), ∃ hx : x ≠ 0, Projectivization.mk ℂ x hx = p ∧
      x ∈ MvPolynomial.zeroLocus ℂ (boundaryChartIdeal Λ G i) ∧ firstPoint x i = 1 ∧
      (C.decode z).val (firstPoint x) = covectorOfPoint (secondPoint x) := by
  have hz' : (C.decode z).val (firstPoint p.rep) = covectorOfPoint (secondPoint p.rep) := hz
  have hfirst := first_ne_zero_of_flat C z p.rep p.rep_nonzero hz'
  obtain ⟨i, hi⟩ : ∃ i, firstPoint p.rep i ≠ 0 := by
    by_contra h
    push Not at h
    exact hfirst (funext h)
  let c : ℂ := (firstPoint p.rep i)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hi
  let x : Point (e + e) := c • p.rep
  have hx : x ≠ 0 := smul_ne_zero hc p.rep_nonzero
  have hmk : Projectivization.mk ℂ x hx = p := by
    conv_rhs => rw [← Projectivization.mk_rep p]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ hx p.rep_nonzero).mpr ⟨c, rfl⟩
  have hxi : firstPoint x i = 1 := by
    simp [x, RulingMaps.firstPoint_smul, c, inv_mul_cancel₀ hi]
  refine ⟨i, x, hx, hmk, ?_, hxi, (flat_smul_iff C z c hc p.rep).mpr hz'⟩
  have hcone : x ∈ Λ.affineCone.points := by
    rw [← ProjectiveVariety.mem_points_mk_iff Λ x hx, hmk]
    exact hp
  apply MvPolynomial.mem_zeroLocus_iff.mpr
  intro f hf
  have hker : boundaryChartIdeal Λ G i ≤
      RingHom.ker (MvPolynomial.aeval x : Poly (e + e) →ₐ[ℂ] ℂ).toRingHom := by
    apply sup_le (sup_le ?_ ?_) ?_
    · intro q hq
      exact (MvPolynomial.mem_zeroLocus_iff.mp hcone) q hq
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change MvPolynomial.aeval x G = 0
      rw [RulingMaps.aeval_smul_of_isHomogeneous hG, hpG, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change MvPolynomial.aeval x (MvPolynomial.X (Fin.castAdd e i) - 1) = 0
      simp only [map_sub, MvPolynomial.aeval_X, map_one]
      rw [show x (Fin.castAdd e i) = firstPoint x i from rfl, hxi, sub_self]
  exact hker hf

theorem boundaryChartIdeal_dim (Λ : ProjectiveVariety (e + e)) (hΛ : Λ.IsIrreducible)
    (k : ℕ) (hΛdim : Λ.dimension = k) (G : Poly (e + e)) (D : ℕ) (hG : G.IsHomogeneous D)
    (hGΛ : G ∉ Λ.ideal) (i : Fin e) (N : Ideal (Poly (e + e))) (hN : N.IsPrime)
    (hle : boundaryChartIdeal Λ G i ≤ N) :
    OAI.QuarticPowerFree.affineDimension N + 1 ≤ k := by
  haveI : Λ.ideal.IsPrime := hΛ
  have hcone := ProjectiveVariety.dimension_cone Λ (ProjectiveFamily.irreducible_points_nonempty Λ hΛ)
  have h := chart_prime_dim Λ.ideal Λ.isHomogeneous G D hG hGΛ (Fin.castAdd e i) N hle
  change OAI.QuarticPowerFree.affineDimension Λ.ideal = Λ.dimension + 1 at hcone
  omega

/-- **Boundary, `j = 0`.** A general point of `V` lies on no boundary flat. -/
theorem boundary_flats_avoid (Λ : ProjectiveVariety (e + e)) (hΛ : Λ.IsIrreducible)
    (k : ℕ) (hk : 1 ≤ k) (hΛdim : Λ.dimension = k) (G : Poly (e + e)) (D : ℕ)
    (hG : G.IsHomogeneous D) (hGΛ : G ∉ Λ.ideal)
    (V : AffineVariety (skewDim e)) (hV : V.IsIrreducible)
    (hVdim : V.dimension = flatDim e + k) :
    ∃ g : Poly (skewDim e), g ∉ V.ideal ∧ ∀ z : Point (skewDim e),
      MvPolynomial.aeval z g ≠ 0 → ∀ p ∈ Λ.points, MvPolynomial.aeval p.rep G = 0 →
        z ∉ evaluationFlat C p := by
  classical
  haveI : V.ideal.IsPrime := hV
  have hchart : ∀ i : Fin e, ∃ g : Poly (skewDim e), g ∉ V.ideal ∧
      ∀ z, MvPolynomial.aeval z g ≠ 0 → ∀ x ∈ MvPolynomial.zeroLocus ℂ (boundaryChartIdeal Λ G i),
        firstPoint x i = 1 → (C.decode z).val (firstPoint x) ≠ covectorOfPoint (secondPoint x) := by
    intro i
    obtain ⟨ψ, _, hψ⟩ := chartKernel_parametrization C i
    have hB : (((k - 1) + flatDim e : ℕ) : Cardinal) <
        Algebra.trdeg ℂ (Poly (skewDim e) ⧸ V.ideal) := by
      rw [← GenericFiber.affineDimension_eq_trdeg]
      change (((k - 1) + flatDim e : ℕ) : Cardinal) < (V.dimension : Cardinal)
      rw [hVdim]
      exact_mod_cast (by omega : (k - 1) + flatDim e < flatDim e + k)
    obtain ⟨g, hg, hvan⟩ := DegreeFacts.exists_vanishing_on_parametrized_image
      (boundaryChartIdeal Λ G i)
      (fun N hN hle => by
        have := boundaryChartIdeal_dim Λ hΛ k hΛdim G D hG hGΛ i N hN hle
        omega)
      (chartPoly C i ψ) (Ideal.Quotient.mkₐ ℂ V.ideal) (Ideal.Quotient.mkₐ_surjective ℂ _) hB
    refine ⟨g, fun h => hg (by
      rw [Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h), ?_⟩
    intro z hgz x hx hxi hflat
    obtain ⟨z', hz', hzz⟩ := chart_repr C i x hxi z hflat
    obtain ⟨t, rfl⟩ := hψ z' hz'
    apply hgz
    have h0 := hvan x hx t
    have hpt : (fun m => MvPolynomial.aeval (Fin.append x t) (chartPoly C i ψ m)) = z := by
      funext m
      rw [eval_chartPoly, hzz]
    rwa [hpt] at h0
  choose gs hgs hgv using hchart
  refine ⟨∏ i, gs i, ?_, ?_⟩
  · intro hmem
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hgs i hi
  · intro z hgz p hp hpG hz
    obtain ⟨i, x, hx0, _, hx, hxi, hflat⟩ := boundary_normalized C Λ G D hG p hp hpG z hz
    apply hgv i z ?_ x hx hxi hflat
    intro h0
    apply hgz
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0

/-- The polynomial ring over a coordinate ring, as a quotient of one more variable. -/
def polyQuotientMap (n : ℕ) (I : Ideal (Poly n)) :
    Poly (n + 1) →ₐ[ℂ] Polynomial (Poly n ⧸ I) :=
  MvPolynomial.aeval (Fin.snoc (fun m => Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.X m)))
    Polynomial.X)

theorem polyQuotientMap_rename (n : ℕ) (I : Ideal (Poly n)) (f : Poly n) :
    polyQuotientMap n I (MvPolynomial.rename Fin.castSucc f) =
      Polynomial.C (Ideal.Quotient.mk I f) := by
  have h : (polyQuotientMap n I).comp (MvPolynomial.rename Fin.castSucc) =
      (Polynomial.CAlgHom).comp (Ideal.Quotient.mkₐ ℂ I) := by
    apply MvPolynomial.algHom_ext
    intro m
    simp [polyQuotientMap]
  exact congrArg (fun φ : Poly n →ₐ[ℂ] Polynomial (Poly n ⧸ I) => φ f) h

theorem polyQuotientMap_surjective (n : ℕ) (I : Ideal (Poly n)) :
    Function.Surjective (polyQuotientMap n I) := by
  intro q
  induction q using Polynomial.induction_on with
  | C a =>
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨_, polyQuotientMap_rename n I f⟩
  | add p q hp hq =>
      obtain ⟨f, rfl⟩ := hp
      obtain ⟨g, rfl⟩ := hq
      exact ⟨f + g, map_add _ _ _⟩
  | monomial k a h =>
      obtain ⟨f, hf⟩ := h
      refine ⟨f * MvPolynomial.X (Fin.last n), ?_⟩
      rw [map_mul, hf, pow_succ, ← mul_assoc]
      congr 1
      simp [polyQuotientMap]

theorem eval_polyQuotientMap (n : ℕ) (I : Ideal (Poly n)) (z : Point n)
    (hz : I ≤ RingHom.ker (MvPolynomial.aeval z : Poly n →ₐ[ℂ] ℂ).toRingHom)
    (F : Poly (n + 1)) (T : ℂ) :
    ((polyQuotientMap n I F).map (Ideal.Quotient.lift I
      (MvPolynomial.aeval z : Poly n →ₐ[ℂ] ℂ).toRingHom hz)).eval T =
      MvPolynomial.aeval (Fin.snoc z T : Point (n + 1)) F := by
  let ev := Ideal.Quotient.lift I (MvPolynomial.aeval z : Poly n →ₐ[ℂ] ℂ).toRingHom hz
  have h : ((Polynomial.evalRingHom T).comp (Polynomial.mapRingHom ev)).comp
      (polyQuotientMap n I).toRingHom =
      (MvPolynomial.aeval (Fin.snoc z T : Point (n + 1)) : Poly (n + 1) →ₐ[ℂ] ℂ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polyQuotientMap, ev]
      rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.lift_mk]
      simp
    · intro m
      refine Fin.lastCases ?_ (fun m => ?_) m
      · simp [polyQuotientMap]
      · simp [polyQuotientMap, ev]
  exact RingHom.congr_fun h F

/-- **Boundary, `j = 1`.** Only finitely many boundary flats pass through a general point. -/
theorem boundary_flats_finite (Λ : ProjectiveVariety (e + e)) (hΛ : Λ.IsIrreducible)
    (k : ℕ) (hΛdim : Λ.dimension = k + 1) (G : Poly (e + e)) (D : ℕ)
    (hG : G.IsHomogeneous D) (hGΛ : G ∉ Λ.ideal)
    (V : AffineVariety (skewDim e)) (hV : V.IsIrreducible)
    (hVdim : V.dimension = flatDim e + k) :
    ∃ g : Poly (skewDim e), g ∉ V.ideal ∧ ∀ z ∈ V.points,
      MvPolynomial.aeval z g ≠ 0 →
        {p | p ∈ Λ.points ∧ MvPolynomial.aeval p.rep G = 0 ∧ z ∈ evaluationFlat C p}.Finite := by
  classical
  haveI : V.ideal.IsPrime := hV
  have hchart : ∀ i : Fin e, ∀ c : Fin (e + e), ∃ g : Poly (skewDim e), g ∉ V.ideal ∧
      ∀ z ∈ V.points, MvPolynomial.aeval z g ≠ 0 →
        {T : ℂ | ∃ x ∈ MvPolynomial.zeroLocus ℂ (boundaryChartIdeal Λ G i),
          firstPoint x i = 1 ∧ (C.decode z).val (firstPoint x) = covectorOfPoint (secondPoint x) ∧
            x c = T}.Finite := by
    intro i c
    obtain ⟨ψ, _, hψ⟩ := chartKernel_parametrization C i
    have hB : ((k + flatDim e : ℕ) : Cardinal) <
        Algebra.trdeg ℂ (Polynomial (Poly (skewDim e) ⧸ V.ideal)) := by
      rw [GenericFiber.trdeg_polynomial_quotient]
      change ((k + flatDim e : ℕ) : Cardinal) < (V.dimension : Cardinal) + 1
      rw [hVdim]
      exact_mod_cast (by omega : k + flatDim e < flatDim e + k + 1)
    let Φ : Fin (skewDim e + 1) → Poly ((e + e) + flatDim e) :=
      Fin.snoc (chartPoly C i ψ) (MvPolynomial.X (Fin.castAdd (flatDim e) c))
    obtain ⟨F, hF, hvan⟩ := DegreeFacts.exists_vanishing_on_parametrized_image
      (boundaryChartIdeal Λ G i)
      (fun N hN hle => by
        have := boundaryChartIdeal_dim Λ hΛ (k + 1) hΛdim G D hG hGΛ i N hN hle
        omega)
      Φ (polyQuotientMap (skewDim e) V.ideal) (polyQuotientMap_surjective _ _) hB
    obtain ⟨n, hn⟩ : ∃ n, (polyQuotientMap (skewDim e) V.ideal F).coeff n ≠ 0 := by
      by_contra h
      push Not at h
      exact hF (Polynomial.ext (by simpa using h))
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
      ((polyQuotientMap (skewDim e) V.ideal F).coeff n)
    refine ⟨g, fun h => hn (by rw [← hg]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h), ?_⟩
    intro z hz hgz
    have hzle : V.ideal ≤ RingHom.ker (MvPolynomial.aeval z : Poly (skewDim e) →ₐ[ℂ] ℂ).toRingHom :=
      fun f hf => (MvPolynomial.mem_zeroLocus_iff.mp hz) f hf
    let q := (polyQuotientMap (skewDim e) V.ideal F).map (Ideal.Quotient.lift V.ideal
      (MvPolynomial.aeval z : Poly (skewDim e) →ₐ[ℂ] ℂ).toRingHom hzle)
    have hq : q ≠ 0 := by
      intro h0
      have := congrArg (fun r => Polynomial.coeff r n) h0
      simp only [q, Polynomial.coeff_map, Polynomial.coeff_zero, ← hg] at this
      exact hgz this
    apply (Polynomial.finite_setOfPred_isRoot hq).subset
    rintro T ⟨x, hx, hxi, hflat, rfl⟩
    obtain ⟨z', hz', hzz⟩ := chart_repr C i x hxi z hflat
    obtain ⟨t, rfl⟩ := hψ z' hz'
    change q.eval (x c) = 0
    rw [eval_polyQuotientMap]
    have h0 := hvan x hx t
    have hpt : (fun m => MvPolynomial.aeval (Fin.append x t) (Φ m)) =
        (Fin.snoc z (x c) : Point (skewDim e + 1)) := by
      funext m
      refine Fin.lastCases ?_ (fun m => ?_) m
      · simp only [Φ, Fin.snoc_last, MvPolynomial.aeval_X, Fin.append_left]
      · simp only [Φ, Fin.snoc_castSucc]
        rw [eval_chartPoly, hzz]
    rwa [hpt] at h0
  choose gs hgs hfin using hchart
  refine ⟨∏ i, ∏ c, gs i c, ?_, ?_⟩
  · intro hmem
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    obtain ⟨c, _, hc⟩ := Ideal.IsPrime.prod_mem_iff.mp hi
    exact hgs i c hc
  · intro z hz hgz
    have hgic : ∀ i c, MvPolynomial.aeval z (gs i c) ≠ 0 := by
      intro i c h0
      apply hgz
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ c) h0
    let X : Fin e → Set (Point (e + e)) := fun i => Set.pi Set.univ (fun c =>
      {T : ℂ | ∃ x ∈ MvPolynomial.zeroLocus ℂ (boundaryChartIdeal Λ G i),
          firstPoint x i = 1 ∧ (C.decode z).val (firstPoint x) = covectorOfPoint (secondPoint x) ∧
            x c = T})
    have hX : ∀ i, (X i).Finite := fun i =>
      Set.Finite.pi (fun c => hfin i c z hz (hgic i c))
    let Y : Fin e → Set (ProjectivePoint (e + e)) := fun i =>
      Projectivization.mk' ℂ '' {v : {v : Point (e + e) // v ≠ 0} | v.1 ∈ X i}
    have hY : ∀ i, (Y i).Finite := fun i =>
      ((hX i).preimage Subtype.val_injective.injOn).image _
    apply (Set.finite_iUnion hY).subset
    rintro p ⟨hp, hpG, hzp⟩
    obtain ⟨i, x, hx0, hmk, hx, hxi, hflat⟩ := boundary_normalized C Λ G D hG p hp hpG z hzp
    refine Set.mem_iUnion.mpr ⟨i, ⟨⟨x, hx0⟩, ?_, hmk⟩⟩
    intro c _
    exact ⟨x, hx, hxi, hflat, rfl⟩

end Boundary

/-! ### The closure of a punctured projective line -/

theorem closure_punctured_plane {n : ℕ} (ψ : Point 2 →ₗ[ℂ] Point n) (hψ : Function.Injective ψ) :
    ProjectiveVariety.closure {p | ∃ t : Point 2, t 0 ≠ 0 ∧ ∃ ht : ψ t ≠ 0,
      Projectivization.mk ℂ (ψ t) ht = p} = linearProjectivePlane (LinearMap.range ψ) := by
  apply ProjectiveVariety.ext
  change ProjectiveVariety.vanishingIdeal _ = ProjectiveVariety.vanishingIdeal _
  apply le_antisymm
  · intro f hf
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro x ⟨hx0, y, ⟨s, rfl⟩, hy0, hxy⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ hy0 hx0).mp hxy
    -- `f ∘ ψ` vanishes off the line `t 0 = 0`, hence everywhere
    let q : Poly 2 := affineLinearPullback 0 ψ f
    have hq : ∀ t : Point 2, MvPolynomial.aeval t q = MvPolynomial.aeval (ψ t) f := by
      intro t
      rw [eval_affineLinearPullback, zero_add]
    have hXq : MvPolynomial.X 0 * q = 0 := by
      apply MvPolynomial.funext
      intro t
      rw [map_mul, map_zero, MvPolynomial.eval_X]
      by_cases ht : t 0 = 0
      · rw [ht, zero_mul]
      · have htne : ψ t ≠ 0 := by
          intro h0
          apply ht
          have := hψ (h0.trans (map_zero ψ).symm)
          rw [this]
          rfl
        have hmem := (MvPolynomial.mem_vanishingIdeal_iff.mp hf) (ψ t) ⟨htne, t, ht, htne, rfl⟩
        have hqt : MvPolynomial.eval t q = MvPolynomial.aeval (ψ t) f := by
          rw [← hq t, MvPolynomial.aeval_eq_eval]
        rw [hqt, hmem, mul_zero]
    have hq0 : q = 0 := (mul_eq_zero.mp hXq).resolve_left (MvPolynomial.X_ne_zero 0)
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hy0
      rw [← hc, zero_smul]
    have hx : x = ψ (c⁻¹ • s) := by
      rw [map_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hx, ← hq, hq0, map_zero]
  · apply MvPolynomial.vanishingIdeal_anti_mono
    rintro x ⟨hx0, t, _, ht, hxt⟩
    exact ⟨hx0, ψ t, ⟨t, rfl⟩, ht, hxt⟩

theorem finrank_range_two {n : ℕ} (ψ : Point 2 →ₗ[ℂ] Point n) (hψ : Function.Injective ψ) :
    Module.finrank ℂ (LinearMap.range ψ) = 2 := by
  rw [LinearMap.finrank_range_of_inj hψ, Module.finrank_fin_fun]

/-! ### The graph map -/

section Graph

variable {e : ℕ} (C : SkewCoordinates e)

theorem point_ext {n m : ℕ} (w w' : Point (n + m)) (h1 : firstPoint w = firstPoint w')
    (h2 : secondPoint w = secondPoint w') : w = w' := by
  rw [← joinPoints_eta w, ← joinPoints_eta w', h1, h2]

def graphLinear (z : Point (skewDim e)) : Point e →ₗ[ℂ] Point (e + e) where
  toFun v := graphVector C z v
  map_add' v w := by
    apply point_ext
    · change firstPoint (graphVector C z (v + w)) =
        firstPoint (graphVector C z v) + firstPoint (graphVector C z w)
      simp only [RulingMaps.firstPoint_graphVector]
    · change secondPoint (graphVector C z (v + w)) =
        secondPoint (graphVector C z v) + secondPoint (graphVector C z w)
      simp only [secondPoint_graphVector, map_add]
      exact (covectorPointLinear e).map_add _ _
  map_smul' c v := by
    apply point_ext
    · change firstPoint (graphVector C z (c • v)) = c • firstPoint (graphVector C z v)
      simp only [RulingMaps.firstPoint_graphVector]
    · change secondPoint (graphVector C z (c • v)) = c • secondPoint (graphVector C z v)
      simp only [secondPoint_graphVector, map_smul]
      exact (covectorPointLinear e).map_smul _ _

theorem graphLinear_apply (z : Point (skewDim e)) (v : Point e) :
    graphLinear C z v = graphVector C z v := rfl

theorem graphLinear_injective (z : Point (skewDim e)) : Function.Injective (graphLinear C z) := by
  intro v w h
  have := congrArg firstPoint h
  simpa [graphLinear_apply, RulingMaps.firstPoint_graphVector] using this

end Graph


/-! ### Assembly -/

section Assembly

variable {e : ℕ} (C : SkewCoordinates e) (a : Fin e)

theorem single_ne_zero' : (Pi.single a (1 : ℂ) : Point e) ≠ 0 := by
  intro h
  have := congrFun h a
  simp at this

/-- The graph parameter as a total function (the junk value is never used). -/
def gpt (z : Point (skewDim e)) (v : Point e) : ProjectivePoint (e + e) :=
  if hv : v ≠ 0 then graphParameter C z v hv
  else graphParameter C z (Pi.single a 1) (single_ne_zero' a)

theorem gpt_eq (z : Point (skewDim e)) (v : Point e) (hv : v ≠ 0) :
    gpt C a z v = graphParameter C z v hv := by
  simp [gpt, hv]

variable {h j N : ℕ} (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- **B11 in unfolded form**, given the parameter-closure dimension (B01). -/
theorem generic_point_fiber_degree_aux (hh : 1 ≤ h) (hd : V.dimension = flatDim e + h)
    (R : IsRulingIncidence C V Γ H a j N)
    (hΛdim : (parameterClosure C Γ H).dimension = h + j) :
    ∃ d : ℚ, 0 < d ∧ d ≤ (N : ℚ) ∧ (j = 1 → d = 1) ∧
      ∃ g : Poly (skewDim e), g ∉ V.ideal ∧ ∀ z ∈ workingPoints V H,
        MvPolynomial.aeval z g ≠ 0 →
          (ProjectiveVariety.closure
            {p | p ∈ parameterClosure C Γ H ∧ z ∈ evaluationFlat C p}).degree = d := by
  classical
  let Λ := parameterClosure C Γ H
  have hΛ : Λ.IsIrreducible := parameterClosure_irreducible C V Γ H a R
  haveI : V.ideal.IsPrime := R.variety_irreducible
  obtain ⟨G, D, hG, hGΛ, hinside⟩ := Request.polynomial_projective_image_contains_open
    Γ R.incidence_irreducible (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R)
    (rulingGraphPolynomials C) (fun w hw _ => rulingGraphPolynomials_nonzero C V Γ H a R w hw)
  rw [ruling_polynomial_projective_image C V Γ H a R] at hGΛ hinside
  have hnorm : ∀ z v, v ∈ directionFiber Γ z → v a = 1 := by
    intro z v hv
    have := R.normalized _ hv
    rwa [RulingMaps.secondPoint_joinPoints] at this
  have hvne : ∀ z v, v ∈ directionFiber Γ z → v ≠ 0 := by
    intro z v hv h0
    have := hnorm z v hv
    rw [h0] at this
    exact zero_ne_one this
  have hsplit : ∀ z ∈ workingPoints V H,
      {p | p ∈ parameterClosure C Γ H ∧ z ∈ evaluationFlat C p} =
        gpt C a z '' directionFiber Γ z ∪
          {p | p ∈ Λ.points ∧ MvPolynomial.aeval p.rep G = 0 ∧ z ∈ evaluationFlat C p} := by
    intro z hz
    ext p
    constructor
    · rintro ⟨hpΛ, hzp⟩
      by_cases hpG : MvPolynomial.aeval p.rep G = 0
      · exact Or.inr ⟨hpΛ, hpG, hzp⟩
      · left
        have hpim : p ∈ parameterImage C Γ H := hinside p hpΛ hpG
        obtain ⟨v, hv, hv0, rfl⟩ := (R.full_parameter_fibers p hpim z hz).mp hzp
        exact ⟨v, hv.1, gpt_eq C a z v hv0⟩
    · rintro (⟨v, hv, rfl⟩ | ⟨hpΛ, _, hzp⟩)
      · have hv0 := hvne z v hv
        rw [gpt_eq C a z v hv0]
        refine ⟨?_, mem_flat_graphParameter C z v hv0⟩
        apply ProjectiveVariety.subset_closure
        refine ⟨z, v, ⟨hv, ?_⟩, hv0, rfl⟩
        rw [RulingMaps.firstPoint_joinPoints]
        exact hz.2
      · exact ⟨hpΛ, hzp⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp R.fiber_cases with hj | hj
  · -- `j = 0`: finitely many points, generically of constant number
    subst hj
    have hΛdim0 : Λ.dimension = h := by simpa using hΛdim
    obtain ⟨gB, hgB, hB⟩ := boundary_flats_avoid C Λ hΛ h hh hΛdim0 G D hG hGΛ V
      R.variety_irreducible hd
    have hΓdim : Γ.dimension = V.dimension := by simpa using R.incidence_dimension
    obtain ⟨gC, hgC, r, hcount⟩ := generic_direction_count V Γ R.variety_irreducible
      R.incidence_irreducible H R.nonzero_section R.point_containment R.dominant hΓdim
    have hg : gB * gC ∉ V.ideal := fun hm =>
      ((inferInstance : V.ideal.IsPrime).mem_or_mem hm).elim hgB hgC
    obtain ⟨z0, hz0, hz0g⟩ := GenericFiber.exists_point_of_not_mem V (gB * gC * H)
      (fun hm => ((inferInstance : V.ideal.IsPrime).mem_or_mem hm).elim hg R.nonzero_section)
    simp only [map_mul] at hz0g
    have hz0w : z0 ∈ workingPoints V H := ⟨hz0, right_ne_zero_of_mul hz0g⟩
    have hgC0 : MvPolynomial.aeval z0 gC ≠ 0 :=
      right_ne_zero_of_mul (left_ne_zero_of_mul hz0g)
    obtain ⟨hfin0, hcard0⟩ := hcount z0 hz0 hgC0
    have hrpos : 0 < r := hcard0 ▸ (Set.ncard_pos hfin0).mpr (R.dominant z0 hz0w)
    have hrN : r ≤ N := hcard0 ▸ (R.finite_fiber rfl z0 hz0w).2
    refine ⟨r, by exact_mod_cast hrpos, by exact_mod_cast hrN, fun h1 => absurd h1 (by norm_num),
      gB * gC, hg, ?_⟩
    intro z hz hgz
    rw [map_mul] at hgz
    have hgBz : MvPolynomial.aeval z gB ≠ 0 := left_ne_zero_of_mul hgz
    have hgCz : MvPolynomial.aeval z gC ≠ 0 := right_ne_zero_of_mul hgz
    obtain ⟨hfin, hcard⟩ := hcount z hz.1 hgCz
    have hbd : {p | p ∈ Λ.points ∧ MvPolynomial.aeval p.rep G = 0 ∧ z ∈ evaluationFlat C p} =
        ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp, hpG, hzp⟩
      exact hB z hgBz p hp hpG hzp
    rw [hsplit z hz, hbd, Set.union_empty]
    have hinj : Set.InjOn (gpt C a z) (directionFiber Γ z) := by
      intro v hv w hw hvw
      rw [gpt_eq C a z v (hvne z v hv), gpt_eq C a z w (hvne z w hw)] at hvw
      exact graphParameter_injective C z a v w _ _ (hnorm z v hv) (hnorm z w hw) hvw
    have hfinI := hfin.image (gpt C a z)
    rw [← hfinI.coe_toFinset, closure_finset_degree, ← Set.ncard_eq_toFinset_card _ hfinI,
      hinj.ncard_image, hcard]
  · -- `j = 1`: a projective line plus finitely many boundary points
    subst hj
    obtain ⟨gB, hgB, hB⟩ := boundary_flats_finite C Λ hΛ h hΛdim G D hG hGΛ V
      R.variety_irreducible hd
    refine ⟨1, one_pos, by exact_mod_cast R.bound_positive, fun _ => rfl, gB, hgB, ?_⟩
    intro z hz hgz
    have hBfin := hB z hz.1 hgz
    obtain ⟨b, a', ha', hline⟩ := R.line_fiber rfl z hz
    have hb : b ∈ directionFiber Γ z := by
      rw [hline]
      exact ⟨0, by simp⟩
    have hba : b + a' ∈ directionFiber Γ z := by
      rw [hline]
      exact ⟨1, by simp⟩
    have hb_a : b a = 1 := hnorm z b hb
    have ha'_a : a' a = 0 := by
      have := hnorm z _ hba
      rw [Pi.add_apply, hb_a] at this
      linear_combination this
    let lin : Point 2 →ₗ[ℂ] Point e :=
      (LinearMap.proj 0).smulRight b + (LinearMap.proj 1).smulRight a'
    have hlin : ∀ t : Point 2, lin t = t 0 • b + t 1 • a' := fun t => rfl
    have hlin_inj : Function.Injective lin := by
      rw [injective_iff_map_eq_zero]
      intro t ht
      rw [hlin] at ht
      have h0 : t 0 = 0 := by
        have := congrFun ht a
        simpa [hb_a, ha'_a] using this
      rw [h0, zero_smul, zero_add, smul_eq_zero] at ht
      have h1 : t 1 = 0 := ht.resolve_right ha'
      funext k
      fin_cases k
      · exact h0
      · exact h1
    let ψ := (graphLinear C z).comp lin
    have hψ : Function.Injective ψ := (graphLinear_injective C z).comp hlin_inj
    have himage : gpt C a z '' directionFiber Γ z =
        {p | ∃ t : Point 2, t 0 ≠ 0 ∧ ∃ ht : ψ t ≠ 0, Projectivization.mk ℂ (ψ t) ht = p} := by
      ext p
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hv' := hv
        rw [hline] at hv'
        obtain ⟨s, rfl⟩ := hv'
        let t : Point 2 := ![1, s]
        have hψt : ψ t = graphVector C z (b + s • a') := by
          change graphLinear C z (lin t) = _
          rw [hlin, graphLinear_apply]
          simp [t]
        refine ⟨t, by simp [t], hψt ▸ graphVector_ne_zero C z _ (hvne z _ hv), ?_⟩
        rw [gpt_eq C a z _ (hvne z _ hv), graphParameter]
        exact RulingMaps.mk_congr hψt _ _
      · rintro ⟨t, ht0, htne, rfl⟩
        let v : Point e := (t 0)⁻¹ • lin t
        have hv : v ∈ directionFiber Γ z := by
          rw [hline]
          refine ⟨(t 0)⁻¹ * t 1, ?_⟩
          simp only [v, hlin, smul_add, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        refine ⟨v, hv, ?_⟩
        rw [gpt_eq C a z v (hvne z v hv), graphParameter]
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ htne).mpr
        refine ⟨(t 0)⁻¹, ?_⟩
        change (t 0)⁻¹ • graphLinear C z (lin t) = graphLinear C z v
        rw [← map_smul]
    rw [hsplit z hz, himage, ← hBfin.coe_toFinset]
    exact closure_union_finset_degree _ (LinearMap.range ψ) (finrank_range_two ψ hψ)
      (closure_punctured_plane ψ hψ) _

end Assembly

end

end DistinctDistances.TrackB.B11
