import DistinctDistances.TrackB.MixedHilbert
import DistinctDistances.TrackB.IncidenceLinearSupport

/-!
Infrastructure for the B13 redesign (`TripleRankRoute.lean`): the special polynomials of the
triple ring, their evaluations at incidence representatives, and rank tools.
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

/-- The triple ambient polynomial ring (directions, parameters, points). -/
abbrev TPoly (e : ℕ) := Poly (e + (e + e) + (skewDim e + 1))

/-- The triple block weight. -/
abbrev tw (e : ℕ) : Fin (e + (e + e) + (skewDim e + 1)) → (Fin 3 →₀ ℕ) :=
  HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))

/-- Section rank of an ideal of the triple ring in tridegree `(s,t,u)`. -/
def secRank {e : ℕ} (J : Ideal (TPoly e)) (s t u : ℕ) : ℕ :=
  Module.finrank ℂ (HilbertMulti.sectionSpace (tw e) J (HilbertMulti.tripleDegree s t u))

/-- Direction variable `d_i`. -/
def dirVar {e : ℕ} (i : Fin e) : TPoly e :=
  MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))

/-- Parameter variable `p_j` (`j < e`: `v_j`; `j = e + k`: `y_k`). -/
def parVar {e : ℕ} (j : Fin (e + e)) : TPoly e :=
  MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e j))

/-- Point variable (`0`: `x0`; `succ kk`: the skew tail coordinate `z_kk`). -/
def ptVar {e : ℕ} (a : Fin (skewDim e + 1)) : TPoly e :=
  MvPolynomial.X (Fin.natAdd (e + (e + e)) a)

/-- The `k`-th coordinate of `ι_d z = (C.decode z) d`, tridegree `(1,0,1)`. -/
def dForm {e : ℕ} (C : SkewCoordinates e) (k : Fin e) : TPoly e :=
  ∑ kk : Fin (skewDim e), ∑ l : Fin e,
    MvPolynomial.C ((((C.decode (Pi.single kk 1)).val (Pi.single l 1)) (Pi.single k 1))) *
      ptVar (Fin.succ kk) * dirVar l

/-- Euler generators `π`: `x0 d_i` (paired with `v_i`) and `(ι_d z)_k` (paired with `y_k`). -/
def eulerGen {e : ℕ} (C : SkewCoordinates e) : Fin (e + e) → TPoly e :=
  Fin.addCases (fun i : Fin e => ptVar 0 * dirVar i) (fun k : Fin e => dForm C k)

/-- Pullback of the pair vanishing ideal of the base. -/
def baseIdeal {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) : Ideal (TPoly e) :=
  Ideal.map (MvPolynomial.rename
    (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
    (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H)))

/-- The incidence vanishing ideal. -/
def incIdeal {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) : Ideal (TPoly e) :=
  MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives (incidenceTriples C Γ H))

/-- Incidence ideal plus the Euler generators (cokernel of the Euler map). -/
def eulerIdeal {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) : Ideal (TPoly e) :=
  incIdeal C Γ H ⊔ Ideal.span (Set.range (eulerGen C))

/-- The kernel-bundle ideal `I_B S + (x0) + ((ι_d z)_k)`. -/
def kernelIdeal {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) : Ideal (TPoly e) :=
  baseIdeal C Γ H ⊔ Ideal.span {ptVar 0} ⊔ Ideal.span (Set.range (dForm C))

/-- Zero-extended base section ranks (`0` in negative point degree). -/
def baseRankZ {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (s t : ℕ) (u : ℤ) : ℤ :=
  if u < 0 then 0 else (secRank (baseIdeal C Γ H) s t u.toNat : ℤ)


section Eval

variable {e : ℕ}

/-- A joined triple representative. -/
abbrev tj (d : Point e) (p : Point (e + e)) (x : Point (skewDim e + 1)) :
    Point (e + (e + e) + (skewDim e + 1)) :=
  joinPoints (joinPoints d p) x

theorem eval_dirVar (d : Point e) (p : Point (e + e)) (x : Point (skewDim e + 1)) (i : Fin e) :
    MvPolynomial.aeval (tj d p x) (dirVar i) = d i := by
  simp [tj, dirVar, joinPoints, Fin.addCases_left, Fin.addCases_right]

theorem eval_parVar (d : Point e) (p : Point (e + e)) (x : Point (skewDim e + 1))
    (j : Fin (e + e)) :
    MvPolynomial.aeval (tj d p x) (parVar j) = p j := by
  simp [tj, parVar, joinPoints, Fin.addCases_left, Fin.addCases_right]

theorem eval_ptVar (d : Point e) (p : Point (e + e)) (x : Point (skewDim e + 1))
    (a : Fin (skewDim e + 1)) :
    MvPolynomial.aeval (tj d p x) (ptVar a) = x a := by
  simp [tj, ptVar, joinPoints, Fin.addCases_left, Fin.addCases_right]

/-- Bilinear expansion of `(decode z)(d, e_k)` in coordinates. -/
theorem decode_expand (C : SkewCoordinates e) (z : Point (skewDim e)) (d : Point e) (k : Fin e) :
    (C.decode z).val d (Pi.single k 1) =
      ∑ kk : Fin (skewDim e), ∑ l : Fin e,
        (((C.decode (Pi.single kk 1)).val (Pi.single l 1)) (Pi.single k 1)) * z kk * d l := by
  have hz : z = ∑ kk : Fin (skewDim e), (z kk) • (Pi.single kk (1 : ℂ) : Point (skewDim e)) := by
    simpa using ((Pi.basisFun ℂ (Fin (skewDim e))).sum_repr z).symm
  have hd : d = ∑ l : Fin e, (d l) • (Pi.single l (1 : ℂ) : Point e) := by
    simpa using ((Pi.basisFun ℂ (Fin e)).sum_repr d).symm
  conv_lhs => rw [hz, hd]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro kk _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem eval_dForm (C : SkewCoordinates e) (d : Point e) (p : Point (e + e))
    (x : Point (skewDim e + 1)) (k : Fin e) :
    MvPolynomial.aeval (tj d p x) (dForm C k) =
      (C.decode (Fin.tail x)).val d (Pi.single k 1) := by
  rw [decode_expand]
  unfold dForm
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, eval_ptVar, eval_dirVar,
    Algebra.algebraMap_self, RingHom.id_apply]
  rfl

theorem eval_eulerGen_left (C : SkewCoordinates e) (d : Point e) (p : Point (e + e))
    (x : Point (skewDim e + 1)) (i : Fin e) :
    MvPolynomial.aeval (tj d p x) (eulerGen C (Fin.castAdd e i)) = x 0 * d i := by
  simp only [eulerGen, Fin.addCases_left, map_mul, eval_ptVar, eval_dirVar]

theorem eval_eulerGen_right (C : SkewCoordinates e) (d : Point e) (p : Point (e + e))
    (x : Point (skewDim e + 1)) (k : Fin e) :
    MvPolynomial.aeval (tj d p x) (eulerGen C (Fin.natAdd e k)) =
      (C.decode (Fin.tail x)).val d (Pi.single k 1) := by
  simp only [eulerGen, Fin.addCases_right]
  exact eval_dForm C d p x k

theorem covector_single (y : Point e) (k : Fin e) :
    covectorOfPoint y (Pi.single k 1) = y k := by
  simp [covectorOfPoint, Pi.single_apply]

/-- Destructuring an incidence representative. -/
theorem incRep_cases (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) {w : Point (e + (e + e) + (skewDim e + 1))}
    (hw : w ∈ tripleRepresentatives (incidenceTriples C Γ H)) :
    ∃ d : Point e, ∃ p : Point (e + e), ∃ x : Point (skewDim e + 1),
      d ≠ 0 ∧ p ≠ 0 ∧ x ≠ 0 ∧ joinPoints d p ∈ pairRepresentatives (liftedParameterBase C Γ H) ∧
      ∃ t c : ℂ, firstPoint p = t • d ∧ covectorOfPoint (secondPoint p) d = 0 ∧
        x 0 = c * t ∧ (C.decode (Fin.tail x)).val d = c • covectorOfPoint (secondPoint p) ∧
        w = tj d p x := by
  obtain ⟨xd, xp, xx, hxd, hxp, hxx, hmem, rfl⟩ := hw
  obtain ⟨hbase, hinc⟩ := hmem
  rw [incidenceCondition_mk_iff C xd xp xx hxd hxp hxx] at hinc
  obtain ⟨t, hfirst, horth, hfiber⟩ := hinc
  change homogeneousEvaluation xd (xx 0, C.decode (Fin.tail xx)) ∈
    Submodule.span ℂ {(t, covectorOfPoint (secondPoint xp))} at hfiber
  rw [Submodule.mem_span_singleton] at hfiber
  obtain ⟨c, hc⟩ := hfiber
  have hx0 : xx 0 = c * t := by
    have h := congrArg Prod.fst hc
    change c * t = xx 0 at h
    exact h.symm
  have hD : (C.decode (Fin.tail xx)).val xd = c • covectorOfPoint (secondPoint xp) := by
    have h := congrArg Prod.snd hc
    simpa [homogeneousEvaluation, alternatingEvaluation] using h.symm
  exact ⟨xd, xp, xx, hxd, hxp, hxx, ⟨xd, xp, hxd, hxp, hbase, rfl⟩, t, c, hfirst, horth, hx0,
    hD, rfl⟩

/-- Constructing an incidence representative. -/
theorem incRep_mk (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (d : Point e) (p : Point (e + e)) (x : Point (skewDim e + 1))
    (hd : d ≠ 0) (hp : p ≠ 0) (hx : x ≠ 0)
    (hB : (Projectivization.mk ℂ d hd, Projectivization.mk ℂ p hp) ∈ liftedParameterBase C Γ H)
    (t c : ℂ) (hfirst : firstPoint p = t • d) (horth : covectorOfPoint (secondPoint p) d = 0)
    (hx0 : x 0 = c * t)
    (hD : (C.decode (Fin.tail x)).val d = c • covectorOfPoint (secondPoint p)) :
    tj d p x ∈ tripleRepresentatives (incidenceTriples C Γ H) := by
  refine ⟨d, p, x, hd, hp, hx, ⟨hB, ?_⟩, rfl⟩
  rw [incidenceCondition_mk_iff C d p x hd hp hx]
  refine ⟨t, hfirst, horth, ?_⟩
  change homogeneousEvaluation d (x 0, C.decode (Fin.tail x)) ∈
    Submodule.span ℂ {(t, covectorOfPoint (secondPoint p))}
  rw [Submodule.mem_span_singleton]
  refine ⟨c, ?_⟩
  ext
  · change c * t = x 0
    rw [hx0]
  · simp [homogeneousEvaluation, alternatingEvaluation, hD]

/-- Pair representatives come from base points. -/
theorem pairRep_cases {T : Set (ProjectivePoint e × ProjectivePoint (e + e))}
    {d : Point e} {p : Point (e + e)} (h : joinPoints d p ∈ pairRepresentatives T) :
    ∃ hd : d ≠ 0, ∃ hp : p ≠ 0,
      (Projectivization.mk ℂ d hd, Projectivization.mk ℂ p hp) ∈ T := by
  obtain ⟨x, y, hx, hy, hmem, heq⟩ := h
  have h1 : d = x := by
    funext i
    have := congrFun heq (Fin.castAdd (e + e) i)
    simpa [joinPoints, Fin.addCases_left] using this
  have h2 : p = y := by
    funext i
    have := congrFun heq (Fin.natAdd e i)
    simpa [joinPoints, Fin.addCases_right] using this
  subst h1 h2
  exact ⟨hx, hy, hmem⟩

end Eval


section Coefficient

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- A polynomial vanishing along a punctured line vanishes at its base point. -/
theorem eval_line_zero {N : ℕ} (g : Poly N) (w v : Point N) (c0 : ℂ)
    (h : ∀ a : ℂ, a ≠ c0 → MvPolynomial.aeval (w + a • v) g = 0) :
    MvPolynomial.aeval w g = 0 := by
  classical
  let f : Fin N → Polynomial ℂ := fun i => Polynomial.C (w i) + Polynomial.C (v i) * Polynomial.X
  let q : Polynomial ℂ := MvPolynomial.aeval f g
  have hq : ∀ a : ℂ, Polynomial.eval a q = MvPolynomial.aeval (w + a • v) g := by
    intro a
    have h1 := MvPolynomial.comp_aeval_apply (f := f) (Polynomial.aeval a) g
    rw [Polynomial.coe_aeval_eq_eval] at h1
    rw [h1]
    have hpt : (fun i => Polynomial.eval a (f i)) = w + a • v := by
      funext i
      simp only [f, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hpt]
  have hzero : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := ({c0}ᶜ : Set ℂ))
    · intro a ha
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, hq]
      exact h a ha
    · exact (Set.finite_singleton c0).infinite_compl
  have := hq 0
  rw [hzero, Polynomial.eval_zero, zero_smul, add_zero] at this
  exact this.symm

/-- Data form of the Euler relation `π_j = c p_j` on the incidence. -/
theorem eulerGen_rel (d : Point e) (p : Point (e + e)) (x : Point (skewDim e + 1)) (t c : ℂ)
    (hfirst : firstPoint p = t • d) (hx0 : x 0 = c * t)
    (hD : (C.decode (Fin.tail x)).val d = c • covectorOfPoint (secondPoint p)) (j : Fin (e + e)) :
    MvPolynomial.aeval (tj d p x) (eulerGen C j) = c * MvPolynomial.aeval (tj d p x) (parVar j) := by
  rw [eval_parVar]
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · rw [eval_eulerGen_left, hx0]
    have hp : p (Fin.castAdd e i) = t * d i := by
      have := congrFun hfirst i
      simpa [firstPoint, smul_eq_mul] using this
    rw [hp]
    ring
  · rw [eval_eulerGen_right, hD]
    simp only [LinearMap.smul_apply, smul_eq_mul, covector_single]
    rfl

/-- The fiber coefficient `c` as a function on the incidence representatives. -/
theorem euler_coeff_exists :
    ∃ cf : Point (e + (e + e) + (skewDim e + 1)) → ℂ,
      ∀ w ∈ tripleRepresentatives (incidenceTriples C Γ H), ∀ j : Fin (e + e),
        MvPolynomial.aeval w (eulerGen C j) = cf w * MvPolynomial.aeval w (parVar j) := by
  classical
  have hpt : ∀ w ∈ tripleRepresentatives (incidenceTriples C Γ H), ∃ c : ℂ, ∀ j : Fin (e + e),
      MvPolynomial.aeval w (eulerGen C j) = c * MvPolynomial.aeval w (parVar j) := by
    intro w hw
    obtain ⟨d, p, x, _, _, _, _, t, c, hfirst, _, hx0, hD, rfl⟩ := incRep_cases C Γ H hw
    exact ⟨c, eulerGen_rel C d p x t c hfirst hx0 hD⟩
  choose! cf hcf using hpt
  exact ⟨cf, hcf⟩

/-- Fiber density: if `c · g` vanishes on the incidence, so does `g`. -/
theorem vanish_of_coeff_mul (cf : Point (e + (e + e) + (skewDim e + 1)) → ℂ)
    (hcf : ∀ w ∈ tripleRepresentatives (incidenceTriples C Γ H), ∀ j : Fin (e + e),
      MvPolynomial.aeval w (eulerGen C j) = cf w * MvPolynomial.aeval w (parVar j))
    (g : TPoly e)
    (hg : ∀ w ∈ tripleRepresentatives (incidenceTriples C Γ H), cf w * MvPolynomial.aeval w g = 0) :
    ∀ w ∈ tripleRepresentatives (incidenceTriples C Γ H), MvPolynomial.aeval w g = 0 := by
  classical
  intro w hw
  obtain ⟨d, p, x, hd, hp, hx, hpair, t, c, hfirst, horth, hx0, hD, rfl⟩ := incRep_cases C Γ H hw
  obtain ⟨hd', hp', hB⟩ := pairRep_cases hpair
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hd (funext hcon)
  let y : Module.Dual ℂ (Point e) := covectorOfPoint (secondPoint p)
  let l : Module.Dual ℂ (Point e) := (d i)⁻¹ • LinearMap.proj i
  have hl : l d = 1 := by
    simp [l, hi]
  let A : alternatingForms (U := Point e) :=
    ⟨IncidenceLocal.anchoredForm l y, IncidenceLocal.anchoredForm_isAlt l y⟩
  have hA : A.val d = y := IncidenceLocal.anchoredForm_evaluate d l hl y horth
  let wh : Point (skewDim e + 1) := Fin.cons t (C.decode.symm A)
  apply eval_line_zero g (tj d p x) (tj 0 0 wh) (-c)
  intro a ha
  have hca : c + a ≠ 0 := by
    intro h; apply ha; linear_combination h
  let x' : Point (skewDim e + 1) := x + a • wh
  have hjoin : tj d p x + a • tj 0 0 wh = tj d p x' := by
    funext k
    refine Fin.addCases (fun k1 => ?_) (fun k2 => ?_) k
    · refine Fin.addCases (fun k3 => ?_) (fun k4 => ?_) k1
      · simp [tj, joinPoints, Fin.addCases_left]
      · simp [tj, joinPoints, Fin.addCases_left, Fin.addCases_right]
    · simp [tj, x', joinPoints, Fin.addCases_right]
  rw [hjoin]
  have hx0' : x' 0 = (c + a) * t := by
    simp [x', wh, hx0]
    ring
  have htail : Fin.tail x' = Fin.tail x + a • C.decode.symm A := by
    funext k
    simp [x', wh, Fin.tail]
  have hD' : (C.decode (Fin.tail x')).val d = (c + a) • y := by
    rw [htail, map_add, map_smul, LinearEquiv.apply_symm_apply]
    simp only [Submodule.coe_add, Submodule.coe_smul, LinearMap.add_apply,
      LinearMap.smul_apply, hA]
    rw [hD, add_smul]
  have hx' : x' ≠ 0 := by
    intro h0
    have h1 : x' 0 = 0 := by rw [h0]; rfl
    rw [hx0'] at h1
    have ht : t = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hca
      · exact h
    have h2 : (c + a) • y = 0 := by
      rw [← hD', h0]
      have : Fin.tail (0 : Point (skewDim e + 1)) = 0 := rfl
      rw [this, map_zero]
      rfl
    have hy : y = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact absurd h hca
      · exact h
    apply hp
    funext k
    refine Fin.addCases (fun k1 => ?_) (fun k2 => ?_) k
    · have := congrFun hfirst k1
      simp only [firstPoint, ht, zero_smul, Pi.zero_apply] at this
      simpa using this
    · have := LinearMap.congr_fun hy (Pi.single k2 1)
      simp only [y, covector_single, LinearMap.zero_apply] at this
      simpa [secondPoint] using this
  have hw' : tj d p x' ∈ tripleRepresentatives (incidenceTriples C Γ H) :=
    incRep_mk C Γ H d p x' hd hp hx' (by simpa using hB) t (c + a) hfirst horth hx0' hD'
  have hrel := eulerGen_rel C d p x' t (c + a) hfirst hx0' hD'
  have hcfeq : cf (tj d p x') = c + a := by
    obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hp (funext hcon)
    have h1 := hcf _ hw' j
    rw [hrel j, eval_parVar] at h1
    exact (mul_right_cancel₀ hj h1).symm
  have := hg _ hw'
  rw [hcfeq] at this
  exact (mul_eq_zero.mp this).resolve_left hca

end Coefficient


section RankTools

theorem finrank_map_add_inf {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (A : Submodule K V) [FiniteDimensional K A] :
    Module.finrank K (A.map f) + Module.finrank K (A ⊓ LinearMap.ker f : Submodule K V) =
      Module.finrank K A := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have h2 : Module.finrank K ((LinearMap.ker f).comap A.subtype) =
      Module.finrank K (A ⊓ LinearMap.ker f : Submodule K V) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective _ A.injective_subtype _).finrank_eq
  omega

variable {e : ℕ}

/-- A tridegree piece of the triple ring. -/
abbrev piece (e : ℕ) (s t u : ℕ) : Submodule ℂ (TPoly e) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e) (HilbertMulti.tripleDegree s t u)

/-- Evaluation of triple polynomials on a set of points. -/
def evSet (X : Set (Point (e + (e + e) + (skewDim e + 1)))) : TPoly e →ₗ[ℂ] (X → ℂ) where
  toFun f := fun w => MvPolynomial.aeval w.1 f
  map_add' f g := by funext w; simp
  map_smul' c f := by funext w; simp

theorem evSet_apply (X : Set (Point (e + (e + e) + (skewDim e + 1)))) (f : TPoly e) (w : X) :
    evSet X f w = MvPolynomial.aeval w.1 f := rfl

theorem ker_evSet (X : Set (Point (e + (e + e) + (skewDim e + 1)))) :
    LinearMap.ker (evSet X) = (MvPolynomial.vanishingIdeal ℂ X).restrictScalars ℂ := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro h w hw
    exact congrFun h ⟨w, hw⟩
  · intro h
    funext w
    exact h w.1 w.2

theorem ker_mkQ (J : Ideal (TPoly e)) :
    LinearMap.ker (Ideal.Quotient.mkₐ ℂ J).toLinearMap = J.restrictScalars ℂ := by
  ext f
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- Section rank plus the image of the ideal part equals the image rank. -/
theorem section_add_image (X : Set (Point (e + (e + e) + (skewDim e + 1))))
    (J : Ideal (TPoly e)) (hIJ : MvPolynomial.vanishingIdeal ℂ X ≤ J) (s t u : ℕ) :
    secRank J s t u +
        Module.finrank ℂ ((piece e s t u ⊓ J.restrictScalars ℂ).map (evSet X)) =
      Module.finrank ℂ ((piece e s t u).map (evSet X)) := by
  haveI : FiniteDimensional ℂ (piece e s t u ⊓ J.restrictScalars ℂ : Submodule ℂ (TPoly e)) :=
    Submodule.finiteDimensional_inf_left _ _
  have h1 : secRank J s t u + Module.finrank ℂ (piece e s t u ⊓ J.restrictScalars ℂ :
      Submodule ℂ (TPoly e)) = Module.finrank ℂ (piece e s t u) := by
    have := finrank_map_add_inf (Ideal.Quotient.mkₐ ℂ J).toLinearMap (piece e s t u)
    rw [ker_mkQ] at this
    exact this
  have h2 := finrank_map_add_inf (evSet X) (piece e s t u)
  have h3 := finrank_map_add_inf (evSet X) (piece e s t u ⊓ J.restrictScalars ℂ)
  rw [ker_evSet] at h2 h3
  have hinf : (piece e s t u ⊓ J.restrictScalars ℂ) ⊓
      (MvPolynomial.vanishingIdeal ℂ X).restrictScalars ℂ =
      piece e s t u ⊓ (MvPolynomial.vanishingIdeal ℂ X).restrictScalars ℂ := by
    rw [inf_assoc]
    congr 1
    exact inf_eq_right.mpr (fun x hx => hIJ hx)
  rw [hinf] at h3
  omega

/-- The section rank of the vanishing ideal is the image rank. -/
theorem secRank_vanishing (X : Set (Point (e + (e + e) + (skewDim e + 1)))) (s t u : ℕ) :
    secRank (MvPolynomial.vanishingIdeal ℂ X) s t u =
      Module.finrank ℂ ((piece e s t u).map (evSet X)) := by
  have h := section_add_image X (MvPolynomial.vanishingIdeal ℂ X) le_rfl s t u
  have h0 : (piece e s t u ⊓ (MvPolynomial.vanishingIdeal ℂ X).restrictScalars ℂ).map
      (evSet X) = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨f, hf, rfl⟩
    have hk : f ∈ LinearMap.ker (evSet X) := by rw [ker_evSet]; exact hf.2
    exact (Submodule.mem_bot ℂ).mpr hk
  rw [h0, finrank_bot] at h
  omega

/-- Homogeneous decomposition of a homogeneous member of `J + (π)`. -/
theorem homogeneous_family_decomposition (J : Ideal (TPoly e))
    (hJ : J.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)))
    {ι : Type*} [Fintype ι] (π : ι → TPoly e) {w0 n : Fin 3 →₀ ℕ}
    (hπ : ∀ k, (π k).IsWeightedHomogeneous (tw e) w0) (f : TPoly e)
    (hf : f.IsWeightedHomogeneous (tw e) (n + w0))
    (hmem : f ∈ J ⊔ Ideal.span (Set.range π)) :
    ∃ h : ι → TPoly e, (∀ k, (h k).IsWeightedHomogeneous (tw e) n) ∧
      f - ∑ k, h k * π k ∈ J := by
  classical
  obtain ⟨j, hj, q, hq, hjq⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨a, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hq
  let 𝒜 := MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)
  refine ⟨fun k => (DirectSum.decompose 𝒜 (a k) n : TPoly e), fun k => (DirectSum.decompose 𝒜 (a k) n).2, ?_⟩
  have hproj := congrArg (GradedRing.proj 𝒜 (n + w0)) hjq
  rw [map_add, map_sum, GradedRing.proj_apply, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_same 𝒜 hf] at hproj
  have key : ∀ k, (GradedRing.proj 𝒜 (n + w0)) (a k * π k) =
      (DirectSum.decompose 𝒜 (a k) n : TPoly e) * π k := by
    intro k
    rw [GradedRing.proj_apply, DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (hπ k)]
  rw [Finset.sum_congr rfl (fun k _ => key k)] at hproj
  have hjJ := (Ideal.IsHomogeneous.mem_iff 𝒜 hJ).mp hj (n + w0)
  have : f - ∑ k, (DirectSum.decompose 𝒜 (a k) n : TPoly e) * π k =
      (DirectSum.decompose 𝒜 j (n + w0) : TPoly e) := by
    rw [← hproj]; ring
  rw [this]
  exact hjJ

end RankTools


section Degrees

variable {e : ℕ}

theorem tripleDegree_add (a b c a' b' c' : ℕ) :
    HilbertMulti.tripleDegree a b c + HilbertMulti.tripleDegree a' b' c' =
      HilbertMulti.tripleDegree (a + a') (b + b') (c + c') := by
  ext j
  fin_cases j <;> simp [HilbertMulti.tripleDegree]

theorem tw_dir (i : Fin e) :
    tw e (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) =
      HilbertMulti.tripleDegree 1 0 0 := by
  simp only [tw, HilbertMulti.blockWeight, HilbertMulti.tripleBlocks, Fin.addCases_left]
  apply Finsupp.ext
  intro j
  fin_cases j <;> simp [HilbertMulti.tripleDegree]

theorem tw_par (j : Fin (e + e)) :
    tw e (Fin.castAdd (skewDim e + 1) (Fin.natAdd e j)) = HilbertMulti.tripleDegree 0 1 0 := by
  simp only [tw, HilbertMulti.blockWeight, HilbertMulti.tripleBlocks, Fin.addCases_left,
    Fin.addCases_right]
  apply Finsupp.ext
  intro k
  fin_cases k <;> simp [HilbertMulti.tripleDegree]

theorem tw_pt (a : Fin (skewDim e + 1)) :
    tw e (Fin.natAdd (e + (e + e)) a) = HilbertMulti.tripleDegree 0 0 1 := by
  simp only [tw, HilbertMulti.blockWeight, HilbertMulti.tripleBlocks, Fin.addCases_right]
  apply Finsupp.ext
  intro k
  fin_cases k <;> simp [HilbertMulti.tripleDegree]

theorem dirVar_hom (i : Fin e) :
    (dirVar i).IsWeightedHomogeneous (tw e) (HilbertMulti.tripleDegree 1 0 0) := by
  have h := MvPolynomial.isWeightedHomogeneous_X ℂ (tw e)
    (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))
  rw [tw_dir] at h
  exact h

theorem parVar_hom (j : Fin (e + e)) :
    (parVar j).IsWeightedHomogeneous (tw e) (HilbertMulti.tripleDegree 0 1 0) := by
  have h := MvPolynomial.isWeightedHomogeneous_X ℂ (tw e)
    (Fin.castAdd (skewDim e + 1) (Fin.natAdd e j))
  rw [tw_par] at h
  exact h

theorem ptVar_hom (a : Fin (skewDim e + 1)) :
    (ptVar a).IsWeightedHomogeneous (tw e) (HilbertMulti.tripleDegree 0 0 1) := by
  have h := MvPolynomial.isWeightedHomogeneous_X ℂ (tw e) (Fin.natAdd (e + (e + e)) a)
  rw [tw_pt] at h
  exact h

theorem dForm_hom (C : SkewCoordinates e) (k : Fin e) :
    (dForm C k).IsWeightedHomogeneous (tw e) (HilbertMulti.tripleDegree 1 0 1) := by
  unfold dForm
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro kk _
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro l _
  have h := ((MvPolynomial.isWeightedHomogeneous_C (R := ℂ) (tw e)
    ((((C.decode (Pi.single kk 1)).val (Pi.single l 1)) (Pi.single k 1)))).mul
      (ptVar_hom (Fin.succ kk))).mul (dirVar_hom l)
  rw [zero_add, tripleDegree_add] at h
  simpa using h

theorem eulerGen_hom (C : SkewCoordinates e) (j : Fin (e + e)) :
    (eulerGen C j).IsWeightedHomogeneous (tw e) (HilbertMulti.tripleDegree 1 0 1) := by
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · simp only [eulerGen, Fin.addCases_left]
    have h := (ptVar_hom (e := e) 0).mul (dirVar_hom i)
    rw [tripleDegree_add] at h
    simpa using h
  · simp only [eulerGen, Fin.addCases_right]
    exact dForm_hom C k

/-- Positive parameter degree: a piece lies in the parameter-variable ideal. -/
theorem piece_succ_mem_parSpan (s t u : ℕ) (f : TPoly e) (hf : f ∈ piece e s (t + 1) u) :
    f ∈ Ideal.span (Set.range (parVar (e := e))) := by
  classical
  have hrange : Set.range (parVar (e := e)) = MvPolynomial.X '' Set.range
      (fun j : Fin (e + e) => Fin.castAdd (skewDim e + 1) (Fin.natAdd e j)) := by
    ext q
    simp [parVar]
  rw [hrange, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  rw [piece, HilbertMulti.tripleBlockPiece, MvPolynomial.mem_restrictSupport_iff] at hf
  have hmS := hf hm
  obtain ⟨_, hmt, _⟩ := hmS
  have hne : (∑ i : Fin (e + e), m (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) ≠ 0 := by
    rw [hmt]; omega
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨_, ⟨i, rfl⟩, hi⟩

/-- Positive parameter degree pieces factor through the parameter variables. -/
theorem piece_succ_decomp (s t u : ℕ) (f : TPoly e) (hf : f ∈ piece e s (t + 1) u) :
    ∃ h : Fin (e + e) → TPoly e, (∀ j, h j ∈ piece e s t u) ∧
      f = ∑ j, h j * parVar j := by
  have hmem : f ∈ (⊥ : Ideal (TPoly e)) ⊔ Ideal.span (Set.range (parVar (e := e))) := by
    rw [bot_sup_eq]
    exact piece_succ_mem_parSpan s t u f hf
  have hf' : f.IsWeightedHomogeneous (tw e)
      (HilbertMulti.tripleDegree s t u + HilbertMulti.tripleDegree 0 1 0) := by
    rw [tripleDegree_add]
    simpa using hf
  obtain ⟨h, hh, hdiff⟩ := homogeneous_family_decomposition ⊥
    (Ideal.IsHomogeneous.bot _) parVar parVar_hom f hf' hmem
  refine ⟨h, fun j => hh j, ?_⟩
  rw [Ideal.mem_bot, sub_eq_zero] at hdiff
  exact hdiff

end Degrees


section Euler

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

theorem tripleHilbert_eq_secRank' (s t u : ℕ) :
    tripleHilbert (incidenceTriples C Γ H) s t u = secRank (incIdeal C Γ H) s t u := by
  have hspace : HilbertMulti.sectionSpace (tw e) (incIdeal C Γ H)
      (HilbertMulti.tripleDegree s t u) = tripleSection (incidenceTriples C Γ H) s t u := by
    rw [HilbertMulti.sectionSpace, HilbertMulti.tripleBlockPiece]
    rfl
  unfold secRank tripleHilbert
  rw [hspace]
  rfl

/-- Multiplication by a coefficient function on functions on a point set. -/
def mulFun {N : ℕ} (X : Set (Point N)) (cf : Point N → ℂ) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun f := fun w => cf w.1 * f w
  map_add' f g := by funext w; simp [mul_add]
  map_smul' a f := by funext w; simp; ring

/-- (P1) Euler step. -/
theorem euler_step' (s t u : ℕ) :
    secRank (eulerIdeal C Γ H) (s + 1) t (u + 1) +
        tripleHilbert (incidenceTriples C Γ H) s (t + 1) u =
      tripleHilbert (incidenceTriples C Γ H) (s + 1) t (u + 1) := by
  classical
  set X := tripleRepresentatives (incidenceTriples C Γ H) with hX
  rw [tripleHilbert_eq_secRank', tripleHilbert_eq_secRank']
  have hI : incIdeal C Γ H = MvPolynomial.vanishingIdeal ℂ X := rfl
  rw [hI, secRank_vanishing X, secRank_vanishing X]
  have hadd := section_add_image X (eulerIdeal C Γ H) (le_sup_left) (s + 1) t (u + 1)
  suffices hK : Module.finrank ℂ ((piece e (s + 1) t (u + 1) ⊓
      (eulerIdeal C Γ H).restrictScalars ℂ).map (evSet X)) =
      Module.finrank ℂ ((piece e s (t + 1) u).map (evSet X)) by
    omega
  obtain ⟨cf, hcf⟩ := euler_coeff_exists C Γ H
  let M := mulFun X cf
  have hEq : (piece e (s + 1) t (u + 1) ⊓ (eulerIdeal C Γ H).restrictScalars ℂ).map (evSet X) =
      ((piece e s (t + 1) u).map (evSet X)).map M := by
    apply le_antisymm
    · rintro _ ⟨f, ⟨hfP, hfE⟩, rfl⟩
      have hf' : f.IsWeightedHomogeneous (tw e)
          (HilbertMulti.tripleDegree s t u + HilbertMulti.tripleDegree 1 0 1) := by
        rw [tripleDegree_add]; exact hfP
      obtain ⟨h, hh, hdiff⟩ := homogeneous_family_decomposition (incIdeal C Γ H)
        (tripleRepresentatives_blockHomogeneous _) (eulerGen C) (eulerGen_hom C) f hf' hfE
      refine ⟨evSet X (∑ j, h j * parVar j), ⟨∑ j, h j * parVar j, ?_, rfl⟩, ?_⟩
      · apply Submodule.sum_mem
        intro j _
        have := (hh j).mul (parVar_hom j)
        rw [tripleDegree_add] at this
        simpa using this
      · funext w
        have hz := (MvPolynomial.mem_vanishingIdeal_iff.mp hdiff) w.1 w.2
        rw [map_sub, sub_eq_zero] at hz
        change cf w.1 * MvPolynomial.aeval w.1 (∑ j, h j * parVar j) = MvPolynomial.aeval w.1 f
        rw [hz]
        simp only [map_sum, map_mul, Finset.mul_sum, hcf w.1 w.2]
        apply Finset.sum_congr rfl
        intro j _
        ring
    · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨h, hh, rfl⟩ := piece_succ_decomp s t u g hg
      refine ⟨∑ j, h j * eulerGen C j, ⟨?_, ?_⟩, ?_⟩
      · apply Submodule.sum_mem
        intro j _
        have := (hh j).mul (eulerGen_hom C j)
        rw [tripleDegree_add] at this
        simpa using this
      · change _ ∈ eulerIdeal C Γ H
        apply Ideal.mem_sup_right
        apply Ideal.sum_mem
        intro j _
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
      · funext w
        change MvPolynomial.aeval w.1 (∑ j, h j * eulerGen C j) =
          cf w.1 * MvPolynomial.aeval w.1 (∑ j, h j * parVar j)
        simp only [map_sum, map_mul, Finset.mul_sum, hcf w.1 w.2]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hEq]
  have hfin := finrank_map_add_inf M ((piece e s (t + 1) u).map (evSet X))
  have hbot : ((piece e s (t + 1) u).map (evSet X) ⊓ LinearMap.ker M : Submodule ℂ (X → ℂ)) = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨⟨g, _, rfl⟩, hker⟩
    have hz : ∀ w ∈ X, cf w * MvPolynomial.aeval w g = 0 := by
      intro w hw
      exact congrFun (LinearMap.mem_ker.mp hker) ⟨w, hw⟩
    have hv := vanish_of_coeff_mul C Γ H cf hcf g hz
    rw [Submodule.mem_bot]
    funext w
    exact hv w.1 w.2
  rw [hbot, finrank_bot, add_zero] at hfin
  exact hfin

end Euler


section Pullback

/-- Splitting the variables of `Poly (a + c)` into base coefficients and fiber variables. -/
def splitHom (a c : ℕ) : Poly (a + c) →ₐ[ℂ] MvPolynomial (Fin c) (Poly a) :=
  MvPolynomial.aeval (fun i : Fin (a + c) =>
    Fin.addCases (fun j => MvPolynomial.C (MvPolynomial.X j)) (fun k => MvPolynomial.X k) i)

/-- Its inverse. -/
def joinHom (a c : ℕ) : MvPolynomial (Fin c) (Poly a) →+* Poly (a + c) :=
  MvPolynomial.eval₂Hom (MvPolynomial.rename (Fin.castAdd c)).toRingHom
    (fun k => MvPolynomial.X (Fin.natAdd a k))

theorem joinHom_splitHom (a c : ℕ) (f : Poly (a + c)) : joinHom a c (splitHom a c f) = f := by
  have h : (joinHom a c).comp (splitHom a c).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [joinHom, splitHom]
    · intro i
      refine Fin.addCases (fun j => ?_) (fun k => ?_) i
      · simp [joinHom, splitHom]
      · simp [joinHom, splitHom]
  exact congrArg (fun φ : Poly (a + c) →+* Poly (a + c) => φ f) h

theorem joinHom_C (a c : ℕ) (g : Poly a) :
    joinHom a c (MvPolynomial.C g) = MvPolynomial.rename (Fin.castAdd c) g := by
  simp [joinHom]

theorem eval_split (a c : ℕ) (b : Point a) (ξ : Point c) (f : Poly (a + c)) :
    MvPolynomial.aeval ξ (MvPolynomial.map (MvPolynomial.aeval b).toRingHom (splitHom a c f)) =
      MvPolynomial.aeval (joinPoints b ξ) f := by
  have h : ((MvPolynomial.aeval ξ).comp ((MvPolynomial.mapAlgHom (MvPolynomial.aeval b)).comp
      (splitHom a c))) = MvPolynomial.aeval (joinPoints b ξ) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [splitHom, joinPoints]
    · simp [splitHom, joinPoints]
  have := congrArg (fun φ : Poly (a + c) →ₐ[ℂ] ℂ => φ f) h
  simpa using this

/-- The pullback of a vanishing ideal is the vanishing ideal of the cylinder. -/
theorem mem_pullback_iff {a c : ℕ} (Y : Set (Point a)) (f : Poly (a + c)) :
    f ∈ Ideal.map (MvPolynomial.rename (Fin.castAdd c)) (MvPolynomial.vanishingIdeal ℂ Y) ↔
      ∀ b ∈ Y, ∀ ξ : Point c, MvPolynomial.aeval (joinPoints b ξ) f = 0 := by
  classical
  constructor
  · intro hf b hb ξ
    have hle : Ideal.map (MvPolynomial.rename (Fin.castAdd c)) (MvPolynomial.vanishingIdeal ℂ Y) ≤
        MvPolynomial.vanishingIdeal ℂ {w : Point (a + c) | ∃ b ∈ Y, ∃ ξ, w = joinPoints b ξ} := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, MvPolynomial.mem_vanishingIdeal_iff]
      rintro _ ⟨b', hb', ξ', rfl⟩
      rw [MvPolynomial.aeval_rename]
      have hcomp : (joinPoints b' ξ') ∘ (Fin.castAdd c) = b' := by
        funext j
        simp [joinPoints]
      rw [hcomp]
      exact MvPolynomial.mem_vanishingIdeal_iff.mp hg b' hb'
    exact MvPolynomial.mem_vanishingIdeal_iff.mp (hle hf) _ ⟨b, hb, ξ, rfl⟩
  · intro hf
    have hF : splitHom a c f ∈ Ideal.map (MvPolynomial.C : Poly a →+* MvPolynomial (Fin c) (Poly a))
        (MvPolynomial.vanishingIdeal ℂ Y) := by
      rw [MvPolynomial.mem_map_C_iff]
      intro m
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro b hb
      have hzero : MvPolynomial.map (MvPolynomial.aeval b).toRingHom (splitHom a c f) = 0 := by
        apply MvPolynomial.funext
        intro ξ
        have := eval_split a c b ξ f
        simp only [MvPolynomial.aeval_eq_eval] at this
        rw [this, map_zero]
        exact hf b hb ξ
      have := congrArg (fun q : MvPolynomial (Fin c) ℂ => q.coeff m) hzero
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
      exact this
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

end Pullback


section DegreeZero

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- Pieces with the same ideal part have the same section rank. -/
theorem secRank_eq_of_piece (J J' : Ideal (TPoly e)) (s t u : ℕ)
    (h : ∀ f ∈ piece e s t u, f ∈ J ↔ f ∈ J') : secRank J s t u = secRank J' s t u := by
  have h1 := finrank_map_add_inf (Ideal.Quotient.mkₐ ℂ J).toLinearMap (piece e s t u)
  have h2 := finrank_map_add_inf (Ideal.Quotient.mkₐ ℂ J').toLinearMap (piece e s t u)
  rw [ker_mkQ] at h1 h2
  have hinf : (piece e s t u ⊓ J.restrictScalars ℂ : Submodule ℂ (TPoly e)) =
      piece e s t u ⊓ J'.restrictScalars ℂ := by
    ext f
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨hf, hJ⟩; exact ⟨hf, (h f hf).mp hJ⟩
    · rintro ⟨hf, hJ⟩; exact ⟨hf, (h f hf).mpr hJ⟩
  rw [hinf] at h1
  change secRank J s t u + _ = _ at h1
  change secRank J' s t u + _ = _ at h2
  omega

/-- Point degree zero polynomials do not see the fiber coordinates. -/
theorem eval_ptdeg_zero (f : TPoly e) (s t : ℕ) (hf : f ∈ piece e s t 0)
    (b : Point (e + (e + e))) (ξ ξ' : Point (skewDim e + 1)) :
    MvPolynomial.aeval (joinPoints b ξ) f = MvPolynomial.aeval (joinPoints b ξ') f := by
  rw [piece, HilbertMulti.tripleBlockPiece, MvPolynomial.mem_restrictSupport_iff] at hf
  change MvPolynomial.eval (joinPoints b ξ) f = MvPolynomial.eval (joinPoints b ξ') f
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨_, _, hm0⟩ := hf hm
  rw [Finset.sum_eq_zero_iff] at hm0
  congr 1
  have hsplit := fun (w : Point (e + (e + e) + (skewDim e + 1))) =>
    Fin.prod_univ_add (a := e + (e + e)) (b := skewDim e + 1) (fun i => w i ^ m i)
  rw [hsplit (joinPoints b ξ), hsplit (joinPoints b ξ')]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [joinPoints]
  · apply Finset.prod_congr rfl
    intro k _
    rw [hm0 k (Finset.mem_univ k)]
    simp

theorem mem_baseIdeal_iff (f : TPoly e) :
    f ∈ baseIdeal C Γ H ↔ ∀ b ∈ pairRepresentatives (liftedParameterBase C Γ H),
      ∀ ξ : Point (skewDim e + 1), MvPolynomial.aeval (joinPoints b ξ) f = 0 :=
  mem_pullback_iff _ f

theorem baseIdeal_le_incIdeal : baseIdeal C Γ H ≤ incIdeal C Γ H := by
  intro f hf
  rw [mem_baseIdeal_iff] at hf
  rw [incIdeal, MvPolynomial.mem_vanishingIdeal_iff]
  intro w hw
  obtain ⟨d, p, x, _, _, _, hpair, _, _, _, _, _, _, rfl⟩ := incRep_cases C Γ H hw
  exact hf _ hpair x

/-- Resolution relations on the base (`v ∥ d`, `y(d) = 0`), proved in `Degree.lean`. -/
def ResolutionBase : Prop :=
  ∀ d : Point e, ∀ p : Point (e + e),
    joinPoints d p ∈ pairRepresentatives (liftedParameterBase C Γ H) →
      (∃ t : ℂ, firstPoint p = t • d) ∧ covectorOfPoint (secondPoint p) d = 0

/-- Every base point carries a nonzero fiber vector. -/
theorem fiber_point_exists (hres : ResolutionBase C Γ H) (d : Point e) (p : Point (e + e))
    (hpair : joinPoints d p ∈ pairRepresentatives (liftedParameterBase C Γ H)) :
    ∃ x : Point (skewDim e + 1), tj d p x ∈ tripleRepresentatives (incidenceTriples C Γ H) := by
  classical
  obtain ⟨hd, hp, hB⟩ := pairRep_cases hpair
  obtain ⟨⟨t, hfirst⟩, horth⟩ := hres d p hpair
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hd (funext hcon)
  let y : Module.Dual ℂ (Point e) := covectorOfPoint (secondPoint p)
  let l : Module.Dual ℂ (Point e) := (d i)⁻¹ • LinearMap.proj i
  have hl : l d = 1 := by simp [l, hi]
  let A : alternatingForms (U := Point e) :=
    ⟨IncidenceLocal.anchoredForm l y, IncidenceLocal.anchoredForm_isAlt l y⟩
  have hA : A.val d = y := IncidenceLocal.anchoredForm_evaluate d l hl y horth
  let x : Point (skewDim e + 1) := Fin.cons t (C.decode.symm A)
  have hx0 : x 0 = 1 * t := by simp [x]
  have hD : (C.decode (Fin.tail x)).val d = (1 : ℂ) • y := by
    have : Fin.tail x = C.decode.symm A := by funext k; simp [x, Fin.tail]
    rw [this, LinearEquiv.apply_symm_apply, hA, one_smul]
  have hx : x ≠ 0 := by
    intro h0
    have ht : t = 0 := by
      have := congrFun h0 0
      simpa [x] using this
    have hy : y = 0 := by
      have h1 : Fin.tail x = 0 := by rw [h0]; rfl
      have h2 : (C.decode (Fin.tail x)).val d = 0 := by rw [h1, map_zero]; rfl
      rw [hD, one_smul] at h2
      exact h2
    apply hp
    funext k
    refine Fin.addCases (fun k1 => ?_) (fun k2 => ?_) k
    · have := congrFun hfirst k1
      simp only [firstPoint, ht, zero_smul, Pi.zero_apply] at this
      simpa using this
    · have := LinearMap.congr_fun hy (Pi.single k2 1)
      simp only [y, covector_single, LinearMap.zero_apply] at this
      simpa [secondPoint] using this
  exact ⟨x, incRep_mk C Γ H d p x hd hp hx (by simpa using hB) t 1 hfirst horth hx0 hD⟩

/-- Point-degree-zero incidence elements are base elements. -/
theorem inc_ptdeg0_base (hres : ResolutionBase C Γ H) (f : TPoly e) (s t : ℕ)
    (hf : f ∈ piece e s t 0) (h : f ∈ incIdeal C Γ H) : f ∈ baseIdeal C Γ H := by
  rw [mem_baseIdeal_iff]
  intro b hb ξ
  obtain ⟨d, p, hd, hp, hB, rfl⟩ := hb
  obtain ⟨x, hx⟩ := fiber_point_exists C Γ H hres d p ⟨d, p, hd, hp, hB, rfl⟩
  rw [eval_ptdeg_zero f s t hf _ ξ x]
  exact MvPolynomial.mem_vanishingIdeal_iff.mp h _ hx

/-- (P0) -/
theorem triple_degree_zero' (hres : ResolutionBase C Γ H) (s t : ℕ) :
    tripleHilbert (incidenceTriples C Γ H) s t 0 = secRank (baseIdeal C Γ H) s t 0 := by
  rw [tripleHilbert_eq_secRank']
  symm
  apply secRank_eq_of_piece
  intro f hf
  constructor
  · intro h; exact baseIdeal_le_incIdeal C Γ H h
  · intro h
    rw [mem_baseIdeal_iff]
    intro b hb ξ
    obtain ⟨d, p, _, _, _, rfl⟩ := hb
    obtain ⟨x, hx⟩ := fiber_point_exists C Γ H hres d p ⟨d, p, by assumption, by assumption,
      by assumption, rfl⟩
    rw [eval_ptdeg_zero f s t hf _ ξ x]
    exact MvPolynomial.mem_vanishingIdeal_iff.mp h _ hx

/-- (P3₀) -/
theorem kernel_degree_zero' (s t : ℕ) :
    secRank (kernelIdeal C Γ H) s t 0 = secRank (baseIdeal C Γ H) s t 0 := by
  symm
  apply secRank_eq_of_piece
  intro f hf
  constructor
  · intro h
    exact Ideal.mem_sup_left (Ideal.mem_sup_left h)
  · intro h
    -- every generator vanishes on the zero section `x = 0` over the base
    have hvan : ∀ g ∈ kernelIdeal C Γ H, ∀ b ∈ pairRepresentatives (liftedParameterBase C Γ H),
        MvPolynomial.aeval (joinPoints b (0 : Point (skewDim e + 1))) g = 0 := by
      intro g hg b hb
      have hle : kernelIdeal C Γ H ≤ MvPolynomial.vanishingIdeal ℂ
          {w | ∃ b ∈ pairRepresentatives (liftedParameterBase C Γ H),
            w = joinPoints b (0 : Point (skewDim e + 1))} := by
        apply sup_le
        apply sup_le
        · intro g hg
          rw [MvPolynomial.mem_vanishingIdeal_iff]
          rintro _ ⟨b, hb, rfl⟩
          exact (mem_baseIdeal_iff C Γ H g).mp hg b hb 0
        · rw [Ideal.span_le]
          rintro _ rfl
          rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_iff]
          rintro _ ⟨b, _, rfl⟩
          obtain ⟨d, p, _, _, _, rfl⟩ := ‹b ∈ _›
          simp [ptVar, joinPoints]
        · rw [Ideal.span_le]
          rintro _ ⟨k, rfl⟩
          rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_iff]
          rintro _ ⟨b, hb', rfl⟩
          obtain ⟨d, p, _, _, _, rfl⟩ := hb'
          change MvPolynomial.aeval (tj d p 0) (dForm C k) = 0
          rw [eval_dForm]
          have : Fin.tail (0 : Point (skewDim e + 1)) = 0 := rfl
          rw [this, map_zero]
          rfl
      exact MvPolynomial.mem_vanishingIdeal_iff.mp (hle hg) _ ⟨b, hb, rfl⟩
    rw [mem_baseIdeal_iff]
    intro b hb ξ
    rw [eval_ptdeg_zero f s t hf b ξ 0]
    exact hvan f h b hb

end DegreeZero


section Torsion

variable {e : ℕ}

/-- Direction degree of a monomial. -/
def ddeg (m : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ) : ℕ :=
  ∑ i : Fin e, m (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))

theorem ddeg_add (m m' : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ) :
    ddeg (m + m') = ddeg m + ddeg m' := by
  simp [ddeg, Finset.sum_add_distrib]

theorem weight_zero_eq_ddeg (m : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ) :
    (Finsupp.weight (tw e) m) 0 = ddeg m := by
  rw [HilbertMulti.weight_blockWeight, HilbertMulti.mapDomain_fin_apply]
  simp [Fin.sum_univ_add, HilbertMulti.tripleBlocks, ddeg]

/-- A monomial of large direction degree is divisible by a large power of one direction. -/
theorem monomial_high (N : ℕ) (m : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ)
    (hm : e * N + 1 ≤ ddeg m) (c : ℂ) :
    ∃ i : Fin e, ∃ q : TPoly e, MvPolynomial.monomial m c = dirVar i ^ N * q := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin e, N < m (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) := by
    by_contra h
    push Not at h
    have : ddeg m ≤ e * N := by
      calc ddeg m ≤ ∑ _i : Fin e, N := Finset.sum_le_sum (fun i _ => h i)
        _ = e * N := by simp
    omega
  let a := Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)
  refine ⟨i, MvPolynomial.monomial (m - Finsupp.single a N) c, ?_⟩
  have hle : Finsupp.single a N ≤ m := Finsupp.single_le_iff.mpr (le_of_lt hi)
  rw [dirVar, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul,
    add_tsub_cancel_of_le hle]

/-- Rank equality for large direction degree from elementwise direction torsion. -/
theorem torsion_compare (J J' : Ideal (TPoly e))
    (hJ : J.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)))
    (hle : J ≤ J') (htor : ∀ f ∈ J', ∀ i : Fin e, ∃ N : ℕ, dirVar i ^ N * f ∈ J) :
    ∃ N0 : ℕ, ∀ s t u : ℕ, N0 ≤ s → secRank J s t u = secRank J' s t u := by
  classical
  obtain ⟨G0, hG0⟩ := (IsNoetherian.noetherian J' : J'.FG)
  have hmemG : ∀ g ∈ G0, g ∈ J' := by
    intro g hg
    rw [← hG0]
    exact Submodule.subset_span hg
  have hex : ∀ p : G0 × Fin e, ∃ N : ℕ, dirVar p.2 ^ N * (p.1 : TPoly e) ∈ J :=
    fun p => htor p.1 (hmemG p.1 p.1.2) p.2
  choose Nf hNf using hex
  let N := Finset.univ.sup Nf
  have hunif : ∀ f ∈ J', ∀ i : Fin e, dirVar i ^ N * f ∈ J := by
    intro f hf i
    have hcolon : J' ≤ J.colon {dirVar i ^ N} := by
      rw [← hG0, Submodule.span_le]
      intro g hg
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]
      have hle' : Nf (⟨g, hg⟩, i) ≤ N := Finset.le_sup (f := Nf) (Finset.mem_univ _)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle'
      have h' := J.mul_mem_left (dirVar i ^ k) (hNf (⟨g, hg⟩, i))
      rw [hk, pow_add]
      convert h' using 1
      simp only
      ring
    have := hcolon hf
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at this
    rw [mul_comm]
    exact this
  let D := G0.sup (fun g => g.support.sup ddeg)
  refine ⟨e * N + 1 + D + 1, ?_⟩
  intro s t u hs
  apply secRank_eq_of_piece
  intro f hf
  refine ⟨fun h => hle h, fun h => ?_⟩
  -- write `f` as a combination of the generators
  rw [← hG0] at h
  obtain ⟨c, _, hc⟩ := Submodule.mem_span_finset.mp h
  let low : TPoly e → TPoly e := fun a =>
    ∑ m ∈ a.support.filter (fun m => ddeg m < e * N + 1), MvPolynomial.monomial m (a.coeff m)
  let high : TPoly e → TPoly e := fun a =>
    ∑ m ∈ a.support.filter (fun m => ¬ ddeg m < e * N + 1), MvPolynomial.monomial m (a.coeff m)
  have hsplit : ∀ a : TPoly e, a = low a + high a := by
    intro a
    conv_lhs => rw [a.as_sum]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  let flow := ∑ g ∈ G0, low (c g) * g
  have hhigh : f - flow ∈ J := by
    have : f - flow = ∑ g ∈ G0, high (c g) * g := by
      rw [← hc]
      simp only [flow, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro g _
      have hs := hsplit (c g)
      calc c g * g - low (c g) * g = (low (c g) + high (c g)) * g - low (c g) * g := by
            rw [← hs]
        _ = high (c g) * g := by ring
    rw [this]
    apply Ideal.sum_mem
    intro g hg
    simp only [high, Finset.sum_mul]
    apply Ideal.sum_mem
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨i, q, hq⟩ := monomial_high N m (by omega) ((c g).coeff m)
    rw [hq, mul_comm (dirVar i ^ N) q, mul_assoc]
    exact J.mul_mem_left _ (hunif g (hmemG g hg) i)
  have hlowsupp : ∀ m ∈ flow.support, ddeg m ≤ e * N + D := by
    intro m hm
    have h1 := MvPolynomial.support_sum hm
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g, hg, h2⟩ := h1
    have h3 := MvPolynomial.support_mul _ _ h2
    rw [Finset.mem_add] at h3
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := h3
    rw [ddeg_add]
    have hm1' : ddeg m1 < e * N + 1 := by
      have h4 := MvPolynomial.support_sum hm1
      rw [Finset.mem_biUnion] at h4
      obtain ⟨m0, hm0, h5⟩ := h4
      rw [Finset.mem_filter] at hm0
      by_cases hc0 : (c g).coeff m0 = 0
      · rw [MvPolynomial.support_monomial, if_pos hc0] at h5
        exact absurd h5 (Finset.notMem_empty _)
      · rw [MvPolynomial.support_monomial, if_neg hc0, Finset.mem_singleton] at h5
        rw [h5]; exact hm0.2
    have hm2' : ddeg m2 ≤ D := by
      have h6 : ddeg m2 ≤ g.support.sup ddeg := Finset.le_sup (f := ddeg) hm2
      exact h6.trans (Finset.le_sup (f := fun g : TPoly e => g.support.sup ddeg) hg)
    omega
  have hcomp0 : MvPolynomial.weightedHomogeneousComponent (tw e)
      (HilbertMulti.tripleDegree s t u) flow = 0 := by
    ext m
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
    split_ifs with hw
    · by_contra hne
      have hm : m ∈ flow.support := MvPolynomial.mem_support_iff.mpr hne
      have h1 := hlowsupp m hm
      have h2 : ddeg m = s := by
        rw [← weight_zero_eq_ddeg, hw]
        simp [HilbertMulti.tripleDegree]
      omega
    · rfl
  have hfself : MvPolynomial.weightedHomogeneousComponent (tw e)
      (HilbertMulti.tripleDegree s t u) f = f :=
    MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hf
  have : f = MvPolynomial.weightedHomogeneousComponent (tw e)
      (HilbertMulti.tripleDegree s t u) (f - flow) := by
    rw [map_sub, hfself, hcomp0, sub_zero]
  rw [this]
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem ℂ (tw e) hJ hhigh _

end Torsion


section Homogeneity

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- The cylinder over the base. -/
def baseCyl : Set (Point (e + (e + e) + (skewDim e + 1))) :=
  {w | ∃ b ∈ pairRepresentatives (liftedParameterBase C Γ H), ∃ ξ : Point (skewDim e + 1),
    w = joinPoints b ξ}

theorem baseIdeal_eq_vanishing :
    baseIdeal C Γ H = MvPolynomial.vanishingIdeal ℂ (baseCyl C Γ H) := by
  ext f
  rw [mem_baseIdeal_iff, MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · rintro h _ ⟨b, hb, ξ, rfl⟩
    exact h b hb ξ
  · intro h b hb ξ
    exact h _ ⟨b, hb, ξ, rfl⟩

theorem baseIdeal_hom :
    (baseIdeal C Γ H).IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) := by
  rw [baseIdeal_eq_vanishing]
  apply HilbertMulti.vanishingIdeal_blockHomogeneous
  rintro _ ⟨b, hb, ξ, rfl⟩ c hc
  have h1 := pairRepresentatives_left_smul _ hb (hc 0)
  have h2 := pairRepresentatives_right_smul _ h1 (hc 1)
  refine ⟨_, h2, c 2 • ξ, ?_⟩
  funext k
  refine Fin.addCases (fun k1 => ?_) (fun k2 => ?_) k
  · refine Fin.addCases (fun k3 => ?_) (fun k4 => ?_) k1
    · simp [joinPoints, firstPoint, secondPoint, HilbertMulti.tripleBlocks, smul_eq_mul]
    · simp [joinPoints, firstPoint, secondPoint, HilbertMulti.tripleBlocks, smul_eq_mul]
  · simp [joinPoints, HilbertMulti.tripleBlocks, smul_eq_mul]

theorem span_hom {ι : Type*} (g : ι → TPoly e) (w0 : Fin 3 →₀ ℕ)
    (hg : ∀ k, (g k).IsWeightedHomogeneous (tw e) w0) :
    (Ideal.span (Set.range g)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨k, rfl⟩
  exact ⟨w0, hg k⟩

theorem incIdeal_hom :
    (incIdeal C Γ H).IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) :=
  tripleRepresentatives_blockHomogeneous _

theorem eulerIdeal_hom :
    (eulerIdeal C Γ H).IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) :=
  (incIdeal_hom C Γ H).sup (span_hom (eulerGen C) _ (eulerGen_hom C))

theorem kernelIdeal_hom :
    (kernelIdeal C Γ H).IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) := by
  have h0 : (Ideal.span {ptVar (e := e) 0}).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)) := by
    have := span_hom (fun _ : Unit => ptVar (e := e) 0) _ (fun _ => ptVar_hom 0)
    simpa using this
  exact ((baseIdeal_hom C Γ H).sup h0).sup (span_hom (dForm C) _ (dForm_hom C))

/-- Scaling the fiber coordinates scales a point-degree-`u` polynomial by `λ^u`. -/
theorem eval_ptdeg_scale (f : TPoly e) (s t u : ℕ) (hf : f ∈ piece e s t u)
    (b : Point (e + (e + e))) (ξ : Point (skewDim e + 1)) (a : ℂ) :
    MvPolynomial.aeval (joinPoints b (a • ξ)) f = a ^ u * MvPolynomial.aeval (joinPoints b ξ) f := by
  rw [piece, HilbertMulti.tripleBlockPiece, MvPolynomial.mem_restrictSupport_iff] at hf
  change MvPolynomial.eval (joinPoints b (a • ξ)) f = a ^ u * MvPolynomial.eval (joinPoints b ξ) f
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨_, _, hmu⟩ := hf hm
  have hsplit := fun (w : Point (e + (e + e) + (skewDim e + 1))) =>
    Fin.prod_univ_add (a := e + (e + e)) (b := skewDim e + 1) (fun i => w i ^ m i)
  rw [hsplit (joinPoints b (a • ξ)), hsplit (joinPoints b ξ)]
  have hx : (∏ k : Fin (skewDim e + 1), joinPoints b (a • ξ) (Fin.natAdd (e + (e + e)) k) ^
      m (Fin.natAdd (e + (e + e)) k)) = a ^ u * ∏ k : Fin (skewDim e + 1),
        joinPoints b ξ (Fin.natAdd (e + (e + e)) k) ^ m (Fin.natAdd (e + (e + e)) k) := by
    simp only [joinPoints, Fin.addCases_right, Pi.smul_apply, smul_eq_mul, mul_pow,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hmu]
  have hb : (∏ k : Fin (e + (e + e)), joinPoints b (a • ξ) (Fin.castAdd (skewDim e + 1) k) ^
      m (Fin.castAdd (skewDim e + 1) k)) = ∏ k : Fin (e + (e + e)),
        joinPoints b ξ (Fin.castAdd (skewDim e + 1) k) ^ m (Fin.castAdd (skewDim e + 1) k) := by
    simp [joinPoints]
  rw [hx, hb]
  ring

/-- Agreement of algebra maps on generators modulo an ideal. -/
theorem algHom_sub_mem {N : ℕ} (φ ψ : Poly N →ₐ[ℂ] Poly N) (I : Ideal (Poly N))
    (h : ∀ a, φ (MvPolynomial.X a) - ψ (MvPolynomial.X a) ∈ I) (f : Poly N) :
    φ f - ψ f ∈ I := by
  have heq : (Ideal.Quotient.mkₐ ℂ I).comp φ = (Ideal.Quotient.mkₐ ℂ I).comp ψ := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (h a)
  have := congrArg (fun χ : Poly N →ₐ[ℂ] Poly N ⧸ I => χ f) heq
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  exact Ideal.Quotient.eq.mp this

end Homogeneity


section Substitution

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- The alternating form `l ∧ y`. -/
def anchAlt (l y : Module.Dual ℂ (Point e)) : alternatingForms (U := Point e) :=
  ⟨IncidenceLocal.anchoredForm l y, IncidenceLocal.anchoredForm_isAlt l y⟩

/-- Coordinates of `e_i^* ∧ e_k^*`. -/
def alphaC (i : Fin e) (kk : Fin (skewDim e)) (k : Fin e) : ℂ :=
  (C.decode.symm (anchAlt (LinearMap.proj i) (LinearMap.proj k))) kk

/-- Scaling the point variables by `d_i`. -/
def scaleHom (i : Fin e) : TPoly e →ₐ[ℂ] TPoly e :=
  MvPolynomial.aeval (fun a : Fin (e + (e + e) + (skewDim e + 1)) =>
    Fin.addCases (fun b => MvPolynomial.X (Fin.castAdd (skewDim e + 1) b))
      (fun k => dirVar i * MvPolynomial.X (Fin.natAdd (e + (e + e)) k)) a)

/-- The kernel projection `x0 ↦ 0`, `z ↦ ρ_i z = d_i z − e_i^* ∧ ι_d z`. -/
def rhoHom (i : Fin e) : TPoly e →ₐ[ℂ] TPoly e :=
  MvPolynomial.aeval (fun a : Fin (e + (e + e) + (skewDim e + 1)) =>
    Fin.addCases (fun b => MvPolynomial.X (Fin.castAdd (skewDim e + 1) b))
      (fun k : Fin (skewDim e + 1) => Fin.cases (0 : TPoly e)
        (fun kk => dirVar i * ptVar (Fin.succ kk) -
          ∑ k' : Fin e, MvPolynomial.C (alphaC C i kk k') * dForm C k') k) a)

theorem joinPoints_split (w : Point (e + (e + e) + (skewDim e + 1))) :
    w = joinPoints (fun b => w (Fin.castAdd (skewDim e + 1) b))
      (fun k => w (Fin.natAdd (e + (e + e)) k)) := by
  funext a
  refine Fin.addCases (fun b => ?_) (fun k => ?_) a
  · simp [joinPoints]
  · simp [joinPoints]

theorem scaleHom_eq (i : Fin e) (f : TPoly e) (s t u : ℕ) (hf : f ∈ piece e s t u) :
    scaleHom i f = dirVar i ^ u * f := by
  apply MvPolynomial.funext
  intro w
  have h1 := MvPolynomial.comp_aeval_apply (MvPolynomial.aeval w) f
    (f := fun a : Fin (e + (e + e) + (skewDim e + 1)) =>
      Fin.addCases (fun b => MvPolynomial.X (Fin.castAdd (skewDim e + 1) b))
        (fun k => dirVar i * MvPolynomial.X (Fin.natAdd (e + (e + e)) k)) a)
  simp only [MvPolynomial.aeval_eq_eval] at h1
  change MvPolynomial.eval w (scaleHom i f) = _
  unfold scaleHom
  rw [h1]
  have hpt : (fun a : Fin (e + (e + e) + (skewDim e + 1)) => MvPolynomial.eval w
      (Fin.addCases (fun b => MvPolynomial.X (Fin.castAdd (skewDim e + 1) b))
        (fun k => dirVar i * MvPolynomial.X (Fin.natAdd (e + (e + e)) k)) a)) =
      joinPoints (fun b => w (Fin.castAdd (skewDim e + 1) b))
        (w (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) •
          (fun k => w (Fin.natAdd (e + (e + e)) k))) := by
    funext a
    refine Fin.addCases (fun b => ?_) (fun k => ?_) a
    · simp [joinPoints]
    · simp [joinPoints, dirVar]
  rw [hpt]
  have h2 := eval_ptdeg_scale f s t u hf (fun b => w (Fin.castAdd (skewDim e + 1) b))
    (fun k => w (Fin.natAdd (e + (e + e)) k)) (w (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)))
  simp only [MvPolynomial.aeval_eq_eval] at h2
  rw [h2, ← joinPoints_split, map_mul, map_pow]
  simp [dirVar]

theorem scale_sub_rho_mem (i : Fin e) (f : TPoly e) :
    scaleHom i f - rhoHom C i f ∈
      Ideal.span {ptVar (e := e) 0} ⊔ Ideal.span (Set.range (dForm C)) := by
  apply algHom_sub_mem
  intro a
  refine Fin.addCases (fun b => ?_) (fun k => ?_) a
  · simp [scaleHom, rhoHom]
  · refine Fin.cases ?_ (fun kk => ?_) k
    · simp only [scaleHom, rhoHom, MvPolynomial.aeval_X, Fin.addCases_right, Fin.cases_zero,
        sub_zero]
      apply Ideal.mem_sup_left
      rw [mul_comm]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · simp only [scaleHom, rhoHom, MvPolynomial.aeval_X, Fin.addCases_right, Fin.cases_succ]
      apply Ideal.mem_sup_right
      have : dirVar i * MvPolynomial.X (Fin.natAdd (e + (e + e)) kk.succ) -
          (dirVar i * ptVar kk.succ - ∑ k' : Fin e, MvPolynomial.C (alphaC C i kk k') * dForm C k') =
          ∑ k' : Fin e, MvPolynomial.C (alphaC C i kk k') * dForm C k' := by
        simp [ptVar]
      rw [this]
      apply Ideal.sum_mem
      intro k' _
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k', rfl⟩)

/-- The substituted fiber vector. -/
def rhoVec (i : Fin e) (d : Point e) (ξ : Point (skewDim e + 1)) : Point (skewDim e + 1) :=
  Fin.cons 0 (d i • Fin.tail ξ - ∑ k' : Fin e,
    ((C.decode (Fin.tail ξ)).val d (Pi.single k' 1)) •
      C.decode.symm (anchAlt (LinearMap.proj i) (LinearMap.proj k')))

theorem rho_eval (i : Fin e) (d : Point e) (p : Point (e + e)) (ξ : Point (skewDim e + 1))
    (f : TPoly e) :
    MvPolynomial.aeval (tj d p ξ) (rhoHom C i f) = MvPolynomial.aeval (tj d p (rhoVec C i d ξ)) f := by
  unfold rhoHom
  rw [MvPolynomial.comp_aeval_apply]
  congr 1
  congr 1
  funext a
  refine Fin.addCases (fun b => ?_) (fun k => ?_) a
  · simp [tj, joinPoints]
  · refine Fin.cases ?_ (fun kk => ?_) k
    · simp [tj, joinPoints, rhoVec]
    · simp only [Fin.addCases_right, Fin.cases_succ, map_sub, map_mul, map_sum,
        MvPolynomial.aeval_C, eval_dirVar, eval_ptVar, eval_dForm, Algebra.algebraMap_self,
        RingHom.id_apply]
      simp [tj, joinPoints, rhoVec, alphaC, Fin.tail, Finset.sum_apply, mul_comm]

theorem rho_kernel (i : Fin e) (d : Point e) (ξ : Point (skewDim e + 1)) :
    (C.decode (Fin.tail (rhoVec C i d ξ))).val d = 0 := by
  have htail : Fin.tail (rhoVec C i d ξ) = d i • Fin.tail ξ - ∑ k' : Fin e,
      ((C.decode (Fin.tail ξ)).val d (Pi.single k' 1)) •
        C.decode.symm (anchAlt (LinearMap.proj i) (LinearMap.proj k')) := by
    funext k; simp [rhoVec, Fin.tail]
  rw [htail]
  set D := C.decode (Fin.tail ξ) with hD
  have hDd : D.val d d = 0 := D.2 d
  have hexp : ∀ w : Point e, D.val d w = ∑ k' : Fin e, w k' * D.val d (Pi.single k' 1) := by
    intro w
    conv_lhs => rw [show w = ∑ k' : Fin e, w k' • (Pi.single k' (1 : ℂ) : Point e) by
      simpa using ((Pi.basisFun ℂ (Fin e)).sum_repr w).symm]
    simp [map_sum, map_smul, smul_eq_mul]
  refine LinearMap.ext (fun w => ?_)
  simp only [map_sub, map_smul, map_sum, LinearEquiv.apply_symm_apply, Submodule.coe_sub,
    Submodule.coe_smul, Submodule.coe_sum, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul, LinearMap.zero_apply]
  simp only [anchAlt, IncidenceLocal.anchoredForm, LinearMap.sub_apply,
    LinearMap.BilinForm.linMulLin_apply, LinearMap.proj_apply]
  have h1 : (∑ k' : Fin e, D.val d (Pi.single k' 1) * (d i * w k' - d k' * w i)) =
      d i * (∑ k' : Fin e, w k' * D.val d (Pi.single k' 1)) -
        w i * (∑ k' : Fin e, d k' * D.val d (Pi.single k' 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k' _; ring
  rw [h1, ← hexp w, ← hexp d, hDd]
  ring

/-- Core of (P2): `d_i^u f ∈ kernelIdeal` for an incidence element of point degree `u ≥ 1`. -/
theorem dir_pow_mem_kernel (hres : ResolutionBase C Γ H) (i : Fin e) (f : TPoly e) (s t u : ℕ)
    (hf : f ∈ piece e s t u) (hinc : f ∈ incIdeal C Γ H) :
    dirVar i ^ u * f ∈ kernelIdeal C Γ H := by
  rcases Nat.eq_zero_or_pos u with hu | hu
  · subst hu
    rw [pow_zero, one_mul]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (inc_ptdeg0_base C Γ H hres f s t hf hinc))
  rw [← scaleHom_eq i f s t u hf]
  have hsplit : scaleHom i f = (scaleHom i f - rhoHom C i f) + rhoHom C i f := by ring
  rw [hsplit]
  apply Ideal.add_mem
  · have := scale_sub_rho_mem C i f
    have hle : Ideal.span {ptVar (e := e) 0} ⊔ Ideal.span (Set.range (dForm C)) ≤
        kernelIdeal C Γ H := by
      apply sup_le
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    exact hle this
  · apply Ideal.mem_sup_left
    apply Ideal.mem_sup_left
    rw [mem_baseIdeal_iff]
    intro b hb ξ
    obtain ⟨d, p, hd, hp, hB, rfl⟩ := hb
    have hpair : joinPoints d p ∈ pairRepresentatives (liftedParameterBase C Γ H) :=
      ⟨d, p, hd, hp, hB, rfl⟩
    change MvPolynomial.aeval (tj d p ξ) (rhoHom C i f) = 0
    rw [rho_eval]
    by_cases hz : rhoVec C i d ξ = 0
    · rw [hz]
      have := eval_ptdeg_scale f s t u hf (joinPoints d p) 0 0
      rw [zero_smul] at this
      change MvPolynomial.aeval (joinPoints (joinPoints d p) 0) f = 0
      rw [this, zero_pow (Nat.pos_iff_ne_zero.mp hu), zero_mul]
    · obtain ⟨⟨t0, hfirst⟩, horth⟩ := hres d p hpair
      have hmem := incRep_mk C Γ H d p (rhoVec C i d ξ) hd hp hz hB t0 0 hfirst horth
        (by simp [rhoVec]) (by rw [rho_kernel, zero_smul])
      exact MvPolynomial.mem_vanishingIdeal_iff.mp hinc _ hmem

/-- `d_i^N f ∈ kernelIdeal` for every incidence element. -/
theorem dir_pow_mem_kernel_all (hres : ResolutionBase C Γ H) (i : Fin e) (f : TPoly e)
    (hinc : f ∈ incIdeal C Γ H) : ∃ N : ℕ, dirVar i ^ N * f ∈ kernelIdeal C Γ H := by
  classical
  let 𝒜 := MvPolynomial.weightedHomogeneousSubmodule ℂ (tw e)
  let S := (DirectSum.decompose 𝒜 f).support
  refine ⟨S.sup (fun d => d 2), ?_⟩
  rw [← DirectSum.sum_support_decompose 𝒜 f, Finset.mul_sum]
  apply Ideal.sum_mem
  intro d hd
  have hcomp : (DirectSum.decompose 𝒜 f d : TPoly e) ∈ incIdeal C Γ H :=
    (Ideal.IsHomogeneous.mem_iff 𝒜 (incIdeal_hom C Γ H)).mp hinc d
  have hdeg : d = HilbertMulti.tripleDegree (d 0) (d 1) (d 2) := by
    apply Finsupp.ext; intro j; fin_cases j <;> simp [HilbertMulti.tripleDegree]
  have h𝒜 : 𝒜 d = piece e (d 0) (d 1) (d 2) := by
    show 𝒜 d = 𝒜 (HilbertMulti.tripleDegree (d 0) (d 1) (d 2))
    congr 1
  have hpiece : (DirectSum.decompose 𝒜 f d : TPoly e) ∈ piece e (d 0) (d 1) (d 2) :=
    h𝒜 ▸ (DirectSum.decompose 𝒜 f d).2
  have hle : d 2 ≤ S.sup (fun d => d 2) := Finset.le_sup (f := fun d => d 2) hd
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, pow_add, mul_comm (dirVar i ^ d 2), mul_assoc]
  exact Ideal.mul_mem_left _ _ (dir_pow_mem_kernel C Γ H hres i _ _ _ _ hpiece hcomp)

/-- (P2) -/
theorem euler_kernel_compare' (hres : ResolutionBase C Γ H) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s →
      secRank (eulerIdeal C Γ H) s t u = secRank (kernelIdeal C Γ H) s t u := by
  classical
  let J'' := eulerIdeal C Γ H ⊔ kernelIdeal C Γ H
  have hKE : ∀ i : Fin e, kernelIdeal C Γ H ≤ (eulerIdeal C Γ H).colon {dirVar i} := by
    intro i
    apply sup_le
    apply sup_le
    · intro g hg
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_sup_left (baseIdeal_le_incIdeal C Γ H hg))
    · rw [Ideal.span_le]
      rintro _ rfl
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]
      apply Ideal.mem_sup_right
      apply Ideal.subset_span
      exact ⟨Fin.castAdd e i, by simp [eulerGen]⟩
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]
      apply Ideal.mul_mem_right
      apply Ideal.mem_sup_right
      apply Ideal.subset_span
      exact ⟨Fin.natAdd e k, by simp only [eulerGen, Fin.addCases_right]⟩
  obtain ⟨N1, h1⟩ := torsion_compare (eulerIdeal C Γ H) J'' (eulerIdeal_hom C Γ H) le_sup_left
    (by
      intro f hf i
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
      refine ⟨1, ?_⟩
      rw [pow_one, mul_add]
      apply Ideal.add_mem
      · exact Ideal.mul_mem_left _ _ ha
      · have := hKE i hb
        rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] at this
        exact this)
  have hπK : Ideal.span (Set.range (eulerGen C)) ≤ kernelIdeal C Γ H := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · simp only [eulerGen, Fin.addCases_left, SetLike.mem_coe]
      exact Ideal.mem_sup_left (Ideal.mem_sup_right
        (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
    · simp only [eulerGen, Fin.addCases_right, SetLike.mem_coe]
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  obtain ⟨N2, h2⟩ := torsion_compare (kernelIdeal C Γ H) J'' (kernelIdeal_hom C Γ H) le_sup_right
    (by
      intro f hf i
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
      obtain ⟨a1, ha1, a2, ha2, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨N, hN⟩ := dir_pow_mem_kernel_all C Γ H hres i a1 ha1
      refine ⟨N, ?_⟩
      rw [mul_add, mul_add]
      refine Ideal.add_mem _ (Ideal.add_mem _ hN ?_) (Ideal.mul_mem_left _ _ hb)
      exact Ideal.mul_mem_left _ _ (hπK ha2))
  refine ⟨max N1 N2, fun s t u hs => ?_⟩
  rw [h1 s t u (le_trans (le_max_left _ _) hs), h2 s t u (le_trans (le_max_right _ _) hs)]

end Substitution

end
end TripleRankRoute
end DistinctDistances.TrackB
