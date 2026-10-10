import DistinctDistances.TrackB.GeometryModel

namespace DistinctDistances.TrackB

set_option autoImplicit false
noncomputable section
open LinearMap (BilinForm)

def segreVector {n m : ℕ} (x : Point n) (y : Point m) : Point (n * m) :=
  fun k => x (finProdFinEquiv.symm k).1 * y (finProdFinEquiv.symm k).2

theorem segreVector_ne_zero {n m : ℕ} (x : Point n) (y : Point m)
    (hx : x ≠ 0) (hy : y ≠ 0) : segreVector x y ≠ 0 := by
  intro hzero
  have hx' : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    funext i
    exact h i
  have hy' : ∃ j, y j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    funext j
    exact h j
  obtain ⟨i, hi⟩ := hx'
  obtain ⟨j, hj⟩ := hy'
  have hcoord := congrFun hzero (finProdFinEquiv (i, j))
  have hmul : x i * y j = 0 := by
    simpa [segreVector] using hcoord
  rcases mul_eq_zero.mp hmul with hi0 | hj0
  · exact hi hi0
  · exact hj hj0

def segrePoint {n m : ℕ} (p : ProjectivePoint n) (q : ProjectivePoint m) :
    ProjectivePoint (n * m) :=
  Projectivization.mk ℂ (segreVector p.rep q.rep)
    (segreVector_ne_zero _ _ p.rep_nonzero q.rep_nonzero)

def pairClosure {n m : ℕ} (T : Set (ProjectivePoint n × ProjectivePoint m)) :
    ProjectiveVariety (n * m) :=
  ProjectiveVariety.closure {w | ∃ p q, (p, q) ∈ T ∧ segrePoint p q = w}

def closedPairs {n m : ℕ} (T : Set (ProjectivePoint n × ProjectivePoint m)) :
    Set (ProjectivePoint n × ProjectivePoint m) :=
  {w | segrePoint w.1 w.2 ∈ pairClosure T}

/-- B=P(O⊕Q*(1)), in its second presentation, as an actual closed projective relation. -/
def resolutionPairs (e : ℕ) : Set (ProjectivePoint e × ProjectivePoint (e + e)) :=
  {w | ∃ t : ℂ, firstPoint w.2.rep = t • w.1.rep ∧
    covectorOfPoint (secondPoint w.2.rep) w.1.rep = 0}

def parameterResolution (e : ℕ) : ProjectiveVariety (e * (e + e)) :=
  pairClosure (resolutionPairs e)

def liftedParameterPairs {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    Set (ProjectivePoint e × ProjectivePoint (e + e)) :=
  {w | ∃ z v, joinPoints z v ∈ rulingPoints Γ H ∧ ∃ hv : v ≠ 0,
    w.1 = Projectivization.mk ℂ v hv ∧ w.2 = graphParameter C z v hv}

def liftedParameterBase {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :=
  closedPairs (liftedParameterPairs C Γ H)

/-- The explicit inverse-image fiber condition defining P(U); t=0 is included. -/
def incidenceCondition {e : ℕ} (C : SkewCoordinates e)
    (d : ProjectivePoint e) (p : ProjectivePoint (e + e))
    (x : ProjectivePoint (skewDim e + 1)) : Prop :=
  ∃ t : ℂ, firstPoint p.rep = t • d.rep ∧
    covectorOfPoint (secondPoint p.rep) d.rep = 0 ∧
    (x.rep 0, C.decode (Fin.tail x.rep)) ∈
      incidenceFiber d.rep t (covectorOfPoint (secondPoint p.rep))

def incidenceTriples {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    Set ((ProjectivePoint e × ProjectivePoint (e + e)) × ProjectivePoint (skewDim e + 1)) :=
  {w | w.1 ∈ liftedParameterBase C Γ H ∧ incidenceCondition C w.1.1 w.1.2 w.2}

def tripleClosure {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) :
    ProjectiveVariety ((n * m) * o) :=
  ProjectiveVariety.closure {w | ∃ p q x, ((p, q), x) ∈ T ∧
    segrePoint (segrePoint p q) x = w}

def compactIncidence {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :=
  tripleClosure (incidenceTriples C Γ H)

def incidencePointImage {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    Set (ProjectivePoint (skewDim e + 1)) :=
  {x | ∃ d p, segrePoint (segrePoint d p) x ∈ compactIncidence C Γ H}

/-- B03, conc:deg-parameter-bundle: the local tensor twist with a chosen generator. -/
theorem tensor_twist_fiber {e : ℕ} (v : Point e) (hv : v ≠ 0) :
    ∃ φ : (ℂ × (Submodule.span ℂ {v}).dualAnnihilator) ≃ₗ[ℂ]
      ((Submodule.span ℂ {v}) × (Submodule.span ℂ {v}).dualAnnihilator),
      ∀ t y, (φ (t, y)).1.val = t • v ∧ (φ (t, y)).2 = y := by
  let f : ℂ ≃ₗ[ℂ] Submodule.span ℂ {v} :=
    LinearEquiv.toSpanNonzeroSingleton ℂ (Point e) v hv
  refine ⟨f.prodCongr (LinearEquiv.refl ℂ _), ?_⟩
  intro t y
  constructor <;> simp [f]

/-- B04, conc:deg-parameter-map: the resolution has a unique lift over Q°. -/
theorem parameterResolution_open (e : ℕ) (p : ProjectivePoint (e + e))
    (hp : p ∈ affineParameters e) :
    ∃! d : ProjectivePoint e, (d, p) ∈ resolutionPairs e := by
  change parameterValue p.rep = 0 ∧ firstPoint p.rep ≠ 0 at hp
  rcases hp with ⟨hpquad, hv⟩
  let v : Point e := firstPoint p.rep
  let y : Module.Dual ℂ (Point e) := covectorOfPoint (secondPoint p.rep)
  have hquad : y v = 0 := by simpa [y, v, parameterValue] using hpquad
  let d : ProjectivePoint e := Projectivization.mk ℂ v hv
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  let b : ℂ := (a⁻¹ : ℂˣ)
  have hba : b * (a : ℂ) = 1 := by simp [b]
  have hfirst : v = b • d.rep := by
    calc
      v = (1 : ℂ) • v := by simp
      _ = (b * (a : ℂ)) • v := by rw [hba]
      _ = b • ((a : ℂ) • v) := by rw [mul_smul]
      _ = b • d.rep := congrArg (fun x => b • x) ha
  have hy : y d.rep = 0 := by
    rw [← ha]
    simp [y, hquad]
  have hd : (d, p) ∈ resolutionPairs e := by
    change ∃ t, v = t • d.rep ∧ y d.rep = 0
    exact ⟨b, hfirst, hy⟩
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  change ∃ t, v = t • d'.rep ∧ y d'.rep = 0 at hd'
  obtain ⟨c, hc, _⟩ := hd'
  have hcne : c ≠ 0 := by
    intro hczero
    apply hv
    calc
      v = c • d'.rep := hc
      _ = 0 := by simp [hczero]
  have hrel : c • d'.rep = b • d.rep := hc.symm.trans hfirst
  have hrep : d'.rep = (c⁻¹ * b) • d.rep := by
    calc
      d'.rep = (1 : ℂ) • d'.rep := by simp
      _ = (c⁻¹ * c) • d'.rep := by simp [hcne]
      _ = c⁻¹ • (c • d'.rep) := by rw [mul_smul]
      _ = c⁻¹ • (b • d.rep) := by rw [hrel]
      _ = (c⁻¹ * b) • d.rep := by rw [mul_smul]
  have hproj : Projectivization.mk ℂ d'.rep d'.rep_nonzero =
      Projectivization.mk ℂ d.rep d.rep_nonzero := by
    apply (Projectivization.mk_eq_mk_iff' ℂ d'.rep d.rep
      d'.rep_nonzero d.rep_nonzero).2
    exact ⟨c⁻¹ * b, hrep.symm⟩
  calc
    d' = Projectivization.mk ℂ d'.rep d'.rep_nonzero :=
      (Projectivization.mk_rep d').symm
    _ = Projectivization.mk ℂ d.rep d.rep_nonzero := hproj
    _ = d := Projectivization.mk_rep d

/-- B04's boundary fiber P(ker y). -/
theorem parameterResolution_boundary (e : ℕ) (p : ProjectivePoint (e + e))
    (hp : firstPoint p.rep = 0) :
    {d | (d, p) ∈ resolutionPairs e} =
      {d : ProjectivePoint e | covectorOfPoint (secondPoint p.rep) d.rep = 0} := by
  ext d
  simp only [Set.mem_setOf_eq, resolutionPairs]
  constructor
  · rintro ⟨t, ht, hy⟩
    exact hy
  · intro hy
    refine ⟨0, ?_, hy⟩
    simpa [hp]

def firstPresentationVector {e : ℕ} (v : Point e) (t : ℂ)
    (y : Module.Dual ℂ (Point e)) : Point (e + e) := joinPoints (t • v) (pointOfCovector y)

/-- B05, conc:deg-hyperplane: the representative has bidegree (1,1), so ell=a+b. -/
theorem hyperplane_transition {e : ℕ} (v : Point e) (t α β : ℂ)
    (y : Module.Dual ℂ (Point e)) :
    firstPresentationVector (β • v) (α * t) ((α * β) • y) =
      (α * β) • firstPresentationVector v t y := by
  ext i
  cases i using Fin.addCases with
  | left i =>
      simp [firstPresentationVector, joinPoints, smul_eq_mul]
      ring
  | right i =>
      simp only [firstPresentationVector, joinPoints, pointOfCovector,
        Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul, Fin.addCases_right]

/-- B07, conc:deg-flat-closure, in the shared projective model. -/
private def affineLinearPolynomial {n : ℕ} (ℓ : Point n →ₗ[ℂ] ℂ) : Poly n :=
  Finset.univ.sum fun i : Fin n => MvPolynomial.C (ℓ (Pi.single i 1)) * MvPolynomial.X i

private theorem affineLinearPolynomial_aeval {n : ℕ} (ℓ : Point n →ₗ[ℂ] ℂ)
    (z : Point n) :
    MvPolynomial.aeval z (affineLinearPolynomial ℓ) = ℓ z := by
  have hz : z = Finset.univ.sum (fun i : Fin n => z i • Pi.single i 1) := by
    ext i
    simp [Pi.single_apply]
  calc
    MvPolynomial.aeval z (affineLinearPolynomial ℓ) =
        Finset.univ.sum (fun i : Fin n => ℓ (Pi.single i 1) * z i) := by
      simp [affineLinearPolynomial]
    _ = ℓ z := by
      rw [hz, map_sum]
      simp [LinearMap.map_smul, smul_eq_mul, mul_comm, Pi.single_apply]

private theorem aeval_affineCurve {n : ℕ} (f : Poly n) (x y : Point n) (t : ℂ) :
    Polynomial.eval t
        (MvPolynomial.aeval (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (y i)) f) =
      MvPolynomial.aeval (fun i => x i + t * y i) f := by
  change (Polynomial.evalRingHom t)
      (MvPolynomial.aeval (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (y i)) f) = _
  rw [MvPolynomial.map_aeval]
  have hcoeff : (Polynomial.evalRingHom t).comp
      (algebraMap ℂ (Polynomial ℂ)) = RingHom.id ℂ := by
    ext c
    simp
  have hvars :
      (fun i : Fin n => (Polynomial.evalRingHom t)
        (Polynomial.C (x i) + Polynomial.X * Polynomial.C (y i))) =
      (fun i => x i + t * y i) := by
    funext i
    simp
    ring
  rw [hcoeff, hvars]
  change MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => x i + t * y i) f = _
  rw [MvPolynomial.eval₂_id]
  rfl

theorem evaluationFlat_projectiveClosure {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e) :
    (ProjectiveVariety.closure (affineEmbedding '' evaluationFlat C p)).points =
      {x : ProjectivePoint (skewDim e + 1) |
        (C.decode (Fin.tail x.rep)).val (firstPoint p.rep) =
          x.rep 0 • covectorOfPoint (secondPoint p.rep)} := by
  classical
  change parameterValue p.rep = 0 ∧ firstPoint p.rep ≠ 0 at hp
  let v : Point e := firstPoint p.rep
  let y : Module.Dual ℂ (Point e) := covectorOfPoint (secondPoint p.rep)
  have hv : v ≠ 0 := by simpa [v] using hp.2
  have hy : y v = 0 := by simpa [v, y, parameterValue] using hp.1
  let E : Point (skewDim e) →ₗ[ℂ] Module.Dual ℂ (Point e) :=
    (alternatingEvaluation v).comp C.decode.toLinearMap
  obtain ⟨D, hD, hDv⟩ := alternating_evaluation_surjective v hv y hy
  let z₀ : Point (skewDim e) := C.decode.symm ⟨D, hD⟩
  let a : Point (skewDim e + 1) := Fin.cons (1 : ℂ) z₀
  have hz₀ : E z₀ = y := by
    change alternatingEvaluation v (C.decode (C.decode.symm ⟨D, hD⟩)) = y
    rw [LinearEquiv.apply_symm_apply]
    exact hDv
  let tailMap : Point (skewDim e + 1) →ₗ[ℂ] Point (skewDim e) :=
    { toFun := Fin.tail
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Set.ext
  intro x
  constructor
  · intro hx
    have hxzero : x.rep ∈ MvPolynomial.zeroLocus ℂ
        (ProjectiveVariety.vanishingIdeal
          (affineEmbedding '' evaluationFlat C p)) := by
      exact hx x.rep x.rep_nonzero (Projectivization.mk_rep x)
    have heq : E (Fin.tail x.rep) = x.rep 0 • y := by
      apply LinearMap.ext
      intro w
      let evalAtW : Module.Dual ℂ (Point e) →ₗ[ℂ] ℂ :=
        { toFun := fun f => f w
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      let ℓ : Point (skewDim e + 1) →ₗ[ℂ] ℂ :=
        (evalAtW.comp E).comp tailMap - (y w) • LinearMap.proj 0
      have hℓ (u : Point (skewDim e + 1)) :
          ℓ u = ((C.decode (Fin.tail u)).val v) w - u 0 * y w := by
        simp [ℓ, evalAtW, E, tailMap, alternatingEvaluation,
          LinearMap.proj_apply, LinearMap.smul_apply, smul_eq_mul]
        linear_combination
      have hlinear : affineLinearPolynomial ℓ ∈
          MvPolynomial.vanishingIdeal ℂ
            (ProjectiveVariety.nonzeroRepresentatives
              (affineEmbedding '' evaluationFlat C p)) := by
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        intro q hq
        rcases hq with ⟨hqne, hqmem⟩
        change ∃ z ∈ evaluationFlat C p,
          affineEmbedding z = Projectivization.mk ℂ q hqne at hqmem
        rcases hqmem with ⟨z, hz, hqproj⟩
        let zvec : Point (skewDim e + 1) := Fin.cons (1 : ℂ) z
        have hzrep : zvec ≠ 0 := by
          intro h
          have h0 := congrFun h 0
          simpa [zvec] using h0
        have hscale : ∃ c : ℂ, c • zvec = q := by
          apply (Projectivization.mk_eq_mk_iff' ℂ q zvec hqne hzrep).mp
          simpa [affineEmbedding, zvec] using hqproj.symm
        obtain ⟨c, hc⟩ := hscale
        have hℓz : ℓ zvec = 0 := by
          rw [hℓ]
          have hEval : E z = y := hz
          have hw := congrArg (fun f : Module.Dual ℂ (Point e) => f w) hEval
          change (C.decode z).val v w = y w at hw
          have htail : Fin.tail zvec = z := by simp [zvec]
          rw [htail, hw]
          simp [zvec]
        rw [affineLinearPolynomial_aeval, ← hc, map_smul, hℓz]
        simp
      have heval := hxzero (affineLinearPolynomial ℓ) hlinear
      have hℓx : ℓ x.rep = 0 := by
        simpa [affineLinearPolynomial_aeval] using heval
      have hscalar := sub_eq_zero.mp (by simpa [hℓ] using hℓx)
      simpa [E, alternatingEvaluation, LinearMap.smul_apply, smul_eq_mul] using hscalar
    simpa [E, alternatingEvaluation] using heq
  · intro hx
    have heq : E (Fin.tail x.rep) = x.rep 0 • y := by
      simpa [E, alternatingEvaluation] using hx
    change ∀ (u : Point (skewDim e + 1)) (hu : u ≠ 0),
      Projectivization.mk ℂ u hu = x →
        u ∈ MvPolynomial.zeroLocus ℂ
          (ProjectiveVariety.vanishingIdeal
            (affineEmbedding '' evaluationFlat C p))
    intro u hu huproj
    obtain ⟨c, hc⟩ :=
      (Projectivization.mk_eq_mk_iff' ℂ u x.rep hu x.rep_nonzero).mp
        (huproj.trans (Projectivization.mk_rep x).symm)
    have hueq : E (Fin.tail u) = u 0 • y := by
      apply LinearMap.ext
      intro w
      have hcoord : u 0 = c * x.rep 0 := by
        calc
          u 0 = (c • x.rep) 0 := by rw [← hc]
          _ = c * x.rep 0 := by simp [Pi.smul_apply, smul_eq_mul]
      have htail : Fin.tail u = c • Fin.tail x.rep := by
        change tailMap u = c • tailMap x.rep
        rw [← hc, map_smul]
      rw [htail, map_smul, heq, hcoord]
      simp [smul_smul]
    change ∀ f, f ∈ MvPolynomial.vanishingIdeal ℂ
        (ProjectiveVariety.nonzeroRepresentatives
          (affineEmbedding '' evaluationFlat C p)) → MvPolynomial.aeval u f = 0
    intro f hf
    have hf' : f ∈ MvPolynomial.vanishingIdeal ℂ
        (ProjectiveVariety.nonzeroRepresentatives
          (affineEmbedding '' evaluationFlat C p)) := hf
    let P : Polynomial ℂ :=
      MvPolynomial.aeval
        (fun i => Polynomial.C (u i) + Polynomial.X * Polynomial.C (a i)) f
    have hpoint (t : ℂ) :
        (fun i : Fin (skewDim e + 1) => u i + t * a i) = u + t • a := by
      funext i
      simp [Pi.smul_apply, smul_eq_mul]
    have hP_eval (t : ℂ) :
        P.eval t = MvPolynomial.aeval (u + t • a) f := by
      calc
        P.eval t = MvPolynomial.aeval (fun i => u i + t * a i) f := by
          simpa [P] using (aeval_affineCurve f u a t)
        _ = MvPolynomial.aeval (u + t • a) f := by rw [hpoint]
    have hroots : Set.Infinite {t : ℂ | P.IsRoot t} := by
      have hgood : {t : ℂ | u 0 + t ≠ 0}.Infinite := by
        apply Set.infinite_of_finite_compl
        have hcompl : {t : ℂ | u 0 + t = 0} = {-(u 0)} := by
          ext t
          simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · intro ht
            linear_combination ht
          · intro ht
            subst t
            simp
        simpa [Set.compl_def, hcompl] using
          (Set.finite_singleton (-(u 0)))
      refine hgood.mono ?_
      intro t ht
      change P.eval t = 0
      let d : ℂ := u 0 + t
      let zt : Point (skewDim e) := d⁻¹ • (Fin.tail u + t • z₀)
      have hd : d ≠ 0 := by simpa [d] using ht
      have hzt : zt ∈ evaluationFlat C p := by
        change E zt = y
        dsimp [zt]
        rw [map_smul, map_add, map_smul, hueq, hz₀, ← add_smul, ← mul_smul]
        simp [d, inv_mul_cancel₀ hd]
      let q : Point (skewDim e + 1) := u + t • a
      let azt : Point (skewDim e + 1) := Fin.cons (1 : ℂ) zt
      have hq : q = d • azt := by
        ext i
        cases i using Fin.cases with
        | zero => simp [q, d, a, azt, Fin.cons_zero]
        | succ i =>
            simp only [q, Pi.add_apply, Pi.smul_apply, Fin.cons_succ, smul_eq_mul,
              azt, a, zt, Fin.tail]
            field_simp [hd] <;> ring
      have hqne : q ≠ 0 := by
        intro hq0
        have h0 := congrFun hq0 0
        apply hd
        simpa [q, d, a, Fin.cons_zero] using h0
      have hqproj : Projectivization.mk ℂ q hqne = affineEmbedding zt := by
        apply (Projectivization.mk_eq_mk_iff' ℂ q azt hqne (by
          intro hz
          have h0 := congrFun hz 0
          simpa [azt] using h0)).2
        exact ⟨d, hq.symm⟩
      have hqmem : q ∈ ProjectiveVariety.nonzeroRepresentatives
          (affineEmbedding '' evaluationFlat C p) := by
        refine ⟨hqne, ?_⟩
        change Projectivization.mk ℂ q hqne ∈ affineEmbedding '' evaluationFlat C p
        exact ⟨zt, hzt, hqproj.symm⟩
      have hvanish := (MvPolynomial.mem_vanishingIdeal_iff.mp hf') q hqmem
      rw [hP_eval]
      simpa [q] using hvanish
    have hPzero := Polynomial.eq_zero_of_infinite_isRoot P hroots
    have hEval0 : MvPolynomial.aeval u f = P.eval 0 := by
      rw [hP_eval]
      simp
    rw [hEval0, hPzero]
    simp

/-- B08, conc:deg-boundary. -/
theorem boundary_no_affine_point {e : ℕ} (C : SkewCoordinates e)
    (d : ProjectivePoint e) (p : ProjectivePoint (e + e))
    (x : ProjectivePoint (skewDim e + 1)) (hx : incidenceCondition C d p x)
    (hp : firstPoint p.rep = 0) : x.rep 0 = 0 := by
  rcases hx with ⟨t, hfirst, hy, hfiber⟩
  have hmul : t • d.rep = 0 := by rw [← hfirst, hp]
  have ht : t = 0 := (smul_eq_zero.mp hmul).resolve_right d.rep_nonzero
  subst t
  exact incidenceFiber_boundary d.rep (covectorOfPoint (secondPoint p.rep))
    (x.rep 0) (C.decode (Fin.tail x.rep)) hfiber

private theorem pointOfCovector_covectorOfPoint {e : ℕ} (v : Point e) :
    pointOfCovector (covectorOfPoint v) = v := by
  ext i
  simp [pointOfCovector, covectorOfPoint, Pi.single_apply]

private theorem covectorOfPoint_pointOfCovector {e : ℕ}
    (f : Module.Dual ℂ (Point e)) :
    covectorOfPoint (pointOfCovector f) = f := by
  apply LinearMap.ext
  intro v
  have hv : v = ∑ i : Fin e, v i • Pi.single i 1 := by
    ext i
    simp [Pi.single_apply]
  rw [hv]
  simp [covectorOfPoint, pointOfCovector, Pi.single_apply]

/-- B10, conc:deg-affine-point-fiber: the full fiber is the linear graph P(E). -/
theorem full_point_fiber {e : ℕ} (C : SkewCoordinates e) (z : Point (skewDim e)) :
    {p | ∃ d : ProjectivePoint e, incidenceCondition C d p (affineEmbedding z)} =
      {p | ∃ v : Point e, ∃ hv : v ≠ 0, p = graphParameter C z v hv} := by
  let x := affineEmbedding z
  let Z := (C.decode z).val
  have hcons : (Fin.cons 1 z : Point (skewDim e + 1)) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa using h0
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (Fin.cons 1 z : Point (skewDim e + 1)) hcons
  have hxrep : (u : ℂ) • Fin.cons 1 z = x.rep := by
    rw [← Units.smul_def]
    simpa [x, affineEmbedding] using hu
  let q : ℂ := u
  have hq : q ≠ 0 := u.ne_zero
  have hx0 : x.rep 0 = q := by
    rw [← hxrep]
    simp [q]
  have hxtail : Fin.tail x.rep = q • z := by
    rw [← hxrep]
    ext i
    change (q • Fin.cons 1 z) (Fin.succ i) = q * z i
    simp [Pi.smul_apply, smul_eq_mul]
  have hdecode : (C.decode (Fin.tail x.rep)).val = q • Z := by
    rw [hxtail]
    simp [Z]
  ext p
  constructor
  · rintro ⟨d, hinc⟩
    rcases hinc with ⟨t, hfirst, hy0, hfiber⟩
    let y := covectorOfPoint (secondPoint p.rep)
    change homogeneousEvaluation d.rep (x.rep 0, C.decode (Fin.tail x.rep)) ∈
      Submodule.span ℂ {(t, y)} at hfiber
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfiber
    have hc1 : c * t = q := by
      have h := congrArg Prod.fst hc
      change c * t = x.rep 0 at h
      exact h.trans hx0
    have hc2 : c • y = (C.decode (Fin.tail x.rep)).val d.rep := by
      have h := congrArg Prod.snd hc
      simpa [homogeneousEvaluation, alternatingEvaluation, y] using h
    have hcne : c ≠ 0 := by
      intro hczero
      apply hq
      calc
        q = c * t := hc1.symm
        _ = 0 := by simp [hczero]
    have htne : t ≠ 0 := by
      intro htzero
      apply hq
      calc
        q = c * t := hc1.symm
        _ = 0 := by simp [htzero]
    have hD : (C.decode (Fin.tail x.rep)).val d.rep = q • Z d.rep := by
      rw [hdecode]
      simp [LinearMap.smul_apply]
    have hcancel : c • y = c • (t • Z d.rep) := by
      calc
        c • y = q • Z d.rep := hc2.trans hD
        _ = (c * t) • Z d.rep := by rw [hc1]
        _ = c • (t • Z d.rep) := by rw [mul_smul]
    have hy : y = t • Z d.rep := by
      have h := congrArg (fun f : Module.Dual ℂ (Point e) => c⁻¹ • f) hcancel
      simpa [smul_smul, hcne] using h
    have hsecond : secondPoint p.rep = t • pointOfCovector (Z d.rep) := by
      calc
        secondPoint p.rep = pointOfCovector y :=
          (pointOfCovector_covectorOfPoint (secondPoint p.rep)).symm
        _ = pointOfCovector (t • Z d.rep) := congrArg pointOfCovector hy
        _ = t • pointOfCovector (Z d.rep) := by
          ext i
          simp [pointOfCovector]
    have hrep : p.rep = t • graphVector C z d.rep := by
      ext i
      cases i using Fin.addCases with
      | left i =>
          simp only [graphVector, joinPoints, Fin.addCases_left, Pi.smul_apply]
          simpa [firstPoint] using congrFun hfirst i
      | right i =>
          simp only [graphVector, joinPoints, Fin.addCases_right, Pi.smul_apply]
          simpa [secondPoint] using congrFun hsecond i
    have hprojective : Projectivization.mk ℂ p.rep p.rep_nonzero =
        Projectivization.mk ℂ (graphVector C z d.rep)
          (graphVector_ne_zero C z d.rep d.rep_nonzero) := by
      apply (Projectivization.mk_eq_mk_iff' ℂ p.rep (graphVector C z d.rep)
        p.rep_nonzero (graphVector_ne_zero C z d.rep d.rep_nonzero)).2
      exact ⟨t, hrep.symm⟩
    refine ⟨d.rep, d.rep_nonzero, ?_⟩
    calc
      p = Projectivization.mk ℂ p.rep p.rep_nonzero :=
        (Projectivization.mk_rep p).symm
      _ = graphParameter C z d.rep d.rep_nonzero := by
        simpa [graphParameter] using hprojective
  · rintro ⟨v, hv, rfl⟩
    let d : ProjectivePoint e := Projectivization.mk ℂ v hv
    let W := graphVector C z v
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
    obtain ⟨b, hb₀⟩ :=
      Projectivization.exists_smul_eq_mk_rep ℂ W (graphVector_ne_zero C z v hv)
    have hb : (b : ℂ) • W = (graphParameter C z v hv).rep := by
      rw [← Units.smul_def]
      simpa [graphParameter, W] using hb₀
    let aC : ℂ := a
    let bC : ℂ := b
    let t : ℂ := bC * aC⁻¹
    let c : ℂ := q * aC * bC⁻¹
    have hfirstV : firstPoint (graphParameter C z v hv).rep = bC • v := by
      rw [← hb]
      ext i
      simp [W, graphVector, firstPoint, joinPoints, Fin.addCases_left, bC]
    have hfirst : firstPoint (graphParameter C z v hv).rep = t • d.rep := by
      have had : d.rep = aC • v := by
        simpa [d, aC, Units.smul_def] using ha.symm
      calc
        firstPoint (graphParameter C z v hv).rep = bC • v := hfirstV
        _ = t • (aC • v) := by
          dsimp [t, aC, bC]
          simp [smul_smul, mul_assoc, a.ne_zero]
        _ = t • d.rep := by rw [← had]
    have hsecondV : secondPoint (graphParameter C z v hv).rep =
        bC • pointOfCovector (Z v) := by
      rw [← hb]
      ext i
      simp only [secondPoint, Pi.smul_apply, W, graphVector, joinPoints,
        Fin.addCases_right, bC, Z]
    have hyfun : covectorOfPoint
        (secondPoint (graphParameter C z v hv).rep) = bC • Z v := by
      rw [hsecondV]
      calc
        covectorOfPoint (bC • pointOfCovector (Z v)) =
            bC • covectorOfPoint (pointOfCovector (Z v)) := by
          apply LinearMap.ext
          intro w
          simp [covectorOfPoint, pointOfCovector, LinearMap.smul_apply,
            smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        _ = bC • Z v := by rw [covectorOfPoint_pointOfCovector]
    have halt : Z v v = 0 := (C.decode z).property v
    have hy0 : covectorOfPoint
        (secondPoint (graphParameter C z v hv).rep) d.rep = 0 := by
      have had : d.rep = aC • v := by
        simpa [d, aC, Units.smul_def] using ha.symm
      rw [hyfun, had]
      simp [LinearMap.smul_apply, LinearMap.map_smul, halt, mul_assoc]
    have hct : c * t = q := by
      dsimp [c, t, aC, bC]
      field_simp [a.ne_zero, b.ne_zero]
    have hD : (C.decode (Fin.tail x.rep)).val d.rep = c •
        covectorOfPoint (secondPoint (graphParameter C z v hv).rep) := by
      have had : d.rep = aC • v := by
        simpa [d, aC, Units.smul_def] using ha.symm
      rw [hdecode, had, hyfun]
      simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_smul]
      congr 1
      dsimp [c, aC, bC]
      field_simp [b.ne_zero]
    have hpair : homogeneousEvaluation d.rep (x.rep 0, C.decode (Fin.tail x.rep)) =
        c • (t, covectorOfPoint (secondPoint (graphParameter C z v hv).rep)) := by
      apply Prod.ext
      · change x.rep 0 = c • t
        rw [hx0]
        exact hct.symm
      · change alternatingEvaluation d.rep (C.decode (Fin.tail x.rep)) = _
        simpa [alternatingEvaluation] using hD
    refine ⟨d, ?_⟩
    change ∃ s, firstPoint (graphParameter C z v hv).rep = s • d.rep ∧
      covectorOfPoint (secondPoint (graphParameter C z v hv).rep) d.rep = 0 ∧
      (x.rep 0, C.decode (Fin.tail x.rep)) ∈
        incidenceFiber d.rep s (covectorOfPoint (secondPoint (graphParameter C z v hv).rep))
    refine ⟨t, hfirst, hy0, ?_⟩
    change homogeneousEvaluation d.rep (x.rep 0, C.decode (Fin.tail x.rep)) ∈
      Submodule.span ℂ {(t, covectorOfPoint (secondPoint (graphParameter C z v hv).rep))}
    rw [hpair]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end
end DistinctDistances.TrackB
