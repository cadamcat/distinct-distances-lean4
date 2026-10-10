import DistinctDistances.TrackB.PolynomialImageSupport
import DistinctDistances.TrackB.TangentLineSupport
import DistinctDistances.TrackB.Requests

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

def rulingOpenPolynomial {e : ℕ} (H : Poly (skewDim e)) : Poly (skewDim e + e) :=
  MvPolynomial.rename (Fin.castAdd e) H

theorem eval_rulingOpenPolynomial {e : ℕ} (H : Poly (skewDim e))
    (w : Point (skewDim e + e)) :
    MvPolynomial.aeval w (rulingOpenPolynomial H) = MvPolynomial.aeval (firstPoint w) H := by
  rw [rulingOpenPolynomial, MvPolynomial.aeval_rename]
  rfl

/-- Polynomial coordinates of (z,v) ↦ (v,zv), before projectivizing. -/
def rulingGraphPolynomials {e : ℕ} (C : SkewCoordinates e) :
    Fin (e + e) → Poly (skewDim e + e) :=
  Fin.addCases
    (fun i => MvPolynomial.X (Fin.natAdd (skewDim e) i))
    (fun i => ∑ k : Fin (skewDim e), ∑ l : Fin e,
      MvPolynomial.C (((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single i 1)) *
        MvPolynomial.X (Fin.castAdd e k) * MvPolynomial.X (Fin.natAdd (skewDim e) l))

theorem eval_rulingGraphPolynomials {e : ℕ} (C : SkewCoordinates e)
    (w : Point (skewDim e + e)) :
    (fun i => MvPolynomial.aeval w (rulingGraphPolynomials C i)) =
      graphVector C (firstPoint w) (secondPoint w) := by
  ext i
  cases i using Fin.addCases with
  | left i => simp [rulingGraphPolynomials, graphVector, joinPoints, secondPoint]
  | right i =>
      let z : Point (skewDim e) := firstPoint w
      let v : Point e := secondPoint w
      have hz : z = ∑ k : Fin (skewDim e), z k • (Pi.single k (1 : ℂ) : Point (skewDim e)) := by
        simpa using ((Pi.basisFun ℂ (Fin (skewDim e))).sum_repr z).symm
      have hv : v = ∑ l : Fin e, v l • (Pi.single l (1 : ℂ) : Point e) := by
        simpa using ((Pi.basisFun ℂ (Fin e)).sum_repr v).symm
      have heval : ((C.decode z).val v) (Pi.single i 1) =
          ∑ k : Fin (skewDim e), ∑ l : Fin e,
            (((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single i 1)) * z k * v l := by
        conv_lhs => rw [hz, hv]
        simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
          LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        ring
      simpa only [rulingGraphPolynomials, graphVector, joinPoints, Fin.addCases_right,
        pointOfCovector, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        z, v, firstPoint, secondPoint, Algebra.algebraMap_self, RingHom.id_apply] using heval.symm

def parameterQuadricPolynomial (e : ℕ) : Poly (e + e) :=
  ∑ i : Fin e, MvPolynomial.X (Fin.castAdd e i) * MvPolynomial.X (Fin.natAdd e i)

theorem eval_parameterQuadricPolynomial {e : ℕ} (w : Point (e + e)) :
    MvPolynomial.aeval w (parameterQuadricPolynomial e) = parameterValue w := by
  simp only [parameterQuadricPolynomial, map_sum, map_mul, MvPolynomial.aeval_X,
    parameterValue, covectorOfPoint, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, firstPoint, secondPoint]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem parameterQuadric_mk_iff {e : ℕ} (w : Point (e + e)) (hw : w ≠ 0) :
    Projectivization.mk ℂ w hw ∈ parameterQuadric e ↔ parameterValue w = 0 := by
  constructor
  · intro hp
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ w hw
    change parameterValue (Projectivization.mk ℂ w hw).rep = 0 at hp
    rw [← hu, Units.smul_def, parameterValue_smul] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ u.ne_zero)
  · exact parameterQuadric_mk w hw

theorem parameterQuadricPolynomial_mem_closure {e : ℕ}
    (T : Set (ProjectivePoint (e + e))) (hT : T ⊆ parameterQuadric e) :
    parameterQuadricPolynomial e ∈ (ProjectiveVariety.closure T).ideal := by
  rintro w ⟨hw, hp⟩
  rw [eval_parameterQuadricPolynomial]
  exact (parameterQuadric_mk_iff w hw).mp (hT hp)

theorem closure_subset_parameterQuadric {e : ℕ}
    (T : Set (ProjectivePoint (e + e))) (hT : T ⊆ parameterQuadric e) :
    (ProjectiveVariety.closure T).points ⊆ parameterQuadric e := by
  intro p hp
  change parameterValue p.rep = 0
  rw [← eval_parameterQuadricPolynomial]
  exact hp p.rep p.rep_nonzero (Projectivization.mk_rep p)
    (parameterQuadricPolynomial e) (parameterQuadricPolynomial_mem_closure T hT)

theorem graphParameter_mem_quadric {e : ℕ} (C : SkewCoordinates e)
    (z : Point (skewDim e)) (v : Point e) (hv : v ≠ 0) :
    graphParameter C z v hv ∈ parameterQuadric e := by
  apply parameterQuadric_mk
  have hfirst : firstPoint (graphVector C z v) = v := by
    ext i
    simp [graphVector, joinPoints, firstPoint]
  have hsecond : secondPoint (graphVector C z v) = pointOfCovector ((C.decode z).val v) := by
    funext i
    change Fin.addCases v (pointOfCovector ((C.decode z).val v)) (Fin.natAdd e i) =
      pointOfCovector ((C.decode z).val v) i
    exact Fin.addCases_right (m := e) (n := e) (motive := fun _ => ℂ)
      (left := v) (right := pointOfCovector ((C.decode z).val v)) i
  rw [parameterValue, hfirst, hsecond, covector_point_inverse]
  exact (C.decode z).property v

theorem parameterClosure_subset_quadric {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    (parameterClosure C Γ H).points ⊆ parameterQuadric e := by
  apply closure_subset_parameterQuadric
  rintro p ⟨z, v, hw, hv, rfl⟩
  exact graphParameter_mem_quadric C z v hv

section Ruling
variable {e j N : ℕ} (C : SkewCoordinates e)
  (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e)) (a : Fin e) (R : IsRulingIncidence C V Γ H a j N)

include R

theorem rulingOpenPolynomial_not_mem : rulingOpenPolynomial H ∉ Γ.ideal := by
  intro hmem
  apply R.nonzero_section
  rw [← V.vanishingIdeal_points]
  intro z hz
  by_contra hzH
  obtain ⟨v, hv⟩ := R.dominant z ⟨hz, hzH⟩
  have hzero := hv (rulingOpenPolynomial H) hmem
  rw [eval_rulingOpenPolynomial] at hzero
  have hfirst : firstPoint (joinPoints z v) = z := by
    ext i
    simp [firstPoint, joinPoints]
  exact hzH (by simpa only [hfirst] using hzero)

theorem rulingGraphPolynomials_nonzero (w : Point (skewDim e + e)) (hw : w ∈ Γ.points) :
    (fun i => MvPolynomial.aeval w (rulingGraphPolynomials C i)) ≠ 0 := by
  rw [eval_rulingGraphPolynomials]
  apply graphVector_ne_zero
  intro hzero
  have h := R.normalized w hw
  rw [hzero] at h
  exact zero_ne_one h

theorem ruling_polynomial_projective_image :
    polynomialProjectiveImage Γ (rulingOpenPolynomial H) (rulingGraphPolynomials C) =
      parameterImage C Γ H := by
  ext p
  constructor
  · rintro ⟨w, hw, hwH, hv, hp⟩
    let z := firstPoint w
    let v := secondPoint w
    have hwjoin : joinPoints z v = w := by
      exact joinPoints_eta w
    have hvne : v ≠ 0 := by
      intro hvzero
      have hnorm := R.normalized w hw
      change v a = 1 at hnorm
      rw [hvzero] at hnorm
      exact zero_ne_one hnorm
    refine ⟨z, v, ?_, hvne, ?_⟩
    · rw [hwjoin]
      exact ⟨hw, (eval_rulingOpenPolynomial H w) ▸ hwH⟩
    · simp only [eval_rulingGraphPolynomials] at hp
      exact hp
  · rintro ⟨z, v, hw, hv, hp⟩
    refine ⟨joinPoints z v, hw.1, ?_, ?_, ?_⟩
    · simpa only [eval_rulingOpenPolynomial] using hw.2
    · exact rulingGraphPolynomials_nonzero C V Γ H a R _ hw.1
    · let f : Point (e + e) :=
        fun i => MvPolynomial.aeval (joinPoints z v) (rulingGraphPolynomials C i)
      have hf : f ≠ 0 := rulingGraphPolynomials_nonzero C V Γ H a R _ hw.1
      have hcoords : f = graphVector C z v := by
        have hfirst : firstPoint (n := skewDim e) (m := e) (joinPoints z v) = z := by
          funext i
          exact Fin.addCases_left (m := skewDim e) (n := e) (motive := fun _ => ℂ)
            (left := z) (right := v) i
        have hsecond : secondPoint (n := skewDim e) (m := e) (joinPoints z v) = v := by
          funext i
          exact Fin.addCases_right (m := skewDim e) (n := e) (motive := fun _ => ℂ)
            (left := z) (right := v) i
        have hcoord := eval_rulingGraphPolynomials C (joinPoints z v)
        rw [hfirst, hsecond] at hcoord
        exact hcoord
      have hmk : Projectivization.mk ℂ f hf = graphParameter C z v hv := by
        apply (Projectivization.mk_eq_mk_iff' ℂ f (graphVector C z v) hf
          (graphVector_ne_zero C z v hv)).mpr
        exact ⟨1, by simpa only [one_smul] using hcoords.symm⟩
      exact hmk.trans hp

/-- B01's linear-algebra adapter, concentration.tex:519–522. The coordinate map is
injective and has precisely s₀ parameters; its nonempty principal open is the literal
parameter-map fiber. Normalization makes the direction vector unique. -/
theorem ruling_polynomial_projective_fiber_coordinates (p : ProjectivePoint (e + e))
    (hp : p ∈ polynomialProjectiveImage Γ (rulingOpenPolynomial H) (rulingGraphPolynomials C)) :
    ∃ (b : Point (skewDim e + e))
      (φ : Point (flatDim e) →ₗ[ℂ] Point (skewDim e + e)), Function.Injective φ ∧
    polynomialProjectiveFiber Γ (rulingOpenPolynomial H) (rulingGraphPolynomials C) p =
        {w | ∃ t : Point (flatDim e), w = b + φ t ∧
          MvPolynomial.aeval w (rulingOpenPolynomial H) ≠ 0} := by
  classical
  obtain ⟨w0, hw0, hH0, hF0, hp0⟩ := hp
  let z0 : Point (skewDim e) := firstPoint w0
  let v0 : Point e := secondPoint w0
  have hv0 : v0 ≠ 0 := by
    intro hv
    have hnorm := R.normalized w0 hw0
    change v0 a = 1 at hnorm
    rw [hv] at hnorm
    exact zero_ne_one hnorm
  have hva0 : v0 a = 1 := R.normalized w0 hw0
  have hwjoin0 : joinPoints z0 v0 = w0 := joinPoints_eta w0
  have hH0z : MvPolynomial.aeval z0 H ≠ 0 := by
    simpa only [z0, eval_rulingOpenPolynomial] using hH0
  have hrule0 : joinPoints z0 v0 ∈ rulingPoints Γ H := by
    rw [hwjoin0]
    exact ⟨hw0, hH0z⟩
  have hFgraph0 :
      (fun i => MvPolynomial.aeval w0 (rulingGraphPolynomials C i)) =
        graphVector C z0 v0 := by
    simpa only [z0, v0] using eval_rulingGraphPolynomials C w0
  have hgv0 : graphVector C z0 v0 ≠ 0 := graphVector_ne_zero C z0 v0 hv0
  have hpGraph : graphParameter C z0 v0 hv0 = p := by
    have hmk : Projectivization.mk ℂ
        (fun i => MvPolynomial.aeval w0 (rulingGraphPolynomials C i)) hF0 =
          Projectivization.mk ℂ (graphVector C z0 v0) hgv0 := by
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hF0 hgv0).2
      exact ⟨1, by simpa only [one_smul] using hFgraph0.symm⟩
    change Projectivization.mk ℂ (graphVector C z0 v0) hgv0 = p
    exact hmk.symm.trans hp0
  have hpimage : p ∈ parameterImage C Γ H := ⟨z0, v0, hrule0, hv0, hpGraph⟩
  obtain ⟨u0, hu0⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (graphVector C z0 v0) hgv0
  have hrep0' : p.rep = (u0 : ℂ) • graphVector C z0 v0 := by
    calc
      p.rep = (graphParameter C z0 v0 hv0).rep := by rw [hpGraph]
      _ = (u0 : ℂ) • graphVector C z0 v0 := by
        exact hu0.symm
  have hfirstRep : firstPoint p.rep = (u0 : ℂ) • v0 := by
    rw [hrep0']
    ext i
    change (u0 : ℂ) *
      Fin.addCases v0 (pointOfCovector ((C.decode z0).val v0)) (Fin.castAdd e i) =
        (u0 : ℂ) * v0 i
    rw [Fin.addCases_left]
  have hsecondRep : secondPoint p.rep =
      (u0 : ℂ) • pointOfCovector ((C.decode z0).val v0) := by
    rw [hrep0']
    ext i
    change (u0 : ℂ) *
      Fin.addCases v0 (pointOfCovector ((C.decode z0).val v0)) (Fin.natAdd e i) =
        (u0 : ℂ) * pointOfCovector ((C.decode z0).val v0) i
    rw [Fin.addCases_right]
  have hcovectorSmul (c : ℂ) (y : Point e) :
      covectorOfPoint (c • y) = c • covectorOfPoint y := by
    ext x
    simp [covectorOfPoint, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  let E : Point (skewDim e) →ₗ[ℂ] Module.Dual ℂ (Point e) :=
    (alternatingEvaluation v0).comp C.decode.toLinearMap
  have hflat : evaluationFlat C p = {z | E z = E z0} := by
    ext z
    change (C.decode z).val (firstPoint p.rep) =
      covectorOfPoint (secondPoint p.rep) ↔ E z = E z0
    constructor
    · intro hz
      have hz' := hz
      rw [hfirstRep, hsecondRep] at hz'
      have hscaled : (u0 : ℂ) • ((C.decode z).val v0) =
          (u0 : ℂ) • ((C.decode z0).val v0) := by
        calc
          (u0 : ℂ) • ((C.decode z).val v0) =
              (C.decode z).val ((u0 : ℂ) • v0) := by rw [map_smul]
          _ = covectorOfPoint ((u0 : ℂ) • pointOfCovector ((C.decode z0).val v0)) := hz'
          _ = (u0 : ℂ) • ((C.decode z0).val v0) := by
            rw [hcovectorSmul, covector_point_inverse]
      have hcancel := u0.isUnit.smul_left_cancel.mp hscaled
      change E z = E z0
      exact hcancel
    · intro hz
      have hz' : (C.decode z).val v0 = (C.decode z0).val v0 := by
        change E z = E z0 at hz
        exact hz
      rw [hfirstRep, hsecondRep]
      calc
        (C.decode z).val ((u0 : ℂ) • v0) =
            (u0 : ℂ) • ((C.decode z).val v0) := by rw [map_smul]
        _ = (u0 : ℂ) • ((C.decode z0).val v0) := congrArg (fun y => (u0 : ℂ) • y) hz'
        _ = covectorOfPoint ((u0 : ℂ) • pointOfCovector ((C.decode z0).val v0)) := by
          rw [hcovectorSmul, covector_point_inverse]
  have hflatV : evaluationFlat C p ⊆ V.points := by
    rw [← hpGraph]
    exact R.actual_flats z0 v0 hrule0 hv0
  let K := LinearMap.ker E
  have hKdim : Module.finrank ℂ K = flatDim e := by
    have hEq := (C.decode.ofSubmodule' (LinearMap.ker (alternatingEvaluation v0))).finrank_eq
    change Module.finrank ℂ K =
      Module.finrank ℂ (LinearMap.ker (alternatingEvaluation v0)) at hEq
    rw [hEq, alternatingEvaluation_kernel_finrank v0 hv0, Module.finrank_fin_fun]
    rfl
  let basisK : Module.Basis (Fin (flatDim e)) ℂ K :=
    (Module.finBasis ℂ K).reindex (finCongr hKdim)
  let kEquiv : K ≃ₗ[ℂ] Point (flatDim e) := basisK.equivFun
  let ψ : Point (flatDim e) →ₗ[ℂ] Point (skewDim e) :=
    K.subtype.comp kEquiv.symm.toLinearMap
  let b0 : Point (skewDim e + e) := joinPoints z0 v0
  let φ : Point (flatDim e) →ₗ[ℂ] Point (skewDim e + e) := {
    toFun t := joinPoints (ψ t) 0
    map_add' t s := by
      change joinPoints (ψ (t + s)) 0 =
        joinPoints (ψ t) 0 + joinPoints (ψ s) 0
      rw [map_add]
      simpa using joinPoints_add (ψ t) (ψ s) 0 0
    map_smul' c t := by
      change joinPoints (ψ (c • t)) 0 = c • joinPoints (ψ t) 0
      rw [map_smul]
      simpa using joinPoints_smul c (ψ t) 0
  }
  have firstPoint_join (x : Point (skewDim e)) (y : Point e) :
      firstPoint (joinPoints x y) = x := by
    funext i
    exact Fin.addCases_left (m := skewDim e) (n := e) (motive := fun _ => ℂ)
      (left := x) (right := y) i
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp kEquiv.symm.injective
  have hφ : Function.Injective φ := by
    intro t s hts
    have hfirst := congrArg firstPoint hts
    have hψ : ψ t = ψ s := by
      calc
        ψ t = firstPoint (joinPoints (ψ t) 0) := (firstPoint_join (ψ t) 0).symm
        _ = firstPoint (joinPoints (ψ s) 0) := hfirst
        _ = ψ s := firstPoint_join (ψ s) 0
    exact hψinj hψ
  have direction_unique :
      ∀ (z₁ z₂ : Point (skewDim e)) (v₁ v₂ : Point e)
        (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hva₁ : v₁ a = 1) (hva₂ : v₂ a = 1),
          graphParameter C z₁ v₁ hv₁ = graphParameter C z₂ v₂ hv₂ →
            v₁ = v₂ := by
    intro z₁ z₂ v₁ v₂ hv₁ hv₂ hva₁ hva₂ heq
    change Projectivization.mk ℂ (graphVector C z₁ v₁) _ =
      Projectivization.mk ℂ (graphVector C z₂ v₂) _ at heq
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq
    have hfirst : (c : ℂ) • v₂ = v₁ := by
      have h := congrArg firstPoint hc
      have hleft : firstPoint ((c : ℂ) • graphVector C z₂ v₂) =
          (c : ℂ) • v₂ := by
        ext i
        simp [firstPoint, Pi.smul_apply, graphVector, joinPoints, Fin.addCases_left]
      have hright : firstPoint (graphVector C z₁ v₁) = v₁ := by
        ext i
        simp [firstPoint, graphVector, joinPoints]
      rw [hleft, hright] at h
      exact h
    have hcval : (c : ℂ) = 1 := by
      have h := congrFun hfirst a
      simpa [Pi.smul_apply, smul_eq_mul, hva₁, hva₂] using h
    rw [hcval, one_smul] at hfirst
    exact hfirst.symm
  refine ⟨b0, φ, hφ, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hwH, hF, hproj⟩
    let z : Point (skewDim e) := firstPoint w
    let v : Point e := secondPoint w
    have hva : v a = 1 := R.normalized w hw
    have hv : v ≠ 0 := by
      intro hvzero
      have h := congrFun hvzero a
      rw [h] at hva
      exact zero_ne_one hva
    have hHz : MvPolynomial.aeval z H ≠ 0 := by
      rw [eval_rulingOpenPolynomial] at hwH
      exact hwH
    have hGcoord :
        (fun i => MvPolynomial.aeval w (rulingGraphPolynomials C i)) =
          graphVector C z v := by
      simpa only [z, v] using eval_rulingGraphPolynomials C w
    have hpw : graphParameter C z v hv = p := by
      have hgv := graphVector_ne_zero C z v hv
      have hmk : Projectivization.mk ℂ
          (fun i => MvPolynomial.aeval w (rulingGraphPolynomials C i)) hF =
            Projectivization.mk ℂ (graphVector C z v) hgv := by
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hF hgv).2
        exact ⟨1, by simpa only [one_smul] using hGcoord.symm⟩
      change Projectivization.mk ℂ (graphVector C z v) hgv = p
      exact hmk.symm.trans hproj
    have hzwork : z ∈ workingPoints V H := by
      refine ⟨?_, hHz⟩
      exact R.point_containment w hw
    have hzflat : z ∈ evaluationFlat C p := by
      have hrule : joinPoints z v ∈ rulingPoints Γ H := by
        have hjoin : joinPoints z v = w := joinPoints_eta w
        rw [hjoin]
        exact ⟨hw, hHz⟩
      apply (R.full_parameter_fibers p hpimage z hzwork).mpr
      exact ⟨v, hrule, hv, hpw⟩
    have hEz : E z = E z0 := by
      rw [hflat] at hzflat
      exact hzflat
    have hk : z - z0 ∈ K := by
      change E (z - z0) = 0
      rw [map_sub, hEz, sub_self]
    let k : K := ⟨z - z0, hk⟩
    let t : Point (flatDim e) := kEquiv k
    have hψt : ψ t = z - z0 := by
      simp [ψ, t, k]
    have hvEq := direction_unique z z0 v v0 hv hv0 hva hva0 (hpw.trans hpGraph.symm)
    have hbφ : b0 + φ t = joinPoints z v0 := by
      calc
        b0 + φ t = joinPoints z0 v0 + joinPoints (z - z0) 0 := by
          simp [b0, φ, hψt]
        _ = joinPoints (z0 + (z - z0)) (v0 + 0) := (joinPoints_add _ _ _ _).symm
        _ = joinPoints z v0 := by congr 1 <;> simp
    have hwEq : w = b0 + φ t := by
      calc
        w = joinPoints z v := (joinPoints_eta w).symm
        _ = b0 + φ t := by rw [hvEq, ← hbφ]
    exact ⟨t, hwEq, hwH⟩
  · rintro ⟨t, rfl, hwH⟩
    let z : Point (skewDim e) := z0 + ψ t
    have hwform : b0 + φ t = joinPoints z v0 := by
      calc
        b0 + φ t = joinPoints z0 v0 + joinPoints (ψ t) 0 := by simp [b0, φ]
        _ = joinPoints (z0 + ψ t) (v0 + 0) := (joinPoints_add _ _ _ _).symm
        _ = joinPoints z v0 := by simp [z]
    have hfirst : firstPoint (b0 + φ t) = z := by
      rw [hwform]
      ext i
      simp [firstPoint, joinPoints, z]
    have hHz : MvPolynomial.aeval z H ≠ 0 := by
      have h := hwH
      rw [eval_rulingOpenPolynomial] at h
      simpa only [hfirst] using h
    have hψK : E (ψ t) = 0 := (kEquiv.symm t).property
    have hEz : E z = E z0 := by
      change E (z0 + ψ t) = E z0
      rw [map_add, hψK, add_zero]
    have hzflat : z ∈ evaluationFlat C p := by
      rw [hflat]
      exact hEz
    have hzwork : z ∈ workingPoints V H := ⟨hflatV hzflat, hHz⟩
    obtain ⟨v, hrule, hv, hpv⟩ := (R.full_parameter_fibers p hpimage z hzwork).mp hzflat
    change joinPoints z v ∈ Γ.points ∧ _ at hrule
    have hva : v a = 1 := by
      have hn := R.normalized (joinPoints z v) hrule.1
      simpa [secondPoint, joinPoints] using hn
    have hvEq := direction_unique z z0 v v0 hv hv0 hva hva0 (hpv.trans hpGraph.symm)
    subst v
    have hwΓ : b0 + φ t ∈ Γ.points := by
      rw [hwform]
      exact hrule.1
    have hF :
        (fun i => MvPolynomial.aeval (b0 + φ t) (rulingGraphPolynomials C i)) ≠ 0 :=
      rulingGraphPolynomials_nonzero C V Γ H a R _ hwΓ
    have hGcoord :
        (fun i => MvPolynomial.aeval (b0 + φ t) (rulingGraphPolynomials C i)) =
          graphVector C z v0 := by
      have h := eval_rulingGraphPolynomials C (b0 + φ t)
      rw [hfirst, show secondPoint (b0 + φ t) = v0 by
        rw [hwform]; ext i; simp [secondPoint, joinPoints]] at h
      exact h
    have hpw : graphParameter C z v0 hv0 = p := hpv
    have hproj :
        Projectivization.mk ℂ
          (fun i => MvPolynomial.aeval (b0 + φ t) (rulingGraphPolynomials C i)) hF = p := by
      have hgv := graphVector_ne_zero C z v0 hv0
      have hmk : Projectivization.mk ℂ
          (fun i => MvPolynomial.aeval (b0 + φ t) (rulingGraphPolynomials C i)) hF =
            Projectivization.mk ℂ (graphVector C z v0) hgv := by
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hF hgv).2
        exact ⟨1, by simpa only [one_smul] using hGcoord.symm⟩
      exact hmk.trans hpw
    exact ⟨hwΓ, hwH, hF, hproj⟩

/-- B01's specialized fiber computation, from the explicit affine linear coordinates
and the shared principal-open dimension interface. -/
theorem ruling_polynomial_projective_fiber_dimension (p : ProjectivePoint (e + e))
    (hp : p ∈ polynomialProjectiveImage Γ (rulingOpenPolynomial H) (rulingGraphPolynomials C)) :
    (AffineVariety.closure (polynomialProjectiveFiber Γ (rulingOpenPolynomial H)
      (rulingGraphPolynomials C) p)).dimension = flatDim e := by
  obtain ⟨b, φ, hφ, hfib⟩ := ruling_polynomial_projective_fiber_coordinates C V Γ H a R p hp
  obtain ⟨w, hw, hwg, hF, hproj⟩ := hp
  have hwfib : w ∈ polynomialProjectiveFiber Γ (rulingOpenPolynomial H) (rulingGraphPolynomials C) p :=
    ⟨hw, hwg, hF, hproj⟩
  rw [hfib] at hwfib
  obtain ⟨t0, rfl, ht0⟩ := hwfib
  rw [hfib]
  exact Request.affine_linear_principal_open_dimension b φ hφ (rulingOpenPolynomial H) t0 ht0

theorem parameterClosure_irreducible : (parameterClosure C Γ H).IsIrreducible := by
  rw [parameterClosure, ← ruling_polynomial_projective_image C V Γ H a R]
  exact polynomialProjectiveImage_irreducible Γ R.incidence_irreducible
    (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R)
    (rulingGraphPolynomials C) (fun w hw _ => rulingGraphPolynomials_nonzero C V Γ H a R w hw)

end Ruling
#print axioms parameterClosure_irreducible
#print axioms parameterClosure_subset_quadric
end
end DistinctDistances.TrackB
