import DistinctDistances.TrackB.SegreClosureSupport
import DistinctDistances.TrackB.TangentLineSupport

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators
open LinearMap (BilinForm)

def pointCovectorLinear (e : ℕ) : Point e →ₗ[ℂ] Module.Dual ℂ (Point e) where
  toFun := covectorOfPoint
  map_add' v w := by
    ext x
    simp [covectorOfPoint, LinearMap.sum_apply, LinearMap.smul_apply,
      Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext x
    simp [covectorOfPoint, LinearMap.sum_apply, LinearMap.smul_apply,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def covectorPointLinear (e : ℕ) : Module.Dual ℂ (Point e) →ₗ[ℂ] Point e where
  toFun := pointOfCovector
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem covectorPointLinear_apply {e : ℕ} (y : Module.Dual ℂ (Point e)) :
    covectorPointLinear e y = pointOfCovector y := rfl

def coordinateWedgeForm {e : ℕ} (i : Fin e) :
    Module.Dual ℂ (Point e) →ₗ[ℂ] alternatingForms (U := Point e) where
  toFun y := ⟨BilinForm.linMulLin (LinearMap.proj i) y -
    BilinForm.linMulLin y (LinearMap.proj i), by
      intro v
      simp [BilinForm.linMulLin_apply]
      ring⟩
  map_add' y z := by
    apply Subtype.ext
    apply BilinForm.ext
    intro v w
    simp only [Submodule.coe_add, LinearMap.sub_apply, LinearMap.add_apply,
      BilinForm.linMulLin_apply]
    ring
  map_smul' c y := by
    apply Subtype.ext
    apply BilinForm.ext
    intro v w
    simp only [Submodule.coe_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      BilinForm.linMulLin_apply, RingHom.id_apply, smul_eq_mul]
    ring

def coordinateWedge {e : ℕ} (C : SkewCoordinates e) (i : Fin e) :
    Point e →ₗ[ℂ] Point (skewDim e) :=
  C.decode.symm.toLinearMap.comp ((coordinateWedgeForm i).comp (pointCovectorLinear e))

/-- Explicit spanning vectors for the incidence fiber, including t=0. -/
def incidenceChartVector {e : ℕ} (C : SkewCoordinates e) (i : Fin e)
    (v : Point e) (p : Point (e + e)) (u : Point (skewDim e + 1)) :
    Point (skewDim e + 1) :=
  Fin.cons (u 0 * firstPoint p i)
    (u 0 • coordinateWedge C i (secondPoint p) + v i • Fin.tail u -
      coordinateWedge C i (pointOfCovector ((C.decode (Fin.tail u)).val v)))

def secondBlockLinear (e : ℕ) : Point (e + e) →ₗ[ℂ] Point e :=
  LinearMap.pi (fun k => LinearMap.proj (Fin.natAdd e k))

theorem secondBlockLinear_apply {e : ℕ} (p : Point (e + e)) :
    secondBlockLinear e p = secondPoint p := rfl

def incidenceChartTailLinear {e : ℕ} (C : SkewCoordinates e) (i : Fin e)
    (j : Fin (e + e)) (u : Point (skewDim e + 1)) :
    Point (e * (e + e)) →ₗ[ℂ] Point (skewDim e) :=
  u 0 • (coordinateWedge C i).comp ((secondBlockLinear e).comp (segreRow i)) +
    LinearMap.smulRight (LinearMap.proj (finProdFinEquiv (i, j))) (Fin.tail u) -
    (coordinateWedge C i).comp ((covectorPointLinear e).comp
      (LinearMap.comp (C.decode (Fin.tail u)).val (segreColumn j)))

/-- At a fixed fiber vector this formula is linear in the Segre base coordinates. -/
def incidenceChartLinear {e : ℕ} (C : SkewCoordinates e) (i : Fin e)
    (j : Fin (e + e)) (u : Point (skewDim e + 1)) :
    Point (e * (e + e)) →ₗ[ℂ] Point (skewDim e + 1) :=
  LinearMap.pi (Fin.cons
    (u 0 • LinearMap.proj (finProdFinEquiv (i, Fin.castAdd e i)))
    (fun k => (LinearMap.proj k).comp (incidenceChartTailLinear C i j u)))

theorem incidenceChartLinear_apply {e : ℕ} (C : SkewCoordinates e) (i : Fin e)
    (j : Fin (e + e)) (u : Point (skewDim e + 1)) (b : Point (e * (e + e))) :
    incidenceChartLinear C i j u b =
      incidenceChartVector C i (segreColumn j b) (segreRow i b) u := by
  funext k
  cases k using Fin.cases <;>
    simp [incidenceChartLinear, incidenceChartTailLinear, incidenceChartVector,
      secondBlockLinear_apply, covectorPointLinear_apply, segreColumn, segreRow,
      firstPoint, secondPoint]

/-- incidenceCondition is independent of the chosen nonzero representatives. -/
theorem incidenceCondition_mk_iff {e : ℕ} (C : SkewCoordinates e)
    (v : Point e) (p : Point (e + e)) (x : Point (skewDim e + 1))
    (hv : v ≠ 0) (hp : p ≠ 0) (hx : x ≠ 0) :
    incidenceCondition C (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ p hp)
      (Projectivization.mk ℂ x hx) ↔
    ∃ t : ℂ, firstPoint p = t • v ∧ covectorOfPoint (secondPoint p) v = 0 ∧
      (x 0, C.decode (Fin.tail x)) ∈ incidenceFiber v t (covectorOfPoint (secondPoint p)) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ p hp
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  let α : ℂ := a
  let β : ℂ := b
  let γ : ℂ := c
  have hdrep : (Projectivization.mk ℂ v hv).rep = α • v := by
    simpa only [α, Units.smul_def] using ha.symm
  have hprep : (Projectivization.mk ℂ p hp).rep = β • p := by
    simpa only [β, Units.smul_def] using hb.symm
  have hxrep : (Projectivization.mk ℂ x hx).rep = γ • x := by
    simpa only [γ, Units.smul_def] using hc.symm
  let y : Module.Dual ℂ (Point e) := covectorOfPoint (secondPoint p)
  let D : alternatingForms (U := Point e) := C.decode (Fin.tail x)
  have hfirstp : firstPoint (β • p) = β • firstPoint p := by
    funext i
    simp [firstPoint, Pi.smul_apply]
  have hsecondp : secondPoint (β • p) = β • secondPoint p := by
    funext i
    simp [secondPoint, Pi.smul_apply]
  have hY : covectorOfPoint (secondPoint (β • p)) = β • y := by
    change pointCovectorLinear e (secondPoint (β • p)) = _
    rw [hsecondp]
    exact (pointCovectorLinear e).map_smul β (secondPoint p)
  have hx0 : (γ • x) 0 = γ * x 0 := by
    simp [Pi.smul_apply, smul_eq_mul]
  have hD : C.decode (Fin.tail (γ • x)) = γ • D := by
    have htail : Fin.tail (γ • x) = γ • Fin.tail x := by
      funext i
      change (γ • x) (Fin.succ i) = γ * x (Fin.succ i)
      simp [Pi.smul_apply, smul_eq_mul]
    rw [htail]
    exact C.decode.map_smul γ (Fin.tail x)
  have hYeval : (β • y) (α • v) = (α * β) * y v := by
    simp only [LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
    ring
  have hEvalScale :
      homogeneousEvaluation (α • v) (γ * x 0, γ • D) =
        (γ * x 0, (α * γ) • alternatingEvaluation v D) := by
    apply Prod.ext
    · rfl
    · change (γ • D).val (α • v) = (α * γ) • D.val v
      simp only [Submodule.coe_smul, LinearMap.smul_apply, LinearMap.map_smul,
        smul_smul, smul_eq_mul]
      congr 1
      ring
  have hα : α ≠ 0 := by simp [α]
  have hβ : β ≠ 0 := by simp [β]
  have hγ : γ ≠ 0 := by simp [γ]
  simp only [incidenceCondition]
  rw [hdrep, hprep, hxrep, hfirstp, hY, hx0, hD]
  constructor
  · rintro ⟨t₀, ht₀, hy₀, hmem₀⟩
    let t : ℂ := α * t₀ / β
    have ht : firstPoint p = t • v := by
      funext i
      have hcoord := congrFun ht₀ i
      dsimp [t]
      simp only [Pi.smul_apply, smul_eq_mul] at hcoord ⊢
      field_simp [hβ]
      linear_combination hcoord
    have hy : y v = 0 := by
      rw [hYeval] at hy₀
      exact (mul_eq_zero.mp hy₀).resolve_left (mul_ne_zero hα hβ)
    change homogeneousEvaluation (α • v) (γ * x 0, γ • D) ∈
      Submodule.span ℂ {(t₀, β • y)} at hmem₀
    rw [hEvalScale, Submodule.mem_span_singleton] at hmem₀
    rcases hmem₀ with ⟨s, hs⟩
    have hfst : γ * x 0 = s * t₀ := by
      have h := congrArg Prod.fst hs
      simpa [smul_eq_mul] using h.symm
    have hsnd : (α * γ) • alternatingEvaluation v D = s • (β • y) := by
      have h := congrArg Prod.snd hs
      simpa [smul_smul] using h.symm
    let r : ℂ := (α * γ)⁻¹ * s * β
    have hDspan : alternatingEvaluation v D = r • y := by
      have hαγ : α * γ ≠ 0 := mul_ne_zero hα hγ
      have h := congrArg (fun z : Module.Dual ℂ (Point e) => (α * γ)⁻¹ • z) hsnd
      simp only [smul_smul] at h
      rw [inv_mul_cancel₀ hαγ, one_smul] at h
      simpa [r, mul_assoc] using h
    have hfstspan : x 0 = r * t := by
      dsimp [r, t]
      field_simp [hα, hβ, hγ] at hfst ⊢
      linear_combination hfst
    have hfiber : (x 0, D) ∈ incidenceFiber v t y := by
      change (x 0, alternatingEvaluation v D) ∈ Submodule.span ℂ {(t, y)}
      rw [Submodule.mem_span_singleton]
      refine ⟨r, ?_⟩
      apply Prod.ext
      · change r * t = x 0
        exact hfstspan.symm
      · change r • y = alternatingEvaluation v D
        exact hDspan.symm
    exact ⟨t, ht, hy, hfiber⟩
  · rintro ⟨t, ht, hy, hfiber⟩
    let t₀ : ℂ := β * t / α
    have ht₀ : firstPoint (β • p) = t₀ • (α • v) := by
      calc
        firstPoint (β • p) = β • firstPoint p := hfirstp
        _ = β • (t • v) := by rw [ht]
        _ = (β * t) • v := by rw [smul_smul]
        _ = t₀ • (α • v) := by
          funext i
          dsimp [t₀]
          change β * t * v i = (β * t / α) * (α * v i)
          field_simp [hα]
    have hy₀ : (β • y) (α • v) = 0 := by
      rw [hYeval, hy]
      simp
    change (x 0, alternatingEvaluation v D) ∈ Submodule.span ℂ {(t, y)} at hfiber
    rw [Submodule.mem_span_singleton] at hfiber
    rcases hfiber with ⟨s, hs⟩
    have hfst : x 0 = s * t := by
      have h := congrArg Prod.fst hs
      simpa [smul_eq_mul] using h.symm
    have hsnd : alternatingEvaluation v D = s • y := by
      have h := congrArg Prod.snd hs
      simpa [smul_smul] using h.symm
    let r' : ℂ := α * γ * s / β
    have hscaled :
        (γ * x 0, (α * γ) • alternatingEvaluation v D) =
          r' • (t₀, β • y) := by
      apply Prod.ext
      · dsimp [r', t₀]
        rw [hfst]
        field_simp [hα, hβ, hγ]
      · rw [hsnd]
        dsimp [r']
        simp only [smul_smul]
        congr 1
        field_simp [hβ]
    have hmem₀ : homogeneousEvaluation (α • v) (γ * x 0, γ • D) ∈
        Submodule.span ℂ {(t₀, β • y)} := by
      rw [hEvalScale, Submodule.mem_span_singleton]
      exact ⟨r', hscaled.symm⟩
    exact ⟨t₀, ht₀, hy₀, hmem₀⟩

private theorem coordinateWedge_apply {e : ℕ} (C : SkewCoordinates e)
    (i : Fin e) (y : Point e) (v w : Point e) :
    ((C.decode (coordinateWedge C i y)).val v) w =
      v i * covectorOfPoint y w - covectorOfPoint y v * w i := by
  have h : C.decode (coordinateWedge C i y) = coordinateWedgeForm i
      (covectorOfPoint y) := by
    simp [coordinateWedge, pointCovectorLinear]
  have hval := congrArg Subtype.val h
  have happly := congrArg (fun B : BilinForm ℂ (Point e) => B v w) hval
  simpa [coordinateWedgeForm, BilinForm.linMulLin_apply,
    LinearMap.proj_apply] using happly

/-- the explicit vectors belong to the linear incidence fiber. -/
theorem incidenceChartVector_mem {e : ℕ} (C : SkewCoordinates e) (i : Fin e)
    (v : Point e) (p : Point (e + e)) (t : ℂ)
    (ht : firstPoint p = t • v) (hy : covectorOfPoint (secondPoint p) v = 0)
    (u : Point (skewDim e + 1)) :
    ((incidenceChartVector C i v p u) 0,
      C.decode (Fin.tail (incidenceChartVector C i v p u))) ∈
      incidenceFiber v t (covectorOfPoint (secondPoint p)) := by
  let y : Module.Dual ℂ (Point e) := covectorOfPoint (secondPoint p)
  let D₀ : alternatingForms (U := Point e) := C.decode (Fin.tail u)
  let q : Point e := pointOfCovector (D₀.val v)
  have hD₀ : D₀.val v v = 0 := D₀.2.self_eq_zero v
  have hq : covectorOfPoint q = D₀.val v := by
    exact covector_point_inverse (D₀.val v)
  have hEval : (C.decode (Fin.tail (incidenceChartVector C i v p u))).val v =
      (u 0 * v i) • y := by
    have hlin : alternatingEvaluation v
        (u 0 • C.decode (coordinateWedge C i (secondPoint p)) +
          v i • D₀ - C.decode (coordinateWedge C i q)) = (u 0 * v i) • y := by
      apply LinearMap.ext
      intro w
      change u 0 * ((C.decode (coordinateWedge C i (secondPoint p))).val v w) +
          v i * (D₀.val v w) -
          ((C.decode (coordinateWedge C i q)).val v w) =
        u 0 * v i * y w
      rw [coordinateWedge_apply, coordinateWedge_apply, hq]
      simp only [y]
      rw [hy, hD₀]
      ring
    have hdecode : C.decode (Fin.tail (incidenceChartVector C i v p u)) =
        u 0 • C.decode (coordinateWedge C i (secondPoint p)) +
          v i • D₀ - C.decode (coordinateWedge C i q) := by
      simp [incidenceChartVector, D₀, q]
    rw [hdecode]
    exact hlin
  have hfirst : (incidenceChartVector C i v p u) 0 = (u 0 * v i) * t := by
    simp only [incidenceChartVector, Fin.cons_zero]
    have hi := congrFun ht i
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      congrArg (fun a : ℂ => u 0 * a) hi
  change homogeneousEvaluation v
      ((incidenceChartVector C i v p u) 0,
        C.decode (Fin.tail (incidenceChartVector C i v p u))) ∈
      Submodule.span ℂ {(t, y)}
  rw [Submodule.mem_span_singleton]
  refine ⟨u 0 * v i, ?_⟩
  have hpair : homogeneousEvaluation v
      ((incidenceChartVector C i v p u) 0,
        C.decode (Fin.tail (incidenceChartVector C i v p u))) =
      (u 0 * v i) • (t, y) := by
    apply Prod.ext
    · change (incidenceChartVector C i v p u) 0 = (u 0 * v i) * t
      rw [hfirst]
    · change alternatingEvaluation v
        (C.decode (Fin.tail (incidenceChartVector C i v p u))) = _
      exact hEval
  exact hpair.symm

/-- where v_i≠0 these vectors span the complete fiber, with no smooth-base input. -/
theorem incidenceChartVector_surjective {e : ℕ} (C : SkewCoordinates e) (i : Fin e)
    (v : Point e) (p : Point (e + e)) (t : ℂ)
    (ht : firstPoint p = t • v) (hy : covectorOfPoint (secondPoint p) v = 0)
    (hvi : v i ≠ 0) (x : Point (skewDim e + 1))
    (hx : (x 0, C.decode (Fin.tail x)) ∈ incidenceFiber v t (covectorOfPoint (secondPoint p))) :
    ∃ u : Point (skewDim e + 1), incidenceChartVector C i v p u = x := by
  let y : Module.Dual ℂ (Point e) := covectorOfPoint (secondPoint p)
  let D : alternatingForms (U := Point e) := C.decode (Fin.tail x)
  change homogeneousEvaluation v (x 0, D) ∈ Submodule.span ℂ {(t, y)} at hx
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨q, hq⟩ := hx
  have hx0 : q * t = x 0 := by
    have h := congrArg Prod.fst hq
    change q * t = x 0 at h
    exact h
  have hDy : q • y = D.val v := by
    have h := congrArg Prod.snd hq
    simpa [homogeneousEvaluation, alternatingEvaluation] using h
  let a : ℂ := v i
  let u : Point (skewDim e + 1) := Fin.cons (q / a) (a⁻¹ • Fin.tail x)
  have hD₀ : C.decode (Fin.tail u) = a⁻¹ • D := by
    simp [u, D, a]
  have hEvalD₀ : (C.decode (Fin.tail u)).val v = a⁻¹ • (q • y) := by
    rw [hD₀]
    simp only [Submodule.coe_smul, LinearMap.smul_apply, LinearMap.map_smul]
    rw [hDy]
  have hpoint : pointOfCovector ((C.decode (Fin.tail u)).val v) =
      a⁻¹ • (q • secondPoint p) := by
    rw [hEvalD₀]
    change covectorPointLinear e (a⁻¹ • (q • y)) = _
    rw [(covectorPointLinear e).map_smul, (covectorPointLinear e).map_smul]
    simp only [y, covectorPointLinear_apply, point_covector_inverse]
  have hcorrection : coordinateWedge C i
      (pointOfCovector ((C.decode (Fin.tail u)).val v)) =
      a⁻¹ • (q • coordinateWedge C i (secondPoint p)) := by
    rw [hpoint]
    simp only [(coordinateWedge C i).map_smul]
  have htail : (q / a) • coordinateWedge C i (secondPoint p) +
      a • (a⁻¹ • Fin.tail x) -
        a⁻¹ • (q • coordinateWedge C i (secondPoint p)) = Fin.tail x := by
    ext k
    change (q / a) * (coordinateWedge C i (secondPoint p)) k +
      a * (a⁻¹ * Fin.tail x k) -
        a⁻¹ * (q * (coordinateWedge C i (secondPoint p)) k) = Fin.tail x k
    field_simp [a, hvi]
    ring
  refine ⟨u, ?_⟩
  ext k
  cases k using Fin.cases with
  | zero =>
      change (q / a) * firstPoint p i = x 0
      have hi : firstPoint p i = t * v i := by
        simpa [Pi.smul_apply, smul_eq_mul] using congrFun ht i
      rw [hi]
      field_simp [a, hvi]
      linear_combination a * hx0
  | succ k =>
      change (q / a) • coordinateWedge C i (secondPoint p) k +
          a • (a⁻¹ • Fin.tail x) k -
            coordinateWedge C i
              (pointOfCovector ((C.decode (Fin.tail u)).val v)) k =
        Fin.tail x k
      rw [hcorrection]
      exact congrFun htail k

/-- above the parameter open the fiber is the actual projective flat closure. -/
theorem incidenceCondition_flatClosure {e : ℕ} (C : SkewCoordinates e)
    (d : ProjectivePoint e) (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (hdp : (d, p) ∈ resolutionPairs e) (x : ProjectivePoint (skewDim e + 1))
    (hx : incidenceCondition C d p x) :
    x ∈ (ProjectiveVariety.closure (affineEmbedding '' evaluationFlat C p)).points := by
  rcases hx with ⟨t, ht, hy, hfiber⟩
  let y : Module.Dual ℂ (Point e) := covectorOfPoint (secondPoint p.rep)
  let D : alternatingForms (U := Point e) := C.decode (Fin.tail x.rep)
  change homogeneousEvaluation d.rep (x.rep 0, D) ∈ Submodule.span ℂ {(t, y)} at hfiber
  rw [Submodule.mem_span_singleton] at hfiber
  obtain ⟨q, hq⟩ := hfiber
  have hfirst : q * t = x.rep 0 := by
    have h := congrArg Prod.fst hq
    change q * t = x.rep 0 at h
    exact h
  have hsecond : q • y = D.val d.rep := by
    have h := congrArg Prod.snd hq
    simpa [homogeneousEvaluation, alternatingEvaluation] using h
  have heval : D.val (firstPoint p.rep) = x.rep 0 • y := by
    calc
      D.val (firstPoint p.rep) = D.val (t • d.rep) := by rw [ht]
      _ = t • D.val d.rep := (D.val).map_smul t d.rep
      _ = t • (q • y) := by rw [hsecond]
      _ = (t * q) • y := by rw [smul_smul]
      _ = (q * t) • y := by congr 1 <;> ring
      _ = x.rep 0 • y := by rw [hfirst]
  rw [evaluationFlat_projectiveClosure C p hp]
  exact heval

/-- the literal graph belongs to the full incidence, before base restriction. -/
theorem graph_incidenceCondition {e : ℕ} (C : SkewCoordinates e)
    (z : Point (skewDim e)) (v : Point e) (hv : v ≠ 0) :
    incidenceCondition C (Projectivization.mk ℂ v hv) (graphParameter C z v hv)
      (affineEmbedding z) := by
  let W : Point (e + e) := graphVector C z v
  let X : Point (skewDim e + 1) := Fin.cons (1 : ℂ) z
  have hW : W ≠ 0 := graphVector_ne_zero C z v hv
  have hxrep : X ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa [X] using h0)
  have hsecond : secondPoint W = pointOfCovector ((C.decode z).val v) := by
    ext i
    change Fin.addCases v (pointOfCovector ((C.decode z).val v)) (Fin.natAdd e i) =
      pointOfCovector ((C.decode z).val v) i
    exact Fin.addCases_right (m := e) (n := e) (motive := fun _ => ℂ)
      (left := v) (right := pointOfCovector ((C.decode z).val v)) i
  have hy : covectorOfPoint (secondPoint W) v = 0 := by
    rw [hsecond, covector_point_inverse]
    exact (C.decode z).2.self_eq_zero v
  have hcov : covectorOfPoint (secondPoint W) = (C.decode z).val v := by
    rw [hsecond, covector_point_inverse]
  have hfiber :
      (X 0, C.decode (Fin.tail X)) ∈
        incidenceFiber v 1 (covectorOfPoint (secondPoint W)) := by
    change homogeneousEvaluation v (X 0, C.decode (Fin.tail X)) ∈
      Submodule.span ℂ {(1, covectorOfPoint (secondPoint W))}
    have hX0 : X 0 = 1 := by simp [X]
    have hXtail : Fin.tail X = z := by simp [X]
    rw [hX0, hXtail]
    change homogeneousEvaluation v (1, C.decode z) ∈
      Submodule.span ℂ {(1, covectorOfPoint (secondPoint W))}
    rw [Submodule.mem_span_singleton]
    refine ⟨1, ?_⟩
    simp [homogeneousEvaluation, alternatingEvaluation, hcov, smul_eq_mul]
  have hraw : incidenceCondition C
      (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ W hW)
      (Projectivization.mk ℂ X hxrep) := by
    apply (incidenceCondition_mk_iff C v W X hv hW hxrep).2
    refine ⟨1, ?_, hy, hfiber⟩
    have hfirst : firstPoint W = v := by
      ext i
      simp [W, graphVector, firstPoint, joinPoints]
    simpa using hfirst
  simpa [W, X, graphParameter, affineEmbedding] using hraw

end
end DistinctDistances.TrackB
