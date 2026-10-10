import DistinctDistances.Bridges.ComplexLineModel
import DistinctDistances.TrackC.Basic
import DistinctDistances.TrackE.Basic

/-! Complex affine lines recover their real affine lines, giving an injective lift. -/

namespace DistinctDistances.Bridges

noncomputable section

theorem cplx_injective {n : ℕ} : Function.Injective (cplx : RPoint n → Point n) := by
  intro x y he
  ext i
  exact Complex.ofReal_injective (congrFun he i)

theorem cplx_add {n : ℕ} (x y : RPoint n) : cplx (x + y) = cplx x + cplx y := by
  funext i
  simp [cplx]

theorem cplx_smul {n : ℕ} (r : ℝ) (x : RPoint n) : cplx (r • x) = (r : ℂ) • cplx x := by
  funext i
  simp [cplx]

theorem realLine_parameters (l : TrackC.Line 3) :
    ∃ a v : RPoint 3, v ≠ 0 ∧
      (l.val : Set (RPoint 3)) = {x | ∃ t : ℝ, x = a + t • v} := by
  classical
  obtain ⟨a, ha⟩ := l.property.1
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one
    (R := ℝ) (M := l.val.direction) l.property.2
  let w : l.val.direction := e 1
  have hw : w ≠ 0 := by
    intro hz
    exact one_ne_zero (e.injective (hz.trans e.map_zero.symm))
  let v : RPoint 3 := w.val
  have hv : v ≠ 0 := fun hz => hw (Subtype.ext hz)
  refine ⟨a, v, hv, ?_⟩
  ext x
  change (x ∈ l.val) ↔ ∃ t : ℝ, x = a + t • v
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem ha x]
  change (x - a ∈ l.val.direction) ↔ ∃ t : ℝ, x = a + t • v
  constructor
  · intro hx
    let u : l.val.direction := ⟨x - a, hx⟩
    let t := e.symm u
    have ht : t • w = u := by
      dsimp only [w]
      rw [← e.map_smul, smul_eq_mul, mul_one]
      exact e.apply_symm_apply u
    have hsub : x - a = t • v := (congrArg Subtype.val ht).symm
    refine ⟨t, ?_⟩
    calc
      x = t • v + a := sub_eq_iff_eq_add.mp hsub
      _ = a + t • v := add_comm _ _
  · rintro ⟨t, rfl⟩
    rw [add_sub_cancel_left]
    exact l.val.direction.smul_mem t w.property

def realLineBase (l : TrackC.Line 3) : RPoint 3 := (realLine_parameters l).choose

def realLineVector (l : TrackC.Line 3) : RPoint 3 := (realLine_parameters l).choose_spec.choose

theorem realLineVector_ne_zero (l : TrackC.Line 3) : realLineVector l ≠ 0 :=
  (realLine_parameters l).choose_spec.choose_spec.1

theorem realLine_parameter_set (l : TrackC.Line 3) :
    (l.val : Set (RPoint 3)) = {x | ∃ t : ℝ, x = realLineBase l + t • realLineVector l} :=
  (realLine_parameters l).choose_spec.choose_spec.2

theorem realLine_pivot (l : TrackC.Line 3) : ∃ j : Fin 3, realLineVector l j ≠ 0 := by
  by_contra h
  push Not at h
  apply realLineVector_ne_zero l
  ext j
  exact h j

def realLineLift (l : TrackC.Line 3) : AffineVariety 3 :=
  complexLine (cplx (realLineBase l)) (cplx (realLineVector l))

theorem cplx_line_param_iff {n : ℕ} (a v : RPoint n) (j : Fin n) (hj : v j ≠ 0)
    (x : RPoint n) :
    (∃ t : ℂ, cplx x = cplx a + t • cplx v) ↔ ∃ r : ℝ, x = a + r • v := by
  constructor
  · rintro ⟨t, he⟩
    have hcoord := congrFun he j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cplx] at hcoord
    have him := congrArg Complex.im hcoord
    simp only [Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      mul_zero, zero_add] at him
    have ht : t.im = 0 := (mul_eq_zero.mp him.symm).resolve_right hj
    have hr : (t.re : ℂ) = t := by
      apply Complex.ext <;> simp [ht]
    refine ⟨t.re, cplx_injective ?_⟩
    simpa only [cplx_add, cplx_smul, hr] using he
  · rintro ⟨r, rfl⟩
    refine ⟨(r : ℂ), ?_⟩
    rw [cplx_add, cplx_smul]

theorem realLineLift_mem_iff (l : TrackC.Line 3) (x : RPoint 3) :
    cplx x ∈ (realLineLift l).points ↔ x ∈ l.val := by
  obtain ⟨j, hj⟩ := realLine_pivot l
  have hjC : cplx (realLineVector l) j ≠ 0 := by
    change ((realLineVector l j : ℝ) : ℂ) ≠ 0
    exact_mod_cast hj
  rw [realLineLift, complexLine_points _ _ j hjC]
  change (∃ t : ℂ, cplx x = cplx (realLineBase l) + t • cplx (realLineVector l)) ↔
    x ∈ (l.val : Set (RPoint 3))
  rw [realLine_parameter_set l]
  exact cplx_line_param_iff _ _ j hj x

theorem realLineLift_injective : Function.Injective realLineLift := by
  intro l m he
  apply Subtype.ext
  apply AffineSubspace.ext
  intro x
  rw [← realLineLift_mem_iff l x, ← realLineLift_mem_iff m x, he]

theorem realLineLift_irreducible (l : TrackC.Line 3) : (realLineLift l).IsIrreducible :=
  complexLine_irreducible _ _

theorem realLineLift_dimension_degree (l : TrackC.Line 3) :
    (realLineLift l).dimension = 1 ∧ (realLineLift l).degree = 1 := by
  obtain ⟨j, hj⟩ := realLine_pivot l
  have hjC : cplx (realLineVector l) j ≠ 0 := by
    change ((realLineVector l j : ℝ) : ℂ) ≠ 0
    exact_mod_cast hj
  exact ⟨complexLine_dimension _ _ j hjC, complexLine_degree _ _ j hjC⟩

theorem realLineLift_points_infinite (l : TrackC.Line 3) : (realLineLift l).points.Infinite := by
  obtain ⟨j, hj⟩ := realLine_pivot l
  have hjC : cplx (realLineVector l) j ≠ 0 := by
    change ((realLineVector l j : ℝ) : ℂ) ≠ 0
    exact_mod_cast hj
  exact complexLine_points_infinite _ _ j hjC

def realLinePullback (l : TrackC.Line 3) : TrackC.Poly 3 →ₐ[ℝ] MvPolynomial (Fin 1) ℝ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (realLineBase l i) +
    MvPolynomial.C (realLineVector l i) * MvPolynomial.X 0)

theorem realLinePullback_map (l : TrackC.Line 3) (f : TrackC.Poly 3) :
    linePullback (cplx (realLineBase l)) (cplx (realLineVector l))
        (MvPolynomial.map (algebraMap ℝ ℂ) f) =
      MvPolynomial.map (algebraMap ℝ ℂ) (realLinePullback l f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [linePullback, realLinePullback]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, MvPolynomial.map_X]
    rw [hf]
    congr 1
    simp [linePullback, realLinePullback, cplx]

theorem realLinePullback_eq_zero (l : TrackC.Line 3) (f : TrackC.Poly 3)
    (h : TrackC.onPolynomial f l) : realLinePullback l f = 0 := by
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have hmem : realLineBase l + x 0 • realLineVector l ∈ l.val := by
    change realLineBase l + x 0 • realLineVector l ∈ (l.val : Set (RPoint 3))
    rw [realLine_parameter_set l]
    exact ⟨x 0, rfl⟩
  have hz := h (realLineBase l + x 0 • realLineVector l) hmem
  have he : MvPolynomial.eval x (realLinePullback l f) =
      TrackC.evalR f (realLineBase l + x 0 • realLineVector l) := by
    change MvPolynomial.aeval x (realLinePullback l f) =
      MvPolynomial.aeval (realLineBase l + x 0 • realLineVector l) f
    rw [realLinePullback, MvPolynomial.comp_aeval_apply]
    apply congrArg (fun ys : Fin 3 → ℝ => MvPolynomial.aeval ys f)
    funext i
    simp [smul_eq_mul, mul_comm]
  exact he.trans hz

theorem realLineLift_onPolynomial (l : TrackC.Line 3) (f : TrackC.Poly 3)
    (h : TrackC.onPolynomial f l) :
    MvPolynomial.map (algebraMap ℝ ℂ) f ∈ (realLineLift l).ideal := by
  change linePullback (cplx (realLineBase l)) (cplx (realLineVector l))
    (MvPolynomial.map (algebraMap ℝ ℂ) f) = 0
  rw [realLinePullback_map, realLinePullback_eq_zero l f h, map_zero]

end
end DistinctDistances.Bridges
