import DistinctDistances.TrackB.GeometryModel
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

def lineRestriction {n : ℕ} (p v : Point n) : Poly n →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X)

theorem eval_lineRestriction {n : ℕ} (p v : Point n) (t : ℂ) (f : Poly n) :
    Polynomial.eval t (lineRestriction p v f) = MvPolynomial.aeval (p + t • v) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [lineRestriction]
  | add f g hf hg => simp only [map_add, Polynomial.eval_add, hf, hg]
  | mul_X f i hf =>
      rw [map_mul, Polynomial.eval_mul, hf]
      simp only [lineRestriction, MvPolynomial.aeval_X, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        map_mul, MvPolynomial.aeval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

theorem coeff_zero_lineRestriction {n : ℕ} (p v : Point n) (f : Poly n) :
    (lineRestriction p v f).coeff 0 = MvPolynomial.aeval p f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa using eval_lineRestriction p v 0 f

theorem differential_add {n : ℕ} (f g : Poly n) (p v : Point n) :
    differential (f + g) p v = differential f p v + differential g p v := by
  simp [differential, LinearMap.sum_apply, LinearMap.smul_apply, add_mul,
    Finset.sum_add_distrib]

theorem differential_mul_X {n : ℕ} (f : Poly n) (i : Fin n) (p v : Point n) :
    differential (f * MvPolynomial.X i) p v =
      p i * differential f p v + MvPolynomial.aeval p f * v i := by
  classical
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, MvPolynomial.pderiv_mul, map_add, map_mul,
    MvPolynomial.aeval_X, MvPolynomial.pderiv_X]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp [Pi.single_apply]

theorem coeff_one_lineRestriction {n : ℕ} (p v : Point n) (f : Poly n) :
    (lineRestriction p v f).coeff 1 = differential f p v := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [lineRestriction, differential, LinearMap.sum_apply]
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg, differential_add]
  | mul_X f i hf =>
      rw [map_mul, Polynomial.mul_coeff_one, coeff_zero_lineRestriction, hf]
      simp [lineRestriction, differential_mul_X] <;> ring

/-- A line contained in the actual point locus supplies a Zariski tangent direction. -/
theorem line_direction_mem_tangent {n : ℕ} (V : AffineVariety n) (p v : Point n)
    (hline : ∀ t : ℂ, p + t • v ∈ V.points) : v ∈ V.tangentSpace p := by
  change v ∈ ⨅ f : V.ideal, LinearMap.ker (differential f.val p)
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro f
  have hz : lineRestriction p v f.val = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hall : {t : ℂ | Polynomial.IsRoot (lineRestriction p v f.val) t} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro t
      change Polynomial.eval t (lineRestriction p v f.val) = 0
      rw [eval_lineRestriction]
      exact hline t f.val f.property
    rw [hall]
    exact Set.infinite_univ
  rw [← coeff_one_lineRestriction, hz, Polynomial.coeff_zero]

theorem zero_mem_projective_cone {n : ℕ} (T : Set (ProjectivePoint n))
    (hT : T.Nonempty) : (0 : Point n) ∈ (ProjectiveVariety.closure T).affineCone.points := by
  obtain ⟨p, hp⟩ := hT
  intro f hf
  have hpoly : lineRestriction 0 p.rep f = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := ({(0 : ℂ)} : Set ℂ)ᶜ)
      ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro t ht
    have ht0 : t ≠ 0 := by simpa using ht
    have htv : t • p.rep ≠ 0 := smul_ne_zero ht0 p.rep_nonzero
    have heq : Projectivization.mk ℂ (t • p.rep) htv = p := by
      calc
        _ = Projectivization.mk ℂ p.rep p.rep_nonzero :=
          (Projectivization.mk_eq_mk_iff' ℂ (t • p.rep) p.rep htv p.rep_nonzero).2 ⟨t, rfl⟩
        _ = p := p.mk_rep
    change Polynomial.eval t (lineRestriction 0 p.rep f) = 0
    rw [eval_lineRestriction, zero_add]
    exact hf (t • p.rep) ⟨htv, heq.symm ▸ hp⟩
  have hz := congrArg (Polynomial.eval (0 : ℂ)) hpoly
  simpa only [eval_lineRestriction, zero_smul, zero_add, Polynomial.eval_zero] using hz

theorem parameterValue_smul {e : ℕ} (t : ℂ) (w : Point (e + e)) :
    parameterValue (t • w) = t ^ 2 * parameterValue w := by
  simp only [parameterValue, covectorOfPoint, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, firstPoint, secondPoint,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem parameterQuadric_mk {e : ℕ} (w : Point (e + e)) (hw : w ≠ 0)
    (hq : parameterValue w = 0) : Projectivization.mk ℂ w hw ∈ parameterQuadric e := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ w hw
  have hrep : (Projectivization.mk ℂ w hw).rep = (u : ℂ) • w := by
    simpa only [Units.smul_def] using hu.symm
  change parameterValue (Projectivization.mk ℂ w hw).rep = 0
  rw [hrep, parameterValue_smul, hq, mul_zero]

theorem parameterQuadric_cone_mem {e : ℕ} (p : ProjectivePoint (e + e))
    (hp : p ∈ parameterQuadric e) (w : Point (e + e)) (hw : parameterValue w = 0) :
    w ∈ (ProjectiveVariety.closure (parameterQuadric e)).affineCone.points := by
  by_cases hw0 : w = 0
  · subst w
    exact zero_mem_projective_cone _ ⟨p, hp⟩
  · apply (ProjectiveVariety.mem_points_mk_iff _ w hw0).mp
    exact ProjectiveVariety.subset_closure _ (parameterQuadric_mk w hw0 hw)

theorem covector_point_inverse {e : ℕ} (f : Module.Dual ℂ (Point e)) :
    covectorOfPoint (pointOfCovector f) = f := by
  apply LinearMap.ext
  intro v
  have hv : v = ∑ i : Fin e, v i • Pi.single i 1 := by
    ext i
    simp [Pi.single_apply]
  rw [hv]
  simp [covectorOfPoint, pointOfCovector, Pi.single_apply]

theorem point_covector_inverse {e : ℕ} (v : Point e) :
    pointOfCovector (covectorOfPoint v) = v := by
  ext i
  simp [pointOfCovector, covectorOfPoint, Pi.single_apply]

theorem joinPoints_eta {n m : ℕ} (w : Point (n + m)) :
    joinPoints (firstPoint w) (secondPoint w) = w := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [joinPoints, firstPoint]
  · intro j; simp [joinPoints, secondPoint]

theorem joinPoints_add {n m : ℕ} (v w : Point n) (y z : Point m) :
    joinPoints (v + w) (y + z) = joinPoints v y + joinPoints w z := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [joinPoints]

theorem joinPoints_smul {n m : ℕ} (t : ℂ) (v : Point n) (y : Point m) :
    joinPoints (t • v) (t • y) = t • joinPoints v y := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [joinPoints]

theorem pointOfCovector_add {e : ℕ} (f g : Module.Dual ℂ (Point e)) :
    pointOfCovector (f + g) = pointOfCovector f + pointOfCovector g := by
  rfl

theorem pointOfCovector_smul {e : ℕ} (t : ℂ) (f : Module.Dual ℂ (Point e)) :
    pointOfCovector (t • f) = t • pointOfCovector f := by
  rfl

theorem parameterValue_join {e : ℕ} (v : Point e) (f : Module.Dual ℂ (Point e)) :
    parameterValue (joinPoints v (pointOfCovector f)) = f v := by
  have hfirst : firstPoint (n := e) (m := e) (joinPoints v (pointOfCovector f)) = v := by
    ext i; simp [firstPoint, joinPoints]
  have hsecond : secondPoint (n := e) (m := e) (joinPoints v (pointOfCovector f)) =
      pointOfCovector f := by
    funext i
    change Fin.addCases v (pointOfCovector f) (Fin.natAdd e i) = pointOfCovector f i
    exact Fin.addCases_right (m := e) (n := e) (motive := fun _ => ℂ)
      (left := v) (right := pointOfCovector f) i
  rw [parameterValue, hfirst, hsecond, covector_point_inverse]

theorem graph_direction_mem_quadric_tangent {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (z0 : Point (skewDim e)) (hz0 : z0 ∈ evaluationFlat C p) (dv : Point e) :
    joinPoints dv (pointOfCovector ((C.decode z0).val dv)) ∈
      (ProjectiveVariety.closure (parameterQuadric e)).affineCone.tangentSpace p.rep := by
  apply line_direction_mem_tangent
  intro t
  apply parameterQuadric_cone_mem p hp.1
  have hpgraph : p.rep = joinPoints (firstPoint p.rep)
      (pointOfCovector ((C.decode z0).val (firstPoint p.rep))) := by
    rw [show (C.decode z0).val (firstPoint p.rep) =
      covectorOfPoint (secondPoint p.rep) from hz0, point_covector_inverse, joinPoints_eta]
  have heq : p.rep + t • joinPoints dv (pointOfCovector ((C.decode z0).val dv)) =
      joinPoints (firstPoint p.rep + t • dv)
        (pointOfCovector ((C.decode z0).val (firstPoint p.rep + t • dv))) := by
    conv_lhs => rw [hpgraph]
    simp only [map_add, map_smul, pointOfCovector_add, pointOfCovector_smul,
      joinPoints_add, joinPoints_smul]
  rw [heq, parameterValue_join]
  exact (C.decode z0).property _

theorem vertical_direction_mem_quadric_tangent {e : ℕ}
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (dy : Module.Dual ℂ (Point e)) (hdy : dy (firstPoint p.rep) = 0) :
    joinPoints (0 : Point e) (pointOfCovector dy) ∈
      (ProjectiveVariety.closure (parameterQuadric e)).affineCone.tangentSpace p.rep := by
  apply line_direction_mem_tangent
  intro t
  apply parameterQuadric_cone_mem p hp.1
  have heq : p.rep + t • joinPoints (0 : Point e) (pointOfCovector dy) =
      joinPoints (firstPoint p.rep)
        (pointOfCovector (covectorOfPoint (secondPoint p.rep) + t • dy)) := by
    simp only [pointOfCovector_add, pointOfCovector_smul, point_covector_inverse]
    conv_lhs => rw [← joinPoints_eta p.rep]
    rw [← joinPoints_smul, ← joinPoints_add, smul_zero, add_zero]
  rw [heq, parameterValue_join]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, hdy, smul_zero, add_zero]
  exact hp.1

#print axioms line_direction_mem_tangent
#print axioms parameterQuadric_cone_mem

end
end DistinctDistances.TrackB
