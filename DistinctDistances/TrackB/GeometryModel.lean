import DistinctDistances.Foundations
import DistinctDistances.TrackB.EvaluationFibers

/-!
Concrete evaluation-flat and ruling inputs in the shared variety model. No dimension,
degree, tangent or multiplicity model is replaced here. The ruling predicate contains
the hypotheses supplied by conc:rulings; it contains no parameter-degree estimate,
Segre identity or isotropic-classification conclusion.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open LinearMap (BilinForm)

def skewDim (e : ℕ) : ℕ := e.choose 2
def flatDim (e : ℕ) : ℕ := (e - 1).choose 2

/-- A linear coordinate choice for S. Degree remains the shared Hilbert degree. -/
structure SkewCoordinates (e : ℕ) where
  decode : Point (skewDim e) ≃ₗ[ℂ] alternatingForms (U := Point e)

private theorem updateVector2_zero {α : Type*} (x y z : α) :
    Function.update (![x, y] : Fin 2 → α) 0 z = ![z, y] := by
  funext i
  fin_cases i <;> simp

private theorem updateVector2_one {α : Type*} (x y z : α) :
    Function.update (![x, y] : Fin 2 → α) 1 z = ![x, z] := by
  funext i
  fin_cases i <;> simp

private def alternatingMapToBilin {e : ℕ}
    (A : Point e [⋀^Fin 2]→ₗ[ℂ] ℂ) : BilinForm ℂ (Point e) := by
  classical
  refine LinearMap.mk₂ ℂ (fun x y => A ![x, y]) ?_ ?_ ?_ ?_
  · intro x y z
    simpa only [updateVector2_zero] using A.map_update_add (![x, z]) (0 : Fin 2) x y
  · intro c x y
    simpa only [updateVector2_zero] using A.map_update_smul (![x, y]) (0 : Fin 2) c x
  · intro x y z
    simpa only [updateVector2_one] using A.map_update_add (![x, y]) (1 : Fin 2) y z
  · intro c x y
    simpa only [updateVector2_one] using A.map_update_smul (![x, y]) (1 : Fin 2) c y

private def formMultilinear {e : ℕ}
    (D : alternatingForms (U := Point e)) :
    MultilinearMap ℂ (fun _ : Fin 2 => Point e) ℂ := by
  classical
  refine MultilinearMap.mk (fun v => D.1 (v 0) (v 1)) ?_ ?_
  · rintro _ v i x y
    fin_cases i
    · simpa using congrArg (fun f : Module.Dual ℂ (Point e) => f (v 1))
        (D.1.map_add (v 0) x y)
    · simpa using (D.1 (v 0)).map_add x y
  · rintro _ v i c x
    fin_cases i
    · simpa using congrArg (fun f : Module.Dual ℂ (Point e) => f (v 1))
        (D.1.map_smul c x)
    · simpa using (D.1 (v 0)).map_smul c x

private def formToAlternatingMap {e : ℕ}
    (D : alternatingForms (U := Point e)) : Point e [⋀^Fin 2]→ₗ[ℂ] ℂ := by
  refine ⟨formMultilinear D, ?_⟩
  intro v i j hij hne
  fin_cases i <;> fin_cases j
  · simp at hne
  · change D.1 (v 0) (v 1) = 0
    calc
      D.1 (v 0) (v 1) = D.1 (v 0) (v 0) := congrArg (D.1 (v 0)) hij.symm
      _ = 0 := D.2.self_eq_zero (v 0)
  · change D.1 (v 0) (v 1) = 0
    calc
      D.1 (v 0) (v 1) = D.1 (v 0) (v 0) := congrArg (D.1 (v 0)) hij
      _ = 0 := D.2.self_eq_zero (v 0)
  · simp at hne

private def alternatingMapToForm {e : ℕ}
    (A : Point e [⋀^Fin 2]→ₗ[ℂ] ℂ) : alternatingForms (U := Point e) := by
  refine ⟨alternatingMapToBilin A, ?_⟩
  intro x
  change A ![x, x] = 0
  exact A.map_eq_zero_of_eq' ![x, x] 0 1 rfl (by decide)

private def alternatingFormsLinearEquiv (e : ℕ) :
    alternatingForms (U := Point e) ≃ₗ[ℂ] Point e [⋀^Fin 2]→ₗ[ℂ] ℂ where
  toFun := formToAlternatingMap
  invFun := alternatingMapToForm
  left_inv D := by
    apply Subtype.ext
    apply LinearMap.BilinForm.ext
    intro x y
    rfl
  right_inv A := by
    apply AlternatingMap.ext
    intro v
    change A ![v 0, v 1] = A v
    congr 1
    ext i
    fin_cases i <;> simp
  map_add' D E := by
    apply AlternatingMap.ext
    intro v
    rfl
  map_smul' c D := by
    apply AlternatingMap.ext
    intro v
    rfl

private theorem alternatingForms_finrank (e : ℕ) :
    Module.finrank ℂ (alternatingForms (U := Point e)) = e.choose 2 := by
  have h := LinearEquiv.finrank_eq
    ((alternatingFormsLinearEquiv e).trans
      (exteriorPower.alternatingMapLinearEquiv (R := ℂ) (n := 2)))
  change Module.finrank ℂ (alternatingForms (U := Point e)) =
    Module.finrank ℂ (Module.Dual ℂ (⋀[ℂ]^2 (Point e))) at h
  rw [Subspace.dual_finrank_eq, exteriorPower.finrank_eq] at h
  simpa [Point, Module.finrank_fin_fun] using h

/-- The coordinate choice exists in every dimension, including the zero-dimensional cases. -/
theorem skewCoordinates_exists (e : ℕ) : Nonempty (SkewCoordinates e) := by
  classical
  letI : Module.Free ℂ (alternatingForms (U := Point e)) :=
    Module.Free.of_equiv
      (((alternatingFormsLinearEquiv e).trans
        (exteriorPower.alternatingMapLinearEquiv (R := ℂ) (n := 2))).symm)
  refine ⟨⟨LinearEquiv.ofFinrankEq _ _ ?_⟩⟩
  change Module.finrank ℂ (Fin (Nat.choose e 2) → ℂ) =
    Module.finrank ℂ (alternatingForms (U := Point e))
  rw [Module.finrank_fin_fun]
  exact (alternatingForms_finrank e).symm

def joinPoints {n m : ℕ} (x : Point n) (y : Point m) : Point (n + m) := Fin.addCases x y
def firstPoint {n m : ℕ} (x : Point (n + m)) : Point n := fun i => x (Fin.castAdd m i)
def secondPoint {n m : ℕ} (x : Point (n + m)) : Point m := fun i => x (Fin.natAdd n i)

def covectorOfPoint {e : ℕ} (y : Point e) : Module.Dual ℂ (Point e) :=
  ∑ i : Fin e, y i • LinearMap.proj i

def pointOfCovector {e : ℕ} (y : Module.Dual ℂ (Point e)) : Point e :=
  fun i => y (Pi.single i 1)

def parameterValue {e : ℕ} (w : Point (e + e)) : ℂ :=
  covectorOfPoint (secondPoint w) (firstPoint w)

def parameterQuadric (e : ℕ) : Set (ProjectivePoint (e + e)) :=
  {p | parameterValue p.rep = 0}

def affineParameters (e : ℕ) : Set (ProjectivePoint (e + e)) :=
  {p | p ∈ parameterQuadric e ∧ firstPoint p.rep ≠ 0}

def evaluationFlat {e : ℕ} (C : SkewCoordinates e) (p : ProjectivePoint (e + e)) :
    Set (Point (skewDim e)) :=
  {z | (C.decode z).val (firstPoint p.rep) = covectorOfPoint (secondPoint p.rep)}

def graphVector {e : ℕ} (C : SkewCoordinates e) (z : Point (skewDim e))
    (v : Point e) : Point (e + e) :=
  joinPoints v (pointOfCovector ((C.decode z).val v))

theorem graphVector_ne_zero {e : ℕ} (C : SkewCoordinates e) (z : Point (skewDim e))
    (v : Point e) (hv : v ≠ 0) : graphVector C z v ≠ 0 := by
  intro h
  apply hv
  have hfirst : firstPoint (graphVector C z v) = v := by
    ext i
    simp [firstPoint, graphVector, joinPoints]
  calc
    v = firstPoint (graphVector C z v) := hfirst.symm
    _ = firstPoint 0 := congrArg firstPoint h
    _ = 0 := rfl

def graphParameter {e : ℕ} (C : SkewCoordinates e) (z : Point (skewDim e))
    (v : Point e) (hv : v ≠ 0) : ProjectivePoint (e + e) :=
  Projectivization.mk ℂ (graphVector C z v) (graphVector_ne_zero C z v hv)

def workingPoints {e : ℕ} (V : AffineVariety (skewDim e)) (H : Poly (skewDim e)) :
    Set (Point (skewDim e)) := {z | z ∈ V ∧ MvPolynomial.aeval z H ≠ 0}

def rulingPoints {e : ℕ} (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    Set (Point (skewDim e + e)) :=
  {w | w ∈ Γ ∧ MvPolynomial.aeval (firstPoint w) H ≠ 0}

def directionFiber {e : ℕ} (Γ : AffineVariety (skewDim e + e)) (z : Point (skewDim e)) :
    Set (Point e) := {v | joinPoints z v ∈ Γ}

def IsAffineLine {e : ℕ} (T : Set (Point e)) : Prop :=
  ∃ b a : Point e, a ≠ 0 ∧ T = {v | ∃ t : ℂ, v = b + t • a}

def parameterImage {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    Set (ProjectivePoint (e + e)) :=
  {p | ∃ z v, joinPoints z v ∈ rulingPoints Γ H ∧
    ∃ hv : v ≠ 0, graphParameter C z v hv = p}

def parameterClosure {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    ProjectiveVariety (e + e) := ProjectiveVariety.closure (parameterImage C Γ H)

def pointProjection (e : ℕ) : Point (skewDim e + e) →ₗ[ℂ] Point (skewDim e) where
  toFun := firstPoint
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Exactly the ruling properties used in the degree proof. Fiber bound N is explicit;
the producer conc:rulings supplies an N depending only on e. -/
structure IsRulingIncidence {e : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (j N : ℕ) : Prop where
  variety_irreducible : V.IsIrreducible
  incidence_irreducible : Γ.IsIrreducible
  nonzero_section : H ∉ V.ideal
  fiber_cases : j ≤ 1
  bound_positive : 1 ≤ N
  incidence_dimension : Γ.dimension = V.dimension + j
  normalized : ∀ w ∈ Γ.points, secondPoint w a = 1
  point_containment : ∀ w ∈ Γ.points, firstPoint w ∈ V
  dominant : ∀ z ∈ workingPoints V H, (directionFiber Γ z).Nonempty
  smooth : ∀ w ∈ rulingPoints Γ H,
    Γ.IsSmoothAt w ∧ V.IsSmoothAt (firstPoint w) ∧
      (Γ.tangentSpace w).map (pointProjection e) = V.tangentSpace (firstPoint w)
  finite_fiber : j = 0 → ∀ z ∈ workingPoints V H,
    (directionFiber Γ z).Finite ∧ (directionFiber Γ z).ncard ≤ N
  line_fiber : j = 1 → ∀ z ∈ workingPoints V H, IsAffineLine (directionFiber Γ z)
  codimension_one : j = 1 → V.dimension + 1 = skewDim e
  actual_flats : ∀ z v, joinPoints z v ∈ rulingPoints Γ H →
    ∀ hv : v ≠ 0, evaluationFlat C (graphParameter C z v hv) ⊆ V.points
  full_parameter_fibers : ∀ p ∈ parameterImage C Γ H, ∀ z ∈ workingPoints V H,
    z ∈ evaluationFlat C p ↔ ∃ v, joinPoints z v ∈ rulingPoints Γ H ∧
      ∃ hv : v ≠ 0, graphParameter C z v hv = p

def linearProjectivePlane {n : ℕ} (L : Submodule ℂ (Point n)) : ProjectiveVariety n :=
  ProjectiveVariety.closure {p | ∃ x ∈ L, ∃ hx : x ≠ 0, Projectivization.mk ℂ x hx = p}

def IsMaximalIsotropic {e : ℕ} (L : Submodule ℂ (Point (e + e))) : Prop :=
  Module.finrank ℂ L = e ∧ ∀ x ∈ L, parameterValue x = 0

end
end DistinctDistances.TrackB
