import DistinctDistances.Foundations

/-! Definitions for track A's consumer-specialized theorem statements.
Geometric bounds are theorem conclusions, never fields of these definitions. -/

namespace DistinctDistances.TrackA

noncomputable section
open scoped BigOperators Classical Topology

/-- Elementary polynomial vanishing order; it is distinct from variety multiplicity. -/
def OrderAtLeast {n : ℕ} {F : Type*} [Field F]
    (f : FieldPoly n F) (x : FieldPoint n F) (r : ℕ) : Prop :=
  f ∈ pointIdealOver x ^ r

def IsolatedPoints {n : ℕ} {F : Type*} [Field F]
    (E : Set (FieldPoly n F)) (S : Finset (FieldPoint n F)) : Prop :=
  ∀ x ∈ S, pointIdealOver x ∈ (Ideal.span E).minimalPrimes

abbrev OriginLocalRing (n : ℕ) (F : Type*) [Field F] :=
  Localization.AtPrime (pointIdealOver (0 : FieldPoint n F))

/-- Union-of-systems hypothesis, with overlapping components counted once. -/
def FromAffineLists {n : ℕ} (F : AffineFamily.Family n) (L : ℕ) : Prop :=
  ∃ (r : ℕ) (lists : Fin r → AffineFamily.Family n) (bounds : Fin r → ℕ),
    (∀ i, 1 ≤ bounds i ∧ AffineFamily.ComponentsDefinedInDegree (lists i) (bounds i)) ∧
    (∀ V, V ∈ F ↔ ∃ i, V ∈ lists i) ∧ L = ∑ i, bounds i

def FromProjectiveLists {n : ℕ} (F : ProjectiveFamily.Family n) (L : ℕ) : Prop :=
  ∃ (r : ℕ) (lists : Fin r → ProjectiveFamily.Family n) (bounds : Fin r → ℕ),
    (∀ i, 1 ≤ bounds i ∧ ProjectiveFamily.ComponentsDefinedInDegree (lists i) (bounds i)) ∧
    (∀ V, V ∈ F ↔ ∃ i, V ∈ lists i) ∧ L = ∑ i, bounds i

def affineWeightedDegree {n : ℕ} (F : AffineFamily.Family n) (L : ℕ) : ℚ :=
  ∑ V ∈ F, V.degree * (L : ℚ) ^ V.dimension

def projectiveWeightedDegree {n : ℕ} (F : ProjectiveFamily.Family n) (L : ℕ) : ℚ :=
  ∑ V ∈ F, V.degree * (L : ℚ) ^ V.dimension

def boundedJacobianKernel {n : ℕ} (F : AffineFamily.Family n) (D : ℕ) (x : Point n) :
    Submodule ℂ (Point n) :=
  ⨅ f : {f : Poly n // f ∈ (AffineFamily.locus F).ideal ∧ f.totalDegree ≤ D},
    LinearMap.ker (differential f.val x)

/-- A principal dense open on an irreducible component tests the bounded equations. -/
def GenericJacobianRank {n : ℕ} (F : AffineFamily.Family n) (V : AffineVariety n)
    (D k : ℕ) : Prop :=
  ∃ g : Poly n, g ∉ V.ideal ∧ ∀ x ∈ V.points, MvPolynomial.eval x g ≠ 0 →
    Module.finrank ℂ (boundedJacobianKernel F D x) = k

def equationLocus {n : ℕ} (E : List (Poly n)) : AffineVariety n :=
  AffineVariety.ofIdeal (Ideal.span {f | f ∈ E})

def SameGermAt {n : ℕ} (V W : AffineVariety n) (x : Point n) : Prop :=
  ∀ᶠ y : Point n in nhds x, (y ∈ V ↔ y ∈ W)

def jacobian {n : ℕ} (E : List (Poly n)) : Matrix (Fin E.length) (Fin n) (Poly n) :=
  fun i j => MvPolynomial.pderiv j (E.get i)

def jacobianMinors {n : ℕ} (E : List (Poly n)) (q : ℕ) : Set (Poly n) :=
  {f | ∃ (rows : Fin q ↪ Fin E.length) (cols : Fin q ↪ Fin n),
    f = Matrix.det ((jacobian E).submatrix rows cols)}

def componentLength {n : ℕ} (I : Ideal (Poly n)) (V : AffineVariety n)
    (hV : V.IsIrreducible) : ℕ∞ := by
  letI : V.ideal.IsPrime := hV
  exact Module.length (Localization.AtPrime V.ideal)
    (Localization.AtPrime V.ideal ⧸ I.map
      (algebraMap (Poly n) (Localization.AtPrime V.ideal)))

def FiniteAffineProjection {n m : ℕ} (φ : AffineProjection n m) (V : AffineVariety n) : Prop :=
  let f : Poly m →+* (Poly n ⧸ V.ideal) :=
    (Ideal.Quotient.mk V.ideal).comp φ.pullback.toRingHom
  letI : Algebra (Poly m) (Poly n ⧸ V.ideal) := f.toAlgebra
  letI : Module (Poly m) (Poly n ⧸ V.ideal) := Algebra.toModule
  Module.Finite (Poly m) (Poly n ⧸ V.ideal)

def ProjectiveMapDefinedOn {n m : ℕ} (φ : LinearProjection n m) (V : ProjectiveVariety n) : Prop :=
  ∀ p ∈ V.points, φ p.rep ≠ 0

def projectiveMap {n m : ℕ} (φ : LinearProjection n m) (p : ProjectivePoint n)
    (hp : φ p.rep ≠ 0) : ProjectivePoint m := Projectivization.mk ℂ (φ p.rep) hp

def projectiveFiber {n m : ℕ} (φ : LinearProjection n m) (V : ProjectiveVariety n)
    (z : ProjectivePoint m) : Set (ProjectivePoint n) :=
  {p | p ∈ V.points ∧ ∃ hp : φ p.rep ≠ 0, projectiveMap φ p hp = z}

def GenericallyFiniteProjectiveDegree {n m : ℕ} (φ : LinearProjection n m)
    (V : ProjectiveVariety n) (r : ℕ) : Prop :=
  0 < r ∧ ∃ (g : Poly m) (D : ℕ), g.IsHomogeneous D ∧ g ∉ (projectiveImage φ V).ideal ∧
    ∀ z ∈ (projectiveImage φ V).points, MvPolynomial.eval z.rep g ≠ 0 →
      (projectiveFiber φ V z).Finite ∧ (projectiveFiber φ V z).ncard = r

def FiniteProjectiveProjection {n m : ℕ} (φ : LinearProjection n m)
    (V : ProjectiveVariety n) : Prop :=
  ProjectiveMapDefinedOn φ V ∧ FiniteAffineProjection ⟨φ, 0⟩ V.affineCone


end
end DistinctDistances.TrackA
