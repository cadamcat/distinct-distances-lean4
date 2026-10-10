import DistinctDistances.TrackA.Projection
import DistinctDistances.Framework

namespace DistinctDistances.TrackA
noncomputable section
open Filter
open scoped BigOperators Classical Topology

def radialMapDegree {d : ℕ} (p : Point d) (Y : AffineVariety d) : ℕ :=
  if h : ∃ r, GenericallyFiniteRadialDegree p Y r then h.choose else 0

def groupDepth {d : ℕ} (p : Point d) (J : AffineFamily.Family d) (Y : AffineVariety d) : ℕ :=
  ∑ Z ∈ J.filter (fun Z => radialImage p Z = radialImage p Y), radialMapDegree p Z

def projectedFamily {d : ℕ} (p : Point d) (J : AffineFamily.Family d) :
    ProjectiveFamily.Family d := J.image (radialImage p)

def joiningLine {d : ℕ} (x y : Point d) : Set (Point d) :=
  {z | ∃ t : ℂ, z = x + t • (y-x)}

def movingRoots {d : ℕ} (x y : Point d) (J : AffineFamily.Family d) : Set (Point d) :=
  {z | z ∈ (AffineFamily.locus J).points ∧ z ∈ joiningLine x y ∧ z ≠ x ∧ z ≠ y}

/-- Generic affine line meetings of an actual fixed target list.
A nonzero polynomial on X×Y certifies a nonempty principal open of pairs. -/
def GenericMovingRootBound {d : ℕ} (X Y : AffineVariety d)
    (J : AffineFamily.Family d) (q : ℕ) : Prop :=
  ∃ H : Poly (d+d),
    (∃ x ∈ X.points, ∃ y ∈ Y.points, MvPolynomial.eval (Fin.append x y) H ≠ 0) ∧
    ∀ x ∈ X.points, ∀ y ∈ Y.points, MvPolynomial.eval (Fin.append x y) H ≠ 0 →
      x ≠ y ∧ (movingRoots x y J).Finite ∧ (movingRoots x y J).ncard ≤ q

abbrev BinaryForm (d : ℕ) := MvPolynomial (Fin 2) (Poly d)

def binaryCoeff {R : Type*} [CommSemiring R] (F : MvPolynomial (Fin 2) R) (a b : ℕ) : R :=
  F.coeff (Finsupp.single 0 a + Finsupp.single 1 b)

def binaryGcd {F : Type*} [Field F] (f g : MvPolynomial (Fin 2) F) :
    MvPolynomial (Fin 2) F := by
  letI : NormalizedGCDMonoid (MvPolynomial (Fin 2) F) := Classical.arbitrary _
  exact gcd f g

/-- Matrix of (a,b) ↦ aF+bG for degree-L binary forms; rows index the
degree-(2L-1) monomials by their V exponent. -/
def sylvesterMatrix {R : Type*} [CommRing R] (L : ℕ)
    (F G : MvPolynomial (Fin 2) R) : Matrix (Fin (2*L)) (Fin (2*L)) R :=
  fun i j =>
    if j.val < L then
      if j.val ≤ i.val ∧ i.val-j.val ≤ L then binaryCoeff F (L-(i.val-j.val)) (i.val-j.val)
      else 0
    else
      let a := j.val-L
      if a ≤ i.val ∧ i.val-a ≤ L then binaryCoeff G (L-(i.val-a)) (i.val-a)
      else 0

def specializeBinary {d : ℕ} (F : BinaryForm d) (p : Point d) : Poly 2 :=
  MvPolynomial.map (MvPolynomial.eval p) F

def GenericMatrixRank {d a b : ℕ} (X : AffineVariety d)
    (A : Matrix (Fin a) (Fin b) (Poly d)) (r : ℕ) : Prop :=
  (∀ (rows : Fin (r+1) ↪ Fin a) (cols : Fin (r+1) ↪ Fin b),
    Matrix.det (A.submatrix rows cols) ∈ X.ideal) ∧
  ∃ (rows : Fin r ↪ Fin a) (cols : Fin r ↪ Fin b), Matrix.det (A.submatrix rows cols) ∉ X.ideal

def genericGcdDegree {d : ℕ} (X : AffineVariety d) (hX : X.IsIrreducible)
    (F G : BinaryForm d) : ℕ := by
  letI : X.ideal.IsPrime := hX
  let K := FractionRing (Poly d ⧸ X.ideal)
  let f : Poly d →+* K := (algebraMap (Poly d ⧸ X.ideal) K).comp (Ideal.Quotient.mk X.ideal)
  exact (binaryGcd (MvPolynomial.map f F) (MvPolynomial.map f G)).totalDegree

/-- Data of a fixed positive-dimensional target plateau. All component
assignments precede later incidence deletions and adaptive subcollections. -/
structure SeparatedDepthData {d : ℕ} (regime : Regime d) (j : ℕ) where
  j_pos : 1 ≤ j
  j_lt : j < d
  s : ℕ → ℝ
  v : ℕ → ℝ
  s_grows : Tendsto s (atTop : Filter ℕ) (atTop : Filter ℝ)
  v_grows : Tendsto v (atTop : Filter ℕ) (atTop : Filter ℝ)
  s_small : Framework.LittleO s (fun i => Real.log (regime.B i))
  v_small : Framework.LittleO v (fun i => Real.log (regime.B i))
  separated : Tendsto (fun i => v i / s i) atTop (𝓝 0) ∨
    Tendsto (fun i => s i / v i) atTop (𝓝 0)
  b : Fin d → ℝ
  b_sorted : Monotone b
  b_sum : ∑ t, b t = 0
  centers : ℕ → Finset (Point d)
  targets : ℕ → Finset (Point d)
  centers_subsample : ∀ i, centers i ⊆ (regime.P i).image OAI.ErdosDistinctDistances.complexPoint
  targets_subsample : ∀ i, targets i ⊆ (regime.P i).image OAI.ErdosDistinctDistances.complexPoint
  carriers : ℕ → AffineFamily.Family d
  carrier_pure : ∀ i, AffineFamily.IsPure (carriers i) (d-j)
  owner : ℕ → Point d → AffineVariety d
  owner_member : ∀ i q, q ∈ targets i → owner i q ∈ carriers i
  owner_contains : ∀ i q, q ∈ targets i → q ∈ (owner i q).points
  pathEquations : ℕ → Finset (Poly d)
  path_component : ∀ i Y, Y ∈ carriers i →
    Y.IsComponentOf (Ideal.span (pathEquations i : Set (Poly d)))
  path_degree : ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in atTop,
    ∀ f ∈ pathEquations i, (f.totalDegree : ℝ) ≤ regime.B i * Real.exp (C*s i)
  source_size : Framework.ExpEquivalent (fun _ => Unit)
    (fun i _ => (centers i).card) (fun i _ => regime.N i) v
  target_size : Framework.ExpEquivalent (fun _ => Unit)
    (fun i _ => (targets i).card) (fun i _ => regime.N i) s

namespace SeparatedDepthData
variable {d j : ℕ} {regime : Regime d} (D : SeparatedDepthData regime j)

def mass (i : ℕ) (Y : AffineVariety d) : ℕ :=
  ((D.targets i).filter (fun q => D.owner i q = Y)).card

def submass (i : ℕ) (J : AffineFamily.Family d) : ℝ := ∑ Y ∈ J, (D.mass i Y : ℝ)

def cutDegree (i : ℕ) (t : Fin d) : ℝ := regime.B i * Real.exp (D.b t * D.s i)
def degreeBudget (i : ℕ) : ℝ := ∏ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), D.cutDegree i t
def tailBudget (i : ℕ) : ℝ := ∏ t ∈ Finset.univ.filter (fun t : Fin d => j ≤ t.val), D.cutDegree i t
def firstRate (i : ℕ) : ℝ := D.cutDegree i ⟨0, by have := D.j_pos; have := D.j_lt; omega⟩
def narrowRate (i : ℕ) : ℝ := regime.B i * Real.exp (-D.s i * ∑ t ∈
  Finset.univ.filter (fun t : Fin d => j ≤ t.val), D.b t)
def wideRate (i : ℕ) : ℝ := regime.B i * Real.exp (-2*D.s i)

def incidenceMass (i : ℕ) (bad : Finset (Point d × AffineVariety d)) : ℝ :=
  (∑ a ∈ bad, (D.mass i a.2 : ℝ)) / ((D.centers i).card * (D.targets i).card : ℝ)

def retained (i : ℕ) (bad : Finset (Point d × AffineVariety d)) (p : Point d) :
    AffineFamily.Family d := (D.carriers i).filter (fun Y => (p,Y) ∉ bad)

def deletedRowMass (i : ℕ) (bad : Finset (Point d × AffineVariety d)) (p : Point d) : ℝ :=
  ∑ Y ∈ (D.carriers i).filter (fun Y => (p,Y) ∈ bad), (D.mass i Y : ℝ)

def DegreeBudgets : Prop :=
  Framework.ExpUpper (fun _ => Unit)
    (fun i _ => (AffineFamily.degree (D.carriers i) : ℝ)) (fun i _ => D.degreeBudget i) D.s ∧
  Framework.ExpUpper (fun i => {J : AffineFamily.Family d // J ⊆ D.carriers i})
    (fun i J => D.submass i J.val)
    (fun i J => (AffineFamily.degree J.val : ℝ) * D.tailBudget i) D.s

/-- Exact small-mass deletion and adaptive degree conclusion. Rho is fixed
after deletion; its eventual-index threshold is allowed to depend on rho. -/
def ProjectedDegreeConclusion (R : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∃ (bad : ℕ → Finset (Point d × AffineVariety d)) (badCenters : ℕ → Finset (Point d)),
    (∀ i, bad i ⊆ (D.centers i).product (D.carriers i) ∧ badCenters i ⊆ D.centers i) ∧
    Framework.LittleO (fun i => D.incidenceMass i (bad i)) (fun _ => 1) ∧
    Framework.LittleO (fun i => ((badCenters i).card : ℝ)) (fun i => (D.centers i).card) ∧
    Framework.UniformLittleO
      (fun i => {p : Point d // p ∈ D.centers i ∧ p ∉ badCenters i})
      (fun i p => D.deletedRowMass i (bad i) p.val) (fun i _ => (D.targets i).card) ∧
    (∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
      ∀ Y ∈ D.retained i (bad i) p, (radialImage p Y).dimension = d-j) ∧
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
      ∀ J : AffineFamily.Family d, J ⊆ D.retained i (bad i) p →
        ρ * ((D.targets i).card : ℝ) ≤ D.submass i J →
        D.degreeBudget i / R i * Real.exp (-ε * D.s i) ≤
          (ProjectiveFamily.degree (projectedFamily p J) : ℝ)

def NegligibleSafeDepth (R : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
  ∃ bad : ℕ → Finset (Point d × AffineVariety d),
    (∀ i, bad i ⊆ (D.centers i).product (D.carriers i)) ∧
    Framework.LittleO (fun i => D.incidenceMass i (bad i)) (fun _ => 1) ∧
    ∀ᶠ i in atTop, ∀ p ∈ D.centers i, ∀ Y ∈ D.retained i (bad i) p,
      (radialImage p Y).dimension = d-j ∧ Y.multiplicity p ≤ Y.degree / 2 ∧
      (groupDepth p (D.retained i (bad i) p) Y : ℝ) ≤ R i * Real.exp (η * D.s i)

end SeparatedDepthData

end
end DistinctDistances.TrackA
