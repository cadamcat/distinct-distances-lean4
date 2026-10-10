import DistinctDistances.TrackA.DepthDefinitions

/-! Inputs consumed from profiles.tex, secants.tex and reduction.tex.
These predicates describe actual samples, equations, flat caps and generic
lists. Actual-center depth bounds are supplied by theorems in Depth.lean. -/

namespace DistinctDistances.TrackA
noncomputable section
open Filter
open scoped BigOperators Classical Topology

abbrev ProperFlat (d : ℕ) :=
  {a : Point d × Submodule ℂ (Point d) // Module.finrank ℂ a.2 < d}

namespace SeparatedDepthData
variable {d j : ℕ} {regime : Regime d} (D : SeparatedDepthData regime j)

def UniformFlatCap : Prop :=
  Framework.UniformLittleO (fun _ => ProperFlat d)
    (fun i a => ((D.centers i).filter (fun p => p-a.val.1 ∈ a.val.2)).card)
    (fun i _ => (D.centers i).card)

def InitialNoCapture : Prop :=
  ∀ q : ℕ, Framework.UniformLittleO
    (fun _ => {f : Poly d // f ≠ 0 ∧ f.totalDegree ≤ q})
    (fun i f => ((D.centers i).filter (fun p => MvPolynomial.eval p f.val = 0)).card)
    (fun i _ => (D.centers i).card)

/-- Profiles' first-carrier regularity; the original equations need not
have independent differentials. Smoothness is a property of their reduced locus. -/
def FirstCutInput : Prop :=
  ∃ (E : ℕ → Finset (Poly d)) (bad : ℕ → Finset (Point d)),
    (∀ i, bad i ⊆ D.targets i) ∧
    Framework.LittleO (fun i => ((bad i).card : ℝ)) (fun i => (D.targets i).card) ∧
    Framework.ExpUpper (fun i => {f : Poly d // f ∈ E i})
      (fun _ f => f.val.totalDegree) (fun i _ => D.firstRate i) D.s ∧
    (∀ i Y, Y ∈ D.carriers i →
      Y.Subvariety (AffineVariety.ofIdeal (Ideal.span (E i : Set (Poly d))))) ∧
    ∀ᶠ i in atTop, ∀ q ∈ D.targets i, q ∉ bad i →
      (AffineVariety.ofIdeal (Ideal.span (E i : Set (Poly d)))).IsSmoothAt q ∧
      (AffineVariety.ofIdeal (Ideal.span (E i : Set (Poly d)))).localDimension q < d

/-- Interpolation isolates the narrower-window center sample, including
when its equations have larger components elsewhere. -/
def NarrowInput : Prop :=
  ∃ (L : ℕ → ℕ) (E : ℕ → Finset (Poly d)),
    (∀ i, 1 ≤ L i ∧ (∀ f ∈ E i, f.totalDegree ≤ L i) ∧
      IsolatedPoints (E i : Set (Poly d)) (D.centers i)) ∧
    Framework.ExpUpper (fun _ => Unit) (fun i _ => (L i : ℝ)) (fun i _ => regime.B i) D.s

def ComponentTests (sources : ℕ → AffineFamily.Family d) (C : ℝ) (i : ℕ) :=
  {h : AffineVariety d → Poly d // ∀ X ∈ sources i,
    h X ∉ X.ideal ∧ ((h X).totalDegree : ℝ) ≤ regime.B i * Real.exp (C*D.s i)}

/-- All list choices are made on the source carrier, before choosing an
actual center. This is the generic-depth input of secants.tex. -/
def WideInput : Prop :=
  ∃ (k : ℕ) (sources : ℕ → AffineFamily.Family d)
    (sourceOwner : ℕ → Point d → AffineVariety d)
    (lists : ℕ → AffineVariety d → AffineFamily.Family d)
    (ignored : ℕ → Finset (Point d)),
    d-j ≤ k ∧ k < d ∧ (∀ i, AffineFamily.IsPure (sources i) k) ∧
    (∀ i, ignored i ⊆ D.centers i) ∧
    Framework.LittleO (fun i => ((ignored i).card : ℝ)) (fun i => (D.centers i).card) ∧
    (∀ i p, p ∈ D.centers i → p ∉ ignored i →
      sourceOwner i p ∈ sources i ∧ p ∈ (sourceOwner i p).points) ∧
    (∀ i X, X ∈ sources i → lists i X ⊆ D.carriers i) ∧
    (∀ᶠ i in atTop, ∀ X ∈ sources i, ∀ Y ∈ lists i X,
      GenericMovingRootBound X Y (lists i X) ⌊regime.B i ^ (1/2 : ℝ)⌋₊) ∧
    Framework.LittleO
      (fun i => D.incidenceMass i (((D.centers i).product (D.carriers i)).filter
        (fun a => a.1 ∈ ignored i ∨ a.2 ∉ lists i (sourceOwner i a.1)))) (fun _ => 1) ∧
    ∀ C : ℝ, 0 < C → Framework.UniformLittleO (D.ComponentTests sources C)
      (fun i h => ((D.centers i).filter
        (fun p => p ∉ ignored i ∧ MvPolynomial.eval p (h.val (sourceOwner i p)) = 0)).card)
      (fun i _ => (D.centers i).card)

/-- Specialized primitive interface of prof:pair-selection/budget/regularity,
geo:generic-depth and red:flat-caps. No actual-center depth conclusion is a field. -/
def Hypotheses : Prop :=
  D.DegreeBudgets ∧ D.UniformFlatCap ∧ D.InitialNoCapture ∧ D.FirstCutInput ∧
  (Tendsto (fun i => D.v i / D.s i) atTop (𝓝 0) → D.NarrowInput) ∧
  (Tendsto (fun i => D.s i / D.v i) atTop (𝓝 0) →
    0 < D.b ⟨j, D.j_lt⟩ → d-j < d-1 → D.WideInput)

end SeparatedDepthData
end
end DistinctDistances.TrackA
