import DistinctDistances.Framework.Diagonal

/-! Worked statement translations. Geometry and assignment data are parameters:
the track owning them instantiates these families with its concrete objects.
These declarations check the framework's quantifiers; they do not assert the
corresponding geometric theorems. -/

open Filter
open scoped Topology

namespace DistinctDistances.Framework.Examples

/-- reduction.tex:135–143: recorded curves cover all but `o(N²)` pairs.
`uncovered` is the real cardinality of the uncovered ordered pairs. -/
def AlmostCompleteCoverage {d : ℕ} (r : Regime d) (uncovered : ℕ → ℝ) : Prop :=
  LittleO uncovered (fun k => r.N k ^ 2)

example {d : ℕ} (r : Regime d) (uncovered : ℕ → ℝ) :
    AlmostCompleteCoverage r uncovered ↔
      Tendsto (fun k => uncovered k / r.N k ^ 2) atTop (𝓝 0) := by
  apply littleO_iff_ratio
  exact Eventually.of_forall fun k => pow_ne_zero _ (ne_of_gt (r.N_pos k))

/-- profiles.tex:516–520: directional
families have degree at most `E = δ N/A`, with `δ → 0`. The same `δ` works
for every center; degree counts are real-valued casts. -/
def SparseDirectionalFamilies {d : ℕ} (r : Regime d) (δ : ℕ → ℝ)
    (Center : ℕ → Type*) (degree : (k : ℕ) → Center k → ℝ) : Prop :=
  Tendsto δ atTop (𝓝 0) ∧ (∀ᶠ k in atTop, 0 ≤ δ k) ∧
    ∀ᶠ k in atTop, ∀ p, degree k p ≤ δ k * r.N k / r.A k

/-- reduction.tex:135–143: fixed `H,K` and positive surviving density
are selected on one subsequence. The constants are outside the eventual limit. -/
def SurvivingPairs {d : ℕ} (r : Regime d)
    (survives : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ H K : ℕ, 0 < H ∧ 0 < K ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      PositiveDensity (fun k => survives H K (φ k)) (fun k => r.N (φ k) ^ 2)

/-- profiles.tex:17–29 and depth.tex:43–49: exponential lower accuracy,
uniformly over pieces, in a window with width tending to infinity. -/
def PieceMassAccuracy {d : ℕ} (r : Regime d) (w : r.Window)
    (Piece : ℕ → Type*) (mass predicted : (k : ℕ) → Piece k → ℝ) : Prop :=
  ExpLower Piece mass predicted w.s

/-- profiles.tex:532–537, 598–602: an outer pool contains only `exp(o(s))`
pieces. The unit family encodes a scalar upper bound. -/
def PoolPieceCount {d : ℕ} (r : Regime d) (w : r.Window) (count : ℕ → ℝ) : Prop :=
  ExpUpper (fun _ => Unit) (fun k _ => count k) (fun _ _ => 1) w.s

/-- profiles.tex:528–530: separated widths both remain below the outer scale
by a vanishing ratio, although their ratio tends to infinity. -/
def SeparatedWidths {d : ℕ} (r : Regime d) (wide narrow : r.Window) : Prop :=
  Tendsto (fun k => wide.s k / narrow.s k) atTop atTop ∧
    LittleO wide.s (fun k => Real.log (r.B k)) ∧
    LittleO narrow.s (fun k => Real.log (r.B k))

/-- profiles.tex:73–75 and 487–488: errors vanish along every choice of pieces.
The shared threshold also covers tests chosen after the piece. `Test k p`
must already restrict degree and chart denominators as in profiles.tex:446–466. -/
def ProductTesting (Piece : ℕ → Type*) (Test : (k : ℕ) → Piece k → Type*)
    (bad total : (k : ℕ) → (p : Piece k) → Test k p → ℝ) : Prop :=
  UniformLittleO (fun k => (p : Piece k) × Test k p)
    (fun k i => bad k i.1 i.2) (fun k i => total k i.1 i.2)

example (Piece : ℕ → Type*) (hne : ∀ k, Nonempty (Piece k))
    (bad mass : (k : ℕ) → Piece k → ℝ) :
    UniformLittleO Piece bad mass ↔
      ∀ p : (k : ℕ) → Piece k, LittleO (fun k => bad k (p k)) (fun k => mass k (p k)) :=
  uniformLittleO_iff_selections hne bad mass

/-- profiles.tex:40–47: cut times have honest limits; a plateau's interior
testing time must have a strict gap from each limiting cut. Repeated limits
are allowed and do not create spurious plateaux. -/
def LimitingCutTimes {d m : ℕ} (r : Regime d) (w : r.Window)
    (degree : ℕ → Fin m → ℝ) (limits : Fin m → ℝ) : Prop :=
  ProfileConverges (fun k j => normalizedTime (r.B k) (w.s k) (degree k j)) limits

def PlateauInterior {m : ℕ} (limits : Fin m → ℝ) (b : ℝ) : Prop :=
  ∀ j, b ≠ limits j

/-- profiles.tex:570–584 and 600–618: precision grows slowly while conditional
uncovered error vanishes. All mass and light-line requirements enter `requirements`
before the diagonal choice, one fixed precision and requirement at a time. -/
example (err : ℕ → ℕ → ℝ) (herr : ∀ h, Tendsto (err h) atTop (𝓝 0))
    (requirements : ℕ → ℕ → ℕ → Prop)
    (hrequirements : ∀ h j, ∀ᶠ k in atTop, requirements h j k) :
    ∃ h : ℕ → ℕ, Monotone h ∧ Tendsto h atTop atTop ∧
      Tendsto (fun k => err (h k) k) atTop (𝓝 0) ∧
      ∀ j, ∀ᶠ k in atTop, requirements (h k) j k :=
  diagonal_errors err herr requirements hrequirements

/-- depth.tex:51–62, 78–83: first fix `ε`, then delete incidences and centers,
then allow every later fixed `ρ` and every retained subcollection. A candidate
bundles its remaining center, later envelope, and retained component subcollection.
`Choice` is the type of whole sequences of deletions, not a fresh choice per `ρ`. -/
def ProjectedDegree (Choice : Type*) (Candidate : Choice → ℕ → Type*)
    (badIncidence incidenceTotal badCenter centerTotal : Choice → ℕ → ℝ)
    (mass total degree base : (c : Choice) → (k : ℕ) → Candidate c k → ℝ)
    (s : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : Choice,
    LittleO (badIncidence c) (incidenceTotal c) ∧
    LittleO (badCenter c) (centerTotal c) ∧
    ForFixedDensity (Candidate c) (mass c) (total c)
      (fun k i => base c k i * Real.exp (-ε * s k) ≤ degree c k i)

/-- sparse-cones.tex:668–678: one set of typical centers for a fixed finite
batch of tolerances serves all subsequent densities and envelope choices.
Candidate membership includes the already-fixed center and target assignments. -/
def TypicalCenters (Choice : Type*) (Candidate : Choice → ℕ → Type*)
    (bad totalCenters : Choice → ℕ → ℝ)
    (mass total : (c : Choice) → (k : ℕ) → Candidate c k → ℝ)
    (batchConclusion : (c : Choice) → (k : ℕ) → Candidate c k → Prop) : Prop :=
  ∃ c : Choice, LittleO (bad c) (totalCenters c) ∧
    ForFixedDensity (Candidate c) (mass c) (total c) (batchConclusion c)

/-- Expanding the preceding predicate shows the order needed by both citations. -/
example (Choice : Type*) (Candidate : Choice → ℕ → Type*)
    (bad totalCenters : Choice → ℕ → ℝ)
    (mass total : (c : Choice) → (k : ℕ) → Candidate c k → ℝ)
    (Q : (c : Choice) → (k : ℕ) → Candidate c k → Prop) :
    TypicalCenters Choice Candidate bad totalCenters mass total Q ↔
      ∃ c : Choice, LittleO (bad c) (totalCenters c) ∧
        ∀ ρ : ℝ, 0 < ρ → ∀ᶠ k in atTop, ∀ i : Candidate c k,
          ρ * total c k i ≤ mass c k i → Q c k i := Iff.rfl

/-- sparse-cones.tex:886–906: the comparison uses the strict logarithmic gap
chosen before the depth deletion, even when `δ` vanishes arbitrarily slowly. -/
example (δ s : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hs : Tendsto s atTop atTop)
    (η ε : ℝ) (hgap : ε < η) :
    Tendsto (fun k => δ k * Real.exp (-(η - ε) * s k)) atTop (𝓝 0) :=
  strict_margin hδ hs hgap

end DistinctDistances.Framework.Examples
