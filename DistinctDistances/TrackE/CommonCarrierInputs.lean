import DistinctDistances.TrackE.CommonCarrierData
import DistinctDistances.TrackE.MECarrierAux

/-! Page-sized pooling and scalar inputs, sparse-cones.tex:122–145. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Fibers of the unchanged owner partition the actual retained finite set. -/
theorem common_owner_family_mass (S : Finset (RPoint d))
    (α : RPoint d → AffineVariety d) :
    TrackD.famMass (commonOwnerFamily S α) (commonOwnerFiber S α) = (S.card : ℝ) := by
  exact MECarrierAux.owner_family_mass_aux S α

/-- Actual fibers are pure disjoint assignments, and every retained flat is real.
These facts hold even at the finitely many indices without a test certificate. -/
theorem common_retained_carrier_structure {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) (hj : j ≤ d) (i : ℕ) :
    AffineFamily.IsPure (W.sourceCarriers i) (d - j) ∧
    AffineFamily.IsPure (W.targetCarriers i) (d - j) ∧
    TrackD.Assignment (regime.P i) (W.sourceCarriers i) (W.sourceAssigned i) ∧
    TrackD.Assignment (regime.P i) (W.targetCarriers i) (W.targetAssigned i) ∧
    (∀ Z ∈ W.sourceCarriers i ∪ W.targetCarriers i,
      TrackD.IsFlat Z → TrackD.IsRealFlat Z) := by
  exact MECarrierAux.retained_carrier_structure_aux W hj i

/-- Coordinatewise profile closeness transfers both prefix and tail products.
The tail comparison uses the balanced reference product, not a recorded sum. -/
theorem common_scale_closeness (B N s ρ : ℝ) (b t : Fin d → ℝ)
    (hB : 0 < B) (hs : 0 ≤ s) (hρ : 0 ≤ ρ)
    (hb : ∑ a, b a = 0) (hBN : B ^ d = N)
    (hclose : ∀ a, |t a - b a| ≤ ρ) (j : ℕ) :
    TrackD.eScale B s t j ≤
      TrackD.eScale B s b j * Real.exp ((d : ℝ) * ρ * s) ∧
    TrackD.tailScale B s t j ≤
      (N / TrackD.eScale B s b j) * Real.exp ((d : ℝ) * ρ * s) := by
  exact MECarrierAux.scale_closeness_aux B N s ρ b t hB hs hρ hb hBN hclose j

/-- Pooling identical carriers costs at most the number of original pieces.
Every piece retains its own original capture bound. -/
theorem common_owner_pooled_bounds (pl : Finset (TrackD.Piece d))
    (S : Finset (RPoint d)) (α : RPoint d → AffineVariety d) (j : ℕ)
    (hS : S ⊆ TrackD.poolPts pl) (hα : TrackD.CarrierAssignment pl j α)
    (hpure : ∀ X ∈ pl, ∀ Z ∈ TrackD.pieceCarrierFamily X j, Z.IsIrreducible)
    (a v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v)
    (hdegree : ∀ X ∈ pl,
      (∑ Z ∈ TrackD.pieceCarrierFamily X j, (Z.degree : ℝ)) ≤ a)
    (hmass : ∀ X ∈ pl, ∀ Z, X.path.IsCarrier j Z →
      (∃ q ∈ X.pts, TrackD.toC q ∈ Z) →
      ((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℝ) ≤ (Z.degree : ℝ) * v) :
    (∑ Z ∈ commonOwnerFamily S α, (Z.degree : ℝ)) ≤ (pl.card : ℝ) * a ∧
    ∀ Z ∈ commonOwnerFamily S α,
      ((commonOwnerFiber S α Z).card : ℝ) ≤ (pl.card : ℝ) * (Z.degree : ℝ) * v := by
  exact MECarrierAux.owner_pooled_bounds_aux pl S α j hS hα hpure a v ha hv hdegree hmass

/-- Little-o physical omissions preserve the two original exponential mass
lower bounds on the same index sequence. -/
theorem common_retained_mass_lower {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      regime.N i * Real.exp (-η * M.s i) ≤ ((W.sources i).card : ℝ) ∧
      regime.N i * Real.exp (-η * M.s i) ≤ ((W.targets i).card : ℝ) := by
  exact MECarrierAux.retained_mass_lower_aux W

/-- Degree-one flats convert literal degree/mass budgets to generic-depth caps. -/
theorem common_flat_budget (𝒳 : AffineFamily.Family d)
    (S : AffineVariety d → Finset (RPoint d))
    (hpure : ∀ X ∈ 𝒳, X.IsIrreducible) (e m c : ℝ)
    (he : 0 < e) (hm : 0 ≤ m) (hc : 0 ≤ c)
    (hdegree : (∑ X ∈ 𝒳, (X.degree : ℝ)) ≤ e * c)
    (hweight : ∀ X ∈ 𝒳, ((S X).card : ℝ) ≤ m * (X.degree : ℝ) / e * c) :
    ((𝒳.filter TrackD.IsFlat).card : ℝ) ≤ e * c ∧
    ∀ X ∈ 𝒳, TrackD.IsFlat X → ((S X).card : ℝ) ≤ m * e⁻¹ * c := by
  exact MECarrierAux.flat_budget_aux 𝒳 S hpure e m c he hm hc hdegree hweight

end
end DistinctDistances.SparseCones
