import DistinctDistances.TrackE.OuterLift
import DistinctDistances.TrackA.Projection

/-! Lift degree bounds and sparse rows (sparse-cones.tex:631–651).

`outer_lift_degree_bound` (sc:631–642): `TrackA.poly_tangent_projection`
gives `mult_p C ≤ deg C / 2` (or zero if `p ∉ C`), and the point-projection
formula yields `deg γ · deg(C→γ) ≥ deg C / 2`. `outer_row_sparse` (sc:643–651):
every remaining target lies on a lift; `Bridges.curve_sample_bound`
summed over the lifts bounds the row by `C·M·(total lift degree)`. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:outer-lift.degree (sparse-cones.tex:631–642). Each
lift loses at most half its degree under projection: if `p ∈ C ⊂ Y`,
uniqueness for the full original physical family at `p` forces `Y = X`
(`huniq`, from `outer_carrier_regular`), so `C ⊆ X`; `X` is smooth at `p` (`hsmooth`) and the marked point satisfies
`q - p ∉ T_p X` (`htan`, from 191 via `hTX`); `TrackA.poly_tangent_projection`
(Projection.lean) gives
`mult_p C ≤ deg C / 2` hence `deg C / 2 ≤ r · deg(radialImage p C)` (its second
conclusion, with `himg`); if `p ∉ C` the multiplicity is zero and the same
conclusion follows from the point-projection formula (cf.
`common_point_projection_budget`, CommonPointProjection.lean). With `himgdeg`
the total is `≤ 2 · deg γ · r`. -/
theorem outer_lift_degree_bound (C X Y : AffineVariety d) (p q : Point d)
    (γ : ProjectiveVariety d)
    (hC : C.IsIrreducible) (hCdim : C.dimension = 1) (hq : q ∈ C.points)
    (hCY : C.Subvariety Y)
    (huniq : p ∈ C.points → Y = X)
    (hsmooth : X.IsSmoothAt p)
    (htan : q - p ∉ X.tangentSpace p)
    (r : ℕ) (hdeg : GenericallyFiniteRadialDegree p C r)
    (himg : (radialImage p C).dimension = 1)
    (himgdeg : (radialImage p C).degree ≤ γ.degree) :
    (C.degree : ℚ) ≤ 2 * γ.degree * (r : ℚ) := by
  have hr_nonneg : (0 : ℚ) ≤ (r : ℚ) := Nat.cast_nonneg r
  have hγ_nonneg : (0 : ℚ) ≤ γ.degree :=
    OAI.PiExponentJets.W22.actualMultiplicity_nonneg _ _ _ le_rfl
  by_cases hp : p ∈ C.points
  · have hCX : C.Subvariety X := huniq hp ▸ hCY
    obtain ⟨_, hsecond⟩ :=
      TrackA.poly_tangent_projection C X hC hCdim hCX p hp hsmooth ⟨q, hq, htan⟩
    have hhalf := hsecond r hdeg himg
    have hle : C.degree / 2 ≤ (r : ℚ) * γ.degree :=
      le_trans hhalf (mul_le_mul_of_nonneg_left himgdeg hr_nonneg)
    have h2 : C.degree ≤ 2 * ((r : ℚ) * γ.degree) := by linarith
    calc C.degree ≤ 2 * ((r : ℚ) * γ.degree) := h2
      _ = 2 * γ.degree * (r : ℚ) := by ring
  · have hmult : C.multiplicity p = 0 := C.multiplicity_eq_zero_off p hp
    have hrad := TrackA.poly_projection_radial C hC 1 le_rfl hCdim p himg r hdeg
    rw [hmult, sub_zero] at hrad
    have hle : (r : ℚ) * (radialImage p C).degree ≤ (r : ℚ) * γ.degree :=
      mul_le_mul_of_nonneg_left himgdeg hr_nonneg
    have hrγ_nonneg : (0 : ℚ) ≤ (r : ℚ) * γ.degree :=
      mul_nonneg hr_nonneg hγ_nonneg
    calc C.degree = (r : ℚ) * (radialImage p C).degree := hrad.symm
      _ ≤ (r : ℚ) * γ.degree := hle
      _ ≤ 2 * γ.degree * (r : ℚ) := by
          have : (r : ℚ) * γ.degree ≤ 2 * ((r : ℚ) * γ.degree) := by linarith
          calc (r : ℚ) * γ.degree ≤ 2 * ((r : ℚ) * γ.degree) := this
            _ = 2 * γ.degree * (r : ℚ) := by ring

/-- sc:outer-row.count (sparse-cones.tex:643–651). Every
remaining target in the row lies on a pooled lift curve (`hcover`); summing
the per-curve sample bound (`hsample`: `Bridges.curve_sample_bound`,
CurveSamples.lean) over the lift family bounds the row by `C₀·M₀·Dtot`. The
assembly supplies `Dtot ≤ 2·E` from 195 + 196 summed over `γ ⊂ C_p`, and
`E·M₀/n ≤ C√δ·M/A → 0` from the pool mass lower bound. -/
theorem outer_row_sparse (row : Finset (RPoint d))
    (Cs : Finset (AffineVariety d))
    (hcover : ∀ q ∈ row, ∃ C ∈ Cs, TrackD.toC q ∈ C.points)
    (hcurves : ∀ C ∈ Cs, C.IsIrreducible ∧ C.dimension = 1)
    (Dtot : ℝ) (hDtot : ∑ C ∈ Cs, ((C.degree : ℚ) : ℝ) ≤ Dtot)
    (C0 M0 : ℝ) (hC0 : 0 ≤ C0) (hM0 : 0 ≤ M0)
    (hsample : ∀ C ∈ Cs, ((row.filter
      (fun q => TrackD.toC q ∈ C.points)).card : ℝ) ≤
      C0 * ((C.degree : ℚ) : ℝ) * M0) :
    ((row.card : ℝ)) ≤ C0 * M0 * Dtot := by
  have hsub : row ⊆ Cs.biUnion (fun C => row.filter (fun q => TrackD.toC q ∈ C.points)) := by
    intro q hq
    obtain ⟨C, hC, hqC⟩ := hcover q hq
    exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_filter.mpr ⟨hq, hqC⟩⟩
  have h1 : (row.card : ℝ) ≤
      ∑ C ∈ Cs, ((row.filter (fun q => TrackD.toC q ∈ C.points)).card : ℝ) := by
    have h := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast h
  calc (row.card : ℝ)
      ≤ ∑ C ∈ Cs, ((row.filter (fun q => TrackD.toC q ∈ C.points)).card : ℝ) := h1
    _ ≤ ∑ C ∈ Cs, C0 * ((C.degree : ℚ) : ℝ) * M0 := Finset.sum_le_sum hsample
    _ = C0 * M0 * ∑ C ∈ Cs, ((C.degree : ℚ) : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun C _ => by ring
    _ ≤ C0 * M0 * Dtot := mul_le_mul_of_nonneg_left hDtot (mul_nonneg hC0 hM0)

end
end DistinctDistances.SparseCones
