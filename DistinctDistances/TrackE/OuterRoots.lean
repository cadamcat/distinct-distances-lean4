import DistinctDistances.TrackD.Secants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Root uniqueness at the outermost sparse-cone endpoint

`sc:u-outer-lift.roots`, sparse-cones.tex:601–629. All lift products use the same
source tangent space and the same smooth local label space. A second root would
force inclusion, then equality, of the two projected tangent spaces.
-/

namespace DistinctDistances.SparseCones

noncomputable section

variable {d : ℕ}

/-- Equal tangent dimensions and injective projection turn the particular-pair
inclusion into equality of projected tangent spaces. -/
theorem projected_tangents_eq_of_inclusion (TX TY : Submodule ℂ (Point d)) (v : Point d)
    (hTX : v ∉ TX) (hTY : v ∉ TY)
    (hdim : Module.finrank ℂ TX = Module.finrank ℂ TY)
    (hinc : TX ≤ TY ⊔ (ℂ ∙ v)) :
    TX ⊔ (ℂ ∙ v) = TY ⊔ (ℂ ∙ v) := by
  apply Submodule.eq_of_le_of_finrank_eq (sup_le hinc le_sup_right)
  rw [Submodule.finrank_sup_span_singleton hTX,
    Submodule.finrank_sup_span_singleton hTY, hdim]

/-- A second distinct physical root at the same label contradicts the retained
tangent-inequality test. The differential hypotheses are precisely D's particular-pair API. -/
theorem outer_root_eq (lam : Point d →ₗ[ℂ] ℂ) (p q z : Point d) (c : ℂ)
    (hqlam : lam (q - p) ≠ 0) (hzlam : lam (z - p) ≠ 0)
    (hz : z - p = c • (q - p))
    (TX TY : Submodule ℂ (Point d)) (TW : Submodule ℂ (Point d × Point d))
    (hTX : q - p ∉ TX) (hTY : q - p ∉ TY)
    (hdim : Module.finrank ℂ TX = Module.finrank ℂ TY)
    (hqW : (TX.prod TY).map (TrackD.labelDeriv lam p q) ≤ TW)
    (hrank : Module.finrank ℂ ((TX.prod TY).map (TrackD.labelDeriv lam p q)) =
      Module.finrank ℂ TX + Module.finrank ℂ TY)
    (hdimW : Module.finrank ℂ TW = Module.finrank ℂ TX + Module.finrank ℂ TY)
    (hzW : (TX.prod (⊥ : Submodule ℂ (Point d))).map (TrackD.labelDeriv lam p z) ≤ TW)
    (hneq : TX ⊔ (ℂ ∙ (q - p)) ≠ TY ⊔ (ℂ ∙ (q - p))) : z = q := by
  by_contra hzq
  have hc0 : c ≠ 0 := by
    intro hc
    apply hzlam
    rw [hz, hc, zero_smul, map_zero]
  have hc1 : c ≠ 1 := by
    intro hc
    apply hzq
    have h := hz
    rw [hc, one_smul] at h
    simpa only [sub_add_cancel] using congrArg (fun v : Point d => v + p) h
  have hinc := TrackD.geo_secants_local lam p q z c hqlam hz hc0 hc1 TX TY TW
    hqW hrank hdimW hzW
  exact hneq (projected_tangents_eq_of_inclusion TX TY (q - p) hTX hTY hdim hinc)

open Classical in
/-- `sc:u-outer-lift.roots.pointwise` (`sparse-cones.tex:612–629`): any finite root
set at a common retained label has cardinality at most one. The source carrier is fixed;
the target tangent may vary with the root. -/
theorem outer_roots_card_le_one (lam : Point d →ₗ[ℂ] ℂ) (p : Point d)
    (Q : Finset (Point d)) (TX : Submodule ℂ (Point d))
    (TY : Point d → Submodule ℂ (Point d)) (TW : Submodule ℂ (Point d × Point d))
    (hchart : ∀ q ∈ Q, lam (q - p) ≠ 0)
    (hline : ∀ q ∈ Q, ∀ z ∈ Q, ∃ c : ℂ, z - p = c • (q - p))
    (hTX : ∀ q ∈ Q, q - p ∉ TX) (hTY : ∀ q ∈ Q, q - p ∉ TY q)
    (hdim : ∀ q ∈ Q, Module.finrank ℂ TX = Module.finrank ℂ (TY q))
    (hqW : ∀ q ∈ Q, (TX.prod (TY q)).map (TrackD.labelDeriv lam p q) ≤ TW)
    (hrank : ∀ q ∈ Q, Module.finrank ℂ ((TX.prod (TY q)).map (TrackD.labelDeriv lam p q)) =
      Module.finrank ℂ TX + Module.finrank ℂ (TY q))
    (hdimW : ∀ q ∈ Q, Module.finrank ℂ TW = Module.finrank ℂ TX + Module.finrank ℂ (TY q))
    (hneq : ∀ q ∈ Q, TX ⊔ (ℂ ∙ (q - p)) ≠ TY q ⊔ (ℂ ∙ (q - p))) :
    Q.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro q hq z hz
  obtain ⟨c, hcz⟩ := hline q hq z hz
  have hzW : (TX.prod (⊥ : Submodule ℂ (Point d))).map (TrackD.labelDeriv lam p z) ≤ TW := by
    apply le_trans _ (hqW z hz)
    apply Submodule.map_mono
    intro v hv
    have hle : (⊥ : Submodule ℂ (Point d)) ≤ TY z := bot_le
    exact ⟨hv.1, hle hv.2⟩
  exact (outer_root_eq lam p q z c (hchart q hq) (hchart z hz) hcz TX (TY q) TW
    (hTX q hq) (hTY q hq) (hdim q hq) (hqW q hq) (hrank q hq) (hdimW q hq) hzW
    (hneq q hq)).symm

open Classical in
/-- Turn disjoint generic fiber lists into the map-degree sum in
`sc:lift-map-degree` (`sparse-cones.tex:603–629`). The lists are chosen at one common
generic direction; their cardinalities are the generic map degrees. -/
theorem lift_map_degree_sum_le_one {ι : Type*} (I : Finset ι)
    (roots : ι → Finset (Point d)) (degree : ι → ℕ)
    (hdisjoint : (I : Set ι).PairwiseDisjoint roots)
    (hcard : ∀ i ∈ I, (roots i).card = degree i)
    (hroots : (I.biUnion roots).card ≤ 1) :
    ∑ i ∈ I, degree i ≤ 1 := by
  classical
  calc
    _ = ∑ i ∈ I, (roots i).card := Finset.sum_congr rfl fun i hi => (hcard i hi).symm
    _ = (I.biUnion roots).card := (Finset.card_biUnion hdisjoint).symm
    _ ≤ 1 := hroots

end

end DistinctDistances.SparseCones
