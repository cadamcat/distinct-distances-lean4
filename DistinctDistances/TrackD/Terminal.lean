import DistinctDistances.TrackD.TerminalNonlinear
import DistinctDistances.TrackD.GeoTerminal

/-!
# `geo:terminal` (`secants.tex:221–512`)

Terminal-curve deletion: uniformly in the assignment and the curves, the ordered pairs whose
target is assigned to a curve projecting into the center's directional family are `o(N^2)`.
Consumer: `prof:pair-selection` (`profiles.tex:546–560`), one global application.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

/-- The pairs removed by terminal deletion: `p ≠ q`, `q` assigned to `Y`, and
`closure(π_p Y) ⊆ C_p` (`secants.tex:236–240`). -/
def terminalPairs {d : ℕ} (P : Finset (Pt d)) (Cf : Pt d → ProjectiveFamily.Family d)
    (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d)) :
    Finset (Pt d × Pt d) :=
  terminalPairsSel P Cf 𝒴 S (fun _ => True)

/-- `geo:terminal` (`secants.tex:233–243`), finitary form. For every `ε > 0` there are `η > 0`
and `N₀`, depending only on `d, c₀, ε`, such that for every sample `P` with `|P| ≥ N₀`,
`M ≤ η A` and the proper-flat cap with exponent `c₀`, every choice of directional families `C_p`
of degree at most `η N / A` (the paper's `E = δ N / A` with `δ ≤ η`), and every partial assignment
of sample points to distinct irreducible complex curves whose line members are real, at most
`ε N^2` ordered pairs `(p, q)`, `p ≠ q`, have `q` assigned to `Y` with `closure(π_p Y) ⊆ C_p`. -/
theorem geo_terminal (d : ℕ) (hd : 3 ≤ d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∃ η > 0, ∃ N₀ : ℕ, ∀ P : Finset (Pt d), N₀ ≤ P.card →
      cfgM P ≤ η * cfgA P → RealFlatCap P c₀ →
      ∀ Cf : Pt d → ProjectiveFamily.Family d,
        (∀ p ∈ P, IsDirectionalFamily (Cf p) ∧
          (ProjectiveFamily.degree (Cf p) : ℝ) ≤ η * cfgN P / cfgA P) →
      ∀ (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d)),
        Assignment P 𝒴 S → (∀ Y ∈ 𝒴, IsCurve Y) → (∀ Y ∈ 𝒴, IsLine Y → IsRealFlat Y) →
        ((terminalPairs P Cf 𝒴 S).card : ℝ) ≤ ε * cfgN P ^ 2 := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨ηL, hηL, NL, hL⟩ := GeoTerminal.lines_small d hd c₀ hc₀ (ε / 2) hhalf
  obtain ⟨ηN, hηN, NN, hN⟩ := GeoTerminal.nonlinear_small d hd c₀ hc₀ (ε / 2) hhalf
  refine ⟨min ηL ηN, lt_min hηL hηN, max (max NL NN) 1, ?_⟩
  intro P hP hM hcap Cf hCf 𝒴 S hS hcurves hreal
  have hNL : NL ≤ P.card := (le_max_left NL NN).trans ((le_max_left _ _).trans hP)
  have hNN : NN ≤ P.card := (le_max_right NL NN).trans ((le_max_left _ _).trans hP)
  have hP1 : 1 ≤ P.card := (le_max_right _ _).trans hP
  obtain ⟨hA, _, _, hNP⟩ := GeoTerminal.cfg_bounds hd P hP1
  have hCf_mono (δ : ℝ) (hδ : min ηL ηN ≤ δ) :
      ∀ p ∈ P, IsDirectionalFamily (Cf p) ∧
        (ProjectiveFamily.degree (Cf p) : ℝ) ≤ δ * cfgN P / cfgA P := by
    intro p hp
    refine ⟨(hCf p hp).1, (hCf p hp).2.trans ?_⟩
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hδ hNP.le) hA.le
  have hlines := hL P hNL
    (hM.trans (mul_le_mul_of_nonneg_right (min_le_left ηL ηN) hA.le))
    hcap Cf (hCf_mono ηL (min_le_left _ _)) 𝒴 S hS hreal
  have hnonlinear := hN P hNN
    (hM.trans (mul_le_mul_of_nonneg_right (min_le_right ηL ηN) hA.le))
    hcap Cf (hCf_mono ηN (min_le_right _ _)) 𝒴 S hS hcurves
  have hcard : ((terminalPairs P Cf 𝒴 S).card : ℝ) ≤
      (terminalPairsSel P Cf 𝒴 S IsLine).card +
        (terminalPairsSel P Cf 𝒴 S (fun Y => ¬ IsLine Y)).card := by
    unfold terminalPairs
    rw [GeoTerminal.selected_union]
    exact_mod_cast Finset.card_union_le
      (terminalPairsSel P Cf 𝒴 S IsLine)
      (terminalPairsSel P Cf 𝒴 S (fun Y => ¬ IsLine Y))
  calc
    _ ≤ _ := hcard
    _ ≤ (ε / 2) * cfgN P ^ 2 + (ε / 2) * cfgN P ^ 2 :=
      add_le_add hlines hnonlinear
    _ = _ := by ring

end

end TrackD
end DistinctDistances
