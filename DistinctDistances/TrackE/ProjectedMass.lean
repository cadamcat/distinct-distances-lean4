import DistinctDistances.Framework.Asymptotics
import DistinctDistances.Foundations.Projective

/-!
# The strict exponent gap in the final sparse-cone curve plateau

`sc:u-final-curve.regularity`, sparse-cones.tex:870–906. The exceptional component
degree has exponent `-ηs`, whereas every later positive-density restriction has
projected degree at least the same scale times `exp(-εs)`, with `ε < η` fixed.
The comparison is uniform over centers and never compares an uncontrolled `o(s)` to δ.
-/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Degree nonnegativity is the original OAI multiplicity theorem applied to the
actual Hilbert polynomial; no geometric estimate is re-proved. -/
theorem projective_degree_nonneg {d : ℕ} (V : ProjectiveVariety d) : 0 ≤ V.degree := by
  exact OAI.PiExponentJets.W22.actualMultiplicity_nonneg V.ideal V.isHomogeneous
    V.dimension le_rfl

/-- The degree of the distinct projected images is monotone under family inclusion. -/
theorem projective_family_degree_mono {d : ℕ} (F G : ProjectiveFamily.Family d)
    (hFG : F ⊆ G) : ProjectiveFamily.degree F ≤ ProjectiveFamily.degree G := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hFG
  intro V _ _
  exact projective_degree_nonneg V

/-- A fixed positive exponent gap gives a single threshold independent of centers,
envelopes and later density restrictions. -/
theorem eventually_exponential_gap (s : ℕ → ℝ) (hs : Tendsto s atTop atTop)
    (C ε η : ℝ) (hC : 0 < C) (hgap : ε < η) :
    ∀ᶠ n in atTop, C * Real.exp (-η * s n) < Real.exp (-ε * s n) := by
  have hpos : 0 < η - ε := by linarith
  filter_upwards [hs.eventually_ge_atTop ((Real.log C + 1) / (η - ε))] with n hn
  have hbound : Real.log C + 1 ≤ (η - ε) * s n := by
    have h := (div_le_iff₀ hpos).mp hn
    nlinarith
  rw [← Real.exp_log hC, ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- `sc:u-final-curve.regularity.mass`: degree bounds for every later fixed positive
density force the mass of an adaptive exceptional family to be uniformly negligible.
All center/family choices belong to `ι n`; the eventual threshold may depend on ρ.
The same normalized degree scale `a` appears in the lower and upper bounds. -/
theorem uniform_small_mass_of_degree_gap (ι : ℕ → Type*)
    (mass total degree : (n : ℕ) → ι n → ℝ) (a s : ℕ → ℝ) (C ε η : ℝ)
    (hs : Tendsto s atTop atTop) (hC : 0 < C) (hgap : ε < η)
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (hmass : ∀ n i, 0 ≤ mass n i) (htotal : ∀ n i, 0 ≤ total n i)
    (hlower : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop, ∀ i : ι n,
      ρ * total n i ≤ mass n i → a n * Real.exp (-ε * s n) ≤ degree n i)
    (hupper : ∀ᶠ n in atTop, ∀ i : ι n,
      degree n i ≤ C * a n * Real.exp (-η * s n)) :
    Framework.UniformLittleO ι mass total := by
  intro ρ hρ
  filter_upwards [hlower ρ hρ, hupper, ha,
    eventually_exponential_gap s hs C ε η hC hgap] with n hlow hu han hstrict
  intro i
  rw [abs_of_nonneg (hmass n i), abs_of_nonneg (htotal n i)]
  have hsmall : mass n i < ρ * total n i := by
    by_contra! hlarge
    have hl := hlow i hlarge
    have hh : degree n i ≤ a n * (C * Real.exp (-η * s n)) := by
      calc
        _ ≤ C * a n * Real.exp (-η * s n) := hu i
        _ = _ := by ring
    have hexp := mul_lt_mul_of_pos_left hstrict han
    exact not_le_of_gt hexp (hl.trans hh)
  exact hsmall.le

end

end DistinctDistances.SparseCones
