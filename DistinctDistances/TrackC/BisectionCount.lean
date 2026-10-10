import DistinctDistances.TrackC.SoftSign

open Filter
open scoped Topology BigOperators

namespace DistinctDistances.TrackC

/-- Balanced bounded approximations cannot approach +1 on more than half of a finite set. -/
theorem bisection_subset_half (d : ℕ) (S P : Finset (E d)) (hPS : P ⊆ S)
    (w : ℕ → E d → ℝ) (hbal : ∀ n, ∑ x ∈ S, w n x = 0)
    (hbound : ∀ n, ∀ x ∈ S, -1 ≤ w n x)
    (hlim : ∀ x ∈ P, Tendsto (fun n => w n x) atTop (𝓝 (1 : ℝ))) :
    (P.card : ℝ) ≤ (S.card : ℝ) / 2 := by
  classical
  by_contra hlarge
  have htwice : S.card + 1 ≤ 2 * P.card := by
    have hreal : (S.card : ℝ) < 2 * (P.card : ℝ) := by linarith
    have hnat : S.card < 2 * P.card := by exact_mod_cast hreal
    omega
  let ε : ℝ := 1 / ((S.card : ℝ) + 1)
  have hden : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have hε : 0 < ε := div_pos zero_lt_one hden
  have hall : ∀ᶠ n in atTop, ∀ x ∈ P, 1 - ε ≤ w n x := by
    apply (eventually_all_finset P).mpr
    intro x hx
    exact ((hlim x hx).eventually (le_mem_nhds (by linarith : 1 - ε < (1 : ℝ))))
  obtain ⟨n, hn⟩ := hall.exists
  let R := S \ P
  have hR : (R.card : ℝ) + (P.card : ℝ) = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hPS
  have hsum : (∑ x ∈ R, w n x) + (∑ x ∈ P, w n x) = 0 := by
    rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hPS, hbal]
  have hp : (P.card : ℝ) * (1 - ε) ≤ ∑ x ∈ P, w n x := by
    calc
      _ = ∑ _x ∈ P, (1 - ε) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hn
  have hr : -(R.card : ℝ) ≤ ∑ x ∈ R, w n x := by
    calc
      _ = ∑ _x ∈ R, (-1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx => hbound n x (Finset.mem_sdiff.mp hx).1)
  have hmargin : (1 : ℝ) ≤ (P.card : ℝ) - R.card := by
    have hcast : (S.card : ℝ) + 1 ≤ 2 * (P.card : ℝ) := by exact_mod_cast htwice
    linarith
  have hcard : (P.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hPS
  have hεcard : ε * (P.card : ℝ) < 1 := by
    have hdiv : (P.card : ℝ) / ((S.card : ℝ) + 1) < 1 :=
      (div_lt_iff₀ hden).mpr (by linarith)
    simpa [ε, div_eq_mul_inv, mul_comm] using hdiv
  nlinarith

end DistinctDistances.TrackC
