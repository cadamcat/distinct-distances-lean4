import DistinctDistances.TrackE.CurveSpan
import DistinctDistances.TrackE.RichRadius
import DistinctDistances.TrackE.SmallSpan

/-!
# The uniform dimension induction for `red:directions.count`

`reduction.tex:145–201`: the induction bound is `2^a C₀ deg(Y) A^a`.
The finitely many dimension losses are absorbed in `2^d C₀` using A's ambient
dimension bound. The small-ratio threshold is fixed before the sample or the stars.
-/

namespace DistinctDistances

noncomputable section

namespace Reduction

variable {d : ℕ}

open Classical in
/-- Core of the frozen direction-count statement, with the exact geometry inputs
passed explicitly and the cardinal threshold fixed to one. -/
theorem direction_caps_core (hd : 3 ≤ d) (hIH : IH d)
    (hbasics : Request.DirectionVarietyBasics d) (hzero : Request.ZeroDimDirectionLocus d)
    (hsections : Request.DirectionHyperplaneSections d) (hcurves : Request.CurveLinearSections d)
    (H K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ P : Finset (RPoint d), 1 ≤ P.card → Mcount P ≤ ε * Ascale d P.card →
      ∀ G : Finset (RPoint d × RPoint d), IsSymmSelection P G →
        (∀ e ∈ G, ((P.filter (· ∈ affineSpan ℝ {e.1, e.2})).card : ℝ) ≤ H) →
        (∀ p : RPoint d, ∀ Y : ProjectiveVariety d, Y.IsIrreducible → Y.dimension = 1 →
          SpansAtMostPlane Y →
          (((star G p).filter fun q => DirMem Y p q).card : ℝ) ≤
            K * Ascale d P.card * (Y.degree : ℝ)) →
        ∀ p : RPoint d, ∀ Y : ProjectiveVariety d, Y.IsIrreducible →
          (((star G p).filter fun q => DirMem Y p q).card : ℝ) ≤
            C * (Y.degree : ℝ) * Ascale d P.card ^ Y.dimension := by
  classical
  obtain ⟨Csmall, hCsmall, hsmall⟩ := exists_small_span_quadratic_bound hd hIH
  obtain ⟨εr, hεr, hrich⟩ := exists_rich_span_direction_bound hd hIH hsections
  let base : ℝ := Csmall + 1 + |H| + |K|
  have hbase : 0 < base := by dsimp [base]; positivity
  have hbaseSmall : Csmall ≤ base := by dsimp [base]; nlinarith [abs_nonneg H, abs_nonneg K]
  have hbaseH : |H| ≤ base := by dsimp [base]; nlinarith [abs_nonneg K]
  have hbaseCurve : 1 + |H| + |K| ≤ base := by dsimp [base]; linarith
  refine ⟨(2 : ℝ) ^ d * base, by positivity, min 1 εr, lt_min (by norm_num) hεr, ?_⟩
  intro P hP hMP G hG hlight hgreedy p
  let A := Ascale d P.card
  have hN : (1 : ℝ) ≤ P.card := by exact_mod_cast hP
  have hA : 1 ≤ A := Real.one_le_rpow hN (by positivity)
  have hA₀ : 0 ≤ A := by linarith
  have hMA : Mcount P ≤ A := hMP.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left 1 εr) hA₀)
  have hMr : Mcount P ≤ εr * A :=
    hMP.trans (mul_le_mul_of_nonneg_right (min_le_right 1 εr) hA₀)
  have hstarP : star G p ⊆ P := by
    intro q hq
    exact (Finset.mem_offDiag.mp (hG.1 (mem_pair_of_mem_star hq))).2.1
  have hline : ∀ q ∈ star G p,
      ((P.filter (· ∈ affineSpan ℝ {p, q})).card : ℝ) ≤ H := by
    intro q hq
    exact hlight (p, q) (mem_pair_of_mem_star hq)
  have hind : ∀ a : ℕ, ∀ Y : ProjectiveVariety d, Y.IsIrreducible → Y.dimension = a →
      (((star G p).filter fun q => DirMem Y p q).card : ℝ) ≤
        (2 : ℝ) ^ a * base * (Y.degree : ℝ) * A ^ a := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro Y hY hdim
      let T := (star G p).filter fun q => DirMem Y p q
      have hTstar : T ⊆ star G p := Finset.filter_subset _ _
      have hTP : T ⊆ P := hTstar.trans hstarP
      have hdir : ∀ q ∈ T, DirMem Y p q := fun q hq => (Finset.mem_filter.mp hq).2
      have hdegree₁ : 1 ≤ (Y.degree : ℝ) := (hbasics Y hY).1
      have hdegree : 0 ≤ (Y.degree : ℝ) := by linarith
      change (T.card : ℝ) ≤ (2 : ℝ) ^ a * base * (Y.degree : ℝ) * A ^ a
      by_cases hempty : T = ∅
      · rw [hempty, Finset.card_empty, Nat.cast_zero]
        positivity
      · by_cases ha0 : a = 0
        · obtain ⟨F, hFY, hFdegree⟩ := hzero Y hY (hdim.trans ha0)
          have hcover : ∀ q ∈ T, ∃ h : cplx q ≠ cplx p,
              radialProjection (cplx p) (cplx q) h ∈ F := by
            intro q hq
            obtain ⟨hc, hqY⟩ := hdir q hq
            exact ⟨hc, hFY hqY⟩
          have hcount := card_partners_on_finite_directions_le_degree P T p F |H|
            (Y.degree : ℝ) (abs_nonneg H) hTP
            (fun q hq => (hline q (hTstar hq)).trans (le_abs_self H)) hcover hFdegree
          simpa only [ha0, pow_zero, one_mul, mul_one] using
            hcount.trans (mul_le_mul_of_nonneg_right hbaseH hdegree)
        · have ha : 1 ≤ a := by omega
          let U := Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))
          have hTU : ∀ q ∈ T, q - p ∈ U := by
            intro q hq
            exact Submodule.subset_span ⟨q, hq, rfl⟩
          have hbasepow : base ≤ (2 : ℝ) ^ a * base := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := a)) hbase.le
          by_cases hU : Module.finrank ℝ U ≤ 3
          · have hlow : (T.card : ℝ) ≤ base * (Y.degree : ℝ) * A ^ a := by
              by_cases ha1 : a = 1
              · have hcurve := curve_direction_count_of_small_span hcurves P T p Y hY
                  (hdim.trans ha1) hTP hdir U hU hTU H K A hA hdegree
                  (fun q hq => hline q (hTstar hq))
                  (fun hplane => hgreedy p Y hY (hdim.trans ha1) hplane)
                have hbound : (T.card : ℝ) ≤ base * (Y.degree : ℝ) * A := by
                  calc
                    _ ≤ (1 + |H| + |K|) * (Y.degree : ℝ) * A := hcurve
                    _ ≤ base * (Y.degree : ℝ) * A := by
                      apply mul_le_mul_of_nonneg_right _ hA₀
                      exact mul_le_mul_of_nonneg_right hbaseCurve hdegree
                simpa only [ha1, pow_one] using hbound
              · have ha2 : 2 ≤ a := by omega
                have hquad := hsmall P hP hMA p T hTP U hU hTU
                have hcount := direction_bound_of_quadratic_bound T Csmall A (Y.degree : ℝ)
                  a hCsmall.le hA hdegree₁ ha2 hquad
                exact hcount.trans (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hbaseSmall hdegree) (pow_nonneg hA₀ _))
            exact hlow.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hbasepow hdegree) (pow_nonneg hA₀ _))
          · have hU4 : 4 ≤ Module.finrank ℝ U := by omega
            obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
            have hp : p ∈ P :=
              (Finset.mem_offDiag.mp (hG.1 (mem_pair_of_mem_star (hTstar hq)))).1
            have hprior : 0 ≤ (2 : ℝ) ^ (a - 1) * base := by positivity
            have hcap : ∀ V : ProjectiveVariety d, V.IsIrreducible →
                V.dimension + 1 = Y.dimension →
                ((T.filter fun q => DirMem V p q).card : ℝ) ≤
                  ((2 : ℝ) ^ (a - 1) * base) * (V.degree : ℝ) * A ^ (Y.dimension - 1) := by
              intro V hV hVdim
              have hVa : V.dimension < a := by omega
              have hVeq : V.dimension = a - 1 := by omega
              have hsub : (T.filter fun q => DirMem V p q) ⊆
                  ((star G p).filter fun q => DirMem V p q) := by
                intro q hq
                obtain ⟨hqT, hqV⟩ := Finset.mem_filter.mp hq
                exact Finset.mem_filter.mpr ⟨hTstar hqT, hqV⟩
              have hprevious := ih V.dimension hVa V hV rfl
              have hcount := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hprevious
              simpa only [hVeq, hdim] using hcount
            have hcount := hrich P p hp hMr T hTP hU4 Y hY
              (by omega : 1 ≤ Y.dimension) hdegree hdir
              ((2 : ℝ) ^ (a - 1) * base) hprior hcap
            have hpow : (2 : ℝ) ^ (a - 1) * 2 = (2 : ℝ) ^ a := by
              rw [← pow_succ, Nat.sub_add_cancel ha]
            calc
              _ ≤ 2 * ((2 : ℝ) ^ (a - 1) * base) * (Y.degree : ℝ) * A ^ a := by
                simpa only [hdim] using hcount
              _ = ((2 : ℝ) ^ (a - 1) * 2) * base * (Y.degree : ℝ) * A ^ a := by ring
              _ = _ := by rw [hpow]
  intro Y hY
  have hdim : Y.dimension ≤ d := (hbasics Y hY).2.le
  have hdegree : 0 ≤ (Y.degree : ℝ) := by have := (hbasics Y hY).1; linarith
  calc
    _ ≤ (2 : ℝ) ^ Y.dimension * base * (Y.degree : ℝ) * A ^ Y.dimension :=
      hind Y.dimension Y hY rfl
    _ ≤ (2 : ℝ) ^ d * base * (Y.degree : ℝ) * A ^ Y.dimension := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hA₀ _)
      apply mul_le_mul_of_nonneg_right _ hdegree
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hdim) hbase.le

end Reduction

end

end DistinctDistances
