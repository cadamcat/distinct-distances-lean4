import DistinctDistances.TrackE.DepthDataCore
import DistinctDistances.TrackE.AssignedMass

/-! Transfer the recorded cut budgets to their limiting profile
(`profiles.tex:236–263`, `depth.tex:4–16`). The index threshold is independent
of the subfamily selected from the persistent carriers. -/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators Classical

noncomputable section

/-- A finite product of cut scales loses at most one time error per coordinate. -/
theorem cut_scale_product_le {d : ℕ} (I : Finset (Fin d))
    (B s δ : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (t b : Fin d → ℝ) (ht : ∀ x ∈ I, t x ≤ b x + δ) :
    (∏ x ∈ I, TrackD.cutScale B s t x) ≤
      (∏ x ∈ I, B * Real.exp (b x * s)) * Real.exp ((d : ℝ) * δ * s) := by
  have hterm (x : Fin d) (hx : x ∈ I) :
      TrackD.cutScale B s t x ≤ B * Real.exp (b x * s) * Real.exp (δ * s) := by
    change B * Real.exp (t x * s) ≤ _
    calc
      B * Real.exp (t x * s) ≤ B * Real.exp ((b x + δ) * s) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (ht x hx) hs)) hB
      _ = _ := by rw [add_mul, Real.exp_add]; ring
  have hprod := Finset.prod_le_prod₀
    (fun x (_ : x ∈ I) => mul_nonneg hB (Real.exp_pos _).le) hterm
  have hcard : (I.card : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (show I.card ≤ d by simpa using Finset.card_le_univ I)
  have he : Real.exp ((I.card : ℝ) * δ * s) ≤ Real.exp ((d : ℝ) * δ * s) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard hδ) hs)
  have hnonneg : 0 ≤ ∏ x ∈ I, B * Real.exp (b x * s) :=
    Finset.prod_nonneg (fun x _ => mul_nonneg hB (Real.exp_pos _).le)
  calc
    _ ≤ ∏ x ∈ I, (B * Real.exp (b x * s) * Real.exp (δ * s)) := hprod
    _ = (∏ x ∈ I, B * Real.exp (b x * s)) *
        Real.exp ((I.card : ℝ) * δ * s) := by
      rw [Finset.prod_mul_distrib]
      simp [Real.exp_nat_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left he hnonneg

/-- Assigned target fibers inject into the union of all points touching the
selected carriers. This bound allows that selection to be made later. -/
theorem assigned_mass_le_covered {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (htargets : ∀ i, D.targets i = (S.sequence.target i).pts.image TrackD.toC)
    (i : ℕ) (J : AffineFamily.Family d) :
    D.submass i J ≤ (((S.sequence.target i).pts.filter
      (fun x => ∃ Y ∈ J, TrackD.toC x ∈ Y)).card : ℝ) := by
  rw [submass_eq_assigned_card, htargets i, Finset.filter_image]
  rw [Finset.card_image_of_injective _ profile_toC_injective]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hx, howner⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx, D.owner i (TrackD.toC x), howner,
    D.owner_contains i (TrackD.toC x) (by rw [htargets i]; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩

/-- The explicit identities used by the frozen G5 wrapper. -/
theorem profile_depth_budgets_core {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hs : D.s = fun i => (S.sequence.target i).width) (hb : D.b = S.b)
    (htargets : ∀ i, D.targets i = (S.sequence.target i).pts.image TrackD.toC)
    (hcarriers : ∀ i, D.carriers i = (D.targets i).image (D.owner i))
    (hcarrier : ∀ i q, q ∈ (S.sequence.target i).pts →
      (S.sequence.target i).path.IsCarrier j (D.owner i (TrackD.toC q))) :
    D.DegreeBudgets := by
  have hd := regime.dimension_ge_three
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hphysical (i : ℕ) (J : AffineFamily.Family d) (hJ : J ⊆ D.carriers i) :
      ∀ Y ∈ J, (S.sequence.target i).path.IsCarrier j Y ∧
        ∃ x ∈ (S.sequence.target i).pts, TrackD.toC x ∈ Y := by
    intro Y hY
    have hY' := hJ hY
    rw [hcarriers i] at hY'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY'
    rw [htargets i] at hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hcarrier i x hx, x, hx,
      D.owner_contains i (TrackD.toC x) (by rw [htargets i]; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
  have hdegrees (i : ℕ) (J : AffineFamily.Family d) (hJ : J ⊆ D.carriers i) :
      0 ≤ (AffineFamily.degree J : ℝ) := by
    change 0 ≤ ((∑ Y ∈ J, Y.degree : ℚ) : ℝ)
    apply Rat.cast_nonneg.mpr
    apply Finset.sum_nonneg
    intro Y hY
    have hirr := (D.carrier_pure i Y (hJ hY)).1
    change 0 ≤ OAI.QuarticPowerFree.affineDegree Y.ideal
    exact le_trans (by norm_num : (0 : ℚ) ≤ 1)
      (OAI.QuarticPowerFree.one_le_affineDegree Y.ideal hirr.ne_top)
  have hbudgets : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      (AffineFamily.degree (D.carriers i) : ℝ) ≤ D.degreeBudget i * Real.exp (ε * D.s i) ∧
      ∀ J : AffineFamily.Family d, J ⊆ D.carriers i →
        D.submass i J ≤ (AffineFamily.degree J : ℝ) * D.tailBudget i * Real.exp (ε * D.s i) := by
    intro ε hε
    let δ : ℝ := ε / (2 * (d : ℝ))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδd : (d : ℝ) * δ = ε / 2 := by dsimp [δ]; field_simp
    obtain ⟨θ, hθ, hbezout⟩ := TrackD.prof_budget_bezout d hd (ε / 2) (by positivity)
    have htimes : ∀ᶠ i in atTop, ∀ t, (S.sequence.target i).path.time t ≤ S.b t + δ := by
      apply eventually_all.mpr
      intro t
      exact (S.target_limit t).eventually (eventually_le_nhds (by linarith : S.b t < S.b t + δ))
    filter_upwards [S.sequence.good θ hθ 1 (by norm_num) 1 le_rfl, htimes] with i hi ht
    have hwidth := (S.sequence.width_pos i).2.le
    have hpre := cut_scale_product_le (Finset.univ.filter (fun t : Fin d => t.val < j))
      (regime.B i) (D.s i) δ (regime.B_pos i).le (by simpa only [hs] using hwidth)
      hδ.le (S.sequence.target i).path.time D.b (fun t _ => by simpa only [hb] using ht t)
    have htail := cut_scale_product_le (Finset.univ.filter (fun t : Fin d => j ≤ t.val))
      (regime.B i) (D.s i) δ (regime.B_pos i).le (by simpa only [hs] using hwidth)
      hδ.le (S.sequence.target i).path.time D.b (fun t _ => by simpa only [hb] using ht t)
    have hpre' : TrackD.eScale (TrackD.cfgB (regime.P i)) (S.sequence.target i).width
        (S.sequence.target i).path.time j ≤ D.degreeBudget i * Real.exp (ε / 2 * D.s i) := by
      simpa only [TrackD.eScale, TrackD.cfgB, Regime.B, Regime.N, hs, hδd,
        TrackA.SeparatedDepthData.degreeBudget, TrackA.SeparatedDepthData.cutDegree] using hpre
    have htail' : TrackD.tailScale (TrackD.cfgB (regime.P i)) (S.sequence.target i).width
        (S.sequence.target i).path.time j ≤ D.tailBudget i * Real.exp (ε / 2 * D.s i) := by
      simpa only [TrackD.tailScale, TrackD.cfgB, Regime.B, Regime.N, hs, hδd,
        TrackA.SeparatedDepthData.tailBudget, TrackA.SeparatedDepthData.cutDegree] using htail
    have hcombine (a : ℝ) : a * Real.exp (ε / 2 * D.s i) * Real.exp (ε / 2 * D.s i) =
        a * Real.exp (ε * D.s i) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    constructor
    · have h := (hbezout (regime.P i) (S.sequence.target i) 1 1 hi.2 hwidth j D.j_lt.le
        (D.carriers i) (hphysical i _ le_rfl)).1
      have h' : (AffineFamily.degree (D.carriers i) : ℝ) ≤
          TrackD.eScale (TrackD.cfgB (regime.P i)) (S.sequence.target i).width
            (S.sequence.target i).path.time j * Real.exp (ε / 2 * D.s i) := by
        simpa only [AffineFamily.degree, Rat.cast_sum, hs] using h
      exact h'.trans ((mul_le_mul_of_nonneg_right hpre' (Real.exp_pos _).le).trans_eq (hcombine _))
    · intro J hJ
      have h := (hbezout (regime.P i) (S.sequence.target i) 1 1 hi.2 hwidth j D.j_lt.le
        J (hphysical i J hJ)).2
      have h' : D.submass i J ≤ (AffineFamily.degree J : ℝ) *
          TrackD.tailScale (TrackD.cfgB (regime.P i)) (S.sequence.target i).width
            (S.sequence.target i).path.time j * Real.exp (ε / 2 * D.s i) := by
        exact (assigned_mass_le_covered S D htargets i J).trans
          (by simpa only [AffineFamily.degree, Rat.cast_sum, hs] using h)
      calc
        D.submass i J ≤ _ := h'
        _ ≤ (AffineFamily.degree J : ℝ) * (D.tailBudget i * Real.exp (ε / 2 * D.s i)) *
            Real.exp (ε / 2 * D.s i) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail' (hdegrees i J hJ))
            (Real.exp_pos _).le
        _ = _ := by rw [← mul_assoc, hcombine]
  constructor
  · intro ε hε
    filter_upwards [hbudgets ε hε] with i hi u
    exact hi.1
  · intro ε hε
    filter_upwards [hbudgets ε hε] with i hi J
    exact hi.2 J.val J.property

end

end DistinctDistances.SparseCones
