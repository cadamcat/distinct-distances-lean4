import DistinctDistances.TrackE.FirstCutInputs
import DistinctDistances.TrackE.RequestsFirstCut
import DistinctDistances.TrackD.Profiles.RegularityChosenJacobian

/-! The first limiting cluster supplies uniform fixed-precision first-system
certificates (`depth.tex:145–168`). Coincident initial cut times are retained. -/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators Classical

noncomputable section

/-- The first strict increase in a monotone limiting profile occurs no later
than any specified open plateau. All preceding times equal the first time. -/
theorem first_cluster_end {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (j : ℕ) (hj : 1 ≤ j) (hjd : j < d)
    (hplateau : S.b ⟨j - 1, by omega⟩ < S.b ⟨j, hjd⟩) :
    ∃ r : Fin d, 0 < r.val ∧ r.val ≤ j ∧
      S.b ⟨0, by omega⟩ < S.b r ∧
      ∀ t : Fin d, t.val < r.val → S.b t = S.b ⟨0, by omega⟩ := by
  let z : Fin d := ⟨0, by omega⟩
  let A : Finset (Fin d) := Finset.univ.filter (fun t => S.b z < S.b t)
  have hjA : (⟨j, hjd⟩ : Fin d) ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (S.sorted (show z ≤ ⟨j - 1, by omega⟩ from
      Fin.le_iff_val_le_val.mpr (Nat.zero_le _))).trans_lt hplateau
  have hA : A.Nonempty := ⟨⟨j, hjd⟩, hjA⟩
  let r : Fin d := A.min' hA
  have hrA : r ∈ A := A.min'_mem hA
  have hgap : S.b z < S.b r := (Finset.mem_filter.mp hrA).2
  have hrpos : 0 < r.val := by
    by_contra h
    have heq : r = z := Fin.ext (by dsimp [z]; omega)
    rw [heq] at hgap
    exact lt_irrefl _ hgap
  have hrj : r.val ≤ j := Fin.le_iff_val_le_val.mp (A.min'_le _ hjA)
  refine ⟨r, hrpos, hrj, hgap, ?_⟩
  intro t ht
  have hlo : S.b z ≤ S.b t := S.sorted (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
  have hhi : S.b t ≤ S.b z := by
    by_contra h
    have htA : t ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩
    have hrt : r.val ≤ t.val := Fin.le_iff_val_le_val.mp (A.min'_le _ htA)
    omega
  exact le_antisymm hhi hlo

/-- The target's fixed physical carriers all receive the first-cluster
equations. The bad set is chosen before any actual-center or density deletion. -/
theorem profile_first_cut_certificates {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hs : D.s = fun i => (S.sequence.target i).width) (hb : D.b = S.b)
    (htargets : ∀ i, D.targets i = (S.sequence.target i).pts.image TrackD.toC)
    (hphysical : ∀ i Y, Y ∈ D.carriers i →
      (S.sequence.target i).path.IsCarrier j Y ∧
        ∃ q ∈ (S.sequence.target i).pts, TrackD.toC q ∈ Y)
    (hplateau : S.b ⟨j - 1, by have := D.j_lt; omega⟩ < S.b ⟨j, D.j_lt⟩) :
    ∀ ε > 0, ∀ θ > 0, ∀ᶠ i in atTop,
      ∃ F bad, FirstCutCertificate D ε θ i F bad := by
  obtain ⟨r, hrpos, hrj, hgap, hprefix⟩ :=
    first_cluster_end S j D.j_pos D.j_lt hplateau
  let z : Fin d := ⟨0, by have := D.j_pos; have := D.j_lt; omega⟩
  let b₀ : ℝ := S.b z
  intro ε hε θ hθ
  let τ : ℝ := min (ε / 2) ((S.b r - b₀) / 2)
  let ξ : ℝ := τ / 2
  have hτ : 0 < τ := by dsimp [τ, b₀, z]; exact lt_min (by positivity) (by linarith)
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hτε : τ ≤ ε / 2 := min_le_left _ _
  have hτgap : τ ≤ (S.b r - b₀) / 2 := min_le_right _ _
  have hplateau₀ : TrackD.OnPlateau S.b r.val ξ (b₀ + τ) := by
    intro t
    constructor
    · intro ht
      rw [hprefix t ht]
      change b₀ + ξ ≤ b₀ + τ
      dsimp [ξ]
      linarith
    · intro ht
      have hbt := S.sorted (Fin.le_iff_val_le_val.mpr ht)
      dsimp [ξ]
      linarith
  obtain ⟨θ₁, hθ₁, η, hη, ρ₀, hρ₀, hηξ, s₁, hregularity⟩ :=
    TrackD.prof_regularity_jacobian_with_margin d regime.dimension_ge_three θ hθ ξ hξ
  have hρ : 0 < ρ₀ / 2 := by positivity
  filter_upwards [target_singleton_pool_good S θ₁ η (ρ₀ / 2)
      hθ₁ hη hρ,
    S.sequence.target_grows.eventually_ge_atTop s₁, target_test_degree_one S (b₀ + τ)]
    with i hpool hwidth htest
  obtain ⟨F, g, hFdeg, hgdeg, hFvan, hkerRank, hbad⟩ :=
    hregularity (regime.P i) {S.sequence.target i} (S.sequence.target i).width
      (ρ₀ / 2) S.b (by linarith) hpool hwidth r.val r.isLt (b₀ + τ) hplateau₀ htest
  let badR := (S.sequence.target i).pts.filter
    (fun q => ¬ TrackD.JacRegularAt {S.sequence.target i} r.val F g (TrackD.toC q))
  let bad := badR.image TrackD.toC
  have htargetCard : (D.targets i).card = (S.sequence.target i).pts.card := by
    rw [htargets i]
    exact Finset.card_image_of_injective _ profile_toC_injective
  have hfirst : D.firstRate i =
      regime.B i * Real.exp (b₀ * (S.sequence.target i).width) := by
    simp [TrackA.SeparatedDepthData.firstRate, TrackA.SeparatedDepthData.cutDegree,
      hs, hb, b₀, z]
  refine ⟨F, bad, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htargets i]
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  · have hc := hbad (S.sequence.target i) (Finset.mem_singleton_self _)
    have hbadCard : bad.card = badR.card :=
      Finset.card_image_of_injective _ profile_toC_injective
    rw [hbadCard, htargetCard]
    exact hc
  · intro f hf
    calc
      (f.totalDegree : ℝ) ≤
          regime.B i * Real.exp ((b₀ + τ) * (S.sequence.target i).width) := hFdeg f hf
      _ ≤ regime.B i * Real.exp ((b₀ + ε) * (S.sequence.target i).width) := by
        apply mul_le_mul_of_nonneg_left _ (regime.B_pos i).le
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (by linarith) (S.sequence.width_pos i).2.le
      _ = D.firstRate i * Real.exp (ε * D.s i) := by
        rw [hfirst, hs, add_mul, Real.exp_add]
        ring
  · intro Y hY
    obtain ⟨hYpath, q, hq, hqY⟩ := hphysical i Y hY
    have hvan := descendant_equations_vanish (S.sequence.target i) r.val j hrj
      q hq Y hYpath hqY F hFvan
    change (Ideal.span (F : Set (Poly d))).radical ≤ Y.ideal
    apply Y.isRadical.radical_le_iff.mpr
    exact Ideal.span_le.mpr hvan
  · intro q hq hqnot
    rw [htargets i] at hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    have hreg : TrackD.JacRegularAt {S.sequence.target i} r.val F g (TrackD.toC x) := by
      by_contra hnot
      exact hqnot (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hnot⟩, rfl⟩)
    obtain ⟨hg, Z, ⟨hZpool, hxZ⟩, hunique, hsmooth, hZker⟩ := hreg
    have hZirr : Z.IsIrreducible := by
      obtain ⟨X, hX, hZpath, _⟩ := hZpool
      exact hZpath.isPrime
    have hloc := Request.smooth_equation_locus_of_carrier F Z (TrackD.toC x)
      hZirr hxZ hsmooth (hFvan Z hZpool) hZker
    refine ⟨hloc.1, ?_⟩
    have hrank := hkerRank (TrackD.toC x) hg
    have hdim : Z.localDimension (TrackD.toC x) =
        Module.finrank ℂ (TrackD.jacKer F (TrackD.toC x)) := by
      rw [← hsmooth.2, hZker]
    rw [hloc.2, hdim]
    omega

end

end DistinctDistances.SparseCones
