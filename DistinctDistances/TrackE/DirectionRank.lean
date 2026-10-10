import DistinctDistances.TrackE.DirectionGroups

/-! Equal-dimension degree and higher-dimension borrowed rank in one later
direction envelope (`sc:separated-rank`, sparse-cones.tex:735–751). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The constant is fixed before centers, rows and envelopes. Every complete
dimension group has a lower rank bound at the envelope's defining degree,
and an upper rank bound at all earlier degrees. -/
theorem direction_envelope_component_rank (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : Point d) (Q : Finset (RPoint d))
      (L : ℕ) (hL : 1 ≤ L) (F : ProjectiveFamily.Family d)
      (hF : ∀ C ∈ F, C.IsIrreducible)
      (hlocus : ProjectiveFamily.locus F = rowDirectionEnvelope p Q L)
      (hdefined : ProjectiveFamily.ComponentsDefinedInDegree F L) (h : ℕ),
      c * (ProjectiveFamily.degree (envelopeDimensionPart F h) : ℝ) * (L : ℝ)^h ≤
        rowDirectionRank p Q L ∧
      ∀ (Q' : Finset (RPoint d)), rowDirections p Q' ⊆
        (ProjectiveFamily.locus (envelopeDimensionPart F h)).points → ∀ E : ℕ,
        (rowDirectionRank p Q' E : ℝ) ≤
          (ProjectiveFamily.degree (envelopeDimensionPart F h) : ℝ) * ((E+h).choose h : ℝ) := by
  classical
  obtain ⟨c, hc, hlow⟩ := TrackA.poly_hilbert_projective_at_L d
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  refine ⟨(c : ℝ), hcR, ?_⟩
  intro p Q L hL F hF hlocus hdefined h
  let C := envelopeDimensionPart F h
  have hpure : ProjectiveFamily.IsPure C h := by
    intro W hW
    obtain ⟨hWF, hdim⟩ := Finset.mem_filter.mp hW
    exact ⟨hF W hWF, hdim⟩
  have hCdefined : ProjectiveFamily.ComponentsDefinedInDegree C L := by
    obtain ⟨E, hE, hcomp⟩ := hdefined
    refine ⟨E, hE, ?_⟩
    intro W hW
    exact hcomp W (Finset.mem_filter.mp hW).1
  have hlists : TrackA.FromProjectiveLists C L := by
    refine ⟨1, fun _ => C, fun _ => L, ?_⟩
    constructor
    · intro a
      exact ⟨hL, hCdefined⟩
    constructor
    · intro W
      simp
    · simp
  have hCenv : ∀ W ∈ C, W.Subvariety (rowDirectionEnvelope p Q L) := by
    intro W hW
    change (rowDirectionEnvelope p Q L).ideal ≤ W.ideal
    rw [← hlocus, ← ProjectiveVariety.vanishingIdeal_points,
      ← ProjectiveVariety.vanishingIdeal_points W]
    apply MvPolynomial.vanishingIdeal_anti_mono (k := ℂ)
    rintro v ⟨hv, hpW⟩
    refine ⟨hv, ?_⟩
    rw [ProjectiveFamily.points_locus]
    exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr
      ⟨(Finset.mem_filter.mp hW).1, hpW⟩⟩
  have hlower := hlow C h L hpure hL hlists
  have hmono := projective_family_hilbert_mono C (rowDirectionEnvelope p Q L) hCenv L
  rw [row_direction_rank_envelope] at hmono
  have hlowerR : (c : ℝ) * (ProjectiveFamily.degree C : ℝ) * (L : ℝ)^h ≤
      (ProjectiveFamily.hilbert C L : ℝ) := by exact_mod_cast hlower
  refine ⟨hlowerR.trans (by exact_mod_cast hmono), ?_⟩
  intro Q' hQ' E
  have hpoint := row_direction_rank_le p Q' (ProjectiveFamily.locus C) hQ' E
  have hupper := TrackA.poly_hilbert_projective_upper C h hpure E
  have hupperR : (ProjectiveFamily.hilbert C E : ℝ) ≤
      (ProjectiveFamily.degree C : ℝ) * ((E+h).choose h : ℝ) := by exact_mod_cast hupper
  exact (show (rowDirectionRank p Q' E : ℝ) ≤ (ProjectiveFamily.hilbert C E : ℝ) by
    exact_mod_cast hpoint).trans hupperR

/-- `sc:separated-rank.rank-alternative`: a later dense surviving row either
gets the adaptive degree lower bound in equal dimension, or borrows the rank
of a genuine dense physical subrow with the higher growth exponent. -/
theorem dense_direction_envelope_rank_alternative {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (S : LimitingSeparatedProfile regime)
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε) (a : α) (τ : ℝ)
    (hτ : S.b ⟨(plateau a).val.val - 1, by have := (plateau a).val.isLt; omega⟩ < τ ∧
      τ < S.b (plateau a).val) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p ∈ (S.sequence.source i).pts.image TrackD.toC, p ∉ H.batch.badCenters i →
      ∀ Q : Finset (RPoint d), Q ⊆ (S.sequence.target i).pts →
        (∀ q ∈ Q, TrackD.toC q ≠ p) →
        (∀ q ∈ Q, TrackD.toC q ∉ batchBadTargets (fun a => H.data (plateau a))
          (fun i => (S.sequence.target i).pts.image TrackD.toC) H.batch.bad i p) →
        ρ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q.card →
        ∃ h : ℕ, d - (plateau a).val.val ≤ h ∧ h ≤ d ∧
          ∃ Q' : Finset (RPoint d), Q' ⊆ Q ∧
            (ρ / (2 * (d + 1 : ℝ))) *
              (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q'.card ∧
            let L := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊;
            (h = d - (plateau a).val.val ∧
              c * ((H.data (plateau a)).degreeBudget i /
                profileDepthRate S (plateau a).val.val (kind a) i *
                Real.exp (-ε a * (H.data (plateau a)).s i)) * (L : ℝ)^h ≤
                  rowDirectionRank p Q L) ∨
            (d - (plateau a).val.val < h ∧ ∀ E : ℕ,
              c * (rowDirectionRank p Q' E : ℝ) * (L : ℝ)^h ≤
                (rowDirectionRank p Q L : ℝ) * ((E+h).choose h : ℝ)) := by
  classical
  obtain ⟨c, hc, hrank⟩ := direction_envelope_component_rank d
  refine ⟨c, hc, ?_⟩
  intro ρ hρ
  let δ : ℝ := ρ / (2 * (d + 1 : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let D := H.data (plateau a)
  have hfrom : DepthFromProfile S D := H.from_profile (plateau a)
  filter_upwards [dense_direction_envelope_group S H a τ hτ ρ hρ,
    H.batch.degree δ hδ, target_test_degree S τ] with i hgroup hdegree htest
  intro p hp htypical Q hQ hneq hsurvives hdense
  let L : ℕ := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊
  have hL : 1 ≤ L := (Nat.le_floor_iff' (by decide : (1 : ℕ) ≠ 0)).mpr
    (by simpa only [Nat.cast_one] using htest)
  obtain ⟨G, hGmass⟩ := hgroup p hp htypical Q hQ hneq hsurvives hdense
  have hparts := hrank p Q L hL G.components
    (fun W hW => (G.components_spec W hW).1) G.components_locus G.components_defined G.dimension
  let C := envelopeDimensionPart G.components G.dimension
  have hCirr : ∀ W ∈ C, W.IsIrreducible := by
    intro W hW
    exact (G.components_spec W (Finset.mem_filter.mp hW).1).1
  have hrowTargets : G.row.image TrackD.toC ⊆ D.targets i := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [(hfrom.2.2.2 i).2.1]
    exact Finset.mem_image.mpr ⟨q, hQ (G.row_subset hq), rfl⟩
  let J : AffineFamily.Family d := G.row.image (fun q => D.owner i (TrackD.toC q))
  have hJsub : J ⊆ D.retained i (H.batch.bad a i) p := by
    intro Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
    exact G.owner_retained q hq
  have hJmass : δ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤
      D.submass i J := hGmass.trans (assigned_submass_of_real_subset D i G.row hrowTargets)
  have hrowDirs : rowDirections p G.row ⊆ (ProjectiveFamily.locus C).points := by
    apply assigned_row_directions_subset D i p G.row C hrowTargets
      (fun q hq => hneq q (G.row_subset hq))
    intro q hq
    exact ⟨G.choice (radialImage p (D.owner i (TrackD.toC q))),
      G.chosen_member q hq, G.chosen_contains q hq⟩
  refine ⟨G.dimension, G.dimension_ge, G.dimension_le, G.row, G.row_subset, hGmass, ?_⟩
  change (G.dimension = d - (plateau a).val.val ∧
    c * (D.degreeBudget i / profileDepthRate S (plateau a).val.val (kind a) i *
      Real.exp (-ε a * D.s i)) * (L : ℝ)^G.dimension ≤ rowDirectionRank p Q L) ∨
    (d - (plateau a).val.val < G.dimension ∧ ∀ E : ℕ,
      c * (rowDirectionRank p G.row E : ℝ) * (L : ℝ)^G.dimension ≤
        (rowDirectionRank p Q L : ℝ) * ((E+G.dimension).choose G.dimension : ℝ))
  by_cases heq : G.dimension = d - (plateau a).val.val
  · refine Or.inl ⟨heq, ?_⟩
    have hprojSub : TrackA.projectedFamily p J ⊆ C := by
      intro W hW
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hW
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
      rw [G.chosen_equal q hq ((G.owner_dimension q hq).trans heq.symm)]
      exact G.chosen_member q hq
    have hdegSub := projective_degree_subset (TrackA.projectedFamily p J) C hprojSub hCirr
    have hdegSubR : (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ) ≤
        (ProjectiveFamily.degree C : ℝ) := by exact_mod_cast hdegSub
    have hlow := hdegree a p hp htypical J hJsub hJmass
    have hpow : 0 ≤ (L : ℝ)^G.dimension := pow_nonneg (Nat.cast_nonneg _) _
    calc
      _ ≤ c * (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ) *
          (L : ℝ)^G.dimension :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hc.le) hpow
      _ ≤ c * (ProjectiveFamily.degree C : ℝ) * (L : ℝ)^G.dimension :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdegSubR hc.le) hpow
      _ ≤ (rowDirectionRank p Q L : ℝ) := hparts.1
  · refine Or.inr ⟨by have := G.dimension_ge; omega, ?_⟩
    intro E
    have hupper := hparts.2 G.row hrowDirs E
    have hpow : 0 ≤ (L : ℝ)^G.dimension := pow_nonneg (Nat.cast_nonneg _) _
    have hchoose : 0 ≤ ((E+G.dimension).choose G.dimension : ℝ) := Nat.cast_nonneg _
    calc
      c * (rowDirectionRank p G.row E : ℝ) * (L : ℝ)^G.dimension ≤
          c * ((ProjectiveFamily.degree C : ℝ) *
            ((E+G.dimension).choose G.dimension : ℝ)) * (L : ℝ)^G.dimension :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hc.le) hpow
      _ = (c * (ProjectiveFamily.degree C : ℝ) * (L : ℝ)^G.dimension) *
          ((E+G.dimension).choose G.dimension : ℝ) := by ring
      _ ≤ (rowDirectionRank p Q L : ℝ) * ((E+G.dimension).choose G.dimension : ℝ) :=
        mul_le_mul_of_nonneg_right hparts.1 hchoose

end
end DistinctDistances.SparseCones
