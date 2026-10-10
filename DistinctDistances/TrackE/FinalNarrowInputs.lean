import DistinctDistances.TrackE.CoveringEnvelope
import DistinctDistances.TrackE.RegularityBudget

/-! Final narrow-center setup and complete-carrier placement inputs,
sparse-cones.tex:802–821, 849–906. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The original owner is tested against the whole covering family envelope. -/
def coveringProjectionFailures {j : ℕ} (D : TrackA.SeparatedDepthData regime j)
    (i : ℕ) (p : Point d) (Q : Finset (RPoint d))
    (C : ProjectiveFamily.Family d) (L : ℕ) : Finset (RPoint d) :=
  Q.filter fun q => ¬ (radialImage p (D.owner i (TrackD.toC q))).Subvariety
    (coveringDirectionEnvelope C L)

/-- The exact-degree envelope of a covered row lies inside the envelope
of the entire covering family. -/
theorem row_envelope_sub_covering (p : Point d) (Q : Finset (RPoint d))
    (C : ProjectiveFamily.Family d) (L : ℕ)
    (hQ : rowDirections p Q ⊆ (ProjectiveFamily.locus C).points) :
    (rowDirectionEnvelope p Q L).Subvariety (coveringDirectionEnvelope C L) := by
  classical
  let Trow := rowDirections p Q
  let Tcover := (ProjectiveFamily.locus C).points
  let Erow := Bridges.homogeneousEquations Trow L
  let Ecover := Bridges.homogeneousEquations Tcover L
  let Vrow := rowDirectionEnvelope p Q L
  let Vcover := coveringDirectionEnvelope C L
  have hspec_row := (Bridges.projective_envelope d Trow L).choose_spec
  have hspec_cover := (Bridges.projective_envelope d Tcover L).choose_spec
  have hVrow : Vrow.points = {z | ∀ f ∈ Erow, MvPolynomial.eval z.rep f = 0} := hspec_row.1
  have hVcover : Vcover.points = {z | ∀ f ∈ Ecover, MvPolynomial.eval z.rep f = 0} :=
    hspec_cover.1
  have hEsub : Ecover ⊆ Erow := by
    intro f hf
    obtain ⟨hfhom, hfvan⟩ := hf
    refine ⟨hfhom, ?_⟩
    intro v hv
    obtain ⟨hv0, hp_row⟩ := hv
    have hp_cover : Projectivization.mk ℂ v hv0 ∈ Tcover := hQ hp_row
    exact hfvan v ⟨hv0, hp_cover⟩
  have hPsub : Vrow.points ⊆ Vcover.points := by
    intro z hz
    have hzrow : z ∈ {z | ∀ f ∈ Erow, MvPolynomial.eval z.rep f = 0} :=
      hVrow ▸ hz
    rw [hVcover]
    intro f hf
    exact hzrow f (hEsub hf)
  have hrep_sub : ProjectiveVariety.nonzeroRepresentatives Vrow.points ⊆
      ProjectiveVariety.nonzeroRepresentatives Vcover.points := by
    intro v hv
    obtain ⟨hv0, hp⟩ := hv
    exact ⟨hv0, hPsub hp⟩
  show Vcover.ideal ≤ Vrow.ideal
  have hVrow_eq : Vrow.ideal = ProjectiveVariety.vanishingIdeal Vrow.points :=
    (ProjectiveVariety.vanishingIdeal_points Vrow).symm
  have hVcover_eq : Vcover.ideal = ProjectiveVariety.vanishingIdeal Vcover.points :=
    (ProjectiveVariety.vanishingIdeal_points Vcover).symm
  rw [hVrow_eq, hVcover_eq]
  exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) hrep_sub

/-- Positive separated widths cannot have both reciprocal ratios tending to
zero. Thus a final narrow-center curve plateau is ineligible for strict rank. -/
theorem narrow_final_plateau_ineligible (S : LimitingSeparatedProfile regime)
    (hnarrow : Tendsto (fun i => (S.sequence.source i).width /
      (S.sequence.target i).width) atTop (𝓝 0))
    (u : ProfilePlateau S) (hu : u.val.val + 1 = d) :
    ¬ StrictPlateauEligible S u := by
  intro hElig
  unfold StrictPlateauEligible at hElig
  have hnotlt : ¬ (u.val.val + 1 < d) := by omega
  rcases hElig with hlt | hwide
  · exact hnotlt hlt
  · -- Both ratios tend to 0, but their product is constantly 1.
    have hprod : Tendsto
        (fun i => (S.sequence.source i).width / (S.sequence.target i).width *
          ((S.sequence.target i).width / (S.sequence.source i).width))
        atTop (𝓝 (0 * 0)) :=
      hnarrow.mul hwide
    simp only [zero_mul] at hprod
    have hone : (fun i => (S.sequence.source i).width / (S.sequence.target i).width *
          ((S.sequence.target i).width / (S.sequence.source i).width)) =
        fun _ => (1 : ℝ) := by
      funext i
      have hs : (S.sequence.source i).width ≠ 0 :=
        ne_of_gt (S.sequence.width_pos i).1
      have ht : (S.sequence.target i).width ≠ 0 :=
        ne_of_gt (S.sequence.width_pos i).2
      field_simp
    rw [hone] at hprod
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique hprod hconst
    exact zero_ne_one h01

/-- A's actual homogeneous minor witness is retained alongside the previously
frozen curve certificate; it controls representatives and physical pullbacks. -/
def HomogeneousCurveRegularityCertificate {n : ℕ}
    (F bad : ProjectiveFamily.Family (n + 1)) (E : List (Poly (n + 1)))
    (g : Poly (n + 1)) (C D : ℕ) : Prop :=
  CurveRegularityCertificate F bad E g C D ∧
  g.IsHomogeneous ((n - 1) * (D - 1)) ∧
  g ∈ Submodule.span ℂ (TrackA.jacobianMinors E (n - 1))

/-- The same whole-family regularity budget, retaining A's homogeneous witness. -/
theorem homogeneous_curve_regularity_budget (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : ProjectiveFamily.Family (n + 1)) (L D : ℕ),
      ProjectiveFamily.IsPure F 1 → 1 ≤ L → TrackA.FromProjectiveLists F L → C * L ≤ D →
      ∀ (Cf Cr δ a η s : ℝ), 0 < Cf → 0 < Cr → 0 ≤ δ → 0 ≤ a →
      (ProjectiveFamily.degree F : ℝ) ≤ Cf * δ * a →
      (L : ℝ) / (D : ℝ) ≤ Cr * Real.exp (-η * s) →
      ∃ (bad : ProjectiveFamily.Family (n + 1)) (E : List (Poly (n + 1))) (g : Poly (n + 1)),
        HomogeneousCurveRegularityCertificate F bad E g C D ∧
        (ProjectiveFamily.degree bad : ℝ) ≤
          ((C : ℝ) * Cf * Cr) * δ * a * Real.exp (-η * s) := by
  obtain ⟨C, hC, hregular⟩ := TrackA.poly_regularity_projective n
  refine ⟨C, hC, ?_⟩
  intro F L D hF hL hLists hD Cf Cr δ a η s hCf hCr hδ ha hdegree hratio
  obtain ⟨bad, E, g, hbad, hdegBad, hE, hgDeg, hgHom, hgSpan, hgGood, hGerm⟩ :=
    hregular F 1 L D hn hF hL hLists hD
  refine ⟨bad, E, g, ⟨⟨hbad, hE, hgDeg, hgGood, ?_⟩, hgHom, hgSpan⟩, ?_⟩
  · intro p hp hgp
    simpa only [Nat.cast_ofNat, Nat.reduceAdd] using hGerm p hp hgp
  · have hdeg : (ProjectiveFamily.degree bad : ℝ) ≤
        (C : ℝ) * (ProjectiveFamily.degree F : ℝ) * (L : ℝ) / (D : ℝ) := by
      exact_mod_cast hdegBad
    have hC₀ : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    have hratio₀ : 0 ≤ (L : ℝ) / (D : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc
      _ ≤ (C : ℝ) * (ProjectiveFamily.degree F : ℝ) * ((L : ℝ) / (D : ℝ)) := by
        simpa only [mul_div_assoc] using hdeg
      _ ≤ (C : ℝ) * (Cf * δ * a) * ((L : ℝ) / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdegree hC₀) hratio₀
      _ ≤ (C : ℝ) * (Cf * δ * a) * (Cr * Real.exp (-η * s)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring

/-- All rates, tolerances, reserved times and the common batch precede every
later center, envelope and positive-density restriction. -/
structure FinalNarrowBatchData {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (S : LimitingSeparatedProfile regime)
    [Fintype (ProfilePlateau S)] where
  finalPlateau : ProfilePlateau S
  final_index : finalPlateau.val.val + 1 = d
  a : ℝ
  b₀ : ℝ
  b_eq : ℝ
  b_test : ℝ
  κ : ℝ
  m : ℝ
  ε : ℝ
  margin_pos : 0 < m
  epsilon_pos : 0 < ε
  epsilon_gap : ε < b_eq - b₀
  before : a ≤ profilePlateauLeft S finalPlateau
  cluster_gap : profilePlateauLeft S finalPlateau - a ≤ κ
  cluster_loss : (d : ℝ) * κ ≤ m / 4
  plateau_time : profilePlateauLeft S finalPlateau < b₀ ∧ b₀ < S.b finalPlateau.val
  reserved_times : b₀ < b_eq ∧ b_eq < b_test ∧ b_test < S.b finalPlateau.val
  endpoint_gap : (d : ℝ) * (profileLastTime S - b₀) < m / 4
  kind : ProfilePlateau S → DepthRateKind
  kind_allowed : ∀ u, profileDepthRateAllowed S u.val.val u.val.isLt (kind u)
  final_rate : kind finalPlateau = .narrow
  H : ProfileDepthBatchData T S id kind (fun _ => ε)
  preceding_rank : DirectionRowRankMargin H a m

end
end DistinctDistances.SparseCones
