import DistinctDistances.TrackE.ProfileBatchGraph
import DistinctDistances.TrackE.AssignedMass
import DistinctDistances.TrackE.RequestsDirectionCuts
import DistinctDistances.Bridges.ProjectiveEnvelope
import DistinctDistances.TrackD.Profiles.Regularity

/-! Primitive envelope, target-plateau and assigned-mass inputs for
sparse-cones.tex:721–751. All envelopes use actual radial directions. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The literal directions from one actual center to the later row subset. -/
def rowDirections (p : Point d) (Q : Finset (RPoint d)) : Set (ProjectivePoint d) :=
  {z | ∃ q ∈ Q, ∃ h : TrackD.toC q ≠ p, radialProjection p (TrackD.toC q) h = z}

/-- The exact-degree homogeneous envelope supplied by the shared model. -/
def rowDirectionEnvelope (p : Point d) (Q : Finset (RPoint d)) (L : ℕ) :
    ProjectiveVariety d :=
  (Bridges.projective_envelope d (rowDirections p Q) L).choose

/-- Count physical targets by their unchanged owner, comparing its complete
radial image to the later testing-degree envelope. -/
def directionEnvelopeFailures {j : ℕ} (D : TrackA.SeparatedDepthData regime j)
    (i : ℕ) (p : Point d) (Q : Finset (RPoint d)) (L : ℕ) : Finset (RPoint d) :=
  Q.filter (fun q => ¬ (radialImage p (D.owner i (TrackD.toC q))).Subvariety
    (rowDirectionEnvelope p Q L))

/-- Leave a fixed margin between a testing time and all limiting cut times,
then transfer it uniformly to the actual target path. -/
theorem target_plateau_margin (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (τ : ℝ)
    (hτ : S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ < τ ∧ τ < S.b u.val) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ᶠ i in atTop,
      TrackD.OnPlateau (S.sequence.target i).path.time u.val.val ξ τ := by
  classical
  let j : ℕ := u.val.val
  let jFin : Fin d := u.val
  let prev : Fin d := ⟨j - 1, by have := u.val.isLt; omega⟩
  have hj_eq : jFin.val = j := rfl
  have hprev_eq : prev.val = j - 1 := rfl
  have hj_ge : 1 ≤ j := u.property.1
  have hτ1 : S.b prev < τ := hτ.1
  have hτ2 : τ < S.b jFin := hτ.2
  have hgap1 : (0 : ℝ) < τ - S.b prev := sub_pos.mpr hτ1
  have hgap2 : (0 : ℝ) < S.b jFin - τ := sub_pos.mpr hτ2
  let ξ : ℝ := min (τ - S.b prev) (S.b jFin - τ) / 4
  have hξpos : 0 < ξ := by
    dsimp [ξ]
    positivity
  refine ⟨ξ, hξpos, ?_⟩
  have hξ_gap1 : 4 * ξ ≤ τ - S.b prev := by
    dsimp [ξ]
    have hmin_le : min (τ - S.b prev) (S.b jFin - τ) ≤ τ - S.b prev :=
      min_le_left _ _
    linarith
  have hξ_gap2 : 4 * ξ ≤ S.b jFin - τ := by
    dsimp [ξ]
    have hmin_le : min (τ - S.b prev) (S.b jFin - τ) ≤ S.b jFin - τ :=
      min_le_right _ _
    linarith
  have hup : ∀ᶠ i in atTop, ∀ t : Fin d,
      (S.sequence.target i).path.time t ≤ S.b t + ξ := by
    apply eventually_all.mpr
    intro t
    exact (S.target_limit t).eventually (eventually_le_nhds (by linarith : S.b t < S.b t + ξ))
  have hlow : ∀ᶠ i in atTop, ∀ t : Fin d,
      S.b t - ξ ≤ (S.sequence.target i).path.time t := by
    apply eventually_all.mpr
    intro t
    exact (S.target_limit t).eventually (eventually_ge_nhds (by linarith : S.b t - ξ < S.b t))
  filter_upwards [hup, hlow] with i hup_i hlow_i
  intro t
  constructor
  · intro hlt
    -- t.val < j, bound by prev
    have ht_le_prev : t.val ≤ prev.val := by
      rw [hprev_eq]
      omega
    have hfin_le : t ≤ prev := Fin.mk_le_mk.mpr ht_le_prev
    have hb_le : S.b t ≤ S.b prev := S.sorted hfin_le
    have htime_le : (S.sequence.target i).path.time t ≤ S.b prev + ξ := by
      linarith [hup_i t, hb_le]
    linarith [hξ_gap1, htime_le, hξpos]
  · intro hle
    -- j ≤ t.val, bound below by jFin
    have hfin_le : jFin ≤ t := Fin.mk_le_mk.mpr (by rw [hj_eq]; exact hle)
    have hb_le : S.b jFin ≤ S.b t := S.sorted hfin_le
    have htime_ge : S.b jFin - ξ ≤ (S.sequence.target i).path.time t := by
      linarith [hlow_i t, hb_le]
    linarith [hξ_gap2, htime_ge, hξpos]

/-- A separated target width is o(log B), so every fixed testing time has
testing degree at least one for all sufficiently large configurations. -/
theorem target_test_degree (S : LimitingSeparatedProfile regime) (τ : ℝ) :
    ∀ᶠ i in atTop, 1 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
      (S.sequence.target i).width τ := by
  by_cases hb : τ = 0
  · subst hb
    filter_upwards [regime.B_tendsto.eventually_ge_atTop 1] with i hB
    change 1 ≤ regime.B i * Real.exp (0 * (S.sequence.target i).width)
    rw [zero_mul, Real.exp_zero, mul_one]
    exact hB
  · have hbpos : 0 < |τ| := abs_pos.mpr hb
    let ε : ℝ := 1 / (2 * |τ|)
    have hε : 0 < ε := by positivity
    have hlog : Tendsto (fun i => Real.log (regime.B i)) atTop atTop :=
      Real.tendsto_log_atTop.comp regime.B_tendsto
    filter_upwards [S.sequence.target_small.def hε, hlog.eventually_ge_atTop 0] with i hi hlog₀
    have hwidth_pos : 0 < (S.sequence.target i).width := (S.sequence.width_pos i).2
    have hsmall : (S.sequence.target i).width ≤ ε * Real.log (regime.B i) := by
      simpa only [Real.norm_eq_abs, abs_of_pos hwidth_pos, abs_of_nonneg hlog₀] using hi
    have hscale : |τ| * (S.sequence.target i).width ≤ (1 / 2 : ℝ) * Real.log (regime.B i) := by
      calc
        |τ| * (S.sequence.target i).width ≤ |τ| * (ε * Real.log (regime.B i)) :=
          mul_le_mul_of_nonneg_left hsmall (abs_nonneg τ)
        _ = (|τ| * (1 / (2 * |τ|))) * Real.log (regime.B i) := by ring
        _ = (1 / 2 : ℝ) * Real.log (regime.B i) := by
          have hne : |τ| ≠ 0 := hbpos.ne'
          have : |τ| * (1 / (2 * |τ|)) = (1 / 2 : ℝ) := by
            field_simp
          rw [this]
    have hbs : - ((1 / 2 : ℝ) * Real.log (regime.B i)) ≤ τ * (S.sequence.target i).width := by
      have hle : - (|τ| * (S.sequence.target i).width) ≤ τ * (S.sequence.target i).width := by
        have : -|τ| ≤ τ := by linarith [neg_le_abs τ]
        nlinarith [hwidth_pos]
      linarith
    have hsum : 0 ≤ Real.log (regime.B i) + τ * (S.sequence.target i).width := by
      linarith
    change 1 ≤ regime.B i * Real.exp (τ * (S.sequence.target i).width)
    have hBpos : 0 < regime.B i := regime.B_pos i
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (Real.log (regime.B i) + τ * (S.sequence.target i).width) :=
        Real.exp_le_exp.mpr hsum
      _ = regime.B i * Real.exp (τ * (S.sequence.target i).width) := by
        rw [Real.exp_add, Real.exp_log hBpos]

/-- A complete projected carrier outside the exact-degree envelope is
separated by one of its original homogeneous degree-L equations. -/
theorem direction_envelope_equation_proper (p : Point d) (Q : Finset (RPoint d))
    (L : ℕ) (Y : AffineVariety d)
    (hY : ¬ (radialImage p Y).Subvariety (rowDirectionEnvelope p Q L)) :
    ∃ f : Poly d, f ∈ Bridges.homogeneousEquations (rowDirections p Q) L ∧
      f ∉ (radialImage p Y).ideal := by
  classical
  by_contra h
  push Not at h
  -- Every homogeneous degree-L equation vanishing on the row lies in the image ideal.
  have hall : ∀ f ∈ Bridges.homogeneousEquations (rowDirections p Q) L,
      f ∈ (radialImage p Y).ideal := fun f hf => h f hf
  let T := rowDirections p Q
  let V := rowDirectionEnvelope p Q L
  let W := radialImage p Y
  have hspec := (Bridges.projective_envelope d T L).choose_spec
  have hVpoints : V.points = {z | ∀ f ∈ Bridges.homogeneousEquations T L,
      MvPolynomial.eval z.rep f = 0} := hspec.1
  have hWsubV : W.points ⊆ V.points := by
    intro z hz
    rw [hVpoints]
    intro f hf
    have hfW : f ∈ W.ideal := hall f hf
    have hzrep : z.rep ∈ MvPolynomial.zeroLocus ℂ W.ideal :=
      hz z.rep z.rep_nonzero (Projectivization.mk_rep z)
    have hae := MvPolynomial.mem_zeroLocus_iff.mp hzrep f hfW
    simpa [MvPolynomial.aeval_eq_eval] using hae
  have hrep_sub : ProjectiveVariety.nonzeroRepresentatives W.points ⊆
      ProjectiveVariety.nonzeroRepresentatives V.points := by
    intro v hv
    obtain ⟨hv0, hp⟩ := hv
    exact ⟨hv0, hWsubV hp⟩
  have hVeq : V.ideal = ProjectiveVariety.vanishingIdeal V.points :=
    (ProjectiveVariety.vanishingIdeal_points V).symm
  have hWeq : W.ideal = ProjectiveVariety.vanishingIdeal W.points :=
    (ProjectiveVariety.vanishingIdeal_points W).symm
  have hle : V.ideal ≤ W.ideal := by
    rw [hVeq, hWeq]
    exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) hrep_sub
  exact hY hle

/-- Select bounded physical cuts on all carriers at once. Each is proper
whenever that carrier's complete projection is outside the row envelope. -/
theorem direction_envelope_proper_cuts (p : Point d) (Q : Finset (RPoint d)) (L : ℕ) :
    ∃ g : AffineVariety d → Poly d,
      (∀ Y, (g Y).totalDegree ≤ L) ∧
      (∀ Y, ¬ (radialImage p Y).Subvariety (rowDirectionEnvelope p Q L) → g Y ∉ Y.ideal) ∧
      ∀ Y q, q ∈ Q → TrackD.toC q ≠ p → MvPolynomial.eval (TrackD.toC q) (g Y) = 0 := by
  classical
  have hYexists : ∀ Y : AffineVariety d, ∃ gY : Poly d,
      (gY.totalDegree ≤ L) ∧
      (¬ (radialImage p Y).Subvariety (rowDirectionEnvelope p Q L) → gY ∉ Y.ideal) ∧
      (∀ q ∈ Q, TrackD.toC q ≠ p → MvPolynomial.eval (TrackD.toC q) gY = 0) := by
    intro Y
    by_cases hY : ¬ (radialImage p Y).Subvariety (rowDirectionEnvelope p Q L)
    · obtain ⟨f, hf_mem, hf_proper⟩ := direction_envelope_equation_proper p Q L Y hY
      obtain ⟨hf_hom, hf_van⟩ := hf_mem
      obtain ⟨g, hg_deg, hg_proper, hg_eval⟩ :=
        Request.bounded_radial_pullback p Y f hf_hom
      refine ⟨g, hg_deg, fun _ => hg_proper hf_proper, ?_⟩
      intro q hq hne
      rw [hg_eval]
      apply hf_van
      show TrackD.toC q - p ∈ ProjectiveVariety.nonzeroRepresentatives (rowDirections p Q)
      refine ⟨sub_ne_zero.mpr hne, ?_⟩
      show Projectivization.mk ℂ (TrackD.toC q - p) _ ∈ rowDirections p Q
      exact ⟨q, hq, hne, rfl⟩
    · refine ⟨0, Nat.zero_le L, fun h => False.elim (hY h), ?_⟩
      intro q _ _
      simp
  choose g hg using hYexists
  exact ⟨g, fun Y => (hg Y).1, fun Y => (hg Y).2.1, fun Y q hq hne => (hg Y).2.2 q hq hne⟩

/-- A real subset injects into the disjoint fibers of its unchanged owner map. -/
theorem assigned_submass_of_real_subset {j : ℕ}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) (Q : Finset (RPoint d))
    (hQ : Q.image TrackD.toC ⊆ D.targets i) :
    (Q.card : ℝ) ≤ D.submass i (Q.image (fun q => D.owner i (TrackD.toC q))) := by
  classical
  let J : AffineFamily.Family d := Q.image (fun q => D.owner i (TrackD.toC q))
  have hsubmass : D.submass i J
      = (((D.targets i).filter (fun q => D.owner i q ∈ J)).card : ℝ) :=
    submass_eq_assigned_card D i J
  rw [hsubmass]
  have himgSub : Q.image TrackD.toC ⊆ (D.targets i).filter (fun q => D.owner i q ∈ J) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have htarget : TrackD.toC q ∈ D.targets i := hQ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    have hown : D.owner i (TrackD.toC q) ∈ J :=
      Finset.mem_image.mpr ⟨q, hq, rfl⟩
    exact Finset.mem_filter.mpr ⟨htarget, hown⟩
  have hcardImg : (Q.image TrackD.toC).card = Q.card :=
    Finset.card_image_of_injective _ profile_toC_injective
  have hleNat : (Q.image TrackD.toC).card ≤ ((D.targets i).filter (fun q => D.owner i q ∈ J)).card :=
    Finset.card_le_card himgSub
  calc
    (Q.card : ℝ) = ((Q.image TrackD.toC).card : ℝ) := by rw [hcardImg]
    _ ≤ (((D.targets i).filter (fun q => D.owner i q ∈ J)).card : ℝ) := by
        exact_mod_cast hleNat

/-- Retained carrier images are irreducible and have the actual depth
dimension. The off-center witness excludes an empty radial image. -/
theorem retained_projected_family_pure {j : ℕ}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) (p : Point d)
    (bad : Finset (Point d × AffineVariety d)) (J : AffineFamily.Family d)
    (hJ : J ⊆ D.retained i bad p)
    (hdim : ∀ Y ∈ D.retained i bad p, (radialImage p Y).dimension = d - j)
    (houtside : ∀ Y ∈ J, ∃ x ∈ Y.points, x ≠ p) :
    ProjectiveFamily.IsPure (TrackA.projectedFamily p J) (d - j) := by
  intro W hW
  obtain ⟨Y, hYJ, rfl⟩ := Finset.mem_image.mp hW
  have hYret : Y ∈ D.retained i bad p := hJ hYJ
  have hYcar : Y ∈ D.carriers i := (Finset.mem_filter.mp hYret).1
  have hirr_car := (D.carrier_pure i Y hYcar).1
  have hirr : (radialImage p Y).IsIrreducible :=
    radialImage_irreducible p Y hirr_car (houtside Y hYJ)
  exact ⟨hirr, hdim Y hYret⟩

end
end DistinctDistances.SparseCones
