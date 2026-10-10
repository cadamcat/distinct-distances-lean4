import DistinctDistances.TrackE.DirectionGrowth

/-! Select all permitted target-plateau rates and their common positive
logarithmic margin before density, center or envelope choices
(`sc:strict-margins`, sparse-cones.tex:758–781). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- `sc:separated-rank.uniform-rate-margin`: one fixed rate for each open
plateau and one common positive endpoint margin. The final narrow-center
curve plateau remains eligible only for its separate endpoint argument. -/
theorem exists_uniform_plateau_rate_margin (S : LimitingSeparatedProfile regime) :
    ∃ (η : ℝ) (kind : ProfilePlateau S → DepthRateKind), 0 < η ∧
      (∀ u, profileDepthRateAllowed S u.val.val u.val.isLt (kind u)) ∧
      ∀ u, StrictPlateauEligible S u → profileRateEndpointLog S u (kind u) ≤ -η := by
  classical
  letI : Fintype (ProfilePlateau S) := by
    unfold ProfilePlateau
    infer_instance
  obtain ⟨κ, hκ, hb₀, hblast, hb₀₁⟩ := S.balance
  have hfirst : S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ < 0 := by linarith
  have hselect : ∀ u : ProfilePlateau S, StrictPlateauEligible S u →
      ∃ k : DepthRateKind, profileDepthRateAllowed S u.val.val u.val.isLt k ∧
        profileRateEndpointLog S u k < 0 := by
    intro u hu
    by_cases hfirstPlateau : u.val.val = 1
    · refine ⟨.first, trivial, ?_⟩
      have hindex : u.val = (⟨1, by have := regime.dimension_ge_three; omega⟩ : Fin d) :=
        Fin.ext hfirstPlateau
      change S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ + S.b u.val < 0
      rw [hindex]
      linarith
    · by_cases hnonpos : S.b u.val ≤ 0
      · refine ⟨.first, trivial, ?_⟩
        change S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ + S.b u.val < 0
        linarith
      · have hpos : 0 < S.b u.val := lt_of_not_ge hnonpos
        by_cases hwide : Tendsto (fun i => (S.sequence.target i).width /
            (S.sequence.source i).width) atTop (𝓝 0)
        · refine ⟨.wide, ?_, ?_⟩
          · exact ⟨hwide, hpos, by have := u.property.1; have := u.val.isLt; omega⟩
          · change S.b u.val - 2 < 0
            have := limiting_profile_time_upper S u.val
            linarith
        · have hnarrow : Tendsto (fun i => (S.sequence.source i).width /
              (S.sequence.target i).width) atTop (𝓝 0) :=
            S.sequence.separated.resolve_right hwide
          have hfinal : u.val.val + 1 < d := hu.resolve_right hwide
          refine ⟨.narrow, hnarrow, ?_⟩
          have hsum := positive_later_profile_sum S u hpos hfinal
          change -(∑ t ∈ (Finset.univ : Finset (Fin d)).filter
            (fun t => u.val.val < t.val), S.b t) < 0
          linarith
  let choice (u : ProfilePlateau S) : DepthRateKind :=
    if hu : StrictPlateauEligible S u then (hselect u hu).choose else .first
  have hchoice (u : ProfilePlateau S) (hu : StrictPlateauEligible S u) :
      profileDepthRateAllowed S u.val.val u.val.isLt (choice u) ∧
        profileRateEndpointLog S u (choice u) < 0 := by
    simpa only [choice, dif_pos hu] using (hselect u hu).choose_spec
  have hallowed : ∀ u, profileDepthRateAllowed S u.val.val u.val.isLt (choice u) := by
    intro u
    by_cases hu : StrictPlateauEligible S u
    · exact (hchoice u hu).1
    · simp only [choice, dif_neg hu, profileDepthRateAllowed]
  let g (u : ProfilePlateau S) : ℝ :=
    if hu : StrictPlateauEligible S u then -profileRateEndpointLog S u (choice u) else 1
  have hgpos : ∀ u, 0 < g u := by
    intro u
    by_cases hu : StrictPlateauEligible S u
    · have := (hchoice u hu).2
      simp only [g, dif_pos hu]
      linarith
    · simp only [g, dif_neg hu]
      norm_num
  let M : Finset ℝ := insert 1 (Finset.univ.image g)
  have hM : M.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let η : ℝ := M.min' hM
  have hpositive : ∀ z ∈ M, 0 < z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · norm_num
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact hgpos u
  have hη : 0 < η := hpositive η (Finset.min'_mem M hM)
  refine ⟨η, choice, hη, hallowed, ?_⟩
  intro u hu
  have hle : η ≤ g u := Finset.min'_le M _
    (Finset.mem_insert.mpr (Or.inr (Finset.mem_image_of_mem g (Finset.mem_univ u))))
  simp only [g, dif_pos hu] at hle
  linarith

end
end DistinctDistances.SparseCones
