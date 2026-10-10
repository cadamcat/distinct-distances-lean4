import DistinctDistances.TrackC.Subdivision

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def prescribedLineMotions (L₁ L₂ L'₁ L'₂ : Line 3) : Set (Motion 3) :=
  {g | mapsLine g L₁ L'₁ ∧ mapsLine g L₂ L'₂}

def lineMatchWeight (X Y : Finset (E 3)) (L L' : Line 3) (g : Motion 3) : ℕ :=
  matchCount (pointsOn X L) (pointsOn Y L') g

private lemma same_norm_line {D : Submodule ℝ (E 3)} (hD : Module.finrank ℝ D = 1)
    {v w : E 3} (hv : v ∈ D) (hw : w ∈ D) (hn : ‖v‖ = ‖w‖) : v = w ∨ v = -w := by
  by_cases hv0 : v = 0
  · left
    have hw0 : w = 0 := by
      apply norm_eq_zero.mp
      rw [← hn, hv0]
      simp
    simp [hv0, hw0]
  · have hspan : D = ℝ ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hD hv hv0
    have hw' : w ∈ ℝ ∙ v := by rw [← hspan]; exact hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw'
    have habs : |a| = 1 := by
      have hn' := hn
      rw [← ha, norm_smul, Real.norm_eq_abs] at hn'
      have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      nlinarith
    by_cases ha0 : 0 ≤ a
    · have haeq : a = 1 := by
        rw [abs_of_nonneg ha0] at habs
        linarith
      left
      simpa [haeq] using ha
    · have haeq : a = -1 := by
        rw [abs_of_nonpos (le_of_not_ge ha0)] at habs
        linarith
      right
      have hneg : w = -v := by simpa [haeq] using ha.symm
      rw [hneg]
      simp

private lemma directions_pair (L₁ L₂ : Line 3) (hnp : ¬ parallel L₁ L₂) :
    ∃ u v : E 3, u ∈ L₁.1.direction ∧ u ≠ 0 ∧ v ∈ L₂.1.direction ∧ v ≠ 0 ∧ v ∉ L₁.1.direction ∧
      Module.finrank ℝ ↥(L₁.1.direction ⊔ L₂.1.direction) = 2 := by
  let D₁ := L₁.1.direction
  let D₂ := L₂.1.direction
  have hD₁ : Module.finrank ℝ D₁ = 1 := L₁.2.2
  have hD₂ : Module.finrank ℝ D₂ = 1 := L₂.2.2
  have hD₁bot : D₁ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hD₁
    norm_num at hD₁
  have hD₂bot : D₂ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hD₂
    norm_num at hD₂
  obtain ⟨u, hu, hu0⟩ := D₁.ne_bot_iff.mp hD₁bot
  obtain ⟨v, hv, hv0⟩ := D₂.ne_bot_iff.mp hD₂bot
  have huSpan : D₁ = ℝ ∙ u := eq_span_singleton_of_mem_of_finrank_eq_one hD₁ hu hu0
  have hvSpan : D₂ = ℝ ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hD₂ hv hv0
  have hnp' : D₁ ≠ D₂ := by simpa [parallel, D₁, D₂] using hnp
  have hvNot : v ∉ D₁ := by
    intro hvD
    have hD₁v : D₁ = ℝ ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hD₁ hvD hv0
    exact hnp' (hD₁v.trans hvSpan.symm)
  have hvNotSpan : v ∉ ℝ ∙ u := by simpa [huSpan] using hvNot
  refine ⟨u, v, hu, hu0, hv, hv0, hvNot, ?_⟩
  change Module.finrank ℝ ↥(D₁ ⊔ D₂) = 2
  rw [huSpan, hvSpan, Submodule.finrank_sup_span_singleton hvNotSpan, finrank_span_singleton hu0]

private lemma span_pair_sup (a b : E 3) :
    Submodule.span ℝ ({a, b} : Set (E 3)) = ℝ ∙ a ⊔ ℝ ∙ b := by
  rw [show ({a, b} : Set (E 3)) = insert a ({b} : Set (E 3)) by ext x; simp,
    Submodule.span_insert]

private lemma directions_basis (L₁ L₂ : Line 3) (hnp : ¬ parallel L₁ L₂) :
    ∃ u v w : E 3,
      u ∈ L₁.1.direction ∧ u ≠ 0 ∧ v ∈ L₂.1.direction ∧ v ≠ 0 ∧
      Module.finrank ℝ ↥(L₁.1.direction ⊔ L₂.1.direction) = 2 ∧
      Submodule.span ℝ ({u, v} : Set (E 3)) = L₁.1.direction ⊔ L₂.1.direction ∧
      w ∈ (L₁.1.direction ⊔ L₂.1.direction)ᗮ ∧
      Submodule.span ℝ ({u, v, w} : Set (E 3)) = ⊤ := by
  obtain ⟨u, v, hu, hu0, hv, hv0, hvnot, hD⟩ := directions_pair L₁ L₂ hnp
  let D : Submodule ℝ (E 3) := L₁.1.direction ⊔ L₂.1.direction
  have hD' : Module.finrank ℝ ↥D = 2 := by simpa [D] using hD
  have hE : Module.finrank ℝ (E 3) = 3 := by simp [E]
  have horth : Module.finrank ℝ ↥(Dᗮ) = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) D
    rw [hD', hE] at hsum
    omega
  have horthbot : Dᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at horth
    norm_num at horth
  obtain ⟨w, hw, hw0⟩ := Dᗮ.ne_bot_iff.mp horthbot
  have hwnot : w ∉ D := by
    intro hwD
    have hmem : w ∈ D ⊓ Dᗮ := ⟨hwD, hw⟩
    have hbot : D ⊓ Dᗮ = ⊥ := (Submodule.orthogonal_disjoint D).eq_bot
    rw [hbot, Submodule.mem_bot] at hmem
    exact hw0 hmem
  have hsup : Module.finrank ℝ ↥(D ⊔ ℝ ∙ w) = 3 := by
    rw [Submodule.finrank_sup_span_singleton hwnot, hD']
  have htop : D ⊔ ℝ ∙ w = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hsup, hE]
  have hpair : Submodule.span ℝ ({u, v} : Set (E 3)) = D := by
    calc
      Submodule.span ℝ ({u, v} : Set (E 3)) = ℝ ∙ u ⊔ ℝ ∙ v := span_pair_sup u v
      _ = D := by simp [D, eq_span_singleton_of_mem_of_finrank_eq_one L₁.2.2 hu hu0,
        eq_span_singleton_of_mem_of_finrank_eq_one L₂.2.2 hv hv0]
  have htriple : ({u, v, w} : Set (E 3)) = ({u, v} : Set (E 3)) ∪ {w} := by
    ext x
    simp <;> tauto
  refine ⟨u, v, w, hu, hu0, hv, hv0, hD', hpair, hw, ?_⟩
  rw [htriple, Submodule.span_union, hpair]
  simpa using htop

private lemma direction_eq_of_mapsLine (g : Motion 3) (l l' : Line 3) (h : mapsLine g l l') :
    l'.1.direction = Submodule.map g.linear.toLinearMap l.1.direction := by
  have heq : l.1.map g.toAffineEquiv = l'.1 := by
    apply SetLike.coe_injective
    simpa [mapsLine] using h
  rw [← heq, AffineSubspace.map_direction]
  change Submodule.map g.linear.toLinearMap l.1.direction = _
  rw [g.linear_eq_linear_isometry]

private lemma prescribed_linear_injective (L₁ L₂ L'₁ L'₂ : Line 3)
    (hdir : L'₁.1.direction ≠ L'₂.1.direction)
    {g h : Motion 3} (hg₁ : mapsLine g L₁ L'₁) (hg₂ : mapsLine g L₂ L'₂)
    (hh₁ : mapsLine h L₁ L'₁) (hh₂ : mapsLine h L₂ L'₂)
    (hlin : g.linearIsometryEquiv = h.linearIsometryEquiv) : g = h := by
  have hshift (x : E 3) : g x -ᵥ g 0 = h x -ᵥ h 0 := by
    calc
      g x -ᵥ g 0 = g.linearIsometryEquiv (x -ᵥ (0 : E 3)) := (g.map_vsub x 0).symm
      _ = h.linearIsometryEquiv (x -ᵥ (0 : E 3)) := by rw [hlin]
      _ = h x -ᵥ h 0 := h.map_vsub x 0
  have hdisp (x : E 3) : g x -ᵥ h x = g 0 -ᵥ h 0 := by
    have hs := hshift x
    simp only [vsub_eq_sub] at hs ⊢
    calc
      g x - h x = (g x - g 0) - (h x - h 0) + (g 0 - h 0) := by abel
      _ = g 0 - h 0 := by rw [hs]; abel
  obtain ⟨p, hp⟩ := L₁.2.1
  obtain ⟨q, hq⟩ := L₂.2.1
  have hgp : g p ∈ (L'₁.1 : Set (E 3)) := by
    have hmem : g p ∈ g '' (L₁.1 : Set (E 3)) := ⟨p, hp, rfl⟩
    change g '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3)) at hg₁
    rw [hg₁] at hmem
    exact hmem
  have hhp : h p ∈ (L'₁.1 : Set (E 3)) := by
    have hmem : h p ∈ h '' (L₁.1 : Set (E 3)) := ⟨p, hp, rfl⟩
    change h '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3)) at hh₁
    rw [hh₁] at hmem
    exact hmem
  have hgq : g q ∈ (L'₂.1 : Set (E 3)) := by
    have hmem : g q ∈ g '' (L₂.1 : Set (E 3)) := ⟨q, hq, rfl⟩
    change g '' (L₂.1 : Set (E 3)) = (L'₂.1 : Set (E 3)) at hg₂
    rw [hg₂] at hmem
    exact hmem
  have hhq : h q ∈ (L'₂.1 : Set (E 3)) := by
    have hmem : h q ∈ h '' (L₂.1 : Set (E 3)) := ⟨q, hq, rfl⟩
    change h '' (L₂.1 : Set (E 3)) = (L'₂.1 : Set (E 3)) at hh₂
    rw [hh₂] at hmem
    exact hmem
  let t : E 3 := g 0 -ᵥ h 0
  have ht₁ : t ∈ L'₁.1.direction := by
    change g 0 -ᵥ h 0 ∈ L'₁.1.direction
    rw [← hdisp p]
    exact AffineSubspace.vsub_mem_direction hgp hhp
  have ht₂ : t ∈ L'₂.1.direction := by
    change g 0 -ᵥ h 0 ∈ L'₂.1.direction
    rw [← hdisp q]
    exact AffineSubspace.vsub_mem_direction hgq hhq
  have ht0 : t = 0 := by
    by_contra hne
    have hs₁ : L'₁.1.direction = ℝ ∙ t :=
      eq_span_singleton_of_mem_of_finrank_eq_one L'₁.2.2 ht₁ hne
    have hs₂ : L'₂.1.direction = ℝ ∙ t :=
      eq_span_singleton_of_mem_of_finrank_eq_one L'₂.2.2 ht₂ hne
    exact hdir (hs₁.trans hs₂.symm)
  have h00 : g 0 = h 0 := by
    exact vsub_eq_zero_iff_eq.mp (by simpa [t] using ht0)
  apply AffineIsometryEquiv.ext
  intro x
  calc
    g x = g.linearIsometryEquiv x + g 0 := by simpa using g.map_vadd 0 x
    _ = h.linearIsometryEquiv x + h 0 := by rw [hlin, h00]
    _ = h x := by
      symm
      simpa using h.map_vadd 0 x

private lemma span_pair_map (S : E 3 ≃ₗᵢ[ℝ] E 3) (u v : E 3) :
    Submodule.span ℝ ({S u, S v} : Set (E 3)) =
      Submodule.map S.toLinearEquiv.toLinearMap (Submodule.span ℝ ({u, v} : Set (E 3))) := by
  rw [Submodule.map_span]
  simp

private lemma span_pair_signs (u v x y : E 3) (hu : u = x ∨ u = -x) (hv : v = y ∨ v = -y) :
    Submodule.span ℝ ({u, v} : Set (E 3)) = Submodule.span ℝ ({x, y} : Set (E 3)) := by
  have pair (a b : E 3) : Submodule.span ℝ ({a, b} : Set (E 3)) = ℝ ∙ a ⊔ ℝ ∙ b :=
    span_pair_sup a b
  have hlineU : ℝ ∙ u = ℝ ∙ x := by
    rcases hu with hu | hu
    · rw [hu]
    · rw [hu]
      exact Submodule.span_singleton_eq_span_singleton.mpr ⟨-1, by simp⟩
  have hlineV : ℝ ∙ v = ℝ ∙ y := by
    rcases hv with hv | hv
    · rw [hv]
    · rw [hv]
      exact Submodule.span_singleton_eq_span_singleton.mpr ⟨-1, by simp⟩
  rw [pair, pair, hlineU, hlineV]


/-- mot:line-images(1), motions.tex:706–713, 728–741. -/
theorem line_images_nonparallel (L₁ L₂ L'₁ L'₂ : Line 3)
    (hL : L₁ ≠ L₂) (hL' : L'₁ ≠ L'₂) (hnp : ¬ parallel L₁ L₂) :
    FiniteCardBound (prescribedLineMotions L₁ L₂ L'₁ L'₂) 8 := by
  classical
  let S : Set (Motion 3) := prescribedLineMotions L₁ L₂ L'₁ L'₂
  by_cases hS : S.Nonempty
  · obtain ⟨g₀, hg₀⟩ := hS
    change mapsLine g₀ L₁ L'₁ ∧ mapsLine g₀ L₂ L'₂ at hg₀
    rcases hg₀ with ⟨hg₀₁, hg₀₂⟩
    obtain ⟨u, v, w, hu, hu0, hv, hv0, hD, hpair, hw, hspan⟩ := directions_basis L₁ L₂ hnp
    let D : Submodule ℝ (E 3) := L₁.1.direction ⊔ L₂.1.direction
    let T₀ : E 3 ≃ₗᵢ[ℝ] E 3 := g₀.linearIsometryEquiv
    have hD' : Module.finrank ℝ ↥D = 2 := by simpa [D] using hD
    have hE : Module.finrank ℝ (E 3) = 3 := by simp [E]
    have hdir₀₁ : L'₁.1.direction = Submodule.map T₀.toLinearEquiv.toLinearMap L₁.1.direction := by
      simpa only [g₀.linear_eq_linear_isometry] using direction_eq_of_mapsLine g₀ L₁ L'₁ hg₀₁
    have hdir₀₂ : L'₂.1.direction = Submodule.map T₀.toLinearEquiv.toLinearMap L₂.1.direction := by
      simpa only [g₀.linear_eq_linear_isometry] using direction_eq_of_mapsLine g₀ L₂ L'₂ hg₀₂
    have hdirne : L'₁.1.direction ≠ L'₂.1.direction := by
      intro heq
      have hmap : Submodule.map T₀.toLinearEquiv.toLinearMap L₁.1.direction =
          Submodule.map T₀.toLinearEquiv.toLinearMap L₂.1.direction := by
        rw [← hdir₀₁, ← hdir₀₂, heq]
      have hsrc : L₁.1.direction = L₂.1.direction :=
        (Submodule.map_injective_of_injective (f := T₀.toLinearEquiv.toLinearMap)
          T₀.toLinearEquiv.injective) hmap
      exact hnp (by simpa [parallel] using hsrc)
    have hT₀u : T₀ u ∈ L'₁.1.direction := by
      rw [hdir₀₁]
      exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    have hT₀v : T₀ v ∈ L'₂.1.direction := by
      rw [hdir₀₂]
      exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    let D₀ : Submodule ℝ (E 3) := Submodule.span ℝ ({T₀ u, T₀ v} : Set (E 3))
    have hD₀map : D₀ = Submodule.map T₀.toLinearEquiv.toLinearMap D := by
      simpa [D₀, D, ← hpair] using span_pair_map T₀ u v
    have hD₀rank : Module.finrank ℝ ↥D₀ = 2 := by
      calc
        Module.finrank ℝ ↥D₀ = Module.finrank ℝ ↥(Submodule.map T₀.toLinearEquiv.toLinearMap D) := by rw [hD₀map]
        _ = Module.finrank ℝ ↥D := T₀.toLinearEquiv.finrank_map_eq D
        _ = 2 := hD'
    have hD₀orth : Module.finrank ℝ ↥(D₀ᗮ) = 1 := by
      have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) D₀
      rw [hD₀rank, hE] at hsum
      omega
    let A : Set (E 3) := insert (T₀ u) {-(T₀ u)}
    let B : Set (E 3) := insert (T₀ v) {-(T₀ v)}
    let C : Set (E 3) := insert (T₀ w) {-(T₀ w)}
    have hAf : A.Finite := Set.Finite.insert _ (Set.finite_singleton _)
    have hBf : B.Finite := Set.Finite.insert _ (Set.finite_singleton _)
    have hCf : C.Finite := Set.Finite.insert _ (Set.finite_singleton _)
    have hAc : A.ncard ≤ 2 := by
      dsimp [A]
      calc
        (insert (T₀ u) {-(T₀ u)} : Set (E 3)).ncard ≤ ({-(T₀ u)} : Set (E 3)).ncard + 1 :=
          Set.ncard_insert_le _ _
        _ = 2 := by simp
    have hBc : B.ncard ≤ 2 := by
      dsimp [B]
      calc
        (insert (T₀ v) {-(T₀ v)} : Set (E 3)).ncard ≤ ({-(T₀ v)} : Set (E 3)).ncard + 1 :=
          Set.ncard_insert_le _ _
        _ = 2 := by simp
    have hCc : C.ncard ≤ 2 := by
      dsimp [C]
      calc
        (insert (T₀ w) {-(T₀ w)} : Set (E 3)).ncard ≤ ({-(T₀ w)} : Set (E 3)).ncard + 1 :=
          Set.ncard_insert_le _ _
        _ = 2 := by simp
    let Cand : Set (E 3 × (E 3 × E 3)) := A ×ˢ (B ×ˢ C)
    have hCandf : Cand.Finite := hAf.prod (hBf.prod hCf)
    have hCandc : Cand.ncard ≤ 8 := by
      dsimp [Cand]
      simp only [Set.ncard_prod]
      calc
        A.ncard * (B.ncard * C.ncard) ≤ 2 * (B.ncard * C.ncard) := Nat.mul_le_mul_right _ hAc
        _ ≤ 2 * (2 * 2) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hBc hCc)
        _ = 8 := by norm_num
    let enc : Motion 3 → E 3 × (E 3 × E 3) :=
      fun g => (g.linearIsometryEquiv u, (g.linearIsometryEquiv v, g.linearIsometryEquiv w))
    have hmaps : ∀ g ∈ S, enc g ∈ Cand := by
      intro g hg
      change mapsLine g L₁ L'₁ ∧ mapsLine g L₂ L'₂ at hg
      rcases hg with ⟨hg₁, hg₂⟩
      have hdir₁ : L'₁.1.direction = Submodule.map g.linearIsometryEquiv.toLinearEquiv.toLinearMap L₁.1.direction := by
        simpa only [g.linear_eq_linear_isometry] using direction_eq_of_mapsLine g L₁ L'₁ hg₁
      have hdir₂ : L'₂.1.direction = Submodule.map g.linearIsometryEquiv.toLinearEquiv.toLinearMap L₂.1.direction := by
        simpa only [g.linear_eq_linear_isometry] using direction_eq_of_mapsLine g L₂ L'₂ hg₂
      have hgu : g.linearIsometryEquiv u ∈ L'₁.1.direction := by
        rw [hdir₁]
        exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
      have hgv : g.linearIsometryEquiv v ∈ L'₂.1.direction := by
        rw [hdir₂]
        exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      have hsu : g.linearIsometryEquiv u = T₀ u ∨ g.linearIsometryEquiv u = -T₀ u :=
        same_norm_line L'₁.2.2 hgu hT₀u (by rw [g.linearIsometryEquiv.norm_map, T₀.norm_map])
      have hsv : g.linearIsometryEquiv v = T₀ v ∨ g.linearIsometryEquiv v = -T₀ v :=
        same_norm_line L'₂.2.2 hgv hT₀v (by rw [g.linearIsometryEquiv.norm_map, T₀.norm_map])
      have hDg : Submodule.span ℝ ({g.linearIsometryEquiv u, g.linearIsometryEquiv v} : Set (E 3)) = D₀ := by
        exact (span_pair_signs _ _ _ _ hsu hsv).trans (by rfl)
      have hDgmap : Submodule.span ℝ ({g.linearIsometryEquiv u, g.linearIsometryEquiv v} : Set (E 3)) =
          Submodule.map g.linearIsometryEquiv.toLinearEquiv.toLinearMap D := by
        simpa [D, ← hpair] using span_pair_map g.linearIsometryEquiv u v
      have hwg : g.linearIsometryEquiv w ∈ D₀ᗮ := by
        rw [← hDg, hDgmap]
        rw [Submodule.mem_orthogonal]
        intro z hz
        rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
        change inner ℝ (g.linearIsometryEquiv x) (g.linearIsometryEquiv w) = 0
        rw [g.linearIsometryEquiv.inner_map_map]
        exact Submodule.inner_right_of_mem_orthogonal hx (by simpa [D] using hw)
      have hw₀ : T₀ w ∈ D₀ᗮ := by
        rw [hD₀map]
        rw [Submodule.mem_orthogonal]
        intro z hz
        rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
        change inner ℝ (T₀ x) (T₀ w) = 0
        rw [T₀.inner_map_map]
        exact Submodule.inner_right_of_mem_orthogonal hx (by simpa [D] using hw)
      have hsw : g.linearIsometryEquiv w = T₀ w ∨ g.linearIsometryEquiv w = -T₀ w :=
        same_norm_line hD₀orth hwg hw₀ (by rw [g.linearIsometryEquiv.norm_map, T₀.norm_map])
      have hAu : g.linearIsometryEquiv u ∈ A := by
        rcases hsu with h | h <;> simp [A, h]
      have hBv : g.linearIsometryEquiv v ∈ B := by
        rcases hsv with h | h <;> simp [B, h]
      have hCw : g.linearIsometryEquiv w ∈ C := by
        rcases hsw with h | h <;> simp [C, h]
      change enc g ∈ A ×ˢ (B ×ˢ C)
      exact ⟨hAu, hBv, hCw⟩
    have hinj : Set.InjOn enc S := by
      intro g hg h hh henc
      change mapsLine g L₁ L'₁ ∧ mapsLine g L₂ L'₂ at hg
      change mapsLine h L₁ L'₁ ∧ mapsLine h L₂ L'₂ at hh
      have huEq : g.linearIsometryEquiv u = h.linearIsometryEquiv u := congrArg Prod.fst henc
      have hvEq : g.linearIsometryEquiv v = h.linearIsometryEquiv v := congrArg (fun z => z.2.1) henc
      have hwEq : g.linearIsometryEquiv w = h.linearIsometryEquiv w := congrArg (fun z => z.2.2) henc
      have hEvalG (x : E 3) : g.linear.toLinearMap x = g.linearIsometryEquiv x := by
        have he := congrArg (fun f : E 3 ≃ₗ[ℝ] E 3 => f x) g.linear_eq_linear_isometry
        simpa using he
      have hEvalH (x : E 3) : h.linear.toLinearMap x = h.linearIsometryEquiv x := by
        have he := congrArg (fun f : E 3 ≃ₗ[ℝ] E 3 => f x) h.linear_eq_linear_isometry
        simpa using he
      have hlin : g.linear.toLinearMap = h.linear.toLinearMap := by
        apply LinearMap.ext_on hspan
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hxu | hxv | hxw
        · simpa [hxu] using (calc
            g.linear.toLinearMap u = g.linearIsometryEquiv u := hEvalG u
            _ = h.linearIsometryEquiv u := huEq
            _ = h.linear.toLinearMap u := (hEvalH u).symm)
        · simpa [hxv] using (calc
            g.linear.toLinearMap v = g.linearIsometryEquiv v := hEvalG v
            _ = h.linearIsometryEquiv v := hvEq
            _ = h.linear.toLinearMap v := (hEvalH v).symm)
        · simpa [hxw] using (calc
            g.linear.toLinearMap w = g.linearIsometryEquiv w := hEvalG w
            _ = h.linearIsometryEquiv w := hwEq
            _ = h.linear.toLinearMap w := (hEvalH w).symm)
      have hS : g.linearIsometryEquiv = h.linearIsometryEquiv := by
        apply LinearIsometryEquiv.ext
        intro x
        calc
          g.linearIsometryEquiv x = g.linear.toLinearMap x := (hEvalG x).symm
          _ = h.linear.toLinearMap x := congrArg (fun f : E 3 →ₗ[ℝ] E 3 => f x) hlin
          _ = h.linearIsometryEquiv x := hEvalH x
      exact prescribed_linear_injective L₁ L₂ L'₁ L'₂ hdirne hg.1 hg.2 hh.1 hh.2 hS
    have hImgf : (enc '' S).Finite := hCandf.subset (by
      rintro z ⟨g, hg, rfl⟩
      exact hmaps g hg)
    have hSfinite : S.Finite := Set.Finite.of_finite_image hImgf hinj
    have hScard : S.ncard ≤ 8 :=
      (Set.ncard_le_ncard_of_injOn enc hmaps hinj hCandf).trans hCandc
    change S.Finite ∧ (S.ncard : ℝ) ≤ 8
    exact ⟨hSfinite, by exact_mod_cast hScard⟩
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    change S.Finite ∧ (S.ncard : ℝ) ≤ 8
    rw [hEmpty]
    simp

private lemma parallel_sep_projection (L₁ L₂ : Line 3) (hp : parallel L₁ L₂)
    (hL : L₁ ≠ L₂) :
    ∃ p ∈ L₁.1, ∃ q ∈ L₂.1, lineSeparation L₁ L₂ = dist p q ∧
      0 < dist p q ∧ q -ᵥ p ∈ L₁.1.directionᗮ := by
  obtain ⟨p, hp₁⟩ := L₁.2.1
  let D : Submodule ℝ (E 3) := L₁.1.direction
  have hdir : L₂.1.direction = D := by simpa [D, parallel] using hp.symm
  have hpnot : p ∉ L₂.1 := by
    intro hp₂
    apply hL
    apply Subtype.ext
    exact AffineSubspace.ext_of_direction_eq (by simpa [D] using hdir.symm) ⟨p, hp₁, hp₂⟩
  obtain ⟨p₂, hp₂⟩ := L₂.2.1
  letI : Nonempty ↥L₂.1 := ⟨⟨p₂, hp₂⟩⟩
  let q : E 3 := (EuclideanGeometry.orthogonalProjection (s := L₂.1) p : E 3)
  have hq : q ∈ L₂.1 := by
    dsimp [q]
    exact EuclideanGeometry.orthogonalProjection_mem (s := L₂.1) p
  have hperp : p -ᵥ q ∈ Dᗮ := by
    rw [← hdir]
    dsimp [q]
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal (s := L₂.1) p
  have hdne : dist p q ≠ 0 := by
    have h := EuclideanGeometry.dist_orthogonalProjection_ne_zero_of_notMem (s := L₂.1) hpnot
    simpa [q] using h
  have hdpos : 0 < dist p q := lt_of_le_of_ne (dist_nonneg : 0 ≤ dist p q) hdne.symm
  have hdist (x : E 3) (hx : x ∈ L₁.1) (y : E 3) (hy : y ∈ L₂.1) :
      dist p q ≤ dist x y := by
    have hxp : x -ᵥ p ∈ D := by
      exact AffineSubspace.vsub_mem_direction hx hp₁
    have hqy : q -ᵥ y ∈ D := by
      have hqy' := AffineSubspace.vsub_mem_direction hq hy
      rw [← hdir]
      exact hqy'
    let a : E 3 := (x -ᵥ p) + (q -ᵥ y)
    let b : E 3 := p -ᵥ q
    have ha : a ∈ D := by exact D.add_mem hxp hqy
    have hdecomp : x -ᵥ y = a + b := by
      dsimp [a, b]
      abel
    have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a b
      (Submodule.inner_right_of_mem_orthogonal ha hperp)
    rw [← hdecomp] at hsq
    have hn : ‖b‖ * ‖b‖ ≤ ‖x -ᵥ y‖ * ‖x -ᵥ y‖ := by nlinarith [hsq, mul_self_nonneg ‖a‖]
    rw [dist_eq_norm_vsub (E 3) p q, dist_eq_norm_vsub (E 3) x y]
    have hpqNonneg : 0 ≤ ‖p -ᵥ q‖ := norm_nonneg _
    have hxyNonneg : 0 ≤ ‖x -ᵥ y‖ := norm_nonneg _
    nlinarith [hn, hpqNonneg, hxyNonneg]
  let R : Set ℝ := {r | ∃ x ∈ (L₁.1 : Set (E 3)), ∃ y ∈ (L₂.1 : Set (E 3)), r = dist x y}
  have hmem : dist p q ∈ R := ⟨p, hp₁, q, hq, rfl⟩
  have hlower : ∀ r ∈ R, dist p q ≤ r := by
    rintro r ⟨x, hx, y, hy, rfl⟩
    exact hdist x hx y hy
  have hsep : lineSeparation L₁ L₂ = dist p q := by
    unfold lineSeparation
    change sInf R = dist p q
    apply le_antisymm
    · exact csInf_le ⟨dist p q, hlower⟩ hmem
    · exact le_csInf ⟨dist p q, hmem⟩ hlower
  have hperpR : q -ᵥ p ∈ Dᗮ := by
    have hneg : q -ᵥ p = -(p -ᵥ q) := by simp only [vsub_eq_sub]; abel
    rw [hneg]
    exact (Dᗮ).neg_mem hperp
  refine ⟨p, hp₁, q, hq, hsep, hdpos, ?_⟩
  simpa [D] using hperpR

private lemma lineSeparation_eq_of_mapsLine (g : Motion 3) (L₁ L₂ L'₁ L'₂ : Line 3)
    (h₁ : mapsLine g L₁ L'₁) (h₂ : mapsLine g L₂ L'₂) :
    lineSeparation L₁ L₂ = lineSeparation L'₁ L'₂ := by
  have hdist (x y : E 3) : dist (g x) (g y) = dist x y := by
    rw [dist_eq_norm_vsub (E 3), dist_eq_norm_vsub (E 3), ← g.map_vsub,
      g.linearIsometryEquiv.norm_map]
  have hset :
      {r : ℝ | ∃ x ∈ (L₁.1 : Set (E 3)), ∃ y ∈ (L₂.1 : Set (E 3)), r = dist x y} =
      {r : ℝ | ∃ x ∈ (L'₁.1 : Set (E 3)), ∃ y ∈ (L'₂.1 : Set (E 3)), r = dist x y} := by
    ext r
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      have hx' : g x ∈ (L'₁.1 : Set (E 3)) := by
        have hmem : g x ∈ g '' (L₁.1 : Set (E 3)) := ⟨x, hx, rfl⟩
        change g '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3)) at h₁
        rw [h₁] at hmem
        exact hmem
      have hy' : g y ∈ (L'₂.1 : Set (E 3)) := by
        have hmem : g y ∈ g '' (L₂.1 : Set (E 3)) := ⟨y, hy, rfl⟩
        change g '' (L₂.1 : Set (E 3)) = (L'₂.1 : Set (E 3)) at h₂
        rw [h₂] at hmem
        exact hmem
      exact ⟨g x, hx', g y, hy', (hdist x y).symm⟩
    · rintro ⟨x, hx, y, hy, hr⟩
      change g '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3)) at h₁
      change g '' (L₂.1 : Set (E 3)) = (L'₂.1 : Set (E 3)) at h₂
      rw [← h₁] at hx
      rw [← h₂] at hy
      rcases hx with ⟨x₀, hx₀, rfl⟩
      rcases hy with ⟨y₀, hy₀, rfl⟩
      exact ⟨x₀, hx₀, y₀, hy₀, hr.trans (hdist x₀ y₀)⟩
  simpa [lineSeparation] using congrArg (fun U : Set ℝ => sInf U) hset

private lemma vadd_image_eq_self (H : AffineSubspace ℝ (E 3)) (v : E 3)
    (hv : v ∈ H.direction) : (fun x : E 3 => v +ᵥ x) '' (H : Set (E 3)) = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact AffineSubspace.vadd_mem_of_mem_direction hv hy
  · intro hx
    refine ⟨(-v) +ᵥ x, AffineSubspace.vadd_mem_of_mem_direction (H.direction.neg_mem hv) hx, ?_⟩
    simp [vadd_vadd]

private lemma affineIso_displacement_eq {g h : Motion 3}
    (hlin : g.linearIsometryEquiv = h.linearIsometryEquiv) (x : E 3) :
    g x -ᵥ h x = g 0 -ᵥ h 0 := by
  have hshift : g x -ᵥ g 0 = h x -ᵥ h 0 := by
    calc
      g x -ᵥ g 0 = g.linearIsometryEquiv (x -ᵥ (0 : E 3)) := (g.map_vsub x 0).symm
      _ = h.linearIsometryEquiv (x -ᵥ (0 : E 3)) := by rw [hlin]
      _ = h x -ᵥ h 0 := h.map_vsub x 0
  have hs := hshift
  simp only [vsub_eq_sub] at hs ⊢
  calc
    g x - h x = (g x - g 0) - (h x - h 0) + (g 0 - h 0) := by abel
    _ = g 0 - h 0 := by rw [hs]; abel

private lemma constVAdd_trans_linear (g : Motion 3) (v : E 3) :
    (g.trans (AffineIsometryEquiv.constVAdd ℝ (E 3) v)).linearIsometryEquiv = g.linearIsometryEquiv := by
  let g' : Motion 3 := g.trans (AffineIsometryEquiv.constVAdd ℝ (E 3) v)
  apply LinearIsometryEquiv.ext
  intro x
  have hx : g' x = v +ᵥ g x := rfl
  have h0 : g' 0 = v +ᵥ g 0 := rfl
  calc
    g'.linearIsometryEquiv x = g' x -ᵥ g' 0 := by simpa using (g'.map_vsub x 0)
    _ = (v +ᵥ g x) -ᵥ (v +ᵥ g 0) := by rw [hx, h0]
    _ = g x -ᵥ g 0 := vadd_vsub_vadd_cancel_left v (g x) (g 0)
    _ = g.linearIsometryEquiv x := by simpa using (g.map_vsub x 0).symm

private lemma perp_frame (L : Line 3) (r : E 3)
    (hr : r ∈ L.1.directionᗮ) (hr0 : r ≠ 0) :
    ∃ u w : E 3,
      u ∈ L.1.direction ∧ u ≠ 0 ∧
      Module.finrank ℝ ↥(L.1.direction ⊔ ℝ ∙ r) = 2 ∧
      Submodule.span ℝ ({u, r} : Set (E 3)) = L.1.direction ⊔ ℝ ∙ r ∧
      w ∈ (L.1.direction ⊔ ℝ ∙ r)ᗮ ∧
      Submodule.span ℝ ({u, r, w} : Set (E 3)) = ⊤ := by
  let D : Submodule ℝ (E 3) := L.1.direction
  have hD : Module.finrank ℝ D = 1 := L.2.2
  have hDbot : D ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hD
    norm_num at hD
  obtain ⟨u, hu, hu0⟩ := D.ne_bot_iff.mp hDbot
  have huSpan : D = ℝ ∙ u := eq_span_singleton_of_mem_of_finrank_eq_one hD hu hu0
  have hrnotD : r ∉ D := by
    intro hrD
    have hmem : r ∈ D ⊓ Dᗮ := ⟨hrD, hr⟩
    have hbot : D ⊓ Dᗮ = ⊥ := (Submodule.orthogonal_disjoint D).eq_bot
    rw [hbot, Submodule.mem_bot] at hmem
    exact hr0 hmem
  have hrnotSpan : r ∉ ℝ ∙ u := by simpa [huSpan] using hrnotD
  let C : Submodule ℝ (E 3) := D ⊔ ℝ ∙ r
  have hCrank : Module.finrank ℝ ↥C = 2 := by
    rw [Submodule.finrank_sup_span_singleton hrnotD, hD]
  have hpair : Submodule.span ℝ ({u, r} : Set (E 3)) = C := by
    calc
      Submodule.span ℝ ({u, r} : Set (E 3)) = ℝ ∙ u ⊔ ℝ ∙ r := by
        rw [show ({u, r} : Set (E 3)) = insert u ({r} : Set (E 3)) by ext x; simp,
          Submodule.span_insert]
      _ = C := by simp [C, huSpan]
  have hE : Module.finrank ℝ (E 3) = 3 := by simp [E]
  have hCorth : Module.finrank ℝ ↥(Cᗮ) = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) C
    rw [hCrank, hE] at hsum
    omega
  have hCorthbot : Cᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hCorth
    norm_num at hCorth
  obtain ⟨w, hw, hw0⟩ := Cᗮ.ne_bot_iff.mp hCorthbot
  have hwnot : w ∉ C := by
    intro hwC
    have hmem : w ∈ C ⊓ Cᗮ := ⟨hwC, hw⟩
    have hbot : C ⊓ Cᗮ = ⊥ := (Submodule.orthogonal_disjoint C).eq_bot
    rw [hbot, Submodule.mem_bot] at hmem
    exact hw0 hmem
  have htop : C ⊔ ℝ ∙ w = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hwnot, hCrank, hE]
  have htriple : ({u, r, w} : Set (E 3)) = ({u, r} : Set (E 3)) ∪ {w} := by
    ext x
    simp <;> tauto
  refine ⟨u, w, hu, hu0, hCrank, hpair, hw, ?_⟩
  rw [htriple, Submodule.span_union, hpair]
  simpa [C] using htop

/-- mot:line-images(2), geometric part, motions.tex:714–717, 743–757. -/
theorem line_images_parallel (L₁ L₂ L'₁ L'₂ : Line 3)
    (hL : L₁ ≠ L₂) (hL' : L'₁ ≠ L'₂) (hp : parallel L₁ L₂)
    (hne : (prescribedLineMotions L₁ L₂ L'₁ L'₂).Nonempty) :
    parallel L'₁ L'₂ ∧ lineSeparation L₁ L₂ = lineSeparation L'₁ L'₂ ∧
      0 < lineSeparation L₁ L₂ ∧
      FiniteCardBound
        ((fun g : Motion 3 => g.linearIsometryEquiv) '' prescribedLineMotions L₁ L₂ L'₁ L'₂) 4 ∧
      ∀ S : E 3 ≃ₗᵢ[ℝ] E 3,
        S ∈ ((fun g : Motion 3 => g.linearIsometryEquiv) '' prescribedLineMotions L₁ L₂ L'₁ L'₂) →
        ∃ T : Line 3, T.1.direction = L'₁.1.direction ∧
          {h : E 3 | ∃ g ∈ prescribedLineMotions L₁ L₂ L'₁ L'₂,
            g.linearIsometryEquiv = S ∧ g 0 = h} = (T.1 : Set (E 3)) := by
  classical
  obtain ⟨g₀, hg₀⟩ := hne
  change mapsLine g₀ L₁ L'₁ ∧ mapsLine g₀ L₂ L'₂ at hg₀
  rcases hg₀ with ⟨hg₀₁, hg₀₂⟩
  let D : Submodule ℝ (E 3) := L₁.1.direction
  let T₀ : E 3 ≃ₗᵢ[ℝ] E 3 := g₀.linearIsometryEquiv
  have hsourceDir : L₂.1.direction = D := by simpa [D, parallel] using hp.symm
  have hdir₀₁ : L'₁.1.direction = Submodule.map T₀.toLinearEquiv.toLinearMap D := by
    simpa only [g₀.linear_eq_linear_isometry] using
      direction_eq_of_mapsLine g₀ L₁ L'₁ hg₀₁
  have hdir₀₂' : L'₂.1.direction = Submodule.map T₀.toLinearEquiv.toLinearMap L₂.1.direction := by
    simpa only [g₀.linear_eq_linear_isometry] using
      direction_eq_of_mapsLine g₀ L₂ L'₂ hg₀₂
  have hdir₀₂ : L'₂.1.direction = Submodule.map T₀.toLinearEquiv.toLinearMap D := by
    simpa [hsourceDir] using hdir₀₂'
  have hdirTar : L'₁.1.direction = L'₂.1.direction := hdir₀₁.trans hdir₀₂.symm
  have hsepEq : lineSeparation L₁ L₂ = lineSeparation L'₁ L'₂ :=
    lineSeparation_eq_of_mapsLine g₀ L₁ L₂ L'₁ L'₂ hg₀₁ hg₀₂
  obtain ⟨p, hp₁, q, hq, hsepProj, hsepPos, hrperp0⟩ :=
    parallel_sep_projection L₁ L₂ hp hL
  have hpos : 0 < lineSeparation L₁ L₂ := by rw [hsepProj]; exact hsepPos
  let r : E 3 := q -ᵥ p
  have hrperp : r ∈ Dᗮ := by simpa [r, D] using hrperp0
  have hr0 : r ≠ 0 := by
    intro hr
    have hqp : q = p := vsub_eq_zero_iff_eq.mp (by simpa [r] using hr)
    subst q
    simp at hsepPos
  obtain ⟨u, w, hu, hu0, hCrank, hCpair, hwC, hspan⟩ :=
    perp_frame L₁ r hrperp hr0
  let Csrc : Submodule ℝ (E 3) := D ⊔ ℝ ∙ r
  have hCsrcEq : Submodule.span ℝ ({u, r} : Set (E 3)) = Csrc := by
    simpa [Csrc, D] using hCpair
  have hC0map : Submodule.span ℝ ({T₀ u, T₀ r} : Set (E 3)) =
      Submodule.map T₀.toLinearEquiv.toLinearMap Csrc := by
    calc
      Submodule.span ℝ ({T₀ u, T₀ r} : Set (E 3)) =
          Submodule.map T₀.toLinearEquiv.toLinearMap (Submodule.span ℝ ({u, r} : Set (E 3))) :=
        span_pair_map T₀ u r
      _ = Submodule.map T₀.toLinearEquiv.toLinearMap Csrc :=
        congrArg (Submodule.map T₀.toLinearEquiv.toLinearMap) hCsrcEq
  let C₀ : Submodule ℝ (E 3) := Submodule.span ℝ ({T₀ u, T₀ r} : Set (E 3))
  have hC₀rank : Module.finrank ℝ ↥C₀ = 2 := by
    calc
      Module.finrank ℝ ↥C₀ = Module.finrank ℝ ↥(Submodule.map T₀.toLinearEquiv.toLinearMap Csrc) := by
        change Module.finrank ℝ ↥(Submodule.span ℝ ({T₀ u, T₀ r} : Set (E 3))) = _
        rw [hC0map]
      _ = Module.finrank ℝ ↥Csrc := T₀.toLinearEquiv.finrank_map_eq Csrc
      _ = 2 := hCrank
  have hE : Module.finrank ℝ (E 3) = 3 := by simp [E]
  have hC₀orth : Module.finrank ℝ ↥(C₀ᗮ) = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) C₀
    rw [hC₀rank, hE] at hsum
    omega
  let D' : Submodule ℝ (E 3) := L'₁.1.direction
  have hD'map : D' = Submodule.map T₀.toLinearEquiv.toLinearMap D := by simpa [D'] using hdir₀₁
  have hT₀u : T₀ u ∈ D' := by
    rw [hD'map]
    exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
  have hT₀r_orth : T₀ r ∈ D'ᗮ := by
    rw [hD'map, Submodule.mem_orthogonal]
    intro z hz
    rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
    change inner ℝ (T₀ x) (T₀ r) = 0
    rw [T₀.inner_map_map]
    exact Submodule.inner_right_of_mem_orthogonal hx hrperp
  have hdirG (g : Motion 3) (hg₁ : mapsLine g L₁ L'₁) :
      D' = Submodule.map g.linearIsometryEquiv.toLinearEquiv.toLinearMap D := by
    have h := direction_eq_of_mapsLine g L₁ L'₁ hg₁
    simpa only [g.linear_eq_linear_isometry] using h
  let A : Set (E 3) := insert (T₀ u) {-(T₀ u)}
  let B : Set (E 3) := {T₀ r}
  let C : Set (E 3) := insert (T₀ w) {-(T₀ w)}
  have hAf : A.Finite := Set.Finite.insert _ (Set.finite_singleton _)
  have hBf : B.Finite := Set.finite_singleton _
  have hCf : C.Finite := Set.Finite.insert _ (Set.finite_singleton _)
  have hAc : A.ncard ≤ 2 := by
    dsimp [A]
    calc
      (insert (T₀ u) {-(T₀ u)} : Set (E 3)).ncard ≤ ({-(T₀ u)} : Set (E 3)).ncard + 1 :=
        Set.ncard_insert_le _ _
      _ = 2 := by simp
  have hBc : B.ncard ≤ 1 := by simp [B]
  have hCc : C.ncard ≤ 2 := by
    dsimp [C]
    calc
      (insert (T₀ w) {-(T₀ w)} : Set (E 3)).ncard ≤ ({-(T₀ w)} : Set (E 3)).ncard + 1 :=
        Set.ncard_insert_le _ _
      _ = 2 := by simp
  let Cand : Set (E 3 × (E 3 × E 3)) := A ×ˢ (B ×ˢ C)
  have hCandf : Cand.Finite := hAf.prod (hBf.prod hCf)
  have hCandc : Cand.ncard ≤ 4 := by
    dsimp [Cand]
    simp only [Set.ncard_prod]
    calc
      A.ncard * (B.ncard * C.ncard) ≤ 2 * (B.ncard * C.ncard) := Nat.mul_le_mul_right _ hAc
      _ ≤ 2 * (1 * 2) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hBc hCc)
      _ = 4 := by norm_num
  let Lin : Set (E 3 ≃ₗᵢ[ℝ] E 3) :=
    (fun g : Motion 3 => g.linearIsometryEquiv) '' prescribedLineMotions L₁ L₂ L'₁ L'₂
  let enc : (E 3 ≃ₗᵢ[ℝ] E 3) → E 3 × (E 3 × E 3) :=
    fun S => (S u, (S r, S w))
  have hmaps : ∀ S ∈ Lin, enc S ∈ Cand := by
    intro S hS
    change S ∈ (fun g : Motion 3 => g.linearIsometryEquiv) '' prescribedLineMotions L₁ L₂ L'₁ L'₂ at hS
    rcases (Set.mem_image _ _ _).mp hS with ⟨g, hg, rfl⟩
    change mapsLine g L₁ L'₁ ∧ mapsLine g L₂ L'₂ at hg
    rcases hg with ⟨hg₁, hg₂⟩
    have hdirg : D' = Submodule.map g.linearIsometryEquiv.toLinearEquiv.toLinearMap D := hdirG g hg₁
    have hgu : g.linearIsometryEquiv u ∈ D' := by
      rw [hdirg]
      exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    have hsu : g.linearIsometryEquiv u = T₀ u ∨ g.linearIsometryEquiv u = -T₀ u :=
      same_norm_line L'₁.2.2 hgu hT₀u (by rw [g.linearIsometryEquiv.norm_map, T₀.norm_map])
    have hqr : g q -ᵥ g₀ q ∈ D' := by
      have hqg : g q ∈ L'₂.1 := by
        have hm : g q ∈ g '' (L₂.1 : Set (E 3)) := ⟨q, hq, rfl⟩
        change g '' (L₂.1 : Set (E 3)) = (L'₂.1 : Set (E 3)) at hg₂
        rw [hg₂] at hm
        exact hm
      have hq₀ : g₀ q ∈ L'₂.1 := by
        have hm : g₀ q ∈ g₀ '' (L₂.1 : Set (E 3)) := ⟨q, hq, rfl⟩
        change g₀ '' (L₂.1 : Set (E 3)) = (L'₂.1 : Set (E 3)) at hg₀₂
        rw [hg₀₂] at hm
        exact hm
      have hqDiff := AffineSubspace.vsub_mem_direction hqg hq₀
      change g q -ᵥ g₀ q ∈ L'₁.1.direction
      rw [hdirTar]
      exact hqDiff
    have hpg : g p -ᵥ g₀ p ∈ D' := by
      have hpg₁ : g p ∈ L'₁.1 := by
        have hm : g p ∈ g '' (L₁.1 : Set (E 3)) := ⟨p, hp₁, rfl⟩
        change g '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3)) at hg₁
        rw [hg₁] at hm
        exact hm
      have hp₀ : g₀ p ∈ L'₁.1 := by
        have hm : g₀ p ∈ g₀ '' (L₁.1 : Set (E 3)) := ⟨p, hp₁, rfl⟩
        change g₀ '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3)) at hg₀₁
        rw [hg₀₁] at hm
        exact hm
      exact AffineSubspace.vsub_mem_direction hpg₁ hp₀
    have hfixedR : g.linearIsometryEquiv r = T₀ r := by
      have hEvalG : g.linearIsometryEquiv r = g q -ᵥ g p := by simpa [r] using g.map_vsub q p
      have hEval₀ : T₀ r = g₀ q -ᵥ g₀ p := by simpa [r, T₀] using g₀.map_vsub q p
      have halg : (g q -ᵥ g p) - (g₀ q -ᵥ g₀ p) =
          (g q -ᵥ g₀ q) - (g p -ᵥ g₀ p) := by
        simp only [vsub_eq_sub]
        abel
      have hdelta : g.linearIsometryEquiv r - T₀ r ∈ D' := by
        rw [hEvalG, hEval₀, halg]
        exact D'.sub_mem hqr hpg
      have hRorth : g.linearIsometryEquiv r ∈ D'ᗮ := by
        rw [hdirg, Submodule.mem_orthogonal]
        intro z hz
        rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
        change inner ℝ (g.linearIsometryEquiv x) (g.linearIsometryEquiv r) = 0
        rw [g.linearIsometryEquiv.inner_map_map]
        exact Submodule.inner_right_of_mem_orthogonal hx hrperp
      have hmeet : g.linearIsometryEquiv r - T₀ r ∈ D'ᗮ := by
        exact (D'ᗮ).sub_mem hRorth hT₀r_orth
      have hbot : D' ⊓ D'ᗮ = ⊥ := (Submodule.orthogonal_disjoint D').eq_bot
      have hz : g.linearIsometryEquiv r - T₀ r = 0 := by
        have hmem : g.linearIsometryEquiv r - T₀ r ∈ D' ⊓ D'ᗮ := ⟨hdelta, hmeet⟩
        rw [hbot, Submodule.mem_bot] at hmem
        exact hmem
      exact sub_eq_zero.mp hz
    let Dg : Submodule ℝ (E 3) := Submodule.span ℝ ({g.linearIsometryEquiv u, g.linearIsometryEquiv r} : Set (E 3))
    have hDg : Dg = Submodule.span ℝ ({T₀ u, T₀ r} : Set (E 3)) := by
      simpa [Dg] using span_pair_signs _ _ _ _ hsu (Or.inl hfixedR)
    have hDgMap : Dg = Submodule.map g.linearIsometryEquiv.toLinearEquiv.toLinearMap Csrc := by
      calc
        Dg = Submodule.map g.linearIsometryEquiv.toLinearEquiv.toLinearMap
            (Submodule.span ℝ ({u, r} : Set (E 3))) := by
          simpa [Dg] using span_pair_map g.linearIsometryEquiv u r
        _ = Submodule.map g.linearIsometryEquiv.toLinearEquiv.toLinearMap Csrc :=
          congrArg (Submodule.map g.linearIsometryEquiv.toLinearEquiv.toLinearMap) hCsrcEq
    have hwg : g.linearIsometryEquiv w ∈ C₀ᗮ := by
      have htarget : Dgᗮ = C₀ᗮ := by rw [hDg]
      rw [← htarget, hDgMap, Submodule.mem_orthogonal]
      intro z hz
      rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
      change inner ℝ (g.linearIsometryEquiv x) (g.linearIsometryEquiv w) = 0
      rw [g.linearIsometryEquiv.inner_map_map]
      exact Submodule.inner_right_of_mem_orthogonal hx hwC
    have hw₀ : T₀ w ∈ C₀ᗮ := by
      change T₀ w ∈ (Submodule.span ℝ ({T₀ u, T₀ r} : Set (E 3)))ᗮ
      rw [hC0map, Submodule.mem_orthogonal]
      intro z hz
      rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
      change inner ℝ (T₀ x) (T₀ w) = 0
      rw [T₀.inner_map_map]
      exact Submodule.inner_right_of_mem_orthogonal hx hwC
    have hsw : g.linearIsometryEquiv w = T₀ w ∨ g.linearIsometryEquiv w = -T₀ w :=
      same_norm_line hC₀orth hwg hw₀ (by rw [g.linearIsometryEquiv.norm_map, T₀.norm_map])
    have hAu : g.linearIsometryEquiv u ∈ A := by rcases hsu with h | h <;> simp [A, h]
    have hBr : g.linearIsometryEquiv r ∈ B := by simp [B, hfixedR]
    have hCw : g.linearIsometryEquiv w ∈ C := by rcases hsw with h | h <;> simp [C, h]
    change enc g.linearIsometryEquiv ∈ A ×ˢ (B ×ˢ C)
    exact ⟨hAu, hBr, hCw⟩
  have hinj : Set.InjOn enc Lin := by
    intro S hS S' hS' heq
    have huEq : S u = S' u := congrArg Prod.fst heq
    have hrEq : S r = S' r := congrArg (fun z => z.2.1) heq
    have hwEq : S w = S' w := congrArg (fun z => z.2.2) heq
    have hlin : S.toLinearEquiv.toLinearMap = S'.toLinearEquiv.toLinearMap := by
      apply LinearMap.ext_on hspan
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hxu | hxr | hxw
      · simpa [hxu] using huEq
      · simpa [hxr] using hrEq
      · simpa [hxw] using hwEq
    apply LinearIsometryEquiv.ext
    intro x
    exact congrArg (fun f : E 3 →ₗ[ℝ] E 3 => f x) hlin
  have hImgf : (enc '' Lin).Finite := hCandf.subset (by rintro z ⟨S, hS, rfl⟩; exact hmaps S hS)
  have hLinFinite : Lin.Finite := Set.Finite.of_finite_image hImgf hinj
  have hLinCard : Lin.ncard ≤ 4 :=
    (Set.ncard_le_ncard_of_injOn enc hmaps hinj hCandf).trans hCandc
  have hFiniteLin : FiniteCardBound Lin 4 := by
    change Lin.Finite ∧ (Lin.ncard : ℝ) ≤ 4
    exact ⟨hLinFinite, by exact_mod_cast hLinCard⟩
  refine ⟨by simpa [parallel] using hdirTar, hsepEq, hpos, hFiniteLin, ?_⟩
  intro S hS
  change S ∈ (fun g : Motion 3 => g.linearIsometryEquiv) '' prescribedLineMotions L₁ L₂ L'₁ L'₂ at hS
  rcases (Set.mem_image _ _ _).mp hS with ⟨g₀, hg₀, rfl⟩
  change mapsLine g₀ L₁ L'₁ ∧ mapsLine g₀ L₂ L'₂ at hg₀
  rcases hg₀ with ⟨hg₀₁, hg₀₂⟩
  let D' : Submodule ℝ (E 3) := L'₁.1.direction
  let T : Line 3 := ⟨AffineSubspace.mk' (g₀ 0) D',
    ⟨⟨g₀ 0, by simp [AffineSubspace.mem_mk']⟩, by rw [AffineSubspace.direction_mk']; exact L'₁.2.2⟩⟩
  have hbase : g₀.linearIsometryEquiv = g₀.linearIsometryEquiv := rfl
  have hfiber :
      {h : E 3 | ∃ g ∈ prescribedLineMotions L₁ L₂ L'₁ L'₂,
        g.linearIsometryEquiv = g₀.linearIsometryEquiv ∧ g 0 = h} = (T.1 : Set (E 3)) := by
    ext z
    constructor
    · rintro ⟨g, hg, hlin, hz⟩
      change z -ᵥ g₀ 0 ∈ D'
      have hmaps : mapsLine g L₁ L'₁ ∧ mapsLine g L₂ L'₂ := by simpa [prescribedLineMotions] using hg
      rcases hmaps with ⟨hg₁, hg₂⟩
      obtain ⟨x, hx⟩ := L₁.2.1
      have hgx : g x ∈ L'₁.1 := by
        have hm : g x ∈ g '' (L₁.1 : Set (E 3)) := ⟨x, hx, rfl⟩
        change g '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3)) at hg₁
        rw [hg₁] at hm
        exact hm
      have hbaseX : g₀ x ∈ L'₁.1 := by
        have hm : g₀ x ∈ g₀ '' (L₁.1 : Set (E 3)) := ⟨x, hx, rfl⟩
        change g₀ '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3)) at hg₀₁
        rw [hg₀₁] at hm
        exact hm
      have hdisp := affineIso_displacement_eq hlin x
      have hmem : g x -ᵥ g₀ x ∈ D' := by
        have h := AffineSubspace.vsub_mem_direction hgx hbaseX
        simpa [D'] using h
      rw [← hz, ← hdisp]
      exact hmem
    · intro hz
      change z -ᵥ g₀ 0 ∈ D' at hz
      let v : E 3 := z -ᵥ g₀ 0
      have hvD : v ∈ D' := by simpa [v] using hz
      let τ : Motion 3 := AffineIsometryEquiv.constVAdd ℝ (E 3) v
      let g : Motion 3 := g₀.trans τ
      have hg₁ : mapsLine g L₁ L'₁ := by
        change (fun x : E 3 => v +ᵥ g₀ x) '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3))
        rw [← Set.image_image, hg₀₁]
        exact vadd_image_eq_self L'₁.1 v hvD
      have hg₂ : mapsLine g L₂ L'₂ := by
        change (fun x : E 3 => v +ᵥ g₀ x) '' (L₂.1 : Set (E 3)) = (L'₂.1 : Set (E 3))
        rw [← Set.image_image, hg₀₂]
        have hv₂ : v ∈ L'₂.1.direction := by
          have hz' : v ∈ D' := by simpa [v] using hz
          simpa [D', hdirTar] using hz'
        exact vadd_image_eq_self L'₂.1 v hv₂
      have hlin : g.linearIsometryEquiv = g₀.linearIsometryEquiv := by
        simpa [g, τ] using constVAdd_trans_linear g₀ v
      have hzero : g 0 = z := by
        change v +ᵥ g₀ 0 = z
        dsimp [v]
        exact vsub_vadd z (g₀ 0)
      exact ⟨g, by change mapsLine g L₁ L'₁ ∧ mapsLine g L₂ L'₂; exact ⟨hg₁, hg₂⟩,
        hlin, hzero⟩
  have hTdir : T.1.direction = D' := by
    change (AffineSubspace.mk' (g₀ 0) D').direction = D'
    rw [AffineSubspace.direction_mk']
  exact ⟨T, by simpa [D'] using hTdir, hfiber⟩

/-- mot:parallel-weight, motions.tex:718–724, 759–771. -/
private lemma motion_eq_of_linear_apply {g h : Motion 3}
    (hlin : g.linearIsometryEquiv = h.linearIsometryEquiv) {x : E 3} (hx : g x = h x) :
    g = h := by
  apply AffineIsometryEquiv.ext
  intro z
  have hv : g z -ᵥ g x = h z -ᵥ h x := by
    calc
      g z -ᵥ g x = g.linearIsometryEquiv (z -ᵥ x) := (g.map_vsub z x).symm
      _ = h.linearIsometryEquiv (z -ᵥ x) := by rw [hlin]
      _ = h z -ᵥ h x := h.map_vsub z x
  calc
    g z = (g z -ᵥ g x) +ᵥ g x := by simp
    _ = (h z -ᵥ h x) +ᵥ g x := by rw [hv]
    _ = (h z -ᵥ h x) +ᵥ h x := by rw [hx]
    _ = h z := by simp

theorem parallel_line_weights (X Y : Finset (E 3)) (L₁ L₂ L'₁ L'₂ : Line 3)
    (H : ℝ) (hH : 0 ≤ H) (hL : L₁ ≠ L₂) (hL' : L'₁ ≠ L'₂) (hp : parallel L₁ L₂)
    (hX₁ : ((pointsOn X L₁).card : ℝ) ≤ H) (hX₂ : ((pointsOn X L₂).card : ℝ) ≤ H)
    (hY₁ : ((pointsOn Y L'₁).card : ℝ) ≤ H) (hY₂ : ((pointsOn Y L'₂).card : ℝ) ≤ H) :
    {g : Motion 3 | g ∈ prescribedLineMotions L₁ L₂ L'₁ L'₂ ∧
      0 < lineMatchWeight X Y L₁ L'₁ g * lineMatchWeight X Y L₂ L'₂ g}.Finite ∧
      ∀ G : Finset (Motion 3),
        (∀ g ∈ G, g ∈ prescribedLineMotions L₁ L₂ L'₁ L'₂) →
        ∑ g ∈ G, (lineMatchWeight X Y L₁ L'₁ g : ℝ) * lineMatchWeight X Y L₂ L'₂ g ≤
          4 * H ^ 3 := by
  classical
  let A : Finset (E 3) := pointsOn X L₁
  let B : Finset (E 3) := pointsOn Y L'₁
  let w₁ : Motion 3 → ℕ := lineMatchWeight X Y L₁ L'₁
  let w₂ : Motion 3 → ℕ := lineMatchWeight X Y L₂ L'₂
  let U : Set (Motion 3) := {g | g ∈ prescribedLineMotions L₁ L₂ L'₁ L'₂ ∧
    0 < w₁ g * w₂ g}
  change U.Finite ∧ ∀ G : Finset (Motion 3),
    (∀ g ∈ G, g ∈ prescribedLineMotions L₁ L₂ L'₁ L'₂) →
    ∑ g ∈ G, (w₁ g : ℝ) * (w₂ g : ℝ) ≤ 4 * H ^ 3
  have hw₁ (g : Motion 3) : 0 ≤ (w₁ g : ℝ) ∧ (w₁ g : ℝ) ≤ H := by
    constructor
    · positivity
    · have hsub : matchPoints A B g ⊆ A := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      have hcard := Finset.card_le_card hsub
      have hcardR : ((matchPoints A B g).card : ℝ) ≤ (A.card : ℝ) := by
        exact_mod_cast hcard
      change ((matchCount (pointsOn X L₁) (pointsOn Y L'₁) g : ℝ)) ≤ H
      have hA : (A.card : ℝ) ≤ H := by simpa [A] using hX₁
      simpa [lineMatchWeight, matchCount, A, B] using hcardR.trans hA
  have hw₂ (g : Motion 3) : 0 ≤ (w₂ g : ℝ) ∧ (w₂ g : ℝ) ≤ H := by
    constructor
    · positivity
    · have hsub : matchPoints (pointsOn X L₂) (pointsOn Y L'₂) g ⊆ pointsOn X L₂ := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      have hcard := Finset.card_le_card hsub
      have hcardR : ((matchPoints (pointsOn X L₂) (pointsOn Y L'₂) g).card : ℝ) ≤
          ((pointsOn X L₂).card : ℝ) := by exact_mod_cast hcard
      change ((matchCount (pointsOn X L₂) (pointsOn Y L'₂) g : ℝ)) ≤ H
      exact hcardR.trans hX₂
  have hfirst_pos (g : Motion 3) (hg : g ∈ U) : 0 < (w₁ g : ℝ) := by
    have hp : 0 < w₁ g := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have hnot : ¬ 0 < w₁ g * w₂ g := by simp [hzero]
      exact hnot hg.2
    exact_mod_cast hp
  by_cases hUne : U.Nonempty
  · obtain ⟨g₀, hg₀⟩ := hUne
    have hpres : (prescribedLineMotions L₁ L₂ L'₁ L'₂).Nonempty := ⟨g₀, hg₀.1⟩
    obtain ⟨hparTar, hsep, hsepPos, hlinBound, hfiber⟩ :=
      line_images_parallel L₁ L₂ L'₁ L'₂ hL hL' hp hpres
    let Sset : Set (E 3 ≃ₗᵢ[ℝ] E 3) :=
      (fun g : Motion 3 => g.linearIsometryEquiv) '' prescribedLineMotions L₁ L₂ L'₁ L'₂
    rcases hlinBound with ⟨hSfinite, hSboundRaw⟩
    have hSbound : (hSfinite.toFinset.card : ℝ) ≤ 4 := by
      rw [← Set.ncard_eq_toFinset_card Sset hSfinite]
      exact hSboundRaw
    let SF : Finset (E 3 ≃ₗᵢ[ℝ] E 3) := hSfinite.toFinset
    have hmatch (g : Motion 3) (hg : g ∈ U) : (matchPoints A B g).Nonempty := by
      have hp : (0 : ℝ) < (w₁ g : ℝ) := hfirst_pos g hg
      have hp' : (0 : ℝ) < ((matchPoints A B g).card : ℝ) := by
        simpa [w₁, lineMatchWeight, matchCount, A, B] using hp
      exact Finset.card_pos.mp (Nat.cast_pos.mp hp')
    let xOf : Motion 3 → E 3 := fun g =>
      if hg : g ∈ U then Classical.choose (hmatch g hg) else 0
    let enc : Motion 3 → (E 3 ≃ₗᵢ[ℝ] E 3) × (E 3 × E 3) :=
      fun g => (g.linearIsometryEquiv, (xOf g, g (xOf g)))
    have htargetFinite :
        (Sset ×ˢ ((A : Set (E 3)) ×ˢ (B : Set (E 3)))).Finite := by
      exact hSfinite.prod (A.finite_toSet.prod B.finite_toSet)
    have hencMaps : ∀ g ∈ U,
        enc g ∈ Sset ×ˢ ((A : Set (E 3)) ×ˢ (B : Set (E 3))) := by
      intro g hg
      have hx : xOf g ∈ matchPoints A B g := by
        simpa [xOf, hg] using Classical.choose_spec (hmatch g hg)
      have hx' : xOf g ∈ A ∧ g (xOf g) ∈ B := by simpa [matchPoints] using hx
      have hlin : g.linearIsometryEquiv ∈ Sset := ⟨g, hg.1, rfl⟩
      exact ⟨hlin, hx'.1, hx'.2⟩
    have hencInj : U.InjOn enc := by
      intro g hg h hh heq
      dsimp [enc] at heq
      have hparts := heq
      simp only [Prod.mk.injEq] at hparts
      rcases hparts with ⟨hlin, hxy⟩
      rcases hxy with ⟨hx, hy⟩
      have hgh : g = h := motion_eq_of_linear_apply hlin (by simpa [hx] using hy)
      exact hgh
    have hencImage : (enc '' U).Finite :=
      htargetFinite.subset (by
        rintro z ⟨g, hg, rfl⟩
        exact hencMaps g hg)
    have hUfinite : U.Finite := Set.Finite.of_finite_image hencImage hencInj
    refine ⟨hUfinite, ?_⟩
    intro G hG
    let T : Finset (Motion 3 × E 3) :=
      (G ×ˢ A).filter (fun gx => gx.2 ∈ matchPoints A B gx.1)
    let target : Finset ((E 3 ≃ₗᵢ[ℝ] E 3) × (E 3 × E 3)) :=
      SF ×ˢ (A ×ˢ B)
    let encT : Motion 3 × E 3 → (E 3 ≃ₗᵢ[ℝ] E 3) × (E 3 × E 3) :=
      fun gx => (gx.1.linearIsometryEquiv, (gx.2, gx.1 gx.2))
    have hTmap : (T : Set (Motion 3 × E 3)).MapsTo Prod.fst (G : Set (Motion 3)) := by
      intro gx hgx
      have hmem := (Finset.mem_filter.mp (Finset.mem_coe.mp hgx)).1
      exact (Finset.mem_product.mp hmem).1
    have hTsum : T.card = ∑ g ∈ G, (matchPoints A B g).card := by
      calc
        T.card = ∑ g ∈ G, (T.filter (fun gx => gx.1 = g)).card :=
          Finset.card_eq_sum_card_fiberwise hTmap
        _ = ∑ g ∈ G, (matchPoints A B g).card := by
          apply Finset.sum_congr rfl
          intro g hg
          symm
          apply Finset.card_bij (fun x _ => (g, x))
          · intro x hx
            have hx' : x ∈ A ∧ g x ∈ B := by simpa [matchPoints] using hx
            simp [T, hg, hx', hx]
          · intro x hx y hy heq
            exact congrArg Prod.snd heq
          · intro z hz
            rcases z with ⟨g', x⟩
            have hz' := Finset.mem_filter.mp hz
            have htz := Finset.mem_filter.mp hz'.1
            have heq : g' = g := hz'.2
            have hxy : x ∈ matchPoints A B g := by simpa [heq] using htz.2
            refine ⟨x, hxy, ?_⟩
            simp [heq]
    have hencTMaps : (T : Set (Motion 3 × E 3)).MapsTo encT (target : Set _) := by
      intro gx hgx
      have hmem := Finset.mem_filter.mp (Finset.mem_coe.mp hgx)
      have hprod := Finset.mem_product.mp hmem.1
      have hxmatch := hmem.2
      have hxA : gx.2 ∈ A := hprod.2
      have hxmatch' : gx.2 ∈ A ∧ gx.1 gx.2 ∈ B := by
        simpa [matchPoints] using hxmatch
      have hyB : gx.1 gx.2 ∈ B := hxmatch'.2
      have hlin : gx.1.linearIsometryEquiv ∈ SF := by
        have hset : gx.1.linearIsometryEquiv ∈ Sset := ⟨gx.1, hG gx.1 hprod.1, rfl⟩
        exact hSfinite.mem_toFinset.mpr hset
      change encT gx ∈ ↑(SF ×ˢ (A ×ˢ B))
      simp only [encT, Finset.mem_product]
      exact ⟨hlin, hxA, hyB⟩
    have hencTInj : (T : Set (Motion 3 × E 3)).InjOn encT := by
      intro a ha b hb heq
      obtain ⟨g, x⟩ := a
      obtain ⟨h, y⟩ := b
      change (g, x) ∈ T at ha
      change (h, y) ∈ T at hb
      dsimp [encT] at heq
      have hparts := heq
      simp only [Prod.mk.injEq] at hparts
      rcases hparts with ⟨hlin, hxy⟩
      rcases hxy with ⟨hxy, hval⟩
      have hgh : g = h := motion_eq_of_linear_apply hlin (by simpa [hxy] using hval)
      subst h
      subst y
      rfl
    have hcardT : T.card ≤ SF.card * A.card * B.card := by
      calc
        T.card ≤ target.card := Finset.card_le_card_of_injOn encT hencTMaps hencTInj
        _ = SF.card * A.card * B.card := by simp [target, Finset.card_product, Nat.mul_assoc]
    have hcardTR : (T.card : ℝ) ≤ (SF.card : ℝ) * (A.card : ℝ) * (B.card : ℝ) := by
      exact_mod_cast hcardT
    have hsumw : (∑ g ∈ G, (w₁ g : ℝ)) = (T.card : ℝ) := by
      have hsumN : (∑ g ∈ G, w₁ g) = T.card := by
        simpa [w₁, lineMatchWeight, matchCount, A, B] using hTsum.symm
      calc
        (∑ g ∈ G, (w₁ g : ℝ)) = ((∑ g ∈ G, w₁ g : ℕ) : ℝ) := by simp [Nat.cast_sum]
        _ = (T.card : ℝ) := by exact_mod_cast hsumN
    have hAreal : (A.card : ℝ) ≤ H := by simpa [A] using hX₁
    have hBreal : (B.card : ℝ) ≤ H := by simpa [B] using hY₁
    have hA0 : 0 ≤ (A.card : ℝ) := by positivity
    have hB0 : 0 ≤ (B.card : ℝ) := by positivity
    have hS0 : 0 ≤ (SF.card : ℝ) := by positivity
    have hpairBound : (SF.card : ℝ) * (A.card : ℝ) * (B.card : ℝ) ≤ 4 * H ^ 2 := by
      calc
        (SF.card : ℝ) * (A.card : ℝ) * (B.card : ℝ) =
            (SF.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) := by ring
        _ ≤ 4 * ((A.card : ℝ) * (B.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hSbound (mul_nonneg hA0 hB0)
        _ ≤ 4 * (H * H) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc
            (A.card : ℝ) * (B.card : ℝ) ≤ H * (B.card : ℝ) :=
              mul_le_mul_of_nonneg_right hAreal hB0
            _ ≤ H * H := mul_le_mul_of_nonneg_left hBreal hH
        _ = 4 * H ^ 2 := by ring
    have hsumwBound : (∑ g ∈ G, (w₁ g : ℝ)) ≤ 4 * H ^ 2 := by
      rw [hsumw]
      exact hcardTR.trans hpairBound
    have hprodSum :
        (∑ g ∈ G, (w₁ g : ℝ) * (w₂ g : ℝ)) ≤ H * (∑ g ∈ G, (w₁ g : ℝ)) := by
      calc
        (∑ g ∈ G, (w₁ g : ℝ) * (w₂ g : ℝ)) ≤
            ∑ g ∈ G, (w₁ g : ℝ) * H := by
          apply Finset.sum_le_sum
          intro g hg
          exact mul_le_mul_of_nonneg_left (hw₂ g).2 (hw₁ g).1
        _ = H * (∑ g ∈ G, (w₁ g : ℝ)) := by
          rw [← Finset.sum_mul]
          ring
    calc
      (∑ g ∈ G, (w₁ g : ℝ) * (w₂ g : ℝ)) ≤ H * (∑ g ∈ G, (w₁ g : ℝ)) := hprodSum
      _ ≤ H * (4 * H ^ 2) := mul_le_mul_of_nonneg_left hsumwBound hH
      _ = 4 * H ^ 3 := by ring
  · have hUeq : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hUne
    refine ⟨by simp [hUeq], ?_⟩
    intro G hG
    have hzero (g : Motion 3) (hg : g ∈ G) : (w₁ g : ℝ) * (w₂ g : ℝ) = 0 := by
      have hnot : ¬ 0 < (w₁ g : ℝ) * (w₂ g : ℝ) := by
        intro hp'
        have hpNatR : (0 : ℝ) < ((w₁ g * w₂ g : ℕ) : ℝ) := by
          simpa [Nat.cast_mul] using hp'
        have hpNat : 0 < w₁ g * w₂ g := Nat.cast_pos.mp hpNatR
        exact hUne ⟨g, hG g hg, hpNat⟩
      have hnonneg : 0 ≤ (w₁ g : ℝ) * (w₂ g : ℝ) :=
        mul_nonneg (by positivity) (by positivity)
      linarith
    calc
      (∑ g ∈ G, (w₁ g : ℝ) * (w₂ g : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro g hg
        exact hzero g hg
      _ ≤ 4 * H ^ 3 := by positivity


/-- Fixed-distance pairs in a plane from the two-common-neighbor property,
motions.tex:783–797. -/
theorem planar_fixed_distance_pairs : ∃ C : ℝ, 0 < C ∧
    ∀ (X : Finset (E 2)) (ρ : ℝ), 0 < ρ →
      ((X.offDiag.filter (fun xy => dist xy.1 xy.2 = ρ)).card : ℝ) ≤
        C * (X.card : ℝ) ^ ((3 : ℝ) / 2) := by
  refine ⟨2, by norm_num, ?_⟩
  intro X ρ hρ
  classical
  let V : Type := {x : E 2 // x ∈ X}
  letI : Fintype V := X.finite_toSet.fintype
  let G : SimpleGraph V := {
    Adj := fun a b => dist a.1 b.1 = ρ
    symm := ⟨fun a b hab => by simpa [dist_comm] using hab⟩
    loopless := ⟨fun a ha => by
      have hz : (0 : ℝ) = ρ := by simpa using ha
      exact (ne_of_gt hρ) hz.symm⟩
  }
  let E₀ : Finset (E 2 × E 2) :=
    X.offDiag.filter (fun xy => dist xy.1 xy.2 = ρ)
  have hcommon (a b : V) (hab : a ≠ b) :
      ((Finset.univ.filter (fun c : V => G.Adj c a ∧ G.Adj c b)).card) ≤ 2 := by
    by_contra hnot
    have hthree : 2 < (Finset.univ.filter (fun c : V => G.Adj c a ∧ G.Adj c b)).card :=
      Nat.lt_of_not_ge hnot
    obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ :=
      Finset.two_lt_card.mp hthree
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq hr
    have habval : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    have hpqval : p.1 ≠ q.1 := by
      intro h
      exact hpq (Subtype.ext h)
    have hp1a : dist p.1 a.1 = ρ := by simpa [G] using hp.1
    have hq1a : dist q.1 a.1 = ρ := by simpa [G] using hq.1
    have hr1a : dist r.1 a.1 = ρ := by simpa [G] using hr.1
    have hp1b : dist p.1 b.1 = ρ := by simpa [G] using hp.2
    have hq1b : dist q.1 b.1 = ρ := by simpa [G] using hq.2
    have hr1b : dist r.1 b.1 = ρ := by simpa [G] using hr.2
    have hgeom := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (V := E 2) (P := E 2) (by simp [E]) habval hpqval
      hp1a hq1a hr1a hp1b hq1b hr1b
    rcases hgeom with h | h
    · exact hpr (Subtype.ext h.symm)
    · exact hqr (Subtype.ext h.symm)
  let W : Type := Σ c : V, ↥((G.neighborFinset c).offDiag)
  let pairOf : W → V × V := fun w => w.2.1
  have hWcard : Fintype.card W = ∑ c : V, (G.neighborFinset c).offDiag.card := by
    change Fintype.card (Σ c : V, ↥((G.neighborFinset c).offDiag)) = _
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro c hc
    exact Fintype.card_coe _
  have hWdegree : Fintype.card W = ∑ c : V, ((G.degree c) ^ 2 - G.degree c) := by
    calc
      Fintype.card W = ∑ c : V, Fintype.card ↥((G.neighborFinset c).offDiag) := by
        change Fintype.card (Σ c : V, ↥((G.neighborFinset c).offDiag)) = _
        rw [Fintype.card_sigma]
      _ = ∑ c : V, (G.neighborFinset c).offDiag.card := by
        apply Finset.sum_congr rfl
        intro c hc
        exact Fintype.card_coe _
      _ = ∑ c : V, ((G.degree c) ^ 2 - G.degree c) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.offDiag_card, G.card_neighborFinset_eq_degree]
        simp [pow_two]
  have hWfib : Fintype.card W =
      ∑ p ∈ (Finset.univ : Finset (V × V)),
        ((Finset.univ : Finset W).filter (fun w => pairOf w = p)).card := by
    have hmap : ((Finset.univ : Finset W) : Set W).MapsTo pairOf
        (Finset.univ : Finset (V × V)) := by
      intro w hw
      simp
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise hmap
  have hWfiber_le (p : V × V) :
      ((Finset.univ : Finset W).filter (fun w => pairOf w = p)).card ≤ 2 := by
    let Fp : Finset W := (Finset.univ : Finset W).filter (fun w => pairOf w = p)
    by_cases hp : p.1 = p.2
    · have hFp : Fp = ∅ := by
        ext w
        simp only [Fp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
        constructor
        · intro hpair
          have hne := (Finset.mem_offDiag.mp w.2.property).2.2
          have hfirst : w.2.1.1 = p.1 := congrArg Prod.fst hpair
          have hsecond : w.2.1.2 = p.2 := congrArg Prod.snd hpair
          exact hne (hfirst.trans (hp.trans hsecond.symm))
        · intro hfalse
          exact hfalse.elim
      simp [Fp, hFp]
    · let C : Finset V := (Finset.univ : Finset V).filter
        (fun c => G.Adj c p.1 ∧ G.Adj c p.2)
      have hmap : (Fp : Set W).MapsTo (fun w : W => w.1) (C : Set V) := by
        intro w hw
        have hpair : pairOf w = p := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
        have hmem := Finset.mem_offDiag.mp w.2.property
        have hfirst : w.2.1.1 = p.1 := congrArg Prod.fst hpair
        have hsecond : w.2.1.2 = p.2 := congrArg Prod.snd hpair
        have hadj₁ : G.Adj w.1 w.2.1.1 := by simpa using hmem.1
        have hadj₂ : G.Adj w.1 w.2.1.2 := by simpa using hmem.2.1
        change w.1 ∈ C
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by simpa [hfirst] using hadj₁, by simpa [hsecond] using hadj₂⟩
      have hinj : (Fp : Set W).InjOn (fun w : W => w.1) := by
        intro w hw z hz hcenter
        have hwpair : pairOf w = p := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
        have hzpair : pairOf z = p := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
        rcases w with ⟨c, x⟩
        rcases z with ⟨d, y⟩
        dsimp at hcenter
        subst d
        have hxy : x.1 = y.1 := by
          apply Prod.ext
          · exact (congrArg Prod.fst hwpair).trans (congrArg Prod.fst hzpair).symm
          · exact (congrArg Prod.snd hwpair).trans (congrArg Prod.snd hzpair).symm
        have hsub : x = y := Subtype.ext hxy
        exact congrArg (fun t => (⟨c, t⟩ : W)) hsub
      have hFcard : Fp.card ≤ C.card := Finset.card_le_card_of_injOn _ hmap hinj
      have hCcard : C.card ≤ 2 := hcommon p.1 p.2 hp
      exact hFcard.trans hCcard
  have hWboundNat : Fintype.card W ≤ 2 * (Fintype.card V) ^ 2 := by
    rw [hWfib]
    calc
      (∑ p ∈ (Finset.univ : Finset (V × V)),
          ((Finset.univ : Finset W).filter (fun w => pairOf w = p)).card) ≤
        ∑ p ∈ (Finset.univ : Finset (V × V)), 2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact hWfiber_le p
      _ = 2 * (Fintype.card V) ^ 2 := by simp [Fintype.card_prod, pow_two]; ring
  have hMomentNat :
      (∑ c : V, (G.degree c) ^ 2) =
        (∑ c : V, G.degree c) + Fintype.card W := by
    calc
      (∑ c : V, (G.degree c) ^ 2) =
          ∑ c : V, (((G.degree c) ^ 2 - G.degree c) + G.degree c) := by
            apply Finset.sum_congr rfl
            intro c hc
            have hd : G.degree c ≤ (G.degree c) ^ 2 := by
              by_cases hzero : G.degree c = 0
              · simp [hzero]
              · have hpos : 1 ≤ G.degree c := Nat.one_le_iff_ne_zero.mpr hzero
                have hm := Nat.mul_le_mul_left (G.degree c) hpos
                simpa [pow_two] using hm
            exact (Nat.sub_add_cancel hd).symm
      _ = (∑ c : V, ((G.degree c) ^ 2 - G.degree c)) + ∑ c : V, G.degree c := by
            rw [Finset.sum_add_distrib]
      _ = Fintype.card W + ∑ c : V, G.degree c := by rw [← hWdegree]
      _ = (∑ c : V, G.degree c) + Fintype.card W := by omega
  have hDartSum : (∑ c : V, G.degree c) = Fintype.card G.Dart :=
    G.dart_card_eq_sum_degrees.symm
  have hEcard : E₀.card = Fintype.card G.Dart := by
    let encode (xy : E 2 × E 2) (hxy : xy ∈ E₀) : G.Dart := by
      have hm := Finset.mem_filter.mp hxy
      have ho := Finset.mem_offDiag.mp hm.1
      refine ⟨(⟨xy.1, ho.1⟩, ⟨xy.2, ho.2.1⟩), ?_⟩
      simpa [G] using hm.2
    apply Finset.card_bij encode
    · intro xy hxy
      exact Finset.mem_univ _
    · intro xy hxy yz hyz heq
      apply Prod.ext
      · exact congrArg (fun d : G.Dart => d.fst.1) heq
      · exact congrArg (fun d : G.Dart => d.snd.1) heq
    · intro d hd
      let xy : E 2 × E 2 := (d.fst.1, d.snd.1)
      have hxy : xy ∈ E₀ := by
        have hne : d.fst.1 ≠ d.snd.1 := by
          intro h
          exact d.fst_ne_snd (Subtype.ext h)
        have hOff : xy ∈ X.offDiag := by
          rw [Finset.mem_offDiag]
          exact ⟨d.fst.2, d.snd.2, hne⟩
        change xy ∈ X.offDiag.filter (fun uv => dist uv.1 uv.2 = ρ)
        have hdist : dist xy.1 xy.2 = ρ := by
          change dist d.fst.1 d.snd.1 = ρ
          exact d.adj
        exact Finset.mem_filter.mpr ⟨hOff, hdist⟩
      refine ⟨xy, hxy, ?_⟩
      apply SimpleGraph.Dart.ext
      rfl
  have hn : Fintype.card V = X.card := by
    simp [V, ← Set.ncard_eq_toFinset_card (X : Set (E 2)) X.finite_toSet]
  have hMboundNat : Fintype.card G.Dart ≤ (Fintype.card V) ^ 2 := by
    rw [← hEcard]
    calc
      E₀.card ≤ X.offDiag.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = X.card * X.card - X.card := Finset.offDiag_card X
      _ ≤ X.card ^ 2 := by rw [pow_two]; exact Nat.sub_le _ _
      _ ≤ (Fintype.card V) ^ 2 := by rw [← hn]
  let nR : ℝ := Fintype.card V
  let mR : ℝ := Fintype.card G.Dart
  have hnR : 0 ≤ nR := by positivity
  have hmR : 0 ≤ mR := by positivity
  have hDartSumR : (∑ c : V, (G.degree c : ℝ)) = mR := by
    dsimp [mR]
    calc
      (∑ c : V, (G.degree c : ℝ)) = ((∑ c : V, G.degree c : ℕ) : ℝ) := by simp
      _ = (Fintype.card G.Dart : ℝ) := by exact_mod_cast hDartSum
  have hWboundR : (Fintype.card W : ℝ) ≤ 2 * nR ^ 2 := by
    dsimp [nR]
    exact_mod_cast hWboundNat
  have hMomentR :
      (∑ c : V, (G.degree c : ℝ) ^ 2) = mR + (Fintype.card W : ℝ) := by
    dsimp [mR]
    have hcast := congrArg (fun k : ℕ => (k : ℝ)) hMomentNat
    simpa [Nat.cast_sum, Nat.cast_pow, hDartSum] using hcast
  have hsecond : (∑ c : V, (G.degree c : ℝ) ^ 2) ≤ mR + 2 * nR ^ 2 := by
    rw [hMomentR]
    linarith [hWboundR]
  have hCS : mR ^ 2 ≤ nR * (∑ c : V, (G.degree c : ℝ) ^ 2) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V)
      (fun _ : V => (1 : ℝ)) (fun c => (G.degree c : ℝ))
    calc
      mR ^ 2 = (∑ c : V, (1 : ℝ) * (G.degree c : ℝ)) ^ 2 := by
        simp [hDartSumR, mR]
      _ ≤ (∑ c ∈ (Finset.univ : Finset V), (1 : ℝ) ^ 2) *
          ∑ c ∈ (Finset.univ : Finset V), (G.degree c : ℝ) ^ 2 := hcs
      _ = nR * (∑ c : V, (G.degree c : ℝ) ^ 2) := by simp [nR]
  have hMboundR : mR ≤ nR ^ 2 := by
    dsimp [mR, nR] at hMboundNat ⊢
    exact_mod_cast hMboundNat
  have hnm : nR * mR ≤ nR ^ 3 := by
    calc
      nR * mR ≤ nR * nR ^ 2 := mul_le_mul_of_nonneg_left hMboundR hnR
      _ = nR ^ 3 := by ring
  have hmsq : mR ^ 2 ≤ 3 * nR ^ 3 := by
    have hCS' : mR ^ 2 ≤ nR * (mR + 2 * nR ^ 2) :=
      hCS.trans (mul_le_mul_of_nonneg_left hsecond hnR)
    nlinarith [hCS', hnm]
  have hpow : (nR ^ ((3 : ℝ) / 2)) ^ 2 = nR ^ 3 := by
    calc
      (nR ^ ((3 : ℝ) / 2)) ^ 2 = (Real.sqrt nR ^ (3 : ℝ)) ^ 2 := by
        rw [Real.rpow_div_two_eq_sqrt 3 hnR]
      _ = (Real.sqrt nR ^ 3) ^ 2 := by
        congr 1
        exact Real.rpow_natCast (Real.sqrt nR) 3
      _ = (Real.sqrt nR) ^ (3 * 2) := (pow_mul (Real.sqrt nR) 3 2).symm
      _ = (Real.sqrt nR) ^ 6 := by norm_num
      _ = (Real.sqrt nR) ^ (2 * 3) := by norm_num
      _ = ((Real.sqrt nR) ^ 2) ^ 3 := pow_mul (Real.sqrt nR) 2 3
      _ = nR ^ 3 := by rw [Real.sq_sqrt hnR]
  have htarget : mR ≤ 2 * nR ^ ((3 : ℝ) / 2) := by
    apply (sq_le_sq₀ hmR (mul_nonneg (by norm_num) (Real.rpow_nonneg hnR _))).mp
    calc
      mR ^ 2 ≤ 3 * nR ^ 3 := hmsq
      _ ≤ 4 * nR ^ 3 := by nlinarith [pow_nonneg hnR 3]
      _ = 2 ^ 2 * nR ^ 3 := by norm_num
      _ = 2 ^ 2 * (nR ^ ((3 : ℝ) / 2)) ^ 2 := by rw [hpow]
      _ = (2 * nR ^ ((3 : ℝ) / 2)) ^ 2 := by rw [mul_pow]
  have hEfinal : (E₀.card : ℝ) ≤ 2 * (X.card : ℝ) ^ ((3 : ℝ) / 2) := by
    calc
      (E₀.card : ℝ) = (Fintype.card G.Dart : ℝ) := by exact_mod_cast hEcard
      _ ≤ 2 * (X.card : ℝ) ^ ((3 : ℝ) / 2) := by simpa [mR, nR, hn] using htarget
  simpa [E₀] using hEfinal

private noncomputable def lineCanonicalPoint (L : Line 3) : E 3 := by
  let p : E 3 := Classical.choose L.2.1
  have hp : p ∈ L.1 := Classical.choose_spec L.2.1
  letI : Nonempty ↥L.1 := ⟨⟨p, hp⟩⟩
  exact (EuclideanGeometry.orthogonalProjection (s := L.1) (0 : E 3) : E 3)

private lemma lineCanonicalPoint_mem (L : Line 3) : lineCanonicalPoint L ∈ L.1 := by
  classical
  let p : E 3 := Classical.choose L.2.1
  have hp : p ∈ L.1 := Classical.choose_spec L.2.1
  letI : Nonempty ↥L.1 := ⟨⟨p, hp⟩⟩
  simpa [lineCanonicalPoint] using
    (EuclideanGeometry.orthogonalProjection_mem (s := L.1) (0 : E 3))

private lemma lineCanonicalPoint_orthogonal (L : Line 3) :
    lineCanonicalPoint L ∈ L.1.directionᗮ := by
  classical
  let p : E 3 := Classical.choose L.2.1
  have hp : p ∈ L.1 := Classical.choose_spec L.2.1
  letI : Nonempty ↥L.1 := ⟨⟨p, hp⟩⟩
  have h := EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
    (s := L.1) (0 : E 3)
  simpa [lineCanonicalPoint, vsub_eq_sub] using L.1.directionᗮ.neg_mem h

private lemma line_perp_finrank (D : Submodule ℝ (E 3))
    (hD : Module.finrank ℝ D = 1) : Module.finrank ℝ Dᗮ = 2 := by
  have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) D
  have hE : Module.finrank ℝ (E 3) = 3 := by simp [E]
  rw [hD, hE] at hsum
  omega

private noncomputable def line_perp_basis (D : Submodule ℝ (E 3))
    (hD : Module.finrank ℝ D = 1) : OrthonormalBasis (Fin 2) ℝ ↥(Dᗮ) :=
  (stdOrthonormalBasis ℝ ↥(Dᗮ)).reindex (finCongr (line_perp_finrank D hD))

private noncomputable def line_perp_coord (D : Submodule ℝ (E 3))
    (hD : Module.finrank ℝ D = 1) (x : E 3) : E 2 :=
  (line_perp_basis D hD).repr (Dᗮ.orthogonalProjectionOnto x)

private noncomputable def line_class_coord (D : Submodule ℝ (E 3))
    (hD : Module.finrank ℝ D = 1) (L : Line 3) : E 2 :=
  line_perp_coord D hD (lineCanonicalPoint L)

private lemma line_class_coord_eq_repr (D : Submodule ℝ (E 3))
    (hD : Module.finrank ℝ D = 1) (L : Line 3)
    (hdir : L.1.direction = D) :
    line_class_coord D hD L = (line_perp_basis D hD).repr
      ⟨lineCanonicalPoint L, by rw [← hdir]; exact lineCanonicalPoint_orthogonal L⟩ := by
  have hmem : lineCanonicalPoint L ∈ Dᗮ := by
    rw [← hdir]
    exact lineCanonicalPoint_orthogonal L
  change (line_perp_basis D hD).repr
      (Dᗮ.orthogonalProjectionOnto
        ((⟨lineCanonicalPoint L, hmem⟩ : ↥Dᗮ) : E 3)) = _
  rw [Dᗮ.orthogonalProjectionOnto_mem_subspace_eq_self]

private lemma line_class_coord_injective (D : Submodule ℝ (E 3))
    (hD : Module.finrank ℝ D = 1) {L₁ L₂ : Line 3}
    (hdir₁ : L₁.1.direction = D) (hdir₂ : L₂.1.direction = D)
    (hcoord : line_class_coord D hD L₁ = line_class_coord D hD L₂) : L₁ = L₂ := by
  rw [line_class_coord_eq_repr D hD L₁ hdir₁,
    line_class_coord_eq_repr D hD L₂ hdir₂] at hcoord
  have hpoint :
      (⟨lineCanonicalPoint L₁, by rw [← hdir₁]; exact lineCanonicalPoint_orthogonal L₁⟩ : ↥Dᗮ) =
      ⟨lineCanonicalPoint L₂, by rw [← hdir₂]; exact lineCanonicalPoint_orthogonal L₂⟩ :=
    (line_perp_basis D hD).repr.injective hcoord
  have hcanonical : lineCanonicalPoint L₁ = lineCanonicalPoint L₂ :=
    congrArg Subtype.val hpoint
  apply Subtype.ext
  apply AffineSubspace.ext_of_direction_eq (by rw [hdir₁, hdir₂])
  exact ⟨lineCanonicalPoint L₁, lineCanonicalPoint_mem L₁,
    hcanonical ▸ lineCanonicalPoint_mem L₂⟩

private lemma line_class_coord_dist (D : Submodule ℝ (E 3))
    (hD : Module.finrank ℝ D = 1) (L₁ L₂ : Line 3)
    (hdir₁ : L₁.1.direction = D) (hdir₂ : L₂.1.direction = D) :
    dist (line_class_coord D hD L₁) (line_class_coord D hD L₂) =
      dist (lineCanonicalPoint L₁) (lineCanonicalPoint L₂) := by
  rw [line_class_coord_eq_repr D hD L₁ hdir₁,
    line_class_coord_eq_repr D hD L₂ hdir₂]
  convert (line_perp_basis D hD).repr.isometry.dist_eq
    (⟨lineCanonicalPoint L₁, by rw [← hdir₁]; exact lineCanonicalPoint_orthogonal L₁⟩ : ↥Dᗮ)
    ⟨lineCanonicalPoint L₂, by rw [← hdir₂]; exact lineCanonicalPoint_orthogonal L₂⟩ using 1 <;> simp

private lemma lineSeparation_eq_canonical_dist (L₁ L₂ : Line 3)
    (hdir : L₁.1.direction = L₂.1.direction) (hL : L₁ ≠ L₂) :
    lineSeparation L₁ L₂ = dist (lineCanonicalPoint L₁) (lineCanonicalPoint L₂) := by
  let D : Submodule ℝ (E 3) := L₁.1.direction
  obtain ⟨p, hp, q, hq, hsep, _, hperp⟩ :=
    parallel_sep_projection L₁ L₂ (by simpa [parallel] using hdir) hL
  have hpdir : p -ᵥ lineCanonicalPoint L₁ ∈ D := by
    simpa [D] using AffineSubspace.vsub_mem_direction hp (lineCanonicalPoint_mem L₁)
  have hqdir : q -ᵥ lineCanonicalPoint L₂ ∈ D := by
    have hqdir' := AffineSubspace.vsub_mem_direction hq (lineCanonicalPoint_mem L₂)
    simpa [D, hdir] using hqdir'
  have hpcan : lineCanonicalPoint L₁ -ᵥ p ∈ D := by
    simpa [vsub_eq_sub] using D.neg_mem hpdir
  have hcan₁ : lineCanonicalPoint L₁ ∈ Dᗮ := by
    simpa [D] using lineCanonicalPoint_orthogonal L₁
  have hcan₂ : lineCanonicalPoint L₂ ∈ Dᗮ := by
    simpa [D, hdir] using lineCanonicalPoint_orthogonal L₂
  have hcanperp : lineCanonicalPoint L₂ -ᵥ lineCanonicalPoint L₁ ∈ Dᗮ := by
    simpa [vsub_eq_sub] using Dᗮ.sub_mem hcan₂ hcan₁
  have hdiff : (q -ᵥ p) - (lineCanonicalPoint L₂ -ᵥ lineCanonicalPoint L₁) =
      (q -ᵥ lineCanonicalPoint L₂) + (lineCanonicalPoint L₁ -ᵥ p) := by
    simp only [vsub_eq_sub]
    abel
  have hdiffD : (q -ᵥ p) - (lineCanonicalPoint L₂ -ᵥ lineCanonicalPoint L₁) ∈ D := by
    rw [hdiff]
    exact D.add_mem hqdir hpcan
  have hdiffPerp :
      (q -ᵥ p) - (lineCanonicalPoint L₂ -ᵥ lineCanonicalPoint L₁) ∈ Dᗮ :=
    Dᗮ.sub_mem hperp hcanperp
  have hbot : D ⊓ Dᗮ = ⊥ := (Submodule.orthogonal_disjoint D).eq_bot
  have hzero : (q -ᵥ p) - (lineCanonicalPoint L₂ -ᵥ lineCanonicalPoint L₁) = 0 := by
    have hmem :
        (q -ᵥ p) - (lineCanonicalPoint L₂ -ᵥ lineCanonicalPoint L₁) ∈ D ⊓ Dᗮ :=
      ⟨hdiffD, hdiffPerp⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have hvec : q -ᵥ p = lineCanonicalPoint L₂ -ᵥ lineCanonicalPoint L₁ :=
    sub_eq_zero.mp hzero
  have hvec' : p -ᵥ q = lineCanonicalPoint L₁ -ᵥ lineCanonicalPoint L₂ := by
    have h := congrArg (fun x : E 3 => -x) hvec
    simpa [vsub_eq_sub] using h
  rw [hsep, dist_eq_norm_vsub, dist_eq_norm_vsub]
  exact congrArg norm hvec'

private theorem line_class_fixed_separation_bound (C₂ : ℝ)
    (hplanar : ∀ (X : Finset (E 2)) (ρ : ℝ), 0 < ρ →
      ((X.offDiag.filter (fun xy => dist xy.1 xy.2 = ρ)).card : ℝ) ≤
        C₂ * (X.card : ℝ) ^ ((3 : ℝ) / 2))
    (D : Submodule ℝ (E 3)) (hD : Module.finrank ℝ D = 1)
    (A : Finset (Line 3)) (hclass : ∀ L ∈ A, L.1.direction = D)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (((A.offDiag.filter (fun ll => lineSeparation ll.1 ll.2 = ρ)).card : ℝ)) ≤
      C₂ * (A.card : ℝ) ^ ((3 : ℝ) / 2) := by
  classical
  let P : Finset (E 2) := A.image (line_class_coord D hD)
  let F : Finset (E 2 × E 2) := P.offDiag.filter (fun xy => dist xy.1 xy.2 = ρ)
  let T : Finset (Line 3 × Line 3) :=
    A.offDiag.filter (fun ll => lineSeparation ll.1 ll.2 = ρ)
  have hinfo (ll : Line 3 × Line 3) (hll : ll ∈ T) :
      ll.1 ∈ A ∧ ll.2 ∈ A ∧ ll.1 ≠ ll.2 ∧ lineSeparation ll.1 ll.2 = ρ := by
    have ht := Finset.mem_filter.mp hll
    have ho := Finset.mem_offDiag.mp ht.1
    exact ⟨ho.1, ho.2.1, ho.2.2, ht.2⟩
  have hcoord_inj : Set.InjOn (line_class_coord D hD) A := by
    intro L₁ hL₁ L₂ hL₂ hcoord
    exact line_class_coord_injective D hD (hclass L₁ hL₁) (hclass L₂ hL₂) hcoord
  have hPcard : P.card = A.card := by
    exact Finset.card_image_of_injOn hcoord_inj
  have hmap : (T : Set (Line 3 × Line 3)).MapsTo
      (fun ll => (line_class_coord D hD ll.1, line_class_coord D hD ll.2)) (F : Set (E 2 × E 2)) := by
    intro ll hll
    rcases hinfo ll (Finset.mem_coe.mp hll) with ⟨hL₁, hL₂, hne, hsep⟩
    have hcan := lineSeparation_eq_canonical_dist ll.1 ll.2
      ((hclass ll.1 hL₁).trans (hclass ll.2 hL₂).symm) hne
    have hdist :
        dist (line_class_coord D hD ll.1) (line_class_coord D hD ll.2) = ρ := by
      calc
        _ = dist (lineCanonicalPoint ll.1) (lineCanonicalPoint ll.2) :=
          line_class_coord_dist D hD ll.1 ll.2 (hclass ll.1 hL₁) (hclass ll.2 hL₂)
        _ = lineSeparation ll.1 ll.2 := hcan.symm
        _ = ρ := hsep
    change (line_class_coord D hD ll.1, line_class_coord D hD ll.2) ∈ F
    simp only [F, Finset.mem_filter, Finset.mem_offDiag]
    refine ⟨⟨Finset.mem_image_of_mem _ hL₁, Finset.mem_image_of_mem _ hL₂, ?_⟩, hdist⟩
    intro heq
    exact hne (line_class_coord_injective D hD (hclass ll.1 hL₁) (hclass ll.2 hL₂) heq)
  have hinj : (T : Set (Line 3 × Line 3)).InjOn
      (fun ll => (line_class_coord D hD ll.1, line_class_coord D hD ll.2)) := by
    intro ll hll ll' hll' heq
    rcases hinfo ll (Finset.mem_coe.mp hll) with ⟨hL₁, hL₂, _, _⟩
    rcases hinfo ll' (Finset.mem_coe.mp hll') with ⟨hL₁', hL₂', _, _⟩
    apply Prod.ext
    · exact line_class_coord_injective D hD (hclass ll.1 hL₁) (hclass ll'.1 hL₁')
        (congrArg Prod.fst heq)
    · exact line_class_coord_injective D hD (hclass ll.2 hL₂) (hclass ll'.2 hL₂')
        (congrArg Prod.snd heq)
  have hcard : T.card ≤ F.card := Finset.card_le_card_of_injOn _ hmap hinj
  calc
    (T.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hcard
    _ ≤ C₂ * (P.card : ℝ) ^ ((3 : ℝ) / 2) := hplanar P ρ hρ
    _ = C₂ * (A.card : ℝ) ^ ((3 : ℝ) / 2) := by rw [hPcard]

/-- mot:parallel-pairs, motions.tex:773–799. -/
theorem mot_parallel_pairs : ∃ C : ℝ, 0 < C ∧
    ∀ (L : Finset (Line 3)) (ρ : ℝ), 0 < ρ →
      ((L.offDiag.filter (fun ll' => parallel ll'.1 ll'.2 ∧
        lineSeparation ll'.1 ll'.2 = ρ)).card : ℝ) ≤ C * (L.card : ℝ) ^ ((3 : ℝ) / 2) := by
  obtain ⟨C₂, hC₂, hplanar⟩ := planar_fixed_distance_pairs
  refine ⟨C₂, hC₂, ?_⟩
  intro L ρ hρ
  classical
  let dirs : Finset (Submodule ℝ (E 3)) := L.image (fun l => l.1.direction)
  let A : Submodule ℝ (E 3) → Finset (Line 3) :=
    fun D => L.filter (fun l => l.1.direction = D)
  let Eρ : Finset (Line 3 × Line 3) :=
    L.offDiag.filter (fun ll => parallel ll.1 ll.2 ∧ lineSeparation ll.1 ll.2 = ρ)
  have hmapDirs : (Eρ : Set (Line 3 × Line 3)).MapsTo
      (fun ll => ll.1.1.direction) (dirs : Set (Submodule ℝ (E 3))) := by
    intro ll hll
    have he := Finset.mem_filter.mp (Finset.mem_coe.mp hll)
    have ho := Finset.mem_offDiag.mp he.1
    exact Finset.mem_image_of_mem _ ho.1
  have hsub (D : Submodule ℝ (E 3)) (hD : D ∈ dirs) :
      Eρ.filter (fun ll => ll.1.1.direction = D) ⊆
        (A D).offDiag.filter (fun ll => lineSeparation ll.1 ll.2 = ρ) := by
    intro ll hll
    have hfiber := Finset.mem_filter.mp hll
    have he := Finset.mem_filter.mp hfiber.1
    have ho := Finset.mem_offDiag.mp he.1
    have hcond := he.2
    have hdir₁ := hfiber.2
    have hdir₂ : ll.2.1.direction = D := by
      have hp : ll.1.1.direction = ll.2.1.direction := by
        simpa [parallel] using hcond.1
      exact hp.symm.trans hdir₁
    have hA₁ : ll.1 ∈ A D := by
      change ll.1 ∈ L.filter (fun l => l.1.direction = D)
      exact Finset.mem_filter.mpr ⟨ho.1, hdir₁⟩
    have hA₂ : ll.2 ∈ A D := by
      change ll.2 ∈ L.filter (fun l => l.1.direction = D)
      exact Finset.mem_filter.mpr ⟨ho.2.1, hdir₂⟩
    have hOff : ll ∈ (A D).offDiag := by
      rw [Finset.mem_offDiag]
      exact ⟨hA₁, hA₂, ho.2.2⟩
    exact Finset.mem_filter.mpr ⟨hOff, hcond.2⟩
  have hclass (D : Submodule ℝ (E 3)) (l : Line 3) (hl : l ∈ A D) :
      l.1.direction = D := by
    change l ∈ L.filter (fun x => x.1.direction = D) at hl
    exact (Finset.mem_filter.mp hl).2
  have hdim (D : Submodule ℝ (E 3)) (hD : D ∈ dirs) :
      Module.finrank ℝ D = 1 := by
    rcases Finset.mem_image.mp hD with ⟨l, hl, rfl⟩
    exact l.2.2
  have hclassBound (D : Submodule ℝ (E 3)) (hD : D ∈ dirs) :
      (((A D).offDiag.filter (fun ll => lineSeparation ll.1 ll.2 = ρ)).card : ℝ) ≤
        C₂ * ((A D).card : ℝ) ^ ((3 : ℝ) / 2) := by
    exact line_class_fixed_separation_bound C₂ hplanar D (hdim D hD) (A D)
      (hclass D) ρ hρ
  have hcardFibers : Eρ.card =
      ∑ D ∈ dirs, (Eρ.filter (fun ll => ll.1.1.direction = D)).card :=
    Finset.card_eq_sum_card_fiberwise hmapDirs
  have hcardClasses : Eρ.card ≤
      ∑ D ∈ dirs, ((A D).offDiag.filter (fun ll => lineSeparation ll.1 ll.2 = ρ)).card := by
    rw [hcardFibers]
    apply Finset.sum_le_sum
    intro D hD
    exact Finset.card_le_card (hsub D hD)
  have hmapLines : (L : Set (Line 3)).MapsTo
      (fun l => l.1.direction) (dirs : Set (Submodule ℝ (E 3))) := by
    intro l hl
    exact Finset.mem_image_of_mem _ hl
  have hcardLines : L.card = ∑ D ∈ dirs, (A D).card := by
    simpa [A] using (Finset.card_eq_sum_card_fiberwise hmapLines)
  have hsumClass : (∑ D ∈ dirs, (A D).card : ℝ) = (L.card : ℝ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hcardLines
    simpa [Nat.cast_sum] using hcast.symm
  have hpow (x : ℝ) (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
    calc
      x ^ ((3 : ℝ) / 2) = Real.sqrt x ^ (3 : ℝ) := Real.rpow_div_two_eq_sqrt 3 hx
      _ = Real.sqrt x ^ 3 := Real.rpow_natCast (Real.sqrt x) 3
      _ = x * Real.sqrt x := by
        calc
          Real.sqrt x ^ 3 = (Real.sqrt x ^ 2) * Real.sqrt x := by ring
          _ = x * Real.sqrt x := by rw [Real.sq_sqrt hx]
  have hsumPow :
      (∑ D ∈ dirs, ((A D).card : ℝ) ^ ((3 : ℝ) / 2)) ≤
        (L.card : ℝ) ^ ((3 : ℝ) / 2) := by
    have hn : 0 ≤ (L.card : ℝ) := by positivity
    have hqle (D : Submodule ℝ (E 3)) (hD : D ∈ dirs) :
        ((A D).card : ℝ) ≤ (L.card : ℝ) := by
      have hnat : (A D).card ≤ L.card := Finset.card_le_card (Finset.filter_subset _ _)
      exact_mod_cast hnat
    calc
      (∑ D ∈ dirs, ((A D).card : ℝ) ^ ((3 : ℝ) / 2)) ≤
          ∑ D ∈ dirs, ((A D).card : ℝ) * Real.sqrt (L.card : ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        have hq : 0 ≤ ((A D).card : ℝ) := by positivity
        calc
          ((A D).card : ℝ) ^ ((3 : ℝ) / 2) =
              ((A D).card : ℝ) * Real.sqrt ((A D).card : ℝ) := hpow _ (by positivity)
          _ ≤ ((A D).card : ℝ) * Real.sqrt (L.card : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hqle D hD)) hq
      _ = (∑ D ∈ dirs, ((A D).card : ℝ)) * Real.sqrt (L.card : ℝ) := by
        rw [← Finset.sum_mul]
      _ = (L.card : ℝ) * Real.sqrt (L.card : ℝ) := by
        rw [hsumClass]
      _ = (L.card : ℝ) ^ ((3 : ℝ) / 2) := (hpow _ hn).symm
  have hcardReal : (Eρ.card : ℝ) ≤
      ∑ D ∈ dirs, (((A D).offDiag.filter
        (fun ll => lineSeparation ll.1 ll.2 = ρ)).card : ℝ) := by
    exact_mod_cast hcardClasses
  have hclassSum :
      (∑ D ∈ dirs, (((A D).offDiag.filter
        (fun ll => lineSeparation ll.1 ll.2 = ρ)).card : ℝ)) ≤
      ∑ D ∈ dirs, C₂ * ((A D).card : ℝ) ^ ((3 : ℝ) / 2) := by
    apply Finset.sum_le_sum
    intro D hD
    exact hclassBound D hD
  calc
    (Eρ.card : ℝ) ≤
        ∑ D ∈ dirs, (((A D).offDiag.filter
          (fun ll => lineSeparation ll.1 ll.2 = ρ)).card : ℝ) := hcardReal
    _ ≤ ∑ D ∈ dirs, C₂ * (A D).card ^ ((3 : ℝ) / 2) := hclassSum
    _ = C₂ * (∑ D ∈ dirs, ((A D).card : ℝ) ^ ((3 : ℝ) / 2)) := by
      rw [← Finset.mul_sum]
    _ ≤ C₂ * (L.card : ℝ) ^ ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hsumPow (le_of_lt hC₂)

/-- mot:distinct-line-pair-mass, motions.tex:955–965. -/
theorem distinct_line_pair_mass {α : Type*} (I : Finset α) (w : α → ℝ) (H : ℝ)
    (hH : 0 ≤ H) (hw : ∀ i ∈ I, 0 ≤ w i ∧ w i ≤ H)
    (hW : 2 * H ≤ ∑ i ∈ I, w i) :
    (∑ i ∈ I, w i) ^ 2 / 2 ≤ ∑ ij ∈ I.offDiag, w ij.1 * w ij.2 := by
  classical
  let W : ℝ := ∑ i ∈ I, w i
  let f : α × α → ℝ := fun ij => w ij.1 * w ij.2
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    linarith
  have hprod : (∑ ij ∈ I ×ˢ I, f ij) = W ^ 2 := by
    rw [Finset.sum_product]
    change (∑ i ∈ I, ∑ j ∈ I, w i * w j) = W ^ 2
    rw [← Finset.sum_mul_sum]
    simp [W, pow_two]
  have hsplit : (∑ ij ∈ I.offDiag, f ij) + ∑ ij ∈ I.diag, f ij = W ^ 2 := by
    have hsum := Finset.sum_filter_add_sum_filter_not (I ×ˢ I)
      (fun ij : α × α => ij.1 ≠ ij.2) f
    have hoff : I.offDiag = (I ×ˢ I).filter (fun ij : α × α => ij.1 ≠ ij.2) := by
      ext ⟨a, b⟩
      simp [Finset.mem_offDiag, and_assoc]
    have hdiag : I.diag = (I ×ˢ I).filter (fun ij : α × α => ¬ ij.1 ≠ ij.2) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_diag, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨ha, hab⟩
        subst b
        exact ⟨⟨ha, ha⟩, by simp⟩
      · rintro ⟨⟨ha, hb⟩, hne⟩
        have hab : a = b := not_ne_iff.mp hne
        subst b
        exact ⟨ha, rfl⟩
    rw [← hoff, ← hdiag, hprod] at hsum
    exact hsum
  have hdiag_le : (∑ ij ∈ I.diag, f ij) ≤ H * W := by
    rw [Finset.sum_diag]
    calc
      (∑ i ∈ I, w i * w i) ≤ ∑ i ∈ I, H * w i := by
        apply Finset.sum_le_sum
        intro i hi
        have hiw := hw i hi
        nlinarith
      _ = H * W := by simp [W, Finset.mul_sum]
  have hHW : H * W ≤ W ^ 2 / 2 := by
    dsimp [W] at hW ⊢
    have hmul := mul_le_mul_of_nonneg_right hW hW_nonneg
    nlinarith [hmul]
  change W ^ 2 / 2 ≤ ∑ ij ∈ I.offDiag, f ij
  linarith [hsplit, hdiag_le, hHW]

/-- Weighted prescription count: nonparallel finite fibers and parallel
translation sums, motions.tex:967–989. -/
private lemma mapsLine_ne_of_ne (g : Motion 3) {L₁ L₂ L'₁ L'₂ : Line 3}
    (hL : L₁ ≠ L₂) (h₁ : mapsLine g L₁ L'₁) (h₂ : mapsLine g L₂ L'₂) :
    L'₁ ≠ L'₂ := by
  intro h'
  have himage : g '' (L₁.1 : Set (E 3)) = g '' (L₂.1 : Set (E 3)) := by
    change g '' (L₁.1 : Set (E 3)) = (L'₁.1 : Set (E 3)) at h₁
    change g '' (L₂.1 : Set (E 3)) = (L'₂.1 : Set (E 3)) at h₂
    rw [h'] at h₁
    exact h₁.trans h₂.symm
  have hset : (L₁.1 : Set (E 3)) = (L₂.1 : Set (E 3)) :=
    Set.image_injective.mpr g.injective himage
  apply hL
  apply Subtype.ext
  exact SetLike.coe_injective hset

private lemma lineMatchWeight_eq_matchCount_of_mapsLine
    (X Y : Finset (E 3)) (g : Motion 3) (L L' : Line 3)
    (hmap : mapsLine g L L') :
    lineMatchWeight X Y L L' g = matchCount (pointsOn X L) Y g := by
  unfold lineMatchWeight matchCount
  congr 1
  ext x
  simp only [matchPoints, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hx, (Finset.mem_filter.mp hy).1⟩
  · rintro ⟨hx, hy⟩
    have hxL : x ∈ L.1 := by
      simpa [pointsOn] using
        (Finset.mem_filter.mp (show x ∈ pointsOn X L from hx)).2
    have himage : g x ∈ g '' (L.1 : Set (E 3)) := ⟨x, hxL, rfl⟩
    have htarget : g x ∈ L'.1 := by
      change g '' (L.1 : Set (E 3)) = (L'.1 : Set (E 3)) at hmap
      rw [hmap] at himage
      exact himage
    exact ⟨hx, Finset.mem_filter.mpr ⟨hy, htarget⟩⟩

private theorem fixed_source_pair_weight_bound (Cpar : ℝ)
    (hCpar : 0 < Cpar)
    (X Y : Finset (E 3)) (LX LY : Finset (Line 3)) (G : Finset (Motion 3))
    (hparPairs : ∀ ρ : ℝ, 0 < ρ →
      ((LY.offDiag.filter (fun tt => parallel tt.1 tt.2 ∧
        lineSeparation tt.1 tt.2 = ρ)).card : ℝ) ≤
          Cpar * (LY.card : ℝ) ^ ((3 : ℝ) / 2))
    (H : ℝ) (w : Motion 3 → Line 3 → ℝ) (hH : 0 ≤ H)
    (hXcap : cloudLineCap X H) (hYcap : cloudLineCap Y H)
    (hw : ∀ g ∈ G, ∀ L ∈ LX,
      0 ≤ w g L ∧ w g L ≤ (matchCount (pointsOn X L) Y g : ℝ) ∧
        (0 < w g L → ∃ L' ∈ LY, mapsLine g L L'))
    (L₁ L₂ : Line 3) (hL₁ : L₁ ∈ LX) (hL₂ : L₂ ∈ LX) (hL : L₁ ≠ L₂) :
    (∑ g ∈ G, w g L₁ * w g L₂) ≤
      8 * H ^ 2 * (LY.card : ℝ) ^ 2 +
        4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := by
  classical
  let targetExists : Motion 3 → Prop := fun g =>
    ∃ tt : Line 3 × Line 3, tt ∈ LY.offDiag ∧
      mapsLine g L₁ tt.1 ∧ mapsLine g L₂ tt.2
  let targetPair : Motion 3 → Line 3 × Line 3 := fun g =>
    if h : targetExists g then Classical.choose h else (L₁, L₁)
  let fiber : Line 3 × Line 3 → ℝ := fun tt =>
    ∑ g ∈ G.filter (fun g => targetPair g = tt), w g L₁ * w g L₂
  have hmatchBound (g : Motion 3) (L : Line 3) :
      (matchCount (pointsOn X L) Y g : ℝ) ≤ ((pointsOn X L).card : ℝ) := by
    unfold matchCount matchPoints
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _))
  have hweightBound (g : Motion 3) (hg : g ∈ G) (L : Line 3) (hLx : L ∈ LX) :
      0 ≤ w g L ∧ w g L ≤ H := by
    have h := hw g hg L hLx
    exact ⟨h.1, h.2.1.trans ((hmatchBound g L).trans (hXcap L))⟩
  have hdefaultNot : (L₁, L₁) ∉ LY.offDiag := by simp [Finset.mem_offDiag]
  have htargetExistsOfPos (g : Motion 3) (hg : g ∈ G)
      (hpos : 0 < w g L₁ * w g L₂) : targetExists g := by
    have hw₁ := hweightBound g hg L₁ hL₁
    have hw₂ := hweightBound g hg L₂ hL₂
    have hpos₁ : 0 < w g L₁ := by
      by_contra hn
      have hle : w g L₁ ≤ 0 := le_of_not_gt hn
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg hle hw₂.1
      linarith
    have hpos₂ : 0 < w g L₂ := by
      by_contra hn
      have hle : w g L₂ ≤ 0 := le_of_not_gt hn
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hw₁.1 hle
      linarith
    obtain ⟨T₁, hT₁, hm₁⟩ := (hw g hg L₁ hL₁).2.2 hpos₁
    obtain ⟨T₂, hT₂, hm₂⟩ := (hw g hg L₂ hL₂).2.2 hpos₂
    refine ⟨(T₁, T₂), ?_, hm₁, hm₂⟩
    rw [Finset.mem_offDiag]
    exact ⟨hT₁, hT₂, mapsLine_ne_of_ne g hL hm₁ hm₂⟩
  have hselected (g : Motion 3) (he : targetExists g) :
      targetPair g ∈ LY.offDiag ∧ mapsLine g L₁ (targetPair g).1 ∧
        mapsLine g L₂ (targetPair g).2 := by
    dsimp [targetPair]
    rw [dif_pos he]
    exact Classical.choose_spec he
  have htargetExistsOfMem (g : Motion 3) (ht : targetPair g ∈ LY.offDiag) :
      targetExists g := by
    by_contra hn
    have hdeq : targetPair g = (L₁, L₁) := by simp [targetPair, hn]
    rw [hdeq] at ht
    exact hdefaultNot ht
  have hselectedMaps (g : Motion 3) (ht : targetPair g ∈ LY.offDiag) :
      mapsLine g L₁ (targetPair g).1 ∧ mapsLine g L₂ (targetPair g).2 := by
    rcases hselected g (htargetExistsOfMem g ht) with ⟨_, hm₁, hm₂⟩
    exact ⟨hm₁, hm₂⟩
  have hdefaultZero (g : Motion 3) (hg : g ∈ G)
      (heq : targetPair g = (L₁, L₁)) : w g L₁ * w g L₂ = 0 := by
    have hw₁ := hweightBound g hg L₁ hL₁
    have hw₂ := hweightBound g hg L₂ hL₂
    have hnonneg : 0 ≤ w g L₁ * w g L₂ := mul_nonneg hw₁.1 hw₂.1
    by_contra hne
    have hpos : 0 < w g L₁ * w g L₂ := lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hex := htargetExistsOfPos g hg hpos
    have hs := (hselected g hex).1
    exact hdefaultNot (heq ▸ hs)
  have hpairCard : (LY.offDiag.card : ℝ) ≤ (LY.card : ℝ) ^ 2 := by
    have hn : LY.offDiag.card ≤ LY.card ^ 2 := by
      rw [Finset.offDiag_card, pow_two]
      exact Nat.sub_le _ _
    exact_mod_cast hn
  have hnonparallelTerm : 0 ≤ 8 * H ^ 2 * (LY.card : ℝ) ^ 2 := by positivity
  have hparallelTerm :
      0 ≤ 4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  by_cases hpar : parallel L₁ L₂
  · obtain ⟨p, hp, q, hq, hsep, hdistpos, _⟩ := parallel_sep_projection L₁ L₂ hpar hL
    have hρpos : 0 < lineSeparation L₁ L₂ := by rw [hsep]; exact hdistpos
    let Tρ : Finset (Line 3 × Line 3) := LY.offDiag.filter
      (fun tt => parallel tt.1 tt.2 ∧ lineSeparation tt.1 tt.2 = lineSeparation L₁ L₂)
    let I : Finset (Line 3 × Line 3) := insert (L₁, L₁) Tρ
    have hnot : (L₁, L₁) ∉ Tρ := by
      intro ht
      exact hdefaultNot (Finset.mem_filter.mp ht).1
    have hmap : (G : Set (Motion 3)).MapsTo targetPair (I : Set (Line 3 × Line 3)) := by
      intro g hg
      change targetPair g ∈ insert (L₁, L₁) Tρ
      by_cases hex : targetExists g
      · rcases hselected g hex with ⟨ht, hm₁, hm₂⟩
        have hTne : (targetPair g).1 ≠ (targetPair g).2 :=
          (Finset.mem_offDiag.mp ht).2.2
        have hpres : (prescribedLineMotions L₁ L₂ (targetPair g).1 (targetPair g).2).Nonempty :=
          by
            refine ⟨g, ?_⟩
            change mapsLine g L₁ (targetPair g).1 ∧ mapsLine g L₂ (targetPair g).2
            exact ⟨hm₁, hm₂⟩
        obtain ⟨hparTar, hsepTar, _, _, _⟩ :=
          line_images_parallel L₁ L₂ (targetPair g).1 (targetPair g).2 hL hTne hpar hpres
        have hmem : targetPair g ∈ Tρ := by
          change targetPair g ∈ LY.offDiag.filter _
          refine Finset.mem_filter.mpr ⟨ht, ?_⟩
          exact ⟨hparTar, hsepTar.symm⟩
        exact Finset.mem_insert_of_mem hmem
      · have hdeq : targetPair g = (L₁, L₁) := by
          dsimp [targetPair]
          rw [dif_neg hex]
        rw [hdeq]
        exact Finset.mem_insert_self _ _
    have hfiberSum : (∑ g ∈ G, w g L₁ * w g L₂) = ∑ tt ∈ I, fiber tt := by
      exact (Finset.sum_fiberwise_of_maps_to hmap (fun g => w g L₁ * w g L₂)).symm
    have hdefaultFiber : fiber (L₁, L₁) = 0 := by
      dsimp [fiber]
      apply Finset.sum_eq_zero
      intro g hg
      rcases Finset.mem_filter.mp hg with ⟨hgG, heq⟩
      exact hdefaultZero g hgG heq
    have hsplit : (∑ tt ∈ I, fiber tt) =
        fiber (L₁, L₁) + ∑ tt ∈ Tρ, fiber tt := by
      rw [show I = insert (L₁, L₁) Tρ from rfl, Finset.sum_insert hnot]
    have hfiberBound (tt : Line 3 × Line 3) (htt : tt ∈ Tρ) : fiber tt ≤ 4 * H ^ 3 := by
      let Gt : Finset (Motion 3) := G.filter (fun g => targetPair g = tt)
      have hpres (g : Motion 3) (hg : g ∈ Gt) :
          g ∈ prescribedLineMotions L₁ L₂ tt.1 tt.2 := by
        have hmem := Finset.mem_filter.mp hg
        have hm := hselectedMaps g (by rw [hmem.2]; exact (Finset.mem_filter.mp htt).1)
        change mapsLine g L₁ tt.1 ∧ mapsLine g L₂ tt.2
        rw [hmem.2] at hm
        exact hm
      have hTne : tt.1 ≠ tt.2 := (Finset.mem_offDiag.mp (Finset.mem_filter.mp htt).1).2.2
      have hparallelBound := parallel_line_weights X Y L₁ L₂ tt.1 tt.2 H hH
        hL hTne hpar (hXcap L₁) (hXcap L₂) (hYcap tt.1) (hYcap tt.2)
      have htermLE (g : Motion 3) (hg : g ∈ Gt) :
          w g L₁ * w g L₂ ≤
            (lineMatchWeight X Y L₁ tt.1 g : ℝ) * lineMatchWeight X Y L₂ tt.2 g := by
        have hgG := (Finset.mem_filter.mp hg).1
        have hm₀ := hselectedMaps g (by rw [(Finset.mem_filter.mp hg).2]; exact
          (Finset.mem_filter.mp htt).1)
        have hm : mapsLine g L₁ tt.1 ∧ mapsLine g L₂ tt.2 := by
          simpa [(Finset.mem_filter.mp hg).2] using hm₀
        have hle₁ : w g L₁ ≤ (lineMatchWeight X Y L₁ tt.1 g : ℝ) := by
          rw [lineMatchWeight_eq_matchCount_of_mapsLine X Y g L₁ tt.1 hm.1]
          exact (hw g hgG L₁ hL₁).2.1
        have hle₂ : w g L₂ ≤ (lineMatchWeight X Y L₂ tt.2 g : ℝ) := by
          rw [lineMatchWeight_eq_matchCount_of_mapsLine X Y g L₂ tt.2 hm.2]
          exact (hw g hgG L₂ hL₂).2.1
        have hw₂ := hweightBound g hgG L₂ hL₂
        calc
          _ ≤ (lineMatchWeight X Y L₁ tt.1 g : ℝ) * w g L₂ :=
            mul_le_mul_of_nonneg_right hle₁ hw₂.1
          _ ≤ (lineMatchWeight X Y L₁ tt.1 g : ℝ) * lineMatchWeight X Y L₂ tt.2 g :=
            mul_le_mul_of_nonneg_left hle₂ (by positivity)
      calc
        fiber tt ≤ ∑ g ∈ Gt,
            (lineMatchWeight X Y L₁ tt.1 g : ℝ) * lineMatchWeight X Y L₂ tt.2 g := by
          dsimp [fiber, Gt]
          apply Finset.sum_le_sum
          intro g hg
          exact htermLE g hg
        _ ≤ 4 * H ^ 3 := hparallelBound.2 Gt hpres
    have hsumT : (∑ tt ∈ Tρ, fiber tt) ≤
        4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := by
      have hTcard : (Tρ.card : ℝ) ≤ Cpar * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := by
        have := hparPairs (lineSeparation L₁ L₂) hρpos
        simpa [Tρ] using this
      calc
        (∑ tt ∈ Tρ, fiber tt) ≤ ∑ tt ∈ Tρ, 4 * H ^ 3 :=
          Finset.sum_le_sum (fun tt htt => hfiberBound tt htt)
        _ = (Tρ.card : ℝ) * (4 * H ^ 3) := by simp
        _ ≤ (Cpar * (LY.card : ℝ) ^ ((3 : ℝ) / 2)) * (4 * H ^ 3) :=
          mul_le_mul_of_nonneg_right hTcard (by positivity)
        _ = 4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := by ring
    calc
      (∑ g ∈ G, w g L₁ * w g L₂) = ∑ tt ∈ I, fiber tt := hfiberSum
      _ = fiber (L₁, L₁) + ∑ tt ∈ Tρ, fiber tt := hsplit
      _ = ∑ tt ∈ Tρ, fiber tt := by rw [hdefaultFiber]; simp
      _ ≤ 4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := hsumT
      _ ≤ 8 * H ^ 2 * (LY.card : ℝ) ^ 2 +
          4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := by linarith [hnonparallelTerm]
  · let T : Finset (Line 3 × Line 3) := LY.offDiag
    let I : Finset (Line 3 × Line 3) := insert (L₁, L₁) T
    have hnot : (L₁, L₁) ∉ T := hdefaultNot
    have hmap : (G : Set (Motion 3)).MapsTo targetPair (I : Set (Line 3 × Line 3)) := by
      intro g hg
      change targetPair g ∈ insert (L₁, L₁) T
      by_cases hex : targetExists g
      · exact Finset.mem_insert_of_mem (hselected g hex).1
      · have hdeq : targetPair g = (L₁, L₁) := by
          dsimp [targetPair]
          rw [dif_neg hex]
        rw [hdeq]
        exact Finset.mem_insert_self _ _
    have hfiberSum : (∑ g ∈ G, w g L₁ * w g L₂) = ∑ tt ∈ I, fiber tt := by
      exact (Finset.sum_fiberwise_of_maps_to hmap (fun g => w g L₁ * w g L₂)).symm
    have hdefaultFiber : fiber (L₁, L₁) = 0 := by
      dsimp [fiber]
      apply Finset.sum_eq_zero
      intro g hg
      rcases Finset.mem_filter.mp hg with ⟨hgG, heq⟩
      exact hdefaultZero g hgG heq
    have hsplit : (∑ tt ∈ I, fiber tt) =
        fiber (L₁, L₁) + ∑ tt ∈ T, fiber tt := by
      rw [show I = insert (L₁, L₁) T from rfl, Finset.sum_insert hnot]
    have hfiberBound (tt : Line 3 × Line 3) (htt : tt ∈ T) : fiber tt ≤ 8 * H ^ 2 := by
      let Gt : Finset (Motion 3) := G.filter (fun g => targetPair g = tt)
      have hpres (g : Motion 3) (hg : g ∈ Gt) :
          g ∈ prescribedLineMotions L₁ L₂ tt.1 tt.2 := by
        have hmem := Finset.mem_filter.mp hg
        have hm := hselectedMaps g (by rw [hmem.2]; exact htt)
        change mapsLine g L₁ tt.1 ∧ mapsLine g L₂ tt.2
        rw [hmem.2] at hm
        exact hm
      have hTne : tt.1 ≠ tt.2 := (Finset.mem_offDiag.mp htt).2.2
      obtain ⟨hfinite, hcount⟩ := line_images_nonparallel L₁ L₂ tt.1 tt.2 hL hTne hpar
      have hGsubset : Gt ⊆ hfinite.toFinset := by
        intro g hg
        exact hfinite.mem_toFinset.mpr (hpres g hg)
      have hGcard : (Gt.card : ℝ) ≤ 8 := by
        calc
          (Gt.card : ℝ) ≤ (hfinite.toFinset.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hGsubset
          _ = (prescribedLineMotions L₁ L₂ tt.1 tt.2).ncard := by
            rw [← Set.ncard_eq_toFinset_card _ hfinite]
          _ ≤ 8 := hcount
      have htermLE (g : Motion 3) (hg : g ∈ Gt) : w g L₁ * w g L₂ ≤ H ^ 2 := by
        have hgG := (Finset.mem_filter.mp hg).1
        have hw₁ := hweightBound g hgG L₁ hL₁
        have hw₂ := hweightBound g hgG L₂ hL₂
        calc
          w g L₁ * w g L₂ ≤ H * w g L₂ := mul_le_mul_of_nonneg_right hw₁.2 hw₂.1
          _ ≤ H * H := mul_le_mul_of_nonneg_left hw₂.2 hH
          _ = H ^ 2 := by ring
      calc
        fiber tt ≤ ∑ g ∈ Gt, H ^ 2 := by
          dsimp [fiber, Gt]
          apply Finset.sum_le_sum
          intro g hg
          exact htermLE g hg
        _ = (Gt.card : ℝ) * H ^ 2 := by simp
        _ ≤ 8 * H ^ 2 := mul_le_mul_of_nonneg_right hGcard (sq_nonneg H)
    have hsumT : (∑ tt ∈ T, fiber tt) ≤ 8 * H ^ 2 * (LY.card : ℝ) ^ 2 := by
      calc
        (∑ tt ∈ T, fiber tt) ≤ ∑ tt ∈ T, 8 * H ^ 2 :=
          Finset.sum_le_sum (fun tt htt => hfiberBound tt htt)
        _ = (T.card : ℝ) * (8 * H ^ 2) := by simp [T]
        _ ≤ (LY.card : ℝ) ^ 2 * (8 * H ^ 2) :=
          mul_le_mul_of_nonneg_right (by simpa [T] using hpairCard)
            (mul_nonneg (by norm_num) (sq_nonneg H))
        _ = 8 * H ^ 2 * (LY.card : ℝ) ^ 2 := by ring
    calc
      (∑ g ∈ G, w g L₁ * w g L₂) = ∑ tt ∈ I, fiber tt := hfiberSum
      _ = fiber (L₁, L₁) + ∑ tt ∈ T, fiber tt := hsplit
      _ = ∑ tt ∈ T, fiber tt := by rw [hdefaultFiber]; simp
      _ ≤ 8 * H ^ 2 * (LY.card : ℝ) ^ 2 := hsumT
      _ ≤ 8 * H ^ 2 * (LY.card : ℝ) ^ 2 +
          4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := by linarith [hparallelTerm]

theorem line_weight_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (X Y : Finset (E 3)) (LX LY : Finset (Line 3)) (G : Finset (Motion 3))
      (H : ℝ) (w : Motion 3 → Line 3 → ℝ), 0 ≤ H →
      cloudLineCap X H → cloudLineCap Y H →
      (∀ g ∈ G, ∀ L ∈ LX,
        0 ≤ w g L ∧ w g L ≤ (matchCount (pointsOn X L) Y g : ℝ) ∧
          (0 < w g L → ∃ L' ∈ LY, mapsLine g L L')) →
      (∑ g ∈ G, ∑ LL' ∈ LX.offDiag, w g LL'.1 * w g LL'.2) ≤
        C * (H ^ 2 * (LX.card : ℝ) ^ 2 * (LY.card : ℝ) ^ 2 +
          H ^ 3 * (LX.card : ℝ) ^ 2 * (LY.card : ℝ) ^ ((3 : ℝ) / 2)) := by
  obtain ⟨Cpar, hCpar, hparPairs⟩ := mot_parallel_pairs
  let C : ℝ := 8 + 4 * Cpar
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro X Y LX LY G H w hH hXcap hYcap hw
  classical
  let A : ℝ := H ^ 2 * (LX.card : ℝ) ^ 2 * (LY.card : ℝ) ^ 2
  let B : ℝ := H ^ 3 * (LX.card : ℝ) ^ 2 * (LY.card : ℝ) ^ ((3 : ℝ) / 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpairCard : (LX.offDiag.card : ℝ) ≤ (LX.card : ℝ) ^ 2 := by
    have hn : LX.offDiag.card ≤ LX.card ^ 2 := by
      rw [Finset.offDiag_card, pow_two]
      exact Nat.sub_le _ _
    exact_mod_cast hn
  have hpairBound (LL' : Line 3 × Line 3) (hLL' : LL' ∈ LX.offDiag) :
      (∑ g ∈ G, w g LL'.1 * w g LL'.2) ≤
        8 * H ^ 2 * (LY.card : ℝ) ^ 2 +
          4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := by
    have hmem := Finset.mem_offDiag.mp hLL'
    exact fixed_source_pair_weight_bound Cpar hCpar X Y LX LY G
      (fun ρ hρ => hparPairs LY ρ hρ) H w hH
      hXcap hYcap hw LL'.1 LL'.2 hmem.1 hmem.2.1 hmem.2.2
  have hKnonneg :
      0 ≤ 8 * H ^ 2 * (LY.card : ℝ) ^ 2 +
        4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have htotal :
      (∑ g ∈ G, ∑ LL' ∈ LX.offDiag, w g LL'.1 * w g LL'.2) ≤
        8 * A + 4 * Cpar * B := by
    calc
      (∑ g ∈ G, ∑ LL' ∈ LX.offDiag, w g LL'.1 * w g LL'.2) =
          ∑ LL' ∈ LX.offDiag, ∑ g ∈ G, w g LL'.1 * w g LL'.2 := by
            rw [Finset.sum_comm]
      _ ≤ ∑ LL' ∈ LX.offDiag,
          (8 * H ^ 2 * (LY.card : ℝ) ^ 2 +
            4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2)) := by
          apply Finset.sum_le_sum
          intro LL' hLL'
          exact hpairBound LL' hLL'
      _ = (LX.offDiag.card : ℝ) *
          (8 * H ^ 2 * (LY.card : ℝ) ^ 2 +
            4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2)) := by simp; ring
      _ ≤ (LX.card : ℝ) ^ 2 *
          (8 * H ^ 2 * (LY.card : ℝ) ^ 2 +
            4 * Cpar * H ^ 3 * (LY.card : ℝ) ^ ((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hpairCard hKnonneg
      _ = 8 * A + 4 * Cpar * B := by simp [A, B]; ring
  have hbudget : 8 * A + 4 * Cpar * B ≤ C * (A + B) := by
    dsimp [C]
    nlinarith [mul_nonneg (le_of_lt hCpar) hA, hB]
  calc
    (∑ g ∈ G, ∑ LL' ∈ LX.offDiag, w g LL'.1 * w g LL'.2) ≤ 8 * A + 4 * Cpar * B := htotal
    _ ≤ C * (A + B) := hbudget
    _ = C * (H ^ 2 * (LX.card : ℝ) ^ 2 * (LY.card : ℝ) ^ 2 +
        H ^ 3 * (LX.card : ℝ) ^ 2 * (LY.card : ℝ) ^ ((3 : ℝ) / 2)) := by
          simp [A, B]

end DistinctDistances.TrackC
