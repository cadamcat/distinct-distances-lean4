import DistinctDistances.TrackD.Basic

/-! The uniqueness of the centre of a perspective, `secants.tex:367–370`.
These incidence arguments use affine lines directly and no polynomial input. -/

namespace DistinctDistances.TrackD

open scoped Classical
noncomputable section
variable {d : ℕ}

theorem complex_pair_line_dimension (p q : Point d) (hpq : p ≠ q) :
    Module.finrank ℂ (affineSpan ℂ {p, q}).direction = 1 := by
  rw [direction_affineSpan, vectorSpan_pair]
  apply finrank_span_singleton
  exact fun h => hpq (vsub_eq_zero_iff_eq.mp h)

/-- Two different affine lines have at most one common point. -/
theorem complex_lines_common_point_unique
    (L L' : AffineSubspace ℂ (Point d))
    (hL : Module.finrank ℂ L.direction = 1)
    (hL' : Module.finrank ℂ L'.direction = 1) (hne : L ≠ L')
    (p q : Point d) (hp : p ∈ L) (hp' : p ∈ L') (hq : q ∈ L) (hq' : q ∈ L') :
    p = q := by
  by_contra hpq
  let M := affineSpan ℂ {p, q}
  have hM : Module.finrank ℂ M.direction = 1 := complex_pair_line_dimension p q hpq
  have hML : M ≤ L := by
    apply affineSpan_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hp
    · exact (Set.mem_singleton_iff.mp hx) ▸ hq
  have hML' : M ≤ L' := by
    apply affineSpan_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hp'
    · exact (Set.mem_singleton_iff.mp hx) ▸ hq'
  have hMne : (M : Set (Point d)).Nonempty :=
    ⟨p, left_mem_affineSpan_pair ℂ p q⟩
  have heq : M = L := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hML) (hM.trans hL.symm))
    hMne hML
  have heq' : M = L' := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hML') (hM.trans hL'.symm))
    hMne hML'
  exact hne (heq.symm.trans heq')

/-- A correspondence on a point set contained in no line determines an exterior
centre from its joining lines. This also permits fixed points of the correspondence. -/
theorem perspective_correspondence_center_unique (S : Set (Point d)) (hne : S.Nonempty)
    (hproper : ∀ L : AffineSubspace ℂ (Point d), Module.finrank ℂ L.direction = 1 →
      ¬ S ⊆ L) (f : S → Point d) (p q : Point d) (hpS : p ∉ S)
    (hp : ∀ x : S, p ∈ affineSpan ℂ {x.val, f x})
    (hq : ∀ x : S, q ∈ affineSpan ℂ {x.val, f x}) : p = q := by
  obtain ⟨x, hx⟩ := hne
  let xS : S := ⟨x, hx⟩
  have hmove : x ≠ f xS := by
    intro h
    have hpx := hp xS
    have heq : p = x := by simpa [xS, ← h] using hpx
    exact hpS (heq ▸ hx)
  let L := affineSpan ℂ {x, f xS}
  have hL : Module.finrank ℂ L.direction = 1 := complex_pair_line_dimension x (f xS) hmove
  obtain ⟨y, hy, hyL⟩ := Set.not_subset.mp (hproper L hL)
  let yS : S := ⟨y, hy⟩
  by_cases hmove' : y = f yS
  · have hpy : p = y := by simpa [yS, ← hmove'] using hp yS
    have hqy : q = y := by simpa [yS, ← hmove'] using hq yS
    exact hpy.trans hqy.symm
  · let L' := affineSpan ℂ {y, f yS}
    have hL' : Module.finrank ℂ L'.direction = 1 :=
      complex_pair_line_dimension y (f yS) hmove'
    have hLL' : L ≠ L' := by
      intro heq
      apply hyL
      rw [heq]
      exact left_mem_affineSpan_pair ℂ y (f yS)
    exact complex_lines_common_point_unique L L' hL hL' hLL' p q (hp xS) (hp yS)
      (hq xS) (hq yS)

end
end DistinctDistances.TrackD
