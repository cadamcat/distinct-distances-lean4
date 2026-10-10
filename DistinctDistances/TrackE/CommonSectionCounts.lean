import DistinctDistances.TrackE.CommonCountedIsolation

/-! The literal SAME-base mixed section bounds varying radial degrees,
`sc:retained-products.family`, sparse-cones.tex:194–207. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

theorem common_fixed_source_mixed_section_bound {d k : ℕ} (i₀ : Fin d)
    (X Y : AffineVariety d) (hY : Y.IsIrreducible) (hkd : k ≤ d)
    (hZ : (commonProductImage i₀ X Y).IsIrreducible)
    (hZd : (commonProductImage i₀ X Y).dimension = 2 * k)
    (φ : AffineProjection d k) (s : Point k) (S : Finset (Point d))
    (hsource : ∀ p ∈ S, commonSectionSourceCondition i₀ X Y φ s p) :
    (∑ p ∈ S, (radialImage p Y).degree) ≤ (commonProductImage i₀ X Y).degree := by
  let R (p : Point d) := TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀)
  have hR (p : Point d) (hp : p ∈ S) : (R p).IsIrreducible ∧
      (R p).dimension = k ∧ (R p).degree = (radialImage p Y).degree := by
    rcases hsource p hp with ⟨_, _, _, hchart, hdim, _⟩
    exact common_radial_slice_geometry i₀ Y hY p hchart hdim
  let F : AffineFamily.Family d := S.image R
  have hF : AffineFamily.IsPure F k := by
    intro V hV
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨(hR p hp).1, (hR p hp).2.1⟩
  obtain ⟨ψ, hψ, hnorm⟩ := TrackA.poly_hilbert_normalization F k hkd hF
  have hnormR (p : Point d) (hp : p ∈ S) : TrackA.FiniteAffineProjection ψ (R p) ∧ ∃ r : ℕ,
      (r : ℚ) = (R p).degree ∧ ψ.GenericallyFiniteOfDegree (R p) r :=
    hnorm (R p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have hopen (p : ↥S) : ∃ g : Poly d, g ∉ (R p.val).ideal ∧
      ∀ v ∈ R p.val, MvPolynomial.eval v g ≠ 0 →
        Function.Injective (ψ.linear.domRestrict ((R p.val).tangentSpace v)) ∧
          ∃ y ∈ Y, commonTangentPair i₀ X Y p.val y ∧
            TrackD.dirChart (LinearMap.proj i₀) (y - p.val) = v := by
    rcases hsource p.val p.property with ⟨_, _, _, hchart, _, htarget⟩
    obtain ⟨a, ha, hgood⟩ := common_principal_open_of_general Y
      (fun y => commonTangentPair i₀ X Y p.val y) htarget
    obtain ⟨b, hb, hlift⟩ := common_radial_slice_lifts_target_open i₀ Y hY p.val hchart a ha
    have hbgen : TrackD.ForGeneralPoint (R p.val) (fun v => MvPolynomial.eval v b ≠ 0) := by
      exact ⟨b, GenericFiber.exists_point_of_not_mem (R p.val) b hb, fun v hv h => h⟩
    have hinj := common_normalization_general_tangent_injective (R p.val)
      (hR p.val p.property).1 (hR p.val p.property).2.1 ψ (hnormR p.val p.property).1
    obtain ⟨g, hg, hall⟩ := common_principal_open_of_general (R p.val) _
      (hinj.and (hR p.val p.property).1 hbgen)
    refine ⟨g, hg, ?_⟩
    intro v hv hgv
    have hh := hall v hv hgv
    obtain ⟨y, hy, _, hya, hdir⟩ := hlift v hv hh.2
    exact ⟨hh.1, y, hy, hgood y hy hya, hdir⟩
  choose g hg hgood using hopen
  let a : Point d → Poly d := fun p => if hp : p ∈ S then g ⟨p, hp⟩ else 1
  have haproper (p : Point d) (hp : p ∈ S) : a p ∉ (R p).ideal := by
    simpa only [a, dif_pos hp] using hg ⟨p, hp⟩
  have hgoodfull (p : Point d) (hp : p ∈ S) (v : Point d) (hv : v ∈ R p)
      (hva : MvPolynomial.eval v (a p) ≠ 0) :
      Function.Injective (ψ.linear.domRestrict ((R p).tangentSpace v)) ∧
        ∃ y ∈ Y, commonTangentPair i₀ X Y p y ∧
          TrackD.dirChart (LinearMap.proj i₀) (y - p) = v := by
    apply hgood ⟨p, hp⟩ v hv
    simpa only [a, dif_pos hp] using hva
  obtain ⟨t, T, hT⟩ := common_simultaneous_normalization_sections_in_open S R
    (fun p hp => ⟨(hR p hp).1, (hR p hp).2.1⟩) ψ hnormR a haproper
  obtain ⟨E, hlin, heval, hkernel⟩ := common_block_affine_equations φ ψ s t
  let W : Finset (Point (d + d)) := S.biUnion (fun p => (T p).image (TrackD.productPoint p))
  have hisolated : ∀ z ∈ W, pointIdeal z ∈
      ((commonProductImage i₀ X Y).ideal ⊔ Ideal.span (Set.range E)).minimalPrimes := by
    intro z hz
    obtain ⟨p, hp, hzimage⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hzimage
    have hvR := ((hT p hp).2.1 v).mp hv
    rcases hsource p hp with ⟨hpX, hφp, hinj, _, _, _⟩
    have hh := hgoodfull p hp v hvR.1 ((hT p hp).2.2 v hv)
    apply common_counted_label_isolated i₀ X Y hZ φ ψ E hlin p v hpX hh.2 hinj hh.1
      ((heval p v).2 ⟨hφp, hvR.2⟩) (hkernel (TrackD.productPoint p v))
  have hbound : (W.card : ℚ) ≤ (commonProductImage i₀ X Y).degree := by
    have h := TrackA.relative_irreducible_point_bound (commonProductImage i₀ X Y) hZ hZd
      (Set.range E) 1 (by norm_num) (by rintro f ⟨i, rfl⟩; exact hlin i) W hisolated
    simpa only [Nat.cast_one, one_pow, mul_one] using h
  have hsum : (W.card : ℚ) = ∑ p ∈ S, (radialImage p Y).degree := by
    dsimp only [W]
    rw [common_label_union_card, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    exact ((hT p hp).1).trans (hR p hp).2.2
  exact hsum ▸ hbound

end
end DistinctDistances.SparseCones
