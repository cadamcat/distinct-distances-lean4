import DistinctDistances.TrackC.GraphDualGeometry
import DistinctDistances.TrackC.ArrangementCounting
import DistinctDistances.TrackC.NullFlatCalculus

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Pulling an injective affine parameterization through a line keeps every
zero and its distinctness. This is the first propagation step in mot:425–473. -/
theorem polynomial_on_mapped_line (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) (l : Line 3) (Z : Finset (E 3)) (f : Poly 6)
    (hZ : ∀ u ∈ Z, u ∈ l.1 ∧ evalR f (φ u) = 0)
    (hdeg : f.totalDegree < Z.card) :
    onPolynomial f (mapped_parameter_flat φ hφ l) := by
  apply polynomial_line_zeros 6 f (mapped_parameter_flat φ hφ l) (Z.image φ)
  · intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    refine ⟨?_,(hZ u hu).2⟩
    change φ u ∈ ((mapped_parameter_flat φ hφ l).1 : Set (E 6))
    rw [mapped_parameter_flat_coe]
    exact Set.mem_image_of_mem φ (hZ u hu).1
  · rwa [Finset.card_image_of_injective _ hφ]

/-- The rich-line certificate extends a polynomial from designated points to
one entire anchor plane. -/
theorem polynomial_on_mapped_anchor (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) (H : Plane 3) (Z : Finset (E 3))
    (L : Finset (Line 3)) (f : Poly 6) (ℓ ρ : ℝ)
    (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hZcard : ρ*ℓ^2 ≤ (Z.card : ℝ)) (hLcard : (L.card : ℝ) ≤ 2*ℓ)
    (hLplane : ∀ l ∈ L, (l.1 : Set (E 3)) ⊆ H.1)
    (hleft : ∀ u ∈ Z, 2 ≤ (L.filter (fun l => u ∈ l.1)).card)
    (hright : ∀ l ∈ L, ((Z.filter (fun u => u ∈ l.1)).card : ℝ) ≤ 2*ℓ)
    (hzero : ∀ u ∈ Z, evalR f (φ u) = 0)
    (hdeg : (f.totalDegree : ℝ) < ρ*ℓ/4) :
    onPolynomial f (mapped_parameter_flat φ hφ H) := by
  obtain ⟨L',hL'sub,hL'card,hL'rich⟩ := arrangement_rich_members Z L
    (fun u l => u ∈ l.1) ℓ ρ hℓ hρ hρ1 hZcard hLcard hleft hright
  let Q := L'.image (mapped_parameter_flat φ hφ)
  have hQcard : Q.card = L'.card := by
    dsimp [Q]
    rw [Finset.card_image_of_injective _ (mapped_parameter_flat_injective φ hφ)]
  apply polynomial_many_hyperplanes 6 1 (mapped_parameter_flat φ hφ H) Q f
  · intro m hm
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hm
    refine ⟨?_,?_⟩
    · intro z hz
      change z ∈ ((mapped_parameter_flat φ hφ l).1 : Set (E 6)) at hz
      rw [mapped_parameter_flat_coe] at hz
      obtain ⟨u,hu,rfl⟩ := hz
      change φ u ∈ ((mapped_parameter_flat φ hφ H).1 : Set (E 6))
      rw [mapped_parameter_flat_coe]
      exact Set.mem_image_of_mem φ (hLplane l (hL'sub hl) hu)
    · apply polynomial_on_mapped_line φ hφ l (Z.filter (fun u => u ∈ l.1)) f
      · intro u hu
        obtain ⟨huZ,hul⟩ := Finset.mem_filter.mp hu
        exact ⟨hul,hzero u huZ⟩
      · exact_mod_cast hdeg.trans_le (hL'rich l hl)
  · rw [hQcard]
    exact_mod_cast hdeg.trans_le hL'card

private def chosenAnchorPlane (x : E 3) : Plane 3 :=
  Classical.choose (graph_dual_plane_geometry x)

private theorem chosenAnchorPlane_coe (x : E 3) :
    ((chosenAnchorPlane x).1 : Set (E 3)) = graphDualPlane x :=
  Classical.choose_spec (graph_dual_plane_geometry x)

private theorem chosenAnchorPlane_injective : Function.Injective chosenAnchorPlane := by
  intro x y hxy
  apply graph_dual_plane_set_injective
  rw [← chosenAnchorPlane_coe x, ← chosenAnchorPlane_coe y, hxy]

/-- Many distinct graph anchor planes extend a polynomial to the whole motion
flat. The point/line certificates are deliberately explicit. -/
theorem polynomial_on_mapped_anchor_family (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) (G : Flat 6 3)
    (hrange : Set.range φ = (G.1 : Set (E 6))) (A : Finset (E 3))
    (f : Poly 6) (ℓ ρ : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hA : ρ*ℓ ≤ (A.card : ℝ))
    (hcert : ∀ x ∈ A, ∃ (Z : Finset (E 3)) (L : Finset (Line 3)),
      ρ*ℓ^2 ≤ (Z.card : ℝ) ∧ (L.card : ℝ) ≤ 2*ℓ ∧
      (∀ l ∈ L, (l.1 : Set (E 3)) ⊆ graphDualPlane x) ∧
      (∀ u ∈ Z, 2 ≤ (L.filter (fun l => u ∈ l.1)).card) ∧
      (∀ l ∈ L, ((Z.filter (fun u => u ∈ l.1)).card : ℝ) ≤ 2*ℓ) ∧
      (∀ u ∈ Z, evalR f (φ u) = 0))
    (hdeg : (f.totalDegree : ℝ) < ρ*ℓ/4) : onPolynomial f G := by
  let planeOf := fun x : E 3 => mapped_parameter_flat φ hφ (chosenAnchorPlane x)
  let Q := A.image planeOf
  have hinj : Function.Injective planeOf :=
    (mapped_parameter_flat_injective φ hφ).comp chosenAnchorPlane_injective
  have hQcard : Q.card = A.card := Finset.card_image_of_injective A hinj
  apply polynomial_many_hyperplanes 6 2 G Q f
  · intro H hH
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hH
    refine ⟨?_,?_⟩
    · intro z hz
      change z ∈ ((mapped_parameter_flat φ hφ (chosenAnchorPlane x)).1 : Set (E 6)) at hz
      rw [mapped_parameter_flat_coe] at hz
      obtain ⟨u,hu,rfl⟩ := hz
      change φ u ∈ (G.1 : Set (E 6))
      rw [← hrange]
      exact Set.mem_range_self u
    · obtain ⟨Z,L,hZ,hL,hplane,hleft,hright,hzero⟩ := hcert x hx
      apply polynomial_on_mapped_anchor φ hφ (chosenAnchorPlane x) Z L f ℓ ρ
        hℓ hρ hρ1 hZ hL _ hleft hright hzero hdeg
      intro l hl
      rw [chosenAnchorPlane_coe]
      exact hplane l hl
  · rw [hQcard]
    have hquarter : ρ*ℓ/4 ≤ ρ*ℓ := by nlinarith [mul_pos hρ hℓ]
    exact_mod_cast (hdeg.trans_le hquarter).trans_le hA

end DistinctDistances.TrackC
