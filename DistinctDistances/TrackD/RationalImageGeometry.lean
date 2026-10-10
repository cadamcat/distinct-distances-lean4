import DistinctDistances.TrackD.Requests
import DistinctDistances.TrackD.ProductTangents

namespace DistinctDistances.TrackD

noncomputable section
variable {d : ℕ}

theorem ForGeneralPair.on_product {X Y : AffineVariety d}
    {Q : Point d → Point d → Prop} (h : ForGeneralPair X Y Q) :
    ForGeneralPoint (productVariety X Y) (fun p => Q (productLeft p) (productRight p)) := by
  obtain ⟨g, ⟨x, hx, y, hy, hg⟩, hQ⟩ := h
  have heval (p : Point (d + d)) :
      MvPolynomial.eval p (MvPolynomial.rename finSumFinEquiv g) =
        MvPolynomial.eval (pairPt (productLeft p) (productRight p)) g := by
    rw [MvPolynomial.eval_rename]
    have heq : p ∘ finSumFinEquiv = pairPt (productLeft p) (productRight p) := by
      funext i
      cases i <;> rfl
    rw [heq]
  have hleft : productLeft (productPoint x y) = x := by
    have h := productLinearEquiv.left_inv (x, y)
    exact congrArg Prod.fst h
  have hright : productRight (productPoint x y) = y := by
    have h := productLinearEquiv.left_inv (x, y)
    exact congrArg Prod.snd h
  refine ⟨MvPolynomial.rename finSumFinEquiv g,
    ⟨productPoint x y, AffineVariety.subset_closure _ ⟨x, hx, y, hy, rfl⟩, ?_⟩, ?_⟩
  · simpa only [heval, hleft, hright] using hg
  · intro p hp hn
    have hpp : productLeft p ∈ X ∧ productRight p ∈ Y := by
      change p ∈ (productVariety X Y).points at hp
      rw [productVariety_points] at hp
      exact hp
    exact hQ (productLeft p) hpp.1 (productRight p) hpp.2 (by simpa only [heval] using hn)

/-- Generic surjectivity onto image tangents bounds the rational image
dimension by its source dimension. The geometric rank input stays explicit. -/
theorem rational_image_dimension_le_of_generic_rank {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (f : Fin m → Poly n) (g : Poly n)
    (hgen : ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0 ∧
      (X.tangentSpace x).map (rationalDifferential f g x) =
        (rationalImage X f g).tangentSpace (rationalPoint f g x) ∧
      Module.finrank ℂ ((rationalImage X f g).tangentSpace (rationalPoint f g x)) =
        (rationalImage X f g).dimension)) :
    (rationalImage X f g).dimension ≤ X.dimension := by
  obtain ⟨x, hx, ⟨hg, hmap, hdI⟩, hdX⟩ :=
    (hgen.and hX (general_tangent_finrank X hX)).exists
  have hbound := LinearMap.finrank_range_le
    ((rationalDifferential f g x).domRestrict (X.tangentSpace x))
  rw [LinearMap.range_domRestrict, hmap, hdI, hdX] at hbound
  exact hbound

/-- The image has full source dimension once its differential has full
source rank generically. Both principal opens are combined before the witness. -/
theorem rational_image_dimension_eq_of_generic_rank {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (f : Fin m → Poly n) (g : Poly n)
    (hgen : ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0 ∧
      (X.tangentSpace x).map (rationalDifferential f g x) =
        (rationalImage X f g).tangentSpace (rationalPoint f g x) ∧
      Module.finrank ℂ ((rationalImage X f g).tangentSpace (rationalPoint f g x)) =
        (rationalImage X f g).dimension))
    (hrank : ForGeneralPoint X (fun x => Module.finrank ℂ
      ((X.tangentSpace x).map (rationalDifferential f g x)) = X.dimension)) :
    (rationalImage X f g).dimension = X.dimension := by
  obtain ⟨x, hx, ⟨hg, hmap, hdI⟩, hrank⟩ := (hgen.and hX hrank).exists
  rwa [hmap, hdI] at hrank

end
end DistinctDistances.TrackD
