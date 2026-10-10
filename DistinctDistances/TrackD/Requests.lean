import DistinctDistances.TrackD.Genericity
import DistinctDistances.TrackD.GenericTangent
import DistinctDistances.TrackD.CurveSections
import DistinctDistances.TrackD.RationalImages
import DistinctDistances.TrackD.RationalContainment
import DistinctDistances.TrackD.RationalTangentAll
import DistinctDistances.TrackD.RationalTangentSpecialization

namespace DistinctDistances.TrackD

noncomputable section

/-- `FA.model`, used at `secants.tex:69–75, 89–102`: the formerly requested generic
tangent dimension is now derived from track A's frozen regularity statement. -/
theorem request_general_tangent_finrank {d : ℕ} (X : AffineVariety d)
    (hX : X.IsIrreducible) :
    ForGeneralPoint X (fun x => Module.finrank ℂ (X.tangentSpace x) = X.dimension) := by
  exact general_tangent_finrank X hX

/-- `FA.bezout`, consumed at `secants.tex:351–367`: the former planar line-section
request is now derived from track A's frozen proper-cut and zero-dimensional bounds. -/
theorem request_planar_curve_line_intersection (Y : AffineVariety 2) (hY : IsCurve Y)
    (L : AffineSubspace ℂ (Point 2)) (hL : Module.finrank ℂ L.direction = 1)
    (hproper : ¬ Y.points ⊆ L) :
    (Y.points ∩ (L : Set (Point 2))).Finite ∧
      ((Y.points ∩ (L : Set (Point 2))).ncard : ℝ) ≤ (Y.degree : ℝ) := by
  exact planar_curve_line_intersection Y hY L hL hproper

/-- Request to track A, `FA.model`, consumed by `secants.tex:63–81`: in
characteristic zero the differential of a dominant rational map covers the
tangent space of its image at a general source point. -/
theorem request_rational_image_generic_tangent {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (f : Fin m → Poly n) (g : Poly n) (hg : g ∉ X.ideal) :
    (rationalImage X f g).IsIrreducible ∧
      ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0 ∧
        (X.tangentSpace x).map (rationalDifferential f g x) =
          (rationalImage X f g).tangentSpace (rationalPoint f g x) ∧
        Module.finrank ℂ ((rationalImage X f g).tangentSpace (rationalPoint f g x)) =
          (rationalImage X f g).dimension) := by
  have hY := rational_image_irreducible X hX f g hg
  refine ⟨hY, ?_⟩
  letI : X.ideal.IsPrime := hX
  let K := FractionRing (Poly n ⧸ X.ideal)
  have hsurj := rational_function_field_tangent_surjective X hX f g hg K
  have htarget := rational_image_field_tangent_finrank X hX f g hg K
  have hlower : (rationalImage X f g).dimension ≤ Module.finrank K
      ((fieldTangent X.ideal K (coordinateFieldMap X.ideal K)).map
        (fieldRationalDifferential K (coordinateFieldMap X.ideal K) f g)) := by
    rw [← htarget]
    exact Submodule.finrank_mono hsurj
  have hsource := rational_differential_generic_finrank X hX f g hg K
  obtain ⟨q, hq, hqt⟩ := general_tangent_finrank (rationalImage X f g) hY
  have hqnot : q ∉ (rationalImage X f g).ideal := by
    intro hmem
    obtain ⟨y, hy, hny⟩ := hq
    exact hny ((mem_ideal_iff_eval_zero (rationalImage X f g) q).mp hmem y hy)
  have htargetOpen := rational_image_nonzero_open X f g q hqnot
  apply (hsource.and hX htargetOpen).mono
  intro x hx h
  have hgx := h.1.1
  have hy := rationalPoint_mem_image X f g x hx hgx
  have hdim := hqt (rationalPoint f g x) hy h.2.2
  have hle := rational_image_tangent_all X f g x hx hgx
  refine ⟨hgx, ?_, hdim⟩
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hupper := Submodule.finrank_mono hle
  have hlower' : (rationalImage X f g).dimension ≤
      Module.finrank ℂ ((X.tangentSpace x).map (rationalDifferential f g x)) := by
    rw [h.1.2]
    exact hlower
  omega

/-- `FA.model`, consumed by `secants.tex:69–81`: the former all-point chain-rule
request is now proved by differentiating cleared image equations. -/
theorem request_rational_image_tangent_all {n m : ℕ}
    (X : AffineVariety n) (f : Fin m → Poly n) (g : Poly n)
    (x : Point n) (hx : x ∈ X) (hg : MvPolynomial.eval x g ≠ 0) :
    (X.tangentSpace x).map (rationalDifferential f g x) ≤
      (rationalImage X f g).tangentSpace (rationalPoint f g x) := by
  exact rational_image_tangent_all X f g x hx hg

/-- `FA.model`, consumed by `secants.tex:63–69`: the former generic closed
containment request is now proved by homogenizing the image equations. -/
theorem request_rational_image_generic_subset {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (f : Fin m → Poly n) (g : Poly n) (W : AffineVariety m)
    (h : ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0 ∧ rationalPoint f g x ∈ W)) :
    (rationalImage X f g).Subvariety W := by
  exact rational_image_generic_subset X hX f g W h

end
end DistinctDistances.TrackD
