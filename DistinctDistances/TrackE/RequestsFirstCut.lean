import DistinctDistances.TrackD.Profiles.Regularity
import DistinctDistances.TrackE.MReqAux

/-! Track A local-geometry request, re-exported by TrackE/Requests.lean.
The smaller module avoids Requests → Directions → SparseCones → DepthAssembly
forming an import cycle. Consumer: `G5.first-cut`, depth.tex:145–168;
supplier: `poly:regularity.minor-certificate`, polynomial.tex:542–555. -/

namespace DistinctDistances.Request

open scoped Classical

noncomputable section

/-- A smooth carrier contained in an equation locus, with the same tangent
kernel, makes that reduced equation locus smooth of the same local dimension. -/
theorem smooth_equation_locus_of_carrier {d : ℕ} (F : Finset (Poly d))
    (Z : AffineVariety d) (q : Point d) (hZ : Z.IsIrreducible)
    (hq : q ∈ Z) (hsmooth : Z.IsSmoothAt q)
    (hF : ∀ f ∈ F, f ∈ Z.ideal) (hker : Z.tangentSpace q = TrackD.jacKer F q) :
    (AffineVariety.ofIdeal (Ideal.span (F : Set (Poly d)))).IsSmoothAt q ∧
      (AffineVariety.ofIdeal (Ideal.span (F : Set (Poly d)))).localDimension q =
        Z.localDimension q := by
  exact MReqAux.smooth_locus_of_tangent_kernel F Z q hZ hq hsmooth hF hker

end

end DistinctDistances.Request
