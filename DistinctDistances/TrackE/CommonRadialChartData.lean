import DistinctDistances.TrackD.RationalImageGeometry
import DistinctDistances.TrackD.SecantsLabelAlgebra
import DistinctDistances.TrackA.ProjectiveChartRankSupport

/-! The literal normalized radial chart, sparse-cones.tex:172–180. -/
namespace DistinctDistances.SparseCones
noncomputable section

def commonRadialNumerator {d : ℕ} (p : Point d) (j : Fin d) : Poly d :=
  MvPolynomial.X j - MvPolynomial.C (p j)

def commonRadialDenominator {d : ℕ} (i₀ : Fin d) (p : Point d) : Poly d :=
  commonRadialNumerator p i₀

def commonRadialChartImage {d : ℕ} (i₀ : Fin d) (p : Point d)
    (Y : AffineVariety d) : AffineVariety d :=
  TrackD.rationalImage Y (commonRadialNumerator p) (commonRadialDenominator i₀ p)

end
end DistinctDistances.SparseCones
