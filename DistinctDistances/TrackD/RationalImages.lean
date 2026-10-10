import DistinctDistances.TrackD.GenericTangent
import OAI.NumberTheory.PowerFree.PatchBounds
import DistinctDistances.TrackA.Intersections

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- A rational map with a single common denominator, sufficient for the
secant label map `secants.tex:57–62`. -/
def rationalPoint {n m : ℕ} (f : Fin m → Poly n) (g : Poly n) (x : Point n) : Point m :=
  fun i => MvPolynomial.eval x (f i) / MvPolynomial.eval x g

/-- Its quotient-rule differential. -/
def rationalDifferential {n m : ℕ} (f : Fin m → Poly n) (g : Poly n) (x : Point n) :
    Point n →ₗ[ℂ] Point m :=
  LinearMap.pi (fun i =>
    (MvPolynomial.eval x g)⁻¹ • differential (f i) x -
      (MvPolynomial.eval x (f i) / (MvPolynomial.eval x g)^2) • differential g x)

/-- Reduced Zariski closure of the image on the denominator chart, in the
same affine-variety model as all carriers. -/
def rationalImage {n m : ℕ} (X : AffineVariety n) (f : Fin m → Poly n) (g : Poly n) :
    AffineVariety m :=
  AffineVariety.closure {y | ∃ x ∈ X, MvPolynomial.eval x g ≠ 0 ∧ rationalPoint f g x = y}

theorem rationalPoint_mem_image {n m : ℕ} (X : AffineVariety n)
    (f : Fin m → Poly n) (g : Poly n) (x : Point n)
    (hx : x ∈ X) (hg : MvPolynomial.eval x g ≠ 0) :
    rationalPoint f g x ∈ rationalImage X f g :=
  AffineVariety.subset_closure _ ⟨x, hx, hg, rfl⟩

/-- Dimension monotonicity for irreducible carriers uses OAI's Hilbert/trdeg
dictionary, with the quotient map providing the comparison. -/
theorem irreducible_dimension_mono {n : ℕ} (V W : AffineVariety n)
    (hV : V.IsIrreducible) (hW : W.IsIrreducible) (hVW : V.Subvariety W) :
    V.dimension ≤ W.dimension := by
  letI : V.ideal.IsPrime := hV
  letI : W.ideal.IsPrime := hW
  exact OAI.QuarticPowerFree.affineDimension_antitone W.ideal V.ideal hVW

/-- In the positive-dimensional case consumed by secants, equal dimension
forces equality. A strict containment would lie in a proper hypersurface
section and therefore in a component of smaller dimension. -/
theorem irreducible_subvariety_eq_of_pos_dimension_eq {n : ℕ}
    (V W : AffineVariety n) (hV : V.IsIrreducible) (hW : W.IsIrreducible)
    (hVW : V.Subvariety W) (hpos : 0 < W.dimension)
    (hdim : V.dimension = W.dimension) : V = W := by
  letI : V.ideal.IsPrime := hV
  by_contra hne
  have hstrict : W.ideal < V.ideal := lt_of_le_of_ne hVW (by
    intro heq
    exact hne (AffineVariety.ext heq.symm))
  obtain ⟨f, hfV, hfW⟩ := SetLike.exists_of_lt hstrict
  have hcut : W.ideal ⊔ Ideal.span {f} ≤ V.ideal := by
    apply sup_le hVW
    apply Ideal.span_le.mpr
    intro a ha
    have heq : a = f := Set.mem_singleton_iff.mp ha
    change a ∈ V.ideal
    rw [heq]
    exact hfV
  obtain ⟨J, hJ, hJV⟩ := Ideal.exists_minimalPrimes_le hcut
  let Z : AffineVariety n := ⟨J, hJ.isPrime.isRadical⟩
  have hcomp : Z.IsComponentOf (W.ideal ⊔ Ideal.span {f}) := hJ
  have hZd : Z.dimension = W.dimension - 1 :=
    TrackA.fa_bezout_proper_dimension W Z hW f hfW hcomp (W.dimension - 1) (by omega)
  have hle : V.dimension ≤ Z.dimension :=
    irreducible_dimension_mono V Z hV hJ.isPrime hJV
  omega

end
end DistinctDistances.TrackD
