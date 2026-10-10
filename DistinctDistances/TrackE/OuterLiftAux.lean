import DistinctDistances.Foundations.Affine
import DistinctDistances.Foundations.Local
import DistinctDistances.Foundations.PointLocal
import DistinctDistances.TrackD.Profiles.Defs
import DistinctDistances.TrackD.Profiles.JacobianGeometry

/-! Small algebraic-geometry infrastructure for the outer lift
(sparse-cones.tex:580–594).

`outer_localDimension_le_jacKerRank` : the local dimension at a
point of an irreducible variety is bounded by the rank of the Jacobian kernel
of any finite set of equations vanishing on it (A-outer-1 of the track-A
requests). `outer_minimal_component_localDimension` : through
every point of an ideal locus there is a prime component whose local dimension
equals its dimension (A-outer-2). Both feed `outer_lift_curve`
(193) once the specialized preimage variety is constructed; both are also
available for adoption into track A Foundations. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section
variable {n : ℕ}

/-- sc:outer-lift.jacobian-bound (sparse-cones.tex:580–594).
Let `V` be irreducible, `x ∈ V`, and `E` a finite set of polynomials in
`V.ideal`. Then `V.localDimension x ≤ finrank (jacKer E x)`. Proof: chain
`AffineVariety.localDimension_le_dimension` (Foundations/Local.lean:670),
`TrackD.tangent_finrank_ge_dimension` (Profiles/JacobianGeometry.lean:173) and
`TrackD.tangent_le_jacKer` (same file:208) with `Submodule.finrank_mono`.
Note `x ∈ V` is `x ∈ V.points` by the `Membership` instance
(Foundations/Affine.lean:36). -/
theorem outer_localDimension_le_jacKerRank (V : AffineVariety n)
    (hV : V.IsIrreducible) (x : Point n) (hx : x ∈ V.points)
    (E : Finset (Poly n)) (hE : ∀ f ∈ E, f ∈ V.ideal) :
    V.localDimension x ≤ Module.finrank ℂ (TrackD.jacKer E x) := by
  have h1 : V.localDimension x ≤ V.dimension :=
    AffineVariety.localDimension_le_dimension V x hx
  have h2 : V.dimension ≤ Module.finrank ℂ (V.tangentSpace x) :=
    TrackD.tangent_finrank_ge_dimension V hV x hx
  have h3 : V.tangentSpace x ≤ TrackD.jacKer E x :=
    TrackD.tangent_le_jacKer V E hE x
  exact le_trans h1 (le_trans h2 (Submodule.finrank_mono h3))

/-- sc:outer-lift.minimal-component (sparse-cones.tex:580–594,
impl). Let `I` be an ideal and `x` a point of its locus. Then there is a prime
`P ⊇ I` with `x` in the locus of `P` and
`(ofIdeal P).localDimension x = (ofIdeal P).dimension`. Proof: mirror
`CommonPhysicalInputs.lean` (~100–120) and `CommonLabelGroupData.lean:98`:
`hx` gives `I ≤ pointIdeal x` (`ideal_le_pointIdeal_of_mem`,
Foundations/Local.lean:21; `pointIdeal x` is prime via
`pointIdeal_isMaximal ... |>.isPrime`, same file:68); obtain `P` from
`Ideal.exists_minimalPrimes_le` at `J = pointIdeal x` (needs the `IsPrime`
instance); `x` is in the locus of `P` since `P ≤ pointIdeal x`
(`points_ofIdeal`, Foundations/Affine.lean:117); `P` prime gives
`(ofIdeal P).IsIrreducible` (`IsIrreducible` is `IsPrime` of the ideal by
definition, Affine.lean:56, and `(ofIdeal P).ideal = P.radical = P` for prime
`P`); conclude with `AffineVariety.localDimension_eq_dimension`
(Foundations/Local.lean:896). -/
theorem outer_minimal_component_localDimension (I : Ideal (Poly n))
    (x : Point n) (hx : x ∈ (AffineVariety.ofIdeal I).points) :
    ∃ P : Ideal (Poly n), P.IsPrime ∧ I ≤ P ∧
      x ∈ (AffineVariety.ofIdeal P).points ∧
      (AffineVariety.ofIdeal P).localDimension x =
        (AffineVariety.ofIdeal P).dimension := by
  have hIx : I ≤ pointIdeal x := by
    have h := AffineVariety.ideal_le_pointIdeal_of_mem (V := AffineVariety.ofIdeal I) hx
    exact le_trans Ideal.le_radical h
  haveI : (pointIdeal x).IsPrime := (pointIdeal_isMaximal x).isPrime
  obtain ⟨P, hPmin, hPJ⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := pointIdeal x) hIx
  have hIP : I ≤ P := hPmin.le
  have hPprime : P.IsPrime := Ideal.IsMinimalPrime.isPrime hPmin
  have hPirr : (AffineVariety.ofIdeal P).IsIrreducible :=
    Ideal.isPrime_radical hPprime.isPrimary
  have hPx : P ≤ pointIdeal x := hPJ
  have hxP : x ∈ (AffineVariety.ofIdeal P).points := by
    rw [AffineVariety.points_ofIdeal]
    intro f hf
    have hfp : f ∈ pointIdeal x := hPx hf
    have hvan : f ∈ MvPolynomial.vanishingIdeal ℂ {x} := by
      simpa [pointIdeal] using hfp
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hvan _ (by simp)
  exact ⟨P, hPprime, hIP, hxP,
    AffineVariety.localDimension_eq_dimension _ _ hPirr hxP⟩

end
end DistinctDistances.SparseCones
