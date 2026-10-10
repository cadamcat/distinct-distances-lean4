import DistinctDistances.TrackA.RadialInfinitySupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

theorem radial_actual_of_generic {n r : ℕ} (X : AffineVariety n) (p : Point n)
    (hr : GenericallyFiniteRadialDegree p X r) : ∃ x ∈ X.points, x ≠ p := by
  obtain ⟨hr, g, D, hg, hgnot, hgeneric⟩ := hr
  change g ∉ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives
    {z | ∃ x ∈ X.points, ∃ hx : x ≠ p, radialProjection p x hx = z}) at hgnot
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hgnot
  push Not at hgnot
  obtain ⟨v, ⟨hv, x, hx, hxne, heq⟩, hgv⟩ := hgnot
  exact ⟨x, hx, hxne⟩

/-- When all projective fibers lie in the original chart, affine embedding
is a bijection of the literal affine and projective fiber sets. -/
theorem radial_projective_fiber_eq {n : ℕ} (X : AffineVariety n) (p : Point n)
    (z : ProjectivePoint n)
    (hchart : ∀ q ∈ projectiveFiber (radialLinearProjection p) (projectiveClosure X) z,
      q.rep 0 ≠ 0) :
    projectiveFiber (radialLinearProjection p) (projectiveClosure X) z =
      affineEmbedding '' radialFiber p X z := by
  ext q
  constructor
  · intro hq
    have hq0 := hchart q hq
    obtain ⟨hqX, hφ, hmap⟩ := hq
    let x := chartCoordinates 0 q
    have hemb : affineEmbedding x = q := affineEmbedding_chartCoordinates q hq0
    have hx : x ∈ X.points := (affineEmbedding_mem_closure X x).mp (by rwa [hemb])
    have hφx : radialLinearProjection p (affineEmbedding x).rep ≠ 0 := by rwa [hemb]
    have hxne : x ≠ p := (radialLinearProjection_embedding_nonzero p x).mp hφx
    refine ⟨x, ⟨hx, hxne, ?_⟩, hemb⟩
    rw [← projectiveMap_radial p x hxne hφx]
    simpa only [hemb] using hmap
  · rintro ⟨x, ⟨hx, hxne, hmap⟩, rfl⟩
    have hφ := (radialLinearProjection_embedding_nonzero p x).mpr hxne
    exact ⟨(affineEmbedding_mem_closure X x).mpr hx, hφ,
      (projectiveMap_radial p x hxne hφ).trans hmap⟩

/-- The generic radial degree is unchanged by completing the source.
Multiply its principal-open witness by the polynomial excluding infinity. -/
theorem radial_generic_projective_degree {n k r : ℕ} (X : AffineVariety n)
    (hX : X.IsIrreducible) (hdim : X.dimension = k) (p : Point n)
    (himage : (radialImage p X).dimension = k) (hr : GenericallyFiniteRadialDegree p X r) :
    GenericallyFiniteProjectiveDegree (radialLinearProjection p) (projectiveClosure X) r := by
  have hactual := radial_actual_of_generic X p hr
  have himageEq := radial_projective_image X p hactual
  have hYirr := radialImage_irreducible p X hX hactual
  obtain ⟨H, E, hHhom, hHnot, hHZ⟩ := radial_no_infinity_polynomial X hX hdim p himage hactual
  obtain ⟨hrpos, g, D, hghom, hgnot, hgeneric⟩ := hr
  refine ⟨hrpos, g*H, D+E, hghom.mul hHhom, ?_, ?_⟩
  · rw [himageEq]
    intro hprod
    exact (hYirr.mem_or_mem hprod).elim hgnot hHnot
  · intro z hz hprod
    rw [himageEq] at hz
    have hprod' : MvPolynomial.eval z.rep g * MvPolynomial.eval z.rep H ≠ 0 := by
      simpa only [map_mul] using hprod
    have hgval : MvPolynomial.aeval z.rep g ≠ 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using (mul_ne_zero_iff.mp hprod').1
    have hHval := (mul_ne_zero_iff.mp hprod').2
    obtain ⟨hfinite, hcard⟩ := hgeneric z hz hgval
    have hchart : ∀ q ∈ projectiveFiber (radialLinearProjection p) (projectiveClosure X) z,
        q.rep 0 ≠ 0 := by
      intro q hq hq0
      obtain ⟨hqX, hφ, hmap⟩ := hq
      have hzInf : z ∈ (radialInfinityImage X p).points := by
        apply ProjectiveVariety.subset_closure
        exact ⟨q.rep, hqX q.rep q.rep_nonzero (Projectivization.mk_rep q), hq0, hφ, hmap⟩
      have hzH : MvPolynomial.eval z.rep H = 0 :=
        hzInf z.rep z.rep_nonzero (Projectivization.mk_rep z) H hHZ
      exact hHval hzH
    rw [radial_projective_fiber_eq X p z hchart]
    exact ⟨hfinite.image affineEmbedding,
      (Set.ncard_image_of_injective _ affineEmbedding_injective).trans hcard⟩

end
end DistinctDistances.TrackA
