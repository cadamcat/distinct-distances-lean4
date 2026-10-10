import DistinctDistances.TrackD.Profiles.Defs
import DistinctDistances.TrackD.CurveSections
import DistinctDistances.TrackA.Hilbert

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

def envelopeComponents (T : Set (Point d)) (D : ℕ) : AffineFamily.Family d :=
  Finset.univ.image (fun W : (envelope T D).Component => W.variety)

theorem subset_envelope (T : Set (Point d)) (D : ℕ) : T ⊆ (envelope T D).points := by
  have hspan : Ideal.span {f : Poly d | f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D} ≤
      MvPolynomial.vanishingIdeal ℂ T := by
    apply Ideal.span_le.mpr
    intro f hf
    exact hf.1
  rw [envelope, AffineVariety.points_ofIdeal]
  intro x hx f hf
  exact hspan hf x hx

theorem envelope_components_defined (T : Set (Point d)) (D : ℕ)
    (F : AffineFamily.Family d) (hF : F ⊆ envelopeComponents T D) :
    AffineFamily.ComponentsDefinedInDegree F D := by
  refine ⟨{f : Poly d | f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D},
    (fun f hf => hf.2), ?_⟩
  intro V hV
  obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp (hF hV)
  change W.val ∈ (Ideal.span {f : Poly d |
    f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D}).minimalPrimes
  simpa only [envelope, AffineVariety.ofIdeal, Ideal.radical_minimalPrimes] using W.property

theorem envelope_family_subvariety (T : Set (Point d)) (D : ℕ)
    (F : AffineFamily.Family d) (hF : F ⊆ envelopeComponents T D) :
    (AffineFamily.locus F).Subvariety (envelope T D) := by
  apply (AffineVariety.subvariety_iff_points_subset _ _).mpr
  rw [AffineFamily.points_locus]
  intro x hx
  obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨W, _, hWV⟩ := Finset.mem_image.mp (hF hV)
  subst V
  rw [AffineVariety.points_components]
  exact Set.mem_iUnion.mpr ⟨W, hxV⟩

theorem closure_subvariety_of_subset {T : Set (Point d)} (V : AffineVariety d)
    (hT : T ⊆ V.points) : (AffineVariety.closure T).Subvariety V := by
  intro f hf x hx
  exact hT hx f hf

/-- `profiles.tex:290–300`: the same selected component degree occurs in
both Hilbert estimates. The lower constant is chosen before the point set,
envelope degree, component selection and later subset. -/
theorem envelope_hilbert_comparison (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (T T' : Set (Point d)) (D h : ℕ), 1 ≤ D →
      ∀ F : AffineFamily.Family d, F ⊆ envelopeComponents T D → AffineFamily.IsPure F h →
        T' ⊆ (AffineFamily.locus F).points →
        c * (AffineFamily.degree F : ℝ) * (D : ℝ)^h ≤ (hilbertOfSet T D : ℝ) ∧
          ∀ U : ℕ, (hilbertOfSet T' U : ℝ) ≤
            (AffineFamily.degree F : ℝ) * ((U + h).choose h : ℝ) := by
  obtain ⟨c, hc, hlower⟩ := TrackA.poly_hilbert_at_L d
  refine ⟨(c : ℝ), by exact_mod_cast hc, ?_⟩
  intro T T' D h hD F hsub hpure hT'
  have hdef := envelope_components_defined T D F hsub
  have hlo := hlower F h D hpure hD hdef
  have hmono := AffineVariety.hilbert_mono (AffineFamily.locus F) (envelope T D)
    (envelope_family_subvariety T D F hsub) D
  have henvelope := envelope_hilbert T D
  have hbound : (AffineFamily.hilbert F D : ℚ) ≤ (hilbertOfSet T D : ℚ) := by
    rw [← henvelope]
    exact_mod_cast hmono
  refine ⟨?_, ?_⟩
  · exact_mod_cast hlo.trans hbound
  · intro U
    have hm := AffineVariety.hilbert_mono (AffineVariety.closure T') (AffineFamily.locus F)
      (closure_subvariety_of_subset (AffineFamily.locus F) hT') U
    have hup := TrackA.poly_hilbert_upper F h hpure U
    have hfirst : (hilbertOfSet T' U : ℚ) ≤ (AffineFamily.hilbert F U : ℚ) := by
      exact_mod_cast hm
    exact_mod_cast hfirst.trans hup

end
end DistinctDistances.TrackD
