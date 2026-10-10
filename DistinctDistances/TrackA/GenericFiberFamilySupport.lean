import DistinctDistances.TrackA.GenericFiberIsolationSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- The literal selected union is finite, and its distinct points are
counted by the sum of component degrees. The empty family is included. -/
theorem affineFamily_genericFiber_finset {n k : ℕ} (F : AffineFamily.Family n)
    (hF : AffineFamily.IsPure F k) (φ : AffineProjection n k)
    (hnorm : ∀ V ∈ F, FiniteAffineProjection φ V ∧ ∃ r : ℕ,
      (r : ℚ) = V.degree ∧ φ.GenericallyFiniteOfDegree V r)
    (K : Type*) [Field K] [Algebra ℂ K] [IsAlgClosed K]
    (t : Fin k → K) (ht : AlgebraicIndependent ℂ t) :
    ∃ S : Finset (FieldPoint n K),
      (∀ x, x ∈ S ↔ ∃ V ∈ F, x ∈ affineFiberOver V φ t) ∧
        (S.card : ℚ) = AffineFamily.degree F := by
  have hfinite (V : AffineVariety n) (hV : V ∈ F) :
      (affineFiberOver V φ t).Finite ∧
        ((affineFiberOver V φ t).ncard : ℚ) = V.degree := by
    obtain ⟨hf, r, hdegree, hr⟩ := hnorm V hV
    obtain ⟨hfin, hcount⟩ := affineFiberOver_generic_count V (hF V hV).1
      (hF V hV).2 φ hf hr K t ht
    exact ⟨hfin, by rw [hcount, hdegree]⟩
  let sheets (V : AffineVariety n) : Finset (FieldPoint n K) :=
    if hV : V ∈ F then (hfinite V hV).1.toFinset else ∅
  have hsheets (V : AffineVariety n) (hV : V ∈ F) (x : FieldPoint n K) :
      x ∈ sheets V ↔ x ∈ affineFiberOver V φ t := by
    simp only [sheets, dif_pos hV, Set.Finite.mem_toFinset]
  have hdisjoint : (F : Set (AffineVariety n)).PairwiseDisjoint sheets := by
    intro V hV W hW hne
    apply Finset.disjoint_left.mpr
    intro x hxV hxW
    exact Set.disjoint_left.mp (affineFiberOver_disjoint V W (hF V hV).1
      (hF W hW).1 hne φ (hnorm V hV).1 (hnorm W hW).1 K t ht)
      ((hsheets V hV x).mp hxV) ((hsheets W hW x).mp hxW)
  refine ⟨F.biUnion sheets, ?_, ?_⟩
  · intro x
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨V, hV, hx⟩
      exact ⟨V, hV, (hsheets V hV x).mp hx⟩
    · rintro ⟨V, hV, hx⟩
      exact ⟨V, hV, (hsheets V hV x).mpr hx⟩
  · rw [Finset.card_biUnion hdisjoint, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro V hV
    simpa only [sheets, dif_pos hV,
      Set.ncard_eq_toFinset_card _ (hfinite V hV).1] using (hfinite V hV).2

/-- Every original component contains the ideal of its reduced union. -/
theorem affineFamily_locus_ideal_le {n : ℕ} (F : AffineFamily.Family n)
    (V : AffineVariety n) (hV : V ∈ F) : (AffineFamily.locus F).ideal ≤ V.ideal := by
  change (⨅ W ∈ F, W.ideal).radical ≤ V.ideal
  calc
    _ ≤ V.ideal.radical := Ideal.radical_mono (iInf₂_le V hV)
    _ = V.ideal := V.isRadical.radical

/-- Actual coordinate evaluation on the selected sheets is a complex
algebra map on the reduced union, preserving the original base coordinates. -/
def affineFamilyFiberEvaluation {n k r : ℕ} (F : AffineFamily.Family n)
    (φ : AffineProjection n k) (K : Type*) [Field K] [Algebra ℂ K]
    (t : Fin k → K) (points : Fin r → FieldPoint n K)
    (hp : ∀ j, ∃ V ∈ F, points j ∈ affineFiberOver V φ t) :
    (Poly n ⧸ (AffineFamily.locus F).ideal) →ₐ[ℂ] (Fin r → K) :=
  AlgHom.pi (fun j => Ideal.Quotient.liftₐ (AffineFamily.locus F).ideal
    (MvPolynomial.aeval (R := ℂ) (points j)) (by
      intro f hf
      obtain ⟨V, hV, hx⟩ := hp j
      exact hx.1 f (affineFamily_locus_ideal_le F V hV hf)))

theorem affineFamilyFiberEvaluation_coordinates {n k r : ℕ} (F : AffineFamily.Family n)
    (φ : AffineProjection n k) (K : Type*) [Field K] [Algebra ℂ K]
    (t : Fin k → K) (points : Fin r → FieldPoint n K)
    (hp : ∀ j, ∃ V ∈ F, points j ∈ affineFiberOver V φ t)
    (f : Poly n) (j : Fin r) :
    affineFamilyFiberEvaluation F φ K t points hp
      (Ideal.Quotient.mk (AffineFamily.locus F).ideal f) j =
        MvPolynomial.eval₂ (algebraMap ℂ K) (points j) f := by
  simp only [affineFamilyFiberEvaluation, AlgHom.pi_apply,
    Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

theorem affineFamilyFiberEvaluation_base {n k r : ℕ} (F : AffineFamily.Family n)
    (φ : AffineProjection n k) (K : Type*) [Field K] [Algebra ℂ K]
    (t : Fin k → K) (points : Fin r → FieldPoint n K)
    (hp : ∀ j, ∃ V ∈ F, points j ∈ affineFiberOver V φ t) (i : Fin k) :
    affineFamilyFiberEvaluation F φ K t points hp
      (Ideal.Quotient.mk (AffineFamily.locus F).ideal (φ.pullback (MvPolynomial.X i))) =
        fun _ => t i := by
  funext j
  rw [affineFamilyFiberEvaluation_coordinates]
  obtain ⟨V, hV, hx⟩ := hp j
  exact hx.2 i

end
end DistinctDistances.TrackA
