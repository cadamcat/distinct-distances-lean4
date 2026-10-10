import DistinctDistances.TrackA.AffineMultiplicityBudgetSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
open OAI.QuarticPowerFree

theorem weighted_cut_core {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (k : ℕ) (hdim : V.dimension = k+1) (f : Poly n) (hf : f ∉ V.ideal)
    (F : AffineFamily.Family n)
    (hF : ∀ W ∈ F, W.IsComponentOf (V.ideal ⊔ Ideal.span {f})) :
    ∃ m : AffineVariety n → ℕ,
      (∀ W ∈ F, ∀ hW : W.IsIrreducible,
        componentLength (V.ideal ⊔ Ideal.span {f}) W hW = (m W : ℕ∞)) ∧
      (∑ W ∈ F, (m W : ℚ) * W.degree) ≤ (f.totalDegree : ℚ) * V.degree := by
  letI : V.ideal.IsPrime := hV
  let I := V.ideal ⊔ Ideal.span {f}
  let Q : F → Ideal (Poly n) := fun W => W.val.ideal
  have hQ : ∀ W : F, Q W ∈ I.minimalPrimes := fun W => hF W.val W.property
  have hQinj : Function.Injective Q := by
    intro W Z h
    exact Subtype.ext (AffineVariety.ext h)
  have hchild : ∀ W : F, affineDimension (Q W) = k := by
    intro W
    letI : (Q W).IsPrime := (hQ W).isPrime
    exact proper_cut_component_dimension V.ideal (Q W) f hf (hQ W) hdim
  have hcut := proper_cut_hilbert_polynomial V.ideal f hf
    (coordinateHilbert V.ideal) (coordinateHilbert I)
    ((coordinateHilbert_eventually V.ideal).mono (fun _ h => h.symm))
    ((coordinateHilbert_eventually I).mono (fun _ h => h.symm)) k hdim.le
  obtain ⟨m₀, hm₀, hbudget⟩ := affine_component_multiplicity_sum I k hcut.1 Q hQ hQinj hchild
  let m : AffineVariety n → ℕ := fun W => if hW : W ∈ F then m₀ ⟨W,hW⟩ else 0
  refine ⟨m, ?_, ?_⟩
  · intro W hWF hW
    have hlen := hm₀ ⟨W,hWF⟩ hW
    simpa only [m, dite_eq_left hWF, componentLength, Q, I] using hlen
  · have hsum : (∑ W ∈ F, (m W : ℚ) * W.degree) =
        ∑ W : F, (m₀ W : ℚ) * affineDegree (Q W) := by
      rw [← Finset.sum_coe_sort F]
      apply Finset.sum_congr rfl
      intro W hW
      simp only [m, dite_eq_left W.property, Q]
    rw [hsum]
    calc
      _ ≤ (k.factorial : ℚ) * (coordinateHilbert I).coeff k := hbudget
      _ ≤ (k.factorial : ℚ) *
          ((f.totalDegree : ℚ) * (k+1) * (coordinateHilbert V.ideal).coeff (k+1)) :=
        mul_le_mul_of_nonneg_left hcut.2 (Nat.cast_nonneg _)
      _ = (f.totalDegree : ℚ) * V.degree := by
        change _ = (f.totalDegree : ℚ) * affineDegree V.ideal
        rw [affineDegree, show affineDimension V.ideal = k+1 from hdim, Nat.factorial_succ]
        push_cast
        ring

end
end DistinctDistances.TrackA
