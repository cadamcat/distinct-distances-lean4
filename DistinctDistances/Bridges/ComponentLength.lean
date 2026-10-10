import DistinctDistances.TrackA.Definitions

/-! The length of a localized quotient is positive when its ideal lies in the local prime. -/

namespace DistinctDistances.Bridges

noncomputable section

theorem componentLength_pos {n : ℕ} (I : Ideal (Poly n)) (V : AffineVariety n)
    (hV : V.IsIrreducible) (hI : I ≤ V.ideal) : 0 < TrackA.componentLength I V hV := by
  let : V.ideal.IsPrime := hV
  let A := Localization.AtPrime V.ideal
  let J := I.map (algebraMap (Poly n) A)
  have hprime : (V.ideal.map (algebraMap (Poly n) A)).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime (q := V.ideal) (S := A) le_rfl
  have hne : J ≠ ⊤ := by
    intro he
    exact hprime.ne_top (top_unique (he ▸ Ideal.map_mono hI))
  let : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  change 0 < Module.length A (A ⧸ J)
  exact Module.length_pos

end
end DistinctDistances.Bridges
