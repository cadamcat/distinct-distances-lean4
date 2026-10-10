import DistinctDistances.TrackA.ChartAmbientSupport
import DistinctDistances.TrackA.ChartIdealSupport
import DistinctDistances.Foundations.GradedEvaluation

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Ring
open MvPolynomial IsLocalRing

set_option backward.isDefEq.respectTransparency false in
/-- An original homogeneous equation changes by the actual unit denominator. -/
theorem chartPointLocalHom_homogeneous {n D : ℕ} (i j : Fin (n+1))
    (p : ProjectivePoint (n+1)) (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0)
    (f : Poly (n+1)) (hf : f.IsHomogeneous D) :
    chartPointLocalHom i j p hi hj
      (algebraMap (Poly n) (PointLocalRing (chartCoordinates i p)) (chartPullback i f)) =
      (algebraMap (Poly n) (PointLocalRing (chartCoordinates j p))
        (chartAmbientCoordinate j i))⁻¹ʳ^D *
      algebraMap (Poly n) (PointLocalRing (chartCoordinates j p)) (chartPullback j f) := by
  let a : Fin (n+1) → PointLocalRing (chartCoordinates j p) := fun k =>
    algebraMap (Poly n) (PointLocalRing (chartCoordinates j p)) (chartAmbientCoordinate j k)
  let c := (a i)⁻¹ʳ
  have hcoords : (fun k : Fin (n+1) => chartAmbientPullback i j p
      (Fin.insertNth (α := fun _ => Poly n) i (MvPolynomial.C 1) MvPolynomial.X k)) =
      (fun k => c * a k) := by
    funext k
    rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨l, hk⟩
    · subst k
      simp only [Fin.insertNth_apply_same, MvPolynomial.C_1, map_one]
      exact (Ring.inverse_mul_cancel _ (chartAmbientCoordinate_isUnit i j p hi hj)).symm
    · subst k
      simp only [Fin.insertNth_apply_succAbove, chartAmbientPullback, MvPolynomial.aeval_X]
      exact mul_comm _ _
  have hb : algebraMap (Poly n) (PointLocalRing (chartCoordinates j p)) (chartPullback j f) =
      MvPolynomial.aeval a f := by
    change (Algebra.algHom ℂ (Poly n) (PointLocalRing (chartCoordinates j p)))
      (MvPolynomial.aeval (Fin.insertNth j (MvPolynomial.C 1) MvPolynomial.X) f) = _
    rw [MvPolynomial.comp_aeval_apply]
    congr 1
  rw [chartPointLocalHom_map]
  change MvPolynomial.aeval _
    (MvPolynomial.aeval (Fin.insertNth i (MvPolynomial.C 1) MvPolynomial.X) f) = _
  rw [MvPolynomial.comp_aeval_apply]
  change MvPolynomial.aeval (fun k => chartAmbientPullback i j p
      (Fin.insertNth (α := fun _ => Poly n) i (MvPolynomial.C 1) MvPolynomial.X k)) f = _
  rw [hcoords, hb]
  have hscale := GenericFiber.aeval_scale_of_isWeightedHomogeneous hf a c
  simpa only [Pi.one_apply, pow_one] using hscale

/-- The original reduced carrier ideal maps into the other chart's actual
localized ideal. Arbitrary equations are decomposed into their original
homogeneous components. -/
theorem chartPointLocalHom_carrier_le {n : ℕ} (V : ProjectiveVariety (n+1))
    (i j : Fin (n+1)) (p : ProjectivePoint (n+1))
    (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0) :
    (localizedIdeal (V.affineChart i).ideal (chartCoordinates i p)).map
        (chartPointLocalHom i j p hi hj).toRingHom ≤
      localizedIdeal (V.affineChart j).ideal (chartCoordinates j p) := by
  have hgen (g : Poly (n+1)) (hg : g ∈ V.ideal) :
      chartPointLocalHom i j p hi hj
        (algebraMap (Poly n) (PointLocalRing (chartCoordinates i p)) (chartPullback i g)) ∈
      localizedIdeal (V.affineChart j).ideal (chartCoordinates j p) := by
    rw [← MvPolynomial.sum_homogeneousComponent g, map_sum, map_sum, map_sum]
    apply Ideal.sum_mem
    intro d hd
    rw [chartPointLocalHom_homogeneous i j p hi hj _
      (MvPolynomial.homogeneousComponent_isHomogeneous d g)]
    apply Ideal.mul_mem_left
    apply Ideal.mem_map_of_mem
    apply Ideal.le_radical
    exact Ideal.mem_map_of_mem _
      (MvPolynomial.homogeneousComponent_mem_of_mem V.isHomogeneous hg d)
  unfold localizedIdeal
  rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro f hf
  rw [affineChart_ideal_exact] at hf
  have hsurj : Function.Surjective (chartPullback i).toRingHom := fun g =>
    ⟨MvPolynomial.rename i.succAbove g, chartPullback_rename i g⟩
  obtain ⟨g, hg, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (chartPullback i).toRingHom hsurj).mp hf
  exact hgen g hg

/-- The original ambient local equivalence transports the literal reduced
carrier ideals in both directions. -/
theorem chartPointLocalEquiv_carrier {n : ℕ} (V : ProjectiveVariety (n+1))
    (i j : Fin (n+1)) (p : ProjectivePoint (n+1))
    (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0) :
    (localizedIdeal (V.affineChart i).ideal (chartCoordinates i p)).map
        (chartPointLocalEquiv i j p hi hj).toRingHom =
      localizedIdeal (V.affineChart j).ideal (chartCoordinates j p) := by
  apply le_antisymm (chartPointLocalHom_carrier_le V i j p hi hj)
  intro a ha
  let e := chartPointLocalEquiv i j p hi hj
  have hb : e.symm a ∈ localizedIdeal (V.affineChart i).ideal (chartCoordinates i p) :=
    chartPointLocalHom_carrier_le V j i p hj hi
      (Ideal.mem_map_of_mem e.symm.toRingHom ha)
  have hc := Ideal.mem_map_of_mem e.toRingHom hb
  change e (e.symm a) ∈
    (localizedIdeal (V.affineChart i).ideal (chartCoordinates i p)).map e.toRingHom at hc
  change a ∈
    (localizedIdeal (V.affineChart i).ideal (chartCoordinates i p)).map e.toRingHom
  simpa only [AlgEquiv.apply_symm_apply] using hc

/-- Both original point-power filtrations are transported by the actual
chart equivalence, together with the original carrier ideals. -/
theorem chartPointLocalEquiv_hilbert_ideal {n : ℕ} (V : ProjectiveVariety (n+1))
    (i j : Fin (n+1)) (p : ProjectivePoint (n+1))
    (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0) (t : ℕ) :
    (localizedIdeal ((V.affineChart i).ideal ⊔ pointIdeal (chartCoordinates i p)^(t+1))
      (chartCoordinates i p)).map (chartPointLocalEquiv i j p hi hj).toRingHom =
      localizedIdeal ((V.affineChart j).ideal ⊔ pointIdeal (chartCoordinates j p)^(t+1))
        (chartCoordinates j p) := by
  have hexpr (k : Fin (n+1)) :
      localizedIdeal ((V.affineChart k).ideal ⊔ pointIdeal (chartCoordinates k p)^(t+1))
        (chartCoordinates k p) =
      localizedIdeal (V.affineChart k).ideal (chartCoordinates k p) ⊔
        maximalIdeal (PointLocalRing (chartCoordinates k p))^(t+1) := by
    unfold localizedIdeal
    rw [Ideal.map_sup, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal (chartCoordinates k p))
        (PointLocalRing (chartCoordinates k p))]
  rw [hexpr i, hexpr j, Ideal.map_sup, Ideal.map_pow,
    chartPointLocalEquiv_carrier V i j p hi hj]
  have hmax : (maximalIdeal (PointLocalRing (chartCoordinates i p))).map
      (chartPointLocalEquiv i j p hi hj).toRingHom =
      maximalIdeal (PointLocalRing (chartCoordinates j p)) :=
    IsLocalRing.map_ringEquiv_maximalIdeal (chartPointLocalEquiv i j p hi hj).toRingEquiv
  rw [hmax]

/-- Every actual original local Hilbert length is independent of the affine
chart containing the original projective point. -/
theorem affineChart_localHilbert_eq {n : ℕ} (V : ProjectiveVariety (n+1))
    (i j : Fin (n+1)) (p : ProjectivePoint (n+1))
    (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0) (t : ℕ) :
    (V.affineChart i).localHilbert (chartCoordinates i p) t =
      (V.affineChart j).localHilbert (chartCoordinates j p) t := by
  let e := Ideal.quotientEquivAlg _ _ (chartPointLocalEquiv i j p hi hj)
    (chartPointLocalEquiv_hilbert_ideal V i j p hi hj t).symm
  unfold AffineVariety.localHilbert localLengthAt
  rw [point_local_length_eq_complex_length (chartCoordinates i p),
    point_local_length_eq_complex_length (chartCoordinates j p)]
  exact e.toLinearEquiv.length_eq

end
end DistinctDistances.TrackA
