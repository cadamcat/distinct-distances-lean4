import DistinctDistances.Foundations.LocalHilbert

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Ring
open MvPolynomial

/-- Evaluation extends to the original point-local ring. -/
def pointLocalEvaluation {n : ℕ} (p : Point n) : PointLocalRing p →ₐ[ℂ] ℂ :=
  IsLocalization.liftAlgHom (M := (pointIdeal p).primeCompl) (f := MvPolynomial.aeval p)
    (fun s => isUnit_iff_ne_zero.mpr (fun h =>
      s.property ((MvPolynomial.mem_vanishingIdeal_singleton_iff p s.val).mpr h)))

@[simp] theorem pointLocalEvaluation_map {n : ℕ} (p : Point n) (f : Poly n) :
    pointLocalEvaluation p (algebraMap (Poly n) (PointLocalRing p) f) =
      MvPolynomial.aeval p f := by
  exact IsLocalization.lift_eq _ f

instance pointLocalEvaluation_isLocalHom {n : ℕ} (p : Point n) :
    IsLocalHom (pointLocalEvaluation p).toRingHom := by
  constructor
  intro a ha
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (pointIdeal p).primeCompl a
  apply (IsLocalization.AtPrime.isUnit_mk'_iff (PointLocalRing p) (pointIdeal p) r s).mpr
  intro hr
  have hrzero : MvPolynomial.aeval p r = 0 :=
    (MvPolynomial.mem_vanishingIdeal_singleton_iff p r).mp hr
  have hsnonzero : MvPolynomial.aeval p s.val ≠ 0 := by
    intro h
    exact s.property ((MvPolynomial.mem_vanishingIdeal_singleton_iff p s.val).mpr h)
  have he := congrArg (pointLocalEvaluation p)
    (IsLocalization.mk'_spec (PointLocalRing p) r s)
  simp only [map_mul, pointLocalEvaluation_map, hrzero] at he
  exact ha.ne_zero ((mul_eq_zero.mp he).resolve_right hsnonzero)

/-- Original ambient homogeneous coordinates in the affine chart. -/
def chartAmbientCoordinate {n : ℕ} (j k : Fin (n+1)) : Poly n :=
  Fin.insertNth (α := fun _ => Poly n) j 1 MvPolynomial.X k

@[simp] theorem chartAmbientCoordinate_eval {n : ℕ} (j k : Fin (n+1))
    (p : ProjectivePoint (n+1)) (hj : p.rep j ≠ 0) :
    MvPolynomial.aeval (chartCoordinates j p) (chartAmbientCoordinate j k) =
      p.rep k / p.rep j := by
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨a, rfl⟩
  · simp [chartAmbientCoordinate, hj]
  · simp [chartAmbientCoordinate, chartCoordinates]

theorem chartAmbientCoordinate_isUnit {n : ℕ} (i j : Fin (n+1))
    (p : ProjectivePoint (n+1)) (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0) :
    IsUnit (algebraMap (Poly n) (PointLocalRing (chartCoordinates j p))
      (chartAmbientCoordinate j i)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (PointLocalRing (chartCoordinates j p)) (pointIdeal (chartCoordinates j p)) _).mpr
  intro h
  have hz := (MvPolynomial.mem_vanishingIdeal_singleton_iff
    (chartCoordinates j p) (chartAmbientCoordinate j i)).mp h
  rw [chartAmbientCoordinate_eval j i p hj] at hz
  exact div_ne_zero hi hj hz

/-- Rational coordinate substitution between two original affine charts,
with the overlap denominator inverted in the original local ring. -/
def chartAmbientPullback {n : ℕ} (i j : Fin (n+1)) (p : ProjectivePoint (n+1)) :
    Poly n →ₐ[ℂ] PointLocalRing (chartCoordinates j p) :=
  MvPolynomial.aeval (fun k =>
    algebraMap (Poly n) (PointLocalRing (chartCoordinates j p))
      (chartAmbientCoordinate j (i.succAbove k)) *
      (algebraMap (Poly n) (PointLocalRing (chartCoordinates j p))
        (chartAmbientCoordinate j i))⁻¹ʳ)

theorem chartAmbientPullback_eval {n : ℕ} (i j : Fin (n+1))
    (p : ProjectivePoint (n+1)) (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0)
    (f : Poly n) :
    pointLocalEvaluation (chartCoordinates j p) (chartAmbientPullback i j p f) =
      MvPolynomial.aeval (chartCoordinates i p) f := by
  suffices he : (pointLocalEvaluation (chartCoordinates j p)).comp
      (chartAmbientPullback i j p) = MvPolynomial.aeval (chartCoordinates i p) from
    congrArg (fun h : Poly n →ₐ[ℂ] ℂ => h f) he
  ext k
  simp only [AlgHom.comp_apply, chartAmbientPullback, MvPolynomial.aeval_X, map_mul]
  rw [pointLocalEvaluation_map, chartAmbientCoordinate_eval j (i.succAbove k) p hj]
  let d := algebraMap (Poly n) (PointLocalRing (chartCoordinates j p))
    (chartAmbientCoordinate j i)
  have hd := chartAmbientCoordinate_isUnit i j p hi hj
  have hinv : pointLocalEvaluation (chartCoordinates j p) d⁻¹ʳ =
      (p.rep i / p.rep j)⁻¹ := by
    have he := congrArg (pointLocalEvaluation (chartCoordinates j p)) (Ring.mul_inverse_cancel d hd)
    simp only [map_mul, map_one] at he
    have hed : pointLocalEvaluation (chartCoordinates j p) d = p.rep i / p.rep j := by
      simpa only [d, pointLocalEvaluation_map] using chartAmbientCoordinate_eval j i p hj
    rw [hed] at he
    exact eq_inv_of_mul_eq_one_right he
  rw [hinv]
  change p.rep (i.succAbove k) / p.rep j * (p.rep i / p.rep j)⁻¹ =
    p.rep (i.succAbove k) / p.rep i
  field_simp

def chartPointLocalHom {n : ℕ} (i j : Fin (n+1)) (p : ProjectivePoint (n+1))
    (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0) :
    PointLocalRing (chartCoordinates i p) →ₐ[ℂ] PointLocalRing (chartCoordinates j p) :=
  IsLocalization.liftAlgHom (M := (pointIdeal (chartCoordinates i p)).primeCompl)
    (f := chartAmbientPullback i j p) (fun s =>
      isUnit_of_map_unit (pointLocalEvaluation (chartCoordinates j p)).toRingHom
        (chartAmbientPullback i j p s.val)
        (isUnit_iff_ne_zero.mpr (by
          change pointLocalEvaluation (chartCoordinates j p)
            (chartAmbientPullback i j p s.val) ≠ 0
          rw [chartAmbientPullback_eval i j p hi hj]
          intro h
          exact s.property ((MvPolynomial.mem_vanishingIdeal_singleton_iff
            (chartCoordinates i p) s.val).mpr h))))

@[simp] theorem chartPointLocalHom_map {n : ℕ} (i j : Fin (n+1))
    (p : ProjectivePoint (n+1)) (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0) (f : Poly n) :
    chartPointLocalHom i j p hi hj
      (algebraMap (Poly n) (PointLocalRing (chartCoordinates i p)) f) =
      chartAmbientPullback i j p f := by
  exact IsLocalization.lift_eq _ f

/-- Ring inverse commutes with an algebra map on an actual unit. -/
theorem algHom_map_ring_inverse {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (a : A) (ha : IsUnit a) :
    f a⁻¹ʳ = (f a)⁻¹ʳ := by
  obtain ⟨u, rfl⟩ := ha
  change f (u : A)⁻¹ʳ = ((Units.map f.toMonoidHom u : Bˣ) : B)⁻¹ʳ
  rw [Ring.inverse_unit, Ring.inverse_unit]
  change (↑(Units.map f.toMonoidHom u⁻¹) : B) =
    (↑((Units.map f.toMonoidHom u)⁻¹) : B)
  rw [map_inv]

/-- The coordinate formula includes the coordinate set to one in the chart. -/
theorem chartPointLocalHom_coordinate {n : ℕ} (i j : Fin (n+1))
    (p : ProjectivePoint (n+1)) (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0)
    (k : Fin (n+1)) :
    chartPointLocalHom i j p hi hj
      (algebraMap (Poly n) (PointLocalRing (chartCoordinates i p))
        (chartAmbientCoordinate i k)) =
      algebraMap (Poly n) (PointLocalRing (chartCoordinates j p))
        (chartAmbientCoordinate j k) *
        (algebraMap (Poly n) (PointLocalRing (chartCoordinates j p))
          (chartAmbientCoordinate j i))⁻¹ʳ := by
  rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨a, hk⟩
  · subst k
    simp only [chartAmbientCoordinate, Fin.insertNth_apply_same, map_one]
    exact (Ring.mul_inverse_cancel _ (chartAmbientCoordinate_isUnit i j p hi hj)).symm
  · subst k
    rw [chartPointLocalHom_map]
    simp [chartAmbientPullback, chartAmbientCoordinate]

/-- The two original rational chart maps are inverse on the ambient local rings. -/
theorem chartPointLocalHom_comp {n : ℕ} (i j : Fin (n+1))
    (p : ProjectivePoint (n+1)) (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0) :
    (chartPointLocalHom j i p hj hi).comp (chartPointLocalHom i j p hi hj) =
      AlgHom.id ℂ (PointLocalRing (chartCoordinates i p)) := by
  apply IsLocalization.algHom_ext (pointIdeal (chartCoordinates i p)).primeCompl
  ext k
  change chartPointLocalHom j i p hj hi
    (chartPointLocalHom i j p hi hj
      (algebraMap (Poly n) (PointLocalRing (chartCoordinates i p)) (MvPolynomial.X k))) =
    algebraMap (Poly n) (PointLocalRing (chartCoordinates i p)) (MvPolynomial.X k)
  have hX : MvPolynomial.X k = chartAmbientCoordinate i (i.succAbove k) := by
    simp [chartAmbientCoordinate]
  rw [hX, chartPointLocalHom_coordinate, map_mul,
    algHom_map_ring_inverse _ _ (chartAmbientCoordinate_isUnit i j p hi hj),
    chartPointLocalHom_coordinate, chartPointLocalHom_coordinate]
  have hself : chartAmbientCoordinate i i = 1 := by simp [chartAmbientCoordinate]
  rw [hself, map_one, one_mul]
  rw [Ring.inverse_inverse (chartAmbientCoordinate_isUnit j i p hj hi),
    Ring.inverse_mul_cancel_right _ _ (chartAmbientCoordinate_isUnit j i p hj hi)]

/-- Ambient local-ring equivalence on the actual overlap of two charts. -/
def chartPointLocalEquiv {n : ℕ} (i j : Fin (n+1)) (p : ProjectivePoint (n+1))
    (hi : p.rep i ≠ 0) (hj : p.rep j ≠ 0) :
    PointLocalRing (chartCoordinates i p) ≃ₐ[ℂ] PointLocalRing (chartCoordinates j p) :=
  AlgEquiv.ofAlgHom (chartPointLocalHom i j p hi hj) (chartPointLocalHom j i p hj hi)
    (chartPointLocalHom_comp j i p hj hi) (chartPointLocalHom_comp i j p hi hj)

end
end DistinctDistances.TrackA
