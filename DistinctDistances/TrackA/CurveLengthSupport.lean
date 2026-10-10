import DistinctDistances.Foundations.PointLocal
import Mathlib.RingTheory.OrderOfVanishing.Basic

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical Pointwise

/-- The cokernel length is subadditive along an exact sequence even when
the left map is not injective. -/
theorem curve_length_le_add_of_exact {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Module.length R N ≤ Module.length R M + Module.length R P := by
  have h := Module.length_eq_add_of_exact (LinearMap.range f).subtype g
    (Submodule.subtype_injective _) hg (by
      rw [LinearMap.exact_iff, Submodule.range_subtype]
      exact LinearMap.exact_iff.mp hex)
  rw [h]
  exact add_le_add (Module.length_le_of_surjective f.rangeRestrict
    (LinearMap.surjective_rangeRestrict f)) le_rfl

/-- A general upper bound suffices for the curve multiplicity argument;
no regular-element or Cohen–Macaulay equality is needed here. -/
theorem curve_length_span_product_le (R : Type*) [CommRing R] (a b : R) :
    Module.length R (R ⧸ Ideal.span {a*b}) ≤
      Module.length R (R ⧸ Ideal.span {a}) + Module.length R (R ⧸ Ideal.span {b}) := by
  have h := curve_length_le_add_of_exact (Ideal.mulQuot b (Ideal.span {a}))
    (Ideal.quotOfMul b (Ideal.span {a})) (Ideal.quotOfMul_surjective _)
    (Ideal.exact_mulQuot_quotOfMul _)
  have he : b • Ideal.span {a} = Ideal.span {b*a} := by
    have h₁ : (({b} : Set R) • Ideal.span {a}) = Ideal.span {b*a} := by
      simp [← Ideal.submodule_span_eq, Submodule.set_smul_span]
    have h₂ : (({b} : Set R) • Ideal.span {a}) = b • Ideal.span {a} :=
      Submodule.singleton_set_smul (Ideal.span {a}) b
    rwa [h₂] at h₁
  rw [he, mul_comm b a] at h
  exact h

theorem curve_length_span_pow_le (R : Type*) [CommRing R] (a : R) (j : ℕ) :
    Module.length R (R ⧸ Ideal.span {a^j}) ≤
      (j : ℕ∞) * Module.length R (R ⧸ Ideal.span {a}) := by
  induction j with
  | zero => simp [Module.length_eq_zero_iff]
  | succ j ih =>
    rw [pow_succ]
    calc
      Module.length R (R ⧸ Ideal.span {a^j*a}) ≤
          Module.length R (R ⧸ Ideal.span {a^j}) + Module.length R (R ⧸ Ideal.span {a}) :=
        curve_length_span_product_le R (a^j) a
      _ ≤ (j : ℕ∞) * Module.length R (R ⧸ Ideal.span {a}) +
          Module.length R (R ⧸ Ideal.span {a}) := add_le_add ih le_rfl
      _ = ((j+1 : ℕ) : ℕ∞) * Module.length R (R ⧸ Ideal.span {a}) := by
        simp [add_mul]

theorem curve_length_quot_sup (R : Type*) [CommRing R] (I J : Ideal R) :
    Module.length R (R ⧸ I ⊔ J) =
      Module.length (R ⧸ I) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) := by
  let e : ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃ₐ[R] (R ⧸ I ⊔ J) :=
    { __ := DoubleQuot.quotQuotEquivQuotSup I J
      commutes' := by intro r; rfl }
  rw [← e.toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem curve_carrier_quotient_length {n : ℕ} (C : AffineVariety n) (p : Point n)
    (J : Ideal (Poly n)) :
    localLengthAt (C.ideal ⊔ J) p =
      Module.length (CarrierLocalRing C p)
        (CarrierLocalRing C p ⧸ J.map ((Ideal.Quotient.mk (localizedIdeal C.ideal p)).comp
          (algebraMap (Poly n) (PointLocalRing p)))) := by
  unfold localLengthAt localizedIdeal
  rw [Ideal.map_sup, curve_length_quot_sup]
  rw [Ideal.map_map]
  rfl

theorem curve_localHilbert_carrier {n : ℕ} (C : AffineVariety n) (p : Point n) (t : ℕ) :
    C.localHilbert p t = Module.length (CarrierLocalRing C p)
      (CarrierLocalRing C p ⧸ carrierMaximalIdeal C p ^ (t+1)) := by
  rw [AffineVariety.localHilbert, curve_carrier_quotient_length]
  have he : (pointIdeal p ^ (t+1)).map
      ((Ideal.Quotient.mk (localizedIdeal C.ideal p)).comp
        (algebraMap (Poly n) (PointLocalRing p))) = carrierMaximalIdeal C p ^ (t+1) :=
    Ideal.map_pow ((Ideal.Quotient.mk (localizedIdeal C.ideal p)).comp
      (algebraMap (Poly n) (PointLocalRing p))) (pointIdeal p) (t+1)
  exact congrArg (fun J : Ideal (CarrierLocalRing C p) =>
    Module.length (CarrierLocalRing C p) (CarrierLocalRing C p ⧸ J)) he

theorem curve_cut_length_carrier {n : ℕ} (C : AffineVariety n) (p : Point n) (f : Poly n) :
    localLengthAt (C.ideal ⊔ Ideal.span {f}) p =
      Module.length (CarrierLocalRing C p)
        (CarrierLocalRing C p ⧸ Ideal.span {localClass C p f}) := by
  rw [curve_carrier_quotient_length, Ideal.map_span, Set.image_singleton]
  rfl

end
end DistinctDistances.TrackA
