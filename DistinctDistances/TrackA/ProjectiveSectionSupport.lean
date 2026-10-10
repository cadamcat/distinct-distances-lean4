import DistinctDistances.TrackA.HilbertUpperBaseSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev NonzeroConePoint {n : ℕ} (V : ProjectiveVariety n) :=
  {x : Point n // x ≠ 0 ∧ x ∈ V.affineCone.points}

/-- Degree-D algebraic sections, represented by homogeneous functions on
the nonzero cone. At each point a homogeneous denominator is nonzero and
a homogeneous numerator represents the function throughout that patch. -/
def IsRegularHomogeneousSection {n : ℕ} (V : ProjectiveVariety n) (D : ℕ)
    (s : NonzeroConePoint V → ℂ) : Prop :=
  ∀ x : NonzeroConePoint V, ∃ (q : ℕ) (a b : Poly n), a.IsHomogeneous (q+D) ∧ b.IsHomogeneous q ∧
    MvPolynomial.eval x.val b ≠ 0 ∧ ∀ y : NonzeroConePoint V,
      MvPolynomial.eval y.val b ≠ 0 → s y * MvPolynomial.eval y.val b = MvPolynomial.eval y.val a

/-- The local homogeneous-fraction definition is closed under the actual
pointwise vector-space operations; finiteness is a separate theorem. -/
def regularSectionSpace {n : ℕ} (V : ProjectiveVariety n) (D : ℕ) :
    Submodule ℂ (NonzeroConePoint V → ℂ) where
  carrier := {s | IsRegularHomogeneousSection V D s}
  zero_mem' := by
    change IsRegularHomogeneousSection V D 0
    unfold IsRegularHomogeneousSection
    intro x
    refine ⟨0, 0, 1, MvPolynomial.isHomogeneous_zero (Fin n) ℂ _,
      MvPolynomial.isHomogeneous_one _ _, by simp, ?_⟩
    intro y hy
    simp
  add_mem' := by
    intro s t hs ht
    change IsRegularHomogeneousSection V D (s+t)
    change IsRegularHomogeneousSection V D s at hs
    change IsRegularHomogeneousSection V D t at ht
    unfold IsRegularHomogeneousSection at *
    intro x
    obtain ⟨q, a, b, ha, hb, hbx, he⟩ := hs x
    obtain ⟨r, c, d, hc, hd, hdx, hf⟩ := ht x
    have had : (a*d).IsHomogeneous (q+r+D) := by
      convert ha.mul hd using 1 <;> omega
    have hcb : (c*b).IsHomogeneous (q+r+D) := by
      convert hc.mul hb using 1 <;> omega
    refine ⟨q+r, a*d+c*b, b*d, had.add hcb, hb.mul hd,
      by simpa only [map_mul] using mul_ne_zero hbx hdx, ?_⟩
    intro y hy
    have hparts : MvPolynomial.eval y.val b ≠ 0 ∧ MvPolynomial.eval y.val d ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using hy
    simp only [Pi.add_apply, map_mul, map_add]
    calc
      (s y+t y) * (MvPolynomial.eval y.val b * MvPolynomial.eval y.val d) =
          (s y * MvPolynomial.eval y.val b) * MvPolynomial.eval y.val d +
          (t y * MvPolynomial.eval y.val d) * MvPolynomial.eval y.val b := by ring
      _ = _ := by rw [he y hparts.1, hf y hparts.2]
  smul_mem' := by
    intro z s hs
    change IsRegularHomogeneousSection V D (z • s)
    change IsRegularHomogeneousSection V D s at hs
    unfold IsRegularHomogeneousSection at *
    intro x
    obtain ⟨q, a, b, ha, hb, hbx, he⟩ := hs x
    refine ⟨q, z • a, b, ?_, hb, hbx, ?_⟩
    · exact (MvPolynomial.homogeneousSubmodule (Fin n) ℂ (q+D)).smul_mem z ha
    · intro y hy
      rw [Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eq_C_mul, map_mul,
        MvPolynomial.eval_C, mul_assoc, he y hy]

/-- The actual coordinate quotient evaluates on the nonzero cone. -/
def coneEvaluation {n : ℕ} (V : ProjectiveVariety n) :
    (Poly n ⧸ V.ideal) →ₗ[ℂ] (NonzeroConePoint V → ℂ) :=
  LinearMap.pi (fun x =>
    (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval x.val)
      (fun f hf => x.property.2 f hf)).toLinearMap)

theorem coneEvaluation_mk {n : ℕ} (V : ProjectiveVariety n) (p : Poly n)
    (x : NonzeroConePoint V) :
    coneEvaluation V (Ideal.Quotient.mk V.ideal p) x = MvPolynomial.eval x.val p := by
  let ev : (Poly n ⧸ V.ideal) →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval x.val) (fun f hf => x.property.2 f hf)
  have hcomp : ev.comp (Ideal.Quotient.mkₐ ℂ V.ideal) = MvPolynomial.aeval x.val :=
    Ideal.Quotient.liftₐ_comp _ _ _
  change (ev.comp (Ideal.Quotient.mkₐ ℂ V.ideal)) p = _
  rw [hcomp, MvPolynomial.aeval_eq_eval]

/-- Reduced saturated ideal recovery makes nonzero-cone evaluation injective. -/
theorem coneEvaluation_injective {n : ℕ} (V : ProjectiveVariety n) :
    Function.Injective (coneEvaluation V) := by
  intro u v huv
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective v
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem p q).mpr
  rw [← V.vanishingIdeal_points]
  change p-q ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives V.points)
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro x hx
  obtain ⟨hx0, hxV⟩ := hx
  have hxCone := (ProjectiveVariety.mem_points_mk_iff V x hx0).mp hxV
  let y : NonzeroConePoint V := ⟨x, hx0, hxCone⟩
  have he := congrFun huv y
  rw [coneEvaluation_mk, coneEvaluation_mk] at he
  simpa only [map_sub, MvPolynomial.aeval_eq_eval] using sub_eq_zero.mpr he

/-- Every homogeneous polynomial restriction is a regular section, with
denominator one on every patch. -/
theorem polynomial_restriction_isRegular {n : ℕ} (V : ProjectiveVariety n) (D : ℕ)
    (u : V.restrictionSpace D) :
    coneEvaluation V u.val ∈ regularSectionSpace V D := by
  obtain ⟨p, hp, hpu⟩ := u.property
  have hhom : p.IsHomogeneous D := hp
  change IsRegularHomogeneousSection V D (coneEvaluation V u.val)
  unfold IsRegularHomogeneousSection
  intro x
  refine ⟨0, p, 1, by simpa only [Nat.zero_add] using hhom,
    MvPolynomial.isHomogeneous_one _ _, by simp, ?_⟩
  intro y hy
  rw [← hpu]
  change coneEvaluation V (Ideal.Quotient.mk V.ideal p) y * MvPolynomial.eval y.val 1 = _
  simpa only [map_one, mul_one] using coneEvaluation_mk V p y

/-- The paper's polynomial-restriction injection into genuine locally
regular homogeneous sections, without any finite-dimensionality premise. -/
def polynomialSectionMap {n : ℕ} (V : ProjectiveVariety n) (D : ℕ) :
    V.restrictionSpace D →ₗ[ℂ] regularSectionSpace V D :=
  ((coneEvaluation V).comp (V.restrictionSpace D).subtype).codRestrict
    (regularSectionSpace V D) (polynomial_restriction_isRegular V D)

theorem polynomialSectionMap_injective {n : ℕ} (V : ProjectiveVariety n) (D : ℕ) :
    Function.Injective (polynomialSectionMap V D) := by
  intro u v huv
  apply Subtype.ext
  exact coneEvaluation_injective V (congrArg Subtype.val huv)

/-- The rank comparison uses actual section-space finiteness; finrank zero
for an infinite-dimensional space is never used as a section bound. -/
theorem hilbert_le_regularSection_finrank {n : ℕ} (V : ProjectiveVariety n) (D : ℕ)
    [Module.Finite ℂ (regularSectionSpace V D)] :
    V.hilbert D ≤ Module.finrank ℂ (regularSectionSpace V D) :=
  LinearMap.finrank_le_finrank_of_injective (polynomialSectionMap_injective V D)

/-- Nonzero scalar multiplication preserves the actual nonzero cone. -/
def nonzeroConeScale {n : ℕ} (V : ProjectiveVariety n) (c : ℂ) (hc : c ≠ 0)
    (x : NonzeroConePoint V) : NonzeroConePoint V :=
  ⟨c • x.val, smul_ne_zero hc x.property.1, cone_smul_mem V x.val x.property.2 c⟩

/-- Local homogeneous fractions force the expected degree-D scaling rule. -/
theorem regularSection_scaling {n : ℕ} (V : ProjectiveVariety n) (D : ℕ)
    (s : regularSectionSpace V D) (x : NonzeroConePoint V) (c : ℂ) (hc : c ≠ 0) :
    s.val (nonzeroConeScale V c hc x) = c^D * s.val x := by
  have hs : IsRegularHomogeneousSection V D s.val := s.property
  obtain ⟨q, a, b, ha, hb, hbx, he⟩ := hs x
  let y := nonzeroConeScale V c hc x
  have hby : MvPolynomial.eval y.val b ≠ 0 := by
    change MvPolynomial.eval (c • x.val) b ≠ 0
    rw [Bridges.homogeneous_eval_smul b hb]
    exact mul_ne_zero (pow_ne_zero q hc) hbx
  have hy := he y hby
  change s.val y * MvPolynomial.eval (c • x.val) b = MvPolynomial.eval (c • x.val) a at hy
  rw [Bridges.homogeneous_eval_smul b hb, Bridges.homogeneous_eval_smul a ha,
    pow_add, ← he x hbx] at hy
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero q hc) hbx)
  calc
    s.val y * (c^q * MvPolynomial.eval x.val b) = c^q * c^D * (s.val x * MvPolynomial.eval x.val b) := hy
    _ = (c^D * s.val x) * (c^q * MvPolynomial.eval x.val b) := by ring

/-- Multiplication by a homogeneous linear equation is the actual section
map used on the left of the hyperplane restriction sequence. -/
def sectionMultiplyLinear {n : ℕ} (V : ProjectiveVariety n) (D : ℕ)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) :
    regularSectionSpace V D →ₗ[ℂ] regularSectionSpace V (D+1) where
  toFun s := ⟨fun x => MvPolynomial.eval x.val ℓ * s.val x, by
    change IsRegularHomogeneousSection V (D+1) _
    unfold IsRegularHomogeneousSection
    intro x
    have hs : IsRegularHomogeneousSection V D s.val := s.property
    obtain ⟨q, a, b, ha, hb, hbx, he⟩ := hs x
    refine ⟨q, ℓ*a, b, ?_, hb, hbx, ?_⟩
    · convert hℓ.mul ha using 1 <;> omega
    · intro y hy
      rw [map_mul, mul_assoc, he y hy]⟩
  map_add' := by
    intro s t
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' := by
    intro c s
    apply Subtype.ext
    funext x
    change MvPolynomial.eval x.val ℓ * (c*s.val x) = c*(MvPolynomial.eval x.val ℓ*s.val x)
    ring

def nonzeroConeInclusion {n : ℕ} (V W : ProjectiveVariety n) (hWV : W.Subvariety V)
    (x : NonzeroConePoint W) : NonzeroConePoint V :=
  ⟨x.val, x.property.1, fun f hf => x.property.2 f (hWV hf)⟩

/-- Restriction to a reduced projective subvariety preserves the local
homogeneous-fraction condition, with the same numerator and denominator. -/
def sectionRestriction {n : ℕ} (V W : ProjectiveVariety n) (hWV : W.Subvariety V) (D : ℕ) :
    regularSectionSpace V D →ₗ[ℂ] regularSectionSpace W D where
  toFun s := ⟨fun x => s.val (nonzeroConeInclusion V W hWV x), by
    change IsRegularHomogeneousSection W D _
    unfold IsRegularHomogeneousSection
    intro x
    have hs : IsRegularHomogeneousSection V D s.val := s.property
    obtain ⟨q, a, b, ha, hb, hbx, he⟩ := hs (nonzeroConeInclusion V W hWV x)
    exact ⟨q, a, b, ha, hb, hbx, fun y hy => he (nonzeroConeInclusion V W hWV y) hy⟩⟩
  map_add' := by intro s t; rfl
  map_smul' := by intro c s; rfl

end
end DistinctDistances.TrackA
