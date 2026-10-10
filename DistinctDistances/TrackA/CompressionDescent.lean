import DistinctDistances.TrackA.Definitions
import DistinctDistances.OAIInterface.PointParameters

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical Pointwise

/-- Finite products of generators span the exact ideal power; the index
type retains repetitions and also handles the empty coordinate set. -/
theorem compression_span_range_pow {R ι : Type*} [CommSemiring R]
    (f : ι → R) (r : ℕ) :
    (Ideal.span (Set.range f))^r =
      Ideal.span (Set.range (fun a : Fin r → ι => ∏ i, f (a i))) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ih, Ideal.span_mul_span]
    congr 1
    ext x
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, v, ⟨b, rfl⟩, rfl⟩
      refine ⟨Fin.cons b a, ?_⟩
      simp [Fin.prod_univ_succ, mul_comm]
    · rintro ⟨a, rfl⟩
      refine ⟨∏ i : Fin r, f (a i.succ), ⟨fun i => a i.succ, rfl⟩,
        f (a 0), ⟨a 0, rfl⟩, ?_⟩
      simp [Fin.prod_univ_succ, mul_comm]

theorem compression_pointIdeal_eq {n : ℕ} {F : Type*} [Field F] (z : FieldPoint n F) :
    pointIdealOver z = OAI.PiExponent.WeightedBezout.pointIdeal z := by
  ext f
  rw [pointIdealOver, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rfl

/-- A polynomial-order certificate is a finite algebraic identity.
Adjoining its coefficient data therefore preserves the certificate under
every specialization, including ones identifying distinct sample points. -/
theorem compression_order_witness {n : ℕ} {F : Type*} [Field F]
    (f : FieldPoly n F) (z : FieldPoint n F) (r : ℕ) (horder : OrderAtLeast f z r) :
    ∃ a : (Fin r → Fin n) → FieldPoly n F,
      f = ∑ e, a e * ∏ i, (MvPolynomial.X (e i) - MvPolynomial.C (z (e i))) := by
  have h : f ∈ Ideal.span (Set.range
      (fun e : Fin r → Fin n => ∏ i, (MvPolynomial.X (e i) - MvPolynomial.C (z (e i))))) := by
    simpa only [OrderAtLeast, compression_pointIdeal_eq,
      OAI.PiExponent.WeightedBezout.pointIdeal_eq_span, compression_span_range_pow] using horder
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
  exact ⟨a, ha.symm⟩

theorem compression_lift_polynomial {n : ℕ} (R : Subalgebra ℤ ℂ) (f : Poly n)
    (hf : ∀ c ∈ f.coeffs, c ∈ R) :
    ∃ fR : MvPolynomial (Fin n) R, MvPolynomial.map R.val.toRingHom fR = f := by
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  exact ⟨⟨c, hf c hc⟩, rfl⟩

theorem compression_eval_lift {n : ℕ} (R : Subalgebra ℤ ℂ)
    (fR : MvPolynomial (Fin n) R) (f : Poly n)
    (hf : MvPolynomial.map R.val.toRingHom fR = f)
    (zR : Fin n → R) (z : Point n) (hz : ∀ j, (zR j : ℂ) = z j) :
    (MvPolynomial.eval zR fR : ℂ) = MvPolynomial.eval z f := by
  change R.val.toRingHom (MvPolynomial.eval zR fR) = _
  rw [MvPolynomial.map_eval, hf]
  have he : R.val.toRingHom ∘ zR = z := funext hz
  rw [he]

/-- The source algebra contains witnesses for order as well as the dual
evaluation moments. All preserved identities are established in that
actual finitely generated subalgebra before any specialization is chosen. -/
theorem compression_finite_data {n : ℕ} (S : Finset (Point n)) (x : Point n)
    (f : Poly n) (r q : ℕ) (weights : S → ℂ)
    (horder : ∀ z ∈ S, OrderAtLeast f z r) (hx : MvPolynomial.eval x f ≠ 0)
    (hmoments : ∀ a : Fin n →₀ ℕ, a.degree ≤ q →
      MvPolynomial.eval x (MvPolynomial.monomial a 1) =
        ∑ z : S, weights z * MvPolynomial.eval z.val (MvPolynomial.monomial a 1)) :
    ∃ R : Subalgebra ℤ ℂ, R.FG ∧
      ∃ (fR : MvPolynomial (Fin n) R) (xR : Fin n → R)
        (zR : S → Fin n → R) (weightsR : S → R) (inv : R),
        MvPolynomial.map R.val.toRingHom fR = f ∧
        (∀ j, (xR j : ℂ) = x j) ∧ (∀ z j, (zR z j : ℂ) = z.val j) ∧
        (MvPolynomial.eval xR fR) * inv = 1 ∧
        (∀ z, fR ∈ (Ideal.span (Set.range (fun j =>
          MvPolynomial.X j - MvPolynomial.C (zR z j))))^r) ∧
        (∀ a : Fin n →₀ ℕ, a.degree ≤ q →
          MvPolynomial.eval xR (MvPolynomial.monomial a 1) =
            ∑ z : S, weightsR z * MvPolynomial.eval (zR z) (MvPolynomial.monomial a 1)) := by
  choose w hw using (fun z : S => compression_order_witness f z.val r (horder z.val z.property))
  let coords : Finset ℂ := (Finset.univ : Finset (Fin n)).image x
  let points : Finset ℂ := (Finset.univ : Finset S).biUnion
    (fun z => (Finset.univ : Finset (Fin n)).image z.val)
  let moments : Finset ℂ := (Finset.univ : Finset S).image weights
  let witnesses : Finset ℂ := (Finset.univ : Finset S).biUnion
    (fun z => (Finset.univ : Finset (Fin r → Fin n)).biUnion (fun e => (w z e).coeffs))
  let T : Finset ℂ := f.coeffs ∪ coords ∪ points ∪ moments ∪ witnesses ∪
    {(MvPolynomial.eval x f)⁻¹}
  let R : Subalgebra ℤ ℂ := Algebra.adjoin ℤ (T : Set ℂ)
  have hmem {c : ℂ} (hc : c ∈ T) : c ∈ R := Algebra.subset_adjoin hc
  have hfc : ∀ c ∈ f.coeffs, c ∈ R := by
    intro c hc
    apply hmem
    simp only [T, Finset.mem_union]
    tauto
  have hxc : ∀ j, x j ∈ R := by
    intro j
    have hj : x j ∈ coords := Finset.mem_image_of_mem _ (Finset.mem_univ j)
    apply hmem
    simp only [T, Finset.mem_union]
    tauto
  have hzc : ∀ (z : S) j, z.val j ∈ R := by
    intro z j
    have hj : z.val j ∈ points := Finset.mem_biUnion.mpr
      ⟨z, Finset.mem_univ z, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
    apply hmem
    simp only [T, Finset.mem_union]
    tauto
  have hmc : ∀ z : S, weights z ∈ R := by
    intro z
    have hz : weights z ∈ moments := Finset.mem_image_of_mem _ (Finset.mem_univ z)
    apply hmem
    simp only [T, Finset.mem_union]
    tauto
  have hwc : ∀ (z : S) e, ∀ c ∈ (w z e).coeffs, c ∈ R := by
    intro z e c hc
    have he : c ∈ witnesses := Finset.mem_biUnion.mpr
      ⟨z, Finset.mem_univ z, Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, hc⟩⟩
    apply hmem
    simp only [T, Finset.mem_union]
    tauto
  have hic : (MvPolynomial.eval x f)⁻¹ ∈ R := by
    apply hmem
    simp [T]
  obtain ⟨fR, hfR⟩ := compression_lift_polynomial R f hfc
  choose wR hwR using (fun (z : S) e => compression_lift_polynomial R (w z e) (hwc z e))
  let xR : Fin n → R := fun j => ⟨x j, hxc j⟩
  let zR : S → Fin n → R := fun z j => ⟨z.val j, hzc z j⟩
  let weightsR : S → R := fun z => ⟨weights z, hmc z⟩
  let inv : R := ⟨(MvPolynomial.eval x f)⁻¹, hic⟩
  refine ⟨R, Subalgebra.fg_adjoin_finset T, fR, xR, zR, weightsR, inv,
    hfR, (fun _ => rfl), (fun _ _ => rfl), ?_, ?_, ?_⟩
  · apply Subtype.val_injective
    change R.val.toRingHom (MvPolynomial.eval xR fR * inv) = R.val.toRingHom 1
    have heval : R.val.toRingHom (MvPolynomial.eval xR fR) = MvPolynomial.eval x f :=
      compression_eval_lift R fR f hfR xR x (fun _ => rfl)
    rw [map_mul, map_one, heval]
    exact mul_inv_cancel₀ hx
  · intro z
    have heq : fR = ∑ e, wR z e * ∏ i,
        (MvPolynomial.X (e i) - MvPolynomial.C (zR z (e i))) := by
      apply MvPolynomial.map_injective R.val.toRingHom Subtype.val_injective
      rw [hfR]
      simp only [map_sum, map_mul, map_prod, map_sub, MvPolynomial.map_X,
        MvPolynomial.map_C, hwR]
      exact hw z
    rw [compression_span_range_pow]
    apply Ideal.mem_span_range_iff_exists_fun.mpr
    exact ⟨wR z, heq.symm⟩
  · intro a ha
    apply Subtype.val_injective
    change R.val.toRingHom (MvPolynomial.eval xR (MvPolynomial.monomial a 1)) =
      R.val.toRingHom (∑ z : S, weightsR z *
        MvPolynomial.eval (zR z) (MvPolynomial.monomial a 1))
    simp only [map_sum, map_mul, MvPolynomial.map_eval, MvPolynomial.map_monomial, map_one]
    exact hmoments a ha

theorem compression_map_degree_le {n : ℕ} {R F : Type*} [CommSemiring R] [CommSemiring F]
    (φ : R →+* F) (f : MvPolynomial (Fin n) R) :
    (MvPolynomial.map φ f).totalDegree ≤ f.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset φ f)

theorem compression_lift_degree {n : ℕ} (R : Subalgebra ℤ ℂ)
    (fR : MvPolynomial (Fin n) R) (f : Poly n) (hf : MvPolynomial.map R.val.toRingHom fR = f) :
    fR.totalDegree = f.totalDegree := by
  rw [← hf]
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective fR (f := R.val.toRingHom) Subtype.val_injective]

theorem compression_order_specialize {n : ℕ} {R F : Type*} [CommRing R] [Field F]
    (φ : R →+* F) (f : MvPolynomial (Fin n) R) (z : Fin n → R) (r : ℕ)
    (horder : f ∈ (Ideal.span (Set.range (fun j => MvPolynomial.X j - MvPolynomial.C (z j))))^r) :
    OrderAtLeast (MvPolynomial.map φ f) (φ ∘ z) r := by
  have h := Ideal.mem_map_of_mem (MvPolynomial.map φ) horder
  rw [Ideal.map_pow] at h
  have he : (Ideal.span (Set.range (fun j => MvPolynomial.X j - MvPolynomial.C (z j)))).map
      (MvPolynomial.map φ) = pointIdealOver (φ ∘ z) := by
    rw [compression_pointIdeal_eq, OAI.PiExponent.WeightedBezout.pointIdeal_eq_span,
      Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext j
    simp [Function.comp_def]
  rw [he] at h
  exact h

theorem compression_eval_from_moments {n : ℕ} {R F τ : Type*}
    [CommRing R] [Field F] [Fintype τ] (q : ℕ)
    (x : Fin n → R) (z : τ → Fin n → R) (weights : τ → R)
    (hmoments : ∀ a : Fin n →₀ ℕ, a.degree ≤ q →
      MvPolynomial.eval x (MvPolynomial.monomial a 1) =
        ∑ t, weights t * MvPolynomial.eval (z t) (MvPolynomial.monomial a 1))
    (φ : R →+* F) (g : FieldPoly n F) (hg : g.totalDegree ≤ q) :
    MvPolynomial.eval (φ ∘ x) g =
      ∑ t, φ (weights t) * MvPolynomial.eval (φ ∘ z t) g := by
  have hm (a : Fin n →₀ ℕ) (ha : a.degree ≤ q) :
      MvPolynomial.eval (φ ∘ x) (MvPolynomial.monomial a 1) =
        ∑ t, φ (weights t) * MvPolynomial.eval (φ ∘ z t) (MvPolynomial.monomial a 1) := by
    have h := congrArg φ (hmoments a ha)
    simpa only [map_sum, map_mul, MvPolynomial.map_eval, MvPolynomial.map_monomial, map_one] using h
  have hev (u : Fin n → F) :
      MvPolynomial.eval u g = ∑ a ∈ g.support,
        g.coeff a * MvPolynomial.eval u (MvPolynomial.monomial a 1) := by
    simpa [MvPolynomial.eval_monomial] using MvPolynomial.eval_eq' u g
  rw [hev]
  calc
    (∑ a ∈ g.support, g.coeff a * MvPolynomial.eval (φ ∘ x) (MvPolynomial.monomial a 1)) =
        ∑ a ∈ g.support, g.coeff a *
          ∑ t, φ (weights t) * MvPolynomial.eval (φ ∘ z t) (MvPolynomial.monomial a 1) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hm a (by
        simpa [Finsupp.degree_apply, Finsupp.sum] using (MvPolynomial.le_totalDegree ha).trans hg)]
    _ = ∑ t, φ (weights t) * MvPolynomial.eval (φ ∘ z t) g := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [hev]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

end
end DistinctDistances.TrackA
