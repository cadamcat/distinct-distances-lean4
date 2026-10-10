import DistinctDistances.TrackD.PolynomialDifferentials
import DistinctDistances.TrackD.SecantsChart
import DistinctDistances.TrackD.ProductTangents
import DistinctDistances.TrackD.Requests
import DistinctDistances.TrackD.RationalImageGeometry

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

@[simp] theorem productPoint_inl (x y : Point d) (i : Fin d) :
    productPoint x y (finSumFinEquiv (Sum.inl i)) = x i := by
  change pairPt x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = x i
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem productPoint_inr (x y : Point d) (i : Fin d) :
    productPoint x y (finSumFinEquiv (Sum.inr i)) = y i := by
  change pairPt x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) = y i
  rw [Equiv.symm_apply_apply]
  rfl

def secantChartDenominator (i : Fin d) : Poly (d + d) :=
  MvPolynomial.X (finSumFinEquiv (Sum.inr i)) -
    MvPolynomial.X (finSumFinEquiv (Sum.inl i))

def secantChartNumerator (i : Fin d) (j : Fin (d + d)) : Poly (d + d) :=
  Sum.elim (fun k => MvPolynomial.X (finSumFinEquiv (Sum.inl k)) * secantChartDenominator i)
    (fun k => MvPolynomial.X (finSumFinEquiv (Sum.inr k)) -
      MvPolynomial.X (finSumFinEquiv (Sum.inl k))) (finSumFinEquiv.symm j)

@[simp] theorem eval_secantChartDenominator (i : Fin d) (x y : Point d) :
    MvPolynomial.eval (productPoint x y) (secantChartDenominator i) = (y - x) i := by
  simp only [secantChartDenominator, map_sub, MvPolynomial.eval_X,
    productPoint, Function.comp_apply, Equiv.symm_apply_apply,
    pairPt, Sum.elim_inl, Sum.elim_inr]
  rfl

@[simp] theorem eval_secantChartNumerator_left (i k : Fin d) (x y : Point d) :
    MvPolynomial.eval (productPoint x y) (secantChartNumerator i (finSumFinEquiv (Sum.inl k))) =
      x k * (y - x) i := by
  simp only [secantChartNumerator, Equiv.symm_apply_apply, Sum.elim_inl, map_mul,
    MvPolynomial.eval_X, productPoint_inl, eval_secantChartDenominator]

@[simp] theorem eval_secantChartNumerator_right (i k : Fin d) (x y : Point d) :
    MvPolynomial.eval (productPoint x y) (secantChartNumerator i (finSumFinEquiv (Sum.inr k))) =
      (y - x) k := by
  simp only [secantChartNumerator, Equiv.symm_apply_apply, Sum.elim_inr, map_sub,
    MvPolynomial.eval_X, productPoint_inl, productPoint_inr]
  rfl

/-- The actual rational label map, represented in the shared product coordinates. -/
theorem rational_secant_label (i : Fin d) (x y : Point d) (hi : (y - x) i ≠ 0) :
    rationalPoint (secantChartNumerator i) (secantChartDenominator i) (productPoint x y) =
      productPoint x (dirChart (LinearMap.proj i) (y - x)) := by
  funext j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  cases q with
  | inl k =>
    change MvPolynomial.eval (productPoint x y) (secantChartNumerator i (finSumFinEquiv (Sum.inl k))) /
      MvPolynomial.eval (productPoint x y) (secantChartDenominator i) =
        productPoint x (dirChart (LinearMap.proj i) (y - x)) (finSumFinEquiv (Sum.inl k))
    rw [productPoint_inl, eval_secantChartNumerator_left, eval_secantChartDenominator]
    exact mul_div_cancel_right₀ (x k) hi
  | inr k =>
    change MvPolynomial.eval (productPoint x y) (secantChartNumerator i (finSumFinEquiv (Sum.inr k))) /
      MvPolynomial.eval (productPoint x y) (secantChartDenominator i) =
        productPoint x (dirChart (LinearMap.proj i) (y - x)) (finSumFinEquiv (Sum.inr k))
    rw [productPoint_inr, eval_secantChartNumerator_right, eval_secantChartDenominator]
    simp only [dirChart, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]

@[simp] theorem differential_secantChartDenominator (i : Fin d) (x y u v : Point d) :
    differential (secantChartDenominator i) (productPoint x y) (productPoint u v) = (v - u) i := by
  rw [secantChartDenominator, differential_sub, differential_X, differential_X]
  simp only [LinearMap.sub_apply, LinearMap.proj_apply, productPoint_inl, productPoint_inr]
  rfl

@[simp] theorem differential_secantChartNumerator_left (i k : Fin d) (x y u v : Point d) :
    differential (secantChartNumerator i (finSumFinEquiv (Sum.inl k)))
        (productPoint x y) (productPoint u v) =
      (y - x) i * u k + x k * (v - u) i := by
  simp only [secantChartNumerator, Equiv.symm_apply_apply, Sum.elim_inl,
    differential_mul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    eval_secantChartDenominator, differential_X, LinearMap.proj_apply,
    MvPolynomial.eval_X, productPoint_inl, differential_secantChartDenominator]

@[simp] theorem differential_secantChartNumerator_right (i k : Fin d) (x y u v : Point d) :
    differential (secantChartNumerator i (finSumFinEquiv (Sum.inr k)))
      (productPoint x y) (productPoint u v) = (v - u) k := by
  simp only [secantChartNumerator, Equiv.symm_apply_apply, Sum.elim_inr,
    differential_sub, differential_X, LinearMap.sub_apply, LinearMap.proj_apply,
    productPoint_inl, productPoint_inr]
  rfl

/-- The quotient-rule differential is exactly the frozen secant label derivative,
after the shared product-coordinate equivalence. -/
theorem rational_secant_label_differential (i : Fin d) (x y : Point d) (hi : (y - x) i ≠ 0) :
    (rationalDifferential (secantChartNumerator i) (secantChartDenominator i)
      (productPoint x y)).comp productLinearEquiv.toLinearMap =
        productLinearEquiv.toLinearMap.comp (labelDeriv (LinearMap.proj i) x y) := by
  apply LinearMap.ext
  intro p
  funext j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  cases q with
  | inl k =>
    simp only [LinearMap.comp_apply]
    change (rationalDifferential (secantChartNumerator i) (secantChartDenominator i)
      (productPoint x y) (productPoint p.1 p.2)) (finSumFinEquiv (Sum.inl k)) =
        productPoint (labelDeriv (LinearMap.proj i) x y p).1
          (labelDeriv (LinearMap.proj i) x y p).2 (finSumFinEquiv (Sum.inl k))
    rw [productPoint_inl]
    change (rationalDifferential (secantChartNumerator i) (secantChartDenominator i)
      (productPoint x y) (productPoint p.1 p.2)) (finSumFinEquiv (Sum.inl k)) = p.1 k
    simp only [rationalDifferential, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, eval_secantChartDenominator,
      eval_secantChartNumerator_left, differential_secantChartNumerator_left,
      differential_secantChartDenominator]
    field_simp [hi]
    ring

  | inr k =>
    simp only [LinearMap.comp_apply]
    change (rationalDifferential (secantChartNumerator i) (secantChartDenominator i)
      (productPoint x y) (productPoint p.1 p.2)) (finSumFinEquiv (Sum.inr k)) =
        productPoint (labelDeriv (LinearMap.proj i) x y p).1
          (labelDeriv (LinearMap.proj i) x y p).2 (finSumFinEquiv (Sum.inr k))
    rw [productPoint_inr]
    change (rationalDifferential (secantChartNumerator i) (secantChartDenominator i)
      (productPoint x y) (productPoint p.1 p.2)) (finSumFinEquiv (Sum.inr k)) =
        (dirChartDeriv (LinearMap.proj i) (y - x) (p.2 - p.1)) k
    simp only [rationalDifferential, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, eval_secantChartDenominator,
      eval_secantChartNumerator_right, differential_secantChartNumerator_right,
      differential_secantChartDenominator, dirChartDeriv, LinearMap.id_apply,
      LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- The kernel of a direction chart consists of the connecting-line direction. -/
theorem dirChartDeriv_kernel_mem_line (lam : Point d →ₗ[ℂ] ℂ) (u w : Point d)
    (hlu : lam u ≠ 0) (hw : dirChartDeriv lam u w = 0) : w ∈ ℂ ∙ u := by
  rw [Submodule.mem_span_singleton]
  have hform : (lam u)⁻¹ • w - (((lam u)^2)⁻¹ * lam w) • u = 0 := by
    simpa [dirChartDeriv, LinearMap.smulRight_apply, smul_smul] using hw
  have heq := sub_eq_zero.mp hform
  have hcoeff : lam u * (((lam u)^2)⁻¹ * lam w) = (lam u)⁻¹ * lam w := by
    field_simp [hlu]
  refine ⟨(lam u)⁻¹ * lam w, ?_⟩
  symm
  calc
    w = lam u • ((lam u)⁻¹ • w) := by simp [smul_smul, hlu]
    _ = lam u • ((((lam u)^2)⁻¹ * lam w) • u) := by rw [heq]
    _ = (lam u * (((lam u)^2)⁻¹ * lam w)) • u := by rw [smul_smul]
    _ = ((lam u)⁻¹ * lam w) • u := by rw [hcoeff]

theorem labelDeriv_injective_on_product (lam : Point d →ₗ[ℂ] ℂ) (x y : Point d)
    (hlam : lam (y - x) ≠ 0) (TX TY : Submodule ℂ (Point d))
    (hTY : y - x ∉ TY) :
    Function.Injective ((labelDeriv lam x y).domRestrict (TX.prod TY)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨⟨ξ, η⟩, hmem⟩ hz
  change labelDeriv lam x y (ξ, η) = 0 at hz
  have hξ : ξ = 0 := by
    simpa [labelDeriv] using congrArg Prod.fst hz
  have hηchart : dirChartDeriv lam (y - x) η = 0 := by
    simpa [labelDeriv, hξ] using congrArg Prod.snd hz
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (dirChartDeriv_kernel_mem_line lam (y - x) η hlam hηchart)
  have ha0 : a = 0 := by
    by_contra hn
    apply hTY
    have hu := TY.smul_mem a⁻¹ hmem.2
    simpa only [← ha, smul_smul, inv_mul_cancel₀ hn, one_smul] using hu
  have hη : η = 0 := by rw [← ha, ha0, zero_smul]
  apply Subtype.ext
  exact Prod.ext hξ hη

theorem labelDeriv_product_finrank (lam : Point d →ₗ[ℂ] ℂ) (x y : Point d)
    (hlam : lam (y - x) ≠ 0) (TX TY : Submodule ℂ (Point d))
    (hTY : y - x ∉ TY) :
    Module.finrank ℂ ((TX.prod TY).map (labelDeriv lam x y)) =
      Module.finrank ℂ TX + Module.finrank ℂ TY := by
  rw [← LinearMap.range_domRestrict]
  exact (LinearMap.finrank_range_of_inj
    (labelDeriv_injective_on_product lam x y hlam TX TY hTY)).trans
      ((prodSubmoduleEquiv TX TY).finrank_eq.trans Module.finrank_prod)

theorem rational_secant_tangent_map (X Y : AffineVariety d) (i : Fin d)
    (x y : Point d) (hx : x ∈ X) (hy : y ∈ Y) (hi : (y - x) i ≠ 0) :
    ((productVariety X Y).tangentSpace (productPoint x y)).map
        (rationalDifferential (secantChartNumerator i) (secantChartDenominator i) (productPoint x y)) =
      (((X.tangentSpace x).prod (Y.tangentSpace y)).map
        (labelDeriv (LinearMap.proj i) x y)).map productLinearEquiv.toLinearMap := by
  rw [← product_tangent_space X Y x y hx hy, ← Submodule.map_comp,
    rational_secant_label_differential i x y hi, Submodule.map_comp]

theorem rational_secant_tangent_finrank (X Y : AffineVariety d) (i : Fin d)
    (x y : Point d) (hx : x ∈ X) (hy : y ∈ Y) (hi : (y - x) i ≠ 0)
    (hTY : y - x ∉ Y.tangentSpace y) :
    Module.finrank ℂ (((productVariety X Y).tangentSpace (productPoint x y)).map
      (rationalDifferential (secantChartNumerator i) (secantChartDenominator i) (productPoint x y))) =
        Module.finrank ℂ (X.tangentSpace x) + Module.finrank ℂ (Y.tangentSpace y) := by
  rw [rational_secant_tangent_map X Y i x y hx hy hi, LinearEquiv.finrank_map_eq]
  exact labelDeriv_product_finrank (LinearMap.proj i) x y hi
    (X.tangentSpace x) (Y.tangentSpace y) hTY

theorem dirChart_smul (lam : Point d →ₗ[ℂ] ℂ) (u : Point d) (c : ℂ)
    (hc : c ≠ 0) (hlu : lam u ≠ 0) : dirChart lam (c • u) = dirChart lam u := by
  have hcoeff : (c * lam u)⁻¹ * c = (lam u)⁻¹ := by field_simp [hc, hlu]
  simp only [dirChart, map_smul, smul_eq_mul, smul_smul, hcoeff]

end
end DistinctDistances.TrackD
