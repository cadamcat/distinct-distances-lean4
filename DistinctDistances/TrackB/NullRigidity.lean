import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
Complex bilinear local rigidity, concentration.tex:932–1002. The algebraic/analytic
chart and Zariski-density bridges remain separate geometric nodes. These statements
use convex neighborhoods as supplied by the local holomorphic chart.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false

open scoped BigOperators

/-- Complex bilinear dot product; no complex conjugation. -/
def complexDot (r : ℕ) (x y : Fin r → ℂ) : ℂ := ∑ i, x i * y i

/-- B26's differentiated Gram identity, concentration.tex:975–981. -/
theorem gram_derivatives_force_zero (r : ℕ)
    (v : Fin r → Fin r → ℂ) (H : Fin r → Fin r → Fin r → ℂ)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤)
    (hsymm : ∀ i j, H i j = H j i)
    (hgram : ∀ i j l,
      complexDot r (H i j) (v l) + complexDot r (v j) (H i l) = 0) :
    ∀ i j, H i j = 0 := by
  classical
  have hdot_comm (x y : Fin r → ℂ) :
      complexDot r x y = complexDot r y x := by
    simp [complexDot, mul_comm]
  intro i j
  have horth : ∀ l, complexDot r (H i j) (v l) = 0 := by
    intro l
    let a := complexDot r (H i j) (v l)
    let b := complexDot r (H i l) (v j)
    let c := complexDot r (H j l) (v i)
    have hab : a + b = 0 := by
      dsimp [a, b]
      calc
        complexDot r (H i j) (v l) + complexDot r (H i l) (v j) =
            complexDot r (H i j) (v l) + complexDot r (v j) (H i l) := by
          rw [hdot_comm (v j) (H i l)]
        _ = 0 := hgram i j l
    have hac : a + c = 0 := by
      dsimp [a, c]
      calc
        complexDot r (H i j) (v l) + complexDot r (H j l) (v i) =
            complexDot r (H j i) (v l) + complexDot r (v i) (H j l) := by
          rw [hsymm i j, hdot_comm (H j l) (v i)]
        _ = 0 := hgram j i l
    have hbc : b + c = 0 := by
      dsimp [b, c]
      calc
        complexDot r (H i l) (v j) + complexDot r (H j l) (v i) =
            complexDot r (H l i) (v j) + complexDot r (v i) (H l j) := by
          rw [← hsymm l i, ← hsymm l j, hdot_comm (H l j) (v i)]
        _ = 0 := hgram l i j
    have h2a : (2 : ℂ) * a = 0 := by
      calc
        (2 : ℂ) * a = (a + b) + (a + c) - (b + c) := by ring
        _ = 0 := by rw [hab, hac, hbc]; ring
    have ha : a = 0 := by
      rcases mul_eq_zero.mp h2a with htwo | ha
      · norm_num at htwo
      · exact ha
    exact ha
  have hdot_zero : ∀ x : Fin r → ℂ, complexDot r (H i j) x = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℂ (Set.range v) := by
      rw [hspan]
      exact Submodule.mem_top
    exact Submodule.span_induction
      (mem := fun y hy => by
        rcases hy with ⟨l, rfl⟩
        exact horth l)
      (zero := by simp [complexDot])
      (add := by
        intro x y hx hy h₁ h₂
        unfold complexDot at h₁ h₂ ⊢
        calc
          (∑ k, H i j k * (x k + y k)) =
              (∑ k, H i j k * x k) + ∑ k, H i j k * y k := by
            calc
              (∑ k, H i j k * (x k + y k)) =
                  ∑ k, (H i j k * x k + H i j k * y k) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
              _ = (∑ k, H i j k * x k) + ∑ k, H i j k * y k :=
                Finset.sum_add_distrib
          _ = 0 := by rw [h₁, h₂]; simp)
      (smul := by
        intro c x hx h₁
        unfold complexDot at h₁ ⊢
        simp only [Pi.smul_apply, smul_eq_mul]
        calc
          (∑ k, H i j k * (c * x k)) = ∑ k, c * (H i j k * x k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = c * ∑ k, H i j k * x k := (Finset.mul_sum ..).symm
          _ = 0 := by rw [h₁]; simp)
      hx
  funext k
  simpa [complexDot, Pi.single_apply] using hdot_zero (Pi.single k 1)

/-- B26, concentration.tex:970–981. Full bilinear metric preservation gives the
coordinate Gram identity without requiring a Hermitian isometry. -/
theorem bilinear_local_isometry_hessian_zero (r : ℕ)
    (F : (Fin r → ℂ) → (Fin r → ℂ)) (Ω : Set (Fin r → ℂ))
    (hopen : IsOpen Ω) (hsmooth : ContDiffOn ℂ 2 F Ω)
    (hmetric : ∀ x ∈ Ω, ∀ a b : Fin r → ℂ,
      complexDot r (fderiv ℂ F x a) (fderiv ℂ F x b) = complexDot r a b) :
    ∀ x ∈ Ω, fderiv ℂ (fderiv ℂ F) x = 0 := by
  classical
  intro x hx
  let G := fderiv ℂ F x
  let D₂ := fderiv ℂ (fderiv ℂ F) x
  have hFx : ContDiffAt ℂ 2 F x := (hsmooth x hx).contDiffAt (hopen.mem_nhds hx)
  have hGcont : ContDiffAt ℂ 1 (fderiv ℂ F) x :=
    hFx.fderiv_right (m := 1) (by norm_num)
  have hGderiv : HasFDerivAt (fderiv ℂ F) D₂ x :=
    hGcont.differentiableAt (by norm_num) |>.hasFDerivAt
  have hdot_comm (a b : Fin r → ℂ) :
      complexDot r a b = complexDot r b a := by
    simp [complexDot, mul_comm]
  have hG_injective : Function.Injective G := by
    intro a b hab
    apply funext
    intro k
    have hzero : G (a - b) = 0 := by
      simp [G, map_sub, hab]
    have h := hmetric x hx (a - b) (Pi.single k 1)
    rw [hzero] at h
    have hk : (a - b) k = 0 := by
      simpa [complexDot, Pi.single_apply] using h.symm
    exact sub_eq_zero.mp hk
  have hG_surjective : Function.Surjective G :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hG_injective
  let v : Fin r → Fin r → ℂ := fun i => G (Pi.single i 1)
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ := by
    apply top_unique
    intro y hy
    obtain ⟨a, ha⟩ := hG_surjective y
    have hdecomp : a = ∑ i : Fin r, a i • Pi.single i 1 := by
      ext i
      simp [Pi.single_apply]
    have hGdecomp : G a = ∑ i : Fin r, a i • v i := by
      calc
        G a = G (∑ i : Fin r, a i • Pi.single i 1) := congrArg G hdecomp
        _ = ∑ i : Fin r, G (a i • Pi.single i 1) := map_sum G _ _
        _ = ∑ i : Fin r, a i • v i := by simp [v]
    rw [← ha, hGdecomp]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let H : Fin r → Fin r → Fin r → ℂ := fun i j => D₂ (Pi.single i 1) (Pi.single j 1)
  have hsymm : ∀ i j, H i j = H j i := by
    have hsymmetric := hFx.isSymmSndFDerivAt (by norm_num [minSmoothness])
    intro i j
    funext k
    exact congrArg (fun y : Fin r → ℂ => y k)
      (hsymmetric (Pi.single i 1) (Pi.single j 1))
  have hgram : ∀ i j l,
      complexDot r (H i j) (v l) + complexDot r (v j) (H i l) = 0 := by
    intro i j l
    let A := fun y : Fin r → ℂ => fderiv ℂ F y (Pi.single j 1)
    let B := fun y : Fin r → ℂ => fderiv ℂ F y (Pi.single l 1)
    let d : (Fin r → ℂ) →L[ℂ] ℂ :=
      ∑ k : Fin r,
        ((A x k) • ((ContinuousLinearMap.proj k).comp (D₂.flip (Pi.single l 1))) +
          (B x k) • ((ContinuousLinearMap.proj k).comp (D₂.flip (Pi.single j 1))))
    have hA : HasFDerivAt A (D₂.flip (Pi.single j 1)) x := by
      simpa [A, D₂, G] using
        hGderiv.clm_apply (hasFDerivAt_const (Pi.single j 1) x)
    have hB : HasFDerivAt B (D₂.flip (Pi.single l 1)) x := by
      simpa [B, D₂, G] using
        hGderiv.clm_apply (hasFDerivAt_const (Pi.single l 1) x)
    have hAcoord (k : Fin r) :
        HasFDerivAt (fun y => A y k)
          ((ContinuousLinearMap.proj k).comp (D₂.flip (Pi.single j 1))) x := by
      simpa [A, Function.comp_def, ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj k).hasFDerivAt.comp x hA
    have hBcoord (k : Fin r) :
        HasFDerivAt (fun y => B y k)
          ((ContinuousLinearMap.proj k).comp (D₂.flip (Pi.single l 1))) x := by
      simpa [B, Function.comp_def, ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj k).hasFDerivAt.comp x hB
    let φ : (Fin r → ℂ) → ℂ := fun y => complexDot r (A y) (B y)
    have hφ : HasFDerivAt φ d x := by
      have hsum : HasFDerivAt
          (∑ k : Fin r, fun y => A y k * B y k) d x :=
        HasFDerivAt.sum (u := Finset.univ) fun k hk => (hAcoord k).mul (hBcoord k)
      have heq : φ =ᶠ[nhds x] (∑ k : Fin r, fun y => A y k * B y k) :=
        Filter.Eventually.of_forall fun y => by simp [φ, complexDot]
      exact hsum.congr_of_eventuallyEq heq
    have hφ_eventually : φ =ᶠ[nhds x] fun _ =>
        complexDot r (Pi.single j 1) (Pi.single l 1) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      simpa [φ, A, B] using hmetric y hy (Pi.single j 1) (Pi.single l 1)
    have hconst : HasFDerivAt
        (fun _ : Fin r → ℂ => complexDot r (Pi.single j 1) (Pi.single l 1))
        (0 : (Fin r → ℂ) →L[ℂ] ℂ) x :=
      hasFDerivAt_const (complexDot r (Pi.single j 1) (Pi.single l 1)) x
    have hφ_const : HasFDerivAt φ (0 : (Fin r → ℂ) →L[ℂ] ℂ) x :=
      hconst.congr_of_eventuallyEq hφ_eventually
    have hd_zero : d = 0 := hφ.unique hφ_const
    have hd_apply := congrArg (fun f : (Fin r → ℂ) →L[ℂ] ℂ => f (Pi.single i 1)) hd_zero
    have hdot :
        complexDot r (v j) (H i l) + complexDot r (v l) (H i j) = 0 := by
      simpa [d, A, B, D₂, G, complexDot, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
        ContinuousLinearMap.flip_apply, Finset.sum_add_distrib] using hd_apply
    calc
      complexDot r (H i j) (v l) + complexDot r (v j) (H i l) =
          complexDot r (v l) (H i j) + complexDot r (v j) (H i l) := by
        rw [hdot_comm]
      _ = 0 := by simpa [add_comm] using hdot
  have hzero := gram_derivatives_force_zero r v H hspan hsymm hgram
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  have ha : a = ∑ i : Fin r, a i • Pi.single i 1 := by
    ext i
    simp [Pi.single_apply]
  have hb : b = ∑ j : Fin r, b j • Pi.single j 1 := by
    ext j
    simp [Pi.single_apply]
  have hPair (i j : Fin r) : D₂ (Pi.single i 1) (Pi.single j 1) = 0 := by
    simpa [H] using hzero i j
  have hinner (i : Fin r) : D₂ (Pi.single i 1) b = 0 := by
    rw [hb]
    simp only [map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hPair i j]
    simp
  rw [ha]
  simp only [map_sum, map_smul]
  simp only [sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hinner i]
  simp

/-- B26, concentration.tex:981–985. A local chart may be restricted to an open
convex neighborhood; affine equality is only asserted on that neighborhood. -/
theorem bilinear_local_isometry_affine (r : ℕ)
    (F : (Fin r → ℂ) → (Fin r → ℂ)) (Ω : Set (Fin r → ℂ))
    (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) (hsmooth : ContDiffOn ℂ 2 F Ω)
    (hmetric : ∀ x ∈ Ω, ∀ a b : Fin r → ℂ,
      complexDot r (fderiv ℂ F x a) (fderiv ℂ F x b) = complexDot r a b) :
    ∀ x0 ∈ Ω, ∀ x ∈ Ω, F x = F x0 + fderiv ℂ F x0 (x - x0) := by
  intro x0 hx0 x hx
  let G := fun y : Fin r → ℂ => fderiv ℂ F y
  have hGdiff : DifferentiableOn ℂ G Ω := by
    intro y hy
    have hFy : ContDiffAt ℂ 2 F y :=
      (hsmooth y hy).contDiffAt (hopen.mem_nhds hy)
    exact ((hFy.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      |>.differentiableWithinAt
  have hGderiv_zero : ∀ y ∈ Ω, fderivWithin ℂ G Ω y = 0 := by
    intro y hy
    rw [fderivWithin_of_isOpen hopen hy]
    change fderiv ℂ (fderiv ℂ F) y = 0
    exact bilinear_local_isometry_hessian_zero r F Ω hopen hsmooth hmetric y hy
  have hGconst : ∀ y ∈ Ω, G y = fderiv ℂ F x0 := by
    intro y hy
    exact hconvex.is_const_of_fderivWithin_eq_zero hGdiff hGderiv_zero hy hx0
  let L := fderiv ℂ F x0
  let g := fun y : Fin r → ℂ => F y - L y
  have hFdiff : DifferentiableOn ℂ F Ω := by
    intro y hy
    exact ((hsmooth y hy).contDiffAt (hopen.mem_nhds hy)).differentiableAt (by norm_num)
      |>.differentiableWithinAt
  have hLdiff : DifferentiableOn ℂ (fun y : Fin r → ℂ => L y) Ω := by
    intro y hy
    exact L.differentiableAt.differentiableWithinAt
  have hgdiff : DifferentiableOn ℂ g Ω := hFdiff.sub hLdiff
  have hgderiv_zero : ∀ y ∈ Ω, fderivWithin ℂ g Ω y = 0 := by
    intro y hy
    rw [fderivWithin_of_isOpen hopen hy]
    have hFy : ContDiffAt ℂ 2 F y :=
      (hsmooth y hy).contDiffAt (hopen.mem_nhds hy)
    have hFAt : DifferentiableAt ℂ F y := hFy.differentiableAt (by norm_num)
    have hLy : DifferentiableAt ℂ (fun z : Fin r → ℂ => L z) y := L.differentiableAt
    rw [fderiv_fun_sub hFAt hLy]
    have hGrad : fderiv ℂ F y = L := by simpa [G, L] using hGconst y hy
    rw [hGrad]
    simp [L]
  have hval : F x0 - L x0 = F x - L x :=
    hconvex.is_const_of_fderivWithin_eq_zero hgdiff hgderiv_zero hx0 hx
  calc
    F x = (F x - L x) + L x := by abel
    _ = (F x0 - L x0) + L x := by rw [hval.symm]
    _ = F x0 + L (x - x0) := by rw [map_sub]; abel

section ConformalChart

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- The normalized vector representative in the hyperbolic quadric chart. -/
def conformalLift (q : QuadraticForm ℂ W) (x : W) : ℂ × (W × ℂ) :=
  (1, x, -q x)

/-- B25: the ambient hyperbolic quadratic value, concentration.tex:938–945. -/
def hyperbolicValue (q : QuadraticForm ℂ W) (x : ℂ × (W × ℂ)) : ℂ :=
  x.1 * x.2.2 + q x.2.1

/-- B25's chart lies on the quadric, concentration.tex:943–949. -/
theorem conformalLift_is_null (q : QuadraticForm ℂ W) (x : W) :
    hyperbolicValue q (conformalLift q x) = 0 := by
  simp [hyperbolicValue, conformalLift]

/-- B25, conc:deg-conformal-chart: the affine chart is an actual projective point map. -/
theorem conformalLift_ne_zero (q : QuadraticForm ℂ W) (x : W) : conformalLift q x ≠ 0 := by
  intro h
  have hfst := congrArg Prod.fst h
  simp [conformalLift] at hfst

noncomputable def conformalChart (q : QuadraticForm ℂ W) (x : W) : Projectivization ℂ (ℂ × (W × ℂ)) :=
  Projectivization.mk ℂ (conformalLift q x) (conformalLift_ne_zero q x)

private theorem hyperbolicValue_smul (q : QuadraticForm ℂ W) (c : ℂ)
    (z : ℂ × (W × ℂ)) :
    hyperbolicValue q (c • z) = c ^ 2 * hyperbolicValue q z := by
  rcases z with ⟨s, x, t⟩
  simp [hyperbolicValue, QuadraticMap.map_smul, smul_eq_mul, pow_two,
    mul_assoc, mul_comm, mul_left_comm]
  <;> ring

/-- The chart and its precise open image, concentration.tex:938–949. -/
theorem conformalChart_bijective (q : QuadraticForm ℂ W) :
    Function.Injective (conformalChart q) ∧
      Set.range (conformalChart q) =
        {p : Projectivization ℂ (ℂ × (W × ℂ)) |
          p.rep.1 ≠ 0 ∧ hyperbolicValue q p.rep = 0} := by
  constructor
  · intro x y hxy
    have hmul : ∃ a : ℂ, a • conformalLift q y = conformalLift q x :=
      (Projectivization.mk_eq_mk_iff' ℂ (conformalLift q x) (conformalLift q y)
        (conformalLift_ne_zero q x) (conformalLift_ne_zero q y)).mp hxy
    obtain ⟨a, ha⟩ := hmul
    have ha1 : a = 1 := by
      have h := congrArg Prod.fst ha
      simpa [conformalLift] using h
    have hxy' : a • y = x := by
      have h := congrArg (fun z : ℂ × (W × ℂ) => z.2.1) ha
      simpa [conformalLift] using h
    simpa [ha1] using hxy'.symm
  · ext p
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep
        ℂ (conformalLift q x) (conformalLift_ne_zero q x)
      constructor
      · have hfirst := congrArg Prod.fst ha
        have ha0 : (a : ℂ) = (conformalChart q x).rep.1 := by
          simpa [conformalLift, conformalChart, Units.smul_def] using hfirst
        rw [← ha0]
        exact a.ne_zero
      · have ha' : (a : ℂ) • conformalLift q x = (conformalChart q x).rep := by
          simpa [conformalChart, Units.smul_def] using ha
        have hval : hyperbolicValue q ((a : ℂ) • conformalLift q x) = 0 := by
          rw [hyperbolicValue_smul, conformalLift_is_null]
          simp
        simpa only [ha'] using hval
    · rintro ⟨ht, hnull⟩
      let t := p.rep.1
      let y := p.rep.2.1
      let z := p.rep.2.2
      let x := t⁻¹ • y
      have ht' : t ≠ 0 := by simpa [t] using ht
      have htz : t * z + q y = 0 := by
        simpa [hyperbolicValue, t, y, z] using hnull
      have hz : t * z = -q y := (eq_neg_iff_add_eq_zero).2 htz
      have hvec : t • conformalLift q x = p.rep := by
        apply Prod.ext
        · simp [conformalLift, t]
        · apply Prod.ext
          · change t • x = y
            simp [x, t, smul_smul, ht]
          · change t * (-q x) = z
            apply (mul_left_cancel₀ ht)
            calc
              t * (t * (-q x)) = -((t * t⁻¹) * (t * t⁻¹)) * q y := by
                change t * (t * (-q (t⁻¹ • y))) =
                  -((t * t⁻¹) * (t * t⁻¹)) * q y
                rw [QuadraticMap.map_smul]
                simp only [smul_eq_mul]
                ring
              _ = -q y := by simp [mul_inv_cancel₀ ht']
              _ = t * z := hz.symm
      have hsmul : t⁻¹ • p.rep = conformalLift q x := by
        calc
          t⁻¹ • p.rep = t⁻¹ • (t • conformalLift q x) := by rw [hvec]
          _ = (t⁻¹ * t) • conformalLift q x := by rw [smul_smul]
          _ = conformalLift q x := by simp [ht']
      have hmk : conformalChart q x = p := by
        rw [← p.mk_rep]
        change Projectivization.mk ℂ (conformalLift q x) (conformalLift_ne_zero q x) =
          Projectivization.mk ℂ p.rep p.rep_nonzero
        exact (Projectivization.mk_eq_mk_iff' ℂ (conformalLift q x) p.rep
          (conformalLift_ne_zero q x) p.rep_nonzero).2 ⟨t⁻¹, hsmul⟩
      exact ⟨x, hmk⟩

/-- The tangent lift has quadratic value q(dx), concentration.tex:947–949. -/
theorem conformal_tangent_value (q : QuadraticForm ℂ W) (x dx : W) :
    hyperbolicValue q (0, dx, -(q (x + dx) - q x - q dx)) = q dx := by
  simp [hyperbolicValue]

/-- B25's affine-plane lift, concentration.tex:987–1002. This is linear algebra;
the geometric closure and density conclusions must use the shared variety model. -/
theorem conformal_null_plane_span (q : QuadraticForm ℂ W) (x0 : W)
    (L : Submodule ℂ W) (hnull : ∀ x ∈ L, q x = 0) :
    let H := Submodule.span ℂ
      (conformalLift q '' {x : W | x - x0 ∈ L})
    Module.finrank ℂ H = Module.finrank ℂ L + 1 ∧
      ∀ x ∈ H, hyperbolicValue q x = 0 := by
  classical
  let H : Submodule ℂ (ℂ × (W × ℂ)) := Submodule.span ℂ
    (conformalLift q '' {x : W | x - x0 ∈ L})
  change Module.finrank ℂ H = Module.finrank ℂ L + 1 ∧
    ∀ x ∈ H, hyperbolicValue q x = 0
  let d : L →ₗ[ℂ] (ℂ × (W × ℂ)) :=
    { toFun := fun w => (0, (w.1, -(q.polarBilin x0 w.1)))
      map_add' := by
        intro u v
        apply Prod.ext
        · simp
        · apply Prod.ext
          · rfl
          · change -(q.polarBilin x0 (u.1 + v.1)) =
              -(q.polarBilin x0 u.1) + -(q.polarBilin x0 v.1)
            simp only [map_add]
            abel
      map_smul' := by
        intro c w
        apply Prod.ext
        · simp
        · apply Prod.ext
          · rfl
          · simp [smul_eq_mul] }
  let g : ℂ × L →ₗ[ℂ] (ℂ × (W × ℂ)) :=
    { toFun := fun z => z.1 • conformalLift q x0 + d z.2
      map_add' := by
        intro z z'
        simp only [Prod.fst_add, Prod.snd_add, add_smul, map_add]
        abel
      map_smul' := by intro c z; simp [smul_smul] }
  have hqsum (w : L) : q (x0 + w.1) = q x0 + q.polarBilin x0 w.1 := by
    rw [QuadraticMap.map_add q x0 w.1, hnull w.1 w.2]
    simp [QuadraticMap.polarBilin_apply_apply]
  have hlift (x : W) (hx : x - x0 ∈ L) :
      conformalLift q x = g (1, ⟨x - x0, hx⟩) := by
    let w : L := ⟨x - x0, hx⟩
    have hq : q x = q x0 + q.polarBilin x0 (x - x0) := by
      calc
        q x = q (x0 + (x - x0)) := by congr 1 <;> abel
        _ = q x0 + q.polarBilin x0 (x - x0) := hqsum w
    apply Prod.ext
    · simp [g, d, conformalLift]
    · apply Prod.ext
      · simp [g, d, conformalLift]
      · simp [g, d, conformalLift, hq, smul_eq_mul]
        abel
  have hg : Function.Injective g := by
    intro z z' hzz'
    have hfst : z.1 = z'.1 := by
      have h := congrArg Prod.fst hzz'
      simpa [g, d, conformalLift] using h
    have hmid : z.1 • x0 + z.2.1 = z'.1 • x0 + z'.2.1 := by
      have h := congrArg (fun y : ℂ × (W × ℂ) => y.2.1) hzz'
      simpa [g, d, conformalLift] using h
    apply Prod.ext hfst
    apply Subtype.ext
    rw [hfst] at hmid
    exact add_left_cancel hmid
  have hbase : conformalLift q x0 ∈ H := by
    apply Submodule.subset_span
    exact ⟨x0, by simp, rfl⟩
  have htranslated (w : L) : conformalLift q (x0 + w.1) ∈ H := by
    apply Submodule.subset_span
    refine ⟨x0 + w.1, ?_, rfl⟩
    simpa using w.2
  have hdirection (w : L) : d w ∈ H := by
    have hd : conformalLift q (x0 + w.1) - conformalLift q x0 = d w := by
      apply Prod.ext
      · simp [conformalLift, d]
      · apply Prod.ext
        · simp [conformalLift, d]
        · simp only [conformalLift, d]
          change -q (x0 + w.1) - -q x0 = -q.polarBilin x0 w.1
          rw [hqsum]
          ring_nf
    rw [← hd]
    exact H.sub_mem (htranslated w) hbase
  have hrange_le : LinearMap.range g ≤ H := by
    rintro z ⟨a, rfl⟩
    exact H.add_mem (H.smul_mem _ hbase) (hdirection a.2)
  have hspan_le : H ≤ LinearMap.range g := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    rw [hlift x hx]
    exact ⟨(1, ⟨x - x0, hx⟩), rfl⟩
  have hH : H = LinearMap.range g := le_antisymm hspan_le hrange_le
  have hquad (c : ℂ) (w : L) :
      q (c • x0 + w.1) = c ^ 2 * q x0 + c * q.polarBilin x0 w.1 := by
    calc
      q (c • x0 + w.1) =
          q (c • x0) + q w.1 + QuadraticMap.polar q (c • x0) w.1 :=
        QuadraticMap.map_add q (c • x0) w.1
      _ = c ^ 2 * q x0 + c * q.polarBilin x0 w.1 := by
        rw [QuadraticMap.map_smul q c x0, hnull w.1 w.2]
        rw [QuadraticMap.polar_smul_left q c x0 w.1]
        rw [← QuadraticMap.polarBilin_apply_apply]
        simp only [smul_eq_mul]
        ring
  have hvalue (c : ℂ) (w : L) : hyperbolicValue q (g (c, w)) = 0 := by
    simp only [hyperbolicValue, g, LinearMap.coe_mk, AddHom.coe_mk,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, d,
      conformalLift, one_smul, zero_add, smul_eq_mul]
    rw [hquad]
    ring
  constructor
  · rw [hH, LinearMap.finrank_range_of_inj hg, Module.finrank_prod]
    rw [Module.finrank_self]
    exact Nat.add_comm _ _
  · intro x hx
    rw [hH] at hx
    obtain ⟨z, rfl⟩ := hx
    exact hvalue z.1 z.2

end ConformalChart

end DistinctDistances.TrackB
