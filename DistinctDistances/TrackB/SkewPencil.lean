import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.CharZero.Infinite

/-!
Model-independent linear algebra for concentration.tex:793–930. The geometric
differential-rank argument is a separate node and must establish the pencil hypothesis.
The pairing is complex bilinear, not a Hermitian inner product.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false

open LinearMap (BilinForm)
open scoped BigOperators

variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

/-- Alternating forms, as an actual subspace of bilinear forms. -/
def alternatingForms : Submodule ℂ (BilinForm ℂ U) where
  carrier := {D | D.IsAlt}
  zero_mem' := LinearMap.BilinForm.isAlt_zero
  add_mem' := fun hD hE => hD.add hE
  smul_mem' := fun c _ hD => hD.smul c

/-- The point-evaluation pencil after tangent coordinates and vertical directions are removed. -/
def skewPencil (Θ : Submodule ℂ (U × Module.Dual ℂ U)) (D : BilinForm ℂ U) :
    Θ →ₗ[ℂ] Module.Dual ℂ U :=
  LinearMap.comp ((LinearMap.snd ℂ U (Module.Dual ℂ U)) -
    LinearMap.comp D (LinearMap.fst ℂ U (Module.Dual ℂ U))) Θ.subtype

/-- B23, concentration.tex:853–854: the projected tangent and vertical dimensions. -/
theorem projected_vertical_finrank (Θ : Submodule ℂ (U × Module.Dual ℂ U))
    (hΘ : Module.finrank ℂ Θ = Module.finrank ℂ U) :
    Module.finrank ℂ ↥(Θ.map (LinearMap.fst ℂ U (Module.Dual ℂ U))) +
      Module.finrank ℂ ↥(Θ ⊓ LinearMap.ker (LinearMap.fst ℂ U (Module.Dual ℂ U))) =
        Module.finrank ℂ U := by
  let f : Θ →ₗ[ℂ] U :=
    LinearMap.comp (LinearMap.fst ℂ U (Module.Dual ℂ U)) Θ.subtype
  have hrange : LinearMap.range f = Θ.map (LinearMap.fst ℂ U (Module.Dual ℂ U)) := by
    ext x
    simp [f, Submodule.mem_map]
  have hkerMap : (LinearMap.ker f).map Θ.subtype =
      Θ ⊓ LinearMap.ker (LinearMap.fst ℂ U (Module.Dual ℂ U)) := by
    ext ⟨u, v⟩
    simp [f, Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, and_comm]
  have hkerFinrank : Module.finrank ℂ (LinearMap.ker f) =
      Module.finrank ℂ ↥(Θ ⊓ LinearMap.ker (LinearMap.fst ℂ U (Module.Dual ℂ U))) := by
    rw [← hkerMap]
    exact (Submodule.finrank_map_subtype_eq Θ (LinearMap.ker f)).symm
  calc
    Module.finrank ℂ ↥(Θ.map (LinearMap.fst ℂ U (Module.Dual ℂ U))) +
        Module.finrank ℂ ↥(Θ ⊓ LinearMap.ker (LinearMap.fst ℂ U (Module.Dual ℂ U))) =
      Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.ker f) := by
        rw [← hrange, ← hkerFinrank]
    _ = Module.finrank ℂ Θ := LinearMap.finrank_range_add_finrank_ker f
    _ = Module.finrank ℂ U := hΘ

/-- The projected subspace `A_*` from conc:deg-quotient-pencil. -/
def projectedTangent (Θ : Submodule ℂ (U × Module.Dual ℂ U)) : Submodule ℂ U :=
  Θ.map (LinearMap.fst ℂ U (Module.Dual ℂ U))

/-- The vertical subspace `B_*`, considered inside the dual rather than the product. -/
def verticalTangent (Θ : Submodule ℂ (U × Module.Dual ℂ U)) :
    Submodule ℂ (Module.Dual ℂ U) :=
  Θ.comap (LinearMap.inr ℂ U (Module.Dual ℂ U))

/-- Restrict the two arguments of a bilinear form to the indicated subspaces. -/
def skewRestriction (A H : Submodule ℂ U) (D : BilinForm ℂ U) :
    A →ₗ[ℂ] Module.Dual ℂ H :=
  LinearMap.comp H.dualRestrict (LinearMap.comp D A.subtype)

/-- The surjective projection from Θ to its first-coordinate image. -/
def tangentProjection (Θ : Submodule ℂ (U × Module.Dual ℂ U)) :
    Θ →ₗ[ℂ] projectedTangent Θ where
  toFun := fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- B23, concentration.tex:853–856. -/
theorem projection_annihilator_finrank (Θ : Submodule ℂ (U × Module.Dual ℂ U))
    (hΘ : Module.finrank ℂ Θ = Module.finrank ℂ U) :
    Module.finrank ℂ (projectedTangent Θ) =
      Module.finrank ℂ (verticalTangent Θ).dualCoannihilator := by
  let ι : Module.Dual ℂ U →ₗ[ℂ] U × Module.Dual ℂ U :=
    LinearMap.inr ℂ U (Module.Dual ℂ U)
  have hverticalMap : (verticalTangent Θ).map ι =
      Θ ⊓ LinearMap.ker (LinearMap.fst ℂ U (Module.Dual ℂ U)) := by
    ext ⟨u, v⟩
    simp [verticalTangent, ι, Submodule.mem_map, Submodule.mem_comap,
      Submodule.mem_inf, LinearMap.mem_ker]
    constructor
    · rintro ⟨rfl, hΘ⟩
      exact ⟨hΘ, rfl⟩
    · rintro ⟨hΘ, rfl⟩
      exact ⟨rfl, hΘ⟩
  let g : ↥(verticalTangent Θ) →ₗ[ℂ] U × Module.Dual ℂ U :=
    LinearMap.comp ι (verticalTangent Θ).subtype
  have hgInj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have hpair : (0, (x : Module.Dual ℂ U)) = (0, (y : Module.Dual ℂ U)) := by
      simpa [g, ι] using hxy
    exact congrArg Prod.snd hpair
  have hrange : LinearMap.range g = (verticalTangent Θ).map ι := by
    ext z
    simp [g, Submodule.mem_map]
  have hverticalFinrank :
      Module.finrank ℂ ↥(Θ ⊓ LinearMap.ker (LinearMap.fst ℂ U (Module.Dual ℂ U))) =
        Module.finrank ℂ (verticalTangent Θ) := by
    have h := LinearMap.finrank_range_of_inj hgInj
    rw [hrange, hverticalMap] at h
    exact h
  have hdual : Module.finrank ℂ (verticalTangent Θ) +
      Module.finrank ℂ (verticalTangent Θ).dualCoannihilator = Module.finrank ℂ U := by
    simpa only [Subspace.dual_finrank_eq] using
      (Subspace.finrank_add_finrank_dualCoannihilator_eq (verticalTangent Θ))
  have hprojected := projected_vertical_finrank Θ hΘ
  change Module.finrank ℂ (Θ.map (LinearMap.fst ℂ U (Module.Dual ℂ U))) +
      Module.finrank ℂ ↥(Θ ⊓ LinearMap.ker (LinearMap.fst ℂ U (Module.Dual ℂ U))) =
        Module.finrank ℂ U at hprojected
  change Module.finrank ℂ (Θ.map (LinearMap.fst ℂ U (Module.Dual ℂ U))) =
    Module.finrank ℂ (verticalTangent Θ).dualCoannihilator
  omega

/-- B23, conc:deg-quotient-pencil, concentration.tex:854–868. This states the induced
map and the invertibility equivalence without choosing determinant bases. -/
theorem quotient_skew_pencil (Θ : Submodule ℂ (U × Module.Dual ℂ U))
    (hΘ : Module.finrank ℂ Θ = Module.finrank ℂ U) :
    ∃ C : projectedTangent Θ →ₗ[ℂ] Module.Dual ℂ (verticalTangent Θ).dualCoannihilator,
      (∀ x : Θ, ∀ h : (verticalTangent Θ).dualCoannihilator,
        C (tangentProjection Θ x) h = x.1.2 h.1) ∧
      (∀ D : BilinForm ℂ U, Function.Bijective (skewPencil Θ D) ↔
        Function.Bijective
          (C - skewRestriction (projectedTangent Θ) (verticalTangent Θ).dualCoannihilator D)) := by
  classical
  let A := projectedTangent Θ
  let B := verticalTangent Θ
  let H := B.dualCoannihilator
  let P := tangentProjection Θ
  have hP : Function.Surjective P := by
    rintro ⟨a, ha⟩
    obtain ⟨w, hw, heq⟩ := ha
    exact ⟨⟨w, hw⟩, Subtype.ext heq⟩
  obtain ⟨s, hs⟩ := P.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hP)
  let μ : Θ →ₗ[ℂ] Module.Dual ℂ U :=
    (LinearMap.snd ℂ U (Module.Dual ℂ U)).comp Θ.subtype
  let C : A →ₗ[ℂ] Module.Dual ℂ H := H.dualRestrict.comp (μ.comp s)
  have heval : ∀ (x : Θ) (h : H), C (P x) h = x.1.2 h.1 := by
    intro x h
    have hfst : (s (P x)).1.1 = x.1.1 := by
      have h := congrArg Subtype.val (LinearMap.congr_fun hs (P x))
      exact h
    let b : Module.Dual ℂ U := (s (P x)).1.2 - x.1.2
    have hb : b ∈ B := by
      change (0, b) ∈ Θ
      have ht := Θ.sub_mem (s (P x)).2 x.2
      have heq : (0, b) = (s (P x)).1 - x.1 := by
        apply Prod.ext
        · change 0 = (s (P x)).1.1 - x.1.1
          simp [hfst]
        · rfl
      rw [heq]
      exact ht
    have hz := (Submodule.mem_dualCoannihilator h.1).mp h.2 b hb
    change (s (P x)).1.2 h.1 - x.1.2 h.1 = 0 at hz
    exact sub_eq_zero.mp hz
  have hdimA : Module.finrank ℂ A = Module.finrank ℂ H := by
    simpa [A, H] using projection_annihilator_finrank Θ hΘ
  let v : B →ₗ[ℂ] Θ :=
    { toFun := fun b => ⟨(0, b.1), by
        have hb := b.2
        change LinearMap.inr ℂ U (Module.Dual ℂ U) b.1 ∈ Θ at hb
        simpa using hb⟩
      map_add' := by intros; apply Subtype.ext; apply Prod.ext <;> simp
      map_smul' := by intros; apply Subtype.ext; apply Prod.ext <;> simp }
  have hvP : ∀ b : B, P (v b) = 0 := by
    intro b
    apply Subtype.ext
    rfl
  have hvL (D : BilinForm ℂ U) (b : B) : skewPencil Θ D (v b) = b.1 := by
    apply LinearMap.ext
    intro u
    simp [skewPencil, v]
  have hdouble : H.dualAnnihilator = B := by
    simpa [H] using
      (Subspace.dualCoannihilator_dualAnnihilator_eq (W := B))
  have hpoint (D : BilinForm ℂ U) (x : Θ) (h : H) :
      (C - skewRestriction A H D) (P x) h = skewPencil Θ D x h.1 := by
    change C (P x) h - D (P x).1 h.1 =
      (x.1.2 - D x.1.1) h.1
    rw [heval x h]
    rfl
  refine ⟨C, heval, ?_⟩
  intro D
  let F : A →ₗ[ℂ] Module.Dual ℂ H := C - skewRestriction A H D
  let L : Θ →ₗ[ℂ] Module.Dual ℂ U := skewPencil Θ D
  have hinj_iff : Function.Injective L ↔ Function.Injective F := by
    constructor
    · intro hL
      apply LinearMap.ker_eq_bot.mp
      apply le_antisymm ?_ bot_le
      intro a ha
      change F a = 0 at ha
      obtain ⟨x, hx⟩ := hP a
      have hFa : F (P x) = 0 := by rw [hx]; exact ha
      have hmem : L x ∈ H.dualAnnihilator := by
        apply (Submodule.mem_dualAnnihilator _).2
        intro h hh
        let h' : H := ⟨h, hh⟩
        have hz := congrArg (fun f : Module.Dual ℂ H => f h') hFa
        have hp := hpoint D x h'
        have hp' : F (P x) h' = L x h := by simpa [F, L, h'] using hp
        exact hp'.symm.trans (by simpa using hz)
      have hmemB : L x ∈ B := hdouble ▸ hmem
      let b : B := ⟨L x, hmemB⟩
      have hzero : L (x - v b) = 0 := by
        rw [map_sub, hvL D b]
        simp [b]
      have heq : x - v b = 0 := hL (by simpa using hzero)
      have hp := congrArg P heq
      have ha0 : a = 0 := by
        apply Subtype.ext
        have hval := congrArg Subtype.val hp
        simpa [map_sub, hvP, hx] using hval
      exact ha0
    · intro hF
      apply LinearMap.ker_eq_bot.mp
      apply le_antisymm ?_ bot_le
      intro x hx
      change x = 0
      have hx' : L x = 0 := hx
      have hFx : F (P x) = 0 := by
        apply LinearMap.ext
        intro h
        have hp : F (P x) h = L x h := hpoint D x h
        change F (P x) h = 0
        rw [hp]
        simp [hx']
      have hPx : P x = 0 := hF (by simpa using hFx)
      have hfst : x.1.1 = 0 := congrArg Subtype.val hPx
      have hsnd : x.1.2 = 0 := by
        change x.1.2 - D x.1.1 = 0 at hx'
        rw [hfst] at hx'
        simpa using hx'
      apply Subtype.ext
      exact Prod.ext hfst hsnd
  have hLdim : Module.finrank ℂ Θ = Module.finrank ℂ (Module.Dual ℂ U) :=
    hΘ.trans Subspace.dual_finrank_eq.symm
  have hFdim : Module.finrank ℂ A = Module.finrank ℂ (Module.Dual ℂ H) :=
    hdimA.trans Subspace.dual_finrank_eq.symm
  have hLbij : Function.Bijective L ↔ Function.Injective L := by
    constructor
    · exact And.left
    · intro hi
      exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hLdim).mp hi⟩
  have hFbij : Function.Bijective F ↔ Function.Injective F := by
    constructor
    · exact And.left
    · intro hi
      exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hFdim).mp hi⟩
  constructor
  · intro h
    exact hFbij.mpr (hinj_iff.mp (hLbij.mp h))
  · intro h
    exact hLbij.mpr (hinj_iff.mpr (hFbij.mp h))

namespace SquareSkewPencil

/-- The alternating form used in B24 on an even-dimensional coordinate space. -/
noncomputable def standardAlternating (k : ℕ) :
    BilinForm ℂ ((Fin k → ℂ) × (Fin k → ℂ)) :=
  LinearMap.mk₂ ℂ
    (fun x y => (∑ i, x.2 i * y.1 i) - ∑ i, x.1 i * y.2 i)
    (by intros; simp [add_mul, Finset.sum_add_distrib]; ring)
    (by
      intros
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        mul_assoc, ← Finset.mul_sum, mul_sub])
    (by intros; simp [mul_add, Finset.sum_add_distrib]; ring)
    (by
      intros
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        mul_left_comm, ← Finset.mul_sum, mul_sub])

theorem standardAlternating_isAlt (k : ℕ) : (standardAlternating k).IsAlt := by
  intro x
  simp [standardAlternating, mul_comm]

theorem standardAlternating_injective (k : ℕ) :
    Function.Injective (standardAlternating k) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  have hx' : standardAlternating k x = 0 := hx
  have h1 : x.1 = 0 := by
    funext i
    have h := congrArg (fun f : Module.Dual ℂ ((Fin k → ℂ) × (Fin k → ℂ)) =>
      f (0, Pi.single i 1)) hx'
    simpa [standardAlternating, Pi.single_apply] using h
  have h2 : x.2 = 0 := by
    funext i
    have h := congrArg (fun f : Module.Dual ℂ ((Fin k → ℂ) × (Fin k → ℂ)) =>
      f (Pi.single i 1, 0)) hx'
    simpa [standardAlternating, Pi.single_apply] using h
  exact Prod.ext h1 h2

theorem even_dimensional_alternating_bijection
    (heven : Even (Module.finrank ℂ U)) :
    ∃ D : BilinForm ℂ U, D.IsAlt ∧ Function.Bijective D := by
  obtain ⟨k, hk⟩ := heven
  let E : U ≃ₗ[ℂ] ((Fin k → ℂ) × (Fin k → ℂ)) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hk)
  let D := (standardAlternating k).compl₁₂ E.toLinearMap E.toLinearMap
  have hD : D.IsAlt := fun x => standardAlternating_isAlt k (E x)
  have hinj : Function.Injective D := by
    intro x y hxy
    apply E.injective
    apply standardAlternating_injective k
    apply LinearMap.ext
    intro z
    have := congrArg (fun f : Module.Dual ℂ U => f (E.symm z)) hxy
    simpa [D] using this
  exact ⟨D, hD, hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq.symm)).mp hinj⟩

/-- The scalar pencil is regular away from the finite spectrum of J⁻¹C.
Used by the even-dimensional contradiction in concentration.tex:888–906. -/
theorem alternating_bijection_has_regular_pencil_member (C J : BilinForm ℂ U)
    (hJ : J.IsAlt) (hbij : Function.Bijective J) :
    ∃ D : BilinForm ℂ U, D.IsAlt ∧ Function.Bijective (C - D) := by
  let E : U ≃ₗ[ℂ] Module.Dual ℂ U := LinearEquiv.ofBijective J hbij
  let T : Module.End ℂ U := E.symm.toLinearMap.comp C
  obtain ⟨t, ht⟩ := (Module.End.finite_spectrum T).exists_notMem
  have hunit : IsUnit (algebraMap ℂ (Module.End ℂ U) t - T) := by
    simpa only [spectrum.mem_iff, not_not] using ht
  have hinjT : Function.Injective (algebraMap ℂ (Module.End ℂ U) t - T) :=
    LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hunit)
  have hinj : Function.Injective (C - t • J) := by
    intro x y hxy
    apply hinjT
    apply E.injective
    have h : t • J x - C x = t • J y - C y := by
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, neg_sub] using
        congrArg Neg.neg hxy
    simpa [T, E, Algebra.algebraMap_eq_smul_one] using h
  exact ⟨t • J, hJ.smul t, hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq.symm)).mp hinj⟩

theorem even_dimensional_skew_perturbation (C : BilinForm ℂ U)
    (heven : Even (Module.finrank ℂ U)) :
    ∃ D : BilinForm ℂ U, D.IsAlt ∧ Function.Bijective (C - D) := by
  obtain ⟨J, hJ, hbij⟩ := even_dimensional_alternating_bijection heven
  exact alternating_bijection_has_regular_pencil_member C J hJ hbij

/-- For C(x,x) ≠ 0, splitting off x reduces the odd-dimensional case to
the even-dimensional form on ker C(-,x). This proves the contradiction needed
at concentration.tex:907–921 without a determinant coefficient calculation. -/
theorem odd_dimensional_nonalt_skew_perturbation (C : BilinForm ℂ U)
    (hodd : Odd (Module.finrank ℂ U)) (hnot : ¬ C.IsAlt) :
    ∃ D : BilinForm ℂ U, D.IsAlt ∧ Function.Bijective (C - D) := by
  classical
  change ¬ ∀ x, C x x = 0 at hnot
  obtain ⟨x, hxx⟩ := not_forall.mp hnot
  let f : Module.Dual ℂ U := C.flip x
  let H : Submodule ℂ U := LinearMap.ker f
  let rho : Module.Dual ℂ U := (C x x)⁻¹ • f
  have hrho : rho x = 1 := by simp [rho, f, hxx]
  have hf : Function.Surjective f := by
    intro c
    refine ⟨(c * (C x x)⁻¹) • x, ?_⟩
    simp [f, hxx]
  have hdim : 1 + Module.finrank ℂ H = Module.finrank ℂ U := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rwa [LinearMap.range_eq_top.mpr hf, finrank_top, Module.finrank_self] at h
  have heven : Even (Module.finrank ℂ H) := by
    obtain ⟨k, hk⟩ := hodd
    refine ⟨k, ?_⟩
    omega
  let pi : U →ₗ[ℂ] H :=
    (LinearMap.id - (LinearMap.toSpanSingleton ℂ U x).comp rho).codRestrict H (by
      intro v
      change f (v - rho v • x) = 0
      simp only [map_sub, map_smul, smul_eq_mul, rho, LinearMap.smul_apply]
      change f v - ((C x x)⁻¹ * f v) * (C x x) = 0
      rw [mul_right_comm, inv_mul_cancel₀ hxx, one_mul, sub_self])
  have hpi_x : pi x = 0 := by
    apply Subtype.ext
    change x - rho x • x = 0
    simp [hrho]
  have hpi_H : ∀ v : H, pi v = v := by
    intro v
    apply Subtype.ext
    change v.1 - rho v.1 • x = v.1
    have hv : f v.1 = 0 := v.2
    simp [rho, hv]
  let C' : BilinForm ℂ H := C.compl₁₂ H.subtype H.subtype
  obtain ⟨D', hD', hbij⟩ := even_dimensional_skew_perturbation C' heven
  let D : BilinForm ℂ U := D'.compl₁₂ pi pi
  have hD : D.IsAlt := fun v => hD' (pi v)
  have hinj : Function.Injective (C - D) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    have hv' : (C - D) v = 0 := hv
    have hfv : f v = 0 := by
      have h := congrArg (fun l : Module.Dual ℂ U => l x) hv'
      simpa [D, hpi_x, f] using h
    let w : H := ⟨v, hfv⟩
    have hpi_v : pi v = w := hpi_H w
    have hw : (C' - D') w = 0 := by
      apply LinearMap.ext
      intro z
      have h := congrArg (fun l : Module.Dual ℂ U => l z.1) hv'
      simpa [C', D, w, hpi_v, hpi_H z] using h
    have hw0 : w = 0 := hbij.1 (by simpa using hw)
    exact congrArg Subtype.val hw0
  exact ⟨D, hD, hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq.symm)).mp hinj⟩

end SquareSkewPencil

namespace MixedSkewPencil

section CoordinateForms

/-- Coordinate pairing for the complementary rows and columns in B24. -/
noncomputable def dotForm (n : ℕ) : BilinForm ℂ (Fin n → ℂ) :=
  LinearMap.mk₂ ℂ (fun x y => ∑ i, x i * y i)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum])

theorem dotForm_injective (n : ℕ) : Function.Injective (dotForm n) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  funext i
  have hx' : dotForm n x = 0 := hx
  have h := congrArg (fun f : Module.Dual ℂ (Fin n → ℂ) => f (Pi.single i 1)) hx'
  simpa [dotForm, Pi.single_apply] using h

variable {I V : Type*} [AddCommGroup I] [Module ℂ I]
  [AddCommGroup V] [Module ℂ V]

def leftEmbedding : (I × V) →ₗ[ℂ] (I × (V × V)) where
  toFun := fun x => (x.1, (x.2, 0))
  map_add' := by intros; simp
  map_smul' := by intros; simp

def rightEmbedding : (I × V) →ₗ[ℂ] (I × (V × V)) where
  toFun := fun x => (x.1, (0, x.2))
  map_add' := by intros; simp
  map_smul' := by intros; simp

noncomputable def evenMixedForm (J : BilinForm ℂ I) (n : ℕ) :
    BilinForm ℂ (I × ((Fin n → ℂ) × (Fin n → ℂ))) :=
  LinearMap.mk₂ ℂ
    (fun x y => J x.1 y.1 + dotForm n x.2.1 y.2.2 - dotForm n y.2.1 x.2.2)
    (by intros; simp [map_add]; ring)
    (by intros; simp [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp [map_add]; ring)
    (by intros; simp [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)

theorem evenMixedForm_isAlt (J : BilinForm ℂ I) (hJ : J.IsAlt) (n : ℕ) :
    (evenMixedForm J n).IsAlt := by
  intro x
  simp [evenMixedForm, hJ x.1]

variable [FiniteDimensional ℂ I]

theorem evenMixedForm_restriction_bijective (J : BilinForm ℂ I)
    (hJ : Function.Injective J) (n : ℕ) :
    Function.Bijective ((evenMixedForm J n).compl₁₂ leftEmbedding rightEmbedding) := by
  let P := (evenMixedForm J n).compl₁₂ leftEmbedding rightEmbedding
  have hinj : Function.Injective P := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    rintro ⟨c, a⟩ hx
    change (c, a) = 0
    have hx' : P (c, a) = 0 := hx
    have hJc : J c = 0 := by
      apply LinearMap.ext
      intro d
      have h := congrArg (fun f : Module.Dual ℂ (I × (Fin n → ℂ)) => f (d, 0)) hx'
      simpa [P, evenMixedForm, leftEmbedding, rightEmbedding] using h
    have hc0 : c = 0 := hJ (by simpa using hJc)
    have hda : dotForm n a = 0 := by
      apply LinearMap.ext
      intro b
      have h := congrArg (fun f : Module.Dual ℂ (I × (Fin n → ℂ)) => f (0, b)) hx'
      simpa [P, evenMixedForm, leftEmbedding, rightEmbedding] using h
    have ha0 : a = 0 := dotForm_injective n (by simpa using hda)
    exact Prod.ext hc0 ha0
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq.symm)).mp hinj⟩

/-- The even alternating block, the mixed [[0,1],[1,0]] block and the
remaining coordinate pairing in concentration.tex:889–895. -/
noncomputable def oddMixedForm (J : BilinForm ℂ I) (n : ℕ) :
    BilinForm ℂ ((I × ℂ) × ((ℂ × (Fin n → ℂ)) × (ℂ × (Fin n → ℂ)))) :=
  LinearMap.mk₂ ℂ
    (fun x y => J x.1.1 y.1.1 + x.1.2 * y.2.2.1 - y.1.2 * x.2.2.1 +
      x.2.1.1 * y.1.2 - y.2.1.1 * x.1.2 +
      dotForm n x.2.1.2 y.2.2.2 - dotForm n y.2.1.2 x.2.2.2)
    (by intros; simp [map_add, add_mul]; ring)
    (by intros; simp [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp [map_add, mul_add]; ring)
    (by intros; simp [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)

theorem oddMixedForm_isAlt (J : BilinForm ℂ I) (hJ : J.IsAlt) (n : ℕ) :
    (oddMixedForm J n).IsAlt := by
  intro x
  simp only [oddMixedForm, LinearMap.mk₂_apply, hJ x.1.1]
  ring

theorem oddMixedForm_restriction_bijective (J : BilinForm ℂ I)
    (hJ : Function.Injective J) (n : ℕ) :
    Function.Bijective ((oddMixedForm J n).compl₁₂ leftEmbedding rightEmbedding) := by
  let P := (oddMixedForm J n).compl₁₂ leftEmbedding rightEmbedding
  have hinj : Function.Injective P := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    rintro ⟨⟨g, t⟩, ⟨u, a⟩⟩ hx
    change ((g, t), (u, a)) = 0
    have hx' : P ((g, t), (u, a)) = 0 := hx
    have hg : J g = 0 := by
      apply LinearMap.ext
      intro d
      have h := congrArg
        (fun f : Module.Dual ℂ ((I × ℂ) × (ℂ × (Fin n → ℂ))) => f ((d, 0), (0, 0))) hx'
      simpa [P, oddMixedForm, leftEmbedding, rightEmbedding] using h
    have hg0 : g = 0 := hJ (by simpa using hg)
    have ht : t = 0 := by
      have h := congrArg
        (fun f : Module.Dual ℂ ((I × ℂ) × (ℂ × (Fin n → ℂ))) => f ((0, 0), (1, 0))) hx'
      simpa [P, oddMixedForm, leftEmbedding, rightEmbedding] using h
    have hu : u = 0 := by
      have h := congrArg
        (fun f : Module.Dual ℂ ((I × ℂ) × (ℂ × (Fin n → ℂ))) => f ((0, 1), (0, 0))) hx'
      simpa [P, oddMixedForm, leftEmbedding, rightEmbedding] using h
    have hda : dotForm n a = 0 := by
      apply LinearMap.ext
      intro b
      have h := congrArg
        (fun f : Module.Dual ℂ ((I × ℂ) × (ℂ × (Fin n → ℂ))) => f ((0, 0), (0, b))) hx'
      simpa [P, oddMixedForm, leftEmbedding, rightEmbedding] using h
    have ha0 : a = 0 := dotForm_injective n (by simpa using hda)
    exact Prod.ext (Prod.ext hg0 ht) (Prod.ext hu ha0)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq.symm)).mp hinj⟩

end CoordinateForms
section Decomposition

variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

/-- Split the common intersection and the two complementary directions,
then retract the ambient space onto that sum (concentration.tex:870–883). -/
theorem common_subspace_decomposition (A H : Submodule ℂ U) :
    ∃ (A0 : Submodule ℂ A) (H0 : Submodule ℂ H)
      (EA : (↥(A ⊓ H) × A0) ≃ₗ[ℂ] A) (EH : (↥(A ⊓ H) × H0) ≃ₗ[ℂ] H)
      (S : (↥(A ⊓ H) × (A0 × H0)) →ₗ[ℂ] U)
      (R : U →ₗ[ℂ] (↥(A ⊓ H) × (A0 × H0))),
      R.comp S = LinearMap.id ∧
      (∀ (c : ↥(A ⊓ H)) (a : A0), S (c, (a, 0)) = (EA (c, a) : U)) ∧
      (∀ (c : ↥(A ⊓ H)) (h : H0), S (c, (0, h)) = (EH (c, h) : U)) := by
  let I := A ⊓ H
  let IA : Submodule ℂ A := I.comap A.subtype
  let IH : Submodule ℂ H := I.comap H.subtype
  obtain ⟨A0, hA0⟩ := IA.exists_isCompl
  obtain ⟨H0, hH0⟩ := IH.exists_isCompl
  let iA : I ≃ₗ[ℂ] IA := (Submodule.comapSubtypeEquivOfLe inf_le_left).symm
  let iH : I ≃ₗ[ℂ] IH := (Submodule.comapSubtypeEquivOfLe inf_le_right).symm
  let EA : (I × A0) ≃ₗ[ℂ] A :=
    (iA.prodCongr (LinearEquiv.refl ℂ A0)).trans (IA.prodEquivOfIsCompl A0 hA0)
  let EH : (I × H0) ≃ₗ[ℂ] H :=
    (iH.prodCongr (LinearEquiv.refl ℂ H0)).trans (IH.prodEquivOfIsCompl H0 hH0)
  let S : (I × (A0 × H0)) →ₗ[ℂ] U :=
    { toFun := fun x => x.1.1 + x.2.1.1.1 + x.2.2.1.1
      map_add' := by
        intro x y
        change ((x.1 : U) + y.1) + ((x.2.1.1 : U) + y.2.1.1) +
            ((x.2.2.1 : U) + y.2.2.1) =
          ((x.1 : U) + x.2.1.1 + x.2.2.1) + ((y.1 : U) + y.2.1.1 + y.2.2.1)
        abel
      map_smul' := by intros; simp [smul_add] }
  have hS : Function.Injective S := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    rintro ⟨c, a, h⟩ hx
    change (c, a, h) = 0
    have hx' : (c : U) + (a.1 : U) + (h.1 : U) = 0 := hx
    have haH : (a.1 : U) ∈ H := by
      have heq : (a.1 : U) = -(c : U) - (h.1 : U) := by
        calc
          (a.1 : U) = ((c : U) + (a.1 : U) + (h.1 : U)) - c - h.1 := by abel
          _ = -(c : U) - (h.1 : U) := by rw [hx']; simp
      rw [heq]
      exact H.sub_mem (H.neg_mem c.2.2) h.1.2
    have haIA : a.1 ∈ IA := ⟨a.1.2, haH⟩
    have ha0 : a = 0 :=
      Submodule.eq_zero_of_coe_mem_of_disjoint hA0.disjoint.symm haIA
    have hhA : (h.1 : U) ∈ A := by
      have heq : (h.1 : U) = -(c : U) := by simpa [ha0] using eq_neg_of_add_eq_zero_right hx'
      rw [heq]
      exact A.neg_mem c.2.1
    have hhIH : h.1 ∈ IH := ⟨hhA, h.1.2⟩
    have hh0 : h = 0 :=
      Submodule.eq_zero_of_coe_mem_of_disjoint hH0.disjoint.symm hhIH
    have hc0 : c = 0 := by
      apply Subtype.ext
      simpa [ha0, hh0] using hx'
    exact Prod.ext hc0 (Prod.ext ha0 hh0)
  obtain ⟨R, hR⟩ := S.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hS)
  refine ⟨A0, H0, EA, EH, S, R, hR, ?_, ?_⟩
  · intro c a
    change (c : U) + (a.1 : U) + 0 = (c : U) + (a.1 : U)
    simp
  · intro c h
    change (c : U) + 0 + (h.1 : U) = (c : U) + (h.1 : U)
    simp


variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem restriction_bijective_of_coordinates (A H : Submodule ℂ U)
    (hdim : Module.finrank ℂ A = Module.finrank ℂ H)
    (E : A ≃ₗ[ℂ] M) (F : H ≃ₗ[ℂ] N) (D : BilinForm ℂ U)
    (P : M →ₗ[ℂ] Module.Dual ℂ N) (hP : Function.Injective P)
    (heval : ∀ (a : A) (h : H), D a.1 h.1 = P (E a) (F h)) :
    Function.Bijective (skewRestriction A H D) := by
  have hinj : Function.Injective (skewRestriction A H D) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    have ha' : skewRestriction A H D a = 0 := ha
    have hp : P (E a) = 0 := by
      apply LinearMap.ext
      intro n
      obtain ⟨h, rfl⟩ := F.surjective n
      have heq := congrArg (fun f : Module.Dual ℂ H => f h) ha'
      change D a.1 h.1 = 0 at heq
      rwa [heval a h] at heq
    have he0 : E a = 0 := hP (by simpa using hp)
    exact E.injective (by simpa using he0)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hdim.trans Subspace.dual_finrank_eq.symm)).mp hinj⟩

variable {I' V : Type*} [AddCommGroup I'] [Module ℂ I']
  [AddCommGroup V] [Module ℂ V]

theorem lift_mixed_form (A H : Submodule ℂ U)
    (hdim : Module.finrank ℂ A = Module.finrank ℂ H)
    (A0 : Submodule ℂ A) (H0 : Submodule ℂ H)
    (EA : (↥(A ⊓ H) × A0) ≃ₗ[ℂ] A) (EH : (↥(A ⊓ H) × H0) ≃ₗ[ℂ] H)
    (R : U →ₗ[ℂ] (↥(A ⊓ H) × (A0 × H0)))
    (hrA : ∀ (c : ↥(A ⊓ H)) (a : A0), R (EA (c, a) : U) = (c, (a, 0)))
    (hrH : ∀ (c : ↥(A ⊓ H)) (h : H0), R (EH (c, h) : U) = (c, (0, h)))
    (EI : ↥(A ⊓ H) ≃ₗ[ℂ] I') (E0 : A0 ≃ₗ[ℂ] V) (F0 : H0 ≃ₗ[ℂ] V)
    (D0 : BilinForm ℂ (I' × (V × V))) (hD0 : D0.IsAlt)
    (hbij : Function.Bijective (D0.compl₁₂ leftEmbedding rightEmbedding)) :
    ∃ D : BilinForm ℂ U, D.IsAlt ∧ Function.Bijective (skewRestriction A H D) := by
  let T := EI.prodCongr (E0.prodCongr F0)
  let RD := T.toLinearMap.comp R
  let D := D0.compl₁₂ RD RD
  let E := EA.symm.trans (EI.prodCongr E0)
  let F := EH.symm.trans (EI.prodCongr F0)
  let P := D0.compl₁₂ leftEmbedding rightEmbedding
  have heval : ∀ (a : A) (h : H), D a.1 h.1 = P (E a) (F h) := by
    intro a h
    obtain ⟨⟨c, a0⟩, rfl⟩ := EA.surjective a
    obtain ⟨⟨d, h0⟩, rfl⟩ := EH.surjective h
    simp [D, RD, T, E, F, P, hrA, hrH, leftEmbedding, rightEmbedding]
  exact ⟨D, (fun x => hD0 (RD x)),
    restriction_bijective_of_coordinates A H hdim E F D P hbij.1 heval⟩
end Decomposition

end MixedSkewPencil

/-- B24's mixed-basis step, concentration.tex:870–901. Only the common intersection
block has to be skew; the other restriction entries can be assigned independently. -/
theorem different_subspaces_skew_restriction (A H : Submodule ℂ U)
    (hdim : Module.finrank ℂ A = Module.finrank ℂ H) (hne : A ≠ H) :
    ∃ D : BilinForm ℂ U, D.IsAlt ∧ Function.Bijective (skewRestriction A H D) := by
  obtain ⟨A0, H0, EA, EH, S, R, hRS, hSA, hSH⟩ := MixedSkewPencil.common_subspace_decomposition A H
  have hrA : ∀ (c : ↥(A ⊓ H)) (a : A0), R (EA (c, a) : U) = (c, (a, 0)) := by
    intro c a
    rw [← hSA c a]
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hRS (c, (a, 0))
  have hrH : ∀ (c : ↥(A ⊓ H)) (h : H0), R (EH (c, h) : U) = (c, (0, h)) := by
    intro c h
    rw [← hSH c h]
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hRS (c, (0, h))
  let I := A ⊓ H
  have hEA : Module.finrank ℂ I + Module.finrank ℂ A0 = Module.finrank ℂ A := by
    simpa only [Module.finrank_prod] using EA.finrank_eq
  have hEH : Module.finrank ℂ I + Module.finrank ℂ H0 = Module.finrank ℂ H := by
    simpa only [Module.finrank_prod] using EH.finrank_eq
  have hd0 : Module.finrank ℂ A0 = Module.finrank ℂ H0 := by omega
  have hk : 1 ≤ Module.finrank ℂ A0 := by
    by_contra hbad
    have hiA : Module.finrank ℂ I = Module.finrank ℂ A := by omega
    have hiH : Module.finrank ℂ I = Module.finrank ℂ H := hiA.trans hdim
    have hIA : I = A := Submodule.eq_of_le_of_finrank_eq inf_le_left hiA
    have hIH : I = H := Submodule.eq_of_le_of_finrank_eq inf_le_right hiH
    exact hne (hIA.symm.trans hIH)
  rcases Nat.even_or_odd (Module.finrank ℂ I) with heven | hodd
  · let n := Module.finrank ℂ A0
    let E0 : A0 ≃ₗ[ℂ] (Fin n → ℂ) := LinearEquiv.ofFinrankEq _ _ (by simp [n])
    let F0 : H0 ≃ₗ[ℂ] (Fin n → ℂ) :=
      LinearEquiv.ofFinrankEq _ _ (by simpa [n] using hd0.symm)
    obtain ⟨J, hJ, hbij⟩ := SquareSkewPencil.even_dimensional_alternating_bijection heven
    exact MixedSkewPencil.lift_mixed_form A H hdim A0 H0 EA EH R hrA hrH
      (LinearEquiv.refl ℂ I) E0 F0 (MixedSkewPencil.evenMixedForm J n)
      (MixedSkewPencil.evenMixedForm_isAlt J hJ n) (MixedSkewPencil.evenMixedForm_restriction_bijective J hbij.1 n)
  · obtain ⟨q, hq⟩ := hodd
    let W := (Fin q → ℂ) × (Fin q → ℂ)
    let n := Module.finrank ℂ A0 - 1
    let EI : I ≃ₗ[ℂ] (W × ℂ) := LinearEquiv.ofFinrankEq _ _ (by simp [W]; omega)
    let E0 : A0 ≃ₗ[ℂ] (ℂ × (Fin n → ℂ)) :=
      LinearEquiv.ofFinrankEq _ _ (by simp [n]; omega)
    let F0 : H0 ≃ₗ[ℂ] (ℂ × (Fin n → ℂ)) :=
      LinearEquiv.ofFinrankEq _ _ (by simp [n]; omega)
    let J := SquareSkewPencil.standardAlternating q
    exact MixedSkewPencil.lift_mixed_form A H hdim A0 H0 EA EH R hrA hrH EI E0 F0 (MixedSkewPencil.oddMixedForm J n)
      (MixedSkewPencil.oddMixedForm_isAlt J (SquareSkewPencil.standardAlternating_isAlt q) n)
      (MixedSkewPencil.oddMixedForm_restriction_bijective J (SquareSkewPencil.standardAlternating_injective q) n)


/-- B24's final square-pencil step, concentration.tex:903–921. -/
theorem everywhere_singular_square_skew_pencil (C : BilinForm ℂ U)
    (hsingular : ∀ D : BilinForm ℂ U, D.IsAlt → ¬ Function.Bijective (C - D)) :
    Odd (Module.finrank ℂ U) ∧ C.IsAlt := by
  have hodd : Odd (Module.finrank ℂ U) := by
    rcases Nat.even_or_odd (Module.finrank ℂ U) with heven | hodd
    · obtain ⟨D, hD, hbij⟩ := SquareSkewPencil.even_dimensional_skew_perturbation C heven
      exact False.elim (hsingular D hD hbij)
    · exact hodd
  refine ⟨hodd, ?_⟩
  by_contra hnot
  obtain ⟨D, hD, hbij⟩ := SquareSkewPencil.odd_dimensional_nonalt_skew_perturbation C hodd hnot
  exact hsingular D hD hbij


namespace PlaneSkewPencil

/-- B24 only needs this direction of B23: a bijective quotient pencil lifts
to a bijective plane pencil. Its C is constructed from an actual linear section
of tangentProjection; the stronger impl iff interface remains independent. -/
theorem plane_quotient_reduction (Θ : Submodule ℂ (U × Module.Dual ℂ U))
    (hΘ : Module.finrank ℂ Θ = Module.finrank ℂ U) :
    Module.finrank ℂ (projectedTangent Θ) =
      Module.finrank ℂ (verticalTangent Θ).dualCoannihilator ∧
    ∃ C : projectedTangent Θ →ₗ[ℂ] Module.Dual ℂ (verticalTangent Θ).dualCoannihilator,
      (∀ (x : Θ) (h : (verticalTangent Θ).dualCoannihilator),
        C (tangentProjection Θ x) h = x.1.2 h.1) ∧
      (∀ D : BilinForm ℂ U,
        Function.Bijective
          (C - skewRestriction (projectedTangent Θ) (verticalTangent Θ).dualCoannihilator D) →
        Function.Bijective (skewPencil Θ D)) := by
  let A := projectedTangent Θ
  let B := verticalTangent Θ
  let H := B.dualCoannihilator
  let P := tangentProjection Θ
  have hP : Function.Surjective P := by
    rintro ⟨a, ha⟩
    obtain ⟨w, hw, heq⟩ := ha
    exact ⟨⟨w, hw⟩, Subtype.ext heq⟩
  let K := LinearMap.ker P
  let f : K →ₗ[ℂ] B :=
    { toFun := fun k => ⟨k.1.1.2, by
        have hk : P k.1 = 0 := k.2
        have hk0 : k.1.1.1 = 0 := congrArg Subtype.val hk
        change (0, k.1.1.2) ∈ Θ
        have heq : (0, k.1.1.2) = k.1.1 := Prod.ext hk0.symm rfl
        rw [heq]
        exact k.1.2⟩
      map_add' := by intros; apply Subtype.ext; rfl
      map_smul' := by intros; apply Subtype.ext; rfl }
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hx : P x.1 = 0 := x.2
      have hy : P y.1 = 0 := y.2
      exact (congrArg Subtype.val hx).trans (congrArg Subtype.val hy).symm
    · exact congrArg Subtype.val hxy
  have hf_surj : Function.Surjective f := by
    intro b
    let x : Θ := ⟨(0, b.1), b.2⟩
    have hx : P x = 0 := by apply Subtype.ext; rfl
    exact ⟨⟨x, hx⟩, rfl⟩
  let E := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hdimK : Module.finrank ℂ K = Module.finrank ℂ B := E.finrank_eq
  have hrank : Module.finrank ℂ A + Module.finrank ℂ B = Module.finrank ℂ Θ := by
    have h := LinearMap.finrank_range_add_finrank_ker P
    rwa [LinearMap.range_eq_top.mpr hP, finrank_top, hdimK] at h
  have hdimH := Subspace.finrank_add_finrank_dualCoannihilator_eq B
  have hdim : Module.finrank ℂ A = Module.finrank ℂ H := by
    change Module.finrank ℂ A = Module.finrank ℂ B.dualCoannihilator
    omega
  refine ⟨hdim, ?_⟩
  obtain ⟨s, hs⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hP)
  let mu : Θ →ₗ[ℂ] Module.Dual ℂ U :=
    (LinearMap.snd ℂ U (Module.Dual ℂ U)).comp Θ.subtype
  let C : A →ₗ[ℂ] Module.Dual ℂ H := H.dualRestrict.comp (mu.comp s)
  have heval : ∀ (x : Θ) (h : H), C (P x) h = x.1.2 h.1 := by
    intro x h
    have hfst : (s (P x)).1.1 = x.1.1 := by
      have h := congrArg Subtype.val (LinearMap.congr_fun hs (P x))
      exact h
    let b : Module.Dual ℂ U := (s (P x)).1.2 - x.1.2
    have hb : b ∈ B := by
      change (0, b) ∈ Θ
      have ht := Θ.sub_mem (s (P x)).2 x.2
      have heq : (0, b) = (s (P x)).1 - x.1 := by
        apply Prod.ext
        · change 0 = (s (P x)).1.1 - x.1.1
          simp [hfst]
        · rfl
      rw [heq]
      exact ht
    have hz := (Submodule.mem_dualCoannihilator h.1).mp h.2 b hb
    change (s (P x)).1.2 h.1 - x.1.2 h.1 = 0 at hz
    exact sub_eq_zero.mp hz
  refine ⟨C, heval, ?_⟩
  intro D hbij
  have hinj : Function.Injective (skewPencil Θ D) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    have hx' : skewPencil Θ D x = 0 := hx
    have hCx : (C - skewRestriction A H D) (P x) = 0 := by
      apply LinearMap.ext
      intro h
      have heq := congrArg (fun l : Module.Dual ℂ U => l h.1) hx'
      change C (P x) h - D (P x).1 h.1 = 0
      rw [heval x h]
      exact heq
    have hPx : P x = 0 := hbij.1 (by simpa using hCx)
    have hx0 : x.1.1 = 0 := congrArg Subtype.val hPx
    have hy0 : x.1.2 = 0 := by
      change x.1.2 - D x.1.1 = 0 at hx'
      simpa [hx0] using hx'
    apply Subtype.ext
    exact Prod.ext hx0 hy0
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hΘ.trans Subspace.dual_finrank_eq.symm)).mp hinj⟩


variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
  [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]

/-- The scalar pencil is invertible for some scalar when its leading map is bijective.
Used on the unequal row/column spaces in concentration.tex:897–901. -/
theorem regular_pencil_member (C J : M →ₗ[ℂ] N) (hJ : Function.Bijective J) :
    ∃ t : ℂ, Function.Bijective (C - t • J) := by
  let E : M ≃ₗ[ℂ] N := LinearEquiv.ofBijective J hJ
  let T : Module.End ℂ M := E.symm.toLinearMap.comp C
  obtain ⟨t, ht⟩ := (Module.End.finite_spectrum T).exists_notMem
  have hunit : IsUnit (algebraMap ℂ (Module.End ℂ M) t - T) := by
    simpa only [spectrum.mem_iff, not_not] using ht
  have hinjT : Function.Injective (algebraMap ℂ (Module.End ℂ M) t - T) :=
    LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hunit)
  have hinj : Function.Injective (C - t • J) := by
    intro x y hxy
    apply hinjT
    apply E.injective
    have h : t • J x - C x = t • J y - C y := by
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, neg_sub] using congrArg Neg.neg hxy
    simpa [T, E, Algebra.algebraMap_eq_smul_one] using h
  exact ⟨t, hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank E.finrank_eq).mp hinj⟩


end PlaneSkewPencil

/-- B24, concentration.tex:845–930. The dimensions are part of the hypothesis:
singularity alone does not imply isotropy for a subspace of arbitrary dimension. -/
theorem singular_skew_pencil_isotropic (Θ : Submodule ℂ (U × Module.Dual ℂ U))
    (hΘ : Module.finrank ℂ Θ = Module.finrank ℂ U)
    (hsingular : ∀ D : BilinForm ℂ U, D.IsAlt →
      ¬ Function.Bijective (skewPencil Θ D)) :
    ∀ x : Θ, x.1.2 x.1.1 = 0 := by
  obtain ⟨hdim, C, heval, hlift⟩ := PlaneSkewPencil.plane_quotient_reduction Θ hΘ
  let A := projectedTangent Θ
  let H := (verticalTangent Θ).dualCoannihilator
  let P := tangentProjection Θ
  have hsingC : ∀ D : BilinForm ℂ U, D.IsAlt →
      ¬ Function.Bijective (C - skewRestriction A H D) := by
    intro D hD hbij
    exact hsingular D hD (hlift D hbij)
  have hAH : A = H := by
    by_contra hne
    obtain ⟨J, hJ, hbij⟩ := different_subspaces_skew_restriction A H hdim hne
    obtain ⟨t, ht⟩ := PlaneSkewPencil.regular_pencil_member C (skewRestriction A H J) hbij
    apply hsingC (t • J) (hJ.smul t)
    have hscale : skewRestriction A H (t • J) = t • skewRestriction A H J := by
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro h
      rfl
    rwa [hscale]
  let F : A ≃ₗ[ℂ] H :=
    { toFun := fun a => ⟨a.1, hAH ▸ a.2⟩
      invFun := fun h => ⟨h.1, hAH.symm ▸ h.2⟩
      left_inv := by intro a; apply Subtype.ext; rfl
      right_inv := by intro h; apply Subtype.ext; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let C_A : BilinForm ℂ A := C.compl₂ F.toLinearMap
  have hsingA : ∀ Z : BilinForm ℂ A, Z.IsAlt → ¬ Function.Bijective (C_A - Z) := by
    intro Z hZ hbij
    obtain ⟨r, hr⟩ := A.subtype.exists_leftInverse_of_injective A.ker_subtype
    have hra : ∀ a : A, r a.1 = a := by
      intro a
      simpa [LinearMap.comp_apply, Submodule.subtype] using LinearMap.congr_fun hr a
    let D : BilinForm ℂ U := Z.compl₁₂ r r
    have hD : D.IsAlt := fun x => hZ (r x)
    apply hsingC D hD
    have hinj : Function.Injective (C - skewRestriction A H D) := by
      apply LinearMap.ker_eq_bot.mp
      apply le_antisymm ?_ bot_le
      intro a ha
      change a = 0
      have ha' : (C - skewRestriction A H D) a = 0 := ha
      have hCa : (C_A - Z) a = 0 := by
        apply LinearMap.ext
        intro a'
        have h := congrArg (fun l : Module.Dual ℂ H => l (F a')) ha'
        simpa [C_A, D, skewRestriction, F, hra] using h
      exact hbij.1 (by simpa using hCa)
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdim.trans Subspace.dual_finrank_eq.symm)).mp hinj⟩
  have hAlt := (everywhere_singular_square_skew_pencil C_A hsingA).2
  intro x
  exact (heval x (F (P x))).symm.trans (hAlt (P x))

/-- B21's quadratic-coordinate calculation, concentration.tex:807–815. -/
theorem tangent_quadratic_coordinate (z : BilinForm ℂ U) (hz : z.IsAlt)
    (dv : U) (dy : Module.Dual ℂ U) :
    (dy - z dv) dv = dy dv := by
  simp [LinearMap.sub_apply, hz dv]

/-- B02's pointwise surjectivity, concentration.tex:536–539. A chosen dual coordinate
is the local splitting used in the evaluation bundle construction. -/
theorem alternating_evaluation_surjective (v : U) (hv : v ≠ 0)
    (y : Module.Dual ℂ U) (hy : y v = 0) :
    ∃ D : BilinForm ℂ U, D.IsAlt ∧ D v = y := by
  obtain ⟨θ, hθ⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  let D : BilinForm ℂ U :=
    LinearMap.mk₂ ℂ (fun x z => θ x * y z - θ z * y x)
      (by
        intro x₁ x₂ z
        simp only [map_add, add_mul, mul_add]
        ring)
      (by
        intro c x z
        simp only [map_smul, smul_eq_mul]
        ring)
      (by
        intro x z₁ z₂
        simp only [map_add, add_mul, mul_add]
        ring)
      (by
        intro c x z
        simp only [map_smul, smul_eq_mul]
        ring)
  refine ⟨D, ?_, ?_⟩
  · intro x
    simp [D]
  · ext z
    simp [D, hθ, hy]

#print axioms singular_skew_pencil_isotropic
#print axioms different_subspaces_skew_restriction
#print axioms everywhere_singular_square_skew_pencil

end DistinctDistances.TrackB
