import DistinctDistances.TrackB.SkewPencil
import DistinctDistances.TrackB.MBFibersAux
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
The linear fibers behind concentration.tex:525–623 and 653–660. These are
the actual kernels and inverse images of evaluation, before algebraic gluing.
They do not substitute for the bundle or projective image closure statements.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false

open LinearMap (BilinForm)

variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

/-- Evaluation of an alternating form on a vector. -/
def alternatingEvaluation (v : U) : alternatingForms (U := U) →ₗ[ℂ] Module.Dual ℂ U where
  toFun := fun D => D.1 v
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- Add the projective point coordinate to the evaluation map. -/
def homogeneousEvaluation (v : U) :
    (ℂ × alternatingForms (U := U)) →ₗ[ℂ] (ℂ × Module.Dual ℂ U) where
  toFun := fun x => (x.1, alternatingEvaluation v x.2)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The fiber of the incidence bundle is the inverse image of the tautological line. -/
def incidenceFiber (v : U) (t : ℂ) (y : Module.Dual ℂ U) :
    Submodule ℂ (ℂ × alternatingForms (U := U)) :=
  (Submodule.span ℂ {(t, y)}).comap (homogeneousEvaluation v)

/-- B02, concentration.tex:538–540. A kernel form descends to the quotient by ℂv. -/
theorem alternating_kernel_descends (v : U) (D : BilinForm ℂ U)
    (hD : D.IsAlt) (hker : D v = 0) :
    ∃ Dbar : BilinForm ℂ (U ⧸ Submodule.span ℂ {v}), Dbar.IsAlt ∧
      ∀ x w : U, D x w = Dbar ((Submodule.span ℂ {v}).mkQ x)
        ((Submodule.span ℂ {v}).mkQ w) := by
  let S := Submodule.span ℂ {v}
  have hleft : S ≤ LinearMap.ker D := by
    apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact LinearMap.mem_ker.mpr hker
  have hright : S ≤ LinearMap.ker (LinearMap.flip D) := by
    rw [hD.isRefl.ker_flip]
    exact hleft
  let Dbar : BilinForm ℂ (U ⧸ S) := D.liftQ₂ S S hleft hright
  have hbar : Dbar.IsAlt := by
    intro x
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp (show x ∈ LinearMap.range S.mkQ by
      rw [S.range_mkQ]
      trivial)
    simpa [Dbar] using hD z
  refine ⟨Dbar, hbar, ?_⟩
  intro x w
  simpa [Dbar] using (LinearMap.liftQ₂_mk hleft hright x w).symm

set_option maxHeartbeats 1000000 in
/-- B02's rank calculation, concentration.tex:539–540. -/
theorem alternatingEvaluation_kernel_finrank (v : U) (hv : v ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (alternatingEvaluation v)) =
      (Module.finrank ℂ U - 1).choose 2 := by
  -- The line has finrank one.
  have hspan1 : Module.finrank ℂ ↥(Submodule.span ℂ {v}) = 1 := by
    let f : ℂ →ₗ[ℂ] ↥(Submodule.span ℂ {v}) :=
      { toFun := fun c => ⟨c • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩,
        map_add' := fun a b => by
          apply Subtype.ext
          show (a + b) • v = a • v + b • v
          exact add_smul _ _ _,
        map_smul' := fun a b => by
          apply Subtype.ext
          show (a * b) • v = a • (b • v)
          exact mul_smul _ _ _ }
    have hinj : Function.Injective f := by
      intro a b hab
      have hcoe : a • v = b • v := congrArg Subtype.val hab
      have h0 : (a - b) • v = 0 := by
        simp only [sub_smul, hcoe, sub_self]
      rcases smul_eq_zero.mp h0 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv
    have hsurjf : Function.Surjective f := by
      intro w
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp w.2
      exact ⟨a, Subtype.ext ha⟩
    have e1 := LinearEquiv.ofBijective f ⟨hinj, hsurjf⟩
    have h1 := e1.finrank_eq
    rw [Module.finrank_self] at h1
    exact h1.symm
  -- Hence the line quotient has finrank one less.
  have hQdim : Module.finrank ℂ (U ⧸ Submodule.span ℂ {v}) =
      Module.finrank ℂ U - 1 := by
    have hsum := Submodule.finrank_quotient_add_finrank (R := ℂ)
      (M := U) (Submodule.span ℂ {v})
    rw [hspan1] at hsum
    omega
  -- The quotient map is surjective.
  have hsurjQ : Function.Surjective (Submodule.span ℂ {v}).mkQ :=
    Submodule.mkQ_surjective _
  -- Bilinear forms on the quotient are determined on representatives.
  have extQ : ∀ B1 B2 : BilinForm ℂ (U ⧸ Submodule.span ℂ {v}),
      (∀ x w : U, B1 ((Submodule.span ℂ {v}).mkQ x)
        ((Submodule.span ℂ {v}).mkQ w) =
        B2 ((Submodule.span ℂ {v}).mkQ x)
        ((Submodule.span ℂ {v}).mkQ w)) → B1 = B2 := by
    intro B1 B2 h
    apply LinearMap.ext
    intro q1
    obtain ⟨x1, rfl⟩ := hsurjQ q1
    apply LinearMap.ext
    intro q2
    obtain ⟨x2, rfl⟩ := hsurjQ q2
    exact h x1 x2
  -- Pullback along the quotient map lands in the kernel.
  let Pb : ↥(DistinctDistances.TrackB.alternatingForms
      (U := U ⧸ Submodule.span ℂ {v})) →ₗ[ℂ]
      ↥(LinearMap.ker (alternatingEvaluation v)) :=
    { toFun := fun Db =>
        ⟨⟨Db.1.comp (Submodule.span ℂ {v}).mkQ (Submodule.span ℂ {v}).mkQ,
          fun x => by
            rw [LinearMap.BilinForm.comp_apply]
            exact Db.2 _⟩,
        by
          rw [LinearMap.mem_ker]
          apply LinearMap.ext
          intro w
          show (Db.1.comp (Submodule.span ℂ {v}).mkQ
            (Submodule.span ℂ {v}).mkQ) v w = 0
          rw [LinearMap.BilinForm.comp_apply]
          have hmv : (Submodule.span ℂ {v}).mkQ v = 0 := by
            have hmem : (Submodule.span ℂ {v}).mkQ v ∈
                Submodule.map (Submodule.span ℂ {v}).mkQ
                  (Submodule.span ℂ {v}) :=
              Submodule.mem_map.mpr
                ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
            rw [Submodule.mkQ_map_self] at hmem
            simpa using hmem
          rw [hmv, map_zero, LinearMap.zero_apply]⟩,
      map_add' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        show (a.1 + b.1).comp (Submodule.span ℂ {v}).mkQ
            (Submodule.span ℂ {v}).mkQ =
          (a.1.comp (Submodule.span ℂ {v}).mkQ (Submodule.span ℂ {v}).mkQ) +
            (b.1.comp (Submodule.span ℂ {v}).mkQ (Submodule.span ℂ {v}).mkQ)
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro w
        simp only [LinearMap.BilinForm.comp_apply, LinearMap.add_apply],
      map_smul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        show ((a • b.1).comp (Submodule.span ℂ {v}).mkQ
            (Submodule.span ℂ {v}).mkQ) =
          a • ((b.1.comp (Submodule.span ℂ {v}).mkQ
            (Submodule.span ℂ {v}).mkQ))
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro w
        simp only [LinearMap.BilinForm.comp_apply, LinearMap.smul_apply,
          smul_eq_mul] }
  have hinj : Function.Injective Pb := by
    intro D1 D2 hD
    have hB : D1.1 = D2.1 := by
      apply extQ
      intro x w
      have h1 : (Pb D1).1.1 x w = (Pb D2).1.1 x w := by rw [hD]
      have e1 : (Pb D1).1.1 x w =
          D1.1 ((Submodule.span ℂ {v}).mkQ x)
            ((Submodule.span ℂ {v}).mkQ w) := by
        show (D1.1.comp _ _) x w = _
        rw [LinearMap.BilinForm.comp_apply]
      have e2 : (Pb D2).1.1 x w =
          D2.1 ((Submodule.span ℂ {v}).mkQ x)
            ((Submodule.span ℂ {v}).mkQ w) := by
        show (D2.1.comp _ _) x w = _
        rw [LinearMap.BilinForm.comp_apply]
      rw [e1, e2] at h1
      exact h1
    exact Subtype.ext hB
  have hsurj : Function.Surjective Pb := by
    intro Dd
    have hDv : Dd.1.1 v = 0 :=
      LinearMap.mem_ker.mp Dd.2
    obtain ⟨Dbar, hDbar, hspec⟩ :=
      alternating_kernel_descends v Dd.1.1 Dd.1.2 hDv
    refine ⟨⟨Dbar, hDbar⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show (Dbar.comp (Submodule.span ℂ {v}).mkQ
        (Submodule.span ℂ {v}).mkQ) = Dd.1.1
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro w
    rw [LinearMap.BilinForm.comp_apply]
    exact (hspec x w).symm
  have e := LinearEquiv.ofBijective Pb ⟨hinj, hsurj⟩
  have hre := e.finrank_eq
  rw [MBFibersAux.finrank_alternatingForms] at hre
  rw [hQdim] at hre
  exact hre.symm

/-- B06's exact quotient on a fiber, concentration.tex:598–602. -/
theorem incidenceFiber_evaluation_image (v : U) (hv : v ≠ 0)
    (t : ℂ) (y : Module.Dual ℂ U) (hy : y v = 0) :
    (incidenceFiber v t y).map (homogeneousEvaluation v) =
      Submodule.span ℂ {(t, y)} := by
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.mpr le_rfl
  · intro z hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz
    obtain ⟨D, hD, hEval⟩ := alternating_evaluation_surjective v hv (a • y) (by
      simp [hy])
    let x : ℂ × alternatingForms (U := U) := (a * t, ⟨D, hD⟩)
    have hxEval : homogeneousEvaluation v x = a • (t, y) := by
      simp [x, homogeneousEvaluation, alternatingEvaluation, hEval, smul_eq_mul]
    have hx : x ∈ incidenceFiber v t y := by
      change homogeneousEvaluation v x ∈ Submodule.span ℂ {(t, y)}
      rw [hxEval]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    rw [Submodule.mem_map]
    exact ⟨x, hx, hxEval.trans ha⟩

set_option maxHeartbeats 1000000 in
/-- B06's rank, concentration.tex:598. Excludes the zero tautological representative. -/
theorem incidenceFiber_finrank (v : U) (hv : v ≠ 0)
    (t : ℂ) (y : Module.Dual ℂ U) (hy : y v = 0) (hty : (t, y) ≠ 0) :
    Module.finrank ℂ (incidenceFiber v t y) =
      (Module.finrank ℂ U - 1).choose 2 + 1 := by
  let E := homogeneousEvaluation v
  let F := incidenceFiber v t y
  let M : Submodule ℂ (ℂ × Module.Dual ℂ U) := Submodule.span ℂ {(t, y)}
  change Module.finrank ℂ F = (Module.finrank ℂ U - 1).choose 2 + 1
  have hker_le : LinearMap.ker E ≤ F := by
    intro x hx
    change E x ∈ M
    rw [LinearMap.mem_ker.mp hx]
    exact M.zero_mem
  have hline : (t, y) ∈ F.map E := by
    rw [incidenceFiber_evaluation_image v hv t y hy]
    exact Submodule.subset_span (by simp)
  obtain ⟨x, hxF, hxE⟩ := (Submodule.mem_map.mp hline)
  have hxnotker : x ∉ LinearMap.ker E := by
    intro hx
    apply hty
    calc
      (t, y) = E x := hxE.symm
      _ = 0 := LinearMap.mem_ker.mp hx
  have hF_eq : F = LinearMap.ker E ⊔ Submodule.span ℂ {x} := by
    apply le_antisymm
    · intro z hz
      change E z ∈ M at hz
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz
      have hdiff : z - a • x ∈ LinearMap.ker E := by
        rw [LinearMap.mem_ker]
        calc
          E (z - a • x) = E z - E (a • x) := map_sub E z (a • x)
          _ = E z - a • E x := by rw [map_smul]
          _ = a • (t, y) - a • (t, y) := by rw [← ha, hxE]
          _ = 0 := sub_self _
      have hspan : a • x ∈ Submodule.span ℂ {x} :=
        Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      rw [Submodule.mem_sup]
      exact ⟨z - a • x, hdiff, a • x, hspan, by abel⟩
    · apply sup_le hker_le
      apply Submodule.span_le.mpr
      intro z hz
      have hz' : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact hxF
  letI : AddCommGroup (Module.Dual ℂ U) := inferInstance
  letI : AddCommGroup (BilinForm ℂ U) := inferInstance
  letI : AddCommGroup (alternatingForms (U := U)) :=
    Submodule.addCommGroup (alternatingForms (U := U))
  letI : Module.Finite ℂ (alternatingForms (U := U)) := inferInstance
  let kerEquiv : LinearMap.ker E ≃ₗ[ℂ]
      LinearMap.ker (alternatingEvaluation v) :=
    { toFun := fun z => ⟨z.1.2, by
        have hz := LinearMap.mem_ker.mp z.2
        change (z.1.1, alternatingEvaluation v z.1.2) = (0, 0) at hz
        exact LinearMap.mem_ker.mpr (congrArg Prod.snd hz)⟩
      invFun := fun z => ⟨(0, z.1), by
        apply LinearMap.mem_ker.mpr
        change (0, alternatingEvaluation v z.1) = (0, 0)
        exact Prod.ext rfl (LinearMap.mem_ker.mp z.2)⟩
      left_inv := by
        intro z
        apply Subtype.ext
        have hz := LinearMap.mem_ker.mp z.2
        change (z.1.1, alternatingEvaluation v z.1.2) = (0, 0) at hz
        have hfirst : z.1.1 = 0 := congrArg Prod.fst hz
        change (0, z.1.2) = z.1
        exact Prod.ext hfirst.symm rfl
      right_inv := by intro z; apply Subtype.ext; rfl
      map_add' := by intro z w; apply Subtype.ext; rfl
      map_smul' := by intro a z; apply Subtype.ext; rfl }
  let decompose : LinearMap.ker E × ℂ →ₗ[ℂ] F :=
    { toFun := fun z => ⟨z.1.1 + z.2 • x,
        F.add_mem (hker_le z.1.2) (F.smul_mem _ hxF)⟩
      map_add' := by
        intro z w
        apply Subtype.ext
        change (z.1.1 + w.1.1) + (z.2 + w.2) • x =
          (z.1.1 + z.2 • x) + (w.1.1 + w.2 • x)
        simp only [add_smul]
        abel_nf
      map_smul' := by
        intro a z
        apply Subtype.ext
        simp [smul_add, smul_smul] }
  have decompose_inj : Function.Injective decompose := by
    intro z w hzw
    have hval : z.1.1 + z.2 • x = w.1.1 + w.2 • x := congrArg Subtype.val hzw
    have hzE : E (z.1.1 + z.2 • x) = z.2 • (t, y) := by
      calc
        E (z.1.1 + z.2 • x) = E z.1.1 + E (z.2 • x) := by rw [map_add]
        _ = 0 + z.2 • E x := by rw [LinearMap.mem_ker.mp z.1.2, map_smul]
        _ = z.2 • (t, y) := by rw [hxE]; simp
    have hwE : E (w.1.1 + w.2 • x) = w.2 • (t, y) := by
      calc
        E (w.1.1 + w.2 • x) = E w.1.1 + E (w.2 • x) := by rw [map_add]
        _ = 0 + w.2 • E x := by rw [LinearMap.mem_ker.mp w.1.2, map_smul]
        _ = w.2 • (t, y) := by rw [hxE]; simp
    have hscalar : z.2 = w.2 :=
      smul_left_injective ℂ hty (hzE.symm.trans ((congrArg E hval).trans hwE))
    have hker : z.1.1 = w.1.1 := by
      rw [hscalar] at hval
      exact add_right_cancel hval
    apply Prod.ext
    · exact Subtype.ext hker
    · exact hscalar
  have decompose_surj : Function.Surjective decompose := by
    intro z
    have hzsup : z.1 ∈ LinearMap.ker E ⊔ Submodule.span ℂ {x} := by
      rw [← hF_eq]
      exact z.2
    obtain ⟨k, hk, s, hs, hks⟩ := Submodule.mem_sup.mp hzsup
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hs
    refine ⟨(⟨k, hk⟩, a), ?_⟩
    apply Subtype.ext
    change k + a • x = z.1
    calc
      k + a • x = k + s := by rw [ha]
      _ = z.1 := hks
  let decomposeEquiv := LinearEquiv.ofBijective decompose ⟨decompose_inj, decompose_surj⟩
  letI : Module.Finite ℂ (LinearMap.ker (alternatingEvaluation v)) := inferInstance
  let prodEquiv := kerEquiv.symm.prodCongr (LinearEquiv.refl ℂ ℂ)
  let totalEquiv := prodEquiv.trans decomposeEquiv
  calc
    Module.finrank ℂ F =
        Module.finrank ℂ (LinearMap.ker (alternatingEvaluation v) × ℂ) :=
      totalEquiv.finrank_eq.symm
    _ = Module.finrank ℂ (LinearMap.ker (alternatingEvaluation v)) + 1 := by
      rw [Module.finrank_prod, Module.finrank_self]
    _ = (Module.finrank ℂ U - 1).choose 2 + 1 := by
      rw [alternatingEvaluation_kernel_finrank v hv]

/-- B07, concentration.tex:613–615, the linear equations of the affine flat's closure. -/
theorem incidenceFiber_affine_equation (v : U) (y : Module.Dual ℂ U)
    (x0 : ℂ) (D : alternatingForms (U := U)) :
    (x0, D) ∈ incidenceFiber v 1 y ↔ alternatingEvaluation v D = x0 • y := by
  change (x0, alternatingEvaluation v D) ∈ Submodule.span ℂ {(1, y)} ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h₁ : c = x0 := by
      simpa using congrArg Prod.fst hc
    have h₂ : c • y = alternatingEvaluation v D := by
      simpa using congrArg Prod.snd hc
    rw [h₁] at h₂
    exact h₂.symm
  · intro h
    refine ⟨x0, ?_⟩
    apply Prod.ext
    · simp
    · simpa using h.symm

/-- B08, concentration.tex:619–623. No boundary parameter lies over an affine point. -/
theorem incidenceFiber_boundary (v : U) (y : Module.Dual ℂ U)
    (x0 : ℂ) (D : alternatingForms (U := U))
    (hmem : (x0, D) ∈ incidenceFiber v 0 y) : x0 = 0 := by
  change (x0, alternatingEvaluation v D) ∈ Submodule.span ℂ {(0, y)} at hmem
  rw [Submodule.mem_span_singleton] at hmem
  rcases hmem with ⟨c, hc⟩
  have hfst := congrArg Prod.fst hc
  simpa using hfst.symm

/-- The injective graph map underlying B10's point-fiber projective space. -/
def evaluationGraph (z : BilinForm ℂ U) : U →ₗ[ℂ] (U × Module.Dual ℂ U) where
  toFun := fun v => (v, z v)
  map_add' := by intros; simp only [map_add]; rfl
  map_smul' := by intros; simp only [map_smul]; rfl

/-- B10, concentration.tex:658–660. -/
theorem evaluationGraph_injective (z : BilinForm ℂ U) :
    Function.Injective (evaluationGraph z) := by
  intro x y h
  simpa [evaluationGraph] using congrArg Prod.fst h

end DistinctDistances.TrackB
