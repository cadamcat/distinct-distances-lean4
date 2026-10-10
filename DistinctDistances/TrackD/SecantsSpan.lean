import DistinctDistances.TrackD.Genericity
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

variable {d : ℕ}

/-- The affine linear equation associated to a covector, based at `y`. -/
def covectorPoly (f : Point d →ₗ[ℂ] ℂ) (y : Point d) : Poly d :=
  (∑ i : Fin d, MvPolynomial.C (f (Pi.single i 1)) * MvPolynomial.X i) - MvPolynomial.C (f y)

theorem covector_sum (f : Point d →ₗ[ℂ] ℂ) (x : Point d) :
    (∑ i : Fin d, f (Pi.single i 1) * x i) = f x := by
  have hs : (∑ i : Fin d, x i • Pi.single i (1 : ℂ)) = x := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = f (∑ i : Fin d, x i • Pi.single i (1 : ℂ)) := by
      simp [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = f x := congrArg f hs

@[simp] theorem eval_covectorPoly (f : Point d →ₗ[ℂ] ℂ) (y x : Point d) :
    MvPolynomial.eval x (covectorPoly f y) = f (x - y) := by
  simp only [covectorPoly, map_sub, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, covector_sum]

@[simp] theorem differential_covectorPoly (f : Point d →ₗ[ℂ] ℂ) (y x v : Point d) :
    differential (covectorPoly f y) x v = f v := by
  have hp : ∀ i : Fin d, MvPolynomial.pderiv i (covectorPoly f y) =
      MvPolynomial.C (f (Pi.single i 1)) := by
    intro i
    simp [covectorPoly, MvPolynomial.pderiv_X, Pi.single_apply]
  simp only [differential, hp, MvPolynomial.aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, covector_sum]

/-- The frozen zero-differential node is supplied as an explicit input to the span core. -/
def TangentConstancy (d : ℕ) : Prop :=
  ∀ (X : AffineVariety d), X.IsIrreducible → ∀ a b : Poly d,
    (∃ x ∈ X, MvPolynomial.eval x b ≠ 0) →
    ForGeneralPoint X (fun x => ∀ v ∈ X.tangentSpace x,
      MvPolynomial.eval x b * differential a x v -
        MvPolynomial.eval x a * differential b x v = 0) →
    ∃ c : ℂ, ∀ x ∈ X, MvPolynomial.eval x a = c * MvPolynomial.eval x b

/-- `secants.tex:89–96`: integrate the projected tangent inclusion using ratios of
affine linear equations annihilating the fixed tangent plane. -/
theorem tangent_integration (zeroDiff : TangentConstancy d)
    (X : AffineVariety d) (hX : X.IsIrreducible) (y : Point d)
    (U : Submodule ℂ (Point d))
    (h : ForGeneralPoint X (fun x => X.tangentSpace x ≤ U ⊔ (ℂ ∙ (x - y)))) :
    ∃ F : AffineSubspace ℂ (Point d),
      Module.finrank ℂ F.direction ≤ Module.finrank ℂ U + 1 ∧
      X.points ⊆ F ∧ y ∈ F ∧ U ≤ F.direction := by
  by_cases hc : ∀ x ∈ X, x - y ∈ U
  · refine ⟨AffineSubspace.mk' y U, ?_, ?_, AffineSubspace.self_mem_mk' _ _, ?_⟩
    · rw [AffineSubspace.direction_mk']; exact Nat.le_succ _
    · intro x hx
      exact AffineSubspace.mem_mk'.mpr (hc x hx)
    · simp
  · push Not at hc
    obtain ⟨x₀, hx₀, hu₀⟩ := hc
    obtain ⟨lam, hlam, hUlam⟩ := U.exists_dual_map_eq_bot_of_notMem hu₀ inferInstance
    have hlamU : ∀ u ∈ U, lam u = 0 := by
      intro u hu
      have hm : lam u ∈ U.map lam := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
      rw [hUlam, Submodule.mem_bot] at hm
      exact hm
    let W := U ⊔ (ℂ ∙ (x₀ - y))
    have hXW : ∀ x ∈ X, x - y ∈ W := by
      intro x hx
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W (x - y)).mp
      intro f hf
      have hfU : ∀ u ∈ U, f u = 0 := by
        intro u hu
        exact ((Submodule.mem_dualAnnihilator f).mp hf) u ((le_sup_left : U ≤ W) hu)
      have hfx₀ : f (x₀ - y) = 0 :=
        ((Submodule.mem_dualAnnihilator f).mp hf) _ ((le_sup_right : (ℂ ∙ (x₀ - y)) ≤ W) (Submodule.mem_span_singleton_self _))
      obtain ⟨c, hc⟩ := zeroDiff X hX (covectorPoly f y) (covectorPoly lam y)
        ⟨x₀, hx₀, by simpa using hlam⟩ (h.mono (by
          intro z hz hzinc v hv
          obtain ⟨u, hu, w, hw, hvw⟩ := Submodule.mem_sup.mp (hzinc hv)
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
          simp only [eval_covectorPoly, differential_covectorPoly]
          rw [← hvw, map_add, map_add, hfU u hu, hlamU u hu, map_smul, map_smul]
          simp only [zero_add, smul_eq_mul]
          ring))
      have hc0 : c = 0 := by
        have heq := hc x₀ hx₀
        simp only [eval_covectorPoly, hfx₀] at heq
        exact (mul_eq_zero.mp heq.symm).resolve_right hlam
      simpa [hc0] using hc x hx
    refine ⟨AffineSubspace.mk' y W, ?_, ?_, AffineSubspace.self_mem_mk' _ _, ?_⟩
    · rw [AffineSubspace.direction_mk']
      exact le_of_eq (Submodule.finrank_sup_span_singleton hu₀)
    · intro x hx
      exact AffineSubspace.mem_mk'.mpr (hXW x hx)
    · simpa only [AffineSubspace.direction_mk'] using (le_sup_left : U ≤ W)

/-- Tangents to a reduced variety annihilate every affine equation of its affine span. -/
theorem tangent_le_complexSpan (X : AffineVariety d) (x : Point d) (hx : x ∈ X) :
    X.tangentSpace x ≤ (complexSpan X).direction := by
  intro v hv
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ v).mp
  intro f hf
  have hfI : covectorPoly f x ∈ X.ideal := (mem_ideal_iff_eval_zero X _).mpr (by
    intro z hz
    simp only [eval_covectorPoly]
    apply ((Submodule.mem_dualAnnihilator f).mp hf)
    exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℂ X.points hz)
      (subset_affineSpan ℂ X.points hx))
  have h : differential (covectorPoly f x) x v = 0 := by
    simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv
    exact hv ⟨covectorPoly f x, hfI⟩
  simpa using h

/-- Generic containment in a flat extends to the whole irreducible variety. -/
theorem ForGeneralPoint.subset_flat {X : AffineVariety d} (hX : X.IsIrreducible)
    (F : AffineSubspace ℂ (Point d)) (h : ForGeneralPoint X (fun x => x ∈ F)) :
    X.points ⊆ F := by
  obtain ⟨y, hy, hyF⟩ := h.exists
  intro x hx
  apply (AffineSubspace.vsub_right_mem_direction_iff_mem hyF x).mp
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ (x - y)).mp
  intro f hf
  have he : ∀ z ∈ X, MvPolynomial.eval z (covectorPoly f y) = 0 :=
    ForGeneralPoint.eval_zero hX (covectorPoly f y) (h.mono (fun z hz hzF => by
      simp only [eval_covectorPoly]
      exact ((Submodule.mem_dualAnnihilator f).mp hf) _
        (AffineSubspace.vsub_mem_direction hzF hyF)))
  simpa only [eval_covectorPoly] using he x hx

/-- A containing flat with no more directions than the affine span equals that span. -/
theorem flat_eq_complexSpan (X : AffineVariety d) (F : AffineSubspace ℂ (Point d))
    (hXF : X.points ⊆ F) (hne : X.points.Nonempty)
    (hdim : Module.finrank ℂ F.direction ≤ Module.finrank ℂ (complexSpan X).direction) :
    F = complexSpan X := by
  have hle : complexSpan X ≤ F := affineSpan_le.mpr hXF
  have hdir : (complexSpan X).direction ≤ F.direction := AffineSubspace.direction_le hle
  have heq : (complexSpan X).direction = F.direction :=
    Submodule.eq_of_le_of_finrank_eq hdir (by
      have := Submodule.finrank_mono hdir
      omega)
  obtain ⟨x, hx⟩ := hne
  exact (AffineSubspace.ext_of_direction_eq heq
    ⟨x, subset_affineSpan ℂ X.points hx, hXF hx⟩).symm

theorem span_sub_rev (x y : Point d) :
    (ℂ ∙ (x - y) : Submodule ℂ (Point d)) = (ℂ ∙ (y - x)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    change x - y ∈ (ℂ ∙ (y - x) : Submodule ℂ (Point d))
    have hh : -(y - x) ∈ (ℂ ∙ (y - x) : Submodule ℂ (Point d)) :=
      Submodule.neg_mem _ (Submodule.mem_span_singleton_self (y - x))
    rwa [neg_sub] at hh
  · apply Submodule.span_le.mpr
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    change y - x ∈ (ℂ ∙ (x - y) : Submodule ℂ (Point d))
    have hh : -(x - y) ∈ (ℂ ∙ (x - y) : Submodule ℂ (Point d)) :=
      Submodule.neg_mem _ (Submodule.mem_span_singleton_self (x - y))
    rwa [neg_sub] at hh

theorem finrank_join_line_le (U : Submodule ℂ (Point d)) (v : Point d) :
    Module.finrank ℂ ↥(U ⊔ (ℂ ∙ v)) ≤ Module.finrank ℂ U + 1 := by
  by_cases hv : v ∈ U
  · have hs : (ℂ ∙ v) ≤ U := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)
    rw [sup_eq_left.mpr hs]
    omega
  · exact le_of_eq (Submodule.finrank_sup_span_singleton hv)

/-- `secants.tex:96–102`: after tangent integration, join the two affine spans.
The generic tangent dimension is an explicit shared-model input. -/
theorem common_flat_of_equal_tangents (zeroDiff : TangentConstancy d)
    (X Y : AffineVariety d) (k : ℕ) (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hTX : ForGeneralPoint X (fun x => Module.finrank ℂ (X.tangentSpace x) = k))
    (hTY : ForGeneralPoint Y (fun y => Module.finrank ℂ (Y.tangentSpace y) = k))
    (heq : ForGeneralPair X Y (fun x y =>
      X.tangentSpace x ⊔ (ℂ ∙ (y - x)) = Y.tangentSpace y ⊔ (ℂ ∙ (y - x)))) :
    ∃ F : AffineSubspace ℂ (Point d),
      Module.finrank ℂ F.direction ≤ k + 1 ∧ X.points ⊆ F ∧ Y.points ⊆ F := by
  have hneX : X.points.Nonempty := by
    obtain ⟨x, hx, _⟩ := hTX.exists
    exact ⟨x, hx⟩
  have hneY : Y.points.Nonempty := by
    obtain ⟨y, hy, _⟩ := hTY.exists
    exact ⟨y, hy⟩
  have hEqRev : ForGeneralPair Y X (fun y x =>
      Y.tangentSpace y ⊔ (ℂ ∙ (x - y)) = X.tangentSpace x ⊔ (ℂ ∙ (x - y))) := by
    obtain ⟨g, hg, h⟩ := heq.swap
    refine ⟨g, hg, ?_⟩
    intro y hy x hx hn
    rw [span_sub_rev x y]
    exact (h y hy x hx hn).symm
  have integ : ∀ (A B : AffineVariety d), A.IsIrreducible → ∀ y : Point d,
      Module.finrank ℂ (B.tangentSpace y) = k →
      ForGeneralPoint A (fun x =>
        A.tangentSpace x ⊔ (ℂ ∙ (y - x)) = B.tangentSpace y ⊔ (ℂ ∙ (y - x))) →
      ∃ F : AffineSubspace ℂ (Point d), Module.finrank ℂ F.direction ≤ k + 1 ∧
        A.points ⊆ F ∧ y ∈ F := by
    intro A B hA y hdim hs
    obtain ⟨F, hFdim, hAF, hyF, _⟩ := tangent_integration zeroDiff A hA y
      (B.tangentSpace y) (hs.mono (by
        intro x hx hxEq
        rw [span_sub_rev x y, ← hxEq]
        exact le_sup_left))
    exact ⟨F, by simpa only [hdim] using hFdim, hAF, hyF⟩
  have bounds : ∀ (A B : AffineVariety d), A.IsIrreducible → B.IsIrreducible →
      ForGeneralPoint B (fun y => Module.finrank ℂ (B.tangentSpace y) = k) →
      ForGeneralPair A B (fun x y =>
        A.tangentSpace x ⊔ (ℂ ∙ (y - x)) = B.tangentSpace y ⊔ (ℂ ∙ (y - x))) →
      Module.finrank ℂ (complexSpan A).direction ≤ k + 1 := by
    intro A B hA hB hTB hEq
    obtain ⟨y, hy, hyDim, hySlice⟩ := (hTB.and hB hEq.fiber_right).exists
    obtain ⟨F, hFdim, hAF, _⟩ := integ A B hA y hyDim hySlice
    exact (Submodule.finrank_mono
      (AffineSubspace.direction_le (affineSpan_le.mpr hAF))).trans hFdim
  have hboundX := bounds X Y hX hY hTY heq
  have hboundY := bounds Y X hY hX hTX hEqRev
  have fullSpan : ∀ (A B : AffineVariety d), A.IsIrreducible → B.IsIrreducible →
      A.points.Nonempty → Module.finrank ℂ (complexSpan A).direction = k + 1 →
      ForGeneralPoint B (fun y => Module.finrank ℂ (B.tangentSpace y) = k) →
      ForGeneralPair A B (fun x y =>
        A.tangentSpace x ⊔ (ℂ ∙ (y - x)) = B.tangentSpace y ⊔ (ℂ ∙ (y - x))) →
      B.points ⊆ complexSpan A := by
    intro A B hA hB hne hdim hTB hEq
    apply ForGeneralPoint.subset_flat hB
    apply (hTB.and hB hEq.fiber_right).mono
    intro y hy hys
    obtain ⟨F, hFdim, hAF, hyF⟩ := integ A B hA y hys.1 hys.2
    have hFeq := flat_eq_complexSpan A F hAF hne (by simpa only [hdim] using hFdim)
    simpa only [hFeq] using hyF
  by_cases hfullX : Module.finrank ℂ (complexSpan X).direction = k + 1
  · exact ⟨complexSpan X, hboundX, subset_affineSpan ℂ X.points,
      fullSpan X Y hX hY hneX hfullX hTY heq⟩
  by_cases hfullY : Module.finrank ℂ (complexSpan Y).direction = k + 1
  · exact ⟨complexSpan Y, hboundY, fullSpan Y X hY hX hneY hfullY hTX hEqRev,
      subset_affineSpan ℂ Y.points⟩
  have hdimX : Module.finrank ℂ (complexSpan X).direction ≤ k := by omega
  have hdimY : Module.finrank ℂ (complexSpan Y).direction ≤ k := by omega
  obtain ⟨y, hy, hyDim, hySlice⟩ := (hTY.and hY heq.fiber_right).exists
  obtain ⟨x, hx, hxDim, hxy⟩ := (hTX.and hX hySlice).exists
  have hdirX : X.tangentSpace x = (complexSpan X).direction :=
    Submodule.eq_of_le_of_finrank_le (tangent_le_complexSpan X x hx) (by
      simpa only [hxDim] using hdimX)
  have hdirY : Y.tangentSpace y = (complexSpan Y).direction :=
    Submodule.eq_of_le_of_finrank_le (tangent_le_complexSpan Y y hy) (by
      simpa only [hyDim] using hdimY)
  let W := X.tangentSpace x ⊔ (ℂ ∙ (y - x))
  let F := AffineSubspace.mk' x W
  have hxF : x ∈ F := AffineSubspace.self_mem_mk' _ _
  have hyF : y ∈ F := AffineSubspace.mem_mk'.mpr
    ((le_sup_right : (ℂ ∙ (y - x)) ≤ W) (Submodule.mem_span_singleton_self (y - x)))
  have hXF : complexSpan X ≤ F := AffineSubspace.le_of_direction_le (by
    rw [AffineSubspace.direction_mk', ← hdirX]
    exact le_sup_left) ⟨x, subset_affineSpan ℂ X.points hx, hxF⟩
  have hYF : complexSpan Y ≤ F := AffineSubspace.le_of_direction_le (by
    rw [AffineSubspace.direction_mk', ← hdirY]
    change Y.tangentSpace y ≤ X.tangentSpace x ⊔ (ℂ ∙ (y - x))
    rw [hxy]
    exact le_sup_left) ⟨y, subset_affineSpan ℂ Y.points hy, hyF⟩
  refine ⟨F, ?_, fun z hz => hXF (subset_affineSpan ℂ X.points hz),
    fun z hz => hYF (subset_affineSpan ℂ Y.points hz)⟩
  rw [AffineSubspace.direction_mk']
  simpa only [hxDim] using finrank_join_line_le (X.tangentSpace x) (y - x)

end
end DistinctDistances.TrackD
