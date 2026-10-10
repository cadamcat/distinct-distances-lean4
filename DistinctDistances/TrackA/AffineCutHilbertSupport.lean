import DistinctDistances.TrackA.Definitions
import Mathlib.RingTheory.Ideal.Colon

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical
open Filter MvPolynomial OAI.QuarticPowerFree

abbrev affineFilteredSpace {n : ℕ} (I : Ideal (Poly n)) (D : ℕ) :=
  (totalSpace D).map (Ideal.Quotient.mkₐ ℂ I).toLinearMap

instance affineFilteredSpace_finite {n : ℕ} (I : Ideal (Poly n)) (D : ℕ) :
    Module.Finite ℂ (affineFilteredSpace I D) := by
  letI := totalSpace_finite (n := n) (K := ℂ) D
  infer_instance

set_option maxHeartbeats 800000 in
/-- The colon quotient embeds into the kernel of the next quotient, with
the multiplier's degree accounted for in the filtration. -/
theorem affine_colon_step_rank {n : ℕ} (I : Ideal (Poly n)) (a : Poly n) (T : ℕ) :
    Module.finrank ℂ (affineFilteredSpace (I.colon {a}) T) +
      Module.finrank ℂ (affineFilteredSpace (I ⊔ Ideal.span {a}) (T+a.totalDegree)) ≤
    Module.finrank ℂ (affineFilteredSpace I (T+a.totalDegree)) := by
  let P := I.colon {a}
  let J := I ⊔ Ideal.span {a}
  let G := affineFilteredSpace P T
  let F := affineFilteredSpace I (T+a.totalDegree)
  let μ : (Poly n ⧸ P) →ₗ[ℂ] (Poly n ⧸ I) :=
    (P.liftQ (I.mkQ.comp (LinearMap.mulLeft (Poly n) a)) (by
      intro q hq
      change Ideal.Quotient.mk I (a*q) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa only [smul_eq_mul, mul_comm] using (Submodule.mem_colon_singleton.mp hq))).restrictScalars ℂ
  have hμ (q : Poly n) : μ (Ideal.Quotient.mk P q) = Ideal.Quotient.mk I (a*q) := rfl
  have hμinj : Function.Injective μ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_ker, hμ] at hx
    have hq : q ∈ P := by
      apply Submodule.mem_colon_singleton.mpr
      simpa only [smul_eq_mul, mul_comm] using Ideal.Quotient.eq_zero_iff_mem.mp hx
    simpa only [Submodule.mem_bot] using Ideal.Quotient.eq_zero_iff_mem.mpr hq
  let g : G →ₗ[ℂ] F :=
    { toFun := fun x => ⟨μ x.val, by
        obtain ⟨q, hq, hqx⟩ := x.property
        change Ideal.Quotient.mk P q = x.val at hqx
        refine ⟨a*q, ?_, ?_⟩
        · apply mem_totalSpace.mpr
          exact (totalDegree_mul a q).trans
            ((Nat.add_le_add_left (mem_totalSpace.mp hq) _).trans_eq (Nat.add_comm _ _))
        · change Ideal.Quotient.mk I (a*q) = μ x.val
          rw [← hμ, hqx]⟩
      map_add' := by intro x y; apply Subtype.ext; exact μ.map_add _ _
      map_smul' := by intro c x; apply Subtype.ext; exact μ.map_smul c x.val }
  let π := (Ideal.Quotient.factorₐ ℂ (show I ≤ J from le_sup_left)).toLinearMap.domRestrict F
  have hg : Function.Injective g := fun x y h => Subtype.ext (hμinj (congrArg Subtype.val h))
  have hgle : LinearMap.range g ≤ LinearMap.ker π := by
    rintro x ⟨y, rfl⟩
    obtain ⟨q, hq, hqy⟩ := y.property
    change Ideal.Quotient.mk P q = y.val at hqy
    change (Ideal.Quotient.factorₐ ℂ (show I ≤ J from le_sup_left)) (μ y.val) = 0
    rw [← hqy, hμ]
    change Ideal.Quotient.mk J (a*q) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mul_mem_right q _
      ((show Ideal.span {a} ≤ J from le_sup_right) (Ideal.subset_span rfl))
  have hk : Module.finrank ℂ G ≤ Module.finrank ℂ (LinearMap.ker π) := by
    rw [← LinearMap.finrank_range_of_inj hg]
    exact Submodule.finrank_mono hgle
  have hdim := π.finrank_range_add_finrank_ker
  have hr : LinearMap.range π = affineFilteredSpace J (T+a.totalDegree) := by
    ext z
    constructor
    · rintro ⟨⟨y, q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨Ideal.Quotient.mk I q, ⟨q, hq, rfl⟩⟩, rfl⟩
  rw [hr] at hdim
  exact (Nat.add_le_add_right hk _).trans_eq (by
    rw [Nat.add_comm]
    exact hdim)

theorem affine_hilbert_degree_mono {n : ℕ} (I J : Ideal (Poly n)) (hIJ : I ≤ J) :
    (coordinateHilbert J).natDegree ≤ (coordinateHilbert I).natDegree := by
  apply natDegree_le_of_eventually_nat_eval_bounds
  · filter_upwards [coordinateHilbert_eventually J] with T hT
    rw [← hT]
    positivity
  · filter_upwards [coordinateHilbert_eventually I, coordinateHilbert_eventually J] with T hI hJ
    rw [← hI, ← hJ]
    exact_mod_cast quotient_hilbert_le I J hIJ T

theorem affine_hilbert_coefficient_nonneg {n : ℕ} (I : Ideal (Poly n)) (k : ℕ)
    (hdeg : (coordinateHilbert I).natDegree ≤ k) :
    0 ≤ (coordinateHilbert I).coeff k := by
  have h0 : (0 : Polynomial ℚ).natDegree ≤ k := by simp
  have hval : ∀ᶠ T : ℕ in atTop,
      (0 : Polynomial ℚ).eval (T : ℚ) ≤ (coordinateHilbert I).eval (T : ℚ) := by
    filter_upwards [coordinateHilbert_eventually I] with T hT
    rw [← hT]
    simp only [Polynomial.eval_zero]
    positivity
  simpa using coeff_le_of_eventually_nat_eval_le 0 (coordinateHilbert I) k h0 hdeg hval

theorem affine_colon_step_coefficient {n : ℕ} (I : Ideal (Poly n)) (a : Poly n) (k : ℕ)
    (hI : (coordinateHilbert I).natDegree ≤ k)
    (hP : (coordinateHilbert (I.colon {a})).natDegree ≤ k) :
    (coordinateHilbert (I.colon {a})).coeff k +
      (coordinateHilbert (I ⊔ Ideal.span {a})).coeff k ≤ (coordinateHilbert I).coeff k := by
  let P := coordinateHilbert (I.colon {a})
  let Q := coordinateHilbert (I ⊔ Ideal.span {a})
  let U := coordinateHilbert I
  let d := a.totalDegree
  have hQ : Q.natDegree ≤ k := (affine_hilbert_degree_mono I _ le_sup_left).trans hI
  have hleft : (P + Polynomial.taylor (d : ℚ) Q).natDegree ≤ k :=
    (Polynomial.natDegree_add_le _ _).trans (max_le hP (by simpa using hQ))
  have hright : (Polynomial.taylor (d : ℚ) U).natDegree ≤ k := by simpa using hI
  have hval : ∀ᶠ T : ℕ in atTop,
      (P + Polynomial.taylor (d : ℚ) Q).eval (T : ℚ) ≤
        (Polynomial.taylor (d : ℚ) U).eval (T : ℚ) := by
    have hQev := (tendsto_add_atTop_nat d).eventually (coordinateHilbert_eventually (I ⊔ Ideal.span {a}))
    have hUev := (tendsto_add_atTop_nat d).eventually (coordinateHilbert_eventually I)
    filter_upwards [coordinateHilbert_eventually (I.colon {a}), hQev, hUev] with T hPev hQev hUev
    have hbound := affine_colon_step_rank I a T
    simp only [Polynomial.eval_add, Polynomial.taylor_eval]
    change P.eval (T : ℚ) + Q.eval ((T : ℚ)+(d : ℚ)) ≤ U.eval ((T : ℚ)+(d : ℚ))
    rw [← Nat.cast_add, ← hPev, ← hQev, ← hUev]
    exact_mod_cast hbound
  have hc := coeff_le_of_eventually_nat_eval_le _ _ k hleft hright hval
  rw [Polynomial.coeff_add, coeff_taylor_high Q (d : ℚ) k hQ,
    coeff_taylor_high U (d : ℚ) k hI] at hc
  exact hc

end
end DistinctDistances.TrackA
