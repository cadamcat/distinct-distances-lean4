import DistinctDistances.TrackA.RayPolynomialSupport
import Mathlib.Data.Set.Card.Arithmetic

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

def rayParameter {n : ℕ} (p : Point n) (z : ProjectivePoint n) (x : Point n) : ℂ :=
  (x (chartIndex z) - p (chartIndex z)) / z.rep (chartIndex z)

theorem radial_fiber_parameter {n : ℕ} (p : Point n) (z : ProjectivePoint n)
    (V : AffineVariety n) (x : Point n) (hx : x ∈ radialFiber p V z) :
    x = p + rayParameter p z x • z.rep := by
  obtain ⟨hxV, hxne, hproj⟩ := hx
  have heq : Projectivization.mk ℂ (x-p) (sub_ne_zero.mpr hxne) =
      Projectivization.mk ℂ z.rep z.rep_nonzero := by
    simpa only [radialProjection, Projectivization.mk_rep] using hproj
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq
  have hxline : x = p + c • z.rep := by
    ext i
    have h := congrFun hc i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -h
  have hparam : rayParameter p z x = c := by
    rw [rayParameter, hxline]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [chartIndex_nonzero z]
    ring
  rwa [hparam]

/-- Pairwise disjoint literal fibers inject into the roots of one nonzero ray polynomial. -/
theorem radial_fiber_sum_le_ray_degree {n : ℕ} (J : AffineFamily.Family n)
    (p : Point n) (z : ProjectivePoint n) (f : Poly n)
    (hzero : ∀ V ∈ J, f ∈ V.ideal)
    (hfinite : ∀ V ∈ J, (radialFiber p V z).Finite)
    (hdisjoint : ∀ V ∈ J, ∀ W ∈ J, V ≠ W → Disjoint (radialFiber p V z) (radialFiber p W z))
    (hQne : rayPolynomial p z.rep f ≠ 0) :
    ∑ V ∈ J, (radialFiber p V z).ncard ≤ f.totalDegree := by
  let S : Set (Point n) := ⋃ V : J, radialFiber p V.val z
  let Q := rayPolynomial p z.rep f
  let T : Set ℂ := {t | Q.eval t = 0}
  have hT : T.Finite := Polynomial.finite_setOfPred_isRoot hQne
  have hS_card : S.ncard = ∑ V ∈ J, (radialFiber p V z).ncard := by
    have h := Set.ncard_iUnion_of_finite (fun V : J => hfinite V.val V.property)
      (fun V W hne => hdisjoint V.val V.property W.val W.property
        (fun he => hne (Subtype.ext he)))
    rw [finsum_eq_sum_of_fintype] at h
    exact h.trans (Finset.sum_coe_sort J (fun V => (radialFiber p V z).ncard))
  have hmaps : ∀ x ∈ S, rayParameter p z x ∈ T := by
    intro x hx
    obtain ⟨V, hxV⟩ := Set.mem_iUnion.mp hx
    change Q.eval (rayParameter p z x) = 0
    rw [rayPolynomial_eval, ← radial_fiber_parameter p z V.val x hxV]
    simpa only [MvPolynomial.aeval_eq_eval] using hxV.1 f (hzero V.val V.property)
  have hinj : Set.InjOn (rayParameter p z) S := by
    intro x hx y hy he
    obtain ⟨V, hxV⟩ := Set.mem_iUnion.mp hx
    obtain ⟨W, hyW⟩ := Set.mem_iUnion.mp hy
    rw [radial_fiber_parameter p z V.val x hxV, radial_fiber_parameter p z W.val y hyW, he]
  have hTdegree : T.ncard ≤ Q.natDegree := by
    rw [Set.ncard_eq_toFinset_card T hT]
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    exact (Polynomial.mem_roots hQne).2 (hT.mem_toFinset.mp ht)
  rw [← hS_card]
  exact (Set.ncard_le_ncard_of_injOn (rayParameter p z) hmaps hinj hT).trans
    (hTdegree.trans (rayPolynomial_degree p z.rep f))

end
end DistinctDistances.TrackA
