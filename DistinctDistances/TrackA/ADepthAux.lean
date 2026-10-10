import DistinctDistances.Foundations.Affine
import OAI.NumberTheory.PowerFree.PointInterpolation

namespace DistinctDistances.TrackA

noncomputable section
open scoped BigOperators Classical

theorem affine_point_degree_one {n : ℕ} (x : Point n) :
    OAI.QuarticPowerFree.affineDegree (MvPolynomial.vanishingIdeal ℂ {x}) = 1 := by
  classical
  let I : Ideal (Poly n) := MvPolynomial.vanishingIdeal ℂ {x}
  let ev : Poly n →ₐ[ℂ] ℂ := MvPolynomial.aeval x
  have hI : I = RingHom.ker ev.toRingHom := by
    ext p
    change p ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n)) ↔
      p ∈ RingHom.ker ev.toRingHom
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, RingHom.mem_ker]
    rfl
  have hev : Function.Surjective ev := by
    intro c
    exact ⟨MvPolynomial.C c, by simp [ev]⟩
  let e : (Poly n ⧸ RingHom.ker ev.toRingHom) ≃ₐ[ℂ] ℂ :=
    Ideal.quotientKerAlgEquivOfSurjective hev
  have hquot : Module.finrank ℂ (Poly n ⧸ I) = 1 := by
    rw [hI]
    simpa using e.toLinearEquiv.finrank_eq
  have hspace (T : ℕ) :
      (OAI.QuarticPowerFree.totalSpace T).map
        (Ideal.Quotient.mkₐ ℂ I).toLinearMap = ⊤ := by
    apply top_unique
    intro y hy
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Submodule.mem_map.mpr ⟨MvPolynomial.C (ev p), ?_, ?_⟩
    · exact OAI.QuarticPowerFree.mem_totalSpace.mpr (by simp)
    · change Ideal.Quotient.mk I (MvPolynomial.C (ev p)) =
        Ideal.Quotient.mk I p
      apply Ideal.Quotient.eq.mpr
      change MvPolynomial.C (ev p) - p ∈
        MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp [ev]
  have hfinrank (T : ℕ) :
      Module.finrank ℂ
        ((OAI.QuarticPowerFree.totalSpace T).map
          (Ideal.Quotient.mkₐ ℂ I).toLinearMap) = 1 := by
    rw [hspace T]
    simpa using hquot
  have hpoly : OAI.QuarticPowerFree.coordinateHilbert I = Polynomial.C 1 :=
    OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq _ _ (by
      filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually I] with T hT
      calc
        (OAI.QuarticPowerFree.coordinateHilbert I).eval (T : ℚ) =
        (Module.finrank ℂ
              ((OAI.QuarticPowerFree.totalSpace T).map
                (Ideal.Quotient.mkₐ ℂ I).toLinearMap) : ℚ) := hT.symm
        _ = 1 := by exact_mod_cast hfinrank T
        _ = (Polynomial.C 1).eval (T : ℚ) := by simp)
  rw [OAI.QuarticPowerFree.affineDegree, OAI.QuarticPowerFree.affineDimension, hpoly]
  simp

theorem zeroDim_irreducible_data {n : ℕ} (W : AffineVariety n)
    (hW : W.IsIrreducible) (hdim : W.dimension = 0) :
    ∃ x : Point n, W.points = {x} ∧ W.degree = 1 := by
  classical
  letI : W.ideal.IsPrime := hW
  have hmax : W.ideal.IsMaximal :=
    OAI.QuarticPowerFree.zeroDim_isMaximal W.ideal hdim
  obtain ⟨x, hIdeal⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hmax
  refine ⟨x, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      funext i
      have hXi : MvPolynomial.X i - MvPolynomial.C (x i) ∈ W.ideal := by
        rw [hIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simp
      have hz := hy (MvPolynomial.X i - MvPolynomial.C (x i)) hXi
      exact sub_eq_zero.mp (by simpa using hz)
    · intro hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      rw [hyx]
      intro p hp
      rw [hIdeal] at hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp hp
  · change OAI.QuarticPowerFree.affineDegree W.ideal = 1
    rw [hIdeal]
    exact affine_point_degree_one x

end
end DistinctDistances.TrackA
