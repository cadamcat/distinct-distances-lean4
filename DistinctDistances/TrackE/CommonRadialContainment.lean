import DistinctDistances.TrackE.CommonPointLifting

/-! Extension of closed radial containment from a generic target open,
sparse-cones.tex:172–178. All representatives are retained. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

/-- Closed radial containment on a nonempty target open extends to the
complete radial image of the same irreducible physical target. -/
theorem common_radial_generic_subset {d : ℕ} (Y : AffineVariety d)
    (hY : Y.IsIrreducible) (p : Point d) (Z : ProjectiveVariety d)
    (hgen : TrackD.ForGeneralPoint Y (fun y =>
      ∃ hy : y ≠ p, radialProjection p y hy ∈ Z)) :
    (radialImage p Y).Subvariety Z := by
  intro a ha
  change a ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives
    {z | ∃ y ∈ Y.points, ∃ hy : y ≠ p, radialProjection p y hy = z})
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro v ⟨hv, y, hy, hpy, hproj⟩
  obtain ⟨c, hscalar⟩ := (Projectivization.mk_eq_mk_iff' ℂ v (y - p) hv
    (sub_ne_zero.mpr hpy)).mp hproj.symm
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at hscalar
    exact hv hscalar.symm
  let pull : Poly d := MvPolynomial.aeval
    (fun i => MvPolynomial.C c * (MvPolynomial.X i - MvPolynomial.C (p i))) a
  have heval (z : Point d) : MvPolynomial.eval z pull =
      MvPolynomial.eval (c • (z - p)) a := by
    dsimp only [pull]
    rw [TrackD.eval_polynomial_substitution]
    apply congrArg (fun t : Point d => MvPolynomial.eval t a)
    funext i
    simp [Pi.smul_apply, smul_eq_mul]
  have hzero : TrackD.ForGeneralPoint Y (fun z => MvPolynomial.eval z pull = 0) := by
    apply hgen.mono
    intro z hz hh
    obtain ⟨hpz, hZ⟩ := hh
    rw [heval]
    have hn : c • (z - p) ≠ 0 := smul_ne_zero hc (sub_ne_zero.mpr hpz)
    have hmk : Projectivization.mk ℂ (c • (z - p)) hn = radialProjection p z hpz :=
      (Projectivization.mk_eq_mk_iff' ℂ (c • (z - p)) (z - p) hn
        (sub_ne_zero.mpr hpz)).mpr ⟨c, rfl⟩
    simpa only [MvPolynomial.aeval_eq_eval] using hZ (c • (z - p)) hn hmk a ha
  have hz := TrackD.ForGeneralPoint.eval_zero hY pull hzero y hy
  rw [heval, hscalar] at hz
  simpa only [MvPolynomial.aeval_eq_eval] using hz

end
end DistinctDistances.SparseCones
