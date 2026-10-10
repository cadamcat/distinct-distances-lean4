import DistinctDistances.Foundations.Projective

/-! Projective envelopes of exact-degree homogeneous equations, including component transfer. -/

namespace DistinctDistances.Bridges

open scoped BigOperators
noncomputable section

def homogeneousEquations {n : ℕ} (T : Set (ProjectivePoint n)) (D : ℕ) : Set (Poly n) :=
  {f | f.IsHomogeneous D ∧ ∀ v ∈ ProjectiveVariety.nonzeroRepresentatives T,
    MvPolynomial.eval v f = 0}

theorem homogeneous_eval_smul {n D : ℕ} (f : Poly n) (hf : f.IsHomogeneous D)
    (c : ℂ) (v : Point n) :
    MvPolynomial.eval (c • v) f = c ^ D * MvPolynomial.eval v f := by
  classical
  simp only [MvPolynomial.eval_eq, Pi.smul_apply, smul_eq_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← hf.degree_eq_sum_deg_support hs]
  ring

theorem homogeneous_eval_zero_mk_iff {n D : ℕ} (f : Poly n) (hf : f.IsHomogeneous D)
    (v : Point n) (hv : v ≠ 0) :
    MvPolynomial.eval (Projectivization.mk ℂ v hv).rep f = 0 ↔
      MvPolynomial.eval v f = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (a : ℂ) • v = (Projectivization.mk ℂ v hv).rep at ha
  rw [← ha, homogeneous_eval_smul f hf]
  simp only [mul_eq_zero, pow_ne_zero D (Units.ne_zero a), false_or]

theorem projective_envelope (n : ℕ) (T : Set (ProjectivePoint n)) (D : ℕ) :
    ∃ V : ProjectiveVariety n,
      V.points = {p | ∀ f ∈ homogeneousEquations T D, MvPolynomial.eval p.rep f = 0} ∧
      (∀ f : Poly n, f.IsHomogeneous D →
        (f ∈ V.ideal ↔ ∀ v ∈ ProjectiveVariety.nonzeroRepresentatives T,
          MvPolynomial.eval v f = 0)) ∧
      ∀ W : ProjectiveVariety n, W.ideal ∈ V.ideal.minimalPrimes →
        W.ideal ∈ (Ideal.span (homogeneousEquations T D)).minimalPrimes := by
  classical
  let E := homogeneousEquations T D
  let S : Set (ProjectivePoint n) := {p | ∀ f ∈ E, MvPolynomial.eval p.rep f = 0}
  let V := ProjectiveVariety.closure S
  have hE (f : Poly n) (hf : f ∈ E) : f ∈ V.ideal := by
    intro v hv
    obtain ⟨hv, hvS⟩ := hv
    exact (homogeneous_eval_zero_mk_iff f hf.1 v hv).mp (hvS f hf)
  have hpoints : V.points = S := by
    apply le_antisymm
    · intro p hp f hf
      exact hp p.rep p.rep_nonzero (Projectivization.mk_rep p) f (hE f hf)
    · exact ProjectiveVariety.subset_closure S
  have hT : T ⊆ S := by
    intro p hp f hf
    apply hf.2 p.rep
    exact ⟨p.rep_nonzero, by simpa only [Projectivization.mk_rep] using hp⟩
  refine ⟨V, hpoints, ?_, ?_⟩
  · intro f hf
    constructor
    · intro hfV v hv
      obtain ⟨hv, hvT⟩ := hv
      exact (ProjectiveVariety.subset_closure S (hT hvT)) v hv rfl f hfV
    · intro hzero
      exact hE f ⟨hf, hzero⟩
  · intro W hW
    let I := Ideal.span E
    have hIV : I ≤ V.ideal := Ideal.span_le.mpr hE
    have hIW : I ≤ W.ideal := hIV.trans hW.le
    let : W.ideal.IsPrime := hW.isPrime
    obtain ⟨P, hP, hPW⟩ := Ideal.exists_minimalPrimes_le hIW
    let : P.IsPrime := hP.isPrime
    obtain ⟨i, hi⟩ : ∃ i : Fin n, MvPolynomial.X i ∉ W.ideal := by
      by_contra h
      push Not at h
      have hone : (1 : Poly n) ∈ W.ideal :=
        W.isSaturated 1 (fun i => ⟨1, by simpa only [pow_one, mul_one] using h i⟩)
      exact hW.isPrime.one_notMem hone
    have hVP : V.ideal ≤ P := by
      intro f hf
      have hxf : MvPolynomial.X i * f ∈ P := by
        rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P]
        intro x hx
        by_cases hxzero : x = 0
        · subst x
          simp
        · have hxS : Projectivization.mk ℂ x hxzero ∈ S := by
            intro g hg
            apply (homogeneous_eval_zero_mk_iff g hg.1 x hxzero).mpr
            exact hx g (hP.le (Ideal.subset_span hg))
          have hfx := (ProjectiveVariety.subset_closure S hxS) x hxzero rfl f hf
          simp only [map_mul, MvPolynomial.aeval_X, hfx, mul_zero]
      exact (hP.isPrime.mem_or_mem hxf).resolve_left (fun hxi => hi (hPW hxi))
    have he : P = W.ideal := le_antisymm hPW (hW.2 ⟨hP.isPrime, hVP⟩ hPW)
    simpa only [he] using hP

end
end DistinctDistances.Bridges
