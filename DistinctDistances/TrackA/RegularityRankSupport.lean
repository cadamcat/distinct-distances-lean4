import DistinctDistances.TrackA.Definitions
import DistinctDistances.OAIInterface.HilbertSimplex

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- `poly:augmented-lower`, polynomial.tex:514–530. The augmented map is
only complex-linear. Its kernel hypothesis applies only in degree D;
its base-multiplication identity differentiates no fiber coefficients. -/
theorem regularity_linear_monomial_lifting {n : ℕ} {Ω : Type*}
    [Field Ω] [Algebra ℂ Ω] (V : AffineVariety n) (k r q D : ℕ)
    (hqD : q ≤ D) (t : Fin k → Ω) (ht : AlgebraicIndependent ℂ t)
    (base : Fin k → Poly n) (hbase : ∀ j, (base j).totalDegree ≤ 1)
    (transverse : Fin r → Poly n)
    (htransverse : ∀ i, (transverse i).totalDegree ≤ q)
    (psi : Poly n →ₗ[ℂ] (Fin r → Ω))
    (hkernel : ∀ f : Poly n, f ∈ V.ideal → f.totalDegree ≤ D → psi f = 0)
    (hmult : ∀ (f : Poly n) (p : Poly k),
      psi (f * MvPolynomial.aeval base p) = MvPolynomial.aeval t p • psi f)
    (hindependent : LinearIndependent Ω (fun i => psi (transverse i))) :
    (r : ℚ) * ((D-q+k).choose k : ℚ) ≤ (V.hilbert D : ℚ) := by
  classical
  let A := OAI.QuarticPowerFree.simplexExponents k (D-q)
  let Alpha := {a : Fin k →₀ ℕ // a ∈ A}
  let Idx := Fin r × Alpha
  let baseEval : MvPolynomial (Fin k) ℂ →ₐ[ℂ] Poly n := MvPolynomial.aeval base
  let baseMono (a : Alpha) : Poly n :=
    baseEval (MvPolynomial.monomial a.val 1)
  let p (z : Idx) : Poly n := transverse z.1 * baseMono z.2
  have hbaseDegree (a : Alpha) : (baseMono a).totalDegree ≤ a.val.degree := by
    change (MvPolynomial.aeval base (MvPolynomial.monomial a.val 1)).totalDegree ≤ _
    rw [MvPolynomial.aeval_monomial]
    simp only [map_one, one_mul]
    calc
      (a.val.prod fun j e => base j ^ e).totalDegree ≤
          ∑ j : Fin k, (base j ^ a.val j).totalDegree := by
        rw [Finsupp.prod_fintype _ _ (by intro j; simp)]
        simpa using
          (MvPolynomial.totalDegree_finsetProd Finset.univ fun j => base j ^ a.val j)
      _ ≤ ∑ j : Fin k, a.val j := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (base j ^ a.val j).totalDegree ≤ a.val j * (base j).totalDegree :=
            MvPolynomial.totalDegree_pow _ _
          _ ≤ a.val j := by
            simpa using Nat.mul_le_mul_left (a.val j) (hbase j)
      _ = a.val.degree := (Finsupp.degree_eq_sum _).symm
  have hpDegree (z : Idx) : (p z).totalDegree ≤ D := by
    have ha := (OAI.QuarticPowerFree.mem_simplexExponents z.2.val).mp z.2.property
    calc
      (p z).totalDegree ≤ (transverse z.1).totalDegree + (baseMono z.2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ q + (D-q) := Nat.add_le_add (htransverse z.1) (hbaseDegree z.2 |>.trans ha)
      _ ≤ D := by omega
  let monEval (a : Alpha) : Ω :=
    MvPolynomial.aeval t (MvPolynomial.monomial a.val (1 : ℂ))
  let w (i : Fin r) : Fin r → Ω := psi (transverse i)
  have hfacet (z : Idx) : psi (p z) = monEval z.2 • w z.1 := by
    exact hmult (transverse z.1) (MvPolynomial.monomial z.2.val 1)
  let v (z : Idx) : V.restrictionSpace D :=
    ⟨Ideal.Quotient.mk V.ideal (p z), by
      change Ideal.Quotient.mk V.ideal (p z) ∈
        (OAI.QuarticPowerFree.totalSpace D).map
          (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap
      apply Submodule.mem_map.mpr
      exact ⟨p z, OAI.QuarticPowerFree.mem_totalSpace.mpr (hpDegree z), rfl⟩⟩
  have hquotientLI : LinearIndependent ℂ
      (fun z : Idx => Ideal.Quotient.mk V.ideal (p z)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let P (i : Fin r) : MvPolynomial (Fin k) ℂ :=
      ∑ a : Alpha, MvPolynomial.C (c (i, a)) * MvPolynomial.monomial a.val 1
    have hPEval (i : Fin r) :
        MvPolynomial.aeval t (P i) =
          ∑ a : Alpha, algebraMap ℂ Ω (c (i, a)) * monEval a := by
      simp [P, monEval]
    have hsumIdeal : (∑ z : Idx, c z • p z) ∈ V.ideal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change (Ideal.Quotient.mkₐ ℂ V.ideal) (∑ z : Idx, c z • p z) = 0
      simpa only [map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk] using hc
    have hsumDegree : (∑ z : Idx, c z • p z).totalDegree ≤ D := by
      apply OAI.QuarticPowerFree.mem_totalSpace.mp
      apply Submodule.sum_mem
      intro z hz
      exact (OAI.QuarticPowerFree.totalSpace D).smul_mem (c z)
        (OAI.QuarticPowerFree.mem_totalSpace.mpr (hpDegree z))
    have hsumEval : ∑ z : Idx, c z • psi (p z) = 0 := by
      simpa only [map_sum, map_smul] using
        hkernel (∑ z : Idx, c z • p z) hsumIdeal hsumDegree
    rw [Fintype.sum_prod_type] at hsumEval
    simp_rw [hfacet] at hsumEval
    simp_rw [Algebra.smul_def] at hsumEval
    have hvector : ∑ i : Fin r, (MvPolynomial.aeval t (P i)) • w i = 0 := by
      ext j
      have hj := congrArg (fun f : Fin r → Ω => f j) hsumEval
      have hcoord :
          ∑ i : Fin r, ∑ a : Alpha,
            algebraMap ℂ Ω (c (i, a)) * (monEval a * w i j) = 0 := by
        simpa using hj
      have hcoord' :
          ∑ i : Fin r, MvPolynomial.aeval t (P i) * w i j = 0 := by
        calc
          _ = ∑ i : Fin r, (∑ a : Alpha,
              algebraMap ℂ Ω (c (i, a)) * monEval a) * w i j := by
            simp_rw [hPEval]
          _ = ∑ i : Fin r, ∑ a : Alpha,
              (algebraMap ℂ Ω (c (i, a)) * monEval a) * w i j := by
            simp_rw [Finset.sum_mul]
          _ = ∑ i : Fin r, ∑ a : Alpha,
              algebraMap ℂ Ω (c (i, a)) * (monEval a * w i j) := by
            simp_rw [mul_assoc]
          _ = 0 := hcoord
      simpa [Pi.smul_apply] using hcoord'
    have hcoeff : ∀ i : Fin r, MvPolynomial.aeval t (P i) = 0 :=
      (Fintype.linearIndependent_iff.mp hindependent) _ hvector
    have htinj : Function.Injective (MvPolynomial.aeval t) :=
      (algebraicIndependent_iff_injective_aeval.mp ht)
    have hPzero (i : Fin r) : P i = 0 := by
      apply htinj
      simpa using hcoeff i
    intro z
    have hc0 := congrArg (fun f : MvPolynomial (Fin k) ℂ => f.coeff z.2.val)
      (hPzero z.1)
    have hc0sum :
        (∑ a : Alpha, c (z.1, a) * if a.val = z.2.val then (1 : ℂ) else 0) = 0 := by
      simpa only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_monomial, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply] using hc0
    have hsumid :
        (∑ a : Alpha, c (z.1, a) * if a.val = z.2.val then (1 : ℂ) else 0) =
          c (z.1, z.2) := by
      rw [Finset.sum_eq_single z.2]
      · simp
      · intro a ha hne
        have hval : a.val ≠ z.2.val := by
          intro he
          exact hne (Subtype.ext he)
        simp [hval]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    exact hsumid.symm.trans hc0sum
  have hli : LinearIndependent ℂ v := by
    apply LinearIndependent.of_comp (V.restrictionSpace D).subtype
    change LinearIndependent ℂ (fun z : Idx => (v z : Poly n ⧸ V.ideal))
    exact hquotientLI
  have hcard : Fintype.card Idx = r * (D-q+k).choose k := by
    simp [Idx, Alpha, A, OAI.QuarticPowerFree.card_simplexExponents]
  have hdim := hli.fintype_card_le_finrank
  rw [hcard] at hdim
  exact_mod_cast hdim

end
end DistinctDistances.TrackA
