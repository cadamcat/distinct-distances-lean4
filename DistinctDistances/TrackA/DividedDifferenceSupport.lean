import DistinctDistances.TrackA.Definitions

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPolynomial

private theorem totalDegree_le_add_of_disjoint {F : Type*} [Field F] {c : ℕ}
    (p q : FieldPoly c F) (h : Disjoint p.support q.support) :
    p.totalDegree ≤ (p+q).totalDegree := by
  apply totalDegree_le_of_support_subset
  have hh := support_sdiff_support_subset_support_add p q
  intro m hm
  exact hh (Finset.mem_sdiff.mpr ⟨hm, fun hq => Finset.disjoint_left.mp h hm hq⟩)

/-- Telescoping divided differences retain the exact degree loss even when
their coefficients lie in an algebra with nilpotents. -/
theorem divided_difference_exists {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    {c : ℕ} (p : FieldPoly c F) (z : Fin c → A) :
    ∃ Q : Fin c → MvPolynomial (Fin c) A,
      (∀ i, Q i = 0 ∨ (Q i).totalDegree < p.totalDegree) ∧
      MvPolynomial.map (algebraMap F A) p - C (aeval z p) =
        ∑ i, Q i * (X i - C (z i)) := by
  induction p using MvPolynomial.induction_on'' with
  | C a =>
    refine ⟨0, by simp, ?_⟩
    simp
  | monomial_add a b f ha hb hf hm =>
    obtain ⟨Q, hQ, heQ⟩ := hm
    obtain ⟨T, hT, heT⟩ := hf
    have hdis := disjoint_support_monomial ha hb
    have hpdeg := totalDegree_le_add_of_disjoint (monomial a b) f hdis
    have hfdeg : f.totalDegree ≤ (monomial a b+f).totalDegree := by
      simpa only [add_comm] using totalDegree_le_add_of_disjoint f (monomial a b) hdis.symm
    refine ⟨fun i => Q i+T i, ?_, ?_⟩
    · intro i
      by_cases hi : Q i+T i = 0
      · exact Or.inl hi
      · right
        have hD : 0 < (monomial a b+f).totalDegree := by
          rcases hQ i with hQi | hQi
          · have hTi : T i ≠ 0 := by intro ht; exact hi (by rw [hQi, ht, add_zero])
            rcases hT i with ht | ht
            · exact False.elim (hTi ht)
            · omega
          · omega
        have hQi : (Q i).totalDegree ≤ (monomial a b+f).totalDegree-1 := by
          rcases hQ i with hqi | hqi
          · simp [hqi]
          · omega
        have hTi : (T i).totalDegree ≤ (monomial a b+f).totalDegree-1 := by
          rcases hT i with hti | hti
          · simp [hti]
          · omega
        have hsum := (totalDegree_add (Q i) (T i)).trans (max_le hQi hTi)
        change (Q i+T i).totalDegree < (monomial a b+f).totalDegree
        omega
    · simp only [map_add, C_add, add_mul, Finset.sum_add_distrib]
      rw [← heQ, ← heT]
      ring
  | mul_X p n hp =>
    by_cases hp0 : p = 0
    · subst p
      refine ⟨0, by simp, ?_⟩
      simp
    obtain ⟨Q, hQ, heQ⟩ := hp
    have hdeg : (p*X n).totalDegree = p.totalDegree+1 := by
      rw [totalDegree_mul_of_isDomain hp0 (X_ne_zero n), totalDegree_X]
    refine ⟨fun i => Q i * X n + if i=n then C (aeval z p) else 0, ?_, ?_⟩
    · intro i
      right
      have hQi : (Q i * X n).totalDegree ≤ p.totalDegree := by
        rcases hQ i with hqi | hqi
        · simp [hqi]
        · have hh := totalDegree_mul (Q i) (X n)
          have hX : (X n : MvPolynomial (Fin c) A).totalDegree ≤ 1 := by
            exact (isHomogeneous_X A n).totalDegree_le
          omega
      have hconst : (if i=n then C (aeval z p) else (0 : MvPolynomial (Fin c) A)).totalDegree = 0 := by
        split_ifs <;> simp only [totalDegree_C, totalDegree_zero]
      have hh := totalDegree_add (Q i*X n) (if i=n then C (aeval z p) else 0)
      rw [hconst] at hh
      change (Q i*X n + if i=n then C (aeval z p) else 0).totalDegree < (p*X n).totalDegree
      rw [hdeg]
      omega
    · simp only [map_mul, map_X, aeval_X]
      have hs : (∑ i, (Q i * X n + if i=n then C (aeval z p) else 0) * (X i-C (z i))) =
          (∑ i, Q i*(X i-C (z i))) * X n + C (aeval z p)*(X n-C (z n)) := by
        simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs, ← heQ]
      ring

end
end DistinctDistances.TrackA
