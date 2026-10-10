import DistinctDistances.TrackB.TripleRankChart

/-!
(P3) Rank recursions of the `x0`-deformation from the chart torsion statements:
`T1–T3` colon steps, the complete-intersection formula for `J_h` (prefix colons), and the
kernel recursion.
-/

namespace DistinctDistances.TrackB
namespace TripleRankRoute

set_option autoImplicit false
noncomputable section
open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

noncomputable local instance : AddRightCancelMonoid (Fin 3 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 3 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

section KernelRanks

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- (T1-rank) `G(s,t,u+1) = ZK(s,t,u+1) + H(s,t,u)` for large `s`. -/
theorem rank_T1 (c : Fin e → ℂ) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s →
      secRank (defJh C Γ H c) s t (u + 1) =
        secRank (kernelIdeal C Γ H) s t (u + 1) + secRank (defJh2 C Γ H c) s t u := by
  obtain ⟨Ntor, htor⟩ := torsion_compare (defJh2 C Γ H c)
    ((defJh C Γ H c).colon {ptVar (e := e) 0}) (defJh2_hom C Γ H c)
    (defJh2_le_colon C Γ H c) (fun f hf i => torsion_Jh_colon_x0' C Γ H c f hf i)
  refine ⟨Ntor, fun s t u hs => ?_⟩
  have heq := triple_shift_x0 s t u
  have hstep := HilbertMulti.colon_rank_step (tw e) (defJh C Γ H c)
    (defJh_hom C Γ H c) (ptVar (e := e) 0) (ptVar_hom (e := e) 0)
    (HilbertMulti.tripleDegree s t u)
  rw [heq] at hstep
  have hJK : Ideal.span ({ptVar (e := e) 0} : Set (TPoly e)) ⊔ defJh C Γ H c =
      kernelIdeal C Γ H := by
    rw [sup_comm]
    exact defJh_add_x0_eq C Γ H c
  rw [hJK] at hstep
  have hcol := htor s t u hs
  simp only [secRank] at hstep hcol ⊢
  omega


/-- (T2-rank) `H(s,t,u+1) = JK2(s,t,u+1) + H(s,t,u)` for large `s`. -/
theorem rank_T2 (c : Fin e → ℂ) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s →
      secRank (defJh2 C Γ H c) s t (u + 1) =
        secRank (defJK2 C Γ H c) s t (u + 1) + secRank (defJh2 C Γ H c) s t u := by
  obtain ⟨Ntor, htor⟩ := torsion_compare (defJh2 C Γ H c)
    ((defJh2 C Γ H c).colon {ptVar (e := e) 0}) (defJh2_hom C Γ H c)
    (OAI.PiExponentJets.W64.ideal_le_colon_singleton _ _)
    (fun f hf i => torsion_Jh2_colon_x0' C Γ H c f hf i)
  refine ⟨Ntor, fun s t u hs => ?_⟩
  have heq := triple_shift_x0 s t u
  have hstep := HilbertMulti.colon_rank_step (tw e) (defJh2 C Γ H c)
    (defJh2_hom C Γ H c) (ptVar (e := e) 0) (ptVar_hom (e := e) 0)
    (HilbertMulti.tripleDegree s t u)
  rw [heq] at hstep
  have hJK : Ideal.span ({ptVar (e := e) 0} : Set (TPoly e)) ⊔ defJh2 C Γ H c =
      defJK2 C Γ H c := by
    rw [sup_comm]
    exact defJh2_add_x0_eq C Γ H c
  rw [hJK] at hstep
  have hcol := htor s t u hs
  simp only [secRank] at hstep hcol ⊢
  omega


/-- (T3-rank) `ZK(s+2,t,u) = JK2(s+2,t,u) + ZK(s,t,u)` for large `s`. -/
theorem rank_T3 (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H))) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s →
      secRank (kernelIdeal C Γ H) (s + 2) t u =
        secRank (defJK2 C Γ H c) (s + 2) t u + secRank (kernelIdeal C Γ H) s t u := by
  obtain ⟨Ntor, htor⟩ := torsion_compare (kernelIdeal C Γ H)
    ((kernelIdeal C Γ H).colon {genQ (e := e) c ^ 2}) (kernelIdeal_hom C Γ H)
    (OAI.PiExponentJets.W64.ideal_le_colon_singleton _ _)
    (fun f hf i => torsion_JK_qsq' C Γ H c hc f hf i)
  refine ⟨Ntor, fun s t u hs => ?_⟩
  have heq := triple_shift_qsq s t u
  have hstep := HilbertMulti.colon_rank_step (tw e) (kernelIdeal C Γ H)
    (kernelIdeal_hom C Γ H) ((genQ (e := e) c) ^ 2) (genQ_sq_hom (e := e) c)
    (HilbertMulti.tripleDegree s t u)
  rw [heq] at hstep
  have hJK : Ideal.span ({genQ (e := e) c ^ 2} : Set (TPoly e)) ⊔ kernelIdeal C Γ H =
      defJK2 C Γ H c := by
    rw [sup_comm]
    rfl
  rw [hJK] at hstep
  have hcol := htor s t u hs
  simp only [secRank] at hstep hcol ⊢
  omega


/-- Prefix CI Koszul sum for the first `m` deformed generators (via `h` colon induction). -/
theorem prefix_rank (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)))
    (m : ℕ) (hm : m ≤ e) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s →
      (secRank (defJprefixNat C Γ H c m) s t u : ℤ) =
        ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (m.choose k : ℤ) *
          baseRankZ C Γ H (s - k) t ((u : ℤ) - k) := by
  induction m with
  | zero =>
    refine ⟨0, fun s t u _ => ?_⟩
    have hbase : defJprefixNat C Γ H c 0 = baseIdeal C Γ H := prefixNat_zero C Γ H c
    rw [hbase]
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
    unfold baseRankZ
    simp only [sub_zero, Nat.cast_zero, sub_zero]
    have hneg : ¬ ((u : ℤ) < 0) := by omega
    rw [if_neg hneg]
    simp
  | succ m ih =>
    by_cases hm' : m + 1 ≤ e
    · have hm_le : m ≤ e := by omega
      obtain ⟨Nm, hNm⟩ := ih hm_le
      have hm_lt : m < e := by omega
      obtain ⟨Ntor, htor⟩ := torsion_compare (defJprefixNat C Γ H c m)
        ((defJprefixNat C Γ H c m).colon {genH C c ⟨m, hm_lt⟩})
        (defJprefixNat_hom C Γ H c m)
        (OAI.PiExponentJets.W64.ideal_le_colon_singleton _ _)
        (fun f hf i => torsion_prefixNat' C Γ H c hc m hm_lt f hf i)
      refine ⟨max (Nm + 1) (max (Ntor + 1) (max e 1)), fun s t u hs => ?_⟩
      rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        have hL : secRank (defJprefixNat C Γ H c (m + 1)) s t 0 =
            secRank (baseIdeal C Γ H) s t 0 :=
          prefixNat_degree_zero C Γ H c (m + 1) s t
        have hR : (∑ k ∈ Finset.range (m + 1 + 1), (-1 : ℤ) ^ k * ((m + 1).choose k : ℤ) *
            baseRankZ C Γ H (s - k) t (((0 : ℕ) : ℤ) - k)) =
            (secRank (baseIdeal C Γ H) s t 0 : ℤ) := by
          rw [Finset.sum_eq_single 0]
          · simp [baseRankZ]
          · intro k hk hne
            have hkpos : 1 ≤ k := by
              have hmem := Finset.mem_range.mp hk
              omega
            have hneg : ((0 : ℕ) : ℤ) - (k : ℤ) < 0 := by
              push_cast
              omega
            unfold baseRankZ
            rw [if_pos hneg]
            ring
          · intro hcon
            simp at hcon
        rw [hL, hR]
      · obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
        obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
        have hsucc := prefixNat_succ C Γ H c m hm_lt
        have heq_shift := triple_shift_h s' t u'
        have hstep := HilbertMulti.colon_rank_step (tw e) (defJprefixNat C Γ H c m)
          (defJprefixNat_hom C Γ H c m) (genH C c ⟨m, hm_lt⟩) (genH_hom C c ⟨m, hm_lt⟩)
          (HilbertMulti.tripleDegree s' t u')
        rw [heq_shift] at hstep
        have hJK : Ideal.span ({genH C c ⟨m, hm_lt⟩} : Set (TPoly e)) ⊔
            defJprefixNat C Γ H c m =
            defJprefixNat C Γ H c (m + 1) := by
          rw [hsucc, sup_comm]
        rw [hJK] at hstep
        have hcol : secRank ((defJprefixNat C Γ H c m).colon
            {genH C c ⟨m, hm_lt⟩}) s' t u' =
            secRank (defJprefixNat C Γ H c m) s' t u' :=
          (htor s' t u' (by omega)).symm
        have hIH1 := hNm (s' + 1) t (u' + 1) (by omega)
        have hIH2 := hNm s' t u' (by omega)
        have hPascal : (∑ k ∈ Finset.range (m + 1 + 1), (-1 : ℤ) ^ k * ((m + 1).choose k : ℤ) *
              baseRankZ C Γ H (s' + 1 - k) t (((u' + 1 : ℕ) : ℤ) - k)) =
            (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (m.choose k : ℤ) *
              baseRankZ C Γ H (s' + 1 - k) t (((u' + 1 : ℕ) : ℤ) - k)) -
            (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (m.choose k : ℤ) *
              baseRankZ C Γ H (s' - k) t (((u' : ℕ) : ℤ) - k)) := by
          rw [alt_pascal (fun k => baseRankZ C Γ H (s' + 1 - k) t (((u' + 1 : ℕ) : ℤ) - k)) m]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          have hsk : s' + 1 - (k + 1) = s' - k := by omega
          have huk : (((u' + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ)) = ((u' : ℕ) : ℤ) - (k : ℤ) := by
            push_cast; ring
          simp only [hsk, huk]
        have hcast1 : ((secRank (defJprefixNat C Γ H c (m + 1)) (s' + 1) t (u' + 1) : ℕ) : ℤ) =
            ((secRank (defJprefixNat C Γ H c m) (s' + 1) t (u' + 1) : ℕ) : ℤ) -
            ((secRank (defJprefixNat C Γ H c m) s' t u' : ℕ) : ℤ) := by
          have hstepZ : ((secRank (defJprefixNat C Γ H c (m + 1)) (s' + 1) t (u' + 1) : ℕ) : ℤ) +
              ((secRank ((defJprefixNat C Γ H c m).colon
                {genH C c ⟨m, hm_lt⟩}) s' t u' : ℕ) : ℤ) =
              ((secRank (defJprefixNat C Γ H c m) (s' + 1) t (u' + 1) : ℕ) : ℤ) := by
            exact_mod_cast hstep
          have hcolZ : ((secRank ((defJprefixNat C Γ H c m).colon
              {genH C c ⟨m, hm_lt⟩}) s' t u' : ℕ) : ℤ) =
              ((secRank (defJprefixNat C Γ H c m) s' t u' : ℕ) : ℤ) := by
            exact_mod_cast hcol
          omega
        rw [hcast1, hIH1, hIH2, hPascal]
    · omega


/-- (T4) Complete-intersection formula for `J_h` (from `prefix_rank` at `m = e`). -/
theorem ci_Jh (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H))) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s →
      (secRank (defJh C Γ H c) s t u : ℤ) =
        ∑ k ∈ Finset.range (e + 1), (-1 : ℤ) ^ k * (e.choose k : ℤ) *
          baseRankZ C Γ H (s - k) t ((u : ℤ) - k) := by
  obtain ⟨N, hN⟩ := prefix_rank C Γ H c hc e le_rfl
  refine ⟨N, fun s t u hs => ?_⟩
  have heq : defJprefixNat C Γ H c e = defJh C Γ H c := prefixNat_ge C Γ H c e le_rfl
  rw [heq] at hN
  exact hN s t u hs


/-- Final `P3` kernel recursion from `T1-T3+T4` . -/
theorem kernel_recursion_complete (c : Fin e → ℂ)
    (hc : ∀ g : Poly (e + (e + e)),
      (∑ k, MvPolynomial.C (c k) * MvPolynomial.X (Fin.castAdd (e + e) k)) * g ∈
        MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)) →
      g ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H))) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s →
      (secRank (kernelIdeal C Γ H) (s + 2) t (u + 1) : ℤ) =
        secRank (kernelIdeal C Γ H) s t u +
          ∑ k ∈ Finset.range (e + 1), (-1 : ℤ) ^ k * (e.choose k : ℤ) *
            (baseRankZ C Γ H (s + 2 - k) t ((u : ℤ) + 1 - k) -
              baseRankZ C Γ H (s + 2 - k) t ((u : ℤ) - k)) := by
  obtain ⟨N1, h1⟩ := rank_T1 C Γ H c
  obtain ⟨N2, h2⟩ := rank_T2 C Γ H c
  obtain ⟨N3, h3⟩ := rank_T3 C Γ H c hc
  obtain ⟨N4, h4⟩ := ci_Jh C Γ H c hc
  refine ⟨N1 + N2 + N3 + N4, fun s t u hs => ?_⟩
  have hZ : ∀ u : ℕ, (secRank (kernelIdeal C Γ H) s t u : ℤ) =
      (secRank (defJh C Γ H c) (s + 2) t u : ℤ) - secRank (defJh2 C Γ H c) (s + 2) t u := by
    intro u
    rcases u with _ | u
    · have a := kernel_degree_zero' C Γ H s t
      have b := defJh_degree_zero C Γ H c (s + 2) t
      have c' := Jh2_degree_zero_eq C Γ H c hc (s + 2) t
      have d := base_add_qsq_rank C Γ H c hc s t 0
      omega
    · have a := h3 s t (u + 1) (by omega)
      have b := h1 (s + 2) t u (by omega)
      have d := h2 (s + 2) t u (by omega)
      omega
  have hT1 := h1 (s + 2) t u (by omega)
  have g1 := h4 (s + 2) t (u + 1) (by omega)
  have g0 := h4 (s + 2) t u (by omega)
  have hK : (secRank (kernelIdeal C Γ H) (s + 2) t (u + 1) : ℤ) =
      (secRank (defJh C Γ H c) (s + 2) t (u + 1) : ℤ) - secRank (defJh2 C Γ H c) (s + 2) t u := by
    omega
  rw [hK, hZ u, g1, g0]
  simp only [mul_sub, Finset.sum_sub_distrib]
  push_cast
  ring


end KernelRanks

end
end TripleRankRoute
end DistinctDistances.TrackB
