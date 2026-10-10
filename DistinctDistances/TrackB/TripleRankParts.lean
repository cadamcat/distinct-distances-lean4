import DistinctDistances.TrackB.MixedHilbert
import DistinctDistances.TrackB.MBPart2Aux

/-!
Step (ii) of `DistinctDistances.TrackB.triple_rank_identity`: chart-torsion uniformity
(per-chart torsion generation implies a uniform exponent and eventual section-rank
agreement), with the finite homogeneous generating sets it uses.
-/

namespace DistinctDistances.TrackB
namespace TripleRankParts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

noncomputable local instance : AddRightCancelMonoid (Fin 2 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 2 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

noncomputable local instance : AddRightCancelMonoid (Fin 3 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 3 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

/-- Finite homogeneous generating set for a block-homogeneous triple ideal,
via Noetherian finite generation plus weighted-component homogenization. -/
theorem chart_finite_hom_gens {e : ℕ}
    (K : Ideal (Poly (e + (e + e) + (skewDim e + 1))))
    (hK : K.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))))) :
    ∃ G : Finset (Poly (e + (e + e) + (skewDim e + 1))),
      (∀ g ∈ G, g ∈ K) ∧
      (∀ g ∈ G, ∃ d, g.IsWeightedHomogeneous
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) d) ∧
      Ideal.span (G : Set (Poly (e + (e + e) + (skewDim e + 1)))) = K := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian K : K.FG)
  refine ⟨s.biUnion (fun g => (g.support.image (Finsupp.weight
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))))).image
      (fun m => MvPolynomial.weightedHomogeneousComponent
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) m g)),
    ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0s, hgmem⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hgmem
    have hg0K : g0 ∈ K := by
      rw [← hs]
      exact Submodule.subset_span hg0s
    exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem ℂ
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      hK hg0K _
  · intro g hg
    obtain ⟨g0, hg0s, hgmem⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hgmem
    exact ⟨m, MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous m g0⟩
  · apply le_antisymm
    · apply Ideal.span_le.mpr
      intro g hg
      have hgF : g ∈ s.biUnion (fun g => (g.support.image (Finsupp.weight
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))))).image
          (fun m => MvPolynomial.weightedHomogeneousComponent
            (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) m g)) :=
        Finset.mem_coe.mp hg
      obtain ⟨g0, hg0s, hgmem⟩ := Finset.mem_biUnion.mp hgF
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hgmem
      have hg0K : g0 ∈ K := by
        rw [← hs]
        exact Submodule.subset_span hg0s
      exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem ℂ
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
        hK hg0K m
    · rw [← hs]
      apply Submodule.span_le.mpr
      intro g hg
      have hsum : g = ∑ m ∈ g.support.image (Finsupp.weight
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))),
          MvPolynomial.weightedHomogeneousComponent
            (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) m g := by
        ext d
        simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_weightedHomogeneousComponent]
        by_cases hd : d ∈ g.support
        · have hwd : Finsupp.weight (HilbertMulti.blockWeight
              (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) d ∈
              g.support.image (Finsupp.weight (HilbertMulti.blockWeight
                (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))) :=
            Finset.mem_image.mpr ⟨d, hd, rfl⟩
          rw [Finset.sum_eq_single (Finsupp.weight (HilbertMulti.blockWeight
            (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) d)]
          · simp
          · intro m hm hne
            have hne' : Finsupp.weight (HilbertMulti.blockWeight
                (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) d ≠ m :=
              fun h => hne h.symm
            simp [hne']
          · intro hcon
            exact False.elim (hcon hwd)
        · have hcoeff : g.coeff d = 0 := MvPolynomial.notMem_support_iff.mp hd
          rw [Finset.sum_eq_zero]
          · simp [hcoeff]
          · intro m hm
            simp only [Finset.mem_image] at hm
            obtain ⟨a, ha, rfl⟩ := hm
            by_cases heq : Finsupp.weight (HilbertMulti.blockWeight
                (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) d =
                Finsupp.weight (HilbertMulti.blockWeight
                  (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) a
            · simp [heq, hcoeff]
            · simp [heq]
      rw [hsum]
      apply Ideal.sum_mem
      intro m hm
      apply Ideal.subset_span
      apply Finset.mem_coe.mpr
      apply Finset.mem_biUnion.mpr
      exact ⟨g, hg, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩

/-- (ii) Chart-torsion uniformity for the fiber equations.

Given fiber polynomials `F`, a base ideal `B`, and the incidence vanishing
ideal `K ⊇ span F ⊔ B`, per-chart torsion generation (each `p ∈ K` is
killed into `span F ⊔ B` by a power of the chart direction variable)
implies a UNIFORM exponent `N` with section-rank agreement against the
actual `tripleHilbert` ranks for all pieces of direction-degree
`s ≥ e * N + 1`.

Concrete instantiation in `Degree.lean`: `F k` is the `μ = 0` image of the
`k`-th deformed equation, `B` is the pair-ideal pullback
(`pairIdeal_map_le_tripleIdeal`), `K` is the triple vanishing ideal
(`hK := rfl`); the per-chart hypothesis is proved in (vi) from
`fiberPolynomial_weighted`, `eval_fiberPolynomial`,
`fiberPolynomial_mem_vanishingIdeal` and the `IncidenceLocal` chart tools
(`quotientEvaluation_free_split`, `directionAnnihilatorEquiv`,
`variables_regular`, `variables_koszul_exact`).

Proof sketch: the quotient `K ⧸ (span F ⊔ B)` is finitely generated
(Noetherian ring), so per-element torsion upgrades to a uniform killer
`N` (one power per generator, take the max); a direction monomial of
degree `s ≥ e * N + 1` is divisible by some `d_{i0}^N` (pigeonhole on the
`e` direction variables, cf. `blockPiece_smul_zero`), so the quotient
sections vanish there; `sectionFactor_surjective` plus kernel-vanishing
give section isomorphisms, hence `finrank` equality against `span F ⊔ B`;
finally `tripleBlockPiece` identifies `K`-sections with `tripleSection`,
i.e. `tripleHilbert`. -/
theorem chart_torsion_uniform {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (F : Fin e → Poly (e + (e + e) + (skewDim e + 1)))
    (B K : Ideal (Poly (e + (e + e) + (skewDim e + 1))))
    (hK : K = MvPolynomial.vanishingIdeal ℂ
      (tripleRepresentatives (incidenceTriples C Γ H)))
    (hFB : Ideal.span (Set.range F) ⊔ B ≤ K)
    (hChart : ∀ i0 : Fin e, ∀ p : Poly (e + (e + e) + (skewDim e + 1)),
      p ∈ K → ∃ N : ℕ,
        (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i0)) ^ N) * p ∈
          Ideal.span (Set.range F) ⊔ B) :
    ∃ N : ℕ, ∀ s t u : ℕ, e * N + 1 ≤ s →
      Module.finrank ℂ (HilbertMulti.sectionSpace
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
        (Ideal.span (Set.range F) ⊔ B) (HilbertMulti.tripleDegree s t u)) =
      tripleHilbert (incidenceTriples C Γ H) s t u := by
  classical
  let w := HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))
  let J : Ideal (Poly (e + (e + e) + (skewDim e + 1))) :=
    Ideal.span (Set.range F) ⊔ B
  have hKhom : K.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ w) := by
    rw [hK]
    exact tripleRepresentatives_blockHomogeneous _
  by_cases he0 : e = 0
  · refine ⟨0, ?_⟩
    intro s t u hs
    subst he0
    simp only [Nat.zero_mul, zero_add] at hs
    have hset_empty : ({d : Fin (0 + (0 + 0) + (skewDim 0 + 1)) →₀ ℕ |
        (∑ i : Fin 0, d (Fin.castAdd (skewDim 0 + 1) (Fin.castAdd (0 + 0) i))) = s ∧
        (∑ i : Fin (0 + 0), d (Fin.castAdd (skewDim 0 + 1) (Fin.natAdd 0 i))) = t ∧
        (∑ i : Fin (skewDim 0 + 1), d (Fin.natAdd (0 + (0 + 0)) i)) = u} : Set _) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro d hd
      simp only [Set.mem_setOf_eq] at hd
      simp at hd
      omega
    have hpiece : MvPolynomial.weightedHomogeneousSubmodule ℂ
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks 0 (0 + 0) (skewDim 0 + 1)))
        (HilbertMulti.tripleDegree s t u) = ⊥ := by
      rw [HilbertMulti.tripleBlockPiece 0 (0 + 0) (skewDim 0 + 1) s t u, hset_empty,
        MvPolynomial.restrictSupport_eq_span, Set.image_empty, Submodule.span_empty]
    have hJ0 : HilbertMulti.sectionSpace
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks 0 (0 + 0) (skewDim 0 + 1)))
        (Ideal.span (Set.range (F : Fin 0 → Poly (0 + (0 + 0) + (skewDim 0 + 1)))) ⊔ B)
        (HilbertMulti.tripleDegree s t u) = ⊥ := by
      unfold HilbertMulti.sectionSpace
      rw [hpiece, Submodule.map_bot]
    have hT0 : tripleSection (incidenceTriples C Γ H) s t u = ⊥ := by
      unfold tripleSection
      rw [hset_empty, MvPolynomial.restrictSupport_eq_span, Set.image_empty,
        Submodule.span_empty, Submodule.map_bot]
    rw [hJ0]
    unfold tripleHilbert
    rw [hT0, finrank_bot, finrank_bot]
  · have hepos : 0 < e := Nat.pos_of_ne_zero he0
    obtain ⟨G, hGmem, hGhom, hGspan⟩ := chart_finite_hom_gens K hKhom
    let pairs : Finset (Fin e × Poly (e + (e + e) + (skewDim e + 1))) :=
      Finset.univ.product G
    have hEx : ∀ ij ∈ pairs, ∃ N : ℕ,
        (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) ij.1)) ^ N) *
          ij.2 ∈ J := by
      intro ij hij
      simp [pairs, Finset.mem_product] at hij
      exact hChart ij.1 ij.2 (hGmem ij.2 hij)
    have hEx' : ∀ ij : Fin e × Poly (e + (e + e) + (skewDim e + 1)), ∃ N : ℕ,
        (ij ∈ pairs →
          (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) ij.1)) ^ N) *
            ij.2 ∈ J) := by
      intro ij
      by_cases hmem : ij ∈ pairs
      · obtain ⟨N, hN⟩ := hEx ij hmem
        exact ⟨N, fun _ => hN⟩
      · exact ⟨0, fun h => False.elim (hmem h)⟩
    choose Nfun hNfun using hEx'
    let N0 : ℕ := pairs.sup (fun ij => Nfun ij)
    have hN0le : ∀ ij ∈ pairs, Nfun ij ≤ N0 := fun ij hij =>
      Finset.le_sup hij
    have hN0kill : ∀ i0 : Fin e, ∀ g ∈ G,
        (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i0)) ^ N0) *
          g ∈ J := by
      intro i0 g hg
      have hijmem : (i0, g) ∈ pairs := by
        simp [pairs, Finset.mem_product, hg]
      have hNle : Nfun (i0, g) ≤ N0 := hN0le _ hijmem
      have hbase := hNfun (i0, g) hijmem
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hNle
      have hpow : ((MvPolynomial.X (Fin.castAdd (skewDim e + 1)
          (Fin.castAdd (e + e) i0)) ^ N0 : Poly (e + (e + e) + (skewDim e + 1)))) =
          (MvPolynomial.X (Fin.castAdd (skewDim e + 1)
            (Fin.castAdd (e + e) i0)) ^ k) *
          ((MvPolynomial.X (Fin.castAdd (skewDim e + 1)
            (Fin.castAdd (e + e) i0)) ^ (Nfun (i0, g)))) := by
        rw [hk, pow_add, mul_comm]
      rw [hpow, mul_assoc]
      apply Ideal.mul_mem_left
      exact hbase
    let Smax : ℕ := G.sup (fun g => g.totalDegree)
    let N : ℕ := N0 + Smax
    have key : ∀ H : Finset (Poly (e + (e + e) + (skewDim e + 1))), H ⊆ G →
        ∀ (p : Poly (e + (e + e) + (skewDim e + 1))) (s t u : ℕ),
        e * N + 1 ≤ s → p.IsWeightedHomogeneous w (HilbertMulti.tripleDegree s t u) →
        p ∈ Ideal.span (H : Set _) → p ∈ J := by
      intro H
      induction H using Finset.induction with
      | empty =>
        intro _ p s t u hs hp hmem
        simp only [Finset.coe_empty, Ideal.span_empty] at hmem
        have hp0 : p = 0 := by simpa using hmem
        rw [hp0]
        exact Ideal.zero_mem J
      | @insert a s has ih =>
        intro hsub p st tt uu hs hp hmem
        have haG : a ∈ G := hsub (Finset.mem_insert_self a s)
        have hsG : s ⊆ G := fun x hx => hsub (Finset.mem_insert_of_mem hx)
        have hIhom : (Ideal.span (s : Set (Poly (e + (e + e) + (skewDim e + 1))))).IsHomogeneous
            (MvPolynomial.weightedHomogeneousSubmodule ℂ w) := by
          apply Ideal.homogeneous_span
          intro g hg
          obtain ⟨d, hd⟩ := hGhom g (hsG hg)
          exact ⟨d, hd⟩
        have hspan_eq : Ideal.span ((insert a s : Finset _) : Set _) =
            Ideal.span ({a} : Set _) ⊔ Ideal.span (s : Set _) := by
          rw [Finset.coe_insert, Ideal.span_insert]
        rw [hspan_eq] at hmem
        by_cases ha0 : a = 0
        · subst ha0
          simp only [Ideal.span_singleton_zero, bot_sup_eq] at hmem
          exact ih hsG p st tt uu hs hp hmem
        · obtain ⟨d0, hd0⟩ := hGhom a haG
          by_cases hle : d0 ≤ HilbertMulti.tripleDegree st tt uu
          · let n : Fin 3 →₀ ℕ := HilbertMulti.tripleDegree st tt uu - d0
            have hnadd : n + d0 = HilbertMulti.tripleDegree st tt uu := by
              ext i
              simp only [n, Finsupp.add_apply, Finsupp.tsub_apply]
              have hi : d0 i ≤ HilbertMulti.tripleDegree st tt uu i := hle i
              omega
            have hp' : p.IsWeightedHomogeneous w (n + d0) := by
              rw [hnadd]
              exact hp
            have hex : ∃ cf : Poly (e + (e + e) + (skewDim e + 1)),
                cf.IsWeightedHomogeneous w n ∧
                p - cf * a ∈ Ideal.span (s : Set _) :=
              HilbertMulti.homogeneous_mem_decomposition w _ hIhom a p hd0 hp' hmem
            obtain ⟨cf, hcfhom, hcfmem⟩ := hex
            have hremJ : p - cf * a ∈ J := by
              apply ih hsG _ st tt uu hs _ hcfmem
              have hcfamul : (cf * a).IsWeightedHomogeneous w
                  (HilbertMulti.tripleDegree st tt uu) := hnadd ▸ hcfhom.mul hd0
              exact hp.sub hcfamul
            have hprodJ : cf * a ∈ J := by
              have haT : ∀ i0 : Fin e,
                  (MvPolynomial.X (Fin.castAdd (skewDim e + 1)
                    (Fin.castAdd (e + e) i0)) ^ N0) * a ∈ J :=
                fun i0 => hN0kill i0 a haG
              have hSle : a.totalDegree ≤ Smax :=
                Finset.le_sup (s := G) (f := fun g => g.totalDegree) haG
              have hdir_le : d0 0 ≤ Smax := by
                have hsupp_ne : a.support.Nonempty := by
                  rw [Finset.nonempty_iff_ne_empty]
                  intro hcon
                  exact ha0 (MvPolynomial.support_eq_empty.mp hcon)
                obtain ⟨b, hb⟩ := hsupp_ne
                have hbw : Finsupp.weight w b = d0 := by
                  have hamem : a ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ w d0 :=
                    hd0
                  rw [HilbertMulti.blockPiece_eq] at hamem
                  rw [MvPolynomial.mem_restrictSupport_iff] at hamem
                  have hbmem : b ∈ {a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
                      a.mapDomain (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) = d0} :=
                    hamem (Finset.mem_coe.mpr hb)
                  have hmap : b.mapDomain (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) = d0 :=
                    hbmem
                  rw [HilbertMulti.weight_blockWeight]
                  exact hmap
                have hdir_eq : (Finsupp.weight w b) 0 =
                    ∑ i : Fin e, b (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) := by
                  rw [HilbertMulti.weight_blockWeight, HilbertMulti.mapDomain_fin_apply]
                  simp [Fin.sum_univ_add, HilbertMulti.tripleBlocks]
                have htot_ge : (∑ i : Fin e, b (Fin.castAdd (skewDim e + 1)
                    (Fin.castAdd (e + e) i))) ≤ b.sum (fun _ e => e) := by
                  have hinj : Function.Injective (fun i : Fin e =>
                      Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i) :
                      Fin e → Fin (e + (e + e) + (skewDim e + 1))) := by
                    intro i j hij
                    have hval := congrArg Fin.val hij
                    simp only [Fin.val_castAdd, Fin.val_castAdd] at hval
                    exact Fin.ext hval
                  have himg : (∑ i : Fin e, b (Fin.castAdd (skewDim e + 1)
                      (Fin.castAdd (e + e) i))) =
                      ∑ j ∈ Finset.image (fun i : Fin e =>
                        Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))
                        Finset.univ, b j := by
                    rw [Finset.sum_image]
                    intro i _ j _ hij
                    exact hinj hij
                  rw [himg]
                  have huniv : (∑ j ∈ Finset.image (fun i : Fin e =>
                      Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))
                      Finset.univ, b j) ≤
                      ∑ j ∈ (Finset.univ : Finset (Fin (e + (e + e) + (skewDim e + 1)))), b j :=
                    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                      (fun j _ _ => Nat.zero_le _)
                  have hsupp_eq : (∑ j ∈ (Finset.univ : Finset (Fin (e + (e + e) + (skewDim e + 1)))), b j) =
                      b.sum (fun _ e => e) := by
                    simp only [Finsupp.sum]
                    apply Eq.symm
                    apply Finset.sum_subset
                    · exact Finset.subset_univ _
                    · intro j _ hjn
                      have hj0 : b j = 0 :=
                        Finsupp.notMem_support_iff.mp hjn
                      simp [hj0]
                  omega
                have hle_tot : b.sum (fun _ e => e) ≤ a.totalDegree :=
                  MvPolynomial.le_totalDegree hb
                calc d0 0 = (Finsupp.weight w b) 0 := by rw [hbw]
                  _ = ∑ i : Fin e, b (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) :=
                    hdir_eq
                  _ ≤ b.sum (fun _ e => e) := htot_ge
                  _ ≤ a.totalDegree := hle_tot
                  _ ≤ Smax := hSle
              have hn0ge : e * N0 + 1 ≤ n 0 := by
                have hst0 : (HilbertMulti.tripleDegree st tt uu) 0 = st := by
                  simp [HilbertMulti.tripleDegree]
                have hn0_eq : n 0 = st - d0 0 := by
                  simp only [n, Finsupp.tsub_apply, hst0]
                have hNdef : N = N0 + Smax := rfl
                have hdist : e * (N0 + Smax) = e * N0 + e * Smax := by
                  rw [mul_add]
                have hSmul : Smax ≤ e * Smax := by
                  have h1e : 1 ≤ e := hepos
                  calc Smax = 1 * Smax := by rw [one_mul]
                    _ ≤ e * Smax := Nat.mul_le_mul_right Smax h1e
                have hsN : e * (N0 + Smax) + 1 ≤ st := by
                  rw [hNdef] at hs
                  exact hs
                set a1 := e * N0 with ha1
                set b1 := e * Smax with hb1
                have hsN' : a1 + b1 + 1 ≤ st := by
                  rw [ha1, hb1, ← hdist]
                  exact hsN
                have hSmul' : Smax ≤ b1 := by
                  rw [hb1]
                  exact hSmul
                omega
              have hcf_eq : cf = ∑ b ∈ cf.support,
                  MvPolynomial.monomial b (cf.coeff b) :=
                MvPolynomial.as_sum cf
              have hterm : ∀ b ∈ cf.support,
                  (MvPolynomial.monomial b (cf.coeff b)) * a ∈ J := by
                intro b hb
                have hbw : Finsupp.weight w b = n := by
                  have hmem2 : cf ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ w n :=
                    hcfhom
                  rw [HilbertMulti.blockPiece_eq] at hmem2
                  rw [MvPolynomial.mem_restrictSupport_iff] at hmem2
                  have hbmem : b ∈ {a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
                      a.mapDomain (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) = n} :=
                    hmem2 (Finset.mem_coe.mpr hb)
                  have hmap : b.mapDomain (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) = n :=
                    hbmem
                  rw [HilbertMulti.weight_blockWeight]
                  exact hmap
                have hdir_sum : (Finsupp.weight w b) 0 = n 0 := by
                  rw [hbw]
                have hdir_eq2 : (Finsupp.weight w b) 0 =
                    ∑ i : Fin e, b (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) := by
                  rw [HilbertMulti.weight_blockWeight, HilbertMulti.mapDomain_fin_apply]
                  simp [Fin.sum_univ_add, HilbertMulti.tripleBlocks]
                have hdir_ge : e * N0 + 1 ≤
                    ∑ i : Fin e, b (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) := by
                  rw [← hdir_eq2, hdir_sum]
                  exact hn0ge
                obtain ⟨i0, hi0⟩ : ∃ i0 : Fin e, N0 ≤
                    b (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i0)) := by
                  by_contra hcon
                  push_neg at hcon
                  have hle : (∑ i : Fin e, b (Fin.castAdd (skewDim e + 1)
                      (Fin.castAdd (e + e) i))) ≤ e * N0 := by
                    calc (∑ i : Fin e, b (Fin.castAdd (skewDim e + 1)
                        (Fin.castAdd (e + e) i)))
                        ≤ ∑ _i : Fin e, N0 := Finset.sum_le_sum (fun i _ => Nat.le_of_lt (hcon i))
                      _ = e * N0 := by simp
                  omega
                have hdiv : Finsupp.single (Fin.castAdd (skewDim e + 1)
                    (Fin.castAdd (e + e) i0)) N0 ≤ b :=
                  Finsupp.single_le_iff.mpr hi0
                have hb_eq : b = (b - Finsupp.single (Fin.castAdd (skewDim e + 1)
                    (Fin.castAdd (e + e) i0)) N0) +
                    Finsupp.single (Fin.castAdd (skewDim e + 1)
                    (Fin.castAdd (e + e) i0)) N0 := by
                  rw [tsub_add_cancel_of_le hdiv]
                have hmon : MvPolynomial.monomial b (cf.coeff b) =
                    MvPolynomial.monomial (b - Finsupp.single (Fin.castAdd (skewDim e + 1)
                      (Fin.castAdd (e + e) i0)) N0) (cf.coeff b) *
                    ((MvPolynomial.X (Fin.castAdd (skewDim e + 1)
                      (Fin.castAdd (e + e) i0)) ^ N0 : Poly (e + (e + e) + (skewDim e + 1)))) := by
                  conv_lhs => rw [hb_eq, MvPolynomial.monomial_add_single]
                  rw [← hb_eq]
                have hmem_single : (MvPolynomial.monomial b (cf.coeff b)) * a ∈ J := by
                  rw [hmon, mul_assoc]
                  apply Ideal.mul_mem_left
                  exact haT i0
                exact hmem_single
              have hsum : cf * a ∈ J := by
                rw [hcf_eq, Finset.sum_mul]
                apply Ideal.sum_mem
                intro b hb
                exact hterm b hb
              exact hsum
            have hpJ : p ∈ J := by
              have heq : p = (p - cf * a) + cf * a := by ring
              rw [heq]
              exact Ideal.add_mem J hremJ hprodJ
            exact hpJ
          · have hpI : p ∈ Ideal.span (s : Set _) := by
              apply HilbertMulti.mem_step_of_not_le
                (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))
                _ hIhom _ _ hd0 hp hle hmem
            exact ih hsG p st tt uu hs hp hpI
    refine ⟨N, ?_⟩
    intro s t u hs
    have hJK : J ≤ K := hFB
    have hsurj := HilbertMulti.sectionFactor_surjective w J K hJK
      (HilbertMulti.tripleDegree s t u)
    have hinj : Function.Injective (HilbertMulti.sectionFactor w J K hJK
      (HilbertMulti.tripleDegree s t u)) := by
      rw [← LinearMap.ker_eq_bot]
      apply le_antisymm _ bot_le
      intro x hx
      rw [LinearMap.mem_ker] at hx
      obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
      have hpK : Ideal.Quotient.mk K p = 0 := by
        have hxv := congrArg Subtype.val hx
        change (Ideal.Quotient.factorₐ ℂ hJK) x.1 = 0 at hxv
        change Ideal.Quotient.mk J p = x.1 at hpx
        rw [← hpx] at hxv
        have hfac : (Ideal.Quotient.factorₐ ℂ hJK)
            (Ideal.Quotient.mk J p) = Ideal.Quotient.mk K p := rfl
        rw [hfac] at hxv
        exact hxv
      have hpKmem : p ∈ K := Ideal.Quotient.eq_zero_iff_mem.mp hpK
      have hpG : p ∈ Ideal.span (G : Set _) := by
        rw [hGspan]
        exact hpKmem
      have hpHom : p.IsWeightedHomogeneous w (HilbertMulti.tripleDegree s t u) := hp
      have hpJ : p ∈ J := key G le_rfl p s t u hs hpHom hpG
      have hx0 : x = 0 := by
        apply Subtype.ext
        change Ideal.Quotient.mk J p = x.1 at hpx
        have hpx0 : Ideal.Quotient.mk J p = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hpJ
        have hx1 : x.1 = 0 := hpx.symm.trans hpx0
        exact hx1
      simp [hx0]
    have hbijective : Function.Bijective (HilbertMulti.sectionFactor w J K hJK
      (HilbertMulti.tripleDegree s t u)) := ⟨hinj, hsurj⟩
    have hfinrank_eq : Module.finrank ℂ (HilbertMulti.sectionSpace w J
        (HilbertMulti.tripleDegree s t u)) =
        Module.finrank ℂ (HilbertMulti.sectionSpace w K
        (HilbertMulti.tripleDegree s t u)) :=
      (LinearEquiv.ofBijective _ hbijective).finrank_eq
    have hfinK : Module.finrank ℂ (HilbertMulti.sectionSpace w K
        (HilbertMulti.tripleDegree s t u)) =
        tripleHilbert (incidenceTriples C Γ H) s t u := by
      rw [hK]
      have hspace : HilbertMulti.sectionSpace w
          (MvPolynomial.vanishingIdeal ℂ
            (tripleRepresentatives (incidenceTriples C Γ H)))
          (HilbertMulti.tripleDegree s t u) =
          tripleSection (incidenceTriples C Γ H) s t u := by
        rw [HilbertMulti.sectionSpace, HilbertMulti.tripleBlockPiece]
        rfl
      rw [hspace]
      rfl
    exact hfinrank_eq.trans hfinK

end TripleRankParts
end DistinctDistances.TrackB
