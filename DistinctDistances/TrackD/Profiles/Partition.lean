import DistinctDistances.TrackD.Profiles.Defs
import DistinctDistances.TrackD.DProfilesAux
import DistinctDistances.TrackD.Profiles.PartitionConstruction

/-!
# `prof:partition` (`profiles.tex:49–218`)
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

/-- `prof:partition.discard` (`profiles.tex:172–195`, eq. `prof:window-discard`): the discarded
fractions are summable over the halving windows uniformly as the smallest width `u → ∞`; no
factor equal to the number of windows is lost. -/
theorem prof_partition_discard (C : ℝ) (hC : 0 ≤ C) :
    ∀ ε > 0, ∃ u₀ : ℝ, ∀ u ≥ u₀,
      Summable (fun m : ℕ => C * (1 + Real.sqrt (Real.log (2 ^ m * u))) *
        Real.exp (-(2 ^ m * u) ^ ((1 : ℝ) / 10) / 2)) ∧
      ∑' m : ℕ, C * (1 + Real.sqrt (Real.log (2 ^ m * u))) *
        Real.exp (-(2 ^ m * u) ^ ((1 : ℝ) / 10) / 2) ≤ ε ∧
      Summable (fun m : ℕ => Real.exp (-(2 ^ m * u) ^ ((1 : ℝ) / 3))) ∧
      ∑' m : ℕ, Real.exp (-(2 ^ m * u) ^ ((1 : ℝ) / 3)) ≤ ε := by
  exact prof_partition_discard_aux C hC

private theorem affineDimension_whole (d : ℕ) : (AffineVariety.whole : AffineVariety d).dimension = d := by
  change OAI.QuarticPowerFree.affineDimension
    ((⊥ : Ideal (Poly d)).radical) = d
  have hrad : Ideal.radical (⊥ : Ideal (Poly d)) = ⊥ :=
    Ideal.radical_bot_of_isReduced
  rw [hrad]
  have htr : Algebra.trdeg ℂ (Poly d ⧸ (⊥ : Ideal (Poly d))) = d := by
    rw [AlgEquiv.trdeg_eq (AlgEquiv.quotientBot ℂ (Poly d))]
    simp
  have hdim := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg
    (⊥ : Ideal (Poly d)) (OAI.QuarticPowerFree.coordinateHilbert (⊥ : Ideal (Poly d)))
    (OAI.QuarticPowerFree.coordinateHilbert_eventually (⊥ : Ideal (Poly d)))
  change (OAI.QuarticPowerFree.affineDimension (⊥ : Ideal (Poly d)) : Cardinal) =
    (Algebra.trdeg ℂ (Poly d ⧸ (⊥ : Ideal (Poly d))) : Cardinal) at hdim
  rw [htr] at hdim
  exact_mod_cast hdim

private theorem CutPath.system_succ {d : ℕ} (π : CutPath d) (j : ℕ) (hj : j < d) :
    π.system (j + 1) = π.system j ⊔ Ideal.span {π.cut ⟨j, hj⟩} := by
  classical
  let p := π.cut ⟨j, hj⟩
  have hset :
      {f | ∃ i : Fin d, i.val < j + 1 ∧ π.cut i = f} =
        {f | ∃ i : Fin d, i.val < j ∧ π.cut i = f} ∪ {p} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hij, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact Or.inl ⟨i, h, rfl⟩
      · right
        have hi : i = ⟨j, hj⟩ := Fin.ext h
        simpa [p, hi]
    · rintro (⟨i, hij, rfl⟩ | rfl)
      · exact ⟨i, Nat.lt_succ_of_lt hij, rfl⟩
      · exact ⟨⟨j, hj⟩, Nat.lt_succ_self j, rfl⟩
  change Ideal.span {f | ∃ i : Fin d, i.val < j + 1 ∧ π.cut i = f} = _
  rw [hset, Ideal.span_union]
  rfl

/-- `prof:partition.pure` (`profiles.tex:66–67`): along a proper path, every local carrier after
`j ≤ d` cuts through a point of the piece has dimension `d - j` (Krull's principal ideal
theorem and properness). -/
theorem prof_partition_pure {d : ℕ} (X : Piece d) (x : Pt d) (hx : x ∈ X.pts)
    (hvan : ∀ i, MvPolynomial.eval (toC x) (X.path.cut i) = 0)
    (hprop : X.path.ProperAt (toC x)) (j : ℕ) (hj : j ≤ d) :
    ∀ Z ∈ X.path.localCarriers j (toC x), Z.IsIrreducible ∧ Z.dimension = d - j := by
  classical
  have hmain : ∀ k, k ≤ d → ∀ Z ∈ X.path.localCarriers k (toC x),
      Z.IsIrreducible ∧ Z.dimension = d - k := by
    intro k
    induction k with
    | zero =>
        intro hk
        intro Z hZ
        have hsys : X.path.system 0 = ⊥ := by simp [CutPath.system]
        have hZmin : Z.ideal ∈ (X.path.system 0).minimalPrimes := hZ.1
        rw [hsys] at hZmin
        have hZeq : Z.ideal = ⊥ := by
          rw [Ideal.minimalPrimes_eq_subsingleton_self] at hZmin
          simpa using hZmin
        refine ⟨?_, ?_⟩
        · change Z.ideal.IsPrime
          rw [hZeq]
          infer_instance
        · change OAI.QuarticPowerFree.affineDimension Z.ideal = d
          rw [hZeq]
          have h := affineDimension_whole d
          change OAI.QuarticPowerFree.affineDimension
            ((⊥ : Ideal (Poly d)).radical) = d at h
          rw [Ideal.radical_bot_of_isReduced] at h
          exact h
    | succ k ih =>
        intro hk
        intro Z hZ
        have hkd : k < d := by omega
        let i : Fin d := ⟨k, hkd⟩
        have hZmin : Z.ideal ∈ (X.path.system (k + 1)).minimalPrimes := hZ.1
        letI : Z.ideal.IsPrime := hZmin.isPrime
        have hprev : X.path.system k ≤ Z.ideal := by
          calc
            X.path.system k ≤ X.path.system k ⊔ Ideal.span {X.path.cut i} := le_sup_left
            _ = X.path.system (k + 1) := (CutPath.system_succ X.path k hkd).symm
            _ ≤ Z.ideal := hZmin.le
        obtain ⟨Q, hQ, hQZ⟩ := Ideal.exists_minimalPrimes_le hprev
        let Y : AffineVariety d := ⟨Q, hQ.isPrime.isRadical⟩
        have hxZ : toC x ∈ Z := hZ.2
        have hxY : toC x ∈ Y := by
          change toC x ∈ MvPolynomial.zeroLocus ℂ Q
          apply MvPolynomial.zeroLocus_anti_mono hQZ
          exact hxZ
        have hYlocal : Y ∈ X.path.localCarriers k (toC x) := by
          constructor
          · change Q ∈ (X.path.system k).minimalPrimes
            exact hQ
          · exact hxY
        have hdimY : Y.dimension = d - k := ih (by omega) Y hYlocal |>.2
        have hproper : X.path.cut i ∉ Q := by
          exact hprop i Y hYlocal
        have hZcut : Z.ideal ∈
            (Q ⊔ Ideal.span {X.path.cut i}).minimalPrimes := by
          change Minimal (fun J : Ideal (Poly d) => J.IsPrime ∧
            Q ⊔ Ideal.span {X.path.cut i} ≤ J) Z.ideal
          refine ⟨⟨hZmin.isPrime, ?_⟩, ?_⟩
          · apply sup_le hQZ
            apply Ideal.span_le.mpr
            intro f hf
            have hfeq : f = X.path.cut i := by
              simpa only [Set.mem_singleton_iff] using hf
            have hcutmem : X.path.cut i ∈ X.path.system (k + 1) := by
              rw [CutPath.system_succ X.path k hkd]
              exact Ideal.mem_sup_right (Ideal.subset_span rfl)
            rw [hfeq]
            exact hZmin.le hcutmem
          · intro J hJ hJZ
            have hsystemJ : X.path.system (k + 1) ≤ J := by
              rw [CutPath.system_succ X.path k hkd]
              exact sup_le (hQ.le.trans (le_sup_left.trans hJ.2)) (Ideal.span_le.mpr (by
                intro f hf
                have hfeq : f = X.path.cut i := by
                  simpa only [Set.mem_singleton_iff] using hf
                rw [hfeq]
                exact hJ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))))
            exact hZmin.2 ⟨hJ.1, hsystemJ⟩ hJZ
        letI : Q.IsPrime := hQ.isPrime
        have hdimcut := OAI.QuarticPowerFree.proper_cut_component_dimension
          Q Z.ideal (X.path.cut i) hproper hZcut (by
            have hdimY' : OAI.QuarticPowerFree.affineDimension Q = (d - (k + 1)) + 1 := by
              change Y.dimension = (d - (k + 1)) + 1
              rw [hdimY]
              omega
            exact hdimY')
        refine ⟨hZmin.isPrime, ?_⟩
        change OAI.QuarticPowerFree.affineDimension Z.ideal = d - (k + 1)
        exact hdimcut
  intro Z hZ
  exact hmain j hj Z hZ

/-- `prof:partition` (`profiles.tex:49–76`), finitary form. For every tolerance `θ`, plateau
margin `ξ`, degree constant `K ≥ 1` and minimal width `s₀` there are `η > 0` and `N₀` such that
every sample with `|P| ≥ N₀`, `M ≤ η A`, and every directional degree ratio `0 ≤ δ ≤ η`
(`E = δ N / A`) admit a partition of all but `θ N` points into a core isolated in degree `L` with
`E L^2 ≤ θ N` and non-core pieces of dyadic widths `s ≥ s₀`, each satisfying `PieceGood` with
`(θ, ξ, K)`: size `N e^{-θ s}`, `d` proper cuts of degree `B e^{(t_i + θ) s}`, recorded times in
`[-1, 1 + θ]` with imbalance `max |t_i| ≥ 1/2 - θ`, and the no-capture property on every
`ξ`-plateau. All quantities are uniform over the pieces. -/
theorem prof_partition (d : ℕ) (hd : 3 ≤ d) :
    ∀ θ > 0, ∀ ξ > 0, ∀ K ≥ 1, ∀ s₀ : ℝ, ∃ η > 0, ∃ N₀ : ℕ,
      ∀ P : Finset (Pt d), N₀ ≤ P.card → cfgM P ≤ η * cfgA P →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ η → ∃ Q : Partition d, Q.Good P δ θ ξ K s₀ := by
  exact partition_construct_all d hd

end

end TrackD
end DistinctDistances
