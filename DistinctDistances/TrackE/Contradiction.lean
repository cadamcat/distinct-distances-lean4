import DistinctDistances.TrackE.Basic
import DistinctDistances.TrackE.ERedBAux

/-!
# One random sample completes the proof (`reduction.tex:455-512`)

Abstract finite forms: a family of sets `flat v` (the pair flats) indexed by retained vertices,
an adjacency, the global rank lower bound, the local cap, and the sample.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

/-- Restriction rank is monotone under inclusion. -/
theorem restrictionRank_mono {σ : Type*} [Fintype σ] {T T' : Set (σ → ℂ)} (h : T ⊆ T') (D : ℕ) :
    restrictionRank T D ≤ restrictionRank T' D := by
  classical
  let r : (T' → ℂ) →ₗ[ℂ] (T → ℂ) :=
    { toFun := fun f x => f ⟨x.1, h x.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hcomp : restrictionMap T D = r.comp (restrictionMap T' D) := by
    ext f x
    rfl
  change Module.finrank ℂ (LinearMap.range (restrictionMap T D)) ≤ _
  rw [hcomp, LinearMap.range_comp]
  exact Submodule.finrank_map_le r (LinearMap.range (restrictionMap T' D))

/-- Restriction rank is subadditive over finite unions (`reduction.tex:486-488`). -/
theorem restrictionRank_biUnion_le {σ ι : Type*} [Fintype σ] (s : Finset ι)
    (T : ι → Set (σ → ℂ)) (D : ℕ) :
    restrictionRank (⋃ i ∈ s, T i) D ≤ ∑ i ∈ s, restrictionRank (T i) D := by
  classical
  let U : Set (σ → ℂ) := ⋃ i ∈ s, T i
  let E : (LinearMap.range (restrictionMap U D)) →ₗ[ℂ]
      (∀ i : {i // i ∈ s}, LinearMap.range (restrictionMap (T i) D)) :=
    { toFun := fun u i =>
        ⟨fun x => u.1 ⟨x.1, Set.mem_iUnion.mpr ⟨i.1,
          Set.mem_iUnion.mpr ⟨i.2, x.2⟩⟩⟩,
          by
            rcases u.2 with ⟨f, hf⟩
            refine ⟨f, ?_⟩
            funext x
            change restrictionMap U D f ⟨x.1,
              Set.mem_iUnion.mpr ⟨i.1, Set.mem_iUnion.mpr ⟨i.2, x.2⟩⟩⟩ = _
            rw [hf]⟩
      map_add' := by
        intro u v
        ext i x
        rfl
      map_smul' := by
        intro c u
        ext i x
        rfl }
  have hE : Function.Injective E := by
    intro u v huv
    apply Subtype.ext
    funext z
    rcases Set.mem_iUnion.mp z.2 with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨his, hz⟩
    have hv := congrArg (fun g => (g ⟨i, his⟩ : T i → ℂ) ⟨z.1, hz⟩) huv
    exact hv
  calc
    restrictionRank U D ≤
      Module.finrank ℂ (∀ i : {i // i ∈ s}, LinearMap.range (restrictionMap (T i) D)) :=
      LinearMap.finrank_le_finrank_of_injective hE
    _ = ∑ i ∈ s, restrictionRank (T i) D := by
      rw [Module.finrank_pi_fintype]
      calc
        _ = ∑ i ∈ (Finset.univ : Finset {i // i ∈ s}),
            Module.finrank ℂ (LinearMap.range (restrictionMap (T i) D)) := rfl
        _ = ∑ i ∈ s.attach,
            Module.finrank ℂ (LinearMap.range (restrictionMap (T i) D)) := by
          rw [Finset.univ_eq_attach]
        _ = ∑ i ∈ s, Module.finrank ℂ (LinearMap.range (restrictionMap (T i) D)) :=
          Finset.sum_attach s (fun i : ι => Module.finrank ℂ (LinearMap.range (restrictionMap (T i) D)))
        _ = _ := rfl

/-- If `T ⊆ T'` and the restriction rank of `T` is smaller, some polynomial of degree at most
`D` vanishes on `T` but not on `T'` (`reduction.tex:504-506`). -/
theorem exists_poly_of_restrictionRank_lt {σ : Type*} [Fintype σ] {T T' : Set (σ → ℂ)} (D : ℕ)
    (h : restrictionRank T D < restrictionRank T' D) :
    ∃ f : MvPolynomial σ ℂ, f.totalDegree ≤ D ∧ (∀ z ∈ T, MvPolynomial.eval z f = 0) ∧
      ∃ z ∈ T', MvPolynomial.eval z f ≠ 0 := by
  classical
  let fT := restrictionMap T D
  let fT' := restrictionMap T' D
  have hdim : Module.finrank ℂ (LinearMap.ker fT') < Module.finrank ℂ (LinearMap.ker fT) := by
    have h1 := fT'.finrank_range_add_finrank_ker
    have h2 := fT.finrank_range_add_finrank_ker
    change Module.finrank ℂ (LinearMap.range fT) < Module.finrank ℂ (LinearMap.range fT') at h
    omega
  have hnot : ¬ LinearMap.ker fT ≤ LinearMap.ker fT' := by
    intro hk
    have hkdim := Submodule.finrank_mono hk
    omega
  have hexker : ∃ f, f ∈ LinearMap.ker fT ∧ f ∉ LinearMap.ker fT' := by
    by_contra hn
    apply hnot
    intro f hfT
    by_contra hfT'
    exact hn ⟨f, hfT, hfT'⟩
  obtain ⟨f, hfT, hfT'⟩ := hexker
  have hT : ∀ z : T, MvPolynomial.eval z (f : MvPolynomial σ ℂ) = 0 := by
    intro z
    have hz := LinearMap.mem_ker.mp hfT
    have heq := congrFun hz z
    simpa [fT, restrictionMap, MvPolynomial.aeval_def] using heq
  have hnotzero : fT' f ≠ 0 := by
    intro hz
    exact hfT' (LinearMap.mem_ker.mpr hz)
  have hex : ∃ z : T', MvPolynomial.eval z (f : MvPolynomial σ ℂ) ≠ 0 := by
    by_contra hn
    apply hnotzero
    ext z
    have hz : MvPolynomial.eval z (f : MvPolynomial σ ℂ) = 0 := by
      by_contra hne
      exact hn ⟨z, hne⟩
    simpa [fT', restrictionMap, MvPolynomial.aeval_def] using hz
  refine ⟨(f : MvPolynomial σ ℂ), ?_, ?_, ?_⟩
  · exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mp f.2
  · intro z hz
    exact hT ⟨z, hz⟩
  · rcases hex with ⟨z, hz⟩
    exact ⟨z, z.2, hz⟩

open Classical in
/-- red:u-sample (`reduction.tex:483-502`), abstract form: if every vertex of `W` has at least
`δ` neighbours in `W` and `|W| exp(-θ²δ/2) < 1/2`, some `T ⊆ W` has `|T| ≤ 2θ|W|` and gives
every vertex at least `θδ/2` neighbours in `T` (independent sampling with probability `θ`,
Markov and Hoeffding, or a counting argument). -/
theorem exists_sample {V : Type*} (W : Finset V) (adj : V → V → Prop) (δ θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (hdeg : ∀ v ∈ W, δ ≤ ((W.filter fun w => adj v w).card : ℝ))
    (hunion : (W.card : ℝ) * Real.exp (-(θ ^ 2 * δ / 2)) < 1 / 2) :
    ∃ T ⊆ W, (T.card : ℝ) ≤ 2 * θ * W.card ∧
      ∀ v ∈ W, θ * δ / 2 ≤ ((T.filter fun w => adj v w).card : ℝ) := by
  exact exists_sample_finiteBernoulli W adj δ θ hθ0 hθ1 hdeg hunion

open Classical in
/-- red:main-contradiction (`reduction.tex:457-512`), abstract finite form. Let the union of
`flat v` (`v ∈ W`) have rank at least `c₄ |W| A^{s₀}` and each `flat v` rank at most
`C₁ A^{s₀}`; let every vertex have at least `δ` neighbours; and let any polynomial of degree at
most `D` that is not identically zero on `flat v` vanish on `flat v ∩ flat w` for at most `K`
neighbours `w`. A sampling probability `θ` with `2θC₁ < c₄`, `K < θδ/2` and
`|W| exp(-θ²δ/2) < 1/2` gives a contradiction. -/
theorem main_contradiction {σ V : Type*} [Fintype σ] (flat : V → Set (σ → ℂ)) (W : Finset V)
    (hW : W.Nonempty) (adj : V → V → Prop) (D s₀ : ℕ) (A c₄ C₁ K δ θ : ℝ) (hA : 0 < A)
    (hglobal : c₄ * W.card * A ^ s₀ ≤ (restrictionRank (⋃ v ∈ W, flat v) D : ℝ))
    (hflat : ∀ v ∈ W, (restrictionRank (flat v) D : ℝ) ≤ C₁ * A ^ s₀)
    (hdeg : ∀ v ∈ W, δ ≤ ((W.filter fun w => adj v w).card : ℝ))
    (hlocal : ∀ v ∈ W, ∀ f : MvPolynomial σ ℂ, f.totalDegree ≤ D →
      (∃ z ∈ flat v, MvPolynomial.eval z f ≠ 0) →
      ((W.filter fun w => adj v w ∧ ∀ z ∈ flat v ∩ flat w, MvPolynomial.eval z f = 0).card : ℝ)
        ≤ K)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hrank : 2 * θ * C₁ < c₄) (hcap : K < θ * δ / 2)
    (hunion : (W.card : ℝ) * Real.exp (-(θ ^ 2 * δ / 2)) < 1 / 2) : False := by
  classical
  obtain ⟨T, hTW, hTcard, hTdeg⟩ := exists_sample W adj δ θ hθ0 hθ1 hdeg hunion
  let U : Set (σ → ℂ) := ⋃ v ∈ T, flat v
  let U' : Set (σ → ℂ) := ⋃ v ∈ W, flat v
  have hWcard : 0 < (W.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hW
  have hpow : 0 < A ^ s₀ := pow_pos hA _
  have hC₁ : 0 ≤ C₁ := by
    obtain ⟨v, hv⟩ := hW
    have hrank_nonneg : 0 ≤ (restrictionRank (flat v) D : ℝ) := Nat.cast_nonneg _
    by_contra hC₁
    have hC₁neg : C₁ < 0 := lt_of_not_ge hC₁
    have hprod : C₁ * A ^ s₀ < 0 := mul_neg_of_neg_of_pos hC₁neg hpow
    linarith [hflat v hv]
  have hUnionRankNat : restrictionRank U D ≤
      ∑ v ∈ T, restrictionRank (flat v) D := by
    simpa [U] using restrictionRank_biUnion_le T flat D
  have hUnionRank : (restrictionRank U D : ℝ) ≤
      ∑ v ∈ T, (restrictionRank (flat v) D : ℝ) := by
    exact_mod_cast hUnionRankNat
  have hsum : (∑ v ∈ T, (restrictionRank (flat v) D : ℝ)) ≤
      (T.card : ℝ) * (C₁ * A ^ s₀) := by
    calc
      _ ≤ ∑ v ∈ T, C₁ * A ^ s₀ :=
        Finset.sum_le_sum fun v hv => hflat v (hTW hv)
      _ = (T.card : ℝ) * (C₁ * A ^ s₀) := by simp
  have hsampleProduct : (T.card : ℝ) * (C₁ * A ^ s₀) ≤
      (2 * θ * (W.card : ℝ)) * (C₁ * A ^ s₀) :=
    mul_le_mul_of_nonneg_right hTcard (mul_nonneg hC₁ (le_of_lt hpow))
  have hstrict : (2 * θ * (W.card : ℝ)) * (C₁ * A ^ s₀) <
      c₄ * (W.card : ℝ) * A ^ s₀ := by
    have hmul := mul_lt_mul_of_pos_right hrank (mul_pos hWcard hpow)
    nlinarith [hmul]
  have hrealRankLT : (restrictionRank U D : ℝ) < (restrictionRank U' D : ℝ) := by
    calc
      (restrictionRank U D : ℝ) ≤
          ∑ v ∈ T, (restrictionRank (flat v) D : ℝ) := hUnionRank
      _ ≤ (T.card : ℝ) * (C₁ * A ^ s₀) := hsum
      _ ≤ (2 * θ * (W.card : ℝ)) * (C₁ * A ^ s₀) := hsampleProduct
      _ < c₄ * (W.card : ℝ) * A ^ s₀ := hstrict
      _ ≤ (restrictionRank U' D : ℝ) := by simpa [U'] using hglobal
  have hrankLT : restrictionRank U D < restrictionRank U' D := by
    exact_mod_cast hrealRankLT
  obtain ⟨f, hfdeg, hfU, hfnot⟩ := exists_poly_of_restrictionRank_lt D hrankLT
  obtain ⟨z, hzU, hzne⟩ := hfnot
  rcases Set.mem_iUnion.mp hzU with ⟨v, hvU⟩
  rcases Set.mem_iUnion.mp hvU with ⟨hvW, hzflat⟩
  let S := W.filter fun w =>
    adj v w ∧ ∀ z ∈ flat v ∩ flat w, MvPolynomial.eval z f = 0
  have hsampleIntoLocal : T.filter (fun w => adj v w) ⊆ S := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwT, hadj⟩
    apply Finset.mem_filter.mpr
    refine ⟨hTW hwT, hadj, ?_⟩
    intro x hx
    apply hfU x
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hwT, hx.2⟩⟩
  have hcount : ((T.filter fun w => adj v w).card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsampleIntoLocal
  have hlocalBound : (S.card : ℝ) ≤ K := by
    simpa [S] using hlocal v hvW f hfdeg ⟨z, hzflat, hzne⟩
  have hdegreeContradiction : θ * δ / 2 ≤ K :=
    le_trans (hTdeg v hvW) (le_trans hcount hlocalBound)
  linarith

end Reduction

end

end DistinctDistances
