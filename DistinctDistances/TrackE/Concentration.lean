import DistinctDistances.TrackE.PairFlats
import DistinctDistances.TrackE.ERedBLocalAux
import DistinctDistances.TrackE.LocalAux
import DistinctDistances.TrackE.Stars
import DistinctDistances.TrackE.GlobalRankInputs

/-!
# Global and local concentration, consumed forms (`reduction.tex:346-453, 464-481`)

The statements here are elementary; their proofs apply `conc:theorem` (track B) with the
component Hilbert bounds (`poly:hilbert`, `poly:envelope`, track A). The variety-level
statement `red:global-concentration` is in `TrackE/GlobalConcentration.lean`.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

/-- red:global-rank, i.e. `eq:global-rank-lower` (`reduction.tex:464-481`, from
`red:global-concentration` and `poly:envelope`): for every set `W` of vertices of `P × Q`, the
union of their pair flats has degree-`⌊A⌋` restriction rank at least `c₄ |W| A^{s₀}`,
`s₀ = C(d,2)`. Here `A = |P|^{2/d}`, and both `P` and `Q` (with `|Q| = |P|`) have at most `A`
as their `M`: this supplies the separators and caps of `conc:theorem` (a). -/
theorem global_rank_lower (hd : 3 ≤ d) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ P Q : Finset (RPoint d), 2 ≤ P.card → Q.card = P.card →
      Mcount P ≤ Ascale d P.card → Mcount Q ≤ Ascale d P.card →
      ∀ W ⊆ P ×ˢ Q,
        c₄ * W.card * Ascale d P.card ^ Nat.choose d 2 ≤
          (restrictionRank (⋃ x ∈ W, pairFlat x.1 x.2) (testDegree d P.card) : ℝ) := by
  classical
  let n := Fintype.card (SkewIdx (d + 1))
  let s₀ := Nat.choose d 2
  obtain ⟨C, hC, hconc⟩ := global_concentration hd
  obtain ⟨c, hc, henv⟩ := TrackA.poly_envelope_lower n
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hden : 0 < C * (2 : ℝ) ^ n := by positivity
  let c₄ : ℝ := (c : ℝ) / (C * (2 : ℝ) ^ n)
  refine ⟨c₄, div_pos hcR hden, ?_⟩
  intro P Q hP hQ hMP hMQ W hW
  let A := Ascale d P.card
  let D := testDegree d P.card
  have hA : 1 ≤ A := (global_parameter_scale hd P.card hP).1
  obtain ⟨hD, hAD⟩ := global_rank_degree_scale A hA
  change 1 ≤ D at hD
  change A ≤ 2 * (D : ℝ) at hAD
  obtain ⟨F, hF, hdefined, hlocus, hcover⟩ :=
    Request.pair_flat_envelope_carriers d W D
  have hdim : ∀ V ∈ F, V.IsIrreducible ∧ V.dimension ≤ n := by
    intro V hV
    exact ⟨hF V hV, Bridges.affine_dimension_le V⟩
  have hn : n = s₀ + d := by
    dsimp [n, s₀]
    rw [card_skewIdx]
    simpa [Nat.choose_one_right, Nat.add_comm] using (Nat.choose_succ_succ d 1)
  have hcomponent : ∀ V ∈ F, s₀ ≤ V.dimension →
      ((W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card : ℝ) ≤
        C * (V.degree : ℝ) * A ^ (V.dimension - s₀) := by
    intro V hV hs
    have hvdim := (hdim V hV).2
    have hh : V.dimension - s₀ ≤ d := by omega
    have hsplit : s₀ + (V.dimension - s₀) = V.dimension := Nat.add_sub_of_le hs
    exact hconc P Q hP hQ hMP hMQ W hW (V.dimension - s₀) hh V (hF V hV) hsplit.symm
  have hcount := global_rank_weighted_count W F C A hC hA hF hcover hcomponent
  have hcompare := global_rank_weighted_compare F A hA D hD hAD hdim
  have hrank := global_rank_envelope_hilbert W D F hlocus
  have henvR : (c : ℝ) * (TrackA.affineWeightedDegree F D : ℝ) ≤
      (restrictionRank (⋃ x ∈ W, pairFlat x.1 x.2) D : ℝ) := by
    have h : (c : ℝ) * (TrackA.affineWeightedDegree F D : ℝ) ≤
        (AffineFamily.hilbert F D : ℝ) := by
      exact_mod_cast henv F D hD hdefined
    rwa [hrank] at h
  have htotal : (c : ℝ) * ((W.card : ℝ) * A ^ s₀) ≤
      (C * (2 : ℝ) ^ n) * (restrictionRank (⋃ x ∈ W, pairFlat x.1 x.2) D : ℝ) := by
    calc
      (c : ℝ) * ((W.card : ℝ) * A ^ s₀) ≤
          (c : ℝ) * (C * ∑ V ∈ F, (V.degree : ℝ) * A ^ V.dimension) :=
            mul_le_mul_of_nonneg_left hcount hcR.le
      _ ≤ (c : ℝ) * (C * ((2 : ℝ) ^ n * (TrackA.affineWeightedDegree F D : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hcompare hC.le) hcR.le
      _ = (C * (2 : ℝ) ^ n) * ((c : ℝ) * (TrackA.affineWeightedDegree F D : ℝ)) := by ring
      _ ≤ (C * (2 : ℝ) ^ n) * (restrictionRank (⋃ x ∈ W, pairFlat x.1 x.2) D : ℝ) :=
            mul_le_mul_of_nonneg_left henvR hden.le
  change ((c : ℝ) / (C * (2 : ℝ) ^ n)) * (W.card : ℝ) * A ^ s₀ ≤
    (restrictionRank (⋃ x ∈ W, pairFlat x.1 x.2) D : ℝ)
  calc
    ((c : ℝ) / (C * (2 : ℝ) ^ n)) * (W.card : ℝ) * A ^ s₀ =
        ((c : ℝ) * ((W.card : ℝ) * A ^ s₀)) / (C * (2 : ℝ) ^ n) := by ring
    _ ≤ (restrictionRank (⋃ x ∈ W, pairFlat x.1 x.2) D : ℝ) :=
        (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using htotal)

/-- red:u-gram (`reduction.tex:430-435`): real vectors with equal Gram matrices,
`u_i · u_j = w_i · w_j`, are related by a linear isometry of `ℝ^d`. -/
theorem exists_linearIsometryEquiv_of_inner_eq {ι : Type*} (u w : ι → RPoint d)
    (h : ∀ i j, inner ℝ (u i) (u j) = inner ℝ (w i) (w j)) :
    ∃ T : RPoint d ≃ₗᵢ[ℝ] RPoint d, ∀ i, T (u i) = w i := by
  classical
  let U : (ι →₀ ℝ) →ₗ[ℝ] RPoint d := Finsupp.linearCombination ℝ u
  let W : (ι →₀ ℝ) →ₗ[ℝ] RPoint d := Finsupp.linearCombination ℝ w
  have hcombo (a b : ι →₀ ℝ) :
      inner ℝ (U a) (U b) = inner ℝ (W a) (W b) := by
    change inner ℝ (a.sum fun i c => c • u i) (b.sum fun i c => c • u i) =
      inner ℝ (a.sum fun i c => c • w i) (b.sum fun i c => c • w i)
    simp_rw [Finsupp.sum_inner, Finsupp.inner_sum, inner_smul_left, inner_smul_right, h]
  have hker : LinearMap.ker U = LinearMap.ker W := by
    ext a
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro ha
      have hzero : inner ℝ (W a) (W a) = 0 := by
        rw [← hcombo a a, ha]
        simp
      exact (inner_self_eq_zero (𝕜 := ℝ)).mp hzero
    · intro ha
      have hzero : inner ℝ (U a) (U a) = 0 := by
        rw [hcombo a a, ha]
        simp
      exact (inner_self_eq_zero (𝕜 := ℝ)).mp hzero
  let e : LinearMap.range U ≃ₗ[ℝ] LinearMap.range W :=
    U.quotKerEquivRange.symm.trans
      ((Submodule.quotEquivOfEq (LinearMap.ker U) (LinearMap.ker W) hker).trans
        W.quotKerEquivRange)
  have heApply (a : ι →₀ ℝ) :
      e ⟨U a, LinearMap.mem_range_self U a⟩ =
        ⟨W a, LinearMap.mem_range_self W a⟩ := by
    calc
      e ⟨U a, LinearMap.mem_range_self U a⟩ =
          W.quotKerEquivRange ((LinearMap.ker W).mkQ a) := by simp [e]
      _ = ⟨W a, LinearMap.mem_range_self W a⟩ := by
        apply Subtype.ext
        exact LinearMap.quotKerEquivRange_apply_mk W a
  have heinner : ∀ x y : LinearMap.range U, inner ℝ (e x) (e y) = inner ℝ x y := by
    intro x y
    rcases x with ⟨x, ⟨a, rfl⟩⟩
    rcases y with ⟨y, ⟨b, rfl⟩⟩
    have hA := congrArg Subtype.val (heApply a)
    have hB := congrArg Subtype.val (heApply b)
    simpa [hA, hB] using (hcombo a b).symm
  let eIso := e.isometryOfInner heinner
  let L : (LinearMap.range U) →ₗᵢ[ℝ] RPoint d :=
    (LinearMap.range W).subtypeₗᵢ.comp eIso.toLinearIsometry
  let T : RPoint d →ₗᵢ[ℝ] RPoint d := LinearIsometry.extend L
  have hTsurj : Function.Surjective T :=
    LinearMap.surjective_of_injective (f := T.toLinearMap) T.injective
  have hTmap (i : ι) : T (u i) = w i := by
    let x : LinearMap.range U :=
      ⟨u i, ⟨Finsupp.single i 1, by simp [U]⟩⟩
    have hx : e x = ⟨w i, ⟨Finsupp.single i 1, by simp [W]⟩⟩ := by
      apply Subtype.ext
      have h := congrArg Subtype.val (heApply (Finsupp.single i (1 : ℝ)))
      simpa [x, U, W] using h
    calc
      T (u i) = T (x : RPoint d) := rfl
      _ = L x := LinearIsometry.extend_apply L x
      _ = w i := by
        change (eIso x : RPoint d) = w i
        exact congrArg Subtype.val hx
  refine ⟨LinearIsometryEquiv.ofSurjective T hTsurj, ?_⟩
  intro i
  simpa using hTmap i

open Classical in
/-- red:local-concentration (`reduction.tex:396-453`), in the paper's `Z`-coordinates on
`F_{p,q}`: let the stars `TP` at `p` and `TQ` at `q` be independent at degree `D ≤ A`, and let
`Nb` be neighbours `(p',q')` with `p' ∈ TP`, `q' ∈ TQ`, `|p'-p| = |q'-q|`, `u + w ≠ 0`
(`u = p'-p`, `w = q'-q`), at most `C₀ A^{d-2}` of them matched by any one `T ∈ O(d)` as
`w = T u`. Then every nonzero polynomial of degree at most `D` in `Z` vanishes on at most
`C A^{d-1}` of the neighbour flats `Z(u+w) = u-w`. `C` depends only on `d` and `C₀`. -/
theorem local_concentration (hd : 3 ≤ d) (C₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ), 1 ≤ A → ∀ D : ℕ, (D : ℝ) ≤ A →
      ∀ (p q : RPoint d) (TP TQ : Finset (RPoint d)),
        IndependentStar D p TP → IndependentStar D q TQ →
      ∀ Nb : Finset (RPoint d × RPoint d),
        (∀ y ∈ Nb, y.1 ∈ TP ∧ y.2 ∈ TQ ∧ dist p y.1 = dist q y.2 ∧
          (y.1 - p) + (y.2 - q) ≠ 0) →
        (∀ T : RPoint d ≃ₗᵢ[ℝ] RPoint d,
          ((Nb.filter fun y => y.2 - q = T (y.1 - p)).card : ℝ) ≤ C₀ * A ^ (d - 2)) →
      ∀ g : MvPolynomial (SkewIdx d) ℂ, g ≠ 0 → g.totalDegree ≤ D →
        ((Nb.filter fun y => ∀ z ∈ evalFlat (cplx ((y.1 - p) + (y.2 - q)))
            (cplx ((y.1 - p) - (y.2 - q))), MvPolynomial.eval z g = 0).card : ℝ) ≤
          C * A ^ (d - 1) := by
  classical
  set C₀' : ℝ := max C₀ 2 with hC₀'def
  have hC₀'1 : 1 ≤ C₀' := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨Cc, hCc, hconc⟩ := Request.uniformConcentration d hd C₀' hC₀'1
  refine ⟨Cc, hCc, ?_⟩
  intro A hA D hDA p q TP TQ hTP hTQ Nb hNb hiso g hg0 hgdeg
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA
  have hnorm : ∀ y ∈ Nb, ‖y.1 - p‖ = ‖y.2 - q‖ := by
    intro y hy
    have h := (hNb y hy).2.2.1
    rwa [dist_eq_norm, dist_eq_norm, norm_sub_rev p, norm_sub_rev q] at h
  have hu0 : ∀ y ∈ Nb, y.1 - p ≠ 0 := by
    intro y hy hu
    have hw : y.2 - q = 0 := by
      have := hnorm y hy
      rw [hu, norm_zero] at this
      exact norm_eq_zero.mp this.symm
    exact (hNb y hy).2.2.2 (by rw [hu, hw, add_zero])
  set lam : RPoint d × RPoint d → (Fin d → ℂ) × (Fin d → ℂ) :=
    fun y => (cplx ((y.1 - p) + (y.2 - q)), cplx ((y.1 - p) - (y.2 - q))) with hlamdef
  have hlam_inj : Function.Injective lam := by
    intro y y' h
    have h1 := cplx_injective (congrArg Prod.fst h)
    have h2 := cplx_injective (congrArg Prod.snd h)
    have hu : y.1 - p = y'.1 - p := by
      have e : (2 : ℝ) • (y.1 - p) = (2 : ℝ) • (y'.1 - p) := by
        rw [two_smul, two_smul]
        calc (y.1 - p) + (y.1 - p) = ((y.1 - p) + (y.2 - q)) + ((y.1 - p) - (y.2 - q)) := by abel
          _ = ((y'.1 - p) + (y'.2 - q)) + ((y'.1 - p) - (y'.2 - q)) := by rw [h1, h2]
          _ = (y'.1 - p) + (y'.1 - p) := by abel
      exact smul_right_injective _ two_ne_zero e
    have hw : y.2 - q = y'.2 - q := by
      have e : (2 : ℝ) • (y.2 - q) = (2 : ℝ) • (y'.2 - q) := by
        rw [two_smul, two_smul]
        calc (y.2 - q) + (y.2 - q) = ((y.1 - p) + (y.2 - q)) - ((y.1 - p) - (y.2 - q)) := by abel
          _ = ((y'.1 - p) + (y'.2 - q)) - ((y'.1 - p) - (y'.2 - q)) := by rw [h1, h2]
          _ = (y'.2 - q) + (y'.2 - q) := by abel
      exact smul_right_injective _ two_ne_zero e
    exact Prod.ext (sub_left_injective hu) (sub_left_injective hw)
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · -- degree zero: `g` is a nonzero constant and vanishes on no (nonempty) neighbour flat
    have hg' : g.totalDegree = 0 := by omega
    have hgC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hg'
    have hc : g.coeff 0 ≠ 0 := by
      intro h; apply hg0; rw [hgC, h, map_zero]
    have hempty : (Nb.filter fun y => ∀ z ∈ evalFlat (cplx ((y.1 - p) + (y.2 - q)))
        (cplx ((y.1 - p) - (y.2 - q))), MvPolynomial.eval z g = 0) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro y hy hall
      obtain ⟨z, hz⟩ := evalFlat_nonempty (y.1 - p) (y.2 - q) (hnorm y hy) (hNb y hy).2.2.2
      have := hall z hz
      rw [hgC, MvPolynomial.eval_C] at this
      exact hc this
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  set Λ := Nb.image lam with hΛdef
  set n := Fintype.card (SkewIdx d) with hndef
  set g' := MvPolynomial.rename (Fintype.equivFin (SkewIdx d)) g with hg'def
  have hg'0 : g' ≠ 0 := by
    intro h
    apply hg0
    apply MvPolynomial.rename_injective _ (Fintype.equivFin (SkewIdx d)).injective
    rw [← hg'def, h, map_zero]
  have hg'deg : g'.totalDegree ≤ D := (MvPolynomial.totalDegree_rename_le _ _).trans hgdeg
  obtain ⟨F, hF, hFdeg, hFaff⟩ := Request.hypersurfaceComponents n g' hg'0
  have hch : d.choose 2 = (d - 1).choose 2 + (d - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have h := Nat.choose_succ_succ k 1
    rw [Nat.choose_one_right] at h
    rw [show (k + 1).choose 2 = k + k.choose 2 from h]
    ring
  have hn : n = d.choose 2 := card_skewIdx d
  -- the parameters satisfy `y(v) = 0`, `v ≠ 0`
  have h1 : ∀ l ∈ Λ, l.1 ≠ 0 ∧ ∑ i, l.2 i * l.1 i = 0 := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hl
    refine ⟨?_, ?_⟩
    · show cplx ((y.1 - p) + (y.2 - q)) ≠ 0
      rw [Ne, cplx_eq_zero_iff]
      exact (hNb y hy).2.2.2
    · show ∑ i, cplx ((y.1 - p) - (y.2 - q)) i * cplx ((y.1 - p) + (y.2 - q)) i = 0
      rw [sum_cplx_mul]
      have : inner ℝ ((y.1 - p) - (y.2 - q)) ((y.1 - p) + (y.2 - q)) =
          ‖y.1 - p‖ ^ 2 - ‖y.2 - q‖ ^ 2 := by
        rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
          real_inner_self_eq_norm_sq, real_inner_comm (y.1 - p) (y.2 - q)]
        ring
      rw [this, hnorm y hy]
      simp
  -- distinct parameters are not proportional (`reduction.tex:408-411`)
  have h2 : ∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ c : ℂ, l' = c • l → l' = l := by
    intro l hl l' hl' c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hl'
    have e1 : cplx ((y'.1 - p) + (y'.2 - q)) = c • cplx ((y.1 - p) + (y.2 - q)) :=
      congrArg Prod.fst hc
    have e2 : cplx ((y'.1 - p) - (y'.2 - q)) = c • cplx ((y.1 - p) - (y.2 - q)) :=
      congrArg Prod.snd hc
    have hcoord : ∀ j, (((y'.1 - p) j : ℝ) : ℂ) = c * (((y.1 - p) j : ℝ) : ℂ) := by
      intro j
      have a1 := congrFun e1 j
      have a2 := congrFun e2 j
      simp only [cplx, PiLp.add_apply, PiLp.sub_apply, Pi.smul_apply, smul_eq_mul] at a1 a2 ⊢
      push_cast at a1 a2 ⊢
      linear_combination (a1 + a2) / 2
    obtain ⟨i, hi⟩ : ∃ i, (y.1 - p) i ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hu0 y hy (by ext j; simp [hall j])
    set t : ℝ := (y'.1 - p) i / (y.1 - p) i with htdef
    have hct : c = (t : ℂ) := by
      have := hcoord i
      rw [htdef, Complex.ofReal_div, this, mul_div_assoc, div_self (by exact_mod_cast hi),
        mul_one]
    have hsmul : y'.1 - p = t • (y.1 - p) := by
      ext j
      have := hcoord j
      rw [hct] at this
      have h' : (((y'.1 - p) j : ℝ) : ℂ) = ((t * (y.1 - p) j : ℝ) : ℂ) := by
        rw [this]; push_cast; ring
      rw [PiLp.smul_apply, smul_eq_mul]
      exact_mod_cast h'
    have hy1 : y'.1 = y.1 := IndependentStar.eq_of_smul hTP (hNb y hy).1 (hNb y' hy').1 t hsmul
    have hc1 : c = 1 := by
      have := hcoord i
      rw [hy1] at this
      have hi' : (((y.1 - p) i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hi
      have h3 : (1 - c) * (((y.1 - p) i : ℝ) : ℂ) = 0 := by linear_combination this
      rcases mul_eq_zero.mp h3 with h4 | h4
      · linear_combination -h4
      · exact absurd h4 hi'
    rw [hc, hc1, one_smul]
  -- separators: products of the two star separators (`reduction.tex:413-418`)
  have hevsub : ∀ (x : Fin d ⊕ Fin d → ℂ) (σ : Fin d → MvPolynomial (Fin d ⊕ Fin d) ℂ)
      (s : MvPolynomial (Fin d) ℂ), MvPolynomial.eval x (MvPolynomial.aeval σ s) =
        MvPolynomial.aeval (fun i => MvPolynomial.eval x (σ i)) s := by
    intro x σ s
    induction s using MvPolynomial.induction_on with
    | C a => simp
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | mul_X a i ha => rw [map_mul, map_mul, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_X, ha]
  set σp : Fin d → MvPolynomial (Fin d ⊕ Fin d) ℂ := fun i =>
    MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i))
    with hσpdef
  set σm : Fin d → MvPolynomial (Fin d ⊕ Fin d) ℂ := fun i =>
    MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i))
    with hσmdef
  have hσp : ∀ i, (σp i).IsHomogeneous 1 := fun i =>
    ((MvPolynomial.isHomogeneous_X ℂ _).add (MvPolynomial.isHomogeneous_X ℂ _)).C_mul _
  have hσm : ∀ i, (σm i).IsHomogeneous 1 := fun i =>
    ((MvPolynomial.isHomogeneous_X ℂ _).sub (MvPolynomial.isHomogeneous_X ℂ _)).C_mul _
  have hevp : ∀ y' : RPoint d × RPoint d,
      (fun i => MvPolynomial.eval (Sum.elim (lam y').1 (lam y').2) (σp i)) = cplx (y'.1 - p) := by
    intro y'
    funext i
    simp only [hσpdef, hlamdef, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_add, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr, cplx,
      PiLp.add_apply, PiLp.sub_apply]
    push_cast
    ring
  have hevm : ∀ y' : RPoint d × RPoint d,
      (fun i => MvPolynomial.eval (Sum.elim (lam y').1 (lam y').2) (σm i)) = cplx (y'.2 - q) := by
    intro y'
    funext i
    simp only [hσmdef, hlamdef, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_sub, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr, cplx,
      PiLp.add_apply, PiLp.sub_apply]
    push_cast
    ring
  have h3 : ∀ l ∈ Λ, ∃ (k : ℕ) (f : MvPolynomial (Fin d ⊕ Fin d) ℂ), 1 ≤ k ∧
      (k : ℝ) ≤ C₀' * A ∧ f.IsHomogeneous k ∧ MvPolynomial.eval (Sum.elim l.1 l.2) f ≠ 0 ∧
      ∀ l' ∈ Λ, l' ≠ l → MvPolynomial.eval (Sum.elim l'.1 l'.2) f = 0 := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨s, hs, hs1, hs0⟩ := IndependentStar.exists_separator hTP (hNb y hy).1
    obtain ⟨t, ht, ht1, ht0⟩ := IndependentStar.exists_separator hTQ (hNb y hy).2.1
    have hev : ∀ y' : RPoint d × RPoint d, MvPolynomial.eval (Sum.elim (lam y').1 (lam y').2)
        (MvPolynomial.aeval σp s * MvPolynomial.aeval σm t) =
          MvPolynomial.aeval (cplx (y'.1 - p)) s * MvPolynomial.aeval (cplx (y'.2 - q)) t := by
      intro y'
      rw [MvPolynomial.eval_mul, hevsub, hevsub, hevp, hevm]
    refine ⟨1 * D + 1 * D, MvPolynomial.aeval σp s * MvPolynomial.aeval σm t, by omega, ?_,
      (hs.aeval σp hσp).mul (ht.aeval σm hσm), ?_, ?_⟩
    · have h2C : (2 : ℝ) ≤ C₀' := le_max_right _ _
      push_cast
      nlinarith
    · rw [hev y, hs1, ht1]
      norm_num
    · intro l' hl' hne
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hl'
      rw [hev y']
      by_cases hy1 : y'.1 = y.1
      · have hy2 : y'.2 ≠ y.2 := fun hy2 => hne (by rw [Prod.ext hy1 hy2])
        rw [ht0 _ (hNb y' hy').2.1 hy2, mul_zero]
      · rw [hs0 _ (hNb y' hy').1 hy1, zero_mul]
  -- the isotropic cap (`reduction.tex:420-444`)
  have h4 : ∀ L : Submodule ℂ ((Fin d → ℂ) × (Fin d → ℂ)), Module.finrank ℂ L = d →
      (∀ x ∈ L, ∀ x' ∈ L, ∑ i, (x.2 i * x'.1 i + x'.2 i * x.1 i) = 0) →
      ((Λ.filter (· ∈ L)).card : ℝ) ≤ C₀' * A ^ (d - 2) := by
    intro L _ hLiso
    set Y := Nb.filter fun y => lam y ∈ L with hYdef
    have hgram : ∀ y y' : Y, inner ℝ ((y : RPoint d × RPoint d).1 - p)
        ((y' : RPoint d × RPoint d).1 - p) =
          inner ℝ ((y : RPoint d × RPoint d).2 - q) ((y' : RPoint d × RPoint d).2 - q) := by
      intro y y'
      have hy := (Finset.mem_filter.mp y.2).2
      have hy' := (Finset.mem_filter.mp y'.2).2
      have hiso' := hLiso _ hy _ hy'
      have := (isotropy_sum_eq ((y : RPoint d × RPoint d).1 - p) ((y : RPoint d × RPoint d).2 - q)
        ((y' : RPoint d × RPoint d).1 - p) ((y' : RPoint d × RPoint d).2 - q)).symm.trans hiso'
      have h0 := Complex.ofReal_eq_zero.mp this
      linarith
    obtain ⟨T, hT⟩ := Reduction.exists_linearIsometryEquiv_of_inner_eq
      (fun y : Y => (y : RPoint d × RPoint d).1 - p) (fun y : Y => (y : RPoint d × RPoint d).2 - q)
      hgram
    have hYsub : Y ⊆ Nb.filter fun y => y.2 - q = T (y.1 - p) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, (hT ⟨y, hy⟩).symm⟩
    have hΛY : Λ.filter (· ∈ L) ⊆ Y.image lam := by
      intro l hl
      obtain ⟨hlΛ, hlL⟩ := Finset.mem_filter.mp hl
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hlΛ
      exact Finset.mem_image_of_mem lam (Finset.mem_filter.mpr ⟨hy, hlL⟩)
    calc ((Λ.filter (· ∈ L)).card : ℝ) ≤ (Y.image lam).card := by
          exact_mod_cast Finset.card_le_card hΛY
      _ ≤ Y.card := by exact_mod_cast Finset.card_image_le
      _ ≤ (Nb.filter fun y => y.2 - q = T (y.1 - p)).card := by
          exact_mod_cast Finset.card_le_card hYsub
      _ ≤ C₀ * A ^ (d - 2) := hiso T
      _ ≤ C₀' * A ^ (d - 2) := by gcongr; exact le_max_left _ _
  -- `conc:theorem` (b) on each hypersurface component
  have hcount : ∀ V ∈ F, ((Λ.filter fun l => skewToPoint '' evalFlat l.1 l.2 ⊆ V.points).card : ℝ)
      ≤ Cc * (V.degree : ℝ) * A ^ (d - 2) := by
    intro V hV
    obtain ⟨hVirr, hVdim, hVzero⟩ := hF V hV
    refine hconc A hA Λ h1 h2 h3 h4 V hVirr (d - 2) (by omega) (by omega) ?_
      (Or.inr ⟨g', hg'0, ?_, hVzero⟩)
    · omega
    · calc (g'.totalDegree : ℝ) ≤ D := by exact_mod_cast hg'deg
        _ ≤ A := hDA
        _ ≤ C₀' * A := le_mul_of_one_le_left hA0.le hC₀'1
  -- every vanishing neighbour flat lies in some component
  have hXsub : (Nb.filter fun y => ∀ z ∈ evalFlat (cplx ((y.1 - p) + (y.2 - q)))
      (cplx ((y.1 - p) - (y.2 - q))), MvPolynomial.eval z g = 0) ⊆
        F.biUnion fun V => Nb.filter fun y => skewToPoint '' evalFlat (lam y).1 (lam y).2 ⊆
          V.points := by
    intro y hy
    obtain ⟨hyN, hyz⟩ := Finset.mem_filter.mp hy
    have hne : (skewAffine (lam y).1 (lam y).2 : Set (Point n)).Nonempty := by
      rw [coe_skewAffine]
      exact (evalFlat_nonempty _ _ (hnorm y hyN) (hNb y hyN).2.2.2).image _
    obtain ⟨V, hV, hLV⟩ := hFaff (skewAffine (lam y).1 (lam y).2) hne (by
      intro x hx
      rw [← SetLike.mem_coe, coe_skewAffine] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [hg'def, eval_rename_skewToPoint]
      exact hyz z hz)
    rw [coe_skewAffine] at hLV
    exact Finset.mem_biUnion.mpr ⟨V, hV, Finset.mem_filter.mpr ⟨hyN, hLV⟩⟩
  have hsumdeg : (∑ V ∈ F, (V.degree : ℝ)) ≤ A :=
    hFdeg.trans ((by exact_mod_cast hg'deg : (g'.totalDegree : ℝ) ≤ D).trans hDA)
  calc ((Nb.filter fun y => ∀ z ∈ evalFlat (cplx ((y.1 - p) + (y.2 - q)))
        (cplx ((y.1 - p) - (y.2 - q))), MvPolynomial.eval z g = 0).card : ℝ)
      ≤ ((F.biUnion fun V => Nb.filter fun y =>
          skewToPoint '' evalFlat (lam y).1 (lam y).2 ⊆ V.points).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hXsub
    _ ≤ ∑ V ∈ F, ((Nb.filter fun y =>
          skewToPoint '' evalFlat (lam y).1 (lam y).2 ⊆ V.points).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ V ∈ F, Cc * (V.degree : ℝ) * A ^ (d - 2) := by
        apply Finset.sum_le_sum
        intro V hV
        refine le_trans ?_ (hcount V hV)
        have hmaps : Set.MapsTo lam
            (Nb.filter fun y => skewToPoint '' evalFlat (lam y).1 (lam y).2 ⊆ V.points)
            (Λ.filter fun l => skewToPoint '' evalFlat l.1 l.2 ⊆ V.points) := by
          intro y hy
          obtain ⟨hyN, hyV⟩ := Finset.mem_filter.mp hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem lam hyN, hyV⟩
        exact_mod_cast Finset.card_le_card_of_injOn lam hmaps hlam_inj.injOn
    _ = Cc * A ^ (d - 2) * ∑ V ∈ F, (V.degree : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro V _
        ring
    _ ≤ Cc * A ^ (d - 2) * A := by gcongr
    _ = Cc * A ^ (d - 1) := by
        rw [mul_assoc, ← pow_succ]
        congr 2
        omega

open Classical in
/-- red:local-concentration, ambient form consumed by `red:main-contradiction`
(`reduction.tex:504-511`): a polynomial of degree at most `D` on skew forms of `ℂ^{d+1}` that
is not identically zero on `F_{p,q}` vanishes on `F_{p,q} ∩ F_{p',q'}` for at most `C A^{d-1}`
neighbours. From `local_concentration` and `mem_pairFlat_inter_iff`. -/
theorem local_concentration_ambient (hd : 3 ≤ d) (C₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ), 1 ≤ A → ∀ D : ℕ, (D : ℝ) ≤ A →
      ∀ (p q : RPoint d) (TP TQ : Finset (RPoint d)),
        IndependentStar D p TP → IndependentStar D q TQ →
      ∀ Nb : Finset (RPoint d × RPoint d),
        (∀ y ∈ Nb, y.1 ∈ TP ∧ y.2 ∈ TQ ∧ dist p y.1 = dist q y.2 ∧
          (y.1 - p) + (y.2 - q) ≠ 0) →
        (∀ T : RPoint d ≃ₗᵢ[ℝ] RPoint d,
          ((Nb.filter fun y => y.2 - q = T (y.1 - p)).card : ℝ) ≤ C₀ * A ^ (d - 2)) →
      ∀ f : MvPolynomial (SkewIdx (d + 1)) ℂ, f.totalDegree ≤ D →
        (∃ z ∈ pairFlat p q, MvPolynomial.eval z f ≠ 0) →
        ((Nb.filter fun y => ∀ z ∈ pairFlat p q ∩ pairFlat y.1 y.2,
            MvPolynomial.eval z f = 0).card : ℝ) ≤ C * A ^ (d - 1) := by
  obtain ⟨C, hC, hlocal⟩ := local_concentration hd C₀
  refine ⟨C, hC, ?_⟩
  intro A hA D hDA p q TP TQ hTP hTQ Nb hNb hIso f hf hfnz
  let g : MvPolynomial (SkewIdx d) ℂ := MvPolynomial.bind₁ (ambientVarLift p q) f
  have hgdegree : g.totalDegree ≤ D := by
    exact (totalDegree_bind₁_le_of_vars_le_one (ambientVarLift p q)
      (ambientVarLift_degree p q) f).trans hf
  have hgfnz : g ≠ 0 := by
    intro hgzero
    obtain ⟨z, hz, hzfnz⟩ := hfnz
    have hEval : MvPolynomial.eval (zBlock z) g = MvPolynomial.eval z f := by
      calc
        MvPolynomial.eval (zBlock z) g =
            MvPolynomial.eval (ambientSection p q (zBlock z)) f := by
              simpa [g] using ambientSection_eq_fun_eval p q (zBlock z) f
        _ = MvPolynomial.eval z f := by
              rw [ambientSection_eq_of_mem_pairFlat p q z hz]
    rw [hgzero] at hEval
    exact hzfnz hEval.symm
  have hlocalCount := hlocal A hA D hDA p q TP TQ hTP hTQ Nb hNb hIso g hgfnz hgdegree
  let ambientBad := Nb.filter fun y => ∀ z ∈ pairFlat p q ∩ pairFlat y.1 y.2,
    MvPolynomial.eval z f = 0
  let coordinateBad := Nb.filter fun y => ∀ Z ∈ evalFlat
      (cplx ((y.1 - p) + (y.2 - q))) (cplx ((y.1 - p) - (y.2 - q))),
        MvPolynomial.eval Z g = 0
  have hbadSub : ambientBad ⊆ coordinateBad := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyNb, hyvanish⟩
    apply Finset.mem_filter.mpr
    refine ⟨hyNb, ?_⟩
    intro Z hZ
    have hbase : ambientSection p q Z ∈ pairFlat p q :=
      ambientSection_mem_pairFlat p q Z
    have hother : ambientSection p q Z ∈ pairFlat y.1 y.2 := by
      apply (mem_pairFlat_inter_iff p q y.1 y.2 (ambientSection p q Z) hbase).2
      simpa only [zBlock_ambientSection] using hZ
    have hvanish := hyvanish (ambientSection p q Z) ⟨hbase, hother⟩
    calc
      MvPolynomial.eval Z g = MvPolynomial.eval (ambientSection p q Z) f := by
        simpa [g] using ambientSection_eq_fun_eval p q Z f
      _ = 0 := hvanish
  have hcard : (ambientBad.card : ℝ) ≤ coordinateBad.card := by
    exact_mod_cast Finset.card_le_card hbadSub
  exact hcard.trans hlocalCount

end Reduction

end

end DistinctDistances
