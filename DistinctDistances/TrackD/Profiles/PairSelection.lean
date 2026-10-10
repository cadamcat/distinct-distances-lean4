import DistinctDistances.TrackD.Profiles.Regularity
import DistinctDistances.TrackD.Profiles.PairSelectionFinite

/-!
# `prof:pair-selection` (`profiles.tex:513–619`)

Finitary form: for a fixed precision `ρ` (profile closeness, width separation, coverage loss,
light-line exponent) the thresholds are chosen first; the paper's diagonal choice "let `h → ∞`
slowly" is then the consumer's passage `ρ → 0` along its contradiction sequence. Consumers:
`sparse-cones.tex:21–28, 340–424, 564–651`, `depth.tex:4–16`.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

variable {d : ℕ}

/-- `prof:pair-selection.lightlines` (`profiles.tex:607–615`), abstract: ordered pairs of distinct
points on lines with more than `H ≥ 2` points number at most `C (n^2/H + n h_max)`, `h_max` the
largest line occupancy. -/
private theorem pairLine_real {m : ℕ} (p q : Pt m) (hpq : p ≠ q) :
    IsRealLine (affineSpan ℝ {p, q}) := by
  dsimp [IsRealLine]
  rw [direction_affineSpan, vectorSpan_pair]
  apply finrank_span_singleton
  intro h
  exact hpq (vsub_eq_zero_iff_eq.mp h)

set_option maxHeartbeats 500000 in
theorem pair_selection_lightlines (m : ℕ) (hST : STRichLines m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset (Pt m)) (H hmax : ℝ), 2 ≤ H → 0 ≤ hmax →
      (∀ ℓ : AffineSubspace ℝ (Pt m), IsRealLine ℓ → (occ Q ℓ : ℝ) ≤ hmax) →
        (((Q ×ˢ Q).filter (fun pq => pq.1 ≠ pq.2 ∧
            H < (occ Q (affineSpan ℝ {pq.1, pq.2}) : ℝ))).card : ℝ) ≤
          C * ((Q.card : ℝ) ^ 2 / H + Q.card * hmax) := by
  obtain ⟨C, hC, hcore⟩ := flatslice_core m hST
  refine ⟨C, hC, ?_⟩
  intro Q H hmax hH hhmax hocc
  let line (pq : Pt m × Pt m) : AffineSubspace ℝ (Pt m) := affineSpan ℝ {pq.1, pq.2}
  let R : Finset (Pt m × Pt m) := (Q ×ˢ Q).filter (fun pq =>
    pq.1 ≠ pq.2 ∧ H < (occ Q (line pq) : ℝ))
  let L : Finset (AffineSubspace ℝ (Pt m)) := R.image line
  let fiber (ℓ : AffineSubspace ℝ (Pt m)) : Finset (Pt m × Pt m) :=
    R.filter (fun pq => line pq = ℓ)
  have hreal : ∀ ℓ ∈ L, IsRealLine ℓ := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨pq, hpq, hline⟩
    subst ℓ
    have hpair := (Finset.mem_filter.mp hpq).2
    exact pairLine_real pq.1 pq.2 hpair.1
  have hrich : ∀ ℓ ∈ L, H < (occ Q ℓ : ℝ) := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨pq, hpq, hline⟩
    subst ℓ
    exact (Finset.mem_filter.mp hpq).2.2
  have hlineData : ∀ ℓ ∈ L, IsRealLine ℓ ∧ (occ Q ℓ : ℝ) ≤ hmax := by
    intro ℓ hℓ
    exact ⟨hreal ℓ hℓ, hocc ℓ (hreal ℓ hℓ)⟩
  have hweighted := hcore Q (fun _ => (1 : ℝ)) 1 H hmax L
    (by intro q hq; simp) hH hhmax hlineData
  have hfilter : L.filter (fun ℓ => H ≤ (occ Q ℓ : ℝ)) = L := by
    ext ℓ
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact h.1
    · intro hℓ
      exact ⟨hℓ, (hrich ℓ hℓ).le⟩
  have hlinesum :
      (∑ ℓ ∈ L, (occ Q ℓ : ℝ) ^ 2) ≤
        C * ((Q.card : ℝ) ^ 2 / H + Q.card * hmax) := by
    rw [hfilter] at hweighted
    simpa [occ] using hweighted
  have hsumfiber : (∑ ℓ ∈ L, ((fiber ℓ).card : ℝ)) = (R.card : ℝ) := by
    have hfilterSum :
        (∑ pq ∈ R with line pq ∈ L, (1 : ℝ)) = (R.card : ℝ) := by
      calc
        (∑ pq ∈ R with line pq ∈ L, (1 : ℝ)) = ∑ pq ∈ R, (1 : ℝ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro pq hpq
          have hpqL : line pq ∈ L := Finset.mem_image.mpr ⟨pq, hpq, rfl⟩
          simp [hpqL]
        _ = (R.card : ℝ) := by simp
    calc
      (∑ ℓ ∈ L, ((fiber ℓ).card : ℝ)) =
          ∑ ℓ ∈ L, ∑ pq ∈ fiber ℓ, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            simp [fiber]
      _ = ∑ pq ∈ R with line pq ∈ L, (1 : ℝ) :=
            Finset.sum_fiberwise_eq_sum_filter R L line (fun _ => (1 : ℝ))
      _ = (R.card : ℝ) := hfilterSum
  have hfiber_sub (ℓ : AffineSubspace ℝ (Pt m)) :
      fiber ℓ ⊆ (Q.filter (· ∈ ℓ)) ×ˢ (Q.filter (· ∈ ℓ)) := by
    intro pq hpq
    rcases Finset.mem_filter.mp hpq with ⟨hpqR, hline⟩
    rcases Finset.mem_filter.mp hpqR with ⟨hpqProd, _⟩
    rcases Finset.mem_product.mp hpqProd with ⟨hp, hq⟩
    have hpℓ : pq.1 ∈ ℓ := by
      rw [← hline]
      exact by simpa [line] using (left_mem_affineSpan_pair ℝ pq.1 pq.2)
    have hqℓ : pq.2 ∈ ℓ := by
      rw [← hline]
      exact by simpa [line] using (right_mem_affineSpan_pair ℝ pq.1 pq.2)
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp, hpℓ⟩,
      Finset.mem_filter.mpr ⟨hq, hqℓ⟩⟩
  have hcardfiber (ℓ : AffineSubspace ℝ (Pt m)) :
      ((fiber ℓ).card : ℝ) ≤ (occ Q ℓ : ℝ) ^ 2 := by
    have hn := Finset.card_le_card (hfiber_sub ℓ)
    have hn' : (fiber ℓ).card ≤ (occ Q ℓ) ^ 2 := by
      have hnprod : (fiber ℓ).card ≤ (Q.filter (· ∈ ℓ)).card * (Q.filter (· ∈ ℓ)).card := by
        simpa using hn
      calc
        (fiber ℓ).card ≤ (Q.filter (· ∈ ℓ)).card * (Q.filter (· ∈ ℓ)).card := hnprod
        _ = (occ Q ℓ) ^ 2 := by simp [occ, pow_two]
    exact_mod_cast hn'
  have hpair_count :
      (R.card : ℝ) ≤ ∑ ℓ ∈ L, (occ Q ℓ : ℝ) ^ 2 := by
    rw [← hsumfiber]
    exact Finset.sum_le_sum (fun ℓ hℓ => hcardfiber ℓ)
  have hresult := hpair_count.trans hlinesum
  simpa [R, line] using hresult

/-- `prof:pair-selection.bins` (`profiles.tex:570–590`), abstract selection. Disjoint weighted
blocks labelled by at most `K` bins, and a set of bad ordered pairs of total size at most
`η (Σ n)^2`: some two blocks in a common bin (possibly equal) have at most `η K n_X n_Y` bad pairs
between them. -/
theorem pair_selection_bins {α β : Type*} (blocks : Finset (Finset α)) (bin : Finset α → β)
    (K : ℕ) (hK : 0 < K) (hbins : (blocks.image bin).card ≤ K)
    (hdisj : (blocks : Set (Finset α)).PairwiseDisjoint id)
    (hne : ∃ X ∈ blocks, X.Nonempty)
    (bad : Finset (α × α)) (η : ℝ)
    (hbad : (bad.card : ℝ) ≤ η * ((blocks.biUnion id).card : ℝ) ^ 2) :
    ∃ X ∈ blocks, ∃ Y ∈ blocks, bin X = bin Y ∧ X.Nonempty ∧ Y.Nonempty ∧
      (((X ×ˢ Y).filter (· ∈ bad)).card : ℝ) ≤ η * K * X.card * Y.card := by
  classical
  let U : Finset α := blocks.biUnion id
  let labels : Finset β := blocks.image bin
  let samePairs : Finset (Finset α × Finset α) :=
    (blocks ×ˢ blocks).filter (fun p => bin p.1 = bin p.2)
  let mass (b : β) : ℝ :=
    ∑ X ∈ blocks.filter (fun X => bin X = b), (X.card : ℝ)
  let weight (p : Finset α × Finset α) : ℝ :=
    (p.1.card : ℝ) * (p.2.card : ℝ)
  let badPart (p : Finset α × Finset α) : Finset (α × α) :=
    (p.1 ×ˢ p.2).filter (· ∈ bad)
  have hUcard : U.card = ∑ X ∈ blocks, X.card := by
    dsimp [U]
    exact Finset.card_biUnion hdisj
  have hmassSum : (∑ b ∈ labels, mass b) = (U.card : ℝ) := by
    dsimp [labels, mass]
    calc
      (∑ b ∈ blocks.image bin, ∑ X ∈ blocks.filter (fun X => bin X = b), (X.card : ℝ)) =
          ∑ X ∈ blocks with bin X ∈ blocks.image bin, (X.card : ℝ) :=
        Finset.sum_fiberwise_eq_sum_filter blocks (blocks.image bin) bin
          (fun X => (X.card : ℝ))
      _ = ∑ X ∈ blocks, (X.card : ℝ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro X hX
        have hlabel : bin X ∈ blocks.image bin := Finset.mem_image.mpr ⟨X, hX, rfl⟩
        simp [hlabel]
      _ = (U.card : ℝ) := by exact_mod_cast hUcard.symm
  have hmassSq : (∑ b ∈ labels, mass b ^ 2) =
      ∑ p ∈ samePairs, weight p := by
    calc
      (∑ b ∈ labels, mass b ^ 2) =
          ∑ b ∈ labels, ∑ X ∈ blocks.filter (fun X => bin X = b),
            (X.card : ℝ) * mass b := by
        apply Finset.sum_congr rfl
        intro b hb
        have hsq : mass b ^ 2 =
            ∑ X ∈ blocks.filter (fun X => bin X = b), (X.card : ℝ) * mass b := by
          calc
            mass b ^ 2 = mass b * mass b := by ring
            _ = (∑ X ∈ blocks.filter (fun X => bin X = b), (X.card : ℝ)) * mass b := rfl
            _ = _ := Finset.sum_mul _ _ _
        exact hsq
      _ = ∑ X ∈ blocks, (X.card : ℝ) * mass (bin X) := by
        have hfib := Finset.sum_fiberwise_eq_sum_filter blocks labels bin
          (fun X => (X.card : ℝ) * mass (bin X))
        calc
          (∑ b ∈ labels, ∑ X ∈ blocks.filter (fun X => bin X = b),
              (X.card : ℝ) * mass b) =
              ∑ b ∈ labels, ∑ X ∈ blocks.filter (fun X => bin X = b),
                (X.card : ℝ) * mass (bin X) := by
            apply Finset.sum_congr rfl
            intro b hb
            apply Finset.sum_congr rfl
            intro X hX
            rw [(Finset.mem_filter.mp hX).2]
          _ = ∑ X ∈ blocks with bin X ∈ labels, (X.card : ℝ) * mass (bin X) := hfib
          _ = ∑ X ∈ blocks, (X.card : ℝ) * mass (bin X) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro X hX
            have hlabel : bin X ∈ labels := Finset.mem_image.mpr ⟨X, hX, rfl⟩
            simp [hlabel]
      _ = ∑ X ∈ blocks, ∑ Y ∈ blocks.filter (fun Y => bin Y = bin X),
            (X.card : ℝ) * (Y.card : ℝ) := by
        apply Finset.sum_congr rfl
        intro X hX
        dsimp [mass]
        rw [Finset.mul_sum]
      _ = ∑ p ∈ samePairs, weight p := by
        simp [samePairs, weight, Finset.sum_filter, Finset.sum_product, eq_comm]
  have hCS : (∑ b ∈ labels, mass b) ^ 2 ≤
      (labels.card : ℝ) * ∑ b ∈ labels, mass b ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul labels
      (f := fun _ : β => (1 : ℝ)) (g := fun b => mass b ^ 2) (r := mass)
      (by intro b hb; norm_num)
      (by intro b hb; exact sq_nonneg (mass b))
      (by intro b hb; simp)
    simpa using h
  have hdenom : (U.card : ℝ) ^ 2 ≤ (K : ℝ) * ∑ p ∈ samePairs, weight p := by
    have hdenom0 : (U.card : ℝ) ^ 2 ≤ (labels.card : ℝ) * ∑ p ∈ samePairs, weight p := by
      rw [hmassSum, hmassSq] at hCS
      exact hCS
    calc
      (U.card : ℝ) ^ 2 ≤ (labels.card : ℝ) * ∑ p ∈ samePairs, weight p := hdenom0
      _ ≤ (K : ℝ) * ∑ p ∈ samePairs, weight p := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbins)
          (Finset.sum_nonneg fun p hp => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hUpos : 0 < (U.card : ℝ) := by
    obtain ⟨X, hX, ⟨a, ha⟩⟩ := hne
    have haU : a ∈ U := Finset.mem_biUnion.mpr ⟨X, hX, ha⟩
    have hcard : 1 ≤ U.card := Finset.one_le_card.mpr ⟨a, haU⟩
    exact_mod_cast hcard
  have hη : 0 ≤ η := by
    by_contra hneg
    have hbad0 : 0 ≤ (bad.card : ℝ) := Nat.cast_nonneg _
    have hn2 : 0 < (U.card : ℝ) ^ 2 := sq_pos_of_pos hUpos
    nlinarith [hbad, hbad0, hn2]
  have hprodDisj : (samePairs : Set (Finset α × Finset α)).PairwiseDisjoint
      (fun p => p.1 ×ˢ p.2) := by
    intro p hp q hq hpq
    rcases Finset.mem_filter.mp hp with ⟨hbp, _⟩
    rcases Finset.mem_filter.mp hq with ⟨hbq, _⟩
    rcases Finset.mem_product.mp hbp with ⟨hp₁, hp₂⟩
    rcases Finset.mem_product.mp hbq with ⟨hq₁, hq₂⟩
    apply Finset.disjoint_left.mpr
    intro z hzP hzQ
    rcases Finset.mem_product.mp hzP with ⟨hz₁, hz₂⟩
    rcases Finset.mem_product.mp hzQ with ⟨hz₁', hz₂'⟩
    by_cases h₁ : p.1 = q.1
    · have h₂ : p.2 ≠ q.2 := by
        intro heq
        apply hpq
        exact Prod.ext h₁ heq
      exact (Finset.disjoint_left.mp (hdisj hp₂ hq₂ h₂)) hz₂ hz₂'
    · exact (Finset.disjoint_left.mp (hdisj hp₁ hq₁ h₁)) hz₁ hz₁'
  have hbadDisj : (samePairs : Set (Finset α × Finset α)).PairwiseDisjoint badPart := by
    intro p hp q hq hpq
    exact (hprodDisj hp hq hpq).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hbadUnion : samePairs.biUnion badPart ⊆ bad := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨p, hp, hpz⟩
    exact (Finset.mem_filter.mp hpz).2
  have hbadSum : (∑ p ∈ samePairs, ((badPart p).card : ℝ)) ≤ (bad.card : ℝ) := by
    calc
      (∑ p ∈ samePairs, ((badPart p).card : ℝ)) =
          ((∑ p ∈ samePairs, (badPart p).card : ℕ) : ℝ) := by simp
      _ = ((samePairs.biUnion badPart).card : ℝ) := by rw [Finset.card_biUnion hbadDisj]
      _ ≤ (bad.card : ℝ) := by exact_mod_cast Finset.card_le_card hbadUnion
  by_contra hnone
  have hno : ∀ X ∈ blocks, ∀ Y ∈ blocks, bin X = bin Y → X.Nonempty → Y.Nonempty →
      ¬ (((X ×ˢ Y).filter (· ∈ bad)).card : ℝ) ≤ η * (K : ℝ) * X.card * Y.card := by
    intro X hX Y hY hbin hXne hYne hle
    apply hnone
    exact ⟨X, hX, Y, hY, hbin, hXne, hYne,
      by simpa [mul_assoc, mul_comm, mul_left_comm] using hle⟩
  have hleWeights : ∀ p ∈ samePairs,
      η * (K : ℝ) * weight p ≤ ((badPart p).card : ℝ) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hbp, hbin⟩
    rcases Finset.mem_product.mp hbp with ⟨hX, hY⟩
    by_cases hXne : p.1.Nonempty
    · by_cases hYne : p.2.Nonempty
      · exact le_of_lt (by
          simpa [weight, mul_assoc, mul_comm, mul_left_comm] using
            (lt_of_not_ge (hno p.1 hX p.2 hY hbin hXne hYne)))
      · have hYempty : p.2 = ∅ := by simpa [Finset.nonempty_iff_ne_empty] using hYne
        simp [badPart, hYempty, weight]
    · have hXempty : p.1 = ∅ := by simpa [Finset.nonempty_iff_ne_empty] using hXne
      simp [badPart, hXempty, weight]
  obtain ⟨X₀, hX₀, ⟨a₀, ha₀⟩⟩ := hne
  have hp₀ : (X₀, X₀) ∈ samePairs := by
    simp [samePairs, hX₀]
  have hstrict : η * (K : ℝ) * weight (X₀, X₀) <
      ((badPart (X₀, X₀)).card : ℝ) := by
    have hno₀ := hno X₀ hX₀ X₀ hX₀ rfl (by exact ⟨a₀, ha₀⟩) (by exact ⟨a₀, ha₀⟩)
    simpa [badPart, weight, mul_assoc, mul_comm, mul_left_comm] using lt_of_not_ge hno₀
  have hsumStrict : (∑ p ∈ samePairs, η * (K : ℝ) * weight p) <
      ∑ p ∈ samePairs, ((badPart p).card : ℝ) :=
    Finset.sum_lt_sum hleWeights ⟨(X₀, X₀), hp₀, hstrict⟩
  have hsumWeight : (∑ p ∈ samePairs, η * (K : ℝ) * weight p) =
      η * (K : ℝ) * ∑ p ∈ samePairs, weight p := by
    calc
      (∑ p ∈ samePairs, η * (K : ℝ) * weight p) =
          ∑ p ∈ samePairs, (η * (K : ℝ)) * weight p := by rfl
      _ = (η * (K : ℝ)) * ∑ p ∈ samePairs, weight p :=
        (Finset.mul_sum samePairs weight (η * (K : ℝ))).symm
      _ = η * (K : ℝ) * ∑ p ∈ samePairs, weight p := rfl
  have hηdenom : η * (U.card : ℝ) ^ 2 ≤
      η * (K : ℝ) * ∑ p ∈ samePairs, weight p := by
    have h := mul_le_mul_of_nonneg_left hdenom hη
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  linarith [hsumStrict, hsumWeight, hbadSum, hbad, hηdenom]

private theorem pairSelection_toC_injective {d : ℕ} : Function.Injective (toC (d := d)) := by
  intro x y h
  ext i
  exact Complex.ofReal_injective (congrFun h i)

private theorem pairSelection_core_empty_of_isolated_zero {d : ℕ} (hd : 1 ≤ d)
    (core : Finset (Pt d)) (hcore : CoreIsolated core 0) : core = ∅ := by
  classical
  obtain ⟨F, hFdegree, hFisolated⟩ := hcore
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let i : Fin d := ⟨0, hd⟩
  have hP := hFisolated x hx
  have hspan_le : Ideal.span F ≤ pointIdeal (toC x) := hP.1.2
  have hFzero : ∀ f ∈ F, f = 0 := by
    intro f hf
    have hdegree : f.totalDegree = 0 := Nat.eq_zero_of_le_zero (hFdegree f hf)
    have hconstant : f = MvPolynomial.C (f.coeff 0) :=
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdegree
    have hfpoint : f ∈ pointIdeal (toC x) := hspan_le (Ideal.subset_span hf)
    have heval : MvPolynomial.eval (toC x) f = 0 := by simpa [pointIdeal] using hfpoint
    rw [hconstant] at heval
    have hcoeff : f.coeff 0 = 0 := by simpa using heval
    rw [hconstant, hcoeff]
    simp
  have hspan : Ideal.span F = ⊥ := by
    apply le_antisymm
    · exact Ideal.span_le.mpr hFzero
    · exact bot_le
  have hPbot := hP
  rw [hspan, Ideal.minimalPrimes_eq_subsingleton_self] at hPbot
  have hpointbot : pointIdeal (toC x) = ⊥ := by simpa using hPbot
  have hvar : MvPolynomial.X i - MvPolynomial.C (toC x i) ∈ pointIdeal (toC x) := by
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    have : y = toC x := Set.mem_singleton_iff.mp hy
    subst y
    simp
  have hvarzero : MvPolynomial.X i - MvPolynomial.C (toC x i) = 0 := by
    have h := hvar
    rw [hpointbot] at h
    exact Ideal.mem_bot.mp h
  let y : Point d := Function.update (toC x) i (toC x i + 1)
  have heval := congrArg (MvPolynomial.eval y) hvarzero
  have : (1 : ℂ) = 0 := by simpa [y, i] using heval
  exact one_ne_zero this

private def pairSelectionShift {n : ℕ} (a : Point n) : Poly n →ₐ[ℂ] Poly n :=
  MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (a i)

private theorem pairSelectionShift_comp {n : ℕ} (a : Point n) :
    (pairSelectionShift a).comp (pairSelectionShift (-a)) = AlgHom.id ℂ (Poly n) ∧
      (pairSelectionShift (-a)).comp (pairSelectionShift a) = AlgHom.id ℂ (Poly n) := by
  constructor <;> ext i <;> simp [pairSelectionShift, add_assoc]

private theorem pairSelectionShift_surjective {n : ℕ} (a : Point n) :
    Function.Surjective (pairSelectionShift a) := by
  intro f
  refine ⟨pairSelectionShift (-a) f, ?_⟩
  have h := (pairSelectionShift_comp a).1
  exact congrArg (fun g : Poly n →ₐ[ℂ] Poly n => g f) h

private theorem pairSelectionShift_injective {n : ℕ} (a : Point n) :
  Function.Injective (pairSelectionShift a) := by
  intro f g h
  have h' := congrArg (fun z : Poly n => pairSelectionShift (-a) z) h
  have hf : pairSelectionShift (-a) (pairSelectionShift a f) = f := by
    simpa using congrArg (fun e : Poly n →ₐ[ℂ] Poly n => e f) (pairSelectionShift_comp a).2
  have hg : pairSelectionShift (-a) (pairSelectionShift a g) = g := by
    simpa using congrArg (fun e : Poly n →ₐ[ℂ] Poly n => e g) (pairSelectionShift_comp a).2
  calc
    f = pairSelectionShift (-a) (pairSelectionShift a f) := hf.symm
    _ = pairSelectionShift (-a) (pairSelectionShift a g) := h'
    _ = g := hg

private theorem pairSelectionShift_monomial_degree {n : ℕ} (a : Point n)
    (s : Fin n →₀ ℕ) (c : ℂ) :
    (pairSelectionShift a (MvPolynomial.monomial s c)).totalDegree ≤ s.sum fun _ e => e := by
  classical
  by_cases hc : c = 0
  · simp [pairSelectionShift, hc]
  · have hbase (i : Fin n) :
        (MvPolynomial.X i + MvPolynomial.C (a i)).totalDegree ≤ 1 := by
      calc
        _ ≤ max (MvPolynomial.X i).totalDegree (MvPolynomial.C (a i)).totalDegree :=
          MvPolynomial.totalDegree_add _ _
        _ ≤ 1 := by simp
    have hprod :
        (s.prod fun i e =>
          (MvPolynomial.X i + MvPolynomial.C (a i)) ^ e).totalDegree ≤
            s.sum fun _ e => e := by
      change (∏ i ∈ s.support,
        (MvPolynomial.X i + MvPolynomial.C (a i)) ^ s i).totalDegree ≤ _
      calc
        _ ≤ ∑ i ∈ s.support,
              ((MvPolynomial.X i + MvPolynomial.C (a i)) ^ s i).totalDegree :=
            MvPolynomial.totalDegree_finsetProd s.support _
        _ ≤ ∑ i ∈ s.support, s i := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            _ ≤ s i * (MvPolynomial.X i + MvPolynomial.C (a i)).totalDegree :=
              MvPolynomial.totalDegree_pow _ _
            _ ≤ s i * 1 := Nat.mul_le_mul_left _ (hbase i)
            _ = s i := Nat.mul_one _
        _ = s.sum fun _ e => e := rfl
    change (pairSelectionShift a (MvPolynomial.monomial s c)).totalDegree ≤ _
    rw [pairSelectionShift, MvPolynomial.aeval_monomial]
    calc
      _ ≤ (algebraMap ℂ (Poly n) c).totalDegree +
            (s.prod fun i e =>
              (MvPolynomial.X i + MvPolynomial.C (a i)) ^ e).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ s.sum fun _ e => e := by simpa using hprod

private theorem pairSelectionShift_totalDegree {n : ℕ} (a : Point n) (f : Poly n) :
    (pairSelectionShift a f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  calc
    (pairSelectionShift a (MvPolynomial.monomial s (f.coeff s))).totalDegree ≤
        s.sum fun _ e => e := pairSelectionShift_monomial_degree a s _
    _ ≤ f.totalDegree := MvPolynomial.le_totalDegree hs

private theorem pairSelectionShift_pointIdeal_map {n : ℕ} (a x : Point n) :
    (pointIdeal x).map (pairSelectionShift a).toRingHom = pointIdeal (x - a) := by
  have hsurj := pairSelectionShift_surjective a
  have hcomap : (pointIdeal (x - a)).comap (pairSelectionShift a).toRingHom = pointIdeal x := by
    ext f
    rw [Ideal.mem_comap]
    change (pairSelectionShift a f) ∈ MvPolynomial.vanishingIdeal ℂ {x - a} ↔
      f ∈ MvPolynomial.vanishingIdeal ℂ {x}
    rw [MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.mem_vanishingIdeal_iff]
    have heval : MvPolynomial.aeval (x - a) (pairSelectionShift a f) =
        MvPolynomial.aeval x f := by
      have hmap : (MvPolynomial.aeval (x - a)).comp (pairSelectionShift a) =
          MvPolynomial.aeval x := by
        apply MvPolynomial.algHom_ext
        intro i
        simp [pairSelectionShift, sub_add_cancel]
      exact congrArg (fun g : Poly n →ₐ[ℂ] ℂ => g f) hmap
    constructor
    · intro hf
      have h := hf (x - a) (by simp)
      rw [heval] at h
      intro y hy
      have hyx : y = x := by simpa using hy
      subst y
      exact h
    · intro hf y hy
      have hyx : y = x - a := by simpa using hy
      subst y
      have h := hf x (by simp)
      rw [heval]
      exact h
  rw [← hcomap]
  exact Ideal.map_comap_of_surjective _ hsurj _

private theorem pairSelectionShift_isolated {n : ℕ} (a x : Point n)
    (F : Set (Poly n)) (hF : pointIdeal x ∈ (Ideal.span F).minimalPrimes) :
    pointIdeal (x - a) ∈ (Ideal.span (pairSelectionShift a '' F)).minimalPrimes := by
  let φ := pairSelectionShift a
  have hsurj : Function.Surjective φ := pairSelectionShift_surjective a
  have hinj : Function.Injective φ := pairSelectionShift_injective a
  have hker : RingHom.ker (φ : Poly n →+* Poly n) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have hmap :
      pointIdeal (x - a) ∈ ((Ideal.span F).map (φ : Poly n →+* Poly n)).minimalPrimes := by
    rw [Ideal.minimalPrimes_map_of_surjective
      (f := (φ : Poly n →+* Poly n)) hsurj (Ideal.span F), hker, sup_bot_eq]
    exact ⟨pointIdeal x, hF, pairSelectionShift_pointIdeal_map a x⟩
  simpa [φ, Ideal.map_span] using hmap

/-- `prof:pair-selection.core` (`profiles.tex:562–568`): the cone over a directional family meets
a core isolated in degree `L` in at most `C · deg(C_p) · L^2` points (isolated Bézout). -/
theorem pair_selection_core (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (core : Finset (Pt d)) (L : ℕ), CoreIsolated core L →
      ∀ (p : Pt d) (Cf : ProjectiveFamily.Family d), IsDirectionalFamily Cf →
        ((core.filter (fun q => DirIn Cf p q)).card : ℝ) ≤
          C * (ProjectiveFamily.degree Cf : ℝ) * (L : ℝ) ^ 2 := by
  refine ⟨1, by norm_num, ?_⟩
  intro core L hcore p Cf hCf
  let selected : Finset (Pt d) := core.filter (fun q => DirIn Cf p q)
  by_cases hLzero : L = 0
  · have hcore0 : CoreIsolated core 0 := by simpa [hLzero] using hcore
    have hcoreEmpty := pairSelection_core_empty_of_isolated_zero (by omega) core hcore0
    simp [selected, hcoreEmpty, hLzero]
  · have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hLzero
    obtain ⟨F, hFdegree, hFisolated⟩ := hcore
    let onCurve (γ : ProjectiveVariety d) (q : Pt d) : Prop :=
      ∃ h : toC q ≠ toC p, radialProjection (toC p) (toC q) h ∈ γ.points
    let curvePoints (γ : ProjectiveVariety d) : Finset (Pt d) :=
      core.filter (onCurve γ)
    have hcurveBound (γ : ProjectiveVariety d) (hγ : γ ∈ Cf) :
        ((curvePoints γ).card : ℝ) ≤ (γ.degree : ℝ) * (L : ℝ) ^ 2 := by
      by_cases hnonempty : (curvePoints γ).Nonempty
      · obtain ⟨q, hq⟩ := hnonempty
        have hqmem := Finset.mem_filter.mp hq
        obtain ⟨hqcore, ⟨hqp, hproj⟩⟩ := hqmem
        have hγdata := hCf γ hγ
        have hγirr : γ.IsIrreducible := hγdata.1
        have hγdim : γ.dimension = 1 := hγdata.2.1
        have hγpts : γ.points.Nonempty := ⟨radialProjection (toC p) (toC q) hqp, hproj⟩
        let cone : AffineVariety d := γ.affineCone
        have hconeDim : cone.dimension = 2 := by
          rw [ProjectiveVariety.dimension_cone γ hγpts, hγdim]
        have hconePure : cone.IsPure 2 := by
          intro W
          have hWmin : W.val ∈ cone.ideal.minimalPrimes := W.property
          have hconeIrr : cone.ideal.IsPrime := hγirr
          have hWeq : W.val = cone.ideal := le_antisymm
            (hWmin.2 ⟨hconeIrr, le_rfl⟩ hWmin.1.2) hWmin.1.2
          have hWvar : W.variety = cone := AffineVariety.ext hWeq
          rw [hWvar]
          exact hconeDim
        let E : Set (Poly d) := pairSelectionShift (toC p) '' F
        have hEdegree : ∀ f ∈ E, f.totalDegree ≤ L := by
          intro f hf
          rcases (Set.mem_image (pairSelectionShift (toC p)) F f).mp hf with ⟨g, hg, rfl⟩
          exact (pairSelectionShift_totalDegree (toC p) g).trans (hFdegree g hg)
        let translated : Finset (Point d) :=
          (curvePoints γ).image (fun q => toC q - toC p)
        have htranslatedCard : translated.card = (curvePoints γ).card := by
          apply Finset.card_image_iff.mpr
          intro q hq r hr hqr
          apply pairSelection_toC_injective
          have hqr' := congrArg (fun z : Point d => z + toC p) hqr
          simpa using hqr'
        have htranslatedIso : ∀ z ∈ translated,
            pointIdeal z ∈ (cone.ideal ⊔ Ideal.span E).minimalPrimes := by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
          have hqmem := Finset.mem_filter.mp hq
          obtain ⟨hqcore, ⟨hqp, hproj⟩⟩ := hqmem
          have hprojective :
              Projectivization.mk ℂ (toC q - toC p) (sub_ne_zero.mpr hqp) ∈ γ.points := by
            simpa [radialProjection] using hproj
          have hconePoint : toC q - toC p ∈ cone.points :=
            (ProjectiveVariety.mem_points_mk_iff γ (toC q - toC p) _).mp hprojective
          have hshifted := pairSelectionShift_isolated (toC p) (toC q) F
            (hFisolated q hqcore)
          have hpointShifted :
              pointIdeal (toC q - toC p) ∈ (Ideal.span E).minimalPrimes := by
            simpa [E] using hshifted
          have hconeLe : cone.ideal ≤ pointIdeal (toC q - toC p) := by
            intro f hf
            rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_iff]
            intro y hy
            have hy' : y = toC q - toC p := by simpa using hy
            subst y
            exact hconePoint f hf
          exact dprofiles2_minimal_of_intermediate (Ideal.span E)
            (cone.ideal ⊔ Ideal.span E) (pointIdeal (toC q - toC p))
            le_sup_right (sup_le hconeLe hpointShifted.1.2) hpointShifted
        have hbezout := TrackA.fa_bezout_relative_points cone 2 hconePure E L hL
          hEdegree translated htranslatedIso
        have hconeDegree : cone.degree = γ.degree := ProjectiveVariety.degree_cone γ
        have htranslatedBound :
            ((curvePoints γ).card : ℚ) ≤ γ.degree * (L : ℚ) ^ 2 := by
          rw [← htranslatedCard, ← hconeDegree]
          exact hbezout
        exact_mod_cast htranslatedBound
      · have hcardzero : (curvePoints γ).card = 0 := by
          have hempty : curvePoints γ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
          simp [hempty]
        have hγdata := hCf γ hγ
        have hγirr : γ.IsIrreducible := hγdata.1
        have hdegLower : 1 ≤ γ.degree := by
          rw [← ProjectiveVariety.degree_cone γ]
          exact AffineVariety.one_le_degree γ.affineCone hγirr.ne_top
        have hdegNonneg : 0 ≤ (γ.degree : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1) hdegLower)
        rw [hcardzero]
        exact_mod_cast (mul_nonneg hdegNonneg (sq_nonneg (L : ℝ)))
    have hselectedCover : selected ⊆ Cf.biUnion curvePoints := by
      intro q hq
      have hqmem := Finset.mem_filter.mp hq
      obtain ⟨hqcore, hDir⟩ := hqmem
      rcases hDir with ⟨hqp, hfamily⟩
      rcases Set.mem_iUnion.mp hfamily with ⟨γ, hγfamily⟩
      rcases Set.mem_iUnion.mp hγfamily with ⟨hγ, hγpoint⟩
      exact Finset.mem_biUnion.mpr ⟨γ, hγ,
        Finset.mem_filter.mpr ⟨hqcore, ⟨hqp, hγpoint⟩⟩⟩
    have hselectedBound :
        (selected.card : ℝ) ≤ ∑ γ ∈ Cf, ((curvePoints γ).card : ℝ) := by
      calc
        (selected.card : ℝ) ≤ ((Cf.biUnion curvePoints).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hselectedCover
        _ ≤ ((∑ γ ∈ Cf, (curvePoints γ).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ = ∑ γ ∈ Cf, ((curvePoints γ).card : ℝ) := by simp
    have hsumBound :
        (∑ γ ∈ Cf, ((curvePoints γ).card : ℝ)) ≤
          ∑ γ ∈ Cf, (γ.degree : ℝ) * (L : ℝ) ^ 2 :=
      Finset.sum_le_sum fun γ hγ => hcurveBound γ hγ
    calc
      (selected.card : ℝ) ≤ ∑ γ ∈ Cf, ((curvePoints γ).card : ℝ) := hselectedBound
      _ ≤ ∑ γ ∈ Cf, (γ.degree : ℝ) * (L : ℝ) ^ 2 := hsumBound
      _ = (ProjectiveFamily.degree Cf : ℝ) * (L : ℝ) ^ 2 := by
        rw [← Finset.sum_mul]
        simp [ProjectiveFamily.degree]
      _ = 1 * (ProjectiveFamily.degree Cf : ℝ) * (L : ℝ) ^ 2 := by ring
      _ = _ := by rfl

private def pairSelectionRestrictLine {d : ℕ} (q r : Pt d) :
    Poly d →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval fun i =>
    Polynomial.C (toC q i) + Polynomial.X * Polynomial.C (toC r i - toC q i)

private theorem pairSelection_realLine_isRealFlat {d : ℕ} (Y : AffineVariety d)
    (hline : IsLine Y) (q r : Pt d) (hqr : q ≠ r)
    (hq : toC q ∈ Y) (hr : toC r ∈ Y) : IsRealFlat Y := by
  classical
  rcases hline with ⟨a, v, hv, hYpoints⟩
  let Lc : AffineSubspace ℂ (Point d) := AffineSubspace.mk' a (ℂ ∙ v)
  have hY_Lc : Y.points = (Lc : Set (Point d)) := by
    ext z
    rw [hYpoints]
    change (∃ t : ℂ, z = a + t • v) ↔ z ∈ Lc
    rw [AffineSubspace.mem_mk']
    constructor
    · rintro ⟨t, rfl⟩
      rw [Submodule.mem_span_singleton]
      exact ⟨t, by simp⟩
    · intro hz
      rw [Submodule.mem_span_singleton] at hz
      rcases hz with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have ht' : z - a = t • v := by simpa using ht.symm
      calc
        z = (z - a) + a := by abel
        _ = t • v + a := by rw [ht']
        _ = a + t • v := by abel
  have hqLc : toC q ∈ Lc := by
    change toC q ∈ Y.points at hq
    rw [hY_Lc] at hq
    exact hq
  have hrLc : toC r ∈ Lc := by
    change toC r ∈ Y.points at hr
    rw [hY_Lc] at hr
    exact hr
  have hqrC : toC q ≠ toC r := by
    intro h
    exact hqr (pairSelection_toC_injective h)
  have hlineLe : affineSpan ℂ ({toC q, toC r} : Set (Point d)) ≤ Lc :=
    affineSpan_pair_le_of_mem_of_mem hqLc hrLc
  have hdirLine : Module.finrank ℂ
      (affineSpan ℂ ({toC q, toC r} : Set (Point d))).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    apply finrank_span_singleton
    intro hz
    exact hqrC (sub_eq_zero.mp hz)
  have hdirLc : Module.finrank ℂ Lc.direction = 1 := by
    dsimp [Lc]
    rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton hv
  have hdirEq :
      (affineSpan ℂ ({toC q, toC r} : Set (Point d))).direction = Lc.direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hlineLe)
      (by rw [hdirLine, hdirLc])
  have hlineEq : affineSpan ℂ ({toC q, toC r} : Set (Point d)) = Lc :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirEq
      ⟨toC q, left_mem_affineSpan_pair ℂ (toC q) (toC r)⟩ hlineLe
  have hYline : Y.points =
      (affineSpan ℂ ({toC q, toC r} : Set (Point d)) : Set (Point d)) := by
    rw [hY_Lc, hlineEq]
  let F : AffineSubspace ℝ (Pt d) := affineSpan ℝ ({q, r} : Set (Pt d))
  let T : Set (Point d) := toC '' (F : Set (Pt d))
  have hF_nonempty : (F : Set (Pt d)).Nonempty := by
    exact ⟨q, left_mem_affineSpan_pair ℝ q r⟩
  have hTsubset : T ⊆ Y.points := by
    intro z hz
    rcases (Set.mem_image toC (F : Set (Pt d)) z).mp hz with ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ :=
      (mem_affineSpan_pair_iff_exists_lineMap_eq (p := x) (p₁ := q) (p₂ := r)).mp hx
    have hcoord : toC x = AffineMap.lineMap (toC q) (toC r) (t : ℂ) := by
      rw [← ht]
      ext i
      simp [AffineMap.lineMap_apply_module', toC]
    rw [hYline]
    rw [hcoord]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hEval (t : ℂ) (f : Poly d) :
      Polynomial.eval t (pairSelectionRestrictLine q r f) =
        MvPolynomial.eval (fun i => toC q i + t * (toC r i - toC q i)) f := by
    change Polynomial.aeval t (pairSelectionRestrictLine q r f) = _
    have hmap : (Polynomial.aeval t).comp (pairSelectionRestrictLine q r) =
        MvPolynomial.aeval (fun i => toC q i + t * (toC r i - toC q i)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [pairSelectionRestrictLine]
    exact congrArg (fun φ : Poly d →ₐ[ℂ] ℂ => φ f) hmap
  have hcoordLine (t : ℂ) :
      AffineMap.lineMap (toC q) (toC r) t =
        (fun i => toC q i + t * (toC r i - toC q i)) := by
    ext i
    simp [AffineMap.lineMap_apply_module', sub_eq_add_neg]
    ring
  have hvanishing : MvPolynomial.vanishingIdeal ℂ T = Y.ideal := by
    apply le_antisymm
    · intro f hf
      rw [← AffineVariety.vanishingIdeal_points Y]
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro z hz
      have hzline : z ∈ affineSpan ℂ ({toC q, toC r} : Set (Point d)) := by
        simpa [hYline] using hz
      obtain ⟨t, ht⟩ :=
        (mem_affineSpan_pair_iff_exists_lineMap_eq
          (p := z) (p₁ := toC q) (p₂ := toC r)).mp hzline
      have hroots : Set.Infinite {t : ℂ | Polynomial.IsRoot (pairSelectionRestrictLine q r f) t} := by
        apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
        intro z hz
        rcases hz with ⟨t, rfl⟩
        have hxT : toC (AffineMap.lineMap q r t) ∈ T :=
          Set.mem_image_of_mem toC (AffineMap.lineMap_mem_affineSpan_pair t q r)
        have hvan := MvPolynomial.mem_vanishingIdeal_iff.mp hf _ hxT
        have hcoordReal : toC (AffineMap.lineMap q r t) =
            fun i => toC q i + (t : ℂ) * (toC r i - toC q i) := by
          ext i
          simp [AffineMap.lineMap_apply_module', toC]
          push_cast
          ring
        change Polynomial.eval (t : ℂ) (pairSelectionRestrictLine q r f) = 0
        rw [hEval]
        simpa [hcoordReal] using hvan
      have hzero : pairSelectionRestrictLine q r f = 0 :=
        Polynomial.eq_zero_of_infinite_isRoot _ hroots
      have hEvalZero := hEval t f
      rw [hzero] at hEvalZero
      have hvec : MvPolynomial.eval (fun i => toC q i + t * (toC r i - toC q i)) f = 0 := by
        simpa using hEvalZero.symm
      have hz' : z = (fun i => toC q i + t * (toC r i - toC q i)) := by
        calc
          z = AffineMap.lineMap (toC q) (toC r) t := ht.symm
          _ = _ := hcoordLine t
      rw [hz']
      have hzEval : MvPolynomial.eval (fun i => toC q i + t * (toC r i - toC q i)) f = 0 := hvec
      exact hzEval
    · intro f hf
      rw [← AffineVariety.vanishingIdeal_points Y] at hf
      rw [MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
      intro z hz
      exact hf z (hTsubset hz)
  have hclosure : AffineVariety.closure T = Y := by
    apply AffineVariety.ext
    exact hvanishing
  exact ⟨F, hF_nonempty, by simpa [T, hclosure]⟩

private theorem pairSelection_localCarrier_exists {d : ℕ} {P : Finset (Pt d)}
    {θ ξ K : ℝ} (X : Piece d) (q : Pt d) (hq : q ∈ X.pts)
    (hX : PieceGood P θ ξ K X) (j : ℕ) (hj : j ≤ d) :
    ∃ Z, X.path.IsCarrier j Z ∧ toC q ∈ Z := by
  have hsysPoint : X.path.system j ≤ pointIdeal (toC q) := by
    apply Ideal.span_le.mpr
    rintro f ⟨i, hi, rfl⟩
    change X.path.cut i ∈ MvPolynomial.vanishingIdeal ℂ {toC q}
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    have hzx : z = toC q := Set.mem_singleton_iff.mp hz
    subst z
    exact hX.vanish q hq i
  letI : (pointIdeal (toC q)).IsPrime := (pointIdeal_isMaximal (toC q)).isPrime
  obtain ⟨I, hI, hIle⟩ := Ideal.exists_minimalPrimes_le hsysPoint
  let Z : AffineVariety d := ⟨I, hI.isPrime.isRadical⟩
  refine ⟨Z, ?_, ?_⟩
  · change I ∈ (X.path.system j).minimalPrimes
    exact hI
  · change toC q ∈ MvPolynomial.zeroLocus ℂ I
    intro f hf
    have hfp : f ∈ pointIdeal (toC q) := hIle hf
    have hvan : f ∈ MvPolynomial.vanishingIdeal ℂ {toC q} := by
      simpa [pointIdeal] using hfp
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hvan (toC q) (by simp)

private def pairSelectionPrefixEquiv {d j : ℕ} (hj : j ≤ d) :
    Fin j ≃ {i : Fin d // i.val < j} where
  toFun i := ⟨⟨i.val, i.isLt.trans_le hj⟩, i.isLt⟩
  invFun i := ⟨i.1.val, i.2⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv i := by apply Subtype.ext; apply Fin.ext; rfl

private theorem pairSelection_eScale_eq_prefix {d j : ℕ} (hj : j ≤ d)
    (B s : ℝ) (t : Fin d → ℝ) :
    eScale B s t j = ∏ i : Fin j, cutScale B s t ⟨i.val, i.isLt.trans_le hj⟩ := by
  let e := pairSelectionPrefixEquiv hj
  symm
  calc
    (∏ i : Fin j, cutScale B s t (e i).1) =
        ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), cutScale B s t i := by
      calc
        (∏ i : Fin j, cutScale B s t (e i).1) =
            ∏ i : {i : Fin d // i.val < j}, cutScale B s t i.1 :=
          Equiv.prod_comp e (fun i => cutScale B s t i.1)
        _ = ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), cutScale B s t i := by
          symm
          exact Finset.prod_subtype (Finset.univ.filter (fun i : Fin d => i.val < j))
            (by intro i; simp) (cutScale B s t)
    _ = eScale B s t j := by rfl

private theorem pairSelection_eScale_formula {d j : ℕ} (hj : j ≤ d)
    (B s : ℝ) (t : Fin d → ℝ) :
    eScale B s t j = (B ^ j) *
      Real.exp ((∑ i : Fin j, t ⟨i.val, i.isLt.trans_le hj⟩) * s) := by
  rw [pairSelection_eScale_eq_prefix hj]
  simp only [cutScale, testDeg]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_const, Finset.card_fin, Real.exp_sum, Finset.sum_mul]

private theorem pairSelection_eScale_filter_formula {d j : ℕ} (B s : ℝ) (t : Fin d → ℝ) :
    eScale B s t j =
      B ^ (Finset.univ.filter (fun i : Fin d => i.val < j)).card *
        Real.exp ((∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), t i) * s) := by
  unfold eScale cutScale testDeg
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_const, Real.exp_sum, Finset.sum_mul]

/-- `prof:pair-selection.terminal` (`profiles.tex:546–560`): a good partition carries a global
terminal assignment whose excluded incidences number at most `ε N^2` (one application of
`geo:terminal`; nonreal lines are omitted at cost `D_d⁻¹ e^{o(s)} n` per piece). -/
theorem pair_selection_terminal (d : ℕ) (hd : 3 ≤ d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∃ θ₁ > 0, ∃ η > 0, ∃ ξ₀ > 0, ∃ s₁ : ℝ, ∃ N₀ : ℕ,
      ∀ (P : Finset (Pt d)) (Q : Partition d) (δ ξ K s₀ : ℝ), N₀ ≤ P.card →
        cfgM P ≤ η * cfgA P → RealFlatCap P c₀ → 0 < ξ → ξ ≤ ξ₀ → 1 ≤ K → s₁ ≤ s₀ →
        Q.Good P δ θ₁ ξ K s₀ →
        ∀ Cf : Pt d → ProjectiveFamily.Family d,
          (∀ p ∈ P, IsDirectionalFamily (Cf p) ∧
            (ProjectiveFamily.degree (Cf p) : ℝ) ≤ η * cfgN P / cfgA P) →
        ∃ τ : Pt d → Option (AffineVariety d), TerminalAssignment Q ε τ ∧
          (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
              ∃ Y, τ pq.2 = some Y ∧ ProjectsInto (Cf pq.1) pq.1 Y)).card : ℝ) ≤
            ε * cfgN P ^ 2 := by
  intro ε hε
  obtain ⟨ηgeo, hηgeo, Ngeo, hgeo⟩ := geo_terminal d hd c₀ hc₀ ε hε
  obtain ⟨c, Cd, hc, hCd, hbudget⟩ := prof_budget d hd
  let θbud : ℝ := c / 8
  have hθbud : 0 < θbud := by dsimp [θbud]; positivity
  obtain ⟨θB, hθB, ξB, hξB, sB, hbudget⟩ := hbudget θbud hθbud 1 (by norm_num)
  let θout : ℝ := min θB (min (ε / 8) (c / 8))
  have hθout : 0 < θout := by dsimp [θout]; positivity
  have hθoutB : θout ≤ θB := by
    dsimp [θout]
    exact min_le_left _ _
  let sOut : ℝ := max sB 0
  let m : ℕ := Nat.ceil (ε⁻¹)
  let Nout : ℕ := max Ngeo (m ^ d)
  refine ⟨θout, hθout, ηgeo, hηgeo, ξB, hξB, sOut, Nout, ?_⟩
  intro P Q δ ξ K s₀ hN hM hcap hξ hξB hK hs₀ hQ Cf hCf
  have hNgeo : Ngeo ≤ P.card := le_trans (le_max_left _ _) hN
  have hmN : m ^ d ≤ P.card := le_trans (le_max_right _ _) hN
  have hmcast : ε⁻¹ ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil _
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    rw [hm0] at hmcast
    have : 0 < ε⁻¹ := by positivity
    linarith
  have hBpow : cfgB P ^ d = cfgN P := by
    dsimp [cfgB, cfgN]
    have hPnonneg : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
    rw [← Real.rpow_natCast, ← Real.rpow_mul hPnonneg]
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hpow : (1 : ℝ) / (d : ℝ) * (d : ℝ) = 1 := by field_simp
    rw [hpow, Real.rpow_one]
  have hmPow : (m : ℝ) ^ d ≤ cfgB P ^ d := by
    rw [hBpow]
    change (m ^ d : ℝ) ≤ (P.card : ℝ)
    exact_mod_cast hmN
  have hBnonneg : 0 ≤ cfgB P := by dsimp [cfgB]; positivity
  have hBLower : (m : ℝ) ≤ cfgB P :=
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) hBnonneg (by omega : d ≠ 0)).mp hmPow
  have hεB : 1 ≤ ε * cfgB P := by
    calc
      1 = ε * ε⁻¹ := by field_simp
      _ ≤ ε * cfgB P := mul_le_mul_of_nonneg_left (hmcast.trans hBLower) hε.le
  have hBge : 1 ≤ cfgB P := by
    have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    exact hmOne.trans hBLower
  have hcandidateOfPiece (q : Pt d) (X : Piece d) (hX : X ∈ Q.pieces)
      (hq : q ∈ X.pts) :
      ∃ XY : Piece d × AffineVariety d, XY.1 ∈ Q.pieces ∧ q ∈ XY.1.pts ∧
        XY.1.path.IsCarrier (d - 1) XY.2 ∧ toC q ∈ XY.2 := by
    obtain ⟨Z, hZ, hZq⟩ := pairSelection_localCarrier_exists X q hq
      (hQ.pieces_good X hX).1 (d - 1) (by omega)
    exact ⟨(X, Z), hX, hq, hZ, hZq⟩
  let candidate (q : Pt d) : Prop :=
    ∃ XY : Piece d × AffineVariety d, XY.1 ∈ Q.pieces ∧ q ∈ XY.1.pts ∧
      XY.1.path.IsCarrier (d - 1) XY.2 ∧ toC q ∈ XY.2
  let chosen (q : Pt d) : Option (Piece d × AffineVariety d) :=
    if h : candidate q then some (Classical.choose h) else none
  have hchosenSpec (q : Pt d) (XY : Piece d × AffineVariety d)
      (hch : chosen q = some XY) :
      XY.1 ∈ Q.pieces ∧ q ∈ XY.1.pts ∧
        XY.1.path.IsCarrier (d - 1) XY.2 ∧ toC q ∈ XY.2 := by
    unfold chosen at hch
    split at hch
    · rename_i hcand
      have heq : Classical.choose hcand = XY := Option.some.inj hch
      subst XY
      exact Classical.choose_spec hcand
    · simp at hch
  let τ : Pt d → Option (AffineVariety d) := fun q =>
    match chosen q with
    | none => none
    | some XY => if IsLine XY.2 ∧ ¬ IsRealFlat XY.2 then none else some XY.2
  have hτWitness (q : Pt d) (Y : AffineVariety d) (hτ : τ q = some Y) :
      ∃ XY : Piece d × AffineVariety d, chosen q = some XY ∧ XY.2 = Y ∧
        XY.1 ∈ Q.pieces ∧ q ∈ XY.1.pts ∧
        XY.1.path.IsCarrier (d - 1) XY.2 ∧ toC q ∈ XY.2 ∧
        ¬ (IsLine XY.2 ∧ ¬ IsRealFlat XY.2) := by
    cases hch : chosen q with
    | none => simp [τ, hch] at hτ
    | some XY =>
      by_cases hbad : IsLine XY.2 ∧ ¬ IsRealFlat XY.2
      · simp [τ, hch, hbad] at hτ
      · have hY : XY.2 = Y := by
          simp [τ, hch, hbad] at hτ
          exact hτ
        subst Y
        rcases hchosenSpec q XY hch with ⟨hX, hq, hcarrier, hmem⟩
        exact ⟨XY, rfl, rfl, hX, hq, hcarrier, hmem, hbad⟩
  have hτNonbad (q : Pt d) (Y : AffineVariety d) (hτ : τ q = some Y) :
      ¬ (IsLine Y ∧ ¬ IsRealFlat Y) := by
    obtain ⟨XY, _, rfl, _, _, _, _, hbad⟩ := hτWitness q Y hτ
    exact hbad
  have hτCarrierFor (q : Pt d) (Y : AffineVariety d) (hτ : τ q = some Y) :
      ∃ X ∈ Q.pieces, q ∈ X.pts ∧ X.path.IsCarrier (d - 1) Y ∧ toC q ∈ Y := by
    obtain ⟨XY, _, hY, hX, hq, hcarrier, hmem, _⟩ := hτWitness q Y hτ
    subst Y
    exact ⟨XY.1, hX, hq, hcarrier, hmem⟩
  let assigned : Finset (Pt d) := P.filter (fun q => τ q ≠ none)
  let carriers : Finset (AffineVariety d) :=
    assigned.image (fun q => (τ q).getD (AffineVariety.empty : AffineVariety d))
  let S : AffineVariety d → Finset (Pt d) := fun Y => P.filter (fun q => τ q = some Y)
  have hcarrierMem (Y : AffineVariety d) (hY : Y ∈ carriers) :
      ∃ q ∈ P, τ q = some Y := by
    rcases Finset.mem_image.mp hY with ⟨q, hq, hEq⟩
    have hSome : τ q ≠ none := (Finset.mem_filter.mp hq).2
    cases hτ : τ q with
    | none => contradiction
    | some Z =>
      have hZ : Z = Y := by simpa [hτ] using hEq
      have hτY : τ q = some Y := by
        rw [hτ]
        exact congrArg some hZ
      exact ⟨q, (Finset.mem_filter.mp hq).1, hτY⟩
  have hYmem (q : Pt d) (hq : q ∈ P) (Y : AffineVariety d) (hτ : τ q = some Y) :
      Y ∈ carriers := by
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ⟨hq, ?_⟩, ?_⟩
    · simp [hτ]
    · simpa [hτ]
  have hAssignment : Assignment P carriers S := by
    refine ⟨?_, ?_, ?_⟩
    · intro Y hY q hq
      exact (Finset.mem_filter.mp hq).1
    · intro Y hY q hq
      have hτ : τ q = some Y := (Finset.mem_filter.mp hq).2
      obtain ⟨X, hX, hqX, hcarrier, hmem⟩ := hτCarrierFor q Y hτ
      exact hmem
    · intro Y hY Z hZ hYZ
      apply Finset.disjoint_left.mpr
      intro q hqY hqZ
      have hτY : τ q = some Y := (Finset.mem_filter.mp hqY).2
      have hτZ : τ q = some Z := (Finset.mem_filter.mp hqZ).2
      have : Y = Z := by simpa [hτY] using hτZ
      exact hYZ this
  have hcarriersCurve : ∀ Y ∈ carriers, IsCurve Y := by
    intro Y hY
    obtain ⟨q, hqP, hτ⟩ := hcarrierMem Y hY
    obtain ⟨X, hX, hqX, hcarrier, hmem⟩ := hτCarrierFor q Y hτ
    have hPiece := (hQ.pieces_good X hX).1
    have hPure := prof_partition_pure X q hqX (hPiece.vanish q hqX)
      (hPiece.proper q hqX) (d - 1) (by omega) Y ⟨hcarrier, hmem⟩
    exact ⟨hPure.1, by omega⟩
  have hUnassignedBound (X : Piece d) (hX : X ∈ Q.pieces) :
      ((X.pts.filter (fun q => τ q = none)).card : ℝ) ≤ ε * X.pts.card := by
    have hPiece := (hQ.pieces_good X hX).1
    have hPieceWidth := (hQ.pieces_good X hX).2
    have hWidthNonneg : 0 ≤ X.width := by
      exact le_trans (le_max_right sB 0) (le_trans hs₀ hPieceWidth)
    have hWidthBudget : sB ≤ X.width := le_trans (le_max_left sB 0) (le_trans hs₀ hPieceWidth)
    have hPieceBudget : PieceGood P θB ξ K X :=
      dprofiles2_pieceGood_mono P X hθoutB hWidthNonneg hPiece
    have hBud := hbudget P X ξ K hξ hξB hK hPieceBudget hWidthBudget
    obtain ⟨hTimeAbs, _, hLast, _⟩ := hBud.1
    let last : Fin d := ⟨d - 1, by omega⟩
    let early : Finset (Fin d) := Finset.univ.filter (fun i => i.val < d - 1)
    have hEarlyCard : early.card ≤ d - 1 := by
      have hinj : Function.Injective
          (fun i : {i : Fin d // i ∈ early} =>
            (⟨i.1.val, (Finset.mem_filter.mp i.2).2⟩ : Fin (d - 1))) := by
        intro i j hij
        have hval : i.1.val = j.1.val := by
          exact congrArg (fun k : Fin (d - 1) => k.val) hij
        exact Subtype.ext (Fin.ext hval)
      have hle := Fintype.card_le_of_injective _ hinj
      simpa using hle
    have hUnion : early ∪ {last} = (Finset.univ : Finset (Fin d)) := by
      ext i
      by_cases hi : i.val < d - 1
      · simp [early, hi]
      · have hlast : i = last := Fin.ext (by simp [last]; omega)
        simp [early, hi, hlast]
    have hDisjoint : Disjoint early ({last} : Finset (Fin d)) := by
      apply Finset.disjoint_left.mpr
      intro i hi hl
      have hiLast : i = last := Finset.mem_singleton.mp hl
      subst i
      have hiLt := (Finset.mem_filter.mp hi).2
      simp [last] at hiLt
    have hSumSplit : (∑ i : Fin d, X.path.time i) =
        (∑ i ∈ early, X.path.time i) + X.path.time last := by
      rw [← hUnion, Finset.sum_union hDisjoint]
      simp
    have hLast' : c ≤ X.path.time last := by simpa [last] using hLast
    have hEarlyBound : (∑ i ∈ early, X.path.time i) ≤ θbud - c := by
      have hTotal := (abs_le.mp hTimeAbs).2
      rw [hSumSplit] at hTotal
      linarith
    let carriersX := dprofiles2ComponentsMeeting (X.path.system (d - 1)) X.pts
    have hcarriersX : ∀ Z ∈ carriersX,
        X.path.IsCarrier (d - 1) Z ∧ ∃ x ∈ X.pts, toC x ∈ Z := by
      intro Z hZ
      have hZ' : Z ∈ dprofiles2ComponentFamily (X.path.system (d - 1)) ∧
          ∃ x ∈ X.pts, toC x ∈ Z := by
        simpa [carriersX, dprofiles2ComponentsMeeting] using hZ
      exact ⟨(dprofiles2_mem_componentFamily _ Z).mp hZ'.1, hZ'.2⟩
    obtain ⟨hdegreeX, _⟩ := hBud.2.1 (d - 1) (by omega) carriersX hcarriersX
    let badLines := carriersX.filter (fun Z => IsLine Z ∧ ¬ IsRealFlat Z)
    have hlinePointCard (Z : AffineVariety d) (hZ : Z ∈ badLines) :
        (X.pts.filter (fun q => toC q ∈ Z)).card ≤ 1 := by
      apply Finset.card_le_one_iff_subsingleton_coe.mpr
      refine ⟨fun q r => ?_⟩
      apply Subtype.ext
      have hq := Finset.mem_filter.mp q.2
      have hr := Finset.mem_filter.mp r.2
      by_contra hqr
      have hZbad := (Finset.mem_filter.mp hZ).2
      exact hZbad.2 (pairSelection_realLine_isRealFlat Z hZbad.1 q.1 r.1 hqr hq.2 hr.2)
    have hdegreeNonneg (Z : AffineVariety d) (hZ : Z ∈ carriersX) :
        0 ≤ (Z.degree : ℝ) := by
      have hirr := (hcarriersX Z hZ).1.isPrime
      have hdeg := AffineVariety.one_le_degree Z hirr.ne_top
      exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1) hdeg)
    have hbadDegreeLe :
        ∑ Z ∈ badLines, (Z.degree : ℝ) ≤ ∑ Z ∈ carriersX, (Z.degree : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by
          intro Z hZ hnot
          exact hdegreeNonneg Z hZ)
    have hbadCardLeDegree :
        (badLines.card : ℝ) ≤ ∑ Z ∈ badLines, (Z.degree : ℝ) := by
      calc
        (badLines.card : ℝ) = ∑ Z ∈ badLines, (1 : ℝ) := by simp
        _ ≤ ∑ Z ∈ badLines, (Z.degree : ℝ) :=
          Finset.sum_le_sum (by
            intro Z hZ
            have hdata := hcarriersX Z ((Finset.mem_filter.mp hZ).1)
            have hdegree := AffineVariety.one_le_degree Z hdata.1.isPrime.ne_top
            exact_mod_cast hdegree)
    have hUnassignedSubset : X.pts.filter (fun q => τ q = none) ⊆
        badLines.biUnion (fun Z => X.pts.filter (fun q => toC q ∈ Z)) := by
      intro q hq
      have hqX := (Finset.mem_filter.mp hq).1
      have hτnone := (Finset.mem_filter.mp hq).2
      have hCand : candidate q := hcandidateOfPiece q X hX hqX
      have hChosen : chosen q = some (Classical.choose hCand) := by
        simp [chosen, hCand]
      have hbad : IsLine (Classical.choose hCand).2 ∧
          ¬ IsRealFlat (Classical.choose hCand).2 := by
        unfold τ at hτnone
        rw [hChosen] at hτnone
        by_cases hbad : IsLine (Classical.choose hCand).2 ∧
            ¬ IsRealFlat (Classical.choose hCand).2
        · exact hbad
        · simp [hbad] at hτnone
      rcases Classical.choose_spec hCand with ⟨hXYpiece, hqXY, hcarrier, hmem⟩
      have hXYeq : (Classical.choose hCand).1 = X := by
        by_contra hne
        have hdis := hQ.pieces_disjoint hXYpiece hX hne
        exact Finset.disjoint_left.mp hdis hqXY hqX
      rw [hXYeq] at hcarrier
      have hZfam : (Classical.choose hCand).2 ∈
          dprofiles2ComponentFamily (X.path.system (d - 1)) := by
        apply (dprofiles2_mem_componentFamily _ (Classical.choose hCand).2).mpr
        change ((Classical.choose hCand).2).ideal ∈ (X.path.system (d - 1)).minimalPrimes
        exact hcarrier
      have hZmeet : ∃ x ∈ X.pts, toC x ∈ (Classical.choose hCand).2 := ⟨q, hqX, hmem⟩
      have hZA : (Classical.choose hCand).2 ∈ carriersX := by
        simp [carriersX, dprofiles2ComponentsMeeting, hZfam, hZmeet]
      have hZbad : (Classical.choose hCand).2 ∈ badLines :=
        Finset.mem_filter.mpr ⟨hZA, hbad⟩
      exact Finset.mem_biUnion.mpr ⟨(Classical.choose hCand).2, hZbad,
        Finset.mem_filter.mpr ⟨hqX, hmem⟩⟩
    have hUnassignedCard :
        ((X.pts.filter (fun q => τ q = none)).card : ℝ) ≤ (badLines.card : ℝ) := by
      calc
        ((X.pts.filter (fun q => τ q = none)).card : ℝ) ≤
            ((badLines.biUnion (fun Z => X.pts.filter (fun q => toC q ∈ Z))).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hUnassignedSubset
        _ ≤ ((∑ Z ∈ badLines, (X.pts.filter (fun q => toC q ∈ Z)).card : ℕ) : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
        _ = ∑ Z ∈ badLines, ((X.pts.filter (fun q => toC q ∈ Z)).card : ℝ) := by simp
        _ ≤ ∑ Z ∈ badLines, (1 : ℝ) :=
              Finset.sum_le_sum (by intro Z hZ; exact_mod_cast hlinePointCard Z hZ)
        _ = (badLines.card : ℝ) := by simp
    have htotalDegree := hUnassignedCard.trans (hbadCardLeDegree.trans
      (hbadDegreeLe.trans hdegreeX))
    have hsumEarly :
        (∑ i ∈ early, X.path.time i) ≤ θbud - c := hEarlyBound
    have hscale := pairSelection_eScale_filter_formula (B := cfgB P) (s := X.width)
      (t := X.path.time) (j := d - 1)
    have hscale' : eScale (cfgB P) X.width X.path.time (d - 1) =
        cfgB P ^ early.card * Real.exp ((∑ i ∈ early, X.path.time i) * X.width) := by
      simpa [early] using hscale
    have hcardEarly : early.card ≤ d - 1 := by
      have hinj : Function.Injective
          (fun i : {i : Fin d // i ∈ early} =>
            (⟨i.1.val, (Finset.mem_filter.mp i.2).2⟩ : Fin (d - 1))) := by
        intro i j hij
        have hval : i.1.val = j.1.val := by
          have h := congrArg (fun k : Fin (d - 1) => k.val) hij
          simpa using h
        exact Subtype.ext (Fin.ext hval)
      have hle := Fintype.card_le_of_injective _ hinj
      simpa using hle
    have hpowEarly : cfgB P ^ early.card ≤ cfgB P ^ (d - 1) :=
      pow_le_pow_right₀ hBge hcardEarly
    have hsumExp :
        Real.exp ((∑ i ∈ early, X.path.time i) * X.width) *
            Real.exp (θbud * X.width) ≤
          Real.exp ((2 * θbud - c) * X.width) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcoef : (∑ i ∈ early, X.path.time i) + θbud ≤ 2 * θbud - c := by
        linarith
      have h := mul_le_mul_of_nonneg_right hcoef hWidthNonneg
      calc
        (∑ i ∈ early, X.path.time i) * X.width + θbud * X.width =
            ((∑ i ∈ early, X.path.time i) + θbud) * X.width := by ring
        _ ≤ (2 * θbud - c) * X.width := h
    have hscaleBound :
        eScale (cfgB P) X.width X.path.time (d - 1) * Real.exp (θbud * X.width) ≤
          cfgB P ^ (d - 1) * Real.exp ((2 * θbud - c) * X.width) := by
      rw [hscale']
      calc
        cfgB P ^ early.card *
            Real.exp ((∑ i ∈ early, X.path.time i) * X.width) *
              Real.exp (θbud * X.width) ≤
            cfgB P ^ early.card * Real.exp ((2 * θbud - c) * X.width) := by
              calc
                _ = cfgB P ^ early.card *
                    (Real.exp ((∑ i ∈ early, X.path.time i) * X.width) *
                      Real.exp (θbud * X.width)) := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left hsumExp (by positivity)
        _ ≤ cfgB P ^ (d - 1) * Real.exp ((2 * θbud - c) * X.width) := by
              exact mul_le_mul_of_nonneg_right hpowEarly (Real.exp_nonneg _)
    have hthetaCoeff : 2 * θbud + θout ≤ c := by
      dsimp [θbud]
      have hθoutc : θout ≤ c / 8 := by
        dsimp [θout]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      nlinarith only [hc, hθoutc]
    have hExpFinal : Real.exp ((2 * θbud - c) * X.width) ≤ Real.exp (-θout * X.width) := by
      apply Real.exp_le_exp.mpr
      have hcoef : 2 * θbud - c ≤ -θout := by linarith only [hthetaCoeff]
      exact mul_le_mul_of_nonneg_right hcoef hWidthNonneg
    have hpowBudget : cfgB P ^ (d - 1) ≤ ε * cfgB P ^ d := by
      calc
        cfgB P ^ (d - 1) = cfgB P ^ (d - 1) * 1 := by simp
        _ ≤ cfgB P ^ (d - 1) * (ε * cfgB P) :=
          mul_le_mul_of_nonneg_left hεB (by positivity)
        _ = ε * cfgB P ^ d := by
          calc
            cfgB P ^ (d - 1) * (ε * cfgB P) =
                ε * (cfgB P ^ (d - 1) * cfgB P) := by ring
            _ = ε * cfgB P ^ ((d - 1) + 1) := by rw [pow_succ]
            _ = ε * cfgB P ^ d := by
              rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
    have hscaleN :
        eScale (cfgB P) X.width X.path.time (d - 1) * Real.exp (θbud * X.width) ≤
          ε * cfgN P * Real.exp (-θout * X.width) := by
      calc
        _ ≤ cfgB P ^ (d - 1) * Real.exp ((2 * θbud - c) * X.width) := hscaleBound
        _ ≤ cfgB P ^ (d - 1) * Real.exp (-θout * X.width) :=
          mul_le_mul_of_nonneg_left hExpFinal (by positivity)
        _ ≤ ε * cfgB P ^ d * Real.exp (-θout * X.width) :=
          mul_le_mul_of_nonneg_right hpowBudget (Real.exp_nonneg _)
        _ = ε * cfgN P * Real.exp (-θout * X.width) := by rw [hBpow]
    calc
      ((X.pts.filter (fun q => τ q = none)).card : ℝ) ≤
          eScale (cfgB P) X.width X.path.time (d - 1) * Real.exp (θbud * X.width) := htotalDegree
      _ ≤ ε * cfgN P * Real.exp (-θout * X.width) := hscaleN
      _ ≤ ε * X.pts.card := by
        have hsize := hPiece.size
        have hmul := mul_le_mul_of_nonneg_left hsize hε.le
        calc
          ε * cfgN P * Real.exp (-θout * X.width) =
              ε * (cfgN P * Real.exp (-θout * X.width)) := by ring
          _ ≤ ε * X.pts.card := by simpa [mul_assoc] using hmul
  have hTerminal : TerminalAssignment Q ε τ := by
    refine ⟨?_, ?_, ?_⟩
    · intro X hX q hq Y hτ
      obtain ⟨X', hX', hq', hcarrier, hmem⟩ := hτCarrierFor q Y hτ
      by_cases hEq : X' = X
      · subst X'
        exact ⟨hcarrier, hmem⟩
      · have hdis := hQ.pieces_disjoint hX' hX hEq
        exact False.elim ((Finset.disjoint_left.mp hdis) hq' hq)
    · intro q Y hτ hline
      by_contra hreal
      exact hτNonbad q Y hτ ⟨hline, hreal⟩
    · intro X hX
      exact hUnassignedBound X hX
  have hgeoPairs := hgeo P hNgeo hM hcap Cf hCf carriers S hAssignment hcarriersCurve
    (by
      intro Y hY hline
      obtain ⟨q, hq, hτ⟩ := hcarrierMem Y hY
      exact hTerminal.realLines q Y hτ hline)
  have hpairSet :
      (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
        ∃ Y, τ pq.2 = some Y ∧ ProjectsInto (Cf pq.1) pq.1 Y) =
      terminalPairs P Cf carriers S := by
    ext pq
    rcases pq with ⟨p, q⟩
    simp only [terminalPairs, terminalPairsSel, Finset.mem_filter, Finset.mem_product]
    constructor
    · intro h
      rcases h with ⟨hpq, hrest⟩
      rcases hpq with ⟨hp, hq⟩
      rcases hrest with ⟨hne, hex⟩
      rcases hex with ⟨Y, hτ, hproj⟩
      refine ⟨⟨hp, hq⟩, ⟨hne, Y, hYmem q hq Y hτ, trivial,
        Finset.mem_filter.mpr ⟨hq, hτ⟩, hproj⟩⟩
    · intro h
      rcases h with ⟨hpq, hrest⟩
      rcases hpq with ⟨hp, hq⟩
      rcases hrest with ⟨hne, hex⟩
      rcases hex with ⟨Y, hY, hrest⟩
      rcases hrest with ⟨_, hqS, hproj⟩
      have hτ : τ q = some Y := (Finset.mem_filter.mp hqS).2
      exact ⟨⟨hp, hq⟩, ⟨hne, Y, hτ, hproj⟩⟩
  refine ⟨τ, hTerminal, ?_⟩
  rw [hpairSet]
  exact hgeoPairs

set_option maxHeartbeats 1000000 in
/-- `prof:pair-selection` (`profiles.tex:515–544`), finitary form. For every precision `ρ`, piece
tolerance `θ`, margin `ξ`, degree constant `K` and minimal width `s₀`, there are `η, N₀` such
that: if `|P| ≥ N₀`, `M ≤ η A`, the proper-flat cap holds, `0 < δ ≤ η`, and directional families
`C_p` of degree `δ N / A` cover all but `η N (N - 1)` ordered pairs in some orientation, then
there are a good partition (tolerance `θ`), a global terminal assignment, a reference profile
`t`, and source/target pools from the partition satisfying a window alternative, with recorded
times within `ρ` of `t`, such that at least `(1/2 - ρ) n_x n_y` ordered pairs of the product are
selected incidences. -/
theorem prof_pair_selection (d : ℕ) (hd : 3 ≤ d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ρ > 0, ∀ θ > 0, ∀ ξ > 0, ∀ K ≥ 1, ∀ s₀ : ℝ, ∃ η > 0, ∃ N₀ : ℕ,
      ∀ P : Finset (Pt d), N₀ ≤ P.card → cfgM P ≤ η * cfgA P → RealFlatCap P c₀ →
      ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∀ Cf : Pt d → ProjectiveFamily.Family d,
        (∀ p ∈ P, IsDirectionalFamily (Cf p) ∧
          (ProjectiveFamily.degree (Cf p) : ℝ) ≤ δ * cfgN P / cfgA P) →
        (1 - η) * cfgN P * (cfgN P - 1) ≤ ((coveredPairs P Cf).card : ℝ) →
        ∃ (Q : Partition d) (τ : Pt d → Option (AffineVariety d))
          (plx ply : Finset (Piece d)) (t : Fin d → ℝ),
          Q.Good P δ θ ξ K s₀ ∧ TerminalAssignment Q θ τ ∧
          plx ⊆ Q.pieces ∧ ply ⊆ Q.pieces ∧ plx.Nonempty ∧ ply.Nonempty ∧
          (∀ X ∈ plx ∪ ply, ∀ i, |X.path.time i - t i| ≤ ρ) ∧
          WindowAlternative P δ ρ plx ply ∧
          (1 / 2 - ρ) * (poolPts plx).card * (poolPts ply).card ≤
            (((poolPts plx ×ˢ poolPts ply).filter (fun pq =>
              SelectedIncidence P Cf τ ρ pq.1 pq.2)).card : ℝ) := by
  intro ρ hρ θ hθ ξ hξ K hK s₀
  obtain ⟨a, ha, hfinite⟩ := pair_selection_finite d ρ hρ
  obtain ⟨C, hC, hcore⟩ := pair_selection_core d hd
  let ε : ℝ := min (a / 16) (θ / 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεa : ε ≤ a / 16 := min_le_left _ _
  have hεθ : ε ≤ θ := (min_le_right _ _).trans (by linarith)
  obtain ⟨θt, hθt, ηt, hηt, ξt, hξt, st, Nt, hterminal⟩ :=
    pair_selection_terminal d hd c₀ hc₀ ε hε
  let θp : ℝ := min θ (min θt (min (1 / 8) (1 / (128 * (C + 1)))))
  let ξp : ℝ := min ξ ξt
  let sp : ℝ := max s₀ (max st 1)
  have hθp : 0 < θp := by dsimp [θp]; positivity
  have hξp : 0 < ξp := by dsimp [ξp]; positivity
  have hθpθ : θp ≤ θ := min_le_left _ _
  have hθpt : θp ≤ θt := (min_le_right _ _).trans (min_le_left _ _)
  have hθp8 : θp ≤ 1 / 8 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hθpC : θp ≤ 1 / (128 * (C + 1)) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hξpx : ξp ≤ ξ := min_le_left _ _
  have hξpt : ξp ≤ ξt := min_le_right _ _
  have hsp1 : 1 ≤ sp := (le_max_right _ _).trans (le_max_right _ _)
  have hspt : st ≤ sp := (le_max_left _ _).trans (le_max_right _ _)
  have hsp0 : s₀ ≤ sp := le_max_left _ _
  obtain ⟨ηp, hηp, Np, hpartition⟩ := prof_partition d hd θp hθp ξp hξp K hK sp
  obtain ⟨CL, hCL, hlight⟩ := pair_selection_lightlines d (ci_st_rich d)
  obtain ⟨Nl, hthreshold⟩ := pair_selection_light_threshold d (by omega) ρ c₀ CL ε
    hρ hc₀ hCL hε
  let η : ℝ := min ηp (min ηt (min (a / 16) (1 / 64)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηp' : η ≤ ηp := min_le_left _ _
  have hηt' : η ≤ ηt := (min_le_right _ _).trans (min_le_left _ _)
  have hηa : η ≤ a / 16 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hη64 : η ≤ 1 / 64 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  let N₀ : ℕ := max Np (max Nt (max Nl (max 64 (Nat.ceil (16 / a)))))
  refine ⟨η, hη, N₀, ?_⟩
  intro P hN₀ hM hcap δ hδ hδη Cf hCf hcover
  have hNp : Np ≤ P.card := (le_max_left _ _).trans hN₀
  have hNt : Nt ≤ P.card := ((le_max_left _ _).trans (le_max_right _ _)).trans hN₀
  have hNl : Nl ≤ P.card :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN₀
  have hN64 : 64 ≤ P.card :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans hN₀
  have hNceil : Nat.ceil (16 / a) ≤ P.card :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans hN₀
  have hN1 : 1 ≤ P.card := by omega
  have hNpos : 0 < cfgN P := by unfold cfgN; exact_mod_cast (by omega : 0 < P.card)
  have hN0 : 0 ≤ cfgN P := hNpos.le
  have hA0 : 0 ≤ cfgA P := by unfold cfgA; positivity
  have hNlarge : 64 ≤ cfgN P := by
    change (64 : ℝ) ≤ (P.card : ℝ)
    exact_mod_cast hN64
  have hNtail : cfgN P ≤ a / 16 * cfgN P ^ 2 := by
    have ht : 16 / a ≤ cfgN P :=
      (Nat.le_ceil _).trans (by
        change (Nat.ceil (16 / a) : ℝ) ≤ (P.card : ℝ)
        exact_mod_cast hNceil)
    have hm := (div_le_iff₀ ha).mp ht
    have hm' := mul_le_mul_of_nonneg_right hm hN0
    nlinarith
  have hMpart : cfgM P ≤ ηp * cfgA P :=
    hM.trans (mul_le_mul_of_nonneg_right hηp' hA0)
  obtain ⟨Q, hQ⟩ := hpartition P hNp hMpart δ hδ.le (hδη.trans hηp')
  have hcover' : (1 - η) * (P.card : ℝ) * ((P.card : ℝ) - 1) ≤
      (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
        (DirIn (Cf pq.1) pq.1 pq.2 ∨ DirIn (Cf pq.2) pq.2 pq.1))).card : ℝ) := by
    simpa only [cfgN, coveredPairs] using hcover
  have hfib : ∀ p ∈ Q.core,
      ((Q.core.filter (fun q => DirIn (Cf p) p q)).card : ℝ) ≤ C * θp * cfgN P := by
    intro p hp
    obtain ⟨hdir, hdeg⟩ := hCf p (hQ.core_subset hp)
    calc
      _ ≤ C * (ProjectiveFamily.degree (Cf p) : ℝ) * (Q.coreDeg : ℝ) ^ 2 :=
        hcore Q.core Q.coreDeg hQ.core_isolated p (Cf p) hdir
      _ ≤ C * (δ * cfgN P / cfgA P) * (Q.coreDeg : ℝ) ^ 2 := by gcongr
      _ = C * (δ * cfgN P / cfgA P * (Q.coreDeg : ℝ) ^ 2) := by ring
      _ ≤ C * (θp * cfgN P) := mul_le_mul_of_nonneg_left hQ.core_degree hC.le
      _ = _ := by ring
  have hcoreCount := pair_selection_core_count P Q.core hQ.core_subset
    (fun p q => DirIn (Cf p) p q) (C * θp * cfgN P) η hη.le hN1 (by
      convert hcover' using 1 <;> congr 2 <;> ext pq <;>
        simp only [Finset.mem_filter, Finset.mem_product]) (by
      intro p hp
      convert hfib p hp using 1 <;> congr 2 <;> ext q <;>
        simp only [Finset.mem_filter])
  have hcoreN : (Q.core.card : ℝ) ≤ cfgN P := by
    change (Q.core.card : ℝ) ≤ (P.card : ℝ)
    exact_mod_cast Finset.card_le_card hQ.core_subset
  have hcoreSmall : (Q.core.card : ℝ) ≤ cfgN P / 4 :=
    pair_selection_small_core (cfgN P) Q.core.card C θp η hNlarge (Nat.cast_nonneg _)
      hcoreN hC hθp hθpC hη64 (by simpa only [cfgN] using hcoreCount)
  have hpoolCard : ((poolPts Q.pieces).card : ℝ) =
      ∑ X ∈ Q.pieces, (X.pts.card : ℝ) := by
    dsimp [poolPts]
    exact_mod_cast Finset.card_biUnion hQ.pieces_disjoint
  have hretained : cfgN P / 2 ≤ (poolPts Q.pieces).card := by
    have hdis := hQ.discard
    rw [← hpoolCard] at hdis
    have hsmall := mul_le_mul_of_nonneg_right hθp8 hN0
    linarith only [hdis, hsmall, hcoreSmall]
  have hQt : Q.Good P δ θt ξp K sp := pair_selection_good_mono P Q δ θp θt ξp ξp
    K sp sp hθpt le_rfl le_rfl (by linarith) hQ
  have hMt : cfgM P ≤ ηt * cfgA P :=
    hM.trans (mul_le_mul_of_nonneg_right hηt' hA0)
  have hCft : ∀ p ∈ P, IsDirectionalFamily (Cf p) ∧
      (ProjectiveFamily.degree (Cf p) : ℝ) ≤ ηt * cfgN P / cfgA P := by
    intro p hp
    refine ⟨(hCf p hp).1, (hCf p hp).2.trans ?_⟩
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hδη.trans hηt') hN0) hA0
  obtain ⟨τ, hτ, hT⟩ := hterminal P Q δ ξp K sp hNt hMt hcap hξp hξpt hK hspt hQt Cf hCft
  obtain ⟨hH, htail⟩ := hthreshold P hNl
  have hlineCap : ∀ ℓ : AffineSubspace ℝ (Pt d), IsRealLine ℓ →
      (occ P ℓ : ℝ) ≤ cfgN P * cfgB P ^ (-c₀) := by
    intro ℓ hℓ
    apply hcap ℓ
    intro htop
    change Module.finrank ℝ ℓ.direction = 1 at hℓ
    rw [htop, AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace,
      Fintype.card_fin] at hℓ
    omega
  have hB0 : 0 ≤ cfgB P := by unfold cfgB; positivity
  have hL := hlight P (cfgB P ^ ρ) (cfgN P * cfgB P ^ (-c₀)) hH
    (mul_nonneg hN0 (Real.rpow_nonneg hB0 _)) hlineCap
  have hLsmall : (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
      cfgB P ^ ρ < (occ P (affineSpan ℝ {pq.1, pq.2}) : ℝ))).card : ℝ) ≤ ε * cfgN P ^ 2 := by
    calc
      _ ≤ CL * ((P.card : ℝ) ^ 2 / cfgB P ^ ρ +
          P.card * (cfgN P * cfgB P ^ (-c₀))) := hL
      _ = (CL * (1 / cfgB P ^ ρ + cfgB P ^ (-c₀))) * cfgN P ^ 2 := by
        unfold cfgN; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right htail (sq_nonneg _)
  have hdeleted := pair_selection_delete_count P (fun p q => DirIn (Cf p) p q)
    (fun p q => ∃ Y, τ q = some Y ∧ ProjectsInto (Cf p) p Y)
    (fun p q => cfgB P ^ ρ < (occ P (affineSpan ℝ {p, q}) : ℝ))
    η ε ε hη.le hN1 (by
      convert hcover' using 1 <;> congr 2 <;> ext pq <;>
        simp only [Finset.mem_filter, Finset.mem_product]) (by
      convert hT using 1 <;> congr 2 <;> ext pq <;>
        simp only [Finset.mem_filter, Finset.mem_product]) (by
      convert hLsmall using 1 <;> congr 2 <;> ext pq <;>
        simp only [Finset.mem_filter, Finset.mem_product])
  have hselected : (((P ×ˢ P).filter (fun pq =>
      ¬ SelectedIncidence P Cf τ ρ pq.1 pq.2 ∧
      ¬ SelectedIncidence P Cf τ ρ pq.2 pq.1)).card : ℝ) ≤
        (η + 2 * ε + 2 * ε) * cfgN P ^ 2 + cfgN P := by
    simpa [SelectedIncidence, not_exists, not_and, not_lt, cfgN] using hdeleted
  have hmissing : (((P ×ˢ P).filter (fun pq =>
      ¬ SelectedIncidence P Cf τ ρ pq.1 pq.2 ∧
      ¬ SelectedIncidence P Cf τ ρ pq.2 pq.1)).card : ℝ) ≤ a * cfgN P ^ 2 := by
    have hcoef : η + 2 * ε + 2 * ε ≤ 5 * a / 16 := by linarith
    have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (cfgN P))
    have hr : (a / 16) * cfgN P ^ 2 ≤ (11 * a / 16) * cfgN P ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith
    nlinarith only [hselected, hm, hNtail, hr]
  obtain ⟨plx, ply, t, hx, hy, hxn, hyn, hclose, hwindow, hdense⟩ :=
    hfinite P Q δ θp ξp K sp (SelectedIncidence P Cf τ ρ) hNpos hδ
      (hδη.trans (hηa.trans (by linarith))) (by linarith) hsp1 hQ hretained hmissing
  refine ⟨Q, τ, plx, ply, t, ?_, ?_, hx, hy, hxn, hyn, hclose, hwindow, hdense⟩
  · exact pair_selection_good_mono P Q δ θp θ ξp ξ K sp s₀ hθpθ hξpx hsp0
      (by linarith) hQ
  · refine { hτ with unassigned := ?_ }
    intro X hX
    exact (hτ.unassigned X hX).trans
      (mul_le_mul_of_nonneg_right hεθ (Nat.cast_nonneg _))

end

end TrackD
end DistinctDistances
