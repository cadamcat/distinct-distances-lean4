import DistinctDistances.TrackE.SparseCones
import DistinctDistances.TrackE.FlatCaps
import DistinctDistances.TrackD.Profiles.PairSelection
import DistinctDistances.TrackE.RadiusClass
import DistinctDistances.TrackE.DirectionFibers
import DistinctDistances.TrackE.RadiusFibers
import DistinctDistances.TrackE.SmallSpan
import DistinctDistances.TrackE.DirectionInduction

/-!
# `red:directions`: a symmetric selection of directions (`reduction.tex:98-202`)

Uniform single-configuration forms. `occ P F` is the number of points of `P` on `F`.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

open Classical in
/-- Number of points of `P` on a real affine subspace. -/
def occ (P : Finset (RPoint d)) (F : AffineSubspace ℝ (RPoint d)) : ℕ :=
  (P.filter (· ∈ F)).card

open Classical in
/-- red:directions.richlines (`reduction.tex:111-124`, from the rich-line form of `ci:st` in
`ℝ^d`): the ordered pairs of distinct points whose line holds more than `H ≥ 2` points number at
most `C (N^2/H + N L_max)`, `L_max` a bound on the occupancy of lines through two points. -/
theorem card_pairs_on_rich_lines :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (RPoint d)) (H Lmax : ℝ), 2 ≤ H → 0 ≤ Lmax →
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → (occ P (affineSpan ℝ {p, q}) : ℝ) ≤ Lmax) →
      ((P.offDiag.filter fun e => H < (occ P (affineSpan ℝ {e.1, e.2}) : ℝ)).card : ℝ) ≤
        C * ((P.card : ℝ) ^ 2 / H + P.card * Lmax) := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := TrackD.pair_selection_lightlines d (TrackD.ci_st_rich d)
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro P H Lmax hH hLmax hpair
  let R := P.offDiag.filter fun e => H < (occ P (affineSpan ℝ {e.1, e.2}) : ℝ)
  by_cases hRzero : R.card = 0
  · have hRcast : (R.card : ℝ) = 0 := by simp [hRzero]
    rw [hRcast]
    positivity
  · have hRpos : 0 < R.card := Nat.pos_of_ne_zero hRzero
    obtain ⟨e, he⟩ := Finset.card_pos.mp hRpos
    rcases Finset.mem_filter.mp he with ⟨heOff, heRich⟩
    rcases Finset.mem_offDiag.mp heOff with ⟨heP, heQ, heNe⟩
    have hLmaxLarge : H < Lmax := lt_of_lt_of_le heRich (hpair e.1 heP e.2 heQ heNe)
    have hLmaxOne : 1 ≤ Lmax := by linarith [hH]
    have hlineOcc : ∀ ℓ : AffineSubspace ℝ (RPoint d), TrackD.IsRealLine ℓ →
        (TrackD.occ P ℓ : ℝ) ≤ Lmax + 1 := by
      intro ℓ hℓ
      let X := P.filter (· ∈ ℓ)
      change (X.card : ℝ) ≤ Lmax + 1
      by_cases hsmall : X.card ≤ 1
      · have hsmallReal : (X.card : ℝ) ≤ 1 := by exact_mod_cast hsmall
        linarith
      · have hgt : 1 < X.card := by omega
        rcases Finset.one_lt_card_iff.mp hgt with ⟨p, q, hpX, hqX, hpq⟩
        have hpmem := (Finset.mem_filter.mp hpX).2
        have hqmem := (Finset.mem_filter.mp hqX).2
        have hpP := (Finset.mem_filter.mp hpX).1
        have hqP := (Finset.mem_filter.mp hqX).1
        let Lpq : AffineSubspace ℝ (RPoint d) := affineSpan ℝ ({p, q} : Set (RPoint d))
        have hle : Lpq ≤ ℓ := by
          exact affineSpan_pair_le_of_mem_of_mem hpmem hqmem
        have hdirle : Lpq.direction ≤ ℓ.direction := AffineSubspace.direction_le hle
        have hdirrank : Module.finrank ℝ Lpq.direction = 1 := by
          dsimp [Lpq]
          rw [direction_affineSpan, vectorSpan_pair]
          have hv : p -ᵥ q ≠ (0 : RPoint d) := by
            intro hv
            exact hpq (vsub_eq_zero_iff_eq.mp hv)
          exact finrank_span_singleton hv
        have hℓrank : Module.finrank ℝ ℓ.direction = 1 := hℓ
        have hdireq : Lpq.direction = ℓ.direction :=
          Submodule.eq_of_le_of_finrank_eq hdirle (by rw [hdirrank, hℓrank])
        have hEq : Lpq = ℓ :=
          AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdireq
            ⟨p, by exact left_mem_affineSpan_pair ℝ p q⟩ hle
        have hpairBound := hpair p hpP q hqP hpq
        have hlineBound : (TrackD.occ P ℓ : ℝ) ≤ Lmax := by
          simpa [TrackD.occ, occ, Lpq, hEq] using hpairBound
        change (X.card : ℝ) ≤ Lmax at hlineBound
        linarith
    have hcount' := hcount P H (Lmax + 1) hH (by linarith) hlineOcc
    have hR_eq : R = (P ×ˢ P).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ H < (TrackD.occ P (affineSpan ℝ {pq.1, pq.2}) : ℝ)) := by
      ext e
      simp only [R, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
      simp [occ, TrackD.occ]
      simp only [and_assoc]
    have hcountR : (R.card : ℝ) ≤ C₀ *
        ((P.card : ℝ) ^ 2 / H + P.card * (Lmax + 1)) := by
      simpa [hR_eq] using hcount'
    have hN : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
    have hdiv : 0 ≤ (P.card : ℝ) ^ 2 / H := div_nonneg (sq_nonneg _) (by linarith)
    have hterm : (P.card : ℝ) ^ 2 / H + P.card * (Lmax + 1) ≤
        2 * ((P.card : ℝ) ^ 2 / H + P.card * Lmax) := by
      have hmul := mul_le_mul_of_nonneg_left (by linarith : Lmax + 1 ≤ 2 * Lmax) hN
      nlinarith
    calc
      (R.card : ℝ) ≤ C₀ * ((P.card : ℝ) ^ 2 / H + P.card * (Lmax + 1)) := hcountR
      _ ≤ C₀ * (2 * ((P.card : ℝ) ^ 2 / H + P.card * Lmax)) :=
        mul_le_mul_of_nonneg_left hterm (le_of_lt hC₀)
      _ = 2 * C₀ * ((P.card : ℝ) ^ 2 / H + P.card * Lmax) := by ring

open Classical in
/-- red:directions.greedy (`reduction.tex:126-133`): greedy removal in one star. For a finite set
`X` of partners of `p` and a threshold `t > 0` there is a directional family `Γ` with
`t · deg Γ ≤ |X|` such that every irreducible curve spanning at most a plane contains at most
`t · deg γ` partners whose direction is not on `Γ`. -/
theorem exists_greedy_family (p : RPoint d) (X : Finset (RPoint d)) (hp : p ∉ X) (t : ℝ)
    (ht : 0 < t) :
    ∃ Γ : ProjectiveFamily.Family d, IsDirectionalFamily Γ ∧
      t * (ProjectiveFamily.degree Γ : ℝ) ≤ X.card ∧
      ∀ γ : ProjectiveVariety d, γ.IsIrreducible → γ.dimension = 1 → SpansAtMostPlane γ →
        ((X.filter fun q => DirMem γ p q ∧ ¬ ∃ γ' ∈ Γ, DirMem γ' p q).card : ℝ) ≤
          t * (γ.degree : ℝ) := by
  classical
  have hdeg1 : ∀ γ : ProjectiveVariety d, γ.IsIrreducible → (1 : ℝ) ≤ (γ.degree : ℝ) := by
    intro γ hirr
    have hne : γ.affineCone.ideal ≠ ⊤ := hirr.ne_top
    have h1 : (1 : ℚ) ≤ γ.affineCone.degree := AffineVariety.one_le_degree _ hne
    rw [ProjectiveVariety.degree_cone] at h1
    exact_mod_cast h1
  have key : ∀ k : ℕ, ∀ Γ₀ : Finset (ProjectiveVariety d), IsDirectionalFamily Γ₀ →
      t * (ProjectiveFamily.degree Γ₀ : ℝ) ≤
        ((X.filter fun q => ∃ γ ∈ Γ₀, DirMem γ p q).card : ℝ) →
      ((X.filter fun q => ¬∃ γ ∈ Γ₀, DirMem γ p q).card) ≤ k →
      ∃ Γ : Finset (ProjectiveVariety d), Γ₀ ⊆ Γ ∧ IsDirectionalFamily Γ ∧
        t * (ProjectiveFamily.degree Γ : ℝ) ≤
          ((X.filter fun q => ∃ γ ∈ Γ, DirMem γ p q).card : ℝ) ∧
        ∀ γ : ProjectiveVariety d, γ.IsIrreducible → γ.dimension = 1 → SpansAtMostPlane γ →
          ((X.filter fun q => DirMem γ p q ∧ ¬∃ γ' ∈ Γ, DirMem γ' p q).card : ℝ) ≤
            t * (γ.degree : ℝ) := by
    intro k
    induction k with
    | zero =>
      intro Γ₀ hdir₀ hdeg₀ hsmall
      by_cases hviol : ∃ γ : ProjectiveVariety d, γ.IsIrreducible ∧ γ.dimension = 1 ∧
          SpansAtMostPlane γ ∧ t * (γ.degree : ℝ) <
            ((X.filter fun q => DirMem γ p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q).card : ℝ)
      · obtain ⟨γs, hirr_s, -, -, hlt_s⟩ := hviol
        exfalso
        have hpos : (0 : ℝ) < t * (γs.degree : ℝ) := by
          have h1 := hdeg1 γs hirr_s
          have hle : t * 1 ≤ t * (γs.degree : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt ht)
          linarith
        have hsub : (X.filter fun q => DirMem γs p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q) ⊆
            (X.filter fun q => ¬∃ γ ∈ Γ₀, DirMem γ p q) := by
          intro q hq
          obtain ⟨hqX, -, hn⟩ := Finset.mem_filter.mp hq
          exact Finset.mem_filter.mpr ⟨hqX, hn⟩
        have h0 : (X.filter fun q => DirMem γs p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q).card = 0 :=
          Nat.le_zero.mp (le_trans (Finset.card_le_card hsub) hsmall)
        rw [h0, Nat.cast_zero] at hlt_s
        linarith
      · refine ⟨Γ₀, Finset.Subset.refl _, hdir₀, hdeg₀, fun γ hirr hdim hspan => ?_⟩
        exact le_of_not_gt (fun hlt => hviol ⟨γ, hirr, hdim, hspan, hlt⟩)
    | succ k ih =>
      intro Γ₀ hdir₀ hdeg₀ hsmall
      by_cases hviol : ∃ γ : ProjectiveVariety d, γ.IsIrreducible ∧ γ.dimension = 1 ∧
          SpansAtMostPlane γ ∧ t * (γ.degree : ℝ) <
            ((X.filter fun q => DirMem γ p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q).card : ℝ)
      · obtain ⟨γs, hirr_s, hdim_s, hspan_s, hlt_s⟩ := hviol
        have hpos : (0 : ℝ) < t * (γs.degree : ℝ) := by
          have h1 := hdeg1 γs hirr_s
          have hle : t * 1 ≤ t * (γs.degree : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt ht)
          linarith
        have hnotmem : γs ∉ Γ₀ := by
          intro hmem
          have hempty : (X.filter fun q =>
              DirMem γs p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro q hq h
            exact h.2 ⟨γs, hmem, h.1⟩
          rw [hempty, Finset.card_empty, Nat.cast_zero] at hlt_s
          linarith
        have hC₁ : (X.filter fun q => ∃ γ ∈ insert γs Γ₀, DirMem γ p q) =
            (X.filter fun q => ∃ γ ∈ Γ₀, DirMem γ p q) ∪
              (X.filter fun q => DirMem γs p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q) := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hqX, γ, hγmem, hγq⟩
            rcases Finset.mem_insert.mp hγmem with rfl | hmem
            · by_cases hcov : ∃ γ' ∈ Γ₀, DirMem γ' p q
              · exact Or.inl ⟨hqX, hcov⟩
              · exact Or.inr ⟨hqX, hγq, hcov⟩
            · exact Or.inl ⟨hqX, γ, hmem, hγq⟩
          · rintro (⟨hqX, hcov⟩ | ⟨hqX, hmem, -⟩)
            · obtain ⟨γ, hγmem, hγq⟩ := hcov
              exact ⟨hqX, γ, Finset.mem_insert_of_mem hγmem, hγq⟩
            · exact ⟨hqX, γs, Finset.mem_insert_self _ _, hmem⟩
        have hdisj : Disjoint (X.filter fun q => ∃ γ ∈ Γ₀, DirMem γ p q)
            (X.filter fun q => DirMem γs p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q) := by
          apply Finset.disjoint_left.mpr
          intro q hqC hqR
          exact ((Finset.mem_filter.mp hqR).2.2) ((Finset.mem_filter.mp hqC).2)
        have hsum : ProjectiveFamily.degree (insert γs Γ₀) =
            γs.degree + ProjectiveFamily.degree Γ₀ :=
          Finset.sum_insert hnotmem
        have hdeg₁ : t * (ProjectiveFamily.degree (insert γs Γ₀) : ℝ) ≤
            ((X.filter fun q => ∃ γ ∈ insert γs Γ₀, DirMem γ p q).card : ℝ) := by
          have e1 : t * (ProjectiveFamily.degree (insert γs Γ₀) : ℝ)
              = t * (ProjectiveFamily.degree Γ₀ : ℝ) + t * (γs.degree : ℝ) := by
            rw [hsum]
            push_cast
            ring
          have e2 : ((X.filter fun q => ∃ γ ∈ insert γs Γ₀, DirMem γ p q).card : ℝ)
              = ((X.filter fun q => ∃ γ ∈ Γ₀, DirMem γ p q).card : ℝ) +
                ((X.filter fun q => DirMem γs p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q).card : ℝ) := by
            rw [hC₁, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
          rw [e1, e2]
          exact add_le_add hdeg₀ (le_of_lt hlt_s)
        have hdir₁ : IsDirectionalFamily (insert γs Γ₀) := by
          intro γ hγ
          rcases Finset.mem_insert.mp hγ with rfl | hmem
          · exact ⟨hirr_s, hdim_s, hspan_s⟩
          · exact hdir₀ γ hmem
        have hRpos : 0 < (X.filter fun q =>
            DirMem γs p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q).card := by
          have hlt : (0 : ℝ) <
              ((X.filter fun q => DirMem γs p q ∧ ¬∃ γ' ∈ Γ₀, DirMem γ' p q).card : ℝ) :=
            lt_trans hpos hlt_s
          exact_mod_cast hlt
        obtain ⟨q₀, hq₀mem⟩ := Finset.card_pos.mp hRpos
        obtain ⟨hq₀X, hq₀dir, hq₀nmem⟩ := Finset.mem_filter.mp hq₀mem
        have hq₀RHS : q₀ ∈ X.filter fun q => ¬∃ γ ∈ Γ₀, DirMem γ p q :=
          Finset.mem_filter.mpr ⟨hq₀X, hq₀nmem⟩
        have hq₀nLHS : q₀ ∉ X.filter fun q => ¬∃ γ ∈ insert γs Γ₀, DirMem γ p q := by
          intro hcon
          obtain ⟨-, hn⟩ := Finset.mem_filter.mp hcon
          exact hn ⟨γs, Finset.mem_insert_self _ _, hq₀dir⟩
        have hstrict : (X.filter fun q => ¬∃ γ ∈ insert γs Γ₀, DirMem γ p q) ⊂
            (X.filter fun q => ¬∃ γ ∈ Γ₀, DirMem γ p q) := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨?_, ?_⟩
          · intro q hq
            obtain ⟨hqX, hn⟩ := Finset.mem_filter.mp hq
            apply Finset.mem_filter.mpr
            refine ⟨hqX, ?_⟩
            rintro ⟨γ, hγmem, hγq⟩
            exact hn ⟨γ, Finset.mem_insert_of_mem hγmem, hγq⟩
          · intro heq
            exact hq₀nLHS (heq.symm ▸ hq₀RHS)
        have hle : ((X.filter fun q => ¬∃ γ ∈ insert γs Γ₀, DirMem γ p q).card) ≤ k :=
          Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.card_lt_card hstrict) hsmall)
        obtain ⟨Γ, hsub, hdir, hdegC, hres⟩ := ih _ hdir₁ hdeg₁ hle
        exact ⟨Γ, (Finset.subset_insert _ _).trans hsub, hdir, hdegC, hres⟩
      · refine ⟨Γ₀, Finset.Subset.refl _, hdir₀, hdeg₀, fun γ hirr hdim hspan => ?_⟩
        exact le_of_not_gt (fun hlt => hviol ⟨γ, hirr, hdim, hspan, hlt⟩)
  have hdeg_empty : t * (ProjectiveFamily.degree (∅ : ProjectiveFamily.Family d) : ℝ) ≤
      ((X.filter fun q => ∃ γ ∈ (∅ : ProjectiveFamily.Family d), DirMem γ p q).card : ℝ) := by
    simp [ProjectiveFamily.degree]
  have hunc_empty : ((X.filter fun q =>
      ¬∃ γ ∈ (∅ : ProjectiveFamily.Family d), DirMem γ p q).card) ≤ X.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨Γ, -, hdir, hdegC, hres⟩ := key X.card (∅ : ProjectiveFamily.Family d)
    (fun γ h => absurd h (Finset.notMem_empty γ)) hdeg_empty hunc_empty
  refine ⟨Γ, hdir, ?_, hres⟩
  calc t * (ProjectiveFamily.degree Γ : ℝ) ≤
        ((X.filter fun q => ∃ γ ∈ Γ, DirMem γ p q).card : ℝ) := hdegC
    _ ≤ (X.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

open Classical in
/-- red:directions.fixHK (`reduction.tex:135-143`, from `sc:theorem`): fixed `H, K` and a
positive-density symmetric selection on light lines (`≤ H` points) whose stars put at most
`K A deg γ` partners on every irreducible curve `γ` spanning at most a plane. -/
theorem exists_light_greedy_selection (hd : 3 ≤ d) (hIH : IH d) :
    ∃ H K c : ℝ, 2 ≤ H ∧ 0 < K ∧ 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ,
      ∀ P : Finset (RPoint d), N₀ ≤ P.card → Mcount P ≤ ε₀ * Ascale d P.card →
        ∃ G : Finset (RPoint d × RPoint d), IsSymmSelection P G ∧
          c * (P.card : ℝ) ^ 2 ≤ G.card ∧
          (∀ e ∈ G, (occ P (affineSpan ℝ {e.1, e.2}) : ℝ) ≤ H) ∧
          ∀ p : RPoint d, ∀ γ : ProjectiveVariety d, γ.IsIrreducible → γ.dimension = 1 →
            SpansAtMostPlane γ →
            (((star G p).filter fun q => DirMem γ p q).card : ℝ) ≤
              K * Ascale d P.card * (γ.degree : ℝ) := by
  classical
  obtain ⟨η, δ₀, εsc, hη, hδ₀, hεsc, Nsc, hsc⟩ := SparseCones.sparse_cones hd hIH
  obtain ⟨Cr, hCr, hrich⟩ := card_pairs_on_rich_lines
  have hCrne : Cr ≠ 0 := ne_of_gt hCr
  have hηne : η ≠ 0 := ne_of_gt hη
  have hδ₀ne : δ₀ ≠ 0 := ne_of_gt hδ₀
  have hH2 : (2 : ℝ) ≤ 2 + 4 * Cr / η :=
    le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) (le_of_lt hCr)) (le_of_lt hη))
  have hKpos : (0 : ℝ) < δ₀⁻¹ := inv_pos.mpr hδ₀
  have hcpos : (0 : ℝ) < η / 2 := by linarith
  have hεpos : (0 : ℝ) < min εsc (η / (8 * Cr)) :=
    lt_min hεsc (div_pos hη (mul_pos (by norm_num) hCr))
  have hCH : Cr / (2 + 4 * Cr / η) ≤ η / 4 := by
    have hHpos : (0 : ℝ) < 2 + 4 * Cr / η := by linarith [hH2]
    rw [div_le_iff₀ hHpos]
    have e : η / 4 * (4 * Cr / η) = Cr := by field_simp
    have hge : 4 * Cr / η ≤ 2 + 4 * Cr / η := le_add_of_nonneg_left (by norm_num)
    calc Cr = η / 4 * (4 * Cr / η) := e.symm
      _ ≤ η / 4 * (2 + 4 * Cr / η) :=
          mul_le_mul_of_nonneg_left hge (div_nonneg (le_of_lt hη) (by norm_num))
  have h2C : 2 * Cr * (min εsc (η / (8 * Cr))) ≤ η / 4 := by
    have h1 : 2 * Cr * (min εsc (η / (8 * Cr))) ≤ 2 * Cr * (η / (8 * Cr)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _)
        (mul_nonneg (by norm_num) (le_of_lt hCr))
    have e : 2 * Cr * (η / (8 * Cr)) = η / 4 := by field_simp; ring
    calc 2 * Cr * (min εsc (η / (8 * Cr))) ≤ 2 * Cr * (η / (8 * Cr)) := h1
      _ = η / 4 := e
  have hmain : ∀ P : Finset (RPoint d), max Nsc 2 ≤ P.card →
      Mcount P ≤ min εsc (η / (8 * Cr)) * Ascale d P.card →
      ∃ G : Finset (RPoint d × RPoint d), IsSymmSelection P G ∧
        η / 2 * (P.card : ℝ) ^ 2 ≤ G.card ∧
        (∀ e ∈ G, (occ P (affineSpan ℝ {e.1, e.2}) : ℝ) ≤ 2 + 4 * Cr / η) ∧
        ∀ p : RPoint d, ∀ γ : ProjectiveVariety d, γ.IsIrreducible → γ.dimension = 1 →
          SpansAtMostPlane γ →
          (((star G p).filter fun q => DirMem γ p q).card : ℝ) ≤
            δ₀⁻¹ * Ascale d P.card * (γ.degree : ℝ) := by
    intro P hN hM
    have hNsc : Nsc ≤ P.card := le_trans (Nat.le_max_left _ _) hN
    have hN2 : 2 ≤ P.card := le_trans (Nat.le_max_right _ _) hN
    have hcard1 : (1 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.card)
    have hcardpos : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast (by omega : 0 < P.card)
    have hN0 : (0 : ℝ) ≤ (P.card : ℝ) := le_of_lt hcardpos
    have hApos : (0 : ℝ) < Ascale d P.card := by
      dsimp [Ascale]
      exact Real.rpow_pos_of_pos hcardpos _
    have hA0 : (0 : ℝ) ≤ Ascale d P.card := le_of_lt hApos
    have hAN : Ascale d P.card ≤ (P.card : ℝ) := by
      dsimp [Ascale]
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hexp : (2 : ℝ) / (d : ℝ) ≤ 1 := by
        rw [div_le_one hdpos]
        exact_mod_cast (by omega : 2 ≤ d)
      calc ((P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ≤ (P.card : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hcard1 hexp
        _ = (P.card : ℝ) := Real.rpow_one _
    have hMsc : Mcount P ≤ εsc * Ascale d P.card :=
      hM.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hA0)
    have hM0 : (0 : ℝ) ≤ Mcount P := by dsimp [Mcount]; positivity
    have hlinecap : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
        (occ P (affineSpan ℝ ({p, q} : Set (RPoint d))) : ℝ) ≤ 2 * Mcount P := by
      intro p hp q hq hpq
      have hfr : Module.finrank ℝ (affineSpan ℝ ({p, q} : Set (RPoint d))).direction = 1 := by
        rw [direction_affineSpan, vectorSpan_pair]
        have hv : p -ᵥ q ≠ (0 : RPoint d) := by
          intro hv
          exact hpq (vsub_eq_zero_iff_eq.mp hv)
        exact finrank_span_singleton hv
      have hcap := card_inter_line_le P _ (le_of_eq hfr)
      simp only [occ]
      exact le_trans hcap (by linarith)
    have hRbound : ((P.offDiag.filter fun e => (2 + 4 * Cr / η) <
        (occ P (affineSpan ℝ ({e.1, e.2} : Set (RPoint d))) : ℝ)).card : ℝ) ≤
        Cr * ((P.card : ℝ) ^ 2 / (2 + 4 * Cr / η) + (P.card : ℝ) * (2 * Mcount P)) :=
      hrich P _ _ hH2 (mul_nonneg (by norm_num) hM0) hlinecap
    have hall : ∀ p : RPoint d, ∃ Γp : ProjectiveFamily.Family d,
        IsDirectionalFamily Γp ∧
          δ₀⁻¹ * Ascale d P.card * (ProjectiveFamily.degree Γp : ℝ) ≤
            ((P.filter fun q => q ≠ p ∧
              (occ P (affineSpan ℝ ({p, q} : Set (RPoint d))) : ℝ) ≤
                2 + 4 * Cr / η).card : ℝ) ∧
          ∀ γ : ProjectiveVariety d, γ.IsIrreducible → γ.dimension = 1 → SpansAtMostPlane γ →
            ((((P.filter fun q => q ≠ p ∧
              (occ P (affineSpan ℝ ({p, q} : Set (RPoint d))) : ℝ) ≤
                2 + 4 * Cr / η).filter
              fun q => DirMem γ p q ∧ ¬∃ γ' ∈ Γp, DirMem γ' p q).card : ℝ)) ≤
              δ₀⁻¹ * Ascale d P.card * (γ.degree : ℝ) := by
      intro p
      have hpnX : p ∉ P.filter fun q => q ≠ p ∧
          (occ P (affineSpan ℝ ({p, q} : Set (RPoint d))) : ℝ) ≤ 2 + 4 * Cr / η := by
        intro hcon
        obtain ⟨-, hne, -⟩ := Finset.mem_filter.mp hcon
        exact hne rfl
      have htpos : (0 : ℝ) < δ₀⁻¹ * Ascale d P.card := mul_pos hKpos hApos
      exact exists_greedy_family p _ hpnX _ htpos
    choose Γ hΓ using hall
    set C : RPoint d → ProjectiveFamily.Family d :=
      fun p => if p ∈ P then Γ p else ∅ with hCdef
    set G : Finset (RPoint d × RPoint d) := P.offDiag.filter fun e =>
      (occ P (affineSpan ℝ ({e.1, e.2} : Set (RPoint d))) : ℝ) ≤ 2 + 4 * Cr / η ∧
      (¬∃ γ' ∈ Γ e.1, DirMem γ' e.1 e.2) ∧
      (¬∃ γ' ∈ Γ e.2, DirMem γ' e.2 e.1) with hGdef
    have hCeq : ∀ p ∈ P, C p = Γ p := fun p hp => if_pos hp
    have hGmem : ∀ e : RPoint d × RPoint d, e ∈ G ↔ e ∈ P.offDiag ∧
        (occ P (affineSpan ℝ ({e.1, e.2} : Set (RPoint d))) : ℝ) ≤ 2 + 4 * Cr / η ∧
        (¬∃ γ' ∈ Γ e.1, DirMem γ' e.1 e.2) ∧
        (¬∃ γ' ∈ Γ e.2, DirMem γ' e.2 e.1) := by
      intro e
      simp only [hGdef, Finset.mem_filter]
    have hsel : IsSymmSelection P G := by
      refine ⟨by rw [hGdef]; exact Finset.filter_subset _ _, ?_⟩
      intro e he
      obtain ⟨heOff, hlight, hS1, hS2⟩ := (hGmem e).mp he
      refine (hGmem e.swap).mpr ⟨?_, ?_, ?_, ?_⟩
      · rw [Finset.mem_offDiag] at heOff ⊢
        obtain ⟨h1, h2, hne⟩ := heOff
        simp only [Prod.fst_swap, Prod.snd_swap]
        exact ⟨h2, h1, Ne.symm hne⟩
      · simp only [Prod.fst_swap, Prod.snd_swap]
        have hpc : ({e.2, e.1} : Set (RPoint d)) = {e.1, e.2} := Set.pair_comm _ _
        rw [hpc]
        exact hlight
      · simp only [Prod.fst_swap, Prod.snd_swap]
        exact hS2
      · simp only [Prod.fst_swap, Prod.snd_swap]
        exact hS1
    have hGlight : ∀ e ∈ G, (occ P (affineSpan ℝ ({e.1, e.2} : Set (RPoint d))) : ℝ) ≤
        2 + 4 * Cr / η := by
      intro e he
      exact ((hGmem e).mp he).2.1
    have hGcurve : ∀ (p : RPoint d) (γ : ProjectiveVariety d), γ.IsIrreducible →
        γ.dimension = 1 → SpansAtMostPlane γ →
        (((star G p).filter fun q => DirMem γ p q).card : ℝ) ≤
          δ₀⁻¹ * Ascale d P.card * (γ.degree : ℝ) := by
      intro p γ hirr hdim hspan
      obtain ⟨-, -, hpres⟩ := hΓ p
      apply le_trans _ (hpres γ hirr hdim hspan)
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro q hq
      obtain ⟨hqstar, hqdir⟩ := Finset.mem_filter.mp hq
      have hmem : (p, q) ∈ G := mem_pair_of_mem_star hqstar
      obtain ⟨hoff, hlight, hncov1, -⟩ := (hGmem (p, q)).mp hmem
      obtain ⟨-, hqP, hqne⟩ := Finset.mem_offDiag.mp hoff
      apply Finset.mem_filter.mpr
      refine ⟨?_, hqdir, hncov1⟩
      apply Finset.mem_filter.mpr
      exact ⟨hqP, Ne.symm hqne, hlight⟩
    have hCdir : ∀ p ∈ P, IsDirectionalFamily (C p) := by
      intro p hp
      rw [hCeq p hp]
      exact ((hΓ p).1)
    have hCdeg : ∀ p ∈ P, (ProjectiveFamily.degree (C p) : ℝ) ≤
        δ₀ * (P.card : ℝ) / Ascale d P.card := by
      intro p hp
      rw [hCeq p hp]
      obtain ⟨-, hpdeg, -⟩ := hΓ p
      have hXpN : ((P.filter fun q => q ≠ p ∧
          (occ P (affineSpan ℝ ({p, q} : Set (RPoint d))) : ℝ) ≤
            2 + 4 * Cr / η).card : ℝ) ≤ (P.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have h1 : δ₀⁻¹ * Ascale d P.card * (ProjectiveFamily.degree (Γ p) : ℝ) ≤
          (P.card : ℝ) := le_trans hpdeg hXpN
      rw [le_div_iff₀ hApos]
      have hKδ : δ₀ * δ₀⁻¹ = 1 := mul_inv_cancel₀ hδ₀ne
      have e : (ProjectiveFamily.degree (Γ p) : ℝ) * Ascale d P.card =
          δ₀ * (δ₀⁻¹ * Ascale d P.card * (ProjectiveFamily.degree (Γ p) : ℝ)) := by
        calc (ProjectiveFamily.degree (Γ p) : ℝ) * Ascale d P.card
              = (δ₀ * δ₀⁻¹) * ((ProjectiveFamily.degree (Γ p) : ℝ) * Ascale d P.card) := by
                rw [hKδ, one_mul]
          _ = δ₀ * (δ₀⁻¹ * Ascale d P.card * (ProjectiveFamily.degree (Γ p) : ℝ)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hδ₀)
    have hU : η * (P.card : ℝ) ^ 2 ≤ ((uncoveredPairs P C).card : ℝ) :=
      hsc P hNsc hMsc C hCdir hCdeg
    have hunion : uncoveredPairs P C ⊆ G ∪ P.offDiag.filter fun e => (2 + 4 * Cr / η) <
        (occ P (affineSpan ℝ ({e.1, e.2} : Set (RPoint d))) : ℝ) := by
      intro e he
      obtain ⟨heOff, hn1, hn2⟩ := Finset.mem_filter.mp (show e ∈ P.offDiag.filter _ from he)
      have hn1' : ¬∃ γ' ∈ C e.1, DirMem γ' e.1 e.2 := hn1
      have hn2' : ¬∃ γ' ∈ C e.2, DirMem γ' e.2 e.1 := hn2
      have he1P : e.1 ∈ P := (Finset.mem_offDiag.mp heOff).1
      have he2P : e.2 ∈ P := (Finset.mem_offDiag.mp heOff).2.1
      by_cases hlight : (occ P (affineSpan ℝ ({e.1, e.2} : Set (RPoint d))) : ℝ) ≤
          2 + 4 * Cr / η
      · apply Finset.mem_union.mpr
        apply Or.inl
        refine (hGmem e).mpr ⟨heOff, hlight, ?_, ?_⟩
        · intro hcon
          obtain ⟨γ', hmem, hq⟩ := hcon
          exact hn1' ⟨γ', (hCeq e.1 he1P).symm ▸ hmem, hq⟩
        · intro hcon
          obtain ⟨γ', hmem, hq⟩ := hcon
          exact hn2' ⟨γ', (hCeq e.2 he2P).symm ▸ hmem, hq⟩
      · apply Finset.mem_union.mpr
        apply Or.inr
        apply Finset.mem_filter.mpr
        exact ⟨heOff, lt_of_not_ge hlight⟩
    have hGU : ((uncoveredPairs P C).card : ℝ) ≤ (G.card : ℝ) +
        ((P.offDiag.filter fun e => (2 + 4 * Cr / η) <
          (occ P (affineSpan ℝ ({e.1, e.2} : Set (RPoint d))) : ℝ)).card : ℝ) := by
      calc ((uncoveredPairs P C).card : ℝ)
            ≤ ((((G ∪ P.offDiag.filter fun e => (2 + 4 * Cr / η) <
                (occ P (affineSpan ℝ ({e.1, e.2} : Set (RPoint d))) : ℝ)).card : ℕ)) : ℝ) :=
              by exact_mod_cast Finset.card_le_card hunion
        _ ≤ (G.card : ℝ) +
              ((P.offDiag.filter fun e => (2 + 4 * Cr / η) <
                (occ P (affineSpan ℝ ({e.1, e.2} : Set (RPoint d))) : ℝ)).card : ℝ) := by
              exact_mod_cast Finset.card_union_le _ _
    have hM2 : (P.card : ℝ) * (2 * Mcount P) ≤
        2 * (min εsc (η / (8 * Cr))) * (P.card : ℝ) ^ 2 := by
      have h1 : (P.card : ℝ) * (2 * Mcount P) ≤
          (P.card : ℝ) * (2 * (min εsc (η / (8 * Cr)) * Ascale d P.card)) := by
        apply mul_le_mul_of_nonneg_left _ hN0
        have hM' := hM
        linarith
      have hNA : (P.card : ℝ) * Ascale d P.card ≤ (P.card : ℝ) ^ 2 := by
        calc (P.card : ℝ) * Ascale d P.card ≤ (P.card : ℝ) * (P.card : ℝ) :=
              mul_le_mul_of_nonneg_left hAN hN0
          _ = (P.card : ℝ) ^ 2 := by ring
      have h2 : (P.card : ℝ) * (2 * (min εsc (η / (8 * Cr)) * Ascale d P.card)) ≤
          2 * (min εsc (η / (8 * Cr))) * (P.card : ℝ) ^ 2 := by
        have e : (P.card : ℝ) * (2 * (min εsc (η / (8 * Cr)) * Ascale d P.card)) =
            2 * (min εsc (η / (8 * Cr))) * ((P.card : ℝ) * Ascale d P.card) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left hNA
          (mul_nonneg (by norm_num) (le_of_lt hεpos))
      exact le_trans h1 h2
    have hCrH : Cr * ((P.card : ℝ) ^ 2 / (2 + 4 * Cr / η)) ≤
        (η / 4) * (P.card : ℝ) ^ 2 := by
      have e : Cr * ((P.card : ℝ) ^ 2 / (2 + 4 * Cr / η)) =
          (Cr / (2 + 4 * Cr / η)) * (P.card : ℝ) ^ 2 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hCH (pow_nonneg hN0 2)
    have hCre2 : Cr * ((P.card : ℝ) * (2 * Mcount P)) ≤ (η / 4) * (P.card : ℝ) ^ 2 := by
      have h1 : Cr * ((P.card : ℝ) * (2 * Mcount P)) ≤
          Cr * (2 * (min εsc (η / (8 * Cr))) * (P.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hM2 (le_of_lt hCr)
      have h2 : Cr * (2 * (min εsc (η / (8 * Cr))) * (P.card : ℝ) ^ 2) ≤
          (η / 4) * (P.card : ℝ) ^ 2 := by
        have e : Cr * (2 * (min εsc (η / (8 * Cr))) * (P.card : ℝ) ^ 2) =
            (2 * Cr * (min εsc (η / (8 * Cr)))) * (P.card : ℝ) ^ 2 := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_right h2C (pow_nonneg hN0 2)
      exact le_trans h1 h2
    have hcard_le : (η / 2) * (P.card : ℝ) ^ 2 ≤ (G.card : ℝ) := by
      linarith [hU, hGU, hRbound, hM2, hCrH, hCre2]
    exact ⟨G, hsel, hcard_le, hGlight, hGcurve⟩
  exact ⟨2 + 4 * Cr / η, δ₀⁻¹, η / 2, hH2, hKpos, hcpos,
    min εsc (η / (8 * Cr)), hεpos, max Nsc 2, hmain⟩

open Classical in
/-- red:directions.count (`reduction.tex:145-201`): on a symmetric selection with light lines and
the greedy curve bound, every irreducible projective variety `Y ⊂ ℙ^{d-1}` of dimension `a`
receives at most `C deg(Y) A^a` partners of each star. Induction on `a`: radius classes and
Cauchy–Schwarz when the displacements span `ℓ ≥ 4` dimensions (the alternative contradicts
`N/M^{d/2} → ∞`), flat caps or the greedy bound when `ℓ ≤ 3`. -/
theorem directionCaps_of_light_greedy (hd : 3 ≤ d) (hIH : IH d) (H K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ,
      ∀ P : Finset (RPoint d), N₀ ≤ P.card → Mcount P ≤ ε₀ * Ascale d P.card →
      ∀ G : Finset (RPoint d × RPoint d), IsSymmSelection P G →
        (∀ e ∈ G, (occ P (affineSpan ℝ {e.1, e.2}) : ℝ) ≤ H) →
        (∀ p : RPoint d, ∀ γ : ProjectiveVariety d, γ.IsIrreducible → γ.dimension = 1 →
          SpansAtMostPlane γ →
          (((star G p).filter fun q => DirMem γ p q).card : ℝ) ≤
            K * Ascale d P.card * (γ.degree : ℝ)) →
        ∀ p : RPoint d, ∀ Y : ProjectiveVariety d, Y.IsIrreducible →
          (((star G p).filter fun q => DirMem Y p q).card : ℝ) ≤
            C * (Y.degree : ℝ) * Ascale d P.card ^ Y.dimension := by
  obtain ⟨C, hC, ε, hε, hcore⟩ := direction_caps_core hd hIH
    (Request.directionVarietyBasics d) (Request.zeroDimDirectionLocus d)
    (Request.directionHyperplaneSections d) (Request.curveLinearSections d) H K
  refine ⟨C, hC, ε, hε, 1, ?_⟩
  intro P hP hMP G hG hlight hgreedy p Y hY
  exact hcore P hP hMP G hG (by simpa only [occ] using hlight) hgreedy p Y hY

open Classical in
/-- red:directions (`reduction.tex:98-108`): a symmetric selection with at least `c N^2` pairs
such that for every vertex `p` and every irreducible projective variety `Y ⊂ ℙ^{d-1}` of
dimension `a`, at most `C deg(Y) A^a` partners `q` have `π_p(q) ∈ Y`. -/
theorem exists_selection_directionCaps (hd : 3 ≤ d) (hIH : IH d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ,
      ∀ P : Finset (RPoint d), N₀ ≤ P.card → Mcount P ≤ ε₀ * Ascale d P.card →
        ∃ G : Finset (RPoint d × RPoint d), IsSymmSelection P G ∧
          c * (P.card : ℝ) ^ 2 ≤ G.card ∧
          ∀ p : RPoint d, ∀ Y : ProjectiveVariety d, Y.IsIrreducible →
            (((star G p).filter fun q => DirMem Y p q).card : ℝ) ≤
              C * (Y.degree : ℝ) * Ascale d P.card ^ Y.dimension := by
  classical
  obtain ⟨H, K, c, hH, hK, hc, ε₁, hε₁, N₁, hG⟩ :=
    exists_light_greedy_selection hd hIH
  obtain ⟨C, hC, ε₂, hε₂, N₂, hCap⟩ := directionCaps_of_light_greedy hd hIH H K
  refine ⟨c, C, hc, hC, min ε₁ ε₂, lt_min hε₁ hε₂, max N₁ N₂, ?_⟩
  intro P hN hM
  have hN₁ : N₁ ≤ P.card := le_trans (Nat.le_max_left _ _) hN
  have hN₂ : N₂ ≤ P.card := le_trans (Nat.le_max_right _ _) hN
  have hA_nonneg : 0 ≤ Ascale d P.card := by
    dsimp [Ascale]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hM₁ : Mcount P ≤ ε₁ * Ascale d P.card :=
    hM.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hA_nonneg)
  have hM₂ : Mcount P ≤ ε₂ * Ascale d P.card :=
    hM.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hA_nonneg)
  obtain ⟨G, hGs, hGc, hGl, hGg⟩ := hG P hN₁ hM₁
  exact ⟨G, hGs, hGc, fun p Y hY => hCap P hN₂ hM₂ G hGs hGl hGg p Y hY⟩

end Reduction

end

end DistinctDistances
