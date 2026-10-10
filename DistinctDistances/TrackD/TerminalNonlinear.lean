import DistinctDistances.TrackD.TerminalLines
import DistinctDistances.TrackD.PerspectiveGeometry
import DistinctDistances.TrackD.PerspectiveReduction
import DistinctDistances.TrackD.TripleDefs
import DistinctDistances.Bridges.HighMultiplicity
import DistinctDistances.TrackD.GeoD4Scale
import DistinctDistances.TrackD.GeoD3Scale
import DistinctDistances.TrackD.MDGeoAux

/-!
# `geo:terminal`, nonlinear curves (`secants.tex:333–512`)

Two abstract weighted counting lemmas (`d ≥ 4`: Cauchy–Schwarz against a pair–center bound;
`d = 3`: Hölder against a triple–center bound) and the geometric inputs that feed them.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

/-- A set has finite cardinality at most `r`. -/
def CardLe {α : Type*} (S : Set α) (r : ℝ) : Prop := S.Finite ∧ (S.ncard : ℝ) ≤ r

/-- Weight carried by the groups: `Σ_p Σ_{i grouped at p} n_i`. Here `grp p i = some γ` says
that at center `p` the curve `i` projects onto the nonlinear directional curve `γ`. -/
def groupedWeight {α ι β : Type*} (Pc : Finset α) (I : Finset ι) (n : ι → ℝ)
    (grp : α → ι → Option β) : ℝ :=
  ∑ p ∈ Pc, ∑ i ∈ I.filter (fun i => (grp p i).isSome), n i

private noncomputable def d4GroupMass {α ι β : Type*} (I : Finset ι) (n : ι → ℝ)
    (grp : α → ι → Option β) (p : α) (γ : β) : ℝ :=
  ∑ i ∈ I, if grp p i = some γ then n i else 0

private theorem groupedWeight_eq_sigma {α ι β : Type*} (Pc : Finset α) (I : Finset ι)
    (n : ι → ℝ) (grp : α → ι → Option β) (Γ : α → Finset β)
    (hΓ : ∀ p ∈ Pc, ∀ i ∈ I, ∀ γ, grp p i = some γ → γ ∈ Γ p) :
    groupedWeight Pc I n grp =
      ∑ z ∈ Pc.sigma Γ, d4GroupMass I n grp z.1 z.2 := by
  classical
  unfold groupedWeight
  simp only [Finset.sum_filter]
  rw [Finset.sum_sigma]
  simp only [d4GroupMass]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hnone : grp p i = none
  · simp [hnone]
  · obtain ⟨γ, hγ⟩ : ∃ γ, grp p i = some γ := by
      cases h : grp p i with
      | none => exact False.elim (hnone h)
      | some γ => exact ⟨γ, rfl⟩
    have hγmem := hΓ p hp i hi γ hγ
    rw [if_pos (by simp [hγ])]
    rw [Finset.sum_eq_single γ]
    · simp [hγ]
    · intro γ' hγ' hne
      simp [hγ, Ne.symm hne]
    · intro hnot
      exact False.elim (hnot hγmem)

private theorem d4GroupMass_sq_le_offdiag {α ι β : Type*} (I : Finset ι)
    (n : ι → ℝ) (grp : α → ι → Option β) (p : α) (γ : β)
    (M C₁ : ℝ) (e : α → β → ℝ) (hM : 0 ≤ M) (hC₁ : 0 < C₁)
    (he : 1 ≤ e p γ)
    (hn : ∀ i ∈ I, 0 ≤ n i)
    (hmass : ∀ i ∈ I, grp p i = some γ → n i ≤ C₁ * M * e p γ)
    (hlarge : 2 * C₁ * M * e p γ < d4GroupMass I n grp p γ) :
    (d4GroupMass I n grp p γ) ^ 2 ≤
      2 * ∑ i ∈ I, ∑ j ∈ I,
        (if i ≠ j ∧ grp p i = some γ ∧ grp p j = some γ then n i * n j else 0) := by
  classical
  let a := C₁ * M * e p γ
  let w := d4GroupMass I n grp p γ
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hw : 0 ≤ w := by
    dsimp [w, d4GroupMass]
    exact Finset.sum_nonneg fun i hi => by
      split_ifs
      · exact hn i hi
      · exact le_rfl
  have hdiag :
      ∑ i ∈ I, (if grp p i = some γ then n i ^ 2 else 0) ≤ a * w := by
    calc
      ∑ i ∈ I, (if grp p i = some γ then n i ^ 2 else 0) ≤
          ∑ i ∈ I, (if grp p i = some γ then a * n i else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with hg
        · have hn' := hn i hi
          have hm' := hmass i hi hg
          change n i ≤ a at hm'
          nlinarith
        · rfl
      _ = a * w := by
        simp [w, a, d4GroupMass, Finset.mul_sum, mul_ite]
  have hexpand : w ^ 2 =
      (∑ i ∈ I, (if grp p i = some γ then n i ^ 2 else 0)) +
        (∑ i ∈ I, ∑ j ∈ I,
          (if i ≠ j ∧ grp p i = some γ ∧ grp p j = some γ then n i * n j else 0)) := by
    let s := I ×ˢ I
    let f : ι × ι → ℝ := fun ij =>
      (if grp p ij.1 = some γ then n ij.1 else 0) *
        (if grp p ij.2 = some γ then n ij.2 else 0)
    have hprod : w ^ 2 = ∑ ij ∈ s, f ij := by
      simp only [w, d4GroupMass, sq, s, f]
      rw [Finset.sum_mul_sum]
      simpa [f, s] using
        (Finset.sum_product' I I
          (fun i j => (if grp p i = some γ then n i else 0) *
            (if grp p j = some γ then n j else 0))).symm
    rw [hprod]
    rw [← Finset.sum_filter_add_sum_filter_not s (fun ij => ij.1 = ij.2) f]
    have hdiag' :
        ∑ ij ∈ s.filter (fun ij => ij.1 = ij.2), f ij =
          ∑ i ∈ I, (if grp p i = some γ then n i ^ 2 else 0) := by
      rw [Finset.sum_filter]
      change ∑ ij ∈ I ×ˢ I, (if ij.1 = ij.2 then f ij else 0) = _
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      simp [f, pow_two, hi]
      intro hnot hgrp
      exact False.elim (hnot hgrp)
    have hoff' :
        ∑ ij ∈ s.filter (fun ij => ¬ ij.1 = ij.2), f ij =
          ∑ i ∈ I, ∑ j ∈ I,
            (if i ≠ j ∧ grp p i = some γ ∧ grp p j = some γ then n i * n j else 0) := by
      rw [Finset.sum_filter]
      change ∑ ij ∈ I ×ˢ I, (if ¬ ij.1 = ij.2 then f ij else 0) = _
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · simp [hij, f]
      · by_cases hgi : grp p i = some γ <;> by_cases hgj : grp p j = some γ <;>
          simp [hij, f, hgi, hgj, and_comm]
    rw [hdiag', hoff']
  have hlarge' : 2 * a < w := by dsimp [a, w]; nlinarith [hlarge]
  have hfinal : w ^ 2 ≤ 2 *
      ∑ i ∈ I, ∑ j ∈ I,
        (if i ≠ j ∧ grp p i = some γ ∧ grp p j = some γ then n i * n j else 0) := by
    rw [hexpand]
    have hgap : 0 ≤ (w - 2 * a) * w := mul_nonneg (by linarith) hw
    nlinarith
  simpa [w] using hfinal

/-- `geo:terminal.d4-core` (`secants.tex:372–389`), abstract. Centers `Pc` (`|Pc| ≤ N`), curve
masses `n_i ≥ 0` with `Σ n_i ≤ N`; at each center the grouped curves form groups `γ` of degree
`e_γ ≥ 1` with `Σ_γ e_γ ≤ E`; a grouped curve has mass at most `C₁ M e_γ`; every ordered pair of
distinct curves is grouped together at centers with `Σ e_γ⁻¹ ≤ C₂`. Then the grouped weight is
at most `2 C₁ M N E + (2 C₂ E)^{1/2} N^{3/2}`. -/
theorem terminal_d4_core {α ι β : Type*} (Pc : Finset α) (I : Finset ι) (n : ι → ℝ)
    (grp : α → ι → Option β) (e : α → β → ℝ) (N M E C₁ C₂ : ℝ)
    (hM : 0 ≤ M) (hE0 : 0 ≤ E)
    (hPc : (Pc.card : ℝ) ≤ N) (hn : ∀ i ∈ I, 0 ≤ n i) (hsum : ∑ i ∈ I, n i ≤ N)
    (he : ∀ p ∈ Pc, ∀ γ, 1 ≤ e p γ)
    (Γ : α → Finset β) (hΓ : ∀ p ∈ Pc, ∀ i ∈ I, ∀ γ, grp p i = some γ → γ ∈ Γ p)
    (hE : ∀ p ∈ Pc, ∑ γ ∈ Γ p, e p γ ≤ E)
    (hC₁ : 0 < C₁) (hmass : ∀ p ∈ Pc, ∀ i ∈ I, ∀ γ, grp p i = some γ → n i ≤ C₁ * M * e p γ)
    (hC₂ : 0 ≤ C₂)
    (hpair : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∑ p ∈ Pc, ∑ γ ∈ Γ p, (if grp p i = some γ ∧ grp p j = some γ then (e p γ)⁻¹ else 0)
        ≤ C₂) :
    groupedWeight Pc I n grp ≤
      2 * C₁ * M * N * E + Real.sqrt (2 * C₂ * E) * N ^ ((3 : ℝ) / 2) := by
  classical
  let G := Pc.sigma Γ
  let w := d4GroupMass I n grp
  let off := fun p γ =>
    ∑ i ∈ I, ∑ j ∈ I,
      (if i ≠ j ∧ grp p i = some γ ∧ grp p j = some γ then n i * n j else 0)
  let small := G.filter (fun z => w z.1 z.2 ≤ 2 * C₁ * M * e z.1 z.2)
  let large := G.filter (fun z => 2 * C₁ * M * e z.1 z.2 < w z.1 z.2)
  have hN0 : 0 ≤ N := by
    have hc : 0 ≤ (Pc.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hfactor0 : 0 ≤ 2 * C₁ * M := by positivity
  have hsumN0 : 0 ≤ ∑ i ∈ I, n i := Finset.sum_nonneg fun i hi => hn i hi
  have htotal : groupedWeight Pc I n grp = ∑ z ∈ G, w z.1 z.2 := by
    simpa [G, w] using groupedWeight_eq_sigma Pc I n grp Γ hΓ
  have hmassE : ∑ z ∈ G, e z.1 z.2 ≤ N * E := by
    rw [Finset.sum_sigma]
    calc
      ∑ p ∈ Pc, ∑ γ ∈ Γ p, e p γ ≤ ∑ p ∈ Pc, E :=
        Finset.sum_le_sum fun p hp => hE p hp
      _ = (Pc.card : ℝ) * E := by simp
      _ ≤ N * E := mul_le_mul_of_nonneg_right hPc hE0
  have hw0 : ∀ z ∈ G, 0 ≤ w z.1 z.2 := by
    intro z hz
    dsimp [w, d4GroupMass]
    exact Finset.sum_nonneg fun i hi => by
      split_ifs
      · exact hn i hi
      · exact le_rfl
  have hoff0 : ∀ z ∈ G, 0 ≤ off z.1 z.2 := by
    intro z hz
    dsimp [off]
    exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => by
      split_ifs with h
      · exact mul_nonneg (hn i hi) (hn j hj)
      · positivity
  have hsplit : ∑ z ∈ G, w z.1 z.2 =
      (∑ z ∈ small, w z.1 z.2) + (∑ z ∈ large, w z.1 z.2) := by
    rw [← Finset.sum_filter_add_sum_filter_not G
      (fun z => w z.1 z.2 ≤ 2 * C₁ * M * e z.1 z.2) (fun z => w z.1 z.2)]
    simp [small, large, not_le]
  have hsmall : ∑ z ∈ small, w z.1 z.2 ≤ 2 * C₁ * M * N * E := by
    calc
      ∑ z ∈ small, w z.1 z.2 ≤ ∑ z ∈ small, 2 * C₁ * M * e z.1 z.2 :=
        Finset.sum_le_sum fun z hz => (Finset.mem_filter.mp hz).2
      _ ≤ ∑ z ∈ G, 2 * C₁ * M * e z.1 z.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
          intro z hz _
          exact mul_nonneg hfactor0
            (le_trans (by norm_num) (he z.1 (Finset.mem_sigma.mp hz).1 z.2)))
      _ = (2 * C₁ * M) * ∑ z ∈ G, e z.1 z.2 := by
        rw [Finset.mul_sum]
      _ ≤ (2 * C₁ * M) * (N * E) := mul_le_mul_of_nonneg_left hmassE hfactor0
      _ = 2 * C₁ * M * N * E := by ring
  have hpairG : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∑ z ∈ G,
        (if grp z.1 i = some z.2 ∧ grp z.1 j = some z.2 then (e z.1 z.2)⁻¹ else 0) ≤ C₂ := by
    intro i hi j hj hij
    simpa [G, Finset.sum_sigma] using hpair i hi j hj hij
  have henergy : ∑ z ∈ G, off z.1 z.2 / e z.1 z.2 ≤ C₂ * (∑ i ∈ I, n i) ^ 2 := by
    calc
      ∑ z ∈ G, off z.1 z.2 / e z.1 z.2 =
          ∑ z ∈ G, ∑ i ∈ I, ∑ j ∈ I,
            n i * n j * (if i ≠ j ∧ grp z.1 i = some z.2 ∧ grp z.1 j = some z.2
              then (e z.1 z.2)⁻¹ else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        dsimp [off]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hcond : i ≠ j ∧ grp z.1 i = some z.2 ∧ grp z.1 j = some z.2
        · simp [hcond, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        · simp [hcond]
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ z ∈ G,
            n i * n j * (if i ≠ j ∧ grp z.1 i = some z.2 ∧ grp z.1 j = some z.2
              then (e z.1 z.2)⁻¹ else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ ≤ ∑ i ∈ I, ∑ j ∈ I, n i * n j * C₂ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i = j
        · have hnonneg : 0 ≤ n i * n i * C₂ := by
            have hnn : 0 ≤ n i * n i := by
              simpa [pow_two] using sq_nonneg (n i)
            exact mul_nonneg hnn hC₂
          simpa [hij] using hnonneg
        · have hcoef :
              ∑ z ∈ G,
                (if grp z.1 i = some z.2 ∧ grp z.1 j = some z.2
                  then (e z.1 z.2)⁻¹ else 0) ≤ C₂ := by
              simpa using hpairG i hi j hj hij
          have hnij : 0 ≤ n i * n j := mul_nonneg (hn i hi) (hn j hj)
          calc
            ∑ z ∈ G, n i * n j *
                (if i ≠ j ∧ grp z.1 i = some z.2 ∧ grp z.1 j = some z.2
                  then (e z.1 z.2)⁻¹ else 0) =
                n i * n j * ∑ z ∈ G,
                  (if grp z.1 i = some z.2 ∧ grp z.1 j = some z.2
                    then (e z.1 z.2)⁻¹ else 0) := by
              simp [hij, Finset.mul_sum]
            _ ≤ n i * n j * C₂ := mul_le_mul_of_nonneg_left hcoef hnij
      _ = C₂ * (∑ i ∈ I, n i) ^ 2 := by
        calc
          ∑ i ∈ I, ∑ j ∈ I, n i * n j * C₂ =
              C₂ * (∑ i ∈ I, ∑ j ∈ I, n i * n j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = C₂ * (∑ i ∈ I, n i) ^ 2 := by
            rw [← Finset.sum_mul_sum]
            ring
  have henergyN : ∑ z ∈ G, off z.1 z.2 / e z.1 z.2 ≤ C₂ * N ^ 2 := by
    have hsumle : (∑ i ∈ I, n i) ^ 2 ≤ N ^ 2 := by
      have hgap := mul_nonneg (sub_nonneg.mpr (by linarith : ∑ i ∈ I, n i ≤ N))
        (add_nonneg hN0 hsumN0)
      nlinarith
    exact le_trans henergy (mul_le_mul_of_nonneg_left hsumle hC₂)
  have hlargeSq : ∑ z ∈ large, w z.1 z.2 ^ 2 / e z.1 z.2 ≤ 2 * C₂ * N ^ 2 := by
    calc
      ∑ z ∈ large, w z.1 z.2 ^ 2 / e z.1 z.2 ≤
          ∑ z ∈ large, 2 * (off z.1 z.2 / e z.1 z.2) := by
        apply Finset.sum_le_sum
        intro z hz
        have hzG : z ∈ G := (Finset.mem_filter.mp hz).1
        have hsq := d4GroupMass_sq_le_offdiag I n grp z.1 z.2 M C₁ e hM hC₁
          (he z.1 (Finset.mem_sigma.mp hzG).1 z.2)
          hn (fun i hi hgi => hmass z.1 (Finset.mem_sigma.mp hzG).1 i hi z.2 hgi)
          (Finset.mem_filter.mp hz).2
        have hepos : 0 < e z.1 z.2 := lt_of_lt_of_le zero_lt_one
          (he z.1 (Finset.mem_sigma.mp hzG).1 z.2)
        calc
          w z.1 z.2 ^ 2 / e z.1 z.2 ≤ (2 * off z.1 z.2) / e z.1 z.2 :=
            div_le_div_of_nonneg_right hsq hepos.le
          _ = 2 * (off z.1 z.2 / e z.1 z.2) := by ring
      _ ≤ 2 * ∑ z ∈ G, off z.1 z.2 / e z.1 z.2 := by
        have hsub : (∑ z ∈ large, off z.1 z.2 / e z.1 z.2) ≤
            ∑ z ∈ G, off z.1 z.2 / e z.1 z.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro z hz _
            exact div_nonneg (hoff0 z hz)
              (lt_of_lt_of_le zero_lt_one (he z.1 (Finset.mem_sigma.mp hz).1 z.2)).le
        calc
          ∑ z ∈ large, 2 * (off z.1 z.2 / e z.1 z.2) =
              2 * ∑ z ∈ large, off z.1 z.2 / e z.1 z.2 := by rw [Finset.mul_sum]
          _ ≤ 2 * ∑ z ∈ G, off z.1 z.2 / e z.1 z.2 :=
            mul_le_mul_of_nonneg_left hsub (by norm_num)
      _ ≤ 2 * C₂ * N ^ 2 := by nlinarith [henergyN]
  have hlargeSum : ∑ z ∈ large, w z.1 z.2 ≤
      Real.sqrt (2 * C₂ * E) * N ^ ((3 : ℝ) / 2) := by
    by_cases hlargeEmpty : large = ∅
    · simp [hlargeEmpty]
      positivity
    · have hlargeNe : large.Nonempty := Finset.nonempty_iff_ne_empty.mpr hlargeEmpty
      have hsumElarge : 0 < ∑ z ∈ large, e z.1 z.2 := by
        apply Finset.sum_pos
        · intro z hz
          exact lt_of_lt_of_le zero_lt_one (he z.1 (Finset.mem_sigma.mp
            ((Finset.mem_filter.mp hz).1)).1 z.2)
        · exact hlargeNe
      have hsumElarge_le : ∑ z ∈ large, e z.1 z.2 ≤ N * E :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun z hz _ => le_trans (by norm_num)
            (he z.1 (Finset.mem_sigma.mp hz).1 z.2))) hmassE
      have hTitu := Finset.sq_sum_div_le_sum_sq_div large (fun z => w z.1 z.2)
        (fun z hz => lt_of_lt_of_le zero_lt_one (he z.1 (Finset.mem_sigma.mp
          ((Finset.mem_filter.mp hz).1)).1 z.2))
      have hsq : (∑ z ∈ large, w z.1 z.2) ^ 2 ≤
          (∑ z ∈ large, w z.1 z.2 ^ 2 / e z.1 z.2) * (∑ z ∈ large, e z.1 z.2) :=
        (div_le_iff₀ hsumElarge).mp hTitu
      have hsq' : (∑ z ∈ large, w z.1 z.2) ^ 2 ≤ 2 * C₂ * E * N ^ 3 := by
        calc
          _ ≤ (∑ z ∈ large, w z.1 z.2 ^ 2 / e z.1 z.2) *
                (∑ z ∈ large, e z.1 z.2) := hsq
          _ ≤ (2 * C₂ * N ^ 2) * (N * E) := mul_le_mul hlargeSq hsumElarge_le
              (Finset.sum_nonneg fun z hz => le_trans (by norm_num) (he z.1
                (Finset.mem_sigma.mp (Finset.mem_filter.mp hz).1).1 z.2))
              (by positivity)
          _ = 2 * C₂ * E * N ^ 3 := by ring
      have hrootSq :
          (Real.sqrt (2 * C₂ * E) * N ^ ((3 : ℝ) / 2)) ^ 2 = 2 * C₂ * E * N ^ 3 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hC₂) hE0)]
        have hpow : (N ^ ((3 : ℝ) / 2)) ^ 2 = N ^ (3 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
          norm_num
        rw [hpow]
      have hL0 : 0 ≤ ∑ z ∈ large, w z.1 z.2 :=
        Finset.sum_nonneg fun z hz => hw0 z (Finset.mem_filter.mp hz).1
      have hR0 : 0 ≤ Real.sqrt (2 * C₂ * E) * N ^ ((3 : ℝ) / 2) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hN0 _)
      nlinarith [hsq', hrootSq]
  rw [htotal, hsplit]
  linarith [hsmall, hlargeSum]

/-- Validity of an ordered triple at a center (`secants.tex:426–428`): all three curves are
grouped together and each index occurs at most its map degree `t p i` times. -/
def TripleValid {α ι β : Type*} [DecidableEq ι] (grp : α → ι → Option β) (t : α → ι → ℕ)
    (p : α) (i j k : ι) : Prop :=
  (grp p i).isSome ∧ grp p i = grp p j ∧ grp p i = grp p k ∧
    ∀ a ∈ ({i, j, k} : Finset ι),
      ((if i = a then 1 else 0) + (if j = a then 1 else 0) + (if k = a then 1 else 0) : ℕ) ≤ t p a

private theorem tripleValid_of_pairwise_ne {α ι β : Type*} [DecidableEq ι]
    (I : Finset ι) (grp : α → ι → Option β) (t : α → ι → ℕ) (p : α)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (γ : β) (hgi : grp p i = some γ) (hgj : grp p j = some γ) (hgk : grp p k = some γ)
    (ht : ∀ a ∈ I, 1 ≤ t p a) (hi : i ∈ I) (hj : j ∈ I) (hk : k ∈ I) :
    TripleValid grp t p i j k := by
  refine ⟨by simp [hgi], by rw [hgi, hgj], by rw [hgi, hgk], ?_⟩
  intro a ha
  have ha' : a = i ∨ a = j ∨ a = k := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using ha
  rcases ha' with hai | haj | hak
  · subst a
    simpa [hij, Ne.symm hij, hik, Ne.symm hik] using ht i hi
  · subst a
    simpa [hij, Ne.symm hij, hjk, Ne.symm hjk] using ht j hj
  · subst a
    simpa [hik, Ne.symm hik, hjk, Ne.symm hjk] using ht k hk

private theorem repeatedLow_of_not_tripleValid {α ι β : Type*} [DecidableEq ι]
    (I : Finset ι) (grp : α → ι → Option β) (t : α → ι → ℕ) (p : α)
    (i j k : ι) (γ : β) (hgi : grp p i = some γ) (hgj : grp p j = some γ)
    (hgk : grp p k = some γ) (ht : ∀ a ∈ I, 1 ≤ t p a)
    (hi : i ∈ I) (hj : j ∈ I) (hk : k ∈ I)
    (hbad : ¬ TripleValid grp t p i j k) :
    (i = j ∧ t p i ≤ 2) ∨ (j = k ∧ t p j ≤ 2) ∨ (i = k ∧ t p i ≤ 2) := by
  classical
  have hnotCounts : ¬ ∀ a ∈ ({i, j, k} : Finset ι),
      ((if i = a then 1 else 0) + (if j = a then 1 else 0) +
        (if k = a then 1 else 0) : ℕ) ≤ t p a := by
    intro hc
    apply hbad
    exact ⟨by simp [hgi], by simp [hgi, hgj], by simp [hgi, hgk], hc⟩
  push_neg at hnotCounts
  obtain ⟨a, ha, hcount⟩ := hnotCounts
  have ha' : a = i ∨ a = j ∨ a = k := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using ha
  have haI : a ∈ I := by
    rcases ha' with hai | haj | hak
    · simpa [hai] using hi
    · simpa [haj] using hj
    · simpa [hak] using hk
  let c := ((if i = a then 1 else 0) + (if j = a then 1 else 0) +
    (if k = a then 1 else 0) : ℕ)
  have hcle : c ≤ 3 := by
    dsimp [c]
    by_cases hia : i = a <;> by_cases hja : j = a <;> by_cases hka : k = a <;>
      simp_all
  change t p a < c at hcount
  have hta : t p a < c := hcount
  have htpos := ht a haI
  have hta2 : t p a ≤ 2 := by omega
  have hcge : 2 ≤ c := by omega
  by_cases hia : i = a
  · subst a
    have hti : t p i ≤ 2 := by simpa using hta2
    by_cases hji : j = i
    · exact Or.inl ⟨hji.symm, hti⟩
    · by_cases hki : k = i
      · exact Or.inr (Or.inr ⟨hki.symm, hti⟩)
      · simp [c, hji, hki] at hcge
  · by_cases hja : j = a
    · subst a
      have htj : t p j ≤ 2 := by simpa using hta2
      by_cases hkj : k = j
      · exact Or.inr (Or.inl ⟨hkj.symm, htj⟩)
      · simp [c, hia, hkj] at hcge
    · by_cases hka : k = a <;> simp [c, hia, hja, hka] at hcge

private noncomputable def d3ValidGroupMass {α ι β : Type*} [DecidableEq ι]
    (I : Finset ι) (n : ι → ℝ) (grp : α → ι → Option β) (t : α → ι → ℕ)
    (p : α) (γ : β) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I,
    (if grp p i = some γ ∧ TripleValid grp t p i j k then n i * n j * n k else 0)

private theorem finset_sum_cube {ι : Type*} (I : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ I, f i) ^ 3 = ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, f i * f j * f k := by
  have htwo : (∑ i ∈ I, f i) ^ 2 = ∑ i ∈ I, ∑ j ∈ I, f i * f j := by
    rw [pow_two, Finset.sum_mul_sum]
  calc
    (∑ i ∈ I, f i) ^ 3 = (∑ i ∈ I, f i) ^ 2 * (∑ k ∈ I, f k) := by ring
    _ = (∑ i ∈ I, ∑ j ∈ I, f i * f j) * (∑ k ∈ I, f k) := by rw [htwo]
    _ = ∑ i ∈ I, ∑ k ∈ I, (∑ j ∈ I, f i * f j) * f k := by
      exact Finset.sum_mul_sum I I (fun i => ∑ j ∈ I, f i * f j) f
    _ = ∑ i ∈ I, ∑ k ∈ I, ∑ j ∈ I, (f i * f j) * f k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, f i * f j * f k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]

private theorem d3GroupMass_cube_lower {α ι β : Type*} [DecidableEq ι]
    (I : Finset ι) (n : ι → ℝ) (grp : α → ι → Option β) (t : α → ι → ℕ)
    (p : α) (γ : β) (M C₁ : ℝ) (e : α → β → ℝ)
    (hM : 0 ≤ M) (hC₁ : 0 < C₁) (he : 1 ≤ e p γ)
    (hn : ∀ i ∈ I, 0 ≤ n i) (ht : ∀ i ∈ I, 1 ≤ t p i)
    (hmass : ∀ i ∈ I, grp p i = some γ → n i ≤ C₁ * M * t p i * e p γ)
    (hlarge : 12 * C₁ * M * e p γ < d4GroupMass I n grp p γ) :
    (d4GroupMass I n grp p γ) ^ 3 ≤
      2 * d3ValidGroupMass I n grp t p γ := by
  classical
  let w := d4GroupMass I n grp p γ
  let a := C₁ * M * e p γ
  let b := fun i => if grp p i = some γ then n i else 0
  let v := fun i j k =>
    if grp p i = some γ ∧ TripleValid grp t p i j k then n i * n j * n k else 0
  let r₁ := fun i j k =>
    if i = j ∧ grp p i = some γ ∧ grp p k = some γ ∧ t p i ≤ 2 then
      n i * n j * n k else 0
  let r₂ := fun i j k =>
    if j = k ∧ grp p i = some γ ∧ grp p j = some γ ∧ t p j ≤ 2 then
      n i * n j * n k else 0
  let r₃ := fun i j k =>
    if i = k ∧ grp p i = some γ ∧ grp p j = some γ ∧ t p i ≤ 2 then
      n i * n j * n k else 0
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hw : 0 ≤ w := by
    dsimp [w, d4GroupMass]
    exact Finset.sum_nonneg fun i hi => by
      split_ifs
      · exact hn i hi
      · exact le_rfl
  have hsmallCap : ∀ i ∈ I, grp p i = some γ → t p i ≤ 2 → n i ≤ 2 * a := by
    intro i hi hgi hti
    have hmass' := hmass i hi hgi
    have htR : (t p i : ℝ) ≤ 2 := by exact_mod_cast hti
    have hscaled : a * (t p i : ℝ) ≤ a * 2 := mul_le_mul_of_nonneg_left htR ha
    have hmass'' : n i ≤ a * (t p i : ℝ) := by
      dsimp [a]
      nlinarith [hmass']
    calc
      n i ≤ a * (t p i : ℝ) := hmass''
      _ ≤ a * 2 := hscaled
      _ = 2 * a := by ring
  have hpoint : ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I,
      b i * b j * b k ≤ v i j k + r₁ i j k + r₂ i j k + r₃ i j k := by
    intro i hi j hj k hk
    have hni := hn i hi
    have hnj := hn j hj
    have hnk := hn k hk
    by_cases hgi : grp p i = some γ
    · by_cases hgj : grp p j = some γ
      · by_cases hgk : grp p k = some γ
        · by_cases hv : TripleValid grp t p i j k
          · have hr₁ : 0 ≤ r₁ i j k := by dsimp [r₁]; split_ifs <;> positivity
            have hr₂ : 0 ≤ r₂ i j k := by dsimp [r₂]; split_ifs <;> positivity
            have hr₃ : 0 ≤ r₃ i j k := by dsimp [r₃]; split_ifs <;> positivity
            simp [b, v, hgi, hgj, hgk, hv]
            nlinarith
          · obtain hlow | hlow | hlow := repeatedLow_of_not_tripleValid
              I grp t p i j k γ hgi hgj hgk ht hi hj hk hv
            · have hniBound := hsmallCap i hi hgi hlow.2
              have hprod0 : 0 ≤ n i * n k := mul_nonneg hni hnk
              have hprodBound : n i * n i * n k ≤ 2 * a * (n i * n k) := by
                have hmul := mul_nonneg (sub_nonneg.mpr hniBound) hprod0
                nlinarith
              have hr₂ : 0 ≤ r₂ i j k := by dsimp [r₂]; split_ifs <;> positivity
              have hr₃ : 0 ≤ r₃ i j k := by dsimp [r₃]; split_ifs <;> positivity
              have htLow : t p i ≤ 2 := hlow.2
              have hji : j = i := hlow.1.symm
              subst j
              simp [b, v, r₁, hgi, hgj, hgk, hv, htLow]
              nlinarith
            · have hnjBound := hsmallCap j hj hgj hlow.2
              have hprod0 : 0 ≤ n i * n j := mul_nonneg hni hnj
              have hprodBound : n i * n j * n j ≤ 2 * a * (n i * n j) := by
                have hmul := mul_nonneg (sub_nonneg.mpr hnjBound) hprod0
                nlinarith
              have hr₁ : 0 ≤ r₁ i j k := by dsimp [r₁]; split_ifs <;> positivity
              have hr₃ : 0 ≤ r₃ i j k := by dsimp [r₃]; split_ifs <;> positivity
              have htLow : t p j ≤ 2 := hlow.2
              have hkj : k = j := hlow.1.symm
              subst k
              simp [b, v, r₂, hgi, hgj, hgk, hv, htLow]
              nlinarith
            · have hniBound := hsmallCap i hi hgi hlow.2
              have hprod0 : 0 ≤ n i * n j := mul_nonneg hni hnj
              have hprodBound : n i * n i * n j ≤ 2 * a * (n i * n j) := by
                have hmul := mul_nonneg (sub_nonneg.mpr hniBound) hprod0
                nlinarith
              have hr₁ : 0 ≤ r₁ i j k := by dsimp [r₁]; split_ifs <;> positivity
              have hr₂ : 0 ≤ r₂ i j k := by dsimp [r₂]; split_ifs <;> positivity
              have htLow : t p i ≤ 2 := hlow.2
              have hki : k = i := hlow.1.symm
              subst k
              simp [b, v, r₃, hgi, hgj, hgk, hv, htLow]
              nlinarith
        · simp [b, v, hgi, hgj, hgk]
          positivity
      · simp [b, v, hgi, hgj]
        positivity
    · simp [b, v, hgi]
      positivity
  have hall : w ^ 3 = ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, b i * b j * b k := by
    have h2 : w ^ 2 = ∑ i ∈ I, ∑ j ∈ I, b i * b j := by
      dsimp [w, d4GroupMass, b]
      rw [pow_two, Finset.sum_mul_sum]
    calc
      w ^ 3 = w ^ 2 * w := by ring
      _ = (∑ i ∈ I, ∑ j ∈ I, b i * b j) * (∑ k ∈ I, b k) := by
        rw [h2]
        rfl
      _ = ∑ i ∈ I, ∑ k ∈ I, (∑ j ∈ I, b i * b j) * b k := by
        rw [Finset.sum_mul_sum]
      _ = ∑ i ∈ I, ∑ k ∈ I, ∑ j ∈ I, (b i * b j) * b k := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_mul]
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, b i * b j * b k := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
  let bad₁ : ℝ := ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, r₁ i j k
  let bad₂ : ℝ := ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, r₂ i j k
  let bad₃ : ℝ := ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, r₃ i j k
  have hConst : ∑ i ∈ I, ∑ j ∈ I, 2 * a * b i * b j = 2 * a * w ^ 2 := by
    calc
      ∑ i ∈ I, ∑ j ∈ I, 2 * a * b i * b j =
          2 * a * ∑ i ∈ I, ∑ j ∈ I, b i * b j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 2 * a * (∑ i ∈ I, b i) ^ 2 := by
        rw [← Finset.sum_mul_sum]
        ring
      _ = 2 * a * w ^ 2 := by simp [w, d4GroupMass, b]
  have hsumAll : w ^ 3 ≤ d3ValidGroupMass I n grp t p γ + bad₁ + bad₂ + bad₃ := by
    rw [hall]
    calc
      ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, b i * b j * b k ≤
          ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, (v i j k + r₁ i j k + r₂ i j k + r₃ i j k) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact hpoint i hi j hj k hk
      _ = d3ValidGroupMass I n grp t p γ + bad₁ + bad₂ + bad₃ := by
        simp [d3ValidGroupMass, bad₁, bad₂, bad₃, v, Finset.sum_add_distrib]
  have hR₁point : ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I,
      r₁ i j k ≤ (if i = j then 2 * a * b j * b k else 0) := by
    intro i hi j hj k hk
    by_cases hcond : i = j ∧ grp p i = some γ ∧ grp p k = some γ ∧ t p i ≤ 2
    · rcases hcond with ⟨hij, hgi, hgk, hti⟩
      have hbound := hsmallCap i hi hgi hti
      have hgj : grp p j = some γ := by simpa [hij] using hgi
      have htj : t p j ≤ 2 := by simpa [hij] using hti
      have hprod0 : 0 ≤ n i * n k := mul_nonneg (hn i hi) (hn k hk)
      have hprodBound : n i * n i * n k ≤ 2 * a * (n i * n k) := by
        have hmul := mul_nonneg (sub_nonneg.mpr hbound) hprod0
        nlinarith
      simpa [r₁, b, hgi, hgj, hgk, hij, htj, mul_assoc, mul_left_comm, mul_comm] using hprodBound
    · by_cases hij : i = j
      · have hnot : ¬ (grp p j = some γ ∧ grp p k = some γ ∧ t p j ≤ 2) := by
          simpa [hij] using hcond
        have hbj : 0 ≤ b j := by
          dsimp [b]
          split_ifs with h
          · exact hn j hj
          · exact le_rfl
        have hbk : 0 ≤ b k := by
          dsimp [b]
          split_ifs with h
          · exact hn k hk
          · exact le_rfl
        have hnonneg : 0 ≤ 2 * a * b j * b k :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) hbj) hbk
        have hzero : r₁ i j k = 0 := by
          dsimp [r₁]
          simp [hij, hnot]
        rw [hzero]
        simpa [hij] using hnonneg
      · simp [r₁, b, hcond, hij]
  have hR₁ : bad₁ ≤ 2 * a * w ^ 2 := by
    calc
      bad₁ ≤ ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I,
          (if i = j then 2 * a * b j * b k else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact hR₁point i hi j hj k hk
      _ = ∑ j ∈ I, ∑ k ∈ I, 2 * a * b j * b k := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hj]
      _ = 2 * a * w ^ 2 := hConst
  have hR₂point : ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I,
      r₂ i j k ≤ (if j = k then 2 * a * b i * b k else 0) := by
    intro i hi j hj k hk
    by_cases hcond : j = k ∧ grp p i = some γ ∧ grp p j = some γ ∧ t p j ≤ 2
    · rcases hcond with ⟨hjk, hgi, hgj, htj⟩
      have hgk : grp p k = some γ := by simpa [hjk] using hgj
      have htk : t p k ≤ 2 := by simpa [hjk] using htj
      have hbound := hsmallCap k hk hgk htk
      have hprod0 : 0 ≤ n i * n k := mul_nonneg (hn i hi) (hn k hk)
      have hprodBound : n i * n k * n k ≤ 2 * a * (n i * n k) := by
        have hmul := mul_nonneg (sub_nonneg.mpr hbound) hprod0
        nlinarith
      simpa [r₂, b, hgi, hgj, hgk, hjk, htk, mul_assoc, mul_left_comm, mul_comm] using hprodBound
    · by_cases hjk : j = k
      · have hnot : ¬ (grp p i = some γ ∧ grp p j = some γ ∧ t p j ≤ 2) := by
          simpa [hjk] using hcond
        have hbi : 0 ≤ b i := by
          dsimp [b]
          split_ifs with h
          · exact hn i hi
          · exact le_rfl
        have hbk : 0 ≤ b k := by
          dsimp [b]
          split_ifs with h
          · exact hn k hk
          · exact le_rfl
        have hnonneg : 0 ≤ 2 * a * b i * b k :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) hbi) hbk
        have hnotCond : ¬ (grp p i = some γ ∧ grp p k = some γ ∧ t p k ≤ 2) := by
          intro h
          apply hcond
          refine ⟨hjk, h.1, ?_, ?_⟩
          · simpa [hjk] using h.2.1
          · simpa [hjk] using h.2.2
        have hzero : r₂ i j k = 0 := by
          dsimp [r₂]
          simp [hjk, hnotCond]
        rw [hzero]
        simpa [hjk] using hnonneg
      · simp [r₂, b, hcond, hjk]
  have hR₂ : bad₂ ≤ 2 * a * w ^ 2 := by
    calc
      bad₂ ≤ ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I,
          (if j = k then 2 * a * b i * b k else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact hR₂point i hi j hj k hk
      _ = ∑ i ∈ I, ∑ j ∈ I, 2 * a * b i * b j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp [hj]
      _ = 2 * a * w ^ 2 := hConst
  have hR₃point : ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I,
      r₃ i j k ≤ (if i = k then 2 * a * b i * b j else 0) := by
    intro i hi j hj k hk
    by_cases hcond : i = k ∧ grp p i = some γ ∧ grp p j = some γ ∧ t p i ≤ 2
    · rcases hcond with ⟨hik, hgi, hgj, hti⟩
      have hgk : grp p k = some γ := by simpa [hik] using hgi
      have hbound := hsmallCap i hi hgi hti
      have hprod0 : 0 ≤ n i * n j := mul_nonneg (hn i hi) (hn j hj)
      have hprodBound : n i * n i * n j ≤ 2 * a * (n i * n j) := by
        have hmul := mul_nonneg (sub_nonneg.mpr hbound) hprod0
        nlinarith
      have htk : t p k ≤ 2 := by simpa [hik] using hti
      simpa [r₃, b, hgi, hgj, hgk, hik, hti, htk, mul_assoc, mul_left_comm, mul_comm]
        using hprodBound
    · by_cases hik : i = k
      · have hnot : ¬ (grp p i = some γ ∧ grp p j = some γ ∧ t p i ≤ 2) := by
          simpa [hik] using hcond
        have hbi : 0 ≤ b i := by
          dsimp [b]
          split_ifs with h
          · exact hn i hi
          · exact le_rfl
        have hbj : 0 ≤ b j := by
          dsimp [b]
          split_ifs with h
          · exact hn j hj
          · exact le_rfl
        have hnonneg : 0 ≤ 2 * a * b i * b j :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) hbi) hbj
        have hnotCond : ¬ (grp p k = some γ ∧ grp p j = some γ ∧ t p k ≤ 2) := by
          intro h
          apply hcond
          refine ⟨hik, ?_, h.2.1, ?_⟩
          · simpa [hik] using h.1
          · simpa [hik] using h.2.2
        have hzero : r₃ i j k = 0 := by
          dsimp [r₃]
          simp [hik, hnotCond]
        rw [hzero]
        simpa [hik] using hnonneg
      · simp [r₃, b, hcond, hik]
  have hR₃ : bad₃ ≤ 2 * a * w ^ 2 := by
    calc
      bad₃ ≤ ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I,
          (if i = k then 2 * a * b i * b j else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact hR₃point i hi j hj k hk
      _ = ∑ i ∈ I, ∑ j ∈ I, 2 * a * b i * b j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp [hi]
      _ = 2 * a * w ^ 2 := hConst
  have hmain : w ^ 3 ≤ d3ValidGroupMass I n grp t p γ + 6 * a * w ^ 2 := by
    calc
      w ^ 3 ≤ d3ValidGroupMass I n grp t p γ + bad₁ + bad₂ + bad₃ := hsumAll
      _ ≤ d3ValidGroupMass I n grp t p γ + 6 * a * w ^ 2 := by nlinarith [hR₁, hR₂, hR₃]
  have hlarge' : 12 * a < w := by dsimp [a, w]; linarith
  have hwpos : 0 < w := by nlinarith [ha, hlarge']
  have hAbsorb : 6 * a * w ^ 2 ≤ w ^ 3 / 2 := by
    have hgap : 0 ≤ (w - 12 * a) * w ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg w)
    nlinarith
  have : w ^ 3 ≤ d3ValidGroupMass I n grp t p γ + w ^ 3 / 2 := by
    calc
      w ^ 3 ≤ d3ValidGroupMass I n grp t p γ + 6 * a * w ^ 2 := hmain
      _ ≤ d3ValidGroupMass I n grp t p γ + w ^ 3 / 2 := by nlinarith [hAbsorb]
  nlinarith

/-- `geo:terminal.d3-core` (`secants.tex:487–512`), abstract. As `terminal_d4_core`, with map
degrees `t p i ≥ 1`, masses `n_i ≤ C₁ M t_i e_γ`, and the triple–center bound
`Σ_{p : (i,j,k) valid at p} e_γ⁻² ≤ C₂` for every ordered triple. Then the grouped weight is at
most `12 C₁ M N E + (2 C₂)^{1/3} N^{5/3} E^{2/3}`. -/
theorem terminal_d3_core {α ι β : Type*} [DecidableEq ι] (Pc : Finset α) (I : Finset ι)
    (n : ι → ℝ) (grp : α → ι → Option β) (e : α → β → ℝ) (t : α → ι → ℕ) (N M E C₁ C₂ : ℝ)
    (hM : 0 ≤ M) (hE0 : 0 ≤ E)
    (hPc : (Pc.card : ℝ) ≤ N) (hn : ∀ i ∈ I, 0 ≤ n i) (hsum : ∑ i ∈ I, n i ≤ N)
    (he : ∀ p ∈ Pc, ∀ γ, 1 ≤ e p γ)
    (Γ : α → Finset β) (hΓ : ∀ p ∈ Pc, ∀ i ∈ I, ∀ γ, grp p i = some γ → γ ∈ Γ p)
    (hE : ∀ p ∈ Pc, ∑ γ ∈ Γ p, e p γ ≤ E)
    (ht : ∀ p ∈ Pc, ∀ i ∈ I, 1 ≤ t p i)
    (hC₁ : 0 < C₁)
    (hmass : ∀ p ∈ Pc, ∀ i ∈ I, ∀ γ, grp p i = some γ → n i ≤ C₁ * M * t p i * e p γ)
    (hC₂ : 0 ≤ C₂)
    (htriple : ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I,
      ∑ p ∈ Pc, ∑ γ ∈ Γ p,
        (if grp p i = some γ ∧ TripleValid grp t p i j k then (e p γ)⁻¹ ^ 2 else 0) ≤ C₂) :
    groupedWeight Pc I n grp ≤
      12 * C₁ * M * N * E + (2 * C₂) ^ ((1 : ℝ) / 3) * N ^ ((5 : ℝ) / 3) * E ^ ((2 : ℝ) / 3) := by
  classical
  let G := Pc.sigma Γ
  let w := d4GroupMass I n grp
  let threshold := 12 * C₁ * M
  let small := G.filter (fun z => w z.1 z.2 ≤ threshold * e z.1 z.2)
  let large := G.filter (fun z => threshold * e z.1 z.2 < w z.1 z.2)
  have hN0 : 0 ≤ N := by
    have hc : 0 ≤ (Pc.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hfactor0 : 0 ≤ threshold := by dsimp [threshold]; positivity
  have hsumN0 : 0 ≤ ∑ i ∈ I, n i := Finset.sum_nonneg fun i hi => hn i hi
  have htotal : groupedWeight Pc I n grp = ∑ z ∈ G, w z.1 z.2 := by
    simpa [G, w] using groupedWeight_eq_sigma Pc I n grp Γ hΓ
  have hmassE : ∑ z ∈ G, e z.1 z.2 ≤ N * E := by
    rw [Finset.sum_sigma]
    calc
      ∑ p ∈ Pc, ∑ γ ∈ Γ p, e p γ ≤ ∑ p ∈ Pc, E :=
        Finset.sum_le_sum fun p hp => hE p hp
      _ = (Pc.card : ℝ) * E := by simp
      _ ≤ N * E := mul_le_mul_of_nonneg_right hPc hE0
  have hw0 : ∀ z ∈ G, 0 ≤ w z.1 z.2 := by
    intro z hz
    dsimp [w, d4GroupMass]
    exact Finset.sum_nonneg fun i hi => by
      split_ifs
      · exact hn i hi
      · exact le_rfl
  have hsplit : ∑ z ∈ G, w z.1 z.2 =
      (∑ z ∈ small, w z.1 z.2) + (∑ z ∈ large, w z.1 z.2) := by
    rw [← Finset.sum_filter_add_sum_filter_not G
      (fun z => w z.1 z.2 ≤ threshold * e z.1 z.2) (fun z => w z.1 z.2)]
    simp [small, large, threshold, not_le]
  have hsmall : ∑ z ∈ small, w z.1 z.2 ≤ 12 * C₁ * M * N * E := by
    calc
      ∑ z ∈ small, w z.1 z.2 ≤ ∑ z ∈ small, threshold * e z.1 z.2 :=
        Finset.sum_le_sum fun z hz => (Finset.mem_filter.mp hz).2
      _ ≤ ∑ z ∈ G, threshold * e z.1 z.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
          intro z hz _
          exact mul_nonneg hfactor0
            (le_trans (by norm_num) (he z.1 (Finset.mem_sigma.mp hz).1 z.2)))
      _ = threshold * ∑ z ∈ G, e z.1 z.2 := by rw [Finset.mul_sum]
      _ ≤ threshold * (N * E) := mul_le_mul_of_nonneg_left hmassE hfactor0
      _ = 12 * C₁ * M * N * E := by dsimp [threshold]; ring
  have htripleG : ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I,
      ∑ z ∈ G,
        (if grp z.1 i = some z.2 ∧ TripleValid grp t z.1 i j k
          then (e z.1 z.2)⁻¹ ^ 2 else 0) ≤ C₂ := by
    intro i hi j hj k hk
    simpa [G, Finset.sum_sigma] using htriple i hi j hj k hk
  have hCubeScale :
      ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, n i * n j * n k * C₂ =
        C₂ * (∑ i ∈ I, n i) ^ 3 := by
    calc
      ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, n i * n j * n k * C₂ =
          C₂ * ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, n i * n j * n k := by
        simp_rw [← Finset.sum_mul]
        ring
      _ = C₂ * (∑ i ∈ I, n i) ^ 3 := by
        rw [finset_sum_cube]
  have henergy :
      ∑ z ∈ G, d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2 ≤
        C₂ * (∑ i ∈ I, n i) ^ 3 := by
    calc
      ∑ z ∈ G, d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2 =
          ∑ z ∈ G, ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I,
            n i * n j * n k *
              (if grp z.1 i = some z.2 ∧ TripleValid grp t z.1 i j k
                then (e z.1 z.2)⁻¹ ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        dsimp [d3ValidGroupMass]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hc : grp z.1 i = some z.2 ∧ TripleValid grp t z.1 i j k
        · simp [hc, div_eq_mul_inv, inv_pow, pow_two, mul_assoc, mul_left_comm, mul_comm]
        · simp [hc]
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I,
            n i * n j * n k * ∑ z ∈ G,
              (if grp z.1 i = some z.2 ∧ TripleValid grp t z.1 i j k
                then (e z.1 z.2)⁻¹ ^ 2 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.mul_sum]
      _ ≤ ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, n i * n j * n k * C₂ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        have hc := htripleG i hi j hj k hk
        have hnprod : 0 ≤ n i * n j * n k :=
          mul_nonneg (mul_nonneg (hn i hi) (hn j hj)) (hn k hk)
        exact mul_le_mul_of_nonneg_left hc hnprod
      _ = C₂ * (∑ i ∈ I, n i) ^ 3 := hCubeScale
  have henergyN :
      ∑ z ∈ G, d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2 ≤ C₂ * N ^ 3 := by
    have hsumCube : (∑ i ∈ I, n i) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ hsumN0 hsum 3
    exact le_trans henergy (mul_le_mul_of_nonneg_left hsumCube hC₂)
  have hV0 : ∀ z ∈ G, 0 ≤ d3ValidGroupMass I n grp t z.1 z.2 := by
    intro z hz
    dsimp [d3ValidGroupMass]
    exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      Finset.sum_nonneg fun k hk => by
        split_ifs with hc
        · exact mul_nonneg (mul_nonneg (hn i hi) (hn j hj)) (hn k hk)
        · exact le_rfl
  have hlargeEnergy :
      ∑ z ∈ large, w z.1 z.2 ^ 3 / (e z.1 z.2) ^ 2 ≤ 2 * C₂ * N ^ 3 := by
    calc
      ∑ z ∈ large, w z.1 z.2 ^ 3 / (e z.1 z.2) ^ 2 ≤
          ∑ z ∈ large, 2 * (d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2) := by
        apply Finset.sum_le_sum
        intro z hz
        have hzG : z ∈ G := (Finset.mem_filter.mp hz).1
        have hp : z.1 ∈ Pc := (Finset.mem_sigma.mp hzG).1
        have hez : 1 ≤ e z.1 z.2 := he z.1 hp z.2
        have hcub := d3GroupMass_cube_lower I n grp t z.1 z.2 M C₁ e hM hC₁ hez
          hn (ht z.1 hp) (fun i hi hgi => hmass z.1 hp i hi z.2 hgi)
          (Finset.mem_filter.mp hz).2
        calc
          w z.1 z.2 ^ 3 / (e z.1 z.2) ^ 2 ≤
              (2 * d3ValidGroupMass I n grp t z.1 z.2) / (e z.1 z.2) ^ 2 :=
            div_le_div_of_nonneg_right hcub (sq_nonneg (e z.1 z.2))
          _ = 2 * (d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2) := by ring
      _ ≤ 2 * ∑ z ∈ G, d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2 := by
        have hsub :
            (∑ z ∈ large, d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2) ≤
              ∑ z ∈ G, d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro z hz _
            exact div_nonneg (hV0 z hz) (sq_nonneg (e z.1 z.2))
        calc
          ∑ z ∈ large, 2 * (d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2) =
              2 * ∑ z ∈ large, d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2 := by
            rw [Finset.mul_sum]
          _ ≤ 2 * ∑ z ∈ G, d3ValidGroupMass I n grp t z.1 z.2 / (e z.1 z.2) ^ 2 :=
            mul_le_mul_of_nonneg_left hsub (by norm_num)
      _ ≤ 2 * C₂ * N ^ 3 := by nlinarith [henergyN]
  have hsumElarge : ∑ z ∈ large, e z.1 z.2 ≤ N * E :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun z hz _ => le_trans (by norm_num) (he z.1 (Finset.mem_sigma.mp hz).1 z.2))) hmassE
  let ew : (Σ p : α, β) → ℝ := fun z => if z ∈ G then e z.1 z.2 else 0
  let fw : (Σ p : α, β) → ℝ := fun z =>
    if z ∈ G then w z.1 z.2 / e z.1 z.2 else 0
  have hew0 : ∀ z, 0 ≤ ew z := by
    intro z
    dsimp [ew]
    split_ifs with hz
    · exact le_trans (by norm_num) (he z.1 (Finset.mem_sigma.mp hz).1 z.2)
    · exact le_rfl
  have hfw0 : ∀ z, 0 ≤ fw z := by
    intro z
    dsimp [fw]
    split_ifs with hz
    · have hwz : 0 ≤ w z.1 z.2 := by
        dsimp [w, d4GroupMass]
        exact Finset.sum_nonneg fun i hi => by
          split_ifs
          · exact hn i hi
          · exact le_rfl
      have hepos : 0 < e z.1 z.2 := lt_of_lt_of_le zero_lt_one
        (he z.1 (Finset.mem_sigma.mp hz).1 z.2)
      exact div_nonneg hwz hepos.le
    · exact le_rfl
  have hleft : ∑ z ∈ large, ew z * fw z = ∑ z ∈ large, w z.1 z.2 := by
    apply Finset.sum_congr rfl
    intro z hz
    have hzG : z ∈ G := (Finset.mem_filter.mp hz).1
    have hepos : 0 < e z.1 z.2 := lt_of_lt_of_le zero_lt_one
      (he z.1 (Finset.mem_sigma.mp hzG).1 z.2)
    simp [ew, fw, hzG]
    field_simp [ne_of_gt hepos]
  have hright :
      ∑ z ∈ large, ew z * (fw z) ^ 3 =
        ∑ z ∈ large, w z.1 z.2 ^ 3 / (e z.1 z.2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro z hz
    have hzG : z ∈ G := (Finset.mem_filter.mp hz).1
    have hepos : 0 < e z.1 z.2 := lt_of_lt_of_le zero_lt_one
      (he z.1 (Finset.mem_sigma.mp hzG).1 z.2)
    simp [ew, fw, hzG]
    field_simp [ne_of_gt hepos]
  have hholder : ∑ z ∈ large, w z.1 z.2 ≤
      (∑ z ∈ large, ew z) ^ ((2 : ℝ) / 3) *
        (∑ z ∈ large, w z.1 z.2 ^ 3 / (e z.1 z.2) ^ 2) ^ ((1 : ℝ) / 3) := by
    have hh := Real.inner_le_weight_mul_Lp_of_nonneg large (p := 3) (by norm_num)
      ew fw hew0 hfw0
    have hh' : ∑ z ∈ large, ew z * fw z ≤
        (∑ z ∈ large, ew z) ^ ((2 : ℝ) / 3) *
          (∑ z ∈ large, ew z * fw z ^ 3) ^ ((1 : ℝ) / 3) := by
      have hh' := hh
      norm_num at hh'
      simpa using hh'
    rw [← hleft]
    simpa [hright] using hh'
  have hsumEW : ∑ z ∈ large, ew z ≤ N * E := by
    calc
      ∑ z ∈ large, ew z = ∑ z ∈ large, e z.1 z.2 := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [ew, (Finset.mem_filter.mp hz).1]
      _ ≤ N * E := hsumElarge
  have hlargeHolder : ∑ z ∈ large, w z.1 z.2 ≤
      (N * E) ^ ((2 : ℝ) / 3) * (2 * C₂ * N ^ 3) ^ ((1 : ℝ) / 3) := by
    calc
      ∑ z ∈ large, w z.1 z.2 ≤
          (∑ z ∈ large, ew z) ^ ((2 : ℝ) / 3) *
            (∑ z ∈ large, w z.1 z.2 ^ 3 / (e z.1 z.2) ^ 2) ^ ((1 : ℝ) / 3) := hholder
      _ ≤ (N * E) ^ ((2 : ℝ) / 3) * (2 * C₂ * N ^ 3) ^ ((1 : ℝ) / 3) := by
        have hlargeEnergy0 : 0 ≤ ∑ z ∈ large, w z.1 z.2 ^ 3 / (e z.1 z.2) ^ 2 :=
          Finset.sum_nonneg fun z hz => div_nonneg
            (mul_nonneg (sq_nonneg (w z.1 z.2)) (hw0 z (Finset.mem_filter.mp hz).1))
            (sq_nonneg (e z.1 z.2))
        apply mul_le_mul
        · exact Real.rpow_le_rpow (Finset.sum_nonneg fun z hz => hew0 z) hsumEW (by norm_num)
        · exact Real.rpow_le_rpow hlargeEnergy0 hlargeEnergy (by norm_num)
        · exact Real.rpow_nonneg hlargeEnergy0 _
        · exact Real.rpow_nonneg (mul_nonneg hN0 hE0) _
  have hpower :
      (N * E) ^ ((2 : ℝ) / 3) * (2 * C₂ * N ^ 3) ^ ((1 : ℝ) / 3) =
        (2 * C₂) ^ ((1 : ℝ) / 3) * N ^ ((5 : ℝ) / 3) * E ^ ((2 : ℝ) / 3) := by
    by_cases hNz : N = 0
    · simp [hNz, Real.zero_rpow]
    · have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
      have hNcube : (N ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
        norm_num
      have hNpow : N ^ ((2 : ℝ) / 3) * N = N ^ ((5 : ℝ) / 3) := by
        calc
          N ^ ((2 : ℝ) / 3) * N = N ^ ((2 : ℝ) / 3) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = N ^ ((2 : ℝ) / 3 + 1) := by rw [← Real.rpow_add hNpos]
          _ = N ^ ((5 : ℝ) / 3) := by congr 1 <;> norm_num
      calc
        (N * E) ^ ((2 : ℝ) / 3) * (2 * C₂ * N ^ 3) ^ ((1 : ℝ) / 3) =
            (N ^ ((2 : ℝ) / 3) * E ^ ((2 : ℝ) / 3)) *
              ((2 * C₂) ^ ((1 : ℝ) / 3) * N) := by
          rw [Real.mul_rpow hN0 hE0]
          rw [show 2 * C₂ * N ^ 3 = (2 * C₂) * (N ^ (3 : ℕ)) by ring]
          rw [Real.mul_rpow (mul_nonneg (by norm_num) hC₂) (by positivity), hNcube]
        _ = (2 * C₂) ^ ((1 : ℝ) / 3) * N ^ ((5 : ℝ) / 3) * E ^ ((2 : ℝ) / 3) := by
          calc
            (N ^ ((2 : ℝ) / 3) * E ^ ((2 : ℝ) / 3)) *
                ((2 * C₂) ^ ((1 : ℝ) / 3) * N) =
                (2 * C₂) ^ ((1 : ℝ) / 3) *
                  (N ^ ((2 : ℝ) / 3) * N) * E ^ ((2 : ℝ) / 3) := by ring
            _ = _ := by
              rw [hNpow]
  have hlargeSum : ∑ z ∈ large, w z.1 z.2 ≤
      (2 * C₂) ^ ((1 : ℝ) / 3) * N ^ ((5 : ℝ) / 3) * E ^ ((2 : ℝ) / 3) := by
    rw [← hpower]
    exact hlargeHolder
  rw [htotal, hsplit]
  linarith [hsmall, hlargeSum]

variable {d : ℕ}

/-- `geo:terminal.perspective` (`secants.tex:343–370`). Two distinct irreducible nonlinear curves
lying in complex affine planes `Π, Π'` have the same radial projection from at most `C deg Y`
centers outside both planes (stabilizer of a nonlinear plane curve among projectivities fixing a
line pointwise; a perspectivity determines its center). -/
theorem terminal_perspective :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y Y' : AffineVariety d) (Pl Pl' : AffineSubspace ℂ (Point d)),
      IsCurve Y → IsCurve Y' → ¬ IsLine Y → ¬ IsLine Y' → Y ≠ Y' →
      Module.finrank ℂ Pl.direction = 2 → Module.finrank ℂ Pl'.direction = 2 →
      Y.points ⊆ Pl → Y'.points ⊆ Pl' →
        CardLe {p : Point d | p ∉ Pl ∧ p ∉ Pl' ∧ radialImage p Y = radialImage p Y'}
          (C * (Y.degree : ℝ)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro Y Y' Pl Pl' hY hY' hline hline' hYY' hPl hPl' hYP hYP'
  simpa only [CardLe, perspectiveCenters, one_mul] using
    perspective_centers_degree_bound Y Y' Pl Pl' hY hY' hline hline'
      hYY' hPl hPl' hYP hYP'

/-- `geo:terminal.highmult` (`secants.tex:397–413`). A nonlinear irreducible curve has at most a
bounded number of points of multiplicity greater than half its degree (generic birational plane
projection, `poly:projection` (ii), and the polar bound `poly:polar`). -/
theorem terminal_highmult :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : AffineVariety d, IsCurve Y → ¬ IsLine Y →
      CardLe {p : Point d | Y.degree / 2 < Y.multiplicity p} C := by
  exact Bridges.curve_highmult_bound d

theorem GeoD3.radialMapDegree_eq (p : Point 3) (Y : AffineVariety 3) (hY : IsCurve Y)
    (himage : (radialImage p Y).dimension = 1) : radialMapDegree p Y = TrackA.radialMapDegree p Y := by
  have hA := TrackA.dep_radial_degree_exists Y hY.1 1 (by norm_num) hY.2 p himage
  have hex : ∃ r, GenericallyFiniteRadialDegree p Y r := ⟨_, hA⟩
  have hD : GenericallyFiniteRadialDegree p Y (radialMapDegree p Y) := by
    unfold radialMapDegree
    rw [dif_pos hex]
    exact Nat.find_spec hex
  exact GeoD3.radial_degree_unique p Y hY _ _ hD hA

theorem GeoD3.curve_valid_of_group_valid
    (Cf : Pt 3 → ProjectiveFamily.Family 3) (p : Pt 3)
    (hC : IsDirectionalFamily (Cf p)) (Y₁ Y₂ Y₃ : AffineVariety 3)
    (hY₁ : IsCurve Y₁) (hY₂ : IsCurve Y₂) (hY₃ : IsCurve Y₃)
    (hnl₁ : ¬ IsLine Y₁) (hnl₂ : ¬ IsLine Y₂) (hnl₃ : ¬ IsLine Y₃)
    (hv : TripleValid (GeoD3.group Cf) GeoD3.mapDegree p Y₁ Y₂ Y₃) :
    CurveTripleValid (toC p) Y₁ Y₂ Y₃ := by
  obtain ⟨γ, hg₁⟩ : ∃ γ, GeoD3.group Cf p Y₁ = some γ := by
    cases h : GeoD3.group Cf p Y₁ with
    | none => have hn := hv.1; simp [h] at hn
    | some γ => exact ⟨γ, rfl⟩
  have hg₂ : GeoD3.group Cf p Y₂ = some γ := hv.2.1.symm.trans hg₁
  have hg₃ : GeoD3.group Cf p Y₃ = some γ := hv.2.2.1.symm.trans hg₁
  have h₁ := (GeoD3.group_eq_some Cf p Y₁ γ).mp hg₁
  have h₂ := (GeoD3.group_eq_some Cf p Y₂ γ).mp hg₂
  have h₃ := (GeoD3.group_eq_some Cf p Y₃ γ).mp hg₃
  have himage := (GeoRadial.radial_member p Y₁ hY₁ hnl₁ (Cf p) hC h₁.1).2
  have hprops : ∀ Y ∈ ({Y₁, Y₂, Y₃} : Finset (AffineVariety 3)),
      IsCurve Y ∧ ¬ IsLine Y ∧ GeoD3.group Cf p Y = some γ := by
    intro Y hY
    have hmem : Y = Y₁ ∨ Y = Y₂ ∨ Y = Y₃ := by simpa using hY
    rcases hmem with rfl | rfl | rfl
    · exact ⟨hY₁, hnl₁, hg₁⟩
    · exact ⟨hY₂, hnl₂, hg₂⟩
    · exact ⟨hY₃, hnl₃, hg₃⟩
  refine ⟨h₁.2.2.2.trans h₂.2.2.2.symm, h₁.2.2.2.trans h₃.2.2.2.symm,
    himage, h₁.2.1, ?_, ?_⟩
  · intro Y hY
    exact ((GeoD3.group_eq_some Cf p Y γ).mp (hprops Y hY).2.2).2.2.1
  · intro Y hY
    have h := hv.2.2.2 Y hY
    rw [GeoD3.group_mapDegree_eq Cf p Y (hprops Y hY).1 (hprops Y hY).2.1 hC γ
      (hprops Y hY).2.2] at h
    rw [GeoD3.radialMapDegree_eq (toC p) Y (hprops Y hY).1
      (GeoRadial.radial_member p Y (hprops Y hY).1 (hprops Y hY).2.1 (Cf p) hC
        ((GeoD3.group_eq_some Cf p Y γ).mp (hprops Y hY).2.2).1).2]
    exact h

/-- `geo:terminal.triple` (`secants.tex:428–485`, eq. `geo:triple-center-bound`). For every ordered
triple of irreducible nonlinear curves in `ℂ^3`, the centers at which the triple is valid satisfy
`Σ_p e_γ⁻² ≤ C`, `e_γ = deg γ` the degree of the common projection. -/
theorem terminal_triple :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y₁ Y₂ Y₃ : AffineVariety 3),
      IsCurve Y₁ → IsCurve Y₂ → IsCurve Y₃ → ¬ IsLine Y₁ → ¬ IsLine Y₂ → ¬ IsLine Y₃ →
      ∀ Pc : Finset (Point 3), (∀ p ∈ Pc, CurveTripleValid p Y₁ Y₂ Y₃) →
        ∑ p ∈ Pc, (((radialImage p Y₁).degree : ℝ))⁻¹ ^ 2 ≤ C := by
  exact TripleGeneric.terminal_triple_of_fiber_multiplicity
    TriplePencil.smooth_radial_fiber_multiplicity_bound

/-- Ordered pairs `(p, q)`, `p ≠ q`, with `q` assigned to a member `Y` satisfying `sel Y` and
`closure(π_p Y) ⊆ C_p`. -/
def terminalPairsSel (P : Finset (Pt d)) (Cf : Pt d → ProjectiveFamily.Family d)
    (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d))
    (sel : AffineVariety d → Prop) : Finset (Pt d × Pt d) :=
  (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
    ∃ Y ∈ 𝒴, sel Y ∧ pq.2 ∈ S Y ∧ ProjectsInto (Cf pq.1) pq.1 Y)

/-- `geo:terminal.d4` (`secants.tex:333–389`): nonlinear curves when `d ≥ 4`. -/
theorem geo_terminal_d4 (d : ℕ) (hd : 4 ≤ d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∃ η > 0, ∃ N₀ : ℕ, ∀ P : Finset (Pt d), N₀ ≤ P.card →
      cfgM P ≤ η * cfgA P → RealFlatCap P c₀ →
      ∀ Cf : Pt d → ProjectiveFamily.Family d,
        (∀ p ∈ P, IsDirectionalFamily (Cf p) ∧
          (ProjectiveFamily.degree (Cf p) : ℝ) ≤ η * cfgN P / cfgA P) →
      ∀ (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d)),
        Assignment P 𝒴 S → (∀ Y ∈ 𝒴, IsCurve Y) →
        ((terminalPairsSel P Cf 𝒴 S (fun Y => ¬ IsLine Y)).card : ℝ) ≤ ε * cfgN P ^ 2 := by
  obtain ⟨C₁, hC₁, hsample⟩ := poly_separators_curve d
  obtain ⟨C₂, hC₂, hperspective⟩ := terminal_perspective (d := d)
  intro ε hε
  obtain ⟨η, hη, ha, hb⟩ := GeoD4.small_constants C₁ C₂ ε hC₁ hC₂ hε
  obtain ⟨N₀, hN₀⟩ := GeoD4.tail_threshold d hd c₀ ε hc₀ hε
  refine ⟨η, hη, max N₀ 1, ?_⟩
  intro P hP hM hcap Cf hCf 𝒴 S hS hcurves
  have hP1 : 1 ≤ P.card := (le_max_right _ _).trans hP
  obtain ⟨hN1, hA1, hM0⟩ := GeoD4.scales P hP1
  let I := GeoD4.planarCurves 𝒴
  let n : AffineVariety d → ℝ := fun Y => (S Y).card
  let grp := GeoD4.exteriorGroup Cf
  let e : Pt d → ProjectiveVariety d → ℝ := fun _ γ => GeoD4.groupDegree γ
  let E := η * cfgN P / cfgA P
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hI : I ⊆ 𝒴 := Finset.filter_subset _ _
  have hprops : ∀ Y ∈ I, Y ∈ 𝒴 ∧ ¬ IsLine Y ∧
      Module.finrank ℂ (complexSpan Y).direction = 2 := by
    intro Y hY
    exact Finset.mem_filter.mp hY
  have hsum : ∑ Y ∈ I, n Y ≤ cfgN P :=
    GeoCounting.assignment_sum_le P 𝒴 S hS I hI
  have hn : ∀ Y ∈ I, 0 ≤ n Y := fun Y _ => Nat.cast_nonneg _
  have he : ∀ p ∈ P, ∀ γ, 1 ≤ e p γ := fun _ _ _ => le_max_left _ _
  have hΓ : ∀ p ∈ P, ∀ Y ∈ I, ∀ γ, grp p Y = some γ → γ ∈ Cf p := by
    intro p hp Y hY γ hgrp
    exact GeoD4.group_mem Cf p Y (hcurves Y (hI hY)) (hprops Y hY).2.1
      (hCf p hp).1 γ hgrp
  have hE : ∀ p ∈ P, ∑ γ ∈ Cf p, e p γ ≤ E := by
    intro p hp
    change (∑ γ ∈ Cf p, GeoD4.groupDegree γ) ≤ E
    rw [GeoD4.degree_sum (Cf p) (hCf p hp).1]
    exact (hCf p hp).2
  have hmass : ∀ p ∈ P, ∀ Y ∈ I, ∀ γ, grp p Y = some γ → n Y ≤ C₁ * cfgM P * e p γ := by
    intro p hp Y hY γ hgrp
    have hYC := hcurves Y (hI hY)
    exact GeoD4.group_mass_le P 𝒴 S hS Cf p (hCf p hp).1 Y (hI hY) hYC
      (hprops Y hY).2.1 γ hgrp C₁ (hsample P Y hYC)
  have hpair : ∀ Y ∈ I, ∀ Y' ∈ I, Y ≠ Y' →
      (∑ p ∈ P, ∑ γ ∈ Cf p,
        if grp p Y = some γ ∧ grp p Y' = some γ then (e p γ)⁻¹ else 0) ≤ C₂ := by
    intro Y hY Y' hY' hne
    have hYC := hcurves Y (hI hY)
    have hY'C := hcurves Y' (hI hY')
    obtain ⟨hfin, hcard⟩ := hperspective Y Y' (complexSpan Y) (complexSpan Y')
      hYC hY'C (hprops Y hY).2.1 (hprops Y' hY').2.1 hne
      (hprops Y hY).2.2 (hprops Y' hY').2.2 (subset_affineSpan ℂ _) (subset_affineSpan ℂ _)
    exact GeoD4.pair_sum_le P Cf (fun p hp => (hCf p hp).1) Y Y' hYC
      (hprops Y hY).2.1 C₂ hfin hcard
  have hcore := terminal_d4_core P I n grp e (cfgN P) (cfgM P) E C₁ C₂
    hM0 hE0 (by unfold cfgN; exact le_rfl) hn hsum he Cf hΓ hE hC₁ hmass hC₂.le hpair
  have hcover := GeoD4.nonlinear_pair_bound d hd P c₀ hcap Cf
    (fun p hp => (hCf p hp).1) 𝒴 S hS hcurves
  have hcount : ((terminalPairsSel P Cf 𝒴 S (fun Y => ¬ IsLine Y)).card : ℝ) ≤
      cfgN P ^ 2 * cfgB P ^ (-c₀) + groupedWeight P I n grp := by
    simpa only [terminalPairsSel, groupedWeight, I, n, grp] using hcover
  have htail := hN₀ P ((le_max_left _ _).trans hP)
  calc
    _ ≤ _ := hcount
    _ ≤ cfgN P ^ 2 * cfgB P ^ (-c₀) +
        (2 * C₁ * cfgM P * cfgN P * E + Real.sqrt (2 * C₂ * E) * cfgN P ^ ((3 : ℝ) / 2)) :=
      add_le_add le_rfl hcore
    _ = cfgN P ^ 2 * cfgB P ^ (-c₀) + 2 * C₁ * cfgM P * cfgN P * E +
        Real.sqrt (2 * C₂ * E) * cfgN P ^ ((3 : ℝ) / 2) := by ring
    _ ≤ _ := GeoD4.core_rhs (cfgN P) (cfgA P) (cfgM P) η C₁ C₂ (cfgB P ^ (-c₀)) ε
      hN1 hA1 hM0 hM hη.le hC₁.le hC₂.le ha hb htail

/-- `geo:terminal.d3` (`secants.tex:391–512`): nonlinear curves when `d = 3`. -/
theorem geo_terminal_d3 (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∃ η > 0, ∃ N₀ : ℕ, ∀ P : Finset (Pt 3), N₀ ≤ P.card →
      cfgM P ≤ η * cfgA P → RealFlatCap P c₀ →
      ∀ Cf : Pt 3 → ProjectiveFamily.Family 3,
        (∀ p ∈ P, IsDirectionalFamily (Cf p) ∧
          (ProjectiveFamily.degree (Cf p) : ℝ) ≤ η * cfgN P / cfgA P) →
      ∀ (𝒴 : Finset (AffineVariety 3)) (S : AffineVariety 3 → Finset (Pt 3)),
        Assignment P 𝒴 S → (∀ Y ∈ 𝒴, IsCurve Y) →
        ((terminalPairsSel P Cf 𝒴 S (fun Y => ¬ IsLine Y)).card : ℝ) ≤ ε * cfgN P ^ 2 := by
  obtain ⟨C, hC, hsample⟩ := poly_separators_curve 3
  obtain ⟨C₂, hC₂, htriple⟩ := terminal_triple
  obtain ⟨H, hH, hhigh⟩ := terminal_highmult (d := 3)
  intro ε hε
  obtain ⟨η, hη, hη1, ha⟩ := GeoD3.small_constant (2*C) ε (by positivity) hε
  let K := (2*C₂)^((1:ℝ)/3)
  obtain ⟨N₀, hN₀⟩ := GeoD3.tail_threshold c₀ ε H K hc₀ hε
  refine ⟨η, hη, max N₀ 1, ?_⟩
  intro P hP hM hcap Cf hCf 𝒴 S hS hcurves
  have hP1 : 1 ≤ P.card := (le_max_right _ _).trans hP
  obtain ⟨hN1, hA1, hM0⟩ := GeoD4.scales P hP1
  let I := GeoD3.nonlinearCurves 𝒴
  let n : AffineVariety 3 → ℝ := fun Y => (S Y).card
  let grp := GeoD3.group Cf
  let e : Pt 3 → ProjectiveVariety 3 → ℝ := fun _ γ => GeoD4.groupDegree γ
  let t := GeoD3.mapDegree
  let E := η*cfgN P/cfgA P
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hI : I ⊆ 𝒴 := Finset.filter_subset _ _
  have hnl : ∀ Y ∈ I, ¬ IsLine Y := fun Y hY => (Finset.mem_filter.mp hY).2
  have hsum : ∑ Y ∈ I, n Y ≤ cfgN P :=
    GeoCounting.assignment_sum_le P 𝒴 S hS I hI
  have hn : ∀ Y ∈ I, 0 ≤ n Y := fun Y _ => Nat.cast_nonneg _
  have he : ∀ p ∈ P, ∀ γ, 1 ≤ e p γ := fun _ _ _ => le_max_left _ _
  have ht : ∀ p ∈ P, ∀ Y ∈ I, 1 ≤ t p Y := fun _ _ _ _ => le_max_left _ _
  have hΓ : ∀ p ∈ P, ∀ Y ∈ I, ∀ γ, grp p Y = some γ → γ ∈ Cf p := by
    intro p hp Y hY γ hg
    exact GeoD3.group_mem Cf p Y (hcurves Y (hI hY)) (hnl Y hY) (hCf p hp).1 γ hg
  have hE : ∀ p ∈ P, ∑ γ ∈ Cf p, e p γ ≤ E := by
    intro p hp
    change (∑ γ ∈ Cf p, GeoD4.groupDegree γ) ≤ E
    rw [GeoD4.degree_sum (Cf p) (hCf p hp).1]
    exact (hCf p hp).2
  have hmass : ∀ p ∈ P, ∀ Y ∈ I, ∀ γ, grp p Y = some γ →
      n Y ≤ (2*C)*cfgM P*t p Y*e p γ := by
    intro p hp Y hY γ hg
    exact GeoD3.group_mass_le P 𝒴 S hS Cf p (hCf p hp).1 Y (hI hY)
      (hcurves Y (hI hY)) (hnl Y hY) γ hg C hC.le (hsample P Y (hcurves Y (hI hY)))
  have htriples : ∀ Y₁ ∈ I, ∀ Y₂ ∈ I, ∀ Y₃ ∈ I,
      (∑ p ∈ P, ∑ γ ∈ Cf p,
        if grp p Y₁ = some γ ∧ TripleValid grp t p Y₁ Y₂ Y₃ then (e p γ)⁻¹ ^ 2 else 0) ≤ C₂ := by
    intro Y₁ hY₁ Y₂ hY₂ Y₃ hY₃
    let Q := fun p => TripleValid grp t p Y₁ Y₂ Y₃
    let Pc := (P.filter Q).image toC
    have hvalid : ∀ z ∈ Pc, CurveTripleValid z Y₁ Y₂ Y₃ := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hpP, hpQ⟩ := Finset.mem_filter.mp hp
      exact GeoD3.curve_valid_of_group_valid Cf p (hCf p hpP).1 Y₁ Y₂ Y₃
        (hcurves Y₁ (hI hY₁)) (hcurves Y₂ (hI hY₂)) (hcurves Y₃ (hI hY₃))
        (hnl Y₁ hY₁) (hnl Y₂ hY₂) (hnl Y₃ hY₃) hpQ
    have hbound := htriple Y₁ Y₂ Y₃ (hcurves Y₁ (hI hY₁)) (hcurves Y₂ (hI hY₂))
      (hcurves Y₃ (hI hY₃)) (hnl Y₁ hY₁) (hnl Y₂ hY₂) (hnl Y₃ hY₃) Pc hvalid
    exact GeoD3.group_sum_le P Cf (fun p hp => (hCf p hp).1) Y₁
      (hcurves Y₁ (hI hY₁)) (hnl Y₁ hY₁) Q C₂ hbound
  have hcore := terminal_d3_core P I n grp e t (cfgN P) (cfgM P) E (2*C) C₂
    hM0 hE0 (by unfold cfgN; exact le_rfl) hn hsum he Cf hΓ hE ht
    (by positivity) hmass hC₂.le htriples
  have hcover := GeoD3.nonlinear_pair_bound P c₀ hcap Cf
    (fun p hp => (hCf p hp).1) 𝒴 S hS hcurves H hH.le
    (fun Y hY hnl => hhigh Y (hcurves Y hY) hnl)
  have hcount : ((terminalPairsSel P Cf 𝒴 S (fun Y => ¬ IsLine Y)).card : ℝ) ≤
      H*cfgN P + cfgN P^2*cfgB P^(-c₀) + groupedWeight P I n grp := by
    simpa only [terminalPairsSel, groupedWeight, I, n, grp] using hcover
  have htail := hN₀ P ((le_max_left _ _).trans hP)
  have hA : cfgA P = (cfgN P)^((2:ℝ)/3) := by norm_num [cfgA, cfgN]
  calc
    _ ≤ _ := hcount
    _ ≤ H*cfgN P + cfgN P^2*cfgB P^(-c₀) +
      (12*(2*C)*cfgM P*cfgN P*E + (2*C₂)^((1:ℝ)/3)*cfgN P^((5:ℝ)/3)*E^((2:ℝ)/3)) :=
      add_le_add le_rfl hcore
    _ = H*cfgN P + cfgN P^2*cfgB P^(-c₀) +
      12*(2*C)*cfgM P*cfgN P*(η*cfgN P/(cfgN P)^((2:ℝ)/3)) +
      K*cfgN P^((5:ℝ)/3)*(η*cfgN P/(cfgN P)^((2:ℝ)/3))^((2:ℝ)/3) := by
      dsimp only [E, K]; rw [hA]; ring
    _ ≤ _ := GeoD3.core_rhs (cfgN P) (cfgM P) η (2*C) K H (cfgB P^(-c₀)) ε
      hN1 hM0 (by rwa [← hA]) hη.le hη1 (by positivity) (by dsimp [K]; positivity) ha htail

end

end TrackD
end DistinctDistances
