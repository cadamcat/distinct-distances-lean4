import DistinctDistances.TrackC.Polynomial
import DistinctDistances.TrackC.RichLinePruning

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Samples on at least three contained lines are critical or flat. -/
theorem three_contained_lines_point (f : Poly 3) (A : Finset (Line 3))
    (hA : ∀ l ∈ A,onPolynomial f l) (x : E 3) (hx : 3 ≤ lineMultiplicity A x) :
    criticalPoint f x ∨ flatPoint f x := by
  have hc : 2 < (A.filter (fun l => x ∈ l.1)).card := by
    change 3 ≤ (A.filter (fun l => x ∈ l.1)).card at hx
    omega
  obtain ⟨l₁,l₂,l₃,hl₁,hl₂,hl₃,h12,h13,h23⟩ := Finset.two_lt_card_iff.mp hc
  exact three_lines_critical_or_flat f x l₁ l₂ l₃ h12 h13 h23
    (hA l₁ (Finset.mem_filter.mp hl₁).1) (hA l₂ (Finset.mem_filter.mp hl₂).1)
    (hA l₃ (Finset.mem_filter.mp hl₃).1) (Finset.mem_filter.mp hl₁).2
    (Finset.mem_filter.mp hl₂).2 (Finset.mem_filter.mp hl₃).2

/-- Many critical-or-flat samples force one of the two line properties. -/
theorem critical_or_flat_line_of_many (f : Poly 3) (l : Line 3) (T : Finset (E 3))
    (hT : ∀ x ∈ T,x ∈ l.1) (htype : ∀ x ∈ T,criticalPoint f x ∨ flatPoint f x)
    (hsize : 6*(f.totalDegree:ℝ) < T.card) : criticalLine f l ∨ flatLine f l := by
  let P := T.filter (fun x => criticalPoint f x)
  let Q := T.filter (fun x => ¬criticalPoint f x)
  have hsplit : P.card+Q.card = T.card := Finset.card_filter_add_card_filter_not (s := T) (fun x => criticalPoint f x)
  by_cases hp : f.totalDegree < P.card
  · left
    apply (many_critical_flat_points f l P (fun x hx => hT x (Finset.mem_filter.mp hx).1)).1 hp
    exact fun x hx => (Finset.mem_filter.mp hx).2
  · right
    have hpR : (P.card:ℝ) ≤ f.totalDegree := by exact_mod_cast (by omega : P.card ≤ f.totalDegree)
    have hsR : (P.card:ℝ)+(Q.card:ℝ) = T.card := by exact_mod_cast hsplit
    have hq : 3*f.totalDegree < Q.card := by
      have hqR : 3*(f.totalDegree:ℝ) < Q.card := by nlinarith [show (0:ℝ) ≤ (f.totalDegree:ℝ) from Nat.cast_nonneg _]
      exact_mod_cast hqR
    apply (many_critical_flat_points f l Q (fun x hx => hT x (Finset.mem_filter.mp hx).1)).2 hq
    intro x hx
    exact (htype x (Finset.mem_filter.mp hx).1).resolve_left (Finset.mem_filter.mp hx).2

def polynomialCore (f : Poly 3) (L : Finset (Line 3)) (S : Finset (E 3)) : Finset (E 3) :=
  S.filter (fun x => 3 ≤ lineMultiplicity (L.filter (fun l => onPolynomial f l)) x)

theorem polynomialCore_subset (f : Poly 3) (L : Finset (Line 3)) (S : Finset (E 3)) :
    polynomialCore f L S ⊆ S := Finset.filter_subset _ _

theorem polynomialCore_point_type (f : Poly 3) (L : Finset (Line 3)) (S : Finset (E 3)) :
    ∀ x ∈ polynomialCore f L S,criticalPoint f x ∨ flatPoint f x := by
  intro x hx
  apply three_contained_lines_point f (L.filter (fun l => onPolynomial f l))
    (fun l hl => (Finset.mem_filter.mp hl).2) x (Finset.mem_filter.mp hx).2

theorem polynomialCore_zero (f : Poly 3) (L : Finset (Line 3)) (S : Finset (E 3)) :
    ∀ x ∈ polynomialCore f L S,evalR f x = 0 := by
  intro x hx
  rcases polynomialCore_point_type f L S x hx with h | h
  · exact h.1
  · exact h.1.1

/-- A line restriction bounds incidences on the zero set for noncontained lines. -/
theorem boundary_line_mass_three (f : Poly 3) (T : Finset (E 3))
    (hT : ∀ x ∈ T,evalR f x = 0) (L : Finset (Line 3))
    (hL : ∀ l ∈ L,¬onPolynomial f l) :
    relationMass T L (fun x l => x ∈ l.1) ≤ (L.card:ℝ)*f.totalDegree := by
  rw [relationMass_swap,relationMass_sum_card]
  calc
    _ ≤ ∑ _l ∈ L,(f.totalDegree:ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      let U := T.filter (fun x => x ∈ l.1)
      have hn : U.card ≤ f.totalDegree := by
        by_contra hnot
        apply hL l hl
        apply polynomial_line_zeros 3 f l U
        · intro x hx
          exact ⟨(Finset.mem_filter.mp hx).2,hT x (Finset.mem_filter.mp hx).1⟩
        · omega
      exact Nat.cast_le.mpr hn
    _ = _ := by simp

/-- Removing the points supported by three contained lines loses only off-boundary mass and LD/k. -/
theorem polynomialCore_discard_bound (f : Poly 3) (L : Finset (Line 3)) (S : Finset (E 3)) (k : ℕ)
    (hk : 3 ≤ k) (hS : ∀ x ∈ S,k ≤ lineMultiplicity L x) :
    ((S \ polynomialCore f L S).card:ℝ) ≤ cloudMass S (zeroSet f)ᶜ+
      3*(L.card:ℝ)*f.totalDegree/k := by
  let LZ := L.filter (fun l => onPolynomial f l)
  let L₀ := L \ LZ
  let Z := S.filter (fun x => evalR f x = 0)
  let E := Z \ polynomialCore f L S
  let O := S \ Z
  have hsubL : LZ ⊆ L := Finset.filter_subset _ _
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hEzero : ∀ x ∈ E,evalR f x = 0 := fun x hx => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).2
  have hnon : ∀ l ∈ L₀,¬onPolynomial f l := by
    intro l hl hon
    obtain ⟨hlL,hnot⟩ := Finset.mem_sdiff.mp hl
    exact hnot (Finset.mem_filter.mpr ⟨hlL,hon⟩)
  have hupper : relationMass E L₀ (fun x l => x ∈ l.1) ≤ (L.card:ℝ)*f.totalDegree := by
    apply (boundary_line_mass_three f E hEzero L₀ hnon).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := L) (t := LZ))
  have hrow : ∀ x ∈ E,(k:ℝ)-2 ≤ lineMultiplicity L₀ x := by
    intro x hx
    obtain ⟨hxZ,hxnot⟩ := Finset.mem_sdiff.mp hx
    have hxS := (Finset.mem_filter.mp hxZ).1
    have hZfew : lineMultiplicity LZ x ≤ 2 := by
      by_contra hnot
      apply hxnot
      exact Finset.mem_filter.mpr ⟨hxS,by change 3 ≤ lineMultiplicity LZ x;omega⟩
    have hsplit : (lineMultiplicity L₀ x:ℝ)+(lineMultiplicity LZ x:ℝ) = lineMultiplicity L x := by
      exact_mod_cast lineMultiplicity_sdiff_add L LZ hsubL x
    have hmin : (k:ℝ) ≤ lineMultiplicity L x := by exact_mod_cast hS x hxS
    have hZfewR : (lineMultiplicity LZ x:ℝ) ≤ 2 := by exact_mod_cast hZfew
    linarith
  have hlower : (E.card:ℝ)*((k:ℝ)-2) ≤ relationMass E L₀ (fun x l => x ∈ l.1) := by
    rw [relationMass_sum_card]
    calc
      _ = ∑ _x ∈ E,((k:ℝ)-2) := by simp;ring
      _ ≤ _ := Finset.sum_le_sum (fun x hx => hrow x hx)
  have hEcount : (E.card:ℝ) ≤ 3*(L.card:ℝ)*f.totalDegree/k := by
    have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
    have hm : (E.card:ℝ)*((k:ℝ)/3) ≤ (L.card:ℝ)*f.totalDegree := by
      apply (mul_le_mul_of_nonneg_left (by linarith : (k:ℝ)/3 ≤ (k:ℝ)-2) (Nat.cast_nonneg E.card)).trans
      exact hlower.trans hupper
    apply (le_div_iff₀ hkpos).mpr
    linarith
  have hsub : S \ polynomialCore f L S ⊆ O ∪ E := by
    intro x hx
    obtain ⟨hxS,hxnot⟩ := Finset.mem_sdiff.mp hx
    by_cases hxZ : x ∈ Z
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxZ,hxnot⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxS,hxZ⟩))
  have hO : O = pointsIn S (zeroSet f)ᶜ := by
    ext x
    simp [O,Z,pointsIn,zeroSet]
    tauto
  have hc : ((S \ polynomialCore f L S).card:ℝ) ≤ (O.card:ℝ)+(E.card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le O E)
  rw [hO] at hc
  exact hc.trans (add_le_add le_rfl hEcount)

end DistinctDistances.TrackC
