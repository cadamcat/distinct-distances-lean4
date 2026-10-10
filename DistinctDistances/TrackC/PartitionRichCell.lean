import DistinctDistances.TrackC.Polynomial
import DistinctDistances.TrackC.CellSelection

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Rich-point ST bounds force almost all samples onto the polynomial boundary at a suitable scale. -/
theorem partition_rich_off_zero_bound (S : Finset (E 3)) (L : Finset (Line 3)) (k r : ℕ)
    (p C ε : ℝ) (hp : 0 < p) (hC : 0 < C) (hε : 0 < ε) (hr : 1 ≤ r) (hk : 2 ≤ k)
    (hs : (0:ℝ) < S.card) (hS : ∀ x ∈ S,k ≤ lineMultiplicity L x)
    (hST : ∀ (A : Finset (Line 3)) (j : ℕ),2 ≤ j →
      FiniteCardBound (richPoints A j) (C*((A.card:ℝ)^2/(j:ℝ)^3+(A.card:ℝ)/j)))
    (f : Poly 3) (cells : Finset (Set (E 3)))
    (hdegree : (f.totalDegree:ℝ) ≤ p*r) (hcard : (cells.card:ℝ) ≤ p*(r:ℝ)^3)
    (hoccup : ∀ R ∈ cells,((pointsIn S R).card:ℝ) ≤ p*S.card/(r:ℝ)^3)
    (hcover : (⋃ R ∈ cells,R) = (zeroSet f)ᶜ)
    (hcross : ∀ l : Line 3,¬onPolynomial f l →
      (cells.filter (fun R => (R ∩ (l.1:Set (E 3))).Nonempty)).card ≤ f.totalDegree+1)
    (hscale : C*(((2*p*(p+1)/ε)*(L.card:ℝ)/(r:ℝ)^2)^2/(k:ℝ)^3+
      ((2*p*(p+1)/ε)*(L.card:ℝ)/(r:ℝ)^2)/k) < ε*S.card/(2*p*(r:ℝ)^3)) :
    cloudMass S (zeroSet f)ᶜ ≤ ε*S.card := by
  have hrpos : (0:ℝ) < r := by positivity
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let L₀ := L.filter (fun l => ¬onPolynomial f l)
  let a : Set (E 3) → ℝ := fun R => (pointsIn S R).card
  let b : Set (E 3) → ℝ := fun R => (L₀.filter (fun l => (R ∩ (l.1:Set (E 3))).Nonempty)).card
  have hsum : (∑ R ∈ cells,b R) ≤ (p+1)*(L.card:ℝ)*r := by
    have hswap := relationMass_swap cells L₀ (fun R l => (R ∩ (l.1:Set (E 3))).Nonempty)
    rw [relationMass_sum_card,relationMass_sum_card] at hswap
    have hm : (∑ R ∈ cells,b R) ≤ (L₀.card:ℝ)*((f.totalDegree:ℝ)+1) := by
      rw [show (∑ R ∈ cells,b R) = ∑ l ∈ L₀,((cells.filter (fun R => (R ∩ (l.1:Set (E 3))).Nonempty)).card:ℝ) from hswap]
      calc
        _ ≤ ∑ _l ∈ L₀,((f.totalDegree:ℝ)+1) := by
          apply Finset.sum_le_sum
          intro l hl
          exact_mod_cast hcross l (Finset.mem_filter.mp hl).2
        _ = _ := by simp;ring
    have hn : (L₀.card:ℝ) ≤ L.card := by exact_mod_cast Finset.card_filter_le L (fun l => ¬onPolynomial f l)
    have hd : (f.totalDegree:ℝ)+1 ≤ (p+1)*r := by
      have hrone : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    calc
      _ ≤ (L₀.card:ℝ)*((f.totalDegree:ℝ)+1) := hm
      _ ≤ (L.card:ℝ)*((p+1)*r) := mul_le_mul hn hd (by positivity) (by positivity)
      _ = _ := by ring
  have hsumA : cloudMass S (zeroSet f)ᶜ ≤ ∑ R ∈ cells,a R := by
    have hsub : pointsIn S (zeroSet f)ᶜ ⊆ cells.biUnion (fun R => pointsIn S R) := by
      intro x hx
      obtain ⟨hxS,hxoff⟩ := (mem_pointsIn S _ x).mp hx
      rw [← hcover] at hxoff
      obtain ⟨R,hR,hxR⟩ := (by simpa using hxoff : ∃ R ∈ cells,x ∈ R)
      exact Finset.mem_biUnion.mpr ⟨R,hR,(mem_pointsIn S R x).mpr ⟨hxS,hxR⟩⟩
    change ((pointsIn S (zeroSet f)ᶜ).card:ℝ) ≤ ∑ R ∈ cells,((pointsIn S R).card:ℝ)
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  by_contra hnot
  obtain ⟨R,hR,hRa,hRb⟩ := occupied_cell_few_lines cells a b p S.card L.card r ε hp hs
    (Nat.cast_nonneg _) hrpos hε
    (fun R hR => ⟨Nat.cast_nonneg _,hoccup R hR⟩) (fun R _ => Nat.cast_nonneg _) hcard
    ((lt_of_not_ge hnot).le.trans hsumA) hsum
  let A := L₀.filter (fun l => (R ∩ (l.1:Set (E 3))).Nonempty)
  have hpointsub : (pointsIn S R:Set (E 3)) ⊆ richPoints A k := by
    intro x hx
    obtain ⟨hxS,hxR⟩ := (mem_pointsIn S R x).mp hx
    have hxoff : x ∉ zeroSet f := by
      have hxunion : x ∈ ⋃ R ∈ cells,R := Set.mem_iUnion.mpr ⟨R,Set.mem_iUnion.mpr ⟨hR,hxR⟩⟩
      rw [hcover] at hxunion
      exact hxunion
    have hlineSub : L.filter (fun l => x ∈ l.1) ⊆ A.filter (fun l => x ∈ l.1) := by
      intro l hl
      obtain ⟨hlL,hxl⟩ := Finset.mem_filter.mp hl
      have hnon : ¬onPolynomial f l := fun hon => hxoff (hon x hxl)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hlL,hnon⟩,x,hxR,hxl⟩,hxl⟩
    exact (hS x hxS).trans (Finset.card_le_card hlineSub)
  have hrich := hST A k hk
  have hpoints : a R ≤ C*((b R)^2/(k:ℝ)^3+b R/k) :=
    (Nat.cast_le.mpr (finset_card_le_ncard _ _ hrich.1 hpointsub)).trans hrich.2
  have hsmall : C*((b R)^2/(k:ℝ)^3+b R/k) ≤
      C*(((2*p*(p+1)/ε)*(L.card:ℝ)/(r:ℝ)^2)^2/(k:ℝ)^3+
        ((2*p*(p+1)/ε)*(L.card:ℝ)/(r:ℝ)^2)/k) := by gcongr
  exact (not_le_of_gt hscale) (hRa.trans (hpoints.trans hsmall))

end DistinctDistances.TrackC
