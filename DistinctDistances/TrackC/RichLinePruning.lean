import DistinctDistances.TrackC.FiniteIncidence
import DistinctDistances.TrackC.RichLineArithmetic

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

theorem lineMultiplicity_mono {d : ℕ} (L L' : Finset (Line d)) (hL : L ⊆ L') (x : E d) :
    lineMultiplicity L x ≤ lineMultiplicity L' x := by
  apply Finset.card_le_card
  intro l hl
  exact Finset.mem_filter.mpr ⟨hL (Finset.mem_filter.mp hl).1,(Finset.mem_filter.mp hl).2⟩

theorem lineMultiplicity_sdiff_add {d : ℕ} (L L' : Finset (Line d)) (hL : L' ⊆ L) (x : E d) :
    lineMultiplicity (L \ L') x+lineMultiplicity L' x = lineMultiplicity L x := by
  have hs : L'.filter (fun l => x ∈ l.1) ⊆ L.filter (fun l => x ∈ l.1) := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨hL (Finset.mem_filter.mp hl).1,(Finset.mem_filter.mp hl).2⟩
  have heq : (L \ L').filter (fun l => x ∈ l.1) =
      L.filter (fun l => x ∈ l.1) \ L'.filter (fun l => x ∈ l.1) := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    tauto
  unfold lineMultiplicity
  rw [heq]
  exact Finset.card_sdiff_add_card_eq_card hs

/-- Selection of a uniform-multiplicity point class on the sparse supporting subfamily. -/
theorem sparse_line_uniformity_selection (L : Finset (Line 3)) (S : Finset (E 3)) (k : ℕ)
    (hL : L.Nonempty) (hk : 3 ≤ k)
    (hS : ∀ x ∈ S,k ≤ lineMultiplicity L x ∧ lineMultiplicity L x ≤ 2*k)
    (L₁ : Finset (Line 3))
    (hL₁ : L₁ = L.filter (fun l => (S.card:ℝ)*k/(100*(L.card:ℝ)) ≤ (pointsOn S l).card))
    (hsparse : (L₁.card:ℝ) < (L.card:ℝ)/100) :
    ∃ (S' : Finset (E 3)) (k' : ℕ), S' ⊆ S ∧ 3 ≤ k' ∧ k' ≤ k ∧
      (k:ℝ)/2 ≤ k' ∧ (∀ x ∈ S',k' ≤ lineMultiplicity L₁ x ∧ lineMultiplicity L₁ x ≤ 2*k') ∧
      (S.card:ℝ) ≤ 4*(S'.card:ℝ) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hLpos : (0:ℝ) < L.card := by exact_mod_cast Finset.card_pos.mpr hL
  have hsub : L₁ ⊆ L := by rw [hL₁];exact Finset.filter_subset _ _
  let L₀ := L \ L₁
  let q : ℝ := 9*(k:ℝ)/10
  let G := S.filter (fun x => q ≤ lineMultiplicity L₁ x)
  let Z := S.filter (fun x => ¬q ≤ lineMultiplicity L₁ x)
  let θ := (S.card:ℝ)*k/(100*(L.card:ℝ))
  have hupper : relationMass S L₀ (fun x l => x ∈ l.1) ≤ (S.card:ℝ)*k/100 := by
    rw [relationMass_swap,relationMass_sum_card]
    calc
      _ ≤ ∑ _l ∈ L₀,θ := by
        apply Finset.sum_le_sum
        intro l hl
        have hlL := (Finset.mem_sdiff.mp hl).1
        have hlnot := (Finset.mem_sdiff.mp hl).2
        have hbad : ¬θ ≤ ((pointsOn S l).card:ℝ) := by
          intro hm
          apply hlnot
          rw [hL₁]
          exact Finset.mem_filter.mpr ⟨hlL,hm⟩
        simpa [pointsOn] using (le_of_lt (lt_of_not_ge hbad))
      _ = (L₀.card:ℝ)*θ := by simp
      _ ≤ (L.card:ℝ)*θ := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [θ];positivity)
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := L) (t := L₁))
      _ = _ := by dsimp [θ];field_simp
  have hrow : ∀ x ∈ Z,(k:ℝ)/10 ≤ lineMultiplicity L₀ x := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hxlow : (lineMultiplicity L₁ x:ℝ) < q := lt_of_not_ge (Finset.mem_filter.mp hx).2
    have hsplit : (lineMultiplicity L₀ x:ℝ)+(lineMultiplicity L₁ x:ℝ) = lineMultiplicity L x := by
      exact_mod_cast lineMultiplicity_sdiff_add L L₁ hsub x
    have hmin : (k:ℝ) ≤ lineMultiplicity L x := by exact_mod_cast (hS x hxS).1
    dsimp [q] at hxlow
    linarith
  have hlower : (Z.card:ℝ)*((k:ℝ)/10) ≤ relationMass Z L₀ (fun x l => x ∈ l.1) := by
    rw [relationMass_sum_card]
    calc
      _ = ∑ _x ∈ Z,(k:ℝ)/10 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx => hrow x hx)
  have hZ : (Z.card:ℝ) ≤ (S.card:ℝ)/10 := by
    have hm := relationMass_mono_left Z S L₀ (fun x l => x ∈ l.1) (Finset.filter_subset _ _)
    nlinarith
  have hsplit : G.card+Z.card = S.card := Finset.card_filter_add_card_filter_not (s := S) (fun x => q ≤ lineMultiplicity L₁ x)
  have hG : (S.card:ℝ) ≤ 2*(G.card:ℝ) := by
    have hs : (G.card:ℝ)+(Z.card:ℝ) = S.card := by exact_mod_cast hsplit
    linarith
  let H := G.filter (fun x => k ≤ lineMultiplicity L₁ x)
  let U := G.filter (fun x => ¬k ≤ lineMultiplicity L₁ x)
  have hsplitGU : H.card+U.card = G.card := Finset.card_filter_add_card_filter_not (s := G) (fun x => k ≤ lineMultiplicity L₁ x)
  have hHsub : H ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hUsub : U ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  by_cases hHlarge : (S.card:ℝ) ≤ 4*(H.card:ℝ)
  · refine ⟨H,k,hHsub,hk,le_rfl,by linarith,?_,hHlarge⟩
    intro x hx
    refine ⟨(Finset.mem_filter.mp hx).2,?_⟩
    exact (lineMultiplicity_mono L₁ L hsub x).trans (hS x (hHsub hx)).2
  · let k' := ⌈q⌉₊
    have hceil : q ≤ (k':ℝ) := Nat.le_ceil q
    have hk'3 : 3 ≤ k' := by
      by_contra hnot
      have hl : (k':ℝ) ≤ 2 := by exact_mod_cast (by omega : k' ≤ 2)
      have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
      dsimp [q] at hceil
      linarith
    have hk'k : k' ≤ k := Nat.ceil_le.mpr (by dsimp [q];linarith)
    have hkhalf : (k:ℝ)/2 ≤ k' := by dsimp [q] at hceil;linarith
    have hktwice : k ≤ 2*k' := by exact_mod_cast (by linarith : (k:ℝ) ≤ 2*(k':ℝ))
    have hUlarge : (S.card:ℝ) ≤ 4*(U.card:ℝ) := by
      have hs : (H.card:ℝ)+(U.card:ℝ) = G.card := by exact_mod_cast hsplitGU
      linarith
    refine ⟨U,k',hUsub,hk'3,hk'k,hkhalf,?_,hUlarge⟩
    intro x hx
    have hxG := (Finset.mem_filter.mp hx).1
    have hxlow := (Finset.mem_filter.mp hx).2
    have hxq : q ≤ (lineMultiplicity L₁ x:ℝ) := (Finset.mem_filter.mp hxG).2
    refine ⟨Nat.ceil_le.mpr hxq,?_⟩
    omega

end DistinctDistances.TrackC
