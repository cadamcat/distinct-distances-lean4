import DistinctDistances.TrackC.FiniteIncidence

open scoped BigOperators
open Classical

namespace DistinctDistances.TrackC

/-- A substantial off-boundary mass supplies an occupied cell met by few lines. -/
theorem occupied_cell_few_lines {α : Type*} (I : Finset α) (a b : α → ℝ)
    (p s L r ε : ℝ) (hp : 0 < p) (hs : 0 < s) (hL : 0 ≤ L) (hr : 0 < r) (hε : 0 < ε)
    (ha : ∀ i ∈ I,0 ≤ a i ∧ a i ≤ p*s/r^3) (hb : ∀ i ∈ I,0 ≤ b i)
    (hcard : (I.card:ℝ) ≤ p*r^3) (hmass : ε*s ≤ ∑ i ∈ I,a i)
    (hlines : (∑ i ∈ I,b i) ≤ (p+1)*L*r) :
    ∃ i ∈ I,ε*s/(2*p*r^3) ≤ a i ∧ b i ≤ (2*p*(p+1)/ε)*L/r^2 := by
  let u := ε*s/(2*p*r^3)
  let v := (2*p*(p+1)/ε)*L/r^2
  let J := I.filter (fun i => u ≤ a i)
  let J' := I.filter (fun i => ¬u ≤ a i)
  have hu : 0 ≤ u := by dsimp [u];positivity
  have hv : 0 ≤ v := by dsimp [v];positivity
  have hsmall : (∑ i ∈ J',a i) ≤ ε*s/2 := by
    calc
      _ ≤ ∑ _i ∈ J',u := Finset.sum_le_sum (fun i hi => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2))
      _ = (J'.card:ℝ)*u := by simp
      _ ≤ (I.card:ℝ)*u := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_filter_le _ _)) hu
      _ ≤ (p*r^3)*u := mul_le_mul_of_nonneg_right hcard hu
      _ = _ := by dsimp [u];field_simp <;> ring
  have hsplit : (∑ i ∈ J,a i)+(∑ i ∈ J',a i) = ∑ i ∈ I,a i :=
    Finset.sum_filter_add_sum_filter_not I (fun i => u ≤ a i) a
  have hlarge : ε*s/2 ≤ ∑ i ∈ J,a i := by linarith
  have hupper : (∑ i ∈ J,a i) ≤ (J.card:ℝ)*p*s/r^3 := by
    calc
      _ ≤ ∑ _i ∈ J,p*s/r^3 := Finset.sum_le_sum (fun i hi => (ha i (Finset.mem_filter.mp hi).1).2)
      _ = _ := by simp;ring
  have hJcard : ε*r^3/(2*p) ≤ (J.card:ℝ) := by
    have hc : (ε/2)*s ≤ ((J.card:ℝ)*p/r^3)*s := by
      calc
        _ = ε*s/2 := by ring
        _ ≤ (J.card:ℝ)*p*s/r^3 := hlarge.trans hupper
        _ = _ := by ring
    have hc' := (mul_le_mul_iff_left₀ hs).mp hc
    have hpow := (le_div_iff₀ (by positivity : (0:ℝ) < r^3)).mp hc'
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*p)).mpr
    nlinarith
  have hJne : J.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0:ℝ) < J.card := lt_of_lt_of_le (by positivity) hJcard
    exact_mod_cast hpos
  have hsumJ : (∑ i ∈ J,b i) ≤ (p+1)*L*r := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i hi _ => hb i hi)).trans hlines
  have hpay : (p+1)*L*r ≤ (J.card:ℝ)*v := by
    calc
      _ = (ε*r^3/(2*p))*v := by dsimp [v];field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hJcard hv
  by_contra! hnot
  have hstrict : (J.card:ℝ)*v < ∑ i ∈ J,b i := by
    calc
      _ = ∑ _i ∈ J,v := by simp
      _ < _ := by
        apply Finset.sum_lt_sum_of_nonempty hJne
        intro i hi
        obtain ⟨hiI,hia⟩ := Finset.mem_filter.mp hi
        exact hnot i hiI hia
  linarith

end DistinctDistances.TrackC
