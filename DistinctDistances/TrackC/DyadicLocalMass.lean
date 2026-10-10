import DistinctDistances.TrackC.Basic

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

theorem exists_dyadic_scale (b n : ℝ) (hb : 0 < b) (hn : b ≤ n) :
    ∃ j : ℕ,b*(2:ℝ)^j ≤ n ∧ n < 2*(b*(2:ℝ)^j) := by
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ hb).mpr (by simpa using hn)) (by norm_num : (1:ℝ) < 2)
  refine ⟨j,?_,?_⟩
  · have h := (le_div_iff₀ hb).mp hlo
    nlinarith
  · have h := (div_lt_iff₀ hb).mp hhi
    rw [pow_succ] at h
    nlinarith

def dyadicLocalLevel (b n : ℝ) (hb : 0 < b) : ℕ :=
  if hn : b ≤ n then (exists_dyadic_scale b n hb hn).choose else 0

theorem dyadicLocalLevel_bounds (b n : ℝ) (hb : 0 < b) (hn : b ≤ n) :
    b*(2:ℝ)^(dyadicLocalLevel b n hb) ≤ n ∧ n < 2*(b*(2:ℝ)^(dyadicLocalLevel b n hb)) := by
  simpa [dyadicLocalLevel,hn] using (exists_dyadic_scale b n hb hn).choose_spec

theorem finite_geometric_sum_le (J : Finset ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑ j ∈ J,q^j) ≤ 1/(1-q) := by
  let n := J.sup id+1
  have hsub : J ⊆ Finset.range n := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  calc
    _ ≤ ∑ j ∈ Finset.range n,q^j := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => pow_nonneg hq j)
    _ ≤ _ := by
      apply (le_div_iff₀ (by linarith : (0:ℝ) < 1-q)).mpr
      have hg := geom_sum_mul q n
      have hpow := pow_nonneg hq n
      nlinarith

/-- A 3/2-power local bucket count sums to a square-root mass saving. -/
theorem dyadic_local_mass_bound {α : Type*} (G : Finset α) (n : α → ℝ) (P : α → ℕ → Prop)
    (b T : ℝ) (hb : 0 < b) (hT : 0 ≤ T)
    (hBuckets : ∀ j : ℕ,
      ((G.filter (fun g => b*(2:ℝ)^j ≤ n g ∧ n g < 2*(b*(2:ℝ)^j) ∧ P g j)).card:ℝ) ≤
        T/(b*(2:ℝ)^j)^((3:ℝ)/2)) :
    (∑ g ∈ G,if b ≤ n g ∧ P g (dyadicLocalLevel b (n g) hb) then n g else 0) ≤
      2*T/(Real.sqrt b*(1-(2:ℝ)^((-1:ℝ)/2))) := by
  let level : α → ℕ := fun g => dyadicLocalLevel b (n g) hb
  let w : α → ℝ := fun g => if b ≤ n g ∧ P g (level g) then n g else 0
  let J := G.image level
  let q : ℝ := (2:ℝ)^((-1:ℝ)/2)
  have hq : 0 < q := by dsimp [q];positivity
  have hq1 : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsum := Finset.sum_fiberwise_of_maps_to (g := level)
    (s := G) (t := J) (fun g hg => Finset.mem_image_of_mem level hg) w
  have hrow : ∀ j ∈ J,(∑ g ∈ G.filter (fun g => level g = j),w g) ≤
      (2*T/Real.sqrt b)*q^j := by
    intro j hj
    let ℓ := b*(2:ℝ)^j
    have hℓ : 0 < ℓ := by dsimp [ℓ];positivity
    let H := (G.filter (fun g => level g = j)).filter (fun g => b ≤ n g ∧ P g j)
    let B := G.filter (fun g => ℓ ≤ n g ∧ n g < 2*ℓ ∧ P g j)
    have hHsub : H ⊆ B := by
      intro g hg
      obtain ⟨hgL,hgN,hgP⟩ := Finset.mem_filter.mp hg
      obtain ⟨hgG,hlevel⟩ := Finset.mem_filter.mp hgL
      have hs := dyadicLocalLevel_bounds b (n g) hb hgN
      change b*(2:ℝ)^(level g) ≤ n g ∧ n g < 2*(b*(2:ℝ)^(level g)) at hs
      rw [hlevel] at hs
      exact Finset.mem_filter.mpr ⟨hgG,hs.1,hs.2,hgP⟩
    have hsumH : (∑ g ∈ G.filter (fun g => level g = j),w g) = ∑ g ∈ H,n g := by
      change (∑ g ∈ G.filter (fun g => level g = j),w g) =
        ∑ g ∈ (G.filter (fun g => level g = j)).filter (fun g => b ≤ n g ∧ P g j),n g
      conv_rhs => rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g hg
      have hl := (Finset.mem_filter.mp hg).2
      simp [w,hl]
    have hbound : (B.card:ℝ) ≤ T/ℓ^((3:ℝ)/2) := hBuckets j
    calc
      _ = ∑ g ∈ H,n g := hsumH
      _ ≤ ∑ _g ∈ H,2*ℓ := by
        apply Finset.sum_le_sum
        intro g hg
        exact (Finset.mem_filter.mp (hHsub hg)).2.2.1.le
      _ = (2*ℓ)*(H.card:ℝ) := by simp [mul_comm]
      _ ≤ (2*ℓ)*(B.card:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hHsub)) (by positivity)
      _ ≤ (2*ℓ)*(T/ℓ^((3:ℝ)/2)) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by
        have hr : ℓ/ℓ^((3:ℝ)/2) = ℓ^((-1:ℝ)/2) := by
          have h := Real.rpow_sub hℓ (1:ℝ) ((3:ℝ)/2)
          norm_num at h
          simpa only [neg_div] using h.symm
        have hp : ((2:ℝ)^j)^((-1:ℝ)/2) = q^j := by
          rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num)]
          rw [show (j:ℝ)*((-1:ℝ)/2) = ((-1:ℝ)/2)*j by ring,
            Real.rpow_mul (by norm_num),Real.rpow_natCast]
        have hbroot : b^((-1:ℝ)/2) = 1/Real.sqrt b := by
          rw [show (-1:ℝ)/2 = -((1:ℝ)/2) by norm_num,Real.rpow_neg hb.le,← Real.sqrt_eq_rpow,one_div]
        calc
          _ = 2*T*(ℓ/ℓ^((3:ℝ)/2)) := by ring
          _ = 2*T*ℓ^((-1:ℝ)/2) := by rw [hr]
          _ = 2*T*(b^((-1:ℝ)/2)*((2:ℝ)^j)^((-1:ℝ)/2)) := by rw [Real.mul_rpow hb.le (by positivity)]
          _ = _ := by rw [hp,hbroot];ring
  calc
    _ = ∑ g ∈ G,w g := rfl
    _ = ∑ j ∈ J,∑ g ∈ G.filter (fun g => level g = j),w g := hsum.symm
    _ ≤ ∑ j ∈ J,(2*T/Real.sqrt b)*q^j := Finset.sum_le_sum hrow
    _ = (2*T/Real.sqrt b)*(∑ j ∈ J,q^j) := (Finset.mul_sum _ _ _).symm
    _ ≤ (2*T/Real.sqrt b)*(1/(1-q)) :=
      mul_le_mul_of_nonneg_left (finite_geometric_sum_le J q hq.le hq1) (by positivity)
    _ = _ := by dsimp [q];simp only [div_eq_mul_inv,mul_inv];ring

end DistinctDistances.TrackC
