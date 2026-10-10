import DistinctDistances.TrackC.LocalNonlineMass
import DistinctDistances.TrackC.LocalLineAssignments
import DistinctDistances.TrackC.PooledLineAssignments

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Global bucket mass splitting before the final power substitutions. -/
theorem motion_bucket_mass_split (P Q : CubePartition) (X Y : Finset (E 3))
    (G : Finset (Motion 3)) (LX LY : Finset (Line 3)) (η K m b k r Kp M : ℝ)
    (hη : 0 < η) (hK : 0 ≤ K) (hm : 0 ≤ m) (hb : 0 < b) (hk : 0 < k) (hr : 0 ≤ r) (hKp : 0 ≤ Kp)
    (hX : (X:Set (E 3)) ⊆ cubeSet P.root) (hY : (Y:Set (E 3)) ⊆ cubeSet Q.root)
    (hPsize : (P.regions.card:ℝ) ≤ 19*r) (hQsize : (Q.regions.card:ℝ) ≤ 19*r)
    (hOverlap : ∀ g ∈ G,(regionOverlap P Q g:ℝ) ≤ Kp*r) (hDiscard : Kp*r*b ≤ k/4)
    (hGlobal : ∀ g ∈ G,k ≤ (matchCount X Y g:ℝ))
    (hLocal : ∀ RR ∈ P.regions ×ˢ Q.regions,∀ ℓ : ℝ,b ≤ ℓ →
      FiniteCardBound {g : Motion 3 | g ∈ motionBucket (pointsIn X (regionSet RR.1)) (pointsIn Y (regionSet RR.2)) ℓ ∧
        nonLineType η ℓ (pointsIn X (regionSet RR.1)) (pointsIn Y (regionSet RR.2)) g} (K*m^3/ℓ^((3:ℝ)/2)))
    (hLX : ∀ l : Line 3,l ∈ LX ↔ η*b ≤ ((pointsOn X l).card:ℝ))
    (hLY : ∀ l : Line 3,l ∈ LY ↔ η*b ≤ ((pointsOn Y l).card:ℝ))
    (hLineCount : ∀ (F : Finset (Motion 3)) (w : Motion 3 → Line 3 → ℝ),
      (∀ g ∈ F,∀ l ∈ LX,0 ≤ w g l ∧ w g l ≤ (matchCount (pointsOn X l) Y g:ℝ) ∧
        (0 < w g l → ∃ l' ∈ LY,mapsLine g l l')) →
      (∀ g ∈ F,(η/4)*k ≤ ∑ l ∈ LX,w g l) → (F.card:ℝ)*k^2 ≤ M) :
    (G.card:ℝ)*k^2 ≤ (2888*K/(1-(2:ℝ)^((-1:ℝ)/2)))*k*r^2*m^3/Real.sqrt b+M := by
  let I := P.regions ×ˢ Q.regions
  let n : Motion 3 → Region × Region → ℝ := fun g RR => localRegionRichness X Y RR g
  let flag : Motion 3 → Region × Region → Prop := fun g RR =>
    nonLineType η (localRegionScale X Y b hb RR g) (pointsIn X (regionSet RR.1)) (pointsIn Y (regionSet RR.2)) g
  let NL : Motion 3 → ℝ := fun g => ∑ RR ∈ I,if b ≤ n g RR ∧ flag g RR then n g RR else 0
  let LL : Motion 3 → ℝ := fun g => ∑ RR ∈ I,if localLineRetained X Y η b hb RR g then n g RR else 0
  let Small : Motion 3 → ℝ := fun g => ∑ RR ∈ I,if n g RR < b then n g RR else 0
  let G₀ := G.filter (fun g => k/4 ≤ NL g)
  let G₁ := G.filter (fun g => ¬k/4 ≤ NL g)
  let q := (2:ℝ)^((-1:ℝ)/2)
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hden : 0 < 1-q := by linarith
  have hIcard : (I.card:ℝ) ≤ 361*r^2 := by
    have hc := mul_le_mul hPsize hQsize (Nat.cast_nonneg Q.regions.card) (by positivity : 0 ≤ 19*r)
    simp only [I,Finset.card_product,Nat.cast_mul]
    convert hc using 1 <;> ring
  have hsmall : ∀ g ∈ G,Small g ≤ k/4 := by
    intro g hg
    have hs : (((I.filter (fun RR => n g RR ≠ 0)).card):ℝ) ≤ Kp*r := by
      have heq : I.filter (fun RR => n g RR ≠ 0) = I.filter (fun RR => (regionPairMatches X Y RR g).card ≠ 0) := by
        ext RR
        simp [n,localRegionRichness]
      rw [heq]
      exact (regionPairMatches_support P Q X Y g).trans (hOverlap g hg)
    have hd := region_discard I (n g) Kp r b hKp hr hb
      (fun RR _ => Nat.cast_nonneg _) hs
    simpa only [Small,Finset.sum_filter] using hd.trans hDiscard
  have hsum : ∀ g,Small g+NL g+LL g = (matchCount X Y g:ℝ) := by
    intro g
    rw [← sum_regionPairMatches P Q X Y g hX hY]
    dsimp [Small,NL,LL]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro RR hRR
    by_cases hn : b ≤ localRegionRichness X Y RR g
    <;> by_cases hf : nonLineType η (localRegionScale X Y b hb RR g)
      (pointsIn X (regionSet RR.1)) (pointsIn Y (regionSet RR.2)) g
    all_goals simp only [n,flag,localLineRetained,lt_iff_not_ge,hn,hf,not_true_eq_false,not_false_eq_true,
      and_false,and_true,false_and,true_and,if_true,if_false,zero_add,add_zero] <;> rfl
  have hNLrow : ∀ RR ∈ I,(∑ g ∈ G₀,if b ≤ n g RR ∧ flag g RR then n g RR else 0) ≤
      2*K*m^3/(Real.sqrt b*(1-q)) := by
    intro RR hRR
    exact local_nonline_mass_sum (pointsIn X (regionSet RR.1)) (pointsIn Y (regionSet RR.2))
      G₀ η K m b hK hm hb (hLocal RR hRR)
  have hG₀ : (G₀.card:ℝ)*k^2 ≤ (2888*K/(1-q))*k*r^2*m^3/Real.sqrt b := by
    have hlo : (G₀.card:ℝ)*(k/4) ≤ ∑ g ∈ G₀,NL g := by
      calc
        _ = ∑ _g ∈ G₀,k/4 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun g hg => (Finset.mem_filter.mp hg).2)
    have hup : (∑ g ∈ G₀,NL g) ≤ 361*r^2*(2*K*m^3/(Real.sqrt b*(1-q))) := by
      unfold NL
      rw [Finset.sum_comm]
      calc
        _ ≤ ∑ _RR ∈ I,2*K*m^3/(Real.sqrt b*(1-q)) := Finset.sum_le_sum hNLrow
        _ = (I.card:ℝ)*(2*K*m^3/(Real.sqrt b*(1-q))) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hIcard (by positivity)
    have hm := mul_le_mul_of_nonneg_right (hlo.trans hup) (by positivity : 0 ≤ 4*k)
    convert hm using 1 <;> simp only [div_eq_mul_inv,mul_inv] <;> ring
  have hLL : ∀ g ∈ G₁,k/2 ≤ LL g := by
    intro g hg
    have hgG := (Finset.mem_filter.mp hg).1
    have hNL : NL g < k/4 := lt_of_not_ge (Finset.mem_filter.mp hg).2
    have hs := hsum g
    have hsm := hsmall g hgG
    have hgl := hGlobal g hgG
    linarith
  let a := localAssignedPoints X Y η b hb
  let pick := localAssignedLine X Y η b hb
  let w := pooledAssignedWeight I a pick
  have hpool := pooled_assignment_weights P Q X Y G₁ LX LY a pick
    (fun g _ RR _ => localAssignedPoints_subset X Y η b hb g RR)
    (fun g _ RR _ l hl => localAssignedPoints_on_line X Y η b hb g RR l hl)
    (fun g _ RR _ hne => localAssignedPoints_rich_lines X Y η b hb hη LX LY hLX hLY g RR hne)
  have hG₁ : (G₁.card:ℝ)*k^2 ≤ M := by
    apply hLineCount G₁ w (fun g hg => (hpool g hg).1)
    intro g hg
    rw [(hpool g hg).2]
    calc
      _ = (η/2)*(k/2) := by ring
      _ ≤ (η/2)*LL g := mul_le_mul_of_nonneg_left (hLL g hg) (by positivity)
      _ = ∑ RR ∈ I,(η/2)*(if localLineRetained X Y η b hb RR g then n g RR else 0) := by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun RR _ => localAssignedPoints_mass X Y η b hb hη g RR)
  have hsplit : (G₀.card:ℝ)+(G₁.card:ℝ) = G.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := G) (fun g => k/4 ≤ NL g)
  change (G.card:ℝ)*k^2 ≤ (2888*K/(1-q))*k*r^2*m^3/Real.sqrt b+M
  nlinarith

end DistinctDistances.TrackC
