import DistinctDistances.TrackC.MotionMassSplit
import DistinctDistances.TrackC.LineMassCounting
import DistinctDistances.TrackC.MotionFiniteness
import DistinctDistances.TrackC.MotionBucketArithmetic

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

set_option maxHeartbeats 2000000 in
/-- The global very-rich bucket estimate, with the earlier scale lemma supplied to avoid an import cycle. -/
theorem motion_bucket_construct
    (hScales : ∀ (N t β : ℝ),1 ≤ N → 1 ≤ t → t ≤ N^((1:ℝ)/3) → 0 < β →
      let A := N^((2:ℝ)/3)
      let r := t^((15:ℝ)/14)
      let m := 8*N/r
      let b := β*A*t^((-1:ℝ)/14)
      1 ≤ r ∧ r ≤ N ∧ 1 ≤ m ∧ b/m^((2:ℝ)/3) = (β/4)*t^((9:ℝ)/14) ∧
        β*t^((3:ℝ)/7) ≤ b/Real.sqrt N) :
    ∃ C β K : ℝ,4 < C ∧ 0 < β ∧ 0 < K ∧
      ∀ (N : ℕ) (X Y : Finset (E 3)) (t : ℝ),2 ≤ N → X.card ≤ N → Y.card ≤ N →
        let A := (N:ℝ)^((2:ℝ)/3)
        cloudLineCap X (2*A) → cloudLineCap Y (2*A) → C ≤ t → t ≤ (N:ℝ)^((1:ℝ)/3) →
        let k := t*A
        let b := β*A*t^((-1:ℝ)/14)
        FiniteCardBound (motionBucket X Y k)
          (K*((N:ℝ)^4/A*t^((-1:ℝ)/28)+A^2*((N:ℝ)/b)^4+
            A^3*((N:ℝ)/b)^((7:ℝ)/2))/k^2) := by
  obtain ⟨η,Cloc,Kloc,hη,hη1,hCloc,hKloc,hLocal⟩ := mot_local
  obtain ⟨Kp,hKp,hPart⟩ := mot_partition
  obtain ⟨Cst,hCst,hST⟩ := ci_st_rich
  obtain ⟨Cw,hCw,hWeights⟩ := line_weight_sum_bound
  let β := 1/(8*Kp)
  have hβ : 0 < β := by dsimp [β];positivity
  obtain ⟨T,hT,hThresholds⟩ := motion_bucket_thresholds η β Cloc hη hβ hCloc
  let D := 1+2*Cst/η
  let ν := η/4
  let q₀ := (2:ℝ)^((-1:ℝ)/2)
  have hD : 1 ≤ D := by
    have hd : 0 ≤ 2*Cst/η := by positivity
    dsimp [D];linarith
  have hν : 0 < ν := by dsimp [ν];positivity
  have hq₀ : q₀ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  let K₀ := (2888*Kloc/(1-q₀))*(512/Real.sqrt β)
  let K₁ := 16*Cw*D^4/ν^2
  let K := K₀+K₁+1
  have hK₀ : 0 < K₀ := by dsimp [K₀];positivity
  have hK₁ : 0 < K₁ := by dsimp [K₁];positivity
  have hK : 0 < K := by dsimp [K];positivity
  have hKleft : K₀ ≤ K := by dsimp [K];linarith
  have hKright : K₁ ≤ K := by dsimp [K];linarith
  refine ⟨T,β,K,hT,hβ,hK,?_⟩
  intro N X Y t hN hX hY
  let A := (N:ℝ)^((2:ℝ)/3)
  dsimp only
  intro hXcap hYcap ht htN
  let r := t^((15:ℝ)/14)
  let m := 8*(N:ℝ)/r
  let k := t*A
  let b := β*A*t^((-1:ℝ)/14)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  have ht1 : 1 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hA1 : 1 ≤ A := Real.one_le_rpow hN1 (by norm_num)
  have hA : 0 < A := by linarith
  have hrpos : 0 < r := by dsimp [r];positivity
  have hb : 0 < b := by dsimp [b];positivity
  have hk : 0 < k := by dsimp [k];positivity
  obtain ⟨hr1,hrN,hm1,hRatio,hRise⟩ := hScales N t β hN1 ht1 htN hβ
  obtain ⟨hLocalScale,hLineScale,hPairScale⟩ := hThresholds t ht
  have hbLocal : Cloc*m^((2:ℝ)/3) ≤ b := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < m^((2:ℝ)/3))).mp
    rw [hRatio]
    exact hLocalScale
  let q := η*b
  have hq : Real.sqrt N ≤ q := by
    rw [← one_mul (Real.sqrt (N:ℝ))]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hNpos)).mp
    have h := mul_le_mul_of_nonneg_left hRise hη.le
    have hlow : 1 ≤ η*(b/Real.sqrt N) := hLineScale.trans (by convert h using 1 <;> ring)
    convert hlow using 1 <;> ring
  have hqpos : 0 < q := by dsimp [q];positivity
  have hqSq : (N:ℝ) ≤ q^2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg (N:ℝ)) hqpos.le).mpr hq
    rwa [Real.sq_sqrt hNpos.le] at h
  have hq1 : 1 < q := by nlinarith
  have hPair : 4*A ≤ ν*k := by
    have h := mul_le_mul_of_nonneg_right hPairScale hA.le
    dsimp [ν,k]
    nlinarith
  have hsmall : Kp*r*b ≤ k/4 := by
    have hident : r*b = β*k := motion_region_threshold_identity t A β htpos
    have hcoeff : Kp*β = 1/8 := by dsimp [β];field_simp <;> ring
    calc
      _ = (Kp*β)*k := by rw [mul_assoc,hident];ring
      _ = k/8 := by rw [hcoeff];ring
      _ ≤ _ := by linarith
  obtain ⟨P,hPX,hPsize,hPmass,hPoverlap⟩ := hPart X N r hN1 hr1 hrN (by exact_mod_cast hX)
  obtain ⟨Q,hQY,hQsize,hQmass,hQoverlap⟩ := hPart Y N r hN1 hr1 hrN (by exact_mod_cast hY)
  have hRichX : ∀ j : ℕ,2 ≤ j → FiniteCardBound (richLines X j)
      (Cst*((X.card:ℝ)^2/(j:ℝ)^3+(X.card:ℝ)/j)) := fun j hj => (hST 3 X ∅ j hj).2
  have hRichY : ∀ j : ℕ,2 ≤ j → FiniteCardBound (richLines Y j)
      (Cst*((Y.card:ℝ)^2/(j:ℝ)^3+(Y.card:ℝ)/j)) := fun j hj => (hST 3 Y ∅ j hj).2
  obtain ⟨LX,hLX,hLXcard⟩ := ambient_rich_line_list X N q Cst hN1 (by exact_mod_cast hX) hq1 hqSq hCst hRichX
  obtain ⟨LY,hLY,hLYcard⟩ := ambient_rich_line_list Y N q Cst hN1 (by exact_mod_cast hY) hq1 hqSq hCst hRichY
  have hDcoef : 2*Cst/η ≤ D := by dsimp [D];linarith
  have hLXsize : (LX.card:ℝ) ≤ D*((N:ℝ)/b) := by
    calc
      _ ≤ 2*Cst*N/q := hLXcard
      _ = (2*Cst/η)*((N:ℝ)/b) := by dsimp [q];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDcoef (by positivity)
  have hLYsize : (LY.card:ℝ) ≤ D*((N:ℝ)/b) := by
    calc
      _ ≤ 2*Cst*N/q := hLYcard
      _ = (2*Cst/η)*((N:ℝ)/b) := by dsimp [q];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDcoef (by positivity)
  have hkcap : 2*A < k := by dsimp [k];nlinarith
  have hfinite := motion_bucket_finite_of_line_cap X Y (2*A) k (by linarith) hXcap hkcap
  let G := hfinite.toFinset
  have hLineCount : ∀ (F : Finset (Motion 3)) (w : Motion 3 → Line 3 → ℝ),
      (∀ g ∈ F,∀ l ∈ LX,0 ≤ w g l ∧ w g l ≤ (matchCount (pointsOn X l) Y g:ℝ) ∧
        (0 < w g l → ∃ l' ∈ LY,mapsLine g l l')) →
      (∀ g ∈ F,(η/4)*k ≤ ∑ l ∈ LX,w g l) →
      (F.card:ℝ)*k^2 ≤ K₁*(A^2*((N:ℝ)/b)^4+A^3*((N:ℝ)/b)^((7:ℝ)/2)) := by
    intro F w hw hmass
    exact line_weights_cardinality_bound Cw D ν A k ((N:ℝ)/b) hCw hD hν hA.le hk (by positivity)
      hPair X Y LX LY F w hXcap hYcap hLXsize hLYsize hw hmass
      (hWeights X Y LX LY F (2*A) w (by positivity) hXcap hYcap hw)
  have hLocalPairs : ∀ RR ∈ P.regions ×ˢ Q.regions,∀ ℓ : ℝ,b ≤ ℓ →
      FiniteCardBound {g : Motion 3 | g ∈ motionBucket (pointsIn X (regionSet RR.1)) (pointsIn Y (regionSet RR.2)) ℓ ∧
        nonLineType η ℓ (pointsIn X (regionSet RR.1)) (pointsIn Y (regionSet RR.2)) g} (Kloc*m^3/ℓ^((3:ℝ)/2)) := by
    intro RR hRR ℓ hℓ
    obtain ⟨hR₁,hR₂⟩ := Finset.mem_product.mp hRR
    exact hLocal _ _ m ℓ hm1 (hPmass RR.1 hR₁) (hQmass RR.2 hR₂) (hbLocal.trans hℓ)
  have hmass := motion_bucket_mass_split P Q X Y G LX LY η Kloc m b k r Kp
    (K₁*(A^2*((N:ℝ)/b)^4+A^3*((N:ℝ)/b)^((7:ℝ)/2))) hη hKloc.le (by linarith) hb hk hrpos.le hKp.le
    hPX hQY hPsize hQsize (fun g _ => hPoverlap Q hQsize g) hsmall
    (fun g hg => (hfinite.mem_toFinset.mp hg).1) hLocalPairs hLX hLY hLineCount
  have hident := motion_nonline_scale_identity N t β hNpos htpos hβ
  have hterm : (2888*Kloc/(1-(2:ℝ)^((-1:ℝ)/2)))*k*r^2*m^3/Real.sqrt b =
      K₀*((N:ℝ)^4/A*t^((-1:ℝ)/28)) := by
    calc
      _ = (2888*Kloc/(1-q₀))*(k*r^2*m^3/Real.sqrt b) := by ring
      _ = (2888*Kloc/(1-q₀))*((512/Real.sqrt β)*((N:ℝ)^4/A*t^((-1:ℝ)/28))) := by rw [hident]
      _ = _ := by dsimp [K₀];ring
  rw [hterm] at hmass
  refine ⟨hfinite,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  apply (le_div_iff₀ (by positivity : (0:ℝ) < k^2)).mpr
  apply hmass.trans
  calc
    _ ≤ K*((N:ℝ)^4/A*t^((-1:ℝ)/28))+
        K*(A^2*((N:ℝ)/b)^4+A^3*((N:ℝ)/b)^((7:ℝ)/2)) := by gcongr
    _ = _ := by ring

end DistinctDistances.TrackC
