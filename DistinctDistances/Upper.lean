import DistinctDistances.Defs
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Dist

/-!
The upper-bound clause of the target: the grid construction (paper, `introduction.tex` 30–35).
-/

namespace DistinctDistances

private def gridPoint (d t : ℕ) (a : Fin d → Fin t) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => ((a i).val : ℝ)

private lemma gridPoint_injective (d t : ℕ) : Function.Injective (gridPoint d t) := by
  intro a b h
  funext i
  apply Fin.ext
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
  exact_mod_cast (by simpa [gridPoint] using hi)

private noncomputable def gridSet (d t : ℕ) : Finset (EuclideanSpace ℝ (Fin d)) :=
  Finset.univ.image (gridPoint d t)

private def gridSq (d : ℕ) {t : ℕ} (a b : Fin d → Fin t) : ℕ :=
  ∑ i, Nat.dist (a i).val (b i).val ^ 2

private lemma natCastDist_eq (x y : ℕ) :
    dist (x : ℝ) y = (Nat.dist x y : ℝ) := by
  rw [Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hxy))]
    rw [Nat.dist_eq_sub_of_le hxy, Nat.cast_sub hxy]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hyx))]
    rw [Nat.dist_eq_sub_of_le_right hyx, Nat.cast_sub hyx]

private lemma gridPoint_dist (d t : ℕ) (a b : Fin d → Fin t) :
    dist (gridPoint d t a) (gridPoint d t b) = Real.sqrt (gridSq d a b : ℝ) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  unfold gridSq
  change (∑ i ∈ (Finset.univ : Finset (Fin d)),
      dist ((a i).val : ℝ) ((b i).val : ℝ) ^ 2) =
    ((∑ i ∈ (Finset.univ : Finset (Fin d)), Nat.dist (a i).val (b i).val ^ 2 : ℕ) : ℝ)
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_pow, natCastDist_eq]

private lemma gridSq_le (d t : ℕ) (a b : Fin d → Fin t) : gridSq d a b ≤ d * t ^ 2 := by
  unfold gridSq
  calc
    (∑ i, Nat.dist (a i).val (b i).val ^ 2) ≤ ∑ _i : Fin d, t ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hdist : Nat.dist (a i).val (b i).val ≤ t := by
        unfold Nat.dist
        omega
      exact (pow_le_pow_left' hdist 2)
    _ = d * t ^ 2 := by simp

private lemma gridSet_card (d t : ℕ) : (gridSet d t).card = t ^ d := by
  classical
  rw [gridSet, Finset.card_image_of_injective _ (gridPoint_injective d t)]
  simp

private lemma gridSet_distinctDistances_le (d t : ℕ) :
    distinctDistances (gridSet d t) ≤ d * t ^ 2 + 1 := by
  classical
  let vals : Finset ℝ := (Finset.range (d * t ^ 2 + 1)).image
    (fun k : ℕ => Real.sqrt (k : ℝ))
  have hsubset : distanceSet (gridSet d t) ⊆ vals := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨pair, hp, rfl⟩
    rcases pair with ⟨x, y⟩
    rcases Finset.mem_offDiag.mp hp with ⟨hx, hy, hxy⟩
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨gridSq d a b, Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.lt_succ_of_le (gridSq_le d t a b)
    · exact (gridPoint_dist d t a b).symm
  change (distanceSet (gridSet d t)).card ≤ d * t ^ 2 + 1
  calc
    (distanceSet (gridSet d t)).card ≤ vals.card := Finset.card_le_card hsubset
    _ ≤ (Finset.range (d * t ^ 2 + 1)).card := Finset.card_image_le
    _ = d * t ^ 2 + 1 := Finset.card_range _

private noncomputable def gridRoot (d n : ℕ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d : ℝ))

private lemma gridRoot_nonneg (d n : ℕ) : 0 ≤ gridRoot d n := by
  exact Real.rpow_nonneg (Nat.cast_nonneg n) _

private lemma gridRoot_one_le (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) :
    1 ≤ gridRoot d n := by
  apply Real.one_le_rpow
  · exact_mod_cast (show 1 ≤ n by omega)
  · have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    positivity

private lemma gridRoot_rpow (d n : ℕ) (hd : 1 ≤ d) :
    gridRoot d n ^ (d : ℝ) = (n : ℝ) := by
  rw [gridRoot, ← Real.rpow_mul (Nat.cast_nonneg n)]
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd))
  have heq : (1 : ℝ) / (d : ℝ) * (d : ℝ) = 1 := by field_simp
  rw [heq, Real.rpow_one]

private lemma gridRoot_sq (d n : ℕ) (hd : 1 ≤ d) :
    gridRoot d n ^ 2 = (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
  rw [← Real.rpow_natCast, gridRoot, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd))
  field_simp
  norm_num

private noncomputable def gridWidth (d n : ℕ) : ℕ := Nat.ceil (gridRoot d n)

private lemma gridWidth_lower (d n : ℕ) : gridRoot d n ≤ (gridWidth d n : ℝ) := by
  exact Nat.le_ceil _

private lemma gridWidth_le_two_root (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) :
    (gridWidth d n : ℝ) ≤ 2 * gridRoot d n := by
  have hceil := Nat.ceil_lt_add_one (gridRoot_nonneg d n)
  have hroot := gridRoot_one_le d n hd hn
  unfold gridWidth at hceil ⊢
  linarith

private lemma gridWidth_card_lower (d n : ℕ) (hd : 1 ≤ d) :
    n ≤ gridWidth d n ^ d := by
  have hpow := Real.rpow_le_rpow (gridRoot_nonneg d n) (gridWidth_lower d n) (by positivity :
    0 ≤ (d : ℝ))
  rw [gridRoot_rpow d n hd] at hpow
  have hreal : (n : ℝ) ≤ (gridWidth d n : ℝ) ^ d := by
    simpa only [Real.rpow_natCast] using hpow
  exact_mod_cast hreal

private lemma gridWidth_square_bound (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) :
    (gridWidth d n : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
  have hwidth := gridWidth_le_two_root d n hd hn
  have hsq : (gridWidth d n : ℝ) ^ 2 ≤ (2 * gridRoot d n) ^ 2 := by
    have hsum : 0 ≤ 2 * gridRoot d n + (gridWidth d n : ℝ) :=
      add_nonneg (mul_nonneg (by norm_num) (gridRoot_nonneg d n)) (Nat.cast_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hwidth) hsum]
  nlinarith [gridRoot_sq d n hd]

/-- For every dimension `d ≥ 1` there is `C > 0` such that for every `n ≥ 2` some `n`-point set in
Euclidean `d`-space determines at most `C n^(2/d)` distinct distances. -/
theorem upper_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n → ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
        (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
  refine ⟨8 * (d : ℝ), by positivity, ?_⟩
  intro n hn
  let t := gridWidth d n
  let G := gridSet d t
  have ht : n ≤ t ^ d := by
    simpa [t] using gridWidth_card_lower d n hd
  have hGcard : n ≤ G.card := by
    rw [gridSet_card]
    exact ht
  obtain ⟨P, hPG, hPcard⟩ := Finset.exists_subset_card_eq hGcard
  refine ⟨P, hPcard, ?_⟩
  have hdist : distinctDistances P ≤ d * t ^ 2 + 1 := by
    calc
      distinctDistances P ≤ distinctDistances G := by
        change (distanceSet P).card ≤ (distanceSet G).card
        exact Finset.card_mono (Finset.image_mono _ (Finset.offDiag_mono hPG))
      _ ≤ d * t ^ 2 + 1 := by
        exact gridSet_distinctDistances_le d t
  have hcount : (distinctDistances P : ℝ) ≤ (d * t ^ 2 + 1 : ℝ) := by
    exact_mod_cast hdist
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have ht1 : 1 ≤ (t : ℝ) := by
    have hroot := gridRoot_one_le d n hd hn
    exact hroot.trans (by simpa [t] using gridWidth_lower d n)
  have hfactor : (d * t ^ 2 + 1 : ℝ) ≤ 2 * (d : ℝ) * (t : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdreal) (sq_nonneg (t : ℝ))]
  have hwidthsq := gridWidth_square_bound d n hd hn
  calc
    (distinctDistances P : ℝ) ≤ (d * t ^ 2 + 1 : ℝ) := hcount
    _ ≤ 2 * (d : ℝ) * (t : ℝ) ^ 2 := hfactor
    _ ≤ (8 * (d : ℝ)) * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
      calc
        2 * (d : ℝ) * (t : ℝ) ^ 2 ≤ 2 * (d : ℝ) *
            (4 * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ))) := by
          gcongr
        _ = (8 * (d : ℝ)) * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by ring

end DistinctDistances
