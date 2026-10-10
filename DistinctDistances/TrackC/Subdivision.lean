import DistinctDistances.TrackC.MotionLocal
import DistinctDistances.TrackC.CloudMass

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

structure Cube where
  corner : E 3
  side : ℝ
  side_pos : 0 < side

def cubeSet (Q : Cube) : Set (E 3) :=
  {x | ∀ i : Fin 3, Q.corner i ≤ x i ∧ x i < Q.corner i + Q.side}

def DyadicDescendant (Q' Q : Cube) : Prop :=
  ∃ (j : ℕ) (k : Fin 3 → ℕ), Q'.side = Q.side / (2 : ℝ) ^ j ∧
    ∀ i, k i < 2 ^ j ∧ Q'.corner i = Q.corner i + (k i : ℝ) * Q'.side

inductive Region where
  | cube (Q : Cube)
  | punctured (Q Q' : Cube) (h : DyadicDescendant Q' Q ∧ Q'.side < Q.side)

def regionOuter : Region → Cube
  | .cube Q => Q
  | .punctured Q _ _ => Q

def regionSet : Region → Set (E 3)
  | .cube Q => cubeSet Q
  | .punctured Q Q' _ => cubeSet Q \ cubeSet Q'

structure CubePartition where
  root : Cube
  regions : Finset Region
  dyadic : ∀ R ∈ regions, DyadicDescendant (regionOuter R) root
  disjoint : ∀ R ∈ regions, ∀ R' ∈ regions, R ≠ R' → Disjoint (regionSet R) (regionSet R')
  covers : (⋃ R ∈ regions, regionSet R) = cubeSet root

def regionOverlap (S T : CubePartition) (g : Motion 3) : ℕ :=
  ((S.regions ×ˢ T.regions).filter (fun RR' =>
    (g '' regionSet RR'.1 ∩ regionSet RR'.2).Nonempty)).card

/-- A finite cloud is contained in a half-open cube with positive side. -/
theorem finite_cloud_containing_cube (X : Finset (E 3)) :
    ∃ Q : Cube, (X : Set (E 3)) ⊆ cubeSet Q := by
  let B : ℕ := X.sup (fun x => Finset.univ.sup (fun i : Fin 3 => ⌈|x i|⌉₊))
  let S : ℝ := (B : ℝ) + 1
  have hS : 0 < S := by dsimp [S]; positivity
  let Q : Cube := ⟨WithLp.toLp 2 (fun _ => -S), 2*S, by positivity⟩
  refine ⟨Q, ?_⟩
  intro x hx i
  have hi : ⌈|x i|⌉₊ ≤ B :=
    (Finset.le_sup (f := fun j : Fin 3 => ⌈|x j|⌉₊) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun y : E 3 => Finset.univ.sup (fun j : Fin 3 => ⌈|y j|⌉₊)) hx)
  have habs : |x i| ≤ (B : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hi)
  change -S ≤ x i ∧ x i < -S + 2*S
  dsimp [S]
  constructor <;> linarith [le_abs_self (x i), neg_abs_le (x i)]

/-- Every cube is its own level-zero dyadic descendant. -/
theorem dyadicDescendant_refl (Q : Cube) : DyadicDescendant Q Q := by
  refine ⟨0, fun _ => 0, ?_, ?_⟩
  · simp
  · intro i
    simp

/-- The single containing cube suffices in the bounded-r regime. -/
theorem cube_partition_small_r (X : Finset (E 3)) (N r : ℝ)
    (hN : 1 ≤ N) (hr : 1 ≤ r) (hr8 : r ≤ 8) (hX : (X.card : ℝ) ≤ N) :
    ∃ S : CubePartition, (X : Set (E 3)) ⊆ cubeSet S.root ∧
      (S.regions.card : ℝ) ≤ 19*r ∧
      ∀ R ∈ S.regions, ((pointsIn X (regionSet R)).card : ℝ) ≤ 8*N/r := by
  obtain ⟨Q, hQ⟩ := finite_cloud_containing_cube X
  let S : CubePartition :=
    { root := Q
      regions := {Region.cube Q}
      dyadic := by intro R hR; simp only [Finset.mem_singleton] at hR; subst R; exact dyadicDescendant_refl Q
      disjoint := by
        intro R hR R' hR' hne
        simp only [Finset.mem_singleton] at hR hR'
        exact (hne (hR.trans hR'.symm)).elim
      covers := by simp [regionSet] }
  refine ⟨S, hQ, ?_, ?_⟩
  · simp only [S, Finset.card_singleton, Nat.cast_one]
    linarith
  · intro R hR
    have hReq : R = Region.cube Q := Finset.mem_singleton.mp hR
    rw [hReq]
    have hsub : (pointsIn X (cubeSet Q)).card ≤ X.card := Finset.card_filter_le _ _
    have hmass : (X.card : ℝ) ≤ 8*N/r := by
      apply (le_div_iff₀ (by linarith : 0 < r)).mpr
      nlinarith
    exact (Nat.cast_le.mpr hsub).trans hmass

/-- One of the eight half-side dyadic children. -/
noncomputable def cubeChild (Q : Cube) (b : Fin 3 → Fin 2) : Cube :=
  ⟨WithLp.toLp 2 (fun i => Q.corner i + ((b i).val : ℝ) * (Q.side/2)),
    Q.side/2, div_pos Q.side_pos (by norm_num)⟩

theorem cubeChild_descendant (Q : Cube) (b : Fin 3 → Fin 2) :
    DyadicDescendant (cubeChild Q b) Q := by
  refine ⟨1, fun i => (b i).val, ?_, ?_⟩
  · simp [cubeChild]
  · intro i
    refine ⟨by simpa using (b i).isLt, ?_⟩
    rfl

theorem cubeChild_subset (Q : Cube) (b : Fin 3 → Fin 2) : cubeSet (cubeChild Q b) ⊆ cubeSet Q := by
  intro x hx i
  have h := hx i
  have hbNat : (b i).val ≤ 1 := by have := (b i).isLt; omega
  have hb0 : (0 : ℝ) ≤ (b i).val := by positivity
  have hb1 : ((b i).val : ℝ) ≤ 1 := by exact_mod_cast hbNat
  change Q.corner i + ((b i).val : ℝ)*(Q.side/2) ≤ x i ∧
    x i < Q.corner i + ((b i).val : ℝ)*(Q.side/2) + Q.side/2 at h
  constructor <;> nlinarith [Q.side_pos]

/-- The half-open convention gives an exact cover, including dyadic boundaries. -/
theorem cubeChildren_cover (Q : Cube) : (⋃ b : Fin 3 → Fin 2, cubeSet (cubeChild Q b)) = cubeSet Q := by
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    exact cubeChild_subset Q b hb
  · intro hx
    let b : Fin 3 → Fin 2 := fun i => if x i < Q.corner i + Q.side/2 then 0 else 1
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_⟩
    intro i
    have h := hx i
    by_cases hi : x i < Q.corner i + Q.side/2
    · simpa [cubeChild, b, hi] using And.intro h.1 hi
    · have hl : Q.corner i + Q.side/2 ≤ x i := le_of_not_gt hi
      change Q.corner i + ((b i).val : ℝ)*(Q.side/2) ≤ x i ∧
        x i < Q.corner i + ((b i).val : ℝ)*(Q.side/2) + Q.side/2
      simp only [b, if_neg hi, Fin.val_one, Nat.cast_one, one_mul]
      constructor
      · exact hl
      · linarith [h.2]

/-- Different dyadic children have disjoint half-open point sets. -/
theorem cubeChildren_disjoint (Q : Cube) (b c : Fin 3 → Fin 2) (hbc : b ≠ c) :
    Disjoint (cubeSet (cubeChild Q b)) (cubeSet (cubeChild Q c)) := by
  apply Set.disjoint_left.mpr
  intro x hxb hxc
  apply hbc
  funext i
  apply Fin.ext
  have hb := (b i).isLt
  have hc := (c i).isLt
  have hXb := hxb i
  have hXc := hxc i
  change Q.corner i + ((b i).val : ℝ)*(Q.side/2) ≤ x i ∧
    x i < Q.corner i + ((b i).val : ℝ)*(Q.side/2) + Q.side/2 at hXb
  change Q.corner i + ((c i).val : ℝ)*(Q.side/2) ≤ x i ∧
    x i < Q.corner i + ((c i).val : ℝ)*(Q.side/2) + Q.side/2 at hXc
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hb0 : (b i).val = 0 := by omega
    have hc1 : (c i).val = 1 := by omega
    rw [hb0] at hXb
    rw [hc1] at hXc
    norm_num at hXb hXc
    linarith
  · have hb1 : (b i).val = 1 := by omega
    have hc0 : (c i).val = 0 := by omega
    rw [hb1] at hXb
    rw [hc0] at hXc
    norm_num at hXb hXc
    linarith

private lemma cubeSet_measurable (Q : Cube) : MeasurableSet (cubeSet Q) := by
  rw [show cubeSet Q = (WithLp.ofLp : E 3 → (Fin 3 → ℝ)) ⁻¹'
      Set.pi Set.univ (fun i => Set.Ico (Q.corner i) (Q.corner i + Q.side)) by
    ext x
    simp [cubeSet, Set.mem_Ico]]
  have hbox : MeasurableSet
      (Set.pi (Set.univ : Set (Fin 3)) (fun i => Set.Ico (Q.corner i) (Q.corner i + Q.side))) := by
    exact MeasurableSet.univ_pi fun i => measurableSet_Ico
  exact hbox.preimage (PiLp.volume_preserving_ofLp (Fin 3)).measurable

private lemma cubeSet_volume (Q : Cube) :
    MeasureTheory.volume (cubeSet Q) = ENNReal.ofReal Q.side ^ 3 := by
  have hbox : MeasurableSet
      (Set.pi (Set.univ : Set (Fin 3)) (fun i => Set.Ico (Q.corner i) (Q.corner i + Q.side))) := by
    exact MeasurableSet.univ_pi fun i => measurableSet_Ico
  rw [show cubeSet Q = (WithLp.ofLp : E 3 → (Fin 3 → ℝ)) ⁻¹'
      Set.pi Set.univ (fun i => Set.Ico (Q.corner i) (Q.corner i + Q.side)) by
    ext x
    simp [cubeSet, Set.mem_Ico]]
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage hbox.nullMeasurableSet]
  rw [Real.volume_pi_Ico]
  simp [Real.volume_Ico, Q.side_pos, Finset.prod_const, Fintype.card_fin]

private lemma cubeSet_ball (Q : Cube) (x : E 3) (hx : x ∈ cubeSet Q) :
    cubeSet Q ⊆ Metric.ball x (Real.sqrt 3 * Q.side) := by
  intro y hy
  rw [Metric.mem_ball, EuclideanSpace.dist_eq]
  have hcoord (i : Fin 3) : dist (y i) (x i) < Q.side := by
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor
    · have hylo := (hy i).1
      have hxhi := (hx i).2
      dsimp [cubeSet] at hylo hxhi
      linarith
    · have hyhi := (hy i).2
      have hxlo := (hx i).1
      dsimp [cubeSet] at hyhi hxlo
      linarith
  have hsum :
      (∑ i : Fin 3, dist (y i) (x i) ^ 2) < 3 * Q.side ^ 2 := by
    calc
      (∑ i : Fin 3, dist (y i) (x i) ^ 2) <
          ∑ i : Fin 3, Q.side ^ 2 := by
            apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            intro i hi
            have h := hcoord i
            have hnonneg : 0 ≤ dist (y i) (x i) := dist_nonneg
            have hprod := mul_pos (sub_pos.mpr h)
              (add_pos_of_nonneg_of_pos hnonneg Q.side_pos)
            nlinarith [hprod]
      _ = 3 * Q.side ^ 2 := by simp
  have hsqrt : Real.sqrt (∑ i : Fin 3, dist (y i) (x i) ^ 2) <
      Real.sqrt 3 * Q.side := by
    have := Real.sqrt_lt_sqrt (by positivity :
      0 ≤ ∑ i : Fin 3, dist (y i) (x i) ^ 2) hsum
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq Q.side_pos.le] at this
    exact this
  exact hsqrt

private lemma exists_scale_dyadic_cube (Q : Cube) (x : E 3) (hx : x ∈ cubeSet Q)
    (s : ℝ) (hs : 0 < s) (hside : s ≤ Q.side) :
    ∃ C : Cube, DyadicDescendant C Q ∧ x ∈ cubeSet C ∧ s / 2 < C.side ∧ C.side ≤ s := by
  have hpow : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)
  obtain ⟨n₀, hn₀⟩ := (hpow.eventually_ge_atTop (Q.side / s)).exists
  have hcross : Q.side ≤ (2 : ℝ) ^ n₀ * s :=
    (div_le_iff₀ hs).mp hn₀
  have hex : ∃ n : ℕ, Q.side / (2 : ℝ) ^ n ≤ s := by
    refine ⟨n₀, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n₀)).2
    nlinarith [hcross]
  let n := Nat.find hex
  have hnhi : Q.side / (2 : ℝ) ^ n ≤ s := Nat.find_spec hex
  have hnlo : s / 2 < Q.side / (2 : ℝ) ^ n := by
    by_cases hn0 : n = 0
    · rw [hn0, pow_zero]
      nlinarith [hside, hnhi]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hprev : s < Q.side / (2 : ℝ) ^ (n - 1) := by
        by_contra hnot
        have hfind : Nat.find hex ≤ n - 1 := Nat.find_min' hex (le_of_not_gt hnot)
        dsimp [n] at hfind
        omega
      have hpowEq : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
        calc
          (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hnpos]
          _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
      have hratio : Q.side / (2 : ℝ) ^ n =
          (Q.side / (2 : ℝ) ^ (n - 1)) / 2 := by
        rw [hpowEq]
        field_simp
      rw [hratio]
      linarith
  let a : ℝ := Q.side / (2 : ℝ) ^ n
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos Q.side_pos (pow_pos (by norm_num) _)
  have hpowMul : (2 : ℝ) ^ n * a = Q.side := by
    dsimp [a]
    field_simp
  let k : Fin 3 → ℕ := fun i => ⌊(x i - Q.corner i) / a⌋₊
  let C : Cube := ⟨WithLp.toLp 2 (fun i => Q.corner i + (k i : ℝ) * a), a, ha⟩
  have hcell (i : Fin 3) :
      k i < 2 ^ n ∧ C.corner i ≤ x i ∧ x i < C.corner i + a := by
    let u : ℝ := (x i - Q.corner i) / a
    have hu0 : 0 ≤ u := by
      dsimp [u]
      exact div_nonneg (sub_nonneg.mpr (hx i).1) ha.le
    have huhi : u < (2 : ℝ) ^ n := by
      apply (div_lt_iff₀ ha).2
      rw [hpowMul]
      dsimp [u]
      linarith [(hx i).2]
    have hklt : k i < 2 ^ n := by
      dsimp [k]
      apply (Nat.floor_lt hu0).2
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using huhi
    have hklow : (k i : ℝ) ≤ u := by
      dsimp [k]
      exact Nat.floor_le hu0
    have hkup : u < (k i : ℝ) + 1 := by
      dsimp [k]
      exact Nat.lt_floor_add_one _
    have hxeq : x i = Q.corner i + u * a := by
      dsimp [u]
      field_simp [ne_of_gt ha]
      <;> ring
    have hlow : Q.corner i + (k i : ℝ) * a ≤ x i := by
      rw [hxeq]
      nlinarith [mul_le_mul_of_nonneg_right hklow ha.le]
    have huupper : Q.corner i + u * a < Q.corner i + (k i : ℝ) * a + a := by
      calc
        Q.corner i + u * a < Q.corner i + ((k i : ℝ) + 1) * a :=
          by nlinarith [mul_lt_mul_of_pos_right hkup ha]
        _ = Q.corner i + (k i : ℝ) * a + a := by ring
    refine ⟨hklt, ?_, ?_⟩
    · simpa [C] using hlow
    · rw [hxeq]
      simpa [C] using huupper
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · refine ⟨n, k, ?_, ?_⟩
    · rfl
    · intro i
      refine ⟨(hcell i).1, ?_⟩
      simp [C]
  · intro i
    exact ⟨(hcell i).2.1, by simpa [C] using (hcell i).2.2⟩
  · simpa [C, a] using hnlo
  · simpa [C, a] using hnhi

private lemma dyadic_intersect_subset (Q C D : Cube)
    (hC : DyadicDescendant C Q) (hD : DyadicDescendant D Q)
    (hside : D.side ≤ C.side) (hne : (cubeSet C ∩ cubeSet D).Nonempty) :
    cubeSet D ⊆ cubeSet C ∧ DyadicDescendant D C := by
  rcases hC with ⟨n, kC, hCs, hCc⟩
  rcases hD with ⟨m, kD, hDs, hDc⟩
  have hside' : Q.side / (2 : ℝ) ^ m ≤ Q.side / (2 : ℝ) ^ n := by
    simpa [hDs, hCs] using hside
  have hcross : Q.side * (2 : ℝ) ^ n ≤ Q.side * (2 : ℝ) ^ m :=
    (div_le_div_iff₀ (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)).mp hside'
  have hpowReal : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ m :=
    le_of_mul_le_mul_left hcross Q.side_pos
  have hnm : n ≤ m := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    exact_mod_cast hpowReal
  have hpow : (2 : ℝ) ^ m = (2 : ℝ) ^ n * (2 : ℝ) ^ (m - n) := by
    calc
      (2 : ℝ) ^ m = (2 : ℝ) ^ (n + (m - n)) := by rw [Nat.add_sub_of_le hnm]
      _ = (2 : ℝ) ^ n * (2 : ℝ) ^ (m - n) := by rw [pow_add]
  have hscale : C.side = (2 : ℝ) ^ (m - n) * D.side := by
    rw [hCs, hDs, hpow]
    field_simp
  obtain ⟨z, hz⟩ := hne
  have hlow (i : Fin 3) : kC i * 2 ^ (m - n) ≤ kD i := by
    have hineq : C.corner i < D.corner i + D.side :=
      lt_of_le_of_lt (hz.1 i).1 (hz.2 i).2
    rw [(hCc i).2, (hDc i).2, hscale] at hineq
    have hineq' : (kC i : ℝ) * (2 : ℝ) ^ (m - n) < (kD i : ℝ) + 1 := by
      nlinarith [hineq, D.side_pos]
    have hineqNat : kC i * 2 ^ (m - n) < kD i + 1 := by exact_mod_cast hineq'
    omega
  have hhigh (i : Fin 3) : kD i + 1 ≤ (kC i + 1) * 2 ^ (m - n) := by
    have hineq : D.corner i < C.corner i + C.side :=
      lt_of_le_of_lt (hz.2 i).1 (hz.1 i).2
    rw [(hDc i).2, (hCc i).2, hscale] at hineq
    have hineq' : (kD i : ℝ) < ((kC i : ℝ) + 1) * (2 : ℝ) ^ (m - n) := by
      nlinarith [hineq, D.side_pos]
    have hineqNat : kD i < (kC i + 1) * 2 ^ (m - n) := by exact_mod_cast hineq'
    omega
  let kRel : Fin 3 → ℕ := fun i => kD i - kC i * 2 ^ (m - n)
  have hsideRel : D.side = C.side / (2 : ℝ) ^ (m - n) := by
    rw [hscale]
    field_simp
  have hrelBound (i : Fin 3) : kRel i < 2 ^ (m - n) := by
    have hlo := hlow i
    have hhi := hhigh i
    have hhi' : kD i + 1 ≤ kC i * 2 ^ (m - n) + 2 ^ (m - n) := by
      simpa [Nat.add_mul] using hhi
    have hdecomp : kC i * 2 ^ (m - n) + kRel i = kD i := by
      dsimp [kRel]
      omega
    dsimp [kRel]
    omega
  have hcornerRel (i : Fin 3) :
      D.corner i = C.corner i + (kRel i : ℝ) * D.side := by
    have hidxNat : kD i = kC i * 2 ^ (m - n) +
        (kD i - kC i * 2 ^ (m - n)) := by
      have hlo := hlow i
      omega
    have hidxReal : (kD i : ℝ) = (kC i : ℝ) * (2 : ℝ) ^ (m - n) +
        (kRel i : ℝ) := by
      dsimp [kRel]
      exact_mod_cast hidxNat
    rw [(hDc i).2, (hCc i).2, hscale, hidxReal]
    ring
  have hdesc : DyadicDescendant D C := ⟨m - n, kRel, hsideRel,
    fun i => ⟨hrelBound i, hcornerRel i⟩⟩
  constructor
  · intro y hy i
    have hlowReal : (kC i : ℝ) * (2 : ℝ) ^ (m - n) ≤ (kD i : ℝ) := by
      exact_mod_cast hlow i
    have hhighReal : (kD i : ℝ) + 1 ≤ ((kC i : ℝ) + 1) * (2 : ℝ) ^ (m - n) := by
      exact_mod_cast hhigh i
    have hLower : C.corner i ≤ D.corner i := by
      rw [(hCc i).2, (hDc i).2, hscale]
      nlinarith [mul_le_mul_of_nonneg_right hlowReal D.side_pos.le]
    have hUpper : D.corner i + D.side ≤ C.corner i + C.side := by
      rw [(hDc i).2, (hCc i).2, hscale]
      nlinarith [mul_le_mul_of_nonneg_right hhighReal D.side_pos.le]
    exact ⟨hLower.trans (hy i).1, lt_of_lt_of_le (hy i).2 hUpper⟩
  · exact hdesc

private lemma dyadicDescendant_subset_cube (Q C : Cube)
    (h : DyadicDescendant C Q) : cubeSet C ⊆ cubeSet Q := by
  rcases h with ⟨j, k, hside, hcorner⟩
  have hpowMul : (2 : ℝ) ^ j * C.side = Q.side := by
    rw [hside]
    field_simp
  intro x hx i
  have hkNat := (hcorner i).1
  have hkR : (k i : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
    exact_mod_cast (Nat.succ_le_of_lt hkNat)
  have hLower : Q.corner i ≤ C.corner i := by
    rw [(hcorner i).2]
    nlinarith [mul_nonneg (Nat.cast_nonneg (k i)) C.side_pos.le]
  have hUpper : C.corner i + C.side ≤ Q.corner i + Q.side := by
    rw [(hcorner i).2]
    nlinarith [mul_le_mul_of_nonneg_right hkR C.side_pos.le, hpowMul]
  exact ⟨hLower.trans (hx i).1, lt_of_lt_of_le (hx i).2 hUpper⟩

/-- Dyadic ancestry composes by concatenating the binary coordinate addresses. -/
theorem dyadicDescendant_trans {A B C : Cube}
    (hCB : DyadicDescendant C B) (hBA : DyadicDescendant B A) : DyadicDescendant C A := by
  rcases hCB with ⟨n, k, hC, hk⟩
  rcases hBA with ⟨m, l, hB, hl⟩
  have hscale : B.side = (2 : ℝ)^n * C.side := by rw [hC]; field_simp
  refine ⟨m+n, fun i => l i * 2^n + k i, ?_, ?_⟩
  · rw [hC, hB, pow_add]
    field_simp
  · intro i
    constructor
    · have hli : l i + 1 ≤ 2^m := Nat.succ_le_of_lt (hl i).1
      have hki := (hk i).1
      rw [Nat.pow_add]
      nlinarith [Nat.mul_le_mul_right (2^n) hli]
    · rw [(hk i).2, (hl i).2, hscale]
      push_cast
      ring

theorem dyadicDescendant_side_le {C Q : Cube} (h : DyadicDescendant C Q) : C.side ≤ Q.side := by
  obtain ⟨j,k,hside,hcorner⟩ := h
  have hp : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  rw [hside]
  exact div_le_self Q.side_pos.le hp

theorem dyadicDescendant_strict {C Q : Cube} (h : DyadicDescendant C Q) (hne : C ≠ Q) :
    C.side < Q.side := by
  obtain ⟨j,k,hside,hcorner⟩ := h
  have hj : j ≠ 0 := by
    intro hj
    subst j
    have hs : C.side = Q.side := by simpa using hside
    have hc : C.corner = Q.corner := by
      ext i
      have hk0 : k i = 0 := by have := (hcorner i).1; norm_num at this; omega
      simpa [hk0] using (hcorner i).2
    apply hne
    cases C
    cases Q
    simp_all
  have hp : (1 : ℝ) < 2^j := one_lt_pow₀ (by norm_num) hj
  rw [hside]
  exact div_lt_self Q.side_pos hp

/-- Finite separation provides a depth at which every cube is light. -/
theorem finite_cloud_light_depth (X : Finset (E 3)) (Q : Cube) (μ : ℝ) (hμ : 1 ≤ μ) :
    ∃ n : ℕ, ∀ C : Cube, C.side = Q.side / (2 : ℝ)^n → cloudMass X (cubeSet C) ≤ μ := by
  obtain ⟨δ,hδ,hsep⟩ := finite_cloud_separation X
  have hp : Filter.Tendsto (fun n : ℕ => (2 : ℝ)^n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨n,hn⟩ := (hp.eventually_ge_atTop (Real.sqrt 3 * Q.side / δ)).exists
  have hsize : Real.sqrt 3 * (Q.side / (2 : ℝ)^n) ≤ δ := by
    have := (div_le_iff₀ hδ).mp hn
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^n)).mpr
    simpa [mul_comm] using this
  refine ⟨n, ?_⟩
  intro C hC
  have hc : (pointsIn X (cubeSet C)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    obtain ⟨hxX,hxC⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyX,hyC⟩ := Finset.mem_filter.mp hy
    have hlow := hsep x hxX y hyX hxy
    have hhigh := Metric.mem_ball.mp (cubeSet_ball C y hyC hxC)
    rw [hC] at hhigh
    linarith
  exact (show cloudMass X (cubeSet C) ≤ 1 by dsimp [cloudMass]; exact_mod_cast hc).trans hμ

noncomputable def cubeSingletonPartition (Q : Cube) : CubePartition :=
  { root := Q
    regions := {Region.cube Q}
    dyadic := by intro R hR; simp only [Finset.mem_singleton] at hR; subst R; exact dyadicDescendant_refl Q
    disjoint := by
      intro R hR R' hR' hne
      simp only [Finset.mem_singleton] at hR hR'
      exact (hne (hR.trans hR'.symm)).elim
    covers := by simp [regionSet] }

theorem CubePartition.region_subset (S : CubePartition) (R : Region) (hR : R ∈ S.regions) :
    regionSet R ⊆ cubeSet S.root := by
  intro x hx
  rw [← S.covers]
  exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR,hx⟩⟩

/-- Complete a partition of a descendant by adjoining the enclosing one-hole region. -/
noncomputable def CubePartition.enclose (S : CubePartition) (Q : Cube)
    (hd : DyadicDescendant S.root Q) : CubePartition := by
  by_cases heq : S.root = Q
  · exact { S with root := Q, dyadic := by simpa [heq] using S.dyadic,
                    covers := by simpa [heq] using S.covers }
  · let H : Region := .punctured Q S.root ⟨hd, dyadicDescendant_strict hd heq⟩
    refine { root := Q, regions := insert H S.regions, dyadic := ?_, disjoint := ?_, covers := ?_ }
    · intro R hR
      rcases Finset.mem_insert.mp hR with rfl | hR
      · exact dyadicDescendant_refl Q
      · exact dyadicDescendant_trans (S.dyadic R hR) hd
    · intro R hR R' hR' hne
      rcases Finset.mem_insert.mp hR with rfl | hR <;>
        rcases Finset.mem_insert.mp hR' with rfl | hR'
      · exact (hne rfl).elim
      · exact Set.disjoint_left.mpr (fun x hx hx' => hx.2 (S.region_subset R' hR' hx'))
      · exact Set.disjoint_left.mpr (fun x hx hx' => hx'.2 (S.region_subset R hR hx))
      · exact S.disjoint R hR R' hR' hne
    · have hsub := dyadicDescendant_subset_cube Q S.root hd
      ext x
      simp only [Finset.mem_insert, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨R, rfl | hR, hx⟩
        · exact hx.1
        · exact hsub (S.region_subset R hR hx)
      · intro hx
        by_cases hin : x ∈ cubeSet S.root
        · have hcov : x ∈ ⋃ R ∈ S.regions, regionSet R := by rw [S.covers]; exact hin
          obtain ⟨R,hR,hxR⟩ := (by simpa using hcov : ∃ R ∈ S.regions, x ∈ regionSet R)
          exact ⟨R,Or.inr hR,hxR⟩
        · exact ⟨H,Or.inl rfl,⟨hx,hin⟩⟩

theorem CubePartition.enclose_card (S : CubePartition) (Q : Cube) (hd : DyadicDescendant S.root Q) :
    (S.enclose Q hd).regions.card ≤ S.regions.card + 1 := by
  unfold CubePartition.enclose
  split
  · simp
  · exact Finset.card_insert_le _ _

theorem CubePartition.enclose_mass (X : Finset (E 3)) (S : CubePartition) (Q : Cube)
    (hd : DyadicDescendant S.root Q) (B : ℝ)
    (hS : ∀ R ∈ S.regions, cloudMass X (regionSet R) ≤ B)
    (hgap : cloudMass X (cubeSet Q \ cubeSet S.root) ≤ B) :
    ∀ R ∈ (S.enclose Q hd).regions, cloudMass X (regionSet R) ≤ B := by
  unfold CubePartition.enclose
  split
  · exact hS
  · intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · exact hgap
    · exact hS R hR

@[simp] theorem CubePartition.enclose_root (S : CubePartition) (Q : Cube) (hd : DyadicDescendant S.root Q) :
    (S.enclose Q hd).root = Q := by
  unfold CubePartition.enclose
  split <;> rfl

/-- Assemble exact partitions of the eight children. -/
noncomputable def cubeChildrenPartition (Q : Cube) (S : (Fin 3 → Fin 2) → CubePartition)
    (hroot : ∀ b, (S b).root = cubeChild Q b) : CubePartition :=
  { root := Q
    regions := Finset.univ.biUnion (fun b => (S b).regions)
    dyadic := by
      intro R hR
      obtain ⟨b,_,hRb⟩ := Finset.mem_biUnion.mp hR
      have hd := (S b).dyadic R hRb
      rw [hroot b] at hd
      exact dyadicDescendant_trans hd (cubeChild_descendant Q b)
    disjoint := by
      intro R hR R' hR' hne
      obtain ⟨b,_,hRb⟩ := Finset.mem_biUnion.mp hR
      obtain ⟨c,_,hRc⟩ := Finset.mem_biUnion.mp hR'
      by_cases hbc : b = c
      · subst c
        exact (S b).disjoint R hRb R' hRc hne
      · have hsubb := (S b).region_subset R hRb
        have hsubc := (S c).region_subset R' hRc
        rw [hroot b] at hsubb
        rw [hroot c] at hsubc
        exact (cubeChildren_disjoint Q b c hbc).mono hsubb hsubc
    covers := by
      ext x
      constructor
      · intro hx
        obtain ⟨R,hR,hxR⟩ := (by simpa using hx : ∃ R ∈ Finset.univ.biUnion (fun b => (S b).regions), x ∈ regionSet R)
        obtain ⟨b,_,hRb⟩ := Finset.mem_biUnion.mp hR
        have hin := (S b).region_subset R hRb hxR
        rw [hroot b] at hin
        exact cubeChild_subset Q b hin
      · intro hx
        rw [← cubeChildren_cover Q] at hx
        obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hx
        rw [← hroot b, ← (S b).covers] at hb
        obtain ⟨R,hR,hxR⟩ := (by simpa using hb : ∃ R ∈ (S b).regions, x ∈ regionSet R)
        exact Set.mem_iUnion.mpr ⟨R,Set.mem_iUnion.mpr
          ⟨Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,hR⟩,hxR⟩⟩ }

theorem cubeChildrenPartition_card (Q : Cube) (S : (Fin 3 → Fin 2) → CubePartition)
    (hroot : ∀ b, (S b).root = cubeChild Q b) :
    ((cubeChildrenPartition Q S hroot).regions.card : ℝ) ≤ ∑ b, ((S b).regions.card : ℝ) := by
  exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := fun b => (S b).regions))

theorem cubeChildrenPartition_mass (X : Finset (E 3)) (Q : Cube)
    (S : (Fin 3 → Fin 2) → CubePartition) (hroot : ∀ b, (S b).root = cubeChild Q b) (M : ℝ)
    (hM : ∀ b, ∀ R ∈ (S b).regions, cloudMass X (regionSet R) ≤ M) :
    ∀ R ∈ (cubeChildrenPartition Q S hroot).regions, cloudMass X (regionSet R) ≤ M := by
  intro R hR
  obtain ⟨b,_,hRb⟩ := Finset.mem_biUnion.mp hR
  exact hM b R hRb

theorem cloudMass_children (X : Finset (E 3)) (Q : Cube) :
    ∑ b : Fin 3 → Fin 2, cloudMass X (cubeSet (cubeChild Q b)) = cloudMass X (cubeSet Q) := by
  rw [← cloudMass_iUnion X Finset.univ (fun b => cubeSet (cubeChild Q b))
    (fun b _ c _ hbc => cubeChildren_disjoint Q b c hbc)]
  simp only [Finset.mem_univ, Set.iUnion_true, cubeChildren_cover]

/-- Seven light siblings contribute at most seven threshold masses. -/
theorem cube_unique_heavy_gap (X : Finset (E 3)) (Q : Cube) (b : Fin 3 → Fin 2)
    (μ : ℝ) (hsiblings : ∀ c, c ≠ b → cloudMass X (cubeSet (cubeChild Q c)) ≤ μ) :
    cloudMass X (cubeSet Q \ cubeSet (cubeChild Q b)) ≤ 7*μ := by
  have hsum := cloudMass_children X Q
  have herase : ∑ c ∈ Finset.univ.erase b, cloudMass X (cubeSet (cubeChild Q c)) ≤ 7*μ := by
    calc
      _ ≤ ∑ _c ∈ Finset.univ.erase b, μ :=
        Finset.sum_le_sum (fun c hc => hsiblings c (Finset.mem_erase.mp hc).1)
      _ = 7*μ := by simp [Fintype.card_fun, Finset.card_erase_of_mem]
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := fun c => cloudMass X (cubeSet (cubeChild Q c))) (Finset.mem_univ b)
  have hmass := cloudMass_diff_add X (cubeChild_subset Q b)
  linarith

/-- Recursive subdivision carries one unfinished one-hole region above its partition. -/
structure CubeFragment (X : Finset (E 3)) (μ : ℝ) (Q : Cube) where
  partition : CubePartition
  descendant : DyadicDescendant partition.root Q
  gap_small : cloudMass X (cubeSet Q \ cubeSet partition.root) < μ
  leaves : ℕ
  leaves_pos : 0 < leaves
  leaves_budget : (leaves : ℝ)*μ < cloudMass X (cubeSet Q)
  count_budget : (partition.regions.card : ℝ)*μ ≤ cloudMass X (cubeSet partition.root) +
    9*(2*(leaves : ℝ)-1)*μ
  mass_bound : ∀ R ∈ partition.regions, cloudMass X (regionSet R) ≤ 8*μ

/-- Finalizing the pending hole adds at most one region. -/
noncomputable def CubeFragment.complete {X : Finset (E 3)} {μ : ℝ} {Q : Cube}
    (F : CubeFragment X μ Q) : CubePartition := F.partition.enclose Q F.descendant

@[simp] theorem CubeFragment.complete_root {X : Finset (E 3)} {μ : ℝ} {Q : Cube}
    (F : CubeFragment X μ Q) : F.complete.root = Q := by simp [CubeFragment.complete]

theorem CubeFragment.complete_card {X : Finset (E 3)} {μ : ℝ} {Q : Cube}
    (F : CubeFragment X μ Q) : F.complete.regions.card ≤ F.partition.regions.card + 1 :=
  F.partition.enclose_card Q F.descendant

theorem CubeFragment.complete_mass {X : Finset (E 3)} {μ : ℝ} {Q : Cube}
    (F : CubeFragment X μ Q) (hμ : 0 ≤ μ) :
    ∀ R ∈ F.complete.regions, cloudMass X (regionSet R) ≤ 8*μ := by
  apply F.partition.enclose_mass X Q F.descendant (8*μ) F.mass_bound
  linarith [F.gap_small]

theorem CubeFragment.unary (X : Finset (E 3)) (μ : ℝ) (hμ : 0 < μ) (Q : Cube)
    (b : Fin 3 → Fin 2) (F : CubeFragment X μ (cubeChild Q b))
    (hsiblings : ∀ c, c ≠ b → cloudMass X (cubeSet (cubeChild Q c)) ≤ μ) :
    Nonempty (CubeFragment X μ Q) := by
  have hd := dyadicDescendant_trans F.descendant (cubeChild_descendant Q b)
  have hmass := cloudMass_diff_add X (dyadicDescendant_subset_cube Q F.partition.root hd)
  have hchildmass := cloudMass_diff_add X
    (dyadicDescendant_subset_cube (cubeChild Q b) F.partition.root F.descendant)
  have hsiblingmass := cloudMass_diff_add X (cubeChild_subset Q b)
  have hgap : cloudMass X (cubeSet Q \ cubeSet F.partition.root) ≤ 8*μ := by
    have hseven := cube_unique_heavy_gap X Q b μ hsiblings
    linarith [F.gap_small]
  have hlbudget : (F.leaves : ℝ)*μ < cloudMass X (cubeSet Q) :=
    F.leaves_budget.trans_le (cloudMass_mono X (cubeChild_subset Q b))
  by_cases hsmall : cloudMass X (cubeSet Q \ cubeSet F.partition.root) < μ
  · exact ⟨{ F with descendant := hd, gap_small := hsmall, leaves_budget := hlbudget }⟩
  · let S := F.partition.enclose Q hd
    have hcard : (S.regions.card : ℝ)*μ ≤ (F.partition.regions.card : ℝ)*μ + μ := by
      have hc : (S.regions.card : ℝ) ≤ F.partition.regions.card + 1 := by
        exact_mod_cast F.partition.enclose_card Q hd
      nlinarith
    refine ⟨{
      partition := S, descendant := ?_, gap_small := ?_,
      leaves := F.leaves, leaves_pos := F.leaves_pos, leaves_budget := hlbudget,
      count_budget := ?_, mass_bound := ?_ }⟩
    · simpa [S] using dyadicDescendant_refl Q
    · simp [S, hμ]
    · have hc := F.count_budget
      have hlarge := le_of_not_gt hsmall
      simp only [S, CubePartition.enclose_root]
      linarith
    · exact F.partition.enclose_mass X Q hd (8*μ) F.mass_bound hgap

/-- Extending a function on a finite subset by zero preserves its sum. -/
theorem sum_finset_dite {α : Type*} [Fintype α] [DecidableEq α] (H : Finset α) (f : H → ℝ) :
    (∑ b : α, if hb : b ∈ H then f ⟨b,hb⟩ else 0) = ∑ b : H, f b := by
  change (∑ b ∈ Finset.univ, if hb : b ∈ H then f ⟨b,hb⟩ else 0) = ∑ b ∈ H.attach, f b
  calc
    _ = ∑ b ∈ H, if hb : b ∈ H then f ⟨b,hb⟩ else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ H)
      intro b _ hb
      simp [hb]
    _ = _ := by
      apply Finset.sum_bij (fun b hb => (⟨b,hb⟩ : H))
      · intro b hb; simp
      · intro b hb c hc hbc; exact congrArg Subtype.val hbc
      · intro b hb; exact ⟨b.val,b.property,rfl⟩
      · intro b hb; exact dif_pos hb

theorem CubeFragment.leaf (X : Finset (E 3)) (μ : ℝ) (hμ : 0 < μ) (Q : Cube)
    (hQ : μ < cloudMass X (cubeSet Q))
    (hchildren : ∀ b, cloudMass X (cubeSet (cubeChild Q b)) ≤ μ) :
    Nonempty (CubeFragment X μ Q) := by
  let S := cubeChildrenPartition Q (fun b => cubeSingletonPartition (cubeChild Q b)) (fun _ => rfl)
  have hcard : (S.regions.card : ℝ) ≤ 8 := by
    have := cubeChildrenPartition_card Q (fun b => cubeSingletonPartition (cubeChild Q b)) (fun _ => rfl)
    simpa [S, cubeSingletonPartition, Fintype.card_fun] using this
  refine ⟨{
    partition := S, descendant := dyadicDescendant_refl Q,
    gap_small := ?_, leaves := 1, leaves_pos := by norm_num,
    leaves_budget := by simpa using hQ, count_budget := ?_, mass_bound := ?_ }⟩
  · simpa [S, cubeChildrenPartition] using hμ
  · have hn := cloudMass_nonneg X (cubeSet Q)
    simp only [S, cubeChildrenPartition, Nat.cast_one]
    change (S.regions.card : ℝ)*μ ≤ cloudMass X (cubeSet Q)+9*(2*(1:ℝ)-1)*μ
    nlinarith
  · apply cubeChildrenPartition_mass X Q (fun b => cubeSingletonPartition (cubeChild Q b)) (fun _ => rfl)
    intro b R hR
    have heq : R = Region.cube (cubeChild Q b) := Finset.mem_singleton.mp hR
    subst R
    change cloudMass X (cubeSet (cubeChild Q b)) ≤ 8*μ
    linarith [hchildren b]

theorem CubeFragment.branch (X : Finset (E 3)) (μ : ℝ) (hμ : 0 < μ) (Q : Cube)
    (H : Finset (Fin 3 → Fin 2)) (hH : 2 ≤ H.card)
    (F : ∀ b : H, CubeFragment X μ (cubeChild Q b.val))
    (hlight : ∀ b, b ∉ H → cloudMass X (cubeSet (cubeChild Q b)) ≤ μ) :
    Nonempty (CubeFragment X μ Q) := by
  let S : (Fin 3 → Fin 2) → CubePartition := fun b =>
    if hb : b ∈ H then (F ⟨b,hb⟩).complete else cubeSingletonPartition (cubeChild Q b)
  have hroot : ∀ b, (S b).root = cubeChild Q b := by
    intro b
    dsimp [S]
    split <;> simp [cubeSingletonPartition]
  let T := cubeChildrenPartition Q S hroot
  let L : ℕ := ∑ b : H, (F b).leaves
  have hLreal : (∑ b : H, ((F b).leaves : ℝ)) = (L : ℝ) := by simp [L]
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty H := ⟨⟨hHne.choose,hHne.choose_spec⟩⟩
  have hLpos : 0 < L := by
    apply Finset.sum_pos
    · intro b _
      exact (F b).leaves_pos
    · exact Finset.univ_nonempty
  have hchildsum : (∑ b : H, cloudMass X (cubeSet (cubeChild Q b.val))) ≤ cloudMass X (cubeSet Q) := by
    change (∑ b ∈ H.attach, cloudMass X (cubeSet (cubeChild Q b.val))) ≤ cloudMass X (cubeSet Q)
    rw [Finset.sum_attach H (fun b => cloudMass X (cubeSet (cubeChild Q b))), ← cloudMass_children X Q]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
    intro b _ _
    exact cloudMass_nonneg X _
  have hLbudget : (L : ℝ)*μ < cloudMass X (cubeSet Q) := by
    have hl : (L : ℝ)*μ < ∑ b : H, cloudMass X (cubeSet (cubeChild Q b.val)) := by
      rw [← hLreal, Finset.sum_mul]
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro b _
      exact (F b).leaves_budget
    exact hl.trans_le hchildsum
  have hcard : (T.regions.card : ℝ) ≤ (∑ b : H, ((F b).partition.regions.card : ℝ)) + 8 := by
    calc
      _ ≤ ∑ b, ((S b).regions.card : ℝ) := cubeChildrenPartition_card Q S hroot
      _ ≤ ∑ b, ((if hb : b ∈ H then ((F ⟨b,hb⟩).partition.regions.card : ℝ) else 0) + 1) := by
        apply Finset.sum_le_sum
        intro b _
        by_cases hb : b ∈ H
        · simp only [S, dif_pos hb]
          exact_mod_cast (F ⟨b,hb⟩).complete_card
        · simp [S, hb, cubeSingletonPartition]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        have hz := sum_finset_dite H (fun b => ((F b).partition.regions.card : ℝ))
        have hc : (∑ _b : Fin 3 → Fin 2, (1:ℝ)) = 8 := by simp [Fintype.card_fun]
        exact congrArg₂ (· + ·) hz hc
  have hmasssum : (∑ b : H, cloudMass X (cubeSet (F b).partition.root)) ≤ cloudMass X (cubeSet Q) := by
    calc
      _ ≤ ∑ b : H, cloudMass X (cubeSet (cubeChild Q b.val)) := by
        apply Finset.sum_le_sum
        intro b _
        exact cloudMass_mono X (dyadicDescendant_subset_cube _ _ (F b).descendant)
      _ ≤ _ := hchildsum
  have hsumBudget : (∑ b : H, ((F b).partition.regions.card : ℝ))*μ ≤
      (∑ b : H, cloudMass X (cubeSet (F b).partition.root)) + 9*(2*(L:ℝ)-(H.card:ℝ))*μ := by
    calc
      _ = ∑ b : H, ((F b).partition.regions.card : ℝ)*μ := Finset.sum_mul _ _ _
      _ ≤ ∑ b : H, (cloudMass X (cubeSet (F b).partition.root) + 9*(2*((F b).leaves:ℝ)-1)*μ) :=
        Finset.sum_le_sum (fun b _ => (F b).count_budget)
      _ = _ := by
        have heq : ∀ b : H, cloudMass X (cubeSet (F b).partition.root) + 9*(2*((F b).leaves:ℝ)-1)*μ =
            cloudMass X (cubeSet (F b).partition.root) + (18*μ)*((F b).leaves:ℝ) - 9*μ := by
          intro b
          ring
        simp_rw [heq]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hLreal]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        ring
  refine ⟨{
    partition := T, descendant := dyadicDescendant_refl Q,
    gap_small := ?_, leaves := L, leaves_pos := hLpos, leaves_budget := hLbudget,
    count_budget := ?_, mass_bound := ?_ }⟩
  · simpa [T, cubeChildrenPartition] using hμ
  · have hh : (2:ℝ) ≤ H.card := by exact_mod_cast hH
    change (T.regions.card : ℝ)*μ ≤ cloudMass X (cubeSet Q)+9*(2*(L:ℝ)-1)*μ
    nlinarith
  · apply cubeChildrenPartition_mass X Q S hroot
    intro b R hR
    by_cases hb : b ∈ H
    · simp only [S, dif_pos hb] at hR
      exact (F ⟨b,hb⟩).complete_mass hμ.le R hR
    · simp only [S, dif_neg hb, cubeSingletonPartition, Finset.mem_singleton] at hR
      subst R
      change cloudMass X (cubeSet (cubeChild Q b)) ≤ 8*μ
      linarith [hlight b hb]

/-- Finite-depth induction for the compressed heavy subtree. -/
theorem cube_fragment_depth (X : Finset (E 3)) (μ : ℝ) (hμ : 0 < μ) (n : ℕ) :
    ∀ Q : Cube, μ < cloudMass X (cubeSet Q) →
      (∀ C : Cube, C.side = Q.side / (2 : ℝ)^n → cloudMass X (cubeSet C) ≤ μ) →
      Nonempty (CubeFragment X μ Q) := by
  induction n with
  | zero =>
    intro Q hQ hterminal
    have ht := hterminal Q (by simp)
    exact (not_lt_of_ge ht hQ).elim
  | succ n ih =>
    intro Q hQ hterminal
    let H : Finset (Fin 3 → Fin 2) := Finset.univ.filter (fun b => μ < cloudMass X (cubeSet (cubeChild Q b)))
    have hlight : ∀ b, b ∉ H → cloudMass X (cubeSet (cubeChild Q b)) ≤ μ := by
      intro b hb
      apply le_of_not_gt
      intro hm
      exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ b,hm⟩)
    have hsubtree : ∀ b : H, Nonempty (CubeFragment X μ (cubeChild Q b.val)) := by
      intro b
      apply ih (cubeChild Q b.val) (Finset.mem_filter.mp b.property).2
      intro C hC
      apply hterminal C
      change C.side = (Q.side/2)/(2:ℝ)^n at hC
      rw [hC, pow_succ]
      field_simp
    let F : ∀ b : H, CubeFragment X μ (cubeChild Q b.val) := fun b => Classical.choice (hsubtree b)
    by_cases hzero : H.card = 0
    · have hempty : H = ∅ := Finset.card_eq_zero.mp hzero
      exact CubeFragment.leaf X μ hμ Q hQ (fun b => hlight b (by simp [hempty]))
    · by_cases hone : H.card = 1
      · obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hone
        have hbmem : b ∈ H := by rw [hb]; simp
        apply CubeFragment.unary X μ hμ Q b (F ⟨b,hbmem⟩)
        intro c hcb
        apply hlight c
        rw [hb]
        simpa using hcb
      · exact CubeFragment.branch X μ hμ Q H (by omega) F hlight

/-- Cardinal budget after completing the pending gap. -/
theorem CubeFragment.final_count {X : Finset (E 3)} {μ : ℝ} {Q : Cube}
    (F : CubeFragment X μ Q) (hμ : 0 < μ) :
    (F.complete.regions.card : ℝ)*μ ≤ 19*cloudMass X (cubeSet Q) := by
  have hcard : (F.complete.regions.card : ℝ) ≤ F.partition.regions.card + 1 := by
    exact_mod_cast F.complete_card
  have hmass : cloudMass X (cubeSet F.partition.root) ≤ cloudMass X (cubeSet Q) :=
    cloudMass_mono X (dyadicDescendant_subset_cube Q F.partition.root F.descendant)
  nlinarith [F.count_budget, F.leaves_budget]

/-- Construct the cubical partition from finite separation and the compressed subtree. -/
theorem cube_partition_construct (X : Finset (E 3)) (N r : ℝ)
    (hN : 1 ≤ N) (hr : 1 ≤ r) (hrN : r ≤ N) (hX : (X.card : ℝ) ≤ N) :
    ∃ S : CubePartition, (X : Set (E 3)) ⊆ cubeSet S.root ∧
      (S.regions.card : ℝ) ≤ 19*r ∧
      ∀ R ∈ S.regions, ((pointsIn X (regionSet R)).card : ℝ) ≤ 8*N/r := by
  obtain ⟨Q,hQ⟩ := finite_cloud_containing_cube X
  let μ := N/r
  have hrpos : 0 < r := by linarith
  have hμone : 1 ≤ μ := (le_div_iff₀ hrpos).mpr (by simpa using hrN)
  have hμ : 0 < μ := by linarith
  by_cases hlight : cloudMass X (cubeSet Q) ≤ μ
  · refine ⟨cubeSingletonPartition Q,hQ,?_,?_⟩
    · simp only [cubeSingletonPartition, Finset.card_singleton, Nat.cast_one]
      linarith
    · intro R hR
      have heq : R = Region.cube Q := Finset.mem_singleton.mp hR
      subst R
      change cloudMass X (cubeSet Q) ≤ 8*N/r
      have heq : 8*N/r = 8*μ := by dsimp [μ]; ring
      rw [heq]
      linarith
  · obtain ⟨n,hn⟩ := finite_cloud_light_depth X Q μ hμone
    let F : CubeFragment X μ Q := Classical.choice (cube_fragment_depth X μ hμ n Q (lt_of_not_ge hlight) hn)
    refine ⟨F.complete,by simpa using hQ,?_,?_⟩
    · have hcount := F.final_count hμ
      have hmass : cloudMass X (cubeSet Q) ≤ N := (cloudMass_le_card X _).trans hX
      have hid : r*μ = N := by dsimp [μ]; field_simp
      apply (mul_le_mul_iff_left₀ hμ).mp
      nlinarith
    · intro R hR
      change cloudMass X (regionSet R) ≤ 8*N/r
      have heq : 8*N/r = 8*μ := by dsimp [μ]; ring
      rw [heq]
      exact F.complete_mass hμ.le R hR

/-- Dyadic subdivision and compressed one-child chains, motions.tex:603–650. -/
theorem cube_partition_exists (X : Finset (E 3)) (N r : ℝ)
    (hN : 1 ≤ N) (hr : 1 ≤ r) (hrN : r ≤ N) (hX : (X.card : ℝ) ≤ N) :
    ∃ S : CubePartition, (X : Set (E 3)) ⊆ cubeSet S.root ∧
      (S.regions.card : ℝ) ≤ 19 * r ∧
      ∀ R ∈ S.regions, ((pointsIn X (regionSet R)).card : ℝ) ≤ 8 * N / r := by
  exact cube_partition_construct X N r hN hr hrN hX

/-- mot:thickness, motions.tex:652–673. -/
theorem region_thickness (R : Region) (x : E 3) (hx : x ∈ regionSet R)
    (s : ℝ) (hs : 0 < s) (hside : s ≤ (regionOuter R).side) :
    ∃ A : Set (E 3), MeasurableSet A ∧ A ⊆ regionSet R ∧
      A ⊆ Metric.ball x (Real.sqrt 3 * s) ∧
      ENNReal.ofReal ((s / 4) ^ 3) ≤ MeasureTheory.volume A := by
  cases R with
  | cube Q =>
      obtain ⟨C, hCdesc, hxC, hClower, hCupper⟩ :=
        exists_scale_dyadic_cube Q x hx s hs hside
      have hCroot : cubeSet C ⊆ cubeSet Q := dyadicDescendant_subset_cube Q C hCdesc
      refine ⟨cubeSet C, cubeSet_measurable C, ?_, ?_, ?_⟩
      · simpa [regionSet] using hCroot
      · intro y hy
        have hball := cubeSet_ball C x hxC hy
        have hradius : Real.sqrt 3 * C.side ≤ Real.sqrt 3 * s :=
          mul_le_mul_of_nonneg_left hCupper (Real.sqrt_nonneg 3)
        exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hball) hradius)
      · rw [cubeSet_volume C]
        have hsideLower : s / 4 ≤ C.side := by linarith
        have hpow : (s / 4) ^ 3 ≤ C.side ^ 3 := by gcongr
        conv_rhs => rw [← ENNReal.ofReal_pow C.side_pos.le]
        exact ENNReal.ofReal_le_ofReal hpow
  | punctured Q Q' hpunctured =>
      rcases hpunctured with ⟨hQ'desc, hQ'small⟩
      have hxQ : x ∈ cubeSet Q := hx.1
      have hxNotQ' : x ∉ cubeSet Q' := hx.2
      obtain ⟨C, hCdesc, hxC, hClower, hCupper⟩ :=
        exists_scale_dyadic_cube Q x hxQ s hs hside
      have hCroot : cubeSet C ⊆ cubeSet Q := dyadicDescendant_subset_cube Q C hCdesc
      by_cases hdisj : Disjoint (cubeSet C) (cubeSet Q')
      · refine ⟨cubeSet C, cubeSet_measurable C, ?_, ?_, ?_⟩
        · intro y hy
          refine ⟨hCroot hy, ?_⟩
          intro hyhole
          exact (Set.disjoint_left.mp hdisj) hy hyhole
        · intro y hy
          have hball := cubeSet_ball C x hxC hy
          have hradius : Real.sqrt 3 * C.side ≤ Real.sqrt 3 * s :=
            mul_le_mul_of_nonneg_left hCupper (Real.sqrt_nonneg 3)
          exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hball) hradius)
        · rw [cubeSet_volume C]
          have hsideLower : s / 4 ≤ C.side := by linarith
          have hpow : (s / 4) ^ 3 ≤ C.side ^ 3 := by gcongr
          conv_rhs => rw [← ENNReal.ofReal_pow C.side_pos.le]
          exact ENNReal.ofReal_le_ofReal hpow
      · have hinter : (cubeSet C ∩ cubeSet Q').Nonempty := by
          by_contra h
          have heq : cubeSet C ∩ cubeSet Q' = ∅ := Set.not_nonempty_iff_eq_empty.mp h
          exact hdisj (Set.disjoint_iff_inter_eq_empty.mpr heq)
        have hnot : ¬ C.side ≤ Q'.side := by
          intro hle
          have hnested := dyadic_intersect_subset Q Q' C hQ'desc hCdesc hle
            (by simpa [Set.inter_comm] using hinter)
          exact hxNotQ' (hnested.1 hxC)
        have hsmall : Q'.side < C.side := lt_of_not_ge hnot
        have hnested := dyadic_intersect_subset Q C Q' hCdesc hQ'desc hsmall.le hinter
        have hQ'subC : cubeSet Q' ⊆ cubeSet C := hnested.1
        have hQ'descC : DyadicDescendant Q' C := hnested.2
        rcases hQ'descC with ⟨j, k, hQ'sideC, hQ'cornerC⟩
        have hj : 0 < j := by
          by_contra hj
          have hj0 : j = 0 := Nat.eq_zero_of_not_pos hj
          have heq : Q'.side = C.side := by simpa [hQ'sideC, hj0]
          rw [heq] at hsmall
          exact (lt_irrefl C.side) hsmall
        have hpowLower : (2 : ℝ) ≤ (2 : ℝ) ^ j := by
          calc
            (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
            _ ≤ (2 : ℝ) ^ j := by
              exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < 2)
                (show 1 ≤ j by omega))
        have hQ'sideLower : Q'.side ≤ C.side / 2 := by
          rw [hQ'sideC]
          exact div_le_div_of_nonneg_left C.side_pos.le (by norm_num) hpowLower
        let A : Set (E 3) := cubeSet C \ cubeSet Q'
        have hAvol : MeasureTheory.volume A = ENNReal.ofReal (C.side ^ 3 - Q'.side ^ 3) := by
          have hfinite : MeasureTheory.volume (cubeSet Q') ≠ ⊤ := by
            rw [cubeSet_volume]
            simp
          calc
            MeasureTheory.volume A = MeasureTheory.volume (cubeSet C) -
                MeasureTheory.volume (cubeSet Q') := by
                  dsimp [A]
                  exact MeasureTheory.measure_sdiff hQ'subC
                    (cubeSet_measurable Q').nullMeasurableSet hfinite
            _ = ENNReal.ofReal (C.side ^ 3 - Q'.side ^ 3) := by
              rw [cubeSet_volume, cubeSet_volume, ← ENNReal.ofReal_pow C.side_pos.le,
                ← ENNReal.ofReal_pow Q'.side_pos.le,
                ← ENNReal.ofReal_sub _ (pow_nonneg Q'.side_pos.le 3)]
        refine ⟨A, (cubeSet_measurable C).diff (cubeSet_measurable Q'), ?_, ?_, ?_⟩
        · intro y hy
          exact ⟨hCroot hy.1, hy.2⟩
        · intro y hy
          have hball := cubeSet_ball C x hxC hy.1
          have hradius : Real.sqrt 3 * C.side ≤ Real.sqrt 3 * s :=
            mul_le_mul_of_nonneg_left hCupper (Real.sqrt_nonneg 3)
          exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hball) hradius)
        · rw [hAvol]
          have hcube : (s / 2) ^ 3 < C.side ^ 3 := by gcongr
          have hhole : Q'.side ^ 3 ≤ (C.side / 2) ^ 3 :=
            pow_le_pow_left₀ Q'.side_pos.le hQ'sideLower 3
          have hratio₁ : (s / 2) ^ 3 = s ^ 3 / 8 := by ring
          have hratio₂ : (C.side / 2) ^ 3 = C.side ^ 3 / 8 := by ring
          have hratio₃ : (s / 4) ^ 3 = s ^ 3 / 64 := by ring
          have hreal : (s / 4) ^ 3 ≤ C.side ^ 3 - Q'.side ^ 3 := by
            have hmiddle : (s / 4) ^ 3 < C.side ^ 3 / 8 := by
              have hdiv := div_lt_div_of_pos_right hcube (by norm_num : (0 : ℝ) < 8)
              calc
                (s / 4) ^ 3 = (s / 2) ^ 3 / 8 := by ring
                _ < C.side ^ 3 / 8 := hdiv
            have hhole' : Q'.side ^ 3 ≤ C.side ^ 3 / 8 := by
              calc
                Q'.side ^ 3 ≤ (C.side / 2) ^ 3 := hhole
                _ = C.side ^ 3 / 8 := hratio₂
            have hlast : C.side ^ 3 / 8 ≤ C.side ^ 3 - Q'.side ^ 3 := by
              nlinarith [hhole', pow_nonneg C.side_pos.le 3]
            exact (hmiddle.trans_le hlast).le
          exact ENNReal.ofReal_le_ofReal hreal

private lemma regionSet_subset_outer (R : Region) :
    regionSet R ⊆ cubeSet (regionOuter R) := by
  cases R <;> simp [regionSet, regionOuter]

private lemma ball_box_bound (x : E 3) (s : ℝ) (hs : 0 < s) :
    Metric.ball x (4 * s) ⊆ cubeSet
      ⟨WithLp.toLp 2 (fun i => x i - 4 * s), 8 * s, by positivity⟩ := by
  intro y hy i
  have hcoord : dist (y i) (x i) < 4 * s :=
    (PiLp.dist_apply_le y x i).trans_lt (Metric.mem_ball.mp hy)
  rw [Real.dist_eq] at hcoord
  have habs := abs_lt.mp hcoord
  change x i - 4 * s ≤ y i ∧ y i < x i - 4 * s + 8 * s
  constructor <;> linarith

private lemma region_partner_count (small : Region) (P : CubePartition)
    (h : Motion 3) :
    ((P.regions.filter (fun V =>
      (regionOuter small).side ≤ (regionOuter V).side ∧
      (h '' regionSet small ∩ regionSet V).Nonempty)).card : ℝ) ≤ 32768 := by
  let F := P.regions.filter (fun V =>
    (regionOuter small).side ≤ (regionOuter V).side ∧
    (h '' regionSet small ∩ regionSet V).Nonempty)
  change (F.card : ℝ) ≤ 32768
  have hcenterExists (V : {V // V ∈ F}) :
      ∃ x, x ∈ regionSet V.1 ∧ x ∈ h '' cubeSet (regionOuter small) := by
    have hmem := Finset.mem_filter.mp V.2
    obtain ⟨x, hx⟩ := hmem.2.2
    refine ⟨x, hx.2, ?_⟩
    rcases (Set.mem_image h (regionSet small) x).mp hx.1 with ⟨y, hy, rfl⟩
    exact Set.mem_image_of_mem h (regionSet_subset_outer small hy)
  let center : {V // V ∈ F} → E 3 := fun V => Classical.choose (hcenterExists V)
  have hcenter (V : {V // V ∈ F}) :
      center V ∈ regionSet V.1 ∧ center V ∈ h '' cubeSet (regionOuter small) :=
    Classical.choose_spec (hcenterExists V)
  have hthick (V : {V // V ∈ F}) :
      ∃ A, MeasurableSet A ∧ A ⊆ regionSet V.1 ∧
        A ⊆ Metric.ball (center V) (Real.sqrt 3 * (regionOuter small).side) ∧
        ENNReal.ofReal (((regionOuter small).side / 4) ^ 3) ≤
          MeasureTheory.volume A := by
    have hmem := Finset.mem_filter.mp V.2
    exact region_thickness V.1 (center V) (hcenter V).1
      (regionOuter small).side (regionOuter small).side_pos hmem.2.1
  let chunk : {V // V ∈ F} → Set (E 3) := fun V => Classical.choose (hthick V)
  have hchunk (V : {V // V ∈ F}) :
      MeasurableSet (chunk V) ∧ chunk V ⊆ regionSet V.1 ∧
        chunk V ⊆ Metric.ball (center V) (Real.sqrt 3 * (regionOuter small).side) ∧
        ENNReal.ofReal (((regionOuter small).side / 4) ^ 3) ≤
          MeasureTheory.volume (chunk V) :=
    Classical.choose_spec (hthick V)
  by_cases hF : F = ∅
  · simp [hF]
  · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    let I := F.attach
    let i₀ : {V // V ∈ F} := ⟨hFne.choose, hFne.choose_spec⟩
    obtain ⟨y₀, hy₀, hy₀eq⟩ :=
      (Set.mem_image h (cubeSet (regionOuter small)) (center i₀)).mp (hcenter i₀).2
    let box : Cube :=
      ⟨WithLp.toLp 2 (fun i => center i₀ i - 4 * (regionOuter small).side),
        8 * (regionOuter small).side,
        mul_pos (by norm_num) (regionOuter small).side_pos⟩
    have hboxvol : MeasureTheory.volume (cubeSet box) =
        ENNReal.ofReal ((8 * (regionOuter small).side) ^ 3) := by
      rw [cubeSet_volume]
      simp only [box]
      rw [ENNReal.ofReal_pow
        (mul_nonneg (by norm_num) (regionOuter small).side_pos.le)]
    have hdisj : Set.PairwiseDisjoint (↑I) chunk := by
      intro V hV W hW hVW
      apply Set.disjoint_left.mpr
      intro z hzV hzW
      have hVWval : V.1 ≠ W.1 := by
        intro hEq
        exact hVW (Subtype.ext hEq)
      have hpart := P.disjoint V.1 (Finset.mem_filter.mp V.2).1
        W.1 (Finset.mem_filter.mp W.2).1 hVWval
      exact (Set.disjoint_left.mp hpart) ((hchunk V).2.1 hzV)
        ((hchunk W).2.1 hzW)
    have hmeas : ∀ V ∈ I, MeasurableSet (chunk V) := by
      intro V hV
      exact (hchunk V).1
    have hunionSub : (⋃ V ∈ I, chunk V) ⊆ cubeSet box := by
      intro z hz
      rcases Set.mem_iUnion.mp hz with ⟨V, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨hV, hzV⟩
      obtain ⟨y, hy, hyeq⟩ :=
        (Set.mem_image h (cubeSet (regionOuter small)) (center V)).mp (hcenter V).2
      have hcenterdist : dist (center V) (center i₀) <
          Real.sqrt 3 * (regionOuter small).side := by
        calc
          dist (center V) (center i₀) = dist (h y) (h y₀) := by rw [hyeq, hy₀eq]
          _ = dist y y₀ := h.isometry.dist_eq y y₀
          _ < Real.sqrt 3 * (regionOuter small).side :=
            cubeSet_ball (regionOuter small) y₀ hy₀ hy
      have hzball : z ∈ Metric.ball (center V)
          (Real.sqrt 3 * (regionOuter small).side) := (hchunk V).2.2.1 hzV
      have hzball₀ : z ∈ Metric.ball (center i₀)
          (4 * (regionOuter small).side) := by
        rw [Metric.mem_ball]
        have htri := dist_triangle z (center V) (center i₀)
        have hsmall : Real.sqrt 3 * (regionOuter small).side +
            Real.sqrt 3 * (regionOuter small).side <
              4 * (regionOuter small).side := by
          have hsqr : Real.sqrt 3 < 2 := by
            nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          nlinarith [hsqr, (regionOuter small).side_pos]
        exact lt_of_le_of_lt htri
          (lt_of_lt_of_le (add_lt_add (Metric.mem_ball.mp hzball)
            hcenterdist) hsmall.le)
      have hzbox := ball_box_bound (center i₀) (regionOuter small).side
        (regionOuter small).side_pos hzball₀
      exact hzbox
    have hsum :
        (∑ V ∈ I, ENNReal.ofReal (((regionOuter small).side / 4) ^ 3)) ≤
          ENNReal.ofReal ((8 * (regionOuter small).side) ^ 3) := by
      calc
        _ ≤ ∑ V ∈ I, MeasureTheory.volume (chunk V) :=
          Finset.sum_le_sum fun V hV => (hchunk V).2.2.2
        _ = MeasureTheory.volume (⋃ V ∈ I, chunk V) :=
          (MeasureTheory.measure_biUnion_finset hdisj hmeas).symm
        _ ≤ MeasureTheory.volume (cubeSet box) := MeasureTheory.measure_mono hunionSub
        _ = ENNReal.ofReal ((8 * (regionOuter small).side) ^ 3) := hboxvol
    have hconst :
        (∑ V ∈ I, ENNReal.ofReal (((regionOuter small).side / 4) ^ 3)) =
          ENNReal.ofReal ((I.card : ℝ) * (((regionOuter small).side / 4) ^ 3)) := by
      simp [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_nsmul]
    have hreal := ENNReal.toReal_mono (by simp) hsum
    have hc_nonneg : 0 ≤ (((regionOuter small).side / 4) ^ 3) :=
      pow_nonneg (div_nonneg (regionOuter small).side_pos.le (by norm_num)) 3
    have hbox_nonneg : 0 ≤ (8 * (regionOuter small).side) ^ 3 :=
      pow_nonneg (mul_nonneg (by norm_num) (regionOuter small).side_pos.le) 3
    have hreal' :
        (I.card : ℝ) * (((regionOuter small).side / 4) ^ 3) ≤
          (8 * (regionOuter small).side) ^ 3 := by
      rw [hconst,
        ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hc_nonneg),
        ENNReal.toReal_ofReal hbox_nonneg] at hreal
      exact hreal
    have hratio : (8 * (regionOuter small).side) ^ 3 =
        32768 * (((regionOuter small).side / 4) ^ 3) := by ring
    have hcard : (F.card : ℝ) ≤ 32768 := by
      have hreal'' :
          (F.card : ℝ) * (((regionOuter small).side / 4) ^ 3) ≤
            (8 * (regionOuter small).side) ^ 3 := by
        simpa [I] using hreal'
      nlinarith [hreal'', hratio, pow_pos (regionOuter small).side_pos 3]
    exact hcard

/-- Charging to the smaller outer cube and volume packing, motions.tex:675–692. -/
theorem partition_overlap : ∃ K : ℝ, 0 < K ∧
    ∀ (S T : CubePartition) (r : ℝ), 1 ≤ r →
      (S.regions.card : ℝ) ≤ 19 * r → (T.regions.card : ℝ) ≤ 19 * r →
      ∀ g : Motion 3, (regionOverlap S T g : ℝ) ≤ K * r := by
  refine ⟨1245184, by norm_num, ?_⟩
  intro S T r hr hS hT g
  let all := (S.regions ×ˢ T.regions).filter fun p =>
    (g '' regionSet p.1 ∩ regionSet p.2).Nonempty
  let F₁ := all.filter fun p =>
    (regionOuter p.1).side ≤ (regionOuter p.2).side
  let F₂ := all.filter fun p =>
    (regionOuter p.2).side < (regionOuter p.1).side
  have hsplit : regionOverlap S T g = F₁.card + F₂.card := by
    change all.card = F₁.card + F₂.card
    have hunion : all = F₁ ∪ F₂ := by
      ext p
      by_cases hle : (regionOuter p.1).side ≤ (regionOuter p.2).side
      · simp [all, F₁, F₂, hle, not_lt_of_ge hle]
      · have hgt : (regionOuter p.2).side < (regionOuter p.1).side := lt_of_not_ge hle
        simp [all, F₁, F₂, hle, hgt]
    have hdisj : Disjoint F₁ F₂ := by
      apply Finset.disjoint_left.mpr
      intro p hp₁ hp₂
      have hle := (Finset.mem_filter.mp hp₁).2
      have hlt := (Finset.mem_filter.mp hp₂).2
      exact (not_lt_of_ge hle) hlt
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hF₁ : (F₁.card : ℝ) ≤ 32768 * (S.regions.card : ℝ) := by
    have hmaps : (F₁ : Set (Region × Region)).MapsTo Prod.fst S.regions := by
      intro p hp
      have hpAll := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
      exact (Finset.mem_product.mp hpAll.1).1
    rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    calc
      _ ≤ ∑ R ∈ S.regions, (32768 : ℝ) := by
        apply Finset.sum_le_sum
        intro R hR
        have hfiber :
            (F₁.filter fun p => p.1 = R).card ≤
              (T.regions.filter fun V =>
                (regionOuter R).side ≤ (regionOuter V).side ∧
                  (g '' regionSet R ∩ regionSet V).Nonempty).card := by
          apply Finset.card_le_card_of_injOn Prod.snd
          · intro p hp
            have hp' := Finset.mem_filter.mp hp
            have hpF := Finset.mem_filter.mp hp'.1
            have hpAll := Finset.mem_filter.mp hpF.1
            have hprod := Finset.mem_product.mp hpAll.1
            have hside : (regionOuter R).side ≤ (regionOuter p.2).side := by
              simpa [hp'.2] using hpF.2
            have hoverlap : (g '' regionSet R ∩ regionSet p.2).Nonempty := by
              simpa [hp'.2] using hpAll.2
            exact Finset.mem_filter.mpr ⟨hprod.2, ⟨hside, hoverlap⟩⟩
          · intro p hp q hq heq
            have hp' := (Finset.mem_filter.mp hp).2
            have hq' := (Finset.mem_filter.mp hq).2
            exact Prod.ext (hp'.trans hq'.symm) heq
        have hbound := region_partner_count R T g
        have hcast : ((F₁.filter fun p => p.1 = R).card : ℝ) ≤ 32768 :=
          (Nat.cast_le.mpr hfiber).trans hbound
        exact hcast
      _ = 32768 * (S.regions.card : ℝ) := by simp; ring
  have hF₂ : (F₂.card : ℝ) ≤ 32768 * (T.regions.card : ℝ) := by
    have hmaps : (F₂ : Set (Region × Region)).MapsTo Prod.snd T.regions := by
      intro p hp
      have hpAll := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
      exact (Finset.mem_product.mp hpAll.1).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    calc
      _ ≤ ∑ V ∈ T.regions, (32768 : ℝ) := by
        apply Finset.sum_le_sum
        intro V hV
        have hfiber :
            (F₂.filter fun p => p.2 = V).card ≤
              (S.regions.filter fun R =>
                (regionOuter V).side ≤ (regionOuter R).side ∧
                  (g.symm '' regionSet V ∩ regionSet R).Nonempty).card := by
          apply Finset.card_le_card_of_injOn Prod.fst
          · intro p hp
            have hp' := Finset.mem_filter.mp hp
            have hpF := Finset.mem_filter.mp hp'.1
            have hpAll := Finset.mem_filter.mp hpF.1
            have hprod := Finset.mem_product.mp hpAll.1
            have hlt : (regionOuter V).side < (regionOuter p.1).side := by
              simpa [hp'.2] using hpF.2
            rcases hpAll.2 with ⟨x, ⟨y, hy, hgy⟩, hxV⟩
            have hoverlap :
                (g.symm '' regionSet V ∩ regionSet p.1).Nonempty := by
              refine ⟨y, ?_⟩
              have hxV' : x ∈ regionSet V := by simpa [hp'.2] using hxV
              exact ⟨⟨x, hxV', by
                calc
                  g.symm x = g.symm (g y) := by rw [hgy]
                  _ = y := g.symm_apply_apply y⟩, hy⟩
            exact Finset.mem_filter.mpr ⟨hprod.1, ⟨le_of_lt hlt, hoverlap⟩⟩
          · intro p hp q hq heq
            have hp' := (Finset.mem_filter.mp hp).2
            have hq' := (Finset.mem_filter.mp hq).2
            exact Prod.ext heq (hp'.trans hq'.symm)
        have hbound := region_partner_count V S g.symm
        have hcast : ((F₂.filter fun p => p.2 = V).card : ℝ) ≤ 32768 :=
          (Nat.cast_le.mpr hfiber).trans hbound
        exact hcast
      _ = 32768 * (T.regions.card : ℝ) := by simp; ring
  rw [hsplit, Nat.cast_add]
  nlinarith [hF₁, hF₂, hS, hT]

/-- mot:partition, motions.tex:581–694. -/
theorem mot_partition : ∃ K : ℝ, 0 < K ∧
    ∀ (X : Finset (E 3)) (N r : ℝ), 1 ≤ N → 1 ≤ r → r ≤ N → (X.card : ℝ) ≤ N →
      ∃ S : CubePartition, (X : Set (E 3)) ⊆ cubeSet S.root ∧
        (S.regions.card : ℝ) ≤ 19 * r ∧
        (∀ R ∈ S.regions, ((pointsIn X (regionSet R)).card : ℝ) ≤ 8 * N / r) ∧
        ∀ T : CubePartition, (T.regions.card : ℝ) ≤ 19 * r →
          ∀ g : Motion 3, (regionOverlap S T g : ℝ) ≤ K * r := by
  obtain ⟨K, hKpos, hKoverlap⟩ := partition_overlap
  refine ⟨K, hKpos, ?_⟩
  intro X N r hN hr hrN hX
  obtain ⟨S, hcover, hsize, hmass⟩ :=
    cube_partition_exists X N r hN hr hrN hX
  refine ⟨S, hcover, hsize, hmass, ?_⟩
  intro T hT g
  exact hKoverlap S T r hr hsize hT g

/-- mot:region-discard, motions.tex:547–570. -/
theorem region_discard {α : Type*} (I : Finset α) (w : α → ℝ) (K r b : ℝ)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hb : 0 < b) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hsupport : ((I.filter (fun i => w i ≠ 0)).card : ℝ) ≤ K * r) :
    ∑ i ∈ I.filter (fun i => w i < b), w i ≤ K * r * b := by
  classical
  let L := I.filter (fun i => w i < b)
  let J := L.filter (fun i => w i ≠ 0)
  have hsum : (∑ i ∈ L, w i) = ∑ i ∈ J, w i := by
    simp [L, J, Finset.sum_filter_ne_zero]
  have hJ : J ⊆ I.filter (fun i => w i ≠ 0) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hi'' := Finset.mem_filter.mp hi'.1
    exact Finset.mem_filter.mpr ⟨hi''.1, hi'.2⟩
  have hcard : (J.card : ℝ) ≤ K * r := by
    calc
      (J.card : ℝ) ≤ ((I.filter (fun i => w i ≠ 0)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hJ
      _ ≤ K * r := hsupport
  have hsum_le : (∑ i ∈ J, w i) ≤ (J.card : ℝ) * b := by
    calc
      (∑ i ∈ J, w i) ≤ J.card • b :=
        Finset.sum_le_card_nsmul J w b (fun i hi =>
          (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.le)
      _ = (J.card : ℝ) * b := by simp
  rw [hsum]
  calc
    (∑ i ∈ J, w i) ≤ (J.card : ℝ) * b := hsum_le
    _ ≤ (K * r) * b := by exact mul_le_mul_of_nonneg_right hcard hb.le
    _ = K * r * b := by ring

end DistinctDistances.TrackC
