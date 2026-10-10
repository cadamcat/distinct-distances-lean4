import DistinctDistances.TrackC.Planar
import DistinctDistances.TrackC.CanonicalMotionModel
import DistinctDistances.TrackC.AxisFrame
import DistinctDistances.TrackC.CanonicalPhysical
import DistinctDistances.TrackC.NormalPlaneUniqueness
import DistinctDistances.TrackC.MotionRotationTransport
import DistinctDistances.TrackC.NormalizedMotionFamily
import DistinctDistances.TrackC.NullFlatCalculus
import DistinctDistances.TrackC.DualArrangementConstruction
import DistinctDistances.TrackC.ArrangementCounting
import DistinctDistances.TrackC.ModelDirectionTransverse
import DistinctDistances.TrackC.FiniteSpatialRotation
import DistinctDistances.TrackC.MCBeckAux

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- mot:beck, motions.tex:74–121. -/
theorem mot_beck : ∃ δ γ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < γ ∧
    ∀ (d : ℕ) (X : Finset (E d)), 2 ≤ X.card → cloudLineCap X (δ * X.card) →
      FiniteCardBound (spannedLines X) ((X.card : ℝ) ^ 2) ∧
      γ * (X.card : ℝ) ^ 2 ≤ (spannedLines X).ncard ∧
      γ * X.card ≤ (anchors X γ).card := by
  obtain ⟨C, hC, hRich⟩ := ci_st_rich
  obtain ⟨K, hK⟩ := exists_nat_gt (16*(C+1))
  have hKpos : (0 : ℝ) < K := by linarith
  refine ⟨1/(16*(C+1)), 1/(8*(K : ℝ)^2), by positivity, ?_, by positivity, ?_⟩
  · apply (div_lt_one (by positivity : (0 : ℝ) < 16*(C+1))).mpr
    linarith
  · intro d X hn hcap
    have hR (k : ℕ) (hk : 2 ≤ k) :
        FiniteCardBound {l : Line d | k ≤ (X.filter (fun x => x ∈ l.1)).card}
          (C*((X.card : ℝ)^2/(k : ℝ)^3+(X.card : ℝ)/k)) := by
      have heq : {l : Line d | k ≤ (X.filter (fun x => x ∈ l.1)).card} =
          richLines X (k : ℝ) := by
        ext l
        simp [richLines, pointsOn]
      rw [heq]
      exact (hRich d X ∅ k hk).2
    have heq : {l : Line d | 2 ≤ (X.filter (fun x => x ∈ l.1)).card} =
        spannedLines X := by
      ext l
      simp [spannedLines, richLines, pointsOn]
    have hh := beck_of_rich C K hC hK.le X (fun (x : E d) (l : Line d) => x ∈ l.1) hn
      (fun x y hxy => beck_affine_pair x y hxy) hcap hR
    simpa only [heq, anchors] using hh

/-- Projective-plane Beck for direction sets, motions.tex:120–121, 437–443. -/
theorem mot_beck_projective : ∃ δ γ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < γ ∧
    ∀ X : Finset (PFlat ℝ 3 1), 2 ≤ X.card →
      (∀ l : PFlat ℝ 3 2, ((X.filter (fun x => x.1 ≤ l.1)).card : ℝ) ≤ δ * X.card) →
      let S : Set (PFlat ℝ 3 2) := {l | 2 ≤ (X.filter (fun x => x.1 ≤ l.1)).card}
      S.Finite ∧ γ * (X.card : ℝ) ^ 2 ≤ S.ncard ∧
        γ * X.card ≤ ((X.filter (fun x => γ * X.card ≤
          ({l : PFlat ℝ 3 2 | l ∈ S ∧ x.1 ≤ l.1}.ncard : ℝ))).card : ℝ) := by
  obtain ⟨C, hC, hRich⟩ := ci_st_rich_projective
  obtain ⟨K, hK⟩ := exists_nat_gt (16*(C+1))
  have hKpos : (0 : ℝ) < K := by linarith
  refine ⟨1/(16*(C+1)), 1/(8*(K : ℝ)^2), by positivity, ?_, by positivity, ?_⟩
  · apply (div_lt_one (by positivity : (0 : ℝ) < 16*(C+1))).mpr
    linarith
  · intro X hn hcap
    have hR (k : ℕ) (hk : 2 ≤ k) :
        FiniteCardBound {l : PFlat ℝ 3 2 | k ≤ (X.filter (fun x => x.1 ≤ l.1)).card}
          (C*((X.card : ℝ)^2/(k : ℝ)^3+(X.card : ℝ)/k)) :=
      (hRich 2 X ∅ k hk).2
    have hh := beck_of_rich C K hC hK.le X
      (fun (x : PFlat ℝ 3 1) (l : PFlat ℝ 3 2) => x.1 ≤ l.1) hn
      (fun x y hxy => beck_projective_pair x y hxy) hcap hR
    exact ⟨hh.1.1, hh.2⟩

/-- Cauchy--Schwarz plane-pair lower bound, motions.tex:169–179. -/
theorem plane_pair_lower (X : Finset (E 3)) (P : Finset (Plane 3)) (m K : ℝ)
    (hm : 0 < m) (hX : (X.card : ℝ) ≤ m) (hK : 0 < K)
    (hP : ∀ H ∈ P, K ≤ (pointsOn X H).card ∧ (pointsOn X H).card < 2 * K) :
    K ^ 2 * (P.card : ℝ) ^ 2 / m - 2 * K * P.card ≤ planePairEnergy X P := by
  classical
  let r : E 3 → ℕ := fun x => (P.filter (fun H => x ∈ H.1)).card
  have hinc : (∑ H ∈ P, (pointsOn X H).card) = ∑ x ∈ X, r x := by
    simp only [pointsOn, r, Finset.card_filter]
    rw [Finset.sum_comm]
  have hpair (x : E 3) :
      ((P.offDiag).filter (fun ab => x ∈ ab.1.1 ∧ x ∈ ab.2.1)).card =
        r x * (r x - 1) := by
    have hfilter :
        (P.offDiag).filter (fun ab => x ∈ ab.1.1 ∧ x ∈ ab.2.1) =
          (P.filter (fun H => x ∈ H.1)).offDiag := by
      ext ab
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      aesop
    rw [hfilter, Finset.offDiag_card]
    have hn (n : ℕ) : n * n - n = n * (n - 1) := by
      cases n with
      | zero => simp
      | succ n => simp [Nat.succ_mul, Nat.mul_succ]
    simpa [r] using hn (P.filter (fun H => x ∈ H.1)).card
  have henergy : planePairEnergy X P = ∑ x ∈ X, r x * (r x - 1) := by
    simp only [planePairEnergy, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    simpa only [Finset.card_filter] using hpair x
  have hincR : (∑ H ∈ P, ((pointsOn X H).card : ℝ)) = ∑ x ∈ X, (r x : ℝ) := by
    exact_mod_cast hinc
  have hsumlo : K * P.card ≤ ∑ x ∈ X, (r x : ℝ) := by
    have hterm : ∀ H ∈ P, K ≤ (pointsOn X H).card := fun H hH => (hP H hH).1
    calc
      K * P.card = ∑ H ∈ P, K := by simp [mul_comm]
      _ ≤ ∑ H ∈ P, ((pointsOn X H).card : ℝ) := by
        exact Finset.sum_le_sum fun H hH => hterm H hH
      _ = _ := hincR
  have hsumhi : (∑ x ∈ X, (r x : ℝ)) ≤ 2 * K * P.card := by
    have hterm : ∀ H ∈ P, ((pointsOn X H).card : ℝ) ≤ 2 * K := fun H hH => (hP H hH).2.le
    calc
      ∑ x ∈ X, (r x : ℝ) = ∑ H ∈ P, ((pointsOn X H).card : ℝ) := hincR.symm
      _ ≤ ∑ H ∈ P, (2 * K : ℝ) :=
        Finset.sum_le_sum hterm
      _ = 2 * K * P.card := by simp [mul_assoc, mul_left_comm, mul_comm]
  have hcs : (∑ x ∈ X, (r x : ℝ)) ^ 2 ≤ (X.card : ℝ) * ∑ x ∈ X, (r x : ℝ) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := X) (f := fun x => (r x : ℝ)))
  by_cases hP0 : P = ∅
  · simp [hP0, planePairEnergy]
  have hXne : X.Nonempty := by
    by_contra h
    have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨H, hH⟩ := Finset.nonempty_iff_ne_empty.mpr hP0
    have hcontra := (hP H hH).1
    simp [hXe, pointsOn] at hcontra
    linarith
  have hXpos : 0 < (X.card : ℝ) := Nat.cast_pos.mpr hXne.card_pos
  have hsqlo : K ^ 2 * (P.card : ℝ) ^ 2 / m ≤ ∑ x ∈ X, (r x : ℝ) ^ 2 := by
    have hsumlo' : K * P.card ≤ ∑ x ∈ X, (r x : ℝ) := hsumlo
    have hprod : (K * P.card : ℝ) ^ 2 ≤ (∑ x ∈ X, (r x : ℝ)) ^ 2 := by
      nlinarith
    have hsq := hcs
    have hmul : (K * P.card : ℝ) ^ 2 ≤ (X.card : ℝ) * ∑ x ∈ X, (r x : ℝ) ^ 2 := hprod.trans hsq
    have hle : (X.card : ℝ) * ∑ x ∈ X, (r x : ℝ) ^ 2 ≤ m * ∑ x ∈ X, (r x : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hX (Finset.sum_nonneg fun x hx => sq_nonneg _)
    rw [div_le_iff₀ hm]
    nlinarith [hmul, hle]
  have hsqsub : (∑ x ∈ X, (r x : ℝ)) ≤ 2 * K * P.card := hsumhi
  have henergy' : (planePairEnergy X P : ℝ) =
      (∑ x ∈ X, (r x : ℝ) ^ 2) - ∑ x ∈ X, (r x : ℝ) := by
    rw [henergy]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    cases hrx : r x with
    | zero => simp [hrx]
    | succ n => simp [hrx]; ring
  rw [henergy']
  nlinarith

private theorem plane_intersection_is_line (H H' : Plane 3) (hne : H ≠ H')
    (hinter : ((H.1 : Set (E 3)) ∩ (H'.1 : Set (E 3))).Nonempty) :
    ∃ l : Line 3, (l.1 : Set (E 3)) = (H.1 : Set (E 3)) ∩ (H'.1 : Set (E 3)) := by
  rcases hinter with ⟨x, hx⟩
  have hxH : x ∈ H.1 := hx.1
  have hxH' : x ∈ H'.1 := hx.2
  let V : Submodule ℝ (E 3) := H.1.direction
  let W : Submodule ℝ (E 3) := H'.1.direction
  let I : AffineSubspace ℝ (E 3) := H.1 ⊓ H'.1
  have hdir : I.direction = (V ⊓ W : Submodule ℝ (E 3)) := by
    exact AffineSubspace.direction_inf_of_mem hxH hxH'
  have hHdim : Module.finrank ℝ V = 2 := H.2.2
  have hH'dim : Module.finrank ℝ W = 2 := H'.2.2
  have hsup : Module.finrank ℝ (V ⊔ W : Submodule ℝ (E 3)) ≤ 3 := by
    calc
      Module.finrank ℝ (V ⊔ W : Submodule ℝ (E 3)) ≤
          Module.finrank ℝ (⊤ : Submodule ℝ (E 3)) := Submodule.finrank_mono le_top
      _ = 3 := by simp [E]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V W
  rw [hHdim, hH'dim] at hsum
  have hIlo : 1 ≤ Module.finrank ℝ I.direction := by
    rw [hdir]
    omega
  have hIhi : Module.finrank ℝ I.direction ≤ 1 := by
    by_contra hnot
    have hIge2 : 2 ≤ Module.finrank ℝ I.direction := by omega
    have hIeq2 : Module.finrank ℝ (V ⊓ W : Submodule ℝ (E 3)) = 2 := by
      apply le_antisymm
      · exact le_trans (Submodule.finrank_mono inf_le_left) (by rw [hHdim])
      · rw [← hdir]
        exact hIge2
    have hsubeqH : (V ⊓ W : Submodule ℝ (E 3)) = V :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hIeq2, hHdim])
    have hsubeqH' : (V ⊓ W : Submodule ℝ (E 3)) = W :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hIeq2, hH'dim])
    have hdirs : H.1.direction = H'.1.direction := by
      change V = W
      exact hsubeqH.symm.trans hsubeqH'
    have hplanes : H.1 = H'.1 :=
      (AffineSubspace.eq_iff_direction_eq_of_mem hxH hxH').2 hdirs
    exact hne (Subtype.ext hplanes)
  have hIdim : Module.finrank ℝ I.direction = 1 := by omega
  refine ⟨⟨I, ⟨?_, hIdim⟩⟩, ?_⟩
  · exact ⟨x, (AffineSubspace.mem_inf_iff x H.1 H'.1).2 ⟨hxH, hxH'⟩⟩
  · change (I : Set (E 3)) = (H.1 : Set (E 3)) ∩ (H'.1 : Set (E 3))
    exact AffineSubspace.coe_inf H.1 H'.1

private theorem plane_meet_eq_common_line (H H' : Plane 3) (hne : H ≠ H')
    (l : Line 3) (hl : l.1 ≤ H.1) (hl' : l.1 ≤ H'.1) :
    H.1 ⊓ H'.1 = l.1 := by
  classical
  obtain ⟨x, hx⟩ := l.2.1
  obtain ⟨j, hj⟩ := plane_intersection_is_line H H' hne
    ⟨x, hl hx, hl' hx⟩
  have hj' : j.1 = H.1 ⊓ H'.1 := by
    apply SetLike.coe_injective
    simpa only [AffineSubspace.coe_inf] using hj
  have hsub : l.1 ≤ H.1 ⊓ H'.1 := by
    intro y hy
    exact AffineSubspace.mem_inf_iff y H.1 H'.1 |>.2 ⟨hl hy, hl' hy⟩
  have hdim : Module.finrank ℝ (H.1 ⊓ H'.1).direction = 1 := by
    rw [← hj']
    exact j.2.2
  have hdirs : l.1.direction = (H.1 ⊓ H'.1).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hsub)
      (by rw [l.2.2, hdim])
  exact (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirs l.2.1 hsub).symm

private theorem plane_line_fiber_card_bound (X : Finset (E 3))
    (P : Finset (Plane 3)) (l : Line 3) (m K : ℝ) (hK : 0 < K)
    (hXm : (X.card : ℝ) ≤ m)
    (hbucket : ∀ H ∈ P, K ≤ (pointsOn X H).card ∧ (pointsOn X H).card < 2 * K ∧
      ∀ l' : Line 3, l'.1 ≤ H.1 →
        ((pointsOn X l').card : ℝ) < ((pointsOn X H).card : ℝ) / 2) :
    ((P.filter (fun H => l.1 ≤ H.1)).card : ℝ) ≤ 2 * m / K := by
  classical
  let F : Finset (Plane 3) := P.filter (fun H => l.1 ≤ H.1)
  let off (H : Plane 3) : Finset (E 3) :=
    (pointsOn X H).filter (fun x => x ∉ (l.1 : Set (E 3)))
  have hoffsub (H : Plane 3) : off H ⊆ X := by
    intro x hx
    exact Finset.mem_filter.mp (Finset.mem_filter.mp hx).1 |>.1
  have hofflower (H : Plane 3) (hH : H ∈ F) :
      K / 2 ≤ ((off H).card : ℝ) := by
    have hplane := hbucket H (Finset.mem_filter.mp hH).1
    have hlineSub : pointsOn X l ⊆ pointsOn X H := by
      intro x hx
      simp only [pointsOn, Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, (Finset.mem_filter.mp hH).2 hx.2⟩
    have hlineFilter : (pointsOn X H).filter (fun x => x ∈ (l.1 : Set (E 3))) =
        pointsOn X l := by
      ext x
      simp only [pointsOn, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hxX, hxH⟩, hxl⟩
        exact ⟨hxX, hxl⟩
      · intro hx
        exact ⟨⟨hx.1, (Finset.mem_filter.mp hH).2 hx.2⟩, hx.2⟩
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := pointsOn X H) (fun x => x ∈ (l.1 : Set (E 3)))
    have hpartition' :
        (pointsOn X l).card + (off H).card = (pointsOn X H).card := by
      dsimp [off]
      rw [← hlineFilter]
      exact hpartition
    have hcap := hplane.2.2 l (Finset.mem_filter.mp hH).2
    have hplaneLower : K ≤ ((pointsOn X H).card : ℝ) := by exact_mod_cast hplane.1
    have hpartitionR : ((pointsOn X l).card : ℝ) + ((off H).card : ℝ) =
        ((pointsOn X H).card : ℝ) := by exact_mod_cast hpartition'
    nlinarith
  have hdisjoint : (F : Set (Plane 3)).PairwiseDisjoint off := by
    intro H hH H' hH' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hxH : x ∈ H.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hxH' : x ∈ H'.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx').1).2
    have hmeet := plane_meet_eq_common_line H H' hne l
      (Finset.mem_filter.mp hH).2 (Finset.mem_filter.mp hH').2
    have hxmeet : x ∈ H.1 ⊓ H'.1 :=
      (AffineSubspace.mem_inf_iff x H.1 H'.1).2 ⟨hxH, hxH'⟩
    have hxl : x ∈ l.1 := by rw [← hmeet]; exact hxmeet
    exact (Finset.mem_filter.mp hx).2 hxl
  let U : Finset (E 3) := F.biUnion off
  have hUsub : U ⊆ X := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨H, hH, hxH⟩
    exact hoffsub H hxH
  have hsum : (∑ H ∈ F, ((off H).card : ℝ)) ≤ m := by
    calc
      ∑ H ∈ F, ((off H).card : ℝ) = (U.card : ℝ) := by
        rw [Finset.card_biUnion hdisjoint]
        norm_cast
      _ ≤ (X.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hUsub)
      _ ≤ m := hXm
  have hprod : (F.card : ℝ) * (K / 2) ≤ m := by
    calc
      (F.card : ℝ) * (K / 2) = ∑ H ∈ F, (K / 2) := by simp [mul_comm]
      _ ≤ ∑ H ∈ F, ((off H).card : ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        exact hofflower H hH
      _ ≤ m := hsum
  apply (le_div_iff₀ hK).2
  nlinarith

private theorem st_rpow_scale (K A n L : ℝ) (hK : 1 ≤ K) (hA : 1 ≤ A)
    (hn0 : 0 ≤ n) (hn : n ≤ 2 * K) (hL0 : 0 ≤ L)
    (hL : L ≤ A * Real.sqrt K) :
    n ^ ((2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) + n + L ≤ (2 * A + 2 + A) * K := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hspos : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
  have hs2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt hKpos.le
  have hsle : Real.sqrt K ≤ K := by nlinarith [hs2]
  have hnPow : n ^ ((2 : ℝ) / 3) ≤ (2 * K) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow hn0 hn (by norm_num)
  have hLPow : L ^ ((2 : ℝ) / 3) ≤
      (A * Real.sqrt K) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow hL0 hL (by norm_num)
  have hscale : (2 * K) ^ ((2 : ℝ) / 3) *
      (A * Real.sqrt K) ^ ((2 : ℝ) / 3) ≤ 2 * A * K := by
    have hcoeff : (2 * A) ^ ((2 : ℝ) / 3) ≤ 2 * A := by
      have h := Real.rpow_le_rpow_of_exponent_le (x := 2 * A)
        (by nlinarith [hA]) (y := (2 : ℝ) / 3) (z := 1) (by norm_num)
      simpa only [Real.rpow_one] using h
    have hKtimes : K * Real.sqrt K = Real.sqrt K ^ 3 := by
      calc
        K * Real.sqrt K = Real.sqrt K ^ 2 * Real.sqrt K := by rw [hs2]
        _ = Real.sqrt K ^ 3 := by ring
    have hrootpow : (Real.sqrt K ^ 3) ^ ((2 : ℝ) / 3) = Real.sqrt K ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hspos)]
      norm_num
    have hpowEq : (2 * K) ^ ((2 : ℝ) / 3) *
        (A * Real.sqrt K) ^ ((2 : ℝ) / 3) =
        (2 * A) ^ ((2 : ℝ) / 3) * K := by
      calc
        _ = (2 ^ ((2 : ℝ) / 3) * K ^ ((2 : ℝ) / 3)) *
            (A ^ ((2 : ℝ) / 3) * Real.sqrt K ^ ((2 : ℝ) / 3)) := by
          rw [Real.mul_rpow (by norm_num) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
        _ = (2 ^ ((2 : ℝ) / 3) * A ^ ((2 : ℝ) / 3)) *
            (K ^ ((2 : ℝ) / 3) * Real.sqrt K ^ ((2 : ℝ) / 3)) := by ring
        _ = (2 * A) ^ ((2 : ℝ) / 3) * (K * Real.sqrt K) ^ ((2 : ℝ) / 3) := by
          rw [← Real.mul_rpow (by norm_num) (by positivity),
            ← Real.mul_rpow (by positivity) (by positivity)]
        _ = (2 * A) ^ ((2 : ℝ) / 3) * (Real.sqrt K ^ 3) ^ ((2 : ℝ) / 3) := by
          rw [hKtimes]
        _ = (2 * A) ^ ((2 : ℝ) / 3) * K := by
          rw [hrootpow, hs2]
    rw [hpowEq]
    exact mul_le_mul_of_nonneg_right hcoeff hKpos.le
  have hprod : n ^ ((2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) ≤ 2 * A * K :=
    (mul_le_mul hnPow hLPow (Real.rpow_nonneg hL0 _) (by positivity)).trans hscale
  calc
    n ^ ((2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) + n + L ≤
        2 * A * K + 2 * K + A * Real.sqrt K := by nlinarith [hprod, hn, hL]
    _ ≤ (2 * A + 2 + A) * K := by nlinarith [hsle, hA]

private theorem rich_line_sqrt_bound (C K n : ℝ) (hC : 0 < C) (hK : 1 ≤ K)
    (hn0 : 0 ≤ n) (hn : n ≤ 2 * K) (k : ℕ) (hk : Real.sqrt K ≤ (k : ℝ)) :
    C * (n ^ 2 / (k : ℝ) ^ 3 + n / (k : ℝ)) ≤ 6 * C * Real.sqrt K := by
  have hspos : 0 < Real.sqrt K := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hK)
  have hs2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith : 0 ≤ K)
  have hkpos : 0 < (k : ℝ) := lt_of_lt_of_le hspos hk
  have hk3 : Real.sqrt K ^ 3 ≤ (k : ℝ) ^ 3 := by gcongr
  have hnum : n ^ 2 ≤ 4 * (Real.sqrt K) ^ 4 := by
    have hKsq : K = Real.sqrt K ^ 2 := hs2.symm
    nlinarith [hn0, hn]
  have hfirst : n ^ 2 / (k : ℝ) ^ 3 ≤ 4 * Real.sqrt K := by
    rw [div_le_iff₀ (by positivity : 0 < (k : ℝ) ^ 3)]
    calc
      n ^ 2 ≤ 4 * Real.sqrt K ^ 4 := hnum
      _ = 4 * Real.sqrt K * Real.sqrt K ^ 3 := by ring
      _ ≤ 4 * Real.sqrt K * (k : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hk3 (by positivity)
  have hsecond : n / (k : ℝ) ≤ 2 * Real.sqrt K := by
    rw [div_le_iff₀ hkpos]
    have hKsqrt : K = Real.sqrt K ^ 2 := hs2.symm
    nlinarith [hn]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC.le]

private theorem finset_sum_const_real {α : Type*} (s : Finset α) (c : ℝ) :
    (∑ _ ∈ s, c) = (s.card : ℝ) * c := by
  simp [mul_comm]

private noncomputable def planePairPoints (X : Finset (E 3)) (H H' : Plane 3) : Finset (E 3) :=
  (pointsOn X H).filter (fun x => x ∈ H'.1)

private theorem planePairEnergy_sum_filter (X : Finset (E 3)) (P : Finset (Plane 3)) :
    (planePairEnergy X P : ℝ) =
      ∑ H ∈ P, ∑ H' ∈ P,
        if H ≠ H' then ((planePairPoints X H H').card : ℝ) else 0 := by
  classical
  have hoff : P.offDiag = (P ×ˢ P).filter (fun ab => ab.1 ≠ ab.2) := by
    ext ab
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨ha, hb, hab⟩
      exact ⟨⟨ha, hb⟩, hab⟩
    · rintro ⟨⟨ha, hb⟩, hab⟩
      exact ⟨ha, hb, hab⟩
  simp only [planePairEnergy]
  rw [hoff, Finset.sum_filter]
  push_cast
  rw [Finset.sum_product]
  simp [planePairPoints, pointsOn, Finset.filter_filter, and_assoc, and_left_comm, and_comm]

set_option maxHeartbeats 4000000 in
private theorem plane_pair_fixed_upper
    (Cr Cs : ℝ) (hCr : 0 < Cr) (hCs : 0 < Cs)
    (X : Finset (E 3)) (P : Finset (Plane 3)) (H : Plane 3) (m K : ℝ)
    (hK : 1 ≤ K) (hXm : (X.card : ℝ) ≤ m) (hHmem : H ∈ P)
    (hbucket : ∀ H ∈ P, K ≤ (pointsOn X H).card ∧ (pointsOn X H).card < 2 * K ∧
      ∀ l : Line 3, l.1 ≤ H.1 →
        ((pointsOn X l).card : ℝ) < ((pointsOn X H).card : ℝ) / 2)
    (hRich : ∀ L : Finset (Line 3), ∀ k : ℕ, 2 ≤ k →
      FiniteCardBound (richLines (pointsOn X H) k)
        (Cr * (((pointsOn X H).card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
          ((pointsOn X H).card : ℝ) / k)))
    (hST : ∀ L : Finset (Line 3), (incidences (pointsOn X H) L : ℝ) ≤ Cs *
      (((pointsOn X H).card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
        (pointsOn X H).card + L.card)) :
    (∑ H' ∈ P, if H ≠ H' then ((planePairPoints X H H').card : ℝ) else 0) ≤
      2 * Real.sqrt K * P.card +
        2 * (Cs * (3 * (6 * Cr + 1) + 2)) * m := by
  classical
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hmnonneg : 0 ≤ m := le_trans (Nat.cast_nonneg X.card) hXm
  have hspos : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
  let I0 : Finset (Plane 3) := P.filter
    (fun H' => H ≠ H' ∧ (planePairPoints X H H').Nonempty)
  let Q := {H' : Plane 3 // H' ∈ I0}
  let I : Finset Q := I0.attach
  have hlineEx (q : Q) :
      ∃ l : Line 3, (l.1 : Set (E 3)) = (H.1 : Set (E 3)) ∩ (q.1.1 : Set (E 3)) := by
    rcases Finset.mem_filter.mp q.2 with ⟨_, hneq, hnonempty⟩
    rcases hnonempty with ⟨x, hx⟩
    have hx' : x ∈ X ∧ x ∈ H.1 ∧ x ∈ q.1.1 := by
      simpa [planePairPoints, pointsOn, Finset.filter_filter, and_assoc, and_left_comm,
        and_comm] using hx
    exact plane_intersection_is_line H q.1 hneq ⟨x, hx'.2.1, hx'.2.2⟩
  let lineOf : Q → Line 3 := fun q => Classical.choose (hlineEx q)
  have hlineSpec (q : Q) :
      (lineOf q : Set (E 3)) = (H.1 : Set (E 3)) ∩ (q.1.1 : Set (E 3)) := by
    simpa using Classical.choose_spec (hlineEx q)
  have hlineMem (q : Q) (x : E 3) :
      x ∈ (lineOf q : Set (E 3)) ↔ x ∈ H.1 ∧ x ∈ q.1.1 := by
    have heq := congrArg (fun s : Set (E 3) => x ∈ s) (hlineSpec q)
    rw [heq]
    exact Set.mem_inter_iff x _ _
  have hlineInside (q : Q) : (lineOf q).1 ≤ H.1 := by
    intro x hx
    exact (hlineMem q x).mp hx |>.1
  have hlineInsidePlane (q : Q) : (lineOf q).1 ≤ q.1.1 := by
    intro x hx
    exact (hlineMem q x).mp hx |>.2
  have hpairLineEq (q : Q) :
      planePairPoints X H q.1 = pointsOn X (lineOf q) := by
    ext x
    simp only [planePairPoints, pointsOn, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxX, hxH⟩, hxH'⟩
      refine ⟨hxX, ?_⟩
      exact (hlineMem q x).mpr ⟨hxH, hxH'⟩
    · rintro ⟨hxX, hxl⟩
      have hxmeet := (hlineMem q x).mp hxl
      exact ⟨⟨hxX, hxmeet.1⟩, hxmeet.2⟩
  have hlinePointsEq (q : Q) :
      pointsOn X (lineOf q) = pointsOn (pointsOn X H) (lineOf q) := by
    ext x
    simp only [pointsOn, Finset.mem_filter]
    constructor
    · rintro ⟨hxX, hxl⟩
      exact ⟨⟨hxX, hlineInside q hxl⟩, hxl⟩
    · rintro ⟨⟨hxX, hxH⟩, hxl⟩
      exact ⟨hxX, hxl⟩
  let LheavyQ : Finset Q := I.filter
    (fun q => 2 * Real.sqrt K ≤ ((pointsOn X (lineOf q)).card : ℝ))
  let Lheavy : Finset (Line 3) := LheavyQ.image lineOf
  let LlowQ : Finset Q := I.filter
    (fun q => ((pointsOn X (lineOf q)).card : ℝ) < 2 * Real.sqrt K)
  have hLheavyMap : ∀ q ∈ LheavyQ, lineOf q ∈ Lheavy :=
    fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hLheavySubset : ∀ l ∈ Lheavy,
      l ∈ richLines (pointsOn X H) (Nat.floor (2 * Real.sqrt K)) := by
    intro l hl
    rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
    change (Nat.floor (2 * Real.sqrt K) : ℝ) ≤
      ((pointsOn (pointsOn X H) (lineOf q)).card : ℝ)
    rw [← hlinePointsEq q]
    exact le_trans (Nat.floor_le (by positivity)) (Finset.mem_filter.mp hq).2
  have hLheavyBound : (Lheavy.card : ℝ) ≤ (6 * Cr + 1) * Real.sqrt K := by
    have hKroot : 1 ≤ Real.sqrt K := by nlinarith [Real.sq_sqrt hKpos.le]
    have hk2 : 2 ≤ Nat.floor (2 * Real.sqrt K) := by
      have hfloor := Nat.floor_mono (show (2 : ℝ) ≤ 2 * Real.sqrt K by nlinarith)
      simpa using hfloor
    obtain ⟨hRichFin, hRichCount⟩ := hRich Lheavy (Nat.floor (2 * Real.sqrt K)) hk2
    have hcardSubset : Lheavy.card ≤ hRichFin.toFinset.card :=
      Finset.card_le_card (by
        intro l hl
        exact (hRichFin.mem_toFinset).mpr (hLheavySubset l hl))
    have hRichCount' :
        (hRichFin.toFinset.card : ℝ) ≤ Cr *
          (((pointsOn X H).card : ℝ) ^ 2 /
            (Nat.floor (2 * Real.sqrt K) : ℝ) ^ 3 +
            ((pointsOn X H).card : ℝ) / Nat.floor (2 * Real.sqrt K)) := by
      simpa [Set.ncard_eq_toFinset_card (richLines (pointsOn X H)
        (Nat.floor (2 * Real.sqrt K))) hRichFin] using hRichCount
    have hN : ((pointsOn X H).card : ℝ) ≤ 2 * K := (hbucket H hHmem).2.1.le
    have hNnonneg : 0 ≤ ((pointsOn X H).card : ℝ) := Nat.cast_nonneg _
    have hkLower : Real.sqrt K ≤ (Nat.floor (2 * Real.sqrt K) : ℝ) := by
      have hf := Nat.lt_floor_add_one (2 * Real.sqrt K)
      have hs : 1 ≤ Real.sqrt K := hKroot
      nlinarith
    have hsmall := rich_line_sqrt_bound Cr K ((pointsOn X H).card : ℝ) hCr hK
      hNnonneg hN (Nat.floor (2 * Real.sqrt K)) hkLower
    calc
      (Lheavy.card : ℝ) ≤ (hRichFin.toFinset.card : ℝ) := Nat.cast_le.mpr hcardSubset
      _ ≤ 6 * Cr * Real.sqrt K := le_trans hRichCount' hsmall
      _ ≤ (6 * Cr + 1) * Real.sqrt K := by nlinarith [hspos]
  let A : ℝ := 6 * Cr + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hNnonneg : 0 ≤ ((pointsOn X H).card : ℝ) := Nat.cast_nonneg _
  have hNbound : ((pointsOn X H).card : ℝ) ≤ 2 * K := (hbucket H hHmem).2.1.le
  have hLnonneg : 0 ≤ (Lheavy.card : ℝ) := Nat.cast_nonneg _
  have hSTbound : (incidences (pointsOn X H) Lheavy : ℝ) ≤
      (Cs * (3 * A + 2)) * K := by
    have hST' := hST Lheavy
    have hscale := st_rpow_scale K A ((pointsOn X H).card : ℝ)
      (Lheavy.card : ℝ) hK hA hNnonneg hNbound hLnonneg hLheavyBound
    calc
      (incidences (pointsOn X H) Lheavy : ℝ) ≤ Cs *
          (((pointsOn X H).card : ℝ) ^ ((2 : ℝ) / 3) *
            (Lheavy.card : ℝ) ^ ((2 : ℝ) / 3) +
            (pointsOn X H).card + Lheavy.card) := hST'
      _ ≤ Cs * ((2 * A + 2 + A) * K) :=
        mul_le_mul_of_nonneg_left hscale hCs.le
      _ = (Cs * (3 * A + 2)) * K := by ring
  have hincSum : (incidences (pointsOn X H) Lheavy : ℝ) =
      ∑ l ∈ Lheavy, ((pointsOn (pointsOn X H) l).card : ℝ) := by
    have hn : incidences (pointsOn X H) Lheavy =
        ∑ l ∈ Lheavy, (pointsOn (pointsOn X H) l).card := by
      simp only [incidences, lineMultiplicity, pointsOn, Finset.card_filter]
      rw [Finset.sum_comm]
    exact_mod_cast hn
  have hfiber (l : Line 3) (hl : l ∈ Lheavy) :
      ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) ≤ 2 * m / K := by
    let Fq := LheavyQ.filter (fun q => lineOf q = l)
    let Fplane := P.filter (fun H' => l.1 ≤ H'.1)
    let imagePlanes := Fq.image (fun q : Q => q.1)
    have hvalinj : Function.Injective (fun q : Q => q.1) := Subtype.val_injective
    have hcardImage : imagePlanes.card = Fq.card := by
      dsimp [imagePlanes]
      exact Finset.card_image_of_injective _ hvalinj
    have himageSub : imagePlanes ⊆ Fplane := by
      intro H' hH'
      rcases Finset.mem_image.mp hH' with ⟨q, hq, rfl⟩
      have hqI := q.2
      have hmem := Finset.mem_filter.mp hqI
      refine Finset.mem_filter.mpr ⟨hmem.1, ?_⟩
      have hlineEq := (Finset.mem_filter.mp hq).2
      rw [← hlineEq]
      exact hlineInsidePlane q
    have hFbound := plane_line_fiber_card_bound X P l m K (by linarith) hXm hbucket
    calc
      (Fq.card : ℝ) = (imagePlanes.card : ℝ) := by rw [hcardImage]
      _ ≤ (Fplane.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card himageSub)
      _ ≤ 2 * m / K := hFbound

  have hI0subP : I0 ⊆ P := by
    intro H' hH'
    simpa [I0] using (Finset.mem_filter.mp hH').1
  have hIcard : I.card = I0.card := by
    change I0.attach.card = I0.card
    rw [Finset.card_attach]
  have hIcardP : I.card ≤ P.card := by
    calc
      I.card = I0.card := hIcard
      _ ≤ P.card := Finset.card_le_card hI0subP
  have hsumI0 :
      (∑ H' ∈ P, if H ≠ H' then ((planePairPoints X H H').card : ℝ) else 0) =
        ∑ H' ∈ I0, ((planePairPoints X H H').card : ℝ) := by
    have hcond :
        (∑ H' ∈ I0, ((planePairPoints X H H').card : ℝ)) =
          ∑ H' ∈ I0, (if H ≠ H' then ((planePairPoints X H H').card : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro H' hH'
      have hneq := (Finset.mem_filter.mp hH').2.1
      simp [hneq]
    have hsubsetSum :
        (∑ H' ∈ I0, (if H ≠ H' then ((planePairPoints X H H').card : ℝ) else 0)) =
          ∑ H' ∈ P, (if H ≠ H' then ((planePairPoints X H H').card : ℝ) else 0) := by
      apply Finset.sum_subset hI0subP
      intro H' hH' hnot
      by_cases hneq : H ≠ H'
      · have hEmpty : planePairPoints X H H' = ∅ := by
          by_contra hne
          apply hnot
          exact Finset.mem_filter.mpr ⟨hH', hneq, Finset.nonempty_iff_ne_empty.mpr hne⟩
        simp [hneq, hEmpty]
      · simp [hneq]
    exact hsubsetSum.symm.trans hcond.symm
  have hsumI :
      (∑ H' ∈ P, if H ≠ H' then ((planePairPoints X H H').card : ℝ) else 0) =
        ∑ q ∈ I, ((planePairPoints X H q.1).card : ℝ) := by
    calc
      _ = ∑ H' ∈ I0, ((planePairPoints X H H').card : ℝ) := hsumI0
      _ = ∑ q ∈ I, ((planePairPoints X H q.1).card : ℝ) := by
        change (∑ H' ∈ I0, ((planePairPoints X H H').card : ℝ)) =
          (∑ q ∈ I0.attach, ((planePairPoints X H q.1).card : ℝ))
        rw [← Finset.sum_attach]
  have hsumLine :
      (∑ q ∈ I, ((planePairPoints X H q.1).card : ℝ)) =
        ∑ q ∈ I, ((pointsOn X (lineOf q)).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hpairLineEq q]
  have hsplit :
      (∑ q ∈ I, ((pointsOn X (lineOf q)).card : ℝ)) =
        (∑ q ∈ LlowQ, ((pointsOn X (lineOf q)).card : ℝ)) +
          (∑ q ∈ LheavyQ, ((pointsOn X (lineOf q)).card : ℝ)) := by
    have hunion : LlowQ ∪ LheavyQ = I := by
      ext q
      simp only [Finset.mem_union, Finset.mem_filter, LlowQ, LheavyQ, Finset.mem_attach,
        true_and]
      constructor
      · rintro (⟨hq, _⟩ | ⟨hq, _⟩)
        · exact hq
        · exact hq
      · intro hq
        rcases lt_or_ge ((pointsOn X (lineOf q)).card : ℝ) (2 * Real.sqrt K) with h | h
        · exact Or.inl ⟨hq, h⟩
        · exact Or.inr ⟨hq, h⟩
    have hdisj : Disjoint LlowQ LheavyQ := by
      rw [Finset.disjoint_left]
      intro q hq hq'
      exact (not_le_of_gt (Finset.mem_filter.mp hq).2) (Finset.mem_filter.mp hq').2
    rw [← hunion, Finset.sum_union hdisj]
  have hlowBound :
      (∑ q ∈ LlowQ, ((pointsOn X (lineOf q)).card : ℝ)) ≤
        2 * Real.sqrt K * P.card := by
    calc
      (∑ q ∈ LlowQ, ((pointsOn X (lineOf q)).card : ℝ)) ≤
          ∑ q ∈ LlowQ, (2 * Real.sqrt K) := by
        apply Finset.sum_le_sum
        intro q hq
        exact le_of_lt (Finset.mem_filter.mp hq).2
      _ = 2 * Real.sqrt K * LlowQ.card := by simp [mul_comm]
      _ ≤ 2 * Real.sqrt K * P.card := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hcard : LlowQ.card ≤ P.card :=
          le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hIcardP
        exact_mod_cast hcard
  have hhighBound :
      (∑ q ∈ LheavyQ, ((pointsOn X (lineOf q)).card : ℝ)) ≤
        2 * (Cs * (3 * A + 2)) * m := by
    have hmap : ∀ q ∈ LheavyQ, lineOf q ∈ Lheavy := hLheavyMap
    have hfiberSum :
        (∑ q ∈ LheavyQ, ((pointsOn X (lineOf q)).card : ℝ)) =
          ∑ l ∈ Lheavy,
            ∑ q ∈ LheavyQ with lineOf q = l, ((pointsOn X (lineOf q)).card : ℝ) := by
      exact (Finset.sum_fiberwise_of_maps_to hmap _).symm
    have hLheavyLineEq (l : Line 3) (hl : l ∈ Lheavy) :
        pointsOn X l = pointsOn (pointsOn X H) l := by
      rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
      exact hlinePointsEq q
    have hconstantFiber (l : Line 3) (hl : l ∈ Lheavy) :
        (∑ q ∈ LheavyQ with lineOf q = l, ((pointsOn X (lineOf q)).card : ℝ)) =
          ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) *
            ((pointsOn X l).card : ℝ) := by
      change (∑ q ∈ LheavyQ.filter (fun q => lineOf q = l),
          ((pointsOn X (lineOf q)).card : ℝ)) = _
      calc
        _ = ∑ q ∈ LheavyQ.filter (fun q => lineOf q = l),
            ((pointsOn X l).card : ℝ) := by
              apply Finset.sum_congr rfl
              intro q hq
              exact congrArg (fun l' => ((pointsOn X l').card : ℝ))
                (Finset.mem_filter.mp hq).2
        _ = _ := finset_sum_const_real _ _
    have hheavyLe :
        (∑ l ∈ Lheavy,
          ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) *
            ((pointsOn X l).card : ℝ)) ≤
          (2 * m / K) * (incidences (pointsOn X H) Lheavy : ℝ) := by
      have hterm (l : Line 3) (hl : l ∈ Lheavy) :
          ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) *
              ((pointsOn X l).card : ℝ) ≤
            (2 * m / K) * ((pointsOn X l).card : ℝ) :=
        mul_le_mul_of_nonneg_right (hfiber l hl) (Nat.cast_nonneg _)
      have hlineOcc :
          (∑ l ∈ Lheavy, ((pointsOn X l).card : ℝ)) =
            (incidences (pointsOn X H) Lheavy : ℝ) := by
        calc
          (∑ l ∈ Lheavy, ((pointsOn X l).card : ℝ)) =
              ∑ l ∈ Lheavy, ((pointsOn (pointsOn X H) l).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [hLheavyLineEq l hl]
          _ = (incidences (pointsOn X H) Lheavy : ℝ) := hincSum.symm
      calc
        _ ≤ ∑ l ∈ Lheavy, (2 * m / K) * ((pointsOn X l).card : ℝ) :=
          Finset.sum_le_sum hterm
        _ = (2 * m / K) *
            (∑ l ∈ Lheavy, ((pointsOn X l).card : ℝ)) := by rw [Finset.mul_sum]
        _ = (2 * m / K) * (incidences (pointsOn X H) Lheavy : ℝ) :=
          congrArg (fun t : ℝ => (2 * m / K) * t) hlineOcc
    rw [hfiberSum]
    calc
      (∑ l ∈ Lheavy,
        ∑ q ∈ LheavyQ with lineOf q = l, ((pointsOn X (lineOf q)).card : ℝ)) ≤
          ∑ l ∈ Lheavy,
            ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) *
              ((pointsOn X l).card : ℝ) := by
                apply Finset.sum_le_sum
                intro l hl
                rw [hconstantFiber l hl]
      _ ≤ (2 * m / K) * (incidences (pointsOn X H) Lheavy : ℝ) := hheavyLe
      _ ≤ (2 * m / K) * ((Cs * (3 * A + 2)) * K) := by
        exact mul_le_mul_of_nonneg_left hSTbound
          (div_nonneg (mul_nonneg (by norm_num) hmnonneg) hKpos.le)
      _ = 2 * (Cs * (3 * A + 2)) * m := by field_simp [hKpos.ne'] <;> ring
  rw [hsumI, hsumLine, hsplit]
  exact add_le_add hlowBound hhighBound

/-- Intersection-line dyadic count, motions.tex:181–206. -/
theorem plane_pair_upper : ∃ C : ℝ, 0 < C ∧
    ∀ (X : Finset (E 3)) (P : Finset (Plane 3)) (m K : ℝ),
      1 ≤ m → (X.card : ℝ) ≤ m → 1 ≤ K →
      (∀ H ∈ P, K ≤ (pointsOn X H).card ∧ (pointsOn X H).card < 2 * K ∧
        ∀ l : Line 3, l.1 ≤ H.1 →
          ((pointsOn X l).card : ℝ) < ((pointsOn X H).card : ℝ) / 2) →
      (planePairEnergy X P : ℝ) ≤ C * P.card * (m + Real.sqrt K * P.card) := by
  classical
  obtain ⟨Cr, hCr, hRich⟩ := ci_st_rich
  obtain ⟨Cs, hCs, hST⟩ := ci_st
  let B : ℝ := Cs * (3 * (6 * Cr + 1) + 2)
  let C : ℝ := 2 + 2 * B
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCge2 : 2 ≤ C := by dsimp [C]; linarith [hBpos]
  have hCge2B : 2 * B ≤ C := by dsimp [C]; linarith [hBpos]
  refine ⟨C, hCpos, ?_⟩
  intro X P m K hm hXm hK hbucket
  have hRichFor (H : Plane 3) (L : Finset (Line 3)) (k : ℕ) (hk : 2 ≤ k) :
      FiniteCardBound (richLines (pointsOn X H) k)
        (Cr * (((pointsOn X H).card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
          ((pointsOn X H).card : ℝ) / k)) :=
    (hRich 3 (pointsOn X H) L k hk).2
  have hSTFor (H : Plane 3) (L : Finset (Line 3)) :
      (incidences (pointsOn X H) L : ℝ) ≤ Cs *
        (((pointsOn X H).card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
          (pointsOn X H).card + L.card) :=
    hST 3 (pointsOn X H) L
  have hfixed (H : Plane 3) (hH : H ∈ P) :
      (∑ H' ∈ P, if H ≠ H' then ((planePairPoints X H H').card : ℝ) else 0) ≤
        2 * Real.sqrt K * P.card + 2 * B * m := by
    have h := plane_pair_fixed_upper Cr Cs hCr hCs X P H m K hK hXm hH hbucket
      (fun L k hk => hRichFor H L k hk) (hSTFor H)
    simpa [B] using h
  have hcountP : (planePairEnergy X P : ℝ) ≤
      (P.card : ℝ) * (2 * Real.sqrt K * P.card + 2 * B * m) := by
    rw [planePairEnergy_sum_filter]
    calc
      (∑ H ∈ P, ∑ H' ∈ P,
          if H ≠ H' then ((planePairPoints X H H').card : ℝ) else 0) ≤
          ∑ H ∈ P, (2 * Real.sqrt K * P.card + 2 * B * m) := by
            apply Finset.sum_le_sum
            intro H hH
            exact hfixed H hH
      _ = (P.card : ℝ) * (2 * Real.sqrt K * P.card + 2 * B * m) :=
        finset_sum_const_real P _
  have hmnonneg : 0 ≤ m := le_trans (Nat.cast_nonneg X.card) hXm
  have hPnonneg : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hterm1 : 2 * Real.sqrt K * (P.card : ℝ) ^ 2 ≤
      C * Real.sqrt K * (P.card : ℝ) ^ 2 := by
    have hcoef : 2 * Real.sqrt K ≤ C * Real.sqrt K :=
      mul_le_mul_of_nonneg_right hCge2 (Real.sqrt_nonneg K)
    calc
      2 * Real.sqrt K * (P.card : ℝ) ^ 2 =
          (2 * Real.sqrt K) * (P.card : ℝ) ^ 2 := by ring
      _ ≤ (C * Real.sqrt K) * (P.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg (P.card : ℝ))
      _ = C * Real.sqrt K * (P.card : ℝ) ^ 2 := by ring
  have hterm2 : 2 * B * m * (P.card : ℝ) ≤ C * m * (P.card : ℝ) := by
    calc
      2 * B * m * (P.card : ℝ) = (2 * B) * (m * (P.card : ℝ)) := by ring
      _ ≤ C * (m * (P.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hCge2B (mul_nonneg hmnonneg hPnonneg)
      _ = C * m * (P.card : ℝ) := by ring
  calc
    (planePairEnergy X P : ℝ) ≤
        (P.card : ℝ) * (2 * Real.sqrt K * P.card + 2 * B * m) := hcountP
    _ = 2 * Real.sqrt K * (P.card : ℝ) ^ 2 + 2 * B * m * (P.card : ℝ) := by ring
    _ ≤ C * Real.sqrt K * (P.card : ℝ) ^ 2 + C * m * (P.card : ℝ) :=
      add_le_add hterm1 hterm2
    _ = C * P.card * (m + Real.sqrt K * P.card) := by ring

private theorem exists_noncollinear_triple_for_plane_aux (S : Finset (E 3))
    (hS : ¬ Collinear ℝ (S : Set (E 3))) :
    ∃ p₀ ∈ S, ∃ p₁ ∈ S, ∃ p₂ ∈ S, ¬ Collinear ℝ ({p₀, p₁, p₂} : Set (E 3)) := by
  classical
  have hne : S.Nonempty := by
    by_contra h
    have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hempty : Collinear ℝ (S : Set (E 3)) := by
      simpa [hzero] using (collinear_empty ℝ (E 3))
    exact hS hempty
  obtain ⟨p₀, hp₀⟩ := hne
  have hp₁ : ∃ p₁ ∈ S, p₁ ≠ p₀ := by
    by_contra h
    have hall : ∀ p ∈ S, p = p₀ := by
      intro p hp
      by_contra hpne
      exact h ⟨p, hp, hpne⟩
    apply hS
    rw [collinear_iff_of_mem hp₀]
    refine ⟨0, ?_⟩
    intro p hp
    rw [hall p hp]
    exact ⟨0, by simp⟩
  obtain ⟨p₁, hp₁S, hp₁ne⟩ := hp₁
  let L : AffineSubspace ℝ (E 3) := line[ℝ, p₀, p₁]
  have hp₂ : ∃ p₂ ∈ S, p₂ ∉ L := by
    by_contra h
    have hall : ∀ p ∈ S, p ∈ L := by
      intro p hp
      by_contra hpL
      exact h ⟨p, hp, hpL⟩
    apply hS
    rw [collinear_iff_of_mem hp₀]
    refine ⟨p₁ -ᵥ p₀, ?_⟩
    intro p hp
    obtain ⟨t, ht⟩ :=
      (mem_affineSpan_pair_iff_exists_lineMap_eq.mp (hall p hp))
    refine ⟨t, ?_⟩
    rw [AffineMap.lineMap_apply] at ht
    exact ht.symm
  obtain ⟨p₂, hp₂S, hp₂L⟩ := hp₂
  refine ⟨p₀, hp₀, p₁, hp₁S, p₂, hp₂S, ?_⟩
  rw [← affineIndependent_iff_not_collinear_set]
  exact affineIndependent_of_ne_of_mem_of_mem_of_notMem
    hp₁ne.symm (left_mem_affineSpan_pair ℝ p₀ p₁)
    (right_mem_affineSpan_pair ℝ p₀ p₁) hp₂L

private noncomputable def planeOfNoncollinearTriple (a b c : E 3)
    (habc : ¬ Collinear ℝ ({a, b, c} : Set (E 3))) : Plane 3 := by
  let src : Fin 3 → E 3 := ![a, b, c]
  have hsrc : AffineIndependent ℝ src := by
    apply affineIndependent_iff_not_collinear_set.mpr
    simpa [src] using habc
  let tri : Affine.Simplex ℝ (E 3) 2 := ⟨src, hsrc⟩
  let A : AffineSubspace ℝ (E 3) := affineSpan ℝ (Set.range tri.points)
  have hAne : (A : Set (E 3)).Nonempty := by
    refine ⟨a, mem_affineSpan ℝ ⟨0, by simp [tri, src]⟩⟩
  have hAdim : Module.finrank ℝ A.direction = 2 := by
    exact (Affine.Simplex.fact_finrank_direction_affineSpan_eq (s := tri)).out
  exact ⟨A, hAne, hAdim⟩

private theorem planeOfNoncollinearTriple_eq (a b c : E 3)
    (habc : ¬ Collinear ℝ ({a, b, c} : Set (E 3))) (H : Plane 3)
    (ha : a ∈ H.1) (hb : b ∈ H.1) (hc : c ∈ H.1) :
    planeOfNoncollinearTriple a b c habc = H := by
  classical
  let src : Fin 3 → E 3 := ![a, b, c]
  have hsrc : AffineIndependent ℝ src := by
    apply affineIndependent_iff_not_collinear_set.mpr
    simpa [src] using habc
  let tri : Affine.Simplex ℝ (E 3) 2 := ⟨src, hsrc⟩
  let A : AffineSubspace ℝ (E 3) := affineSpan ℝ (Set.range tri.points)
  have hsub : Set.range tri.points ⊆ (H.1 : Set (E 3)) := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa [tri, src] using ha
    · simpa [tri, src] using hb
    · simpa [tri, src] using hc
  have hAle : A ≤ H.1 := affineSpan_le_of_subset_coe hsub
  have hAdim : Module.finrank ℝ A.direction = 2 :=
    (Affine.Simplex.fact_finrank_direction_affineSpan_eq (s := tri)).out
  have hdir : A.direction = H.1.direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hAle)
      (by rw [hAdim, H.2.2])
  have haA : a ∈ A := by
    exact mem_affineSpan ℝ ⟨0, by simp [tri, src]⟩
  have hAeq : A = H.1 := AffineSubspace.ext_of_direction_eq hdir ⟨a, haA, ha⟩
  apply Subtype.ext
  exact hAeq

private theorem plane_line_off_fiber_bound (X : Finset (E 3))
    (P : Finset (Plane 3)) (l : Line 3) (m q : ℝ) (hq : 0 < q)
    (hXm : (X.card : ℝ) ≤ m)
    (hoff : ∀ H ∈ P, l.1 ≤ H.1 → q ≤
      ((pointsOn X H).filter (fun x => x ∉ (l.1 : Set (E 3)))).card) :
    ((P.filter (fun H => l.1 ≤ H.1)).card : ℝ) ≤ m / q := by
  classical
  let F : Finset (Plane 3) := P.filter (fun H => l.1 ≤ H.1)
  let off (H : Plane 3) : Finset (E 3) :=
    (pointsOn X H).filter (fun x => x ∉ (l.1 : Set (E 3)))
  have hoffsub (H : Plane 3) : off H ⊆ X := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hdisjoint : (F : Set (Plane 3)).PairwiseDisjoint off := by
    intro H hH H' hH' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hxH : x ∈ H.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hxH' : x ∈ H'.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx').1).2
    have hmeet := plane_meet_eq_common_line H H' hne l
      (Finset.mem_filter.mp hH).2 (Finset.mem_filter.mp hH').2
    have hxmeet : x ∈ H.1 ⊓ H'.1 :=
      (AffineSubspace.mem_inf_iff x H.1 H'.1).2 ⟨hxH, hxH'⟩
    have hxl : x ∈ l.1 := by rw [← hmeet]; exact hxmeet
    exact (Finset.mem_filter.mp hx).2 hxl
  let U : Finset (E 3) := F.biUnion off
  have hUsub : U ⊆ X := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨H, hH, hxH⟩
    exact hoffsub H hxH
  have hsum : (∑ H ∈ F, ((off H).card : ℝ)) ≤ m := by
    calc
      ∑ H ∈ F, ((off H).card : ℝ) = (U.card : ℝ) := by
        rw [Finset.card_biUnion hdisjoint]
        norm_cast
      _ ≤ (X.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hUsub)
      _ ≤ m := hXm
  have hprod : (F.card : ℝ) * q ≤ m := by
    calc
      (F.card : ℝ) * q = ∑ H ∈ F, q := by simp [mul_comm]
      _ ≤ ∑ H ∈ F, ((off H).card : ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        exact hoff H (Finset.mem_filter.mp hH).1 (Finset.mem_filter.mp hH).2
      _ ≤ m := hsum
  rw [show F = P.filter (fun H => l.1 ≤ H.1) from rfl] at hprod
  exact (le_div_iff₀ hq).2 (by simpa [mul_comm] using hprod)

private theorem plane_pair_energy_lower_variable (X : Finset (E 3))
    (P : Finset (Plane 3)) (m : ℝ) (hm : 0 < m)
    (hXm : (X.card : ℝ) ≤ m) (hXne : X.Nonempty) :
    (∑ H ∈ P, ((pointsOn X H).card : ℝ)) ^ 2 / m -
      ∑ H ∈ P, ((pointsOn X H).card : ℝ) ≤ (planePairEnergy X P : ℝ) := by
  classical
  let r : E 3 → ℕ := fun x => (P.filter (fun H => x ∈ H.1)).card
  have hinc : (∑ H ∈ P, (pointsOn X H).card) = ∑ x ∈ X, r x := by
    simp only [pointsOn, r, Finset.card_filter]
    rw [Finset.sum_comm]
  have hpair (x : E 3) :
      ((P.offDiag).filter (fun ab => x ∈ ab.1.1 ∧ x ∈ ab.2.1)).card =
        r x * (r x - 1) := by
    have hfilter :
        (P.offDiag).filter (fun ab => x ∈ ab.1.1 ∧ x ∈ ab.2.1) =
          (P.filter (fun H => x ∈ H.1)).offDiag := by
      ext ab
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      aesop
    rw [hfilter, Finset.offDiag_card]
    have hn (n : ℕ) : n * n - n = n * (n - 1) := by
      cases n with
      | zero => simp
      | succ n => simp [Nat.succ_mul, Nat.mul_succ]
    simpa [r] using hn (P.filter (fun H => x ∈ H.1)).card
  have henergy : planePairEnergy X P = ∑ x ∈ X, r x * (r x - 1) := by
    simp only [planePairEnergy, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    simpa only [Finset.card_filter] using hpair x
  have hincR : (∑ H ∈ P, ((pointsOn X H).card : ℝ)) =
      ∑ x ∈ X, (r x : ℝ) := by exact_mod_cast hinc
  have hcs : (∑ x ∈ X, (r x : ℝ)) ^ 2 ≤
      (X.card : ℝ) * ∑ x ∈ X, (r x : ℝ) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := X) (f := fun x => (r x : ℝ)))
  have hsqlo : (∑ x ∈ X, (r x : ℝ)) ^ 2 / m ≤
      ∑ x ∈ X, (r x : ℝ) ^ 2 := by
    have hmul := hcs
    have hsumSq : 0 ≤ ∑ x ∈ X, (r x : ℝ) ^ 2 :=
      Finset.sum_nonneg fun x hx => sq_nonneg _
    have hcard : (X.card : ℝ) ≤ m := hXm
    have hle : (X.card : ℝ) * ∑ x ∈ X, (r x : ℝ) ^ 2 ≤
        m * ∑ x ∈ X, (r x : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard hsumSq
    rw [div_le_iff₀ hm]
    nlinarith
  have henergy' : (planePairEnergy X P : ℝ) =
      (∑ x ∈ X, (r x : ℝ) ^ 2) - ∑ x ∈ X, (r x : ℝ) := by
    rw [henergy]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    cases hrx : r x with
    | zero => simp [hrx]
    | succ n => simp [hrx]; ring
  rw [hincR, henergy']
  nlinarith [hsqlo]

set_option maxHeartbeats 12000000 in
private theorem plane_pair_fixed_upper_effective
    (Cr Cs : ℝ) (hCr : 0 < Cr) (hCs : 0 < Cs)
    (X : Finset (E 3)) (P : Finset (Plane 3)) (H₀ : Plane 3)
    (m Hmin : ℝ) (hHmin : 1 ≤ Hmin) (hXm : (X.card : ℝ) ≤ m)
    (hHmem : H₀ ∈ P)
    (hplanes : ∀ H ∈ P, Hmin ≤ (pointsOn X H).card ∧
      ∀ l : Line 3, l.1 ≤ H.1 →
        ((pointsOn X l).card : ℝ) < ((pointsOn X H).card : ℝ) / 2)
    (hRich : ∀ L : Finset (Line 3), ∀ k : ℕ, 2 ≤ k →
      FiniteCardBound (richLines (pointsOn X H₀) k)
        (Cr * (((pointsOn X H₀).card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
          ((pointsOn X H₀).card : ℝ) / k)))
    (hST : ∀ L : Finset (Line 3), (incidences (pointsOn X H₀) L : ℝ) ≤ Cs *
      (((pointsOn X H₀).card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
        (pointsOn X H₀).card + L.card)) :
    (∑ H' ∈ P, if H₀ ≠ H' then ((planePairPoints X H₀ H').card : ℝ) else 0) ≤
      2 * Real.sqrt ((pointsOn X H₀).card : ℝ) * P.card +
        2 * (Cs * (3 * (6 * Cr + 1) + 2)) * m *
          ((pointsOn X H₀).card : ℝ) / Hmin := by
  classical
  let I₀ : Finset (Plane 3) := P.filter
    (fun H' => H₀ ≠ H' ∧ (planePairPoints X H₀ H').Nonempty)
  let Q := {H' : Plane 3 // H' ∈ I₀}
  let I : Finset Q := I₀.attach
  have hlineEx (q : Q) :
      ∃ l : Line 3, (l.1 : Set (E 3)) =
        (H₀.1 : Set (E 3)) ∩ (q.1.1 : Set (E 3)) := by
    rcases Finset.mem_filter.mp q.2 with ⟨_, hneq, hnonempty⟩
    rcases hnonempty with ⟨x, hx⟩
    have hx' : x ∈ X ∧ x ∈ H₀.1 ∧ x ∈ q.1.1 := by
      simpa [planePairPoints, pointsOn, Finset.filter_filter, and_assoc,
        and_left_comm, and_comm] using hx
    exact plane_intersection_is_line H₀ q.1 hneq ⟨x, hx'.2.1, hx'.2.2⟩
  let lineOf : Q → Line 3 := fun q => Classical.choose (hlineEx q)
  have hlineSpec (q : Q) :
      (lineOf q : Set (E 3)) = (H₀.1 : Set (E 3)) ∩ (q.1.1 : Set (E 3)) := by
    simpa using Classical.choose_spec (hlineEx q)
  have hlineMem (q : Q) (x : E 3) :
      x ∈ (lineOf q : Set (E 3)) ↔ x ∈ H₀.1 ∧ x ∈ q.1.1 := by
    have heq := congrArg (fun s : Set (E 3) => x ∈ s) (hlineSpec q)
    rw [heq]
    exact Set.mem_inter_iff x _ _
  have hlineInside (q : Q) : (lineOf q).1 ≤ H₀.1 := by
    intro x hx
    exact (hlineMem q x).mp hx |>.1
  have hlineInsidePlane (q : Q) : (lineOf q).1 ≤ q.1.1 := by
    intro x hx
    exact (hlineMem q x).mp hx |>.2
  have hpairLineEq (q : Q) :
      planePairPoints X H₀ q.1 = pointsOn X (lineOf q) := by
    ext x
    simp only [planePairPoints, pointsOn, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxX, hxH⟩, hxH'⟩
      refine ⟨hxX, ?_⟩
      exact (hlineMem q x).mpr ⟨hxH, hxH'⟩
    · rintro ⟨hxX, hxl⟩
      have hxmeet := (hlineMem q x).mp hxl
      exact ⟨⟨hxX, hxmeet.1⟩, hxmeet.2⟩
  have hlinePointsEq (q : Q) :
      pointsOn X (lineOf q) = pointsOn (pointsOn X H₀) (lineOf q) := by
    ext x
    simp only [pointsOn, Finset.mem_filter]
    constructor
    · rintro ⟨hxX, hxl⟩
      exact ⟨⟨hxX, hlineInside q hxl⟩, hxl⟩
    · rintro ⟨⟨hxX, hxH⟩, hxl⟩
      exact ⟨hxX, hxl⟩
  let n : ℝ := (pointsOn X H₀).card
  let LheavyQ : Finset Q := I.filter
    (fun q => 2 * Real.sqrt n ≤ ((pointsOn X (lineOf q)).card : ℝ))
  let Lheavy : Finset (Line 3) := LheavyQ.image lineOf
  let LlowQ : Finset Q := I.filter
    (fun q => ((pointsOn X (lineOf q)).card : ℝ) < 2 * Real.sqrt n)
  have hLheavyMap : ∀ q ∈ LheavyQ, lineOf q ∈ Lheavy :=
    fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hLheavySubset : ∀ l ∈ Lheavy,
      l ∈ richLines (pointsOn X H₀) (Nat.floor (2 * Real.sqrt n)) := by
    intro l hl
    rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
    change (Nat.floor (2 * Real.sqrt n) : ℝ) ≤
      ((pointsOn (pointsOn X H₀) (lineOf q)).card : ℝ)
    rw [← hlinePointsEq q]
    exact le_trans (Nat.floor_le (by positivity)) (Finset.mem_filter.mp hq).2
  have hnmin : Hmin ≤ n := by
    simpa [n] using (hplanes H₀ hHmem).1
  have hn1 : 1 ≤ n := le_trans hHmin hnmin
  have hroot1 : 1 ≤ Real.sqrt n := by
    have hs2 := Real.sq_sqrt (show 0 ≤ n by linarith)
    nlinarith [Real.sqrt_nonneg n, hs2]
  have hk2 : 2 ≤ Nat.floor (2 * Real.sqrt n) := by
    have hf := Nat.floor_mono (show (2 : ℝ) ≤ 2 * Real.sqrt n by nlinarith)
    simpa using hf
  have hLheavyBound : (Lheavy.card : ℝ) ≤ (6 * Cr + 1) * Real.sqrt n := by
    obtain ⟨hRichFin, hRichCount⟩ := hRich Lheavy (Nat.floor (2 * Real.sqrt n)) hk2
    have hcardSubset : Lheavy.card ≤ hRichFin.toFinset.card :=
      Finset.card_le_card (by
        intro l hl
        exact (hRichFin.mem_toFinset).mpr (hLheavySubset l hl))
    have hRichCount' :
        (hRichFin.toFinset.card : ℝ) ≤ Cr *
          (n ^ 2 / (Nat.floor (2 * Real.sqrt n) : ℝ) ^ 3 +
            n / Nat.floor (2 * Real.sqrt n)) := by
      have hcard : (richLines (pointsOn X H₀) (Nat.floor (2 * Real.sqrt n))).ncard =
          hRichFin.toFinset.card :=
        Set.ncard_eq_toFinset_card _ hRichFin
      rw [← hcard]
      simpa [n] using hRichCount
    have hHminNonneg : 0 ≤ Hmin := le_trans (by norm_num : (0 : ℝ) ≤ 1) hHmin
    have hnnonneg : 0 ≤ n := le_trans hHminNonneg hnmin
    have hkLower : Real.sqrt n ≤ (Nat.floor (2 * Real.sqrt n) : ℝ) := by
      have hf := Nat.lt_floor_add_one (2 * Real.sqrt n)
      nlinarith [hroot1]
    have hsmall := rich_line_sqrt_bound Cr n n hCr hn1 hnnonneg
      (by nlinarith) (Nat.floor (2 * Real.sqrt n)) hkLower
    calc
      (Lheavy.card : ℝ) ≤ (hRichFin.toFinset.card : ℝ) := Nat.cast_le.mpr hcardSubset
      _ ≤ 6 * Cr * Real.sqrt n := le_trans hRichCount' hsmall
      _ ≤ (6 * Cr + 1) * Real.sqrt n := by nlinarith [Real.sqrt_pos.2 (by linarith : 0 < n)]
  let A : ℝ := 6 * Cr + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hHminNonneg : 0 ≤ Hmin := le_trans (by norm_num : (0 : ℝ) ≤ 1) hHmin
  have hNnonneg : 0 ≤ n := le_trans hHminNonneg hnmin
  have hLnonneg : 0 ≤ (Lheavy.card : ℝ) := Nat.cast_nonneg _
  have hSTbound : (incidences (pointsOn X H₀) Lheavy : ℝ) ≤
      (Cs * (3 * A + 2)) * n := by
    have hST' := hST Lheavy
    have hscale := st_rpow_scale n A n (Lheavy.card : ℝ) hn1 hA hNnonneg
      (by nlinarith) hLnonneg hLheavyBound
    have hscale' : n ^ ((2 : ℝ) / 3) * (Lheavy.card : ℝ) ^ ((2 : ℝ) / 3) +
        (pointsOn X H₀).card + Lheavy.card ≤ (3 * A + 2) * n := by
      have hscale'' := hscale
      rw [show 2 * A + 2 + A = 3 * A + 2 by ring] at hscale''
      simpa [n] using hscale''
    calc
      (incidences (pointsOn X H₀) Lheavy : ℝ) ≤ Cs *
          (n ^ ((2 : ℝ) / 3) * (Lheavy.card : ℝ) ^ ((2 : ℝ) / 3) +
            (pointsOn X H₀).card + Lheavy.card) := by simpa [n] using hST'
      _ ≤ Cs * ((3 * A + 2) * n) := by
        exact mul_le_mul_of_nonneg_left hscale' hCs.le
      _ = (Cs * (3 * A + 2)) * n := by ring
  have hincSum : (incidences (pointsOn X H₀) Lheavy : ℝ) =
      ∑ l ∈ Lheavy, ((pointsOn (pointsOn X H₀) l).card : ℝ) := by
    have hn' : incidences (pointsOn X H₀) Lheavy =
        ∑ l ∈ Lheavy, (pointsOn (pointsOn X H₀) l).card := by
      simp only [incidences, lineMultiplicity, pointsOn, Finset.card_filter]
      rw [Finset.sum_comm]
    exact_mod_cast hn'
  have hfiber (l : Line 3) (hl : l ∈ Lheavy) :
      ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) ≤ 2 * m / Hmin := by
    let Fq := LheavyQ.filter (fun q => lineOf q = l)
    let Fplane := P.filter (fun H' => l.1 ≤ H'.1)
    let imagePlanes := Fq.image (fun q : Q => q.1)
    have hvalinj : Function.Injective (fun q : Q => q.1) := Subtype.val_injective
    have hcardImage : imagePlanes.card = Fq.card := by
      dsimp [imagePlanes]
      exact Finset.card_image_of_injective _ hvalinj
    have himageSub : imagePlanes ⊆ Fplane := by
      intro H' hH'
      rcases Finset.mem_image.mp hH' with ⟨q, hq, rfl⟩
      have hmem := Finset.mem_filter.mp q.2
      refine Finset.mem_filter.mpr ⟨hmem.1, ?_⟩
      have hlineEq := (Finset.mem_filter.mp hq).2
      rw [← hlineEq]
      exact hlineInsidePlane q
    have hoffplane (H' : Plane 3) (hH' : H' ∈ P) (hlH : l.1 ≤ H'.1) :
        Hmin / 2 ≤ ((pointsOn X H').filter
          (fun x => x ∉ (l.1 : Set (E 3)))).card := by
      have hph := hplanes H' hH'
      have hlineSub : pointsOn X l ⊆ pointsOn X H' := by
        intro x hx
        simp only [pointsOn, Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hlH hx.2⟩
      have hlineFilter : (pointsOn X H').filter
          (fun x => x ∈ (l.1 : Set (E 3))) = pointsOn X l := by
        ext x
        simp only [pointsOn, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hxX, hxH⟩, hxl⟩
          exact ⟨hxX, hxl⟩
        · intro hx
          exact ⟨⟨hx.1, hlH hx.2⟩, hx.2⟩
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := pointsOn X H') (fun x => x ∈ (l.1 : Set (E 3)))
      have hpartition' : (pointsOn X l).card +
          ((pointsOn X H').filter (fun x => x ∉ (l.1 : Set (E 3)))).card =
            (pointsOn X H').card := by
        rw [← hlineFilter]
        exact hpartition
      have hcap := hph.2 l hlH
      have hpartR : ((pointsOn X l).card : ℝ) +
          ((pointsOn X H').filter
            (fun x => x ∉ (l.1 : Set (E 3)))).card = (pointsOn X H').card := by
        exact_mod_cast hpartition'
      have hN := hph.1
      nlinarith
    have hfiberPlanes := plane_line_off_fiber_bound X P l m (Hmin / 2)
      (by linarith) hXm hoffplane
    calc
      (Fq.card : ℝ) = (imagePlanes.card : ℝ) := by rw [hcardImage]
      _ ≤ (Fplane.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card himageSub)
      _ ≤ m / (Hmin / 2) := hfiberPlanes
      _ = 2 * m / Hmin := by field_simp [ne_of_gt (by linarith : 0 < Hmin)] <;> ring
  have hI₀subP : I₀ ⊆ P := by
    intro H' hH'
    simpa [I₀] using (Finset.mem_filter.mp hH').1
  have hIcard : I.card = I₀.card := by
    change I₀.attach.card = I₀.card
    rw [Finset.card_attach]
  have hIcardP : I.card ≤ P.card := by
    calc I.card = I₀.card := hIcard
      _ ≤ P.card := Finset.card_le_card hI₀subP
  have hsumI₀ :
      (∑ H' ∈ P, if H₀ ≠ H' then ((planePairPoints X H₀ H').card : ℝ) else 0) =
        ∑ H' ∈ I₀, ((planePairPoints X H₀ H').card : ℝ) := by
    have hcond :
        (∑ H' ∈ I₀, ((planePairPoints X H₀ H').card : ℝ)) =
          ∑ H' ∈ I₀, (if H₀ ≠ H' then ((planePairPoints X H₀ H').card : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro H' hH'
      simp [(Finset.mem_filter.mp hH').2.1]
    have hsubsetSum :
        (∑ H' ∈ I₀, (if H₀ ≠ H' then ((planePairPoints X H₀ H').card : ℝ) else 0)) =
          ∑ H' ∈ P, (if H₀ ≠ H' then ((planePairPoints X H₀ H').card : ℝ) else 0) := by
      apply Finset.sum_subset hI₀subP
      intro H' hH' hnot
      by_cases hneq : H₀ ≠ H'
      · have hEmpty : planePairPoints X H₀ H' = ∅ := by
          by_contra hne
          apply hnot
          exact Finset.mem_filter.mpr ⟨hH', hneq,
            Finset.nonempty_iff_ne_empty.mpr hne⟩
        simp [hneq, hEmpty]
      · simp [hneq]
    exact hsubsetSum.symm.trans hcond.symm
  have hsumI :
      (∑ H' ∈ P, if H₀ ≠ H' then ((planePairPoints X H₀ H').card : ℝ) else 0) =
        ∑ q ∈ I, ((planePairPoints X H₀ q.1).card : ℝ) := by
    calc
      _ = ∑ H' ∈ I₀, ((planePairPoints X H₀ H').card : ℝ) := hsumI₀
      _ = ∑ q ∈ I, ((planePairPoints X H₀ q.1).card : ℝ) := by
        change (∑ H' ∈ I₀, ((planePairPoints X H₀ H').card : ℝ)) =
          (∑ q ∈ I₀.attach, ((planePairPoints X H₀ q.1).card : ℝ))
        rw [← Finset.sum_attach]
  have hsumLine :
      (∑ q ∈ I, ((planePairPoints X H₀ q.1).card : ℝ)) =
        ∑ q ∈ I, ((pointsOn X (lineOf q)).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hpairLineEq q]
  have hsplit :
      (∑ q ∈ I, ((pointsOn X (lineOf q)).card : ℝ)) =
        (∑ q ∈ LlowQ, ((pointsOn X (lineOf q)).card : ℝ)) +
          (∑ q ∈ LheavyQ, ((pointsOn X (lineOf q)).card : ℝ)) := by
    have hunion : LlowQ ∪ LheavyQ = I := by
      ext q
      simp only [Finset.mem_union, Finset.mem_filter, LlowQ, LheavyQ,
        Finset.mem_attach, true_and]
      constructor
      · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
      · intro hq
        rcases lt_or_ge ((pointsOn X (lineOf q)).card : ℝ) (2 * Real.sqrt n) with h | h
        · exact Or.inl ⟨hq, h⟩
        · exact Or.inr ⟨hq, h⟩
    have hdisj : Disjoint LlowQ LheavyQ := by
      rw [Finset.disjoint_left]
      intro q hq hq'
      exact (not_le_of_gt (Finset.mem_filter.mp hq).2) (Finset.mem_filter.mp hq').2
    rw [← hunion, Finset.sum_union hdisj]
  have hlowBound :
      (∑ q ∈ LlowQ, ((pointsOn X (lineOf q)).card : ℝ)) ≤
        2 * Real.sqrt n * P.card := by
    calc
      (∑ q ∈ LlowQ, ((pointsOn X (lineOf q)).card : ℝ)) ≤
          ∑ q ∈ LlowQ, (2 * Real.sqrt n) := by
        apply Finset.sum_le_sum
        intro q hq
        exact le_of_lt (Finset.mem_filter.mp hq).2
      _ = 2 * Real.sqrt n * LlowQ.card := by simp [mul_comm]
      _ ≤ 2 * Real.sqrt n * P.card := by
        have hLlowSub : LlowQ ⊆ I := by
          intro q hq
          exact (Finset.mem_filter.mp hq).1
        have hcard : LlowQ.card ≤ P.card :=
          calc
            LlowQ.card ≤ I.card := Finset.card_le_card hLlowSub
            _ ≤ P.card := hIcardP
        have hcardReal : (LlowQ.card : ℝ) ≤ P.card := by exact_mod_cast hcard
        have hcoeff : 0 ≤ 2 * Real.sqrt n := mul_nonneg (by norm_num) (Real.sqrt_nonneg n)
        exact mul_le_mul_of_nonneg_left hcardReal hcoeff
  have hhighBound :
      (∑ q ∈ LheavyQ, ((pointsOn X (lineOf q)).card : ℝ)) ≤
        2 * (Cs * (3 * A + 2)) * m * n / Hmin := by
    have hmap : ∀ q ∈ LheavyQ, lineOf q ∈ Lheavy := hLheavyMap
    have hfiberSum :
        (∑ q ∈ LheavyQ, ((pointsOn X (lineOf q)).card : ℝ)) =
          ∑ l ∈ Lheavy,
            ∑ q ∈ LheavyQ with lineOf q = l, ((pointsOn X (lineOf q)).card : ℝ) :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    have hLheavyLineEq (l : Line 3) (hl : l ∈ Lheavy) :
        pointsOn X l = pointsOn (pointsOn X H₀) l := by
      rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
      exact hlinePointsEq q
    have hconstantFiber (l : Line 3) (hl : l ∈ Lheavy) :
        (∑ q ∈ LheavyQ with lineOf q = l,
          ((pointsOn X (lineOf q)).card : ℝ)) =
          ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) *
            ((pointsOn X l).card : ℝ) := by
      change (∑ q ∈ LheavyQ.filter (fun q => lineOf q = l),
        ((pointsOn X (lineOf q)).card : ℝ)) = _
      calc
        _ = ∑ q ∈ LheavyQ.filter (fun q => lineOf q = l),
            ((pointsOn X l).card : ℝ) := by
              apply Finset.sum_congr rfl
              intro q hq
              exact congrArg (fun l' => ((pointsOn X l').card : ℝ))
                (Finset.mem_filter.mp hq).2
        _ = _ := finset_sum_const_real _ _
    have hlineOcc :
        (∑ l ∈ Lheavy, ((pointsOn X l).card : ℝ)) =
          (incidences (pointsOn X H₀) Lheavy : ℝ) := by
      calc
        _ = ∑ l ∈ Lheavy, ((pointsOn (pointsOn X H₀) l).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [hLheavyLineEq l hl]
        _ = _ := hincSum.symm
    have hheavyLe :
        (∑ l ∈ Lheavy,
          ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) *
            ((pointsOn X l).card : ℝ)) ≤
          (2 * m / Hmin) * (incidences (pointsOn X H₀) Lheavy : ℝ) := by
      have hterm (l : Line 3) (hl : l ∈ Lheavy) :
          ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) *
              ((pointsOn X l).card : ℝ) ≤
            (2 * m / Hmin) * ((pointsOn X l).card : ℝ) :=
        mul_le_mul_of_nonneg_right (hfiber l hl) (Nat.cast_nonneg _)
      calc
        _ ≤ ∑ l ∈ Lheavy, (2 * m / Hmin) * ((pointsOn X l).card : ℝ) :=
          Finset.sum_le_sum hterm
        _ = (2 * m / Hmin) *
            (∑ l ∈ Lheavy, ((pointsOn X l).card : ℝ)) := by rw [Finset.mul_sum]
        _ = (2 * m / Hmin) * (incidences (pointsOn X H₀) Lheavy : ℝ) :=
          congrArg (fun t : ℝ => (2 * m / Hmin) * t) hlineOcc
    rw [hfiberSum]
    calc
      (∑ l ∈ Lheavy,
        ∑ q ∈ LheavyQ with lineOf q = l, ((pointsOn X (lineOf q)).card : ℝ)) ≤
          ∑ l ∈ Lheavy,
            ((LheavyQ.filter (fun q => lineOf q = l)).card : ℝ) *
              ((pointsOn X l).card : ℝ) := by
                apply Finset.sum_le_sum
                intro l hl
                rw [hconstantFiber l hl]
      _ ≤ (2 * m / Hmin) * (incidences (pointsOn X H₀) Lheavy : ℝ) := hheavyLe
      _ ≤ (2 * m / Hmin) * ((Cs * (3 * A + 2)) * n) := by
        exact mul_le_mul_of_nonneg_left hSTbound
          (div_nonneg (mul_nonneg (by norm_num) (le_trans (Nat.cast_nonneg _) hXm))
            (by linarith))
      _ = 2 * (Cs * (3 * A + 2)) * m * n / Hmin := by
        field_simp [ne_of_gt (by linarith : 0 < Hmin)] <;> ring
  rw [hsumI, hsumLine, hsplit]
  calc
    (∑ q ∈ LlowQ, ((pointsOn X (lineOf q)).card : ℝ)) +
        (∑ q ∈ LheavyQ, ((pointsOn X (lineOf q)).card : ℝ)) ≤
      2 * Real.sqrt n * P.card +
        2 * (Cs * (3 * A + 2)) * m * n / Hmin := add_le_add hlowBound hhighBound
    _ = 2 * Real.sqrt ((pointsOn X H₀).card : ℝ) * P.card +
        2 * (Cs * (3 * (6 * Cr + 1) + 2)) * m *
          ((pointsOn X H₀).card : ℝ) / Hmin := by simp [n, A]

private theorem richestLineOccupancy_le (X : Finset (E 3)) (H : Plane 3) :
    richestLineOccupancy X H ≤ (pointsOn X H).card := by
  classical
  unfold richestLineOccupancy
  apply csSup_le'
  intro n hn
  rcases hn with ⟨l, hl, hcard⟩
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  simp only [pointsOn, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hl hx.2⟩

private theorem line_occupancy_le_richest (X : Finset (E 3)) (H : Plane 3)
    (l : Line 3) (hl : l.1 ≤ H.1) :
    (pointsOn X l).card ≤ richestLineOccupancy X H := by
  classical
  unfold richestLineOccupancy
  have hmem : (pointsOn X l).card ∈
      {n : ℕ | ∃ l' : Line 3, l'.1 ≤ H.1 ∧ (pointsOn X l').card = n} :=
    ⟨l, hl, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ l' : Line 3, l'.1 ≤ H.1 ∧
      (pointsOn X l').card = n} := by
    refine ⟨(pointsOn X H).card, ?_⟩
    intro n hn
    rcases hn with ⟨l', hl', hcard⟩
    rw [← hcard]
    apply Finset.card_le_card
    intro x hx
    simp only [pointsOn, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hl' hx.2⟩
  exact le_csSup hbdd hmem

private noncomputable def lineFlatOfDistinct_effective (p q : E 3) (hpq : p ≠ q) : Line 3 := by
  let L : AffineSubspace ℝ (E 3) := line[ℝ, p, q]
  refine ⟨L, ?_, ?_⟩
  · exact ⟨p, by simpa [L] using left_mem_affineSpan_pair ℝ p q⟩
  · have hdir : L.direction = Submodule.span ℝ {(q - p : E 3)} := by
      change (line[ℝ, p, q]).direction = _
      rw [direction_affineSpan]
      rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_insert p ({q} : Set (E 3)))]
      simp [vsub_eq_sub]
    rw [hdir]
    exact finrank_span_singleton (sub_ne_zero.mpr hpq.symm)

private theorem exists_line_containing_of_collinear_effective {S : Finset (E 3)}
    (hcard : 2 ≤ S.card) (hcol : Collinear ℝ (S : Set (E 3))) :
    ∃ l : Line 3, ∀ x ∈ S, x ∈ l.1 := by
  obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
  refine ⟨lineFlatOfDistinct_effective p q hpq, ?_⟩
  intro z hz
  change z ∈ line[ℝ, p, q]
  rw [hcol.affineSpan_eq_of_ne (by simpa using hp) (by simpa using hq) hpq]
  exact mem_affineSpan ℝ (Finset.mem_coe.mpr hz)

private theorem exists_line_in_plane_containing_of_collinear_effective
    {S : Finset (E 3)} (H : Plane 3)
    (hsubset : ∀ x ∈ S, x ∈ H.1) (hcard : 2 ≤ S.card)
    (hcol : Collinear ℝ (S : Set (E 3))) :
    ∃ l : Line 3, l.1 ≤ H.1 ∧ ∀ x ∈ S, x ∈ l.1 := by
  obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
  let l := lineFlatOfDistinct_effective p q hpq
  refine ⟨l, ?_, ?_⟩
  · change line[ℝ, p, q] ≤ H.1
    apply affineSpan_le_of_subset_coe
    intro x hx
    have hx' : x = p ∨ x = q := by simpa using hx
    rcases hx' with hxp | hxq
    · rw [hxp]
      exact hsubset p hp
    · rw [hxq]
      exact hsubset q hq
  · intro z hz
    change z ∈ line[ℝ, p, q]
    rw [hcol.affineSpan_eq_of_ne (by simpa using hp) (by simpa using hq) hpq]
    exact mem_affineSpan ℝ (Finset.mem_coe.mpr hz)

private theorem effectiveSize_le_offLine_card (X : Finset (E 3))
    (H : Plane 3) (l : Line 3) (hl : l.1 ≤ H.1) :
    effectiveSize X H ≤
      ((pointsOn X H).filter (fun x => x ∉ (l.1 : Set (E 3)))).card := by
  classical
  have hline : (pointsOn X l).card ≤ richestLineOccupancy X H :=
    line_occupancy_le_richest X H l hl
  have hlineFilter : (pointsOn X H).filter
      (fun x => x ∈ (l.1 : Set (E 3))) = pointsOn X l := by
    ext x
    simp only [pointsOn, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxX, hxH⟩, hxl⟩
      exact ⟨hxX, hxl⟩
    · intro hx
      exact ⟨⟨hx.1, hl hx.2⟩, hx.2⟩
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := pointsOn X H) (fun x => x ∈ (l.1 : Set (E 3)))
  have hpartition' : (pointsOn X l).card +
      ((pointsOn X H).filter (fun x => x ∉ (l.1 : Set (E 3)))).card =
        (pointsOn X H).card := by
    rw [← hlineFilter]
    exact hpartition
  have hmax := richestLineOccupancy_le X H
  dsimp [effectiveSize]
  omega

set_option maxHeartbeats 12000000 in
/-- mot:effective-planes, motions.tex:138–213. -/
theorem mot_effective_planes : ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (X : Finset (E 3)) (m H : ℝ), 1 ≤ m → (X.card : ℝ) ≤ m →
      C * m ^ ((2 : ℝ) / 3) ≤ H →
      FiniteCardBound {Hplane : Plane 3 | H ≤ (effectiveSize X Hplane : ℝ)} (K * m ^ 2 / H ^ 2) := by
  classical
  obtain ⟨Cr, hCr, hRich⟩ := ci_st_rich
  obtain ⟨Cs, hCs, hST⟩ := ci_st
  let D : ℝ := 2 * (Cs * (3 * (6 * Cr + 1) + 2))
  let K₂ : ℝ := 68 * Cr + 2 * (1 + D)
  have hK₂ : 0 < K₂ := by dsimp [K₂, D]; positivity
  refine ⟨8, K₂, by norm_num, hK₂, ?_⟩
  intro X m H hm hXm hthreshold
  let S : Set (Plane 3) := {Hplane | H ≤ (effectiveSize X Hplane : ℝ)}
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hmPow : 1 ≤ m ^ ((2 : ℝ) / 3) := Real.one_le_rpow hm (by norm_num)
  have hH8 : 8 ≤ H := by nlinarith [hthreshold, hmPow]
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH8
  have htargetOcc (Q : Plane 3) (hQ : Q ∈ S) :
      H ≤ (pointsOn X Q).card := by
    change H ≤ (effectiveSize X Q : ℝ) at hQ
    have hEff : effectiveSize X Q ≤ (pointsOn X Q).card := by
      simp [effectiveSize]
    exact hQ.trans (by exact_mod_cast hEff)
  by_cases hHm : H ≤ m
  · have hnotcol (Q : Plane 3) (hQ : Q ∈ S) :
        ¬ Collinear ℝ (pointsOn X Q : Set (E 3)) := by
      have hcard3 : 3 ≤ (pointsOn X Q).card := by
        exact_mod_cast (show (3 : ℝ) ≤ (pointsOn X Q).card by
          linarith [hH8, htargetOcc Q hQ])
      intro hcol
      obtain ⟨l, hlQ, hall⟩ := exists_line_in_plane_containing_of_collinear_effective Q
        (by intro x hx; exact (Finset.mem_filter.mp hx).2) (by omega) hcol
      have hpoints : pointsOn X l = pointsOn X Q := by
        ext x
        simp only [pointsOn, Finset.mem_filter]
        constructor
        · rintro ⟨hxX, hxl⟩
          exact ⟨hxX, hlQ hxl⟩
        · rintro ⟨hxX, hxQ⟩
          have hxpoints : x ∈ pointsOn X Q := by
            simp [pointsOn, hxX, hxQ]
          exact ⟨hxX, hall x hxpoints⟩
      have hrich : richestLineOccupancy X Q = (pointsOn X Q).card := by
        apply le_antisymm
        · exact richestLineOccupancy_le X Q
        · rw [← hpoints]
          exact line_occupancy_le_richest X Q l hlQ
      have heff : effectiveSize X Q = 0 := by simp [effectiveSize, hrich]
      change H ≤ (effectiveSize X Q : ℝ) at hQ
      rw [heff] at hQ
      norm_num at hQ
      linarith [hHpos]
    let T : Finset (E 3 × E 3 × E 3) := X.product (X.product X)
    let U : Finset (E 3 × E 3 × E 3) := T.filter
      (fun t => ¬ Collinear ℝ ({t.1, t.2.1, t.2.2} : Set (E 3)))
    let f : {t : E 3 × E 3 × E 3 // t ∈ U} → Plane 3 := fun t =>
      planeOfNoncollinearTriple t.1.1 t.1.2.1 t.1.2.2
        (Finset.mem_filter.mp t.2 |>.2)
    let F : Finset (Plane 3) := U.attach.image f
    have hSsub : S ⊆ (F : Set (Plane 3)) := by
      intro Q hQ
      obtain ⟨a, ha, b, hb, c, hc, habc⟩ :=
        exists_noncollinear_triple_for_plane_aux (pointsOn X Q) (hnotcol Q hQ)
      let t : E 3 × E 3 × E 3 := (a, (b, c))
      have haX : a ∈ X := (Finset.mem_filter.mp ha).1
      have hbX : b ∈ X := (Finset.mem_filter.mp hb).1
      have hcX : c ∈ X := (Finset.mem_filter.mp hc).1
      have htU : t ∈ U := by
        apply Finset.mem_filter.mpr
        constructor
        · simp [T, t, Finset.mem_product, haX, hbX, hcX]
        · simpa [t] using habc
      let u : {t : E 3 × E 3 × E 3 // t ∈ U} := ⟨t, htU⟩
      have hfu : f u = Q := by
        apply planeOfNoncollinearTriple_eq a b c habc Q
        · exact (Finset.mem_filter.mp ha).2
        · exact (Finset.mem_filter.mp hb).2
        · exact (Finset.mem_filter.mp hc).2
      have huF : f u ∈ F := Finset.mem_image.mpr ⟨u, Finset.mem_attach _ _, rfl⟩
      change Q ∈ (F : Set (Plane 3))
      rwa [← hfu]
    have hSfinite : S.Finite := F.finite_toSet.subset hSsub
    let Pall : Finset (Plane 3) := hSfinite.toFinset
    have hPall (Q : Plane 3) : Q ∈ Pall ↔ Q ∈ S := hSfinite.mem_toFinset
    let isDom (Q : Plane 3) : Prop := ∃ l : Line 3,
      l.1 ≤ Q.1 ∧ ((pointsOn X Q).card : ℝ) / 2 ≤ (pointsOn X l).card
    let Pdom : Finset (Plane 3) := Pall.filter isDom
    let Pnon : Finset (Plane 3) := Pall.filter (fun Q => ¬ isDom Q)
    have hpartition := Finset.card_filter_add_card_filter_not (s := Pall) isDom
    have hPnonOcc (Q : Plane 3) (hQ : Q ∈ Pnon) :
        H ≤ (pointsOn X Q).card ∧
          ∀ l : Line 3, l.1 ≤ Q.1 →
            ((pointsOn X l).card : ℝ) < ((pointsOn X Q).card : ℝ) / 2 := by
      have hQall : Q ∈ Pall := (Finset.mem_filter.mp hQ).1
      have hQS : Q ∈ S := (hPall Q).1 hQall
      refine ⟨htargetOcc Q hQS, ?_⟩
      intro l hl
      have hnotdom := (Finset.mem_filter.mp hQ).2
      by_contra hn
      have hdom : isDom Q := ⟨l, hl, le_of_not_gt hn⟩
      exact hnotdom hdom
    have hXocc (Q : Plane 3) : (pointsOn X Q).card ≤ X.card := by
      apply Finset.card_le_card
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    have hXoccReal (Q : Plane 3) : ((pointsOn X Q).card : ℝ) ≤ m := by
      exact (Nat.cast_le.mpr (hXocc Q)).trans hXm
    let k : ℕ := Nat.floor (H / 2)
    have hk2 : 2 ≤ k := by
      have hf := Nat.floor_mono (show (4 : ℝ) ≤ H / 2 by linarith [hH8])
      have hf' : 4 ≤ k := by simpa [k] using hf
      omega
    let Rbound := (hRich 3 X (∅ : Finset (Line 3)) k hk2).2
    let R : Finset (Line 3) := Rbound.1.toFinset
    have hRcard : (R.card : ℝ) ≤ Cr *
        (((X.card : ℝ) ^ 2 / (k : ℝ) ^ 3) + (X.card : ℝ) / k) := by
      have h := Rbound.2
      simpa [R, Set.ncard_eq_toFinset_card (richLines X k) Rbound.1] using h
    have hRmem (l : Line 3) (hl : l ∈ R) :
        (k : ℝ) ≤ (pointsOn X l).card := by
      exact (Rbound.1.mem_toFinset).mp hl
    have hkH : H / 4 ≤ (k : ℝ) := by
      have hf := Nat.lt_floor_add_one (H / 2)
      change H / 2 < (k : ℝ) + 1 at hf
      nlinarith [hH8]
    have hmPow43 : m ≤ m ^ ((4 : ℝ) / 3) := by
      have h := Real.rpow_le_rpow_of_exponent_le (x := m) hm
        (y := (1 : ℝ)) (z := (4 : ℝ) / 3) (by norm_num)
      simpa using h
    have hpow23 : (m ^ ((2 : ℝ) / 3)) ^ 2 = m ^ ((4 : ℝ) / 3) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hmpos)]
      norm_num
    have hHsq : m ≤ H ^ 2 := by
      have hbase : (8 * m ^ ((2 : ℝ) / 3)) ^ 2 ≤ H ^ 2 := by gcongr
      rw [show (8 * m ^ ((2 : ℝ) / 3)) ^ 2 =
        64 * m ^ ((4 : ℝ) / 3) by rw [mul_pow, hpow23]; ring] at hbase
      nlinarith [hbase, hmPow43]
    have hRupper : (R.card : ℝ) ≤ 68 * Cr * m / H := by
      have hkpos : 0 < (k : ℝ) :=
        lt_of_lt_of_le (by positivity : (0 : ℝ) < H / 4) hkH
      have hnum : (X.card : ℝ) ^ 2 ≤ m ^ 2 := by gcongr
      have hterms :
          (X.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (X.card : ℝ) / k ≤
            64 * m ^ 2 / H ^ 3 + 4 * m / H := by
        have hfirst : (X.card : ℝ) ^ 2 / (k : ℝ) ^ 3 ≤ 64 * m ^ 2 / H ^ 3 := by
          have hk3 : (H / 4) ^ 3 ≤ (k : ℝ) ^ 3 := by gcongr
          have hk3' : H ^ 3 ≤ 64 * (k : ℝ) ^ 3 := by nlinarith [hk3]
          apply (div_le_div_iff₀ (by positivity : 0 < (k : ℝ) ^ 3)
            (by positivity : 0 < H ^ 3)).2
          calc
            (X.card : ℝ) ^ 2 * H ^ 3 ≤ m ^ 2 * H ^ 3 :=
              mul_le_mul_of_nonneg_right hnum (by positivity)
            _ ≤ 64 * m ^ 2 * (k : ℝ) ^ 3 := by
              have h := mul_le_mul_of_nonneg_left hk3' (sq_nonneg m)
              nlinarith [h]
        have hsecond : (X.card : ℝ) / k ≤ 4 * m / H := by
          apply (div_le_div_iff₀ hkpos hHpos).2
          calc
            (X.card : ℝ) * H ≤ m * H := mul_le_mul_of_nonneg_right hXm hHpos.le
            _ ≤ m * (4 * (k : ℝ)) := by
              exact mul_le_mul_of_nonneg_left (by nlinarith [hkH]) (le_trans (Nat.cast_nonneg _) hXm)
            _ = 4 * m * k := by ring
        linarith
      have hterms' : 64 * m ^ 2 / H ^ 3 + 4 * m / H ≤ 68 * m / H := by
        have hmain : m ^ 2 / H ^ 3 ≤ m / H := by
          apply (div_le_div_iff₀ (by positivity : 0 < H ^ 3) hHpos).2
          have hmul := mul_le_mul_of_nonneg_left hHsq hmpos.le
          have hmul' := mul_le_mul_of_nonneg_right hmul hHpos.le
          nlinarith [hmul']
        have hmain' := mul_le_mul_of_nonneg_left hmain (by norm_num : 0 ≤ (64 : ℝ))
        calc
          64 * m ^ 2 / H ^ 3 + 4 * m / H =
              64 * (m ^ 2 / H ^ 3) + 4 * m / H := by ring
          _ ≤ 64 * (m / H) + 4 * m / H := by nlinarith [hmain']
          _ = 68 * m / H := by ring
      calc
        (R.card : ℝ) ≤ Cr *
            ((X.card : ℝ) ^ 2 / (k : ℝ) ^ 3 + (X.card : ℝ) / k) := hRcard
        _ ≤ Cr * (68 * m / H) := by
          apply mul_le_mul_of_nonneg_left (hterms.trans hterms') hCr.le
        _ = 68 * Cr * m / H := by ring
    let Ddom : Finset {Q : Plane 3 // Q ∈ Pdom} := Pdom.attach
    have hdomWitness (p : {Q : Plane 3 // Q ∈ Pdom}) :
        ∃ l : Line 3, l.1 ≤ p.1.1 ∧ H / 2 ≤ (pointsOn X l).card := by
      rcases (Finset.mem_filter.mp p.2) with ⟨hQall, hdom⟩
      rcases hdom with ⟨l, hl, hOcc⟩
      have hQS := (hPall p.1).1 hQall
      refine ⟨l, hl, ?_⟩
      exact (div_le_div_of_nonneg_right (htargetOcc p.1 hQS) (by norm_num)).trans hOcc
    let lineOfDom : {Q : Plane 3 // Q ∈ Pdom} → Line 3 :=
      fun p => Classical.choose (hdomWitness p)
    have hlineOfDomSpec (p : {Q : Plane 3 // Q ∈ Pdom}) :
        (lineOfDom p).1 ≤ p.1.1 ∧ H / 2 ≤ (pointsOn X (lineOfDom p)).card :=
      Classical.choose_spec (hdomWitness p)
    have hlineOfDomRich (p : {Q : Plane 3 // Q ∈ Pdom}) : lineOfDom p ∈ R := by
      apply (Rbound.1.mem_toFinset).2
      change (k : ℝ) ≤ (pointsOn X (lineOfDom p)).card
      exact (le_trans (Nat.floor_le (by positivity)) (hlineOfDomSpec p).2)
    let Rused : Finset (Line 3) := Ddom.image lineOfDom
    have hRusedSub : Rused ⊆ R := by
      intro l hl
      rcases Finset.mem_image.mp hl with ⟨p, hp, rfl⟩
      exact hlineOfDomRich p
    have hdomFiber (l : Line 3) (hl : l ∈ Rused) :
        ((Ddom.filter (fun p => lineOfDom p = l)).card : ℝ) ≤ m / H := by
      let Fp := Ddom.filter (fun p => lineOfDom p = l)
      let Qplanes := Fp.image (fun p : {Q : Plane 3 // Q ∈ Pdom} => p.1)
      have hvalinj : Function.Injective
          (fun p : {Q : Plane 3 // Q ∈ Pdom} => p.1) := Subtype.val_injective
      have hcardImage : Qplanes.card = Fp.card := by
        dsimp [Qplanes]
        exact Finset.card_image_of_injective _ hvalinj
      have hlineSub (Q : Plane 3) (hQ : Q ∈ Qplanes) : l.1 ≤ Q.1 := by
        rcases Finset.mem_image.mp hQ with ⟨p, hp, rfl⟩
        rw [← (Finset.mem_filter.mp hp).2]
        exact (hlineOfDomSpec p).1
      have hlineFilter : Qplanes.filter (fun Q => l.1 ≤ Q.1) = Qplanes := by
        ext Q
        simp only [Finset.mem_filter]
        constructor
        · exact And.left
        · intro hQ
          exact ⟨hQ, hlineSub Q hQ⟩
      have hoff (Q : Plane 3) (hQ : Q ∈ Qplanes) (hlQ : l.1 ≤ Q.1) :
          H ≤ ((pointsOn X Q).filter
            (fun x => x ∉ (l.1 : Set (E 3)))).card := by
        rcases Finset.mem_image.mp hQ with ⟨p, hp, rfl⟩
        have hQS := (hPall p.1).1 (Finset.mem_filter.mp p.2).1
        have hEff := effectiveSize_le_offLine_card X p.1 l (by
          rw [← (Finset.mem_filter.mp hp).2]
          exact (hlineOfDomSpec p).1)
        have hTarget : H ≤ (effectiveSize X p.1 : ℝ) := hQS
        exact hTarget.trans (by exact_mod_cast hEff)
      have hbound := plane_line_off_fiber_bound X Qplanes l m H hHpos hXm hoff
      have hbound' : (Qplanes.card : ℝ) ≤ m / H := by
        rw [← hlineFilter]
        exact hbound
      calc
        (Fp.card : ℝ) = (Qplanes.card : ℝ) := by rw [hcardImage]
        _ ≤ m / H := hbound'
    have hmapDom : ∀ p ∈ Ddom, lineOfDom p ∈ Rused := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hsumDom :
        (∑ p ∈ Ddom, (1 : ℝ)) =
          ∑ l ∈ Rused, ∑ p ∈ Ddom with lineOfDom p = l, (1 : ℝ) :=
      (Finset.sum_fiberwise_of_maps_to hmapDom _).symm
    have hDcard : (Pdom.card : ℝ) ≤ (R.card : ℝ) * (m / H) := by
      have hDcardEq : (Ddom.card : ℝ) = (Pdom.card : ℝ) := by
        simp [Ddom]
      have hsumCard : (Ddom.card : ℝ) =
          ∑ l ∈ Rused, ((Ddom.filter (fun p => lineOfDom p = l)).card : ℝ) := by
        have h := hsumDom
        simpa [finset_sum_const_real] using h
      rw [← hDcardEq, hsumCard]
      calc
        (∑ l ∈ Rused, ((Ddom.filter (fun p => lineOfDom p = l)).card : ℝ)) ≤
            ∑ l ∈ Rused, (m / H) := by
          apply Finset.sum_le_sum
          intro l hl
          exact hdomFiber l hl
        _ = (Rused.card : ℝ) * (m / H) := by simp [mul_comm]
        _ ≤ (R.card : ℝ) * (m / H) := by
          apply mul_le_mul_of_nonneg_right _ (div_nonneg (le_trans (Nat.cast_nonneg _) hXm) hHpos.le)
          exact_mod_cast Finset.card_le_card hRusedSub
    have hDdom : (Pdom.card : ℝ) ≤ 68 * Cr * m ^ 2 / H ^ 2 := by
      calc
        (Pdom.card : ℝ) ≤ (R.card : ℝ) * (m / H) := hDcard
        _ ≤ (68 * Cr * m / H) * (m / H) := by
          exact mul_le_mul_of_nonneg_right hRupper
            (div_nonneg (le_trans (Nat.cast_nonneg _) hXm) hHpos.le)
        _ = 68 * Cr * m ^ 2 / H ^ 2 := by field_simp [ne_of_gt hHpos] <;> ring
    by_cases hPnonEmpty : Pnon.Nonempty
    · let fNon : ℝ := Pnon.card
      let I : ℝ := ∑ Q ∈ Pnon, ((pointsOn X Q).card : ℝ)
      have hIlo : H * fNon ≤ I := by
        calc
          H * fNon = ∑ Q ∈ Pnon, H := by simp [fNon, mul_comm]
          _ ≤ ∑ Q ∈ Pnon, ((pointsOn X Q).card : ℝ) := by
            apply Finset.sum_le_sum
            intro Q hQ
            exact (hPnonOcc Q hQ).1
          _ = I := rfl
      have hIhi : I ≤ m * fNon := by
        calc
          I = ∑ Q ∈ Pnon, ((pointsOn X Q).card : ℝ) := rfl
          _ ≤ ∑ Q ∈ Pnon, m := by
            apply Finset.sum_le_sum
            intro Q hQ
            exact hXoccReal Q
          _ = m * fNon := by simp [fNon, mul_comm]
      have hRichFor (Q : Plane 3) (L : Finset (Line 3)) (k' : ℕ)
          (hk' : 2 ≤ k') :
          FiniteCardBound (richLines (pointsOn X Q) k')
            (Cr * (((pointsOn X Q).card : ℝ) ^ 2 / (k' : ℝ) ^ 3 +
              ((pointsOn X Q).card : ℝ) / k')) :=
        (hRich 3 (pointsOn X Q) L k' hk').2
      have hSTFor (Q : Plane 3) (L : Finset (Line 3)) :
          (incidences (pointsOn X Q) L : ℝ) ≤ Cs *
            (((pointsOn X Q).card : ℝ) ^ ((2 : ℝ) / 3) *
                (L.card : ℝ) ^ ((2 : ℝ) / 3) +
              (pointsOn X Q).card + L.card) := hST 3 (pointsOn X Q) L
      have hfixed (Q : Plane 3) (hQ : Q ∈ Pnon) :
          (∑ Q' ∈ Pnon,
            if Q ≠ Q' then ((planePairPoints X Q Q').card : ℝ) else 0) ≤
            2 * Real.sqrt ((pointsOn X Q).card : ℝ) * Pnon.card +
              D * m * ((pointsOn X Q).card : ℝ) / H := by
        have h := plane_pair_fixed_upper_effective Cr Cs hCr hCs X Pnon Q m H
          (by linarith [hH8]) hXm hQ
          (fun Q' hQ' => hPnonOcc Q' hQ')
          (hRichFor Q) (hSTFor Q)
        simpa [D] using h
      have hpairUpper : (planePairEnergy X Pnon : ℝ) ≤
          2 * fNon * I / Real.sqrt H + D * m * I / H := by
        have hterm (Q : Plane 3) (hQ : Q ∈ Pnon) :
            (∑ Q' ∈ Pnon,
              if Q ≠ Q' then ((planePairPoints X Q Q').card : ℝ) else 0) ≤
              2 * (Pnon.card : ℝ) / Real.sqrt H *
                  ((pointsOn X Q).card : ℝ) +
                D * m / H * ((pointsOn X Q).card : ℝ) := by
          have hN := hPnonOcc Q hQ |>.1
          have hsqrt : Real.sqrt H ≤
              Real.sqrt ((pointsOn X Q).card : ℝ) :=
            Real.sqrt_le_sqrt (by exact_mod_cast hN)
          have hsqrtHpos : 0 < Real.sqrt H := Real.sqrt_pos.2 hHpos
          have hrootBound : Real.sqrt ((pointsOn X Q).card : ℝ) ≤
              ((pointsOn X Q).card : ℝ) / Real.sqrt H := by
            apply (le_div_iff₀ hsqrtHpos).2
            calc
              Real.sqrt ((pointsOn X Q).card : ℝ) * Real.sqrt H ≤
                  Real.sqrt ((pointsOn X Q).card : ℝ) *
                    Real.sqrt ((pointsOn X Q).card : ℝ) :=
                mul_le_mul_of_nonneg_left hsqrt
                  (Real.sqrt_nonneg ((pointsOn X Q).card : ℝ))
              _ = Real.sqrt ((pointsOn X Q).card : ℝ) ^ 2 := by ring
              _ = (pointsOn X Q).card := Real.sq_sqrt (Nat.cast_nonneg _)
          have hscaled := mul_le_mul_of_nonneg_left hrootBound
            (by norm_num : (0 : ℝ) ≤ 2)
          have hlowTerm := mul_le_mul_of_nonneg_right hscaled
            (Nat.cast_nonneg (Pnon.card))
          calc
            _ ≤ 2 * Real.sqrt ((pointsOn X Q).card : ℝ) * Pnon.card +
                D * m * ((pointsOn X Q).card : ℝ) / H := hfixed Q hQ
            _ ≤ 2 * (((pointsOn X Q).card : ℝ) / Real.sqrt H) * Pnon.card +
                D * m * ((pointsOn X Q).card : ℝ) / H :=
                  add_le_add hlowTerm le_rfl
            _ = 2 * (Pnon.card : ℝ) / Real.sqrt H *
                ((pointsOn X Q).card : ℝ) +
                  D * m / H * ((pointsOn X Q).card : ℝ) := by ring
        have hsumFixed : (planePairEnergy X Pnon : ℝ) ≤
            ∑ Q ∈ Pnon,
              (2 * (Pnon.card : ℝ) / Real.sqrt H *
                  ((pointsOn X Q).card : ℝ) +
                D * m / H * ((pointsOn X Q).card : ℝ)) := by
          calc
            (planePairEnergy X Pnon : ℝ) =
                ∑ Q ∈ Pnon, ∑ Q' ∈ Pnon,
                  if Q ≠ Q' then ((planePairPoints X Q Q').card : ℝ) else 0 :=
                    planePairEnergy_sum_filter X Pnon
            _ ≤ _ := Finset.sum_le_sum hterm
        calc
          (planePairEnergy X Pnon : ℝ) ≤ _ := hsumFixed
          _ = (2 * (Pnon.card : ℝ) / Real.sqrt H) * I + (D * m / H) * I := by
            rw [Finset.sum_add_distrib]
            change
              (∑ Q ∈ Pnon,
                2 * (Pnon.card : ℝ) / Real.sqrt H * ((pointsOn X Q).card : ℝ)) +
              (∑ Q ∈ Pnon, D * m / H * ((pointsOn X Q).card : ℝ)) =
              (2 * (Pnon.card : ℝ) / Real.sqrt H) *
                (∑ Q ∈ Pnon, ((pointsOn X Q).card : ℝ)) +
              (D * m / H) * (∑ Q ∈ Pnon, ((pointsOn X Q).card : ℝ))
            rw [Finset.mul_sum, Finset.mul_sum]
          _ = 2 * fNon * I / Real.sqrt H + D * m * I / H := by
            simp [fNon]
            ring
      obtain ⟨Q₀, hQ₀⟩ := hPnonEmpty
      have hXnon : X.Nonempty := by
        have hOccPos : 0 < (pointsOn X Q₀).card := by
          by_contra hnot
          have hz : (pointsOn X Q₀).card = 0 := by omega
          have hreal : (0 : ℝ) < (pointsOn X Q₀).card :=
            lt_of_lt_of_le hHpos (hPnonOcc Q₀ hQ₀).1
          rw [hz] at hreal
          norm_num at hreal
        have hplaneNon : (pointsOn X Q₀).Nonempty := Finset.card_pos.mp hOccPos
        have hsub : pointsOn X Q₀ ⊆ X := by
          intro x hx
          exact (Finset.mem_filter.mp hx).1
        exact hplaneNon.mono hsub
      have hpairLower := plane_pair_energy_lower_variable X Pnon m hmpos hXm hXnon
      have hIpos : 0 < I := by
        have hfpos : 0 < fNon := by
          dsimp [fNon]
          have hcardPos : 0 < Pnon.card := Finset.card_pos.mpr ⟨Q₀, hQ₀⟩
          exact Nat.cast_pos.mpr hcardPos
        have : 0 < H * fNon := mul_pos hHpos hfpos
        linarith [hIlo]
      have hdiv : I / m - 1 ≤
          2 * fNon / Real.sqrt H + D * m / H := by
        apply (mul_le_mul_iff_of_pos_right hIpos).1
        calc
          (I / m - 1) * I = I ^ 2 / m - I := by ring
          _ ≤ 2 * fNon * I / Real.sqrt H + D * m * I / H :=
            hpairLower.trans hpairUpper
          _ = (2 * fNon / Real.sqrt H + D * m / H) * I := by ring
      have hincDiv : H * fNon / m - 1 ≤ I / m - 1 := by
        have h := div_le_div_of_nonneg_right hIlo hmpos.le
        have h' : H * fNon / m ≤ I / m := by simpa using h
        exact sub_le_sub_right h' 1
      have hmain : (H / m - 2 / Real.sqrt H) * fNon ≤ 1 + D * m / H := by
        have hfactor : (H / m - 2 / Real.sqrt H) * fNon =
            H * fNon / m - 2 * fNon / Real.sqrt H := by ring
        rw [hfactor]
        linarith [hdiv, hincDiv]
      have hu3 : (m ^ ((2 : ℝ) / 3)) ^ 3 = m ^ 2 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (le_of_lt hmpos)]
        norm_num
      have hHcube : 16 * m ^ 2 ≤ H ^ 3 := by
        have hbase : (8 * m ^ ((2 : ℝ) / 3)) ^ 3 ≤ H ^ 3 := by gcongr
        rw [show (8 * m ^ ((2 : ℝ) / 3)) ^ 3 =
          512 * m ^ 2 by rw [mul_pow, hu3]; ring] at hbase
        nlinarith [hbase]
      have hHsqrt : 4 * m ≤ H * Real.sqrt H := by
        have hsquare : (H * Real.sqrt H) ^ 2 = H ^ 3 := by
          rw [mul_pow, Real.sq_sqrt hHpos.le]
          ring
        have hnonneg : 0 ≤ H * Real.sqrt H := mul_nonneg hHpos.le (Real.sqrt_nonneg _)
        nlinarith [hHcube, hsquare]
      have hcoef : H / (2 * m) ≤ H / m - 2 / Real.sqrt H := by
        have hspos : 0 < Real.sqrt H := Real.sqrt_pos.2 hHpos
        have hm2pos : 0 < 2 * m := by positivity
        have hfrac : 2 / Real.sqrt H ≤ H / (2 * m) := by
          apply (div_le_iff₀ hspos).2
          calc
            2 ≤ H * Real.sqrt H / (2 * m) :=
              (le_div_iff₀ hm2pos).2 (by nlinarith [hHsqrt])
            _ = H / (2 * m) * Real.sqrt H := by ring
        have hratio : H / m = 2 * (H / (2 * m)) := by field_simp [ne_of_gt hmpos] <;> ring
        rw [hratio]
        linarith [hfrac]
      have hcoefUpper : H / (2 * m) * fNon ≤ 1 + D * m / H := by
        calc
          H / (2 * m) * fNon ≤ (H / m - 2 / Real.sqrt H) * fNon :=
            mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
          _ ≤ 1 + D * m / H := hmain
      have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
      have hmOverH : 1 ≤ m / H := by
        rw [le_div_iff₀ hHpos]
        nlinarith [hHm]
      have hcoefUpper' : H / (2 * m) * fNon ≤ (1 + D) * (m / H) := by
        calc
          H / (2 * m) * fNon ≤ 1 + D * m / H := hcoefUpper
          _ ≤ m / H + D * m / H := by linarith [hmOverH]
          _ = (1 + D) * (m / H) := by ring
      have hNnon : fNon ≤ 2 * (1 + D) * m ^ 2 / H ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hHpos)).2
        have hcross := mul_le_mul_of_nonneg_right hcoefUpper'
          (by positivity : 0 ≤ 2 * m * H)
        have hcross' : fNon * H ^ 2 ≤ 2 * (1 + D) * m ^ 2 := by
          convert hcross using 1 <;> field_simp [ne_of_gt hmpos, ne_of_gt hHpos] <;> ring
        exact hcross'
      have htotal : (Pdom.card : ℝ) + (Pnon.card : ℝ) ≤ K₂ * m ^ 2 / H ^ 2 := by
        calc
          (Pdom.card : ℝ) + (Pnon.card : ℝ) ≤
              68 * Cr * m ^ 2 / H ^ 2 + 2 * (1 + D) * m ^ 2 / H ^ 2 :=
                add_le_add hDdom (by simpa [fNon] using hNnon)
          _ = K₂ * m ^ 2 / H ^ 2 := by dsimp [K₂]; ring
      refine ⟨hSfinite, ?_⟩
      calc
        (S.ncard : ℝ) = (Pall.card : ℝ) := by
          simp [Pall, Set.ncard_eq_toFinset_card S hSfinite]
        _ = (Pdom.card : ℝ) + (Pnon.card : ℝ) := by exact_mod_cast hpartition.symm
        _ ≤ K₂ * m ^ 2 / H ^ 2 := htotal
    · have hPnonEq : Pnon = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPnonEmpty
      have htotal : (Pdom.card : ℝ) + (Pnon.card : ℝ) ≤ K₂ * m ^ 2 / H ^ 2 := by
        rw [hPnonEq]
        simp only [Finset.card_empty, Nat.cast_zero, add_zero]
        calc
          (Pdom.card : ℝ) ≤ 68 * Cr * m ^ 2 / H ^ 2 := hDdom
          _ ≤ (68 * Cr + 2 * (1 + D)) * m ^ 2 / H ^ 2 := by
            have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
            have hfactor : 68 * Cr ≤ 68 * Cr + 2 * (1 + D) := by nlinarith [hDnonneg]
            have h := mul_le_mul_of_nonneg_right hfactor
              (div_nonneg (sq_nonneg m) (sq_nonneg H))
            convert h using 1 <;> ring
          _ = K₂ * m ^ 2 / H ^ 2 := by dsimp [K₂]
      refine ⟨hSfinite, ?_⟩
      calc
        (S.ncard : ℝ) = (Pall.card : ℝ) := by
          simp [Pall, Set.ncard_eq_toFinset_card S hSfinite]
        _ = (Pdom.card : ℝ) + (Pnon.card : ℝ) := by exact_mod_cast hpartition.symm
        _ ≤ K₂ * m ^ 2 / H ^ 2 := htotal
  · have hMlt : m < H := lt_of_not_ge hHm
    have hSempty : S = ∅ := by
      ext Q
      simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · intro hQ
        have hEff : (effectiveSize X Q : ℝ) ≤ (pointsOn X Q).card := by
          exact_mod_cast (show effectiveSize X Q ≤ (pointsOn X Q).card by simp [effectiveSize])
        have hplaneSub : pointsOn X Q ⊆ X := by
          intro x hx
          exact (Finset.mem_filter.mp hx).1
        have hocc : (effectiveSize X Q : ℝ) ≤ m :=
          hEff.trans ((Nat.cast_le.mpr (Finset.card_le_card hplaneSub)).trans hXm)
        exact (not_le_of_gt hMlt) (hQ.trans hocc)
      · intro hfalse
        cases hfalse
    change FiniteCardBound S (K₂ * m ^ 2 / H ^ 2)
    constructor
    · rw [hSempty]
      exact Set.finite_empty
    · rw [hSempty]
      simp
      positivity

private theorem exists_noncollinear_triple_of_not_collinear (S : Finset (E 3))
    (hS : ¬ Collinear ℝ (S : Set (E 3))) :
    ∃ p₀ ∈ S, ∃ p₁ ∈ S, ∃ p₂ ∈ S, ¬ Collinear ℝ ({p₀, p₁, p₂} : Set (E 3)) := by
  classical
  have hne : S.Nonempty := by
    by_contra h
    have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hempty : Collinear ℝ (S : Set (E 3)) := by
      simpa [hzero] using (collinear_empty ℝ (E 3))
    exact hS hempty
  obtain ⟨p₀, hp₀⟩ := hne
  have hp₁ : ∃ p₁ ∈ S, p₁ ≠ p₀ := by
    by_contra h
    have hall : ∀ p ∈ S, p = p₀ := by
      intro p hp
      by_contra hpne
      exact h ⟨p, hp, hpne⟩
    apply hS
    rw [collinear_iff_of_mem hp₀]
    refine ⟨0, ?_⟩
    intro p hp
    rw [hall p hp]
    exact ⟨0, by simp⟩
  obtain ⟨p₁, hp₁S, hp₁ne⟩ := hp₁
  let L : AffineSubspace ℝ (E 3) := line[ℝ, p₀, p₁]
  have hp₂ : ∃ p₂ ∈ S, p₂ ∉ L := by
    by_contra h
    have hall : ∀ p ∈ S, p ∈ L := by
      intro p hp
      by_contra hpL
      exact h ⟨p, hp, hpL⟩
    apply hS
    rw [collinear_iff_of_mem hp₀]
    refine ⟨p₁ -ᵥ p₀, ?_⟩
    intro p hp
    obtain ⟨t, ht⟩ :=
      (mem_affineSpan_pair_iff_exists_lineMap_eq.mp (hall p hp))
    refine ⟨t, ?_⟩
    rw [AffineMap.lineMap_apply] at ht
    exact ht.symm
  obtain ⟨p₂, hp₂S, hp₂L⟩ := hp₂
  refine ⟨p₀, hp₀, p₁, hp₁S, p₂, hp₂S, ?_⟩
  rw [← affineIndependent_iff_not_collinear_set]
  exact affineIndependent_of_ne_of_mem_of_mem_of_notMem
    hp₁ne.symm (left_mem_affineSpan_pair ℝ p₀ p₁)
    (right_mem_affineSpan_pair ℝ p₀ p₁) hp₂L

private theorem finite_motions_with_triangle_images (a b c u v w : E 3)
    (habc : ¬ Collinear ℝ ({a, b, c} : Set (E 3))) :
    FiniteCardBound {g : Motion 3 | g a = u ∧ g b = v ∧ g c = w} 2 := by
  classical
  let src : Fin 3 → E 3 := ![a, b, c]
  have hsrc : AffineIndependent ℝ src := by
    apply affineIndependent_iff_not_collinear_set.mpr
    simpa [src] using habc
  let tri : Affine.Simplex ℝ (E 3) 2 := ⟨src, hsrc⟩
  let A : AffineSubspace ℝ (E 3) := affineSpan ℝ (Set.range tri.points)
  have hAdim : Module.finrank ℝ A.direction = 2 := by
    exact (Affine.Simplex.fact_finrank_direction_affineSpan_eq (s := tri)).out
  have hAorthdim : Module.finrank ℝ A.directionᗮ = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal A.direction
    rw [hAdim, finrank_euclideanSpace_fin] at hsum
    omega
  have hAorthpos : 0 < Module.finrank ℝ A.directionᗮ := by
    rw [hAorthdim]
    norm_num
  obtain ⟨z, hz⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := A.directionᗮ)).mp hAorthpos
  have hzE : (z : E 3) ≠ 0 := by
    intro hz0
    apply hz
    exact Subtype.ext hz0
  have hzorth : (z : E 3) ∈ A.directionᗮ := z.property
  let q : E 3 := (z : E 3) +ᵥ tri.circumcenter
  have hcenter : tri.circumcenter ∈ A := by
    simpa [A, tri] using tri.circumcenter_mem_affineSpan
  have hznotdir : (z : E 3) ∉ A.direction := by
    intro hzdirection
    have hmem : (z : E 3) ∈ A.direction ⊓ A.directionᗮ := ⟨hzdirection, hzorth⟩
    have hbot : (z : E 3) ∈ (⊥ : Submodule ℝ (E 3)) := by
      rw [← (Submodule.orthogonal_disjoint A.direction).eq_bot]
      exact hmem
    exact hzE (by simpa only [Submodule.mem_bot] using hbot)
  have hqv : q -ᵥ tri.circumcenter = (z : E 3) := by
    simp [q]
  have hqnotdir : q -ᵥ tri.circumcenter ∉ A.direction := by
    rw [hqv]
    exact hznotdir
  let A4 : AffineSubspace ℝ (E 3) := affineSpan ℝ (insert q (A : Set (E 3)))
  let D : Submodule ℝ (E 3) :=
    A.direction ⊔ (Submodule.span ℝ ({q -ᵥ tri.circumcenter} : Set (E 3)))
  have hA4direction : A4.direction = D := by
    change (affineSpan ℝ (insert q (A : Set (E 3)))).direction =
      A.direction ⊔ Submodule.span ℝ ({q -ᵥ tri.circumcenter} : Set (E 3))
    rw [AffineSubspace.direction_affineSpan_insert hcenter, sup_comm]
  have hA4dim : Module.finrank ℝ A4.direction = 3 := by
    calc
      Module.finrank ℝ A4.direction = Module.finrank ℝ D := by rw [hA4direction]
      _ = Module.finrank ℝ A.direction + 1 :=
        Submodule.finrank_sup_span_singleton hqnotdir
      _ = 3 := by norm_num [hAdim]
  have hA4dir : A4.direction = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [E] using hA4dim
  have hA4ne : (A4 : Set (E 3)).Nonempty := by
    exact ⟨q, mem_affineSpan ℝ (Set.mem_insert _ _)⟩
  have hA4top : A4 = ⊤ := (AffineSubspace.direction_eq_top_iff_of_nonempty hA4ne).mp hA4dir
  have hspan4 : affineSpan ℝ (insert q (Set.range tri.points)) = ⊤ := by
    rw [← affineSpan_insert_affineSpan ℝ q (Set.range tri.points)]
    simpa [A4, A] using hA4top
  have hqdist : ∃ r : ℝ, ∀ i : Fin 3, dist q (tri.points i) = r := by
    refine ⟨dist q (tri.points 0), fun i => ?_⟩
    have hsquare (j : Fin 3) :
        dist q (tri.points j) * dist q (tri.points j) =
          tri.circumradius * tri.circumradius + ‖(z : E 3)‖ * ‖(z : E 3)‖ := by
      have h := EuclideanGeometry.dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd
        (tri.circumcenter_mem_affineSpan) (mem_affineSpan ℝ (Set.mem_range_self j))
        (1 : ℝ) 0 hzorth
      simpa [q, tri.dist_circumcenter_eq_circumradius, dist_comm] using h
    exact (mul_self_inj_of_nonneg dist_nonneg dist_nonneg).1
      ((hsquare i).trans (hsquare 0).symm)
  let F : Set (Motion 3) := {g | g a = u ∧ g b = v ∧ g c = w}
  change F.Finite ∧ (F.ncard : ℝ) ≤ 2
  by_cases hF : F.Nonempty
  · obtain ⟨g₀, hg₀⟩ := hF
    let tri' : Affine.Simplex ℝ (E 3) 2 :=
      tri.map g₀.toAffineEquiv.toAffineMap g₀.toAffineEquiv.injective
    have himage : (g₀.toAffineEquiv : E 3 → E 3) '' insert q (Set.range tri.points) =
        insert (g₀ q) (Set.range tri'.points) := by
      ext y
      simp [tri', Affine.Simplex.map]
    have hspan' : affineSpan ℝ (insert (g₀ q) (Set.range tri'.points)) = ⊤ := by
      have hmap := AffineSubspace.map_span g₀.toAffineEquiv.toAffineMap
        (insert q (Set.range tri.points))
      rw [hspan4,
        AffineMap.map_top_of_surjective g₀.toAffineEquiv.toAffineMap
          g₀.toAffineEquiv.surjective] at hmap
      change ⊤ = affineSpan ℝ
        ((g₀.toAffineEquiv : E 3 → E 3) '' insert q (Set.range tri.points)) at hmap
      rw [himage] at hmap
      exact hmap.symm
    have hEvalInj : Set.InjOn (fun g : Motion 3 => g q) F := by
      intro g hg h hh heval
      apply AffineIsometryEquiv.toAffineEquiv_injective
      apply AffineEquiv.ext_on hspan4 g.toAffineEquiv h.toAffineEquiv
      intro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact heval
      · obtain ⟨i, rfl⟩ := Set.mem_range.mp hy
        fin_cases i
        · exact hg.1.trans hh.1.symm
        · exact hg.2.1.trans hh.2.1.symm
        · exact hg.2.2.trans hh.2.2.symm
    have hImageSubset : (fun g : Motion 3 => g q) '' F ⊆
        {g₀ q, EuclideanGeometry.reflection (affineSpan ℝ (Set.range tri'.points)) (g₀ q)} := by
      rintro y ⟨g, hg, rfl⟩
      obtain ⟨r, hr⟩ := hqdist
      have hmatch (i : Fin 3) : g (tri.points i) = g₀ (tri.points i) := by
        fin_cases i
        · simpa [tri, src] using hg.1.trans hg₀.1.symm
        · simpa [tri, src] using hg.2.1.trans hg₀.2.1.symm
        · simpa [tri, src] using hg.2.2.trans hg₀.2.2.symm
      have h₀dist : ∀ i : Fin 3, dist (tri'.points i) (g₀ q) = r := by
        intro i
        change dist (g₀ (tri.points i)) (g₀ q) = r
        rw [AffineIsometryEquiv.dist_map, dist_comm]
        exact hr i
      have hdist : ∀ i : Fin 3, dist (tri'.points i) (g q) = r := by
        intro i
        change dist (g₀ (tri.points i)) (g q) = r
        rw [← hmatch i, AffineIsometryEquiv.dist_map, dist_comm]
        exact hr i
      have hp₀ : g₀ q ∈ affineSpan ℝ (insert (g₀ q) (Set.range tri'.points)) :=
        mem_affineSpan ℝ (Set.mem_insert _ _)
      have hp : g q ∈ affineSpan ℝ (insert (g₀ q) (Set.range tri'.points)) := by
        rw [hspan']
        exact Set.mem_univ _
      rcases EuclideanGeometry.eq_or_eq_reflection_of_dist_eq
          (s := tri') (p := g₀ q) hp₀ hp h₀dist hdist with heq | heq
      · exact Or.inl heq.symm
      · right
        have := congrArg (EuclideanGeometry.reflection (affineSpan ℝ (Set.range tri'.points))) heq
        simpa using this.symm
    have hPairFinite :
        ({g₀ q, EuclideanGeometry.reflection (affineSpan ℝ (Set.range tri'.points)) (g₀ q)} :
          Set (E 3)).Finite := by simp
    have hImageFinite : ((fun g : Motion 3 => g q) '' F).Finite := hPairFinite.subset hImageSubset
    have hFfinite : F.Finite := hImageFinite.of_finite_image hEvalInj
    have hFbound : (F.ncard : ℝ) ≤ 2 := by
      calc
        (F.ncard : ℝ) = (((fun g : Motion 3 => g q) '' F).ncard : ℝ) := by
          rw [hEvalInj.ncard_image]
        _ ≤ ((({g₀ q,
          EuclideanGeometry.reflection (affineSpan ℝ (Set.range tri'.points)) (g₀ q)} :
            Set (E 3)).ncard : ℝ)) := by
          exact_mod_cast Set.ncard_le_ncard hImageSubset hPairFinite
        _ ≤ 2 := by
          simpa using (Set.ncard_insert_le (g₀ q)
            ({EuclideanGeometry.reflection (affineSpan ℝ (Set.range tri'.points)) (g₀ q)} :
              Set (E 3)))
    exact ⟨hFfinite, hFbound⟩
  · have hFempty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    constructor
    · rw [hFempty]
      exact Set.finite_empty
    · rw [hFempty]
      simp

/-- Finite noncollinear match lists, motions.tex:247–251, 833–839. -/
theorem spatial_motions_finite (X Y : Finset (E 3)) :
    {g : Motion 3 | ¬ Collinear ℝ (matchPoints X Y g : Set (E 3))}.Finite := by
  classical
  let XT := {x : E 3 // x ∈ X}
  let YT := {y : E 3 // y ∈ Y}
  letI : Fintype XT := X.finite_toSet.fintype
  letI : Fintype YT := Y.finite_toSet.fintype
  let T := (Fin 3 → XT) × (Fin 3 → YT)
  let source : T → Fin 3 → E 3 := fun t i => (t.1 i).1
  let target : T → Fin 3 → E 3 := fun t i => (t.2 i).1
  let I : Set T := {t | ¬ Collinear ℝ ({source t 0, source t 1, source t 2} : Set (E 3))}
  have hI : I.Finite := Set.toFinite I
  letI : Fintype I := hI.fintype
  let fiber : T → Set (Motion 3) := fun t =>
    {g | ∀ i : Fin 3, g (source t i) = target t i}
  have hFiber (i : I) : (fiber i.1).Finite := by
    let a := source i.1 0
    let b := source i.1 1
    let c := source i.1 2
    let u := target i.1 0
    let v := target i.1 1
    let w := target i.1 2
    have heq : fiber i.1 = {g | g a = u ∧ g b = v ∧ g c = w} := by
      ext g
      simp only [fiber, Set.mem_setOf_eq]
      constructor
      · intro hg
        exact ⟨hg 0, hg 1, hg 2⟩
      · rintro ⟨h₀, h₁, h₂⟩ j
        fin_cases j
        · exact h₀
        · exact h₁
        · exact h₂
    rw [heq]
    exact (finite_motions_with_triangle_images a b c u v w i.2).1
  have hUnion : (⋃ i : I, fiber i.1).Finite :=
    Set.finite_iUnion (fun i => hFiber i)
  refine hUnion.subset ?_
  intro g hg
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, htri⟩ :=
    exists_noncollinear_triple_of_not_collinear (matchPoints X Y g) hg
  have hparts₀ : x₀ ∈ X ∧ g x₀ ∈ Y := by simpa [matchPoints] using hx₀
  have hparts₁ : x₁ ∈ X ∧ g x₁ ∈ Y := by simpa [matchPoints] using hx₁
  have hparts₂ : x₂ ∈ X ∧ g x₂ ∈ Y := by simpa [matchPoints] using hx₂
  let sx : Fin 3 → XT := ![⟨x₀, hparts₀.1⟩, ⟨x₁, hparts₁.1⟩, ⟨x₂, hparts₂.1⟩]
  let ty : Fin 3 → YT := ![⟨g x₀, hparts₀.2⟩, ⟨g x₁, hparts₁.2⟩, ⟨g x₂, hparts₂.2⟩]
  let i : T := (sx, ty)
  have hi : i ∈ I := by
    change ¬ Collinear ℝ ({source i 0, source i 1, source i 2} : Set (E 3))
    simpa [source, i, sx] using htri
  have hgi : g ∈ fiber i := by
    simp only [fiber, Set.mem_setOf_eq]
    intro j
    fin_cases j <;> simp [source, target, i, sx, ty]
  exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hgi⟩

/-- Elementary line cap, motions.tex:35–43. -/
theorem physical_line_cap (X : Finset (E 3)) :
    cloudLineCap X (1 + 2 * (positiveDistances X).card) := by
  classical
  intro l
  let T := pointsOn X l
  by_cases hT : T.Nonempty
  · obtain ⟨p, hpT⟩ := hT
    let V : Submodule ℝ (E 3) := l.1.direction
    have hV : Module.finrank ℝ V = 1 := l.2.2
    have hVpos : 0 < Module.finrank ℝ V := by rw [hV]; norm_num
    obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := V)).mp hVpos
    have hvE : (v : E 3) ≠ 0 := by
      intro h
      apply hv
      exact Subtype.ext h
    have hpLine : p ∈ l.1 := by
      have h := hpT
      simp only [T, pointsOn, Finset.mem_filter] at h
      exact h.2
    have hpX : p ∈ X := by
      have h := hpT
      simp only [T, pointsOn, Finset.mem_filter] at h
      exact h.1
    have hcoord (q : E 3) (hq : q ∈ l.1) :
        ∃ t : ℝ, q = p + t • (v : E 3) := by
      have hsub : q - p ∈ V := by
        exact AffineSubspace.vsub_mem_direction hq hpLine
      obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hV hv ⟨q - p, hsub⟩
      refine ⟨t, ?_⟩
      have ht' : t • (v : E 3) = q - p := congrArg Subtype.val ht
      calc
        q = p + (q - p) := by abel
        _ = p + t • (v : E 3) := by rw [← ht']
    let S := T.filter (fun q => q ≠ p)
    have hpnotS : p ∉ S := by simp [S]
    have hTinsert : T = insert p S := by
      ext q
      simp only [S, Finset.mem_filter, Finset.mem_insert]
      constructor
      · intro hq
        by_cases hqp : q = p
        · exact Or.inl hqp
        · exact Or.inr ⟨hq, hqp⟩
      · rintro (rfl | ⟨hq, _⟩)
        · exact hpT
        · exact hq
    have hline (q : ↥S) : q.1 ∈ l.1 := by
      have hq := q.2
      simp only [S, Finset.mem_filter, T, pointsOn, Finset.mem_filter] at hq
      exact hq.1.2
    have hxinX (q : ↥S) : q.1 ∈ X := by
      have hq := q.2
      simp only [S, Finset.mem_filter, T, pointsOn, Finset.mem_filter] at hq
      exact hq.1.1
    let t (q : ↥S) : ℝ := Classical.choose (hcoord q.1 (hline q))
    have ht (q : ↥S) : q.1 = p + t q • (v : E 3) :=
      Classical.choose_spec (hcoord q.1 (hline q))
    have hdistmem (q : ↥S) : dist p q.1 ∈ positiveDistances X := by
      rw [positiveDistances]
      apply Finset.mem_image.mpr
      refine ⟨(p, q.1), Finset.mem_offDiag.mpr ⟨hpX, hxinX q, ?_⟩, rfl⟩
      intro h
      have hq := q.2
      simp only [S, Finset.mem_filter] at hq
      exact hq.2 h.symm
    have hvnorm : 0 < ‖(v : E 3)‖ := norm_pos_iff.mpr hvE
    have hdistcoord (q : ↥S) :
        dist p q.1 = |t q| * ‖(v : E 3)‖ := by
      rw [ht q, dist_eq_norm]
      simp [norm_smul, Real.norm_eq_abs]
    let f (q : ↥S) : ℝ × Bool :=
      (dist p q.1, decide (t q < 0))
    have hinj : Function.Injective f := by
      intro q r hqr
      apply Subtype.ext
      have hdist : dist p q.1 = dist p r.1 := congrArg Prod.fst hqr
      have hside : decide (t q < 0) = decide (t r < 0) := congrArg Prod.snd hqr
      have hnegiff : (t q < 0) ↔ (t r < 0) := by
        constructor
        · intro hq
          have hq' : decide (t q < 0) = true := decide_eq_true_eq.mpr hq
          rw [hside] at hq'
          exact decide_eq_true_eq.mp hq'
        · intro hr
          have hr' : decide (t r < 0) = true := decide_eq_true_eq.mpr hr
          rw [← hside] at hr'
          exact decide_eq_true_eq.mp hr'
      have habs : |t q| = |t r| := by
        rw [hdistcoord q, hdistcoord r] at hdist
        exact (mul_right_cancel₀ hvnorm.ne') hdist
      rcases abs_eq_abs.mp habs with hteq | hteq
      · calc
          q.1 = p + t q • (v : E 3) := ht q
          _ = p + t r • (v : E 3) := by rw [hteq]
          _ = r.1 := (ht r).symm
      · by_cases hqneg : t q < 0
        · have hrneg := hnegiff.mp hqneg
          rw [hteq] at hqneg
          linarith
        · have hqnonneg : 0 ≤ t q := le_of_not_gt hqneg
          have hrnonneg : 0 ≤ t r := le_of_not_gt (fun hr => hqneg (hnegiff.mpr hr))
          rw [hteq] at hqnonneg
          have htrzero : t r = 0 := by linarith
          have hcoordEq : t q = t r := by rw [htrzero] at hteq; linarith
          calc
            q.1 = p + t q • (v : E 3) := ht q
            _ = p + t r • (v : E 3) := by rw [hcoordEq]
            _ = r.1 := (ht r).symm
    let target := positiveDistances X ×ˢ (Finset.univ : Finset Bool)
    have himage : S.attach.image f ⊆ target := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
      exact Finset.mem_product.mpr ⟨hdistmem q, Finset.mem_univ _⟩
    have hScard : S.card ≤ 2 * (positiveDistances X).card := by
      have hcard := Finset.card_image_of_injective S.attach hinj
      rw [Finset.card_attach] at hcard
      calc
        S.card = (S.attach.image f).card := hcard.symm
        _ ≤ target.card := Finset.card_le_card himage
        _ = 2 * (positiveDistances X).card := by simp [target, Nat.mul_comm]
    have hTcard : T.card ≤ 1 + 2 * (positiveDistances X).card := by
      rw [hTinsert, Finset.card_insert_of_notMem hpnotS]
      omega
    exact_mod_cast hTcard
  · have hzero : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [T, hzero]
    positivity

/-- Generic reversing chart and nonvertical triples, motions.tex:253–277. -/
theorem spatial_generic_rotation (X Y : Finset (E 3)) (G : Finset (Motion 3))
    (hG : ∀ g ∈ G, reverseMotion g) :
    ∃ R : E 3 ≃ₗᵢ[ℝ] E 3,
      LinearMap.det R.toLinearEquiv.toLinearMap = 1 ∧
      ∀ g ∈ G, let g' := g.trans R.toAffineIsometryEquiv
        Module.finrank ℝ (axis g') = 1 ∧ axisAvoidsTriples g' (matchPoints X (Y.image R) g') := by
  let triples := X ×ˢ (X ×ˢ X)
  let normal : E 3 × (E 3 × E 3) → E 3 := fun xyz =>
    (triple_direction_normal xyz.1 xyz.2.1 xyz.2.2).choose
  let e : E 3 := EuclideanSpace.single (0:Fin 3) 1
  have he : e ≠ 0 := by
    intro hz
    have h := congrArg (fun v : E 3 => v 0) hz
    simpa [e] using h
  let N := insert e (triples.image normal)
  have hN : ∀ g ∈ G,∀ n ∈ N,n ≠ 0 := by
    intro g hg n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact he
    · obtain ⟨xyz,hxyz,rfl⟩ := Finset.mem_image.mp hn
      exact (triple_direction_normal xyz.1 xyz.2.1 xyz.2.2).choose_spec.1
  have hS : ∀ g ∈ G,LinearMap.det g.linearIsometryEquiv.toLinearMap = -1 := by
    intro g hg
    simpa only [reverseMotion,g.linear_eq_linear_isometry] using hG g hg
  obtain ⟨R,hR,havoid⟩ := finite_spatial_rotation_normals G (fun g => g.linearIsometryEquiv) (fun _ => N)
    hS hN (fun g hg => ⟨e,Finset.mem_insert_self _ _⟩)
  refine ⟨R,hR,?_⟩
  intro g hg
  dsimp only
  refine ⟨?_,?_⟩
  · change Module.finrank ℝ (LinearMap.ker ((g.linearIsometryEquiv.trans R).toLinearMap+LinearMap.id)) = 1
    exact (havoid g hg).1
  · intro x hx y hy z hz hnoncol
    have hxX := (Finset.mem_filter.mp hx).1
    have hyX := (Finset.mem_filter.mp hy).1
    have hzX := (Finset.mem_filter.mp hz).1
    let n := normal (x,(y,z))
    have hn : n ∈ N := Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨(x,(y,z)),Finset.mem_product.mpr ⟨hxX,Finset.mem_product.mpr ⟨hyX,hzX⟩⟩,rfl⟩)
    have hV : vectorSpan ℝ ({x,y,z}:Set (E 3)) ≤ LinearMap.ker (spatialNormalFunctional n) :=
      (triple_direction_normal x y z).choose_spec.2
    change LinearMap.ker ((g.linearIsometryEquiv.trans R).toLinearMap+LinearMap.id) ⊓
      vectorSpan ℝ ({x,y,z}:Set (E 3)) = ⊥
    apply le_antisymm _ bot_le
    calc
      _ ≤ LinearMap.ker ((g.linearIsometryEquiv.trans R).toLinearMap+LinearMap.id) ⊓
          LinearMap.ker (spatialNormalFunctional n) := inf_le_inf le_rfl hV
      _ = ⊥ := (havoid g hg).2 n hn

/-- Motion flats, graph duality and all three distinctness assertions,
motions.tex:298–372. -/
theorem normalized_motion_flats (X Y : Finset (E 3)) (G : Finset (Motion 3))
    (hG : ∀ g ∈ G, reverseMotion g ∧ Module.finrank ℝ (axis g) = 1 ∧
      axisAvoidsTriples g (matchPoints X Y g)) :
    ∃ F : Motion 3 → Flat 6 3,
      Set.InjOn F (G : Set (Motion 3)) ∧
      (∀ g ∈ G, MotionFlatModel g (matchPoints X Y g) (F g)) ∧
      (∀ x ∈ X, ∀ y ∈ Y, ∀ g ∈ G, ∀ g' ∈ G,
        g x = y → g' x = y → g ≠ g' →
          pairFlatSet x y ∩ ((F g).1 : Set (E 6)) ≠
            pairFlatSet x y ∩ ((F g').1 : Set (E 6))) := by
  exact normalized_motion_flats_construct X Y G hG

/-- Bipartite pruning, motions.tex:379–391. -/
theorem bipartite_pruning {α β : Type*} (A : Finset α) (B : Finset β)
    (edges : Finset (α × β)) (hne : edges.Nonempty)
    (hsub : ∀ ab ∈ edges, ab.1 ∈ A ∧ ab.2 ∈ B) :
    ∃ E' : Finset (α × β), E' ⊆ edges ∧ E'.Nonempty ∧
      ∀ ab ∈ E',
        (edges.card : ℝ) / (4 * A.card) ≤ (E'.filter (fun e => e.1 = ab.1)).card ∧
        (edges.card : ℝ) / (4 * B.card) ≤ (E'.filter (fun e => e.2 = ab.2)).card := by
  classical
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq β := Classical.decEq β
  obtain ⟨ab₀, hab₀⟩ := hne
  have hApos : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨ab₀.1, (hsub ab₀ hab₀).1⟩)
  have hBpos : 0 < (B.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨ab₀.2, (hsub ab₀ hab₀).2⟩)
  let q : ℝ := edges.card
  let qA : ℝ := q / (4 * A.card)
  let qB : ℝ := q / (4 * B.card)
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨ab₀, hab₀⟩)
  have hqApos : 0 < qA := by
    dsimp [qA]
    positivity
  have hqBpos : 0 < qB := by
    dsimp [qB]
    positivity
  let VL : Finset (Sum α β) := A.image Sum.inl
  let VR : Finset (Sum α β) := B.image Sum.inr
  let V : Finset (Sum α β) := VL ∪ VR
  let w : Sum α β → ℝ := Sum.elim (fun _ => qA) (fun _ => qB)
  let induced (U : Finset (Sum α β)) : Finset (α × β) :=
    edges.filter (fun e => Sum.inl e.1 ∈ U ∧ Sum.inr e.2 ∈ U)
  let potential (U : Finset (Sum α β)) : ℝ :=
    (induced U).card - ∑ v ∈ U, w v
  have hdisj : Disjoint VL VR := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    rcases Finset.mem_image.mp hvL with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hvR with ⟨b, hb, heq⟩
    simp at heq
  have hsumL : (∑ v ∈ VL, w v) = q / 4 := by
    calc
      (∑ v ∈ VL, w v) = ∑ a ∈ A, w (Sum.inl a) := by
        dsimp [VL]
        rw [Finset.sum_image (fun a ha b hb hab => Sum.inl.inj hab)]
      _ = q / 4 := by
        simp only [w, Sum.elim_inl]
        simp only [Finset.sum_const, nsmul_eq_mul]
        dsimp [qA]
        field_simp [hApos.ne'] <;> ring
  have hsumR : (∑ v ∈ VR, w v) = q / 4 := by
    calc
      (∑ v ∈ VR, w v) = ∑ b ∈ B, w (Sum.inr b) := by
        dsimp [VR]
        rw [Finset.sum_image (fun a ha b hb hab => Sum.inr.inj hab)]
      _ = q / 4 := by
        simp only [w, Sum.elim_inr]
        simp only [Finset.sum_const, nsmul_eq_mul]
        dsimp [qB]
        field_simp [hBpos.ne'] <;> ring
  have hsumV : (∑ v ∈ V, w v) = q / 2 := by
    calc
      (∑ v ∈ V, w v) = (∑ v ∈ VL, w v) + ∑ v ∈ VR, w v := by
        dsimp [V]
        rw [Finset.sum_union hdisj]
      _ = q / 2 := by rw [hsumL, hsumR]; ring
  have hinducedV : induced V = edges := by
    ext e
    constructor
    · intro he
      exact (Finset.mem_filter.mp he).1
    · intro he
      have he' := hsub e he
      apply Finset.mem_filter.mpr
      refine ⟨he, ?_⟩
      constructor
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨e.1, he'.1, rfl⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨e.2, he'.2, rfl⟩
  have hw_nonneg (v : Sum α β) : 0 ≤ w v := by
    cases v <;> simp [w] <;> positivity
  have hpotentialV : potential V = q / 2 := by
    dsimp [potential]
    rw [hinducedV, hsumV]
    dsimp [q]
    ring
  obtain ⟨U, hUmem, hUmax⟩ :=
    Finset.exists_max_image V.powerset potential (Finset.powerset_nonempty V)
  have hUsub : U ⊆ V := Finset.mem_powerset.mp hUmem
  let E' : Finset (α × β) := induced U
  have hmaxV : potential V ≤ potential U := hUmax V (Finset.mem_powerset_self V)
  have hpotUpos : 0 < potential U := lt_of_lt_of_le (by linarith [hqpos]) hmaxV
  have hpotle : potential U ≤ (E'.card : ℝ) := by
    dsimp [potential, E']
    have hs : 0 ≤ ∑ v ∈ U, w v := Finset.sum_nonneg fun v hv => hw_nonneg v
    linarith
  have hE'ne : E'.Nonempty := by
    by_contra h
    have hEzero : E' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hEzero] at hpotle
    linarith
  have hpartition (v : Sum α β) :
      (induced U).card = (induced (U.erase v)).card +
        ((induced U).filter (fun e => Sum.inl e.1 = v ∨ Sum.inr e.2 = v)).card := by
    have hunion : induced U = induced (U.erase v) ∪
        (induced U).filter (fun e => Sum.inl e.1 = v ∨ Sum.inr e.2 = v) := by
      ext e
      constructor
      · intro he
        rcases Finset.mem_filter.mp he with ⟨he, ⟨hleft, hright⟩⟩
        have heU : e ∈ induced U := Finset.mem_filter.mpr ⟨he, ⟨hleft, hright⟩⟩
        by_cases ht : Sum.inl e.1 = v ∨ Sum.inr e.2 = v
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heU, ht⟩)
        · apply Finset.mem_union_left
          apply Finset.mem_filter.mpr
          refine ⟨he, ?_⟩
          exact ⟨Finset.mem_erase.mpr ⟨(fun h => ht (Or.inl h)), hleft⟩,
            Finset.mem_erase.mpr ⟨(fun h => ht (Or.inr h)), hright⟩⟩
      · intro he
        rcases Finset.mem_union.mp he with hE | hE
        · rcases Finset.mem_filter.mp hE with ⟨he, ⟨hleft, hright⟩⟩
          exact Finset.mem_filter.mpr ⟨he, ⟨(Finset.mem_erase.mp hleft).2,
            (Finset.mem_erase.mp hright).2⟩⟩
        · exact (Finset.mem_filter.mp hE).1
    have hdisjoint : Disjoint (induced (U.erase v))
        ((induced U).filter (fun e => Sum.inl e.1 = v ∨ Sum.inr e.2 = v)) := by
      apply Finset.disjoint_left.mpr
      intro e heE heR
      rcases Finset.mem_filter.mp heE with ⟨he, ⟨hleft, hright⟩⟩
      rcases (Finset.mem_filter.mp heR).2 with h | h
      · exact (Finset.mem_erase.mp hleft).1 h
      · exact (Finset.mem_erase.mp hright).1 h
    have hcardEq := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisjoint] at hcardEq
    exact hcardEq
  have hpotentialErase (v : Sum α β) (hv : v ∈ U) :
      potential (U.erase v) = potential U + w v -
        ((induced U).filter (fun e => Sum.inl e.1 = v ∨ Sum.inr e.2 = v)).card := by
    have hcard := hpartition v
    have hsum := Finset.add_sum_erase U w hv
    have hcardR : ((induced U).card : ℝ) =
        ((induced (U.erase v)).card : ℝ) +
          (((induced U).filter (fun e => Sum.inl e.1 = v ∨ Sum.inr e.2 = v)).card : ℝ) := by
      exact_mod_cast hcard
    dsimp [potential]
    rw [← hsum, hcardR]
    ring
  have hleft (a : α) (ha : Sum.inl a ∈ U) :
      qA ≤ ((E'.filter (fun e => e.1 = a)).card : ℝ) := by
    by_contra hbad
    have hdeg : ((E'.filter (fun e => e.1 = a)).card : ℝ) < qA := lt_of_not_ge hbad
    have hincident : (induced U).filter
        (fun (e : α × β) => (Sum.inl e.1 : Sum α β) = Sum.inl a ∨
          (Sum.inr e.2 : Sum α β) = Sum.inl a) =
          E'.filter (fun e => e.1 = a) := by
      classical
      ext e
      simp [E', Sum.inl.injEq]
    have hchange : potential (U.erase (Sum.inl a)) =
        potential U + qA - (E'.filter (fun e => e.1 = a)).card := by
      rw [hpotentialErase (Sum.inl a) ha, hincident]
      simp [w]
    have hstrict : potential U < potential (U.erase (Sum.inl a)) := by
      rw [hchange]
      linarith
    have hmaxErase := hUmax (U.erase (Sum.inl a))
      (Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.erase_subset _ _) hUsub))
    linarith
  have hright (b : β) (hb : Sum.inr b ∈ U) :
      qB ≤ ((E'.filter (fun e => e.2 = b)).card : ℝ) := by
    by_contra hbad
    have hdeg : ((E'.filter (fun e => e.2 = b)).card : ℝ) < qB := lt_of_not_ge hbad
    have hincident : (induced U).filter
        (fun (e : α × β) => (Sum.inl e.1 : Sum α β) = Sum.inr b ∨
          (Sum.inr e.2 : Sum α β) = Sum.inr b) =
          E'.filter (fun e => e.2 = b) := by
      classical
      ext e
      simp [E', Sum.inr.injEq]
    have hchange : potential (U.erase (Sum.inr b)) =
        potential U + qB - (E'.filter (fun e => e.2 = b)).card := by
      rw [hpotentialErase (Sum.inr b) hb, hincident]
      simp [w]
    have hstrict : potential U < potential (U.erase (Sum.inr b)) := by
      rw [hchange]
      linarith
    have hmaxErase := hUmax (U.erase (Sum.inr b))
      (Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.erase_subset _ _) hUsub))
    linarith
  refine ⟨E', ?_, hE'ne, ?_⟩
  · intro e he
    exact (Finset.mem_filter.mp he).1
  · intro e he
    have he' := (Finset.mem_filter.mp he).2
    rcases hsub e (Finset.mem_filter.mp he).1 with ⟨heA, heB⟩
    exact ⟨hleft e.1 he'.1, hright e.2 he'.2⟩

/-- Two Beck applications and dual arrangement propagation,
motions.tex:425–473. -/
theorem dual_arrangement_derivatives : ∃ η₁ η₂ ε : ℝ,
    0 < η₁ ∧ 0 < η₂ ∧ 0 < ε ∧ η₁ ≤ η₂ / 100 ∧ η₂ < 1 ∧
    ∀ (g : Motion 3) (S : Finset (E 3)) (G : Flat 6 3) (f : Poly 6) (ℓ : ℝ),
      0 < ℓ → ℓ / 4 ≤ (S.card : ℝ) → (S.card : ℝ) < 2 * ℓ →
      (∀ l : Line 3, ((pointsOn S l).card : ℝ) < η₁ * ℓ) →
      (∀ H : Plane 3, ((pointsOn S H).card : ℝ) < η₂ * ℓ) →
      MotionFlatModel g S G → (f.totalDegree : ℝ) < ε * ℓ →
      onPolynomial f G → (∀ x ∈ S, ∀ z ∈ pairFlatSet x (g x), evalR f z = 0) →
      ∀ i : Fin 6, onPolynomial (MvPolynomial.pderiv i f) G := by
  obtain ⟨δ,γ,hδ,_,hγ,hBeck⟩ := mot_beck
  obtain ⟨δp,γp,hδp,_,hγp,hProj⟩ := mot_beck_projective
  refine dual_arrangement_construct δ γ δp γp hδ hγ hδp hγp ?_ ?_
  · intro S hS hcap
    exact (hBeck 3 S hS hcap).2.2
  · intro D hD hcap
    have h := hProj D hD hcap
    exact ⟨h.1,h.2.1⟩

/-- Characteristic-zero derivative descent, motions.tex:475–480. -/
theorem derivative_descent (n k D : ℕ) (H : Finset (Flat n k)) (hH : H.Nonempty)
    (hstable : ∀ f : Poly n, f.totalDegree ≤ D → (∀ h ∈ H, onPolynomial f h) →
      ∀ i : Fin n, ∀ h ∈ H, onPolynomial (MvPolynomial.pderiv i f) h) :
    ∀ f : Poly n, f.totalDegree ≤ D → (∀ h ∈ H, onPolynomial f h) → f = 0 := by
  classical
  have pderivDegreeLt (f : Poly n) (i : Fin n)
      (hder : MvPolynomial.pderiv i f ≠ 0) :
      (MvPolynomial.pderiv i f).totalDegree < f.totalDegree := by
    let g := MvPolynomial.pderiv i f
    have hterm (s : Fin n →₀ ℕ) (hs : s ∈ g.support) :
        (s.sum fun _ e => e) < f.totalDegree := by
      have hcoeff := MvPolynomial.mem_support_iff.mp hs
      rw [MvPolynomial.coeff_pderiv] at hcoeff
      have hcoeffF : f.coeff (s + Finsupp.single i 1) ≠ 0 := by
        by_contra hzero
        simp [hzero] at hcoeff
      have hsF : s + Finsupp.single i 1 ∈ f.support :=
        MvPolynomial.mem_support_iff.mpr hcoeffF
      have hsum : (s + Finsupp.single i 1).sum (fun _ e => e) =
          (s.sum fun _ e => e) + 1 := by
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
        simp
      have htotal := MvPolynomial.le_totalDegree hsF
      rw [hsum] at htotal
      omega
    have hbound : ∀ s ∈ g.support, (s.sum fun _ e => e) ≤ f.totalDegree - 1 := by
      intro s hs
      exact Nat.le_sub_one_of_lt (hterm s hs)
    have hdeg : g.totalDegree ≤ f.totalDegree - 1 := by
      change g.support.sup (fun s => s.sum fun _ e => e) ≤ _
      exact Finset.sup_le hbound
    have hpos : 0 < f.totalDegree := by
      obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hder
      have := hterm s hs
      omega
    have hdeg' : (MvPolynomial.pderiv i f).totalDegree ≤ f.totalDegree - 1 := by
      simpa [g] using hdeg
    omega
  have zeroPartialsDegreeZero (f : Poly n)
      (hzero : ∀ i : Fin n, MvPolynomial.pderiv i f = 0) : f.totalDegree = 0 := by
    by_contra hne
    have hpos : 0 < f.totalDegree := Nat.pos_of_ne_zero hne
    rw [MvPolynomial.totalDegree] at hpos
    have hfsupp : f.support.Nonempty := by
      by_contra h
      have hempty : f.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hf : f = 0 := MvPolynomial.support_eq_empty.mp hempty
      simp [hf] at hpos
    obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup f.support hfsupp
      (fun s => s.sum fun _ e => e)
    have hspos : 0 < s.sum (fun _ e => e) := by
      rw [← hsup]
      exact hpos
    have hsne : s ≠ 0 := by
      intro hs0
      simp [hs0] at hspos
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hsne
    have his : s i ≠ 0 := Finsupp.mem_support_iff.mp hi
    let m : Fin n →₀ ℕ := s - Finsupp.single i 1
    have hplus : m + Finsupp.single i 1 = s := Finsupp.sub_add_single_one_cancel his
    have hcoeffzero : (MvPolynomial.pderiv i f).coeff m = 0 := by
      rw [hzero i]
      simp
    rw [MvPolynomial.coeff_pderiv, hplus] at hcoeffzero
    have hcoeff : f.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hfactor : ((m i : ℝ) + 1) ≠ 0 := by positivity
    exact (mul_ne_zero hcoeff hfactor) hcoeffzero
  have main : ∀ d : ℕ, ∀ f : Poly n, f.totalDegree = d → d ≤ D →
      (∀ h ∈ H, onPolynomial f h) → f = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro f hdegree hd hvan
      have hfd : f.totalDegree ≤ D := by simpa [hdegree] using hd
      have hstablef := hstable f hfd hvan
      have hpartials : ∀ i : Fin n, MvPolynomial.pderiv i f = 0 := by
        intro i
        by_contra hzero
        have hne : MvPolynomial.pderiv i f ≠ 0 := hzero
        have hlt := pderivDegreeLt f i hne
        have hltD : (MvPolynomial.pderiv i f).totalDegree < d := by
          simpa [hdegree] using hlt
        have hD' : (MvPolynomial.pderiv i f).totalDegree ≤ D := by omega
        have hresult := ih (MvPolynomial.pderiv i f).totalDegree hltD
          (MvPolynomial.pderiv i f) rfl hD' (hstablef i)
        exact hzero hresult
      have hdegree0 := zeroPartialsDegreeZero f hpartials
      have hfC : f = MvPolynomial.C (f.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree0
      obtain ⟨h, hh⟩ := hH
      obtain ⟨x, hx⟩ := h.2.1
      have hfx : evalR f x = 0 := hvan h hh x hx
      rw [hfC] at hfx
      simp [evalR] at hfx
      rw [hfC, hfx]
      simp
  intro f hf hvan
  exact main f.totalDegree f rfl hf hvan

private def graphDualPlaneLinear (x : E 3) : E 2 →ₗ[ℝ] E 3 where
  toFun q := WithLp.toLp 2 ![q 0, q 1, -(q 0 * x 0 + q 1 * x 1)]
  map_add' u v := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r u := by
    ext i
    fin_cases i <;> simp <;> ring

private theorem graphDualPlaneLinear_injective (x : E 3) :
    Function.Injective (graphDualPlaneLinear x) := by
  intro u v huv
  ext i
  fin_cases i
  · have h := congrArg (fun z : E 3 => z 0) huv
    simpa [graphDualPlaneLinear] using h
  · have h := congrArg (fun z : E 3 => z 1) huv
    simpa [graphDualPlaneLinear] using h

private def graphDualPlaneSubspace (x : E 3) : AffineSubspace ℝ (E 3) :=
  AffineSubspace.mk' (WithLp.toLp 2 ![0, 0, x 2])
    (LinearMap.range (graphDualPlaneLinear x))

private theorem graphDualPlaneSubspace_coe (x : E 3) :
    (graphDualPlaneSubspace x : Set (E 3)) = graphDualPlane x := by
  classical
  let p : E 3 := WithLp.toLp 2 ![0, 0, x 2]
  ext u
  constructor
  · intro hu
    have hu' : u -ᵥ p ∈ LinearMap.range (graphDualPlaneLinear x) := by
      simpa [graphDualPlaneSubspace, p, AffineSubspace.mem_mk'] using hu
    obtain ⟨q, hq⟩ := LinearMap.mem_range.mp hu'
    have h0 : q 0 = u 0 := by
      have h := congrArg (fun z : E 3 => z 0) hq
      simpa [graphDualPlaneLinear, p, vsub_eq_sub] using h
    have h1 : q 1 = u 1 := by
      have h := congrArg (fun z : E 3 => z 1) hq
      simpa [graphDualPlaneLinear, p, vsub_eq_sub] using h
    have h2 : -(q 0 * x 0 + q 1 * x 1) = u 2 - x 2 := by
      have h := congrArg (fun z : E 3 => z 2) hq
      simpa [graphDualPlaneLinear, p, vsub_eq_sub] using h
    change u 2 + u 0 * x 0 + u 1 * x 1 = x 2
    rw [← h0, ← h1]
    linarith
  · intro hu
    change u 2 + u 0 * x 0 + u 1 * x 1 = x 2 at hu
    let q : E 2 := WithLp.toLp 2 ![u 0, u 1]
    have hq : graphDualPlaneLinear x q = u - p := by
      apply (WithLp.ext_iff 2).2
      funext i
      fin_cases i
      · simp [graphDualPlaneLinear, q, p, vsub_eq_sub]
      · simp [graphDualPlaneLinear, q, p, vsub_eq_sub]
      · simp [graphDualPlaneLinear, q, p, vsub_eq_sub]
        linarith
    have hu' : u -ᵥ p ∈ LinearMap.range (graphDualPlaneLinear x) := by
      rw [vsub_eq_sub, ← hq]
      exact LinearMap.mem_range.mpr ⟨q, rfl⟩
    simpa [graphDualPlaneSubspace, p, AffineSubspace.mem_mk'] using hu'

private noncomputable def graphDualPlaneFlat (x : E 3) : Flat 3 2 := by
  let p : E 3 := WithLp.toLp 2 ![0, 0, x 2]
  refine ⟨graphDualPlaneSubspace x, ?_, ?_⟩
  · refine ⟨p, ?_⟩
    simp [graphDualPlaneSubspace, p, AffineSubspace.mem_mk']
  · rw [graphDualPlaneSubspace, AffineSubspace.direction_mk']
    change Module.finrank ℝ (LinearMap.range (graphDualPlaneLinear x)) = 2
    rw [LinearMap.finrank_range_of_inj (graphDualPlaneLinear_injective x)]
    simp [E]

private theorem graphDualPlaneFlat_coe (x : E 3) :
    (graphDualPlaneFlat x).1 = graphDualPlane x := graphDualPlaneSubspace_coe x

private theorem affineMap_linear_injective (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) : Function.Injective φ.linear := by
  intro u v huv
  have hpoints : φ (u +ᵥ (0 : E 3)) = φ (v +ᵥ (0 : E 3)) := by
    calc
      φ (u +ᵥ (0 : E 3)) = φ.linear u +ᵥ φ 0 := φ.map_vadd 0 u
      _ = φ.linear v +ᵥ φ 0 := by rw [huv]
      _ = φ (v +ᵥ (0 : E 3)) := (φ.map_vadd 0 v).symm
  have h := hφ hpoints
  simpa using h

private theorem finrank_affineMap_map_direction (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) (s : AffineSubspace ℝ (E 3)) :
    Module.finrank ℝ (s.map φ).direction = Module.finrank ℝ s.direction := by
  rw [AffineSubspace.map_direction]
  let g : s.direction →ₗ[ℝ] E 6 := φ.linear.comp s.direction.subtype
  have hginj : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    exact affineMap_linear_injective φ hφ (by simpa [g] using huv)
  have hrange : LinearMap.range g = s.direction.map φ.linear := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hz
      exact Submodule.mem_map.mpr ⟨u.1, u.2, rfl⟩
    · intro hz
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
      exact LinearMap.mem_range.mpr ⟨⟨u, hu⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hginj]

private noncomputable def mapGraphDualPlaneFlat {φ : E 3 →ᵃ[ℝ] E 6}
    (hφ : Function.Injective φ) (x : E 3) : Flat 6 2 := by
  let P := graphDualPlaneFlat x
  let Q := P.1.map φ
  refine ⟨Q, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := P.2.1
    exact ⟨φ p, AffineSubspace.mem_map.mpr ⟨p, hp, rfl⟩⟩
  · rw [finrank_affineMap_map_direction φ hφ P.1, P.2.2]

private theorem mapGraphDualPlaneFlat_coe {φ : E 3 →ᵃ[ℝ] E 6}
    (hφ : Function.Injective φ) (x : E 3) :
    (mapGraphDualPlaneFlat (φ := φ) hφ x).1 = φ '' graphDualPlane x := by
  change ((graphDualPlaneFlat x).1.map φ : Set (E 6)) = _
  rw [AffineSubspace.coe_map, graphDualPlaneFlat_coe]

private theorem motion_pair_intersection_is_flat (g : Motion 3) (S : Finset (E 3))
    (G : Flat 6 3) (hmodel : MotionFlatModel g S G) (x : E 3) (hx : x ∈ S) :
    ∃ H : Flat 6 2,
      (H.1 : Set (E 6)) = pairFlatSet x (g x) ∩ (G.1 : Set (E 6)) := by
  rcases hmodel with ⟨_, T, φ, hφ, _, hinter, _⟩
  refine ⟨mapGraphDualPlaneFlat (φ := φ) hφ (T x), ?_⟩
  rw [mapGraphDualPlaneFlat_coe (φ := φ) hφ]
  exact (hinter x hx).symm

private theorem motionFlatModel_subset {g : Motion 3} {S S' : Finset (E 3)}
    {G : Flat 6 3} (hS' : S' ⊆ S) (hmodel : MotionFlatModel g S G) :
    MotionFlatModel g S' G := by
  rcases hmodel with ⟨hnull, T, φ, hφ, hrange, hinter, hnoncol⟩
  refine ⟨hnull, T, φ, hφ, hrange, ?_, ?_⟩
  · intro x hx
    exact hinter x (hS' hx)
  · intro x hx y hy z hz hxyz
    exact hnoncol x (hS' hx) y (hS' hy) z (hS' hz) hxyz

private theorem propagate_polynomial_to_pair_flat (X Y : Finset (E 3))
    (G : Finset (Motion 3)) (M : Motion 3 → Flat 6 3)
    (hmodel : ∀ g ∈ G, MotionFlatModel g (matchPoints X Y g) (M g))
    (hdistinct : ∀ x ∈ X, ∀ y ∈ Y, ∀ g ∈ G, ∀ g' ∈ G,
      g x = y → g' x = y → g ≠ g' →
        pairFlatSet x y ∩ (M g).1 ≠ pairFlatSet x y ∩ (M g').1)
    (f : Poly 6) (hf : ∀ g ∈ G, onPolynomial f (M g))
    (I : Finset (Motion 3)) (hIsub : I ⊆ G) (x : E 3) (hx : x ∈ X)
    (y : E 3) (hy : y ∈ Y) (hIxy : ∀ g ∈ I, g x = y)
    (hIdeg : f.totalDegree < I.card) :
    ∀ z ∈ pairFlatSet x y, evalR f z = 0 := by
  classical
  obtain ⟨F, hF, _⟩ := pair_flat_geometry x y
  have hPlaneExist (g : ↥I) :
      ∃ H : Flat 6 2, (H.1 : Set (E 6)) = pairFlatSet x y ∩ (M g.1).1 := by
    have hgG : g.1 ∈ G := hIsub g.2
    have hgxy : g.1 x = y := hIxy g.1 g.2
    have hmatch : x ∈ matchPoints X Y g.1 := by
      simp [matchPoints, hx, hy, hgxy]
    obtain ⟨H, hH⟩ := motion_pair_intersection_is_flat g.1 (matchPoints X Y g.1)
      (M g.1) (hmodel g.1 hgG) x hmatch
    refine ⟨H, ?_⟩
    simpa [hgxy] using hH
  let planeOf : ↥I → Flat 6 2 := fun g => Classical.choose (hPlaneExist g)
  have hplaneOf (g : ↥I) :
      (planeOf g).1 = pairFlatSet x y ∩ (M g.1).1 := Classical.choose_spec (hPlaneExist g)
  have hinj : Function.Injective planeOf := by
    intro g g' hgg'
    have hset : pairFlatSet x y ∩ (M g.1).1 = pairFlatSet x y ∩ (M g'.1).1 := by
      calc
        pairFlatSet x y ∩ (M g.1).1 = (planeOf g).1 := (hplaneOf g).symm
        _ = (planeOf g').1 := congrArg (fun H : Flat 6 2 => (H.1 : Set (E 6))) hgg'
        _ = pairFlatSet x y ∩ (M g'.1).1 := hplaneOf g'
    have hgG : g.1 ∈ G := hIsub g.2
    have hg'G : g'.1 ∈ G := hIsub g'.2
    have hgxy := hIxy g.1 g.2
    have hg'xy := hIxy g'.1 g'.2
    have hne : g.1 = g'.1 := by
      by_contra hne
      exact (hdistinct x hx y hy g.1 hgG g'.1 hg'G hgxy hg'xy hne) hset
    exact Subtype.ext hne
  let P : Finset (Flat 6 2) := Finset.univ.image planeOf
  have hPcard : P.card = I.card := by
    dsimp [P]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hP : ∀ H ∈ P, H.1 ≤ F.1 ∧ onPolynomial f H := by
    intro H hH
    rcases Finset.mem_image.mp hH with ⟨g, hg, rfl⟩
    have hgG : g.1 ∈ G := hIsub g.2
    constructor
    · intro z hz
      change z ∈ ((planeOf g).1 : Set (E 6)) at hz
      rw [hplaneOf g] at hz
      change z ∈ (F.1 : Set (E 6))
      rw [hF]
      exact (Set.mem_inter_iff z _ _).mp hz |>.1
    · intro z hz
      change z ∈ ((planeOf g).1 : Set (E 6)) at hz
      rw [hplaneOf g] at hz
      exact hf g.1 hgG z ((Set.mem_inter_iff z _ _).mp hz).2
  have hdeg : f.totalDegree < P.card := by rw [hPcard]; exact hIdeg
  have hvan : onPolynomial f F := polynomial_many_hyperplanes 6 2 F P f hP hdeg
  intro z hz
  apply hvan z
  change z ∈ (F.1 : Set (E 6))
  rw [hF]
  exact hz

private theorem flat_interpolation_choose_bound (D T : ℕ) (hD : 10 ≤ D)
    (hT : 10000 * T < D ^ 3) :
    T * Nat.choose (D + 3) 3 < Nat.choose (D + 6) 6 := by
  have hDpow : 720 ≤ D ^ 3 := by
    have h : (10 : ℕ) ^ 3 ≤ D ^ 3 := by gcongr
    norm_num at h
    omega
  have hchooseUpper : Nat.choose (D + 3) 3 ≤ 8 * D ^ 3 := by
    calc
      Nat.choose (D + 3) 3 ≤ (D + 3) ^ 3 := Nat.choose_le_pow _ _
      _ ≤ (2 * D) ^ 3 := by gcongr <;> omega
      _ = 8 * D ^ 3 := by ring
  have hchooseLower : (D + 1 : ℚ) ^ 6 / 720 ≤ (Nat.choose (D + 6) 6 : ℚ) := by
    have h := Nat.pow_le_choose (α := ℚ) 6 (D + 6)
    have hsub : D + 6 + 1 - 6 = D + 1 := by omega
    norm_num [hsub, Nat.factorial_succ] at h
    exact h
  have hgap : (10000 * T + 1) * D ^ 3 ≤ D ^ 6 := by
    calc
      (10000 * T + 1) * D ^ 3 ≤ D ^ 3 * D ^ 3 :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hT)
      _ = D ^ 6 := by ring
  have hdivmul : (8 * T * D ^ 3 + 1) * 720 ≤ D ^ 6 := by
    nlinarith [hgap, hDpow]
  have hquot : ((8 * T * D ^ 3 + 1 : ℕ) : ℚ) ≤ (D : ℚ) ^ 6 / 720 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 720)]
    exact_mod_cast hdivmul
  have hDmono : (D : ℚ) ^ 6 / 720 ≤ (D + 1 : ℚ) ^ 6 / 720 := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 720)]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) 6
  have hquot' : 8 * T * D ^ 3 + 1 ≤ Nat.choose (D + 6) 6 := by
    exact_mod_cast (hquot.trans (hDmono.trans hchooseLower))
  calc
    T * Nat.choose (D + 3) 3 ≤ T * (8 * D ^ 3) := Nat.mul_le_mul_left _ hchooseUpper
    _ < 8 * T * D ^ 3 + 1 := by
      have heq : T * (8 * D ^ 3) = 8 * T * D ^ 3 := by ring
      rw [heq]
      omega
    _ ≤ Nat.choose (D + 6) 6 := hquot'

private def motionIncidenceFiber (X Y : Finset (E 3)) (g : Motion 3) :
    Finset (Motion 3 × (E 3 × E 3)) :=
  (matchPoints X Y g).image fun x => (g, (x, g x))

private def motionIncidenceEdges (X Y : Finset (E 3)) (G : Finset (Motion 3)) :
    Finset (Motion 3 × (E 3 × E 3)) :=
  G.biUnion (motionIncidenceFiber X Y)

private theorem motionIncidenceEdges_card (X Y : Finset (E 3)) (G : Finset (Motion 3)) :
    (motionIncidenceEdges X Y G).card = ∑ g ∈ G, (matchPoints X Y g).card := by
  classical
  have hdisj : (G : Set (Motion 3)).PairwiseDisjoint (motionIncidenceFiber X Y) := by
    intro g hg g' hg' hne
    apply Finset.disjoint_left.mpr
    intro e he he'
    rcases Finset.mem_image.mp he with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp he' with ⟨x', hx', hEq⟩
    exact hne (congrArg Prod.fst hEq).symm
  rw [motionIncidenceEdges, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro g hg
  rw [motionIncidenceFiber, Finset.card_image_of_injective _ ?_]
  intro x x' hEq
  exact congrArg (fun e : Motion 3 × (E 3 × E 3) => e.2.1) hEq

private theorem motionIncidenceEdges_endpoints (X Y : Finset (E 3)) (G : Finset (Motion 3))
    (e : Motion 3 × (E 3 × E 3)) (he : e ∈ motionIncidenceEdges X Y G) :
    e.1 ∈ G ∧ e.2 ∈ X.product Y := by
  classical
  rcases Finset.mem_biUnion.mp he with ⟨g, hg, hmem⟩
  rcases Finset.mem_image.mp hmem with ⟨x, hx, rfl⟩
  have hx' : x ∈ X ∧ g x ∈ Y := by simpa [matchPoints] using hx
  exact ⟨hg, Finset.mem_product.mpr ⟨hx'.1, hx'.2⟩⟩

private theorem motionIncidenceEdges_repr (X Y : Finset (E 3)) (G : Finset (Motion 3))
    (e : Motion 3 × (E 3 × E 3)) :
    e ∈ motionIncidenceEdges X Y G ↔
      ∃ g ∈ G, ∃ x ∈ matchPoints X Y g, e = (g, (x, g x)) := by
  classical
  simp [motionIncidenceEdges, motionIncidenceFiber, Finset.mem_biUnion, Finset.mem_image, eq_comm]

private noncomputable def lineFlatOfDistinct (p q : E 3) (hpq : p ≠ q) : Line 3 := by
  let L : AffineSubspace ℝ (E 3) := line[ℝ, p, q]
  refine ⟨L, ?_, ?_⟩
  · exact ⟨p, by simpa [L] using left_mem_affineSpan_pair ℝ p q⟩
  · have hdir : L.direction = Submodule.span ℝ {(q - p : E 3)} := by
      change (line[ℝ, p, q]).direction = _
      rw [direction_affineSpan]
      rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_insert p ({q} : Set (E 3)))]
      simp [vsub_eq_sub]
    rw [hdir]
    exact finrank_span_singleton (sub_ne_zero.mpr hpq.symm)

private theorem exists_line_containing_of_collinear {S : Finset (E 3)}
    (hcard : 2 ≤ S.card) (hcol : Collinear ℝ (S : Set (E 3))) :
    ∃ l : Line 3, ∀ x ∈ S, x ∈ l.1 := by
  obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
  refine ⟨lineFlatOfDistinct p q hpq, ?_⟩
  intro z hz
  change z ∈ line[ℝ, p, q]
  rw [hcol.affineSpan_eq_of_ne (by simpa using hp) (by simpa using hq) hpq]
  exact mem_affineSpan ℝ (Finset.mem_coe.mpr hz)

private theorem matches_noncollinear_of_line_cap (X Y : Finset (E 3)) (g : Motion 3)
    (η ℓ : ℝ) (hη : η < 1) (hℓ : 0 < ℓ)
    (hcount : ℓ ≤ (matchCount X Y g : ℝ))
    (hcard : 2 ≤ (matchPoints X Y g).card)
    (hline : nonLineType η ℓ X Y g) :
    ¬ Collinear ℝ (matchPoints X Y g : Set (E 3)) := by
  intro hcol
  obtain ⟨l, hl⟩ := exists_line_containing_of_collinear hcard hcol
  have hpoints : pointsOn (matchPoints X Y g) l = matchPoints X Y g := by
    ext x
    simp only [pointsOn, Finset.mem_filter]
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, hl x hx⟩
  have hbad := hline l
  rw [hpoints] at hbad
  have hcardReal : ℓ ≤ ((matchPoints X Y g).card : ℝ) := by
    exact_mod_cast hcount
  have hηell : η * ℓ < ℓ := by
    calc
      η * ℓ < 1 * ℓ := mul_lt_mul_of_pos_right hη hℓ
      _ = ℓ := by ring
  exact (not_lt_of_ge hcardReal) (hbad.trans hηell)

private theorem matchPoints_trans_image (X Y : Finset (E 3)) (g Q : Motion 3) :
    matchPoints X (Y.image Q) (g.trans Q) = matchPoints X Y g := by
  classical
  ext x
  simp only [matchPoints, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hx, y, hy, hEq⟩
    have hEq' : Q y = Q (g x) := by simpa using hEq
    have hyEq : y = g x := Q.injective hEq'
    exact ⟨hx, hyEq ▸ hy⟩
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    exact ⟨g x, hy, by simp⟩

private noncomputable def orientationFlip : Motion 3 :=
  (LinearIsometryEquiv.neg ℝ (E := E 3)).toAffineIsometryEquiv

private theorem orientationFlip_det :
    LinearMap.det orientationFlip.toAffineEquiv.linear.toLinearMap = -1 := by
  have hlin : orientationFlip.toAffineEquiv.linear.toLinearMap =
      (-1 : ℝ) • (LinearMap.id : E 3 →ₗ[ℝ] E 3) := by
    apply LinearMap.ext
    intro x
    change -x = (-1 : ℝ) • x
    simp
  rw [hlin, LinearMap.det_smul, LinearMap.det_id]
  norm_num [E]

private theorem motion_det_eq_one_or_neg_one (g : Motion 3) :
    LinearMap.det g.toAffineEquiv.linear.toLinearMap = 1 ∨
      LinearMap.det g.toAffineEquiv.linear.toLinearMap = -1 := by
  have hnorm := g.linearIsometryEquiv.toLinearIsometry.normDet_eq_one
  rw [LinearMap.normDet_eq_abs_det] at hnorm
  have hlin : g.toAffineEquiv.linear.toLinearMap =
      g.linearIsometryEquiv.toLinearIsometry.toLinearMap := by
    ext x
    rfl
  have habs : |LinearMap.det g.toAffineEquiv.linear.toLinearMap| = |(1 : ℝ)| := by
    rw [hlin]
    simpa using hnorm
  rcases abs_eq_abs.mp habs with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

private theorem reverseMotion_trans_orientationFlip (g : Motion 3)
    (hg : LinearMap.det g.toAffineEquiv.linear.toLinearMap = 1) :
    reverseMotion (g.trans orientationFlip) := by
  change LinearMap.det
    (orientationFlip.toAffineEquiv.linear.toLinearMap.comp g.toAffineEquiv.linear.toLinearMap) = -1
  rw [LinearMap.det_comp, orientationFlip_det, hg]
  norm_num

private theorem reverseMotion_trans_rotation (g : Motion 3) (R : E 3 ≃ₗᵢ[ℝ] E 3)
    (hR : LinearMap.det R.toLinearEquiv.toLinearMap = 1) (hg : reverseMotion g) :
    reverseMotion (g.trans R.toAffineIsometryEquiv) := by
  change LinearMap.det
    (R.toAffineIsometryEquiv.toAffineEquiv.linear.toLinearMap.comp
      g.toAffineEquiv.linear.toLinearMap) = -1
  rw [LinearMap.det_comp]
  have hRlin : R.toAffineIsometryEquiv.toAffineEquiv.linear.toLinearMap =
      R.toLinearEquiv.toLinearMap := by
    ext x
    rfl
  have hR' : LinearMap.det R.toAffineIsometryEquiv.toAffineEquiv.linear.toLinearMap = 1 := by
    rw [hRlin]
    exact hR
  rw [hR', hg]
  ring

private theorem rpow_three_halves_eq_sqrt_cube (x : ℝ) (hx : 0 ≤ x) :
    x ^ ((3 : ℝ) / 2) = Real.sqrt x ^ 3 := by
  simpa using Real.rpow_div_two_eq_sqrt (3 : ℝ) hx

private theorem degree_threshold_absorbs (ε C m ℓ : ℝ) (hm : 1 ≤ m)
    (hε : 0 < ε) (hℓ : C * m ^ ((2 : ℝ) / 3) ≤ ℓ) (hC : 1 ≤ C)
    (hCε : 10000 < ε * C ^ ((3 : ℝ) / 2)) :
    10000 * m / Real.sqrt ℓ < ε * ℓ := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hℓpos : 0 < ℓ := by
    have hm23 : 0 < m ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hmpos _
    exact lt_of_lt_of_le (mul_pos hCpos hm23) hℓ
  have hsqrtpos : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓpos
  have hsqrtCpos : 0 < Real.sqrt C := Real.sqrt_pos.2 hCpos
  have hsqrtsqC : Real.sqrt C ^ 2 = C := Real.sq_sqrt (le_of_lt hCpos)
  have hrootC : 1 ≤ Real.sqrt C := by nlinarith [hsqrtsqC]
  have hCpow : C ≤ C ^ ((3 : ℝ) / 2) := by
    rw [rpow_three_halves_eq_sqrt_cube C (le_of_lt hCpos)]
    calc
      C = C * 1 := by ring
      _ ≤ C * Real.sqrt C := mul_le_mul_of_nonneg_left hrootC (le_of_lt hCpos)
      _ = Real.sqrt C ^ 3 := by
        calc
          C * Real.sqrt C = Real.sqrt C ^ 2 * Real.sqrt C := by rw [hsqrtsqC]
          _ = Real.sqrt C ^ 3 := by ring
  have hmpow : (m ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = m := by
    rw [← Real.rpow_mul (le_of_lt hmpos)]
    norm_num
  have hlarge : 10000 * m < ε * ℓ ^ ((3 : ℝ) / 2) := by
    have hbaseNonneg : 0 ≤ C * m ^ ((2 : ℝ) / 3) := by positivity
    have hbase := Real.rpow_le_rpow hbaseNonneg hℓ (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)
    rw [Real.mul_rpow (le_of_lt hCpos)
      (Real.rpow_nonneg (le_of_lt hmpos) ((2 : ℝ) / 3)), hmpow] at hbase
    have hcoeff : 10000 * m < ε * (C ^ ((3 : ℝ) / 2) * m) := by
      calc
        10000 * m < (ε * C ^ ((3 : ℝ) / 2)) * m := mul_lt_mul_of_pos_right hCε hmpos
        _ = ε * (C ^ ((3 : ℝ) / 2) * m) := by ring
    have hscaled : ε * (C ^ ((3 : ℝ) / 2) * m) ≤ ε * (ℓ ^ ((3 : ℝ) / 2)) := by
      exact mul_le_mul_of_nonneg_left hbase (le_of_lt hε)
    exact lt_of_lt_of_le hcoeff hscaled
  have hpow := rpow_three_halves_eq_sqrt_cube ℓ (le_of_lt hℓpos)
  have hsqrtsq : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt (le_of_lt hℓpos)
  have hsqrtcube : Real.sqrt ℓ ^ 3 = ℓ * Real.sqrt ℓ := by
    calc
      Real.sqrt ℓ ^ 3 = Real.sqrt ℓ ^ 2 * Real.sqrt ℓ := by ring
      _ = ℓ * Real.sqrt ℓ := by rw [hsqrtsq]
  apply (div_lt_iff₀ hsqrtpos).2
  rw [hpow] at hlarge
  rw [hsqrtcube] at hlarge
  simpa [mul_assoc] using hlarge

set_option maxHeartbeats 1000000 in
private theorem general_motion_bound_reversing
    (η₁ η₂ ε C : ℝ) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (hrel : η₁ ≤ η₂ / 100) (hη₂lt : η₂ < 1) (hε : 0 < ε)
    (hC4 : 4 ≤ C) (hCε : 10000 < ε * C ^ ((3 : ℝ) / 2))
    (hdual : ∀ (g : Motion 3) (S : Finset (E 3)) (F : Flat 6 3)
      (f : Poly 6) (ℓ : ℝ),
      0 < ℓ → ℓ / 4 ≤ (S.card : ℝ) → (S.card : ℝ) < 2 * ℓ →
      (∀ l : Line 3, ((pointsOn S l).card : ℝ) < η₁ * ℓ) →
      (∀ H : Plane 3, ((pointsOn S H).card : ℝ) < η₂ * ℓ) →
      MotionFlatModel g S F → (f.totalDegree : ℝ) < ε * ℓ → onPolynomial f F →
      (∀ x ∈ S, ∀ z ∈ pairFlatSet x (g x), evalR f z = 0) →
      ∀ i : Fin 6, onPolynomial (MvPolynomial.pderiv i f) F)
    (X Y : Finset (E 3)) (m ℓ : ℝ) (hm : 1 ≤ m)
    (hXm : (X.card : ℝ) ≤ m) (hYm : (Y.card : ℝ) ≤ m)
    (hℓ : C * m ^ ((2 : ℝ) / 3) ≤ ℓ)
    (G : Finset (Motion 3))
    (hGrev : ∀ g ∈ G, reverseMotion g)
    (hGbucket : ∀ g ∈ G, g ∈ motionBucket X Y ℓ)
    (hGline : ∀ g ∈ G, nonLineType η₁ ℓ X Y g)
    (hGplanar : ∀ g ∈ G, ¬ planarType η₂ ℓ X Y g) :
    (G.card : ℝ) ≤ (100000 : ℝ) * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := by
  classical
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hCpos : 0 < C := by linarith
  have hℓpos : 0 < ℓ := by
    have hmPow : 0 < m ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hmpos _
    exact lt_of_lt_of_le (mul_pos hCpos hmPow) hℓ
  by_contra hnot
  have htarget : (100000 : ℝ) * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) < (G.card : ℝ) :=
    lt_of_not_ge hnot
  let r : ℝ := m / Real.sqrt ℓ
  let q : ℝ := (100000 : ℝ) * m ^ 3 / ℓ ^ ((3 : ℝ) / 2)
  have hq : q < (G.card : ℝ) := htarget
  have hqeq : q = (100000 : ℝ) * r ^ 3 := by
    dsimp [q]
    rw [rpow_three_halves_eq_sqrt_cube ℓ (le_of_lt hℓpos)]
    dsimp [r]
    field_simp [Real.sqrt_pos.2 hℓpos]
  have hqnonneg : 0 ≤ q := le_of_lt (by dsimp [q, r]; positivity)
  let T : ℕ := Nat.floor q + 1
  have hfloorLE : (Nat.floor q : ℝ) ≤ q := Nat.floor_le hqnonneg
  have hfloorLT : Nat.floor q < G.card := by
    by_contra h
    have hge : G.card ≤ Nat.floor q := Nat.le_of_not_gt h
    have hge' : (G.card : ℝ) ≤ (Nat.floor q : ℝ) := by exact_mod_cast hge
    exact not_lt_of_ge (le_trans hge' hfloorLE) hq
  have hTle : T ≤ G.card := by dsimp [T]; omega
  obtain ⟨G₀, hG₀sub, hG₀card⟩ := Finset.exists_subset_card_eq hTle
  have hTpos : 0 < T := by dsimp [T]; omega
  have hG₀ne : G₀.Nonempty := Finset.card_pos.mp (by omega)
  have hmpow : 1 ≤ m ^ ((2 : ℝ) / 3) := Real.one_le_rpow hm (by norm_num)
  have hℓge4 : 4 ≤ ℓ := by
    calc
      4 ≤ C := hC4
      _ = C * 1 := by ring
      _ ≤ C * m ^ ((2 : ℝ) / 3) := mul_le_mul_of_nonneg_left hmpow hCpos.le
      _ ≤ ℓ := hℓ
  have hℓleM : ℓ ≤ m := by
    obtain ⟨g, hg⟩ := hG₀ne
    rcases hGbucket g (hG₀sub hg) with ⟨hcount, _⟩
    have hmatchLE : matchCount X Y g ≤ X.card := by
      dsimp [matchCount, matchPoints]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hmatchReal : (matchCount X Y g : ℝ) ≤ m :=
      (Nat.cast_le.mpr hmatchLE).trans hXm
    exact hcount.trans hmatchReal
  have hsqrtpos : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓpos
  have hsqrtsq : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓpos.le
  have hrootle : Real.sqrt ℓ ≤ ℓ := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.rpow_le_rpow_of_exponent_le (x := ℓ)
      (by linarith [hℓge4]) (y := (1 : ℝ) / 2) (z := 1) (by norm_num)
    simpa using h
  have hrge1 : 1 ≤ m / Real.sqrt ℓ := by
    apply (le_div_iff₀ hsqrtpos).2
    simpa only [one_mul] using hrootle.trans hℓleM
  have hrpos : 0 < m / Real.sqrt ℓ := div_pos hmpos hsqrtpos
  have hnpos : 1 ≤ Nat.floor (m / Real.sqrt ℓ) := by
    have hfloor := Nat.floor_mono hrge1
    simpa using hfloor
  have hrle2n : m / Real.sqrt ℓ ≤ 2 * (Nat.floor (m / Real.sqrt ℓ) : ℝ) := by
    have hfloor : m / Real.sqrt ℓ < (Nat.floor (m / Real.sqrt ℓ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hnreal : (1 : ℝ) ≤ Nat.floor (m / Real.sqrt ℓ) := by exact_mod_cast hnpos
    nlinarith [hnreal]
  have hTreal : (T : ℝ) ≤ 16 * (100000 : ℝ) *
      (Nat.floor (m / Real.sqrt ℓ) : ℝ) ^ 3 := by
    have hfloor : (Nat.floor q : ℝ) ≤ q := Nat.floor_le hqnonneg
    have hqone : 1 ≤ q := by
      rw [hqeq]
      have hrpow : 1 ≤ r ^ 3 := by
        calc
          1 = 1 ^ 3 := by norm_num
          _ ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hrge1 3
      nlinarith [hrpow]
    have hTq : (T : ℝ) ≤ 2 * q := by
      dsimp [T]
      push_cast
      linarith
    calc
      (T : ℝ) ≤ 2 * q := hTq
      _ = 2 * (100000 : ℝ) * (m / Real.sqrt ℓ) ^ 3 := by
        rw [hqeq]
        dsimp [r]
        ring
      _ ≤ 2 * (100000 : ℝ) * (2 * (Nat.floor (m / Real.sqrt ℓ) : ℝ)) ^ 3 := by
        gcongr
      _ = 16 * (100000 : ℝ) * (Nat.floor (m / Real.sqrt ℓ) : ℝ) ^ 3 := by ring
  have hTnat : T ≤ 16 * 100000 * (Nat.floor (m / Real.sqrt ℓ)) ^ 3 := by
    exact_mod_cast hTreal
  let D : ℕ := 10000 * Nat.floor (m / Real.sqrt ℓ)
  have hDlarge : 10 ≤ D := by dsimp [D]; omega
  have hTinterp : 10000 * T < D ^ 3 := by
    have hn3 : 1 ≤ (Nat.floor (m / Real.sqrt ℓ)) ^ 3 := by
      have hpos : 0 < (Nat.floor (m / Real.sqrt ℓ)) ^ 3 := pow_pos (by omega) _
      omega
    have hT' : 10000 * T ≤ 16000000000 * (Nat.floor (m / Real.sqrt ℓ)) ^ 3 := by
      calc
        10000 * T ≤ 10000 * (16 * 100000 * (Nat.floor (m / Real.sqrt ℓ)) ^ 3) :=
          Nat.mul_le_mul_left _ hTnat
        _ = 16000000000 * (Nat.floor (m / Real.sqrt ℓ)) ^ 3 := by ring
    have hDcube : D ^ 3 = 1000000000000 * (Nat.floor (m / Real.sqrt ℓ)) ^ 3 := by
      dsimp [D]
      ring
    rw [hDcube]
    nlinarith [hT', hn3]
  have hDdegree : (D : ℝ) < ε * ℓ := by
    have hDle : (D : ℝ) ≤ 10000 * m / Real.sqrt ℓ := by
      dsimp [D]
      push_cast
      calc
        10000 * (Nat.floor (m / Real.sqrt ℓ) : ℝ) ≤
            10000 * (m / Real.sqrt ℓ) :=
          mul_le_mul_of_nonneg_left (Nat.floor_le (le_of_lt hrpos)) (by norm_num)
        _ = 10000 * m / Real.sqrt ℓ := by ring
    have hC1 : 1 ≤ C := by linarith
    have hsmall := degree_threshold_absorbs ε C m ℓ hm hε hℓ hC1 hCε
    exact lt_of_le_of_lt hDle hsmall
  have hη₁lt : η₁ < 1 := by nlinarith [hrel, hη₂lt]
  obtain ⟨R, hRdet, hRgeneric⟩ :=
    spatial_generic_rotation X Y G₀ (fun g hg => hGrev g (hG₀sub hg))
  let rot : Motion 3 → Motion 3 := fun g => g.trans R.toAffineIsometryEquiv
  let Grot : Finset (Motion 3) := G₀.image rot
  have hrotinj : Function.Injective rot := by
    intro g g' hgg'
    apply AffineIsometryEquiv.ext
    intro x
    have h := congrArg (fun u : Motion 3 => u x) hgg'
    apply R.toAffineIsometryEquiv.injective
    simpa [rot] using h
  have hGrotcard : Grot.card = T := by
    dsimp [Grot]
    rw [Finset.card_image_of_injective _ hrotinj, hG₀card]
  have hrotData : ∀ g ∈ G₀,
      reverseMotion (rot g) ∧ Module.finrank ℝ (axis (rot g)) = 1 ∧
        axisAvoidsTriples (rot g) (matchPoints X (Y.image R) (rot g)) := by
    intro g hg
    have hrev := reverseMotion_trans_rotation g R hRdet (hGrev g (hG₀sub hg))
    have hgeom := hRgeneric g hg
    have hgeom' : Module.finrank ℝ (axis (rot g)) = 1 ∧
        axisAvoidsTriples (rot g) (matchPoints X (Y.image R) (rot g)) := by
      simpa [rot] using hgeom
    exact ⟨hrev, hgeom'.1, hgeom'.2⟩
  have hGrotData : ∀ g ∈ Grot,
      reverseMotion g ∧ Module.finrank ℝ (axis g) = 1 ∧
        axisAvoidsTriples g (matchPoints X (Y.image R) g) := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨g₀, hg₀, rfl⟩
    exact hrotData g₀ hg₀
  obtain ⟨M, hMinj, hMmodel, hMdistinct⟩ :=
    normalized_motion_flats X (Y.image R) Grot hGrotData
  have hmatchEq (g : Motion 3) :
      matchPoints X (Y.image R) (rot g) = matchPoints X Y g := by
    exact matchPoints_trans_image X Y g R.toAffineIsometryEquiv
  have hcountEq (g : Motion 3) :
      matchCount X (Y.image R) (rot g) = matchCount X Y g := by
    change (matchPoints X (Y.image R) (rot g)).card = (matchPoints X Y g).card
    rw [hmatchEq g]
  have hrotBucket : ∀ g ∈ G₀, rot g ∈ motionBucket X (Y.image R) ℓ := by
    intro g hg
    change ℓ ≤ (matchCount X (Y.image R) (rot g) : ℝ) ∧
      (matchCount X (Y.image R) (rot g) : ℝ) < 2 * ℓ
    rw [hcountEq g]
    exact hGbucket g (hG₀sub hg)
  have hrotLine : ∀ g ∈ G₀, nonLineType η₁ ℓ X (Y.image R) (rot g) := by
    intro g hg
    intro l
    change ((pointsOn (matchPoints X (Y.image R) (rot g)) l).card : ℝ) < η₁ * ℓ
    rw [hmatchEq g]
    exact hGline g (hG₀sub hg) l
  have hrotPlanar : ∀ g ∈ G₀, ¬ planarType η₂ ℓ X (Y.image R) (rot g) := by
    intro g hg
    intro hplanar
    rcases hplanar with ⟨H, hH⟩
    apply hGplanar g (hG₀sub hg)
    refine ⟨H, ?_⟩
    rw [hmatchEq g] at hH
    exact hH
  have hGrotBucket : ∀ g ∈ Grot, g ∈ motionBucket X (Y.image R) ℓ := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨g₀, hg₀, rfl⟩
    exact hrotBucket g₀ hg₀
  have hGrotLine : ∀ g ∈ Grot, nonLineType η₁ ℓ X (Y.image R) g := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨g₀, hg₀, rfl⟩
    exact hrotLine g₀ hg₀
  have hGrotPlanar : ∀ g ∈ Grot, ¬ planarType η₂ ℓ X (Y.image R) g := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨g₀, hg₀, rfl⟩
    exact hrotPlanar g₀ hg₀
  let B : Finset (E 3 × E 3) := X.product (Y.image R)
  let edges := motionIncidenceEdges X (Y.image R) Grot
  have hYimage : (Y.image R).card = Y.card :=
    Finset.card_image_of_injective _ R.injective
  have hBcard : (B.card : ℝ) ≤ m ^ 2 := by
    calc
      (B.card : ℝ) = (X.card : ℝ) * ((Y.image R).card : ℝ) := by simp [B]
      _ = (X.card : ℝ) * (Y.card : ℝ) := by rw [hYimage]
      _ ≤ m * m := mul_le_mul hXm hYm (Nat.cast_nonneg _) (le_of_lt hmpos)
      _ = m ^ 2 := by ring
  have hEndpoints : ∀ e ∈ edges, e.1 ∈ Grot ∧ e.2 ∈ B := by
    intro e he
    exact motionIncidenceEdges_endpoints X (Y.image R) Grot e he
  have hEdgesCard : (edges.card : ℝ) =
      ∑ g ∈ Grot, (matchCount X (Y.image R) g : ℝ) := by
    change ((motionIncidenceEdges X (Y.image R) Grot).card : ℝ) = _
    rw [motionIncidenceEdges_card]
    norm_cast
  have hEdgesLower : (T : ℝ) * ℓ ≤ (edges.card : ℝ) := by
    rw [hEdgesCard]
    calc
      (T : ℝ) * ℓ = (Grot.card : ℝ) * ℓ := by rw [hGrotcard]
      _ = ∑ g ∈ Grot, ℓ := by simp
      _ ≤ ∑ g ∈ Grot, (matchCount X (Y.image R) g : ℝ) := by
        apply Finset.sum_le_sum
        intro g hg
        exact (hGrotBucket g hg).1
  have hEdgesPos : 0 < edges.card := by
    have hpos : 0 < (edges.card : ℝ) := by
      exact lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr hTpos) hℓpos) hEdgesLower
    exact_mod_cast hpos
  have hEdgesNonempty : edges.Nonempty := Finset.card_pos.mp hEdgesPos
  have hBpos : 0 < (B.card : ℝ) := by
    obtain ⟨e, he⟩ := hEdgesNonempty
    have hEnd := hEndpoints e he
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨e.2, hEnd.2⟩)
  obtain ⟨E', hE'sub, hE'ne, hprune⟩ :=
    bipartite_pruning Grot B edges hEdgesNonempty hEndpoints
  have hpruneMotion (e : Motion 3 × (E 3 × E 3)) (he : e ∈ E') :
      ℓ / 4 ≤ ((E'.filter (fun z => z.1 = e.1)).card : ℝ) := by
    have hdeg := (hprune e he).1
    have hratio : ℓ / 4 ≤ (edges.card : ℝ) / (4 * (Grot.card : ℝ)) := by
      have hGrotcardR : (Grot.card : ℝ) = T := by exact_mod_cast hGrotcard
      rw [hGrotcardR]
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
        (by positivity : (0 : ℝ) < 4 * (T : ℝ))).2
      calc
        ℓ * (4 * (T : ℝ)) = 4 * ((T : ℝ) * ℓ) := by ring
        _ ≤ 4 * (edges.card : ℝ) := mul_le_mul_of_nonneg_left hEdgesLower (by norm_num)
        _ = (edges.card : ℝ) * 4 := by ring
    exact hratio.trans (by simpa using hdeg)
  letI : DecidableEq (E 3 × E 3) := Classical.decEq _
  have hprunePair (ab : Motion 3 × (E 3 × E 3)) (hab : ab ∈ E') :
      (T : ℝ) * ℓ / (4 * m ^ 2) ≤
        ((E'.filter (fun e => e.2 = ab.2)).card : ℝ) := by
    have hdeg := (hprune ab hab).2
    have hratio : (T : ℝ) * ℓ / (4 * m ^ 2) ≤
        (edges.card : ℝ) / (4 * (B.card : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * m ^ 2)
        (by positivity : (0 : ℝ) < 4 * (B.card : ℝ))).2
      have hmul : (T : ℝ) * ℓ * (B.card : ℝ) ≤
          (edges.card : ℝ) * m ^ 2 := by
        exact le_trans (mul_le_mul_of_nonneg_left hBcard (by positivity))
          (mul_le_mul_of_nonneg_right hEdgesLower (by positivity))
      calc
        (T : ℝ) * ℓ * (4 * (B.card : ℝ)) =
            4 * ((T : ℝ) * ℓ * (B.card : ℝ)) := by ring
        _ ≤ 4 * ((edges.card : ℝ) * m ^ 2) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = (edges.card : ℝ) * (4 * m ^ 2) := by ring
    have hdeg' : (edges.card : ℝ) / (4 * (B.card : ℝ)) ≤
        ((E'.filter (fun e => e.2 = ab.2)).card : ℝ) := by
      exact hdeg
    exact hratio.trans hdeg'
  have hEdgeEval (e : Motion 3 × (E 3 × E 3)) (he : e ∈ edges) :
      e.2.2 = e.1 e.2.1 := by
    rcases (motionIncidenceEdges_repr X (Y.image R) Grot e).mp he with
      ⟨g, hg, x, hx, rfl⟩
    rfl
  let G' : Finset (Motion 3) := E'.image Prod.fst
  have hG'sub : G' ⊆ Grot := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨e, he, rfl⟩
    exact (hEndpoints e (hE'sub he)).1
  have hG'ne : G'.Nonempty := by
    rcases hE'ne with ⟨e, he⟩
    exact ⟨e.1, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  have hG'card : G'.card ≤ T := by
    calc
      G'.card ≤ Grot.card := Finset.card_le_card hG'sub
      _ = T := hGrotcard
  have hM'inj : Set.InjOn M (G' : Set (Motion 3)) := by
    intro g hg g' hg' hgg'
    exact hMinj (hG'sub hg) (hG'sub hg') hgg'
  let H : Finset (Flat 6 3) := G'.image M
  have hHcard : H.card = G'.card := by
    dsimp [H]
    exact Finset.card_image_of_injOn hM'inj
  have hHsize : H.card * Nat.choose (D + 3) 3 < Nat.choose (D + 6) 6 := by
    calc
      H.card * Nat.choose (D + 3) 3 = G'.card * Nat.choose (D + 3) 3 := by
        rw [hHcard]
      _ ≤ T * Nat.choose (D + 3) 3 := Nat.mul_le_mul_right _ hG'card
      _ < Nat.choose (D + 6) 6 := flat_interpolation_choose_bound D T hDlarge hTinterp
  obtain ⟨f, hfnz, hfdegree, hfH⟩ := flat_interpolation 6 3 D H hHsize
  have hfG' : ∀ g ∈ G', onPolynomial f (M g) := by
    intro g hg
    apply hfH
    exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
  have hqgt : q < (T : ℝ) := by
    dsimp [T]
    exact_mod_cast Nat.lt_floor_add_one q
  have hqr : q * ℓ / (4 * m ^ 2) = 25000 * r := by
    rw [hqeq]
    dsimp [r]
    field_simp [hsqrtpos.ne', hmpos.ne']
    rw [hsqrtsq]
    ring
  have hqratio : q * ℓ / (4 * m ^ 2) < (T : ℝ) * ℓ / (4 * m ^ 2) := by
    have hden : 0 < 4 * m ^ 2 := by positivity
    apply (div_lt_div_iff₀ hden hden).2
    exact mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right hqgt hℓpos) hden
  have hDle' : (D : ℝ) ≤ 10000 * m / Real.sqrt ℓ := by
    dsimp [D]
    push_cast
    calc
      10000 * (Nat.floor (m / Real.sqrt ℓ) : ℝ) ≤
          10000 * (m / Real.sqrt ℓ) :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (le_of_lt hrpos)) (by norm_num)
      _ = 10000 * m / Real.sqrt ℓ := by ring
  have hDler : (D : ℝ) ≤ 10000 * r := by
    dsimp [r]
    calc
      (D : ℝ) ≤ 10000 * m / Real.sqrt ℓ := hDle'
      _ = 10000 * (m / Real.sqrt ℓ) := by ring
  have hthreshold : (D : ℝ) < (T : ℝ) * ℓ / (4 * m ^ 2) := by
    calc
      (D : ℝ) ≤ 10000 * r := hDler
      _ < q * ℓ / (4 * m ^ 2) := by rw [hqr]; nlinarith [hrpos]
      _ < (T : ℝ) * ℓ / (4 * m ^ 2) := hqratio
  have hpairVanishing (p : Poly 6) (hpdeg : p.totalDegree ≤ D)
      (hp : ∀ g ∈ G', onPolynomial p (M g))
      (ab : Motion 3 × (E 3 × E 3)) (hab : ab ∈ E') :
      ∀ z ∈ pairFlatSet ab.2.1 ab.2.2, evalR p z = 0 := by
    let F := E'.filter (fun e : Motion 3 × (E 3 × E 3) => e.2 = ab.2)
    let I : Finset (Motion 3) := F.image Prod.fst
    have hIcard : I.card = F.card := by
      dsimp [I, F]
      apply Finset.card_image_of_injOn
      intro e he e' he' hefst
      apply Prod.ext
      · exact hefst
      · exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp he').2.symm
    have hIdegReal : (D : ℝ) < (I.card : ℝ) := by
      have hIbound := hprunePair ab hab
      have hIbound' : (T : ℝ) * ℓ / (4 * m ^ 2) ≤ (I.card : ℝ) := by
        dsimp [I, F]
        rw [hIcard]
        exact hIbound
      exact lt_of_lt_of_le hthreshold hIbound'
    have hIdeg : D < I.card := by exact_mod_cast hIdegReal
    have hIdegP : p.totalDegree < I.card := lt_of_le_of_lt hpdeg hIdeg
    have hIsub : I ⊆ G' := by
      intro g hg
      rcases Finset.mem_image.mp hg with ⟨e, he, rfl⟩
      exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩
    have hIxy : ∀ g ∈ I, g ab.2.1 = ab.2.2 := by
      intro g hg
      rcases Finset.mem_image.mp hg with ⟨e, he, rfl⟩
      have heE : e ∈ edges := hE'sub (Finset.mem_filter.mp he).1
      have hepair := (Finset.mem_filter.mp he).2
      have hx : e.2.1 = ab.2.1 := congrArg Prod.fst hepair
      have hy : e.2.2 = ab.2.2 := congrArg Prod.snd hepair
      rw [← hx]
      exact (hEdgeEval e heE).symm.trans hy
    have habmem := hEndpoints ab (hE'sub hab)
    have habprod : ab.2.1 ∈ X ∧ ab.2.2 ∈ Y.image R :=
      Finset.mem_product.mp habmem.2
    exact propagate_polynomial_to_pair_flat X (Y.image R) G' M
      (fun g hg => hMmodel g (hG'sub hg))
      (fun x hx y hy g hg g' hg' hgy hg'y hne =>
        hMdistinct x hx y hy g (hG'sub hg) g' (hG'sub hg') hgy hg'y hne)
      p hp I hIsub ab.2.1 habprod.1 ab.2.2 habprod.2 hIxy hIdegP
  let Sg : Motion 3 → Finset (E 3) := fun g =>
    (E'.filter (fun e : Motion 3 × (E 3 × E 3) => e.1 = g)).image
      (fun e => e.2.1)
  have hEdgeMatch (e : Motion 3 × (E 3 × E 3)) (he : e ∈ edges) :
      e.2.1 ∈ matchPoints X (Y.image R) e.1 := by
    rcases (motionIncidenceEdges_repr X (Y.image R) Grot e).mp he with
      ⟨g, hg, x, hx, heq⟩
    rw [heq]
    exact hx
  have hSgsub (g : Motion 3) : Sg g ⊆ matchPoints X (Y.image R) g := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
    have heE : e ∈ edges := hE'sub (Finset.mem_filter.mp he).1
    have hmatch := hEdgeMatch e heE
    simpa [(Finset.mem_filter.mp he).2] using hmatch
  have hSgcard (e : Motion 3 × (E 3 × E 3)) (he : e ∈ E') :
      (Sg e.1).card = (E'.filter (fun z => z.1 = e.1)).card := by
    dsimp [Sg]
    apply Finset.card_image_of_injOn
    intro e₁ he₁ e₂ he₂ heX
    have hfst : e₁.1 = e₂.1 := by
      exact (Finset.mem_filter.mp he₁).2.trans (Finset.mem_filter.mp he₂).2.symm
    have he₁E : e₁ ∈ edges := hE'sub (Finset.mem_filter.mp he₁).1
    have he₂E : e₂ ∈ edges := hE'sub (Finset.mem_filter.mp he₂).1
    apply Prod.ext
    · exact hfst
    · apply Prod.ext
      · exact heX
      · calc
          e₁.2.2 = e₁.1 e₁.2.1 := hEdgeEval e₁ he₁E
          _ = e₂.1 e₂.2.1 := congrArg₂ (fun g x => g x) hfst heX
          _ = e₂.2.2 := (hEdgeEval e₂ he₂E).symm
  have hSgLower (g : Motion 3) (hg : g ∈ G') :
      ℓ / 4 ≤ ((Sg g).card : ℝ) := by
    rcases Finset.mem_image.mp hg with ⟨e, he, rfl⟩
    rw [hSgcard e he]
    exact hpruneMotion e he
  have hSgUpper (g : Motion 3) (hg : g ∈ G') :
      ((Sg g).card : ℝ) < 2 * ℓ := by
    have hcard := Finset.card_le_card (hSgsub g)
    calc
      ((Sg g).card : ℝ) ≤ ((matchPoints X (Y.image R) g).card : ℝ) := Nat.cast_le.mpr hcard
      _ < 2 * ℓ := by simpa [matchCount] using (hGrotBucket g (hG'sub hg)).2
  have hSgLine (g : Motion 3) (hg : g ∈ G') (l : Line 3) :
      ((pointsOn (Sg g) l).card : ℝ) < η₁ * ℓ := by
    have hsubset : pointsOn (Sg g) l ⊆ pointsOn (matchPoints X (Y.image R) g) l := by
      intro x hx
      change x ∈ (Sg g).filter (fun x => x ∈ l.1) at hx
      change x ∈ (matchPoints X (Y.image R) g).filter (fun x => x ∈ l.1)
      exact Finset.mem_filter.mpr
        ⟨hSgsub g (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans_lt
      (hGrotLine g (hG'sub hg) l)
  have hSgPlane (g : Motion 3) (hg : g ∈ G') (P : Plane 3) :
      ((pointsOn (Sg g) P).card : ℝ) < η₂ * ℓ := by
    have hsubset : pointsOn (Sg g) P ⊆ pointsOn (matchPoints X (Y.image R) g) P := by
      intro x hx
      change x ∈ (Sg g).filter (fun x => x ∈ P.1) at hx
      change x ∈ (matchPoints X (Y.image R) g).filter (fun x => x ∈ P.1)
      exact Finset.mem_filter.mpr
        ⟨hSgsub g (Finset.mem_filter.mp hx).1,
          (Finset.mem_filter.mp hx).2⟩
    have hfull : ((pointsOn (matchPoints X (Y.image R) g) P).card : ℝ) < η₂ * ℓ := by
      have hnot := hGrotPlanar g (hG'sub hg)
      simp only [planarType, not_exists] at hnot
      exact lt_of_not_ge (hnot P)
    exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans_lt hfull
  have hstable : ∀ p : Poly 6, p.totalDegree ≤ D →
      (∀ h ∈ H, onPolynomial p h) →
      ∀ i : Fin 6, ∀ h ∈ H, onPolynomial (MvPolynomial.pderiv i p) h := by
    intro p hpdeg hpH i h hh
    rcases Finset.mem_image.mp hh with ⟨g, hg, rfl⟩
    rcases Finset.mem_image.mp hg with ⟨e, he, rfl⟩
    have hg' : e.1 ∈ G' := Finset.mem_image.mpr ⟨e, he, rfl⟩
    have hpG' : ∀ g ∈ G', onPolynomial p (M g) := by
      intro g hg
      apply hpH
      exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
    have hmodelSg : MotionFlatModel e.1 (Sg e.1) (M e.1) :=
      motionFlatModel_subset (hSgsub e.1) (hMmodel e.1 (hG'sub hg'))
    have hpM : onPolynomial p (M e.1) := hpG' e.1 hg'
    have hpdegReal : (p.totalDegree : ℝ) < ε * ℓ := by
      exact lt_of_le_of_lt (by exact_mod_cast hpdeg) hDdegree
    have hpairs : ∀ x ∈ Sg e.1, ∀ z ∈ pairFlatSet x (e.1 x), evalR p z = 0 := by
      intro x hx z hz
      rcases Finset.mem_image.mp hx with ⟨edge, hedge, rfl⟩
      have hedgeE : edge ∈ edges := hE'sub (Finset.mem_filter.mp hedge).1
      have hxy : edge.2.2 = e.1 edge.2.1 := by
        calc
          edge.2.2 = edge.1 edge.2.1 := hEdgeEval edge hedgeE
          _ = e.1 edge.2.1 := by rw [(Finset.mem_filter.mp hedge).2]
      have hvan := hpairVanishing p hpdeg hpG' edge (Finset.mem_filter.mp hedge).1
      rw [← hxy] at hz
      exact hvan z hz
    have hderivs := hdual e.1 (Sg e.1) (M e.1) p ℓ hℓpos
      (hSgLower e.1 hg') (hSgUpper e.1 hg')
      (hSgLine e.1 hg') (hSgPlane e.1 hg') hmodelSg hpdegReal hpM hpairs
    exact hderivs i
  have hHne : H.Nonempty := by
    rcases hG'ne with ⟨g, hg⟩
    exact ⟨M g, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩
  have hzero := derivative_descent 6 3 D H hHne hstable f hfdegree hfH
  exact hfnz hzero

/-- General-type local bound, motions.tex:245–480. -/
theorem general_motion_bound : ∃ η₁ η₂ C K : ℝ,
    0 < η₁ ∧ 0 < η₂ ∧ η₁ ≤ η₂ / 100 ∧ η₂ < 1 ∧ 0 < C ∧ 0 < K ∧
    ∀ (X Y : Finset (E 3)) (m ℓ : ℝ), 1 ≤ m → (X.card : ℝ) ≤ m →
      (Y.card : ℝ) ≤ m → C * m ^ ((2 : ℝ) / 3) ≤ ℓ →
      FiniteCardBound {g : Motion 3 | g ∈ motionBucket X Y ℓ ∧
        nonLineType η₁ ℓ X Y g ∧ ¬ planarType η₂ ℓ X Y g}
        (K * m ^ 3 / ℓ ^ ((3 : ℝ) / 2)) := by
  classical
  obtain ⟨η₁, η₂, ε, hη₁, hη₂, hε, hrel, hη₂lt, hdual⟩ :=
    dual_arrangement_derivatives
  let C : ℝ := 4 + 10001 / ε
  let K : ℝ := 200000
  have hC4 : 4 ≤ C := by
    dsimp [C]
    have hratio : 0 < 10001 / ε := div_pos (by norm_num) hε
    linarith
  have hCpos : 0 < C := by linarith [hC4]
  have hC1 : 1 ≤ C := by linarith [hC4]
  have hCε : 10000 < ε * C ^ ((3 : ℝ) / 2) := by
    have hCmono : C ≤ C ^ ((3 : ℝ) / 2) := by
      have hpow := Real.rpow_le_rpow_of_exponent_le (x := C) hC1
        (y := 1) (z := (3 : ℝ) / 2) (by norm_num)
      simpa only [Real.rpow_one] using hpow
    have hlinear : 10000 < ε * C := by
      dsimp [C]
      field_simp [hε.ne']
      nlinarith
    calc
      10000 < ε * C := hlinear
      _ ≤ ε * C ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_left hCmono hε.le
  have hKpos : 0 < K := by norm_num [K]
  refine ⟨η₁, η₂, C, K, hη₁, hη₂, hrel, hη₂lt, hCpos, hKpos, ?_⟩
  intro X Y m ℓ hm hXm hYm hℓ
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hmpow : 1 ≤ m ^ ((2 : ℝ) / 3) := Real.one_le_rpow hm (by norm_num)
  have hℓge4 : 4 ≤ ℓ := by
    calc
      4 ≤ C := hC4
      _ = C * 1 := by ring
      _ ≤ C * m ^ ((2 : ℝ) / 3) := mul_le_mul_of_nonneg_left hmpow hCpos.le
      _ ≤ ℓ := hℓ
  have hℓpos : 0 < ℓ := lt_of_lt_of_le (by norm_num) hℓge4
  have hη₁lt : η₁ < 1 := by nlinarith [hrel, hη₂lt]
  let A : Set (Motion 3) := {g | g ∈ motionBucket X Y ℓ ∧
    nonLineType η₁ ℓ X Y g ∧ ¬ planarType η₂ ℓ X Y g}
  have hAfinite : A.Finite := by
    apply (spatial_motions_finite X Y).subset
    intro g hg
    change g ∈ motionBucket X Y ℓ ∧ nonLineType η₁ ℓ X Y g ∧
      ¬ planarType η₂ ℓ X Y g at hg
    rcases hg with ⟨hb, hline, _⟩
    change ℓ ≤ (matchCount X Y g : ℝ) ∧ _ at hb
    have hcount2 : (2 : ℝ) ≤ (matchCount X Y g : ℝ) := by
      exact le_trans (by linarith) hb.1
    have hmatchReal : (2 : ℝ) ≤ ((matchPoints X Y g).card : ℝ) := by
      simpa [matchCount] using hcount2
    have hmatchcard : 2 ≤ (matchPoints X Y g).card := by exact_mod_cast hmatchReal
    exact matches_noncollinear_of_line_cap X Y g η₁ ℓ hη₁lt hℓpos hb.1
      hmatchcard hline
  let GA : Finset (Motion 3) := hAfinite.toFinset
  have hGAmem (g : Motion 3) : g ∈ GA ↔ g ∈ A := by
    dsimp [GA]
    exact hAfinite.mem_toFinset
  let Gminus : Finset (Motion 3) := GA.filter reverseMotion
  let Gplus : Finset (Motion 3) := GA.filter
    (fun g => LinearMap.det g.toAffineEquiv.linear.toLinearMap = 1)
  have hGminusRev : ∀ g ∈ Gminus, reverseMotion g := by
    intro g hg
    exact (Finset.mem_filter.mp hg).2
  have hGminusBucket : ∀ g ∈ Gminus, g ∈ motionBucket X Y ℓ := by
    intro g hg
    have hga := (hGAmem g).mp (Finset.mem_filter.mp hg).1
    change g ∈ motionBucket X Y ℓ ∧ _ ∧ _ at hga
    exact hga.1
  have hGminusLine : ∀ g ∈ Gminus, nonLineType η₁ ℓ X Y g := by
    intro g hg
    have hga := (hGAmem g).mp (Finset.mem_filter.mp hg).1
    change g ∈ motionBucket X Y ℓ ∧ _ ∧ _ at hga
    exact hga.2.1
  have hGminusPlanar : ∀ g ∈ Gminus, ¬ planarType η₂ ℓ X Y g := by
    intro g hg
    have hga := (hGAmem g).mp (Finset.mem_filter.mp hg).1
    change g ∈ motionBucket X Y ℓ ∧ _ ∧ _ at hga
    exact hga.2.2
  have hminusBound := general_motion_bound_reversing η₁ η₂ ε C hη₁ hη₂
    hrel hη₂lt hε hC4 hCε hdual X Y m ℓ hm hXm hYm hℓ
    Gminus hGminusRev hGminusBucket hGminusLine hGminusPlanar
  let Q : Motion 3 := orientationFlip
  let YQ : Finset (E 3) := Y.image Q
  have hYQcard : YQ.card = Y.card := Finset.card_image_of_injective _ Q.injective
  have hYmQ : (YQ.card : ℝ) ≤ m := by rw [hYQcard]; exact hYm
  let post : Motion 3 → Motion 3 := fun g => g.trans Q
  have hpostinj : Function.Injective post := by
    intro g g' h
    apply AffineIsometryEquiv.ext
    intro x
    apply Q.injective
    have hx := congrArg (fun u : Motion 3 => u x) h
    simpa [post] using hx
  let GplusQ : Finset (Motion 3) := Gplus.image post
  have hGplusQcard : GplusQ.card = Gplus.card := by
    dsimp [GplusQ]
    rw [Finset.card_image_of_injective _ hpostinj]
  have hGplusQRev : ∀ g ∈ GplusQ, reverseMotion g := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨g₀, hg₀, rfl⟩
    have hdet := (Finset.mem_filter.mp hg₀).2
    exact reverseMotion_trans_orientationFlip g₀ hdet
  have hcountPost (g : Motion 3) :
      matchCount X (Y.image Q) (g.trans Q) = matchCount X Y g := by
    change (matchPoints X (Y.image Q) (g.trans Q)).card = (matchPoints X Y g).card
    rw [matchPoints_trans_image]
  have hGplusQBucket : ∀ g ∈ GplusQ, g ∈ motionBucket X (Y.image Q) ℓ := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨g₀, hg₀, rfl⟩
    have hga := (hGAmem g₀).mp (Finset.mem_filter.mp hg₀).1
    change g₀ ∈ motionBucket X Y ℓ ∧ _ ∧ _ at hga
    change ℓ ≤ (matchCount X (Y.image Q) (g₀.trans Q) : ℝ) ∧
      (matchCount X (Y.image Q) (g₀.trans Q) : ℝ) < 2 * ℓ
    rw [hcountPost]
    exact hga.1
  have hGplusQLine : ∀ g ∈ GplusQ, nonLineType η₁ ℓ X (Y.image Q) g := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨g₀, hg₀, rfl⟩
    have hga := (hGAmem g₀).mp (Finset.mem_filter.mp hg₀).1
    change g₀ ∈ motionBucket X Y ℓ ∧ _ ∧ _ at hga
    intro l
    change ((pointsOn (matchPoints X (Y.image Q) (g₀.trans Q)) l).card : ℝ) < η₁ * ℓ
    rw [matchPoints_trans_image]
    exact hga.2.1 l
  have hGplusQPlanar : ∀ g ∈ GplusQ, ¬ planarType η₂ ℓ X (Y.image Q) g := by
    intro g hg hplanar
    rcases Finset.mem_image.mp hg with ⟨g₀, hg₀, rfl⟩
    have hga := (hGAmem g₀).mp (Finset.mem_filter.mp hg₀).1
    change g₀ ∈ motionBucket X Y ℓ ∧ _ ∧ _ at hga
    apply hga.2.2
    rcases hplanar with ⟨P, hP⟩
    refine ⟨P, ?_⟩
    rw [matchPoints_trans_image X Y g₀ Q] at hP
    exact hP
  have hplusBound := general_motion_bound_reversing η₁ η₂ ε C hη₁ hη₂
    hrel hη₂lt hε hC4 hCε hdual X (Y.image Q) m ℓ hm hXm hYmQ hℓ
    GplusQ hGplusQRev hGplusQBucket hGplusQLine hGplusQPlanar
  have hplusBound' : (Gplus.card : ℝ) ≤
      (100000 : ℝ) * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := by
    rw [← hGplusQcard]
    exact hplusBound
  have hcover : GA ⊆ Gminus ∪ Gplus := by
    intro g hg
    rcases motion_det_eq_one_or_neg_one g with hdet | hdet
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hg, hdet⟩
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hg, by simpa [reverseMotion] using hdet⟩
  have hcardGA : GA.card ≤ Gminus.card + Gplus.card := by
    exact le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  have hcardGAR : (GA.card : ℝ) ≤ (Gminus.card : ℝ) + (Gplus.card : ℝ) := by
    exact_mod_cast hcardGA
  have hbound : (GA.card : ℝ) ≤ K * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := by
    calc
      (GA.card : ℝ) ≤ (Gminus.card : ℝ) + (Gplus.card : ℝ) := hcardGAR
      _ ≤ (100000 : ℝ) * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) +
          (100000 : ℝ) * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := add_le_add hminusBound hplusBound'
      _ = K * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := by dsimp [K]; ring
  refine ⟨hAfinite, ?_⟩
  have hcardn : A.ncard = GA.card := by
    rw [Set.ncard_eq_toFinset_card A hAfinite]
  rw [hcardn]
  exact hbound

private noncomputable def planeCoordinates (P : Plane 3) [Nonempty P.1] : E 2 ≃ᵃⁱ[ℝ] P.1 := by
  let p : P.1 := Classical.choice inferInstance
  have hdim : Module.finrank ℝ P.1.direction = 2 := P.2.2
  let B : OrthonormalBasis (Fin 2) ℝ P.1.direction :=
    (stdOrthonormalBasis ℝ P.1.direction).reindex (finCongr hdim)
  let L : E 2 ≃ₗᵢ[ℝ] P.1.direction := B.repr.symm
  refine AffineIsometryEquiv.mk' (fun z => (L z) +ᵥ p) L 0 ?_
  intro z
  simp [L, p]

private noncomputable def motionOnPlanes (P Q : Plane 3) [Nonempty P.1] [Nonempty Q.1]
    (g : Motion 3) (h : P.1.map g.toAffineIsometry.toAffineMap = Q.1) : Motion 2 :=
  (planeCoordinates P).trans
    ((P.1.isometryEquivMap g.toAffineIsometry).trans
      ((AffineIsometryEquiv.ofEq (P.1.map g.toAffineIsometry.toAffineMap) Q.1 h).trans
        (planeCoordinates Q).symm))

private theorem motionOnPlanes_apply (P Q : Plane 3) [Nonempty P.1] [Nonempty Q.1]
    (g : Motion 3) (h : P.1.map g.toAffineIsometry.toAffineMap = Q.1) (x : P.1) :
    ∃ y : Q.1, (y : E 3) = g x ∧
      (motionOnPlanes P Q g h) ((planeCoordinates P).symm x) =
        (planeCoordinates Q).symm y := by
  have hx : (g x : E 3) ∈ P.1.map g.toAffineIsometry.toAffineMap :=
    ⟨x, x.property, rfl⟩
  have hy : (g x : E 3) ∈ Q.1 := by
    simpa [h] using hx
  let y : Q.1 := ⟨g x, hy⟩
  refine ⟨y, rfl, ?_⟩
  simp [motionOnPlanes, y]
  apply Subtype.ext
  rfl

private theorem plane_nonempty (P : Plane 3) : Nonempty P.1 := by
  rcases P.2.1 with ⟨p, hp⟩
  exact ⟨⟨p, hp⟩⟩

private instance planeSubtypeNonempty (P : Plane 3) : Nonempty P.1 := plane_nonempty P

private noncomputable def planeImage (P : Plane 3) (g : Motion 3) : Plane 3 := by
  letI : Nonempty P.1 := plane_nonempty P
  let T := P.1.isometryEquivMap g.toAffineIsometry
  refine ⟨P.1.map g.toAffineIsometry.toAffineMap, ?_, ?_⟩
  · change (g.toAffineIsometry '' (P.1 : Set (E 3))).Nonempty
    exact P.2.1.image g.toAffineIsometry
  · have hdim := LinearEquiv.finrank_eq T.linear
    rw [← hdim]
    exact P.2.2

private theorem plane_contains_line (P : Plane 3) : ∃ l : Line 3, l.1 ≤ P.1 := by
  have hdim : 0 < Module.finrank ℝ P.1.direction := by rw [P.2.2]; norm_num
  obtain ⟨v, hv⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := P.1.direction)).mp hdim
  rcases P.2.1 with ⟨p, hp⟩
  let q : E 3 := (v : E 3) +ᵥ p
  have hq : q ∈ P.1 := by
    rw [AffineSubspace.vadd_mem_iff_mem_direction (v : E 3) hp]
    exact v.property
  have hpq : p ≠ q := by
    intro h
    have hv0 : (v : E 3) = 0 := by
      simpa [q] using (congrArg (fun x : E 3 => x -ᵥ p) h).symm
    exact hv (Subtype.ext hv0)
  let l : Line 3 := lineFlatOfDistinct_effective p q hpq
  refine ⟨l, ?_⟩
  change line[ℝ, p, q] ≤ P.1
  apply affineSpan_le_of_subset_coe
  intro x hx
  have hx' : x = p ∨ x = q := by simpa using hx
  rcases hx' with rfl | rfl
  · exact hp
  · exact hq

private theorem richestLine_attained (X : Finset (E 3)) (P : Plane 3) :
    ∃ l : Line 3, l.1 ≤ P.1 ∧
      (pointsOn X l).card = richestLineOccupancy X P := by
  classical
  let T : Set ℕ := {n | ∃ l : Line 3, l.1 ≤ P.1 ∧ (pointsOn X l).card = n}
  have hTnonempty : T.Nonempty := by
    obtain ⟨l, hl⟩ := plane_contains_line P
    exact ⟨(pointsOn X l).card, l, hl, rfl⟩
  have hTfinite : T.Finite := by
    apply (Set.finite_Iic (pointsOn X P).card).subset
    intro n hn
    rcases hn with ⟨l, hl, rfl⟩
    apply Finset.card_le_card
    intro x hx
    simp only [pointsOn, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hl hx.2⟩
  have hs : sSup T ∈ T := hTnonempty.csSup_mem hTfinite
  rcases hs with ⟨l, hl, hcard⟩
  refine ⟨l, hl, ?_⟩
  simpa [richestLineOccupancy, T] using hcard

private noncomputable def planeReducedPoints (X : Finset (E 3)) (P : Plane 3)
    (l : Line 3) : Finset (E 3) :=
  (pointsOn X P).filter (fun x => x ∉ (l.1 : Set (E 3)))

private theorem planeReducedPoints_card (X : Finset (E 3)) (P : Plane 3)
    (l : Line 3) (hl : l.1 ≤ P.1)
    (hmax : (pointsOn X l).card = richestLineOccupancy X P) :
    (planeReducedPoints X P l).card = effectiveSize X P := by
  classical
  have hlinefilter : (pointsOn X P).filter (fun x => x ∈ (l.1 : Set (E 3))) =
      pointsOn X l := by
    ext x
    simp only [pointsOn, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxX, hxP⟩, hxl⟩
      exact ⟨hxX, hxl⟩
    · intro hx
      exact ⟨⟨hx.1, hl hx.2⟩, hx.2⟩
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := pointsOn X P) (fun x => x ∈ (l.1 : Set (E 3)))
  have hpartition' : (pointsOn X l).card + (planeReducedPoints X P l).card =
      (pointsOn X P).card := by
    rw [← hlinefilter]
    simpa [planeReducedPoints] using hpartition
  simp only [effectiveSize]
  rw [← hmax]
  omega

private noncomputable def planeReducedCoordinates (X : Finset (E 3)) (P : Plane 3)
    (l : Line 3) [Nonempty P.1] : Finset (E 2) :=
  (planeReducedPoints X P l).attach.image fun x =>
    (planeCoordinates P).symm
      ⟨x.1, (Finset.mem_filter.mp (Finset.mem_filter.mp x.2).1).2⟩

private theorem planeReducedCoordinates_card (X : Finset (E 3)) (P : Plane 3)
    (l : Line 3) [Nonempty P.1] :
    (planeReducedCoordinates X P l).card = (planeReducedPoints X P l).card := by
  classical
  let f : {x // x ∈ planeReducedPoints X P l} → E 2 := fun x =>
    (planeCoordinates P).symm
      ⟨x.1, (Finset.mem_filter.mp (Finset.mem_filter.mp x.2).1).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    let pa : P.1 :=
      ⟨a.1, (Finset.mem_filter.mp (Finset.mem_filter.mp a.2).1).2⟩
    let pb : P.1 :=
      ⟨b.1, (Finset.mem_filter.mp (Finset.mem_filter.mp b.2).1).2⟩
    have hab' : (planeCoordinates P).symm pa = (planeCoordinates P).symm pb := by
      simpa [f, pa, pb] using hab
    have hp : pa = pb := (planeCoordinates P).symm.injective hab'
    have hx : (a.1 : E 3) = b.1 := by
      have h := congrArg (fun x : P.1 => (x : E 3)) hp
      simpa [pa, pb] using h
    exact Subtype.ext hx
  change ((planeReducedPoints X P l).attach.image f).card = _
  rw [Finset.card_image_of_injective _ hf]
  simp

private noncomputable def richestLineOf (X : Finset (E 3)) (P : Plane 3) : Line 3 :=
  Classical.choose (richestLine_attained X P)

private theorem richestLineOf_spec (X : Finset (E 3)) (P : Plane 3) :
    (richestLineOf X P).1 ≤ P.1 ∧
      (pointsOn X (richestLineOf X P)).card = richestLineOccupancy X P :=
  Classical.choose_spec (richestLine_attained X P)

private theorem planeReducedCoordinates_effective_card (X : Finset (E 3)) (P : Plane 3) :
    (planeReducedCoordinates X P (richestLineOf X P)).card = effectiveSize X P := by
  rw [planeReducedCoordinates_card]
  exact planeReducedPoints_card X P (richestLineOf X P)
    (richestLineOf_spec X P).1 (richestLineOf_spec X P).2

private theorem planeReduced_mem_plane (X : Finset (E 3)) (P : Plane 3) (l : Line 3)
    {x : E 3} (hx : x ∈ planeReducedPoints X P l) : x ∈ P.1 := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2

private theorem planeReduced_matchCount (X Y : Finset (E 3)) (P Q : Plane 3)
    [Nonempty P.1] [Nonempty Q.1] (l l' : Line 3)
    (g : Motion 3) (h : P.1.map g.toAffineIsometry.toAffineMap = Q.1) :
    matchCount (planeReducedCoordinates X P l) (planeReducedCoordinates Y Q l')
      (motionOnPlanes P Q g h) =
      ((planeReducedPoints X P l).filter
        (fun x => g x ∈ planeReducedPoints Y Q l')).card := by
  classical
  let A := (planeReducedPoints X P l).filter
    (fun x => g x ∈ planeReducedPoints Y Q l')
  let U := planeReducedCoordinates X P l
  let V := planeReducedCoordinates Y Q l'
  let f := motionOnPlanes P Q g h
  let B := matchPoints U V f
  have hcard : A.card = B.card := by
    refine Finset.card_bij (s := A) (t := B)
      (fun x hx => (planeCoordinates P).symm
        ⟨x, planeReduced_mem_plane X P l (Finset.mem_filter.mp hx).1⟩)
      ?_ ?_ ?_
    · intro x hx
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_image.mpr
        refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, Finset.mem_attach _ _, ?_⟩
        rfl
      · obtain ⟨y, hyval, hycoord⟩ := motionOnPlanes_apply P Q g h
          ⟨x, planeReduced_mem_plane X P l (Finset.mem_filter.mp hx).1⟩
        rw [hycoord]
        apply Finset.mem_image.mpr
        let b : {z // z ∈ planeReducedPoints Y Q l'} :=
          ⟨g x, (Finset.mem_filter.mp hx).2⟩
        refine ⟨b, Finset.mem_attach _ _, ?_⟩
        apply congrArg (fun z : Q.1 => (planeCoordinates Q).symm z)
        exact Subtype.ext hyval.symm
    · intro x hx x' hx' heq
      have hplane :
          (⟨x, planeReduced_mem_plane X P l (Finset.mem_filter.mp hx).1⟩ : P.1) =
          ⟨x', planeReduced_mem_plane X P l (Finset.mem_filter.mp hx').1⟩ :=
        (planeCoordinates P).symm.injective heq
      have hval := congrArg (fun z : P.1 => (z : E 3)) hplane
      exact hval
    · intro z hz
      have hz' : z ∈ U ∧ f z ∈ V := by
        exact (Finset.mem_filter.mp hz)
      rcases Finset.mem_image.mp hz'.1 with ⟨a, ha, haz⟩
      have haRed : a.1 ∈ planeReducedPoints X P l := a.2
      let xP : P.1 := ⟨a.1, planeReduced_mem_plane X P l haRed⟩
      obtain ⟨yQ, hyval, hycoord⟩ := motionOnPlanes_apply P Q g h xP
      have hyV : (planeCoordinates Q).symm yQ ∈ V := by
        rw [← hycoord, haz]
        exact hz'.2
      rcases Finset.mem_image.mp hyV with ⟨b, hb, hbcoord⟩
      have hbRed : b.1 ∈ planeReducedPoints Y Q l' := b.2
      let bQ : Q.1 := ⟨b.1, planeReduced_mem_plane Y Q l' hbRed⟩
      have hbEq : bQ = yQ :=
        (planeCoordinates Q).symm.injective (by simpa [bQ] using hbcoord)
      have hgRed : g a.1 ∈ planeReducedPoints Y Q l' := by
        have hval := congrArg (fun z : Q.1 => (z : E 3)) hbEq
        rw [hyval] at hval
        simpa [bQ] using hval.symm ▸ hbRed
      have hA : a.1 ∈ A := Finset.mem_filter.mpr ⟨haRed, hgRed⟩
      refine ⟨a.1, hA, ?_⟩
      simpa [U, f, haz, xP] using rfl
  change B.card = A.card
  rw [hcard]

private theorem flat_nonempty {d k : ℕ} (H : Flat d k) : Nonempty H.1 := by
  rcases H.2.1 with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩

private noncomputable def flatImage {d k : ℕ} (H : Flat d k) (g : Motion d) : Flat d k := by
  letI : Nonempty H.1 := flat_nonempty H
  let T := H.1.isometryEquivMap g.toAffineIsometry
  refine ⟨H.1.map g.toAffineIsometry.toAffineMap, ?_, ?_⟩
  · change (g.toAffineIsometry '' (H.1 : Set (E d))).Nonempty
    exact H.2.1.image g.toAffineIsometry
  · have hdim := LinearEquiv.finrank_eq T.linear
    rw [← hdim]
    exact H.2.2

private theorem flatImage_mem {d k : ℕ} (H : Flat d k) (g : Motion d) (x : E d) :
    x ∈ (flatImage H g).1 ↔ g.symm x ∈ H.1 := by
  change x ∈ (g.toAffineIsometry '' (H.1 : Set (E d))) ↔ g.symm x ∈ H.1
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g.symm x, hx, by simp⟩

private theorem flatImage_symm_mem {d k : ℕ} (H : Flat d k) (g : Motion d) (x : E d) :
    x ∈ (flatImage H g.symm).1 ↔ g x ∈ H.1 := by
  simpa using flatImage_mem H g.symm x

private theorem planeImage_map (P : Plane 3) (g : Motion 3) :
    (planeImage P g.symm).1.map g.toAffineIsometry.toAffineMap = P.1 := by
  change (P.1.map g.symm.toAffineIsometry.toAffineMap).map
    g.toAffineIsometry.toAffineMap = P.1
  rw [AffineSubspace.map_map]
  have hcomp :
      g.toAffineIsometry.toAffineMap.comp g.symm.toAffineIsometry.toAffineMap =
        AffineMap.id ℝ (E 3) := by
    ext x
    simp
  rw [hcomp, AffineSubspace.map_id]

private theorem planeReduced_matches_not_collinear (X Y : Finset (E 3))
    (P Q : Plane 3) (l l' : Line 3) (η₁ ℓ : ℝ) (g : Motion 3) (k : ℕ)
    (hk : 3 ≤ k)
    (hcount : k ≤ matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g)
    (hcut : η₁ * ℓ < (k : ℝ))
    (hnonline : nonLineType η₁ ℓ X Y g) :
    ¬ Collinear ℝ
      (matchPoints (planeReducedPoints X P l) (planeReducedPoints Y Q l') g : Set (E 3)) := by
  classical
  let M := matchPoints (planeReducedPoints X P l) (planeReducedPoints Y Q l') g
  intro hcol
  have hcard2 : 2 ≤ M.card := by
    dsimp [M]
    change 2 ≤ matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g
    exact le_trans (by omega) hcount
  obtain ⟨L, hL⟩ := exists_line_containing_of_collinear_effective hcard2 hcol
  have hsub : M ⊆ pointsOn (matchPoints X Y g) L := by
    intro x hx
    simp only [pointsOn, Finset.mem_filter]
    refine ⟨?_, hL x hx⟩
    simp only [M, matchPoints, Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hx, hgx⟩
    refine ⟨?_, ?_⟩
    · have hx' := (Finset.mem_filter.mp hx).1
      exact (Finset.mem_filter.mp hx').1
    · have hgx' := (Finset.mem_filter.mp hgx).1
      exact (Finset.mem_filter.mp hgx').1
  have hcard : M.card ≤ (pointsOn (matchPoints X Y g) L).card :=
    Finset.card_le_card hsub
  have hcountR : (k : ℝ) ≤ (M.card : ℝ) := by exact_mod_cast hcount
  have hcardR : (M.card : ℝ) ≤ (pointsOn (matchPoints X Y g) L).card :=
    Nat.cast_le.mpr hcard
  have hline := hnonline L
  change ((pointsOn (matchPoints X Y g) L).card : ℝ) < η₁ * ℓ at hline
  linarith

private theorem plane_matches_not_collinear (X Y : Finset (E 3)) (P : Plane 3)
    (η₁ η₂ ℓ : ℝ) (g : Motion 3) (hη₁ : 0 < η₁) (hη : η₁ < η₂)
    (hℓ : 0 < ℓ) (h2 : 2 ≤ η₂ * ℓ)
    (hOcc : η₂ * ℓ ≤ (pointsOn (matchPoints X Y g) P).card)
    (hnonline : nonLineType η₁ ℓ X Y g) :
    ¬ Collinear ℝ (pointsOn (matchPoints X Y g) P : Set (E 3)) := by
  classical
  let S := pointsOn (matchPoints X Y g) P
  intro hcol
  have hcard2 : 2 ≤ S.card := by
    dsimp [S]
    have hreal : (2 : ℝ) ≤ (pointsOn (matchPoints X Y g) P).card := by
      exact le_trans h2 hOcc
    exact_mod_cast hreal
  obtain ⟨L, hL⟩ := exists_line_containing_of_collinear_effective hcard2 hcol
  have hsub : S ⊆ pointsOn (matchPoints X Y g) L := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hL x hx⟩
  have hcard : S.card ≤ (pointsOn (matchPoints X Y g) L).card := Finset.card_le_card hsub
  have hcardR : (S.card : ℝ) ≤ (pointsOn (matchPoints X Y g) L).card := Nat.cast_le.mpr hcard
  have hline := hnonline L
  change ((pointsOn (matchPoints X Y g) L).card : ℝ) < η₁ * ℓ at hline
  change η₂ * ℓ ≤ (S.card : ℝ) at hOcc
  have hηprod : η₁ * ℓ < η₂ * ℓ := mul_lt_mul_of_pos_right hη hℓ
  linarith

private theorem reduced_plane_matches_lower (η₁ η₂ ℓ : ℝ) (X Y : Finset (E 3))
    (P Q : Plane 3) (g : Motion 3) (hη : η₁ < η₂) (hℓ : 0 < ℓ)
    (hmap : P.1.map g.toAffineIsometry.toAffineMap = Q.1)
    (hOcc : η₂ * ℓ ≤ (pointsOn (matchPoints X Y g) P).card)
    (hnonline : nonLineType η₁ ℓ X Y g) (l l' : Line 3)
    (hl : l.1 ≤ P.1) (hl' : l'.1 ≤ Q.1) :
    Nat.ceil ((η₂ - 2 * η₁) * ℓ) ≤
      matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g := by
  classical
  let M := matchPoints X Y g
  let S := pointsOn M P
  let Lpre : Line 3 := flatImage l' g.symm
  let Drop1 := S.filter (fun x => x ∈ (l.1 : Set (E 3)))
  let S0 := S.filter (fun x => x ∉ (l.1 : Set (E 3)))
  let Drop2 := S0.filter (fun x => x ∈ (Lpre.1 : Set (E 3)))
  let Keep := S0.filter (fun x => x ∉ (Lpre.1 : Set (E 3)))
  have hDrop1 : Drop1 ⊆ pointsOn M l := by
    intro x hx
    simp only [Drop1, S, pointsOn, Finset.mem_filter] at hx ⊢
    rcases hx with ⟨⟨hxM, hxP⟩, hxl⟩
    exact ⟨hxM, hxl⟩
  have hDrop2 : Drop2 ⊆ pointsOn M Lpre := by
    intro x hx
    simp only [Drop2, S0, S, pointsOn, Finset.mem_filter] at hx ⊢
    rcases hx with ⟨⟨⟨hxM, hxP⟩, hxnotl⟩, hxpre⟩
    exact ⟨hxM, hxpre⟩
  have hDrop1R : (Drop1.card : ℝ) < η₁ * ℓ :=
    (Nat.cast_le.mpr (Finset.card_le_card hDrop1)).trans_lt (hnonline l)
  have hDrop2R : (Drop2.card : ℝ) < η₁ * ℓ :=
    (Nat.cast_le.mpr (Finset.card_le_card hDrop2)).trans_lt (hnonline Lpre)
  have hpart1 := Finset.card_filter_add_card_filter_not
    (s := S) (fun x => x ∈ (l.1 : Set (E 3)))
  have hpart1' : Drop1.card + S0.card = S.card := by
    simpa [Drop1, S0] using hpart1
  have hpart2 := Finset.card_filter_add_card_filter_not
    (s := S0) (fun x => x ∈ (Lpre.1 : Set (E 3)))
  have hpart2' : Drop2.card + Keep.card = S0.card := by
    simpa [Drop2, Keep] using hpart2
  have hKeepR : (η₂ - 2 * η₁) * ℓ < (Keep.card : ℝ) := by
    have hSreal : η₂ * ℓ ≤ (S.card : ℝ) := by simpa [S] using hOcc
    have hpart1R : (Drop1.card : ℝ) + S0.card = S.card := by exact_mod_cast hpart1'
    have hpart2R : (Drop2.card : ℝ) + Keep.card = S0.card := by exact_mod_cast hpart2'
    have hηprod : η₁ * ℓ < η₂ * ℓ := mul_lt_mul_of_pos_right hη hℓ
    linarith
  have hKeepSub : Keep ⊆
      matchPoints (planeReducedPoints X P l) (planeReducedPoints Y Q l') g := by
    intro x hx
    simp only [Keep, S0, S, M, Finset.mem_filter, pointsOn, matchPoints] at hx
    rcases hx with ⟨⟨⟨hmatch, hxP⟩, hxnotl⟩, hxnotpre⟩
    rcases hmatch with ⟨hxX, hgxY⟩
    have hgxQ : g x ∈ Q.1 := by
      have hxmap : g x ∈ P.1.map g.toAffineIsometry.toAffineMap := ⟨x, hxP, rfl⟩
      simpa [hmap] using hxmap
    have hgxnotl : g x ∉ (l'.1 : Set (E 3)) := by
      intro hgxl
      have hxpre : x ∈ (Lpre.1 : Set (E 3)) :=
        (flatImage_symm_mem l' g x).2 hgxl
      exact hxnotpre hxpre
    have hxbase : x ∈ pointsOn X P := by simp [pointsOn, hxX, hxP]
    have hxred : x ∈ planeReducedPoints X P l := by
      change x ∈ (pointsOn X P).filter (fun y => y ∉ (l.1 : Set (E 3)))
      exact Finset.mem_filter.mpr ⟨hxbase, hxnotl⟩
    have hgxbase : g x ∈ pointsOn Y Q := by simp [pointsOn, hgxY, hgxQ]
    have hgxred : g x ∈ planeReducedPoints Y Q l' := by
      change g x ∈ (pointsOn Y Q).filter (fun y => y ∉ (l'.1 : Set (E 3)))
      exact Finset.mem_filter.mpr ⟨hgxbase, hgxnotl⟩
    change x ∈ (planeReducedPoints X P l).filter
      (fun y => g y ∈ planeReducedPoints Y Q l')
    exact Finset.mem_filter.mpr ⟨hxred, hgxred⟩
  have hKeepCard : Keep.card ≤
      matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g := by
    change Keep.card ≤
      (matchPoints (planeReducedPoints X P l) (planeReducedPoints Y Q l') g).card
    exact Finset.card_le_card hKeepSub
  have hceil : Nat.ceil ((η₂ - 2 * η₁) * ℓ) ≤ Keep.card := by
    exact Nat.ceil_le.mpr (le_of_lt hKeepR)
  exact hceil.trans hKeepCard

private theorem reduced_matchCount_le_source (X Y : Finset (E 3)) (g : Motion 3) :
    matchCount X Y g ≤ X.card := by
  change (matchPoints X Y g).card ≤ X.card
  simp only [matchPoints]
  exact Finset.card_filter_le _ _

private theorem reduced_matchCount_le_target (X Y : Finset (E 3)) (g : Motion 3) :
    matchCount X Y g ≤ Y.card := by
  classical
  let M := matchPoints X Y g
  have himage : (M.image g).card = M.card := Finset.card_image_of_injective _ g.injective
  have hsub : M.image g ⊆ Y := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact (Finset.mem_filter.mp hx).2
  change M.card ≤ Y.card
  calc
    M.card = (M.image g).card := himage.symm
    _ ≤ Y.card := Finset.card_le_card hsub

private theorem planar_witness_effective_sizes (η₁ η₂ ℓ : ℝ)
    (hη : η₁ < η₂) (hℓ : 0 < ℓ) (X Y : Finset (E 3)) (g : Motion 3)
    (P : Plane 3) (hOcc : η₂ * ℓ ≤ (pointsOn (matchPoints X Y g) P).card)
    (hnonline : nonLineType η₁ ℓ X Y g) :
    Nat.ceil ((η₂ - 2 * η₁) * ℓ) ≤ effectiveSize X P ∧
      Nat.ceil ((η₂ - 2 * η₁) * ℓ) ≤ effectiveSize Y (planeImage P g) := by
  let Q := planeImage P g
  let l := richestLineOf X P
  let l' := richestLineOf Y Q
  have hred := reduced_plane_matches_lower η₁ η₂ ℓ X Y P Q g hη hℓ
    (show P.1.map g.toAffineIsometry.toAffineMap = Q.1 from rfl)
    hOcc hnonline l l' (richestLineOf_spec X P).1 (richestLineOf_spec Y Q).1
  have hcountX := reduced_matchCount_le_source
    (planeReducedPoints X P l) (planeReducedPoints Y Q l') g
  have hcountY := reduced_matchCount_le_target
    (planeReducedPoints X P l) (planeReducedPoints Y Q l') g
  refine ⟨?_, ?_⟩
  · calc
      Nat.ceil ((η₂ - 2 * η₁) * ℓ) ≤
          matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g := hred
      _ ≤ (planeReducedPoints X P l).card := hcountX
      _ = effectiveSize X P :=
        planeReducedPoints_card X P l (richestLineOf_spec X P).1 (richestLineOf_spec X P).2
  · calc
      Nat.ceil ((η₂ - 2 * η₁) * ℓ) ≤
          matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g := hred
      _ ≤ (planeReducedPoints Y Q l').card := hcountY
      _ = effectiveSize Y Q :=
        planeReducedPoints_card Y Q l' (richestLineOf_spec Y Q).1 (richestLineOf_spec Y Q).2

private theorem planar_witness_pair_data (η₁ η₂ ℓ : ℝ) (hη₁ : 0 < η₁)
    (hη : η₁ < η₂) (hℓ : 0 < ℓ) (h2 : 2 ≤ η₂ * ℓ)
    (X Y : Finset (E 3)) (g : Motion 3) (hnonline : nonLineType η₁ ℓ X Y g)
    (hplanar : planarType η₂ ℓ X Y g) (k : ℕ)
    (hk : 3 ≤ k) (hkceil : k ≤ Nat.ceil ((η₂ - 2 * η₁) * ℓ)) :
    ∃ P Q : Plane 3, ∃ l l' : Line 3,
      P.1.map g.toAffineIsometry.toAffineMap = Q.1 ∧
      η₂ * ℓ ≤ (pointsOn (matchPoints X Y g) P).card ∧
      l.1 ≤ P.1 ∧
      (pointsOn X l).card = richestLineOccupancy X P ∧
      l'.1 ≤ Q.1 ∧
      (pointsOn Y l').card = richestLineOccupancy Y Q ∧
      k ≤ matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g ∧
      k ≤ (planeReducedCoordinates X P l).card ∧
      k ≤ (planeReducedCoordinates Y Q l').card := by
  classical
  rcases hplanar with ⟨P, hOcc⟩
  let Q : Plane 3 := planeImage P g
  letI : Nonempty P.1 := plane_nonempty P
  letI : Nonempty Q.1 := plane_nonempty Q
  have hmap : P.1.map g.toAffineIsometry.toAffineMap = Q.1 := rfl
  obtain ⟨l, hl, hmax⟩ := richestLine_attained X P
  obtain ⟨l', hl', hmax'⟩ := richestLine_attained Y Q
  have hmatch := reduced_plane_matches_lower η₁ η₂ ℓ X Y P Q g hη hℓ
    hmap hOcc hnonline l l' hl hl'
  have hkmatch : k ≤
      matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g :=
    hkceil.trans hmatch
  have hsource :
      matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g ≤
        (planeReducedPoints X P l).card := by
    change ((planeReducedPoints X P l).filter
      (fun x => g x ∈ planeReducedPoints Y Q l')).card ≤ _
    exact Finset.card_filter_le _ _
  have htarget :
      matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g ≤
        (planeReducedPoints Y Q l').card := by
    let M := matchPoints (planeReducedPoints X P l) (planeReducedPoints Y Q l') g
    have himage : (M.image g).card = M.card :=
      Finset.card_image_of_injective _ g.injective
    have hsub : M.image g ⊆ planeReducedPoints Y Q l' := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.mp hx).2
    change M.card ≤ (planeReducedPoints Y Q l').card
    calc
      M.card = (M.image g).card := himage.symm
      _ ≤ _ := Finset.card_le_card hsub
  refine ⟨P, Q, l, l', hmap, hOcc, hl, hmax, hl', hmax', hkmatch, ?_, ?_⟩
  · rw [planeReducedCoordinates_card]
    exact hkmatch.trans hsource
  · rw [planeReducedCoordinates_card]
    exact hkmatch.trans htarget

private theorem nat_dyadic_level_spec (e k n : ℕ) (hk : 0 < k) (hke : k ≤ e)
    (hen : e ≤ n) :
    ∃ j : ℕ, j ≤ Nat.log 4 n ∧ k * 4 ^ j ≤ e ∧ e < k * 4 ^ (j + 1) := by
  let j : ℕ := Nat.log 4 (e / k)
  have hqpos : 0 < e / k := Nat.div_pos hke hk
  have hqne : e / k ≠ 0 := Nat.ne_of_gt hqpos
  have hpowlo : 4 ^ j ≤ e / k := by
    exact Nat.pow_log_le_self 4 hqne
  have hlo : k * 4 ^ j ≤ e := by
    calc
      k * 4 ^ j ≤ k * (e / k) := Nat.mul_le_mul_left k hpowlo
      _ = (e / k) * k := by ring
      _ ≤ e := Nat.div_mul_le_self e k
  have hqhi : e / k < 4 ^ (j + 1) := by
    simpa [j, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) (e / k))
  have hhi' : e < 4 ^ (j + 1) * k := (Nat.div_lt_iff_lt_mul hk).mp hqhi
  have hhi : e < k * 4 ^ (j + 1) := by simpa [Nat.mul_comm] using hhi'
  have hquot : e / k ≤ n := (Nat.div_le_self e k).trans hen
  refine ⟨j, ?_, hlo, hhi⟩
  dsimp [j]
  exact Nat.log_mono_right hquot

private theorem sum_half_powers_eq (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) = 2 - 2 * (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

private theorem sum_half_powers_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) ≤ 2 := by
  rw [sum_half_powers_eq]
  have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ N := pow_nonneg (by norm_num) _
  linarith

private theorem nat_dyadic_inv_sqrt (k j : ℕ) (hk : 0 < k) :
    ((k * 4 ^ j : ℕ) : ℝ) ^ ((-1 : ℝ) / 2) =
      (k : ℝ) ^ ((-1 : ℝ) / 2) * (1 / 2 : ℝ) ^ j := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hpow0 : 0 ≤ (4 : ℝ) ^ j := by positivity
  have h4 : (4 : ℝ) ^ ((-1 : ℝ) / 2) = (1 / 2 : ℝ) := by
    rw [show (-1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg (by norm_num : 0 ≤ (4 : ℝ)) (1 / 2),
      ← Real.sqrt_eq_rpow (4 : ℝ)]
    norm_num
  have hpow : ((4 : ℝ) ^ j) ^ ((-1 : ℝ) / 2) = (1 / 2 : ℝ) ^ j := by
    rw [← Real.rpow_natCast (4 : ℝ) j]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (4 : ℝ)) (j : ℝ) ((-1 : ℝ) / 2)]
    rw [show (j : ℝ) * ((-1 : ℝ) / 2) = ((-1 : ℝ) / 2) * j by ring]
    rw [Real.rpow_mul_natCast (by norm_num : 0 ≤ (4 : ℝ)) ((-1 : ℝ) / 2) j, h4]
  push_cast
  rw [Real.mul_rpow hk0 hpow0, hpow]

private theorem rpow_three_halves_ratio (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x * y) ^ ((3 : ℝ) / 2) / (x ^ 2 * y ^ 2) =
      x ^ ((-1 : ℝ) / 2) * y ^ ((-1 : ℝ) / 2) := by
  have hsubx : x ^ ((3 : ℝ) / 2) / x ^ 2 = x ^ ((-1 : ℝ) / 2) := by
    have hthree : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring, Real.rpow_add hx,
        Real.rpow_one, ← Real.sqrt_eq_rpow x]
    have hminus : x ^ ((-1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
      rw [show (-1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg (le_of_lt hx), ← Real.sqrt_eq_rpow x]
    rw [hthree, hminus]
    field_simp [ne_of_gt hx, ne_of_gt (Real.sqrt_pos.2 hx)]
    rw [Real.sq_sqrt hx.le]
  have hsuby : y ^ ((3 : ℝ) / 2) / y ^ 2 = y ^ ((-1 : ℝ) / 2) := by
    have hthree : y ^ ((3 : ℝ) / 2) = y * Real.sqrt y := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring, Real.rpow_add hy,
        Real.rpow_one, ← Real.sqrt_eq_rpow y]
    have hminus : y ^ ((-1 : ℝ) / 2) = (Real.sqrt y)⁻¹ := by
      rw [show (-1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg (le_of_lt hy), ← Real.sqrt_eq_rpow y]
    rw [hthree, hminus]
    field_simp [ne_of_gt hy, ne_of_gt (Real.sqrt_pos.2 hy)]
    rw [Real.sq_sqrt hy.le]
  rw [Real.mul_rpow hx.le hy.le]
  calc
    _ = (x ^ ((3 : ℝ) / 2) / x ^ 2) *
        (y ^ ((3 : ℝ) / 2) / y ^ 2) := by
          field_simp [ne_of_gt (pow_pos hx 2), ne_of_gt (pow_pos hy 2)] <;> ring
    _ = _ := by rw [hsubx, hsuby]

set_option maxHeartbeats 12000000 in
private theorem planar_pair_motion_bound (Cplan : ℝ)
    (hPlanar : ∀ (U V : Finset (E 2)) (k : ℕ), 3 ≤ k → k ≤ min U.card V.card →
      FiniteCardBound (richMotions U V k)
        (Cplan * ((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2))
    (η₁ η₂ ℓ : ℝ) (hη₁ : 0 < η₁)
    (hη : η₁ < η₂) (hℓ : 0 < ℓ) (h2 : 2 ≤ η₂ * ℓ)
    (k : ℕ) (hk : 3 ≤ k) (X Y : Finset (E 3)) (P Q : Plane 3)
    [Nonempty P.1] [Nonempty Q.1] (l l' : Line 3)
    (hU : k ≤ (planeReducedCoordinates X P l).card)
    (hV : k ≤ (planeReducedCoordinates Y Q l').card) :
    FiniteCardBound
        {g : Motion 3 | P.1.map g.toAffineIsometry.toAffineMap = Q.1 ∧
          η₂ * ℓ ≤ (pointsOn (matchPoints X Y g) P).card ∧
          nonLineType η₁ ℓ X Y g ∧
          k ≤ matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g}
        (2 * Cplan *
          (((planeReducedCoordinates X P l).card : ℝ) *
            (planeReducedCoordinates Y Q l').card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by
  classical
  let U := planeReducedCoordinates X P l
  let V := planeReducedCoordinates Y Q l'
  let G : Set (Motion 3) := {g | P.1.map g.toAffineIsometry.toAffineMap = Q.1 ∧
    η₂ * ℓ ≤ (pointsOn (matchPoints X Y g) P).card ∧
    nonLineType η₁ ℓ X Y g ∧
    k ≤ matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g}
  have hGsubset : G ⊆
      {g : Motion 3 | ¬ Collinear ℝ (matchPoints X Y g : Set (E 3))} := by
    intro g hg hcol
    have hnot := plane_matches_not_collinear X Y P η₁ η₂ ℓ g hη₁ hη hℓ h2
      hg.2.1 hg.2.2.1
    have hsub : (pointsOn (matchPoints X Y g) P : Set (E 3)) ⊆
        (matchPoints X Y g : Set (E 3)) := by
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    exact hnot (Collinear.subset hsub hcol)
  have hGfinite : G.Finite := (spatial_motions_finite X Y).subset hGsubset
  have hGcard : (G.ncard : ℝ) ≤ 2 * Cplan *
      (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by
    let Gfin := hGfinite.toFinset
    let G' := Gfin.attach
    let φ : {g // g ∈ Gfin} → Motion 2 := fun g =>
      motionOnPlanes P Q g.1 ((hGfinite.mem_toFinset (a := g.1)).mp g.2 |>.1)
    let F : Finset (Motion 2) := G'.image φ
    let R : Set (Motion 2) := richMotions U V k
    have hR := hPlanar U V k hk (Nat.le_min.mpr ⟨hU, hV⟩)
    have hRfinite : R.Finite := by
      change (richMotions U V k).Finite
      exact hR.1
    have hRbound : (R.ncard : ℝ) ≤ Cplan *
        (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by
      change ((richMotions U V k).ncard : ℝ) ≤ _
      calc
        _ ≤ Cplan * ((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2 := hR.2
        _ = Cplan * (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by ring
    have hFsubset : (F : Set (Motion 2)) ⊆ R := by
      intro f hf
      rcases Finset.mem_image.mp hf with ⟨g, hg, rfl⟩
      have hgG : g.1 ∈ G := (hGfinite.mem_toFinset (a := g.1)).mp g.2
      rcases hgG with ⟨hmap, hocc, hline, hcnt⟩
      let hmap' := (hGfinite.mem_toFinset (a := g.1)).mp g.2 |>.1
      have hmem : φ g ∈ richMotions U V k := by
        simp only [richMotions, Set.mem_setOf_eq]
        rw [show φ g = motionOnPlanes P Q g.1 hmap' from rfl]
        rw [planeReduced_matchCount X Y P Q l l' g.1 hmap']
        exact_mod_cast hcnt
      exact hmem
    have hFcard : (F.card : ℝ) ≤ (R.ncard : ℝ) := by
      have hsub : F ⊆ hRfinite.toFinset := by
        intro f hf
        exact (hRfinite.mem_toFinset (a := f)).2 (hFsubset (Finset.mem_coe.mpr hf))
      rw [Set.ncard_eq_toFinset_card R hRfinite]
      exact_mod_cast Finset.card_le_card hsub
    have hmap : ∀ g ∈ G', φ g ∈ F := fun g hg => Finset.mem_image.mpr ⟨g, hg, rfl⟩
    have hsumNat := Finset.card_eq_sum_card_fiberwise hmap
    have hsum : (G'.card : ℝ) =
        ∑ f ∈ F, ((G'.filter (fun g => φ g = f)).card : ℝ) := by
      exact_mod_cast hsumNat
    have hfiber (f : Motion 2) (hf : f ∈ F) :
        ((G'.filter (fun g => φ g = f)).card : ℝ) ≤ 2 := by
      let T := G'.filter (fun g => φ g = f)
      by_cases hT : T.Nonempty
      · obtain ⟨g₀, hg₀⟩ := hT
        have hg₀G : g₀.1 ∈ G := (hGfinite.mem_toFinset (a := g₀.1)).mp g₀.2
        have hnoncol := plane_matches_not_collinear X Y P η₁ η₂ ℓ g₀.1 hη₁ hη hℓ h2
          hg₀G.2.1 hg₀G.2.2.1
        obtain ⟨a, ha, b, hb, c, hc, habc⟩ :=
          exists_noncollinear_triple_of_not_collinear
            (pointsOn (matchPoints X Y g₀.1) P)
            hnoncol
        have haM : a ∈ matchPoints X Y g₀.1 := (Finset.mem_filter.mp ha).1
        have hbM : b ∈ matchPoints X Y g₀.1 := (Finset.mem_filter.mp hb).1
        have hcM : c ∈ matchPoints X Y g₀.1 := (Finset.mem_filter.mp hc).1
        let aP : P.1 := ⟨a, (Finset.mem_filter.mp ha).2⟩
        let bP : P.1 := ⟨b, (Finset.mem_filter.mp hb).2⟩
        let cP : P.1 := ⟨c, (Finset.mem_filter.mp hc).2⟩
        let u := g₀.1 a
        let v := g₀.1 b
        let w := g₀.1 c
        let Tri : Set (Motion 3) := {g | g a = u ∧ g b = v ∧ g c = w}
        have hTri := finite_motions_with_triangle_images a b c u v w habc
        have hmapTri : (T : Set {g // g ∈ Gfin}).MapsTo (fun g => g.1) hTri.1.toFinset := by
          intro g hg
          have hgG : g.1 ∈ G := (hGfinite.mem_toFinset (a := g.1)).mp g.2
          have hφ : φ g = φ g₀ := by
            exact (Finset.mem_filter.mp hg).2.trans (Finset.mem_filter.mp hg₀).2.symm
          have hEqAt (x : E 3) (hx : x ∈ P.1) : g.1 x = g₀.1 x := by
            let xP : P.1 := ⟨x, hx⟩
            obtain ⟨y, hy, hycoord⟩ := motionOnPlanes_apply P Q g.1 hgG.1 xP
            obtain ⟨y₀, hy₀, hycoord₀⟩ := motionOnPlanes_apply P Q g₀.1 hg₀G.1 xP
            have hcoords : (planeCoordinates Q).symm y = (planeCoordinates Q).symm y₀ := by
              calc
                (planeCoordinates Q).symm y = (φ g) ((planeCoordinates P).symm xP) := hycoord.symm
                _ = (φ g₀) ((planeCoordinates P).symm xP) := by
                  exact congrArg (fun m : Motion 2 => m ((planeCoordinates P).symm xP)) hφ
                _ = (planeCoordinates Q).symm y₀ := hycoord₀
            have hyy : y = y₀ := (planeCoordinates Q).symm.injective hcoords
            have hval := congrArg (fun z : Q.1 => (z : E 3)) hyy
            rw [hy, hy₀] at hval
            exact hval
          have hta : g.1 a = u := by simpa [u] using hEqAt a aP.property
          have htb : g.1 b = v := by simpa [v] using hEqAt b bP.property
          have htc : g.1 c = w := by simpa [w] using hEqAt c cP.property
          exact (hTri.1.mem_toFinset (a := g.1)).2 ⟨hta, htb, htc⟩
        have hinj : ((G'.filter (fun g => φ g = f)) : Set {g // g ∈ Gfin}).InjOn
            (fun g => g.1) := by
          intro g hg g' hg' heq
          exact Subtype.ext heq
        have hcardNat : (G'.filter (fun g => φ g = f)).card ≤ hTri.1.toFinset.card :=
          Finset.card_le_card_of_injOn (fun g : {g // g ∈ Gfin} => g.1) hmapTri hinj
        have hcardR : (T.card : ℝ) ≤ (Tri.ncard : ℝ) := by
          rw [Set.ncard_eq_toFinset_card Tri hTri.1]
          exact_mod_cast hcardNat
        exact hcardR.trans hTri.2
      · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
        have hTempty' : G'.filter (fun g => φ g = f) = ∅ := by
          simpa [T] using hTempty
        simp [hTempty']
    have hsumle :
        (∑ f ∈ F, ((G'.filter (fun g => φ g = f)).card : ℝ)) ≤
          ∑ f ∈ F, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro f hf
      exact hfiber f hf
    have hGcardR : (G.ncard : ℝ) = (G'.card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card G hGfinite]
      change (Gfin.card : ℝ) = (Gfin.attach.card : ℝ)
      simp
    calc
      (G.ncard : ℝ) = (G'.card : ℝ) := hGcardR
      _ = ∑ f ∈ F, ((G'.filter (fun g => φ g = f)).card : ℝ) := hsum
      _ ≤ ∑ f ∈ F, (2 : ℝ) := hsumle
      _ = 2 * F.card := by simp [mul_comm]
      _ ≤ 2 * (R.ncard : ℝ) := mul_le_mul_of_nonneg_left hFcard (by norm_num)
      _ ≤ 2 * (Cplan * (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hRbound (by norm_num)
      _ = 2 * Cplan * (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by ring
  change FiniteCardBound G _
  constructor
  · exact hGfinite
  · calc
      (G.ncard : ℝ) ≤ 2 * Cplan *
          ((((planeReducedCoordinates X P l).card : ℝ) *
            (planeReducedCoordinates Y Q l').card) ^ ((3 : ℝ) / 2) /
              (k : ℝ) ^ 2) := by
            simpa [U, V] using hGcard
      _ = 2 * Cplan *
          (((planeReducedCoordinates X P l).card : ℝ) *
            (planeReducedCoordinates Y Q l').card) ^ ((3 : ℝ) / 2) /
              (k : ℝ) ^ 2 := by ring

private theorem effective_plane_power_sum_bound (Ceff Keff : ℝ) (hKeff : 0 < Keff)
    (hEff : ∀ (X : Finset (E 3)) (m H : ℝ), 1 ≤ m →
      (X.card : ℝ) ≤ m → Ceff * m ^ ((2 : ℝ) / 3) ≤ H →
      FiniteCardBound {P : Plane 3 | H ≤ (effectiveSize X P : ℝ)}
        (Keff * m ^ 2 / H ^ 2))
    (X : Finset (E 3)) (m H : ℝ) (hm : 1 ≤ m) (hXm : (X.card : ℝ) ≤ m)
    (hthreshold : Ceff * m ^ ((2 : ℝ) / 3) ≤ H)
    (S : Finset (Plane 3)) (hS : ∀ P ∈ S, H ≤ (effectiveSize X P : ℝ))
    (k : ℕ) (hkEq : k = Nat.ceil H) (hk : 0 < k) :
    (∑ P ∈ S, (effectiveSize X P : ℝ) ^ ((3 : ℝ) / 2)) ≤
      16 * Keff * m ^ 2 * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  classical
  let N : ℕ := Nat.log 4 (X.card + 1) + 1
  let J : Finset ℕ := Finset.range N
  let e (P : Plane 3) : ℕ := effectiveSize X P
  let term (P : Plane 3) (j : ℕ) : ℝ :=
    if k * 4 ^ j ≤ e P then
      ((4 * (k * 4 ^ j) : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
    else 0
  have hkH : H ≤ (k : ℝ) := by
    rw [hkEq]
    exact Nat.le_ceil H
  have hpointwise (P : Plane 3) (hP : P ∈ S) :
      (e P : ℝ) ^ ((3 : ℝ) / 2) ≤ ∑ j ∈ J, term P j := by
    have hke : k ≤ e P := by
      have hceil : Nat.ceil H ≤ e P := Nat.ceil_le.mpr (hS P hP)
      simpa [hkEq] using hceil
    have heX : e P ≤ X.card := by
      dsimp [e, effectiveSize]
      exact (Nat.sub_le _ _).trans (Finset.card_filter_le _ _)
    have hen : e P ≤ X.card + 1 := by omega
    obtain ⟨j, hjlog, hjlo, hjhi⟩ :=
      nat_dyadic_level_spec (e P) k (X.card + 1) hk hke hen
    have hjmem : j ∈ J := by
      simp [J, N]
      exact hjlog
    have hjle : e P ≤ 4 * (k * 4 ^ j) := by
      have hmul : k * 4 ^ (j + 1) = 4 * (k * 4 ^ j) := by
        rw [pow_succ]
        ring
      rw [← hmul]
      exact Nat.le_of_lt hjhi
    have hpow : (e P : ℝ) ^ ((3 : ℝ) / 2) ≤
        ((4 * (k * 4 ^ j) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _)
      · exact_mod_cast hjle
      · norm_num
    have hterm : (e P : ℝ) ^ ((3 : ℝ) / 2) ≤ term P j := by
      simpa [term, hjlo, Nat.cast_mul, Nat.cast_pow] using hpow
    exact hterm.trans (Finset.single_le_sum (f := term P)
      (fun j' hj' => by positivity [term]) hjmem)
  have hsumPointwise :
      (∑ P ∈ S, (e P : ℝ) ^ ((3 : ℝ) / 2)) ≤
        ∑ P ∈ S, ∑ j ∈ J, term P j := by
    apply Finset.sum_le_sum
    intro P hP
    exact hpointwise P hP
  have hswap :
      (∑ P ∈ S, ∑ j ∈ J, term P j) =
        ∑ j ∈ J, ∑ P ∈ S, term P j := by rw [Finset.sum_comm]
  have htermBound (j : ℕ) (hj : j ∈ J) :
      (∑ P ∈ S, term P j) ≤
        8 * Keff * m ^ 2 * (k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ j := by
    let t : ℕ := k * 4 ^ j
    let Tail : Set (Plane 3) := {P | (t : ℝ) ≤ (effectiveSize X P : ℝ)}
    have hpowNat : 1 ≤ 4 ^ j := Nat.one_le_pow j 4 (by decide)
    have hkTnat : k ≤ t := by
      dsimp [t]
      calc
        k = k * 1 := by simp
        _ ≤ k * 4 ^ j := Nat.mul_le_mul_left k hpowNat
    have htH : Ceff * m ^ ((2 : ℝ) / 3) ≤ (t : ℝ) := by
      calc
        Ceff * m ^ ((2 : ℝ) / 3) ≤ H := hthreshold
        _ ≤ (k : ℝ) := hkH
        _ ≤ (t : ℝ) := by exact_mod_cast hkTnat
    have hTail := hEff X m (t : ℝ) hm hXm htH
    have hTailSub : (S.filter (fun P => t ≤ e P) : Set (Plane 3)) ⊆ Tail := by
      intro P hP
      have hPe : t ≤ e P := (Finset.mem_filter.mp hP).2
      change (t : ℝ) ≤ (effectiveSize X P : ℝ)
      exact_mod_cast hPe
    have hFilterSub : S.filter (fun P => t ≤ e P) ⊆ hTail.1.toFinset := by
      intro P hP
      exact (hTail.1.mem_toFinset).2 (hTailSub (Finset.mem_coe.mpr hP))
    have hFilterCard :
        ((S.filter (fun P => t ≤ e P)).card : ℝ) ≤
          Keff * m ^ 2 / (t : ℝ) ^ 2 := by
      have hnat := Finset.card_le_card hFilterSub
      have hTailBound' := hTail.2
      rw [Set.ncard_eq_toFinset_card Tail hTail.1] at hTailBound'
      calc
        _ ≤ (hTail.1.toFinset.card : ℝ) := by exact_mod_cast hnat
        _ ≤ Keff * m ^ 2 / (t : ℝ) ^ 2 := hTailBound'
    let A : ℝ := ((4 * t : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
    have hAover : A / (t : ℝ) ^ 2 = 8 * (t : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have htpos : 0 < (t : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le hk hkTnat)
      have hratio := rpow_three_halves_ratio 1 (t : ℝ) (by norm_num) htpos
      have hfour : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring, Real.rpow_add (by norm_num),
          Real.rpow_one, ← Real.sqrt_eq_rpow]
        norm_num
      have hmul :
          ((4 : ℝ) * (t : ℝ)) ^ ((3 : ℝ) / 2) =
            (4 : ℝ) ^ ((3 : ℝ) / 2) * (t : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) (le_of_lt htpos)
      dsimp [A]
      rw [Nat.cast_mul]
      norm_num
      rw [hmul, hfour]
      have hratio' : (t : ℝ) ^ ((3 : ℝ) / 2) / (t : ℝ) ^ 2 =
          (t : ℝ) ^ (-(1 / 2 : ℝ)) := by
        norm_num at hratio
        simpa only [one_mul, one_pow, Real.one_rpow] using hratio
      calc
        8 * (t : ℝ) ^ ((3 : ℝ) / 2) / (t : ℝ) ^ 2 =
            8 * ((t : ℝ) ^ ((3 : ℝ) / 2) / (t : ℝ) ^ 2) := by ring
        _ = 8 * (t : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hratio']
    have hsumFilter :
        (∑ P ∈ S, term P j) =
          ((S.filter (fun P => t ≤ e P)).card : ℝ) * A := by
      rw [← Finset.sum_filter]
      simp [term, A, t, mul_comm]
    have hA_nonneg : 0 ≤ A := by positivity
    have hbound :
        ((S.filter (fun P => t ≤ e P)).card : ℝ) * A ≤
          8 * Keff * m ^ 2 * (t : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have htpos : 0 < (t : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le hk hkTnat)
      calc
        _ ≤ (Keff * m ^ 2 / (t : ℝ) ^ 2) * A :=
          mul_le_mul_of_nonneg_right hFilterCard hA_nonneg
        _ = Keff * m ^ 2 * (A / (t : ℝ) ^ 2) := by
          field_simp [ne_of_gt htpos]
        _ = 8 * Keff * m ^ 2 * (t : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [hAover]
          ring
    have hInv :
        (t : ℝ) ^ (-(1 / 2 : ℝ)) = (k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ j := by
      have hInv0 := nat_dyadic_inv_sqrt k j hk
      norm_num at hInv0
      simpa [t] using hInv0
    rw [hsumFilter]
    calc
      ((S.filter (fun P => t ≤ e P)).card : ℝ) * A ≤
          8 * Keff * m ^ 2 * (t : ℝ) ^ (-(1 / 2 : ℝ)) := hbound
      _ = 8 * Keff * m ^ 2 * (k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ j := by
        rw [hInv]
        ring
  have hsumLevels :
      (∑ j ∈ J, 8 * Keff * m ^ 2 * (k : ℝ) ^ (-(1 / 2 : ℝ)) *
        (1 / 2 : ℝ) ^ j) ≤ 16 * Keff * m ^ 2 * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    let A : ℝ := 8 * Keff * m ^ 2 * (k : ℝ) ^ (-(1 / 2 : ℝ))
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hgeo := sum_half_powers_le_two N
    calc
      (∑ j ∈ J, A * (1 / 2 : ℝ) ^ j) = A * ∑ j ∈ J, (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
      _ ≤ A * 2 := mul_le_mul_of_nonneg_left (by simpa [J, N] using hgeo) hA
      _ = 16 * Keff * m ^ 2 * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by dsimp [A]; ring
  calc
    _ ≤ ∑ P ∈ S, ∑ j ∈ J, term P j := hsumPointwise
    _ = ∑ j ∈ J, ∑ P ∈ S, term P j := hswap
    _ ≤ ∑ j ∈ J,
        8 * Keff * m ^ 2 * (k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          exact htermBound j hj
    _ ≤ 16 * Keff * m ^ 2 * (k : ℝ) ^ (-(1 / 2 : ℝ)) := hsumLevels

/-- Planar-type contribution, motions.tex:483–535. -/
theorem planar_type_motion_bound (η₁ η₂ : ℝ) (hη₁ : 0 < η₁) (hη₂ : η₂ < 1)
    (hsmall : 2 * η₁ < η₂) : ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (X Y : Finset (E 3)) (m ℓ : ℝ), 1 ≤ m → (X.card : ℝ) ≤ m →
      (Y.card : ℝ) ≤ m → C * m ^ ((2 : ℝ) / 3) ≤ ℓ →
      FiniteCardBound {g : Motion 3 | g ∈ motionBucket X Y ℓ ∧
        nonLineType η₁ ℓ X Y g ∧ planarType η₂ ℓ X Y g}
        (K * m ^ 4 / ℓ ^ 3) := by
  classical
  obtain ⟨Ceff, Keff, hCeff, hKeff, hEff⟩ := mot_effective_planes
  obtain ⟨Cplan, hCplan, hPlanar⟩ := ci_planar_motions
  let τ : ℝ := η₂ - 2 * η₁
  have hτ : 0 < τ := by dsimp [τ]; linarith [hsmall]
  let C : ℝ := max (Ceff / τ) (max (8 / τ) (3 / τ)) + 1
  let K : ℝ := 512 * Cplan * Keff ^ 2 / τ ^ 3 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, K, hC, hK, ?_⟩
  intro X Y m ℓ hm hXm hYm hℓ
  have hmpos : 0 < m := by linarith
  have hmPow : 1 ≤ m ^ ((2 : ℝ) / 3) := Real.one_le_rpow hm (by norm_num)
  have hpowpos : 0 < m ^ ((2 : ℝ) / 3) := by positivity
  have hℓpos : 0 < ℓ :=
    lt_of_lt_of_le (mul_pos hC hpowpos) hℓ
  let Hbase : ℝ := τ * ℓ
  have hC8 : 8 / τ ≤ C := by
    dsimp [C]
    calc
      8 / τ ≤ max (8 / τ) (3 / τ) := le_max_left _ _
      _ ≤ max (Ceff / τ) (max (8 / τ) (3 / τ)) := le_max_right _ _
      _ ≤ max (Ceff / τ) (max (8 / τ) (3 / τ)) + 1 :=
        le_add_of_nonneg_right (by norm_num)
  have hC3 : 3 / τ ≤ C := by
    dsimp [C]
    calc
      3 / τ ≤ max (8 / τ) (3 / τ) := le_max_right _ _
      _ ≤ max (Ceff / τ) (max (8 / τ) (3 / τ)) := le_max_right _ _
      _ ≤ max (Ceff / τ) (max (8 / τ) (3 / τ)) + 1 :=
        le_add_of_nonneg_right (by norm_num)
  have hCeffBound : Ceff / τ ≤ C := by
    dsimp [C]
    calc
      Ceff / τ ≤ max (Ceff / τ) (max (8 / τ) (3 / τ)) := le_max_left _ _
      _ ≤ max (Ceff / τ) (max (8 / τ) (3 / τ)) + 1 :=
        le_add_of_nonneg_right (by norm_num)
  have hτC8 : 8 ≤ τ * C := by
    calc
      8 ≤ C * τ := (div_le_iff₀ hτ).mp hC8
      _ = τ * C := by ring
  have hτC3 : 3 ≤ τ * C := by
    calc
      3 ≤ C * τ := (div_le_iff₀ hτ).mp hC3
      _ = τ * C := by ring
  have hτCeff : Ceff ≤ τ * C := by
    calc
      Ceff ≤ C * τ := (div_le_iff₀ hτ).mp hCeffBound
      _ = τ * C := by ring
  have hHeff : Ceff * m ^ ((2 : ℝ) / 3) ≤ Hbase := by
    dsimp [Hbase]
    calc
      Ceff * m ^ ((2 : ℝ) / 3) ≤ (τ * C) * m ^ ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hτCeff (by positivity)
      _ = τ * (C * m ^ ((2 : ℝ) / 3)) := by ring
      _ ≤ τ * ℓ := mul_le_mul_of_nonneg_left hℓ hτ.le
  have hH8 : 8 * m ^ ((2 : ℝ) / 3) ≤ Hbase := by
    dsimp [Hbase]
    calc
      8 * m ^ ((2 : ℝ) / 3) ≤ (τ * C) * m ^ ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hτC8 (by positivity)
      _ = τ * (C * m ^ ((2 : ℝ) / 3)) := by ring
      _ ≤ τ * ℓ := mul_le_mul_of_nonneg_left hℓ hτ.le
  have hH3 : 3 ≤ Hbase := by
    dsimp [Hbase]
    calc
      3 ≤ τ * C := hτC3
      _ = (τ * C) * 1 := by ring
      _ ≤ (τ * C) * m ^ ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left hmPow (mul_nonneg hτ.le hC.le)
      _ = τ * (C * m ^ ((2 : ℝ) / 3)) := by ring
      _ ≤ τ * ℓ := mul_le_mul_of_nonneg_left hℓ hτ.le
  have hηrel : η₁ < η₂ := by nlinarith [hη₁, hsmall]
  have hη₂pos : 0 < η₂ := lt_trans hη₁ hηrel
  have hτη : τ < η₂ := by dsimp [τ]; linarith [hη₁]
  have hτellη₂ : τ * ℓ < η₂ * ℓ := mul_lt_mul_of_pos_right hτη hℓpos
  have h2 : 2 ≤ η₂ * ℓ := by dsimp [Hbase] at hH3; linarith
  let k0 : ℕ := Nat.ceil Hbase
  have hk0H : Hbase ≤ (k0 : ℝ) := by dsimp [k0]; exact Nat.le_ceil _
  have hk0pos : 0 < k0 := by
    have hHpos : 0 < Hbase := mul_pos hτ hℓpos
    have h := Nat.one_le_ceil_iff.mpr hHpos
    simpa [k0] using h
  have hk0three : 3 ≤ k0 := by
    have hlt : (2 : ℝ) < Hbase := by dsimp [Hbase]; linarith [hH3]
    have h := Nat.add_one_le_ceil_iff.mpr hlt
    simpa [k0] using h
  let SXset : Set (Plane 3) := {P | Hbase ≤ (effectiveSize X P : ℝ)}
  let SYset : Set (Plane 3) := {P | Hbase ≤ (effectiveSize Y P : ℝ)}
  have hSX : FiniteCardBound SXset (Keff * m ^ 2 / Hbase ^ 2) := by
    simpa [SXset] using hEff X m Hbase hm hXm hHeff
  have hSY : FiniteCardBound SYset (Keff * m ^ 2 / Hbase ^ 2) := by
    simpa [SYset] using hEff Y m Hbase hm hYm hHeff
  let SX : Finset (Plane 3) := hSX.1.toFinset
  let SY : Finset (Plane 3) := hSY.1.toFinset
  have hsumX := effective_plane_power_sum_bound Ceff Keff hKeff hEff X m Hbase
    hm hXm hHeff SX (by
      intro P hP
      exact (hSX.1.mem_toFinset).1 hP) k0 rfl hk0pos
  have hsumY := effective_plane_power_sum_bound Ceff Keff hKeff hEff Y m Hbase
    hm hYm hHeff SY (by
      intro P hP
      exact (hSY.1.mem_toFinset).1 hP) k0 rfl hk0pos
  let G : Set (Motion 3) := {g | g ∈ motionBucket X Y ℓ ∧
    nonLineType η₁ ℓ X Y g ∧ planarType η₂ ℓ X Y g}
  have hGsubset : G ⊆ {g : Motion 3 | ¬ Collinear ℝ (matchPoints X Y g : Set (E 3))} := by
    intro g hg hcol
    rcases hg.2.2 with ⟨P, hOcc⟩
    have hnot := plane_matches_not_collinear X Y P η₁ η₂ ℓ g hη₁ hηrel hℓpos h2
      hOcc hg.2.1
    have hsub : (pointsOn (matchPoints X Y g) P : Set (E 3)) ⊆
        (matchPoints X Y g : Set (E 3)) := by
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    exact hnot (Collinear.subset hsub hcol)
  have hGfinite : G.Finite := (spatial_motions_finite X Y).subset hGsubset
  change (G.Finite ∧ ((G.ncard : ℝ) ≤ K * m ^ 4 / ℓ ^ 3))
  constructor
  · exact hGfinite
  ·
      let Gfin : Finset (Motion 3) := hGfinite.toFinset
      let G' := Gfin.attach
      have hmemG (g : {g // g ∈ Gfin}) : g.1 ∈ G :=
        (hGfinite.mem_toFinset (a := g.1)).mp g.2
      have hplanarMem (g : {g // g ∈ Gfin}) : planarType η₂ ℓ X Y g.1 :=
        (hmemG g).2.2
      let sourcePlane (g : {g // g ∈ Gfin}) : Plane 3 := Classical.choose (hplanarMem g)
      have hsourceOcc (g : {g // g ∈ Gfin}) :
          η₂ * ℓ ≤ (pointsOn (matchPoints X Y g.1) (sourcePlane g)).card :=
        Classical.choose_spec (hplanarMem g)
      let targetPlane (g : {g // g ∈ Gfin}) : Plane 3 := planeImage (sourcePlane g) g.1
      let φ : {g // g ∈ Gfin} → Plane 3 × Plane 3 := fun g => (sourcePlane g, targetPlane g)
      let F : Finset (Plane 3 × Plane 3) := SX.product SY
      have hmap : ∀ g ∈ G', φ g ∈ F := by
        intro g hg
        have hgG := hmemG g
        have hsizes := planar_witness_effective_sizes η₁ η₂ ℓ hηrel hℓpos X Y g.1
          (sourcePlane g) (hsourceOcc g) hgG.2.1
        have hXNat : k0 ≤ effectiveSize X (sourcePlane g) := by
          simpa [k0, Hbase, τ] using hsizes.1
        have hYNat : k0 ≤ effectiveSize Y (targetPlane g) := by
          simpa [targetPlane, k0, Hbase, τ] using hsizes.2
        have hXBase : Hbase ≤ (effectiveSize X (sourcePlane g) : ℝ) := by
          calc
            Hbase ≤ (k0 : ℝ) := hk0H
            _ ≤ (effectiveSize X (sourcePlane g) : ℝ) := by exact_mod_cast hXNat
        have hYBase : Hbase ≤ (effectiveSize Y (targetPlane g) : ℝ) := by
          calc
            Hbase ≤ (k0 : ℝ) := hk0H
            _ ≤ (effectiveSize Y (targetPlane g) : ℝ) := by exact_mod_cast hYNat
        exact Finset.mem_product.mpr
          ⟨(hSX.1.mem_toFinset).2 hXBase, (hSY.1.mem_toFinset).2 hYBase⟩
      let wX : Plane 3 → ℝ := fun P => (effectiveSize X P : ℝ) ^ ((3 : ℝ) / 2)
      let wY : Plane 3 → ℝ := fun P => (effectiveSize Y P : ℝ) ^ ((3 : ℝ) / 2)
      let Acoef : ℝ := 2 * Cplan / (k0 : ℝ) ^ 2
      let pairWeight : Plane 3 × Plane 3 → ℝ := fun PQ => Acoef * wX PQ.1 * wY PQ.2
      have hPairWeight (P Q : Plane 3) :
          pairWeight (P, Q) = Acoef * wX P * wY Q := rfl
      have hFiber (pq : Plane 3 × Plane 3) (hpq : pq ∈ F) :
          ((G'.filter (fun g => φ g = pq)).card : ℝ) ≤ pairWeight pq := by
        rcases pq with ⟨P, Q⟩
        rcases Finset.mem_product.mp hpq with ⟨hPmem, hQmem⟩
        let l := richestLineOf X P
        let l' := richestLineOf Y Q
        have hPbase : Hbase ≤ (effectiveSize X P : ℝ) := (hSX.1.mem_toFinset).1 hPmem
        have hQbase : Hbase ≤ (effectiveSize Y Q : ℝ) := (hSY.1.mem_toFinset).1 hQmem
        have hU : k0 ≤ (planeReducedCoordinates X P l).card := by
          change k0 ≤ (planeReducedCoordinates X P (richestLineOf X P)).card
          rw [planeReducedCoordinates_effective_card]
          simpa [k0] using (Nat.ceil_le.mpr hPbase)
        have hV : k0 ≤ (planeReducedCoordinates Y Q l').card := by
          change k0 ≤ (planeReducedCoordinates Y Q (richestLineOf Y Q)).card
          rw [planeReducedCoordinates_effective_card]
          simpa [k0] using (Nat.ceil_le.mpr hQbase)
        let PairSet : Set (Motion 3) := {g |
          P.1.map g.toAffineIsometry.toAffineMap = Q.1 ∧
          η₂ * ℓ ≤ (pointsOn (matchPoints X Y g) P).card ∧
          nonLineType η₁ ℓ X Y g ∧
          k0 ≤ matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') g}
        have hPair : FiniteCardBound PairSet
            (2 * Cplan *
              (((planeReducedCoordinates X P l).card : ℝ) *
                ((planeReducedCoordinates Y Q l').card : ℝ)) ^ ((3 : ℝ) / 2) /
              (k0 : ℝ) ^ 2) := by
          simpa [PairSet] using
            (planar_pair_motion_bound Cplan hPlanar η₁ η₂ ℓ hη₁ hηrel hℓpos h2
              k0 hk0three X Y P Q l l' hU hV)
        have hPairBound := hPair.2
        rw [Set.ncard_eq_toFinset_card PairSet hPair.1] at hPairBound
        have hPairBoundEff : (hPair.1.toFinset.card : ℝ) ≤ pairWeight (P, Q) := by
          calc
            _ ≤ 2 * Cplan *
                ((effectiveSize X P : ℝ) * (effectiveSize Y Q : ℝ)) ^ ((3 : ℝ) / 2) /
                  (k0 : ℝ) ^ 2 := by
                    simpa [l, l', planeReducedCoordinates_effective_card] using hPairBound
          _ = pairWeight (P, Q) := by
              dsimp [pairWeight, Acoef, wX, wY]
              rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
              ring
        let T := G'.filter (fun g => φ g = (P, Q))
        let Timg := T.image (fun g : {g // g ∈ Gfin} => g.1)
        have hvalinj : Function.Injective (fun g : {g // g ∈ Gfin} => g.1) := by
          intro a b hab
          exact Subtype.ext hab
        have hTimgSub : Timg ⊆ hPair.1.toFinset := by
          intro g hg
          rcases Finset.mem_image.mp hg with ⟨z, hz, rfl⟩
          have hzphi : φ z = (P, Q) := (Finset.mem_filter.mp hz).2
          have hzG := hmemG z
          have hPof : sourcePlane z = P := congrArg Prod.fst hzphi
          have hQof : targetPlane z = Q := congrArg Prod.snd hzphi
          have hocc : η₂ * ℓ ≤ (pointsOn (matchPoints X Y z.1) P).card := by
            simpa [hPof] using hsourceOcc z
          have hmapPQ : P.1.map z.1.toAffineIsometry.toAffineMap = Q.1 := by
            calc
              P.1.map z.1.toAffineIsometry.toAffineMap =
                  (sourcePlane z).1.map z.1.toAffineIsometry.toAffineMap := by rw [hPof]
              _ = (planeImage (sourcePlane z) z.1).1 := rfl
              _ = Q.1 := congrArg Subtype.val hQof
          have hred := reduced_plane_matches_lower η₁ η₂ ℓ X Y P Q z.1 hηrel hℓpos
            hmapPQ hocc hzG.2.1 l l'
            (richestLineOf_spec X P).1 (richestLineOf_spec Y Q).1
          have hcount : k0 ≤
              matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') z.1 := by
            simpa [k0, Hbase, τ] using hred
          have hPairMem : z.1 ∈ PairSet := by
            change P.1.map z.1.toAffineIsometry.toAffineMap = Q.1 ∧
              η₂ * ℓ ≤ (pointsOn (matchPoints X Y z.1) P).card ∧
              nonLineType η₁ ℓ X Y z.1 ∧
              k0 ≤ matchCount (planeReducedPoints X P l) (planeReducedPoints Y Q l') z.1
            exact ⟨hmapPQ, hocc, hzG.2.1, hcount⟩
          exact (hPair.1.mem_toFinset).2 hPairMem
        have hTcard : T.card ≤ hPair.1.toFinset.card := by
          calc
            T.card = Timg.card := (Finset.card_image_of_injective T hvalinj).symm
            _ ≤ hPair.1.toFinset.card := Finset.card_le_card hTimgSub
        calc
          (T.card : ℝ) ≤ (hPair.1.toFinset.card : ℝ) := by exact_mod_cast hTcard
          _ ≤ pairWeight (P, Q) := hPairBoundEff
      have hsumNat := Finset.card_eq_sum_card_fiberwise hmap
      have hsumReal : (G'.card : ℝ) =
          ∑ pq ∈ F, ((G'.filter (fun g => φ g = pq)).card : ℝ) := by
        exact_mod_cast hsumNat
      have hsumFibers :
          (∑ pq ∈ F, ((G'.filter (fun g => φ g = pq)).card : ℝ)) ≤
            ∑ pq ∈ F, pairWeight pq := by
        apply Finset.sum_le_sum
        intro pq hpq
        exact hFiber pq hpq
      have hGcardR : (G.ncard : ℝ) = (G'.card : ℝ) := by
        rw [Set.ncard_eq_toFinset_card G hGfinite]
        change (Gfin.card : ℝ) = (Gfin.attach.card : ℝ)
        simp [G']
      have hpairWeightSum :
          (∑ pq ∈ F, pairWeight pq) =
            Acoef * (∑ P ∈ SX, wX P) * (∑ Q ∈ SY, wY Q) := by
        calc
          (∑ pq ∈ F, pairWeight pq) =
              ∑ P ∈ SX, ∑ Q ∈ SY, pairWeight (P, Q) := by
                simpa [F] using (Finset.sum_product SX SY pairWeight)
          _ = ∑ P ∈ SX, ∑ Q ∈ SY, Acoef * wX P * wY Q := by
                apply Finset.sum_congr rfl
                intro P hP
                apply Finset.sum_congr rfl
                intro Q hQ
                exact hPairWeight P Q
          _ = ∑ P ∈ SX, (Acoef * wX P) * (∑ Q ∈ SY, wY Q) := by
                apply Finset.sum_congr rfl
                intro P hP
                rw [← Finset.mul_sum]
          _ = Acoef * (∑ P ∈ SX, wX P) * (∑ Q ∈ SY, wY Q) := by
                rw [← Finset.sum_mul, ← Finset.mul_sum]
      have hGcard : (G.ncard : ℝ) ≤
          Acoef * (∑ P ∈ SX, wX P) * (∑ Q ∈ SY, wY Q) := by
        calc
          (G.ncard : ℝ) = (G'.card : ℝ) := hGcardR
          _ = ∑ pq ∈ F, ((G'.filter (fun g => φ g = pq)).card : ℝ) := hsumReal
          _ ≤ ∑ pq ∈ F, pairWeight pq := hsumFibers
          _ = Acoef * (∑ P ∈ SX, wX P) * (∑ Q ∈ SY, wY Q) := hpairWeightSum
      let W : ℝ := 16 * Keff * m ^ 2 * (k0 : ℝ) ^ (-(1 / 2 : ℝ))
      have hsumX' : (∑ P ∈ SX, wX P) ≤ W := by simpa [wX, W] using hsumX
      have hsumY' : (∑ Q ∈ SY, wY Q) ≤ W := by simpa [wY, W] using hsumY
      have hsumYnonneg : 0 ≤ ∑ Q ∈ SY, wY Q := by
        apply Finset.sum_nonneg
        intro Q hQ
        positivity
      have hWnonneg : 0 ≤ W := by dsimp [W]; positivity
      have hAcoef : 0 ≤ Acoef := by dsimp [Acoef]; positivity
      have hproduct :
          (∑ P ∈ SX, wX P) * (∑ Q ∈ SY, wY Q) ≤ W * W :=
        mul_le_mul hsumX' hsumY' hsumYnonneg hWnonneg
      have hHpos : 0 < Hbase := mul_pos hτ hℓpos
      have hkposR : 0 < (k0 : ℝ) := by exact_mod_cast hk0pos
      have hcube : Hbase ^ 3 ≤ (k0 : ℝ) ^ 3 :=
        pow_le_pow_left₀ hHpos.le hk0H 3
      have hrecip : 1 / (k0 : ℝ) ^ 3 ≤ 1 / Hbase ^ 3 := by
        rw [div_le_div_iff₀ (by positivity : 0 < (k0 : ℝ) ^ 3)
          (by positivity : 0 < Hbase ^ 3)]
        nlinarith
      have hKcoeff : 512 * Cplan * Keff ^ 2 / τ ^ 3 ≤ K := by
        dsimp [K]
        exact le_add_of_nonneg_right (by norm_num)
      have hcoeff : 0 ≤ 512 * Cplan * Keff ^ 2 * m ^ 4 := by
        positivity
      exact calc
        (G.ncard : ℝ) ≤ Acoef * (∑ P ∈ SX, wX P) * (∑ Q ∈ SY, wY Q) := hGcard
        _ ≤ Acoef * W * W := by
          calc
            Acoef * (∑ P ∈ SX, wX P) * (∑ Q ∈ SY, wY Q) =
                Acoef * ((∑ P ∈ SX, wX P) * (∑ Q ∈ SY, wY Q)) := by ring
            _ ≤ Acoef * (W * W) := mul_le_mul_of_nonneg_left hproduct hAcoef
            _ = Acoef * W * W := by ring
        _ = 512 * Cplan * Keff ^ 2 * m ^ 4 / (k0 : ℝ) ^ 3 := by
          have hkposR : 0 < (k0 : ℝ) := by exact_mod_cast hk0pos
          have hInvSq : ((k0 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (k0 : ℝ) := by
            have hroot : (k0 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (k0 : ℝ))⁻¹ := by
              rw [show -(1 / 2 : ℝ) = -((1 / 2 : ℝ)) by ring,
                Real.rpow_neg (le_of_lt hkposR), ← Real.sqrt_eq_rpow]
            rw [hroot, inv_pow, Real.sq_sqrt hkposR.le]
            simp [div_eq_mul_inv]
          dsimp [Acoef, W]
          have haux :
              (16 * Keff * m ^ 2 * (k0 : ℝ) ^ (-(1 / 2 : ℝ))) *
                (16 * Keff * m ^ 2 * (k0 : ℝ) ^ (-(1 / 2 : ℝ))) =
              256 * Keff ^ 2 * m ^ 4 * ((k0 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by ring
          rw [mul_assoc, haux, hInvSq]
          field_simp [ne_of_gt hkposR]
          <;> ring
        _ ≤ 512 * Cplan * Keff ^ 2 * m ^ 4 / Hbase ^ 3 := by
          calc
            512 * Cplan * Keff ^ 2 * m ^ 4 / (k0 : ℝ) ^ 3 =
                (512 * Cplan * Keff ^ 2 * m ^ 4) * ((k0 : ℝ) ^ 3)⁻¹ := by rw [div_eq_mul_inv]
            _ ≤ (512 * Cplan * Keff ^ 2 * m ^ 4) * (Hbase ^ 3)⁻¹ :=
              mul_le_mul_of_nonneg_left (by simpa [div_eq_mul_inv] using hrecip) hcoeff
            _ = 512 * Cplan * Keff ^ 2 * m ^ 4 / Hbase ^ 3 := by rw [div_eq_mul_inv]
        _ = (512 * Cplan * Keff ^ 2 / τ ^ 3) * m ^ 4 / ℓ ^ 3 := by
          dsimp [Hbase]
          field_simp [ne_of_gt hτ, ne_of_gt hℓpos]
          <;> ring
        _ ≤ K * m ^ 4 / ℓ ^ 3 := by
          calc
            (512 * Cplan * Keff ^ 2 / τ ^ 3) * m ^ 4 / ℓ ^ 3 =
                (512 * Cplan * Keff ^ 2 / τ ^ 3) * (m ^ 4 / ℓ ^ 3) := by ring
            _ ≤ K * (m ^ 4 / ℓ ^ 3) :=
              mul_le_mul_of_nonneg_right hKcoeff (by positivity)
            _ = K * m ^ 4 / ℓ ^ 3 := by ring

/-- mot:local, motions.tex:233–543; both orientations. -/
theorem mot_local : ∃ η C K : ℝ, 0 < η ∧ η < 1 ∧ 0 < C ∧ 0 < K ∧
    ∀ (X Y : Finset (E 3)) (m ℓ : ℝ), 1 ≤ m → (X.card : ℝ) ≤ m →
      (Y.card : ℝ) ≤ m → C * m ^ ((2 : ℝ) / 3) ≤ ℓ →
      FiniteCardBound {g : Motion 3 | g ∈ motionBucket X Y ℓ ∧ nonLineType η ℓ X Y g}
        (K * m ^ 3 / ℓ ^ ((3 : ℝ) / 2)) := by
  obtain ⟨η₁, η₂, Cg, Kg, hη₁, hη₂, hrel, hη₂lt, hCg, hKg, hgeneral⟩ :=
    general_motion_bound
  have hsmall : 2 * η₁ < η₂ := by
    have hη₂pos : 0 < η₂ := hη₂
    nlinarith
  have hη₁lt : η₁ < 1 := by nlinarith [hrel, hη₂lt]
  obtain ⟨Cp, Kp, hCp, hKp, hplanar⟩ :=
    planar_type_motion_bound η₁ η₂ hη₁ hη₂lt hsmall
  let C : ℝ := Cg + Cp + 1
  let K : ℝ := Kg + Kp
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hCgeCg : Cg ≤ C := by dsimp [C]; linarith
  have hCgeCp : Cp ≤ C := by dsimp [C]; linarith
  have hCgeOne : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨η₁, C, K, hη₁, hη₁lt, hCpos, hKpos, ?_⟩
  intro X Y m ℓ hm hXm hYm hℓ
  let A : Set (Motion 3) := {g | g ∈ motionBucket X Y ℓ ∧
    nonLineType η₁ ℓ X Y g ∧ ¬ planarType η₂ ℓ X Y g}
  let B : Set (Motion 3) := {g | g ∈ motionBucket X Y ℓ ∧
    nonLineType η₁ ℓ X Y g ∧ planarType η₂ ℓ X Y g}
  let T : Set (Motion 3) := {g | g ∈ motionBucket X Y ℓ ∧ nonLineType η₁ ℓ X Y g}
  have hℓg : Cg * m ^ ((2 : ℝ) / 3) ≤ ℓ := by
    calc
      Cg * m ^ ((2 : ℝ) / 3) ≤ C * m ^ ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hCgeCg (by positivity)
      _ ≤ ℓ := hℓ
  have hℓp : Cp * m ^ ((2 : ℝ) / 3) ≤ ℓ := by
    calc
      Cp * m ^ ((2 : ℝ) / 3) ≤ C * m ^ ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hCgeCp (by positivity)
      _ ≤ ℓ := hℓ
  have hA := hgeneral X Y m ℓ (by linarith) hXm hYm hℓg
  have hB := hplanar X Y m ℓ (by linarith) hXm hYm hℓp
  change A.Finite ∧ (A.ncard : ℝ) ≤ Kg * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) at hA
  change B.Finite ∧ (B.ncard : ℝ) ≤ Kp * m ^ 4 / ℓ ^ 3 at hB
  have hℓpos : 0 < ℓ := by
    have hmpos : 0 < m := by linarith
    have hpowpos : 0 < m ^ ((2 : ℝ) / 3) := by positivity
    have := mul_pos hCpos hpowpos
    linarith
  have hmpos : 0 < m := by linarith
  have hbase : m ^ ((2 : ℝ) / 3) ≤ ℓ := by
    have hpowpos : 0 < m ^ ((2 : ℝ) / 3) := by positivity
    calc
      m ^ ((2 : ℝ) / 3) ≤ C * m ^ ((2 : ℝ) / 3) := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hCgeOne (le_of_lt hpowpos))
      _ ≤ ℓ := hℓ
  have hpow : m ≤ ℓ ^ ((3 : ℝ) / 2) := by
    have hmono := Real.rpow_le_rpow (by positivity : 0 ≤ m ^ ((2 : ℝ) / 3))
      hbase (by norm_num : 0 ≤ (3 : ℝ) / 2)
    have hleft : (m ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = m := by
      rw [← Real.rpow_mul (by positivity : 0 ≤ m)]
      norm_num
    rw [← hleft]
    exact hmono
  have hpowSq : (ℓ ^ ((3 : ℝ) / 2)) ^ 2 = ℓ ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ ℓ)]
    norm_num
  have hfrac : m ^ 4 / ℓ ^ 3 ≤ m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := by
    rw [div_le_div_iff₀ (by positivity : 0 < ℓ ^ 3)
      (by positivity : 0 < ℓ ^ ((3 : ℝ) / 2))]
    have hmul : m * ℓ ^ ((3 : ℝ) / 2) ≤
        ℓ ^ ((3 : ℝ) / 2) * ℓ ^ ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    calc
      m ^ 4 * ℓ ^ ((3 : ℝ) / 2) = m ^ 3 * (m * ℓ ^ ((3 : ℝ) / 2)) := by ring
      _ ≤ m ^ 3 * ((ℓ ^ ((3 : ℝ) / 2)) ^ 2) := by
        simpa only [pow_two] using (mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ m ^ 3))
      _ = m ^ 3 * ℓ ^ 3 := by rw [hpowSq]
  have hB' : (B.ncard : ℝ) ≤ Kp * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := by
    calc
      (B.ncard : ℝ) ≤ Kp * m ^ 4 / ℓ ^ 3 := hB.2
      _ = Kp * (m ^ 4 / ℓ ^ 3) := by ring
      _ ≤ Kp * (m ^ 3 / ℓ ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hfrac (le_of_lt hKp)
      _ = Kp * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := by ring
  have hsplit : T = A ∪ B := by
    ext g
    simp only [T, A, B, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨hb, hn⟩
      by_cases hp : planarType η₂ ℓ X Y g
      · exact Or.inr ⟨hb, hn, hp⟩
      · exact Or.inl ⟨hb, hn, hp⟩
    · rintro (⟨hb, hn, _⟩ | ⟨hb, hn, _⟩)
      · exact ⟨hb, hn⟩
      · exact ⟨hb, hn⟩
  refine ⟨?_, ?_⟩
  · change T.Finite
    rw [hsplit]
    exact hA.1.union hB.1
  · have hcard : (T.ncard : ℝ) ≤ (A.ncard : ℝ) + (B.ncard : ℝ) := by
      rw [hsplit]
      exact_mod_cast (Set.ncard_union_le A B)
    change (T.ncard : ℝ) ≤ K * m ^ 3 / ℓ ^ ((3 : ℝ) / 2)
    calc
      (T.ncard : ℝ) ≤ (A.ncard : ℝ) + (B.ncard : ℝ) := hcard
      _ ≤ Kg * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) +
          Kp * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := add_le_add hA.2 hB'
      _ = K * m ^ 3 / ℓ ^ ((3 : ℝ) / 2) := by dsimp [K]; ring

end DistinctDistances.TrackC
