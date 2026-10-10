import Mathlib

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- `profiles.tex:576–590`: finitely many labels for the d recorded times
and one normalized width, chosen before the sample. -/
theorem pair_selection_profile_grid (d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ K : ℕ, 0 < K ∧ ∃ label : (Fin (d + 1) → ℝ) → Fin K,
      ∀ v w : Fin (d + 1) → ℝ,
        (∀ i, -1 ≤ v i ∧ v i ≤ 2) → (∀ i, -1 ≤ w i ∧ w i ≤ 2) →
        label v = label w → ∀ i, |v i - w i| ≤ ρ := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / ρ)
  have h3ρ : (0 : ℝ) < 3 / ρ := by positivity
  have hnPos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [Nat.cast_zero] at hn
      linarith
    · exact h
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnPos
  have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hδpos : (0 : ℝ) < 3 / (n : ℝ) := div_pos (by norm_num) hnR
  have hδne : (3 : ℝ) / (n : ℝ) ≠ 0 := ne_of_gt hδpos
  have h3lt : (3 : ℝ) < (n : ℝ) * ρ := (div_lt_iff₀ hρ).mp hn
  have hδle : 3 / (n : ℝ) ≤ ρ := by
    rw [div_le_iff₀ hnR, mul_comm]
    exact le_of_lt h3lt
  have hnδ : (n : ℝ) * (3 / (n : ℝ)) = 3 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hnRne
  have : Nonempty (Fin (d + 1) → Fin (n + 1)) :=
    ⟨fun _ => ⟨0, Nat.succ_pos _⟩⟩
  refine ⟨Fintype.card (Fin (d + 1) → Fin (n + 1)), Fintype.card_pos, ?_⟩
  refine ⟨fun v => Fintype.equivFin _
    (fun i => (⟨(Int.floor ((v i + 1) / (3 / (n : ℝ)))).toNat % (n + 1),
      Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (n + 1))), ?_⟩
  intro v w hv hw hlab i
  have hfun : (fun i => (⟨(Int.floor ((v i + 1) / (3 / (n : ℝ)))).toNat % (n + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (n + 1)))
      = (fun i => (⟨(Int.floor ((w i + 1) / (3 / (n : ℝ)))).toNat % (n + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (n + 1))) :=
    (Fintype.equivFin _).injective hlab
  have hcoord : (⟨(Int.floor ((v i + 1) / (3 / (n : ℝ)))).toNat % (n + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (n + 1))
      = (⟨(Int.floor ((w i + 1) / (3 / (n : ℝ)))).toNat % (n + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (n + 1)) :=
    congrFun hfun i
  have hval : (Int.floor ((v i + 1) / (3 / (n : ℝ)))).toNat % (n + 1)
      = (Int.floor ((w i + 1) / (3 / (n : ℝ)))).toNat % (n + 1) :=
    Fin.ext_iff.mp hcoord
  have hx1 := (hv i).1
  have hx2 := (hv i).2
  have hy1 := (hw i).1
  have hy2 := (hw i).2
  have ha0 : (0 : ℝ) ≤ (v i + 1) / (3 / (n : ℝ)) :=
    div_nonneg (by linarith) hδpos.le
  have haN : (v i + 1) / (3 / (n : ℝ)) ≤ (n : ℝ) := by
    rw [div_le_iff₀ hδpos]
    have hxi : v i + 1 ≤ 3 := by linarith
    linarith [hnδ]
  have hb0 : (0 : ℝ) ≤ (w i + 1) / (3 / (n : ℝ)) :=
    div_nonneg (by linarith) hδpos.le
  have hbN : (w i + 1) / (3 / (n : ℝ)) ≤ (n : ℝ) := by
    rw [div_le_iff₀ hδpos]
    have hyi : w i + 1 ≤ 3 := by linarith
    linarith [hnδ]
  set fa := Int.floor ((v i + 1) / (3 / (n : ℝ))) with hfad
  set fb := Int.floor ((w i + 1) / (3 / (n : ℝ))) with hfbd
  have hfa0 : 0 ≤ fa := Int.floor_nonneg.mpr ha0
  have hfb0 : 0 ≤ fb := Int.floor_nonneg.mpr hb0
  have hfaN : fa ≤ (n : ℤ) := by
    have h1 : (fa : ℝ) ≤ (n : ℝ) := le_trans (Int.floor_le _) haN
    exact_mod_cast h1
  have hfbN : fb ≤ (n : ℤ) := by
    have h1 : (fb : ℝ) ≤ (n : ℝ) := le_trans (Int.floor_le _) hbN
    exact_mod_cast h1
  have hfa_lt : fa.toNat < n + 1 := by
    have hle : fa.toNat ≤ n := by
      have h1 : ((fa.toNat : ℕ) : ℤ) ≤ (n : ℤ) := by
        rw [Int.toNat_of_nonneg hfa0]
        exact hfaN
      exact_mod_cast h1
    omega
  have hfb_lt : fb.toNat < n + 1 := by
    have hle : fb.toNat ≤ n := by
      have h1 : ((fb.toNat : ℕ) : ℤ) ≤ (n : ℤ) := by
        rw [Int.toNat_of_nonneg hfb0]
        exact hfbN
      exact_mod_cast h1
    omega
  rw [Nat.mod_eq_of_lt hfa_lt, Nat.mod_eq_of_lt hfb_lt] at hval
  have hfab : fa = fb := by
    have h1 : ((fa.toNat : ℕ) : ℤ) = fa := Int.toNat_of_nonneg hfa0
    have h2 : ((fb.toNat : ℕ) : ℤ) = fb := Int.toNat_of_nonneg hfb0
    have h3 : ((fa.toNat : ℕ) : ℤ) = ((fb.toNat : ℕ) : ℤ) := by
      exact_mod_cast hval
    rw [h1] at h3
    rw [h2] at h3
    exact h3
  have hfa_le : (fa : ℝ) ≤ (v i + 1) / (3 / (n : ℝ)) := Int.floor_le _
  have ha_lt : (v i + 1) / (3 / (n : ℝ)) < (fa : ℝ) + 1 := Int.lt_floor_add_one _
  have hfb_le : (fb : ℝ) ≤ (w i + 1) / (3 / (n : ℝ)) := Int.floor_le _
  have hb_lt : (w i + 1) / (3 / (n : ℝ)) < (fb : ℝ) + 1 := Int.lt_floor_add_one _
  rw [hfab] at hfa_le ha_lt
  have hab1 : |(v i + 1) / (3 / (n : ℝ)) - (w i + 1) / (3 / (n : ℝ))| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have e1 : (3 : ℝ) / (n : ℝ) * ((v i + 1) / (3 / (n : ℝ))) = v i + 1 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hδne
  have e2 : (3 : ℝ) / (n : ℝ) * ((w i + 1) / (3 / (n : ℝ))) = w i + 1 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hδne
  have hdiff : v i - w i
      = (3 / (n : ℝ)) * ((v i + 1) / (3 / (n : ℝ)) - (w i + 1) / (3 / (n : ℝ))) := by
    rw [mul_sub, e1, e2]
    ring
  have habs : |v i - w i|
      = (3 / (n : ℝ)) * |(v i + 1) / (3 / (n : ℝ)) - (w i + 1) / (3 / (n : ℝ))| := by
    rw [hdiff, abs_mul, abs_of_pos hδpos]
  have hlt : |v i - w i| < ρ :=
    calc |v i - w i|
          = (3 / (n : ℝ)) * |(v i + 1) / (3 / (n : ℝ)) - (w i + 1) / (3 / (n : ℝ))| :=
            habs
        _ < (3 / (n : ℝ)) * 1 := mul_lt_mul_of_pos_left hab1 hδpos
        _ = 3 / (n : ℝ) := mul_one _
        _ ≤ ρ := hδle
  exact hlt.le

/-- `profiles.tex:576–593`: agreement of dyadic residues makes unequal
windows separated at the fixed selection precision. -/
theorem pair_selection_residue_gap (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (b : ℝ), 0 < b → ∀ i j : ℕ,
      i ≠ j → i % M = j % M →
      b / (2 : ℝ) ^ i ≤ ρ * (b / (2 : ℝ) ^ j) ∨
        b / (2 : ℝ) ^ j ≤ ρ * (b / (2 : ℝ) ^ i) := by
  obtain ⟨M₀, hM₀⟩ := pow_unbounded_of_one_lt (1 / ρ) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨max M₀ 1, by omega, ?_⟩
  have hMle : M₀ ≤ max M₀ 1 := Nat.le_max_left _ _
  have h2mono : (2 : ℝ) ^ M₀ ≤ (2 : ℝ) ^ (max M₀ 1) :=
    pow_le_pow_right₀ (by norm_num) hMle
  have h12 : (1 : ℝ) / ρ < (2 : ℝ) ^ (max M₀ 1) := lt_of_lt_of_le hM₀ h2mono
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (max M₀ 1) := by positivity
  have hkey : (1 : ℝ) / (2 : ℝ) ^ (max M₀ 1) ≤ ρ := by
    have h1 : (1 : ℝ) < (2 : ℝ) ^ (max M₀ 1) * ρ := (div_lt_iff₀ hρ).mp h12
    rw [div_le_iff₀ h2pos]
    linarith [mul_comm ((2 : ℝ) ^ (max M₀ 1)) ρ]
  have aux : ∀ p q : ℕ, p < q → p % (max M₀ 1) = q % (max M₀ 1) →
      ∀ (b : ℝ), 0 < b → b / (2 : ℝ) ^ q ≤ ρ * (b / (2 : ℝ) ^ p) := by
    intro p q hpq hmod b hb
    have hMeq : p ≡ q [MOD (max M₀ 1)] := hmod
    have hdvd : max M₀ 1 ∣ q - p :=
      (Nat.modEq_iff_dvd' (Nat.le_of_lt hpq)).mp hMeq
    have hqp : 0 < q - p := Nat.sub_pos_of_lt hpq
    have hMle_qp : max M₀ 1 ≤ q - p := Nat.le_of_dvd hqp hdvd
    have h2le : (2 : ℝ) ^ (max M₀ 1) ≤ (2 : ℝ) ^ (q - p) :=
      pow_le_pow_right₀ (by norm_num) hMle_qp
    have h2qp_pos : (0 : ℝ) < (2 : ℝ) ^ (q - p) := by positivity
    have hinv : (1 : ℝ) / (2 : ℝ) ^ (q - p) ≤ ρ :=
      le_trans (one_div_le_one_div_of_le h2pos h2le) hkey
    have hsplit : (2 : ℝ) ^ q = (2 : ℝ) ^ p * (2 : ℝ) ^ (q - p) := by
      conv_lhs => rw [← Nat.add_sub_cancel' (Nat.le_of_lt hpq)]
      rw [pow_add]
    have h2p_ne : (2 : ℝ) ^ p ≠ 0 := pow_ne_zero p (by norm_num)
    have h2qp_ne : (2 : ℝ) ^ (q - p) ≠ 0 := pow_ne_zero (q - p) (by norm_num)
    have heq : b / (2 : ℝ) ^ q = (b / (2 : ℝ) ^ p) * (1 / (2 : ℝ) ^ (q - p)) := by
      rw [hsplit]
      field_simp
    have hbi : (0 : ℝ) ≤ b / (2 : ℝ) ^ p :=
      div_nonneg hb.le (pow_nonneg (by norm_num) p)
    calc b / (2 : ℝ) ^ q = (b / (2 : ℝ) ^ p) * (1 / (2 : ℝ) ^ (q - p)) := heq
      _ ≤ (b / (2 : ℝ) ^ p) * ρ := mul_le_mul_of_nonneg_left hinv hbi
      _ = ρ * (b / (2 : ℝ) ^ p) := mul_comm _ _
  intro b hb i j hne hmod
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr (aux i j h hmod b hb)
  · exact Or.inl (aux j i h hmod.symm b hb)

/-- Close normalized widths and a separated ratio force both widths to
lie in the small-width alternative. -/
theorem pair_selection_separated_small (b s t ρ : ℝ) (hb : 0 < b)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 2)
    (hratio : s ≤ ρ * t) (hclose : |s / b - t / b| ≤ ρ / 2) :
    s ≤ ρ * b ∧ t ≤ ρ * b := by
  have hdiff : t - s ≤ ρ / 2 * b := by
    have h := (abs_le.mp hclose).1
    have hm := mul_le_mul_of_nonneg_right h hb.le
    field_simp [hb.ne'] at hm
    nlinarith
  have htbound : t ≤ ρ * b := by nlinarith
  have hst : s ≤ t := by nlinarith
  exact ⟨hst.trans htbound, htbound⟩

end
end DistinctDistances.TrackD
