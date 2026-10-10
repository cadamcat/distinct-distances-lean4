import DistinctDistances.TrackC.FiniteIncidence

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Ordered pairs in a finite linear incidence structure are counted once. -/
theorem beck_pair_sum {α β : Type*} (X : Finset α) (L : Finset β)
    (e : α → β → Prop)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      ∃! l, l ∈ L ∧ e x l ∧ e y l) :
    (∑ l ∈ L, (((X.filter (fun x => e x l)).card : ℝ) ^ 2 -
      (X.filter (fun x => e x l)).card)) = (X.card : ℝ) ^ 2 - X.card := by
  classical
  have hrow (p : α × α) (hp : p ∈ X.offDiag) :
      (L.filter (fun l => e p.1 l ∧ e p.2 l)).card = 1 := by
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨l, hl, huniq⟩ := hpair p.1 hx p.2 hy hne
    apply Finset.card_eq_one.mpr
    refine ⟨l, ?_⟩
    ext l'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact huniq l' ⟨h.1, h.2.1, h.2.2⟩
    · rintro rfl
      exact ⟨hl.1, hl.2⟩
  have hfib (l : β) :
      X.offDiag.filter (fun p => e p.1 l ∧ e p.2 l) =
      (X.filter (fun x => e x l)).offDiag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    tauto
  have hnat : (∑ l ∈ L, (X.filter (fun x => e x l)).offDiag.card) = X.offDiag.card := by
    calc
      _ = ∑ l ∈ L, (X.offDiag.filter (fun p => e p.1 l ∧ e p.2 l)).card :=
        Finset.sum_congr rfl (fun l _ => congrArg Finset.card (hfib l).symm)
      _ = ∑ p ∈ X.offDiag, (L.filter (fun l => e p.1 l ∧ e p.2 l)).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
      _ = ∑ _p ∈ X.offDiag, 1 := Finset.sum_congr rfl hrow
      _ = _ := by simp
  have hcast (n : ℕ) : ((n * n - n : ℕ) : ℝ) = (n : ℝ)^2 - n := by
    rw [Nat.cast_sub (Nat.le_mul_self n)]
    simp [pow_two]
  have hreal := congrArg (Nat.cast : ℕ → ℝ) hnat
  push_cast at hreal
  simpa only [Finset.offDiag_card, hcast] using hreal

/-- A point lies on at most n spanned lines: choose a second point on each. -/
theorem beck_degree_le {α β : Type*} (X : Finset α) (L : Finset β)
    (e : α → β → Prop)
    (hline : ∀ l ∈ L, 2 ≤ (X.filter (fun x => e x l)).card)
    (huniq : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∀ l ∈ L, ∀ l' ∈ L,
      e x l → e y l → e x l' → e y l' → l = l')
    (x : α) (hx : x ∈ X) : (L.filter (e x)).card ≤ X.card := by
  classical
  let B := L.filter (e x)
  have hex (l : {l : β // l ∈ B}) : ∃ y ∈ X, y ≠ x ∧ e y l.1 := by
    have hl := Finset.mem_filter.mp l.2
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp
      (show 1 < (X.filter (fun y => e y l.1)).card from lt_of_lt_of_le (by decide) (hline l.1 hl.1))
    by_cases hax : a = x
    · exact ⟨b, (Finset.mem_filter.mp hb).1, by aesop, (Finset.mem_filter.mp hb).2⟩
    · exact ⟨a, (Finset.mem_filter.mp ha).1, hax, (Finset.mem_filter.mp ha).2⟩
  let f (l : {l : β // l ∈ B}) : α := Classical.choose (hex l)
  have hf (l : {l : β // l ∈ B}) : f l ∈ X ∧ f l ≠ x ∧ e (f l) l.1 :=
    Classical.choose_spec (hex l)
  have hinj : Function.Injective f := by
    intro l l' heq
    apply Subtype.ext
    have hl := Finset.mem_filter.mp l.2
    have hl' := Finset.mem_filter.mp l'.2
    exact huniq x hx (f l) (hf l).1 (hf l).2.1.symm l.1 hl.1 l'.1 hl'.1
      hl.2 (hf l).2.2 hl'.2 (by simpa only [heq] using (hf l').2.2)
  calc
    _ = (B.attach.image f).card := by rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
    _ ≤ X.card := Finset.card_le_card (by
      intro y hy
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy
      exact (hf l).1)

/-- The integer layer bound for occupancy squares. -/
theorem beck_square_layers (K M r : ℕ) (hr : r ≤ M) :
    (r : ℝ)^2 ≤ (K : ℝ)^2 +
      ∑ k ∈ Finset.Icc (K + 1) M, if k ≤ r then 2 * (k : ℝ) else 0 := by
  classical
  induction M generalizing r with
  | zero =>
    have hr0 : r = 0 := by omega
    subst r
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0)]
    have he : Finset.Icc (K+1) 0 = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [he, Finset.sum_empty, add_zero]
    positivity
  | succ M ih =>
    by_cases hKM : K + 1 ≤ M + 1
    · rw [Finset.sum_Icc_succ_top hKM]
      by_cases hrM : r ≤ M
      · have hh := ih r hrM
        have hnot : ¬ M + 1 ≤ r := by omega
        simp only [hnot, ↓reduceIte, add_zero]
        exact hh
      · have hrEq : r = M + 1 := by omega
        subst r
        have hprev := ih (r := M) (by omega)
        have hsum : (∑ k ∈ Finset.Icc (K + 1) M, if k ≤ M then 2 * (k : ℝ) else 0) =
            ∑ k ∈ Finset.Icc (K + 1) M, if k ≤ M + 1 then 2 * (k : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkM := (Finset.mem_Icc.mp hk).2
          simp [hkM, show k ≤ M+1 by omega]
        rw [hsum] at hprev
        simp only [le_refl, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        nlinarith
    · have hrK : r ≤ K := by omega
      have hrr : (r : ℝ) ≤ K := Nat.cast_le.mpr hrK
      have hemp : Finset.Icc (K+1) (M+1) = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
      rw [hemp, Finset.sum_empty, add_zero]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hrr _

/-- Reciprocal-square tails are bounded by a telescoping reciprocal sum. -/
theorem beck_reciprocal_tail (K M : ℕ) (hK : 1 ≤ K) :
    (∑ k ∈ Finset.Icc (K + 1) M, 1 / (k : ℝ)^2) ≤ 1 / (K : ℝ) := by
  classical
  have hstrong : ∀ M, K ≤ M →
      (∑ k ∈ Finset.Icc (K+1) M, 1 / (k : ℝ)^2) ≤ 1 / (K : ℝ) - 1 / (M : ℝ) := by
    intro M hKM
    induction M, hKM using Nat.le_induction with
    | base => simp
    | succ M hKM ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
      have hstep : 1 / ((M+1 : ℕ) : ℝ)^2 ≤ 1 / (M : ℝ) - 1 / ((M+1 : ℕ) : ℝ) := by
        push_cast
        field_simp
        nlinarith
      linarith
  by_cases hKM : K ≤ M
  · have hn : 0 ≤ 1 / (M : ℝ) := by positivity
    linarith [hstrong M hKM]
  · rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]
    positivity


/-- Summing integer layers converts the rich-line bound into a square bound. -/
theorem beck_square_sum {β : Type*} (L : Finset β) (r : β → ℕ)
    (n C : ℝ) (K M : ℕ) (hK : 1 ≤ K) (hn : 0 ≤ n) (hC : 0 ≤ C)
    (hr : ∀ l ∈ L, r l ≤ M)
    (hRich : ∀ k : ℕ, 2 ≤ k →
      ((L.filter (fun l => k ≤ r l)).card : ℝ) ≤ C * (n^2 / (k : ℝ)^3 + n / k)) :
    (∑ l ∈ L, (r l : ℝ)^2) ≤
      (K : ℝ)^2 * L.card + 2*C*(n^2/(K : ℝ)+n*M) := by
  classical
  have hfirst : (∑ l ∈ L, (r l : ℝ)^2) ≤ (K : ℝ)^2 * L.card +
      ∑ k ∈ Finset.Icc (K+1) M, 2*(k : ℝ)*(L.filter (fun l => k ≤ r l)).card := by
    calc
      _ ≤ ∑ l ∈ L, ((K : ℝ)^2 +
          ∑ k ∈ Finset.Icc (K+1) M, if k ≤ r l then 2*(k : ℝ) else 0) :=
        Finset.sum_le_sum (fun l hl => beck_square_layers K M (r l) (hr l hl))
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp [← Finset.sum_filter, mul_comm]
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc (K+1) M) :
      2*(k : ℝ)*(L.filter (fun l => k ≤ r l)).card ≤
        2*C*(n^2/(k : ℝ)^2+n) := by
    have hk2 : 2 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    calc
      _ ≤ 2*(k : ℝ)*(C*(n^2/(k : ℝ)^3+n/k)) :=
        mul_le_mul_of_nonneg_left (hRich k hk2) (by positivity)
      _ = _ := by field_simp
  have htail : (∑ k ∈ Finset.Icc (K+1) M, 2*C*(n^2/(k : ℝ)^2+n)) ≤
      2*C*(n^2/(K : ℝ)+n*M) := by
    have hcard : (Finset.Icc (K+1) M).card ≤ M := by
      rw [Nat.card_Icc]; omega
    have hrec := beck_reciprocal_tail K M hK
    calc
      _ = 2*C*(n^2*(∑ k ∈ Finset.Icc (K+1) M, 1/(k : ℝ)^2) +
          n*(Finset.Icc (K+1) M).card) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp only [div_eq_mul_inv, one_mul, Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hrec' := mul_le_mul_of_nonneg_left hrec (sq_nonneg n)
        have hcard' := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard :
          ((Finset.Icc (K+1) M).card : ℝ) ≤ M) hn
        simpa [div_eq_mul_inv] using add_le_add hrec' hcard'
  exact hfirst.trans (add_le_add_right ((Finset.sum_le_sum hterm).trans htail) _)

/-- Many lines imply many points of large degree. -/
theorem beck_many_anchors {α β : Type*} (X : Finset α) (L : Finset β)
    (e : α → β → Prop) (γ : ℝ) (hγ : 0 ≤ γ) (hn : 0 < (X.card : ℝ))
    (hline : ∀ l ∈ L, 2 ≤ (X.filter (fun x => e x l)).card)
    (hdeg : ∀ x ∈ X, (L.filter (e x)).card ≤ X.card)
    (hcount : 2*γ*(X.card : ℝ)^2 ≤ L.card) :
    γ*X.card ≤ (X.filter (fun x => γ*X.card ≤ ((L.filter (e x)).card : ℝ))).card := by
  classical
  let A := X.filter (fun x => γ*X.card ≤ ((L.filter (e x)).card : ℝ))
  have hlo : 2*(L.card : ℝ) ≤ ∑ x ∈ X, ((L.filter (e x)).card : ℝ) := by
    have hswap := relationMass_swap X L e
    rw [relationMass_sum_card, relationMass_sum_card] at hswap
    rw [hswap]
    calc
      2*(L.card : ℝ) = ∑ _l ∈ L, (2 : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun l hl => Nat.cast_le.mpr (hline l hl))
  have hhi : (∑ x ∈ X, ((L.filter (e x)).card : ℝ)) ≤
      (X.card : ℝ)*A.card + γ*(X.card : ℝ)^2 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not X
      (fun x => γ*X.card ≤ ((L.filter (e x)).card : ℝ))
      (fun x => ((L.filter (e x)).card : ℝ))
    rw [← hsplit]
    have hA : (∑ x ∈ A, ((L.filter (e x)).card : ℝ)) ≤ (X.card : ℝ)*A.card := by
      calc
        _ ≤ ∑ _x ∈ A, (X.card : ℝ) := Finset.sum_le_sum (fun x hx =>
          Nat.cast_le.mpr (hdeg x (Finset.mem_filter.mp hx).1))
        _ = _ := by simp [mul_comm]
    have hB : (∑ x ∈ X.filter (fun x => ¬ γ*X.card ≤ ((L.filter (e x)).card : ℝ)),
        ((L.filter (e x)).card : ℝ)) ≤ γ*(X.card : ℝ)^2 := by
      calc
        _ ≤ ∑ _x ∈ X.filter (fun x => ¬ γ*X.card ≤ ((L.filter (e x)).card : ℝ)),
            γ*X.card := Finset.sum_le_sum (fun x hx => (lt_of_not_ge (Finset.mem_filter.mp hx).2).le)
        _ = γ*X.card*(X.filter (fun x => ¬ γ*X.card ≤ ((L.filter (e x)).card : ℝ))).card := by simp [mul_comm]
        _ ≤ γ*X.card*X.card := mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (by positivity)
        _ = _ := by ring
    exact add_le_add hA hB
  have hprod : γ*(X.card : ℝ)^2 ≤ (X.card : ℝ)*A.card := by
    nlinarith [mul_nonneg hγ (sq_nonneg (X.card : ℝ))]
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

/-- Beck's quantitative counting step, uniform over finite incidence structures. -/
theorem beck_finite {α β : Type*} (C : ℝ) (K : ℕ) (hC : 0 < C)
    (hK : 16*(C+1) ≤ (K : ℝ))
    (X : Finset α) (L : Finset β) (e : α → β → Prop)
    (hn : 2 ≤ X.card)
    (hline : ∀ l ∈ L, 2 ≤ (X.filter (fun x => e x l)).card)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∃! l, l ∈ L ∧ e x l ∧ e y l)
    (hcap : ∀ l ∈ L, ((X.filter (fun x => e x l)).card : ℝ) ≤
      (1/(16*(C+1)))*X.card)
    (hRich : ∀ k : ℕ, 2 ≤ k →
      ((L.filter (fun l => k ≤ (X.filter (fun x => e x l)).card)).card : ℝ) ≤
      C*((X.card : ℝ)^2/(k : ℝ)^3+(X.card : ℝ)/k)) :
    (L.card : ℝ) ≤ (X.card : ℝ)^2 ∧
    (1/(8*(K : ℝ)^2))*(X.card : ℝ)^2 ≤ L.card ∧
    (1/(8*(K : ℝ)^2))*X.card ≤
      (X.filter (fun x => (1/(8*(K : ℝ)^2))*X.card ≤
        ((L.filter (e x)).card : ℝ))).card := by
  classical
  let r (l : β) := (X.filter (fun x => e x l)).card
  let M := L.sup r
  have hKpos : (0 : ℝ) < K := by linarith
  have hKnat : 1 ≤ K := by exact_mod_cast (by linarith : (1 : ℝ) ≤ K)
  have hnR : (2 : ℝ) ≤ X.card := Nat.cast_le.mpr hn
  have hnpos : (0 : ℝ) < X.card := by linarith
  have hpairSum := beck_pair_sum X L e hpair
  have hupper : (L.card : ℝ) ≤ (X.card : ℝ)^2 := by
    have hh : (L.card : ℝ) ≤ ∑ l ∈ L, ((r l : ℝ)^2-r l) := by
      calc
        _ = ∑ _l ∈ L, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun l hl => by
          have hr : (2 : ℝ) ≤ r l := Nat.cast_le.mpr (hline l hl)
          nlinarith)
    change (∑ l ∈ L, ((r l : ℝ)^2-r l)) = _ at hpairSum
    rw [hpairSum] at hh
    linarith
  have hMcap : (M : ℝ) ≤ (1/(16*(C+1)))*X.card := by
    by_cases hL : L.Nonempty
    · obtain ⟨l, hl, heq⟩ := Finset.exists_mem_eq_sup L hL r
      change (↑(L.sup r) : ℝ) ≤ _
      rw [heq]
      exact hcap l hl
    · have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      simp [M, he]
      positivity
  have hsquare := beck_square_sum L r (X.card : ℝ) C K M hKnat
    (Nat.cast_nonneg _) hC.le (fun l hl => Finset.le_sup hl) hRich
  have htail : 2*C*((X.card : ℝ)^2/(K : ℝ)+(X.card : ℝ)*M) ≤ (X.card : ℝ)^2/4 := by
    have hC1 : 0 < C+1 := by linarith
    have hsmall : 2*C/(K : ℝ) ≤ 1/8 := by
      apply (div_le_iff₀ hKpos).mpr
      linarith
    have hdelta : 2*C*(1/(16*(C+1))) ≤ 1/8 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 16*(C+1))]
      linarith
    have hm := mul_le_mul_of_nonneg_left hMcap (by positivity : 0 ≤ 2*C*(X.card : ℝ))
    have hk := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (X.card : ℝ))
    have hd := mul_le_mul_of_nonneg_right hdelta (sq_nonneg (X.card : ℝ))
    calc
      _ = (2*C/(K : ℝ))*(X.card : ℝ)^2+2*C*(X.card : ℝ)*M := by ring
      _ ≤ (X.card : ℝ)^2/8+(2*C*(1/(16*(C+1))))*(X.card : ℝ)^2 := by nlinarith
      _ ≤ _ := by nlinarith
  have hpairLe : (X.card : ℝ)^2-X.card ≤ ∑ l ∈ L, (r l : ℝ)^2 := by
    rw [← hpairSum]
    exact Finset.sum_le_sum (fun l _ => by
      change (r l : ℝ)^2-r l ≤ (r l : ℝ)^2
      have hh : (0 : ℝ) ≤ r l := Nat.cast_nonneg _
      linarith)
  have hlower : (X.card : ℝ)^2/4 ≤ (K : ℝ)^2*L.card := by
    nlinarith
  have hcount : 2*(1/(8*(K : ℝ)^2))*(X.card : ℝ)^2 ≤ L.card := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hKpos)).mp
    have hid : (K : ℝ)^2*(2*(1/(8*(K : ℝ)^2))*(X.card : ℝ)^2) = (X.card : ℝ)^2/4 := by
      field_simp; ring
    rw [hid]
    exact hlower
  have hγ : 0 ≤ (1/(8*(K : ℝ)^2) : ℝ) := by positivity
  refine ⟨hupper, ?_, ?_⟩
  · nlinarith [mul_nonneg hγ (sq_nonneg (X.card : ℝ))]
  · apply beck_many_anchors X L e _ hγ hnpos hline _ hcount
    intro x hx
    apply beck_degree_le X L e hline _ x hx
    intro a ha b hb hab l hl l' hl' hal hbl hal' hbl'
    obtain ⟨m, hm, hu⟩ := hpair a ha b hb hab
    exact (hu l ⟨hl, hal, hbl⟩).trans (hu l' ⟨hl', hal', hbl'⟩).symm


/-- Set-valued form of the shared Beck estimate. -/
theorem beck_of_rich {α β : Type*} (C : ℝ) (K : ℕ) (hC : 0 < C)
    (hK : 16*(C+1) ≤ (K : ℝ)) (X : Finset α) (e : α → β → Prop)
    (hn : 2 ≤ X.card)
    (hpair : ∀ x y : α, x ≠ y → ∃! l : β, e x l ∧ e y l)
    (hcap : ∀ l : β, ((X.filter (fun x => e x l)).card : ℝ) ≤
      (1/(16*(C+1)))*X.card)
    (hRich : ∀ k : ℕ, 2 ≤ k →
      FiniteCardBound {l : β | k ≤ (X.filter (fun x => e x l)).card}
      (C*((X.card : ℝ)^2/(k : ℝ)^3+(X.card : ℝ)/k))) :
    let S : Set β := {l | 2 ≤ (X.filter (fun x => e x l)).card}
    FiniteCardBound S ((X.card : ℝ)^2) ∧
    (1/(8*(K : ℝ)^2))*(X.card : ℝ)^2 ≤ S.ncard ∧
    (1/(8*(K : ℝ)^2))*X.card ≤
      (X.filter (fun x => (1/(8*(K : ℝ)^2))*X.card ≤
        ({l : β | l ∈ S ∧ e x l}.ncard : ℝ))).card := by
  classical
  let S : Set β := {l | 2 ≤ (X.filter (fun x => e x l)).card}
  have hS : S.Finite := (hRich 2 (by omega)).1
  let L := hS.toFinset
  have hline (l : β) (hl : l ∈ L) : 2 ≤ (X.filter (fun x => e x l)).card :=
    hS.mem_toFinset.mp hl
  have hpairs : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∃! l, l ∈ L ∧ e x l ∧ e y l := by
    intro x hx y hy hxy
    obtain ⟨l, hl, hu⟩ := hpair x y hxy
    have hlS : l ∈ S := by
      change 2 ≤ (X.filter (fun x => e x l)).card
      have hh : 1 < (X.filter (fun x => e x l)).card :=
        Finset.one_lt_card_iff.mpr ⟨x, y, Finset.mem_filter.mpr ⟨hx, hl.1⟩,
          Finset.mem_filter.mpr ⟨hy, hl.2⟩, hxy⟩
      omega
    refine ⟨l, ⟨hS.mem_toFinset.mpr hlS, hl⟩, ?_⟩
    intro l' hl'
    exact hu l' hl'.2
  have hr (k : ℕ) (hk : 2 ≤ k) :
      ((L.filter (fun l => k ≤ (X.filter (fun x => e x l)).card)).card : ℝ) ≤
      C*((X.card : ℝ)^2/(k : ℝ)^3+(X.card : ℝ)/k) := by
    have hh := hRich k hk
    exact (Nat.cast_le.mpr (finset_card_le_ncard _ _ hh.1 (by
      intro l hl
      exact (Finset.mem_filter.mp hl).2))).trans hh.2
  obtain ⟨hup, hlo, ha⟩ := beck_finite C K hC hK X L e hn hline hpairs
    (fun l _ => hcap l) hr
  have hcard : S.ncard = L.card := Set.ncard_eq_toFinset_card S hS
  have hdeg (x : α) : {l : β | l ∈ S ∧ e x l} = (L.filter (e x) : Set β) := by
    ext l
    simp [L]
  change FiniteCardBound S ((X.card : ℝ)^2) ∧
    (1/(8*(K : ℝ)^2))*(X.card : ℝ)^2 ≤ S.ncard ∧
    (1/(8*(K : ℝ)^2))*X.card ≤
      (X.filter (fun x => (1/(8*(K : ℝ)^2))*X.card ≤
        ({l : β | l ∈ S ∧ e x l}.ncard : ℝ))).card
  refine ⟨⟨hS, by rwa [hcard]⟩, by rwa [hcard], ?_⟩
  simpa only [hdeg, Set.ncard_coe_finset] using ha

/-- Two distinct affine points determine a unique line. -/
theorem beck_affine_pair {d : ℕ} (x y : E d) (hxy : x ≠ y) :
    ∃! l : Line d, x ∈ l.1 ∧ y ∈ l.1 := by
  classical
  let l : Line d := ⟨affineSpan ℝ ({x, y} : Set (E d)),
    ⟨⟨x, left_mem_affineSpan_pair ℝ x y⟩, by
      rw [direction_affineSpan, vectorSpan_pair_rev]
      apply finrank_span_singleton
      intro hv
      exact hxy.symm (vsub_eq_zero_iff_eq.mp hv)⟩⟩
  refine ⟨l, ⟨left_mem_affineSpan_pair ℝ x y, right_mem_affineSpan_pair ℝ x y⟩, ?_⟩
  intro l' hl'
  have hv : y-x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hd : l'.1.direction = l.1.direction := by
    rw [eq_span_singleton_of_mem_of_finrank_eq_one l'.2.2
        (l'.1.vsub_mem_direction hl'.2 hl'.1) hv,
      eq_span_singleton_of_mem_of_finrank_eq_one l.2.2
        (l.1.vsub_mem_direction (right_mem_affineSpan_pair ℝ x y)
          (left_mem_affineSpan_pair ℝ x y)) hv]
  exact Subtype.ext ((AffineSubspace.eq_iff_direction_eq_of_mem hl'.1
    (left_mem_affineSpan_pair ℝ x y)).mpr hd)

/-- Two distinct projective points determine their rank-two supremum. -/
theorem beck_projective_pair {n : ℕ} (p q : PFlat ℝ n 1) (hpq : p ≠ q) :
    ∃! l : PFlat ℝ n 2, p.1 ≤ l.1 ∧ q.1 ≤ l.1 := by
  classical
  have hdis : Disjoint p.1 q.1 := by
    apply Submodule.disjoint_def.mpr
    intro v hp hq
    by_contra hv
    have heq : p.1 = q.1 := by
      rw [eq_span_singleton_of_mem_of_finrank_eq_one p.2 hp hv,
        eq_span_singleton_of_mem_of_finrank_eq_one q.2 hq hv]
    exact hpq (Subtype.ext heq)
  have hrank : Module.finrank ℝ (p.1 ⊔ q.1 : Submodule ℝ (Fin n → ℝ)) = 2 := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq p.1 q.1
    rw [p.2, q.2, hdis.eq_bot, finrank_bot] at hh
    omega
  let l : PFlat ℝ n 2 := ⟨p.1 ⊔ q.1, hrank⟩
  refine ⟨l, ⟨le_sup_left, le_sup_right⟩, ?_⟩
  intro l' hl'
  apply Subtype.ext
  exact (Submodule.eq_of_le_of_finrank_eq (sup_le hl'.1 hl'.2)
    (by rw [hrank, l'.2])).symm

end DistinctDistances.TrackC
