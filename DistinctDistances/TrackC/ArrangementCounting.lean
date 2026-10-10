import DistinctDistances.TrackC.FiniteIncidence

open Classical

namespace DistinctDistances.TrackC

/-- The incidence count producing many rich lines in an anchor arrangement,
motions.tex:451–461; input to dual_arrangement_derivatives. -/
theorem arrangement_rich_members {α β : Type*} (A : Finset α) (B : Finset β)
    (e : α → β → Prop) (ℓ c : ℝ) (hℓ : 0 < ℓ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hA : c*ℓ^2 ≤ (A.card : ℝ)) (hB : (B.card : ℝ) ≤ 2*ℓ)
    (hleft : ∀ a ∈ A, 2 ≤ (B.filter (e a)).card)
    (hright : ∀ b ∈ B, ((A.filter (fun a => e a b)).card : ℝ) ≤ 2*ℓ) :
    ∃ B' : Finset β, B' ⊆ B ∧ c*ℓ/4 ≤ (B'.card : ℝ) ∧
      ∀ b ∈ B', c*ℓ/4 ≤ ((A.filter (fun a => e a b)).card : ℝ) := by
  classical
  let deg : β → ℝ := fun b => ((A.filter (fun a => e a b)).card : ℝ)
  let rich : β → Prop := fun b => c*ℓ/4 ≤ deg b
  let B' : Finset β := B.filter rich
  have hmass_lower : 2*c*ℓ^2 ≤ relationMass A B e := by
    have hsum_lower : 2*(A.card : ℝ) ≤
        ∑ a ∈ A, ((B.filter (e a)).card : ℝ) := by
      calc
        2*(A.card : ℝ) = ∑ a ∈ A, (2 : ℝ) := by simp [mul_comm]
        _ ≤ ∑ a ∈ A, ((B.filter (e a)).card : ℝ) :=
          Finset.sum_le_sum (fun a ha => by exact_mod_cast hleft a ha)
    rw [relationMass_sum_card]
    nlinarith [hA, hsum_lower]
  have hmass_as_degrees : relationMass A B e = ∑ b ∈ B, deg b := by
    rw [relationMass_swap, relationMass_sum_card]
  have hsplit : (∑ b ∈ B, deg b) =
      (∑ b ∈ B.filter rich, deg b) +
      (∑ b ∈ B.filter (fun b => ¬ rich b), deg b) := by
    exact (Finset.sum_filter_add_sum_filter_not B rich deg).symm
  have hrich_upper : (∑ b ∈ B.filter rich, deg b) ≤
      (2*ℓ) * ((B.filter rich).card : ℝ) := by
    calc
      (∑ b ∈ B.filter rich, deg b) ≤
          ∑ b ∈ B.filter rich, (2*ℓ : ℝ) :=
        Finset.sum_le_sum (fun b hb => hright b (Finset.mem_filter.mp hb).1)
      _ = (2*ℓ) * ((B.filter rich).card : ℝ) := by simp [mul_comm]
  have hpoor_upper : (∑ b ∈ B.filter (fun b => ¬ rich b), deg b) ≤
      (c*ℓ/4) * ((B.filter (fun b => ¬ rich b)).card : ℝ) := by
    calc
      (∑ b ∈ B.filter (fun b => ¬ rich b), deg b) ≤
          ∑ b ∈ B.filter (fun b => ¬ rich b), (c*ℓ/4 : ℝ) :=
        Finset.sum_le_sum (fun b hb => by
          have hnot : ¬ c*ℓ/4 ≤ deg b := Finset.mem_filter.mp hb |>.2
          exact le_of_lt (lt_of_not_ge hnot))
      _ = (c*ℓ/4) * ((B.filter (fun b => ¬ rich b)).card : ℝ) := by
        simp [mul_comm]
  have hpoor_card : ((B.filter (fun b => ¬ rich b)).card : ℝ) ≤ 2*ℓ := by
    calc
      ((B.filter (fun b => ¬ rich b)).card : ℝ) ≤ (B.card : ℝ) := by
        exact_mod_cast (Finset.card_filter_le B (fun b => ¬ rich b))
      _ ≤ 2*ℓ := hB
  have hpoor_mass : (∑ b ∈ B.filter (fun b => ¬ rich b), deg b) ≤
      c*ℓ^2/2 := by
    have hmul := mul_le_mul_of_nonneg_left hpoor_card (by positivity : 0 ≤ c*ℓ/4)
    have hupper := hpoor_upper.trans hmul
    nlinarith
  have hcount : c*ℓ/4 ≤ ((B.filter rich).card : ℝ) := by
    have hmass_rich : 2*c*ℓ^2 ≤
        (2*ℓ) * ((B.filter rich).card : ℝ) + c*ℓ^2/2 := by
      calc
        2*c*ℓ^2 ≤ relationMass A B e := hmass_lower
        _ = (∑ b ∈ B.filter rich, deg b) +
            (∑ b ∈ B.filter (fun b => ¬ rich b), deg b) := by
          rw [hmass_as_degrees, hsplit]
        _ ≤ (2*ℓ) * ((B.filter rich).card : ℝ) + c*ℓ^2/2 :=
          add_le_add hrich_upper hpoor_mass
    by_contra hnot
    have hsmall : ((B.filter rich).card : ℝ) < c*ℓ/4 := lt_of_not_ge hnot
    have hstrict := mul_lt_mul_of_pos_left hsmall (by positivity : 0 < 2*ℓ)
    nlinarith [hmass_rich]
  refine ⟨B', ?_, ?_, ?_⟩
  · exact Finset.filter_subset _ _
  · simpa [B', rich] using hcount
  · intro b hb
    simpa [B', rich, deg] using (Finset.mem_filter.mp hb).2

end DistinctDistances.TrackC
