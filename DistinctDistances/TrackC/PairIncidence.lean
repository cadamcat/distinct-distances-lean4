import DistinctDistances.TrackC.FiniteIncidence

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Pairwise intersections bound the incidences of a small contained family. -/
theorem relationMass_pair_bound {α β : Type*} (A : Finset α) (B : Finset β)
    (e : α → β → Prop) (t : ℕ)
    (hpair : ∀ bc ∈ B.offDiag, (A.filter (fun a => e a bc.1 ∧ e a bc.2)).card ≤ t) :
    relationMass A B e ≤ (A.card:ℝ)+(t:ℝ)*(B.card:ℝ)^2 := by
  have hrow : ∀ a, (B.filter (e a)).card ≤ 1+
      ((B.offDiag).filter (fun bc => e a bc.1 ∧ e a bc.2)).card := by
    intro a
    have heq : (B.offDiag).filter (fun bc => e a bc.1 ∧ e a bc.2) = (B.filter (e a)).offDiag := by
      ext bc
      simp [Finset.mem_offDiag]
      tauto
    rw [heq,Finset.offDiag_card]
    let d := (B.filter (e a)).card
    change d ≤ 1+(d*d-d)
    rcases le_or_gt d 1 with h | h
    · omega
    · have hh : 2*d ≤ d*d := Nat.mul_le_mul_right d (by omega : 2 ≤ d)
      omega
  have hfirst : relationMass A B e ≤ (A.card:ℝ)+
      relationMass A B.offDiag (fun a bc => e a bc.1 ∧ e a bc.2) := by
    rw [relationMass_sum_card,relationMass_sum_card]
    calc
      _ ≤ ∑ a ∈ A, ((1:ℝ)+((B.offDiag.filter (fun bc => e a bc.1 ∧ e a bc.2)).card:ℝ)) := by
        apply Finset.sum_le_sum
        intro a ha
        exact_mod_cast hrow a
      _ = _ := by
        simp [Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        congr 2
        ext bc
        simp only [Finset.mem_filter]
  have hsecond : relationMass A B.offDiag (fun a bc => e a bc.1 ∧ e a bc.2) ≤
      (t:ℝ)*(B.card:ℝ)^2 := by
    rw [relationMass_swap,relationMass_sum_card]
    calc
      _ ≤ ∑ _bc ∈ B.offDiag, (t:ℝ) := by
        apply Finset.sum_le_sum
        intro bc hbc
        convert (show ((A.filter (fun a => e a bc.1 ∧ e a bc.2)).card:ℝ) ≤ (t:ℝ) from Nat.cast_le.mpr (hpair bc hbc)) using 1
        congr 2
        ext a
        simp only [Finset.mem_filter]
      _ = (t:ℝ)*(B.offDiag.card:ℝ) := by simp [mul_comm]
      _ ≤ (t:ℝ)*(B.card:ℝ)^2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg t)
        have hcard : B.offDiag.card ≤ B.card*B.card := by rw [Finset.offDiag_card]; omega
        simpa [pow_two] using (Nat.cast_le.mpr hcard : (B.offDiag.card:ℝ) ≤ ((B.card*B.card:ℕ):ℝ))
  exact hfirst.trans (add_le_add_right hsecond _)

/-- Two distinct affine lines share at most one point. -/
theorem affine_lines_intersection_bound (d : ℕ) (l l' : Line d) (hne : l ≠ l') :
    FiniteCardBound ((l.1:Set (E d)) ∩ (l'.1:Set (E d))) 1 := by
  have hss : ((l.1:Set (E d)) ∩ (l'.1:Set (E d))).Subsingleton := by
    intro x hx y hy
    by_contra hxy
    have hv : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have hdir : l.1.direction = l'.1.direction := by
      rw [eq_span_singleton_of_mem_of_finrank_eq_one l.2.2 (l.1.vsub_mem_direction hy.1 hx.1) hv,
        eq_span_singleton_of_mem_of_finrank_eq_one l'.2.2 (l'.1.vsub_mem_direction hy.2 hx.2) hv]
    exact hne (Subtype.ext ((AffineSubspace.eq_iff_direction_eq_of_mem hx.1 hx.2).mpr hdir))
  refine ⟨hss.finite,?_⟩
  exact_mod_cast (Set.ncard_le_one hss.finite).mpr hss

/-- A contained planar line family has at most n+L² incidences. -/
theorem line_pair_incidence_bound (X : Finset (E 2)) (L : Finset (Line 2)) :
    relationMass X L (fun x l => x ∈ l.1) ≤ X.card+(L.card:ℝ)^2 := by
  have h : ∀ ll ∈ L.offDiag, (X.filter (fun x => x ∈ ll.1.1 ∧ x ∈ ll.2.1)).card ≤ 1 := by
    intro ll hll
    have hc := affine_lines_intersection_bound 2 ll.1 ll.2 (Finset.mem_offDiag.mp hll).2.2
    have hsub : ((X.filter (fun x => x ∈ ll.1.1 ∧ x ∈ ll.2.1)):Set (E 2)) ⊆
        ((ll.1.1:Set (E 2)) ∩ (ll.2.1:Set (E 2))) := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hb := finset_card_le_ncard _ _ hc.1 hsub
    have hreal : ((X.filter (fun x => x ∈ ll.1.1 ∧ x ∈ ll.2.1)).card:ℝ) ≤ 1 :=
      (Nat.cast_le.mpr hb).trans hc.2
    exact_mod_cast hreal
  simpa using relationMass_pair_bound X L (fun x l => x ∈ l.1) 1 h

end DistinctDistances.TrackC
