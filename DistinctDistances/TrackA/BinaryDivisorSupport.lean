import DistinctDistances.TrackA.DepthDefinitions
import DistinctDistances.OAIInterface.BinaryForms
import DistinctDistances.OAIInterface.PlaneHilbert

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical
open MvPolynomial OAI.Nagata.W02

private theorem multiset_partition_card {α : Type*} (s : Multiset α) (k : ℕ)
    (hk : k ≤ s.card) :
    ∃ a b : Multiset α, s = a+b ∧ a.card = k := by
  refine ⟨(s.toList.take k : Multiset α), (s.toList.drop k : Multiset α), ?_, ?_⟩
  · rw [Multiset.coe_add, List.take_append_drop, Multiset.coe_toList]
  · simp only [Multiset.coe_card, List.length_take, Multiset.length_toList]
    exact Nat.min_eq_left hk

/-- A nonzero binary form over ℂ has a homogeneous divisor of every degree
between zero and its degree, including divisors supported at infinity. -/
theorem binary_divisor_of_degree (f : Poly 2) (d k : ℕ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hk : k ≤ d) :
    ∃ H : Poly 2, H ≠ 0 ∧ H.IsHomogeneous k ∧ H ∣ f := by
  obtain ⟨c, e, s, hc, he, hfac⟩ := binary_homogeneous_factorization hf hf0
  let b := min k e
  have hb : b ≤ e := Nat.min_le_right k e
  have hbk : b ≤ k := Nat.min_le_left k e
  have hk' : k-b ≤ s.card := by dsimp [b]; omega
  obtain ⟨s₁, s₂, hs, hs₁⟩ := multiset_partition_card s (k-b) hk'
  let H : Poly 2 := X 1 ^ b * binaryRootProduct s₁
  have hH : H.IsHomogeneous k := by
    have hh := ((isHomogeneous_X ℂ (1 : Fin 2)).pow b).mul
      (binaryRootProduct_homogeneous s₁)
    simpa only [one_mul, hs₁, Nat.add_sub_of_le hbk] using hh
  have hmul : f = H * (C c * (X 1 ^ (e-b) * binaryRootProduct s₂)) := by
    rw [hfac, hs]
    dsimp [H]
    simp only [binaryRootProduct, Multiset.map_add, Multiset.prod_add]
    have hpow : (X 1 : Poly 2)^e = X 1^b * X 1^(e-b) := by
      rw [← pow_add, Nat.add_sub_of_le hb]
    rw [hpow]
    ring
  refine ⟨H, ?_, hH, ⟨_, hmul⟩⟩
  intro hz
  rw [hz, zero_mul] at hmul
  exact hf0 hmul

/-- Select an exact-degree common homogeneous divisor from a sufficiently
large specialized gcd. The forms may include one zero form. -/
theorem binary_common_divisor_of_degree (f g : Poly 2) (L k : ℕ)
    (hf : f.IsHomogeneous L) (hg : g.IsHomogeneous L)
    (h0 : f ≠ 0 ∨ g ≠ 0) (hk : k ≤ (binaryGcd f g).totalDegree) :
    ∃ H : Poly 2, H ≠ 0 ∧ H.IsHomogeneous k ∧ H ∣ f ∧ H ∣ g := by
  letI : NormalizedGCDMonoid (Poly 2) := Classical.arbitrary _
  change k ≤ (gcd f g).totalDegree at hk
  have hh0 : gcd f g ≠ 0 := by
    intro hh
    rcases h0 with hf0 | hg0
    · exact hf0 (by simpa [hh] using gcd_dvd_left f g)
    · exact hg0 (by simpa [hh] using gcd_dvd_right f g)
  have hh : (gcd f g).IsHomogeneous (gcd f g).totalDegree := by
    rcases h0 with hf0 | hg0
    · exact OAI.Nagata.Workers.W30.homogeneous_of_dvd hf0 hf (gcd_dvd_left f g)
    · exact OAI.Nagata.Workers.W30.homogeneous_of_dvd hg0 hg (gcd_dvd_right f g)
  obtain ⟨H, hH0, hH, hHd⟩ := binary_divisor_of_degree (gcd f g) _ k hh hh0 hk
  exact ⟨H, hH0, hH, hHd.trans (gcd_dvd_left f g), hHd.trans (gcd_dvd_right f g)⟩

end
end DistinctDistances.TrackA
