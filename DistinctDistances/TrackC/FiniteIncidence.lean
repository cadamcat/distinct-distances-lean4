import DistinctDistances.TrackC.CloudMass

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

@[simp] theorem mem_pointsIn {d : ℕ} (X : Finset (E d)) (S : Set (E d)) (x : E d) :
    x ∈ pointsIn X S ↔ x ∈ X ∧ x ∈ S := by
  exact Finset.mem_filter

/-- Real-valued finite incidence count, for changing the summation order. -/
def relationMass {α β : Type*} (A : Finset α) (B : Finset β) (e : α → β → Prop) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ B, if e a b then 1 else 0

def relationEdges {α β : Type*} (A : Finset α) (B : Finset β) (e : α → β → Prop) : Finset (α × β) :=
  (A ×ˢ B).filter (fun ab => e ab.1 ab.2)

theorem relationMass_sum_card {α β : Type*} (A : Finset α) (B : Finset β) (e : α → β → Prop) :
    relationMass A B e = ∑ a ∈ A, ((B.filter (e a)).card : ℝ) := by
  simp [relationMass]

theorem relationMass_edges {α β : Type*} (A : Finset α) (B : Finset β) (e : α → β → Prop) :
    relationMass A B e = (relationEdges A B e).card := by
  unfold relationEdges relationMass
  rw [← Finset.sum_boole (fun ab : α × β => e ab.1 ab.2) (A ×ˢ B)]
  exact (Finset.sum_product A B (fun ab => if e ab.1 ab.2 then (1:ℝ) else 0)).symm

theorem relationMass_swap {α β : Type*} (A : Finset α) (B : Finset β) (e : α → β → Prop) :
    relationMass A B e = relationMass B A (fun b a => e a b) := Finset.sum_comm

theorem finset_card_le_ncard {α : Type*} (A : Finset α) (S : Set α) (hS : S.Finite)
    (hA : (A : Set α) ⊆ S) : A.card ≤ S.ncard := by
  simpa using Set.ncard_le_ncard hA hS

theorem relationMass_mono_left {α β : Type*} (A A' : Finset α) (B : Finset β)
    (e : α → β → Prop) (hA : A ⊆ A') : relationMass A B e ≤ relationMass A' B e := by
  rw [relationMass_edges,relationMass_edges]
  have hs : relationEdges A B e ⊆ relationEdges A' B e := by
    intro ab hab
    obtain ⟨habAB,he⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp habAB
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hA ha,hb⟩,he⟩
  exact_mod_cast Finset.card_le_card hs

theorem relationMass_cover {α β ι : Type*} (A : Finset α) (B : Finset β)
    (e : α → β → Prop) (I : Finset ι) (A' : ι → Finset α)
    (hcover : ∀ a ∈ A, ∃ i ∈ I, a ∈ A' i) :
    relationMass A B e ≤ ∑ i ∈ I, relationMass (A' i) B e := by
  have hsub : relationEdges A B e ⊆ I.biUnion (fun i => relationEdges (A' i) B e) := by
    intro ab hab
    obtain ⟨habAB,he⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp habAB
    obtain ⟨i,hi,hai⟩ := hcover ab.1 ha
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hai,hb⟩,he⟩⟩
  simp only [relationMass_edges]
  exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le

theorem relationMass_restrict_right {α β : Type*} (A : Finset α) (B : Finset β)
    (e : α → β → Prop) (p : β → Prop)
    (hp : ∀ a ∈ A, ∀ b ∈ B, e a b → p b) :
    relationMass A B e = relationMass A (B.filter p) e := by
  rw [relationMass_edges,relationMass_edges]
  congr 2
  ext ab
  simp only [relationEdges, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨ha,hb⟩,he⟩
    exact ⟨⟨ha,hb,hp ab.1 ha ab.2 hb he⟩,he⟩
  · tauto

theorem relationMass_split_left {α β : Type*} (A : Finset α) (B : Finset β)
    (e : α → β → Prop) (p : α → Prop) :
    relationMass A B e = relationMass (A.filter p) B e + relationMass (A.filter (fun a => ¬p a)) B e := by
  unfold relationMass
  exact (Finset.sum_filter_add_sum_filter_not A p (fun a => ∑ b ∈ B, if e a b then (1:ℝ) else 0)).symm

theorem relationMass_split_right {α β : Type*} (A : Finset α) (B : Finset β)
    (e : α → β → Prop) (p : β → Prop) :
    relationMass A B e = relationMass A (B.filter p) e + relationMass A (B.filter (fun b => ¬p b)) e := by
  unfold relationMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact (Finset.sum_filter_add_sum_filter_not B p (fun b => if e a b then (1:ℝ) else 0)).symm

theorem relationMass_pointsIn {d : ℕ} {β : Type*} (X : Finset (E d)) (S : Set (E d))
    (B : Finset β) (e : E d → β → Prop) :
    relationMass (pointsIn X S) B e = ∑ b ∈ B, cloudMass X (S ∩ {x | e x b}) := by
  rw [relationMass_swap, relationMass_sum_card]
  apply Finset.sum_congr rfl
  intro b hb
  unfold cloudMass
  congr 2
  ext x
  simp [pointsIn]
  tauto

theorem cloudMass_le_finite_bound {d : ℕ} (X : Finset (E d)) (S : Set (E d)) (B : ℝ)
    (hS : FiniteCardBound S B) : cloudMass X S ≤ B := by
  have hs : (pointsIn X S).card ≤ S.ncard :=
    finset_card_le_ncard _ S hS.1 (fun x hx => (Finset.mem_filter.mp hx).2)
  exact (Nat.cast_le.mpr hs).trans hS.2

/-- Hölder's inequality in the exponent used by point-circle cells. -/
theorem sum_two_thirds_le {α : Type*} (I : Finset α) (a : α → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i) :
    (∑ i ∈ I, (a i)^((2:ℝ)/3)) ≤ (∑ i ∈ I, a i)^((2:ℝ)/3)*(I.card:ℝ)^((1:ℝ)/3) := by
  have hpq : Real.HolderConjugate ((3:ℝ)/2) 3 := Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg I hpq
    (f := fun i => (a i)^((2:ℝ)/3)) (g := fun _ => 1)
    (fun i hi => Real.rpow_nonneg (ha i hi) _) (fun _ _ => by norm_num)
  have hpow : ∀ i ∈ I, ((a i)^((2:ℝ)/3))^((3:ℝ)/2) = a i := by
    intro i hi
    rw [← Real.rpow_mul (ha i hi)]
    norm_num
  have hsum : (∑ i ∈ I, ((a i)^((2:ℝ)/3))^((3:ℝ)/2)) = ∑ i ∈ I, a i :=
    Finset.sum_congr rfl hpow
  simp only [mul_one, hsum, Real.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  norm_num at h
  exact h

end DistinctDistances.TrackC
