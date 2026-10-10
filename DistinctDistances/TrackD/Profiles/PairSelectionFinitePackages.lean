import DistinctDistances.TrackD.Profiles.PairSelectionDefs
import DistinctDistances.TrackD.Profiles.PairSelectionPackages

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section

/-- `profiles.tex:566–572`: count the two orientations on the core
by the outgoing fibres of the directional relation. -/
theorem pair_selection_core_count {α : Type*} (P S : Finset α) (hS : S ⊆ P)
    (R : α → α → Prop) (F η : ℝ) (hη : 0 ≤ η) (hN : 1 ≤ P.card)
    (hcover : (1 - η) * (P.card : ℝ) * ((P.card : ℝ) - 1) ≤
      (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
    (hfib : ∀ p ∈ S, ((S.filter (R p)).card : ℝ) ≤ F) :
    (S.card : ℝ) ^ 2 ≤ 2 * F * S.card + η * (P.card : ℝ) ^ 2 + S.card := by
  classical
  -- product and diagonal cards
  have hProdS : (S ×ˢ S).card = S.card * S.card :=
    Finset.card_product S S
  have hProdP : (P ×ˢ P).card = P.card * P.card :=
    Finset.card_product P P
  have hDiagS : ((S ×ˢ S).filter (fun pq : α × α => pq.1 = pq.2)).card
      = S.card := by
    have heq : ((S ×ˢ S).filter (fun pq : α × α => pq.1 = pq.2))
        = S.image (fun p => (p, p)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        subst hab
        exact ⟨a, ha, rfl, rfl⟩
      · rintro ⟨p, hp, rfl, rfl⟩
        exact ⟨⟨hp, hp⟩, rfl⟩
    rw [heq]
    exact Finset.card_image_of_injective S
      (fun a b h => congrArg Prod.fst h)
  have hDiagP : ((P ×ˢ P).filter (fun pq : α × α => pq.1 = pq.2)).card
      = P.card := by
    have heq : ((P ×ˢ P).filter (fun pq : α × α => pq.1 = pq.2))
        = P.image (fun p => (p, p)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        subst hab
        exact ⟨a, ha, rfl, rfl⟩
      · rintro ⟨p, hp, rfl, rfl⟩
        exact ⟨⟨hp, hp⟩, rfl⟩
    rw [heq]
    exact Finset.card_image_of_injective P
      (fun a b h => congrArg Prod.fst h)
  -- split product into diagonal and off-diagonal
  have hSplitS : ((S ×ˢ S).filter (fun pq : α × α => pq.1 = pq.2)) ∪
      ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2)) = S ×ˢ S := by
    ext pq
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hmem, _⟩ | ⟨hmem, _⟩) <;> exact hmem
    · intro hmem
      by_cases h : pq.1 = pq.2
      · exact Or.inl ⟨hmem, h⟩
      · exact Or.inr ⟨hmem, h⟩
  have hDisjS : Disjoint
      ((S ×ˢ S).filter (fun pq : α × α => pq.1 = pq.2))
      ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2)) := by
    rw [Finset.disjoint_left]
    intro pq h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hSplitP : ((P ×ˢ P).filter (fun pq : α × α => pq.1 = pq.2)) ∪
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)) = P ×ˢ P := by
    ext pq
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hmem, _⟩ | ⟨hmem, _⟩) <;> exact hmem
    · intro hmem
      by_cases h : pq.1 = pq.2
      · exact Or.inl ⟨hmem, h⟩
      · exact Or.inr ⟨hmem, h⟩
  have hDisjP : Disjoint
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 = pq.2))
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)) := by
    rw [Finset.disjoint_left]
    intro pq h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hOffS_card : ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2)).card
      + S.card = S.card * S.card := by
    have hcard := Finset.card_union_of_disjoint hDisjS
    rw [hSplitS, hProdS, hDiagS] at hcard
    omega
  have hOffP_card : ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)).card
      + P.card = P.card * P.card := by
    have hcard := Finset.card_union_of_disjoint hDisjP
    rw [hSplitP, hProdP, hDiagP] at hcard
    omega
  -- split off-diagonal into covered and uncovered
  have hOffS_split : ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      (R pq.1 pq.2 ∨ R pq.2 pq.1))) ∪
      ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1)))
      = ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2)) := by
    ext pq
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hmem, hne, _⟩ | ⟨hmem, hne, _⟩) <;> exact ⟨hmem, hne⟩
    · rintro ⟨hmem, hne⟩
      by_cases hR : R pq.1 pq.2 ∨ R pq.2 pq.1
      · exact Or.inl ⟨hmem, hne, hR⟩
      · exact Or.inr ⟨hmem, hne, hR⟩
  have hOffS_disj : Disjoint
      ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1)))
      ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))) := by
    rw [Finset.disjoint_left]
    intro pq h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2.2 h1.2.2
  have hOffP_split : ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      (R pq.1 pq.2 ∨ R pq.2 pq.1))) ∪
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1)))
      = ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)) := by
    ext pq
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hmem, hne, _⟩ | ⟨hmem, hne, _⟩) <;> exact ⟨hmem, hne⟩
    · rintro ⟨hmem, hne⟩
      by_cases hR : R pq.1 pq.2 ∨ R pq.2 pq.1
      · exact Or.inl ⟨hmem, hne, hR⟩
      · exact Or.inr ⟨hmem, hne, hR⟩
  have hOffP_disj : Disjoint
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1)))
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))) := by
    rw [Finset.disjoint_left]
    intro pq h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2.2 h1.2.2
  -- directed fibre bounds
  have hDirA_eq : ((S ×ˢ S).filter (fun pq : α × α => R pq.1 pq.2)).card
      = ∑ p ∈ S, (S.filter (R p)).card := by
    have hUnion : ((S ×ˢ S).filter (fun pq : α × α => R pq.1 pq.2))
        = S.biUnion (fun p => ({p} : Finset α) ×ˢ (S.filter (R p))) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_singleton, Finset.mem_filter]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨a, ha, rfl, hb, hab⟩
      · rintro ⟨p, hp, rfl, hb, hab⟩
        exact ⟨⟨hp, hb⟩, hab⟩
    have hDisj : ((S : Set α)).PairwiseDisjoint
        (fun p => ({p} : Finset α) ×ˢ (S.filter (R p))) := by
      intro p _ q _ hne
      apply Finset.disjoint_left.mpr
      intro pq h1 h2
      rcases Finset.mem_product.mp h1 with ⟨hm1, _⟩
      rcases Finset.mem_product.mp h2 with ⟨hm2, _⟩
      simp only [Finset.mem_singleton] at hm1 hm2
      exact hne (hm1.symm.trans hm2)
    rw [hUnion, Finset.card_biUnion hDisj]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.card_product, Finset.card_singleton, one_mul]
  have hDirB_eq : ((S ×ˢ S).filter (fun pq : α × α => R pq.2 pq.1)).card
      = ∑ q ∈ S, (S.filter (R q)).card := by
    have hUnion : ((S ×ˢ S).filter (fun pq : α × α => R pq.2 pq.1))
        = S.biUnion (fun q => (S.filter (R q)) ×ˢ ({q} : Finset α)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_singleton, Finset.mem_filter]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨b, hb, ⟨ha, hab⟩, rfl⟩
      · rintro ⟨q, hq, ⟨ha, hab⟩, rfl⟩
        exact ⟨⟨ha, hq⟩, hab⟩
    have hDisj : ((S : Set α)).PairwiseDisjoint
        (fun q => (S.filter (R q)) ×ˢ ({q} : Finset α)) := by
      intro p _ q _ hne
      apply Finset.disjoint_left.mpr
      intro pq h1 h2
      rcases Finset.mem_product.mp h1 with ⟨_, hm1⟩
      rcases Finset.mem_product.mp h2 with ⟨_, hm2⟩
      simp only [Finset.mem_singleton] at hm1 hm2
      exact hne (hm1.symm.trans hm2)
    rw [hUnion, Finset.card_biUnion hDisj]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.card_product, Finset.card_singleton, mul_one]
  have hDirA_real : (((S ×ˢ S).filter
      (fun pq : α × α => R pq.1 pq.2)).card : ℝ)
      = ∑ p ∈ S, ((S.filter (R p)).card : ℝ) := by
    rw [hDirA_eq]
    push_cast
    rfl
  have hDirB_real : (((S ×ˢ S).filter
      (fun pq : α × α => R pq.2 pq.1)).card : ℝ)
      = ∑ q ∈ S, ((S.filter (R q)).card : ℝ) := by
    rw [hDirB_eq]
    push_cast
    rfl
  have hDirA_le : (((S ×ˢ S).filter
      (fun pq : α × α => R pq.1 pq.2)).card : ℝ) ≤ F * S.card := by
    rw [hDirA_real]
    calc ∑ p ∈ S, ((S.filter (R p)).card : ℝ)
        ≤ ∑ _p ∈ S, F := Finset.sum_le_sum (fun p hp => hfib p hp)
      _ = F * S.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hDirB_le : (((S ×ˢ S).filter
      (fun pq : α × α => R pq.2 pq.1)).card : ℝ) ≤ F * S.card := by
    rw [hDirB_real]
    calc ∑ q ∈ S, ((S.filter (R q)).card : ℝ)
        ≤ ∑ _q ∈ S, F := Finset.sum_le_sum (fun q hq => hfib q hq)
      _ = F * S.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- covered in S bounded by the two directed counts
  have hCovSub : ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      (R pq.1 pq.2 ∨ R pq.2 pq.1)))
      ⊆ ((S ×ˢ S).filter (fun pq : α × α => R pq.1 pq.2)) ∪
        ((S ×ˢ S).filter (fun pq : α × α => R pq.2 pq.1)) := by
    intro pq h
    simp only [Finset.mem_filter, Finset.mem_product,
      Finset.mem_union] at h ⊢
    obtain ⟨⟨hs1, hs2⟩, _, hor⟩ := h
    rcases hor with hR | hR
    · exact Or.inl ⟨⟨hs1, hs2⟩, hR⟩
    · exact Or.inr ⟨⟨hs1, hs2⟩, hR⟩
  have hCov_le : ((((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      ≤ (((S ×ˢ S).filter (fun pq : α × α => R pq.1 pq.2)).card : ℝ)
        + (((S ×ˢ S).filter (fun pq : α × α => R pq.2 pq.1)).card : ℝ) := by
    calc ((((S ×ˢ S).filter _).card : ℝ))
        ≤ (((((S ×ˢ S).filter (fun pq : α × α => R pq.1 pq.2)) ∪
          ((S ×ˢ S).filter (fun pq : α × α => R pq.2 pq.1))).card : ℝ)) :=
          by exact_mod_cast Finset.card_le_card hCovSub
      _ ≤ _ + _ := by
          exact_mod_cast Finset.card_union_le _ _
  -- uncovered in S is contained in uncovered in P
  have hUncSub : ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1)))
      ⊆ ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))) := by
    intro pq h
    simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
    obtain ⟨⟨hs1, hs2⟩, hne, hR⟩ := h
    exact ⟨⟨hS hs1, hS hs2⟩, hne, hR⟩
  have hUncS_le_UncP : ((((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      ≤ ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ)) := by
    exact_mod_cast Finset.card_le_card hUncSub
  -- global uncovered bound from coverage hypothesis
  have hPpos : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hP1 : (1 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hN
  have hOffP_real : ((((P ×ˢ P).filter
      (fun pq : α × α => pq.1 ≠ pq.2)).card : ℝ))
      = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
    have hcast : ((((P ×ˢ P).filter
        (fun pq : α × α => pq.1 ≠ pq.2)).card : ℝ)) + (P.card : ℝ)
        = (P.card : ℝ) * (P.card : ℝ) := by
      have h1 : (((((P ×ˢ P).filter
          (fun pq : α × α => pq.1 ≠ pq.2)).card + P.card : ℕ) : ℝ))
          = (((P.card * P.card : ℕ)) : ℝ) := by
        exact_mod_cast hOffP_card
      rwa [Nat.cast_add, Nat.cast_mul] at h1
    have hEq : (P.card : ℝ) * ((P.card : ℝ) - 1)
        = (P.card : ℝ) * (P.card : ℝ) - (P.card : ℝ) := by ring
    linarith
  have hCovP_add_UncP : ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      + ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
    have hNat : ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1))).card
        + ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
          ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card
        = ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)).card := by
      have hcard := Finset.card_union_of_disjoint hOffP_disj
      rw [hOffP_split] at hcard
      omega
    have hcast : ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
        + ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
          ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
        = ((((P ×ˢ P).filter
          (fun pq : α × α => pq.1 ≠ pq.2)).card : ℝ)) := by
      exact_mod_cast hNat
    rw [hcast, hOffP_real]
  have hUncP_le : ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      ≤ η * (P.card : ℝ) ^ 2 := by
    have hM : (P.card : ℝ) * ((P.card : ℝ) - 1)
        = ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
          (R pq.1 pq.2 ∨ R pq.2 pq.1))).card
          + (((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
            ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ) := by
      linarith [hCovP_add_UncP]
    have hExpand : (1 - η) * ((P.card : ℝ) * ((P.card : ℝ) - 1))
        = ((P.card : ℝ) * ((P.card : ℝ) - 1))
          - η * ((P.card : ℝ) * ((P.card : ℝ) - 1)) := by ring
    have hU_le_M : ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
        ≤ η * ((P.card : ℝ) * ((P.card : ℝ) - 1)) := by
      linarith [hcover, hM, hExpand]
    have h2 : ((P.card : ℝ) * ((P.card : ℝ) - 1)) ≤ (P.card : ℝ) ^ 2 := by
      nlinarith [hPpos, hP1]
    have h3 : η * ((P.card : ℝ) * ((P.card : ℝ) - 1))
        ≤ η * (P.card : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 hη
    linarith [hU_le_M, h3]
  -- assemble S square
  have hS_real : ((((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      + ((((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      + (S.card : ℝ) = (S.card : ℝ) ^ 2 := by
    have hNat1 : ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1))).card
        + ((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
          ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card
        + S.card = S.card * S.card := by
      have hcard := Finset.card_union_of_disjoint hOffS_disj
      rw [hOffS_split] at hcard
      omega
    have hcast : ((((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
        + ((((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
          ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
        + (S.card : ℝ) = ((S.card * S.card : ℕ) : ℝ) := by
      exact_mod_cast hNat1
    rw [hcast]
    push_cast
    ring
  have hCovS_le : ((((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ)) ≤ 2 * F * S.card := by
    calc ((((S ×ˢ S).filter _).card : ℝ))
        ≤ (((S ×ˢ S).filter (fun pq : α × α => R pq.1 pq.2)).card : ℝ)
          + (((S ×ˢ S).filter (fun pq : α × α => R pq.2 pq.1)).card : ℝ) :=
          hCov_le
      _ ≤ F * S.card + F * S.card := add_le_add hDirA_le hDirB_le
      _ = 2 * F * S.card := by ring
  have hUncS_le : ((((S ×ˢ S).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ)) ≤ η * (P.card : ℝ) ^ 2 :=
    hUncS_le_UncP.trans hUncP_le
  linarith [hS_real, hCovS_le, hUncS_le]

/-- `profiles.tex:546–560, 607–619`: deletion from unoriented coverage.
The diagonal costs N; each oriented exceptional relation costs twice its size. -/
theorem pair_selection_delete_count {α : Type*} (P : Finset α)
    (R T L : α → α → Prop) (η εT εL : ℝ) (hη : 0 ≤ η) (hN : 1 ≤ P.card)
    (hcover : (1 - η) * (P.card : ℝ) * ((P.card : ℝ) - 1) ≤
      (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
    (hT : (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧ T pq.1 pq.2)).card : ℝ) ≤
      εT * (P.card : ℝ) ^ 2)
    (hL : (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧ L pq.1 pq.2)).card : ℝ) ≤
      εL * (P.card : ℝ) ^ 2) :
    (((P ×ˢ P).filter (fun pq =>
      ¬ (pq.1 ≠ pq.2 ∧ R pq.1 pq.2 ∧ ¬ T pq.1 pq.2 ∧ ¬ L pq.1 pq.2) ∧
      ¬ (pq.2 ≠ pq.1 ∧ R pq.2 pq.1 ∧ ¬ T pq.2 pq.1 ∧ ¬ L pq.2 pq.1))).card : ℝ) ≤
        (η + 2 * εT + 2 * εL) * (P.card : ℝ) ^ 2 + P.card := by
  classical
  -- diagonal card
  have hProdP : (P ×ˢ P).card = P.card * P.card :=
    Finset.card_product P P
  have hDiagP : ((P ×ˢ P).filter (fun pq : α × α => pq.1 = pq.2)).card
      = P.card := by
    have heq : ((P ×ˢ P).filter (fun pq : α × α => pq.1 = pq.2))
        = P.image (fun p => (p, p)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        subst hab
        exact ⟨a, ha, rfl, rfl⟩
      · rintro ⟨p, hp, rfl, rfl⟩
        exact ⟨⟨hp, hp⟩, rfl⟩
    rw [heq]
    exact Finset.card_image_of_injective P
      (fun a b h => congrArg Prod.fst h)
  -- off-diagonal split for the global uncovered bound
  have hSplitP : ((P ×ˢ P).filter (fun pq : α × α => pq.1 = pq.2)) ∪
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)) = P ×ˢ P := by
    ext pq
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hmem, _⟩ | ⟨hmem, _⟩) <;> exact hmem
    · intro hmem
      by_cases h : pq.1 = pq.2
      · exact Or.inl ⟨hmem, h⟩
      · exact Or.inr ⟨hmem, h⟩
  have hDisjP : Disjoint
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 = pq.2))
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)) := by
    rw [Finset.disjoint_left]
    intro pq h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hOffP_card : ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)).card
      + P.card = P.card * P.card := by
    have hcard := Finset.card_union_of_disjoint hDisjP
    rw [hSplitP, hProdP, hDiagP] at hcard
    omega
  have hOffP_split : ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      (R pq.1 pq.2 ∨ R pq.2 pq.1))) ∪
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1)))
      = ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)) := by
    ext pq
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hmem, hne, _⟩ | ⟨hmem, hne, _⟩) <;> exact ⟨hmem, hne⟩
    · rintro ⟨hmem, hne⟩
      by_cases hR : R pq.1 pq.2 ∨ R pq.2 pq.1
      · exact Or.inl ⟨hmem, hne, hR⟩
      · exact Or.inr ⟨hmem, hne, hR⟩
  have hOffP_disj : Disjoint
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1)))
      ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))) := by
    rw [Finset.disjoint_left]
    intro pq h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2.2 h1.2.2
  have hPpos : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hP1 : (1 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hN
  have hOffP_real : ((((P ×ˢ P).filter
      (fun pq : α × α => pq.1 ≠ pq.2)).card : ℝ))
      = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
    have hcast : ((((P ×ˢ P).filter
        (fun pq : α × α => pq.1 ≠ pq.2)).card : ℝ)) + (P.card : ℝ)
        = (P.card : ℝ) * (P.card : ℝ) := by
      have h1 : (((((P ×ˢ P).filter
          (fun pq : α × α => pq.1 ≠ pq.2)).card + P.card : ℕ) : ℝ))
          = (((P.card * P.card : ℕ)) : ℝ) := by
        exact_mod_cast hOffP_card
      rwa [Nat.cast_add, Nat.cast_mul] at h1
    have hEq : (P.card : ℝ) * ((P.card : ℝ) - 1)
        = (P.card : ℝ) * (P.card : ℝ) - (P.card : ℝ) := by ring
    linarith
  have hCovP_add_UncP : ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      + ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
    have hNat : ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1))).card
        + ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
          ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card
        = ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2)).card := by
      have hcard := Finset.card_union_of_disjoint hOffP_disj
      rw [hOffP_split] at hcard
      omega
    have hcast : ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
        + ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
          ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
        = ((((P ×ˢ P).filter
          (fun pq : α × α => pq.1 ≠ pq.2)).card : ℝ)) := by
      exact_mod_cast hNat
    rw [hcast, hOffP_real]
  have hUncP_le : ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
      ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
      ≤ η * (P.card : ℝ) ^ 2 := by
    have hM : (P.card : ℝ) * ((P.card : ℝ) - 1)
        = ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
          (R pq.1 pq.2 ∨ R pq.2 pq.1))).card
          + (((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
            ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ) := by
      linarith [hCovP_add_UncP]
    have hExpand : (1 - η) * ((P.card : ℝ) * ((P.card : ℝ) - 1))
        = ((P.card : ℝ) * ((P.card : ℝ) - 1))
          - η * ((P.card : ℝ) * ((P.card : ℝ) - 1)) := by ring
    have hU_le_M : ((((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
        ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))).card : ℝ))
        ≤ η * ((P.card : ℝ) * ((P.card : ℝ) - 1)) := by
      linarith [hcover, hM, hExpand]
    have h2 : ((P.card : ℝ) * ((P.card : ℝ) - 1)) ≤ (P.card : ℝ) ^ 2 := by
      nlinarith [hPpos, hP1]
    have h3 : η * ((P.card : ℝ) * ((P.card : ℝ) - 1))
        ≤ η * (P.card : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 hη
    linarith [hU_le_M, h3]
  -- transpose preserves cardinality
  have hSwap_inj : Function.Injective (Prod.swap : α × α → α × α) := by
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    simp only [Prod.swap, Prod.mk.injEq] at h ⊢
    obtain ⟨h2, h1⟩ := h
    exact ⟨h1, h2⟩
  have hTt_eq : ((P ×ˢ P).filter (fun pq : α × α => pq.2 ≠ pq.1 ∧ T pq.2 pq.1))
      = (((P ×ˢ P).filter
        (fun pq : α × α => pq.1 ≠ pq.2 ∧ T pq.1 pq.2)).image Prod.swap) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hne, hT⟩
      exact ⟨(b, a), ⟨⟨hb, ha⟩, hne, hT⟩, rfl⟩
    · rintro ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, hne, hT⟩, hEq⟩
      simp only [Prod.swap, Prod.mk.injEq] at hEq
      obtain ⟨h1, h2⟩ := hEq
      subst h1
      subst h2
      exact ⟨⟨hd, hc⟩, hne, hT⟩
  have hLt_eq : ((P ×ˢ P).filter (fun pq : α × α => pq.2 ≠ pq.1 ∧ L pq.2 pq.1))
      = (((P ×ˢ P).filter
        (fun pq : α × α => pq.1 ≠ pq.2 ∧ L pq.1 pq.2)).image Prod.swap) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hne, hL⟩
      exact ⟨(b, a), ⟨⟨hb, ha⟩, hne, hL⟩, rfl⟩
    · rintro ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, hne, hL⟩, hEq⟩
      simp only [Prod.swap, Prod.mk.injEq] at hEq
      obtain ⟨h1, h2⟩ := hEq
      subst h1
      subst h2
      exact ⟨⟨hd, hc⟩, hne, hL⟩
  have hTt_card : ((((P ×ˢ P).filter
      (fun pq : α × α => pq.2 ≠ pq.1 ∧ T pq.2 pq.1)).card : ℝ))
      ≤ εT * (P.card : ℝ) ^ 2 := by
    rw [hTt_eq, Finset.card_image_of_injective _ hSwap_inj]
    exact hT
  have hLt_card : ((((P ×ˢ P).filter
      (fun pq : α × α => pq.2 ≠ pq.1 ∧ L pq.2 pq.1)).card : ℝ))
      ≤ εL * (P.card : ℝ) ^ 2 := by
    rw [hLt_eq, Finset.card_image_of_injective _ hSwap_inj]
    exact hL
  -- deleted set is covered by diagonal, uncovered, T/Tt, L/Lt
  have hDelSub : ((P ×ˢ P).filter (fun pq : α × α =>
      ¬ (pq.1 ≠ pq.2 ∧ R pq.1 pq.2 ∧ ¬ T pq.1 pq.2 ∧ ¬ L pq.1 pq.2) ∧
      ¬ (pq.2 ≠ pq.1 ∧ R pq.2 pq.1 ∧ ¬ T pq.2 pq.1 ∧ ¬ L pq.2 pq.1)))
      ⊆ ((P ×ˢ P).filter (fun pq : α × α => pq.1 = pq.2)) ∪
        ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧
          ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1))) ∪
        ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧ T pq.1 pq.2)) ∪
        ((P ×ˢ P).filter (fun pq : α × α => pq.2 ≠ pq.1 ∧ T pq.2 pq.1)) ∪
        ((P ×ˢ P).filter (fun pq : α × α => pq.1 ≠ pq.2 ∧ L pq.1 pq.2)) ∪
        ((P ×ˢ P).filter (fun pq : α × α => pq.2 ≠ pq.1 ∧ L pq.2 pq.1)) := by
    intro pq h
    simp only [Finset.mem_filter, Finset.mem_product,
      Finset.mem_union] at h ⊢
    obtain ⟨⟨hP1, hP2⟩, hnA, hnB⟩ := h
    by_cases hdiag : pq.1 = pq.2
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        ⟨⟨hP1, hP2⟩, hdiag⟩))))
    · have hne : pq.1 ≠ pq.2 := hdiag
      have hne' : pq.2 ≠ pq.1 := Ne.symm hne
      by_cases hR : R pq.1 pq.2 ∨ R pq.2 pq.1
      · rcases hR with hR1 | hR2
        · have hTL : T pq.1 pq.2 ∨ L pq.1 pq.2 := by
            by_contra hcon
            push Not at hcon
            exact hnA ⟨hne, hR1, hcon.1, hcon.2⟩
          rcases hTL with hT1 | hL1
          · exact Or.inl (Or.inl (Or.inl (Or.inr
              ⟨⟨hP1, hP2⟩, hne, hT1⟩)))
          · exact Or.inl (Or.inr
              ⟨⟨hP1, hP2⟩, hne, hL1⟩)
        · have hTL : T pq.2 pq.1 ∨ L pq.2 pq.1 := by
            by_contra hcon
            push Not at hcon
            exact hnB ⟨hne', hR2, hcon.1, hcon.2⟩
          rcases hTL with hT2 | hL2
          · exact Or.inl (Or.inl (Or.inr
              ⟨⟨hP1, hP2⟩, hne', hT2⟩))
          · exact Or.inr
              ⟨⟨hP1, hP2⟩, hne', hL2⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
          ⟨⟨hP1, hP2⟩, hne, hR⟩))))
  set Dg : Finset (α × α) :=
    (P ×ˢ P).filter (fun pq => pq.1 = pq.2) with hDg_def
  set U0 : Finset (α × α) := (P ×ˢ P).filter (fun pq =>
    pq.1 ≠ pq.2 ∧ ¬ (R pq.1 pq.2 ∨ R pq.2 pq.1)) with hU0_def
  set T0 : Finset (α × α) := (P ×ˢ P).filter (fun pq =>
    pq.1 ≠ pq.2 ∧ T pq.1 pq.2) with hT0_def
  set Tt0 : Finset (α × α) := (P ×ˢ P).filter (fun pq =>
    pq.2 ≠ pq.1 ∧ T pq.2 pq.1) with hTt0_def
  set L0 : Finset (α × α) := (P ×ˢ P).filter (fun pq =>
    pq.1 ≠ pq.2 ∧ L pq.1 pq.2) with hL0_def
  set Lt0 : Finset (α × α) := (P ×ˢ P).filter (fun pq =>
    pq.2 ≠ pq.1 ∧ L pq.2 pq.1) with hLt0_def
  have hDg_card : Dg.card = P.card := hDiagP
  have hUnion_le : ((Dg ∪ U0 ∪ T0 ∪ Tt0 ∪ L0 ∪ Lt0).card : ℝ)
      ≤ (P.card : ℝ) + η * (P.card : ℝ) ^ 2
        + εT * (P.card : ℝ) ^ 2 + εT * (P.card : ℝ) ^ 2
        + εL * (P.card : ℝ) ^ 2 + εL * (P.card : ℝ) ^ 2 := by
    have h1 : (Dg ∪ U0 ∪ T0 ∪ Tt0 ∪ L0 ∪ Lt0).card
        ≤ P.card + U0.card + T0.card + Tt0.card + L0.card + Lt0.card := by
      calc (Dg ∪ U0 ∪ T0 ∪ Tt0 ∪ L0 ∪ Lt0).card
          ≤ (Dg ∪ U0 ∪ T0 ∪ Tt0 ∪ L0).card + Lt0.card :=
            Finset.card_union_le _ _
        _ ≤ P.card + U0.card + T0.card + Tt0.card + L0.card + Lt0.card := by
            have h := Finset.card_union_le
              (Dg ∪ U0 ∪ T0 ∪ Tt0 ∪ L0) Lt0
            have h2 := Finset.card_union_le
              (Dg ∪ U0 ∪ T0 ∪ Tt0) L0
            have h3 := Finset.card_union_le
              (Dg ∪ U0 ∪ T0) Tt0
            have h4 := Finset.card_union_le
              (Dg ∪ U0) T0
            have h5 := Finset.card_union_le Dg U0
            rw [hDg_card] at h5
            omega
    have hcast : ((Dg ∪ U0 ∪ T0 ∪ Tt0 ∪ L0 ∪ Lt0).card : ℝ)
        ≤ (P.card : ℝ) + (U0.card : ℝ) + (T0.card : ℝ)
          + (Tt0.card : ℝ) + (L0.card : ℝ) + (Lt0.card : ℝ) := by
      have h1r : (((Dg ∪ U0 ∪ T0 ∪ Tt0 ∪ L0 ∪ Lt0).card : ℕ) : ℝ)
          ≤ (((P.card + U0.card + T0.card + Tt0.card + L0.card
            + Lt0.card : ℕ)) : ℝ) := by
        exact_mod_cast h1
      rwa [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_add,
        Nat.cast_add] at h1r
    have hT0r : (T0.card : ℝ) ≤ εT * (P.card : ℝ) ^ 2 := hT
    have hTt0r : (Tt0.card : ℝ) ≤ εT * (P.card : ℝ) ^ 2 := hTt_card
    have hL0r : (L0.card : ℝ) ≤ εL * (P.card : ℝ) ^ 2 := hL
    have hLt0r : (Lt0.card : ℝ) ≤ εL * (P.card : ℝ) ^ 2 := hLt_card
    have hU0r : (U0.card : ℝ) ≤ η * (P.card : ℝ) ^ 2 := hUncP_le
    linarith [hcast, hU0r, hT0r, hTt0r, hL0r, hLt0r]
  have hDelSub' : ((P ×ˢ P).filter (fun pq : α × α =>
      ¬ (pq.1 ≠ pq.2 ∧ R pq.1 pq.2 ∧ ¬ T pq.1 pq.2 ∧ ¬ L pq.1 pq.2) ∧
      ¬ (pq.2 ≠ pq.1 ∧ R pq.2 pq.1 ∧ ¬ T pq.2 pq.1 ∧ ¬ L pq.2 pq.1)))
      ⊆ Dg ∪ U0 ∪ T0 ∪ Tt0 ∪ L0 ∪ Lt0 := hDelSub
  calc (((P ×ˢ P).filter (fun pq =>
      ¬ (pq.1 ≠ pq.2 ∧ R pq.1 pq.2 ∧ ¬ T pq.1 pq.2 ∧ ¬ L pq.1 pq.2) ∧
      ¬ (pq.2 ≠ pq.1 ∧ R pq.2 pq.1 ∧ ¬ T pq.2 pq.1 ∧ ¬ L pq.2 pq.1))).card : ℝ)
      ≤ (((Dg ∪ U0 ∪ T0 ∪ Tt0 ∪ L0 ∪ Lt0).card : ℝ)) := by
        exact_mod_cast Finset.card_le_card hDelSub'
    _ ≤ (P.card : ℝ) + η * (P.card : ℝ) ^ 2
        + εT * (P.card : ℝ) ^ 2 + εT * (P.card : ℝ) ^ 2
        + εL * (P.card : ℝ) ^ 2 + εL * (P.card : ℝ) ^ 2 := hUnion_le
    _ = (η + 2 * εT + 2 * εL) * (P.card : ℝ) ^ 2 + P.card := by ring

/-- `profiles.tex:596–606`: outer-window refinement. The threshold
precedes P, δ, the pieces and the retained directed relation. -/
theorem pair_selection_outer_pool (d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ a > 0, ∀ (P : Finset (Pt d)) (pl : Finset (Piece d)) (δ : ℝ)
      (R : Pt d → Pt d → Prop),
      0 < cfgN P → 0 < δ → δ ≤ a →
      (∀ X ∈ pl, X.pts ⊆ P) → (pl : Set (Piece d)).PairwiseDisjoint Piece.pts →
      (∀ X ∈ pl, ∀ i, -1 ≤ X.path.time i ∧ X.path.time i ≤ 2) →
      (∀ X ∈ pl, X.width = Real.log (cfgB P)) →
      cfgN P / 4 ≤ (poolPts pl).card →
      (((P ×ˢ P).filter (fun pq => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ) ≤
        a * cfgN P ^ 2 →
      ∃ (pool : Finset (Piece d)) (t : Fin d → ℝ), pool ⊆ pl ∧ pool.Nonempty ∧
        (∀ X ∈ pool, ∀ i, |X.path.time i - t i| ≤ ρ) ∧
        cfgN P * Real.sqrt δ ≤ (poolPts pool).card ∧
        (1 / 2 - ρ) * (poolPts pool).card * (poolPts pool).card ≤
          (((poolPts pool ×ˢ poolPts pool).filter (fun pq => R pq.1 pq.2)).card : ℝ) := by
  classical
  obtain ⟨K, hK, label, hlabel⟩ := pair_selection_profile_grid d ρ hρ
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK2 : (0 : ℝ) < 16 * ((K : ℝ) ^ 2) := by positivity
  refine ⟨min (1 / (16 * ((K : ℝ) ^ 2))) (ρ / (16 * ((K : ℝ) ^ 2))),
    lt_min (by positivity) (by positivity), ?_⟩
  intro P pl δ R hN hδ hδa hsub hdisj htime _hwidth hmass hbad
  simp only [cfgN] at hN hmass ⊢
  -- extended profiles in [-1,2]
  let v : Piece d → (Fin (d + 1) → ℝ) := fun X j =>
    if h : j.val < d then X.path.time ⟨j.val, h⟩ else 0
  have hv_mem : ∀ X ∈ pl, ∀ j, -1 ≤ v X j ∧ v X j ≤ 2 := by
    intro X hX j
    dsimp [v]
    by_cases hj : j.val < d
    · rw [dif_pos hj]
      exact htime X hX ⟨j.val, hj⟩
    · rw [dif_neg hj]
      constructor <;> norm_num
  let bin : Piece d → Fin K := fun X => label (v X)
  -- mass per label
  let mass : Fin K → ℝ := fun k =>
    ((poolPts (pl.filter (fun X => bin X = k))).card : ℝ)
  have hdisjF : ∀ k, ((pl.filter (fun X => bin X = k) : Finset (Piece d)) :
      Set (Piece d)).PairwiseDisjoint Piece.pts := by
    intro k X hX Y hY hXY
    have hXpl : X ∈ pl := (Finset.mem_filter.mp (Finset.mem_coe.mp hX)).1
    have hYpl : Y ∈ pl := (Finset.mem_filter.mp (Finset.mem_coe.mp hY)).1
    exact hdisj hXpl hYpl hXY
  have hcardF : ∀ k, ((poolPts (pl.filter (fun X => bin X = k))).card : ℝ)
      = ∑ X ∈ pl.filter (fun X => bin X = k), ((X.pts.card : ℝ)) := by
    intro k
    have h := Finset.card_biUnion (hdisjF k)
    simp only [poolPts] at h ⊢
    rw [h]
    push_cast
    rfl
  have htotal : ((poolPts pl).card : ℝ)
      = ∑ k ∈ (Finset.univ : Finset (Fin K)), mass k := by
    have hcardPl : ((poolPts pl).card : ℝ)
        = ∑ X ∈ pl, ((X.pts.card : ℝ)) := by
      have h := Finset.card_biUnion hdisj
      simp only [poolPts] at h ⊢
      rw [h]
      push_cast
      rfl
    rw [hcardPl]
    dsimp only [mass]
    simp only [hcardF]
    have hfib := Finset.sum_fiberwise_eq_sum_filter pl Finset.univ bin
      (fun X => ((X.pts.card : ℝ)))
    simpa [Finset.mem_univ] using hfib.symm
  -- largest label pool
  have hKne : (Finset.univ : Finset (Fin K)).Nonempty := by
    have h0 : (⟨0, hK⟩ : Fin K) ∈ (Finset.univ : Finset (Fin K)) :=
      Finset.mem_univ _
    exact ⟨_, h0⟩
  have hImgNe : ((Finset.univ : Finset (Fin K)).image mass).Nonempty :=
    Finset.image_nonempty.mpr hKne
  obtain ⟨k0, hk0mem, hk0eq⟩ :
      ∃ k0 ∈ (Finset.univ : Finset (Fin K)),
        mass k0 = ((Finset.univ : Finset (Fin K)).image mass).max' hImgNe := by
    have hmem := Finset.max'_mem _ hImgNe
    obtain ⟨k0, hk0, hk0eq⟩ := Finset.mem_image.mp hmem
    exact ⟨k0, hk0, hk0eq⟩
  have hk0max : ∀ k ∈ (Finset.univ : Finset (Fin K)), mass k ≤ mass k0 := by
    intro k hk
    have hmem : mass k ∈ (Finset.univ : Finset (Fin K)).image mass :=
      Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hle := Finset.le_max' _ _ hmem
    rwa [← hk0eq] at hle
  have hsum_le : ∑ k ∈ (Finset.univ : Finset (Fin K)), mass k
      ≤ ((Finset.univ : Finset (Fin K)).card : ℝ) * mass k0 := by
    calc ∑ k ∈ (Finset.univ : Finset (Fin K)), mass k
        ≤ ∑ _k ∈ (Finset.univ : Finset (Fin K)), mass k0 :=
          Finset.sum_le_sum (fun k hk => hk0max k hk)
      _ = ((Finset.univ : Finset (Fin K)).card : ℝ) * mass k0 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcardK : (Finset.univ : Finset (Fin K)).card = K := by simp
  have hmass0 : ((poolPts pl).card : ℝ) / (K : ℝ) ≤ mass k0 := by
    have hKne' : (K : ℝ) ≠ 0 := ne_of_gt hKr
    have h1 : ∑ k ∈ (Finset.univ : Finset (Fin K)), mass k
        ≤ (K : ℝ) * mass k0 := by
      have hsum := hsum_le
      rw [hcardK] at hsum
      simpa [hcardK] using hsum
    have h2 : (∑ k ∈ (Finset.univ : Finset (Fin K)), mass k) / (K : ℝ)
        ≤ ((K : ℝ) * mass k0) / (K : ℝ) :=
      div_le_div_of_nonneg_right h1 hKr.le
    rw [mul_div_cancel_left₀ _ hKne'] at h2
    rwa [htotal]
  -- the pool is the largest label class
  set pool : Finset (Piece d) := pl.filter (fun X => bin X = k0) with hpool_def
  have hpool_sub : pool ⊆ pl := Finset.filter_subset _ _
  have hmass_pool : mass k0 = ((poolPts pool).card : ℝ) := rfl
  have hPoolMass : (P.card : ℝ) / (4 * (K : ℝ)) ≤ ((poolPts pool).card : ℝ) := by
    have htot : (P.card : ℝ) / 4 ≤ ((poolPts pl).card : ℝ) := hmass
    have hle : ((poolPts pl).card : ℝ) / (K : ℝ) ≤ ((poolPts pool).card : ℝ) := by
      rw [← hmass_pool]
      exact hmass0
    have hKpos : (0 : ℝ) < (K : ℝ) := hKr
    have h4K : (0 : ℝ) < 4 * (K : ℝ) := by positivity
    rw [div_le_iff₀ hKpos] at hle
    rw [div_le_iff₀ h4K]
    nlinarith [htot, hle, htot]
  have hpool_ne : pool.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have hempty : poolPts pool = ∅ := by
      simp [poolPts, hcon]
    have hzero : ((poolPts pool).card : ℝ) = 0 := by
      simp [hempty]
    have hPpos : (0 : ℝ) < (P.card : ℝ) := hN
    have h4K : (0 : ℝ) < 4 * (K : ℝ) := by positivity
    have hpos : (0 : ℝ) < (P.card : ℝ) / (4 * (K : ℝ)) :=
      div_pos hPpos h4K
    linarith [hPoolMass, hzero, hpos]
  obtain ⟨X0, hX0⟩ := hpool_ne
  have hX0pl : X0 ∈ pl := hpool_sub hX0
  let t : Fin d → ℝ := X0.path.time
  have hclose : ∀ X ∈ pool, ∀ i, |X.path.time i - t i| ≤ ρ := by
    intro X hX i
    have hXpl : X ∈ pl := hpool_sub hX
    have hbinX : bin X = k0 := (Finset.mem_filter.mp hX).2
    have hbin0 : bin X0 = k0 := (Finset.mem_filter.mp hX0).2
    have hlab : label (v X) = label (v X0) := by
      dsimp [bin] at hbinX hbin0
      rw [hbinX, hbin0]
    have hvX := hv_mem X hXpl
    have hv0 := hv_mem X0 hX0pl
    have hgrid := hlabel (v X) (v X0) hvX hv0 hlab
    let j : Fin (d + 1) := Fin.castSucc i
    have hji : j.val = i.val := rfl
    have hlt : j.val < d := by
      rw [hji]
      exact i.isLt
    have hXeq : v X j = X.path.time i := by
      have hEq : (⟨(j.val), hlt⟩ : Fin d) = i := Fin.ext hji
      simp only [v, dif_pos hlt, hEq]
    have h0eq : v X0 j = t i := by
      have hEq : (⟨(j.val), hlt⟩ : Fin d) = i := Fin.ext hji
      simp only [v, t, dif_pos hlt, hEq]
    have hji_le := hgrid j
    rwa [hXeq, h0eq] at hji_le
  have ha1 : min (1 / (16 * ((K : ℝ) ^ 2))) (ρ / (16 * ((K : ℝ) ^ 2)))
      ≤ 1 / (16 * ((K : ℝ) ^ 2)) := min_le_left _ _
  have ha2 : min (1 / (16 * ((K : ℝ) ^ 2))) (ρ / (16 * ((K : ℝ) ^ 2)))
      ≤ ρ / (16 * ((K : ℝ) ^ 2)) := min_le_right _ _
  have hδsmall : δ ≤ 1 / (16 * ((K : ℝ) ^ 2)) := hδa.trans ha1
  have hsqrt_le : Real.sqrt δ ≤ 1 / (4 * (K : ℝ)) := by
    have hsq : ((1 / (4 * (K : ℝ))) : ℝ) ^ 2 = 1 / (16 * ((K : ℝ) ^ 2)) := by
      field_simp
      ring
    have hnn : (0 : ℝ) ≤ 1 / (4 * (K : ℝ)) := by positivity
    have hδsq : δ ≤ ((1 / (4 * (K : ℝ))) : ℝ) ^ 2 := hsq ▸ hδsmall
    calc Real.sqrt δ ≤ Real.sqrt (((1 / (4 * (K : ℝ))) : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt hδsq
      _ = 1 / (4 * (K : ℝ)) := Real.sqrt_sq hnn
  have hsqrt_mass : (P.card : ℝ) * Real.sqrt δ ≤ ((poolPts pool).card : ℝ) := by
    have hle : (P.card : ℝ) * Real.sqrt δ
        ≤ (P.card : ℝ) * (1 / (4 * (K : ℝ))) := by
      apply mul_le_mul_of_nonneg_left hsqrt_le hN.le
    have heq : (P.card : ℝ) * (1 / (4 * (K : ℝ)))
        = (P.card : ℝ) / (4 * (K : ℝ)) := by
      field_simp
    linarith [hle, heq, hPoolMass]
  set U : Finset (Pt d) := poolPts pool with hU_def
  have hUsub : U ⊆ P := by
    intro x hx
    simp only [hU_def, poolPts, Finset.mem_biUnion] at hx
    obtain ⟨X, hX, hxX⟩ := hx
    exact hsub X (hpool_sub hX) hxX
  have hUprod_sub : U ×ˢ U ⊆ P ×ˢ P :=
    Finset.product_subset_product hUsub hUsub
  have hBadU_le : ((((U ×ˢ U).filter
      (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ))
      ≤ min (1 / (16 * ((K : ℝ) ^ 2))) (ρ / (16 * ((K : ℝ) ^ 2)))
        * (P.card : ℝ) ^ 2 := by
    have hSub : ((U ×ˢ U).filter
        (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1))
        ⊆ ((P ×ˢ P).filter
          (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)) := by
      intro pq h
      simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
      obtain ⟨⟨hu1, hu2⟩, hR⟩ := h
      exact ⟨⟨hUsub hu1, hUsub hu2⟩, hR⟩
    calc ((((U ×ˢ U).filter _).card : ℝ))
        ≤ ((((P ×ˢ P).filter
          (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) := by
          exact_mod_cast Finset.card_le_card hSub
      _ ≤ min (1 / (16 * ((K : ℝ) ^ 2))) (ρ / (16 * ((K : ℝ) ^ 2)))
          * (P.card : ℝ) ^ 2 := by
          simpa [cfgN] using hbad
  have hSwapU : Function.Injective (Prod.swap : Pt d × Pt d → Pt d × Pt d) := by
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    simp only [Prod.swap, Prod.mk.injEq] at h ⊢
    obtain ⟨h2, h1⟩ := h
    exact ⟨h1, h2⟩
  have hFB : (((U ×ˢ U).filter
      (fun pq : Pt d × Pt d => R pq.2 pq.1)).card : ℕ)
      = (((U ×ˢ U).filter
        (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℕ) := by
    have heq : ((U ×ˢ U).filter
        (fun pq : Pt d × Pt d => R pq.2 pq.1))
        = (((U ×ˢ U).filter
          (fun pq : Pt d × Pt d => R pq.1 pq.2)).image Prod.swap) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, hb⟩, hR⟩
        exact ⟨(b, a), ⟨⟨hb, ha⟩, hR⟩, rfl⟩
      · rintro ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, hR⟩, hEq⟩
        simp only [Prod.swap, Prod.mk.injEq] at hEq
        obtain ⟨h1, h2⟩ := hEq
        subst h1
        subst h2
        exact ⟨⟨hd, hc⟩, hR⟩
    rw [heq, Finset.card_image_of_injective _ hSwapU]
  have hCoverU : U ×ˢ U ⊆ ((U ×ˢ U).filter
      (fun pq : Pt d × Pt d => R pq.1 pq.2)) ∪
        ((U ×ˢ U).filter
          (fun pq : Pt d × Pt d => R pq.2 pq.1)) ∪
        ((U ×ˢ U).filter
          (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)) := by
    intro pq h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_union] at h ⊢
    obtain ⟨hu1, hu2⟩ := h
    by_cases hR : R pq.1 pq.2 ∨ R pq.2 pq.1
    · rcases hR with hR1 | hR2
      · exact Or.inl (Or.inl ⟨⟨hu1, hu2⟩, hR1⟩)
      · exact Or.inl (Or.inr ⟨⟨hu1, hu2⟩, hR2⟩)
    · have hn1 : ¬ R pq.1 pq.2 := fun h => hR (Or.inl h)
      have hn2 : ¬ R pq.2 pq.1 := fun h => hR (Or.inr h)
      exact Or.inr ⟨⟨hu1, hu2⟩, hn1, hn2⟩
  have hProdU : (U ×ˢ U).card = U.card * U.card := Finset.card_product _ _
  have hcard_le : (U.card : ℝ) * (U.card : ℝ)
      ≤ 2 * ((((U ×ˢ U).filter
        (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ))
        + ((((U ×ˢ U).filter
          (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) := by
    have hNat : (U ×ˢ U).card ≤ (((U ×ˢ U).filter
        (fun pq : Pt d × Pt d => R pq.1 pq.2)).card)
        + (((U ×ˢ U).filter
          (fun pq : Pt d × Pt d => R pq.2 pq.1)).card)
        + (((U ×ˢ U).filter
          (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card) := by
      have h1 := Finset.card_union_le
        (((U ×ˢ U).filter (fun pq : Pt d × Pt d => R pq.1 pq.2)) ∪
          ((U ×ˢ U).filter (fun pq : Pt d × Pt d => R pq.2 pq.1)))
        (((U ×ˢ U).filter
          (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)))
      have h2 := Finset.card_union_le
        (((U ×ˢ U).filter (fun pq : Pt d × Pt d => R pq.1 pq.2)))
        (((U ×ˢ U).filter (fun pq : Pt d × Pt d => R pq.2 pq.1)))
      have h3 := Finset.card_le_card hCoverU
      rw [hProdU] at h3 ⊢
      omega
    have hcast : ((U.card : ℝ) * (U.card : ℝ))
        = ((((U ×ˢ U).card : ℕ)) : ℝ) := by
      rw [hProdU]
      push_cast
      ring
    have hNatR : ((((U ×ˢ U).card : ℕ)) : ℝ)
        ≤ ((((U ×ˢ U).filter
          (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ))
          + ((((U ×ˢ U).filter
            (fun pq : Pt d × Pt d => R pq.2 pq.1)).card : ℝ))
          + ((((U ×ˢ U).filter
            (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) := by
      exact_mod_cast hNat
    rw [← hcast] at hNatR
    have hBeq : ((((U ×ˢ U).filter
        (fun pq : Pt d × Pt d => R pq.2 pq.1)).card : ℝ))
        = ((((U ×ˢ U).filter
          (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ)) := by
      exact_mod_cast hFB
    linarith [hNatR, hBeq]
  have hNp : (P.card : ℝ) / (4 * (K : ℝ)) ≤ (U.card : ℝ) := hPoolMass
  have hdens : (1 / 2 - ρ) * (U.card : ℝ) * (U.card : ℝ)
      ≤ ((((U ×ˢ U).filter
        (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ)) := by
    have hBad_le : ((((U ×ˢ U).filter
        (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ))
        ≤ 2 * ρ * (U.card : ℝ) * (U.card : ℝ) := by
      have ha_le : min (1 / (16 * ((K : ℝ) ^ 2))) (ρ / (16 * ((K : ℝ) ^ 2)))
          * (P.card : ℝ) ^ 2 ≤ 2 * ρ * (U.card : ℝ) * (U.card : ℝ) := by
        have hNp2 : ((P.card : ℝ) / (4 * (K : ℝ))) ^ 2 ≤ (U.card : ℝ) ^ 2 := by
          apply sq_le_sq.mpr
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (P.card:ℝ)/(4*(K:ℝ)))]
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
          exact hNp
        have hKsq : (P.card : ℝ) ^ 2 / (16 * ((K : ℝ) ^ 2))
            ≤ (U.card : ℝ) ^ 2 := by
          have : ((P.card : ℝ) / (4 * (K : ℝ))) ^ 2
              = (P.card : ℝ) ^ 2 / (16 * ((K : ℝ) ^ 2)) := by
            field_simp
            ring
          linarith [hNp2, this]
        have hmin : min (1 / (16 * ((K : ℝ) ^ 2))) (ρ / (16 * ((K : ℝ) ^ 2)))
            ≤ ρ / (16 * ((K : ℝ) ^ 2)) := min_le_right _ _
        have hmul : min (1 / (16 * ((K : ℝ) ^ 2))) (ρ / (16 * ((K : ℝ) ^ 2)))
            * (P.card : ℝ) ^ 2
            ≤ (ρ / (16 * ((K : ℝ) ^ 2))) * (P.card : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hmin (sq_nonneg _)
        have heq : (ρ / (16 * ((K : ℝ) ^ 2))) * (P.card : ℝ) ^ 2
            = ρ * ((P.card : ℝ) ^ 2 / (16 * ((K : ℝ) ^ 2))) := by ring
        have hle2 : ρ * ((P.card : ℝ) ^ 2 / (16 * ((K : ℝ) ^ 2)))
            ≤ ρ * (U.card : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hKsq hρ.le
        have heq2 : 2 * ρ * (U.card : ℝ) * (U.card : ℝ)
            = 2 * (ρ * (U.card : ℝ) ^ 2) := by ring
        linarith [hmul, heq, hle2, heq2]
      linarith [hBadU_le, ha_le]
    nlinarith [hcard_le, hBad_le]
  refine ⟨pool, t, hpool_sub, ⟨X0, hX0⟩, hclose, ?_, ?_⟩
  · simpa [cfgN, hU_def] using hsqrt_mass
  · simpa [hU_def] using hdens

set_option maxHeartbeats 5000000 in
/-- `profiles.tex:576–595`: inner-window selection from the finite
profile grid, dyadic residue gaps, bin selection and an orientation. -/
theorem pair_selection_inner_pieces (d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ a > 0, ∀ (P : Finset (Pt d)) (pl : Finset (Piece d))
      (R : Pt d → Pt d → Prop),
      0 < cfgN P →
      (∀ X ∈ pl, X.pts ⊆ P) → (pl : Set (Piece d)).PairwiseDisjoint Piece.pts →
      (∀ X ∈ pl, ∀ i, -1 ≤ X.path.time i ∧ X.path.time i ≤ 2) →
      (∀ X ∈ pl, 0 < X.width ∧ X.width < Real.log (cfgB P) ∧
        ∃ i : ℕ, X.width = Real.log (cfgB P) / 2 ^ i) →
      cfgN P / 4 ≤ (poolPts pl).card →
      (((P ×ˢ P).filter (fun pq => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ) ≤
        a * cfgN P ^ 2 →
      ∃ X ∈ pl, ∃ Y ∈ pl, ∃ t : Fin d → ℝ,
        (∀ i, |X.path.time i - t i| ≤ ρ ∧ |Y.path.time i - t i| ≤ ρ) ∧
        ((X.width = Y.width ∧ X.width < Real.log (cfgB P)) ∨
          ((X.width ≤ ρ * Y.width ∨ Y.width ≤ ρ * X.width) ∧
            X.width ≤ ρ * Real.log (cfgB P) ∧ Y.width ≤ ρ * Real.log (cfgB P))) ∧
        (1 / 2 - ρ) * X.pts.card * Y.pts.card ≤
          (((X.pts ×ˢ Y.pts).filter (fun pq => R pq.1 pq.2)).card : ℝ) := by
  classical
  -- mesh and grid/residue data (depend only on d, ρ)
  set μ : ℝ := min (ρ / 2) (1 / 4) with hμ_def
  have hμpos : 0 < μ := lt_min (by linarith) (by norm_num)
  have hμρ : μ ≤ ρ := by
    have h : μ ≤ ρ / 2 := min_le_left _ _
    linarith
  have hμ14 : μ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨K, hK, label, hlabel⟩ := pair_selection_profile_grid d μ hμpos
  obtain ⟨M, hM, hgap⟩ := pair_selection_residue_gap μ hμpos
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  -- global threshold (depends only on K, M, ρ)
  set KM : ℝ := (K : ℝ) * (M : ℝ) with hKM_def
  have hKMpos : 0 < KM := by positivity
  refine ⟨ρ / (16 * KM ^ 2), by positivity, ?_⟩
  intro P pl R hN hsub hdisj htime hwidth hmass hbad
  simp only [cfgN] at hN hmass ⊢
  -- contradictory small cases: d = 0 or N ≤ 1 gives empty widths
  by_cases hd0 : d = 0
  · subst hd0
    have hlog0 : Real.log (cfgB P) = 0 := by
      simp only [cfgB, Nat.cast_zero, div_zero, Real.rpow_zero, Real.log_one]
    have hpl_empty : pl = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro X hX
      obtain ⟨h0, hlt, _⟩ := hwidth X hX
      rw [hlog0] at hlt
      linarith
    simp [hpl_empty, poolPts] at hmass
    have hPpos : (0 : ℝ) < (P.card : ℝ) := hN
    linarith
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    by_cases hN1 : P.card ≤ 1
    · have hcardPos : 0 < P.card := Nat.cast_pos.mp hN
      have hcard1 : P.card = 1 := by omega
      have hlog0 : Real.log (cfgB P) = 0 := by
        have hB1 : cfgB P = 1 := by
          simp only [cfgB, hcard1, Nat.cast_one, Real.one_rpow]
        rw [hB1, Real.log_one]
      have hpl_empty : pl = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro X hX
        obtain ⟨h0, hlt, _⟩ := hwidth X hX
        rw [hlog0] at hlt
        linarith
      simp [hpl_empty, poolPts] at hmass
      have hPpos : (0 : ℝ) < (P.card : ℝ) := hN
      linarith
    · have hN2 : 2 ≤ P.card := by omega
      have hNr : (1 : ℝ) < (P.card : ℝ) := by
        have h2 : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hN2
        linarith
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      have hexpPos : (0 : ℝ) < (1 : ℝ) / (d : ℝ) := by positivity
      have hB1 : (1 : ℝ) < cfgB P := by
        simp only [cfgB]
        exact Real.one_lt_rpow hNr hexpPos
      have hlogPos : 0 < Real.log (cfgB P) := Real.log_pos hB1
      -- extended profiles: times plus normalized width
      let w : Piece d → ℝ := fun X => X.width / Real.log (cfgB P)
      let v : Piece d → (Fin (d + 1) → ℝ) := fun X j =>
        if h : j.val < d then X.path.time ⟨j.val, h⟩ else w X
      have hv_mem : ∀ X ∈ pl, ∀ j, -1 ≤ v X j ∧ v X j ≤ 2 := by
        intro X hX j
        dsimp [v]
        by_cases hj : j.val < d
        · rw [dif_pos hj]
          exact htime X hX ⟨j.val, hj⟩
        · rw [dif_neg hj]
          have hw0 : 0 < w X := by
            dsimp [w]
            obtain ⟨h0, _, _⟩ := hwidth X hX
            exact div_pos h0 hlogPos
          have hw1 : w X < 1 := by
            dsimp [w]
            obtain ⟨_, hlt, _⟩ := hwidth X hX
            rw [div_lt_one hlogPos]
            exact hlt
          constructor <;> linarith
      -- dyadic indices via choice
      have hIdxEx : ∀ X : Piece d, ∃ i : ℕ,
          X ∈ pl → X.width = Real.log (cfgB P) / 2 ^ i := by
        intro X
        by_cases hX : X ∈ pl
        · obtain ⟨_, _, i, hi⟩ := hwidth X hX
          exact ⟨i, fun _ => hi⟩
        · exact ⟨0, fun h => absurd h hX⟩
      choose idx hidx using hIdxEx
      let binP : Piece d → (Fin K × Fin M) := fun X =>
        (label (v X), ⟨idx X % M, Nat.mod_lt _ hM⟩)
      -- mass per bin
      let massB : (Fin K × Fin M) → ℝ := fun k =>
        ((poolPts (pl.filter (fun X => binP X = k))).card : ℝ)
      have hdisjB : ∀ k, ((pl.filter (fun X => binP X = k) :
          Finset (Piece d)) : Set (Piece d)).PairwiseDisjoint Piece.pts := by
        intro k X hX Y hY hXY
        have hXpl : X ∈ pl := (Finset.mem_filter.mp (Finset.mem_coe.mp hX)).1
        have hYpl : Y ∈ pl := (Finset.mem_filter.mp (Finset.mem_coe.mp hY)).1
        exact hdisj hXpl hYpl hXY
      have hcardB : ∀ k, ((poolPts (pl.filter
          (fun X => binP X = k))).card : ℝ)
          = ∑ X ∈ pl.filter (fun X => binP X = k), ((X.pts.card : ℝ)) := by
        intro k
        have h := Finset.card_biUnion (hdisjB k)
        simp only [poolPts] at h ⊢
        rw [h]
        push_cast
        rfl
      have htotalB : ((poolPts pl).card : ℝ)
          = ∑ k ∈ (Finset.univ : Finset (Fin K × Fin M)), massB k := by
        have hcardPl : ((poolPts pl).card : ℝ)
            = ∑ X ∈ pl, ((X.pts.card : ℝ)) := by
          have h := Finset.card_biUnion hdisj
          simp only [poolPts] at h ⊢
          rw [h]
          push_cast
          rfl
        rw [hcardPl]
        dsimp only [massB]
        simp only [hcardB]
        have hfib := Finset.sum_fiberwise_eq_sum_filter pl Finset.univ binP
          (fun X => ((X.pts.card : ℝ)))
        simpa [Finset.mem_univ] using hfib.symm
      have hUne : (Finset.univ : Finset (Fin K × Fin M)).Nonempty := by
        have h0K : (⟨0, hK⟩ : Fin K) ∈ (Finset.univ : Finset (Fin K)) :=
          Finset.mem_univ _
        have h0M : (⟨0, hM⟩ : Fin M) ∈ (Finset.univ : Finset (Fin M)) :=
          Finset.mem_univ _
        have h0 : ((⟨0, hK⟩, ⟨0, hM⟩) : Fin K × Fin M) ∈
            (Finset.univ : Finset (Fin K × Fin M)) := Finset.mem_univ _
        exact ⟨_, h0⟩
      have hImgNe : ((Finset.univ : Finset (Fin K × Fin M)).image massB).Nonempty :=
        Finset.image_nonempty.mpr hUne
      obtain ⟨k0, hk0mem, hk0eq⟩ :
          ∃ k0 ∈ (Finset.univ : Finset (Fin K × Fin M)),
            massB k0 = ((Finset.univ : Finset (Fin K × Fin M)).image massB).max'
              hImgNe := by
        have hmem := Finset.max'_mem _ hImgNe
        obtain ⟨k0, hk0, hk0eq⟩ := Finset.mem_image.mp hmem
        exact ⟨k0, hk0, hk0eq⟩
      have hk0max : ∀ k ∈ (Finset.univ : Finset (Fin K × Fin M)),
          massB k ≤ massB k0 := by
        intro k hk
        have hmem : massB k ∈
            (Finset.univ : Finset (Fin K × Fin M)).image massB :=
          Finset.mem_image.mpr ⟨k, hk, rfl⟩
        have hle := Finset.le_max' _ _ hmem
        rwa [← hk0eq] at hle
      have hcardKM : (Finset.univ : Finset (Fin K × Fin M)).card = K * M := by
        simp [Fintype.card_prod]
      have hsum_leB : ∑ k ∈ (Finset.univ : Finset (Fin K × Fin M)), massB k
          ≤ (((Finset.univ : Finset (Fin K × Fin M)).card : ℕ) : ℝ)
            * massB k0 := by
        calc ∑ k ∈ (Finset.univ : Finset (Fin K × Fin M)), massB k
            ≤ ∑ _k ∈ (Finset.univ : Finset (Fin K × Fin M)), massB k0 :=
              Finset.sum_le_sum (fun k hk => hk0max k hk)
          _ = (((Finset.univ : Finset (Fin K × Fin M)).card : ℕ) : ℝ)
              * massB k0 := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hmass0B : ((poolPts pl).card : ℝ) / ((K * M : ℕ) : ℝ) ≤ massB k0 := by
        have hKMc : ((K * M : ℕ) : ℝ) ≠ 0 := by
          have hK0 : (K : ℝ) ≠ 0 := ne_of_gt hKr
          have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMr
          simp [Nat.cast_mul, hK0, hM0]
        have h1 : ∑ k ∈ (Finset.univ : Finset (Fin K × Fin M)), massB k
            ≤ (((K * M : ℕ)) : ℝ) * massB k0 := by
          have hsum := hsum_leB
          rw [hcardKM] at hsum
          simpa using hsum
        have h2 : (∑ k ∈ (Finset.univ : Finset (Fin K × Fin M)), massB k)
            / (((K * M : ℕ)) : ℝ)
            ≤ ((((K * M : ℕ)) : ℝ) * massB k0) / (((K * M : ℕ)) : ℝ) :=
          div_le_div_of_nonneg_right h1 (by positivity)
        rw [mul_div_cancel_left₀ _ hKMc] at h2
        rwa [htotalB]
      set grp : Finset (Piece d) :=
        pl.filter (fun X => binP X = k0) with hgrp_def
      have hgrp_sub : grp ⊆ pl := Finset.filter_subset _ _
      have hmass_grp : massB k0 = ((poolPts grp).card : ℝ) := rfl
      -- any two in grp share label and residue
      have hgrp_bin : ∀ X ∈ grp, binP X = k0 :=
        fun X hX => (Finset.mem_filter.mp hX).2
      have hgrp_label : ∀ X ∈ grp, ∀ Y ∈ grp, label (v X) = label (v Y) := by
        intro X hX Y hY
        have hx := hgrp_bin X hX
        have hy := hgrp_bin Y hY
        dsimp [binP] at hx hy
        have : (label (v X), (⟨idx X % M, Nat.mod_lt _ hM⟩ : Fin M))
            = (label (v Y), (⟨idx Y % M, Nat.mod_lt _ hM⟩ : Fin M)) := by
          rw [hx, hy]
        exact congrArg Prod.fst this
      have hgrp_res : ∀ X ∈ grp, ∀ Y ∈ grp, idx X % M = idx Y % M := by
        intro X hX Y hY
        have hx := hgrp_bin X hX
        have hy := hgrp_bin Y hY
        dsimp [binP] at hx hy
        have h : (label (v X), (⟨idx X % M, Nat.mod_lt _ hM⟩ : Fin M))
            = (label (v Y), (⟨idx Y % M, Nat.mod_lt _ hM⟩ : Fin M)) := by
          rw [hx, hy]
        have h2 := congrArg Prod.snd h
        simpa [Fin.mk.injEq] using h2
      -- times and normalized widths close within μ
      have hgrp_close : ∀ X ∈ grp, ∀ Y ∈ grp, ∀ i : Fin d,
          |X.path.time i - Y.path.time i| ≤ μ := by
        intro X hX Y hY i
        have hXpl : X ∈ pl := hgrp_sub hX
        have hYpl : Y ∈ pl := hgrp_sub hY
        have hvX := hv_mem X hXpl
        have hvY := hv_mem Y hYpl
        have hlab := hgrp_label X hX Y hY
        have hgrid := hlabel (v X) (v Y) hvX hvY hlab
        let j : Fin (d + 1) := Fin.castSucc i
        have hji : j.val = i.val := rfl
        have hlt : j.val < d := by
          rw [hji]
          exact i.isLt
        have hXeq : v X j = X.path.time i := by
          have hEq : (⟨(j.val), hlt⟩ : Fin d) = i := Fin.ext hji
          simp only [v, dif_pos hlt, hEq]
        have hYeq : v Y j = Y.path.time i := by
          have hEq : (⟨(j.val), hlt⟩ : Fin d) = i := Fin.ext hji
          simp only [v, dif_pos hlt, hEq]
        have hji_le := hgrid j
        rwa [hXeq, hYeq] at hji_le
      have hgrp_wclose : ∀ X ∈ grp, ∀ Y ∈ grp,
          |w X - w Y| ≤ μ := by
        intro X hX Y hY
        have hXpl : X ∈ pl := hgrp_sub hX
        have hYpl : Y ∈ pl := hgrp_sub hY
        have hvX := hv_mem X hXpl
        have hvY := hv_mem Y hYpl
        have hlab := hgrp_label X hX Y hY
        have hgrid := hlabel (v X) (v Y) hvX hvY hlab
        let j : Fin (d + 1) := Fin.last d
        have hjv : j.val = d := Fin.val_last d
        have hjnlt : ¬ j.val < d := by
          rw [hjv]
          exact lt_irrefl d
        have hXeq : v X j = w X := by
          simp only [v, dif_neg hjnlt]
        have hYeq : v Y j = w Y := by
          simp only [v, dif_neg hjnlt]
        have hji_le := hgrid j
        rwa [hXeq, hYeq] at hji_le
      -- window alternative for any pair in grp
      have hgrp_window : ∀ X ∈ grp, ∀ Y ∈ grp,
          (X.width = Y.width ∧ X.width < Real.log (cfgB P)) ∨
          ((X.width ≤ ρ * Y.width ∨ Y.width ≤ ρ * X.width) ∧
            X.width ≤ ρ * Real.log (cfgB P) ∧
            Y.width ≤ ρ * Real.log (cfgB P)) := by
        intro X hX Y hY
        have hXpl : X ∈ pl := hgrp_sub hX
        have hYpl : Y ∈ pl := hgrp_sub hY
        have hXw := hidx X hXpl
        have hYw := hidx Y hYpl
        have hXlt := (hwidth X hXpl).2.1
        have hres := hgrp_res X hX Y hY
        by_cases hij : idx X = idx Y
        · left
          rw [hij] at hXw
          -- widths equal via same index
          have hEq : X.width = Y.width := by
            rw [hXw, hYw]
          exact ⟨hEq, hXlt⟩
        · right
          have hgap := hgap (Real.log (cfgB P)) hlogPos (idx X) (idx Y)
            hij hres
          -- hgap : logB/2^i ≤ μ*(logB/2^j) ∨ ...
          have hXeq : X.width = Real.log (cfgB P) / 2 ^ idx X := hXw
          have hYeq : Y.width = Real.log (cfgB P) / 2 ^ idx Y := hYw
          rw [← hXeq, ← hYeq] at hgap
          -- normalized closeness gives separated_small hypothesis
          have hwclose := hgrp_wclose X hX Y hY
          have hwdiv : |X.width / Real.log (cfgB P)
              - Y.width / Real.log (cfgB P)| ≤ μ := by
            simp only [w] at hwclose
            exact hwclose
          set r : ℝ := 2 * μ with hr_def
          have hrρ : r ≤ ρ := by
            simp only [hr_def]
            have h : μ ≤ ρ / 2 := min_le_left _ _
            linarith
          have hr12 : r ≤ 1 / 2 := by
            simp only [hr_def]
            have h : μ ≤ 1 / 4 := min_le_right _ _
            linarith
          have hratio : X.width ≤ r * Y.width ∨ Y.width ≤ r * X.width := by
            rcases hgap with h1 | h1
            · left
              have hμr : μ ≤ r := by
                simp only [hr_def]
                linarith [hμpos]
              have hYnn : 0 ≤ Y.width := (hwidth Y hYpl).1.le
              calc X.width ≤ μ * Y.width := h1
                _ ≤ r * Y.width :=
                  mul_le_mul_of_nonneg_right hμr hYnn
            · right
              have hμr : μ ≤ r := by
                simp only [hr_def]
                linarith [hμpos]
              have hXnn : 0 ≤ X.width := (hwidth X hXpl).1.le
              calc Y.width ≤ μ * X.width := h1
                _ ≤ r * X.width :=
                  mul_le_mul_of_nonneg_right hμr hXnn
          have hclose2 : |X.width / Real.log (cfgB P)
              - Y.width / Real.log (cfgB P)| ≤ r / 2 := by
            simp only [hr_def]
            linarith [hwdiv, hμpos]
          have hsmall : X.width ≤ r * Real.log (cfgB P) ∧
              Y.width ≤ r * Real.log (cfgB P) := by
            rcases hratio with h1 | h1
            · exact pair_selection_separated_small
                (Real.log (cfgB P)) X.width Y.width r hlogPos
                (hwidth X hXpl).1.le (hwidth Y hYpl).1.le
                (by linarith [hμpos, hr12] : 0 < r)
                hr12 h1 hclose2
            · have hclose2' : |Y.width / Real.log (cfgB P)
                  - X.width / Real.log (cfgB P)| ≤ r / 2 := by
                simpa [abs_sub_comm] using hclose2
              have h := pair_selection_separated_small
                (Real.log (cfgB P)) Y.width X.width r hlogPos
                (hwidth Y hYpl).1.le (hwidth X hXpl).1.le
                (by linarith [hμpos, hr12] : 0 < r)
                hr12 h1 hclose2'
              exact ⟨h.2, h.1⟩
          obtain ⟨hs, ht⟩ := hsmall
          have hsρ : X.width ≤ ρ * Real.log (cfgB P) := by
            have hle : r * Real.log (cfgB P) ≤ ρ * Real.log (cfgB P) :=
              mul_le_mul_of_nonneg_right hrρ hlogPos.le
            linarith [hs, hle]
          have htρ : Y.width ≤ ρ * Real.log (cfgB P) := by
            have hle : r * Real.log (cfgB P) ≤ ρ * Real.log (cfgB P) :=
              mul_le_mul_of_nonneg_right hrρ hlogPos.le
            linarith [ht, hle]
          -- ratio in terms of ρ (since r ≤ ρ)
          have hratioρ : X.width ≤ ρ * Y.width ∨ Y.width ≤ ρ * X.width := by
            rcases hratio with h1 | h1
            · left
              have hYnn : 0 ≤ Y.width := (hwidth Y hYpl).1.le
              have hle : r * Y.width ≤ ρ * Y.width :=
                mul_le_mul_of_nonneg_right hrρ hYnn
              linarith
            · right
              have hXnn : 0 ≤ X.width := (hwidth X hXpl).1.le
              have hle : r * X.width ≤ ρ * X.width :=
                mul_le_mul_of_nonneg_right hrρ hXnn
              linarith
          exact ⟨hratioρ, hsρ, htρ⟩
      -- mass of max group
      have hGrpMass : (P.card : ℝ) / (4 * (((K * M : ℕ)) : ℝ))
          ≤ ((poolPts grp).card : ℝ) := by
        have htot : (P.card : ℝ) / 4 ≤ ((poolPts pl).card : ℝ) := hmass
        have hle : ((poolPts pl).card : ℝ) / (((K * M : ℕ)) : ℝ)
            ≤ ((poolPts grp).card : ℝ) := by
          have hmass0B' : ((poolPts pl).card : ℝ) / (((K * M : ℕ)) : ℝ)
              ≤ massB k0 := hmass0B
          rwa [hmass_grp] at hmass0B'
        have hKMposN : (0 : ℝ) < (((K * M : ℕ)) : ℝ) := by
          have hK0 : (0 : ℝ) < (K : ℝ) := hKr
          have hM0 : (0 : ℝ) < (M : ℝ) := hMr
          have : (((K * M : ℕ)) : ℝ) = (K : ℝ) * (M : ℝ) := by
            simp [Nat.cast_mul]
          rw [this]
          positivity
        have h4KM : (0 : ℝ) < 4 * (((K * M : ℕ)) : ℝ) := by positivity
        rw [div_le_iff₀ hKMposN] at hle
        rw [div_le_iff₀ h4KM]
        nlinarith [htot, hle, htot]
      have hgrp_ne : grp.Nonempty := by
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty] at hcon
        have hempty : poolPts grp = ∅ := by
          simp [poolPts, hcon]
        have hzero : ((poolPts grp).card : ℝ) = 0 := by
          simp [hempty]
        have hPpos : (0 : ℝ) < (P.card : ℝ) := hN
        have hKMposN : (0 : ℝ) < 4 * (((K * M : ℕ)) : ℝ) := by
          have hK0 : (0 : ℝ) < (K : ℝ) := hKr
          have hM0 : (0 : ℝ) < (M : ℝ) := hMr
          have : (((K * M : ℕ)) : ℝ) = (K : ℝ) * (M : ℝ) := by
            simp [Nat.cast_mul]
          rw [this]
          positivity
        have hpos : (0 : ℝ) < (P.card : ℝ) / (4 * (((K * M : ℕ)) : ℝ)) :=
          div_pos hPpos hKMposN
        linarith [hGrpMass, hzero, hpos]
      -- bad sum over piece pairs in grp
      set Ugrp : Finset (Pt d) := poolPts grp with hUgrp_def
      have hUgrp_sub : Ugrp ⊆ P := by
        intro x hx
        simp only [hUgrp_def, poolPts, Finset.mem_biUnion] at hx
        obtain ⟨X, hX, hxX⟩ := hx
        exact hsub X (hgrp_sub hX) hxX
      -- disjointness of products X×Y across pairs
      have hGrpDisj : ((grp : Finset (Piece d)) : Set (Piece d)).PairwiseDisjoint
          Piece.pts := by
        intro X hX Y hY hXY
        have hXpl : X ∈ pl := hgrp_sub (Finset.mem_coe.mp hX)
        have hYpl : Y ∈ pl := hgrp_sub (Finset.mem_coe.mp hY)
        exact hdisj hXpl hYpl hXY
      have hProdDisj : ((grp ×ˢ grp : Finset (Piece d × Piece d)) :
          Set (Piece d × Piece d)).PairwiseDisjoint
          (fun p => p.1.pts ×ˢ p.2.pts) := by
        intro p hp q hq hne
        have hpF : p ∈ grp ×ˢ grp :=
          Finset.mem_coe.mp hp
        have hqF : q ∈ grp ×ˢ grp :=
          Finset.mem_coe.mp hq
        obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpF
        obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqF
        have hp1S : p.1 ∈ (grp : Set (Piece d)) := Finset.mem_coe.mpr hp1
        have hp2S : p.2 ∈ (grp : Set (Piece d)) := Finset.mem_coe.mpr hp2
        have hq1S : q.1 ∈ (grp : Set (Piece d)) := Finset.mem_coe.mpr hq1
        have hq2S : q.2 ∈ (grp : Set (Piece d)) := Finset.mem_coe.mpr hq2
        by_cases hX : p.1 = q.1
        · have hY : p.2 ≠ q.2 := by
            intro heq
            apply hne
            exact Prod.ext hX heq
          have hDisjY := hGrpDisj hp2S hq2S hY
          apply Finset.disjoint_left.mpr
          intro pq h1 h2
          rcases Finset.mem_product.mp h1 with ⟨_, hm2⟩
          rcases Finset.mem_product.mp h2 with ⟨_, hm2'⟩
          exact Finset.disjoint_left.mp hDisjY hm2 hm2'
        · have hDisjX := hGrpDisj hp1S hq1S hX
          apply Finset.disjoint_left.mpr
          intro pq h1 h2
          rcases Finset.mem_product.mp h1 with ⟨hm1, _⟩
          rcases Finset.mem_product.mp h2 with ⟨hm1', _⟩
          exact Finset.disjoint_left.mp hDisjX hm1 hm1'
      -- bad pieces partition bad in Ugrp
      have hBadEq : ((Ugrp ×ˢ Ugrp).filter
          (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1))
          = (grp ×ˢ grp).biUnion
            (fun p : Piece d × Piece d =>
              ((p.1.pts ×ˢ p.2.pts).filter
                (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1))) := by
        ext pq
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
          hUgrp_def, poolPts, Finset.mem_biUnion]
        constructor
        · rintro ⟨⟨⟨X, hX, hxX⟩, ⟨Y, hY, hxY⟩⟩, hR⟩
          exact ⟨(X, Y), ⟨hX, hY⟩, ⟨⟨hxX, hxY⟩, hR⟩⟩
        · rintro ⟨⟨X, Y⟩, ⟨hX, hY⟩, ⟨⟨hxX, hxY⟩, hR⟩⟩
          exact ⟨⟨⟨X, hX, hxX⟩, ⟨Y, hY, hxY⟩⟩, hR⟩
      have hBadDisj : (((grp ×ˢ grp : Finset (Piece d × Piece d))) :
          Set (Piece d × Piece d)).PairwiseDisjoint
          (fun p => ((p.1.pts ×ˢ p.2.pts).filter
            (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1))) := by
        intro p hp q hq hne
        have hdisj := hProdDisj hp hq hne
        exact hdisj.mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hBadSum : ((((Ugrp ×ˢ Ugrp).filter
          (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ))
          = ∑ p ∈ grp ×ˢ grp, ((((p.1.pts ×ˢ p.2.pts).filter
            (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) := by
        rw [hBadEq, Finset.card_biUnion hBadDisj]
        push_cast
        rfl
      have hBadGrp_le : ((((Ugrp ×ˢ Ugrp).filter
          (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ))
          ≤ ρ / (16 * KM ^ 2) * (P.card : ℝ) ^ 2 := by
        have hSub : ((Ugrp ×ˢ Ugrp).filter
            (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1))
            ⊆ ((P ×ˢ P).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)) := by
          intro pq h
          simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
          obtain ⟨⟨hu1, hu2⟩, hR⟩ := h
          exact ⟨⟨hUgrp_sub hu1, hUgrp_sub hu2⟩, hR⟩
        calc ((((Ugrp ×ˢ Ugrp).filter _).card : ℝ))
            ≤ ((((P ×ˢ P).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) := by
              exact_mod_cast Finset.card_le_card hSub
          _ ≤ ρ / (16 * KM ^ 2) * (P.card : ℝ) ^ 2 := by
              simpa [cfgN] using hbad
      have hMassSq : (((poolPts grp).card : ℝ)) ^ 2
          = ∑ p ∈ grp ×ˢ grp,
            ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ)) := by
        have hcard : ((poolPts grp).card : ℝ)
            = ∑ X ∈ grp, ((X.pts.card : ℝ)) := by
          have h := Finset.card_biUnion hGrpDisj
          simp only [poolPts] at h ⊢
          rw [h]
          push_cast
          rfl
        calc (((poolPts grp).card : ℝ)) ^ 2
            = (∑ X ∈ grp, ((X.pts.card : ℝ)))
              * (∑ Y ∈ grp, ((Y.pts.card : ℝ))) := by
              rw [← hcard]; ring
          _ = ∑ X ∈ grp, ∑ Y ∈ grp,
              ((X.pts.card : ℝ)) * ((Y.pts.card : ℝ)) := by
              rw [Finset.sum_mul_sum]
          _ = ∑ p ∈ grp ×ˢ grp,
              ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ)) := by
              rw [Finset.sum_product]
      have hPairsNe : (grp ×ˢ grp : Finset (Piece d × Piece d)).Nonempty := by
        obtain ⟨X0, hX0⟩ := hgrp_ne
        exact ⟨(X0, X0), Finset.mem_product.mpr ⟨hX0, hX0⟩⟩
      obtain ⟨p0, hp0mem, hp0le⟩ :
          ∃ p ∈ grp ×ˢ grp,
            ((((p.1.pts ×ˢ p.2.pts).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ))
            ≤ 2 * ρ * ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ)) := by
        by_contra hcon
        push Not at hcon
        have hgt : ∀ p ∈ grp ×ˢ grp,
            2 * ρ * ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ))
            < ((((p.1.pts ×ˢ p.2.pts).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) := by
          intro p hp
          exact hcon p hp
        have hle_all : ∀ p ∈ grp ×ˢ grp,
            2 * ρ * ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ))
            ≤ ((((p.1.pts ×ˢ p.2.pts).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) := by
          intro p hp
          exact le_of_lt (hgt p hp)
        obtain ⟨pW, hpW⟩ := hPairsNe
        have hex : ∃ p ∈ grp ×ˢ grp,
            2 * ρ * ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ))
            < ((((p.1.pts ×ˢ p.2.pts).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) :=
          ⟨pW, hpW, hgt pW hpW⟩
        have hsum_gt : ∑ p ∈ grp ×ˢ grp,
            2 * ρ * ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ))
            < ∑ p ∈ grp ×ˢ grp, ((((p.1.pts ×ˢ p.2.pts).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) :=
          Finset.sum_lt_sum hle_all hex
        have hsum_eq : ∑ p ∈ grp ×ˢ grp,
            2 * ρ * ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ))
            = 2 * ρ * (((poolPts grp).card : ℝ)) ^ 2 := by
          have h1 : ∑ p ∈ grp ×ˢ grp,
              2 * ρ * ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ))
              = (2 * ρ) * ∑ p ∈ grp ×ˢ grp,
                ((p.1.pts.card : ℝ)) * ((p.2.pts.card : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            ring
          rw [h1, ← hMassSq]
        have hle : ∑ p ∈ grp ×ˢ grp, ((((p.1.pts ×ˢ p.2.pts).filter
            (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ))
            ≤ ρ / (16 * KM ^ 2) * (P.card : ℝ) ^ 2 := by
          rw [← hBadSum]
          exact hBadGrp_le
        have ha_contra : ρ / (16 * KM ^ 2) * (P.card : ℝ) ^ 2
            < 2 * ρ * (((poolPts grp).card : ℝ)) ^ 2 := by
          have hMassPos : 0 < ((poolPts grp).card : ℝ) := by
            have hPpos : (0 : ℝ) < (P.card : ℝ) := hN
            have hKMposN : (0 : ℝ) < 4 * (((K * M : ℕ)) : ℝ) := by
              have hK0 : (0 : ℝ) < (K : ℝ) := hKr
              have hM0 : (0 : ℝ) < (M : ℝ) := hMr
              have : (((K * M : ℕ)) : ℝ) = (K : ℝ) * (M : ℝ) := by
                simp [Nat.cast_mul]
              rw [this]
              positivity
            have hpos : (0 : ℝ) < (P.card : ℝ) / (4 * (((K * M : ℕ)) : ℝ)) :=
              div_pos hPpos hKMposN
            linarith [hGrpMass, hpos]
          have hSqPos : 0 < (((poolPts grp).card : ℝ)) ^ 2 :=
            sq_pos_of_pos hMassPos
          have hNp2 : ((P.card : ℝ) / (4 * (((K * M : ℕ)) : ℝ))) ^ 2
              ≤ (((poolPts grp).card : ℝ)) ^ 2 := by
            apply sq_le_sq.mpr
            rw [abs_of_nonneg (by positivity)]
            rw [abs_of_nonneg (Nat.cast_nonneg _)]
            exact hGrpMass
          have hKM_eq : (((K * M : ℕ)) : ℝ) = KM := by
            rw [Nat.cast_mul, ← hKM_def]
          have hKMeq : (4 * (((K * M : ℕ)) : ℝ)) ^ 2 = 16 * KM ^ 2 := by
            rw [hKM_eq]
            ring
          have hdiv : (P.card : ℝ) ^ 2 / (16 * KM ^ 2)
              ≤ (((poolPts grp).card : ℝ)) ^ 2 := by
            have : ((P.card : ℝ) / (4 * (((K * M : ℕ)) : ℝ))) ^ 2
                = (P.card : ℝ) ^ 2 / (16 * KM ^ 2) := by
              rw [hKM_eq]
              field_simp
              ring
            linarith [hNp2, this]
          have hmul : ρ / (16 * KM ^ 2) * (P.card : ℝ) ^ 2
              = ρ * ((P.card : ℝ) ^ 2 / (16 * KM ^ 2)) := by ring
          have hle2 : ρ * ((P.card : ℝ) ^ 2 / (16 * KM ^ 2))
              ≤ ρ * (((poolPts grp).card : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hdiv hρ.le
          have heq2 : 2 * ρ * (((poolPts grp).card : ℝ)) ^ 2
              = 2 * (ρ * (((poolPts grp).card : ℝ)) ^ 2) := by ring
          have hpos2 : 0 < ρ * (((poolPts grp).card : ℝ)) ^ 2 :=
            mul_pos hρ hSqPos
          linarith [hmul, hle2, heq2, hpos2]
        linarith [hsum_gt, hsum_eq, hle, ha_contra]
      -- extract pieces X0 Y0 from p0
      obtain ⟨X0, Y0⟩ := p0
      have hp0XY : X0 ∈ grp ∧ Y0 ∈ grp := Finset.mem_product.mp hp0mem
      obtain ⟨hX0grp, hY0grp⟩ := hp0XY
      have hX0pl : X0 ∈ pl := hgrp_sub hX0grp
      have hY0pl : Y0 ∈ pl := hgrp_sub hY0grp
      have hBad0 := hp0le
      simp only at hBad0
      -- window and closeness for this pair (from grp)
      have hclose0 : ∀ i, |X0.path.time i - X0.path.time i| ≤ ρ ∧
          |Y0.path.time i - X0.path.time i| ≤ ρ := by
        intro i
        have hXYclose := hgrp_close X0 hX0grp Y0 hY0grp i
        constructor
        · simp [hρ.le]
        · calc |Y0.path.time i - X0.path.time i|
              = |X0.path.time i - Y0.path.time i| := abs_sub_comm _ _
            _ ≤ μ := hXYclose
            _ ≤ ρ := hμρ
      have hwin0 := hgrp_window X0 hX0grp Y0 hY0grp
      -- orientation: forward or swapped gives density
      have hProdXY : (X0.pts ×ˢ Y0.pts).card
          = X0.pts.card * Y0.pts.card := Finset.card_product _ _
      have hCoverXY : X0.pts ×ˢ Y0.pts ⊆
          ((X0.pts ×ˢ Y0.pts).filter (fun pq : Pt d × Pt d => R pq.1 pq.2)) ∪
          ((X0.pts ×ˢ Y0.pts).filter
            (fun pq : Pt d × Pt d => R pq.2 pq.1)) ∪
          ((X0.pts ×ˢ Y0.pts).filter
            (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)) := by
        intro pq h
        simp only [Finset.mem_product, Finset.mem_filter,
          Finset.mem_union] at h ⊢
        obtain ⟨hx, hy⟩ := h
        by_cases hR : R pq.1 pq.2 ∨ R pq.2 pq.1
        · rcases hR with hR1 | hR2
          · exact Or.inl (Or.inl ⟨⟨hx, hy⟩, hR1⟩)
          · exact Or.inl (Or.inr ⟨⟨hx, hy⟩, hR2⟩)
        · have hn1 : ¬ R pq.1 pq.2 := fun h => hR (Or.inl h)
          have hn2 : ¬ R pq.2 pq.1 := fun h => hR (Or.inr h)
          exact Or.inr ⟨⟨hx, hy⟩, hn1, hn2⟩
      have hSwapXY : Function.Injective
          (Prod.swap : Pt d × Pt d → Pt d × Pt d) := by
        intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
        simp only [Prod.swap, Prod.mk.injEq] at h ⊢
        obtain ⟨h2, h1⟩ := h
        exact ⟨h1, h2⟩
      have hBackEq : (((X0.pts ×ˢ Y0.pts).filter
          (fun pq : Pt d × Pt d => R pq.2 pq.1)).card : ℕ)
          = (((Y0.pts ×ˢ X0.pts).filter
            (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℕ) := by
        have heq : ((X0.pts ×ˢ Y0.pts).filter
            (fun pq : Pt d × Pt d => R pq.2 pq.1))
            = (((Y0.pts ×ˢ X0.pts).filter
              (fun pq : Pt d × Pt d => R pq.1 pq.2)).image Prod.swap) := by
          ext ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          constructor
          · rintro ⟨⟨ha, hb⟩, hR⟩
            exact ⟨(b, a), ⟨⟨hb, ha⟩, hR⟩, rfl⟩
          · rintro ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, hR⟩, hEq⟩
            simp only [Prod.swap, Prod.mk.injEq] at hEq
            obtain ⟨h1, h2⟩ := hEq
            subst h1
            subst h2
            exact ⟨⟨hd, hc⟩, hR⟩
        rw [heq, Finset.card_image_of_injective _ hSwapXY]
      have hcard_leXY : ((X0.pts.card : ℝ)) * ((Y0.pts.card : ℝ))
          ≤ ((((X0.pts ×ˢ Y0.pts).filter
            (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ))
          + ((((Y0.pts ×ˢ X0.pts).filter
            (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ))
          + ((((X0.pts ×ˢ Y0.pts).filter
            (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) := by
        have hNat : (X0.pts ×ˢ Y0.pts).card ≤
            (((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => R pq.1 pq.2)).card)
            + (((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => R pq.2 pq.1)).card)
            + (((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card) := by
          have h1 := Finset.card_union_le
            (((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => R pq.1 pq.2)) ∪
              ((X0.pts ×ˢ Y0.pts).filter
                (fun pq : Pt d × Pt d => R pq.2 pq.1)))
            (((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)))
          have h2 := Finset.card_union_le
            (((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => R pq.1 pq.2)))
            (((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => R pq.2 pq.1)))
          have h3 := Finset.card_le_card hCoverXY
          rw [hProdXY] at h3 ⊢
          omega
        have hcast : (((X0.pts.card : ℝ)) * ((Y0.pts.card : ℝ)))
            = ((((X0.pts ×ˢ Y0.pts).card : ℕ)) : ℝ) := by
          rw [hProdXY]
          push_cast
          ring
        have hNatR : ((((X0.pts ×ˢ Y0.pts).card : ℕ)) : ℝ)
            ≤ ((((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ))
            + ((((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => R pq.2 pq.1)).card : ℝ))
            + ((((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ)) := by
          exact_mod_cast hNat
        rw [← hcast] at hNatR
        have hBeq : ((((X0.pts ×ˢ Y0.pts).filter
            (fun pq : Pt d × Pt d => R pq.2 pq.1)).card : ℝ))
            = ((((Y0.pts ×ˢ X0.pts).filter
              (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ)) := by
          exact_mod_cast hBackEq
        linarith [hNatR, hBeq]
      -- select orientation
      by_cases hFwd : (1 / 2 - ρ) * ((X0.pts.card : ℝ)) * ((Y0.pts.card : ℝ))
          ≤ ((((X0.pts ×ˢ Y0.pts).filter
            (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ))
      · exact ⟨X0, hX0pl, Y0, hY0pl, X0.path.time,
          (fun i => ⟨by simp [hρ.le], by
            have h := (hclose0 i).2
            simpa using h⟩),
          hwin0, by simpa using hFwd⟩
      · have hBwd : (1 / 2 - ρ) * ((Y0.pts.card : ℝ)) * ((X0.pts.card : ℝ))
          ≤ ((((Y0.pts ×ˢ X0.pts).filter
            (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ)) := by
          have hBad : ((((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ))
              ≤ 2 * ρ * ((X0.pts.card : ℝ)) * ((Y0.pts.card : ℝ)) := hp0le
          have hlt : ((((X0.pts ×ˢ Y0.pts).filter
              (fun pq : Pt d × Pt d => R pq.1 pq.2)).card : ℝ))
              < (1 / 2 - ρ) * ((X0.pts.card : ℝ)) * ((Y0.pts.card : ℝ)) :=
            not_le.mp hFwd
          have heq : (1 / 2 - ρ) * ((Y0.pts.card : ℝ)) * ((X0.pts.card : ℝ))
              = (1 / 2 - ρ) * ((X0.pts.card : ℝ)) * ((Y0.pts.card : ℝ)) := by
            ring
          rw [heq]
          linarith [hcard_leXY, hBad, hlt]
        have hwin_symm : ((Y0.width = X0.width ∧ Y0.width < Real.log (cfgB P)) ∨
            ((Y0.width ≤ ρ * X0.width ∨ X0.width ≤ ρ * Y0.width) ∧
              Y0.width ≤ ρ * Real.log (cfgB P) ∧
              X0.width ≤ ρ * Real.log (cfgB P))) := by
          rcases hwin0 with h | h
          · left
            obtain ⟨heq, hlt⟩ := h
            exact ⟨heq.symm, heq ▸ hlt⟩
          · right
            obtain ⟨hratio, hs, ht⟩ := h
            exact ⟨Or.comm.mp hratio, ht, hs⟩
        exact ⟨Y0, hY0pl, X0, hX0pl, X0.path.time,
          (fun i => ⟨(hclose0 i).2, (hclose0 i).1⟩),
          hwin_symm, hBwd⟩

end
end DistinctDistances.TrackD
