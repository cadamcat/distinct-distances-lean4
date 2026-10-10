import DistinctDistances.TrackA.Depth

/-! Finite incidence inputs for `sc:u-typical` (sparse-cones.tex:668–678).
The fixed carrier assignments may differ between plateau applications, while
the physical center and target sets are exactly the same. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d} {α : Type*} [Fintype α]

/-- Targets removed in a row by any application in the fixed finite batch. -/
def batchBadTargets {j : α → ℕ}
    (D : (a : α) → TrackA.SeparatedDepthData regime (j a))
    (targets : ℕ → Finset (Point d))
    (bad : α → ℕ → Finset (Point d × AffineVariety d)) (i : ℕ) (p : Point d) :
    Finset (Point d) :=
  (targets i).filter (fun q => ∃ a, (p, (D a).owner i q) ∈ bad a i)

/-- The union of all literal center-target incidence deletions in the batch. -/
def batchBadPairs {j : α → ℕ}
    (D : (a : α) → TrackA.SeparatedDepthData regime (j a))
    (centers targets : ℕ → Finset (Point d))
    (bad : α → ℕ → Finset (Point d × AffineVariety d)) (i : ℕ) :
    Finset (Point d × Point d) :=
  (centers i ×ˢ targets i).filter (fun pq =>
    ∃ a, (pq.1, (D a).owner i pq.2) ∈ bad a i)

/-- Count the deleted physical pairs using the assigned target fibers.
Overlaps between different plateau deletions only reduce the union count. -/
theorem batch_incidence_card_bound {j : α → ℕ}
    (D : (a : α) → TrackA.SeparatedDepthData regime (j a))
    (centers targets : ℕ → Finset (Point d))
    (bad : α → ℕ → Finset (Point d × AffineVariety d))
    (htargets : ∀ a i, (D a).targets i = targets i)
    (hbad : ∀ a i, bad a i ⊆ centers i ×ˢ (D a).carriers i) :
    ∀ i, ((batchBadPairs D centers targets bad i).card : ℝ) ≤
      ∑ a, ∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ) := by
  intro i
  let A : α → Finset (Point d × Point d) := fun a =>
    (centers i ×ˢ targets i).filter (fun pq => (pq.1, (D a).owner i pq.2) ∈ bad a i)
  have hsubUnion : batchBadPairs D centers targets bad i ⊆
      (Finset.univ : Finset α).biUnion A := by
    intro pq hpq
    rw [batchBadPairs, Finset.mem_filter] at hpq
    obtain ⟨hpqProd, a, ha⟩ := hpq
    rw [Finset.mem_biUnion]
    exact ⟨a, Finset.mem_univ a, Finset.mem_filter.mpr ⟨hpqProd, ha⟩⟩
  have hcardUnion : ((batchBadPairs D centers targets bad i).card : ℝ) ≤
      ∑ a, ((A a).card : ℝ) := by
    have h1 := Finset.card_le_card hsubUnion
    exact_mod_cast h1.trans Finset.card_biUnion_le
  have hA_le (a : α) : ((A a).card : ℝ) ≤ ∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ) := by
    let F : Point d × AffineVariety d → Finset (Point d × Point d) := fun u =>
      {u.1} ×ˢ ((targets i).filter (fun q => (D a).owner i q = u.2))
    have hsubF : A a ⊆ (bad a i).biUnion F := by
      intro pq hpq
      rw [Finset.mem_filter] at hpq
      obtain ⟨hpqProd, ha⟩ := hpq
      rw [Finset.mem_biUnion]
      refine ⟨(pq.1, (D a).owner i pq.2), ha, ?_⟩
      rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter]
      exact ⟨rfl, (Finset.mem_product.mp hpqProd).2, rfl⟩
    have hcardF : ((A a).card : ℝ) ≤ ∑ u ∈ bad a i, ((F u).card : ℝ) := by
      have h1 := Finset.card_le_card hsubF
      exact_mod_cast h1.trans Finset.card_biUnion_le
    have hFcard (u : Point d × AffineVariety d) :
        (F u).card = (D a).mass i u.2 := by
      dsimp [F]
      rw [Finset.card_product, Finset.card_singleton, one_mul]
      rw [← htargets a i]
      rfl
    have hsumEq : (∑ u ∈ bad a i, ((F u).card : ℝ)) =
        ∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [hFcard u]
    rw [← hsumEq]
    exact hcardF
  exact hcardUnion.trans (Finset.sum_le_sum fun a _ => hA_le a)

/-- A fixed finite batch of negligible weighted deletions is negligible on
the common literal product; source and target widths are never compared. -/
theorem batch_incidence_small {j : α → ℕ}
    (D : (a : α) → TrackA.SeparatedDepthData regime (j a))
    (centers targets : ℕ → Finset (Point d))
    (bad : α → ℕ → Finset (Point d × AffineVariety d))
    (hcenters : ∀ a i, (D a).centers i = centers i)
    (htargets : ∀ a i, (D a).targets i = targets i)
    (hbad : ∀ a i, bad a i ⊆ centers i ×ˢ (D a).carriers i)
    (hsmall : ∀ a, Framework.LittleO
      (fun i => (D a).incidenceMass i (bad a i)) (fun _ => 1)) :
    Framework.LittleO (fun i => ((batchBadPairs D centers targets bad i).card : ℝ))
      (fun i => (centers i).card * (targets i).card) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let m : ℝ := (Fintype.card α : ℝ) + 1
  have hmPos : 0 < m := by
    dsimp [m]
    positivity
  have hεm : 0 < ε / m := div_pos hε hmPos
  have hbound (a : α) : ∀ᶠ i in atTop,
      ‖(D a).incidenceMass i (bad a i)‖ ≤ (ε / m) * ‖(1 : ℝ)‖ :=
    (hsmall a).def hεm
  have hall : ∀ᶠ i in atTop, ∀ a ∈ (Finset.univ : Finset α),
      ‖(D a).incidenceMass i (bad a i)‖ ≤ (ε / m) * ‖(1 : ℝ)‖ :=
    Framework.eventually_finite (Finset.univ : Finset α) _ (fun a _ => hbound a)
  filter_upwards [hall] with i hi
  let N : ℝ := ((centers i).card : ℝ) * (targets i).card
  have hcardBound := batch_incidence_card_bound D centers targets bad htargets hbad i
  have hterm (a : α) : (∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ)) ≤ (ε / m) * N := by
    by_cases hN : N = 0
    · have hsumZero : (∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ)) = 0 := by
        dsimp [N] at hN
        rcases mul_eq_zero.mp hN with hc | ht
        · have hcen : (centers i).card = 0 := by exact_mod_cast hc
          have hcenEmpty : centers i = ∅ := Finset.card_eq_zero.mp hcen
          have hbadEmpty : bad a i = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro u hu
            have hsub := hbad a i hu
            rw [Finset.mem_product] at hsub
            rw [hcenEmpty] at hsub
            cases hsub.1
          rw [hbadEmpty, Finset.sum_empty]
        · have htgt : (targets i).card = 0 := by exact_mod_cast ht
          have htgtEmpty : targets i = ∅ := Finset.card_eq_zero.mp htgt
          have htgtA : (D a).targets i = ∅ := by rw [htargets a i, htgtEmpty]
          have hmassZero (u : Point d × AffineVariety d) : ((D a).mass i u.2 : ℝ) = 0 := by
            dsimp [TrackA.SeparatedDepthData.mass]
            rw [htgtA, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
          have hsumEq : (∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ)) =
              ∑ _u ∈ bad a i, (0 : ℝ) := by
            apply Finset.sum_congr rfl
            intro u _
            exact hmassZero u
          rw [hsumEq, Finset.sum_const_zero]
      rw [hsumZero, hN, mul_zero]
    · have hNpos : 0 < N := by
        dsimp [N]
        have h1 : 0 ≤ ((centers i).card : ℝ) := Nat.cast_nonneg _
        have h2 : 0 ≤ ((targets i).card : ℝ) := Nat.cast_nonneg _
        have hprod : 0 ≤ ((centers i).card : ℝ) * (targets i).card := mul_nonneg h1 h2
        exact lt_of_le_of_ne hprod (Ne.symm hN)
      have hinc : (D a).incidenceMass i (bad a i) =
          (∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ)) / N := by
        dsimp [TrackA.SeparatedDepthData.incidenceMass, N]
        rw [hcenters a i, htargets a i]
      have ha := hi a (Finset.mem_univ a)
      have hmass_nonneg : 0 ≤ (∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ)) :=
        Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hinc_nonneg : 0 ≤ (D a).incidenceMass i (bad a i) := by
        rw [hinc]
        exact div_nonneg hmass_nonneg (le_of_lt hNpos)
      rw [Real.norm_of_nonneg hinc_nonneg, norm_one, mul_one] at ha
      rw [hinc] at ha
      exact (div_le_iff₀ hNpos).mp ha
  have hsumLe : (∑ a, ∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ)) ≤
      (Fintype.card α : ℝ) * ((ε / m) * N) := by
    have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset α)) (fun a _ => hterm a)
    have h2 : (∑ _a : α, (ε / m) * N) = (Fintype.card α : ℝ) * ((ε / m) * N) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  have hmLe : (Fintype.card α : ℝ) * (ε / m) ≤ ε := by
    have hcardLt : (Fintype.card α : ℝ) < m := by
      dsimp [m]
      linarith
    have hdiv : (Fintype.card α : ℝ) / m < 1 := by
      rw [div_lt_iff₀ hmPos]
      linarith
    calc
      (Fintype.card α : ℝ) * (ε / m) = ((Fintype.card α : ℝ) / m) * ε := by ring
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hdiv.le hε.le
      _ = ε := one_mul ε
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  calc
    ((batchBadPairs D centers targets bad i).card : ℝ) ≤
        ∑ a, ∑ u ∈ bad a i, ((D a).mass i u.2 : ℝ) := hcardBound
    _ ≤ (Fintype.card α : ℝ) * ((ε / m) * N) := hsumLe
    _ = ((Fintype.card α : ℝ) * (ε / m)) * N := by ring
    _ ≤ ε * N := mul_le_mul_of_nonneg_right hmLe (by positivity)

/-- Apply finite row Markov once to the common physical incidence deletion.
Empty products are allowed; the deletion and typical centers precede density. -/
theorem finite_incidence_row_deletion (centers targets : ℕ → Finset (Point d))
    (bad : ℕ → Finset (Point d × Point d))
    (hbad : ∀ i, bad i ⊆ centers i ×ˢ targets i)
    (hsmall : Framework.LittleO (fun i => ((bad i).card : ℝ))
      (fun i => (centers i).card * (targets i).card)) :
    ∃ badCenters : ℕ → Finset (Point d),
      (∀ i, badCenters i ⊆ centers i) ∧
      Framework.LittleO (fun i => ((badCenters i).card : ℝ))
        (fun i => (centers i).card) ∧
      Framework.UniformLittleO
        (fun i => {p : Point d // p ∈ centers i ∧ p ∉ badCenters i})
        (fun i p => (((targets i).filter (fun q => (p.val, q) ∈ bad i)).card : ℝ))
        (fun i _ => (targets i).card) := by
  let rowMass (i : ℕ) (p : Point d) : ℝ :=
    (((targets i).filter (fun q => (p, q) ∈ bad i)).card : ℝ)
  let valid (i : ℕ) : Prop := 1 ≤ (centers i).card ∧ 1 ≤ (targets i).card
  let α (i : ℕ) : ℝ :=
    if valid i then
      ((bad i).card : ℝ) / (((centers i).card : ℝ) * (targets i).card)
    else 0
  let root (i : ℕ) : ℝ := Real.sqrt (α i)
  let threshold (i : ℕ) : ℝ := (targets i).card * root i
  let badCenters (i : ℕ) : Finset (Point d) :=
    if valid i then
      (centers i).filter (fun p => threshold i < rowMass i p)
    else ∅
  have hsubset (i : ℕ) : badCenters i ⊆ centers i := by
    dsimp [badCenters]
    split_ifs
    · exact Finset.filter_subset _ _
    · exact Finset.empty_subset _
  have hrowSum (i : ℕ) : (∑ p ∈ centers i, rowMass i p) = ((bad i).card : ℝ) := by
    dsimp [rowMass]
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    have hstep1 : (∑ p ∈ centers i, ∑ q ∈ (targets i).filter (fun q => (p, q) ∈ bad i), (1 : ℝ)) =
        ∑ p ∈ centers i, ∑ q ∈ targets i, if (p, q) ∈ bad i then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_filter]
    rw [hstep1, ← Finset.sum_product']
    have hstep2 : (∑ x ∈ centers i ×ˢ targets i, if x ∈ bad i then (1 : ℝ) else 0) =
        ∑ x ∈ (centers i ×ˢ targets i).filter (fun x => x ∈ bad i), (1 : ℝ) := by
      rw [Finset.sum_filter]
    rw [hstep2]
    have heq : (centers i ×ˢ targets i).filter (fun x => x ∈ bad i) = bad i := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun hx => ⟨hbad i hx, hx⟩⟩
    rw [heq, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcardLe (i : ℕ) : ((badCenters i).card : ℝ) ≤ (centers i).card * root i := by
    by_cases hv : valid i
    · have hbadCenDef : badCenters i = (centers i).filter (fun p => threshold i < rowMass i p) := by
        dsimp [badCenters]; rw [if_pos hv]
      have htotalPos : 0 < ((centers i).card : ℝ) * (targets i).card := by
        have : 0 < (centers i).card := hv.1
        have : 0 < (targets i).card := hv.2
        positivity
      have hα_eq : α i = ((bad i).card : ℝ) / (((centers i).card : ℝ) * (targets i).card) := by
        dsimp [α]
        rw [if_pos hv]
      have hbadCard_eq : ((bad i).card : ℝ) = α i * (((centers i).card : ℝ) * (targets i).card) := by
        rw [hα_eq, div_mul_cancel₀ _ (ne_of_gt htotalPos)]
      by_cases hrootZero : root i = 0
      · have hαZero : α i = 0 := by
          have hroot : Real.sqrt (α i) = 0 := hrootZero
          have hsq := congr_arg (fun x : ℝ => x ^ 2) hroot
          have hnonneg : 0 ≤ α i := by
            rw [hα_eq]
            exact div_nonneg (Nat.cast_nonneg _) (le_of_lt htotalPos)
          rw [Real.sq_sqrt hnonneg] at hsq
          exact hsq.trans (by ring)
        have hbadZero : ((bad i).card : ℝ) = 0 := by rw [hbadCard_eq, hαZero, zero_mul]
        have hrowZero (p : Point d) (hp : p ∈ centers i) : rowMass i p = 0 := by
          have hle : rowMass i p ≤ ∑ q ∈ centers i, rowMass i q := by
            apply Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hp
          rw [hrowSum i, hbadZero] at hle
          have hnonneg : 0 ≤ rowMass i p := Nat.cast_nonneg _
          linarith
        have hfilterEmpty : (centers i).filter (fun p => threshold i < rowMass i p) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro p hp
          rw [Finset.mem_filter] at hp
          have hprow := hrowZero p hp.1
          have : threshold i = 0 := by dsimp [threshold]; rw [hrootZero, mul_zero]
          linarith [hp.2]
        rw [hbadCenDef, hfilterEmpty, Finset.card_empty, Nat.cast_zero, hrootZero, mul_zero]
      · have hthreshPos : 0 < threshold i := by
          dsimp [threshold]
          have hrootPos : 0 < root i := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hrootZero)
          have htgtPos : 0 < ((targets i).card : ℝ) := Nat.cast_pos.mpr hv.2
          exact mul_pos htgtPos hrootPos
        have hbadRowsLower : ((badCenters i).card : ℝ) * threshold i ≤
            ∑ p ∈ badCenters i, rowMass i p := by
          calc
            ((badCenters i).card : ℝ) * threshold i = ∑ _p ∈ badCenters i, threshold i := by
              rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ p ∈ badCenters i, rowMass i p := by
              apply Finset.sum_le_sum
              intro p hp
              rw [hbadCenDef, Finset.mem_filter] at hp
              exact hp.2.le
        have hbadRowsUpper : (∑ p ∈ badCenters i, rowMass i p) ≤ ((bad i).card : ℝ) := by
          calc
            (∑ p ∈ badCenters i, rowMass i p) ≤ ∑ p ∈ centers i, rowMass i p := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (hsubset i)
              intro p _ _
              exact Nat.cast_nonneg _
            _ = ((bad i).card : ℝ) := hrowSum i
        have hchain : ((badCenters i).card : ℝ) * threshold i ≤
            α i * (((centers i).card : ℝ) * (targets i).card) := by
          rw [← hbadCard_eq]
          exact hbadRowsLower.trans hbadRowsUpper
        have hrootSq : α i = (root i) ^ 2 := by
          have hnonneg : 0 ≤ α i := by
            rw [hα_eq]
            exact div_nonneg (Nat.cast_nonneg _) (le_of_lt htotalPos)
          exact (Real.sq_sqrt hnonneg).symm
        have hid : α i * (((centers i).card : ℝ) * (targets i).card) =
            ((centers i).card : ℝ) * root i * threshold i := by
          dsimp [threshold]
          rw [hrootSq]
          ring
        rw [hid] at hchain
        nlinarith [hthreshPos, hchain]
    · have hbadCenDef : badCenters i = ∅ := by
        dsimp [badCenters]; rw [if_neg hv]
      rw [hbadCenDef, Finset.card_empty, Nat.cast_zero]
      positivity
  have hrowLe (i : ℕ) (p : Point d) (hp : p ∈ centers i) (hpnot : p ∉ badCenters i) :
      rowMass i p ≤ (targets i).card * root i := by
    dsimp [badCenters] at hpnot
    split_ifs at hpnot with hv
    · rw [Finset.mem_filter, not_and] at hpnot
      have hnot := hpnot hp
      push_neg at hnot
      exact hnot
    · dsimp [valid] at hv
      by_cases hc : (centers i).card = 0
      · have : centers i = ∅ := Finset.card_eq_zero.mp hc
        rw [this] at hp
        cases hp
      · have ht : (targets i).card = 0 := by
          have : 1 ≤ (centers i).card := Nat.one_le_iff_ne_zero.mpr hc
          omega
        have : targets i = ∅ := Finset.card_eq_zero.mp ht
        have hlhs : rowMass i p = 0 := by
          dsimp [rowMass]; rw [this, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
        have hrhs : ((targets i).card : ℝ) * root i = 0 := by
          rw [ht, Nat.cast_zero, zero_mul]
        rw [hlhs, hrhs]
  have hrootSmall : Framework.LittleO root (fun _ => 1) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ζ hζ
    have hζ2 : 0 < ζ ^ 2 := by positivity
    filter_upwards [hsmall.def hζ2] with i hi
    have hrootNonneg : 0 ≤ root i := Real.sqrt_nonneg _
    dsimp [root, α]
    split_ifs with hv
    · have htotalPos : 0 < ((centers i).card : ℝ) * (targets i).card := by
        have : 0 < (centers i).card := hv.1
        have : 0 < (targets i).card := hv.2
        positivity
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)] at hi
      have hdiv : ((bad i).card : ℝ) / (((centers i).card : ℝ) * (targets i).card) ≤ ζ ^ 2 := by
        exact (div_le_iff₀ htotalPos).mpr hi
      have hsqrt : Real.sqrt (((bad i).card : ℝ) / (((centers i).card : ℝ) * (targets i).card)) ≤
          Real.sqrt (ζ ^ 2) := Real.sqrt_le_sqrt hdiv
      rw [Real.sqrt_sq hζ.le] at hsqrt
      rw [abs_one, mul_one, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hsqrt
    · rw [Real.sqrt_zero, abs_zero, abs_one, mul_one]
      exact hζ.le
  refine ⟨badCenters, hsubset, ?_, ?_⟩
  · apply Asymptotics.IsLittleO.of_bound
    intro ζ hζ
    filter_upwards [hrootSmall.def hζ] with i hi
    rw [norm_one, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hi
    have hbound := hcardLe i
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc
      ((badCenters i).card : ℝ) ≤ (centers i).card * root i := hbound
      _ ≤ (centers i).card * ζ := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
      _ = ζ * ((centers i).card : ℝ) := by ring
  · intro ζ hζ
    filter_upwards [hrootSmall.def hζ] with i hi p
    rw [norm_one, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hi
    have hrow := hrowLe i p.val p.property.1 p.property.2
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      rowMass i p.val ≤ (targets i).card * root i := hrow
      _ ≤ (targets i).card * ζ := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
      _ = ζ * ((targets i).card : ℝ) := by ring

/-- A fixed finite union of negligible center sets remains negligible. -/
theorem finite_center_union_small (centers : ℕ → Finset (Point d))
    (badCenters : α → ℕ → Finset (Point d))
    (hsmall : ∀ a, Framework.LittleO (fun i => ((badCenters a i).card : ℝ))
      (fun i => (centers i).card)) :
    Framework.LittleO
      (fun i => (((Finset.univ : Finset α).biUnion (fun a => badCenters a i)).card : ℝ))
      (fun i => (centers i).card) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let m : ℝ := (Fintype.card α : ℝ) + 1
  have hmPos : 0 < m := by
    dsimp [m]
    positivity
  have hεm : 0 < ε / m := div_pos hε hmPos
  have hbound (a : α) : ∀ᶠ i in atTop,
      ‖((badCenters a i).card : ℝ)‖ ≤ (ε / m) * ‖((centers i).card : ℝ)‖ :=
    (hsmall a).def hεm
  have hall : ∀ᶠ i in atTop, ∀ a ∈ (Finset.univ : Finset α),
      ‖((badCenters a i).card : ℝ)‖ ≤ (ε / m) * ‖((centers i).card : ℝ)‖ :=
    Framework.eventually_finite (Finset.univ : Finset α) _ (fun a _ => hbound a)
  filter_upwards [hall] with i hi
  have hcardUnion : (((Finset.univ : Finset α).biUnion (fun a => badCenters a i)).card : ℝ) ≤
      ∑ a, ((badCenters a i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have hsumBound : (∑ a, ((badCenters a i).card : ℝ)) ≤
      (Fintype.card α : ℝ) * ((ε / m) * ((centers i).card : ℝ)) := by
    have hterm (a : α) : ((badCenters a i).card : ℝ) ≤ (ε / m) * ((centers i).card : ℝ) := by
      have ha := hi a (Finset.mem_univ a)
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at ha
      exact ha
    have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset α)) (fun a _ => hterm a)
    have h2 : (∑ _a : α, (ε / m) * ((centers i).card : ℝ)) =
        (Fintype.card α : ℝ) * ((ε / m) * ((centers i).card : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  have hmLe : (Fintype.card α : ℝ) * (ε / m) ≤ ε := by
    have hcardLt : (Fintype.card α : ℝ) < m := by
      dsimp [m]
      linarith
    have hdiv : (Fintype.card α : ℝ) / m < 1 := by
      rw [div_lt_iff₀ hmPos]
      linarith
    calc
      (Fintype.card α : ℝ) * (ε / m) = ((Fintype.card α : ℝ) / m) * ε := by ring
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hdiv.le hε.le
      _ = ε := one_mul ε
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  calc
    (((Finset.univ : Finset α).biUnion (fun a => badCenters a i)).card : ℝ)
      ≤ ∑ a, ((badCenters a i).card : ℝ) := hcardUnion
    _ ≤ (Fintype.card α : ℝ) * ((ε / m) * ((centers i).card : ℝ)) := hsumBound
    _ = ((Fintype.card α : ℝ) * (ε / m)) * ((centers i).card : ℝ) := by ring
    _ ≤ ε * ((centers i).card : ℝ) :=
      mul_le_mul_of_nonneg_right hmLe (Nat.cast_nonneg (centers i).card)

/-- Every surviving physical target retains its fixed owner in every plateau
application. No assignment is recomputed after the common row deletion. -/
theorem batch_owner_retained {j : α → ℕ}
    (D : (a : α) → TrackA.SeparatedDepthData regime (j a))
    (targets : ℕ → Finset (Point d))
    (bad : α → ℕ → Finset (Point d × AffineVariety d))
    (htargets : ∀ a i, (D a).targets i = targets i)
    (i : ℕ) (p q : Point d) (hq : q ∈ targets i)
    (hnot : q ∉ batchBadTargets D targets bad i p) :
    ∀ a, (D a).owner i q ∈ (D a).retained i (bad a i) p := by
  intro a
  have hqTarget : q ∈ (D a).targets i := by rwa [htargets a i]
  have hownerCarrier : (D a).owner i q ∈ (D a).carriers i :=
    (D a).owner_member i q hqTarget
  rw [TrackA.SeparatedDepthData.retained, Finset.mem_filter]
  refine ⟨hownerCarrier, ?_⟩
  intro hbad
  apply hnot
  rw [batchBadTargets, Finset.mem_filter]
  exact ⟨hq, ⟨a, hbad⟩⟩

end

end DistinctDistances.SparseCones
