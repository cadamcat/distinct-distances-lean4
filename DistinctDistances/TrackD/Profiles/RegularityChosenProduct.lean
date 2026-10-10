import DistinctDistances.TrackD.Profiles.Regularity
import DistinctDistances.TrackD.Profiles.RegularityChosenCuts

/-!
# Chosen-margin product testing (`profiles.tex:446-510`)

With-margin copies of the pool-cut lift and the two product-testing
statements. The capture margin `η` is chosen before the pools and before
all later dense subsets and polynomial tests; the finite pool inputs carry
that chosen margin. Proofs are the existing `Regularity.lean` arguments
with `prof_regularity_cuts_with_margin` in place of `prof_regularity_cuts`.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

variable {d : ℕ}

/-- Specialize the source variables of a polynomial on pairs. -/
private def dprofiles2PairSourceSlice (F : PairPoly d) (x : Point d) : Poly d :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin d ⊕ Fin d => match i with
      | Sum.inl k => MvPolynomial.C (x k)
      | Sum.inr k => MvPolynomial.X k) F

/-- Specialize the target variables of a polynomial on pairs. -/
private def dprofiles2PairTargetSlice (F : PairPoly d) (y : Point d) : Poly d :=
  dprofiles2PairSourceSlice (MvPolynomial.rename Sum.swap F) y

private theorem dprofiles2PairSourceSlice_degree (F : PairPoly d) (x : Point d) :
    (dprofiles2PairSourceSlice F x).totalDegree ≤ F.totalDegree := by
  classical
  change (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : Fin d ⊕ Fin d => match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k) F).totalDegree ≤ F.totalDegree
  conv_lhs => rw [MvPolynomial.as_sum F]
  simp only [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  rw [MvPolynomial.eval₂Hom_monomial]
  have hfactor (i : Fin d ⊕ Fin d) (e : ℕ) :
      ((match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k) ^ e).totalDegree ≤
        (match i with | Sum.inl _ => 0 | Sum.inr _ => e) := by
    cases i with
    | inl k =>
      calc
        _ ≤ e * (MvPolynomial.C (x k) : Poly d).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ = 0 := by simp
    | inr k => simpa using (MvPolynomial.totalDegree_pow (MvPolynomial.X k) e)
  have hprod :
      (m.prod fun i e => (match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k) ^ e).totalDegree ≤
      m.sum fun i e => (match i with | Sum.inl _ => 0 | Sum.inr _ => e) := by
    have hprodDegree :
        (m.support.prod fun i => (match i with
          | Sum.inl k => MvPolynomial.C (x k)
          | Sum.inr k => MvPolynomial.X k) ^ m i).totalDegree ≤
          ∑ i ∈ m.support, ((match i with
            | Sum.inl k => MvPolynomial.C (x k)
            | Sum.inr k => MvPolynomial.X k) ^ m i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    have hterms :
        (∑ i ∈ m.support, ((match i with
            | Sum.inl k => MvPolynomial.C (x k)
            | Sum.inr k => MvPolynomial.X k) ^ m i).totalDegree) ≤
          ∑ i ∈ m.support, (match i with | Sum.inl _ => 0 | Sum.inr _ => m i) :=
      Finset.sum_le_sum (fun i hi => hfactor i (m i))
    rw [Finsupp.prod, Finsupp.sum]
    exact hprodDegree.trans hterms
  have hle :
      (m.sum fun i e => (match i with | Sum.inl _ => 0 | Sum.inr _ => e)) ≤
        m.sum fun _ e => e := by
    apply Finsupp.sum_le_sum
    intro i e
    cases i <;> simp
  calc
    _ ≤ (MvPolynomial.C (F.coeff m)).totalDegree +
        (m.prod fun i e => (match i with
          | Sum.inl k => MvPolynomial.C (x k)
          | Sum.inr k => MvPolynomial.X k) ^ e).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ m.sum fun _ e => e := by
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact hprod.trans hle
    _ ≤ F.totalDegree := MvPolynomial.le_totalDegree hm

private theorem dprofiles2PairTargetSlice_degree (F : PairPoly d) (y : Point d) :
    (dprofiles2PairTargetSlice F y).totalDegree ≤ F.totalDegree := by
  classical
  have h := dprofiles2PairSourceSlice_degree (d := d) (MvPolynomial.rename Sum.swap F) y
  have h1 := MvPolynomial.totalDegree_rename_le Sum.swap F
  simpa [dprofiles2PairTargetSlice] using h.trans h1

private theorem dprofiles2PairSourceSlice_eval (F : PairPoly d) (x y : Point d) :
    MvPolynomial.eval y (dprofiles2PairSourceSlice F x) =
      MvPolynomial.eval (pairPt x y) F := by
  classical
  change MvPolynomial.eval y (MvPolynomial.eval₂ MvPolynomial.C
      (fun i : Fin d ⊕ Fin d => match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k) F) = _
  rw [MvPolynomial.eval_eval₂]
  have hcoeff : (MvPolynomial.eval y).comp MvPolynomial.C = RingHom.id ℂ := by
    ext z
    simp
  rw [hcoeff, MvPolynomial.eval₂_id]
  have hvars : (fun i : Fin d ⊕ Fin d => MvPolynomial.eval y
      (match i with
        | Sum.inl k => MvPolynomial.C (x k)
        | Sum.inr k => MvPolynomial.X k)) = pairPt x y := by
    funext i
    cases i <;> simp [pairPt]
  simp [hvars]

private theorem dprofiles2PairTargetSlice_eval (F : PairPoly d) (x y : Point d) :
    MvPolynomial.eval x (dprofiles2PairTargetSlice F y) =
      MvPolynomial.eval (pairPt x y) F := by
  classical
  change MvPolynomial.eval x (dprofiles2PairSourceSlice (MvPolynomial.rename Sum.swap F) y) = _
  rw [dprofiles2PairSourceSlice_eval]
  rw [MvPolynomial.eval_rename]
  have hp : pairPt y x ∘ Sum.swap = pairPt x y := by
    funext i
    cases i <;> rfl
  rw [hp]

private theorem dprofiles2_close_plateau {d : ℕ} (t u : Fin d → ℝ) (j : ℕ)
    (η b ρ : ℝ) (hclose : ∀ i, |u i - t i| ≤ ρ) (hρ : ρ ≤ η / 2)
    (hplateau : OnPlateau t j (2 * η) b) : OnPlateau u j η b := by
  intro i
  have hdiff := abs_le.mp (hclose i)
  constructor
  · intro hi
    have ht := (hplateau i).1 hi
    nlinarith
  · intro hi
    have ht := (hplateau i).2 hi
    nlinarith


private theorem dprofiles2_cardPairsBoundFst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (B : Finset (α × β))
    (hB : B ⊆ S ×ˢ T) (u : ℝ)
    (hfiber : ∀ x ∈ S, ((T.filter (fun y => (x, y) ∈ B)).card : ℝ) ≤
      u * (T.card : ℝ)) :
    (B.card : ℝ) ≤ u * (S.card : ℝ) * (T.card : ℝ) := by
  classical
  have hmaps : (B : Set (α × β)).MapsTo Prod.fst S := by
    intro z hz
    exact (Finset.mem_product.mp (hB hz)).1
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiberCard (x : α) :
      (B.filter (fun z => z.1 = x)).card = (T.filter (fun y => (x, y) ∈ B)).card := by
    apply Finset.card_bij (fun z hz => z.2)
    · intro z hz
      have hzB := (Finset.mem_filter.mp hz).1
      have hzx := (Finset.mem_filter.mp hz).2
      have hzT := (Finset.mem_product.mp (hB hzB)).2
      have hzEq : z = (x, z.2) := Prod.ext hzx rfl
      have hzB' : (x, z.2) ∈ B := hzEq ▸ hzB
      exact Finset.mem_filter.mpr ⟨hzT, hzB'⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      apply Prod.ext
      · exact (Finset.mem_filter.mp hz₁).2.trans (Finset.mem_filter.mp hz₂).2.symm
      · exact heq
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyT, hyB⟩
      exact ⟨(x, y), Finset.mem_filter.mpr ⟨hyB, rfl⟩, rfl⟩
  have hsumReal : (B.card : ℝ) =
      ∑ x ∈ S, ((T.filter (fun y => (x, y) ∈ B)).card : ℝ) := by
    calc
      (B.card : ℝ) = ((∑ x ∈ S, (B.filter (fun z => z.1 = x)).card : ℕ) : ℝ) := by
        rw [hsum]
      _ = ∑ x ∈ S, ((B.filter (fun z => z.1 = x)).card : ℝ) := by norm_cast
      _ = ∑ x ∈ S, ((T.filter (fun y => (x, y) ∈ B)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact_mod_cast hfiberCard x
  calc
    (B.card : ℝ) = ∑ x ∈ S, ((T.filter (fun y => (x, y) ∈ B)).card : ℝ) := hsumReal
    _ ≤ ∑ x ∈ S, u * (T.card : ℝ) := Finset.sum_le_sum (by
      intro x hx
      exact hfiber x hx)
    _ = u * (S.card : ℝ) * (T.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_cast
      ring

private theorem dprofiles2_cardPairsBoundSnd {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (B : Finset (α × β))
    (hB : B ⊆ S ×ˢ T) (u : ℝ)
    (hfiber : ∀ y ∈ T, ((S.filter (fun x => (x, y) ∈ B)).card : ℝ) ≤
      u * (S.card : ℝ)) :
    (B.card : ℝ) ≤ u * (T.card : ℝ) * (S.card : ℝ) := by
  classical
  have hmaps : (B : Set (α × β)).MapsTo Prod.snd T := by
    intro z hz
    exact (Finset.mem_product.mp (hB hz)).2
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiberCard (y : β) :
      (B.filter (fun z => z.2 = y)).card = (S.filter (fun x => (x, y) ∈ B)).card := by
    apply Finset.card_bij (fun z hz => z.1)
    · intro z hz
      have hzB := (Finset.mem_filter.mp hz).1
      have hzy := (Finset.mem_filter.mp hz).2
      have hzS := (Finset.mem_product.mp (hB hzB)).1
      have hzEq : z = (z.1, y) := Prod.ext rfl hzy
      have hzB' : (z.1, y) ∈ B := hzEq ▸ hzB
      exact Finset.mem_filter.mpr ⟨hzS, hzB'⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      apply Prod.ext
      · exact heq
      · exact (Finset.mem_filter.mp hz₁).2.trans (Finset.mem_filter.mp hz₂).2.symm
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxS, hxB⟩
      exact ⟨(x, y), Finset.mem_filter.mpr ⟨hxB, rfl⟩, rfl⟩
  have hsumReal : (B.card : ℝ) =
      ∑ y ∈ T, ((S.filter (fun x => (x, y) ∈ B)).card : ℝ) := by
    calc
      (B.card : ℝ) = ((∑ y ∈ T, (B.filter (fun z => z.2 = y)).card : ℕ) : ℝ) := by
        rw [hsum]
      _ = ∑ y ∈ T, ((B.filter (fun z => z.2 = y)).card : ℝ) := by norm_cast
      _ = ∑ y ∈ T, ((S.filter (fun x => (x, y) ∈ B)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact_mod_cast hfiberCard y
  calc
    (B.card : ℝ) = ∑ y ∈ T, ((S.filter (fun x => (x, y) ∈ B)).card : ℝ) := hsumReal
    _ ≤ ∑ y ∈ T, u * (S.card : ℝ) := Finset.sum_le_sum (by
      intro y hy
      exact hfiber y hy)
    _ = u * (T.card : ℝ) * (S.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_cast
      ring


/-- The homogeneous numerator of one monomial after pulling back the direction chart. -/
private def dprofiles2LabelClearTerm (i₀ : Fin d) (N : ℕ)
    (m : (Fin d ⊕ Fin d) →₀ ℕ) (c : ℂ) : PairPoly d :=
  MvPolynomial.C c *
    (m.prod fun i e => match i with
      | Sum.inl k => MvPolynomial.X (Sum.inl k) ^ e
      | Sum.inr k =>
          (MvPolynomial.X (Sum.inr k) - MvPolynomial.X (Sum.inl k)) ^ e) *
    (MvPolynomial.X (Sum.inr i₀) - MvPolynomial.X (Sum.inl i₀)) ^
      (N - m.sum fun i e => match i with
        | Sum.inl _ => 0
        | Sum.inr _ => e)

/-- Clear a common denominator of exponent `N` in the chart pullback. -/
private def dprofiles2LabelClear (i₀ : Fin d) (N : ℕ) (G : PairPoly d) : PairPoly d :=
  ∑ m ∈ G.support, dprofiles2LabelClearTerm i₀ N m (G.coeff m)

private theorem dprofiles2LabelClearTerm_degree (i₀ : Fin d) (N : ℕ)
    (m : (Fin d ⊕ Fin d) →₀ ℕ) (c : ℂ)
    (htotal : m.sum (fun _ e => e) ≤ N) :
    (dprofiles2LabelClearTerm i₀ N m c).totalDegree ≤ 2 * N := by
  classical
  let δ : PairPoly d := MvPolynomial.X (Sum.inr i₀) - MvPolynomial.X (Sum.inl i₀)
  let base : PairPoly d := m.prod fun i e => match i with
    | Sum.inl k => MvPolynomial.X (Sum.inl k) ^ e
    | Sum.inr k => (MvPolynomial.X (Sum.inr k) - MvPolynomial.X (Sum.inl k)) ^ e
  have hfactorL (k : Fin d) (e : ℕ) :
      ((MvPolynomial.X (Sum.inl k) : PairPoly d) ^ e).totalDegree ≤ e := by simp
  have hfactorR (k : Fin d) (e : ℕ) :
      (((MvPolynomial.X (Sum.inr k) : PairPoly d) - MvPolynomial.X (Sum.inl k)) ^ e).totalDegree ≤ e := by
    have hbase :
        ((MvPolynomial.X (Sum.inr k) : PairPoly d) - MvPolynomial.X (Sum.inl k)).totalDegree ≤ 1 := by
      calc
        _ ≤ max (MvPolynomial.totalDegree (MvPolynomial.X (Sum.inr k) : PairPoly d))
            (MvPolynomial.totalDegree (MvPolynomial.X (Sum.inl k) : PairPoly d)) :=
          MvPolynomial.totalDegree_sub _ _
        _ ≤ 1 := by simp
    calc
      _ ≤ e * ((MvPolynomial.X (Sum.inr k) : PairPoly d) -
          MvPolynomial.X (Sum.inl k)).totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ e * 1 := Nat.mul_le_mul_left _ hbase
      _ = e := Nat.mul_one _
  have hbase : base.totalDegree ≤ m.sum (fun _ e => e) := by
    change ((∏ i ∈ m.support, (match i with
      | Sum.inl k => (MvPolynomial.X (Sum.inl k) : PairPoly d) ^ m i
      | Sum.inr k => ((MvPolynomial.X (Sum.inr k) : PairPoly d) -
          MvPolynomial.X (Sum.inl k)) ^ m i)).totalDegree) ≤ _
    calc
      _ ≤ ∑ i ∈ m.support,
          ((match i with
            | Sum.inl k => (MvPolynomial.X (Sum.inl k) : PairPoly d) ^ m i
            | Sum.inr k =>
                ((MvPolynomial.X (Sum.inr k) : PairPoly d) -
                  MvPolynomial.X (Sum.inl k)) ^ m i) : PairPoly d).totalDegree :=
        MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ i ∈ m.support, m i := Finset.sum_le_sum (by
        intro i hi
        cases i with
        | inl k => simpa using hfactorL k (m (Sum.inl k))
        | inr k => simpa using hfactorR k (m (Sum.inr k)))
      _ = m.sum (fun _ e => e) := by rw [Finsupp.sum]
  have hδ : δ.totalDegree ≤ 1 := by
    dsimp [δ]
    calc
      _ ≤ max (MvPolynomial.totalDegree (MvPolynomial.X (Sum.inr i₀) : PairPoly d))
          (MvPolynomial.totalDegree (MvPolynomial.X (Sum.inl i₀) : PairPoly d)) :=
        MvPolynomial.totalDegree_sub _ _
      _ ≤ 1 := by simp
  have hδpow (q : ℕ) : (δ ^ q).totalDegree ≤ q := by
    calc
      _ ≤ q * δ.totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ q * 1 := Nat.mul_le_mul_left _ hδ
      _ = q := Nat.mul_one _
  have hq : N - m.sum (fun i e => match i with
      | Sum.inl _ => 0
      | Sum.inr _ => e) ≤ N := Nat.sub_le _ _
  change (MvPolynomial.C c * base * δ ^ (N - m.sum (fun i e => match i with
      | Sum.inl _ => 0
      | Sum.inr _ => e))).totalDegree ≤ 2 * N
  calc
    _ ≤ (MvPolynomial.C c).totalDegree + base.totalDegree +
        (δ ^ (N - m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e))).totalDegree := by
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _)
    _ ≤ 0 + N + (N - m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e)) := by
      exact Nat.add_le_add (Nat.add_le_add (by simp) (hbase.trans htotal))
        (hδpow _)
    _ ≤ 2 * N := by omega

private theorem dprofiles2LabelClear_degree (i₀ : Fin d) (N : ℕ) (G : PairPoly d)
    (hG : G.totalDegree ≤ N) : (dprofiles2LabelClear i₀ N G).totalDegree ≤ 2 * N := by
  classical
  unfold dprofiles2LabelClear
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply dprofiles2LabelClearTerm_degree
  exact (MvPolynomial.le_totalDegree hm).trans hG

private theorem dprofiles2LabelClearTerm_eval (i₀ : Fin d) (N : ℕ)
    (m : (Fin d ⊕ Fin d) →₀ ℕ) (c : ℂ) (x y : Point d)
    (htotal : m.sum (fun _ e => e) ≤ N)
    (hδ : (y - x) i₀ ≠ 0) :
    MvPolynomial.eval (pairPt x y) (dprofiles2LabelClearTerm i₀ N m c) =
      ((y - x) i₀) ^ N *
        MvPolynomial.eval (labelPt i₀ x y) (MvPolynomial.monomial m c) := by
  classical
  let u : Point d := y - x
  let δ : ℂ := u i₀
  let base : PairPoly d := m.prod fun i e => match i with
    | Sum.inl k => MvPolynomial.X (Sum.inl k) ^ e
    | Sum.inr k => (MvPolynomial.X (Sum.inr k) - MvPolynomial.X (Sum.inl k)) ^ e
  have hδ' : δ ≠ 0 := by simpa [δ, u] using hδ
  have hsecond : m.sum (fun i e => match i with
      | Sum.inl _ => 0
      | Sum.inr _ => e) ≤ N := by
    calc
      _ ≤ m.sum (fun _ e => e) := by
        apply Finsupp.sum_le_sum
        intro i e
        cases i <;> simp
      _ ≤ N := htotal
  let labelCoord : Fin d ⊕ Fin d → ℂ := fun i => match i with
    | Sum.inl k => x k
    | Sum.inr k => δ⁻¹ * u k
  have hlabel (i : Fin d ⊕ Fin d) : labelPt i₀ x y i = labelCoord i := by
    cases i with
    | inl k => simp [labelPt, labelCoord, pairPt]
    | inr k => simp [labelPt, labelCoord, pairPt, u, δ, smul_eq_mul]
  have hfactor (i : Fin d ⊕ Fin d) (e : ℕ) :
      (match i with
        | Sum.inl k => x k ^ e
        | Sum.inr k => u k ^ e) =
      labelCoord i ^ e * δ ^ (match i with
        | Sum.inl _ => 0
        | Sum.inr _ => e) := by
    cases i with
    | inl k => change x k ^ e = x k ^ e * δ ^ 0; simp
    | inr k =>
      change u k ^ e = (δ⁻¹ * u k) ^ e * δ ^ e
      have hmul : (δ⁻¹ * u k) * δ = u k := by
        calc
          _ = δ⁻¹ * (u k * δ) := by ring
          _ = δ⁻¹ * (δ * u k) := by rw [mul_comm (u k) δ]
          _ = (δ⁻¹ * δ) * u k := by ring
          _ = u k := by simp [hδ']
      calc
        u k ^ e = ((δ⁻¹ * u k) * δ) ^ e := by rw [hmul]
        _ = (δ⁻¹ * u k) ^ e * δ ^ e := by rw [mul_pow]
  have hbaseEval : MvPolynomial.eval (pairPt x y) base =
      m.prod (fun i e => match i with
        | Sum.inl k => x k ^ e
        | Sum.inr k => u k ^ e) := by
    change MvPolynomial.eval (pairPt x y) (m.prod fun i e => match i with
      | Sum.inl k => MvPolynomial.X (Sum.inl k) ^ e
      | Sum.inr k => (MvPolynomial.X (Sum.inr k) - MvPolynomial.X (Sum.inl k)) ^ e) = _
    rw [Finsupp.prod, Finsupp.prod, MvPolynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i hi
    cases i <;> simp [pairPt, u]
  have hprod :
      m.prod (fun i e => match i with
        | Sum.inl k => x k ^ e
        | Sum.inr k => u k ^ e) =
      (m.prod fun i e => labelCoord i ^ e) *
        δ ^ m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e) := by
    calc
      _ = m.prod (fun i e => labelCoord i ^ e *
          δ ^ (match i with
            | Sum.inl _ => 0
            | Sum.inr _ => e)) := by
        exact Finsupp.prod_congr (fun i hi => hfactor i (m i))
      _ = (m.prod fun i e => labelCoord i ^ e) *
          (m.prod fun i e => δ ^ (match i with
            | Sum.inl _ => 0
            | Sum.inr _ => e)) := Finsupp.prod_mul
      _ = (m.prod fun i e => labelCoord i ^ e) *
          δ ^ m.sum (fun i e => match i with
            | Sum.inl _ => 0
            | Sum.inr _ => e) := by
        congr 1
        rw [Finsupp.prod, Finsupp.sum]
        exact Finset.prod_pow_eq_pow_sum m.support
          (fun i => match i with
            | Sum.inl _ => 0
            | Sum.inr _ => m i) δ
  have hpow : δ ^ m.sum (fun i e => match i with
      | Sum.inl _ => 0
      | Sum.inr _ => e) *
      δ ^ (N - m.sum (fun i e => match i with
        | Sum.inl _ => 0
        | Sum.inr _ => e)) = δ ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hsecond]
  have hlabelProd : MvPolynomial.eval (labelPt i₀ x y)
      (MvPolynomial.monomial m c) = c * (m.prod fun i e => labelCoord i ^ e) := by
    rw [MvPolynomial.eval_monomial]
    congr 1
    exact Finsupp.prod_congr (fun i hi => by rw [hlabel i])
  have hδeval : MvPolynomial.eval (pairPt x y)
      (MvPolynomial.X (Sum.inr i₀) - MvPolynomial.X (Sum.inl i₀)) = δ := by
    simp [pairPt, u, δ]
  rw [dprofiles2LabelClearTerm, MvPolynomial.eval_mul, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, hbaseEval, MvPolynomial.eval_pow, hδeval,
    hlabelProd, hprod]
  calc
    c * ((m.prod fun i e => labelCoord i ^ e) *
        δ ^ m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e)) *
        δ ^ (N - m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e)) =
      (c * (m.prod fun i e => labelCoord i ^ e)) *
        (δ ^ m.sum (fun i e => match i with
          | Sum.inl _ => 0
          | Sum.inr _ => e) *
          δ ^ (N - m.sum (fun i e => match i with
            | Sum.inl _ => 0
            | Sum.inr _ => e))) := by ring
    _ = _ := by rw [hpow]
    _ = _ := by
      rw [mul_comm (c * (m.prod fun i e => labelCoord i ^ e)) (δ ^ N)]

private theorem dprofiles2LabelClear_eval (i₀ : Fin d) (N : ℕ) (G : PairPoly d)
    (hG : G.totalDegree ≤ N) (x y : Point d) (hδ : (y - x) i₀ ≠ 0) :
    MvPolynomial.eval (pairPt x y) (dprofiles2LabelClear i₀ N G) =
      ((y - x) i₀) ^ N * MvPolynomial.eval (labelPt i₀ x y) G := by
  classical
  rw [dprofiles2LabelClear, MvPolynomial.eval_sum]
  calc
    _ = ∑ m ∈ G.support,
        ((y - x) i₀) ^ N *
          MvPolynomial.eval (labelPt i₀ x y) (MvPolynomial.monomial m (G.coeff m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact dprofiles2LabelClearTerm_eval i₀ N m (G.coeff m) x y
        ((MvPolynomial.le_totalDegree hm).trans hG) hδ
    _ = ((y - x) i₀) ^ N *
        MvPolynomial.eval (labelPt i₀ x y)
          (∑ m ∈ G.support, MvPolynomial.monomial m (G.coeff m)) := by
      rw [MvPolynomial.eval_sum, Finset.mul_sum]
    _ = _ := by rw [← G.as_sum]

/-- Choose one finite linear combination that stays nonzero at each of finitely many witnesses. -/
private theorem dprofiles2_exists_generic_coefficients {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ι → ℂ) (hdiag : ∀ i ∈ s, v i i ≠ 0) :
    ∃ c : ι → ℂ, ∀ i ∈ s, (∑ j ∈ s, c j * v j i) ≠ 0 := by
  classical
  revert hdiag
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      intro hdiag
      have hdiagS : ∀ i ∈ s, v i i ≠ 0 := fun i hi => hdiag i (Finset.mem_insert_of_mem hi)
      obtain ⟨c, hc⟩ := ih hdiagS
      let oldSum : ι → ℂ := fun i => ∑ j ∈ s, c j * v j i
      let forbidden : Finset ℂ :=
        (s.image fun i => if hv : v a i = 0 then 0 else -oldSum i / v a i) ∪
          {-oldSum a / v a a}
      obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset forbidden
      let c' : ι → ℂ := Function.update c a t
      have hsum (i : ι) :
          (∑ j ∈ insert a s, c' j * v j i) = oldSum i + t * v a i := by
        rw [Finset.sum_insert ha]
        have htail : (∑ j ∈ s, c' j * v j i) = oldSum i := by
          apply Finset.sum_congr rfl
          intro j hj
          have hja : j ≠ a := fun h => ha (h ▸ hj)
          simp [c', oldSum, hja]
        calc
          _ = t * v a i + oldSum i := by
            rw [show c' a = t by simp [c'], htail]
          _ = oldSum i + t * v a i := by ring
      have hnew (i : ι) (hi : i ∈ s) : oldSum i + t * v a i ≠ 0 := by
        by_cases hv : v a i = 0
        · simpa [oldSum, hv] using hc i hi
        · intro hz
          have htval : t = -oldSum i / v a i := by
            calc
              t = (t * v a i) / v a i := by field_simp [hv]
              _ = -oldSum i / v a i := by
                congr 1
                linear_combination hz
          have hmem : t ∈ s.image
              (fun q => if hq : v a q = 0 then 0 else -oldSum q / v a q) := by
            apply Finset.mem_image.mpr
            refine ⟨i, hi, ?_⟩
            simpa [hv] using htval.symm
          exact ht (Finset.mem_union.mpr (Or.inl hmem))
      have hnewA : oldSum a + t * v a a ≠ 0 := by
        have hdiagA := hdiag a (Finset.mem_insert_self a s)
        intro hz
        have htval : t = -oldSum a / v a a := by
          calc
            t = (t * v a a) / v a a := by field_simp [hdiagA]
            _ = -oldSum a / v a a := by
              congr 1
              linear_combination hz
        have hmem : t ∈ ({-oldSum a / v a a} : Finset ℂ) := by simp [htval]
        exact ht (Finset.mem_union.mpr (Or.inr hmem))
      refine ⟨c', ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa [hsum] using hnewA
      · rw [hsum]
        exact hnew i hi

/-- With-margin lift of the individual-cut estimate from pieces to a disjoint
pool. The capture margin `η ≤ ξ / 4` is chosen before the pool; the pool
plateau stays at the fixed gap `ξ`. Proved from
`prof_regularity_cuts_with_margin` at gap `ξ / 2`, via the same close-plateau
step (`ξ` to `ξ / 2` with `ρ ≤ ξ / 4`). -/
private theorem dprofiles2_pool_cut_count_with_margin (d : ℕ) (hd : 3 ≤ d) :
    ∀ (ε : ℝ), ε > 0 → ∀ (ξ : ℝ), ξ > 0 → ∀ (K : ℝ), K ≥ 1 →
      ∃ θ₁ > 0, ∃ η > 0, η ≤ ξ / 4 ∧ ∃ ρ₀ > 0, ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (pl : Finset (Piece d)) (s ρ : ℝ) (t : Fin d → ℝ),
        ρ ≤ ρ₀ → PoolGood P θ₁ η 1 ρ pl s t → s₁ ≤ s →
        ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau t j ξ b →
          1 ≤ testDeg (cfgB P) s b →
          ∀ α : Pt d → AffineVariety d, CarrierAssignment pl j α →
          ∀ g : AffineVariety d → Poly d,
            (∀ Z, ((g Z).totalDegree : ℝ) ≤ K * testDeg (cfgB P) s b) →
            (((poolPts pl).filter (fun p => g (α p) ∉ (α p).ideal ∧
              MvPolynomial.eval (toC p) (g (α p)) = 0)).card : ℝ) ≤
              ε * (poolPts pl).card := by
  intro ε hε ξ hξ K hK
  obtain ⟨θc, hθc, ηc, hηc, hηc_le, sc, hcuts⟩ :=
    prof_regularity_cuts_with_margin d hd ε hε (ξ / 2) (by positivity) K hK
  have hηc4 : ηc ≤ ξ / 4 := hηc_le.trans (by linarith)
  refine ⟨θc, hθc, ηc, hηc, hηc4, ξ / 4, by positivity, sc, ?_⟩
  intro P pl s ρ t hρ hpool hs j hj b hb hT α hα g hg
  classical
  let captured (X : Piece d) : Finset (Pt d) := X.pts.filter (fun p =>
    g (α p) ∉ (α p).ideal ∧ MvPolynomial.eval (toC p) (g (α p)) = 0)
  let allCaptured := (poolPts pl).filter (fun p =>
    g (α p) ∉ (α p).ideal ∧ MvPolynomial.eval (toC p) (g (α p)) = 0)
  have hρhalf : ρ ≤ (ξ / 2) / 2 := by linarith
  have hb2 : OnPlateau t j (2 * (ξ / 2)) b := by
    have h2 : 2 * (ξ / 2) = ξ := by ring
    rwa [h2]
  have hplateauX (X : Piece d) (hX : X ∈ pl) :
      OnPlateau X.path.time j (ξ / 2) b := by
    apply dprofiles2_close_plateau t X.path.time j (ξ / 2) b ρ
      (fun i => by simpa [abs_sub_comm] using hpool.close X hX i) hρhalf hb2
  have hcapturedBound (X : Piece d) (hX : X ∈ pl) :
      ((captured X).card : ℝ) ≤ ε * (X.pts.card : ℝ) := by
    have hpiece := hpool.pieces X hX
    have hwidth := hpool.width X hX
    have htestX : 1 ≤ testDeg (cfgB P) X.width b := by simpa [hwidth] using hT
    have hdegreeX : ∀ Z, ((g Z).totalDegree : ℝ) ≤
        K * testDeg (cfgB P) X.width b := by
      intro Z
      simpa [hwidth] using hg Z
    have hcutsBound := hcuts P X hpiece (by simpa [hwidth] using hs) j hj b
      (hplateauX X hX) htestX g hdegreeX
    have hsub : captured X ⊆ X.pts.filter (fun p =>
        ∃ Z ∈ X.path.localCarriers j (toC p),
          g Z ∉ Z.ideal ∧ MvPolynomial.eval (toC p) (g Z) = 0) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpX, hgood⟩
      rcases hα X hX p hpX with ⟨hcarrier, hpoint⟩
      exact Finset.mem_filter.mpr ⟨hpX, α p, ⟨hcarrier, hpoint⟩, hgood⟩
    have hcardNat := Finset.card_le_card hsub
    have hcardReal : ((captured X).card : ℝ) ≤
        ((X.pts.filter (fun p => ∃ Z ∈ X.path.localCarriers j (toC p),
          g Z ∉ Z.ideal ∧ MvPolynomial.eval (toC p) (g Z) = 0)).card : ℝ) := by
      exact_mod_cast hcardNat
    exact hcardReal.trans hcutsBound
  have hsub : allCaptured ⊆ pl.biUnion captured := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpPool, hgood⟩
    rcases Finset.mem_biUnion.mp hpPool with ⟨X, hX, hpX⟩
    exact Finset.mem_biUnion.mpr ⟨X, hX, Finset.mem_filter.mpr ⟨hpX, hgood⟩⟩
  have hcardNat : allCaptured.card ≤ ∑ X ∈ pl, (captured X).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsum : (∑ X ∈ pl, ((captured X).card : ℝ)) ≤
      ε * ∑ X ∈ pl, (X.pts.card : ℝ) := by
    calc
      _ ≤ ∑ X ∈ pl, ε * (X.pts.card : ℝ) := Finset.sum_le_sum (by
        intro X hX
        exact hcapturedBound X hX)
      _ = _ := by rw [Finset.mul_sum]
  have hcardPool : ((poolPts pl).card : ℝ) = ∑ X ∈ pl, (X.pts.card : ℝ) := by
    change ((pl.biUnion Piece.pts).card : ℝ) = _
    rw [Finset.card_biUnion hpool.disjoint]
    norm_cast
  calc
    (allCaptured.card : ℝ) ≤ ∑ X ∈ pl, ((captured X).card : ℝ) := by exact_mod_cast hcardNat
    _ ≤ ε * ∑ X ∈ pl, (X.pts.card : ℝ) := hsum
    _ = ε * (poolPts pl).card := by rw [hcardPool]

/-- `prof:product-testing` with chosen capture margin (`profiles.tex:446–459`).
The margin `η ≤ ξ / 4` is chosen before the pools and before all later dense
subsets and polynomial tests; the two finite pool inputs carry it. Proved
from `dprofiles2_pool_cut_count_with_margin` by the existing product
argument. -/
theorem prof_product_testing_with_margin (d : ℕ) (hd : 3 ≤ d) :
    ∀ θ > 0, ∀ ξ > 0, ∀ K ≥ 1, ∃ θ₁ > 0, ∃ η > 0, η ≤ ξ / 4 ∧ ∃ ρ₀ > 0, ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (plx ply : Finset (Piece d)) (s ρ : ℝ) (t : Fin d → ℝ),
        ρ ≤ ρ₀ → PoolGood P θ₁ η 1 ρ plx s t → PoolGood P θ₁ η 1 ρ ply s t →
        s₁ ≤ s → ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau t j ξ b →
          1 ≤ testDeg (cfgB P) s b →
          ∀ αx αy : Pt d → AffineVariety d, CarrierAssignment plx j αx →
            CarrierAssignment ply j αy →
          ∀ F : PairPoly d, (F.totalDegree : ℝ) ≤ K * testDeg (cfgB P) s b →
          (((poolPts plx ×ˢ poolPts ply).filter (fun pq =>
                MvPolynomial.eval (pairPt (toC pq.1) (toC pq.2)) F = 0 ∧
                ¬ VanishesOnProduct F (αx pq.1) (αy pq.2))).card : ℝ) ≤
              θ * (poolPts plx).card * (poolPts ply).card := by
  intro θ hθ ξ hξ K hK
  obtain ⟨θc, hθc, ηc, hηc, hηc4, ρ₀, hρ₀, s₁, hcuts⟩ :=
    dprofiles2_pool_cut_count_with_margin d hd (θ / 2) (by positivity) ξ hξ K hK
  refine ⟨θc, hθc, ηc, hηc, hηc4, ρ₀, hρ₀, s₁, ?_⟩
  intro P plx ply s ρ t hρ hpoolX hpoolY hs j hj b hb hT αx αy hαx hαy F hF
  classical
  by_cases hxempty : plx = ∅
  · simp [poolPts, hxempty]
  by_cases hyempty : ply = ∅
  · simp [poolPts, hyempty]
  let Sx := poolPts plx
  let Sy := poolPts ply
  let bad := (Sx ×ˢ Sy).filter (fun pq =>
    MvPolynomial.eval (pairPt (toC pq.1) (toC pq.2)) F = 0 ∧
      ¬ VanishesOnProduct F (αx pq.1) (αy pq.2))
  let badX := (Sx ×ˢ Sy).filter (fun pq =>
    MvPolynomial.eval (pairPt (toC pq.1) (toC pq.2)) F = 0 ∧
      dprofiles2PairSourceSlice F (toC pq.1) ∉ (αy pq.2).ideal)
  let badY := (Sx ×ˢ Sy).filter (fun pq =>
    MvPolynomial.eval (pairPt (toC pq.1) (toC pq.2)) F = 0 ∧
      dprofiles2PairSourceSlice F (toC pq.1) ∈ (αy pq.2).ideal ∧
      ¬ VanishesOnProduct F (αx pq.1) (αy pq.2))
  have hbadSubset : bad ⊆ badX ∪ badY := by
    intro pq hpq
    rcases Finset.mem_filter.mp hpq with ⟨hpqProd, ⟨heval, hnonvan⟩⟩
    by_cases hmem : dprofiles2PairSourceSlice F (toC pq.1) ∈ (αy pq.2).ideal
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨hpqProd, heval, hmem, hnonvan⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨hpqProd, heval, hmem⟩))
  have hbadXsubset : badX ⊆ Sx ×ˢ Sy := Finset.filter_subset _ _
  have hbadYsubset : badY ⊆ Sx ×ˢ Sy := Finset.filter_subset _ _
  have hbadXfiber (p : Pt d) (hp : p ∈ Sx) :
      ((Sy.filter (fun q => (p, q) ∈ badX)).card : ℝ) ≤
        (θ / 2) * (Sy.card : ℝ) := by
    have hdegree (Z : AffineVariety d) :
        ((dprofiles2PairSourceSlice F (toC p)).totalDegree : ℝ) ≤
          K * testDeg (cfgB P) s b := by
      have hdegSlice :
          (dprofiles2PairSourceSlice F (toC p)).totalDegree ≤ F.totalDegree :=
        dprofiles2PairSourceSlice_degree F (toC p)
      have hdegReal :
          ((dprofiles2PairSourceSlice F (toC p)).totalDegree : ℝ) ≤
            (F.totalDegree : ℝ) := by exact_mod_cast hdegSlice
      exact hdegReal.trans hF
    have hpoolBound := hcuts P ply s ρ t hρ hpoolY hs j hj b hb hT αy hαy
      (fun _ => dprofiles2PairSourceSlice F (toC p)) hdegree
    have hfiberSet : Sy.filter (fun q => (p, q) ∈ badX) =
        (poolPts ply).filter (fun q =>
          dprofiles2PairSourceSlice F (toC p) ∉ (αy q).ideal ∧
          MvPolynomial.eval (toC q) (dprofiles2PairSourceSlice F (toC p)) = 0) := by
      ext q
      simp [badX, Sy, hp, dprofiles2PairSourceSlice_eval, and_comm, and_left_comm, and_assoc]
    rw [hfiberSet]
    exact hpoolBound
  have hbadXbound := dprofiles2_cardPairsBoundFst Sx Sy badX hbadXsubset
    (θ / 2) hbadXfiber
  have hbadYfiber (q : Pt d) (hq : q ∈ Sy) :
      ((Sx.filter (fun p => (p, q) ∈ badY)).card : ℝ) ≤
        (θ / 2) * (Sx.card : ℝ) := by
    let hqSlice : AffineVariety d → Poly d := fun Z =>
      if hz : ∃ y : Point d, y ∈ αy q ∧ dprofiles2PairTargetSlice F y ∉ Z.ideal then
        dprofiles2PairTargetSlice F (Classical.choose hz)
      else 0
    have hdegree (Z : AffineVariety d) :
        ((hqSlice Z).totalDegree : ℝ) ≤ K * testDeg (cfgB P) s b := by
      dsimp [hqSlice]
      split_ifs with hz
      · have hdegSlice : (dprofiles2PairTargetSlice F (Classical.choose hz)).totalDegree ≤
            F.totalDegree := dprofiles2PairTargetSlice_degree F (Classical.choose hz)
        have hdegReal :
            ((dprofiles2PairTargetSlice F (Classical.choose hz)).totalDegree : ℝ) ≤
              (F.totalDegree : ℝ) := by exact_mod_cast hdegSlice
        exact hdegReal.trans hF
      · simpa using mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hK)
          (le_trans (by norm_num : (0 : ℝ) ≤ 1) hT)
    have hpoolBound := hcuts P plx s ρ t hρ hpoolX hs j hj b hb hT αx hαx hqSlice hdegree
    have hcapSubset : Sx.filter (fun p => (p, q) ∈ badY) ⊆
        (Sx.filter (fun p => hqSlice (αx p) ∉ (αx p).ideal ∧
          MvPolynomial.eval (toC p) (hqSlice (αx p)) = 0)) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpX, hpBad⟩
      rcases Finset.mem_filter.mp hpBad with ⟨hpProd, ⟨heval, hsliceMem, hnonvan⟩⟩
      have hprodWitness : ∃ x' ∈ αx p, ∃ y' ∈ αy q,
          MvPolynomial.eval (pairPt x' y') F ≠ 0 := by
        by_contra hn
        apply hnonvan
        intro x' hx' y' hy'
        by_contra hzero
        exact hn ⟨x', hx', y', hy', hzero⟩
      rcases hprodWitness with ⟨x', hx', y', hy', hne⟩
      have hnotmem : dprofiles2PairTargetSlice F y' ∉ (αx p).ideal := by
        intro hmem
        have hmem' := hmem
        rw [← AffineVariety.vanishingIdeal_points] at hmem'
        have heval' := MvPolynomial.mem_vanishingIdeal_iff.mp hmem' x' hx'
        change MvPolynomial.eval x' (dprofiles2PairTargetSlice F y') = 0 at heval'
        rw [dprofiles2PairTargetSlice_eval] at heval'
        exact hne heval'
      have hex : ∃ y : Point d, y ∈ αy q ∧
          dprofiles2PairTargetSlice F y ∉ (αx p).ideal := ⟨y', hy', hnotmem⟩
      have hspec := Classical.choose_spec hex
      have hproper : hqSlice (αx p) ∉ (αx p).ideal := by
        simp [hqSlice, hex, hspec.2]
      have hvan : MvPolynomial.eval (Classical.choose hex)
          (dprofiles2PairSourceSlice F (toC p)) = 0 := by
        have hmem' : dprofiles2PairSourceSlice F (toC p) ∈
            MvPolynomial.vanishingIdeal ℂ (αy q).points := by
          have hmem'' := hsliceMem
          rw [← AffineVariety.vanishingIdeal_points] at hmem''
          exact hmem''
        exact MvPolynomial.mem_vanishingIdeal_iff.mp hmem'
          (Classical.choose hex) hspec.1
      have hevalhq : MvPolynomial.eval (toC p) (hqSlice (αx p)) = 0 := by
        calc
          _ = MvPolynomial.eval (toC p) (dprofiles2PairTargetSlice F
              (Classical.choose hex)) := by simp [hqSlice, hex]
          _ = MvPolynomial.eval (pairPt (toC p) (Classical.choose hex)) F :=
              dprofiles2PairTargetSlice_eval F (toC p) (Classical.choose hex)
          _ = MvPolynomial.eval (Classical.choose hex)
              (dprofiles2PairSourceSlice F (toC p)) :=
                (dprofiles2PairSourceSlice_eval F (toC p) (Classical.choose hex)).symm
          _ = 0 := hvan
      exact Finset.mem_filter.mpr ⟨hpX, hproper, hevalhq⟩
    have hcardNat := Finset.card_le_card hcapSubset
    have hcardReal :
        ((Sx.filter (fun p => (p, q) ∈ badY)).card : ℝ) ≤
          ((Sx.filter (fun p => hqSlice (αx p) ∉ (αx p).ideal ∧
            MvPolynomial.eval (toC p) (hqSlice (αx p)) = 0)).card : ℝ) := by
      exact_mod_cast hcardNat
    exact hcardReal.trans hpoolBound
  have hbadYbound := dprofiles2_cardPairsBoundSnd Sx Sy badY hbadYsubset
    (θ / 2) hbadYfiber
  have hbadBound : (bad.card : ℝ) ≤ θ * (Sx.card : ℝ) * (Sy.card : ℝ) := by
    calc
      (bad.card : ℝ) ≤ ((badX ∪ badY).card : ℝ) := by exact_mod_cast Finset.card_le_card hbadSubset
      _ ≤ (badX.card : ℝ) + (badY.card : ℝ) := by
        exact_mod_cast (Finset.card_union_le badX badY)
      _ ≤ (θ / 2) * (Sx.card : ℝ) * (Sy.card : ℝ) +
          (θ / 2) * (Sy.card : ℝ) * (Sx.card : ℝ) := add_le_add hbadXbound hbadYbound
      _ = θ * (Sx.card : ℝ) * (Sy.card : ℝ) := by ring
  simpa [bad, Sx, Sy] using hbadBound

/-- `prof:product-testing.labels` with chosen capture margin
(`profiles.tex:461–472, 490–510`). The margin `η ≤ ξ / 4` is chosen before
the pools and before all later graphs and label families; the two finite
pool inputs carry it. Proved from `prof_product_testing_with_margin` by the
existing label-clearing argument. -/
theorem prof_product_testing_labels_with_margin (d : ℕ) (hd : 3 ≤ d) :
    ∀ θ > 0, ∀ ξ > 0, ∀ K ≥ 1, ∃ θ₁ > 0, ∃ η > 0, η ≤ ξ / 4 ∧ ∃ ρ₀ > 0, ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (plx ply : Finset (Piece d)) (s ρ : ℝ) (t : Fin d → ℝ),
        ρ ≤ ρ₀ → PoolGood P θ₁ η 1 ρ plx s t → PoolGood P θ₁ η 1 ρ ply s t →
        s₁ ≤ s → ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau t j ξ b →
          1 ≤ testDeg (cfgB P) s b →
          ∀ αx αy : Pt d → AffineVariety d, CarrierAssignment plx j αx →
            CarrierAssignment ply j αy →
          ∀ (i₀ : Fin d) (𝒢 : Set (PairPoly d)),
            (∀ G ∈ 𝒢, (G.totalDegree : ℝ) ≤ K * testDeg (cfgB P) s b) →
          ∀ Γ ⊆ poolPts plx ×ˢ poolPts ply,
            (∀ pq ∈ Γ, (toC pq.2 - toC pq.1) i₀ ≠ 0 ∧
              ∀ G ∈ 𝒢, MvPolynomial.eval (labelPt i₀ (toC pq.1) (toC pq.2)) G = 0) →
            ((Γ.filter (fun pq => ∃ G ∈ 𝒢, ∃ x ∈ αx pq.1, ∃ y ∈ αy pq.2,
                (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (labelPt i₀ x y) G ≠ 0)).card : ℝ) ≤
              θ * (poolPts plx).card * (poolPts ply).card := by
  intro θ hθ ξ hξ K hK
  have h2K : 1 ≤ 2 * K := by nlinarith
  obtain ⟨θ₁, hθ₁, η, hη, hη4, ρ₀, hρ₀, s₁, hproduct⟩ :=
    prof_product_testing_with_margin d hd θ hθ ξ hξ (2 * K) h2K
  refine ⟨θ₁, hθ₁, η, hη, hη4, ρ₀, hρ₀, s₁, ?_⟩
  intro P plx ply s ρ t hρ hpoolX hpoolY hs j hj b hb hT αx αy hαx hαy i₀ 𝒢 hdegree Γ hΓsub hgraph
  classical
  let R : ℝ := K * testDeg (cfgB P) s b
  let N : ℕ := ⌊R⌋₊
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hT0 : 0 ≤ testDeg (cfgB P) s b := le_trans (by norm_num) hT
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := by
    dsimp [R]
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hT)]
  have hNreal : (N : ℝ) ≤ R := by exact Nat.floor_le hR0
  have hGdegreeNat (G : PairPoly d) (hG : G ∈ 𝒢) : G.totalDegree ≤ N := by
    apply (Nat.le_floor_iff hR0).2
    simpa [R] using hdegree G hG
  let bad : Finset (Pt d × Pt d) := Γ.filter (fun pq =>
    ∃ G ∈ 𝒢, ∃ x ∈ αx pq.1, ∃ y ∈ αy pq.2,
      (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (labelPt i₀ x y) G ≠ 0)
  have hwitExists (q : {pq : Pt d × Pt d // pq ∈ bad}) :
      ∃ w : PairPoly d × (Point d × Point d),
        w.1 ∈ 𝒢 ∧ w.2.1 ∈ αx q.val.1 ∧ w.2.2 ∈ αy q.val.2 ∧
          (w.2.2 - w.2.1) i₀ ≠ 0 ∧
          MvPolynomial.eval (labelPt i₀ w.2.1 w.2.2) w.1 ≠ 0 := by
    rcases Finset.mem_filter.mp q.property with ⟨_, hbad⟩
    rcases hbad with ⟨G, hG, x, hx, y, hy, hchart, hne⟩
    exact ⟨(G, (x, y)), hG, hx, hy, hchart, hne⟩
  let witness : {pq : Pt d × Pt d // pq ∈ bad} → PairPoly d × (Point d × Point d) :=
    fun q => Classical.choose (hwitExists q)
  have hwitnessSpec (q : {pq : Pt d × Pt d // pq ∈ bad}) :=
      Classical.choose_spec (hwitExists q)
  let v : {pq : Pt d × Pt d // pq ∈ bad} → {pq : Pt d × Pt d // pq ∈ bad} → ℂ :=
    fun q r => MvPolynomial.eval (labelPt i₀ (witness r).2.1 (witness r).2.2) (witness q).1
  have hdiag : ∀ q ∈ bad.attach, v q q ≠ 0 := by
    intro q hq
    exact (hwitnessSpec q).2.2.2.2
  obtain ⟨coeff, hcoeff⟩ := dprofiles2_exists_generic_coefficients bad.attach v hdiag
  let H : PairPoly d :=
    ∑ q ∈ bad.attach, MvPolynomial.C (coeff q) * (witness q).1
  have hHdegree : H.totalDegree ≤ N := by
    unfold H
    apply MvPolynomial.totalDegree_finsetSum_le
    intro q hq
    calc
      _ ≤ (MvPolynomial.C (coeff q)).totalDegree + (witness q).1.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ N := by
        simpa using hGdegreeNat (witness q).1 (hwitnessSpec q).1
  let F : PairPoly d := dprofiles2LabelClear i₀ N H
  have hFdegreeNat : F.totalDegree ≤ 2 * N := by
    simpa [F] using dprofiles2LabelClear_degree i₀ N H hHdegree
  have hFdegree : (F.totalDegree : ℝ) ≤ (2 * K) * testDeg (cfgB P) s b := by
    calc
      _ ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hFdegreeNat
      _ = (2 : ℝ) * (N : ℝ) := by norm_num
      _ ≤ (2 : ℝ) * R := mul_le_mul_of_nonneg_left hNreal (by norm_num)
      _ = (2 * K) * testDeg (cfgB P) s b := by dsimp [R]; ring
  have hHzero (pq : Pt d × Pt d) (hpq : pq ∈ Γ) :
      MvPolynomial.eval (labelPt i₀ (toC pq.1) (toC pq.2)) H = 0 := by
    change MvPolynomial.eval (labelPt i₀ (toC pq.1) (toC pq.2))
      (∑ q ∈ bad.attach, MvPolynomial.C (coeff q) * (witness q).1) = 0
    rw [MvPolynomial.eval_sum]
    apply Finset.sum_eq_zero
    intro q hq
    have hGzero := (hgraph pq hpq).2 (witness q).1 (hwitnessSpec q).1
    simp [hGzero]
  have hHnonzero (q : {pq : Pt d × Pt d // pq ∈ bad}) :
      MvPolynomial.eval (labelPt i₀ (witness q).2.1 (witness q).2.2) H ≠ 0 := by
    have heval : MvPolynomial.eval (labelPt i₀ (witness q).2.1 (witness q).2.2) H =
        ∑ r ∈ bad.attach, coeff r * v r q := by
      simp [H, v]
    rw [heval]
    exact hcoeff q (Finset.mem_attach _ _)
  let tested : Finset (Pt d × Pt d) := (poolPts plx ×ˢ poolPts ply).filter (fun pq =>
    MvPolynomial.eval (pairPt (toC pq.1) (toC pq.2)) F = 0 ∧
      ¬ VanishesOnProduct F (αx pq.1) (αy pq.2))
  have hFsample (q : {pq : Pt d × Pt d // pq ∈ bad}) (hqΓ : q.val ∈ Γ) :
      MvPolynomial.eval (pairPt (toC q.val.1) (toC q.val.2)) F = 0 := by
    have hchart := (hgraph q.val hqΓ).1
    change MvPolynomial.eval (pairPt (toC q.val.1) (toC q.val.2))
      (dprofiles2LabelClear i₀ N H) = 0
    rw [dprofiles2LabelClear_eval i₀ N H hHdegree
      (toC q.val.1) (toC q.val.2) hchart, hHzero q.val hqΓ]
    simp
  have hFnonzero (q : {pq : Pt d × Pt d // pq ∈ bad}) :
      MvPolynomial.eval (pairPt (witness q).2.1 (witness q).2.2) F ≠ 0 := by
    have hchart := (hwitnessSpec q).2.2.2.1
    change MvPolynomial.eval (pairPt (witness q).2.1 (witness q).2.2)
      (dprofiles2LabelClear i₀ N H) ≠ 0
    rw [dprofiles2LabelClear_eval i₀ N H hHdegree
      (witness q).2.1 (witness q).2.2 hchart]
    exact mul_ne_zero (pow_ne_zero _ hchart) (hHnonzero q)
  have hFnotVanish (q : {pq : Pt d × Pt d // pq ∈ bad}) :
      ¬ VanishesOnProduct F (αx q.val.1) (αy q.val.2) := by
    intro hvan
    rcases hwitnessSpec q with ⟨_, hx, hy, _, _⟩
    exact hFnonzero q (hvan (witness q).2.1 hx (witness q).2.2 hy)
  have hbadSubset : bad ⊆ tested := by
    intro pq hpq
    let q : {pq : Pt d × Pt d // pq ∈ bad} := ⟨pq, hpq⟩
    have hqΓ : pq ∈ Γ := (Finset.mem_filter.mp hpq).1
    exact Finset.mem_filter.mpr ⟨hΓsub hqΓ, hFsample q hqΓ, hFnotVanish q⟩
  have htested := hproduct P plx ply s ρ t hρ hpoolX hpoolY hs j hj b hb hT
    αx αy hαx hαy F hFdegree
  have hcardNat := Finset.card_le_card hbadSubset
  have hcardReal : (bad.card : ℝ) ≤ (tested.card : ℝ) := by exact_mod_cast hcardNat
  have hfinal : (bad.card : ℝ) ≤ θ * (poolPts plx).card * (poolPts ply).card :=
    hcardReal.trans htested
  simpa [bad] using hfinal


end

end TrackD
end DistinctDistances
