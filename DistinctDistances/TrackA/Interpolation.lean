import DistinctDistances.TrackA.Definitions
import DistinctDistances.TrackA.SeparatorOriginSupport
import DistinctDistances.TrackA.SeparatorTranslationSupport
import DistinctDistances.TrackA.SocleSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- `poly:socle`, polynomial.tex:121–162. Used by interpolation:213–219.
Grade lead: determinant identification in the top Koszul/Ext map. -/
theorem poly_socle {F : Type*} [Field F] [IsAlgClosed F] (c : ℕ)
    (f : Fin c → OriginLocalRing c F) (Q : Matrix (Fin c) (Fin c) (OriginLocalRing c F))
    (hfinite : Module.length (OriginLocalRing c F)
      (OriginLocalRing c F ⧸ Ideal.span (Set.range f)) < ⊤)
    (hQ : ∀ i, f i = ∑ j, Q i j *
      algebraMap (FieldPoly c F) (OriginLocalRing c F) (MvPolynomial.X j)) :
    Matrix.det Q ∉ Ideal.span (Set.range f) :=
  Socle.origin_det_not_mem c f Q hfinite hQ

/-- `poly:interpolation.separators`, polynomial.tex:164–171,179–219.
The separator vanishes at every other zero, including larger components. -/
theorem poly_interpolation_separators {F : Type*} [Field F] [IsAlgClosed F]
    (c L : ℕ) (hL : 1 ≤ L) (E : Set (FieldPoly c F))
    (hE : ∀ f ∈ E, f.totalDegree ≤ L) (S : Finset (FieldPoint c F))
    (hS : IsolatedPoints E S) :
    ∀ z ∈ S, ∃ s : FieldPoly c F, s.totalDegree ≤ c * (L-1) ∧
      MvPolynomial.eval z s = 1 ∧
      ∀ y ∈ MvPolynomial.zeroLocus F (Ideal.span E), y ≠ z → MvPolynomial.eval y s = 0 := by
  intro z hz
  let shift := OAI.PiExponent.WeightedBezout.translationEquiv z
  let E₀ := shift '' E
  have hE₀ : ∀ f ∈ E₀, f.totalDegree ≤ L := by
    rintro _ ⟨f, hf, rfl⟩
    exact (separator_translation_degree z f).trans (hE f hf)
  have hmin := separator_translation_minimal z E (hS z hz)
  obtain ⟨s₀, hdeg, hval, hzero⟩ := origin_isolated_separator c L E₀ hE₀ hmin (poly_socle c)
  let s := OAI.PiExponent.WeightedBezout.translationEquiv (-z) s₀
  have hseval (y : FieldPoint c F) : MvPolynomial.eval y s = MvPolynomial.eval (y-z) s₀ := by
    rw [separator_translation_eval]
    have heq : -z+y = y-z := by module
    rw [heq]
  refine ⟨s, (separator_translation_degree (-z) s₀).trans hdeg, ?_, ?_⟩
  · rw [hseval, sub_self]
    exact hval
  · intro y hy hyz
    rw [hseval]
    apply hzero (y-z) _ (sub_ne_zero.mpr hyz)
    rw [MvPolynomial.zeroLocus_span]
    rintro _ ⟨f, hf, rfl⟩
    rw [MvPolynomial.aeval_eq_eval, separator_translation_eval]
    have heq : z+(y-z) = y := by module
    rw [heq]
    have h := hy f (Ideal.subset_span hf)
    rwa [MvPolynomial.aeval_eq_eval] at h

lemma isolatedPoints_subset_zeroLocus {F : Type*} [Field F] {c : ℕ}
    {E : Set (FieldPoly c F)} {S : Finset (FieldPoint c F)}
    (hS : IsolatedPoints E S) {z : FieldPoint c F} (hz : z ∈ S) :
    z ∈ MvPolynomial.zeroLocus F (Ideal.span E) := by
  have hmin := hS z hz
  have hle : Ideal.span E ≤ pointIdealOver z := hmin.le
  rw [MvPolynomial.zeroLocus_span]
  intro f hf
  have hf_in : f ∈ pointIdealOver z := hle (Ideal.subset_span hf)
  exact (MvPolynomial.mem_vanishingIdeal_iff.mp hf_in) z (Set.mem_singleton z)

lemma totalDegree_X_sub_C {F : Type*} [Field F] {c : ℕ} (j : Fin c) (a : F) :
    ((MvPolynomial.X j - MvPolynomial.C a : FieldPoly c F)).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  decide

lemma eval_separator_at_point {F : Type*} [Field F] {c : ℕ}
    {E : Set (FieldPoly c F)} {S : Finset (FieldPoint c F)}
    (hS : IsolatedPoints E S)
    (s : FieldPoint c F → FieldPoly c F)
    (hs_eval : ∀ z ∈ S, MvPolynomial.eval z (s z) = 1 ∧
      ∀ y ∈ MvPolynomial.zeroLocus F (Ideal.span E), y ≠ z → MvPolynomial.eval y (s z) = 0)
    {z w : FieldPoint c F} (hz : z ∈ S) (hw : w ∈ S) :
    MvPolynomial.eval w (s z) = if z = w then 1 else 0 := by
  by_cases h : z = w
  · rw [if_pos h, h]
    exact (hs_eval w hw).1
  · rw [if_neg h]
    exact (hs_eval z hz).2 w (isolatedPoints_subset_zeroLocus hS hw) (Ne.symm h)

def jetValuePoly {F : Type*} [CommRing F] {c : ℕ} (s : FieldPoly c F) : FieldPoly c F :=
  (s * s + s * s + s * s) - (s * (s * s) + s * (s * s))

def jetDerivPoly {F : Type*} [CommRing F] {c : ℕ} (z : FieldPoint c F) (i : Fin c)
    (s : FieldPoly c F) : FieldPoly c F :=
  (MvPolynomial.X i - MvPolynomial.C (z i)) * (s * s)

lemma eval_jetValuePoly {F : Type*} [CommRing F] {c : ℕ} (s : FieldPoly c F) (w : FieldPoint c F) :
    MvPolynomial.eval w (jetValuePoly s) =
      let val := MvPolynomial.eval w s
      (val * val + val * val + val * val) - (val * (val * val) + val * (val * val)) := by
  simp only [jetValuePoly, map_sub, map_add, map_mul]

lemma eval_jetValuePoly_of_zero {F : Type*} [CommRing F] {c : ℕ} (s : FieldPoly c F) (w : FieldPoint c F)
    (hw : MvPolynomial.eval w s = 0) : MvPolynomial.eval w (jetValuePoly s) = 0 := by
  rw [eval_jetValuePoly, hw]
  ring

lemma eval_jetValuePoly_of_one {F : Type*} [CommRing F] {c : ℕ} (s : FieldPoly c F) (w : FieldPoint c F)
    (hw : MvPolynomial.eval w s = 1) : MvPolynomial.eval w (jetValuePoly s) = 1 := by
  rw [eval_jetValuePoly, hw]
  ring

lemma eval_pderiv_jetValuePoly {F : Type*} [CommRing F] {c : ℕ} (j : Fin c) (s : FieldPoly c F)
    (w : FieldPoint c F) (hw : MvPolynomial.eval w s = 0 ∨ MvPolynomial.eval w s = 1) :
    MvPolynomial.eval w (MvPolynomial.pderiv j (jetValuePoly s)) = 0 := by
  simp only [jetValuePoly, map_sub, map_add, MvPolynomial.pderiv_mul, map_mul]
  rcases hw with hw0 | hw1
  · rw [hw0]
    ring
  · rw [hw1]
    ring

lemma eval_jetDerivPoly {F : Type*} [CommRing F] {c : ℕ} (z : FieldPoint c F) (i : Fin c)
    (s : FieldPoly c F) (w : FieldPoint c F) :
    MvPolynomial.eval w (jetDerivPoly z i s) =
      (w i - z i) * (MvPolynomial.eval w s * MvPolynomial.eval w s) := by
  simp only [jetDerivPoly, map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]

lemma eval_jetDerivPoly_at_point {F : Type*} [CommRing F] {c : ℕ} (z : FieldPoint c F) (i : Fin c)
    (s : FieldPoly c F) (w : FieldPoint c F) (hw : w = z ∨ MvPolynomial.eval w s = 0) :
    MvPolynomial.eval w (jetDerivPoly z i s) = 0 := by
  rw [eval_jetDerivPoly]
  rcases hw with rfl | hw0
  · simp only [sub_self, zero_mul]
  · rw [hw0]
    ring

lemma eval_pderiv_jetDerivPoly {F : Type*} [Field F] {c : ℕ} (j : Fin c) (z : FieldPoint c F)
    (i : Fin c) (s : FieldPoly c F) (w : FieldPoint c F) :
    MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i s)) =
      (if i = j then (1 : F) else 0) * (MvPolynomial.eval w s * MvPolynomial.eval w s) +
      (w i - z i) * MvPolynomial.eval w (MvPolynomial.pderiv j (s * s)) := by
  simp only [jetDerivPoly, MvPolynomial.pderiv_mul, map_add, map_mul, map_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.pderiv_C, sub_zero]
  congr 1
  by_cases hij : i = j
  · subst hij
    rw [MvPolynomial.pderiv_X_self, map_one, if_pos rfl]
  · rw [MvPolynomial.pderiv_X_of_ne hij, map_zero, zero_mul, if_neg hij, zero_mul]

lemma eval_pderiv_jetDerivPoly_at_same {F : Type*} [Field F] {c : ℕ} (j : Fin c) (z : FieldPoint c F)
    (i : Fin c) (s : FieldPoly c F) (hs1 : MvPolynomial.eval z s = 1) :
    MvPolynomial.eval z (MvPolynomial.pderiv j (jetDerivPoly z i s)) = if i = j then 1 else 0 := by
  rw [eval_pderiv_jetDerivPoly, hs1]
  have hsub : z i - z i = 0 := sub_self (z i)
  rw [hsub, zero_mul, add_zero, mul_one, mul_one]

lemma eval_pderiv_jetDerivPoly_at_other {F : Type*} [Field F] {c : ℕ} (j : Fin c) (z : FieldPoint c F)
    (i : Fin c) (s : FieldPoly c F) (w : FieldPoint c F) (hs0 : MvPolynomial.eval w s = 0) :
    MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i s)) = 0 := by
  rw [eval_pderiv_jetDerivPoly, hs0]
  have hds2 : MvPolynomial.pderiv j (s * s) = MvPolynomial.pderiv j s * s + s * MvPolynomial.pderiv j s :=
    MvPolynomial.pderiv_mul
  rw [hds2]
  simp only [map_add, map_mul, hs0, mul_zero, zero_mul, add_zero]

lemma totalDegree_jetValuePoly {F : Type*} [CommRing F] {c : ℕ} (s : FieldPoly c F) :
    (jetValuePoly s).totalDegree ≤ 3 * s.totalDegree := by
  dsimp [jetValuePoly]
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  have hmul2 : (s * s).totalDegree ≤ 2 * s.totalDegree := by
    refine (MvPolynomial.totalDegree_mul s s).trans ?_
    linarith
  have hmul3 : (s * (s * s)).totalDegree ≤ 3 * s.totalDegree := by
    refine (MvPolynomial.totalDegree_mul s (s * s)).trans ?_
    linarith [hmul2]
  have h2 : (s * s + s * s + s * s).totalDegree ≤ 3 * s.totalDegree := by
    refine (MvPolynomial.totalDegree_add _ _).trans ?_
    refine (max_le ?_ hmul2).trans ?_
    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le hmul2 hmul2)
    · linarith
  have h3 : (s * (s * s) + s * (s * s)).totalDegree ≤ 3 * s.totalDegree := by
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le hmul3 hmul3)
  exact max_le h2 h3

lemma totalDegree_jetDerivPoly {F : Type*} [Field F] {c : ℕ} (z : FieldPoint c F) (i : Fin c)
    (s : FieldPoly c F) :
    (jetDerivPoly z i s).totalDegree ≤ 1 + 2 * s.totalDegree := by
  dsimp [jetDerivPoly]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hX := totalDegree_X_sub_C i (z i)
  have hs2 : (s * s).totalDegree ≤ 2 * s.totalDegree := by
    refine (MvPolynomial.totalDegree_mul s s).trans ?_
    linarith
  linarith

lemma jet_degree_bound_1 (c L d : ℕ) (hd : d ≤ c * (L - 1)) :
    3 * d ≤ (3 * c + 1) * L := by
  have hdL : d ≤ c * L := hd.trans (Nat.mul_le_mul_left c (Nat.sub_le L 1))
  have h1 : 3 * d ≤ (3 * c) * L := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left 3 hdL
  have h2 : (3 * c) * L ≤ (3 * c + 1) * L :=
    Nat.mul_le_mul_right L (Nat.le_succ (3 * c))
  exact h1.trans h2

lemma jet_degree_bound_2 (c L d : ℕ) (hL : 1 ≤ L) (hd : d ≤ c * (L - 1)) :
    1 + 2 * d ≤ (3 * c + 1) * L := by
  have hdL : d ≤ c * L := hd.trans (Nat.mul_le_mul_left c (Nat.sub_le L 1))
  have h1 : 1 + 2 * d ≤ L + 2 * (c * L) := by
    have : 2 * d ≤ 2 * (c * L) := Nat.mul_le_mul_left 2 hdL
    omega
  have h2 : L + 2 * (c * L) ≤ (3 * c + 1) * L := by
    rw [add_mul, one_mul, mul_assoc]
    have : 2 * c * L ≤ 3 * c * L := by
      refine Nat.mul_le_mul_right L ?_
      omega
    omega
  exact h1.trans h2

/-- `poly:interpolation.jets`, polynomial.tex:221–236. Grade impl once separators exist. -/
theorem poly_interpolation_jets (c : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : Type) [Field F] [IsAlgClosed F]
      (L : ℕ), 1 ≤ L → ∀ (E : Set (FieldPoly c F)),
      (∀ f ∈ E, f.totalDegree ≤ L) → ∀ (S : Finset (FieldPoint c F)),
      IsolatedPoints E S → ∀ (values : FieldPoint c F → F)
      (derivatives : FieldPoint c F → Fin c → F),
      ∃ g : FieldPoly c F, g.totalDegree ≤ C * L ∧
        ∀ z ∈ S, MvPolynomial.eval z g = values z ∧
          ∀ j, MvPolynomial.eval z (MvPolynomial.pderiv j g) = derivatives z j := by
  refine ⟨3 * c + 1, Nat.succ_pos _, fun F _ _ L hL E hE S hS values derivatives => ?_⟩
  by_cases hS_empty : S = ∅
  · refine ⟨0, by rw [MvPolynomial.totalDegree_zero]; exact Nat.zero_le _, fun z hz => ?_⟩
    subst hS_empty
    cases hz
  · have hsep := poly_interpolation_separators c L hL E hE S hS
    have hsep' : ∀ z : FieldPoint c F, ∃ s : FieldPoly c F,
        (z ∈ S → s.totalDegree ≤ c * (L - 1) ∧
         MvPolynomial.eval z s = 1 ∧
         ∀ y ∈ MvPolynomial.zeroLocus F (Ideal.span E), y ≠ z → MvPolynomial.eval y s = 0) := by
      intro z
      by_cases hz : z ∈ S
      · obtain ⟨s, h1, h2, h3⟩ := hsep z hz
        exact ⟨s, fun _ => ⟨h1, h2, h3⟩⟩
      · exact ⟨0, fun hz_in => (hz hz_in).elim⟩
    choose s hs using hsep'
    have hs_deg : ∀ z ∈ S, (s z).totalDegree ≤ c * (L - 1) := fun z hz => (hs z hz).1
    have hs_eval1 : ∀ z ∈ S, MvPolynomial.eval z (s z) = 1 := fun z hz => (hs z hz).2.1
    have hs_eval2 : ∀ z ∈ S, ∀ y ∈ MvPolynomial.zeroLocus F (Ideal.span E), y ≠ z → MvPolynomial.eval y (s z) = 0 :=
      fun z hz => (hs z hz).2.2
    have hs_point : ∀ {z w : FieldPoint c F}, z ∈ S → w ∈ S →
        MvPolynomial.eval w (s z) = if z = w then 1 else 0 :=
      fun hz hw => eval_separator_at_point hS s (fun z hz => ⟨hs_eval1 z hz, hs_eval2 z hz⟩) hz hw
    let g : FieldPoly c F := ∑ z ∈ S, (MvPolynomial.C (values z) * jetValuePoly (s z) +
      ∑ i : Fin c, MvPolynomial.C (derivatives z i) * jetDerivPoly z i (s z))
    have hdeg : g.totalDegree ≤ (3 * c + 1) * L := by
      refine (MvPolynomial.totalDegree_finsetSum_le (d := (3 * c + 1) * L) fun z hz => ?_)
      refine (MvPolynomial.totalDegree_add _ _).trans ?_
      have h1 : (MvPolynomial.C (values z) * jetValuePoly (s z)).totalDegree ≤ (3 * c + 1) * L := by
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_C, zero_add]
        refine (totalDegree_jetValuePoly (s z)).trans ?_
        exact jet_degree_bound_1 c L (s z).totalDegree (hs_deg z hz)
      have h2 : (∑ i : Fin c, MvPolynomial.C (derivatives z i) * jetDerivPoly z i (s z)).totalDegree ≤ (3 * c + 1) * L := by
        refine (MvPolynomial.totalDegree_finsetSum_le (d := (3 * c + 1) * L) fun i _ => ?_)
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_C, zero_add]
        refine (totalDegree_jetDerivPoly z i (s z)).trans ?_
        exact jet_degree_bound_2 c L (s z).totalDegree hL (hs_deg z hz)
      exact max_le h1 h2
    have heval : ∀ w ∈ S, MvPolynomial.eval w g = values w := by
      intro w hw
      simp only [g, map_sum, map_add, map_mul, MvPolynomial.eval_C]
      have hrew : (∑ z ∈ S, (values z * MvPolynomial.eval w (jetValuePoly (s z)) +
          ∑ i : Fin c, derivatives z i * MvPolynomial.eval w (jetDerivPoly z i (s z)))) =
          ∑ z ∈ S, (if z = w then values w else 0) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        have hsp := hs_point hz hw
        by_cases hzw : z = w
        · have hval : MvPolynomial.eval w (jetValuePoly (s z)) = 1 := by
            rw [hzw]
            rw [hzw, if_pos rfl] at hsp
            exact eval_jetValuePoly_of_one (s w) w hsp
          have hder : (∑ i : Fin c, derivatives z i * MvPolynomial.eval w (jetDerivPoly z i (s z))) = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            rw [eval_jetDerivPoly_at_point z i (s z) w (Or.inl hzw.symm), mul_zero]
          rw [if_pos hzw, hval, hder, mul_one, add_zero, hzw]
        · rw [if_neg hzw] at hsp
          have hval : MvPolynomial.eval w (jetValuePoly (s z)) = 0 :=
            eval_jetValuePoly_of_zero (s z) w hsp
          have hder : (∑ i : Fin c, derivatives z i * MvPolynomial.eval w (jetDerivPoly z i (s z))) = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            rw [eval_jetDerivPoly_at_point z i (s z) w (Or.inr hsp), mul_zero]
          rw [if_neg hzw, hval, hder, mul_zero, add_zero]
      rw [hrew, Finset.sum_ite_eq']
      simp only [hw, ↓reduceIte]
    have hpderiv : ∀ w ∈ S, ∀ j : Fin c, MvPolynomial.eval w (MvPolynomial.pderiv j g) = derivatives w j := by
      intro w hw j
      simp only [g, map_sum, map_add, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C]
      have hrew : (∑ z ∈ S, (values z * MvPolynomial.eval w (MvPolynomial.pderiv j (jetValuePoly (s z))) +
          ∑ i : Fin c, derivatives z i * MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i (s z))))) =
          ∑ z ∈ S, (if z = w then derivatives w j else 0) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        have hsp := hs_point hz hw
        have hval : MvPolynomial.eval w (MvPolynomial.pderiv j (jetValuePoly (s z))) = 0 := by
          apply eval_pderiv_jetValuePoly
          by_cases hzw' : z = w
          · rw [if_pos hzw'] at hsp; exact Or.inr hsp
          · rw [if_neg hzw'] at hsp; exact Or.inl hsp
        by_cases hzw : z = w
        · have hder : (∑ i : Fin c, derivatives z i * MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i (s z)))) =
              derivatives w j := by
            have hterm : ∀ i : Fin c, MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i (s z))) = if i = j then 1 else 0 := by
              intro i
              rw [hzw]
              have hspw : MvPolynomial.eval w (s w) = 1 := by
                have := hs_point (hzw ▸ hz) hw
                rwa [if_pos rfl] at this
              exact eval_pderiv_jetDerivPoly_at_same j w i (s w) hspw
            simp_rw [hterm, hzw]
            have hsum : (∑ i : Fin c, derivatives w i * (if i = j then (1 : F) else 0)) =
                ∑ i : Fin c, (if i = j then derivatives w j else 0) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases hij : i = j
              · subst hij; rw [if_pos rfl, if_pos rfl, mul_one]
              · rw [if_neg hij, if_neg hij, mul_zero]
            rw [hsum, Finset.sum_ite_eq']
            simp only [Finset.mem_univ, ↓reduceIte]
          rw [if_pos hzw, hval, mul_zero, zero_add, hder]
        · rw [if_neg hzw] at hsp
          have hder : (∑ i : Fin c, derivatives z i * MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i (s z)))) = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            rw [eval_pderiv_jetDerivPoly_at_other j z i (s z) w hsp, mul_zero]
          rw [if_neg hzw, hval, mul_zero, zero_add, hder]
      rw [hrew, Finset.sum_ite_eq']
      simp only [hw, ↓reduceIte]
    refine ⟨g, hdeg, fun w hw => ⟨heval w hw, hpderiv w hw⟩⟩

lemma mem_zeroLocus_span_finset {F : Type*} [Field F] {c : ℕ}
    (eqs : Finset (FieldPoly c F)) (x : FieldPoint c F) :
    x ∈ MvPolynomial.zeroLocus F (Ideal.span (eqs : Set (FieldPoly c F))) ↔
      ∀ f ∈ eqs, MvPolynomial.eval x f = 0 := by
  rw [MvPolynomial.zeroLocus_span]
  simp only [Finset.mem_coe, MvPolynomial.aeval_eq_eval]
  rfl


/-- `poly:interpolation.isolation`, polynomial.tex:238–242; profiles.tex:100–108. -/
theorem poly_interpolation_isolation {F : Type*} [Field F] [IsAlgClosed F]
    (c L : ℕ) (hL : 1 ≤ L) (E : Set (FieldPoly c F))
    (hE : ∀ f ∈ E, f.totalDegree ≤ L) (S : Finset (FieldPoint c F))
    (hS : IsolatedPoints E S) :
    ∃ equations : Finset (FieldPoly c F),
      (∀ f ∈ equations, f.totalDegree ≤ c * (L-1) + 1) ∧
      MvPolynomial.zeroLocus F (Ideal.span (equations : Set (FieldPoly c F))) =
        (S : Set (FieldPoint c F)) := by
  by_cases hS_empty : S = ∅
  · refine ⟨{1}, ?_, ?_⟩
    · intro f hf
      simp only [Finset.mem_singleton] at hf
      subst hf
      rw [MvPolynomial.totalDegree_one]
      exact Nat.zero_le _
    · simp only [hS_empty, Finset.coe_empty]
      rw [Finset.coe_singleton, Ideal.span_singleton_one, MvPolynomial.zeroLocus_top]
      rfl
  · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    have hsep := poly_interpolation_separators c L hL E hE S hS
    have hsep' : ∀ z : FieldPoint c F, ∃ s : FieldPoly c F,
        (z ∈ S → s.totalDegree ≤ c * (L - 1) ∧
         MvPolynomial.eval z s = 1 ∧
         ∀ y ∈ MvPolynomial.zeroLocus F (Ideal.span E), y ≠ z → MvPolynomial.eval y s = 0) := by
      intro z
      by_cases hz : z ∈ S
      · obtain ⟨s, h1, h2, h3⟩ := hsep z hz
        exact ⟨s, fun _ => ⟨h1, h2, h3⟩⟩
      · exact ⟨0, fun hz_in => (hz hz_in).elim⟩
    choose s hs using hsep'
    have hs_deg : ∀ z ∈ S, (s z).totalDegree ≤ c * (L - 1) := fun z hz => (hs z hz).1
    have hs_eval1 : ∀ z ∈ S, MvPolynomial.eval z (s z) = 1 := fun z hz => (hs z hz).2.1
    have hs_eval2 : ∀ z ∈ S, ∀ y ∈ MvPolynomial.zeroLocus F (Ideal.span E), y ≠ z → MvPolynomial.eval y (s z) = 0 :=
      fun z hz => (hs z hz).2.2
    have hs_point : ∀ {z w : FieldPoint c F}, z ∈ S → w ∈ S →
        MvPolynomial.eval w (s z) = if z = w then 1 else 0 :=
      fun hz hw => eval_separator_at_point hS s (fun z hz => ⟨hs_eval1 z hz, hs_eval2 z hz⟩) hz hw
    let eq0 : FieldPoly c F := 1 - ∑ z ∈ S, s z
    let eq_coords : Finset (FieldPoly c F) :=
      S.biUnion fun z => Finset.univ.image fun j => (MvPolynomial.X j - MvPolynomial.C (z j)) * s z
    let equations : Finset (FieldPoly c F) := insert eq0 eq_coords
    refine ⟨equations, ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · refine (MvPolynomial.totalDegree_sub _ _).trans ?_
        rw [MvPolynomial.totalDegree_one]
        have hsum : (∑ z ∈ S, s z).totalDegree ≤ c * (L - 1) :=
          MvPolynomial.totalDegree_finsetSum_le (fun z hz => hs_deg z hz)
        exact (max_le (Nat.zero_le _) hsum).trans (Nat.le_add_right _ 1)
      · obtain ⟨z, hz, hj⟩ := Finset.mem_biUnion.mp hf
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hj
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        have hX := totalDegree_X_sub_C j (z j)
        have hs := hs_deg z hz
        linarith
    · ext x
      rw [mem_zeroLocus_span_finset]
      constructor
      · intro hzeros
        have heq0 : MvPolynomial.eval x eq0 = 0 :=
          hzeros eq0 (Finset.mem_insert_self _ _)
        simp only [eq0, map_sub, map_one, map_sum] at heq0
        have hsum_one : ∑ z ∈ S, MvPolynomial.eval x (s z) = 1 := by
          linear_combination -heq0
        have hexists : ∃ z ∈ S, MvPolynomial.eval x (s z) ≠ 0 := by
          by_contra! hcontra
          have hzero : ∑ z ∈ S, MvPolynomial.eval x (s z) = 0 :=
            Finset.sum_eq_zero hcontra
          rw [hzero] at hsum_one
          exact one_ne_zero hsum_one.symm
        obtain ⟨z, hz, hzne⟩ := hexists
        have hcoords : ∀ j : Fin c, x j = z j := by
          intro j
          have hj_mem : (MvPolynomial.X j - MvPolynomial.C (z j)) * s z ∈ equations := by
            apply Finset.mem_insert_of_mem
            apply Finset.mem_biUnion.mpr
            exact ⟨z, hz, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
          have heval_j := hzeros _ hj_mem
          simp only [map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at heval_j
          cases mul_eq_zero.mp heval_j with
          | inl h => exact sub_eq_zero.mp h
          | inr h => exact False.elim (hzne h)
        have hx_eq : x = z := funext hcoords
        subst hx_eq
        exact hz
      · intro hx
        simp only [Finset.mem_coe] at hx
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · simp only [eq0, map_sub, map_one, map_sum]
          have hsum : ∑ z' ∈ S, MvPolynomial.eval x (s z') = 1 := by
            have hrew : (∑ z' ∈ S, MvPolynomial.eval x (s z')) =
                ∑ z' ∈ S, (if z' = x then (1 : F) else 0) := by
              refine Finset.sum_congr rfl fun z' hz' => ?_
              exact hs_point hz' hx
            rw [hrew, Finset.sum_ite_eq']
            simp only [hx, ↓reduceIte]
          rw [hsum, sub_self]
        · obtain ⟨z, hz, hj⟩ := Finset.mem_biUnion.mp hf
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hj
          simp only [map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
          by_cases hzx : z = x
          · subst hzx
            simp only [sub_self, zero_mul]
          · have hzero : MvPolynomial.eval x (s z) = 0 := by
              have := hs_point hz hx
              rw [if_neg hzx] at this
              exact this
            rw [hzero, mul_zero]

lemma union_jet_degree_bound_1 (c B d : ℕ) (hd : d ≤ (c + 1) * B) :
    3 * d ≤ (3 * c + 4) * B := by
  have h1 : 3 * d ≤ 3 * ((c + 1) * B) := Nat.mul_le_mul_left 3 hd
  have h2 : 3 * ((c + 1) * B) ≤ (3 * c + 4) * B := by
    rw [← mul_assoc]
    refine Nat.mul_le_mul_right B ?_
    omega
  exact h1.trans h2

lemma union_jet_degree_bound_2 (c B d : ℕ) (hB : 1 ≤ B) (hd : d ≤ (c + 1) * B) :
    1 + 2 * d ≤ (3 * c + 4) * B := by
  have h1 : 1 + 2 * d ≤ B + 2 * ((c + 1) * B) := by
    have : 2 * d ≤ 2 * ((c + 1) * B) := Nat.mul_le_mul_left 2 hd
    omega
  have h2 : B + 2 * ((c + 1) * B) ≤ (3 * c + 4) * B := by
    have : B + 2 * ((c + 1) * B) = (1 + 2 * (c + 1)) * B := by ring
    rw [this]
    refine Nat.mul_le_mul_right B ?_
    omega
  exact h1.trans h2

lemma jet_eval_eq {F : Type*} [Field F] {c : ℕ} (S : Finset (FieldPoint c F))
    (s : FieldPoint c F → FieldPoly c F)
    (hs_point : ∀ {z w : FieldPoint c F}, z ∈ S → w ∈ S → MvPolynomial.eval w (s z) = if z = w then 1 else 0)
    (values : FieldPoint c F → F)
    (derivatives : FieldPoint c F → Fin c → F)
    {w : FieldPoint c F} (hw : w ∈ S) :
    MvPolynomial.eval w (∑ z ∈ S, (MvPolynomial.C (values z) * jetValuePoly (s z) +
      ∑ i : Fin c, MvPolynomial.C (derivatives z i) * jetDerivPoly z i (s z))) = values w := by
  simp only [map_sum, map_add, map_mul, MvPolynomial.eval_C]
  have hrew : (∑ z ∈ S, (values z * MvPolynomial.eval w (jetValuePoly (s z)) +
      ∑ i : Fin c, derivatives z i * MvPolynomial.eval w (jetDerivPoly z i (s z)))) =
      ∑ z ∈ S, (if z = w then values w else 0) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    have hsp := hs_point hz hw
    by_cases hzw : z = w
    · have hval : MvPolynomial.eval w (jetValuePoly (s z)) = 1 := by
        rw [hzw]
        rw [hzw, if_pos rfl] at hsp
        exact eval_jetValuePoly_of_one (s w) w hsp
      have hder : (∑ i : Fin c, derivatives z i * MvPolynomial.eval w (jetDerivPoly z i (s z))) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [eval_jetDerivPoly_at_point z i (s z) w (Or.inl hzw.symm), mul_zero]
      rw [if_pos hzw, hval, hder, mul_one, add_zero, hzw]
    · rw [if_neg hzw] at hsp
      have hval : MvPolynomial.eval w (jetValuePoly (s z)) = 0 :=
        eval_jetValuePoly_of_zero (s z) w hsp
      have hder : (∑ i : Fin c, derivatives z i * MvPolynomial.eval w (jetDerivPoly z i (s z))) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [eval_jetDerivPoly_at_point z i (s z) w (Or.inr hsp), mul_zero]
      rw [if_neg hzw, hval, hder, mul_zero, add_zero]
  rw [hrew, Finset.sum_ite_eq']
  simp only [hw, ↓reduceIte]

lemma jet_pderiv_eq {F : Type*} [Field F] {c : ℕ} (S : Finset (FieldPoint c F))
    (s : FieldPoint c F → FieldPoly c F)
    (hs_point : ∀ {z w : FieldPoint c F}, z ∈ S → w ∈ S → MvPolynomial.eval w (s z) = if z = w then 1 else 0)
    (values : FieldPoint c F → F)
    (derivatives : FieldPoint c F → Fin c → F)
    {w : FieldPoint c F} (hw : w ∈ S) (j : Fin c) :
    MvPolynomial.eval w (MvPolynomial.pderiv j (∑ z ∈ S, (MvPolynomial.C (values z) * jetValuePoly (s z) +
      ∑ i : Fin c, MvPolynomial.C (derivatives z i) * jetDerivPoly z i (s z)))) = derivatives w j := by
  simp only [map_sum, map_add, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C]
  have hrew : (∑ z ∈ S, (values z * MvPolynomial.eval w (MvPolynomial.pderiv j (jetValuePoly (s z))) +
      ∑ i : Fin c, derivatives z i * MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i (s z))))) =
      ∑ z ∈ S, (if z = w then derivatives w j else 0) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    have hsp := hs_point hz hw
    have hval : MvPolynomial.eval w (MvPolynomial.pderiv j (jetValuePoly (s z))) = 0 := by
      apply eval_pderiv_jetValuePoly
      by_cases hzw' : z = w
      · rw [if_pos hzw'] at hsp; exact Or.inr hsp
      · rw [if_neg hzw'] at hsp; exact Or.inl hsp
    by_cases hzw : z = w
    · have hder : (∑ i : Fin c, derivatives z i * MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i (s z)))) =
          derivatives w j := by
        have hterm : ∀ i : Fin c, MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i (s z))) = if i = j then 1 else 0 := by
          intro i
          rw [hzw]
          have hspw : MvPolynomial.eval w (s w) = 1 := by
            have := hs_point (hzw ▸ hz) hw
            rwa [if_pos rfl] at this
          exact eval_pderiv_jetDerivPoly_at_same j w i (s w) hspw
        simp_rw [hterm, hzw]
        have hsum : (∑ i : Fin c, derivatives w i * (if i = j then (1 : F) else 0)) =
            ∑ i : Fin c, (if i = j then derivatives w j else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hij : i = j
          · subst hij; rw [if_pos rfl, if_pos rfl, mul_one]
          · rw [if_neg hij, if_neg hij, mul_zero]
        rw [hsum, Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ↓reduceIte]
      rw [if_pos hzw, hval, mul_zero, zero_add, hder]
    · rw [if_neg hzw] at hsp
      have hder : (∑ i : Fin c, derivatives z i * MvPolynomial.eval w (MvPolynomial.pderiv j (jetDerivPoly z i (s z)))) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [eval_pderiv_jetDerivPoly_at_other j z i (s z) w hsp, mul_zero]
      rw [if_neg hzw, hval, mul_zero, zero_add, hder]
  rw [hrew, Finset.sum_ite_eq']
  simp only [hw, ↓reduceIte]

/-- `poly:union-interpolation`, polynomial.tex:253–271; profiles.tex:405–411.
The finite lists may overlap. Grade impl: multiply normalized list separators. -/
theorem poly_union_interpolation (c : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : Type) [Field F] [IsAlgClosed F]
      (r : ℕ) (lists : Fin r → Finset (FieldPoint c F))
      (equations : Fin r → Set (FieldPoly c F)) (bounds : Fin r → ℕ),
      (∀ i, 1 ≤ bounds i ∧ (∀ f ∈ equations i, f.totalDegree ≤ bounds i) ∧
        IsolatedPoints (equations i) (lists i)) →
      ∀ (S : Finset (FieldPoint c F)),
      (∀ z, z ∈ S ↔ ∃ i, z ∈ lists i) →
      ∀ (values : FieldPoint c F → F) (derivatives : FieldPoint c F → Fin c → F),
      ∃ g : FieldPoly c F, g.totalDegree ≤ C * (∑ i, bounds i) ∧
        ∀ z ∈ S, MvPolynomial.eval z g = values z ∧
          ∀ j, MvPolynomial.eval z (MvPolynomial.pderiv j g) = derivatives z j := by
  refine ⟨3 * c + 4, Nat.succ_pos _, fun F _ _ r lists equations bounds h_hyp S hS values derivatives => ?_⟩
  by_cases hS_empty : S = ∅
  · refine ⟨0, by rw [MvPolynomial.totalDegree_zero]; exact Nat.zero_le _, fun z hz => ?_⟩
    subst hS_empty
    cases hz
  have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  obtain ⟨z0, hz0⟩ := hS_nonempty
  have hz0_in := (hS z0).mp hz0
  obtain ⟨i0, -⟩ := hz0_in
  have hB1 : 1 ≤ ∑ i, bounds i := by
    refine (h_hyp i0).1.trans ?_
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
  have hP_ex : ∀ (z : FieldPoint c F) (hz : z ∈ S) (i : Fin r), ∃ P : FieldPoly c F,
      P.totalDegree ≤ (c + 1) * bounds i ∧
      MvPolynomial.eval z P = 1 ∧
      ∀ w ∈ lists i, w ≠ z → MvPolynomial.eval w P = 0 := by
    intro z hz i
    have hb := (h_hyp i).1
    have he := (h_hyp i).2.1
    have hi := (h_hyp i).2.2
    by_cases hzin : z ∈ lists i
    · obtain ⟨sep, hsep_deg, hsep_eval, hsep_zero⟩ :=
        poly_interpolation_separators c (bounds i) hb (equations i) he (lists i) hi z hzin
      refine ⟨sep, ?_, hsep_eval, fun w hw hne => ?_⟩
      · have : c * (bounds i - 1) ≤ (c + 1) * bounds i := by
          refine (Nat.mul_le_mul_left c (Nat.sub_le _ _)).trans ?_
          rw [add_mul, one_mul]
          exact Nat.le_add_right _ _
        exact hsep_deg.trans this
      · exact hsep_zero w (isolatedPoints_subset_zeroLocus hi hw) hne
    · obtain ⟨eqs, heqs_deg, heqs_locus⟩ :=
        poly_interpolation_isolation c (bounds i) hb (equations i) he (lists i) hi
      have hznin_locus : z ∉ MvPolynomial.zeroLocus F (Ideal.span (eqs : Set (FieldPoly c F))) := by
        rw [heqs_locus]
        exact fun hz_mem => hzin (Finset.mem_coe.mp hz_mem)
      have hnot_all : ¬(∀ f ∈ eqs, MvPolynomial.eval z f = 0) := by
        intro hall
        apply hznin_locus
        rw [mem_zeroLocus_span_finset]
        exact hall
      push_neg at hnot_all
      obtain ⟨f, hf_in, hf_ne⟩ := hnot_all
      let P := MvPolynomial.C ((MvPolynomial.eval z f)⁻¹) * f
      refine ⟨P, ?_, ?_, ?_⟩
      · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_C, zero_add]
        have hf_deg := heqs_deg f hf_in
        have : c * (bounds i - 1) + 1 ≤ (c + 1) * bounds i := by
          have h1 : c * (bounds i - 1) ≤ c * bounds i :=
            Nat.mul_le_mul_left c (Nat.sub_le _ _)
          have h2 : c * (bounds i - 1) + 1 ≤ c * bounds i + bounds i :=
            Nat.add_le_add h1 hb
          rw [add_mul, one_mul]
          exact h2
        exact hf_deg.trans this
      · simp only [P, map_mul, MvPolynomial.eval_C]
        exact inv_mul_cancel₀ hf_ne
      · intro w hw hne
        have hw_locus : w ∈ MvPolynomial.zeroLocus F (Ideal.span (eqs : Set (FieldPoly c F))) := by
          rw [heqs_locus]
          exact Finset.mem_coe.mpr hw
        have hw_zero : MvPolynomial.eval w f = 0 := by
          rw [mem_zeroLocus_span_finset] at hw_locus
          exact hw_locus f hf_in
        simp only [P, map_mul, MvPolynomial.eval_C, hw_zero, mul_zero]
  have hP_all : ∀ z : FieldPoint c F, ∃ P : Fin r → FieldPoly c F,
      z ∈ S → ∀ i : Fin r, (P i).totalDegree ≤ (c + 1) * bounds i ∧
        MvPolynomial.eval z (P i) = 1 ∧
        ∀ w ∈ lists i, w ≠ z → MvPolynomial.eval w (P i) = 0 := by
    intro z
    by_cases hz : z ∈ S
    · have hzi : ∀ i : Fin r, ∃ P : FieldPoly c F,
          P.totalDegree ≤ (c + 1) * bounds i ∧
          MvPolynomial.eval z P = 1 ∧
          ∀ w ∈ lists i, w ≠ z → MvPolynomial.eval w P = 0 := fun i => hP_ex z hz i
      choose P hP using hzi
      exact ⟨P, fun _ i => hP i⟩
    · exact ⟨fun _ => 0, fun hz_in => (hz hz_in).elim⟩
  choose P hP using hP_all
  let s : FieldPoint c F → FieldPoly c F := fun z => ∏ i : Fin r, P z i
  have hs_eval1 : ∀ z ∈ S, MvPolynomial.eval z (s z) = 1 := by
    intro z hz
    simp only [s, map_prod]
    have : (∏ i : Fin r, MvPolynomial.eval z (P z i)) = ∏ i : Fin r, (1 : F) :=
      Finset.prod_congr rfl fun i _ => (hP z hz i).2.1
    rw [this, Finset.prod_const_one]
  have hs_eval0 : ∀ z ∈ S, ∀ w ∈ S, w ≠ z → MvPolynomial.eval w (s z) = 0 := by
    intro z hz w hw hne
    simp only [s, map_prod]
    rw [hS] at hw
    obtain ⟨k, hkw⟩ := hw
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    exact (hP z hz k).2.2 w hkw hne
  have hs_point : ∀ {z w : FieldPoint c F}, z ∈ S → w ∈ S →
      MvPolynomial.eval w (s z) = if z = w then 1 else 0 := by
    intro z w hz hw
    by_cases hzw : z = w
    · rw [hzw, if_pos rfl, hs_eval1 w hw]
    · rw [if_neg hzw, hs_eval0 z hz w hw (Ne.symm hzw)]
  have hs_deg : ∀ z ∈ S, (s z).totalDegree ≤ (c + 1) * ∑ i, bounds i := by
    intro z hz
    simp only [s]
    refine (MvPolynomial.totalDegree_finsetProd Finset.univ (fun i => P z i)).trans ?_
    have : (∑ i : Fin r, (P z i).totalDegree) ≤ ∑ i : Fin r, (c + 1) * bounds i :=
      Finset.sum_le_sum fun i _ => (hP z hz i).1
    refine this.trans ?_
    rw [← Finset.mul_sum]
  let g : FieldPoly c F := ∑ z ∈ S, (MvPolynomial.C (values z) * jetValuePoly (s z) +
    ∑ i : Fin c, MvPolynomial.C (derivatives z i) * jetDerivPoly z i (s z))
  have hdeg : g.totalDegree ≤ (3 * c + 4) * ∑ i, bounds i := by
    refine (MvPolynomial.totalDegree_finsetSum_le (d := (3 * c + 4) * ∑ i, bounds i) fun z hz => ?_)
    refine (MvPolynomial.totalDegree_add _ _).trans ?_
    have h1 : (MvPolynomial.C (values z) * jetValuePoly (s z)).totalDegree ≤ (3 * c + 4) * ∑ i, bounds i := by
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (totalDegree_jetValuePoly (s z)).trans ?_
      exact union_jet_degree_bound_1 c (∑ i, bounds i) (s z).totalDegree (hs_deg z hz)
    have h2 : (∑ i : Fin c, MvPolynomial.C (derivatives z i) * jetDerivPoly z i (s z)).totalDegree ≤ (3 * c + 4) * ∑ i, bounds i := by
      refine (MvPolynomial.totalDegree_finsetSum_le (d := (3 * c + 4) * ∑ i, bounds i) fun i _ => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (totalDegree_jetDerivPoly z i (s z)).trans ?_
      exact union_jet_degree_bound_2 c (∑ i, bounds i) (s z).totalDegree hB1 (hs_deg z hz)
    exact max_le h1 h2
  have heval : ∀ w ∈ S, MvPolynomial.eval w g = values w :=
    fun w hw => jet_eval_eq S s hs_point values derivatives hw
  have hpderiv : ∀ w ∈ S, ∀ j : Fin c, MvPolynomial.eval w (MvPolynomial.pderiv j g) = derivatives w j :=
    fun w hw j => jet_pderiv_eq S s hs_point values derivatives hw j
  exact ⟨g, hdeg, fun w hw => ⟨heval w hw, hpderiv w hw⟩⟩

end
end DistinctDistances.TrackA
