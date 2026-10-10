import DistinctDistances.TrackB.Degree
import DistinctDistances.TrackB.Recurrence
import DistinctDistances.TrackB.RefinementCore
import DistinctDistances.TrackB.Requests
import DistinctDistances.TrackB.MBRecAux
import DistinctDistances.TrackB.FlatIdentificationSupport
import Mathlib.Tactic.Positivity

namespace DistinctDistances.TrackB

set_option autoImplicit false
noncomputable section
open scoped BigOperators

def containedFlatCount {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (V : AffineVariety (skewDim e)) : ℕ := by
  classical
  exact (P.filter fun p => evaluationFlat C p ⊆ V.points).card

def HasSeparators {e : ℕ} (P : Finset (ProjectivePoint (e + e))) (L : ℝ) : Prop :=
  ∀ p ∈ P, ∃ (f : Poly (e + e)) (D : ℕ), 0 < D ∧ (D : ℝ) ≤ L ∧
    f.IsHomogeneous D ∧ MvPolynomial.aeval p.rep f ≠ 0 ∧
      ∀ q ∈ P, q ≠ p → MvPolynomial.aeval q.rep f = 0

def HasIsotropicCap {e : ℕ} (P : Finset (ProjectivePoint (e + e))) (L : ℝ) : Prop :=
  ∀ U : Submodule ℂ (Point (e + e)), IsMaximalIsotropic U →
    (((P : Set (ProjectivePoint (e + e))) ∩ (linearProjectivePlane U).points).ncard : ℝ) ≤ L

/-- true is specification (a); false is specification (b). -/
def AllowedCarrier {e : ℕ} (ambient : Bool) (A C0 : ℝ)
    (V : AffineVariety (skewDim e)) : Prop :=
  V.IsIrreducible ∧ V ≠ AffineVariety.whole ∧
    (ambient = true ∨ ∃ f : Poly (skewDim e), f ≠ 0 ∧ f ∈ V.ideal ∧
      (f.totalDegree : ℝ) ≤ C0 * A)

def normalizedFlatCount {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (A : ℝ)
    (V : AffineVariety (skewDim e)) (h : ℕ) : ℝ :=
  (containedFlatCount C P V : ℝ) / ((V.degree : ℝ) * A ^ h)

/-- Zero is inserted before the real supremum, as required for an empty carrier set. -/
def concentrationProfile {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (ambient : Bool) (A C0 : ℝ) (h : ℕ) : ℝ :=
  if h = e - 1 then
    if ambient = true then (P.card : ℝ) / A ^ h else 0
  else sSup (insert 0 {t | ∃ V : AffineVariety (skewDim e),
    AllowedCarrier ambient A C0 V ∧ V.dimension = flatDim e + h ∧
      t = normalizedFlatCount C P A V h})

structure ApproximateDescription {n : ℕ} (V : AffineVariety n) (c : ℕ) where
  equations : Fin c → Poly n
  upper : Fin c → ℕ
  positive : ∀ i, 0 < (equations i).totalDegree
  vanish : ∀ i, equations i ∈ V.ideal
  degree_bounds : ∀ i, (equations i).totalDegree ≤ upper i
  sorted : Monotone upper
  component : V.IsComponentOf (Ideal.span (Set.range equations))

def ApproximateDescription.degreeProduct {n c : ℕ} {V : AffineVariety n}
    (D : ApproximateDescription V c) : ℕ := ∏ i, D.upper i

def ApproximateDescription.prefixProduct {n c : ℕ} {V : AffineVariety n}
    (D : ApproximateDescription V c) (p : ℕ) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin c => i.val < p), D.upper i

def ApproximateDescription.prefixIdeal {n c : ℕ} {V : AffineVariety n}
    (D : ApproximateDescription V c) (p : ℕ) : Ideal (Poly n) :=
  Ideal.span (Set.range (fun i : Fin c => if i.val < p then D.equations i else 0))

/-- The geometric prefix property consumed by descent; no global CI assumption is added. -/
def ApproximateDescription.RegularPrefixes {n c : ℕ} {V : AffineVariety n}
    (D : ApproximateDescription V c) : Prop :=
  ∀ p ≤ c, ∀ W : AffineVariety n, W.IsComponentOf (D.prefixIdeal p) →
    V.Subvariety W → W.dimension + p = n

def ApproximateDescription.MinimalFirst {n c : ℕ} {V : AffineVariety n}
    (D : ApproximateDescription V c) (hc : 0 < c) : Prop :=
  D.upper ⟨0, hc⟩ = (D.equations ⟨0, hc⟩).totalDegree ∧
    ∀ q : Poly n, q ≠ 0 → q ∈ V.ideal → D.upper ⟨0, hc⟩ ≤ q.totalDegree

/-- B30, conc:description-product. The Walsh product estimate is an input, not reproved.
The conclusion exposes only the minimal equation and prefix properties needed by descent. -/
theorem refine_description {n c : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (hc : 0 < c) (hd : V.dimension + c = n) (D : ApproximateDescription V c)
    (Cdesc : ℝ) (hbudget : (D.degreeProduct : ℝ) ≤ Cdesc * (V.degree : ℝ)) :
    ∃ D' : ApproximateDescription V c, D'.RegularPrefixes ∧ D'.MinimalFirst hc ∧
      (∀ i, D'.upper i ≤ D.upper i) ∧
      (D'.degreeProduct : ℝ) ≤ Cdesc * (V.degree : ℝ) := by
  classical
  obtain ⟨g, hgbounds, hmin, hreg⟩ := replacement_equations_exists V hV hc hd
    D.equations D.upper D.sorted D.degree_bounds D.positive D.vanish D.component
  let i0 : Fin c := ⟨0, hc⟩
  let d : Fin c → ℕ := fun i => if i = i0 then (g i0).totalDegree else D.upper i
  have hupper : ∀ i, d i ≤ D.upper i := by
    intro i
    by_cases hi : i = i0
    · subst i
      simpa [d] using (hgbounds i0).2.2
    · simp [d, hi]
  have hdegrees : ∀ i, (g i).totalDegree ≤ d i := by
    intro i
    by_cases hi : i = i0
    · subst i
      simp [d]
    · simpa [d, hi] using (hgbounds i).2.2
  have hsort : Monotone d := by
    intro i j hij
    by_cases hi : i = i0
    · subst i
      by_cases hj : j = i0
      · subst j
        exact le_rfl
      · simpa [d, hj] using ((hgbounds i0).2.2).trans (D.sorted hij)
    · have hj : j ≠ i0 := by
        intro hj
        subst j
        have heq : i = i0 := by
          apply Fin.ext
          have hij' : i.val ≤ 0 := by change i.val ≤ 0 at hij; exact hij
          change i.val = 0
          omega
        exact hi heq
      simpa [d, hi, hj] using D.sorted hij
  have hgV : ∀ i, g i ∈ V.ideal := fun i => (hgbounds i).2.1
  have hnewle : Ideal.span (Set.range g) ≤ V.ideal := by
    apply Ideal.span_le.mpr
    rintro q ⟨i, rfl⟩
    exact hgV i
  letI : V.ideal.IsPrime := hV
  obtain ⟨P, hP, hPV⟩ := Ideal.exists_minimalPrimes_le hnewle
  let U : AffineVariety n := ⟨P, hP.isPrime.isRadical⟩
  have hUcomp : U.IsComponentOf (equationPrefixIdeal g c) := by
    change U.ideal ∈ (equationPrefixIdeal g c).minimalPrimes
    rw [equationPrefixIdeal_full]
    exact hP
  have hUdim := hreg c le_rfl U hUcomp hPV
  letI : P.IsPrime := hP.isPrime
  have hPI : P = V.ideal := Request.affine_prime_same_dimension_eq P V.ideal hPV
    (show U.dimension = V.dimension by omega) rfl
  have hgcomp : V.IsComponentOf (Ideal.span (Set.range g)) := by
    change V.ideal ∈ (Ideal.span (Set.range g)).minimalPrimes
    rw [← hPI]
    exact hP
  let D' : ApproximateDescription V c :=
    { equations := g
      upper := d
      positive := fun i => (hgbounds i).1
      vanish := hgV
      degree_bounds := hdegrees
      sorted := hsort
      component := hgcomp }
  refine ⟨D', hreg, ?_, hupper, ?_⟩
  · constructor
    · simp [D', d, i0]
    · exact hmin
  · have hprod : D'.degreeProduct ≤ D.degreeProduct :=
      Finset.prod_le_prod (fun i hi => hupper i)
    exact (Nat.cast_le.mpr hprod).trans hbudget

theorem containedFlatCount_le_one_of_dimension {e : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (P : Finset (ProjectivePoint (e + e))) (hP : ∀ p ∈ P, p ∈ affineParameters e)
    (V : AffineVariety (skewDim e)) (hV : V.IsIrreducible) (hdim : V.dimension = flatDim e) :
    containedFlatCount C P V ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpP, hpV⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqP, hqV⟩ := Finset.mem_filter.mp hq
  exact same_dimension_carrier_unique_parameter C he V hV hdim p q (hP p hpP) (hP q hqP) hpV hqV

/-- B29: each fixed-sample supremum is bounded, and its base endpoint is at most one. -/
theorem concentrationProfile_endpoints {e : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (P : Finset (ProjectivePoint (e + e))) (hP : ∀ p ∈ P, p ∈ affineParameters e)
    (ambient : Bool) (A C0 : ℝ) (hA : 1 ≤ A) (hC0 : 1 ≤ C0)
    (hcard : ambient = true → (P.card : ℝ) ≤ C0 * A ^ (e - 1)) :
    (∀ h < e - 1, 0 ≤ concentrationProfile C P ambient A C0 h ∧
      concentrationProfile C P ambient A C0 h ≤ (P.card : ℝ)) ∧
    concentrationProfile C P ambient A C0 0 ≤ 1 ∧
    (ambient = true → concentrationProfile C P ambient A C0 (e - 1) ≤ C0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Bounded supremum below the endpoint: nonnegativity and the sample bound.
    intro h hh
    have hne : h ≠ e - 1 := ne_of_lt hh
    have hprof : concentrationProfile C P ambient A C0 h =
        sSup (insert 0 {t | ∃ V : AffineVariety (skewDim e),
          AllowedCarrier ambient A C0 V ∧ V.dimension = flatDim e + h ∧
            t = normalizedFlatCount C P A V h}) := by
      unfold concentrationProfile
      rw [if_neg hne]
    rw [hprof]
    -- Every value in the set is at most the sample cardinality.
    have hdeg1 : ∀ V : AffineVariety (skewDim e), V.IsIrreducible →
        (1 : ℝ) ≤ V.degree := by
      intro V hV
      exact_mod_cast OAI.QuarticPowerFree.one_le_affineDegree V.ideal hV.ne_top
    have hle : ∀ V : AffineVariety (skewDim e), V.IsIrreducible →
        normalizedFlatCount C P A V h ≤ (P.card : ℝ) := by
      classical
      intro V hV
      have hd := hdeg1 V hV
      have hpow : 1 ≤ A ^ h := one_le_pow₀ hA
      have hden : 1 ≤ (V.degree : ℝ) * A ^ h := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hpow)]
      have hc : (containedFlatCount C P V : ℝ) ≤ (P.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hn : (0 : ℝ) ≤ (containedFlatCount C P V : ℝ) := by positivity
      unfold normalizedFlatCount
      calc
        (containedFlatCount C P V : ℝ) / ((V.degree : ℝ) * A ^ h) ≤
            (containedFlatCount C P V : ℝ) := by
          apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)).mpr
          nlinarith
        _ ≤ (P.card : ℝ) := hc
    have hbdd : BddAbove (insert (0 : ℝ) {t | ∃ V : AffineVariety (skewDim e),
        AllowedCarrier ambient A C0 V ∧ V.dimension = flatDim e + h ∧
          t = normalizedFlatCount C P A V h}) := by
      refine ⟨(P.card : ℝ), ?_⟩
      intro t ht
      rcases Set.mem_insert_iff.mp ht with rfl | ht
      · positivity
      · obtain ⟨V, hV, _, rfl⟩ := ht
        exact hle V hV.1
    constructor
    · exact le_csSup hbdd (Set.mem_insert 0 _)
    · refine csSup_le ⟨0, Set.mem_insert 0 _⟩ ?_
      intro t ht
      rcases Set.mem_insert_iff.mp ht with rfl | ht
      · positivity
      · obtain ⟨V, hV, _, rfl⟩ := ht
        exact hle V hV.1
  · have hne : (0 : ℕ) ≠ e - 1 := by omega
    unfold concentrationProfile
    rw [if_neg hne]
    refine csSup_le ⟨0, Set.mem_insert 0 _⟩ ?_
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · norm_num
    · obtain ⟨V, hV, hdim, rfl⟩ := ht
      have hc : (containedFlatCount C P V : ℝ) ≤ 1 := by
        exact_mod_cast containedFlatCount_le_one_of_dimension C he P hP V hV.1
          (by simpa only [Nat.add_zero] using hdim)
      have hdge : (1 : ℝ) ≤ V.degree := by
        exact_mod_cast OAI.QuarticPowerFree.one_le_affineDegree V.ideal hV.1.ne_top
      unfold normalizedFlatCount
      simp only [pow_zero, mul_one]
      apply (div_le_iff₀ (lt_of_lt_of_le one_pos hdge)).mpr
      simpa only [one_mul] using hc.trans hdge
  · -- Ambient endpoint from the cardinality hypothesis.
    intro hamb
    have hprof : concentrationProfile C P ambient A C0 (e - 1) =
        (P.card : ℝ) / A ^ (e - 1) := by
      simp [concentrationProfile, hamb]
    rw [hprof]
    have hApos : 0 < A := lt_of_lt_of_le one_pos hA
    have hpow : 0 < A ^ (e - 1) := pow_pos hApos _
    rw [div_le_iff₀ hpow]
    exact hcard hamb

namespace LowRecurrence

open scoped Classical

theorem profile_set_bddAbove {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (ambient : Bool) (A C0 : ℝ)
    (hA : 1 ≤ A) (i : ℕ) :
    BddAbove (insert (0 : ℝ) {t | ∃ V : AffineVariety (skewDim e),
      AllowedCarrier ambient A C0 V ∧ V.dimension = flatDim e + i ∧
        t = normalizedFlatCount C P A V i}) := by
  classical
  refine ⟨(P.card : ℝ), ?_⟩
  intro t ht
  rcases Set.mem_insert_iff.mp ht with rfl | ⟨V, hV, hdim, rfl⟩
  · positivity
  · have hdeg : (1 : ℝ) ≤ (V.degree : ℝ) := by
      exact_mod_cast V.one_le_degree hV.1.ne_top
    have hpow : 1 ≤ A ^ i := one_le_pow₀ hA
    have hden : 1 ≤ (V.degree : ℝ) * A ^ i := by nlinarith
    have hcount : (containedFlatCount C P V : ℝ) ≤ P.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hcount0 : (0 : ℝ) ≤ containedFlatCount C P V := by positivity
    unfold normalizedFlatCount
    apply (div_le_iff₀ (zero_lt_one.trans_le hden)).mpr
    nlinarith

theorem profile_nonnegative {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (ambient : Bool) (A C0 : ℝ)
    (hA : 1 ≤ A) (i : ℕ) (hi : i < e - 1) :
    0 ≤ concentrationProfile C P ambient A C0 i := by
  rw [concentrationProfile, if_neg (ne_of_lt hi)]
  exact le_csSup (profile_set_bddAbove C P ambient A C0 hA i) (Set.mem_insert 0 _)

theorem carrier_count_le_profile {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (ambient : Bool) (A C0 : ℝ)
    (hA : 1 ≤ A) (i : ℕ) (hi : i < e - 1) (W : AffineVariety (skewDim e))
    (hW : AllowedCarrier ambient A C0 W) (hdim : W.dimension = flatDim e + i) :
    (containedFlatCount C P W : ℝ) ≤
      concentrationProfile C P ambient A C0 i * (W.degree : ℝ) * A ^ i := by
  have hnorm : normalizedFlatCount C P A W i ≤ concentrationProfile C P ambient A C0 i := by
    rw [concentrationProfile, if_neg (ne_of_lt hi)]
    exact le_csSup (profile_set_bddAbove C P ambient A C0 hA i)
      (Set.mem_insert_of_mem 0 ⟨W, hW, hdim, rfl⟩)
  have hdeg : (0 : ℝ) < (W.degree : ℝ) := by
    have h := W.one_le_degree hW.1.ne_top
    exact zero_lt_one.trans_le (by exact_mod_cast h)
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hden : 0 < (W.degree : ℝ) * A ^ i := mul_pos hdeg (pow_pos hApos _)
  unfold normalizedFlatCount at hnorm
  simpa [mul_assoc] using (div_le_iff₀ hden).mp hnorm

theorem allowed_of_subvariety {e : ℕ} (ambient : Bool) (A C0 : ℝ)
    (V W : AffineVariety (skewDim e)) (hV : AllowedCarrier ambient A C0 V)
    (hW : W.IsIrreducible) (hsub : W.Subvariety V) : AllowedCarrier ambient A C0 W := by
  refine ⟨hW, ?_, ?_⟩
  · intro hwhole
    have hbot : V.ideal ≤ ⊥ := by
      simpa only [AffineVariety.Subvariety, hwhole, AffineVariety.whole, AffineVariety.ofIdeal,
        Ideal.radical_bot_of_isReduced] using hsub
    apply hV.2.1
    apply AffineVariety.ext
    change V.ideal = (⊥ : Ideal (Poly (skewDim e))).radical
    rw [Ideal.radical_bot_of_isReduced]
    exact le_antisymm hbot bot_le
  · rcases hV.2.2 with hamb | ⟨f, hf, hfV, hfdeg⟩
    · exact Or.inl hamb
    · exact Or.inr ⟨f, hf, hsub hfV, hfdeg⟩

theorem count_le_component_sum {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (hP : ∀ p ∈ P, p ∈ affineParameters e)
    (V : AffineVariety (skewDim e)) :
    containedFlatCount C P V ≤ ∑ W : V.Component, containedFlatCount C P W.variety := by
  classical
  let F (W : V.Component) := P.filter (fun p => evaluationFlat C p ⊆ W.variety.points)
  have hsub : P.filter (fun p => evaluationFlat C p ⊆ V.points) ⊆ Finset.univ.biUnion F := by
    intro p hp
    obtain ⟨hpP, hpV⟩ := Finset.mem_filter.mp hp
    obtain ⟨W, hW⟩ := MBRec.contained_in_component V (evaluationFlat C p)
      (MBRec.evaluationFlat_closure_irreducible C p (hP p hpP)) hpV
    exact Finset.mem_biUnion.mpr ⟨W, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hpP, hW⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

theorem exceptional_count_le {e : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (P : Finset (ProjectivePoint (e + e))) (hP : ∀ p ∈ P, p ∈ affineParameters e)
    (ambient : Bool) (A C0 : ℝ) (hA : 1 ≤ A) (V : AffineVariety (skewDim e))
    (h : ℕ) (hh : 1 ≤ h) (hhend : h + 2 ≤ e)
    (hV : AllowedCarrier ambient A C0 V) (hdim : V.dimension = flatDim e + h)
    (H : Poly (skewDim e)) (hH : H ∉ V.ideal) :
    (containedFlatCount C P (V.cut H) : ℝ) ≤
      concentrationProfile C P ambient A C0 (h - 1) *
        (H.totalDegree : ℝ) * (V.degree : ℝ) * A ^ (h - 1) := by
  classical
  let X := V.cut H
  letI : V.ideal.IsPrime := hV.1
  have hcomp (W : X.Component) : W.variety.IsComponentOf (V.ideal ⊔ Ideal.span {H}) := by
    have hw := W.property
    change W.val ∈ (V.ideal ⊔ Ideal.span {H}).radical.minimalPrimes at hw
    rw [Ideal.radical_minimalPrimes] at hw
    exact hw
  have hd : V.dimension = (flatDim e + (h - 1)) + 1 := by omega
  have hWdim (W : X.Component) : W.variety.dimension = flatDim e + (h - 1) := by
    letI : W.val.IsPrime := W.property.isPrime
    exact OAI.QuarticPowerFree.proper_cut_component_dimension V.ideal W.val H hH (hcomp W) hd
  have hsub (W : X.Component) : W.variety.Subvariety V :=
    le_sup_left.trans (hcomp W).le
  have hallowed (W : X.Component) : AllowedCarrier ambient A C0 W.variety :=
    allowed_of_subvariety ambient A C0 V W.variety hV W.property.isPrime (hsub W)
  have hdegree : (∑ W : X.Component, W.variety.degree) ≤ (H.totalDegree : ℚ) * V.degree := by
    exact OAI.QuarticPowerFree.proper_cut_sum_affineDegree_le V.ideal H hH hd
      (fun W : X.Component => W.val) (fun W => hcomp W)
      (fun W Z heq => Subtype.ext heq)
  have hdegreeR : (∑ W : X.Component, (W.variety.degree : ℝ)) ≤
      (H.totalDegree : ℝ) * (V.degree : ℝ) := by exact_mod_cast hdegree
  have hR : 0 ≤ concentrationProfile C P ambient A C0 (h - 1) :=
    profile_nonnegative C P ambient A C0 hA (h - 1) (by omega)
  have hpow : 0 ≤ A ^ (h - 1) := pow_nonneg (zero_le_one.trans hA) _
  calc
    (containedFlatCount C P X : ℝ) ≤ ∑ W : X.Component, (containedFlatCount C P W.variety : ℝ) := by
      exact_mod_cast count_le_component_sum C P hP X
    _ ≤ ∑ W : X.Component,
        concentrationProfile C P ambient A C0 (h - 1) * (W.variety.degree : ℝ) * A ^ (h - 1) := by
      apply Finset.sum_le_sum
      intro W hW
      exact carrier_count_le_profile C P ambient A C0 hA (h - 1) (by omega)
        W.variety (hallowed W) (hWdim W)
    _ = concentrationProfile C P ambient A C0 (h - 1) *
        (∑ W : X.Component, (W.variety.degree : ℝ)) * A ^ (h - 1) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ concentrationProfile C P ambient A C0 (h - 1) *
        ((H.totalDegree : ℝ) * (V.degree : ℝ)) * A ^ (h - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdegreeR hR) hpow
    _ = _ := by ring

theorem ruling_parameter_count_le {e h M : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (P : Finset (ProjectivePoint (e + e))) (A C0 Bsep : ℝ)
    (hA : 1 ≤ A) (hC0 : 1 ≤ C0) (hBsep : 1 ≤ Bsep)
    (hcap : HasIsotropicCap P (C0 * A ^ (e - 2)))
    (hseparator : ∀ (Y : ProjectiveVariety (e + e)) (a : ℕ), Y.IsIrreducible →
      Y.dimension = a → a ≤ e + e →
      ((P.filter fun p => p ∈ Y.points).card : ℝ) ≤ Bsep * (Y.degree : ℝ) * A ^ a)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (j : ℕ)
    (hh : 1 ≤ h) (hhend : h + 2 ≤ e) (hdim : V.dimension = flatDim e + h)
    (R : IsRulingIncidence C V Γ H a j M)
    (hY : (parameterClosure C Γ H).IsIrreducible) :
    ((P.filter fun p => p ∈ parameterImage C Γ H).card : ℝ) ≤
      (Bsep * M + C0) * (V.degree : ℝ) * A ^ h := by
  classical
  have hsubset : P.filter (fun p => p ∈ parameterImage C Γ H) ⊆
      P.filter (fun p => p ∈ (parameterClosure C Γ H).points) := by
    intro p hp
    obtain ⟨hpP, hpimage⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpP, ProjectiveVariety.subset_closure _ hpimage⟩
  have hcount : ((P.filter fun p => p ∈ parameterImage C Γ H).card : ℝ) ≤
      (P.filter fun p => p ∈ (parameterClosure C Γ H).points).card := by
    exact_mod_cast Finset.card_le_card hsubset
  obtain ⟨hYdim, hYdegree, hline⟩ := degree_comparison C V Γ H a he ⟨hh, hhend⟩ hdim R
  have hdegree : (1 : ℝ) ≤ (V.degree : ℝ) := by
    exact_mod_cast V.one_le_degree R.variety_irreducible.ne_top
  have hpow : 0 ≤ A ^ h := pow_nonneg (zero_le_one.trans hA) _
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hC00 : 0 ≤ C0 := zero_le_one.trans hC0
  have hBsep0 : 0 ≤ Bsep := zero_le_one.trans hBsep
  by_cases hj : j = 0
  · have hYdim' : (parameterClosure C Γ H).dimension = h := by simpa [hj] using hYdim
    have hse := hseparator (parameterClosure C Γ H) h hY hYdim' (by omega)
    have hYdegreeR : ((parameterClosure C Γ H).degree : ℝ) ≤ (M : ℝ) * (V.degree : ℝ) := by
      exact_mod_cast hYdegree
    calc
      _ ≤ ((P.filter fun p => p ∈ (parameterClosure C Γ H).points).card : ℝ) := hcount
      _ ≤ Bsep * ((parameterClosure C Γ H).degree : ℝ) * A ^ h := hse
      _ ≤ Bsep * ((M : ℝ) * (V.degree : ℝ)) * A ^ h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYdegreeR hBsep0) hpow
      _ = (Bsep * M) * (V.degree : ℝ) * A ^ h := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC00) (zero_le_one.trans hdegree)) hpow
  · have hj1 : j = 1 := by have := R.fiber_cases; omega
    obtain ⟨hh', L, hL, hplane⟩ := hline hj1
    have hset : ((P.filter fun p => p ∈ (parameterClosure C Γ H).points) : Set (ProjectivePoint (e + e))) =
        (P : Set (ProjectivePoint (e + e))) ∩ (linearProjectivePlane L).points := by
      ext p
      simp [hplane]
    have hcap' := hcap L hL
    rw [← hset, Set.ncard_coe_finset, ← hh'] at hcap'
    calc
      _ ≤ ((P.filter fun p => p ∈ (parameterClosure C Γ H).points).card : ℝ) := hcount
      _ ≤ C0 * A ^ h := hcap'
      _ ≤ C0 * (V.degree : ℝ) * A ^ h := by
        have hscale := mul_le_mul_of_nonneg_left hdegree (mul_nonneg hC00 hpow)
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hBsep0 hM))
          (zero_le_one.trans hdegree)) hpow

theorem count_le_cut_add_rulings {e M : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (hP : ∀ p ∈ P, p ∈ affineParameters e)
    (V : AffineVariety (skewDim e)) (L : ℝ) (F : MBRec.ControlledRulings C V M L) :
    containedFlatCount C P V ≤ containedFlatCount C P (V.cut F.exceptional) +
      ∑ i, (P.filter fun p => p ∈ parameterImage C (F.incidences i) F.exceptional).card := by
  classical
  let G (i : Fin F.size) := P.filter fun p => p ∈ parameterImage C (F.incidences i) F.exceptional
  have hsub : P.filter (fun p => evaluationFlat C p ⊆ V.points) ⊆
      P.filter (fun p => evaluationFlat C p ⊆ (V.cut F.exceptional).points) ∪ Finset.univ.biUnion G := by
    intro p hp
    obtain ⟨hpP, hpV⟩ := Finset.mem_filter.mp hp
    rcases F.coverage p (hP p hpP) hpV with hcut | ⟨i, hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpP, hcut⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hpP, hi⟩⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))

theorem normalized_count_le_of_rulings {e h M : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (P : Finset (ProjectivePoint (e + e))) (hP : ∀ p ∈ P, p ∈ affineParameters e)
    (ambient : Bool) (A C0 K Bsep : ℝ) (hA : 1 ≤ A) (hC0 : 1 ≤ C0)
    (hK : 0 < K) (hBsep : 1 ≤ Bsep)
    (hcap : HasIsotropicCap P (C0 * A ^ (e - 2)))
    (hseparator : ∀ (Y : ProjectiveVariety (e + e)) (a : ℕ), Y.IsIrreducible →
      Y.dimension = a → a ≤ e + e →
      ((P.filter fun p => p ∈ Y.points).card : ℝ) ≤ Bsep * (Y.degree : ℝ) * A ^ a)
    (V : AffineVariety (skewDim e)) (hV : AllowedCarrier ambient A C0 V)
    (hh : 1 ≤ h) (hhend : h + 2 ≤ e) (hdim : V.dimension = flatDim e + h)
    (F : MBRec.ControlledRulings C V M ((M : ℝ) * K * A)) :
    normalizedFlatCount C P A V h ≤
      (M : ℝ) * (Bsep * M + C0) + (M : ℝ) * K * concentrationProfile C P ambient A C0 (h - 1) := by
  classical
  let R := concentrationProfile C P ambient A C0 (h - 1)
  have hR : 0 ≤ R := profile_nonnegative C P ambient A C0 hA (h - 1) (by omega)
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hVdegree : (1 : ℝ) ≤ (V.degree : ℝ) := by exact_mod_cast V.one_le_degree hV.1.ne_top
  have hden : 0 < (V.degree : ℝ) * A ^ h :=
    mul_pos (zero_lt_one.trans_le hVdegree) (pow_pos hApos _)
  have hpow : A ^ (h - 1) * A = A ^ h := by
    rw [← pow_succ]
    congr 1
    omega
  have hcut : (containedFlatCount C P (V.cut F.exceptional) : ℝ) ≤
      (M : ℝ) * K * R * ((V.degree : ℝ) * A ^ h) := by
    have hbase := exceptional_count_le C he P hP ambient A C0 hA V h hh hhend hV hdim
      F.exceptional F.section_nonzero
    apply hbase.trans
    calc
      R * (F.exceptional.totalDegree : ℝ) * (V.degree : ℝ) * A ^ (h - 1) =
          (R * (V.degree : ℝ) * A ^ (h - 1)) * (F.exceptional.totalDegree : ℝ) := by ring
      _ ≤ (R * (V.degree : ℝ) * A ^ (h - 1)) * ((M : ℝ) * K * A) :=
        mul_le_mul_of_nonneg_left F.section_degree (by positivity)
      _ = (M : ℝ) * K * R * ((V.degree : ℝ) * A ^ h) := by rw [← hpow]; ring
  have hrepresented : (∑ i, ((P.filter fun p => p ∈ parameterImage C (F.incidences i) F.exceptional).card : ℝ)) ≤
      (M : ℝ) * (Bsep * M + C0) * (V.degree : ℝ) * A ^ h := by
    have hi (i : Fin F.size) := ruling_parameter_count_le C he P A C0 Bsep hA hC0 hBsep
      hcap hseparator V (F.incidences i) F.exceptional (F.charts i) (F.fiber_dimensions i)
      hh hhend hdim (F.properties i) (F.parameter_irreducible i)
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin F.size))) => hi i)
    have hsize : (F.size : ℝ) ≤ M := by exact_mod_cast F.size_bound
    calc
      _ ≤ ∑ _i : Fin F.size, (Bsep * M + C0) * (V.degree : ℝ) * A ^ h := hs
      _ = (F.size : ℝ) * ((Bsep * M + C0) * (V.degree : ℝ) * A ^ h) := by simp
      _ ≤ (M : ℝ) * ((Bsep * M + C0) * (V.degree : ℝ) * A ^ h) :=
        mul_le_mul_of_nonneg_right hsize (by positivity)
      _ = _ := by ring
  have hcoverage : (containedFlatCount C P V : ℝ) ≤
      (containedFlatCount C P (V.cut F.exceptional) : ℝ) +
        ∑ i, ((P.filter fun p => p ∈ parameterImage C (F.incidences i) F.exceptional).card : ℝ) := by
    exact_mod_cast count_le_cut_add_rulings C P hP V ((M : ℝ) * K * A) F
  unfold normalizedFlatCount
  apply (div_le_iff₀ hden).mpr
  exact hcoverage.trans ((add_le_add hcut hrepresented).trans_eq (by dsimp [R]; ring))

end LowRecurrence

/-- B31, conc:low-recurrence. Cdesc is fixed dimensionally by the Walsh producer. -/
theorem low_recurrence (e : ℕ) (he : 3 ≤ e) (C0 Cdesc : ℝ)
    (hC0 : 1 ≤ C0) (hCdesc : 1 ≤ Cdesc) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (C : SkewCoordinates e) (A K : ℝ), 1 ≤ A → 0 < K →
      ∀ (P : Finset (ProjectivePoint (e + e))) (ambient : Bool),
        (∀ p ∈ P, p ∈ affineParameters e) → HasSeparators P (C0 * A) →
        HasIsotropicCap P (C0 * A ^ (e - 2)) →
        ∀ (V : AffineVariety (skewDim e)) (h c : ℕ),
          AllowedCarrier ambient A C0 V → 1 ≤ h → h + 2 ≤ e →
          V.dimension = flatDim e + h → V.dimension + c = skewDim e →
          ∀ D : ApproximateDescription V c,
            (D.degreeProduct : ℝ) ≤ Cdesc * (V.degree : ℝ) →
            (∀ i, (D.upper i : ℝ) ≤ K * A) →
            normalizedFlatCount C P A V h ≤
              B * (1 + K * concentrationProfile C P ambient A C0 (h - 1)) := by
  classical
  obtain ⟨M, hM, hproduce⟩ :
      ∃ M : ℕ, 1 ≤ M ∧ ∀ (C : SkewCoordinates e) (A K : ℝ), 1 ≤ A → 0 < K →
        ∀ (V : AffineVariety (skewDim e)) (h c : ℕ), V.IsIrreducible →
          1 ≤ h → h + 2 ≤ e → V.dimension = flatDim e + h → V.dimension + c = skewDim e →
          ∀ D : ApproximateDescription V c,
            (D.degreeProduct : ℝ) ≤ Cdesc * (V.degree : ℝ) →
            (∀ i, (D.upper i : ℝ) ≤ K * A) →
            Nonempty (MBRec.ControlledRulings C V M ((M : ℝ) * K * A)) := by
    obtain ⟨Creg, hCreg, hregular⟩ := MBRec.regular_equations_from_components (skewDim e)
    obtain ⟨M, hM, hgeometry⟩ :
        ∃ M : ℕ, 1 ≤ M ∧ ∀ (C : SkewCoordinates e) (V : AffineVariety (skewDim e))
          (h c L : ℕ), V.IsIrreducible → 1 ≤ h → h + 2 ≤ e →
          V.dimension = flatDim e + h → V.dimension + c = skewDim e → 1 ≤ L →
          ∀ (g : Fin c → Poly (skewDim e)) (H0 : Poly (skewDim e)),
            (∀ i, g i ∈ V.ideal ∧ (g i).totalDegree ≤ Creg * L) →
            H0 ∉ V.ideal → H0.totalDegree ≤ Creg * L →
            (∀ x ∈ V.points, MvPolynomial.eval x H0 ≠ 0 →
              V.IsSmoothAt x ∧ V.tangentSpace x = ⨅ i : Fin c, LinearMap.ker (differential (g i) x)) →
            Nonempty (MBRec.ControlledRulings C V M ((M : ℝ) * (L : ℝ))) := by
      obtain ⟨Broot, hBroot, hroot⟩ :
          ∃ Broot : ℕ, 2 ≤ Broot ∧
            ∀ (C : SkewCoordinates e) (V : AffineVariety (skewDim e)) [V.ideal.IsPrime]
              (c D : ℕ), V.IsIrreducible → V.dimension + c = skewDim e →
              ∀ (g : Fin c → Poly (skewDim e)) (first : Fin c),
                (∀ i, g i ∈ V.ideal ∧ (g i).totalDegree ≤ D) →
                ∀ H0 : Poly (skewDim e), H0 ∉ V.ideal → H0.totalDegree ≤ D →
                  (∀ z ∈ V.points, MvPolynomial.eval z H0 ≠ 0 →
                    V.IsSmoothAt z ∧ V.tangentSpace z = ⨅ i : Fin c, LinearMap.ker (differential (g i) z)) →
                  ∀ a b : Fin e, MBRec.normalPolynomial C (g first) a b ∉ V.ideal →
                    ((∃ l i j, (MBRec.residualParameterPolynomial (MBRec.normalPolynomial C (g first))
                      (MBRec.normalPolynomial C (g l)) a b i j).map (MBRec.coordinateMap V) ≠ 0) ∨
                    (∃ i j l, (MBRec.firstHorizontalTest C (MBRec.normalPolynomial C (g first)) a b i j l).map
                      (MBRec.coordinateMap V) ≠ 0)) →
                    Nonempty (MBRec.ControlledChart C V a Broot ((Broot : ℝ) * (D : ℝ))) := by
        exact MBRec.nonzero_combined_chart e
      let B := max 2 Broot
      let N := (e + 1) * B + 1
      let M := N * (Creg + 1)
      have hB2 : 2 ≤ B := Nat.le_max_left _ _
      have hBrootB : Broot ≤ B := Nat.le_max_right _ _
      have hBpos : 1 ≤ B := by omega
      have hN : 1 ≤ N := by dsimp [N]; omega
      have hM : 1 ≤ M := Nat.mul_le_mul hN (show 1 ≤ Creg + 1 by omega)
      refine ⟨M, hM, ?_⟩
      intro C V h c L hV hh hhend hdim hcodim hL g H0 hg hH0 hH0deg hregular
      letI : V.ideal.IsPrime := hV
      have hchoose : skewDim e = flatDim e + (e - 1) := by
        simp only [skewDim, flatDim]
        rw [show e = (e - 1) + 1 by omega, Nat.choose_succ_succ']
        simp [Nat.choose_one_right, Nat.add_comm]
      have hc : 0 < c := by omega
      let first : Fin c := ⟨0,hc⟩
      let D := Creg * L
      obtain ⟨i0,j0,hproper⟩ := MBRec.first_normal_polynomial_nonzero C V hV hcodim g first H0 hH0 hregular
      have hwiden2 (a : Fin e) (F : MBRec.ControlledChart C V a 2 (2 * (D : ℝ))) :
          MBRec.ControlledChart C V a B ((B : ℝ) * (D : ℝ)) :=
        F.mono hB2 hBpos (mul_le_mul_of_nonneg_right (by exact_mod_cast hB2) (Nat.cast_nonneg D))
      have hwidenroot (a : Fin e) (F : MBRec.ControlledChart C V a Broot ((Broot : ℝ) * (D : ℝ))) :
          MBRec.ControlledChart C V a B ((B : ℝ) * (D : ℝ)) :=
        F.mono hBrootB hBpos (mul_le_mul_of_nonneg_right (by exact_mod_cast hBrootB) (Nat.cast_nonneg D))
      have hcharts : ∀ a : Fin e, Nonempty (MBRec.ControlledChart C V a B ((B : ℝ) * (D : ℝ))) := by
        intro a
        by_cases hrow : ∀ b, MBRec.normalPolynomial C (g first) a b ∈ V.ideal
        · obtain ⟨F⟩ := MBRec.empty_controlled_chart C V hV (g first) (hg first).1 (hg first).2
            H0 hH0 hH0deg a i0 j0 hproper hrow
          exact ⟨hwiden2 a F⟩
        · push_neg at hrow
          obtain ⟨b,hb⟩ := hrow
          by_cases hres : ∀ l i j, (MBRec.residualParameterPolynomial (MBRec.normalPolynomial C (g first))
              (MBRec.normalPolynomial C (g l)) a b i j).map (MBRec.coordinateMap V) = 0
          · by_cases hfirst : ∀ i j l, (MBRec.firstHorizontalTest C (MBRec.normalPolynomial C (g first)) a b i j l).map
                (MBRec.coordinateMap V) = 0
            · obtain ⟨F⟩ := MBRec.all_zero_controlled_chart C V hV hcodim g first hg H0 hH0 hH0deg hregular a b hb hres hfirst
              exact ⟨hwiden2 a F⟩
            · push_neg at hfirst
              obtain ⟨F⟩ := hroot C V c D hV hcodim g first hg H0 hH0 hH0deg hregular a b hb (Or.inr hfirst)
              exact ⟨hwidenroot a F⟩
          · push_neg at hres
            obtain ⟨F⟩ := hroot C V c D hV hcodim g first hg H0 hH0 hH0deg hregular a b hb (Or.inl hres)
            exact ⟨hwidenroot a F⟩
      let F (a : Fin e) := Classical.choice (hcharts a)
      obtain ⟨R⟩ := MBRec.controlled_chart_union C V hV B ((B : ℝ) * (D : ℝ)) F
      have hNM : N ≤ M := by
        calc
          N = N * 1 := (Nat.mul_one _).symm
          _ ≤ N * (Creg + 1) := Nat.mul_le_mul_left _ (by omega)
      have hBN : e * B ≤ N := by dsimp [N]; nlinarith
      have hcoefNat : e * B * Creg ≤ M :=
        (Nat.mul_le_mul_right Creg hBN).trans (Nat.mul_le_mul_left N (Nat.le_add_right _ _))
      have hcoef : (e : ℝ) * (B : ℝ) * (Creg : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcoefNat
      have hbudget : (e : ℝ) * ((B : ℝ) * (D : ℝ)) ≤ (M : ℝ) * (L : ℝ) := by
        simpa only [D,Nat.cast_mul,mul_assoc] using mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg L)
      exact ⟨R.widen hNM hM hbudget⟩
    refine ⟨M, hM, ?_⟩
    intro C A K hA hK V h c hV hh hhend hdim hcodim D hbudget hsmall
    have hchoose : skewDim e = flatDim e + (e - 1) := by
      simp only [skewDim, flatDim]
      rw [show e = (e - 1) + 1 by omega, Nat.choose_succ_succ']
      simp [Nat.choose_one_right, Nat.add_comm]
    have hc : 0 < c := by omega
    let last : Fin c := ⟨c - 1, by omega⟩
    let L := D.upper last
    have hL : 1 ≤ L := by
      have hpos := D.positive last
      have hbound := D.degree_bounds last
      change 1 ≤ D.upper last
      omega
    have hdefined : AffineFamily.ComponentsDefinedInDegree {V} L := by
      refine ⟨Set.range D.equations, ?_, ?_⟩
      · rintro f ⟨i, rfl⟩
        exact (D.degree_bounds i).trans (D.sorted (by change i.val ≤ last.val; dsimp [last]; omega))
      · intro W hW
        have hWV : W = V := Finset.mem_singleton.mp hW
        subst W
        exact D.component
    obtain ⟨g, H0, hg, hH0, hH0deg, hsmooth⟩ := hregular V c L hV hcodim hL hdefined
    obtain ⟨F⟩ := hgeometry C V h c L hV hh hhend hdim hcodim hL g H0 hg hH0 hH0deg hsmooth
    refine ⟨F.mono ?_⟩
    have hreal : (L : ℝ) ≤ K * A := hsmall last
    have hmul := mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    simpa only [mul_assoc] using hmul
  obtain ⟨Bsep, hBsep, hsepcount⟩ := MBRec.projective_separator_count (e + e) C0 hC0
  let B := max 1 (max ((M : ℝ) * (Bsep * M + C0)) (M : ℝ))
  have hBone : 1 ≤ B := le_max_left _ _
  have hconstant : (M : ℝ) * (Bsep * M + C0) ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hMB : (M : ℝ) ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hBone, ?_⟩
  intro C A K hA hK P ambient hP hsep hcap V h c hV hh hhend hdim hcodim D hbudget hsmall
  obtain ⟨F⟩ := hproduce C A K hA hK V h c hV.1 hh hhend hdim hcodim D hbudget hsmall
  have hsepP : ∀ p ∈ P, ∃ (f : Poly (e + e)) (d : ℕ), (d : ℝ) ≤ C0 * A ∧
      f.IsHomogeneous d ∧ MvPolynomial.aeval p.rep f ≠ 0 ∧
        ∀ q ∈ P, q ≠ p → MvPolynomial.aeval q.rep f = 0 := by
    intro p hp
    obtain ⟨f, d, hdpos, hdbound, hhom, hnonzero, hzero⟩ := hsep p hp
    exact ⟨f, d, hdbound, hhom, hnonzero, hzero⟩
  have hmain := LowRecurrence.normalized_count_le_of_rulings C he P hP ambient A C0 K Bsep
    hA hC0 hK hBsep hcap (hsepcount A hA P hsepP) V hV hh hhend hdim F
  have hR : 0 ≤ concentrationProfile C P ambient A C0 (h - 1) :=
    LowRecurrence.profile_nonnegative C P ambient A C0 hA (h - 1) (by omega)
  calc
    normalizedFlatCount C P A V h ≤ (M : ℝ) * (Bsep * M + C0) +
        (M : ℝ) * K * concentrationProfile C P ambient A C0 (h - 1) := hmain
    _ ≤ B + B * K * concentrationProfile C P ambient A C0 (h - 1) :=
      add_le_add hconstant (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMB hK.le) hR)
    _ = B * (1 + K * concentrationProfile C P ambient A C0 (h - 1)) := by ring

/-- B32, concentration.tex:1109. The shared Hilbert degree of the empty-prefix carrier. -/
theorem whole_degree (n : ℕ) :
    (AffineVariety.whole : AffineVariety n).degree = 1 := by
  have hp : (AffineVariety.whole : AffineVariety n).hilbertPolynomial =
      Polynomial.preHilbertPoly ℚ n 0 := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [(AffineVariety.whole : AffineVariety n).hilbert_eventually] with D hD
    rw [← hD, Polynomial.preHilbertPoly_eq_choose_add_sub ℚ n (Nat.zero_le (D+n))]
    simp only [Nat.sub_zero]
    congr 1
    let H := OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) D
    letI := OAI.QuarticPowerFree.totalSpace_finite (n := n) (K := ℂ) D
    let q : H →ₗ[ℂ] (Poly n ⧸ (⊥ : Ideal (Poly n))) :=
      (Ideal.Quotient.mkₐ ℂ ⊥).toLinearMap.comp H.subtype
    have hker : LinearMap.ker q = ⊥ := by
      ext f
      change Ideal.Quotient.mk ⊥ f.val = 0 ↔ f = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simp
    have hrange : LinearMap.range q = H.map (Ideal.Quotient.mkₐ ℂ ⊥).toLinearMap := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have h := q.finrank_range_add_finrank_ker
    rw [hker, finrank_bot, add_zero, hrange] at h
    have hi : (AffineVariety.whole : AffineVariety n).ideal = ⊥ :=
      Ideal.radical_bot_of_isReduced
    change Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace D).map
      (Ideal.Quotient.mkₐ ℂ (AffineVariety.whole : AffineVariety n).ideal).toLinearMap) = _
    rw [hi]
    exact h.trans (OAI.QuarticPowerFree.totalSpace_finrank D)
  change ((AffineVariety.whole : AffineVariety n).hilbertPolynomial.natDegree.factorial : ℚ) *
      (AffineVariety.whole : AffineVariety n).hilbertPolynomial.coeff
        (AffineVariety.whole : AffineVariety n).hilbertPolynomial.natDegree = 1
  rw [hp, Polynomial.natDegree_preHilbertPoly, Polynomial.coeff_preHilbertPoly_self]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n)

namespace ApproximateDescription
variable {n c : ℕ} {V : AffineVariety n} (D : ApproximateDescription V c)

theorem prefixIdeal_zero : D.prefixIdeal 0 = ⊥ := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    simp
  · exact bot_le

theorem prefixIdeal_succ (p : ℕ) (hp : p < c) :
    D.prefixIdeal (p + 1) = D.prefixIdeal p ⊔ Ideal.span {D.equations ⟨p, hp⟩} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    change (if i.val < p + 1 then D.equations i else 0) ∈ _
    by_cases hi : i.val < p
    · rw [if_pos (show i.val < p + 1 by omega)]
      apply (show D.prefixIdeal p ≤ D.prefixIdeal p ⊔
        Ideal.span {D.equations ⟨p, hp⟩} from le_sup_left)
      apply Ideal.subset_span
      exact ⟨i, by simp [hi]⟩
    · by_cases his : i.val < p + 1
      · have hieq : i = ⟨p, hp⟩ := by apply Fin.ext; change i.val = p; omega
        subst i
        simpa using (le_sup_right : Ideal.span {D.equations ⟨p, hp⟩} ≤
          D.prefixIdeal p ⊔ Ideal.span {D.equations ⟨p, hp⟩})
          (Ideal.subset_span (Set.mem_singleton _))
      · simp [his]
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro f ⟨i, rfl⟩
      by_cases hi : i.val < p
      · apply Ideal.subset_span
        exact ⟨i, by simp [hi, show i.val < p + 1 by omega]⟩
      · simp [hi]
    · apply Ideal.span_le.mpr
      rintro f rfl
      apply Ideal.subset_span
      exact ⟨⟨p, hp⟩, by simp⟩

theorem prefixProduct_succ (p : ℕ) (hp : p < c) :
    D.prefixProduct (p + 1) = D.upper ⟨p, hp⟩ * D.prefixProduct p := by
  classical
  have hs : Finset.univ.filter (fun i : Fin c => i.val < p + 1) =
      insert ⟨p, hp⟩ (Finset.univ.filter (fun i : Fin c => i.val < p)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases h : i.val < p
      · exact Or.inr h
      · exact Or.inl (by apply Fin.ext; change i.val = p; omega)
    · rintro (rfl | hi)
      · change p < p + 1
        omega
      · omega
  unfold prefixProduct
  rw [hs, Finset.prod_insert]
  simp

theorem prefixIdeal_le_variety (p : ℕ) : D.prefixIdeal p ≤ V.ideal := by
  apply Ideal.span_le.mpr
  rintro f ⟨i, rfl⟩
  change (if i.val < p then D.equations i else 0) ∈ _
  split
  · exact D.vanish i
  · exact Ideal.zero_mem _

/-- B32, concentration.tex:1100–1107. A component of a regular prefix containing V
has the product degree bound. Descend to a component of the preceding prefix, then
apply OAI proper-cut Bezout; minimality makes the current component a proper-cut component. -/
theorem prefix_component_degree_le (hprefix : D.RegularPrefixes)
    (p : ℕ) (hp : p ≤ c) (W : AffineVariety n)
    (hW : W.IsComponentOf (D.prefixIdeal p)) (hVW : V.Subvariety W) :
    W.degree ≤ (D.prefixProduct p : ℚ) := by
  classical
  induction p generalizing W with
  | zero =>
      have hWI : W.ideal = ⊥ := by
        have hW' : W.ideal ∈ (⊥ : Ideal (Poly n)).minimalPrimes := by
          simpa [AffineVariety.IsComponentOf, prefixIdeal_zero D] using hW
        simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hW'
      have hwhole : W = AffineVariety.whole := by
        apply AffineVariety.ext
        rw [hWI]
        exact Ideal.radical_bot_of_isReduced.symm
      rw [hwhole, whole_degree]
      simp [prefixProduct]
  | succ p ih =>
      have hpc : p < c := by omega
      let f := D.equations ⟨p, hpc⟩
      letI : W.ideal.IsPrime := hW.isPrime
      have hprev_le : D.prefixIdeal p ≤ W.ideal := by
        rw [prefixIdeal_succ D p hpc] at hW
        exact le_sup_left.trans hW.le
      obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hprev_le
      let U : AffineVariety n := ⟨Q, hQ.isPrime.isRadical⟩
      have hVU : V.Subvariety U := hQW.trans hVW
      have hUcomp : U.IsComponentOf (D.prefixIdeal p) := hQ
      have hUdim := hprefix p (by omega) U hUcomp hVU
      have hWdim := hprefix (p + 1) hp W hW hVW
      have hfW : f ∈ W.ideal := by
        apply hW.le
        rw [prefixIdeal_succ D p hpc]
        exact (show Ideal.span {f} ≤ D.prefixIdeal p ⊔ Ideal.span {f} from le_sup_right)
          (Ideal.subset_span (Set.mem_singleton _))
      have hsup_le : Q ⊔ Ideal.span {f} ≤ W.ideal :=
        sup_le hQW (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfW))
      have hpre_sup : D.prefixIdeal (p + 1) ≤ Q ⊔ Ideal.span {f} := by
        rw [prefixIdeal_succ D p hpc]
        exact sup_le_sup hQ.le le_rfl
      have hWcut : W.ideal ∈ (Q ⊔ Ideal.span {f}).minimalPrimes := by
        refine ⟨⟨hW.isPrime, hsup_le⟩, ?_⟩
        intro J hJ hJW
        exact hW.2 ⟨hJ.1, hpre_sup.trans hJ.2⟩ hJW
      have hfU : f ∉ Q := by
        intro hfQ
        have hQover : D.prefixIdeal (p + 1) ≤ Q :=
          hpre_sup.trans (sup_le le_rfl
            (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfQ)))
        have hWQ : W.ideal ≤ Q := hW.2 ⟨hQ.isPrime, hQover⟩ hQW
        have heq : W = U := AffineVariety.ext (le_antisymm hWQ hQW)
        rw [heq] at hWdim
        omega
      letI : Q.IsPrime := hQ.isPrime
      have hdim : OAI.QuarticPowerFree.affineDimension Q = (n - (p + 1)) + 1 := by
        change U.dimension = _
        omega
      have hdeg := OAI.QuarticPowerFree.proper_cut_sum_affineDegree_le Q f hfU hdim
        (fun _ : Fin 1 => W.ideal) (fun _ => hWcut) (by intro i j h; exact Subsingleton.elim _ _)
      have hdegree : W.degree ≤ (f.totalDegree : ℚ) * U.degree := by
        simpa [AffineVariety.degree, U] using hdeg
      have hUdegree := ih (by omega) U hUcomp hVU
      have hfdeg : (f.totalDegree : ℚ) ≤ (D.upper ⟨p, hpc⟩ : ℚ) :=
        Nat.cast_le.mpr (D.degree_bounds ⟨p, hpc⟩)
      have hUnonneg : (0 : ℚ) ≤ U.degree :=
        le_trans (by norm_num) (AffineVariety.one_le_degree U hQ.isPrime.ne_top)
      calc
        W.degree ≤ (f.totalDegree : ℚ) * U.degree := hdegree
        _ ≤ (D.upper ⟨p, hpc⟩ : ℚ) * U.degree :=
          mul_le_mul_of_nonneg_right hfdeg hUnonneg
        _ ≤ (D.upper ⟨p, hpc⟩ : ℚ) * (D.prefixProduct p : ℚ) :=
          mul_le_mul_of_nonneg_left hUdegree (Nat.cast_nonneg _)
        _ = (D.prefixProduct (p + 1) : ℚ) := by
          rw [prefixProduct_succ D p hpc, Nat.cast_mul]

end ApproximateDescription

/-- B32, concentration.tex:1111–1114. The actual finite prefix/tail product yields
the carrier degree gain, including the empty prefix. -/
theorem prefix_tail_degree_gain {n c : ℕ} {V : AffineVariety n}
    (D : ApproximateDescription V c) (p : ℕ) (hp : p ≤ c)
    (t budget : ℝ) (ht : 0 ≤ t) (hlarge : ∀ i : Fin c, p ≤ i.val → t ≤ D.upper i)
    (W : AffineVariety n) (hdegree : (W.degree : ℝ) ≤ D.prefixProduct p)
    (hbudget : (D.degreeProduct : ℝ) ≤ budget * (V.degree : ℝ)) :
    (W.degree : ℝ) * t ^ (c - p) ≤ budget * (V.degree : ℝ) := by
  classical
  let T := Finset.univ.filter (fun i : Fin c => ¬ i.val < p)
  have hcard : T.card = c - p := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin c))) (fun i : Fin c => i.val < p)
    rw [Fin.card_filter_val_lt] at hsum
    simp only [Finset.card_univ, Fintype.card_fin, Nat.min_eq_right hp] at hsum
    change (Finset.univ.filter (fun i : Fin c => ¬ i.val < p)).card = _
    omega
  have htail : t ^ (c - p) ≤ ∏ i ∈ T, (D.upper i : ℝ) := by
    have hprod : (∏ _i ∈ T, t) ≤ ∏ i ∈ T, (D.upper i : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact ht
      · intro i hi
        exact hlarge i (by have := (Finset.mem_filter.mp hi).2; omega)
    simpa only [Finset.prod_const, hcard] using hprod
  have hsplit : (D.prefixProduct p : ℝ) * (∏ i ∈ T, (D.upper i : ℝ)) =
      (D.degreeProduct : ℝ) := by
    simp only [ApproximateDescription.prefixProduct, ApproximateDescription.degreeProduct,
      Nat.cast_prod, T]
    exact Finset.prod_filter_mul_prod_filter_not _ _ _
  calc
    (W.degree : ℝ) * t ^ (c - p) ≤
        (D.prefixProduct p : ℝ) * t ^ (c - p) :=
      mul_le_mul_of_nonneg_right hdegree (pow_nonneg ht _)
    _ ≤ (D.prefixProduct p : ℝ) * ∏ i ∈ T, (D.upper i : ℝ) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
    _ = (D.degreeProduct : ℝ) := hsplit
    _ ≤ budget * (V.degree : ℝ) := hbudget

/-- B32, conc:degree-comparison: one real carrier of the small prefix, with degree gain.
The allowedness conclusion explicitly handles the ambient endpoint only in case (a). -/
theorem large_description_carrier {e h c : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (hh : 1 ≤ h ∧ h + 2 ≤ e) (hc : 0 < c)
    (V : AffineVariety (skewDim e)) (hd : V.dimension = flatDim e + h)
    (hcodim : V.dimension + c = skewDim e)
    (ambient : Bool) (A C0 K Cdesc : ℝ) (hA : 1 ≤ A) (hC0 : 1 ≤ C0) (hK : C0 < K)
    (hallowed : AllowedCarrier ambient A C0 V)
    (D : ApproximateDescription V c) (hprefix : D.RegularPrefixes) (hfirst : D.MinimalFirst hc)
    (hbudget : (D.degreeProduct : ℝ) ≤ Cdesc * (V.degree : ℝ))
    (p : ℕ) (hp : p < c)
    (hsmall : ∀ i : Fin c, i.val < p → (D.upper i : ℝ) ≤ K * A)
    (hlarge : ∀ i : Fin c, p ≤ i.val → K * A < (D.upper i : ℝ)) :
    ∃ W : AffineVariety (skewDim e), W.IsIrreducible ∧ V.Subvariety W ∧
      W.dimension = flatDim e + (e - 1 - p) ∧
      (W.degree : ℝ) ≤ (D.prefixProduct p : ℝ) ∧
      (W.degree : ℝ) * (K * A) ^ (c - p) ≤ Cdesc * (V.degree : ℝ) ∧
      ((e - 1 - p < e - 1 ∧ AllowedCarrier ambient A C0 W) ∨
        (ambient = true ∧ p = 0 ∧ W = AffineVariety.whole)) := by
  classical
  have hV : V.IsIrreducible := hallowed.1
  letI : V.ideal.IsPrime := hV
  obtain ⟨Q, hQ, hQV⟩ := Ideal.exists_minimalPrimes_le (D.prefixIdeal_le_variety p)
  let W : AffineVariety (skewDim e) := ⟨Q, hQ.isPrime.isRadical⟩
  have hVW : V.Subvariety W := hQV
  have hWcomp : W.IsComponentOf (D.prefixIdeal p) := hQ
  have hdim := hprefix p hp.le W hWcomp hVW
  have hchoose : skewDim e = flatDim e + (e - 1) := by
    simp only [skewDim, flatDim]
    rw [show e = (e - 1) + 1 by omega, Nat.choose_succ_succ']
    simp [Nat.choose_one_right, Nat.add_comm]
  have hWdim : W.dimension = flatDim e + (e - 1 - p) := by omega
  have hdeg : (W.degree : ℝ) ≤ (D.prefixProduct p : ℝ) := by
    exact_mod_cast D.prefix_component_degree_le hprefix p hp.le W hWcomp hVW
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) (hC0.trans hK.le)
  have hKA : 0 ≤ K * A := mul_nonneg hKpos.le (le_trans (by norm_num) hA)
  have hgain : (W.degree : ℝ) * (K * A) ^ (c - p) ≤ Cdesc * (V.degree : ℝ) :=
    prefix_tail_degree_gain D p hp.le (K * A) Cdesc hKA
      (fun i hi => (hlarge i hi).le) W hdeg hbudget
  refine ⟨W, hQ.isPrime, hVW, hWdim, hdeg, hgain, ?_⟩
  have hfirst_nonzero : D.equations ⟨0, hc⟩ ≠ 0 := by
    intro hz
    have hpos := D.positive ⟨0, hc⟩
    rw [hz, MvPolynomial.totalDegree_zero] at hpos
    omega
  have hfirst_bound : ambient = false → (D.upper ⟨0, hc⟩ : ℝ) ≤ C0 * A := by
    intro hamb
    obtain ⟨q, hq, hqV, hqdeg⟩ := hallowed.2.2.resolve_left (by simp [hamb])
    exact le_trans (Nat.cast_le.mpr (hfirst.2 q hq hqV)) hqdeg
  have hzero_ambient : p = 0 → ambient = true := by
    intro hp0
    cases hamb : ambient
    · have hmin := hfirst_bound hamb
      have hlarge0 := hlarge ⟨0, hc⟩ (by omega)
      have hmul : C0 * A < K * A := mul_lt_mul_of_pos_right hK (lt_of_lt_of_le (by norm_num) hA)
      linarith
    · rfl
  by_cases hp0 : p = 0
  · right
    refine ⟨hzero_ambient hp0, hp0, ?_⟩
    apply AffineVariety.ext
    have hQI : Q = ⊥ := by
      have hQ' : Q ∈ (⊥ : Ideal (Poly (skewDim e))).minimalPrimes := by
        simpa [hp0, D.prefixIdeal_zero] using hQ
      simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hQ'
    change Q = (AffineVariety.whole : AffineVariety (skewDim e)).ideal
    rw [hQI]
    exact Ideal.radical_bot_of_isReduced.symm
  · left
    have hppos : 0 < p := Nat.pos_of_ne_zero hp0
    have hfQ : D.equations ⟨0, hc⟩ ∈ Q := by
      apply hQ.le
      apply Ideal.subset_span
      exact ⟨⟨0, hc⟩, by simp [hppos]⟩
    have hWwhole : W ≠ AffineVariety.whole := by
      intro hwhole
      have hbot : Q = ⊥ := by
        change W.ideal = ⊥
        rw [hwhole]
        exact Ideal.radical_bot_of_isReduced
      rw [hbot] at hfQ
      exact hfirst_nonzero (by simpa using hfQ)
    refine ⟨by omega, hQ.isPrime, hWwhole, ?_⟩
    cases hamb : ambient
    · right
      refine ⟨D.equations ⟨0, hc⟩, hfirst_nonzero, hfQ, ?_⟩
      have heq := congrArg (fun x : ℕ => (x : ℝ)) hfirst.1
      rw [← heq]
      exact hfirst_bound hamb
    · exact Or.inl rfl

namespace HighCarrier

/-- Direct reuse of OAI degree positivity for the recurrence denominators. -/
theorem irreducible_degree_one_le {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible) :
    (1 : ℝ) ≤ (V.degree : ℝ) := by
  exact_mod_cast OAI.QuarticPowerFree.one_le_affineDegree V.ideal hV.ne_top

theorem contained_count_le {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (V W : AffineVariety (skewDim e))
    (hsub : V.Subvariety W) : containedFlatCount C P V ≤ containedFlatCount C P W := by
  classical
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpP, hpV⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨hpP, ?_⟩
  exact hpV.trans ((AffineVariety.subvariety_iff_points_subset V W).mp hsub)

theorem normalized_count_le_card {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (A : ℝ) (hA : 1 ≤ A)
    (V : AffineVariety (skewDim e)) (hV : V.IsIrreducible) (i : ℕ) :
    normalizedFlatCount C P A V i ≤ (P.card : ℝ) := by
  classical
  have hd := irreducible_degree_one_le V hV
  have hpow : 1 ≤ A ^ i := one_le_pow₀ hA
  have hden : 1 ≤ (V.degree : ℝ) * A ^ i := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hpow)]
  have hc : (containedFlatCount C P V : ℝ) ≤ (P.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hn : (0 : ℝ) ≤ (containedFlatCount C P V : ℝ) := by positivity
  unfold normalizedFlatCount
  calc
    (containedFlatCount C P V : ℝ) / ((V.degree : ℝ) * A ^ i) ≤
        (containedFlatCount C P V : ℝ) := by
      apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)).mpr
      nlinarith
    _ ≤ (P.card : ℝ) := hc

/-- A fixed-sample profile includes each allowed carrier. Degree positivity
bounds its actual supremum by the sample cardinality, in both specifications. -/
theorem profile_contains_carrier {e : ℕ} (C : SkewCoordinates e)
    (P : Finset (ProjectivePoint (e + e))) (ambient : Bool) (A C0 : ℝ) (hA : 1 ≤ A)
    (W : AffineVariety (skewDim e)) (i : ℕ) (hi : i < e - 1)
    (hW : AllowedCarrier ambient A C0 W) (hWdim : W.dimension = flatDim e + i) :
    normalizedFlatCount C P A W i ≤ concentrationProfile C P ambient A C0 i := by
  let S : Set ℝ := insert 0 {t | ∃ V : AffineVariety (skewDim e),
    AllowedCarrier ambient A C0 V ∧ V.dimension = flatDim e + i ∧
      t = normalizedFlatCount C P A V i}
  have hbound : BddAbove S := by
    refine ⟨(P.card : ℝ), ?_⟩
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · positivity
    · obtain ⟨V, hV, _, rfl⟩ := ht
      exact normalized_count_le_card C P A hA V hV.1 i
  have hmem : normalizedFlatCount C P A W i ∈ S :=
    Set.mem_insert_of_mem 0 ⟨W, hW, hWdim, rfl⟩
  simpa only [concentrationProfile, if_neg (ne_of_lt hi), S] using le_csSup hbound hmem

end HighCarrier

/-- B32, conc:high-recurrence, counting on the actual enlarged carrier. -/
theorem high_recurrence_of_carrier {e h i : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (P : Finset (ProjectivePoint (e + e))) (ambient : Bool) (A C0 K Cdesc : ℝ)
    (hA : 1 ≤ A) (hC0 : 1 ≤ C0) (hK : 0 < K) (hCdesc : 1 ≤ Cdesc)
    (V W : AffineVariety (skewDim e)) (hh : 1 ≤ h ∧ h + 2 ≤ e) (hi : h < i)
    (hallowed : AllowedCarrier ambient A C0 V) (hsub : V.Subvariety W)
    (hVdim : V.dimension = flatDim e + h) (hWdim : W.dimension = flatDim e + i)
    (hWallowed : (i < e - 1 ∧ AllowedCarrier ambient A C0 W) ∨
      (ambient = true ∧ i = e - 1 ∧ W = AffineVariety.whole))
    (hgain : (W.degree : ℝ) * (K * A) ^ (i - h) ≤ Cdesc * (V.degree : ℝ)) :
    normalizedFlatCount C P A V h ≤
      Cdesc * concentrationProfile C P ambient A C0 i / K ^ (i - h) := by
  classical
  have hVdeg := HighCarrier.irreducible_degree_one_le V hallowed.1
  have hWdeg : (1 : ℝ) ≤ (W.degree : ℝ) := by
    rcases hWallowed with ⟨_, hW⟩ | ⟨_, _, rfl⟩
    · exact HighCarrier.irreducible_degree_one_le W hW.1
    · have hI : (AffineVariety.whole : AffineVariety (skewDim e)).ideal ≠ ⊤ := by
        simp [AffineVariety.whole, AffineVariety.ofIdeal]
      exact_mod_cast OAI.QuarticPowerFree.one_le_affineDegree
        (AffineVariety.whole : AffineVariety (skewDim e)).ideal hI
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hdenV : 0 < (V.degree : ℝ) * A ^ h :=
    mul_pos (lt_of_lt_of_le (by norm_num) hVdeg) (pow_pos hApos h)
  have hdenW : 0 < (W.degree : ℝ) * A ^ i :=
    mul_pos (lt_of_lt_of_le (by norm_num) hWdeg) (pow_pos hApos i)
  have hprofile : normalizedFlatCount C P A W i ≤ concentrationProfile C P ambient A C0 i := by
    rcases hWallowed with ⟨hlevel, hW⟩ | ⟨hamb, hlevel, _⟩
    · exact HighCarrier.profile_contains_carrier C P ambient A C0 hA W i hlevel hW hWdim
    · have hc : (containedFlatCount C P W : ℝ) ≤ (P.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hn : (0 : ℝ) ≤ (containedFlatCount C P W : ℝ) := by positivity
      have hd : A ^ i ≤ (W.degree : ℝ) * A ^ i := by
        nlinarith [pow_pos hApos i]
      unfold normalizedFlatCount
      calc
        (containedFlatCount C P W : ℝ) / ((W.degree : ℝ) * A ^ i) ≤
            (containedFlatCount C P W : ℝ) / A ^ i :=
          div_le_div_of_nonneg_left hn (pow_pos hApos i) hd
        _ ≤ (P.card : ℝ) / A ^ i := div_le_div_of_nonneg_right hc (pow_pos hApos i).le
        _ = concentrationProfile C P ambient A C0 i := by
          simp [concentrationProfile, hlevel, hamb]
  let R := concentrationProfile C P ambient A C0 i
  have hR : 0 ≤ R := by
    have hn : 0 ≤ normalizedFlatCount C P A W i :=
      div_nonneg (by positivity) hdenW.le
    exact hn.trans hprofile
  have hcount : (containedFlatCount C P V : ℝ) ≤ R * ((W.degree : ℝ) * A ^ i) := by
    have hm : (containedFlatCount C P V : ℝ) ≤ (containedFlatCount C P W : ℝ) := by
      exact_mod_cast HighCarrier.contained_count_le C P V W hsub
    exact hm.trans ((div_le_iff₀ hdenW).mp hprofile)
  have hkpow : 0 < K ^ (i - h) := pow_pos hK _
  have hai : A ^ i = A ^ h * A ^ (i - h) := by
    rw [← pow_add]
    congr 1
    omega
  have hgain' : R * ((W.degree : ℝ) * A ^ i) * K ^ (i - h) ≤
      Cdesc * R * ((V.degree : ℝ) * A ^ h) := by
    have hg := mul_le_mul_of_nonneg_left hgain (mul_nonneg hR (pow_pos hApos h).le)
    rw [mul_pow] at hg
    rw [hai]
    convert hg using 1 <;> ring
  have hfinal := (mul_le_mul_of_nonneg_right hcount hkpow.le).trans hgain'
  apply (le_div_iff₀ hkpow).mpr
  unfold normalizedFlatCount
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hdenV).mpr hfinal

/-- B33, conc:recurrence-system: the finite inequalities for the actual fixed-sample profile. -/
theorem geometric_recurrence_system (e : ℕ) (he : 3 ≤ e) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (C : SkewCoordinates e) (A : ℝ), 1 ≤ A →
      ∀ (P : Finset (ProjectivePoint (e + e))) (ambient : Bool),
        (∀ p ∈ P, p ∈ affineParameters e) → HasSeparators P (C0 * A) →
        HasIsotropicCap P (C0 * A ^ (e - 2)) →
        (ambient = true → (P.card : ℝ) ≤ C0 * A ^ (e - 1)) →
        ∀ K : ℕ → ℝ, (∀ h, 1 ≤ h → h + 2 ≤ e → C0 < K h) →
          ∀ h, 1 ≤ h → h + 2 ≤ e →
            concentrationProfile C P ambient A C0 h ≤
              B * (1 + K h * concentrationProfile C P ambient A C0 (h - 1)) ∨
            ∃ i, h < i ∧ (i < e - 1 ∨ (ambient = true ∧ i = e - 1)) ∧
              concentrationProfile C P ambient A C0 h ≤
                B * concentrationProfile C P ambient A C0 i / K h ^ (i - h) := by
  classical
  -- Walsh's constant precedes the sample, carrier, and degree thresholds.
  obtain ⟨Cdesc, hCdesc, hdescriptions⟩ :
      ∃ Cdesc : ℝ, 1 ≤ Cdesc ∧
        ∀ (V : AffineVariety (skewDim e)) (c : ℕ), V.IsIrreducible →
          V ≠ AffineVariety.whole → 0 < c → V.dimension + c = skewDim e →
          ∃ D : ApproximateDescription V c,
            (D.degreeProduct : ℝ) ≤ Cdesc * (V.degree : ℝ) := by
    obtain ⟨Cdesc, hCdesc, hdesc⟩ := MBRec.walsh_description (skewDim e)
    refine ⟨Cdesc, hCdesc, ?_⟩
    intro V c hV hproper hc hd
    obtain ⟨f, d, hbounds, hmono, hcomp, hbudget⟩ := hdesc V c hV hc hd
    refine ⟨{ equations := f
              upper := d
              positive := fun i => (hbounds i).1
              vanish := fun i => (hbounds i).2.1
              degree_bounds := fun i => (hbounds i).2.2
              sorted := hmono
              component := hcomp }, hbudget⟩
  obtain ⟨Blow, hBlow, hlow⟩ := low_recurrence e he C0 Cdesc hC0 hCdesc
  let B := max Blow Cdesc
  have hBlowB : Blow ≤ B := le_max_left _ _
  have hCdescB : Cdesc ≤ B := le_max_right _ _
  refine ⟨B, hBlow.trans hBlowB, ?_⟩
  intro C A hA P ambient hP hsep hcap hcard K hK h hh hhend
  have hKh : C0 < K h := hK h hh hhend
  have hKpos : 0 < K h := lt_of_lt_of_le one_pos (hC0.trans hKh.le)
  have hprevious : 0 ≤ concentrationProfile C P ambient A C0 (h - 1) :=
    (concentrationProfile_endpoints C he P hP ambient A C0 hA hC0 hcard).1
      (h - 1) (by omega) |>.1
  let low := B * (1 + K h * concentrationProfile C P ambient A C0 (h - 1))
  let available := (Finset.range e).filter fun i =>
    h < i ∧ (i < e - 1 ∨ (ambient = true ∧ i = e - 1))
  let candidates := insert h available
  let bound (i : ℕ) := if i = h then low else
    B * concentrationProfile C P ambient A C0 i / K h ^ (i - h)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image candidates bound
    ⟨h, Finset.mem_insert_self _ _⟩
  have hlowmax : low ≤ bound m := by
    simpa [bound] using hmax h (Finset.mem_insert_self _ _)
  have hmaxnonneg : 0 ≤ bound m := by
    apply le_trans (b := low) _ hlowmax
    dsimp [low]
    positivity
  have hchoose : skewDim e = flatDim e + (e - 1) := by
    simp only [skewDim, flatDim]
    rw [show e = (e - 1) + 1 by omega, Nat.choose_succ_succ']
    simp [Nat.choose_one_right, Nat.add_comm]
  have hcarrier : ∀ V : AffineVariety (skewDim e),
      AllowedCarrier ambient A C0 V → V.dimension = flatDim e + h →
      normalizedFlatCount C P A V h ≤ bound m := by
    intro V hallowed hdim
    let c := e - 1 - h
    have hc : 0 < c := by dsimp [c]; omega
    have hcodim : V.dimension + c = skewDim e := by dsimp [c]; omega
    obtain ⟨D, hbudget⟩ := hdescriptions V c hallowed.1 hallowed.2.1 hc hcodim
    obtain ⟨D', hprefix, hfirst, hupper, hbudget'⟩ :=
      refine_description V hallowed.1 hc hcodim D Cdesc hbudget
    by_cases hsmall : ∀ i : Fin c, (D'.upper i : ℝ) ≤ K h * A
    · have hv := hlow C A (K h) hA hKpos P ambient hP hsep hcap
        V h c hallowed hh hhend hdim hcodim D' hbudget' hsmall
      have hfactor : 0 ≤ 1 + K h * concentrationProfile C P ambient A C0 (h - 1) :=
        add_nonneg zero_le_one (mul_nonneg hKpos.le hprevious)
      exact hv.trans ((mul_le_mul_of_nonneg_right hBlowB hfactor).trans hlowmax)
    · have hex : ∃ p : ℕ, ∃ i : Fin c, i.val = p ∧ K h * A < (D'.upper i : ℝ) := by
        obtain ⟨i, hi⟩ := not_forall.mp hsmall
        exact ⟨i.val, i, rfl, lt_of_not_ge hi⟩
      let p := Nat.find hex
      obtain ⟨i0, hi0, hi0large⟩ := Nat.find_spec hex
      have hp : p < c := by change Nat.find hex < c; omega
      have hpresmall : ∀ i : Fin c, i.val < p → (D'.upper i : ℝ) ≤ K h * A := by
        intro i hi
        by_contra hnot
        exact Nat.find_min hex hi ⟨i, rfl, lt_of_not_ge hnot⟩
      have htail : ∀ i : Fin c, p ≤ i.val → K h * A < (D'.upper i : ℝ) := by
        intro i hi
        exact hi0large.trans_le (Nat.cast_le.mpr (D'.sorted (by change i0.val ≤ i.val; omega)))
      obtain ⟨W, hW, hVW, hWdim, hWdeg, hgain, hWallowed⟩ :=
        large_description_carrier C he ⟨hh, hhend⟩ hc V hdim hcodim ambient A C0
          (K h) Cdesc hA hC0 hKh hallowed D' hprefix hfirst hbudget'
          p hp hpresmall htail
      let i := e - 1 - p
      have hhi : h < i := by dsimp [i, c] at *; omega
      have hindex : i < e - 1 ∨ (ambient = true ∧ i = e - 1) := by
        rcases hWallowed with ⟨hlt, _⟩ | ⟨hamb, hp0, _⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨hamb, by simp [i, hp0]⟩
      have hallowedW : (i < e - 1 ∧ AllowedCarrier ambient A C0 W) ∨
          (ambient = true ∧ i = e - 1 ∧ W = AffineVariety.whole) := by
        rcases hWallowed with hW | ⟨hamb, hp0, hwhole⟩
        · exact Or.inl hW
        · exact Or.inr ⟨hamb, by simp [i, hp0], hwhole⟩
      have hgain' : (W.degree : ℝ) * (K h * A) ^ (i - h) ≤ Cdesc * (V.degree : ℝ) := by
        have hexp : i - h = c - p := by dsimp [i, c]; omega
        simpa [hexp] using hgain
      have hv := high_recurrence_of_carrier C he P ambient A C0 (K h) Cdesc
        hA hC0 hKpos hCdesc V W ⟨hh, hhend⟩ hhi hallowed hVW hdim hWdim
        hallowedW hgain'
      have hprofnonneg : 0 ≤ concentrationProfile C P ambient A C0 i := by
        rcases hindex with hlt | ⟨hamb, hi⟩
        · exact (concentrationProfile_endpoints C he P hP ambient A C0 hA hC0 hcard).1 i hlt |>.1
        · simp [concentrationProfile, hi, hamb]
          positivity
      have hscale :
          Cdesc * concentrationProfile C P ambient A C0 i / K h ^ (i - h) ≤
            B * concentrationProfile C P ambient A C0 i / K h ^ (i - h) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCdescB hprofnonneg) (pow_pos hKpos _).le
      have himem : i ∈ candidates := by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rcases hindex with hi | ⟨_, hi⟩ <;> omega),
          hhi, hindex⟩
      have himax : B * concentrationProfile C P ambient A C0 i / K h ^ (i - h) ≤ bound m := by
        simpa [bound, ne_of_gt hhi] using hmax i himem
      exact hv.trans (hscale.trans himax)
  have hprofile : concentrationProfile C P ambient A C0 h ≤ bound m := by
    rw [concentrationProfile, if_neg (show h ≠ e - 1 by omega)]
    apply csSup_le ⟨0, Set.mem_insert 0 _⟩
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | ⟨V, hallowed, hdim, rfl⟩
    · exact hmaxnonneg
    · exact hcarrier V hallowed hdim
  rcases Finset.mem_insert.mp hm with hmh | hm
  · left
    simpa [bound, hmh, low] using hprofile
  · right
    obtain ⟨_, hhm, hindex⟩ := Finset.mem_filter.mp hm
    refine ⟨m, hhm, hindex, ?_⟩
    simpa [bound, ne_of_gt hhm] using hprofile

/-- B36, conc:theorem / conc:uniform-completion. The constant precedes A, P, all
carriers and the specification flag; case (b) has no sample-cardinality hypothesis. -/
theorem uniform_concentration (e : ℕ) (he : 3 ≤ e) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ B : ℝ, 0 < B ∧ ∀ (C : SkewCoordinates e) (A : ℝ), 1 ≤ A →
      ∀ (P : Finset (ProjectivePoint (e + e))) (ambient : Bool),
        (∀ p ∈ P, p ∈ affineParameters e) → HasSeparators P (C0 * A) →
        HasIsotropicCap P (C0 * A ^ (e - 2)) →
        (ambient = true → (P.card : ℝ) ≤ C0 * A ^ (e - 1)) →
        ∀ (V : AffineVariety (skewDim e)) (h : ℕ),
          AllowedCarrier ambient A C0 V → 1 ≤ h → h + 2 ≤ e →
          V.dimension = flatDim e + h →
          (containedFlatCount C P V : ℝ) ≤ B * (V.degree : ℝ) * A ^ h := by
  classical
  obtain ⟨Crec, hCrec, hgeom⟩ := geometric_recurrence_system e he C0 hC0
  obtain ⟨K, b, hb, hK, hbound⟩ := concentration_recurrence_bound (e - 1)
    (by omega) Crec C0 hCrec hC0
  let B : ℝ := 1 + ∑ j ∈ Finset.range e, |b j|
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro C A hA P ambient hP hsep hcap hcard V h hallowed hh hhe hdim
  let R : ℕ → ℝ := concentrationProfile C P ambient A C0
  have hend := concentrationProfile_endpoints C he P hP ambient A C0 hA hC0 hcard
  have hnonneg : ∀ i ≤ e - 1, 0 ≤ R i := by
    intro i hi
    by_cases hir : i < e - 1
    · exact (hend.1 i hir).1
    · have heq : i = e - 1 := by omega
      by_cases hamb : ambient = true
      · change 0 ≤ concentrationProfile C P ambient A C0 i
        rw [concentrationProfile, if_pos heq, if_pos hamb]
        exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
      · simp [R, concentrationProfile, heq, hamb]
  have hrec := hgeom C A hA P ambient hP hsep hcap hcard K
    (by intro i hi hie; exact hK i hi (by omega))
  have hRb : R h ≤ b h := hbound ambient R hnonneg hend.2.1 hend.2.2
    (by intro i hi hir; exact hrec i hi (by omega)) h (Or.inl (by omega))
  have hbB : b h ≤ B := by
    have hsum : |b h| ≤ ∑ j ∈ Finset.range e, |b j| :=
      Finset.single_le_sum (fun j hj => abs_nonneg (b j)) (Finset.mem_range.mpr (by omega))
    dsimp [B]
    linarith [le_abs_self (b h)]
  have hnorm : normalizedFlatCount C P A V h ≤ B :=
    (HighCarrier.profile_contains_carrier C P ambient A C0 hA V h (by omega)
      hallowed hdim).trans (hRb.trans hbB)
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hdeg : 0 < (V.degree : ℝ) :=
    lt_of_lt_of_le (by norm_num) (HighCarrier.irreducible_degree_one_le V hallowed.1)
  have hden : 0 < (V.degree : ℝ) * A ^ h := mul_pos hdeg (pow_pos hApos _)
  have hcount := (div_le_iff₀ hden).mp hnorm
  simpa only [mul_assoc] using hcount


#print axioms refine_description
#print axioms containedFlatCount_le_one_of_dimension
#print axioms concentrationProfile_endpoints
#print axioms large_description_carrier
#print axioms high_recurrence_of_carrier
#print axioms uniform_concentration

end
end DistinctDistances.TrackB
