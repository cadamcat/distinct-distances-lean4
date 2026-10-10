import DistinctDistances.TrackA.Hilbert
import DistinctDistances.TrackB.EquationPrefixes
import DistinctDistances.TrackB.RefinementCore
import DistinctDistances.TrackB.Requests
import DistinctDistances.TrackB.GeometryModel
import DistinctDistances.TrackA.Regularity
import Mathlib.Tactic.LinearCombination
import DistinctDistances.Bridges.ProjectiveEnvelope
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Finiteness
import DistinctDistances.TrackB.TangentLineSupport

namespace DistinctDistances.TrackB.MBRec

noncomputable section
open scoped BigOperators Classical

def boundedEquationIdeal {n : ℕ} (V : AffineVariety n) (D : ℕ) : Ideal (Poly n) :=
  Ideal.span {f : Poly n | f ∈ V.ideal ∧ f.totalDegree ≤ D}

theorem boundedEquationIdeal_le {n : ℕ} (V : AffineVariety n) (D : ℕ) :
    boundedEquationIdeal V D ≤ V.ideal := by
  apply Ideal.span_le.mpr
  exact fun _ hf => hf.1

theorem boundedEquationIdeal_mono {n : ℕ} (V : AffineVariety n) {D E : ℕ}
    (hDE : D ≤ E) : boundedEquationIdeal V D ≤ boundedEquationIdeal V E := by
  apply Ideal.span_mono
  exact fun _ hf => ⟨hf.1, hf.2.trans hDE⟩

theorem boundedEquationIdeal_zero {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) : boundedEquationIdeal V 0 = ⊥ := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro f hf
    have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      (Nat.eq_zero_of_le_zero hf.2)
    by_cases hz : f.coeff 0 = 0
    · rw [heq, hz, MvPolynomial.C_0]
      exact Ideal.zero_mem _
    · have hu : IsUnit (MvPolynomial.C (f.coeff 0) : Poly n) :=
        (isUnit_iff_ne_zero.mpr hz).map MvPolynomial.C
      exact (hV.ne_top (V.ideal.eq_top_of_isUnit_mem (heq ▸ hf.1) hu)).elim
  · exact bot_le

theorem boundedEquationIdeal_eventually_full {n : ℕ} (V : AffineVariety n) :
    ∃ D : ℕ, boundedEquationIdeal V D = V.ideal := by
  classical
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian V.ideal)
  let D := S.sup MvPolynomial.totalDegree
  refine ⟨D, le_antisymm (boundedEquationIdeal_le V D) ?_⟩
  rw [← hS]
  apply Ideal.span_le.mpr
  intro f hf
  apply Ideal.subset_span
  refine ⟨?_, Finset.le_sup hf⟩
  rw [← hS]
  exact Ideal.subset_span hf

def adequateDegree {n : ℕ} (V : AffineVariety n) (i D : ℕ) : Prop :=
  ∀ Q : Ideal (Poly n), Q ∈ (boundedEquationIdeal V D).minimalPrimes →
    Q ≤ V.ideal → OAI.QuarticPowerFree.affineDimension Q + i ≤ n

theorem adequateDegree_exists {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n) (i : ℕ) (hi : i ≤ c) :
    ∃ D : ℕ, adequateDegree V i D := by
  obtain ⟨D, hD⟩ := boundedEquationIdeal_eventually_full V
  refine ⟨D, ?_⟩
  intro Q hQ hQV
  rw [hD] at hQ
  letI : V.ideal.IsPrime := hV
  have hQI : Q = V.ideal := by
    simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hQ
  rw [hQI]
  change V.dimension + i ≤ n
  omega

def partialDegree {n c : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (hd : V.dimension + c = n) (i : ℕ) : ℕ :=
  Nat.find (adequateDegree_exists V hV hd (min i c) (Nat.min_le_right _ _))

theorem partialDegree_adequate {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n) (i : ℕ) (hi : i ≤ c) :
    adequateDegree V i (partialDegree V hV hd i) := by
  simpa [partialDegree, Nat.min_eq_left hi] using
    Nat.find_spec (adequateDegree_exists V hV hd (min i c) (Nat.min_le_right _ _))

theorem partialDegree_min {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n) (i D : ℕ) (hi : i ≤ c)
    (hD : D < partialDegree V hV hd i) : ¬ adequateDegree V i D := by
  simpa [Nat.min_eq_left hi] using
    Nat.find_min (adequateDegree_exists V hV hd (min i c) (Nat.min_le_right _ _)) hD

theorem partialDegree_mono {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n) :
    Monotone (partialDegree V hV hd) := by
  intro i j hij
  apply Nat.find_min'
  intro Q hQ hQV
  have hgood := Nat.find_spec
    (adequateDegree_exists V hV hd (min j c) (Nat.min_le_right _ _))
  have hdim := hgood Q hQ hQV
  have hm := min_le_min_right c hij
  omega

theorem partialDegree_zero {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n) : partialDegree V hV hd 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min'
  intro Q hQ hQV
  have hdim : OAI.QuarticPowerFree.affineDimension Q ≤ n :=
    (OAI.QuarticPowerFree.coordinate_hilbert_eventually_polynomial Q).choose_spec.1
  simpa using hdim

theorem partialDegree_positive {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n) (i : ℕ)
    (hi : i ≤ c) (hipos : 0 < i) : 0 < partialDegree V hV hd i := by
  by_contra hnot
  have hz : partialDegree V hV hd i = 0 := by omega
  have hgood := partialDegree_adequate V hV hd i hi
  rw [hz] at hgood
  have hbot : (⊥ : Ideal (Poly n)) ∈ (boundedEquationIdeal V 0).minimalPrimes := by
    simp [boundedEquationIdeal_zero V hV, Ideal.minimalPrimes_eq_subsingleton_self]
  have hdim := hgood ⊥ hbot bot_le
  have hwhole : OAI.QuarticPowerFree.affineDimension (⊥ : Ideal (Poly n)) = n := by
    simpa [AffineVariety.whole, AffineVariety.ofIdeal, AffineVariety.dimension,
      Ideal.radical_bot_of_isReduced] using Bridges.affine_whole_dimension n
  rw [hwhole] at hdim
  omega

/-- A partial-degree threshold supplies a polynomial avoiding every relevant
component of the preceding prefix. -/
theorem partialDegree_avoiding_equation {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n)
    (g : Fin c → Poly n) (hgV : ∀ i, g i ∈ V.ideal)
    (p : ℕ) (hp : p < c)
    (hreg : ∀ W : AffineVariety n,
      W.IsComponentOf (equationPrefixIdeal g p) → V.Subvariety W → W.dimension + p = n) :
    ∃ q : Poly n, 0 < q.totalDegree ∧ q ∈ V.ideal ∧
      q.totalDegree ≤ partialDegree V hV hd (p + 1) ∧
      ∀ Q : Ideal (Poly n), Q ∈ (equationPrefixIdeal g p).minimalPrimes →
        Q ≤ V.ideal → q ∉ Q := by
  classical
  let D := partialDegree V hV hd (p + 1)
  let T := (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n)
    (equationPrefixIdeal g p)).toFinset
  let S := T.filter (fun Q => Q ≤ V.ideal)
  have hmem : ∀ Q : Ideal (Poly n), Q ∈ S ↔
      Q ∈ (equationPrefixIdeal g p).minimalPrimes ∧ Q ≤ V.ideal := by
    intro Q
    simp [S, T]
  have hproper : ∀ Q ∈ S, ∃ f : Poly n,
      f ∈ V.ideal ∧ f.totalDegree ≤ D ∧ f ∉ Q := by
    intro Q hQS
    obtain ⟨hQ, hQV⟩ := (hmem Q).mp hQS
    by_contra hno
    push_neg at hno
    have hle : boundedEquationIdeal V D ≤ Q := by
      apply Ideal.span_le.mpr
      exact fun f hf => hno f hf.1 hf.2
    letI : Q.IsPrime := hQ.isPrime
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hle
    let U : AffineVariety n := ⟨P, hP.isPrime.isRadical⟩
    let W : AffineVariety n := ⟨Q, hQ.isPrime.isRadical⟩
    have hWdim := hreg W hQ hQV
    have hUdim := partialDegree_adequate V hV hd (p + 1) (by omega)
      P hP (hPQ.trans hQV)
    have hmono : W.dimension ≤ U.dimension := affine_dimension_mono U W hPQ
    change U.dimension + (p + 1) ≤ n at hUdim
    omega
  let H : Submodule ℂ (Poly n) :=
    V.ideal.restrictScalars ℂ ⊓ OAI.QuarticPowerFree.totalSpace D
  let bad : {Q : Ideal (Poly n) // Q ∈ S} → Submodule ℂ H :=
    fun Q => Submodule.comap H.subtype (Q.1.restrictScalars ℂ)
  have hbad : ∀ Q, bad Q ≠ ⊤ := by
    intro Q htop
    obtain ⟨f, hfV, hfD, hfQ⟩ := hproper Q.1 Q.2
    let x : H := ⟨f, hfV, OAI.QuarticPowerFree.mem_totalSpace.mpr hfD⟩
    have hx : x ∈ bad Q := by rw [htop]; exact Submodule.mem_top
    exact hfQ hx
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  have havoid : ∀ Q, Q ∈ (equationPrefixIdeal g p).minimalPrimes →
      Q ≤ V.ideal → x.val ∉ Q := by
    intro Q hQ hQV hxin
    exact hx ⟨Q, (hmem Q).mpr ⟨hQ, hQV⟩⟩ hxin
  have hpre : equationPrefixIdeal g p ≤ V.ideal :=
    equationPrefixIdeal_le_variety g V hgV p
  letI : V.ideal.IsPrime := hV
  obtain ⟨Q, hQ, hQV⟩ := Ideal.exists_minimalPrimes_le hpre
  have hxne : x.val ≠ 0 := by
    intro hz
    exact havoid Q hQ hQV (hz ▸ Ideal.zero_mem Q)
  exact ⟨x.val, nonzero_equation_positive V hV x.val hxne x.property.1,
    x.property.1, OAI.QuarticPowerFree.mem_totalSpace.mp x.property.2, havoid⟩

/-- Compatible cuts at the successive partial degrees. Their prefixes have the
exact codimension at every component containing V. -/
theorem compatible_partial_cuts {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n) :
    ∃ g : Fin c → Poly n,
      (∀ i, 0 < (g i).totalDegree ∧ g i ∈ V.ideal ∧
        (g i).totalDegree ≤ partialDegree V hV hd (i.val + 1)) ∧
      V.IsComponentOf (Ideal.span (Set.range g)) ∧
      ∀ p ≤ c, ∀ W : AffineVariety n,
        W.IsComponentOf (equationPrefixIdeal g p) → V.Subvariety W → W.dimension + p = n := by
  classical
  have hex : ∀ p ≤ c, ∃ g : Fin c → Poly n,
      (∀ i, g i ∈ V.ideal ∧ (g i).totalDegree ≤ partialDegree V hV hd (i.val + 1)) ∧
      (∀ i, i.val < p → 0 < (g i).totalDegree) ∧
      ∀ r ≤ p, ∀ W : AffineVariety n,
        W.IsComponentOf (equationPrefixIdeal g r) → V.Subvariety W → W.dimension + r = n := by
    intro p
    induction p with
    | zero =>
      intro hp
      refine ⟨fun _ => 0, (fun i => by simp), ?_, ?_⟩
      · intro i hi
        omega
      · intro r hr W hW hVW
        have hr0 : r = 0 := by omega
        subst r
        have hlower := prefix_component_dimension_lower (fun _ : Fin c => (0 : Poly n))
          0 (by omega) W hW
        have hupper := Bridges.affine_dimension_le W
        omega
    | succ p ih =>
      intro hpc
      obtain ⟨g, hgbounds, hgpos, hgreg⟩ := ih (by omega)
      have hp : p < c := by omega
      obtain ⟨q, hqpos, hqV, hqdeg, hqavoid⟩ := partialDegree_avoiding_equation V hV hd
        g (fun i => (hgbounds i).1) p hp (hgreg p le_rfl)
      let g' := Function.update g ⟨p, hp⟩ q
      refine ⟨g', ?_, ?_, regular_prefix_extension V hV (by omega) g p hp hgreg q hqavoid⟩
      · intro i
        by_cases hi : i = ⟨p, hp⟩
        · subst i
          simpa [g'] using And.intro hqV hqdeg
        · simpa [g', Function.update_of_ne hi] using hgbounds i
      · intro i hi
        by_cases hieq : i = ⟨p, hp⟩
        · subst i
          simpa [g'] using hqpos
        · have hip : i.val < p := by
            have hine : i.val ≠ p := by intro heq; exact hieq (Fin.ext heq)
            omega
          simpa [g', Function.update_of_ne hieq] using hgpos i hip
  obtain ⟨g, hgbounds, hgpos, hgreg⟩ := hex c le_rfl
  have hle : Ideal.span (Set.range g) ≤ V.ideal := by
    apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    exact (hgbounds i).1
  letI : V.ideal.IsPrime := hV
  obtain ⟨P, hP, hPV⟩ := Ideal.exists_minimalPrimes_le hle
  let U : AffineVariety n := ⟨P, hP.isPrime.isRadical⟩
  have hUpre : U.IsComponentOf (equationPrefixIdeal g c) := by
    change P ∈ (equationPrefixIdeal g c).minimalPrimes
    rw [equationPrefixIdeal_full]
    exact hP
  have hUdim := hgreg c le_rfl U hUpre hPV
  letI : P.IsPrime := hP.isPrime
  have heq : P = V.ideal := Request.affine_prime_same_dimension_eq P V.ideal hPV
    (show U.dimension = V.dimension by omega) rfl
  refine ⟨g, (fun i => ⟨hgpos i i.isLt, (hgbounds i).1, (hgbounds i).2⟩), ?_, hgreg⟩
  change V.ideal ∈ (Ideal.span (Set.range g)).minimalPrimes
  rw [← heq]
  exact hP

theorem shared_hilbert_of_bounded_equations {n : ℕ} (V W : AffineVariety n)
    (D : ℕ) (hVW : V.Subvariety W) (hbounded : boundedEquationIdeal V D ≤ W.ideal) :
    W.hilbert D = V.hilbert D := by
  let E := envelope V.points D
  have hWE : W.Subvariety E := by
    change (Ideal.span {f : Poly n | f ∈ MvPolynomial.vanishingIdeal ℂ V.points ∧
      f.totalDegree ≤ D}).radical ≤ W.ideal
    rw [V.vanishingIdeal_points]
    exact W.isRadical.radical_le_iff.mpr hbounded
  have hclosure : AffineVariety.closure V.points = V :=
    AffineVariety.ext V.vanishingIdeal_points
  have hE : E.hilbert D = V.hilbert D := by
    simpa [E, hilbertOfSet, hclosure] using envelope_hilbert V.points D
  apply le_antisymm
  · exact (W.hilbert_mono E hWE D).trans_eq hE
  · exact V.hilbert_mono W hVW D

/-- Below the next partial-degree threshold, one component of a compatible
prefix has exactly the same bounded-degree equations and restriction rank as V. -/
theorem compatible_prefix_shared_rank {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n)
    (g : Fin c → Poly n)
    (hgbounds : ∀ i, g i ∈ V.ideal ∧ (g i).totalDegree ≤ partialDegree V hV hd (i.val + 1))
    (hgreg : ∀ p ≤ c, ∀ W : AffineVariety n,
      W.IsComponentOf (equationPrefixIdeal g p) → V.Subvariety W → W.dimension + p = n)
    (j m : ℕ) (hj : j < c)
    (hsmall : partialDegree V hV hd j ≤ m) (hlarge : m < partialDegree V hV hd (j + 1)) :
    ∃ W : AffineVariety n, W.IsComponentOf (equationPrefixIdeal g j) ∧
      V.Subvariety W ∧ W.dimension + j = n ∧
      boundedEquationIdeal V m ≤ W.ideal ∧ W.hilbert m = V.hilbert m := by
  classical
  have hnot := partialDegree_min V hV hd (j + 1) m (by omega) hlarge
  unfold adequateDegree at hnot
  push_neg at hnot
  obtain ⟨Q, hQ, hQV, hQdim⟩ := hnot
  have hpre : equationPrefixIdeal g j ≤ boundedEquationIdeal V m := by
    apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    change (if i.val < j then g i else 0) ∈ _
    split
    · apply Ideal.subset_span
      exact ⟨(hgbounds i).1, (hgbounds i).2.trans
        ((partialDegree_mono V hV hd (by omega)).trans hsmall)⟩
    · exact Ideal.zero_mem _
  letI : Q.IsPrime := hQ.isPrime
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (hpre.trans hQ.le)
  let W : AffineVariety n := ⟨P, hP.isPrime.isRadical⟩
  let U : AffineVariety n := ⟨Q, hQ.isPrime.isRadical⟩
  have hWV : V.Subvariety W := hPQ.trans hQV
  have hWdim := hgreg j (by omega) W hP hWV
  have hmono : U.dimension ≤ W.dimension := affine_dimension_mono W U hPQ
  change n < U.dimension + (j + 1) at hQdim
  have heqdim : W.dimension = U.dimension := by omega
  letI : P.IsPrime := hP.isPrime
  have heq : P = Q := Request.affine_prime_same_dimension_eq P Q hPQ heqdim rfl
  have hbounded : boundedEquationIdeal V m ≤ W.ideal := by
    change boundedEquationIdeal V m ≤ P
    rw [heq]
    exact hQ.le
  exact ⟨W, hP, hWV, hWdim, hbounded, shared_hilbert_of_bounded_equations V W m hWV hbounded⟩

theorem binomial_upper_power (n k m : ℕ) (hk : k ≤ n) (hm : 1 ≤ m) :
    (m + k).choose k ≤ (n + 1) ^ n * m ^ k := by
  have hbase : m + k ≤ (n + 1) * m := by nlinarith
  calc
    (m + k).choose k ≤ (m + k) ^ k := Nat.choose_le_pow _ _
    _ ≤ ((n + 1) * m) ^ k := Nat.pow_le_pow_left hbase k
    _ = (n + 1) ^ k * m ^ k := mul_pow _ _ _
    _ ≤ (n + 1) ^ n * m ^ k :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hk)

theorem affine_locus_singleton {n : ℕ} (V : AffineVariety n) :
    AffineFamily.locus {V} = V := by
  apply AffineVariety.ext
  simp [AffineFamily.locus, AffineVariety.ofIdeal, V.isRadical.radical]

theorem irreducible_hilbert_upper_power {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (k m : ℕ) (hdim : V.dimension = k) (hm : 1 ≤ m) :
    (V.hilbert m : ℚ) ≤ (n + 1 : ℚ) ^ n * V.degree * (m : ℚ) ^ k := by
  have hpure : AffineFamily.IsPure {V} k := by
    intro W hW
    have heq : W = V := Finset.mem_singleton.mp hW
    subst W
    exact ⟨hV, hdim⟩
  have hh := TrackA.poly_hilbert_upper {V} k hpure m
  simp only [AffineFamily.hilbert, affine_locus_singleton, AffineFamily.degree,
    Finset.sum_singleton] at hh
  have hk : k ≤ n := by rw [← hdim]; exact Bridges.affine_dimension_le V
  have hchoose : ((m + k).choose k : ℚ) ≤ (n + 1 : ℚ) ^ n * (m : ℚ) ^ k := by
    exact_mod_cast binomial_upper_power n k m hk hm
  have hdeg : 0 ≤ V.degree := zero_le_one.trans (V.one_le_degree hV.ne_top)
  calc
    (V.hilbert m : ℚ) ≤ V.degree * ((m + k).choose k : ℚ) := hh
    _ ≤ V.degree * ((n + 1 : ℚ) ^ n * (m : ℚ) ^ k) :=
      mul_le_mul_of_nonneg_left hchoose hdeg
    _ = _ := by ring

theorem compatible_prefix_defined_in_degree {n c : ℕ} (g : Fin c → Poly n)
    (j m : ℕ) (hdeg : ∀ i : Fin c, i.val < j → (g i).totalDegree ≤ m)
    (W : AffineVariety n) (hW : W.IsComponentOf (equationPrefixIdeal g j)) :
    AffineFamily.ComponentsDefinedInDegree {W} m := by
  refine ⟨Set.range (fun i : Fin c => if i.val < j then g i else 0), ?_, ?_⟩
  · rintro f ⟨i, rfl⟩
    change (if i.val < j then g i else 0).totalDegree ≤ m
    split
    · exact hdeg i ‹_›
    · simp
  · intro U hU
    have heq : U = W := Finset.mem_singleton.mp hU
    subst U
    exact hW

theorem prefix_budget_step (a b γ P m δ d : ℚ) (n j s : ℕ)
    (hb : 0 < b) (hγ : 0 < γ) (hγone : γ ≤ 1) (hP : 0 ≤ P)
    (hm : 0 ≤ m) (hδ : 0 ≤ δ) (hδm : δ ≤ 2 * m)
    (hjs : j < s) (hsn : s ≤ n) (hsmall : γ * 2 ^ n * b ≤ a)
    (hineq : a * γ ^ j * P * m ^ (s - j) ≤ b * d) :
    γ ^ s * (P * δ ^ (s - j)) ≤ d := by
  have hγpow : γ ^ (s - j) ≤ γ := by
    calc
      γ ^ (s - j) = γ * γ ^ (s - j - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      _ ≤ γ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hγ.le hγone) hγ.le
      _ = γ := mul_one _
  have hδpow : δ ^ (s - j) ≤ 2 ^ n * m ^ (s - j) := by
    calc
      δ ^ (s - j) ≤ (2 * m) ^ (s - j) := pow_le_pow_left₀ hδ hδm _
      _ = 2 ^ (s - j) * m ^ (s - j) := mul_pow _ _ _
      _ ≤ 2 ^ n * m ^ (s - j) := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) (pow_nonneg hm _)
  have hsplit : γ ^ s = γ ^ j * γ ^ (s - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hbound : γ ^ s * (P * δ ^ (s - j)) ≤
      γ ^ j * γ * (P * (2 ^ n * m ^ (s - j))) := by
    rw [hsplit]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hγpow (pow_nonneg hγ.le _)
    · exact mul_le_mul_of_nonneg_left hδpow hP
    · positivity
    · positivity
  apply (mul_le_mul_iff_right₀ hb).mp
  calc
    b * (γ ^ s * (P * δ ^ (s - j))) ≤
        b * (γ ^ j * γ * (P * (2 ^ n * m ^ (s - j)))) :=
      mul_le_mul_of_nonneg_left hbound hb.le
    _ = (γ * 2 ^ n * b) * (γ ^ j * P * m ^ (s - j)) := by ring
    _ ≤ a * (γ ^ j * P * m ^ (s - j)) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = a * γ ^ j * P * m ^ (s - j) := by ring
    _ ≤ b * d := hineq

/-- The Hilbert comparison in approximation.tex:101–163, applied to all
components of every compatible prefix, gives the Walsh degree product budget. -/
theorem compatible_prefix_degree_lower {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension + c = n)
    (g : Fin c → Poly n)
    (hgbounds : ∀ i, g i ∈ V.ideal ∧ (g i).totalDegree ≤ partialDegree V hV hd (i.val + 1))
    (hgreg : ∀ p ≤ c, ∀ W : AffineVariety n,
      W.IsComponentOf (equationPrefixIdeal g p) → V.Subvariety W → W.dimension + p = n)
    (a γ : ℚ) (ha : 0 < a) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hγsmall : γ * 2 ^ n * (n + 1 : ℚ) ^ n ≤ a)
    (hlower : ∀ (F : AffineFamily.Family n) (k L : ℕ),
      AffineFamily.IsPure F k → 1 ≤ L → AffineFamily.ComponentsDefinedInDegree F L →
      a * AffineFamily.degree F * (L : ℚ) ^ k ≤ (AffineFamily.hilbert F L : ℚ))
    (s : ℕ) (hs : s ≤ c) (U : AffineVariety n)
    (hU : U.IsComponentOf (equationPrefixIdeal g s)) (hVU : V.Subvariety U) :
    γ ^ s * (∏ t ∈ Finset.range s, (partialDegree V hV hd (t + 1) : ℚ)) ≤ U.degree := by
  classical
  induction s using Nat.strong_induction_on generalizing U with
  | h s ih =>
    let δ := partialDegree V hV hd
    let P (r : ℕ) : ℚ := ∏ t ∈ Finset.range r, (δ (t + 1) : ℚ)
    have hUdim := hgreg s hs U hU hVU
    have hdegree : (1 : ℚ) ≤ U.degree := U.one_le_degree hU.isPrime.ne_top
    have hsn : s ≤ n := by omega
    by_cases hs0 : s = 0
    · subst s
      simpa using hdegree
    have hspos : 0 < s := by omega
    have hδpos : 0 < δ s := partialDegree_positive V hV hd s hs hspos
    by_cases hδone : δ s = 1
    · have hP : P s = 1 := by
        apply Finset.prod_eq_one
        intro t ht
        have hts : t + 1 ≤ s := by have := Finset.mem_range.mp ht; omega
        have hlow := partialDegree_positive V hV hd (t + 1) (by omega) (by omega)
        have hupp := partialDegree_mono V hV hd hts
        have heq : δ (t + 1) = 1 := by
          change 0 < δ (t + 1) at hlow
          change δ (t + 1) ≤ δ s at hupp
          omega
        simp [heq]
      change γ ^ s * P s ≤ U.degree
      rw [hP, mul_one]
      exact (pow_le_one₀ hγ.le hγone).trans hdegree
    let m := δ s - 1
    have hm : 1 ≤ m := by dsimp [m]; omega
    let J := (Finset.range s).filter fun j => δ j < δ s
    have hJ : J.Nonempty := by
      refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hspos, ?_⟩⟩
      simpa [δ, partialDegree_zero V hV hd] using hδpos
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image J id hJ
    obtain ⟨hjs, hjδ⟩ := Finset.mem_filter.mp hj
    have hjs' : j < s := Finset.mem_range.mp hjs
    have hδnext : δ (j + 1) = δ s := by
      have hle := partialDegree_mono V hV hd (show j + 1 ≤ s by omega)
      change δ (j + 1) ≤ δ s at hle
      by_contra hne
      have hlt : δ (j + 1) < δ s := lt_of_le_of_ne hle hne
      by_cases hlast : j + 1 = s
      · simpa [hlast] using hlt
      · have hmem : j + 1 ∈ J := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hlt⟩
        have hbad := hjmax (j + 1) hmem
        change j + 1 ≤ j at hbad
        omega
    have hsmall : δ j ≤ m := by dsimp [m]; omega
    have hlarge : m < δ (j + 1) := by rw [hδnext]; dsimp [m]; omega
    obtain ⟨W, hW, hVW, hWdim, hbounded, hshared⟩ := compatible_prefix_shared_rank
      V hV hd g hgbounds hgreg j m (by omega) hsmall hlarge
    have hWdegree := ih j hjs' (by omega) W hW hVW
    change γ ^ j * P j ≤ W.degree at hWdegree
    have hpure : AffineFamily.IsPure {W} (n - j) := by
      intro Z hZ
      have heq : Z = W := Finset.mem_singleton.mp hZ
      subst Z
      exact ⟨hW.isPrime, by omega⟩
    have hdefined : AffineFamily.ComponentsDefinedInDegree {W} m :=
      compatible_prefix_defined_in_degree g j m (by
        intro i hi
        exact (hgbounds i).2.trans
          ((partialDegree_mono V hV hd (by omega)).trans hsmall)) W hW
    have hWlower := hlower {W} (n - j) m hpure hm hdefined
    simp only [AffineFamily.hilbert, affine_locus_singleton, AffineFamily.degree,
      Finset.sum_singleton] at hWlower
    have hupper := irreducible_hilbert_upper_power U hU.isPrime (n - s) m (by omega) hm
    have hmono : (V.hilbert m : ℚ) ≤ (U.hilbert m : ℚ) := by
      exact_mod_cast V.hilbert_mono U hVU m
    have hcomparison : a * γ ^ j * P j * (m : ℚ) ^ (n - j) ≤
        (n + 1 : ℚ) ^ n * U.degree * (m : ℚ) ^ (n - s) := by
      calc
        a * γ ^ j * P j * (m : ℚ) ^ (n - j) =
            a * (γ ^ j * P j) * (m : ℚ) ^ (n - j) := by ring
        _ ≤ a * W.degree * (m : ℚ) ^ (n - j) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWdegree ha.le) (by positivity)
        _ ≤ (W.hilbert m : ℚ) := hWlower
        _ = (V.hilbert m : ℚ) := by rw [hshared]
        _ ≤ (U.hilbert m : ℚ) := hmono
        _ ≤ _ := hupper
    have hmpos : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
    have hpow : (m : ℚ) ^ (n - j) = (m : ℚ) ^ (s - j) * (m : ℚ) ^ (n - s) := by
      rw [← pow_add]
      congr 1
      omega
    have hineq : a * γ ^ j * P j * (m : ℚ) ^ (s - j) ≤ (n + 1 : ℚ) ^ n * U.degree := by
      apply (mul_le_mul_iff_left₀ (pow_pos hmpos (n - s))).mp
      rw [hpow] at hcomparison
      convert hcomparison using 1 <;> ring
    have htail : P s = P j * (δ s : ℚ) ^ (s - j) := by
      have hsum : s = j + (s - j) := by omega
      change (∏ t ∈ Finset.range s, (δ (t + 1) : ℚ)) = _
      rw [hsum, Finset.prod_range_add]
      rw [← hsum]
      change P j * (∏ t ∈ Finset.range (s - j), (δ (j + t + 1) : ℚ)) = _
      congr 1
      calc
        (∏ t ∈ Finset.range (s - j), (δ (j + t + 1) : ℚ)) =
            ∏ _t ∈ Finset.range (s - j), (δ s : ℚ) := by
          apply Finset.prod_congr rfl
          intro t ht
          have ht' := Finset.mem_range.mp ht
          have hlo := partialDegree_mono V hV hd (show j + 1 ≤ j + t + 1 by omega)
          have hhi := partialDegree_mono V hV hd (show j + t + 1 ≤ s by omega)
          have heq : δ (j + t + 1) = δ s := by
            change δ (j + 1) ≤ δ (j + t + 1) at hlo
            change δ (j + t + 1) ≤ δ s at hhi
            omega
          rw [heq]
        _ = (δ s : ℚ) ^ (s - j) := by simp
    change γ ^ s * P s ≤ U.degree
    rw [htail]
    apply prefix_budget_step a ((n + 1 : ℚ) ^ n) γ (P j) m (δ s) U.degree n j s
      (by positivity) hγ hγone (by dsimp [P]; positivity) hmpos.le (Nat.cast_nonneg _)
      (by exact_mod_cast (show δ s ≤ 2 * m by dsimp [m]; omega)) hjs' hsn hγsmall hineq

/-- Walsh's approximate complete-intersection producer, in the shared affine
model. The upper bounds are the nondecreasing partial degrees. -/
theorem walsh_description (n : ℕ) :
    ∃ Cdesc : ℝ, 1 ≤ Cdesc ∧
      ∀ (V : AffineVariety n) (c : ℕ), V.IsIrreducible →
        0 < c → V.dimension + c = n →
        ∃ (f : Fin c → Poly n) (d : Fin c → ℕ),
          (∀ i, 0 < (f i).totalDegree ∧ f i ∈ V.ideal ∧ (f i).totalDegree ≤ d i) ∧
          Monotone d ∧ V.IsComponentOf (Ideal.span (Set.range f)) ∧
          ((∏ i, d i : ℕ) : ℝ) ≤ Cdesc * (V.degree : ℝ) := by
  classical
  obtain ⟨a, ha, hlower⟩ := TrackA.poly_hilbert_at_L n
  let b : ℚ := (n + 1 : ℚ) ^ n
  let γ : ℚ := min 1 (a / (2 ^ n * b))
  have hb : 0 < b := by dsimp [b]; positivity
  have hden : (0 : ℚ) < 2 ^ n * b := by positivity
  have hγ : 0 < γ := lt_min (by norm_num) (div_pos ha hden)
  have hγone : γ ≤ 1 := min_le_left _ _
  have hγsmall : γ * 2 ^ n * (n + 1 : ℚ) ^ n ≤ a := by
    have hbound : γ ≤ a / (2 ^ n * b) := min_le_right _ _
    have hmul := (le_div_iff₀ hden).mp hbound
    simpa [b, mul_assoc] using hmul
  let Cdesc : ℚ := 1 / γ ^ n
  have hγn : 0 < γ ^ n := pow_pos hγ _
  have hCdesc : 1 ≤ Cdesc := by
    apply (le_div_iff₀ hγn).mpr
    simpa using pow_le_one₀ hγ.le hγone (n := n)
  refine ⟨(Cdesc : ℝ), by exact_mod_cast hCdesc, ?_⟩
  intro V c hV hc hd
  obtain ⟨f, hfbounds, hfcomp, hfreg⟩ := compatible_partial_cuts V hV hd
  let d : Fin c → ℕ := fun i => partialDegree V hV hd (i.val + 1)
  have hcomp : V.IsComponentOf (equationPrefixIdeal f c) := by
    rw [equationPrefixIdeal_full]
    exact hfcomp
  have hbudget := compatible_prefix_degree_lower V hV hd f
    (fun i => ⟨(hfbounds i).2.1, (hfbounds i).2.2⟩) hfreg
    a γ ha hγ hγone hγsmall hlower c le_rfl V hcomp le_rfl
  have hprod : (∏ t ∈ Finset.range c, (partialDegree V hV hd (t + 1) : ℚ)) =
      ((∏ i, d i : ℕ) : ℚ) := by
    simp only [Nat.cast_prod, d]
    exact (Fin.prod_univ_eq_prod_range
      (fun t => (partialDegree V hV hd (t + 1) : ℚ)) c).symm
  rw [hprod] at hbudget
  have hcn : c ≤ n := by omega
  have hpower : γ ^ n ≤ γ ^ c := pow_le_pow_of_le_one hγ.le hγone hcn
  have hbudget' : γ ^ n * ((∏ i, d i : ℕ) : ℚ) ≤ V.degree :=
    (mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg _)).trans hbudget
  have hfinal : ((∏ i, d i : ℕ) : ℚ) ≤ Cdesc * V.degree := by
    change _ ≤ (1 / γ ^ n) * V.degree
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ hγn).mpr
    simpa [mul_comm] using hbudget'
  refine ⟨f, d, hfbounds, ?_, hfcomp, by exact_mod_cast hfinal⟩
  intro i j hij
  exact partialDegree_mono V hV hd (Nat.succ_le_succ hij)

#print axioms walsh_description

theorem sample_common_linear_form {n : ℕ} (S : Finset (ProjectivePoint n)) :
    ∃ ℓ : Poly n, ℓ.IsHomogeneous 1 ∧
      ∀ p ∈ S, MvPolynomial.aeval p.rep ℓ ≠ 0 := by
  let H := MvPolynomial.homogeneousSubmodule (Fin n) ℂ 1
  let ev (p : S) : H →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval p.val.rep).toLinearMap.comp H.subtype
  let bad (p : S) := LinearMap.ker (ev p)
  have hbad : ∀ p, bad p ≠ ⊤ := by
    intro p htop
    have hz : p.val.rep = 0 := by
      funext i
      let x : H := ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩
      have hx : x ∈ bad p := by rw [htop]; exact Submodule.mem_top
      simpa [bad, ev, x] using hx
    exact p.val.rep_nonzero hz
  obtain ⟨ℓ, hℓ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨ℓ.val, ℓ.property, ?_⟩
  intro p hp hzero
  exact hℓ ⟨p, hp⟩ hzero

theorem projective_sample_card_le_hilbert {n : ℕ} (Y : ProjectiveVariety n)
    (S : Finset (ProjectivePoint n)) (L : ℕ)
    (hY : ∀ p ∈ S, p ∈ Y.points)
    (hsep : ∀ p ∈ S, ∃ (f : Poly n) (D : ℕ), D ≤ L ∧
      f.IsHomogeneous D ∧ MvPolynomial.aeval p.rep f ≠ 0 ∧
      ∀ q ∈ S, q ≠ p → MvPolynomial.aeval q.rep f = 0) :
    S.card ≤ Y.hilbert L := by
  obtain ⟨ℓ, hℓhom, hℓnonzero⟩ := sample_common_linear_form S
  choose f D hDL hhom hnonzero hvanish using fun p : S => hsep p.val p.property
  let F (p : S) : Poly n := f p * ℓ ^ (L - D p)
  have hFhom (p : S) : (F p).IsHomogeneous L := by
    simpa [F, Nat.add_sub_of_le (hDL p)] using (hhom p).mul (hℓhom.pow (L - D p))
  have hFnonzero (p : S) : MvPolynomial.aeval p.val.rep (F p) ≠ 0 := by
    simp only [F, map_mul, map_pow]
    exact mul_ne_zero (hnonzero p) (pow_ne_zero _ (hℓnonzero p.val p.property))
  let G (p : S) : Poly n :=
    MvPolynomial.C ((MvPolynomial.aeval p.val.rep (F p))⁻¹) * F p
  have hGhom (p : S) : (G p).IsHomogeneous L := by
    exact (hFhom p).C_mul _
  have hGval (p q : S) : MvPolynomial.aeval q.val.rep (G p) = if q = p then 1 else 0 := by
    by_cases hqp : q = p
    · subst q
      simp only [G, map_mul, MvPolynomial.aeval_C, if_pos rfl]
      exact inv_mul_cancel₀ (hFnonzero p)
    · have hval : q.val ≠ p.val := by intro heq; exact hqp (Subtype.ext heq)
      have hfzero := hvanish p q.val q.property hval
      simp only [G, F, map_mul, MvPolynomial.aeval_C, map_pow, hfzero, mul_zero,
        zero_mul, if_neg hqp]
  have hI (p : S) : Y.ideal ≤ RingHom.ker (MvPolynomial.aeval p.val.rep).toRingHom := by
    intro g hg
    exact hY p.val p.property p.val.rep p.val.rep_nonzero p.val.mk_rep g hg
  let e (p : S) : (Poly n ⧸ Y.ideal) →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ Y.ideal (MvPolynomial.aeval p.val.rep) (hI p)
  let ev : Y.restrictionSpace L →ₗ[ℂ] (S → ℂ) :=
    (LinearMap.pi (fun p => (e p).toLinearMap)).comp (Y.restrictionSpace L).subtype
  let columns (p : S) : Y.restrictionSpace L :=
    ⟨(Ideal.Quotient.mkₐ ℂ Y.ideal).toLinearMap (G p),
      Submodule.mem_map.mpr ⟨G p, hGhom p, rfl⟩⟩
  have hcolumns (p q : S) : ev (columns p) q = if q = p then 1 else 0 := by
    have hcomp : (e q).comp (Ideal.Quotient.mkₐ ℂ Y.ideal) = MvPolynomial.aeval q.val.rep :=
      Ideal.Quotient.liftₐ_comp Y.ideal (MvPolynomial.aeval q.val.rep) (hI q)
    change ((e q).comp (Ideal.Quotient.mkₐ ℂ Y.ideal)) (G p) = _
    rw [hcomp]
    exact hGval p q
  have hsurj : Function.Surjective ev := by
    intro values
    refine ⟨∑ p, values p • columns p, ?_⟩
    funext q
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp [hcolumns]
  have hdim := LinearMap.finrank_le_finrank_of_surjective hsurj
  simpa [ProjectiveVariety.hilbert, Module.finrank_fintype_fun_eq_card] using hdim

/-- The separator count used in concentration.tex:108–133, obtained from
independent restriction classes and the frozen projective Hilbert bound. -/
theorem projective_separator_count (n : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (A : ℝ), 1 ≤ A →
      ∀ P : Finset (ProjectivePoint n),
        (∀ p ∈ P, ∃ (f : Poly n) (D : ℕ), (D : ℝ) ≤ C0 * A ∧
          f.IsHomogeneous D ∧ MvPolynomial.aeval p.rep f ≠ 0 ∧
          ∀ q ∈ P, q ≠ p → MvPolynomial.aeval q.rep f = 0) →
        ∀ (Y : ProjectiveVariety n) (a : ℕ), Y.IsIrreducible →
          Y.dimension = a → a ≤ n →
          ((P.filter fun p => p ∈ Y.points).card : ℝ) ≤ B * (Y.degree : ℝ) * A ^ a := by
  classical
  let T : ℝ := C0 + 1 + n
  have hT : 1 ≤ T := by dsimp [T]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine ⟨T ^ n, one_le_pow₀ hT, ?_⟩
  intro A hA P hsep Y a hY hdim ha
  let L := Nat.ceil (C0 * A)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hCA : 0 ≤ C0 * A := mul_nonneg (zero_le_one.trans hC0) hA0
  have hL : (L : ℝ) ≤ C0 * A + 1 := (Nat.ceil_lt_add_one hCA).le
  let S := P.filter fun p => p ∈ Y.points
  have hcard : S.card ≤ Y.hilbert L := by
    apply projective_sample_card_le_hilbert Y S L
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp
      obtain ⟨f, D, hD, hhom, hnonzero, hzero⟩ := hsep p (Finset.mem_filter.mp hp).1
      refine ⟨f, D, ?_, hhom, hnonzero, ?_⟩
      · exact_mod_cast hD.trans (Nat.le_ceil (C0 * A))
      · intro q hq hqp
        exact hzero q (Finset.mem_filter.mp hq).1 hqp
  have hpure : ProjectiveFamily.IsPure {Y} a := by
    intro Z hZ
    have hZY : Z = Y := Finset.mem_singleton.mp hZ
    subst Z
    exact ⟨hY, hdim⟩
  have hupper := TrackA.poly_hilbert_projective_upper {Y} a hpure L
  simp only [ProjectiveFamily.hilbert, ProjectiveFamily.locus_singleton,
    ProjectiveFamily.degree, Finset.sum_singleton] at hupper
  have hupperR : (Y.hilbert L : ℝ) ≤ (Y.degree : ℝ) * ((L + a).choose a : ℝ) := by
    exact_mod_cast hupper
  have hdegree : (0 : ℝ) ≤ (Y.degree : ℝ) := by
    have hd : (1 : ℚ) ≤ Y.degree := by
      rw [← Y.degree_cone]
      exact Y.affineCone.one_le_degree hY.ne_top
    exact zero_le_one.trans (by exact_mod_cast hd)
  have hbase : (L + a : ℝ) ≤ T * A := by
    have ha' : (a : ℝ) ≤ n := by exact_mod_cast ha
    dsimp [T]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sub_nonneg.mpr hA)]
  have hbinom : ((L + a).choose a : ℝ) ≤ T ^ n * A ^ a := by
    calc
      ((L + a).choose a : ℝ) ≤ (L + a : ℝ) ^ a := by
        exact_mod_cast Nat.choose_le_pow (L + a) a
      _ ≤ (T * A) ^ a := pow_le_pow_left₀ (by positivity) hbase _
      _ = T ^ a * A ^ a := mul_pow _ _ _
      _ ≤ T ^ n * A ^ a := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hT ha) (pow_nonneg hA0 _)
  calc
    (S.card : ℝ) ≤ (Y.hilbert L : ℝ) := by exact_mod_cast hcard
    _ ≤ (Y.degree : ℝ) * ((L + a).choose a : ℝ) := hupperR
    _ ≤ (Y.degree : ℝ) * (T ^ n * A ^ a) :=
      mul_le_mul_of_nonneg_left hbinom hdegree
    _ = T ^ n * (Y.degree : ℝ) * A ^ a := by ring

theorem affineFiber_closure_irreducible {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℂ M] (L : Point n →ₗ[ℂ] M) (y : M)
    (hT : ∃ z : Point n, L z = y) :
    (AffineVariety.closure {z : Point n | L z = y}).IsIrreducible := by
  classical
  obtain ⟨z0, hz0⟩ := hT
  let K := LinearMap.ker L
  let b := Module.finBasis ℂ K
  let φ : AffineProjection (Module.finrank ℂ K) n :=
    { linear := K.subtype.comp b.equivFun.symm.toLinearMap
      offset := z0 }
  have hwhole : (AffineVariety.whole : AffineVariety (Module.finrank ℂ K)).points = Set.univ := by
    ext z
    simp [AffineVariety.whole, AffineVariety.points_ofIdeal, MvPolynomial.zeroLocus]
  have himage : φ.apply '' (AffineVariety.whole : AffineVariety (Module.finrank ℂ K)).points =
      {z : Point n | L z = y} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change L ((b.equivFun.symm x : K).val + z0) = y
      rw [map_add, show L (b.equivFun.symm x : K).val = 0 from
        LinearMap.mem_ker.mp (b.equivFun.symm x : K).property, zero_add]
      exact hz0
    · intro hz
      let w : K := ⟨z - z0, by change L (z - z0) = 0; rw [map_sub, hz, hz0, sub_self]⟩
      refine ⟨b.equivFun w, by rw [hwhole]; exact Set.mem_univ _, ?_⟩
      change (b.equivFun.symm (b.equivFun w) : K).val + z0 = z
      rw [LinearEquiv.symm_apply_apply]
      dsimp [w]
      abel
  have hwholeI : (AffineVariety.whole : AffineVariety (Module.finrank ℂ K)).IsIrreducible := by
    change (⊥ : Ideal (Poly (Module.finrank ℂ K))).radical.IsPrime
    rw [Ideal.radical_bot_of_isReduced]
    infer_instance
  have hirr := φ.image_irreducible AffineVariety.whole hwholeI
  rw [φ.image_eq_closure, himage] at hirr
  exact hirr

theorem evaluationFlat_closure_irreducible {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e) :
    (AffineVariety.closure (evaluationFlat C p)).IsIrreducible := by
  let v := firstPoint p.rep
  let y := covectorOfPoint (secondPoint p.rep)
  let L : Point (skewDim e) →ₗ[ℂ] Module.Dual ℂ (Point e) :=
    (alternatingEvaluation v).comp C.decode.toLinearMap
  have hv : v ≠ 0 := hp.2
  have hy : y v = 0 := hp.1
  obtain ⟨D, hD, hEval⟩ := alternating_evaluation_surjective v hv y hy
  apply affineFiber_closure_irreducible L y
  refine ⟨C.decode.symm ⟨D, hD⟩, ?_⟩
  change alternatingEvaluation v (C.decode (C.decode.symm ⟨D, hD⟩)) = y
  rw [LinearEquiv.apply_symm_apply]
  exact hEval

/-- An irreducible affine set contained in a finite component union lies in
one component; no unique-component choice is required for counting. -/
theorem contained_in_component {n : ℕ} (V : AffineVariety n) (T : Set (Point n))
    (hT : (AffineVariety.closure T).IsIrreducible) (hTV : T ⊆ V.points) :
    ∃ W : V.Component, T ⊆ W.variety.points := by
  classical
  have hle : V.ideal ≤ (AffineVariety.closure T).ideal := by
    intro f hf z hz
    exact hTV hz f hf
  letI : (AffineVariety.closure T).ideal.IsPrime := hT
  obtain ⟨Q, hQ, hQT⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨⟨Q, hQ⟩, ?_⟩
  exact (AffineVariety.subset_closure T).trans (MvPolynomial.zeroLocus_anti_mono hQT)

/-- The geometric output of the controlled ruling construction. It records
coverage and incidence properties, without asserting a sample-count bound. -/
structure ControlledRulings {e : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (M : ℕ) (L : ℝ) where
  exceptional : Poly (skewDim e)
  section_nonzero : exceptional ∉ V.ideal
  section_degree : (exceptional.totalDegree : ℝ) ≤ L
  size : ℕ
  size_bound : size ≤ M
  incidences : Fin size → AffineVariety (skewDim e + e)
  charts : Fin size → Fin e
  fiber_dimensions : Fin size → ℕ
  properties : ∀ i, IsRulingIncidence C V (incidences i) exceptional (charts i) (fiber_dimensions i) M
  parameter_irreducible : ∀ i, (parameterClosure C (incidences i) exceptional).IsIrreducible
  coverage : ∀ p ∈ affineParameters e, evaluationFlat C p ⊆ V.points →
    evaluationFlat C p ⊆ (V.cut exceptional).points ∨
      ∃ i, p ∈ parameterImage C (incidences i) exceptional

/-- Apply the frozen Jacobian germ criterion after adjoining a finite generating
set for I(V). This makes its smooth-locus conclusion about V itself. -/
theorem smooth_of_jacobian_minor {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (k : ℕ) (hdim : V.dimension = k) (E : List (Poly n))
    (hE : ∀ f ∈ E, f ∈ V.ideal) (m : Poly n)
    (hm : m ∈ TrackA.jacobianMinors E (n - k))
    (x : Point n) (hx : x ∈ V.points) (hmx : MvPolynomial.eval x m ≠ 0) :
    V.IsSmoothAt x := by
  classical
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian V.ideal
  let E' := E ++ S.toList
  have hAll : ∀ f ∈ E', f ∈ V.ideal := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hE f hf
    · rw [← hS]
      exact Ideal.subset_span (by simpa using hf)
  have hspan : Ideal.span {f : Poly n | f ∈ E'} = V.ideal := by
    apply le_antisymm
    · exact Ideal.span_le.mpr hAll
    · rw [← hS]
      apply Ideal.span_mono
      intro f hf
      exact List.mem_append_right E (by simpa using hf)
  have hEq : TrackA.equationLocus E' = V := by
    apply AffineVariety.ext
    change (Ideal.span {f : Poly n | f ∈ E'}).radical = V.ideal
    rw [hspan, V.isRadical.radical]
  have hm' : m ∈ TrackA.jacobianMinors E' (n - k) := by
    obtain ⟨rows, cols, rfl⟩ := hm
    let rows' : Fin (n - k) ↪ Fin E'.length :=
      { toFun := fun i => ⟨(rows i).val, by dsimp [E']; rw [List.length_append]; omega⟩
        inj' := by
          intro i j hij
          apply rows.injective
          apply Fin.ext
          exact congrArg (fun q : Fin E'.length => q.val) hij }
    refine ⟨rows', cols, ?_⟩
    congr 1
    apply Matrix.ext
    intro i j
    change MvPolynomial.pderiv (cols j) (E.get (rows i)) =
      MvPolynomial.pderiv (cols j) (E'.get (rows' i))
    congr 1
    change E[(rows i).val] = (E ++ S.toList)[(rows i).val]
    exact (List.getElem_append_left (rows i).isLt).symm
  have hk : k ≤ n := by rw [← hdim]; exact Bridges.affine_dimension_le V
  have hF : AffineFamily.IsPure {V} k := by
    intro W hW
    have heq : W = V := Finset.mem_singleton.mp hW
    subst W
    exact ⟨hV, hdim⟩
  have hAllF : ∀ f ∈ E', f ∈ (AffineFamily.locus {V}).ideal := by
    simpa only [affine_locus_singleton] using hAll
  have hxF : x ∈ (AffineFamily.locus {V}).points := by
    simpa only [affine_locus_singleton] using hx
  obtain ⟨hgerm, hsmooth, hlocal, hunique⟩ := TrackA.request_pure_family_jacobian_germ
    {V} k hk hF E' hAllF x hxF ⟨m, hm', hmx⟩
  simpa only [hEq] using hsmooth

theorem singleton_from_affine_list {n : ℕ} (V : AffineVariety n) (L : ℕ)
    (hL : 1 ≤ L) (hdefined : AffineFamily.ComponentsDefinedInDegree {V} L) :
    TrackA.FromAffineLists {V} L := by
  refine ⟨1, fun _ => {V}, fun _ => L, (fun _ => ⟨hL, hdefined⟩), ?_, ?_⟩
  · intro W
    constructor
    · intro hW
      exact ⟨0, hW⟩
    · rintro ⟨i, hi⟩
      exact hi
  · simp

/-- Effective generic equations for a single component. Frozen whole-family
regularity excludes its only possible bad component once D=2CL. -/
theorem regular_equations_from_components (n : ℕ) :
    ∃ Creg : ℕ, 1 ≤ Creg ∧
      ∀ (V : AffineVariety n) (c L : ℕ), V.IsIrreducible →
        V.dimension + c = n → 1 ≤ L → AffineFamily.ComponentsDefinedInDegree {V} L →
        ∃ (g : Fin c → Poly n) (H : Poly n),
          (∀ i, g i ∈ V.ideal ∧ (g i).totalDegree ≤ Creg * L) ∧
          H ∉ V.ideal ∧ H.totalDegree ≤ Creg * L ∧
          ∀ x ∈ V.points, MvPolynomial.eval x H ≠ 0 →
            V.IsSmoothAt x ∧ V.tangentSpace x = ⨅ i : Fin c, LinearMap.ker (differential (g i) x) := by
  classical
  obtain ⟨C, hC, hregular⟩ := TrackA.poly_regularity_exceptional_degree n
  let Creg := 2 * C * (n + 1)
  refine ⟨Creg, by dsimp [Creg]; nlinarith, ?_⟩
  intro V c L hV hcodim hL hdefined
  have hk : V.dimension ≤ n := Bridges.affine_dimension_le V
  have hpure : AffineFamily.IsPure {V} V.dimension := by
    intro W hW
    have heq : W = V := Finset.mem_singleton.mp hW
    subst W
    exact ⟨hV, rfl⟩
  let D := 2 * C * L
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨bad, hbad, hbaddegree, hrank⟩ := hregular {V} V.dimension L D hk hpure hL
    (singleton_from_affine_list V L hL hdefined) (by dsimp [D]; nlinarith)
  have hVnot : V ∉ bad := by
    intro hmem
    have hbadEq : bad = {V} := le_antisymm hbad (Finset.singleton_subset_iff.mpr hmem)
    simp only [hbadEq, AffineFamily.degree, Finset.sum_singleton] at hbaddegree
    have hDpos : (0 : ℚ) < D := by exact_mod_cast hD
    have hmul := (le_div_iff₀ hDpos).mp hbaddegree
    have hprodpos : (0 : ℚ) < (C : ℚ) * V.degree * (L : ℚ) :=
      mul_pos (mul_pos (by exact_mod_cast hC) (zero_lt_one.trans_le (V.one_le_degree hV.ne_top)))
        (by exact_mod_cast (show 0 < L by omega))
    have hmul' : 2 * ((C : ℚ) * V.degree * (L : ℚ)) ≤ (C : ℚ) * V.degree * (L : ℚ) := by
      convert hmul using 1 <;> simp only [D, Nat.cast_mul, Nat.cast_ofNat] <;> ring
    linarith
  obtain ⟨E, hE, hspan⟩ := TrackA.bounded_equation_list {V} D
  have hEideal : ∀ f ∈ E, f ∈ V.ideal := by
    intro f hf
    simpa only [affine_locus_singleton] using (hE f hf).1
  obtain ⟨m, hm, hmnot⟩ := TrackA.generic_rank_detected_by_minor {V} V V.dimension D hk E hE hspan
    (hrank V (Finset.mem_singleton_self V) hVnot)
  have hc : n - V.dimension = c := by omega
  have hm' : m ∈ TrackA.jacobianMinors E c := by simpa only [hc] using hm
  obtain ⟨rows, cols, hmEq⟩ := hm'
  let g : Fin c → Poly n := fun i => E.get (rows i)
  have hgreg : ∀ i, g i ∈ V.ideal ∧ (g i).totalDegree ≤ Creg * L := by
    intro i
    have h := hE (E.get (rows i)) (List.get_mem _ _)
    refine ⟨hEideal _ (List.get_mem _ _), h.2.trans ?_⟩
    calc
      D = D * 1 := (Nat.mul_one D).symm
      _ ≤ D * (n + 1) := Nat.mul_le_mul_left D (by omega)
      _ = Creg * L := by dsimp [D, Creg]; ring
  have hdegree : m.totalDegree ≤ Creg * L := by
    have hmdeg := TrackA.jacobian_minor_totalDegree E D c (fun f hf => (hE f hf).2) m
      (by simpa only [hc] using hm)
    have hcn : c ≤ n := by omega
    apply hmdeg.trans
    calc
      c * (D - 1) ≤ n * D := Nat.mul_le_mul hcn (Nat.sub_le _ _)
      _ ≤ Creg * L := by
        calc
          n * D ≤ (n + 1) * D := Nat.mul_le_mul_right D (by omega)
          _ = Creg * L := by dsimp [D, Creg]; ring
  refine ⟨g, m, hgreg, hmnot, hdegree, ?_⟩
  intro x hx hmx
  have hsmooth := smooth_of_jacobian_minor V hV V.dimension rfl E hEideal m hm x hx hmx
  refine ⟨hsmooth, ?_⟩
  let B : Matrix (Fin c) (Fin n) ℂ := fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (g i))
  have hBdet : (B.submatrix id cols).det ≠ 0 := by
    rw [hmEq, (MvPolynomial.eval x).map_det] at hmx
    exact hmx
  have hBrank : c ≤ B.rank := by
    have h := B.rank_submatrix_le id cols
    rw [Matrix.rank_of_det_ne_zero hBdet, Fintype.card_fin] at h
    exact h
  have hkerdim : Module.finrank ℂ (LinearMap.ker B.mulVecLin) ≤ V.dimension := by
    have hrankdim := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    change B.rank + Module.finrank ℂ (LinearMap.ker B.mulVecLin) = Module.finrank ℂ (Point n) at hrankdim
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrankdim
    omega
  have hker : LinearMap.ker B.mulVecLin = ⨅ i : Fin c, LinearMap.ker (differential (g i) x) := by
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff]
    simp [B, differential, Matrix.mulVec, dotProduct, MvPolynomial.aeval_eq_eval]
  have htan : V.tangentSpace x ≤ LinearMap.ker B.mulVecLin := by
    rw [hker]
    apply le_iInf
    intro i
    exact iInf_le_of_le ⟨g i, (hgreg i).1⟩ le_rfl
  have htandim : Module.finrank ℂ (V.tangentSpace x) = V.dimension :=
    hsmooth.2.trans (V.localDimension_eq_dimension x hV hx)
  have heq : V.tangentSpace x = LinearMap.ker B.mulVecLin :=
    Submodule.eq_of_le_of_finrank_le htan (by rw [htandim]; exact hkerdim)
  exact heq.trans hker

def normalizedDirectionProjection {e : ℕ} (a : Fin e) (v : Point e) : Point e →ₗ[ℂ] Point e :=
  LinearMap.id - (LinearMap.proj a).smulRight v

def normalizedDirectionPullback {e : ℕ} (a : Fin e) (v : Point e) :
    alternatingForms (U := Point e) →ₗ[ℂ] alternatingForms (U := Point e) where
  toFun D := ⟨D.val.comp (normalizedDirectionProjection a v) (normalizedDirectionProjection a v),
    fun x => D.property ((normalizedDirectionProjection a v) x)⟩
  map_add' D E := by
    apply Subtype.ext
    apply LinearMap.BilinForm.ext
    intro x y
    simp [LinearMap.BilinForm.comp_apply]
  map_smul' c D := by
    apply Subtype.ext
    apply LinearMap.BilinForm.ext
    intro x y
    simp [LinearMap.BilinForm.comp_apply]

def coordinateSkewPair (e : ℕ) (i j : Fin e) : alternatingForms (U := Point e) :=
  ⟨MBFibersAux.skewPair e i j, MBFibersAux.skewPair_isAlt e i j⟩

def normalizedKernelPair {e : ℕ} (a : Fin e) (v : Point e) (i j : Fin e) :
    alternatingForms (U := Point e) :=
  normalizedDirectionPullback a v (coordinateSkewPair e i j)

theorem normalizedDirectionPullback_eval_zero {e : ℕ} (a : Fin e) (v : Point e)
    (hva : v a = 1) (D : alternatingForms (U := Point e)) :
    alternatingEvaluation v (normalizedDirectionPullback a v D) = 0 := by
  have hPv : normalizedDirectionProjection a v v = 0 := by
    simp [normalizedDirectionProjection, hva]
  apply LinearMap.ext
  intro x
  change D.val (normalizedDirectionProjection a v v) (normalizedDirectionProjection a v x) = 0
  rw [hPv, map_zero, LinearMap.zero_apply]

theorem normalizedDirectionPullback_eq {e : ℕ} (a : Fin e) (v : Point e)
    (D : alternatingForms (U := Point e)) (hDv : alternatingEvaluation v D = 0) :
    normalizedDirectionPullback a v D = D := by
  apply Subtype.ext
  apply LinearMap.BilinForm.ext
  intro x y
  have hvD : D.val v = 0 := hDv
  have hxv : D.val x v = 0 := by
    have h := D.property.neg_eq v x
    rw [hvD, LinearMap.zero_apply, neg_zero] at h
    exact h.symm
  change D.val (x - x a • v) (y - y a • v) = D.val x y
  simp [map_sub, map_smul, hvD, hxv]

theorem normalizedKernelPair_expansion {e : ℕ} (a : Fin e) (v : Point e) (i j : Fin e) :
    normalizedKernelPair a v i j = coordinateSkewPair e i j -
      v j • coordinateSkewPair e i a - v i • coordinateSkewPair e a j := by
  apply Subtype.ext
  change (MBFibersAux.skewPair e i j).comp (normalizedDirectionProjection a v)
      (normalizedDirectionProjection a v) = MBFibersAux.skewPair e i j -
        v j • MBFibersAux.skewPair e i a - v i • MBFibersAux.skewPair e a j
  apply LinearMap.BilinForm.ext
  intro x y
  simp only [normalizedKernelPair, normalizedDirectionPullback, coordinateSkewPair,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.BilinForm.comp_apply,
    normalizedDirectionProjection, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, MBFibersAux.skewPair,
    LinearMap.BilinForm.linMulLin_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.smul_apply]
  ring

theorem normalized_skew_kernel_span {e : ℕ} (a : Fin e) (v : Point e) (hva : v a = 1) :
    LinearMap.ker (alternatingEvaluation v) =
      Submodule.span ℂ (Set.range (fun p : Fin e × Fin e => normalizedKernelPair a v p.1 p.2)) := by
  classical
  let S := Submodule.span ℂ (Set.range (fun p : Fin e × Fin e => normalizedKernelPair a v p.1 p.2))
  have hmap : (Submodule.span ℂ (Set.range (MBFibersAux.skewElt e))).map
      (normalizedDirectionPullback a v) ≤ S := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro D ⟨p, rfl⟩
    exact Submodule.subset_span ⟨p.val, rfl⟩
  apply le_antisymm
  · intro D hD
    have hDspan : D ∈ Submodule.span ℂ (Set.range (MBFibersAux.skewElt e)) := by
      rw [MBFibersAux.skewElt_span]
      exact Submodule.mem_top
    have hPB := hmap (Submodule.mem_map.mpr ⟨D, hDspan, rfl⟩)
    rw [normalizedDirectionPullback_eq a v D (LinearMap.mem_ker.mp hD)] at hPB
    exact hPB
  · apply Submodule.span_le.mpr
    rintro D ⟨p, rfl⟩
    exact normalizedDirectionPullback_eval_zero a v hva (coordinateSkewPair e p.1 p.2)

theorem coordinateSkewPair_flip (e : ℕ) (i j : Fin e) :
    coordinateSkewPair e i j = -coordinateSkewPair e j i := by
  apply Subtype.ext
  change MBFibersAux.skewPair e i j = -MBFibersAux.skewPair e j i
  unfold MBFibersAux.skewPair
  abel

theorem coordinateSkewPair_self (e : ℕ) (i : Fin e) : coordinateSkewPair e i i = 0 := by
  apply Subtype.ext
  change MBFibersAux.skewPair e i i = 0
  simp [MBFibersAux.skewPair]

def normalCoordinates {e : ℕ} (α : alternatingForms (U := Point e) →ₗ[ℂ] ℂ) :
    Fin e → Fin e → ℂ := fun i j => α (coordinateSkewPair e i j)

theorem normal_map_neg {e : ℕ} (α : alternatingForms (U := Point e) →ₗ[ℂ] ℂ)
    (D : alternatingForms (U := Point e)) : α (-D) = -α D := by
  have h := congrArg α (neg_add_cancel D)
  rw [α.map_add, α.map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem normal_map_sub {e : ℕ} (α : alternatingForms (U := Point e) →ₗ[ℂ] ℂ)
    (D E : alternatingForms (U := Point e)) : α (D - E) = α D - α E := by
  have hsub : D - E = D + (-E) := by
    apply Subtype.ext
    apply LinearMap.BilinForm.ext
    intro x y
    change D.val x y - E.val x y = D.val x y + -E.val x y
    ring
  rw [hsub, α.map_add, normal_map_neg]
  ring

theorem normalCoordinates_flip {e : ℕ} (α : alternatingForms (U := Point e) →ₗ[ℂ] ℂ)
    (i j : Fin e) : normalCoordinates α i j = -normalCoordinates α j i := by
  unfold normalCoordinates
  rw [coordinateSkewPair_flip]
  exact normal_map_neg α _

theorem normalCoordinates_self {e : ℕ} (α : alternatingForms (U := Point e) →ₗ[ℂ] ℂ)
    (i : Fin e) : normalCoordinates α i i = 0 := by
  simp [normalCoordinates, coordinateSkewPair_self]

theorem normalCoordinates_injective (e : ℕ) :
    Function.Injective (normalCoordinates (e := e)) := by
  intro α β h
  have hspan : Submodule.span ℂ (Set.range (MBFibersAux.skewElt e)) ≤ LinearMap.ker (α - β) := by
    apply Submodule.span_le.mpr
    rintro D ⟨p, rfl⟩
    have hp := congrFun (congrFun h p.val.1) p.val.2
    change α (MBFibersAux.skewElt e p) - β (MBFibersAux.skewElt e p) = 0
    exact sub_eq_zero.mpr hp
  apply LinearMap.ext
  intro D
  have hD : D ∈ Submodule.span ℂ (Set.range (MBFibersAux.skewElt e)) := by
    rw [MBFibersAux.skewElt_span]
    exact Submodule.mem_top
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hspan hD))

theorem normalizedKernelPair_normal {e : ℕ} (α : alternatingForms (U := Point e) →ₗ[ℂ] ℂ)
    (a : Fin e) (v : Point e) (i j : Fin e) :
    α (normalizedKernelPair a v i j) = normalCoordinates α i j +
      v j * normalCoordinates α a i - v i * normalCoordinates α a j := by
  rw [normalizedKernelPair_expansion]
  rw [normal_map_sub, normal_map_sub, α.map_smul, α.map_smul]
  simp only [smul_eq_mul]
  change normalCoordinates α i j - v j * normalCoordinates α i a -
    v i * normalCoordinates α a j = _
  rw [normalCoordinates_flip α i a]
  ring

def SkewChartConstraints {K : Type*} [Field K] {e : ℕ}
    (w : Fin e → Fin e → K) (a : Fin e) (v : Fin e → K) : Prop :=
  ∀ i j, w i j = v i * w a j - v j * w a i

theorem annihilates_skew_kernel_iff {e : ℕ} (α : alternatingForms (U := Point e) →ₗ[ℂ] ℂ)
    (a : Fin e) (v : Point e) (hva : v a = 1) :
    LinearMap.ker (alternatingEvaluation v) ≤ LinearMap.ker α ↔
      SkewChartConstraints (normalCoordinates α) a v := by
  rw [normalized_skew_kernel_span a v hva]
  constructor
  · intro h i j
    have hmem := h (Submodule.subset_span ⟨(i, j), rfl⟩)
    have hz := LinearMap.mem_ker.mp hmem
    rw [normalizedKernelPair_normal] at hz
    linear_combination hz
  · intro h
    apply Submodule.span_le.mpr
    rintro D ⟨p, rfl⟩
    change α (normalizedKernelPair a v p.1 p.2) = 0
    rw [normalizedKernelPair_normal]
    linear_combination h p.1 p.2

def directionGraph {K : Type*} [Field K] {e : ℕ}
    (w : Fin e → Fin e → K) (a b : Fin e) (t : K) : Fin e → K :=
  fun i => (w i b + t * w a i) / w a b

def directionResidualConstant {K : Type*} [Field K] {e : ℕ}
    (w u : Fin e → Fin e → K) (a b i j : Fin e) : K :=
  u i j * w a b - w i b * u a j + w j b * u a i

def directionResidualLinear {K : Type*} [Field K] {e : ℕ}
    (w u : Fin e → Fin e → K) (a b i j : Fin e) : K :=
  w a j * u a i - w a i * u a j

theorem directionGraph_of_constraints {K : Type*} [Field K] {e : ℕ}
    (w : Fin e → Fin e → K) (a b : Fin e) (hwpivot : w a b ≠ 0)
    (v : Fin e → K) (hv : SkewChartConstraints w a v) :
    v = directionGraph w a b (v b) := by
  funext i
  apply (eq_div_iff hwpivot).mpr
  have h := hv i b
  linear_combination -h

theorem directionGraph_normalized {K : Type*} [Field K] {e : ℕ}
    (w : Fin e → Fin e → K) (a b : Fin e) (hwpivot : w a b ≠ 0)
    (hwa : w a a = 0) (hwb : w b b = 0) (t : K) :
    directionGraph w a b t a = 1 ∧ directionGraph w a b t b = t := by
  simp [directionGraph, hwa, hwb, hwpivot]

theorem directionGraph_constraints_iff {K : Type*} [Field K] {e : ℕ}
    (w u : Fin e → Fin e → K) (a b : Fin e) (hwpivot : w a b ≠ 0) (t : K) :
    SkewChartConstraints u a (directionGraph w a b t) ↔
      ∀ i j, directionResidualConstant w u a b i j + t * directionResidualLinear w u a b i j = 0 := by
  have hid (i j : Fin e) :
      directionResidualConstant w u a b i j + t * directionResidualLinear w u a b i j =
        (u i j - directionGraph w a b t i * u a j + directionGraph w a b t j * u a i) * w a b := by
    dsimp [directionResidualConstant, directionResidualLinear, directionGraph]
    field_simp [hwpivot]
    ring
  constructor
  · intro hv i j
    rw [hid]
    have hz : u i j - directionGraph w a b t i * u a j + directionGraph w a b t j * u a i = 0 := by
      linear_combination hv i j
    rw [hz, zero_mul]
  · intro h i j
    have hm := h i j
    rw [hid] at hm
    have hz := (mul_eq_zero.mp hm).resolve_right hwpivot
    linear_combination hz

/-- A full affine line of normalized directions forces every additional
conormal to be proportional to the first. -/
theorem direction_line_normals_proportional {K : Type*} [Field K] {e : ℕ}
    (w u : Fin e → Fin e → K) (a b : Fin e) (hwpivot : w a b ≠ 0)
    (hw : ∀ i j, directionResidualConstant w w a b i j = 0)
    (hu0 : ∀ i j, directionResidualConstant w u a b i j = 0)
    (hu1 : ∀ i j, directionResidualLinear w u a b i j = 0) :
    ∀ i j, u i j = (u a b / w a b) * w i j := by
  have haj (j : Fin e) : u a j * w a b = u a b * w a j := by
    have h := hu1 b j
    dsimp [directionResidualLinear] at h
    linear_combination -h
  intro i j
  have h (i j : Fin e) : (u i j * w a b - w i b * u a j + w j b * u a i) * w a b = 0 := by
    have hz := hu0 i j
    dsimp [directionResidualConstant] at hz
    exact mul_eq_zero_of_left hz _
  have hwi := hw i j
  dsimp [directionResidualConstant] at hwi
  have hprod : (u i j * w a b - u a b * w i j) * w a b = 0 := by
    linear_combination h i j - w j b * haj i + w i b * haj j - u a b * hwi
  have hcancel := (mul_eq_zero.mp hprod).resolve_right hwpivot
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hwpivot).mpr (sub_eq_zero.mp hcancel)

theorem differential_apply_sum {n : ℕ} (f : Poly n) (x d : Point n) :
    differential f x d = ∑ i : Fin n, MvPolynomial.aeval x (MvPolynomial.pderiv i f) * d i := by
  simp [differential, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem differential_mul_apply {n : ℕ} (f g : Poly n) (x d : Point n) :
    differential (f * g) x d = MvPolynomial.aeval x f * differential g x d +
      MvPolynomial.aeval x g * differential f x d := by
  simp only [differential_apply_sum]
  calc
    (∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i (f * g)) * d i) =
        ∑ i, (MvPolynomial.aeval x f * MvPolynomial.aeval x (MvPolynomial.pderiv i g) +
          MvPolynomial.aeval x g * MvPolynomial.aeval x (MvPolynomial.pderiv i f)) * d i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Derivation.leibniz]
      simp [smul_eq_mul]
    _ = _ := by
      simp_rw [add_mul, mul_assoc]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem differential_X_apply {n : ℕ} (i : Fin n) (x d : Point n) :
    differential (MvPolynomial.X i : Poly n) x d = d i := by
  simp [differential_apply_sum, MvPolynomial.pderiv_X, Pi.single_apply]

def polynomialLine {n : ℕ} (x d : Point n) : Poly n →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (d i))

theorem eval_polynomialLine {n : ℕ} (x d : Point n) (f : Poly n) (t : ℂ) :
    Polynomial.aeval t (polynomialLine x d f) = MvPolynomial.aeval (x + t • d) f := by
  unfold polynomialLine
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun y : Point n => MvPolynomial.aeval y f)
  funext i
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply] <;> ring

theorem polynomialLine_derivative_zero {n : ℕ} (f : Poly n) (x d : Point n) :
    Polynomial.aeval 0 (polynomialLine x d f).derivative = differential f x d := by
  have heval (g : Poly n) : Polynomial.aeval 0 (polynomialLine x d g) = MvPolynomial.aeval x g := by
    simpa using eval_polynomialLine x d g 0
  induction f using MvPolynomial.induction_on with
  | C c => simp [polynomialLine, differential_apply_sum, MvPolynomial.pderiv_C]
  | add f g hf hg =>
    rw [map_add, Polynomial.derivative_add, map_add, hf, hg]
    simp [differential_apply_sum, map_add, add_mul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    have hXi : Polynomial.aeval 0 (polynomialLine x d (MvPolynomial.X i)).derivative = d i := by
      simp [polynomialLine]
    rw [map_mul, Polynomial.derivative_mul, map_add, map_mul, map_mul, hf, hXi, heval, heval]
    rw [differential_mul_apply, differential_X_apply, MvPolynomial.aeval_X]
    ring

theorem polynomial_line_differential_zero {n : ℕ} (f : Poly n) (x d : Point n)
    (hzero : ∀ t : ℂ, MvPolynomial.aeval (x + t • d) f = 0) : differential f x d = 0 := by
  have hline : polynomialLine x d f = 0 := by
    apply Polynomial.funext
    intro t
    change Polynomial.aeval t (polynomialLine x d f) = Polynomial.aeval t 0
    rw [map_zero, eval_polynomialLine]
    exact hzero t
  have h := polynomialLine_derivative_zero f x d
  rw [hline] at h
  simpa using h.symm

/-- Every direction of a genuinely contained evaluation flat is tangent to the
carrier, by differentiating its polynomial identities along the full flat. -/
theorem evaluationFlat_direction_tangent {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (V : AffineVariety (skewDim e))
    (hflat : evaluationFlat C p ⊆ V.points) (x : Point (skewDim e))
    (hx : x ∈ evaluationFlat C p) (d : Point (skewDim e))
    (hd : alternatingEvaluation (firstPoint p.rep) (C.decode d) = 0) :
    d ∈ V.tangentSpace x := by
  rw [AffineVariety.tangentSpace, Submodule.mem_iInf]
  intro f
  apply polynomial_line_differential_zero f.val x d
  intro t
  have hxt : x + t • d ∈ evaluationFlat C p := by
    change alternatingEvaluation (firstPoint p.rep) (C.decode (x + t • d)) =
      covectorOfPoint (secondPoint p.rep)
    rw [map_add, map_smul, map_add, map_smul, hd, smul_zero, add_zero]
    exact hx
  exact hflat hxt f.val f.property

def normalPolynomial {e : ℕ} (C : SkewCoordinates e) (f : Poly (skewDim e))
    (i j : Fin e) : Poly (skewDim e) :=
  ∑ k : Fin (skewDim e), MvPolynomial.C ((C.decode.symm (coordinateSkewPair e i j)) k) *
    MvPolynomial.pderiv k f

theorem eval_normalPolynomial {e : ℕ} (C : SkewCoordinates e) (f : Poly (skewDim e))
    (x : Point (skewDim e)) (i j : Fin e) :
    MvPolynomial.aeval x (normalPolynomial C f i j) =
      normalCoordinates ((differential f x).comp C.decode.symm.toLinearMap) i j := by
  simp only [normalPolynomial, map_sum, map_mul, MvPolynomial.aeval_C,
    normalCoordinates, LinearMap.comp_apply]
  rw [differential_apply_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  exact mul_comm _ _

theorem normalPolynomial_flip {e : ℕ} (C : SkewCoordinates e) (f : Poly (skewDim e))
    (i j : Fin e) : normalPolynomial C f i j = -normalPolynomial C f j i := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x (normalPolynomial C f i j) = MvPolynomial.aeval x (-normalPolynomial C f j i)
  rw [map_neg, eval_normalPolynomial, eval_normalPolynomial]
  exact normalCoordinates_flip _ i j

theorem normalPolynomial_self {e : ℕ} (C : SkewCoordinates e) (f : Poly (skewDim e))
    (i : Fin e) : normalPolynomial C f i i = 0 := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x (normalPolynomial C f i i) = MvPolynomial.aeval x 0
  rw [map_zero, eval_normalPolynomial]
  exact normalCoordinates_self _ i

theorem normalPolynomial_degree_le {e : ℕ} (C : SkewCoordinates e) (f : Poly (skewDim e))
    (D : ℕ) (hf : f.totalDegree ≤ D) (i j : Fin e) :
    (normalPolynomial C f i j).totalDegree ≤ D - 1 := by
  unfold normalPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  calc
    (MvPolynomial.C ((C.decode.symm (coordinateSkewPair e i j)) k) * MvPolynomial.pderiv k f).totalDegree ≤
        (MvPolynomial.C ((C.decode.symm (coordinateSkewPair e i j)) k)).totalDegree +
          (MvPolynomial.pderiv k f).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (MvPolynomial.pderiv k f).totalDegree := by simp
    _ ≤ D - 1 := OAI.QuarticPowerFree.pderiv_degree_le_sub_one f D hf k

theorem contained_flat_normal_constraints {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (V : AffineVariety (skewDim e))
    (hflat : evaluationFlat C p ⊆ V.points) (x : Point (skewDim e))
    (hx : x ∈ evaluationFlat C p) (f : Poly (skewDim e)) (hf : f ∈ V.ideal)
    (v : Point e) (a : Fin e) (hva : v a = 1) (t : ℂ)
    (ht : firstPoint p.rep = t • v) :
    SkewChartConstraints (fun i j => MvPolynomial.aeval x (normalPolynomial C f i j)) a v := by
  let α := (differential f x).comp C.decode.symm.toLinearMap
  have hker : LinearMap.ker (alternatingEvaluation v) ≤ LinearMap.ker α := by
    intro D hD
    have hd : alternatingEvaluation (firstPoint p.rep) (C.decode (C.decode.symm D)) = 0 := by
      rw [LinearEquiv.apply_symm_apply]
      change D.val (firstPoint p.rep) = 0
      rw [ht, map_smul]
      have hDv : D.val v = 0 := hD
      rw [hDv, smul_zero]
    have htan := evaluationFlat_direction_tangent C p V hflat x hx (C.decode.symm D) hd
    rw [AffineVariety.tangentSpace, Submodule.mem_iInf] at htan
    exact htan ⟨f, hf⟩
  have h := (annihilates_skew_kernel_iff α a v hva).mp hker
  intro i j
  simpa only [eval_normalPolynomial, α] using h i j

/-- Numerator/denominator data with actual polynomial degree bounds. A proper
denominator is nonzero in the carrier's coordinate field. -/
structure PolynomialFraction {n : ℕ} (V : AffineVariety n) (D : ℕ) where
  numerator : Poly n
  denominator : Poly n
  denominator_proper : denominator ∉ V.ideal
  numerator_degree : numerator.totalDegree ≤ D
  denominator_degree : denominator.totalDegree ≤ D

namespace PolynomialFraction

def eval {n D : ℕ} {V : AffineVariety n} (F : PolynomialFraction V D) (x : Point n) : ℂ :=
  MvPolynomial.aeval x F.numerator / MvPolynomial.aeval x F.denominator

def ofPolynomial {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (f : Poly n) (D : ℕ) (hf : f.totalDegree ≤ D) : PolynomialFraction V D :=
  { numerator := f
    denominator := 1
    denominator_proper := hV.one_notMem
    numerator_degree := hf
    denominator_degree := by simp }

def add {n D E : ℕ} {V : AffineVariety n} (hV : V.IsIrreducible)
    (F : PolynomialFraction V D) (G : PolynomialFraction V E) : PolynomialFraction V (D + E) :=
  { numerator := F.numerator * G.denominator + G.numerator * F.denominator
    denominator := F.denominator * G.denominator
    denominator_proper := fun h => (hV.mem_or_mem h).elim F.denominator_proper G.denominator_proper
    numerator_degree := by
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · exact (MvPolynomial.totalDegree_mul _ _).trans
          (Nat.add_le_add F.numerator_degree G.denominator_degree)
      · exact (MvPolynomial.totalDegree_mul _ _).trans
          (by have := Nat.add_le_add G.numerator_degree F.denominator_degree; omega)
    denominator_degree := (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add F.denominator_degree G.denominator_degree) }

def mul {n D E : ℕ} {V : AffineVariety n} (hV : V.IsIrreducible)
    (F : PolynomialFraction V D) (G : PolynomialFraction V E) : PolynomialFraction V (D + E) :=
  { numerator := F.numerator * G.numerator
    denominator := F.denominator * G.denominator
    denominator_proper := fun h => (hV.mem_or_mem h).elim F.denominator_proper G.denominator_proper
    numerator_degree := (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add F.numerator_degree G.numerator_degree)
    denominator_degree := (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add F.denominator_degree G.denominator_degree) }

def neg {n D : ℕ} {V : AffineVariety n} (F : PolynomialFraction V D) : PolynomialFraction V D :=
  { numerator := -F.numerator
    denominator := F.denominator
    denominator_proper := F.denominator_proper
    numerator_degree := by simpa using F.numerator_degree
    denominator_degree := F.denominator_degree }

def inv {n D : ℕ} {V : AffineVariety n} (F : PolynomialFraction V D)
    (hf : F.numerator ∉ V.ideal) : PolynomialFraction V D :=
  { numerator := F.denominator
    denominator := F.numerator
    denominator_proper := hf
    numerator_degree := F.denominator_degree
    denominator_degree := F.numerator_degree }

def pderiv {n D : ℕ} {V : AffineVariety n} (hV : V.IsIrreducible)
    (F : PolynomialFraction V D) (i : Fin n) : PolynomialFraction V (2 * D) :=
  { numerator := MvPolynomial.pderiv i F.numerator * F.denominator -
      F.numerator * MvPolynomial.pderiv i F.denominator
    denominator := F.denominator * F.denominator
    denominator_proper := fun h => (hV.mem_or_mem h).elim F.denominator_proper F.denominator_proper
    numerator_degree := by
      apply (MvPolynomial.totalDegree_sub _ _).trans
      apply max_le
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        have hd := OAI.QuarticPowerFree.pderiv_degree_le_sub_one F.numerator D F.numerator_degree i
        have hden := F.denominator_degree
        omega
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        have hd := OAI.QuarticPowerFree.pderiv_degree_le_sub_one F.denominator D F.denominator_degree i
        have hnum := F.numerator_degree
        omega
    denominator_degree := (MvPolynomial.totalDegree_mul _ _).trans
      (by have := Nat.add_le_add F.denominator_degree F.denominator_degree; omega) }

theorem eval_add {n D E : ℕ} {V : AffineVariety n} (hV : V.IsIrreducible)
    (F : PolynomialFraction V D) (G : PolynomialFraction V E) (x : Point n)
    (hf : MvPolynomial.aeval x F.denominator ≠ 0) (hg : MvPolynomial.aeval x G.denominator ≠ 0) :
    (F.add hV G).eval x = F.eval x + G.eval x := by
  dsimp [add, eval]
  simp only [MvPolynomial.aeval_eq_eval] at hf hg ⊢
  simp only [map_add, map_mul]
  field_simp [hf, hg] <;> ring

theorem eval_mul {n D E : ℕ} {V : AffineVariety n} (hV : V.IsIrreducible)
    (F : PolynomialFraction V D) (G : PolynomialFraction V E) (x : Point n) :
    (F.mul hV G).eval x = F.eval x * G.eval x := by
  simp [mul, eval, map_mul, mul_div_mul_comm]

theorem eval_neg {n D : ℕ} {V : AffineVariety n} (F : PolynomialFraction V D) (x : Point n) :
    F.neg.eval x = -F.eval x := by simp [neg, eval, neg_div]

theorem eval_inv {n D : ℕ} {V : AffineVariety n} (F : PolynomialFraction V D)
    (hf : F.numerator ∉ V.ideal) (x : Point n) : (F.inv hf).eval x = (F.eval x)⁻¹ := by
  simp [inv, eval]

end PolynomialFraction

def ControlledRulings.mono {e M : ℕ} {C : SkewCoordinates e} {V : AffineVariety (skewDim e)}
    {L L' : ℝ} (F : ControlledRulings C V M L) (hL : L ≤ L') : ControlledRulings C V M L' :=
  { F with section_degree := F.section_degree.trans hL }

abbrev CarrierField {n : ℕ} (V : AffineVariety n) := FractionRing (Poly n ⧸ V.ideal)

def coordinateMap {n : ℕ} (V : AffineVariety n) : Poly n →+* CarrierField V :=
  (algebraMap (Poly n ⧸ V.ideal) (CarrierField V)).comp (Ideal.Quotient.mk V.ideal)

theorem coordinateMap_eq_zero_iff {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime] (f : Poly n) :
    coordinateMap V f = 0 ↔ f ∈ V.ideal := by
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (Poly n ⧸ V.ideal) (CarrierField V)
    simpa only [coordinateMap, RingHom.comp_apply, map_zero] using h
  · intro h
    simp only [coordinateMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

namespace PolynomialFraction

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

def value {D : ℕ} (F : PolynomialFraction V D) : CarrierField V :=
  coordinateMap V F.numerator / coordinateMap V F.denominator

theorem value_denominator_ne_zero {D : ℕ} (F : PolynomialFraction V D) :
    coordinateMap V F.denominator ≠ 0 :=
  fun h => F.denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)

theorem value_eq_zero_iff {D : ℕ} (F : PolynomialFraction V D) :
    F.value = 0 ↔ F.numerator ∈ V.ideal := by
  rw [value, div_eq_zero_iff]
  simp only [F.value_denominator_ne_zero, or_false]
  exact coordinateMap_eq_zero_iff V _

theorem value_add {D E : ℕ} (F : PolynomialFraction V D) (G : PolynomialFraction V E) :
    (F.add (inferInstance : V.ideal.IsPrime) G).value = F.value + G.value := by
  dsimp [value, add]
  simp only [map_add, map_mul]
  field_simp [F.value_denominator_ne_zero, G.value_denominator_ne_zero] <;> ring

theorem value_mul {D E : ℕ} (F : PolynomialFraction V D) (G : PolynomialFraction V E) :
    (F.mul (inferInstance : V.ideal.IsPrime) G).value = F.value * G.value := by
  simp [value, mul, map_mul, mul_div_mul_comm]

theorem value_neg {D : ℕ} (F : PolynomialFraction V D) : F.neg.value = -F.value := by
  simp [value, neg, neg_div]

theorem value_inv {D : ℕ} (F : PolynomialFraction V D) (hf : F.numerator ∉ V.ideal) :
    (F.inv hf).value = (F.value)⁻¹ := by simp [value, inv]

theorem value_eq_iff_cross_mem {D E : ℕ} (F : PolynomialFraction V D) (G : PolynomialFraction V E) :
    F.value = G.value ↔ F.numerator * G.denominator - G.numerator * F.denominator ∈ V.ideal := by
  rw [value, value, div_eq_div_iff F.value_denominator_ne_zero G.value_denominator_ne_zero]
  rw [← (coordinateMap V).map_mul, ← (coordinateMap V).map_mul, ← sub_eq_zero,
    ← (coordinateMap V).map_sub, coordinateMap_eq_zero_iff]

theorem eval_eq_of_value_eq {D E : ℕ} (F : PolynomialFraction V D) (G : PolynomialFraction V E)
    (h : F.value = G.value) (x : Point n) (hx : x ∈ V.points)
    (hf : MvPolynomial.aeval x F.denominator ≠ 0) (hg : MvPolynomial.aeval x G.denominator ≠ 0) :
    F.eval x = G.eval x := by
  have hmem := (F.value_eq_iff_cross_mem G).mp h
  have hz := hx _ hmem
  simp only [map_sub, map_mul] at hz
  exact (div_eq_div_iff hf hg).mpr (sub_eq_zero.mp hz)

end PolynomialFraction


def FractionBound {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (D : ℕ) (x : CarrierField V) : Prop :=
  ∃ F : PolynomialFraction V D, F.value = x

namespace FractionBound

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem mono {D E : ℕ} {x : CarrierField V} (hx : FractionBound V D x) (hDE : D ≤ E) :
    FractionBound V E x := by
  obtain ⟨F, hF⟩ := hx
  refine ⟨{ numerator := F.numerator
            denominator := F.denominator
            denominator_proper := F.denominator_proper
            numerator_degree := F.numerator_degree.trans hDE
            denominator_degree := F.denominator_degree.trans hDE }, hF⟩

theorem zero (D : ℕ) : FractionBound V D (0 : CarrierField V) := by
  refine ⟨PolynomialFraction.ofPolynomial V (inferInstance : V.ideal.IsPrime) 0 D (by simp), ?_⟩
  simp [PolynomialFraction.ofPolynomial, PolynomialFraction.value]

theorem polynomial (f : Poly n) (D : ℕ) (hf : f.totalDegree ≤ D) :
    FractionBound V D (coordinateMap V f) := by
  refine ⟨PolynomialFraction.ofPolynomial V (inferInstance : V.ideal.IsPrime) f D hf, ?_⟩
  simp [PolynomialFraction.ofPolynomial, PolynomialFraction.value]

theorem add {D E : ℕ} {x y : CarrierField V} (hx : FractionBound V D x) (hy : FractionBound V E y) :
    FractionBound V (D + E) (x + y) := by
  obtain ⟨F, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hy
  exact ⟨F.add (inferInstance : V.ideal.IsPrime) G, F.value_add G⟩

theorem mul {D E : ℕ} {x y : CarrierField V} (hx : FractionBound V D x) (hy : FractionBound V E y) :
    FractionBound V (D + E) (x * y) := by
  obtain ⟨F, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hy
  exact ⟨F.mul (inferInstance : V.ideal.IsPrime) G, F.value_mul G⟩

theorem neg {D : ℕ} {x : CarrierField V} (hx : FractionBound V D x) : FractionBound V D (-x) := by
  obtain ⟨F, rfl⟩ := hx
  exact ⟨F.neg, F.value_neg⟩

theorem sub {D E : ℕ} {x y : CarrierField V} (hx : FractionBound V D x) (hy : FractionBound V E y) :
    FractionBound V (D + E) (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem inv {D : ℕ} {x : CarrierField V} (hx : FractionBound V D x) (hx0 : x ≠ 0) :
    FractionBound V D x⁻¹ := by
  obtain ⟨F, hF⟩ := hx
  have hf : F.numerator ∉ V.ideal := by
    intro hnum
    exact hx0 (hF.symm.trans (F.value_eq_zero_iff.mpr hnum))
  exact ⟨F.inv hf, F.value_inv hf |>.trans (congrArg Inv.inv hF)⟩

theorem div {D E : ℕ} {x y : CarrierField V} (hx : FractionBound V D x) (hy : FractionBound V E y)
    (hy0 : y ≠ 0) : FractionBound V (D + E) (x / y) := by
  simpa [div_eq_mul_inv] using hx.mul (hy.inv hy0)

theorem sum {ι : Type*} (s : Finset ι) (f : ι → CarrierField V) (D : ℕ)
    (hf : ∀ i ∈ s, FractionBound V D (f i)) :
    FractionBound V (s.card * D) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (V := V) 0
  | @insert i s hi ih =>
    have hi' := hf i (Finset.mem_insert_self _ _)
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa [Finset.card_insert_of_notMem hi, Finset.sum_insert hi, Nat.succ_mul, Nat.add_comm] using hi'.add hs

end FractionBound

def CoefficientBound {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (D : ℕ) (p : Polynomial (CarrierField V)) : Prop :=
  ∀ i : ℕ, FractionBound V D (p.coeff i)

namespace CoefficientBound

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem mono {D E : ℕ} {p : Polynomial (CarrierField V)} (hp : CoefficientBound V D p) (hDE : D ≤ E) :
    CoefficientBound V E p := fun i => (hp i).mono hDE

theorem zero (D : ℕ) : CoefficientBound V D (0 : Polynomial (CarrierField V)) := by
  intro i
  simpa using FractionBound.zero (V := V) D

theorem C {D : ℕ} {x : CarrierField V} (hx : FractionBound V D x) :
    CoefficientBound V D (Polynomial.C x) := by
  intro i
  cases i with
  | zero => simpa using hx
  | succ i => simpa using FractionBound.zero (V := V) D

theorem add {D E : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hq : CoefficientBound V E q) : CoefficientBound V (D + E) (p + q) := by
  intro i
  simpa only [Polynomial.coeff_add] using (hp i).add (hq i)

theorem neg {D : ℕ} {p : Polynomial (CarrierField V)} (hp : CoefficientBound V D p) :
    CoefficientBound V D (-p) := by
  intro i
  simpa only [Polynomial.coeff_neg] using (hp i).neg

theorem sub {D E : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hq : CoefficientBound V E q) : CoefficientBound V (D + E) (p - q) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem C_mul {D E : ℕ} {x : CarrierField V} {p : Polynomial (CarrierField V)}
    (hx : FractionBound V D x) (hp : CoefficientBound V E p) : CoefficientBound V (D + E) (Polynomial.C x * p) := by
  intro i
  simpa only [Polynomial.coeff_C_mul] using hx.mul (hp i)

theorem mul_C {D E : ℕ} {x : CarrierField V} {p : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hx : FractionBound V E x) : CoefficientBound V (D + E) (p * Polynomial.C x) := by
  intro i
  simpa only [Polynomial.coeff_mul_C] using (hp i).mul hx

theorem mul_X_pow {D : ℕ} {p : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (k : ℕ) : CoefficientBound V D (p * Polynomial.X ^ k) := by
  intro i
  rw [Polynomial.coeff_mul_X_pow']
  split
  · exact hp _
  · exact FractionBound.zero D

theorem mul {D E : ℕ} {p q : Polynomial (CarrierField V)} (hp : CoefficientBound V D p)
    (hq : CoefficientBound V E q) (d : ℕ) (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d) :
    CoefficientBound V ((2 * d + 1) * (D + E)) (p * q) := by
  intro i
  by_cases hi : i ≤ 2 * d
  · rw [Polynomial.coeff_mul]
    have h := FractionBound.sum (Finset.HasAntidiagonal.antidiagonal i) (fun j => p.coeff j.1 * q.coeff j.2)
      (D + E) (fun j hj => (hp j.1).mul (hq j.2))
    rw [Finset.Nat.card_antidiagonal] at h
    exact h.mono (Nat.mul_le_mul_right (D + E) (by omega))
  · have hdegree : (p * q).natDegree < i := by
      have hmul := Polynomial.natDegree_mul_le (p := p) (q := q)
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdegree]
    exact FractionBound.zero _

end CoefficientBound

namespace CoefficientBound

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem monic_step {D : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hq : CoefficientBound V D q) (k : ℕ) :
    CoefficientBound V (3 * D) (p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ k)) := by
  have hlc : FractionBound V D p.leadingCoeff := hp p.natDegree
  have hprod := (hq.mul_C hlc).mul_X_pow k
  have hsub := hp.sub hprod
  simpa only [mul_assoc, show D + (D + D) = 3 * D by omega] using hsub

theorem modByMonic_step {p q : Polynomial (CarrierField V)} (hq : q.Monic)
    (hstep : q.degree ≤ p.degree ∧ p ≠ 0) :
    p %ₘ q = (p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))) %ₘ q := by
  simp only [Polynomial.modByMonic, dif_pos hq]
  conv_lhs => rw [Polynomial.divModByMonicAux]
  simp only [dif_pos hstep]

theorem monic_remainder {D : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hqbound : CoefficientBound V D q) (hq : q.Monic) :
    CoefficientBound V (3 ^ (p.natDegree + 1) * D) (p %ₘ q) := by
  classical
  generalize hm : p.natDegree = m
  induction m using Nat.strong_induction_on generalizing p D with
  | h m ih =>
    by_cases hp0 : p = 0
    · subst p
      simpa using zero (V := V) (3 ^ (m + 1) * D)
    by_cases hqp : q.degree ≤ p.degree
    · let r := p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))
      have hrbound : CoefficientBound V (3 * D) r := hp.monic_step hqbound _
      have hqbound' : CoefficientBound V (3 * D) q := hqbound.mono (by omega)
      rw [modByMonic_step hq ⟨hqp, hp0⟩]
      change CoefficientBound V (3 ^ (m + 1) * D) (r %ₘ q)
      by_cases hr0 : r = 0
      · rw [hr0, Polynomial.zero_modByMonic]
        exact zero _
      have hdegree : r.degree < p.degree := Polynomial.div_wf_lemma ⟨hqp, hp0⟩ hq
      have hnat : r.natDegree < p.natDegree := by
        rw [Polynomial.degree_eq_natDegree hr0, Polynomial.degree_eq_natDegree hp0] at hdegree
        exact_mod_cast hdegree
      have hrec := ih r.natDegree (by omega) hrbound hqbound' rfl
      apply hrec.mono
      calc
        3 ^ (r.natDegree + 1) * (3 * D) = 3 ^ (r.natDegree + 2) * D := by
          rw [show r.natDegree + 2 = (r.natDegree + 1) + 1 by omega, pow_succ]
          ring
        _ ≤ 3 ^ (m + 1) * D :=
          Nat.mul_le_mul_right D (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [(Polynomial.modByMonic_eq_self_iff hq).mpr (lt_of_not_ge hqp)]
      apply hp.mono
      calc
        D = 1 * D := (one_mul D).symm
        _ ≤ 3 ^ (m + 1) * D := Nat.mul_le_mul_right D (one_le_pow₀ (by norm_num))

end CoefficientBound

namespace CoefficientBound

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem remainder {D : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hqbound : CoefficientBound V D q)
    (d : ℕ) (hpdeg : p.natDegree ≤ d) :
    CoefficientBound V ((2 * 3 ^ (d + 1)) * D) (p % q) := by
  classical
  by_cases hq0 : q = 0
  · rw [hq0, EuclideanDomain.mod_zero]
    apply hp.mono
    have hpow : 1 ≤ 3 ^ (d + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  have hlead : FractionBound V D q.leadingCoeff := hqbound q.natDegree
  have hscaled : CoefficientBound V (2 * D) (q * Polynomial.C q.leadingCoeff⁻¹) := by
    simpa only [two_mul] using hqbound.mul_C (hlead.inv hlc)
  rw [Polynomial.mod_def]
  have hresult := monic_remainder (hp.mono (show D ≤ 2 * D by omega)) hscaled
    (Polynomial.monic_mul_leadingCoeff_inv hq0)
  apply hresult.mono
  calc
    3 ^ (p.natDegree + 1) * (2 * D) ≤ 3 ^ (d + 1) * (2 * D) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = (2 * 3 ^ (d + 1)) * D := by ring

theorem euclidean_gcd {D : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hq : CoefficientBound V D q)
    (d : ℕ) (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d) :
    CoefficientBound V ((2 * 3 ^ (d + 1)) ^ (p.natDegree + 1) * D) (EuclideanDomain.gcd p q) := by
  classical
  let M := 2 * 3 ^ (d + 1)
  have hM : 1 ≤ M := by dsimp [M]; have h := one_le_pow₀ (by norm_num : 1 ≤ (3 : ℕ)) (n := d + 1); omega
  generalize hm : p.natDegree = m
  induction m using Nat.strong_induction_on generalizing p q D with
  | h m ih =>
    by_cases hp0 : p = 0
    · rw [hp0, EuclideanDomain.gcd_zero_left]
      apply hq.mono
      simpa only [one_mul, M] using Nat.mul_le_mul_right D (one_le_pow₀ hM (n := m + 1))
    have hr := hq.remainder hp d hqdeg
    have hp' : CoefficientBound V (M * D) p := hp.mono (by nlinarith)
    rw [EuclideanDomain.gcd_val]
    by_cases hr0 : q % p = 0
    · rw [hr0, EuclideanDomain.gcd_zero_left]
      apply hp.mono
      simpa only [one_mul, M] using Nat.mul_le_mul_right D (one_le_pow₀ hM (n := m + 1))
    have hdegree : (q % p).degree < p.degree := Polynomial.degree_mod_lt q hp0
    have hnat : (q % p).natDegree < p.natDegree := by
      rw [Polynomial.degree_eq_natDegree hr0, Polynomial.degree_eq_natDegree hp0] at hdegree
      exact_mod_cast hdegree
    have hrdeg : (q % p).natDegree ≤ d := by omega
    have hrec := ih (q % p).natDegree (by omega) hr hp' hrdeg hpdeg rfl
    apply hrec.mono
    calc
      M ^ ((q % p).natDegree + 1) * (M * D) = M ^ ((q % p).natDegree + 2) * D := by
        rw [show (q % p).natDegree + 2 = ((q % p).natDegree + 1) + 1 by omega, pow_succ]
        ring
      _ ≤ M ^ (m + 1) * D := Nat.mul_le_mul_right D (Nat.pow_le_pow_right hM (by omega))

end CoefficientBound

namespace FractionBound

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem natCast (k D : ℕ) : FractionBound V D (k : CarrierField V) := by
  have hk : (k : Poly n) = MvPolynomial.C (k : ℂ) := (map_natCast MvPolynomial.C k).symm
  have h := polynomial (V := V) (k : Poly n) D
    (by rw [hk]; simp only [MvPolynomial.totalDegree_C, Nat.zero_le])
  simpa only [map_natCast] using h

end FractionBound

namespace CoefficientBound

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem derivative {D : ℕ} {p : Polynomial (CarrierField V)} (hp : CoefficientBound V D p) :
    CoefficientBound V D p.derivative := by
  intro i
  rw [Polynomial.coeff_derivative]
  simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using
    (hp (i + 1)).mul (FractionBound.natCast (V := V) (i + 1) 0)

theorem divByMonic_step {p q : Polynomial (CarrierField V)} (hq : q.Monic)
    (hstep : q.degree ≤ p.degree ∧ p ≠ 0) :
    p /ₘ q = Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree) +
      (p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))) /ₘ q := by
  simp only [Polynomial.divByMonic, dif_pos hq]
  conv_lhs => rw [Polynomial.divModByMonicAux]
  simp only [dif_pos hstep]

theorem monic_quotient {D : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hqbound : CoefficientBound V D q) (hq : q.Monic) :
    CoefficientBound V (4 ^ (p.natDegree + 1) * D) (p /ₘ q) := by
  classical
  generalize hm : p.natDegree = m
  induction m using Nat.strong_induction_on generalizing p D with
  | h m ih =>
    by_cases hp0 : p = 0
    · subst p
      simpa using zero (V := V) (4 ^ (m + 1) * D)
    by_cases hqp : q.degree ≤ p.degree
    · let r := p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))
      let z := Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree)
      have hz : CoefficientBound V D z := (C (hp p.natDegree)).mul_X_pow _
      have hrbound : CoefficientBound V (3 * D) r := hp.monic_step hqbound _
      have hqbound' : CoefficientBound V (3 * D) q := hqbound.mono (by omega)
      rw [divByMonic_step hq ⟨hqp, hp0⟩]
      change CoefficientBound V (4 ^ (m + 1) * D) (z + r /ₘ q)
      by_cases hr0 : r = 0
      · rw [hr0, Polynomial.zero_divByMonic, add_zero]
        apply hz.mono
        simpa only [one_mul] using Nat.mul_le_mul_right D
          (one_le_pow₀ (by norm_num : 1 ≤ (4 : ℕ)) (n := m + 1))
      have hdegree : r.degree < p.degree := Polynomial.div_wf_lemma ⟨hqp, hp0⟩ hq
      have hnat : r.natDegree < p.natDegree := by
        rw [Polynomial.degree_eq_natDegree hr0, Polynomial.degree_eq_natDegree hp0] at hdegree
        exact_mod_cast hdegree
      have hrec := ih r.natDegree (by omega) hrbound hqbound' rfl
      apply (hz.add hrec).mono
      have hpow : 1 ≤ 4 ^ m := one_le_pow₀ (by norm_num)
      calc
        D + 4 ^ (r.natDegree + 1) * (3 * D) ≤ 4 ^ m * D + 4 ^ m * (3 * D) :=
          Nat.add_le_add (by simpa only [one_mul] using Nat.mul_le_mul_right D hpow)
            (Nat.mul_le_mul_right (3 * D) (Nat.pow_le_pow_right (by norm_num) (by omega)))
        _ = 4 ^ (m + 1) * D := by rw [pow_succ]; ring
    · rw [(Polynomial.divByMonic_eq_zero_iff hq).mpr (lt_of_not_ge hqp)]
      exact zero _

theorem quotient {D : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hqbound : CoefficientBound V D q)
    (d : ℕ) (hpdeg : p.natDegree ≤ d) :
    CoefficientBound V ((3 * 4 ^ (d + 1)) * D) (p / q) := by
  classical
  by_cases hq0 : q = 0
  · rw [hq0, EuclideanDomain.div_zero]
    exact zero _
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  have hlead : FractionBound V D q.leadingCoeff := hqbound q.natDegree
  have hscaled : CoefficientBound V (2 * D) (q * Polynomial.C q.leadingCoeff⁻¹) := by
    simpa only [two_mul] using hqbound.mul_C (hlead.inv hlc)
  rw [Polynomial.div_def]
  have hresult := monic_quotient (hp.mono (show D ≤ 2 * D by omega)) hscaled
    (Polynomial.monic_mul_leadingCoeff_inv hq0)
  have hmul := C_mul (hlead.inv hlc) hresult
  apply hmul.mono
  have hpow : 1 ≤ 4 ^ (d + 1) := one_le_pow₀ (by norm_num)
  calc
    D + 4 ^ (p.natDegree + 1) * (2 * D) ≤ 4 ^ (d + 1) * D + 4 ^ (d + 1) * (2 * D) :=
      Nat.add_le_add (by simpa only [one_mul] using Nat.mul_le_mul_right D hpow)
        (Nat.mul_le_mul_right (2 * D) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    _ = (3 * 4 ^ (d + 1)) * D := by ring

end CoefficientBound

namespace FractionBound

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem intCast (k : ℤ) (D : ℕ) : FractionBound V D (k : CarrierField V) := by
  have hk : (k : Poly n) = MvPolynomial.C (k : ℂ) :=
    (map_intCast (MvPolynomial.C : ℂ →+* Poly n) k).symm
  have h := polynomial (V := V) (k : Poly n) D
    (by rw [hk]; simp only [MvPolynomial.totalDegree_C, Nat.zero_le])
  simpa only [map_intCast] using h

theorem prod {ι : Type*} (s : Finset ι) (f : ι → CarrierField V) (D : ℕ)
    (hf : ∀ i ∈ s, FractionBound V D (f i)) :
    FractionBound V (s.card * D) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using natCast (V := V) 1 0
  | @insert i s hi ih =>
    have hi' := hf i (Finset.mem_insert_self _ _)
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa [Finset.card_insert_of_notMem hi, Finset.prod_insert hi, Nat.succ_mul, Nat.add_comm] using hi'.mul hs

theorem det {m : ℕ} (A : Matrix (Fin m) (Fin m) (CarrierField V)) (D : ℕ)
    (hA : ∀ i j, FractionBound V D (A i j)) :
    FractionBound V (Fintype.card (Equiv.Perm (Fin m)) * m * D) A.det := by
  classical
  rw [Matrix.det_apply']
  have hterm (σ : Equiv.Perm (Fin m)) :
      FractionBound V (m * D) (((Equiv.Perm.sign σ : ℤ) : CarrierField V) * ∏ i, A (σ i) i) := by
    have hp := prod (Finset.univ : Finset (Fin m)) (fun i => A (σ i) i) D
      (fun i hi => hA (σ i) i)
    have hs := (intCast (V := V) (Equiv.Perm.sign σ : ℤ) 0).mul hp
    simpa using hs
  have hsum := sum Finset.univ
    (fun σ : Equiv.Perm (Fin m) => ((Equiv.Perm.sign σ : ℤ) : CarrierField V) * ∏ i, A (σ i) i)
    (m * D) (fun σ hσ => hterm σ)
  simpa [mul_assoc] using hsum

end FractionBound

theorem polynomial_mem_of_zero_on_principal_open {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (H f : Poly n) (hH : H ∉ V.ideal)
    (hf : ∀ x ∈ V.points, MvPolynomial.aeval x H ≠ 0 → MvPolynomial.aeval x f = 0) :
    f ∈ V.ideal := by
  have hprod : H * f ∈ V.ideal := by
    rw [← V.vanishingIdeal_points]
    intro x hx
    rw [map_mul]
    by_cases hzero : MvPolynomial.aeval x H = 0
    · rw [hzero, zero_mul]
    · rw [hf x hx hzero, mul_zero]
  exact (hV.mem_or_mem hprod).resolve_left hH

def vectorDerivation {n : ℕ} (b : Fin n → Poly n) : Derivation ℂ (Poly n) (Poly n) :=
  ∑ i : Fin n, b i • MvPolynomial.pderiv i

theorem eval_vectorDerivation {n : ℕ} (b : Fin n → Poly n) (f : Poly n) (x : Point n) :
    MvPolynomial.aeval x (vectorDerivation b f) =
      differential f x (fun i => MvPolynomial.aeval x (b i)) := by
  have hsum : vectorDerivation b f = ∑ i : Fin n, b i * MvPolynomial.pderiv i f := by
    change ((∑ i : Fin n, b i • MvPolynomial.pderiv i) : Derivation ℂ (Poly n) (Poly n)).toLinearMap f = _
    rw [Derivation.coe_sum_linearMap, LinearMap.sum_apply]
    simp [Derivation.smul_apply, smul_eq_mul]
  rw [hsum]
  simp only [map_sum, map_mul, differential_apply_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem tangent_vectorDerivation_preserves_ideal {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (H : Poly n) (hH : H ∉ V.ideal) (b : Fin n → Poly n)
    (htan : ∀ x ∈ V.points, MvPolynomial.aeval x H ≠ 0 →
      (fun i => MvPolynomial.aeval x (b i)) ∈ V.tangentSpace x) :
    ∀ f ∈ V.ideal, vectorDerivation b f ∈ V.ideal := by
  intro f hf
  apply polynomial_mem_of_zero_on_principal_open V hV H _ hH
  intro x hx hxH
  rw [eval_vectorDerivation]
  have h := htan x hx hxH
  rw [AffineVariety.tangentSpace, Submodule.mem_iInf] at h
  exact h ⟨f, hf⟩

theorem eval_polynomialLine_derivative {n : ℕ} (f : Poly n) (x d : Point n) (t : ℂ) :
    Polynomial.aeval t (polynomialLine x d f).derivative = differential f (x + t • d) d := by
  have heval (g : Poly n) : Polynomial.aeval t (polynomialLine x d g) =
      MvPolynomial.aeval (x + t • d) g := eval_polynomialLine x d g t
  induction f using MvPolynomial.induction_on with
  | C c => simp [polynomialLine, differential_apply_sum]
  | add f g hf hg =>
    rw [map_add, Polynomial.derivative_add, map_add, hf, hg]
    simp [differential_apply_sum, map_add, add_mul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    have hXi : Polynomial.aeval t (polynomialLine x d (MvPolynomial.X i)).derivative = d i := by
      simp [polynomialLine]
    rw [map_mul, Polynomial.derivative_mul, map_add, map_mul, map_mul, hf, hXi, heval, heval]
    rw [differential_mul_apply, differential_X_apply, MvPolynomial.aeval_X]
    ring

theorem polynomialLine_vectorDerivation {n : ℕ} (b : Fin n → Poly n) (f : Poly n)
    (x d : Point n) (hb : ∀ t : ℂ, ∀ i, MvPolynomial.aeval (x + t • d) (b i) = d i) :
    polynomialLine x d (vectorDerivation b f) = (polynomialLine x d f).derivative := by
  apply Polynomial.funext
  intro t
  change Polynomial.aeval t (polynomialLine x d (vectorDerivation b f)) =
    Polynomial.aeval t (polynomialLine x d f).derivative
  rw [eval_polynomialLine, eval_vectorDerivation, eval_polynomialLine_derivative]
  rw [show (fun i => MvPolynomial.aeval (x + t • d) (b i)) = d from funext (hb t)]

theorem polynomial_eq_zero_of_all_derivatives (p : Polynomial ℂ)
    (hp : ∀ k : ℕ, Polynomial.aeval (0 : ℂ) (Polynomial.derivative^[k] p) = 0) : p = 0 := by
  ext k
  have h := hp k
  have hc := Polynomial.coeff_iterate_derivative (k := k) p 0
  have hzero : (Polynomial.derivative^[k] p).coeff 0 = 0 := by
    change Polynomial.eval (0 : ℂ) (Polynomial.derivative^[k] p) = 0 at h
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact h
  rw [hc] at hzero
  simp only [Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul] at hzero
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  exact (mul_eq_zero.mp hzero).resolve_left hfac

theorem translation_of_vectorDerivation_stable {n : ℕ} (V : AffineVariety n)
    (b : Fin n → Poly n) (hstable : ∀ f ∈ V.ideal, vectorDerivation b f ∈ V.ideal)
    (x d : Point n) (hx : x ∈ V.points)
    (hb : ∀ t : ℂ, ∀ i, MvPolynomial.aeval (x + t • d) (b i) = d i) :
    ∀ t : ℂ, x + t • d ∈ V.points := by
  intro t f hf
  have hmem : ∀ k : ℕ, (vectorDerivation b)^[k] f ∈ V.ideal := by
    intro k
    induction k with
    | zero => exact hf
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hstable _ ih
  have hcommute : ∀ k : ℕ, Polynomial.derivative^[k] (polynomialLine x d f) =
      polynomialLine x d ((vectorDerivation b)^[k] f) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact (polynomialLine_vectorDerivation b _ x d hb).symm
  have hline : polynomialLine x d f = 0 := by
    apply polynomial_eq_zero_of_all_derivatives
    intro k
    rw [hcommute, eval_polynomialLine]
    simpa using hx _ (hmem k)
  have heval := eval_polynomialLine x d f t
  rw [hline, map_zero] at heval
  exact heval.symm

def polynomialPointMap {n m : ℕ} (F : Fin m → Poly n) (x : Point n) : Point m :=
  fun i => MvPolynomial.aeval x (F i)

def polynomialParameterImage {n m : ℕ} (V : AffineVariety n) (H : Poly n)
    (F : Fin m → Poly n) : Set (ProjectivePoint m) :=
  {p | ∃ x ∈ V.points, MvPolynomial.aeval x H ≠ 0 ∧
    ∃ hx : polynomialPointMap F x ≠ 0, Projectivization.mk ℂ (polynomialPointMap F x) hx = p}

theorem eval_polynomialPoint_pullback {n m : ℕ} (F : Fin m → Poly n) (x : Point n) (f : Poly m) :
    MvPolynomial.aeval x (MvPolynomial.aeval F f) = MvPolynomial.aeval (polynomialPointMap F x) f := by
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem polynomialParameter_homogeneous_mem_iff {n m D : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (H : Poly n) (hH : H ∉ V.ideal) (F : Fin m → Poly n)
    (hF : ∀ x ∈ V.points, polynomialPointMap F x ≠ 0)
    (f : Poly m) (hf : f.IsHomogeneous D) :
    f ∈ (ProjectiveVariety.closure (polynomialParameterImage V H F)).ideal ↔
      MvPolynomial.aeval F f ∈ V.ideal := by
  constructor
  · intro h
    apply polynomial_mem_of_zero_on_principal_open V hV H _ hH
    intro x hx hxH
    rw [eval_polynomialPoint_pullback]
    exact h (polynomialPointMap F x) ⟨hF x hx, x, hx, hxH, hF x hx, rfl⟩
  · intro h v hv
    obtain ⟨hv0, x, hx, hxH, hx0, hproj⟩ := hv
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ v (polynomialPointMap F x) hv0 hx0).mp hproj.symm
    have hzero : MvPolynomial.aeval (polynomialPointMap F x) f = 0 := by
      rw [← eval_polynomialPoint_pullback]
      exact hx _ h
    change MvPolynomial.eval v f = 0
    rw [← hc, Bridges.homogeneous_eval_smul f hf]
    have hz : MvPolynomial.eval (polynomialPointMap F x) f = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using hzero
    rw [hz, mul_zero]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomialParameter_closure_irreducible {n m : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (H : Poly n) (hH : H ∉ V.ideal) (F : Fin m → Poly n)
    (hF : ∀ x ∈ V.points, polynomialPointMap F x ≠ 0) :
    (ProjectiveVariety.closure (polynomialParameterImage V H F)).IsIrreducible := by
  apply (ProjectiveVariety.closure (polynomialParameterImage V H F)).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
  · intro htop
    have hone : (1 : Poly m) ∈ (ProjectiveVariety.closure (polynomialParameterImage V H F)).ideal := by
      rw [htop]
      trivial
    have h := (polynomialParameter_homogeneous_mem_iff V hV H hH F hF
      1 (MvPolynomial.isHomogeneous_one _ _)).mp hone
    exact hV.one_notMem (by simpa using h)
  · intro f g hf hg hfg
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    have hprod : MvPolynomial.aeval F f * MvPolynomial.aeval F g ∈ V.ideal := by
      have h := (polynomialParameter_homogeneous_mem_iff V hV H hH F hF (f * g) (ha.mul hb)).mp hfg
      simpa only [map_mul] using h
    rcases hV.mem_or_mem hprod with h | h
    · exact Or.inl ((polynomialParameter_homogeneous_mem_iff V hV H hH F hF f ha).mpr h)
    · exact Or.inr ((polynomialParameter_homogeneous_mem_iff V hV H hH F hF g hb).mpr h)

/-- Ambient polynomial representatives for parameter coefficients. Addition
does not increase this budget, unlike addition of arbitrary fractions. -/
def AmbientCoefficientBound {n : ℕ} (D : ℕ) (p : Polynomial (Poly n)) : Prop :=
  ∀ r, (p.coeff r).totalDegree ≤ D

namespace AmbientCoefficientBound

variable {n D E : ℕ} {p q : Polynomial (Poly n)}

theorem C {f : Poly n} (hf : f.totalDegree ≤ D) :
    AmbientCoefficientBound D (Polynomial.C f) := by
  intro r
  cases r <;> simp [hf]

theorem add (hp : AmbientCoefficientBound D p) (hq : AmbientCoefficientBound E q) :
    AmbientCoefficientBound (max D E) (p + q) := by
  intro r
  rw [Polynomial.coeff_add]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max (hp r) (hq r))

theorem sub (hp : AmbientCoefficientBound D p) (hq : AmbientCoefficientBound E q) :
    AmbientCoefficientBound (max D E) (p - q) := by
  intro r
  rw [Polynomial.coeff_sub]
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max (hp r) (hq r))

theorem mul (hp : AmbientCoefficientBound D p) (hq : AmbientCoefficientBound E q) :
    AmbientCoefficientBound (D + E) (p * q) := by
  intro r
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hp s.1) (hq s.2))

theorem mul_X (hp : AmbientCoefficientBound D p) :
    AmbientCoefficientBound D (p * Polynomial.X) := by
  intro r
  cases r with
  | zero => simp
  | succ r => simpa only [Polynomial.coeff_mul_X] using hp r

theorem sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Poly n))
    (hf : ∀ i ∈ s, AmbientCoefficientBound D (f i)) :
    AmbientCoefficientBound D (∑ i ∈ s, f i) := by
  intro r
  rw [Polynomial.finsetSum_coeff]
  exact MvPolynomial.totalDegree_finsetSum_le (fun i hi => hf i hi r)

theorem map_coordinate {V : AffineVariety n} [V.ideal.IsPrime]
    (hp : AmbientCoefficientBound D p) :
    CoefficientBound V D (p.map (coordinateMap V)) := by
  intro r
  rw [Polynomial.coeff_map]
  exact FractionBound.polynomial _ _ (hp r)

end AmbientCoefficientBound

/-- Numerators of all normalized directions on a nonzero conormal pivot.
The denominator is w a b, and the free coordinate is v b. -/
def directionNumerator {n e : ℕ} (w : Fin e → Fin e → Poly n) (a b i : Fin e) :
    Polynomial (Poly n) := Polynomial.C (w i b) + Polynomial.C (w a i) * Polynomial.X

def kernelDirectionNumerator {e : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (a b i j : Fin e)
    (m : Fin (skewDim e)) : Polynomial (Poly (skewDim e)) :=
  Polynomial.C (w a b) * Polynomial.C (MvPolynomial.C ((C.decode.symm (coordinateSkewPair e i j)) m)) -
    directionNumerator w a b j * Polynomial.C (MvPolynomial.C ((C.decode.symm (coordinateSkewPair e i a)) m)) -
    directionNumerator w a b i * Polynomial.C (MvPolynomial.C ((C.decode.symm (coordinateSkewPair e a j)) m))

def directionDerivativeNumerator {n e : ℕ} (w : Fin e → Fin e → Poly n)
    (a b l : Fin e) (m : Fin n) : Polynomial (Poly n) :=
  Polynomial.C (MvPolynomial.pderiv m (w l b) * w a b - w l b * MvPolynomial.pderiv m (w a b)) +
    Polynomial.C (MvPolynomial.pderiv m (w a l) * w a b - w a l * MvPolynomial.pderiv m (w a b)) * Polynomial.X

/-- The first horizontal test, with every denominator cleared. -/
def firstHorizontalTest {e : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (a b i j l : Fin e) :
    Polynomial (Poly (skewDim e)) :=
  ∑ m : Fin (skewDim e), kernelDirectionNumerator C w a b i j m *
    directionDerivativeNumerator w a b l m

theorem affineParameter_natDegree_le {R : Type*} [Semiring R] (u v : R) :
    (Polynomial.C u + Polynomial.C v * Polynomial.X).natDegree ≤ 1 := by
  exact Polynomial.natDegree_add_le_of_degree_le
    (by simp) ((Polynomial.natDegree_mul_le).trans (by simpa using (Polynomial.natDegree_X_le (R := R))))

theorem directionNumerator_degree {n e : ℕ} (w : Fin e → Fin e → Poly n) (a b i : Fin e) :
    (directionNumerator w a b i).natDegree ≤ 1 := affineParameter_natDegree_le _ _

theorem directionNumerator_coefficients {n e D : ℕ} (w : Fin e → Fin e → Poly n)
    (hw : ∀ i j, (w i j).totalDegree ≤ D) (a b i : Fin e) :
    AmbientCoefficientBound D (directionNumerator w a b i) := by
  simpa only [directionNumerator, max_self] using
    (AmbientCoefficientBound.C (hw i b)).add ((AmbientCoefficientBound.C (hw a i)).mul_X)

theorem kernelDirectionNumerator_degree {e : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (a b i j : Fin e) (m : Fin (skewDim e)) :
    (kernelDirectionNumerator C w a b i j m).natDegree ≤ 1 := by
  unfold kernelDirectionNumerator
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
    · exact (Polynomial.natDegree_mul_le).trans (by simpa using directionNumerator_degree w a b j)
  · exact (Polynomial.natDegree_mul_le).trans (by simpa using directionNumerator_degree w a b i)

theorem kernelDirectionNumerator_coefficients {e D : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (hw : ∀ i j, (w i j).totalDegree ≤ D)
    (a b i j : Fin e) (m : Fin (skewDim e)) :
    AmbientCoefficientBound D (kernelDirectionNumerator C w a b i j m) := by
  have hc (u v : Fin e) : AmbientCoefficientBound (n := skewDim e) 0
      (Polynomial.C (MvPolynomial.C ((C.decode.symm (coordinateSkewPair e u v)) m))) :=
    AmbientCoefficientBound.C (by simp)
  have h0 := (AmbientCoefficientBound.C (hw a b)).mul (hc i j)
  have h1 := (directionNumerator_coefficients w hw a b j).mul (hc i a)
  have h2 := (directionNumerator_coefficients w hw a b i).mul (hc a j)
  simpa only [kernelDirectionNumerator, Nat.add_zero, max_self] using (h0.sub h1).sub h2

theorem directionDerivativeNumerator_degree {n e : ℕ} (w : Fin e → Fin e → Poly n)
    (a b l : Fin e) (m : Fin n) :
    (directionDerivativeNumerator w a b l m).natDegree ≤ 1 := affineParameter_natDegree_le _ _

theorem directionDerivativeNumerator_coefficients {n e D : ℕ} (w : Fin e → Fin e → Poly n)
    (hw : ∀ i j, (w i j).totalDegree ≤ D) (a b l : Fin e) (m : Fin n) :
    AmbientCoefficientBound (2 * D) (directionDerivativeNumerator w a b l m) := by
  have hd (i j : Fin e) : (MvPolynomial.pderiv m (w i j)).totalDegree ≤ D :=
    (OAI.QuarticPowerFree.pderiv_degree_le_sub_one _ _ (hw i j) m).trans (Nat.sub_le _ _)
  have h (f g : Poly n) (hf : f.totalDegree ≤ D) (hg : g.totalDegree ≤ D) :
      (MvPolynomial.pderiv m f * g - f * MvPolynomial.pderiv m g).totalDegree ≤ 2 * D := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      have := OAI.QuarticPowerFree.pderiv_degree_le_sub_one f D hf m
      omega
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      have := OAI.QuarticPowerFree.pderiv_degree_le_sub_one g D hg m
      omega
  simpa only [directionDerivativeNumerator, max_self] using
    (AmbientCoefficientBound.C (h _ _ (hw l b) (hw a b))).add
      ((AmbientCoefficientBound.C (h _ _ (hw a l) (hw a b))).mul_X)

theorem firstHorizontalTest_degree {e : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (a b i j l : Fin e) :
    (firstHorizontalTest C w a b i j l).natDegree ≤ 2 := by
  unfold firstHorizontalTest
  apply Polynomial.natDegree_sum_le_of_forall_le _
  intro m hm
  exact Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add (kernelDirectionNumerator_degree C w a b i j m)
      (directionDerivativeNumerator_degree w a b l m))

theorem firstHorizontalTest_coefficients {e D : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (hw : ∀ i j, (w i j).totalDegree ≤ D)
    (a b i j l : Fin e) : AmbientCoefficientBound (3 * D) (firstHorizontalTest C w a b i j l) := by
  unfold firstHorizontalTest
  apply AmbientCoefficientBound.sum
  intro m hm
  simpa only [show D + 2 * D = 3 * D by omega] using
    (kernelDirectionNumerator_coefficients C w hw a b i j m).mul
      (directionDerivativeNumerator_coefficients w hw a b l m)

theorem eval_directionNumerator {n e : ℕ} (w : Fin e → Fin e → Poly n)
    (a b i : Fin e) (x : Point n) (t : ℂ) :
    (directionNumerator w a b i).eval₂ (MvPolynomial.aeval x).toRingHom t =
      MvPolynomial.aeval x (w i b) + t * MvPolynomial.aeval x (w a i) := by
  simp only [directionNumerator, Polynomial.eval₂_add, Polynomial.eval₂_C,
    Polynomial.eval₂_mul, Polynomial.eval₂_X]
  exact congrArg₂ (· + ·) rfl (mul_comm _ _)

theorem eval_kernelDirectionNumerator {e : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (a b i j : Fin e)
    (x : Point (skewDim e)) (v : Point e)
    (hv : ∀ l, MvPolynomial.aeval x (w l b) + v b * MvPolynomial.aeval x (w a l) =
      MvPolynomial.aeval x (w a b) * v l) (m : Fin (skewDim e)) :
    (kernelDirectionNumerator C w a b i j m).eval₂ (MvPolynomial.aeval x).toRingHom (v b) =
      MvPolynomial.aeval x (w a b) * (C.decode.symm (normalizedKernelPair a v i j)) m := by
  simp only [kernelDirectionNumerator, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, eval_directionNumerator, hv]
  change MvPolynomial.aeval x (w a b) *
      MvPolynomial.aeval x (MvPolynomial.C ((C.decode.symm (coordinateSkewPair e i j)) m)) -
    MvPolynomial.aeval x (w a b) * v j *
      MvPolynomial.aeval x (MvPolynomial.C ((C.decode.symm (coordinateSkewPair e i a)) m)) -
    MvPolynomial.aeval x (w a b) * v i *
      MvPolynomial.aeval x (MvPolynomial.C ((C.decode.symm (coordinateSkewPair e a j)) m)) = _
  simp only [MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  let α := (LinearMap.proj m : Point (skewDim e) →ₗ[ℂ] ℂ).comp C.decode.symm.toLinearMap
  change _ = MvPolynomial.aeval x (w a b) * α (normalizedKernelPair a v i j)
  rw [normalizedKernelPair_expansion, normal_map_sub, normal_map_sub, α.map_smul, α.map_smul]
  dsimp [α]
  ring

theorem eval_directionDerivativeNumerator {n e : ℕ} (w : Fin e → Fin e → Poly n)
    (a b l : Fin e) (m : Fin n) (x : Point n) (t : ℂ) :
    (directionDerivativeNumerator w a b l m).eval₂ (MvPolynomial.aeval x).toRingHom t =
      (MvPolynomial.aeval x (MvPolynomial.pderiv m (w l b)) * MvPolynomial.aeval x (w a b) -
        MvPolynomial.aeval x (w l b) * MvPolynomial.aeval x (MvPolynomial.pderiv m (w a b))) +
      t * (MvPolynomial.aeval x (MvPolynomial.pderiv m (w a l)) * MvPolynomial.aeval x (w a b) -
        MvPolynomial.aeval x (w a l) * MvPolynomial.aeval x (MvPolynomial.pderiv m (w a b))) := by
  simp only [directionDerivativeNumerator, Polynomial.eval₂_add, Polynomial.eval₂_C,
    Polynomial.eval₂_mul, Polynomial.eval₂_X]
  change MvPolynomial.aeval x (_ - _) + MvPolynomial.aeval x (_ - _) * t = _
  simp only [map_sub, map_mul]
  ring

theorem eval_firstHorizontalTest {e : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (a b i j l : Fin e)
    (x : Point (skewDim e)) (v : Point e)
    (hv : ∀ q, MvPolynomial.aeval x (w q b) + v b * MvPolynomial.aeval x (w a q) =
      MvPolynomial.aeval x (w a b) * v q) :
    (firstHorizontalTest C w a b i j l).eval₂ (MvPolynomial.aeval x).toRingHom (v b) =
      (MvPolynomial.aeval x (w a b)) ^ 2 *
        differential (w l b + MvPolynomial.C (v b) * w a l -
          MvPolynomial.C (v l) * w a b) x (C.decode.symm (normalizedKernelPair a v i j)) := by
  let d := C.decode.symm (normalizedKernelPair a v i j)
  unfold firstHorizontalTest
  rw [Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, eval_kernelDirectionNumerator C w a b i j x v hv]
  rw [differential_apply_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_directionDerivativeNumerator]
  simp only [map_sub, map_add, Derivation.leibniz, MvPolynomial.pderiv_C,
    zero_smul, zero_add, smul_eq_mul, map_zero, map_mul, MvPolynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply]
  have h := hv l
  dsimp [d]
  simp only [MvPolynomial.aeval_eq_eval] at h ⊢
  linear_combination -(MvPolynomial.eval x (MvPolynomial.pderiv m (w a b)) *
    (C.decode.symm (normalizedKernelPair a v i j)) m * MvPolynomial.eval x (w a b)) * h

theorem contained_flat_firstHorizontalTest {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (V : AffineVariety (skewDim e))
    (hflat : evaluationFlat C p ⊆ V.points) (f : Poly (skewDim e)) (hf : f ∈ V.ideal)
    (x : Point (skewDim e)) (hx : x ∈ evaluationFlat C p)
    (v : Point e) (a : Fin e) (hva : v a = 1) (s : ℂ)
    (hs : firstPoint p.rep = s • v) (b i j l : Fin e) :
    (firstHorizontalTest C (normalPolynomial C f) a b i j l).eval₂
      (MvPolynomial.aeval x).toRingHom (v b) = 0 := by
  let w := normalPolynomial C f
  have hrelation (y : Point (skewDim e)) (hy : y ∈ evaluationFlat C p) (q : Fin e) :
      MvPolynomial.aeval y (w q b) + v b * MvPolynomial.aeval y (w a q) =
        MvPolynomial.aeval y (w a b) * v q := by
    have hc := contained_flat_normal_constraints C p V hflat y hy f hf v a hva s hs q b
    change MvPolynomial.aeval y (w q b) =
      v q * MvPolynomial.aeval y (w a b) - v b * MvPolynomial.aeval y (w a q) at hc
    linear_combination hc
  rw [eval_firstHorizontalTest C w a b i j l x v (hrelation x hx)]
  let d := C.decode.symm (normalizedKernelPair a v i j)
  have hd : alternatingEvaluation (firstPoint p.rep) (C.decode d) = 0 := by
    rw [hs, LinearEquiv.apply_symm_apply]
    change (normalizedKernelPair a v i j).val (s • v) = 0
    rw [map_smul]
    have hz := normalizedDirectionPullback_eval_zero a v hva (coordinateSkewPair e i j)
    change (normalizedKernelPair a v i j).val v = 0 at hz
    rw [hz, smul_zero]
  have hline (t : ℂ) : x + t • d ∈ evaluationFlat C p := by
    change alternatingEvaluation (firstPoint p.rep) (C.decode (x + t • d)) =
      covectorOfPoint (secondPoint p.rep)
    rw [map_add, map_smul, map_add, map_smul, hd, smul_zero, add_zero]
    exact hx
  have hder : differential (w l b + MvPolynomial.C (v b) * w a l -
      MvPolynomial.C (v l) * w a b) x d = 0 := by
    apply polynomial_line_differential_zero
    intro t
    simp only [map_sub, map_add, map_mul, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply]
    exact sub_eq_zero.mpr ((hrelation _ (hline t) l).trans (mul_comm _ _))
  rw [hder, mul_zero]

theorem SkewChartConstraints.exists_pivot {K : Type*} [Field K] {e : ℕ}
    (w : Fin e → Fin e → K) (a : Fin e) (v : Fin e → K)
    (hw : w ≠ 0) (hv : SkewChartConstraints w a v) : ∃ b, w a b ≠ 0 := by
  by_contra hn
  apply hw
  funext i j
  rw [hv i j]
  have hz (b : Fin e) : w a b = 0 := not_not.mp (fun hb => hn ⟨b, hb⟩)
  simp only [hz, mul_zero, sub_self, Pi.zero_apply]

/-- The linear residual constraints and the quadratic horizontal tests can
be included in one bounded family; no generic elimination is needed first. -/
def residualParameterPolynomial {n e : ℕ} (w u : Fin e → Fin e → Poly n)
    (a b i j : Fin e) : Polynomial (Poly n) :=
  Polynomial.C (u i j * w a b - w i b * u a j + w j b * u a i) +
    Polynomial.C (w a j * u a i - w a i * u a j) * Polynomial.X

theorem residualParameterPolynomial_degree {n e : ℕ} (w u : Fin e → Fin e → Poly n)
    (a b i j : Fin e) : (residualParameterPolynomial w u a b i j).natDegree ≤ 1 :=
  affineParameter_natDegree_le _ _

theorem residualParameterPolynomial_coefficients {n e D : ℕ} (w u : Fin e → Fin e → Poly n)
    (hw : ∀ i j, (w i j).totalDegree ≤ D) (hu : ∀ i j, (u i j).totalDegree ≤ D)
    (a b i j : Fin e) : AmbientCoefficientBound (2 * D) (residualParameterPolynomial w u a b i j) := by
  have hm (f g : Poly n) (hf : f.totalDegree ≤ D) (hg : g.totalDegree ≤ D) :
      (f * g).totalDegree ≤ 2 * D :=
    (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  have h0 : (u i j * w a b - w i b * u a j + w j b * u a i).totalDegree ≤ 2 * D := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_sub _ _).trans
        (max_le (hm _ _ (hu i j) (hw a b)) (hm _ _ (hw i b) (hu a j)))
    · exact hm _ _ (hw j b) (hu a i)
  have h1 : (w a j * u a i - w a i * u a j).totalDegree ≤ 2 * D :=
    (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (hm _ _ (hw a j) (hu a i)) (hm _ _ (hw a i) (hu a j)))
  simpa only [residualParameterPolynomial, max_self] using
    (AmbientCoefficientBound.C h0).add ((AmbientCoefficientBound.C h1).mul_X)

theorem eval_residualParameterPolynomial {n e : ℕ} (w u : Fin e → Fin e → Poly n)
    (a b i j : Fin e) (x : Point n) (t : ℂ) :
    (residualParameterPolynomial w u a b i j).eval₂ (MvPolynomial.aeval x).toRingHom t =
      directionResidualConstant (fun k l => MvPolynomial.aeval x (w k l))
        (fun k l => MvPolynomial.aeval x (u k l)) a b i j +
      t * directionResidualLinear (fun k l => MvPolynomial.aeval x (w k l))
        (fun k l => MvPolynomial.aeval x (u k l)) a b i j := by
  simp only [residualParameterPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  change MvPolynomial.aeval x (_ + _) + MvPolynomial.aeval x (_ - _) * t = _
  simp only [map_add, map_sub, map_mul, directionResidualConstant, directionResidualLinear]
  ring

theorem contained_flat_residualParameterPolynomial {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (V : AffineVariety (skewDim e))
    (hflat : evaluationFlat C p ⊆ V.points) (f g : Poly (skewDim e))
    (hf : f ∈ V.ideal) (hg : g ∈ V.ideal) (x : Point (skewDim e))
    (hx : x ∈ evaluationFlat C p) (v : Point e) (a : Fin e) (hva : v a = 1)
    (s : ℂ) (hs : firstPoint p.rep = s • v) (b i j : Fin e)
    (hpivot : MvPolynomial.aeval x (normalPolynomial C f a b) ≠ 0) :
    (residualParameterPolynomial (normalPolynomial C f) (normalPolynomial C g) a b i j).eval₂
      (MvPolynomial.aeval x).toRingHom (v b) = 0 := by
  rw [eval_residualParameterPolynomial]
  have hw := contained_flat_normal_constraints C p V hflat x hx f hf v a hva s hs
  have hu := contained_flat_normal_constraints C p V hflat x hx g hg v a hva s hs
  have hv := directionGraph_of_constraints _ a b hpivot v hw
  rw [hv] at hu
  have hres := (directionGraph_constraints_iff _ _ a b hpivot (v b)).mp hu
  exact hres i j

/-- Differentiate the carrier coordinates while holding the normalized
direction's free coordinate fixed. -/
def parameterPartialDerivative {n : ℕ} (m : Fin n) (Q : Polynomial (Poly n)) :
    Polynomial (Poly n) := Q.sum fun r f => Polynomial.monomial r (MvPolynomial.pderiv m f)

theorem parameterPartialDerivative_coeff {n : ℕ} (m : Fin n) (Q : Polynomial (Poly n)) (r : ℕ) :
    (parameterPartialDerivative m Q).coeff r = MvPolynomial.pderiv m (Q.coeff r) := by
  classical
  unfold parameterPartialDerivative Polynomial.sum
  rw [Polynomial.finsetSum_coeff]
  by_cases hr : r ∈ Q.support
  · simp [Polynomial.coeff_monomial, hr]
  · have hzero : Q.coeff r = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hr
    simp [Polynomial.coeff_monomial, hr, hzero]

theorem parameterPartialDerivative_degree {n : ℕ} (m : Fin n) (Q : Polynomial (Poly n)) :
    (parameterPartialDerivative m Q).natDegree ≤ Q.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro r hr
  rw [parameterPartialDerivative_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hr, map_zero]

theorem parameterPartialDerivative_coefficients {n D : ℕ} (m : Fin n)
    (Q : Polynomial (Poly n)) (hQ : AmbientCoefficientBound D Q) :
    AmbientCoefficientBound D (parameterPartialDerivative m Q) := by
  intro r
  rw [parameterPartialDerivative_coeff]
  exact (OAI.QuarticPowerFree.pderiv_degree_le_sub_one _ _ (hQ r) m).trans (Nat.sub_le _ _)

theorem parameterPartialDerivative_add {n : ℕ} (m : Fin n) (Q R : Polynomial (Poly n)) :
    parameterPartialDerivative m (Q + R) = parameterPartialDerivative m Q + parameterPartialDerivative m R := by
  ext r
  simp only [parameterPartialDerivative_coeff, Polynomial.coeff_add, map_add]

theorem parameterPartialDerivative_monomial {n : ℕ} (m : Fin n) (r : ℕ) (f : Poly n) :
    parameterPartialDerivative m (Polynomial.monomial r f) = Polynomial.monomial r (MvPolynomial.pderiv m f) := by
  ext s
  rw [parameterPartialDerivative_coeff]
  by_cases h : r = s <;> simp [Polynomial.coeff_monomial, h]

theorem parameterPartialDerivative_eval {n : ℕ} (m : Fin n) (Q : Polynomial (Poly n)) (t : ℂ) :
    (parameterPartialDerivative m Q).eval (MvPolynomial.C t) =
      MvPolynomial.pderiv m (Q.eval (MvPolynomial.C t)) := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
      rw [parameterPartialDerivative_add, Polynomial.eval_add, Polynomial.eval_add, map_add, hQ, hR]
  | monomial r f =>
      rw [parameterPartialDerivative_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial]
      simp only [Derivation.leibniz, MvPolynomial.pderiv_C, Derivation.leibniz_pow,
        smul_eq_mul, mul_zero, zero_add, zero_mul, add_zero]
      ring

theorem eval_parameterPolynomial {n : ℕ} (Q : Polynomial (Poly n)) (x : Point n) (t : ℂ) :
    MvPolynomial.aeval x (Q.eval (MvPolynomial.C t)) = Q.eval₂ (MvPolynomial.aeval x).toRingHom t := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR => simp only [Polynomial.eval_add, map_add, Polynomial.eval₂_add, hQ, hR]
  | monomial r f =>
      simp only [Polynomial.eval_monomial, Polynomial.eval₂_monomial, map_mul, map_pow,
        MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
      rfl

/-- The second test can be computed from a cleared polynomial for the
squarefree gcd. At a root, multiplying by a nonvanishing denominator preserves
the horizontal tangency condition. -/
def secondHorizontalTest {e : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (a b i j : Fin e)
    (Q : Polynomial (Poly (skewDim e))) : Polynomial (Poly (skewDim e)) :=
  ∑ m : Fin (skewDim e), kernelDirectionNumerator C w a b i j m * parameterPartialDerivative m Q

theorem secondHorizontalTest_degree {e : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (a b i j : Fin e)
    (Q : Polynomial (Poly (skewDim e))) :
    (secondHorizontalTest C w a b i j Q).natDegree ≤ Q.natDegree + 1 := by
  unfold secondHorizontalTest
  apply Polynomial.natDegree_sum_le_of_forall_le _
  intro m hm
  exact Polynomial.natDegree_mul_le.trans
    ((Nat.add_le_add (kernelDirectionNumerator_degree C w a b i j m)
      (parameterPartialDerivative_degree m Q)).trans (by omega))

theorem secondHorizontalTest_coefficients {e D E : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (hw : ∀ i j, (w i j).totalDegree ≤ D)
    (a b i j : Fin e) (Q : Polynomial (Poly (skewDim e))) (hQ : AmbientCoefficientBound E Q) :
    AmbientCoefficientBound (D + E) (secondHorizontalTest C w a b i j Q) := by
  unfold secondHorizontalTest
  apply AmbientCoefficientBound.sum
  intro m hm
  exact (kernelDirectionNumerator_coefficients C w hw a b i j m).mul
    (parameterPartialDerivative_coefficients m Q hQ)

theorem eval_secondHorizontalTest {e : ℕ} (C : SkewCoordinates e)
    (w : Fin e → Fin e → Poly (skewDim e)) (a b i j : Fin e)
    (Q : Polynomial (Poly (skewDim e))) (x : Point (skewDim e)) (v : Point e)
    (hv : ∀ q, MvPolynomial.aeval x (w q b) + v b * MvPolynomial.aeval x (w a q) =
      MvPolynomial.aeval x (w a b) * v q) :
    (secondHorizontalTest C w a b i j Q).eval₂ (MvPolynomial.aeval x).toRingHom (v b) =
      MvPolynomial.aeval x (w a b) * differential (Q.eval (MvPolynomial.C (v b))) x
        (C.decode.symm (normalizedKernelPair a v i j)) := by
  unfold secondHorizontalTest
  rw [Polynomial.eval₂_finsetSum, differential_apply_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.eval₂_mul, eval_kernelDirectionNumerator C w a b i j x v hv,
    ← eval_parameterPolynomial, parameterPartialDerivative_eval]
  ring

theorem contained_flat_secondHorizontalTest {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (V : AffineVariety (skewDim e))
    (hflat : evaluationFlat C p ⊆ V.points) (f : Poly (skewDim e)) (hf : f ∈ V.ideal)
    (x : Point (skewDim e)) (hx : x ∈ evaluationFlat C p)
    (v : Point e) (a : Fin e) (hva : v a = 1) (s : ℂ)
    (hs : firstPoint p.rep = s • v) (b i j : Fin e) (Q : Polynomial (Poly (skewDim e)))
    (hQ : ∀ y ∈ evaluationFlat C p, Q.eval₂ (MvPolynomial.aeval y).toRingHom (v b) = 0) :
    (secondHorizontalTest C (normalPolynomial C f) a b i j Q).eval₂
      (MvPolynomial.aeval x).toRingHom (v b) = 0 := by
  have hrelation (q : Fin e) :
      MvPolynomial.aeval x (normalPolynomial C f q b) + v b * MvPolynomial.aeval x (normalPolynomial C f a q) =
        MvPolynomial.aeval x (normalPolynomial C f a b) * v q := by
    have hc := contained_flat_normal_constraints C p V hflat x hx f hf v a hva s hs q b
    linear_combination hc
  rw [eval_secondHorizontalTest C _ a b i j Q x v hrelation]
  let d := C.decode.symm (normalizedKernelPair a v i j)
  have hd : alternatingEvaluation (firstPoint p.rep) (C.decode d) = 0 := by
    rw [hs, LinearEquiv.apply_symm_apply]
    change (normalizedKernelPair a v i j).val (s • v) = 0
    rw [map_smul]
    have hz := normalizedDirectionPullback_eval_zero a v hva (coordinateSkewPair e i j)
    change (normalizedKernelPair a v i j).val v = 0 at hz
    rw [hz, smul_zero]
  have hder : differential (Q.eval (MvPolynomial.C (v b))) x d = 0 := by
    apply polynomial_line_differential_zero
    intro t
    rw [eval_parameterPolynomial]
    apply hQ
    change alternatingEvaluation (firstPoint p.rep) (C.decode (x + t • d)) =
      covectorOfPoint (secondPoint p.rep)
    rw [map_add, map_smul, map_add, map_smul, hd, smul_zero, add_zero]
    exact hx
  rw [hder, mul_zero]

namespace CoefficientBound

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem normalization {D : ℕ} {p : Polynomial (CarrierField V)} (hp : CoefficientBound V D p) :
    CoefficientBound V (2 * D) (normalize p) := by
  classical
  by_cases h0 : p = 0
  · subst p
    simpa using zero (V := V) (2 * D)
  rw [normalize_apply, Polynomial.coe_normUnit_of_ne_zero h0]
  have hlc : FractionBound V D p.leadingCoeff := hp p.natDegree
  simpa only [two_mul] using hp.mul_C (hlc.inv (Polynomial.leadingCoeff_ne_zero.mpr h0))

theorem monic_gcd {D : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hq : CoefficientBound V D q)
    (d : ℕ) (hpd : p.natDegree ≤ d) (hqd : q.natDegree ≤ d) :
    CoefficientBound V ((2 * (2 * 3 ^ (d + 1)) ^ (d + 1)) * D)
      (normalize (EuclideanDomain.gcd p q)) := by
  classical
  have h := (euclidean_gcd hp hq d hpd hqd).normalization
  apply h.mono
  have he := Nat.mul_le_mul_right (2 * D) (Nat.pow_le_pow_right
    (show 1 ≤ 2 * 3 ^ (d + 1) by have h := one_le_pow₀ (by norm_num : 1 ≤ (3 : ℕ)) (n := d + 1); omega)
    (Nat.add_le_add_right hpd 1))
  nlinarith

/-- A bounded Euclidean certificate, including the Bézout coefficients needed
for specialization. The parameter d is fixed by the chart's degrees. -/
theorem euclidean_bezout {D : ℕ} {p q : Polynomial (CarrierField V)}
    (hp : CoefficientBound V D p) (hq : CoefficientBound V D q)
    (d : ℕ) (hpd : p.natDegree ≤ d) (hqd : q.natDegree ≤ d) :
    ∃ u v : Polynomial (CarrierField V),
      EuclideanDomain.gcd p q = p * u + q * v ∧
      u.natDegree ≤ p.natDegree * d ∧ v.natDegree ≤ p.natDegree * d ∧
      CoefficientBound V (((2 * (d * (d + 1)) + 2) *
        (2 * 3 ^ (d + 1) + 3 * 4 ^ (d + 1) + 1)) ^ (p.natDegree + 1) * D) u ∧
      CoefficientBound V (((2 * (d * (d + 1)) + 2) *
        (2 * 3 ^ (d + 1) + 3 * 4 ^ (d + 1) + 1)) ^ (p.natDegree + 1) * D) v := by
  classical
  let R := 2 * 3 ^ (d + 1)
  let S := 3 * 4 ^ (d + 1)
  let J := 2 * (d * (d + 1)) + 1
  let T := (J + 1) * (R + S + 1)
  have hR : 1 ≤ R := by dsimp [R]; have h := one_le_pow₀ (by norm_num : 1 ≤ (3 : ℕ)) (n := d + 1); omega
  have hT : 1 ≤ T := by
    exact (show (1 : ℕ) * 1 ≤ (J + 1) * (R + S + 1) from
      Nat.mul_le_mul (by omega) (by omega))
  have hone (E : ℕ) : CoefficientBound V E (1 : Polynomial (CarrierField V)) := by
    simpa using C (FractionBound.natCast (V := V) 1 E)
  change ∃ u v, _ ∧ _ ∧ _ ∧ CoefficientBound V (T ^ (p.natDegree + 1) * D) u ∧
    CoefficientBound V (T ^ (p.natDegree + 1) * D) v
  generalize hm : p.natDegree = m
  induction m using Nat.strong_induction_on generalizing p q D with
  | h m ih =>
    by_cases hp0 : p = 0
    · refine ⟨0, 1, ?_, by simp, by simp, zero _, hone _⟩
      simp [hp0]
    by_cases hr0 : q % p = 0
    · refine ⟨1, 0, ?_, by simp, by simp, hone _, zero _⟩
      rw [EuclideanDomain.gcd_val, hr0, EuclideanDomain.gcd_zero_left]
      ring
    have hrbound : CoefficientBound V (R * D) (q % p) := hq.remainder hp d hqd
    have hpbound : CoefficientBound V (R * D) p := hp.mono (by nlinarith)
    have hdegree : (q % p).degree < p.degree := Polynomial.degree_mod_lt q hp0
    have hnat : (q % p).natDegree < p.natDegree := by
      rw [Polynomial.degree_eq_natDegree hr0, Polynomial.degree_eq_natDegree hp0] at hdegree
      exact_mod_cast hdegree
    obtain ⟨u, v, heq, hudeg, hvdeg, hubound, hvbound⟩ :=
      ih (q % p).natDegree (by omega) hrbound hpbound (by omega) hpd rfl
    have hquotdeg : (q / p).natDegree ≤ d :=
      (Polynomial.natDegree_le_natDegree (Polynomial.degree_div_le q p)).trans hqd
    have hquotbound : CoefficientBound V (S * D) (q / p) := hq.quotient hp d hqd
    let E := T ^ m * (R * D)
    let F := T ^ m * (S * D)
    have hub : CoefficientBound V E u := hubound.mono
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hT (by omega)))
    have hvb : CoefficientBound V E v := hvbound.mono
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hT (by omega)))
    have hqb : CoefficientBound V F (q / p) := hquotbound.mono (by
      dsimp [F]
      simpa only [one_mul] using Nat.mul_le_mul_right (S * D) (one_le_pow₀ hT (n := m)))
    have hucap : u.natDegree ≤ d * (d + 1) := hudeg.trans (by nlinarith)
    have hqcap : (q / p).natDegree ≤ d * (d + 1) := hquotdeg.trans (by nlinarith)
    have hprod : CoefficientBound V (J * (E + F)) (u * (q / p)) := hub.mul hqb _ hucap hqcap
    have hnew : CoefficientBound V (T ^ (m + 1) * D) (v - u * (q / p)) := by
      apply (hvb.sub hprod).mono
      have hscalar : R + J * (R + S) ≤ T := by dsimp [T]; nlinarith
      calc
        E + J * (E + F) = T ^ m * (R + J * (R + S)) * D := by dsimp [E, F]; ring
        _ ≤ T ^ m * T * D := Nat.mul_le_mul_right D (Nat.mul_le_mul_left _ hscalar)
        _ = T ^ (m + 1) * D := by rw [pow_succ]
    have hud : u.natDegree ≤ m * d := hudeg.trans (Nat.mul_le_mul_right d (by omega))
    have hvd : (v - u * (q / p)).natDegree ≤ m * d := by
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · exact hvdeg.trans (Nat.mul_le_mul_right d (by omega))
      · apply Polynomial.natDegree_mul_le.trans
        have ha := Nat.add_le_add hudeg hquotdeg
        have hb := Nat.mul_le_mul_right d (show (q % p).natDegree + 1 ≤ m by omega)
        nlinarith
    refine ⟨v - u * (q / p), u, ?_, hvd, hud, hnew, ?_⟩
    · rw [EuclideanDomain.gcd_val, heq, EuclideanDomain.mod_eq_sub_mul_div]
      ring
    · apply hub.mono
      have hRT : R ≤ T := by dsimp [T]; nlinarith
      calc
        E = T ^ m * R * D := by dsimp [E]; ring
        _ ≤ T ^ m * T * D := Nat.mul_le_mul_right D (Nat.mul_le_mul_left _ hRT)
        _ = T ^ (m + 1) * D := by rw [pow_succ]

end CoefficientBound

theorem AmbientCoefficientBound.monomial {n D : ℕ} (r : ℕ) (f : Poly n) (hf : f.totalDegree ≤ D) :
    AmbientCoefficientBound D (Polynomial.monomial r f) := by
  intro s
  by_cases hrs : r = s <;> simp [Polynomial.coeff_monomial, hrs, hf]

/-- Clear all coefficients of a bounded parameter polynomial with one proper
denominator. The degree cost is linear in the ambient coefficient budget. -/
theorem clear_parameter_coefficients {n D : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (p : Polynomial (CarrierField V)) (hp : CoefficientBound V D p)
    (d : ℕ) (hpd : p.natDegree ≤ d) :
    ∃ (H : Poly n) (Q : Polynomial (Poly n)), H ∉ V.ideal ∧
      H.totalDegree ≤ (d + 1) * D ∧ Q.natDegree ≤ d ∧
      AmbientCoefficientBound ((d + 1) * D) Q ∧
      Q.map (coordinateMap V) = Polynomial.C (coordinateMap V H) * p := by
  classical
  choose F hF using fun i : Fin (d + 1) => hp i.val
  let H := ∏ i : Fin (d + 1), (F i).denominator
  let N (i : Fin (d + 1)) := (F i).numerator *
    ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, (F j).denominator
  let Q := ∑ i : Fin (d + 1), Polynomial.monomial i.val (N i)
  have hprod (s : Finset (Fin (d + 1))) :
      (∏ i ∈ s, (F i).denominator).totalDegree ≤ s.card * D := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    exact (Finset.sum_le_sum (fun i hi => (F i).denominator_degree)).trans_eq (by simp)
  have hN (i : Fin (d + 1)) : (N i).totalDegree ≤ (d + 1) * D := by
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have ht := hprod ((Finset.univ : Finset (Fin (d + 1))).erase i)
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel] at ht
    have hn := (F i).numerator_degree
    nlinarith
  have hH : H ∉ V.ideal := by
    intro hmem
    have hz := (coordinateMap_eq_zero_iff V H).mpr hmem
    have hn : coordinateMap V H ≠ 0 := by
      dsimp [H]
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => (F i).value_denominator_ne_zero)
    exact hn hz
  refine ⟨H, Q, hH, ?_, ?_, ?_, ?_⟩
  · simpa only [Finset.card_univ, Fintype.card_fin] using hprod Finset.univ
  · apply Polynomial.natDegree_sum_le_of_forall_le _
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  · apply AmbientCoefficientBound.sum
    intro i hi
    exact AmbientCoefficientBound.monomial _ _ (hN i)
  · ext r
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
    by_cases hr : r ≤ d
    · let i : Fin (d + 1) := ⟨r, by omega⟩
      have hcoeff : Q.coeff r = N i := by
        dsimp [Q]
        rw [Polynomial.finsetSum_coeff]
        rw [Finset.sum_eq_single i]
        · simp [Polynomial.coeff_monomial, i]
        · intro j hj hji
          have hval : j.val ≠ r := by intro h; apply hji; apply Fin.ext; exact h
          simp [Polynomial.coeff_monomial, hval]
        · intro hi
          exact (hi (Finset.mem_univ _)).elim
      rw [hcoeff, ← hF i]
      have hfactor : H = (F i).denominator *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, (F j).denominator :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      rw [hfactor]
      dsimp [N, PolynomialFraction.value]
      simp only [map_mul]
      field_simp [(F i).value_denominator_ne_zero]
    · have hpzero : p.coeff r = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hpzero, mul_zero]
      have hQzero : Q.coeff r = 0 := by
        dsimp [Q]
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro i hi
        have hval : i.val ≠ r := by omega
        simp [Polynomial.coeff_monomial, hval]
      rw [hQzero, map_zero]

theorem parameterPolynomial_specialization {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (Q R : Polynomial (Poly n)) (hQR : Q.map (coordinateMap V) = R.map (coordinateMap V))
    (x : Point n) (hx : x ∈ V.points) (t : ℂ) :
    Q.eval₂ (MvPolynomial.aeval x).toRingHom t = R.eval₂ (MvPolynomial.aeval x).toRingHom t := by
  have hcoeff (r : ℕ) : MvPolynomial.aeval x (Q.coeff r) = MvPolynomial.aeval x (R.coeff r) := by
    have h := congrArg (fun p : Polynomial (CarrierField V) => p.coeff r) hQR
    simp only [Polynomial.coeff_map] at h
    have hmem : Q.coeff r - R.coeff r ∈ V.ideal := by
      apply (coordinateMap_eq_zero_iff V _).mp
      rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (by simpa only [map_sub] using hx _ hmem)
  have hmap : Q.map (MvPolynomial.aeval x).toRingHom = R.map (MvPolynomial.aeval x).toRingHom := by
    ext r
    simp only [Polynomial.coeff_map]
    change MvPolynomial.aeval x (Q.coeff r) = MvPolynomial.aeval x (R.coeff r)
    exact hcoeff r
  rw [← Polynomial.eval_map, ← Polynomial.eval_map, hmap]

instance carrierFieldCharZero {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime] : CharZero (CarrierField V) :=
  (RingHom.charZero_iff (ϕ := (coordinateMap V).comp (MvPolynomial.C : ℂ →+* Poly n))
    (RingHom.injective _)).mp inferInstance

theorem monic_quadratic_expansion {K : Type*} [Field K] (p : Polynomial K)
    (hp : p.Monic) (hdeg : p.natDegree = 2) :
    p = Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
  ext r
  have hlead : p.coeff 2 = 1 := by simpa only [hdeg] using hp.coeff_natDegree
  by_cases h0 : r = 0
  · subst r; simp
  by_cases h1 : r = 1
  · subst r; simp
  by_cases h2 : r = 2
  · subst r; simp [hlead]
  have hr : p.natDegree < r := by omega
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hr, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C, h0, h1, h2, Ne.symm h0, Ne.symm h1, Ne.symm h2]

theorem monic_quadratic_separable {K : Type*} [Field K] [CharZero K]
    (p : Polynomial K) (hp : p.Monic) (hdeg : p.natDegree = 2)
    (hdelta : 4 * p.coeff 0 - (p.coeff 1) ^ 2 ≠ 0) : p.Separable := by
  let b := p.coeff 1
  let c := p.coeff 0
  let δ := 4 * c - b ^ 2
  have hδ : δ ≠ 0 := hdelta
  have hraw : Polynomial.C (4 : K) * p -
      (Polynomial.C (2 : K) * Polynomial.X + Polynomial.C b) * p.derivative = Polynomial.C δ := by
    rw [monic_quadratic_expansion p hp hdeg]
    change Polynomial.C (4 : K) * (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) -
      (Polynomial.C (2 : K) * Polynomial.X + Polynomial.C b) *
        (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c).derivative = _
    simp only [Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_X,
      Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, mul_zero, zero_add,
      add_zero, mul_one, pow_one, Nat.cast_ofNat]
    simp only [δ, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [Polynomial.separable_def']
  refine ⟨Polynomial.C δ⁻¹ * Polynomial.C 4,
    -(Polynomial.C δ⁻¹ * (Polynomial.C 2 * Polynomial.X + Polynomial.C b)), ?_⟩
  calc
    _ = Polynomial.C δ⁻¹ * (Polynomial.C 4 * p -
        (Polynomial.C 2 * Polynomial.X + Polynomial.C b) * p.derivative) := by ring
    _ = Polynomial.C δ⁻¹ * Polynomial.C δ := by rw [hraw]
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hδ, map_one]

theorem monic_quadratic_double_root {K : Type*} [Field K] [CharZero K]
    (p : Polynomial K) (hp : p.Monic) (hdeg : p.natDegree = 2)
    (hdelta : 4 * p.coeff 0 - (p.coeff 1) ^ 2 = 0) :
    p = (Polynomial.X + Polynomial.C (p.coeff 1 / 2)) ^ 2 := by
  have hc : p.coeff 0 = (p.coeff 1 / 2) ^ 2 := by
    field_simp
    linear_combination hdelta
  have hb : Polynomial.C (p.coeff 1) =
      2 * Polynomial.C (p.coeff 1 / 2) := by
    have h : (p.coeff 1 / 2) * (2 : K) = p.coeff 1 := by field_simp
    have h' := congrArg (fun x : K => Polynomial.C x) h
    simpa only [map_mul, map_ofNat, mul_comm] using h'.symm
  conv_lhs => rw [monic_quadratic_expansion p hp hdeg]
  rw [hc, map_pow, hb]
  ring

namespace CoefficientBound

variable {n : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem X (D : ℕ) : CoefficientBound V D (Polynomial.X : Polynomial (CarrierField V)) := by
  intro r
  by_cases h : r = 1
  · subst r
    simpa using FractionBound.natCast (V := V) 1 D
  · simpa [Polynomial.coeff_X, h, Ne.symm h] using FractionBound.zero (V := V) D

/-- The ruling tests are quadratic in the free coordinate, so their squarefree
part is obtained with a bounded explicit degree split. -/
theorem quadratic_squarefree {D : ℕ} (p : Polynomial (CarrierField V))
    (hp : p.Monic) (hdeg : p.natDegree ≤ 2) (hbound : CoefficientBound V D p) :
    ∃ G : Polynomial (CarrierField V), G.Monic ∧ G.Separable ∧ G.natDegree ≤ 2 ∧
      CoefficientBound V (3 * D) G ∧ G ∣ p ∧ p ∣ G ^ 2 := by
  classical
  by_cases h0 : p.natDegree = 0
  · have heq : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hp h0
    subst p
    refine ⟨1, Polynomial.monic_one, Polynomial.separable_one, by simp, ?_, dvd_rfl, by simp⟩
    exact hbound.mono (by omega)
  by_cases h1 : p.natDegree = 1
  · refine ⟨p, hp, ?_, hdeg, hbound.mono (by omega), dvd_rfl, dvd_pow_self _ (by decide)⟩
    rw [hp.eq_X_add_C h1]
    exact Polynomial.separable_X_add_C _
  have h2 : p.natDegree = 2 := by omega
  by_cases hδ : 4 * p.coeff 0 - (p.coeff 1) ^ 2 = 0
  · let G := Polynomial.X + Polynomial.C (p.coeff 1 / 2)
    have hrep : p = G ^ 2 := monic_quadratic_double_root p hp h2 hδ
    have hGbound : CoefficientBound V (3 * D) G := by
      have htwo : FractionBound V D (2 : CarrierField V) := FractionBound.natCast 2 D
      have hdiv := (hbound 1).div htwo (by norm_num)
      simpa only [G, show D + (D + D) = 3 * D by omega] using (X D).add (C hdiv)
    refine ⟨G, Polynomial.monic_X_add_C _, Polynomial.separable_X_add_C _, ?_, hGbound, ?_, ?_⟩
    · change (Polynomial.X + Polynomial.C _).natDegree ≤ 2
      simpa using (Polynomial.natDegree_X_add_C (p.coeff 1 / 2)).le.trans (by decide : 1 ≤ 2)
    · rw [hrep]
      exact dvd_pow_self _ (by decide)
    · rw [hrep]
  · refine ⟨p, hp, monic_quadratic_separable p hp h2 hδ, hdeg,
      hbound.mono (by omega), dvd_rfl, dvd_pow_self _ (by decide)⟩

end CoefficientBound

/-- Uniform bounded certificates for a finite family of parameter tests.
The equations and Bézout identity characterize their common roots after
specialization; this record does not assert any geometric conclusion. -/
theorem bounded_family_bezout (m d : ℕ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
      (D : ℕ) (f : Fin m → Polynomial (CarrierField V)),
      (∀ i, CoefficientBound V D (f i)) → (∀ i, (f i).natDegree ≤ d) →
      ∃ (g : Polynomial (CarrierField V)) (U : Fin m → Polynomial (CarrierField V)),
        g.natDegree ≤ d ∧ (∀ i, (U i).natDegree ≤ m * d ^ 2) ∧
        CoefficientBound V (B * D) g ∧ (∀ i, CoefficientBound V (B * D) (U i)) ∧
        (∀ i, g ∣ f i) ∧ g = ∑ i, f i * U i := by
  classical
  induction m with
  | zero =>
      refine ⟨1, le_rfl, ?_⟩
      intro n V inst D f hb hd
      refine ⟨0, Fin.elim0, by simp, (fun i => Fin.elim0 i), ?_,
        (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), by simp⟩
      exact CoefficientBound.zero _
  | succ m ih =>
      obtain ⟨B, hB, hprevious⟩ := ih
      let E := max B 1
      let R := (2 * 3 ^ (d + 1)) ^ (d + 1)
      let S := ((2 * (d * (d + 1)) + 2) *
        (2 * 3 ^ (d + 1) + 3 * 4 ^ (d + 1) + 1)) ^ (d + 1)
      let J := 2 * ((m + 1) * d ^ 2) + 1
      let B' := 1 + R * E + S * E + J * (B + S * E)
      have hbase : 1 ≤ (2 * (d * (d + 1)) + 2) *
          (2 * 3 ^ (d + 1) + 3 * 4 ^ (d + 1) + 1) :=
        (show (1 : ℕ) * 1 ≤ (2 * (d * (d + 1)) + 2) *
          (2 * 3 ^ (d + 1) + 3 * 4 ^ (d + 1) + 1) from Nat.mul_le_mul (by omega) (by omega))
      refine ⟨B', by dsimp [B']; omega, ?_⟩
      intro n V inst D f hb hd
      obtain ⟨g, U, hgdeg, hUdeg, hgbound, hUbound, hdiv, heq⟩ :=
        hprevious V D (fun i => f i.succ) (fun i => hb i.succ) (fun i => hd i.succ)
      have hgb : CoefficientBound V (E * D) g :=
        hgbound.mono (Nat.mul_le_mul_right _ (le_max_left _ _))
      have hfb : CoefficientBound V (E * D) (f 0) :=
        (hb 0).mono (by simpa only [one_mul] using Nat.mul_le_mul_right D (le_max_right B 1))
      obtain ⟨u, v, hbez, hud, hvd, hub, hvb⟩ :=
        CoefficientBound.euclidean_bezout hgb hfb d hgdeg (hd 0)
      let P := EuclideanDomain.gcd g (f 0)
      let W : Fin (m + 1) → Polynomial (CarrierField V) := Fin.cons v (fun i => U i * u)
      have hude : u.natDegree ≤ d ^ 2 := hud.trans (by simpa only [pow_two] using Nat.mul_le_mul_right d hgdeg)
      have hvde : v.natDegree ≤ d ^ 2 := hvd.trans (by simpa only [pow_two] using Nat.mul_le_mul_right d hgdeg)
      have hub' : CoefficientBound V ((S * E) * D) u := by
        apply hub.mono
        dsimp [S]
        simpa only [mul_assoc] using Nat.mul_le_mul_right (E * D)
          (Nat.pow_le_pow_right hbase (Nat.add_le_add_right hgdeg 1))
      have hvb' : CoefficientBound V ((S * E) * D) v := by
        apply hvb.mono
        dsimp [S]
        simpa only [mul_assoc] using Nat.mul_le_mul_right (E * D)
          (Nat.pow_le_pow_right hbase (Nat.add_le_add_right hgdeg 1))
      have hPdeg : P.natDegree ≤ d := by
        by_cases hg0 : g = 0
        · simpa only [P, hg0, EuclideanDomain.gcd_zero_left] using hd 0
        · exact (Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left g (f 0)) hg0).trans hgdeg
      have hPbound : CoefficientBound V (B' * D) P := by
        have hraw := CoefficientBound.euclidean_gcd hgb hfb d hgdeg (hd 0)
        apply hraw.mono
        have hpow := Nat.pow_le_pow_right
          (show 1 ≤ 2 * 3 ^ (d + 1) by have h := one_le_pow₀ (by norm_num : 1 ≤ (3 : ℕ)) (n := d + 1); omega)
          (Nat.add_le_add_right hgdeg 1)
        have hR : R * E ≤ B' := by dsimp [B']; omega
        exact (Nat.mul_le_mul_right _ hpow).trans (by
          simpa only [mul_assoc] using Nat.mul_le_mul_right D hR)
      refine ⟨P, W, hPdeg, ?_, hPbound, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [W, Fin.cons_zero] using hvde.trans
            (by simpa only [one_mul] using Nat.mul_le_mul_right (d ^ 2) (by omega : 1 ≤ m + 1))
        · simpa only [W, Fin.cons_succ] using Polynomial.natDegree_mul_le.trans
            ((Nat.add_le_add (hUdeg j) hude).trans_eq (by ring))
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change CoefficientBound V (B' * D) v
          exact hvb'.mono (Nat.mul_le_mul_right D (by dsimp [B']; omega))
        · change CoefficientBound V (B' * D) (U j * u)
          have hu : u.natDegree ≤ (m + 1) * d ^ 2 := hude.trans
            (by simpa only [one_mul] using Nat.mul_le_mul_right (d ^ 2) (by omega : 1 ≤ m + 1))
          have hU : (U j).natDegree ≤ (m + 1) * d ^ 2 := (hUdeg j).trans
            (Nat.mul_le_mul_right _ (by omega))
          have hmul := (hUbound j).mul hub' _ hU hu
          apply hmul.mono
          have hc : J * (B + S * E) ≤ B' := by dsimp [B']; omega
          convert Nat.mul_le_mul_right D hc using 1 <;> dsimp [J] <;> ring
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact EuclideanDomain.gcd_dvd_right g (f 0)
        · exact (EuclideanDomain.gcd_dvd_left g (f 0)).trans (hdiv j)
      · dsimp [P]
        rw [hbez, heq, Fin.sum_univ_succ]
        simp only [W, Fin.cons_zero, Fin.cons_succ]
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul]
        ring

theorem bounded_family_gcd (m d : ℕ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
      (D : ℕ) (f : Fin m → Polynomial (CarrierField V)),
      (∀ i, CoefficientBound V D (f i)) → (∀ i, (f i).natDegree ≤ d) →
      ∃ (P : Polynomial (CarrierField V)) (U Q : Fin m → Polynomial (CarrierField V)),
        (P = 0 ∨ P.Monic) ∧ P.natDegree ≤ d ∧
        (∀ i, (U i).natDegree ≤ m * d ^ 2) ∧ (∀ i, (Q i).natDegree ≤ d) ∧
        CoefficientBound V (B * D) P ∧
        (∀ i, CoefficientBound V (B * D) (U i)) ∧
        (∀ i, CoefficientBound V (B * D) (Q i)) ∧
        (∀ i, f i = P * Q i) ∧ P = ∑ i, f i * U i := by
  classical
  obtain ⟨B, hB, hraw⟩ := bounded_family_bezout m d
  let E := max 1 (2 * B)
  let T := 3 * 4 ^ (d + 1)
  let B' := 1 + 2 * B + T * E
  refine ⟨B', by dsimp [B']; omega, ?_⟩
  intro n V inst D f hb hd
  obtain ⟨g, U, hgdeg, hUdeg, hgb, hUb, hdiv, heq⟩ := hraw V D f hb hd
  have hBB : 2 * B ≤ B' := by dsimp [B']; omega
  by_cases hg0 : g = 0
  · have hfzero (i : Fin m) : f i = 0 := by
      have h := hdiv i
      rw [hg0, zero_dvd_iff] at h
      exact h
    refine ⟨0, (fun _ => 0), (fun _ => 0), Or.inl rfl, by simp,
      (fun _ => by simp), (fun _ => by simp), CoefficientBound.zero _,
      (fun _ => CoefficientBound.zero _), (fun _ => CoefficientBound.zero _), ?_, by simp⟩
    intro i
    simp only [hfzero i, zero_mul]
  let P := normalize g
  have hPmonic : P.Monic := Polynomial.monic_normalize hg0
  have hPzero : P ≠ 0 := hPmonic.ne_zero
  have hPdeg : P.natDegree ≤ d := by simpa only [P, Polynomial.natDegree_normalize] using hgdeg
  let a := g.leadingCoeff⁻¹
  have hab : FractionBound V (B * D) a := by
    have hlead : FractionBound V (B * D) g.leadingCoeff := hgb g.natDegree
    exact hlead.inv (Polynomial.leadingCoeff_ne_zero.mpr hg0)
  let W := fun i => U i * Polynomial.C a
  let Q := fun i => f i / P
  have hPdiv (i : Fin m) : P ∣ f i := (normalize_dvd_iff).mpr (hdiv i)
  have hPbound : CoefficientBound V ((2 * B) * D) P := by
    simpa only [P, mul_assoc] using hgb.normalization
  have hWeq : P = ∑ i, f i * W i := by
    dsimp [P, W, a]
    rw [normalize_apply, Polynomial.coe_normUnit_of_ne_zero hg0, heq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  refine ⟨P, W, Q, Or.inr hPmonic, hPdeg, ?_, ?_, ?_, ?_, ?_, ?_, hWeq⟩
  · intro i
    exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, Nat.add_zero] using hUdeg i)
  · intro i
    exact (Polynomial.natDegree_le_natDegree (Polynomial.degree_div_le (f i) P)).trans (hd i)
  · exact hPbound.mono (Nat.mul_le_mul_right D hBB)
  · intro i
    have h := (hUb i).mul_C hab
    apply h.mono
    simpa only [← two_mul, mul_assoc] using Nat.mul_le_mul_right D hBB
  · intro i
    have hp : CoefficientBound V (E * D) P := hPbound.mono
      (Nat.mul_le_mul_right D (le_max_right _ _))
    have hf : CoefficientBound V (E * D) (f i) := (hb i).mono
      (by simpa only [one_mul] using Nat.mul_le_mul_right D (le_max_left 1 (2 * B)))
    have h := hf.quotient hp d (hd i)
    apply h.mono
    simpa only [T, mul_assoc] using Nat.mul_le_mul_right D (show T * E ≤ B' by dsimp [B']; omega)
  · intro i
    exact (EuclideanDomain.mul_div_cancel' hPzero (hPdiv i)).symm

/-- A polynomial in the free chart coordinate with one common ambient
denominator. It can be specialized at every carrier point away from that pole. -/
structure ParameterFraction {n : ℕ} (V : AffineVariety n) (D : ℕ) where
  numerator : Polynomial (Poly n)
  denominator : Poly n
  denominator_proper : denominator ∉ V.ideal
  numerator_degree : AmbientCoefficientBound D numerator
  denominator_degree : denominator.totalDegree ≤ D

namespace ParameterFraction

variable {n D E : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

def value (F : ParameterFraction V D) : Polynomial (CarrierField V) :=
  F.numerator.map (coordinateMap V) * Polynomial.C (coordinateMap V F.denominator)⁻¹

def eval (F : ParameterFraction V D) (x : Point n) (t : ℂ) : ℂ :=
  F.numerator.eval₂ (MvPolynomial.aeval x).toRingHom t / MvPolynomial.aeval x F.denominator

theorem value_denominator_ne_zero (F : ParameterFraction V D) : coordinateMap V F.denominator ≠ 0 :=
  fun h => F.denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)

theorem coeff_value (F : ParameterFraction V D) (r : ℕ) :
    F.value.coeff r = coordinateMap V (F.numerator.coeff r) / coordinateMap V F.denominator := by
  simp only [value, Polynomial.coeff_mul_C, Polynomial.coeff_map, div_eq_mul_inv]

def ofPolynomial (Q : Polynomial (Poly n)) (hQ : AmbientCoefficientBound D Q) : ParameterFraction V D where
  numerator := Q
  denominator := 1
  denominator_proper := (inferInstance : V.ideal.IsPrime).one_notMem
  numerator_degree := hQ
  denominator_degree := by simp

theorem value_ofPolynomial (Q : Polynomial (Poly n)) (hQ : AmbientCoefficientBound D Q) :
    (ofPolynomial (V := V) Q hQ).value = Q.map (coordinateMap V) := by
  simp [value, ofPolynomial]

def add (F : ParameterFraction V D) (G : ParameterFraction V E) : ParameterFraction V (D + E) where
  numerator := F.numerator * Polynomial.C G.denominator + G.numerator * Polynomial.C F.denominator
  denominator := F.denominator * G.denominator
  denominator_proper := fun h => ((inferInstance : V.ideal.IsPrime).mem_or_mem h).elim F.denominator_proper G.denominator_proper
  numerator_degree := by
    have hF := F.numerator_degree.mul (AmbientCoefficientBound.C G.denominator_degree)
    have hG := G.numerator_degree.mul (AmbientCoefficientBound.C F.denominator_degree)
    simpa only [Nat.add_comm E D, max_self] using hF.add hG
  denominator_degree := (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add F.denominator_degree G.denominator_degree)

def mul (F : ParameterFraction V D) (G : ParameterFraction V E) : ParameterFraction V (D + E) where
  numerator := F.numerator * G.numerator
  denominator := F.denominator * G.denominator
  denominator_proper := fun h => ((inferInstance : V.ideal.IsPrime).mem_or_mem h).elim F.denominator_proper G.denominator_proper
  numerator_degree := F.numerator_degree.mul G.numerator_degree
  denominator_degree := (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add F.denominator_degree G.denominator_degree)

def neg (F : ParameterFraction V D) : ParameterFraction V D where
  numerator := -F.numerator
  denominator := F.denominator
  denominator_proper := F.denominator_proper
  numerator_degree := by intro r; simpa only [Polynomial.coeff_neg, MvPolynomial.totalDegree_neg] using F.numerator_degree r
  denominator_degree := F.denominator_degree

theorem value_add (F : ParameterFraction V D) (G : ParameterFraction V E) :
    (F.add G).value = F.value + G.value := by
  ext r
  simp only [coeff_value, add, Polynomial.coeff_add, Polynomial.coeff_mul_C, map_add, map_mul]
  field_simp [F.value_denominator_ne_zero, G.value_denominator_ne_zero] <;> ring

theorem value_mul (F : ParameterFraction V D) (G : ParameterFraction V E) :
    (F.mul G).value = F.value * G.value := by
  simp only [value, mul, Polynomial.map_mul, map_mul, mul_inv_rev, map_mul]
  ring

theorem value_neg (F : ParameterFraction V D) : F.neg.value = -F.value := by
  ext r
  simp only [coeff_value, neg, Polynomial.coeff_neg, map_neg, neg_div]

theorem eval_add (F : ParameterFraction V D) (G : ParameterFraction V E)
    (x : Point n) (t : ℂ) (hF : MvPolynomial.aeval x F.denominator ≠ 0)
    (hG : MvPolynomial.aeval x G.denominator ≠ 0) : (F.add G).eval x t = F.eval x t + G.eval x t := by
  simp only [eval, add, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, map_mul]
  change (_ * MvPolynomial.aeval x G.denominator + _ * MvPolynomial.aeval x F.denominator) / _ = _
  simp only [MvPolynomial.aeval_eq_eval] at hF hG ⊢
  field_simp [hF, hG] <;> ring

theorem eval_mul (F : ParameterFraction V D) (G : ParameterFraction V E) (x : Point n) (t : ℂ) :
    (F.mul G).eval x t = F.eval x t * G.eval x t := by
  simp only [eval, mul, Polynomial.eval₂_mul, map_mul, mul_div_mul_comm]

theorem eval_neg (F : ParameterFraction V D) (x : Point n) (t : ℂ) : F.neg.eval x t = -F.eval x t := by
  simp [eval, neg, neg_div]

theorem eval_eq_of_value_eq (F : ParameterFraction V D) (G : ParameterFraction V E)
    (hFG : F.value = G.value) (x : Point n) (hx : x ∈ V.points) (t : ℂ)
    (hF : MvPolynomial.aeval x F.denominator ≠ 0) (hG : MvPolynomial.aeval x G.denominator ≠ 0) :
    F.eval x t = G.eval x t := by
  have hcross : (F.numerator * Polynomial.C G.denominator).map (coordinateMap V) =
      (G.numerator * Polynomial.C F.denominator).map (coordinateMap V) := by
    ext r
    have hc := congrArg (fun p : Polynomial (CarrierField V) => p.coeff r) hFG
    rw [F.coeff_value, G.coeff_value] at hc
    have h := (div_eq_div_iff F.value_denominator_ne_zero G.value_denominator_ne_zero).mp hc
    simpa only [Polynomial.coeff_map, Polynomial.coeff_mul_C, map_mul] using h
  have h := parameterPolynomial_specialization V _ _ hcross x hx t
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
  change F.numerator.eval₂ (MvPolynomial.aeval x).toRingHom t * MvPolynomial.aeval x G.denominator =
    G.numerator.eval₂ (MvPolynomial.aeval x).toRingHom t * MvPolynomial.aeval x F.denominator at h
  exact (div_eq_div_iff hF hG).mpr h

end ParameterFraction

theorem parameterFraction_of_coefficients {n D : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (p : Polynomial (CarrierField V)) (hp : CoefficientBound V D p) (d : ℕ) (hpd : p.natDegree ≤ d) :
    ∃ F : ParameterFraction V ((d + 1) * D), F.value = p ∧ F.numerator.natDegree ≤ d := by
  obtain ⟨H, Q, hH, hHd, hQd, hQ, hmap⟩ := clear_parameter_coefficients V p hp d hpd
  let F : ParameterFraction V ((d + 1) * D) := ⟨Q, H, hH, hQ, hHd⟩
  refine ⟨F, ?_, hQd⟩
  dsimp [F, ParameterFraction.value]
  rw [hmap]
  have hHne : coordinateMap V H ≠ 0 := fun h => hH ((coordinateMap_eq_zero_iff V H).mp h)
  calc
    _ = p * (Polynomial.C (coordinateMap V H) * Polynomial.C (coordinateMap V H)⁻¹) := by ring
    _ = p := by rw [← map_mul, mul_inv_cancel₀ hHne, map_one, mul_one]

namespace ParameterFraction

variable {n D E : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

def mono (F : ParameterFraction V D) (hDE : D ≤ E) : ParameterFraction V E :=
  { F with numerator_degree := fun r => (F.numerator_degree r).trans hDE
           denominator_degree := F.denominator_degree.trans hDE }

theorem value_mono (F : ParameterFraction V D) (hDE : D ≤ E) : (F.mono hDE).value = F.value := rfl

theorem eval_mono (F : ParameterFraction V D) (hDE : D ≤ E) (x : Point n) (t : ℂ) :
    (F.mono hDE).eval x t = F.eval x t := rfl

def derivative (F : ParameterFraction V D) : ParameterFraction V D where
  numerator := F.numerator.derivative
  denominator := F.denominator
  denominator_proper := F.denominator_proper
  numerator_degree := by
    intro r
    rw [Polynomial.coeff_derivative]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have hc : (((r + 1 : ℕ) : Poly n)).totalDegree = 0 := by
      change (MvPolynomial.C ((r + 1 : ℕ) : ℂ)).totalDegree = 0
      exact MvPolynomial.totalDegree_C _
    simp only [Nat.cast_add, Nat.cast_one] at hc
    simpa only [hc, Nat.add_zero] using F.numerator_degree (r + 1)
  denominator_degree := F.denominator_degree

theorem value_derivative (F : ParameterFraction V D) : F.derivative.value = F.value.derivative := by
  simp only [value, derivative, Polynomial.derivative_mul, Polynomial.derivative_C,
    mul_zero, add_zero, Polynomial.derivative_map]

theorem eval_derivative (F : ParameterFraction V D) (x : Point n) (t : ℂ) :
    F.derivative.eval x t = (F.numerator.map (MvPolynomial.aeval x).toRingHom).derivative.eval t /
      MvPolynomial.aeval x F.denominator := by
  simp only [eval, derivative, Polynomial.derivative_map, Polynomial.eval_map]

theorem eval_eq_zero_of_value_eq_zero (F : ParameterFraction V D) (hF : F.value = 0)
    (x : Point n) (hx : x ∈ V.points) (t : ℂ) (hden : MvPolynomial.aeval x F.denominator ≠ 0) :
    F.eval x t = 0 := by
  let Z := ofPolynomial (V := V) (0 : Polynomial (Poly n)) (D := 0)
    (by intro r; simp)
  have hZ : Z.value = 0 := by
    dsimp [Z, value, ofPolynomial]
    rw [Polynomial.map_zero, zero_mul]
  have h := F.eval_eq_of_value_eq Z (hF.trans hZ.symm) x hx t hden (by simp [Z, ofPolynomial])
  simpa only [Z, eval, ofPolynomial, Polynomial.eval₂_zero, zero_div] using h

theorem separable_specialization {J : ℕ} (F : ParameterFraction V D)
    (U : ParameterFraction V E) (W : ParameterFraction V J)
    (hbez : U.value * F.value + W.value * F.derivative.value = 1)
    (x : Point n) (hx : x ∈ V.points) (t : ℂ)
    (hF : MvPolynomial.aeval x F.denominator ≠ 0)
    (hU : MvPolynomial.aeval x U.denominator ≠ 0)
    (hW : MvPolynomial.aeval x W.denominator ≠ 0) (hroot : F.eval x t = 0) :
    (F.numerator.map (MvPolynomial.aeval x).toRingHom).derivative.eval t ≠ 0 := by
  let T := (U.mul F).add (W.mul F.derivative)
  let O := ofPolynomial (V := V) (1 : Polynomial (Poly n)) (D := 0)
    (by
      simpa only [Polynomial.C_1] using
        (AmbientCoefficientBound.C (n := n) (D := 0) (f := 1) MvPolynomial.totalDegree_one.le))
  have hOvalue : O.value = 1 := by
    simp only [O, value, ofPolynomial, Polynomial.map_one, map_one, inv_one, mul_one]
  have hT : T.value = O.value := by
    rw [hOvalue]
    simpa only [T, value_add, value_mul] using hbez
  have hdenT : MvPolynomial.aeval x T.denominator ≠ 0 := by
    simp only [T, add, mul, derivative, map_mul]
    exact mul_ne_zero (mul_ne_zero hU hF) (mul_ne_zero hW hF)
  have h := T.eval_eq_of_value_eq O hT x hx t hdenT (by simp [O, ofPolynomial])
  have hUF : MvPolynomial.aeval x (U.mul F).denominator ≠ 0 := by
    simpa only [mul, map_mul] using mul_ne_zero hU hF
  have hWF : MvPolynomial.aeval x (W.mul F.derivative).denominator ≠ 0 := by
    simpa only [mul, derivative, map_mul] using mul_ne_zero hW hF
  simp only [T, eval_add _ _ x t hUF hWF, eval_mul, hroot, mul_zero, zero_add] at h
  have hone : O.eval x t = 1 := by simp [O, ofPolynomial, eval]
  rw [hone, eval_derivative] at h
  intro hz
  rw [hz, zero_div, mul_zero] at h
  exact zero_ne_one h

end ParameterFraction

theorem exclude_parameter_poles {n m D : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (F : Fin m → ParameterFraction V D) :
    ∃ H : Poly n, H ∉ V.ideal ∧ H.totalDegree ≤ m * D ∧
      ∀ x : Point n, MvPolynomial.aeval x H ≠ 0 →
        ∀ i, MvPolynomial.aeval x (F i).denominator ≠ 0 := by
  let H := ∏ i : Fin m, (F i).denominator
  have hH : H ∉ V.ideal := by
    intro hmem
    have hz := (coordinateMap_eq_zero_iff V H).mpr hmem
    have hn : coordinateMap V H ≠ 0 := by
      dsimp [H]
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => (F i).value_denominator_ne_zero)
    exact hn hz
  refine ⟨H, hH, ?_, ?_⟩
  · apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => (F i).denominator_degree)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  · intro x hx i
    have h : (∏ j : Fin m, MvPolynomial.aeval x (F j).denominator) ≠ 0 := by
      simpa only [H, map_prod] using hx
    exact Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ _)

namespace ParameterFraction

variable {n D : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

def sum : {m : ℕ} → (Fin m → ParameterFraction V D) → ParameterFraction V (m * D)
  | 0, _ => ofPolynomial (V := V) (0 : Polynomial (Poly n)) (by intro r; simp)
  | m + 1, F => ((F 0).add (sum (fun i : Fin m => F i.succ))).mono
      (by simp only [Nat.add_mul, one_mul]; omega)
termination_by m _ => m

theorem value_sum {m : ℕ} (F : Fin m → ParameterFraction V D) :
    (sum F).value = ∑ i, (F i).value := by
  induction m with
  | zero =>
      rw [sum]
      simp only [value, ofPolynomial, Polynomial.map_zero, zero_mul, Fin.sum_univ_zero]
  | succ m ih =>
      rw [sum, value_mono, value_add, ih, Fin.sum_univ_succ]

theorem sum_denominator_nonzero {m : ℕ} (F : Fin m → ParameterFraction V D) (x : Point n)
    (hF : ∀ i, MvPolynomial.aeval x (F i).denominator ≠ 0) :
    MvPolynomial.aeval x (sum F).denominator ≠ 0 := by
  induction m with
  | zero => rw [sum]; change MvPolynomial.aeval x (1 : Poly n) ≠ 0; simp
  | succ m ih =>
      rw [sum]
      change MvPolynomial.aeval x ((F 0).denominator * (sum (fun i : Fin m => F i.succ)).denominator) ≠ 0
      rw [map_mul]
      exact mul_ne_zero (hF 0) (ih _ (fun i => hF i.succ))

theorem eval_sum {m : ℕ} (F : Fin m → ParameterFraction V D) (x : Point n) (t : ℂ)
    (hF : ∀ i, MvPolynomial.aeval x (F i).denominator ≠ 0) :
    (sum F).eval x t = ∑ i, (F i).eval x t := by
  induction m with
  | zero =>
      rw [sum]
      simp only [eval, ofPolynomial, Polynomial.eval₂_zero, zero_div, Fin.sum_univ_zero]
  | succ m ih =>
      rw [sum, eval_mono, eval_add _ _ x t (hF 0) (sum_denominator_nonzero _ x (fun i => hF i.succ)),
        ih _ (fun i => hF i.succ), Fin.sum_univ_succ]

theorem common_roots_of_gcd_identities {m E J : ℕ}
    (F : Fin m → ParameterFraction V D) (P : ParameterFraction V E)
    (Q U : Fin m → ParameterFraction V J)
    (hquot : ∀ i, (F i).value = P.value * (Q i).value)
    (hbez : P.value = ∑ i, (F i).value * (U i).value)
    (x : Point n) (hx : x ∈ V.points) (t : ℂ)
    (hF : ∀ i, MvPolynomial.aeval x (F i).denominator ≠ 0)
    (hP : MvPolynomial.aeval x P.denominator ≠ 0)
    (hQ : ∀ i, MvPolynomial.aeval x (Q i).denominator ≠ 0)
    (hU : ∀ i, MvPolynomial.aeval x (U i).denominator ≠ 0) :
    P.eval x t = 0 ↔ ∀ i, (F i).eval x t = 0 := by
  constructor
  · intro hroot i
    have hden : MvPolynomial.aeval x (P.mul (Q i)).denominator ≠ 0 := by
      simpa only [mul, map_mul] using mul_ne_zero hP (hQ i)
    have h := (F i).eval_eq_of_value_eq (P.mul (Q i))
      ((hquot i).trans (value_mul _ _).symm) x hx t (hF i) hden
    simpa only [eval_mul, hroot, zero_mul] using h
  · intro hroot
    let S := sum (fun i => (F i).mul (U i))
    have hS : P.value = S.value := by simpa only [S, value_sum, value_mul] using hbez
    have hden (i : Fin m) : MvPolynomial.aeval x ((F i).mul (U i)).denominator ≠ 0 := by
      simpa only [mul, map_mul] using mul_ne_zero (hF i) (hU i)
    have h := P.eval_eq_of_value_eq S hS x hx t hP (sum_denominator_nonzero _ x hden)
    rw [h]
    dsimp [S]
    rw [eval_sum _ x t hden]
    apply Finset.sum_eq_zero
    intro i hi
    rw [eval_mul, hroot i, zero_mul]

end ParameterFraction

theorem bounded_separability_bezout (d : ℕ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
      (D : ℕ) (p : Polynomial (CarrierField V)), CoefficientBound V D p →
      p.natDegree ≤ d → p.Separable →
      ∃ U W : Polynomial (CarrierField V),
        U * p + W * p.derivative = 1 ∧
        U.natDegree ≤ 2 * d ^ 2 ∧ W.natDegree ≤ 2 * d ^ 2 ∧
        CoefficientBound V (B * D) U ∧ CoefficientBound V (B * D) W := by
  classical
  obtain ⟨B, hB, hfamily⟩ := bounded_family_gcd 2 d
  refine ⟨2 * B, by omega, ?_⟩
  intro n V inst D p hb hd hs
  let f : Fin 2 → Polynomial (CarrierField V) := fun i => if i = 0 then p else p.derivative
  have hfb (i : Fin 2) : CoefficientBound V (2 * D) (f i) := by
    by_cases hi : i = 0
    · simpa only [f, if_pos hi] using hb.mono (show D ≤ 2 * D by omega)
    · simpa only [f, if_neg hi] using hb.derivative.mono (show D ≤ 2 * D by omega)
  have hfd (i : Fin 2) : (f i).natDegree ≤ d := by
    by_cases hi : i = 0
    · simpa only [f, if_pos hi] using hd
    · simpa only [f, if_neg hi] using
        ((Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)).trans hd
  obtain ⟨P, U, Q, hmono, hPd, hUd, hQd, hPb, hUb, hQb, hquot, heq⟩ := hfamily V (2 * D) f hfb hfd
  have hquot0 : p = P * Q 0 := by simpa only [f, if_pos rfl] using hquot 0
  have hquot1 : p.derivative = P * Q 1 := by simpa [f] using hquot 1
  have hPzero : P ≠ 0 := by intro h; exact hs.ne_zero (by simpa only [h, zero_mul] using hquot0)
  have hPmonic : P.Monic := hmono.resolve_left hPzero
  have hPunit : IsUnit P := by
    obtain ⟨a, b, hab⟩ := hs
    apply isUnit_of_dvd_one
    rw [← hab]
    exact dvd_add (dvd_mul_of_dvd_right ⟨Q 0, hquot0⟩ a) (dvd_mul_of_dvd_right ⟨Q 1, hquot1⟩ b)
  have hPone : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hPmonic
    (Polynomial.natDegree_eq_zero_of_isUnit hPunit)
  refine ⟨U 0, U 1, ?_, hUd 0, hUd 1, ?_, ?_⟩
  · rw [hPone, Fin.sum_univ_two] at heq
    simp [f] at heq
    linear_combination -heq
  · simpa only [mul_assoc, mul_left_comm] using hUb 0
  · simpa only [mul_assoc, mul_left_comm] using hUb 1

namespace ParameterFraction

variable {n D : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]

theorem specialized_monic_coefficient (F : ParameterFraction V D) (hF : F.value.Monic)
    (x : Point n) (hx : x ∈ V.points) :
    (F.numerator.map (MvPolynomial.aeval x).toRingHom).coeff F.value.natDegree =
      MvPolynomial.aeval x F.denominator := by
  have hlead := hF.coeff_natDegree
  rw [coeff_value] at hlead
  have hcoeff : coordinateMap V (F.numerator.coeff F.value.natDegree) = coordinateMap V F.denominator := by
    simpa only [one_mul] using (div_eq_iff F.value_denominator_ne_zero).mp hlead
  have hmem : F.numerator.coeff F.value.natDegree - F.denominator ∈ V.ideal := by
    apply (coordinateMap_eq_zero_iff V _).mp
    rw [map_sub, hcoeff, sub_self]
  have heval := hx _ hmem
  rw [map_sub] at heval
  rw [Polynomial.coeff_map]
  exact sub_eq_zero.mp heval

theorem specialized_nonzero (F : ParameterFraction V D) (hF : F.value.Monic)
    (x : Point n) (hx : x ∈ V.points) (hden : MvPolynomial.aeval x F.denominator ≠ 0) :
    F.numerator.map (MvPolynomial.aeval x).toRingHom ≠ 0 := by
  intro hzero
  have h := congrArg (fun Q : Polynomial ℂ => Q.coeff F.value.natDegree) hzero
  rw [F.specialized_monic_coefficient hF x hx, Polynomial.coeff_zero] at h
  exact hden h

theorem specialized_degree (F : ParameterFraction V D) (hF : F.value.Monic)
    (hdegree : F.numerator.natDegree ≤ F.value.natDegree) (x : Point n) (hx : x ∈ V.points)
    (hden : MvPolynomial.aeval x F.denominator ≠ 0) :
    (F.numerator.map (MvPolynomial.aeval x).toRingHom).natDegree = F.value.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (Polynomial.natDegree_map_le.trans hdegree)
  rw [F.specialized_monic_coefficient hF x hx]
  exact hden

end ParameterFraction

/-- A monic separable coordinate-field equation admits one bounded principal
open on which every specialized fiber has the same degree and simple roots. -/
theorem bounded_simple_root_fraction (d : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
      (D : ℕ) (p : Polynomial (CarrierField V)), CoefficientBound V D p →
      p.natDegree ≤ d → p.Monic → p.Separable →
      ∃ (H : Poly n) (F : ParameterFraction V (M * D)), H ∉ V.ideal ∧
        H.totalDegree ≤ M * D ∧ F.value = p ∧ F.numerator.natDegree ≤ p.natDegree ∧
        ∀ x ∈ V.points, MvPolynomial.aeval x H ≠ 0 →
          MvPolynomial.aeval x F.denominator ≠ 0 ∧
          (F.numerator.map (MvPolynomial.aeval x).toRingHom).natDegree = p.natDegree ∧
          F.numerator.map (MvPolynomial.aeval x).toRingHom ≠ 0 ∧
          ∀ t : ℂ, (F.numerator.map (MvPolynomial.aeval x).toRingHom).eval t = 0 →
            (F.numerator.map (MvPolynomial.aeval x).toRingHom).derivative.eval t ≠ 0 := by
  classical
  obtain ⟨B, hB, hbezout⟩ := bounded_separability_bezout d
  let E := d + 1 + (2 * d ^ 2 + 1) * B
  refine ⟨3 * E, by dsimp [E]; omega, ?_⟩
  intro n V inst D p hb hd hm hs
  obtain ⟨u, w, hbez, hud, hwd, hub, hwb⟩ := hbezout V D p hb hd hs
  obtain ⟨F₀, hF₀, hFdegree⟩ := parameterFraction_of_coefficients V p hb p.natDegree le_rfl
  obtain ⟨U₀, hU₀, hUdegree⟩ := parameterFraction_of_coefficients V u hub (2 * d ^ 2) hud
  obtain ⟨W₀, hW₀, hWdegree⟩ := parameterFraction_of_coefficients V w hwb (2 * d ^ 2) hwd
  have hFbudget : (p.natDegree + 1) * D ≤ E * D :=
    Nat.mul_le_mul_right D (by dsimp [E]; omega)
  have hUbudget : (2 * d ^ 2 + 1) * (B * D) ≤ E * D := by
    simpa only [mul_assoc] using Nat.mul_le_mul_right D (show (2 * d ^ 2 + 1) * B ≤ E by dsimp [E]; omega)
  let F := F₀.mono hFbudget
  let U := U₀.mono hUbudget
  let W := W₀.mono hUbudget
  have hF : F.value = p := hF₀
  have hU : U.value = u := hU₀
  have hW : W.value = w := hW₀
  let T : Fin 3 → ParameterFraction V (E * D) := fun i => if i = 0 then F else if i = 1 then U else W
  obtain ⟨H, hH, hHdeg, hpoles⟩ := exclude_parameter_poles V T
  have hbudget : E * D ≤ (3 * E) * D := Nat.mul_le_mul_right D (by omega : E ≤ 3 * E)
  let F' := F.mono hbudget
  refine ⟨H, F', hH, ?_, hF, hFdegree, ?_⟩
  · simpa only [mul_assoc] using hHdeg
  · intro x hx hxH
    change MvPolynomial.aeval x F.denominator ≠ 0 ∧
      (F.numerator.map (MvPolynomial.aeval x).toRingHom).natDegree = p.natDegree ∧
      F.numerator.map (MvPolynomial.aeval x).toRingHom ≠ 0 ∧
      ∀ t : ℂ, (F.numerator.map (MvPolynomial.aeval x).toRingHom).eval t = 0 →
        (F.numerator.map (MvPolynomial.aeval x).toRingHom).derivative.eval t ≠ 0
    have hFp : MvPolynomial.aeval x F.denominator ≠ 0 := by simpa [T] using hpoles x hxH 0
    have hUp : MvPolynomial.aeval x U.denominator ≠ 0 := by simpa [T] using hpoles x hxH 1
    have hWp : MvPolynomial.aeval x W.denominator ≠ 0 := by simpa [T] using hpoles x hxH 2
    have hFm : F.value.Monic := hF.symm ▸ hm
    have hnum : F.numerator.natDegree ≤ F.value.natDegree := by
      rw [hF]
      change F₀.numerator.natDegree ≤ p.natDegree
      exact hFdegree
    refine ⟨hFp, by simpa only [hF] using F.specialized_degree hFm hnum x hx hFp,
      F.specialized_nonzero hFm x hx hFp, ?_⟩
    intro t hroot
    have hFroot : F.eval x t = 0 := by
      change F.numerator.eval₂ (MvPolynomial.aeval x).toRingHom t / MvPolynomial.aeval x F.denominator = 0
      rw [← Polynomial.eval_map, hroot, zero_div]
    have hSF : U.value * F.value + W.value * F.derivative.value = 1 := by
      rw [ParameterFraction.value_derivative, hF, hU, hW]
      exact hbez
    exact F.separable_specialization U W hSF x hx t hFp hUp hWp hFroot

theorem bounded_simple_root_equation (d : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
      (D : ℕ) (p : Polynomial (CarrierField V)), CoefficientBound V D p →
      p.natDegree ≤ d → p.Monic → p.Separable →
      ∃ (H : Poly n) (Q : Polynomial (Poly n)), H ∉ V.ideal ∧
        H.totalDegree ≤ M * D ∧ AmbientCoefficientBound (M * D) Q ∧
        Q.natDegree ≤ p.natDegree ∧
        ∀ x ∈ V.points, MvPolynomial.aeval x H ≠ 0 →
          (Q.map (MvPolynomial.aeval x).toRingHom).natDegree = p.natDegree ∧
          Q.map (MvPolynomial.aeval x).toRingHom ≠ 0 ∧
          ∀ t : ℂ, (Q.map (MvPolynomial.aeval x).toRingHom).eval t = 0 →
            (Q.map (MvPolynomial.aeval x).toRingHom).derivative.eval t ≠ 0 := by
  obtain ⟨M, hM, hproduce⟩ := bounded_simple_root_fraction d
  refine ⟨M, hM, ?_⟩
  intro n V inst D p hb hd hm hs
  obtain ⟨H, F, hH, hHd, hF, hFd, hgood⟩ := hproduce V D p hb hd hm hs
  exact ⟨H, F.numerator, hH, hHd, F.numerator_degree, hFd, fun x hx hHx => (hgood x hx hHx).2⟩

theorem complex_root_fiber (q : Polynomial ℂ) (hq : q ≠ 0) :
    {t : ℂ | q.eval t = 0}.Finite ∧ {t : ℂ | q.eval t = 0}.ncard ≤ q.natDegree ∧
      (0 < q.natDegree → {t : ℂ | q.eval t = 0}.Nonempty) := by
  classical
  have hset : {t : ℂ | q.eval t = 0} = (q.roots.toFinset : Set ℂ) := by
    ext t
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hq,
      Polynomial.IsRoot]
  refine ⟨by rw [hset]; exact Finset.finite_toSet _, ?_, ?_⟩
  · rw [hset, Set.ncard_coe_finset]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' q)
  · intro hpos
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root q (by
      rw [Polynomial.degree_eq_natDegree hq]
      exact_mod_cast ne_of_gt hpos)
    exact ⟨t, ht⟩

theorem directionGraph_injective {K : Type*} [Field K] {e : ℕ}
    (w : Fin e → Fin e → K) (a b : Fin e) (hpivot : w a b ≠ 0) (hbb : w b b = 0) :
    Function.Injective (directionGraph w a b) := by
  intro s t hst
  have h := congrFun hst b
  simpa [directionGraph, hbb, hpivot] using h

theorem directionGraph_root_fiber {e : ℕ} (w : Fin e → Fin e → ℂ)
    (a b : Fin e) (hpivot : w a b ≠ 0) (hbb : w b b = 0)
    (q : Polynomial ℂ) (hq : q ≠ 0) :
    (directionGraph w a b '' {t : ℂ | q.eval t = 0}).Finite ∧
      (directionGraph w a b '' {t : ℂ | q.eval t = 0}).ncard ≤ q.natDegree := by
  obtain ⟨hfinite, hcard, hnonempty⟩ := complex_root_fiber q hq
  refine ⟨hfinite.image _, ?_⟩
  rw [Set.ncard_image_of_injective _ (directionGraph_injective w a b hpivot hbb)]
  exact hcard

/-- Use the shared Hilbert/transcendence-degree bridge when constructing the
generic root-cover components. No new dimension convention is introduced. -/
theorem affine_dimension_eq_trdeg {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime] :
    (V.dimension : Cardinal) = Algebra.trdeg ℂ (Poly n ⧸ V.ideal) := by
  exact OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg V.ideal
    (OAI.QuarticPowerFree.coordinateHilbert V.ideal)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal)

/-- Every component of a flat algebra over a domain dominates the base. -/
theorem flat_minimal_prime_under_eq_bot {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    (Q : Ideal S) (hQ : Q ∈ minimalPrimes S) : Q.under R = ⊥ := by
  letI : Q.IsPrime := hQ.isPrime
  obtain ⟨P, hPQ, hP, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R))
      (q := Q.under R) Q bot_le
  have hQP : Q ≤ P := hQ.2 ⟨hP, bot_le⟩ hPQ
  have hEq : P = Q := le_antisymm hPQ hQP
  subst P
  exact hPover.over.symm

/-- Integral components obtained from a flat cover have a point above every
base prime. This uses going down only to establish dominance. -/
theorem integral_flat_component_lies_over {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra.IsIntegral R S]
    (Q : Ideal S) (hQ : Q ∈ minimalPrimes S) (P : Ideal R) [P.IsPrime] :
    ∃ T : Ideal S, Q ≤ T ∧ T.IsPrime ∧ T.under R = P := by
  letI : Q.IsPrime := hQ.isPrime
  exact Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P Q
    (by rw [flat_minimal_prime_under_eq_bot Q hQ]; exact bot_le)

/-- The monic root algebra is finite free, so none of its irreducible
components is supported only over a proper closed subset of the base. -/
theorem monic_root_minimal_prime_under_eq_bot {R : Type*} [CommRing R] [IsDomain R]
    (q : Polynomial R) (hq : q.Monic) (Q : Ideal (AdjoinRoot q))
    (hQ : Q ∈ minimalPrimes (AdjoinRoot q)) : Q.under R = ⊥ := by
  letI : Module.Free R (AdjoinRoot q) := hq.free_adjoinRoot
  exact flat_minimal_prime_under_eq_bot Q hQ

theorem monic_root_component_lies_over {R : Type*} [CommRing R] [IsDomain R]
    (q : Polynomial R) (hq : q.Monic) (Q : Ideal (AdjoinRoot q))
    (hQ : Q ∈ minimalPrimes (AdjoinRoot q)) (P : Ideal R) [P.IsPrime] :
    ∃ T : Ideal (AdjoinRoot q), Q ≤ T ∧ T.IsPrime ∧ T.under R = P := by
  letI : Module.Free R (AdjoinRoot q) := hq.free_adjoinRoot
  letI : Algebra.IsIntegral R (AdjoinRoot q) := AdjoinRoot.isIntegral_of_monic hq
  exact integral_flat_component_lies_over Q hQ P

/-- Lying over an algebraically closed point produces a literal algebra
homomorphism extending that point, with a prescribed prime component in its
kernel. No choice of rational factor coefficients is involved. -/
theorem integral_point_extension {k R S : Type*} [Field k] [IsAlgClosed k]
    [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] [Algebra R S]
    [IsScalarTower k R S] [Algebra.IsIntegral R S]
    (f : R →ₐ[k] k) (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.under R ≤ RingHom.ker f.toRingHom) :
    ∃ g : S →ₐ[k] k, (∀ r, g (algebraMap R S r) = f r) ∧
      Q ≤ RingHom.ker g.toRingHom := by
  classical
  let P := RingHom.ker f.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime f.toRingHom
  obtain ⟨T, hQT, hT, hTP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P Q hQ
  letI : T.IsPrime := hT
  let h : R →ₐ[k] S ⧸ T :=
    (Ideal.Quotient.mkₐ k T).comp (IsScalarTower.toAlgHom k R S)
  have hf : Function.Surjective f := fun x => ⟨algebraMap k R x, f.commutes x⟩
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker h.toRingHom := by
    intro r hr
    change Ideal.Quotient.mk T (algebraMap R S r) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change r ∈ T.under R
    rw [hTP]
    exact hr
  let hbar : k →ₐ[k] S ⧸ T := AlgHom.liftOfSurjective f hf h hker
  have hbase (r : R) : algebraMap k (S ⧸ T) (f r) = algebraMap R (S ⧸ T) r := by
    have hh := AlgHom.liftOfSurjective_apply f hf h hker r
    have hc := hbar.commutes (f r)
    simpa only [Algebra.algebraMap_self, RingHom.id_apply, hbar, h, AlgHom.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.toAlgHom_apply,
      Ideal.Quotient.mk_algebraMap] using hc.symm.trans hh
  have hcomp : (algebraMap k (S ⧸ T)).comp f.toRingHom = algebraMap R (S ⧸ T) :=
    RingHom.ext hbase
  letI : Algebra.IsIntegral k (S ⧸ T) := ⟨fun x => by
    have hx : (algebraMap R (S ⧸ T)).IsIntegralElem x := Algebra.IsIntegral.isIntegral x
    rw [← hcomp] at hx
    exact hx.of_comp⟩
  let E : k ≃ₐ[k] S ⧸ T := AlgEquiv.ofBijective (Algebra.ofId k (S ⧸ T))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let g : S →ₐ[k] k := E.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k T)
  refine ⟨g, ?_, ?_⟩
  · intro r
    change E.symm (algebraMap R (S ⧸ T) r) = f r
    rw [← hbase]
    exact E.symm.commutes (f r)
  · intro s hs
    change E.symm (Ideal.Quotient.mk T s) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hQT hs), map_zero]

theorem monic_root_component_point {k R : Type*} [Field k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [Algebra k R]
    (q : Polynomial R) (hq : q.Monic) (Q : Ideal (AdjoinRoot q))
    (hQ : Q ∈ minimalPrimes (AdjoinRoot q)) (f : R →ₐ[k] k) :
    ∃ g : AdjoinRoot q →ₐ[k] k, (∀ r, g (algebraMap R (AdjoinRoot q) r) = f r) ∧
      Q ≤ RingHom.ker g.toRingHom := by
  letI : Q.IsPrime := hQ.isPrime
  letI : Algebra.IsIntegral R (AdjoinRoot q) := AdjoinRoot.isIntegral_of_monic hq
  exact integral_point_extension f Q
    (by rw [monic_root_minimal_prime_under_eq_bot q hq Q hQ]; exact bot_le)

theorem quotient_algebraMap_injective_of_under_eq_bot {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (Q : Ideal S) (hQ : Q.under R = ⊥) :
    Function.Injective (algebraMap R (S ⧸ Q)) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  ext r
  simp only [RingHom.mem_ker, ← Ideal.Quotient.mk_algebraMap,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  change r ∈ Q.under R ↔ r = 0
  rw [hQ]
  exact Ideal.mem_bot

/-- The dimension calculation for integral components is the tower law for
transcendence degree, with the faithful base map supplied by dominance. -/
theorem integral_component_trdeg {k R S : Type} [Field k]
    [CommRing R] [IsDomain R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra R S] [IsScalarTower k R S] [Algebra.IsIntegral R S]
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.under R = ⊥) :
    Algebra.trdeg k (S ⧸ Q) = Algebra.trdeg k R := by
  letI : FaithfulSMul R (S ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective R (S ⧸ Q)).mpr
      (quotient_algebraMap_injective_of_under_eq_bot Q hQ)
  have htower := trdeg_add_eq k R (A := S ⧸ Q)
  rw [trdeg_eq_zero (R := R) (A := S ⧸ Q), add_zero] at htower
  exact htower.symm

theorem monic_root_component_trdeg {k R : Type} [Field k]
    [CommRing R] [IsDomain R] [Algebra k R]
    (q : Polynomial R) (hq : q.Monic) (Q : Ideal (AdjoinRoot q))
    (hQ : Q ∈ minimalPrimes (AdjoinRoot q)) :
    Algebra.trdeg k (AdjoinRoot q ⧸ Q) = Algebra.trdeg k R := by
  letI : Q.IsPrime := hQ.isPrime
  letI : Algebra.IsIntegral R (AdjoinRoot q) := AdjoinRoot.isIntegral_of_monic hq
  exact integral_component_trdeg (k := k) Q (monic_root_minimal_prime_under_eq_bot q hq Q hQ)

/-- An affine incidence is the actual prime kernel of its coordinate map. -/
def kernelGraphVariety {m : ℕ} {T : Type} [CommRing T] [IsDomain T] [Algebra ℂ T]
    (φ : Poly m →ₐ[ℂ] T) : AffineVariety m :=
  ⟨RingHom.ker φ.toRingHom, (RingHom.ker_isPrime φ.toRingHom).isRadical⟩

theorem kernelGraphVariety_irreducible {m : ℕ} {T : Type} [CommRing T]
    [IsDomain T] [Algebra ℂ T] (φ : Poly m →ₐ[ℂ] T) :
    (kernelGraphVariety φ).IsIrreducible := RingHom.ker_isPrime φ.toRingHom

theorem kernelGraphVariety_point {m : ℕ} {T : Type} [CommRing T]
    [IsDomain T] [Algebra ℂ T] (φ : Poly m →ₐ[ℂ] T) (g : T →ₐ[ℂ] ℂ) :
    (fun i => g (φ (MvPolynomial.X i))) ∈ (kernelGraphVariety φ).points := by
  intro f hf
  have hmap : MvPolynomial.aeval (fun i => g (φ (MvPolynomial.X i))) = g.comp φ := by
    exact (MvPolynomial.aeval_unique (g.comp φ)).symm
  rw [hmap]
  change g (φ f) = 0
  rw [show φ f = 0 from hf, map_zero]

/-- Sandwich the incidence coordinate ring between the original carrier's
coordinate ring and its algebraic root extension. -/
theorem kernelGraphVariety_dimension {n m : ℕ} {T : Type} [CommRing T]
    [IsDomain T] [Algebra ℂ T] (V : AffineVariety n) [V.ideal.IsPrime]
    (φ : Poly m →ₐ[ℂ] T) (ι : Poly n →ₐ[ℂ] Poly m)
    (hbase : RingHom.ker (φ.comp ι).toRingHom = V.ideal)
    (htrdeg : Algebra.trdeg ℂ T = Algebra.trdeg ℂ (Poly n ⧸ V.ideal)) :
    (kernelGraphVariety φ).dimension = V.dimension := by
  let Γ := kernelGraphVariety φ
  letI : Γ.ideal.IsPrime := kernelGraphVariety_irreducible φ
  have hcomap : Γ.ideal.comap ι.toRingHom = V.ideal := hbase
  let b : (Poly n ⧸ V.ideal) →ₐ[ℂ] Poly m ⧸ Γ.ideal :=
    Ideal.quotientMapₐ Γ.ideal ι (le_of_eq hcomap.symm)
  have hb : Function.Injective b := Ideal.quotientMap_injective'
    (H := le_of_eq hcomap.symm) (le_of_eq hcomap)
  have hlower := trdeg_le_of_injective b hb
  have hupper := trdeg_le_of_injective (Ideal.kerLiftAlg φ) (Ideal.kerLiftAlg_injective φ)
  have heq : Algebra.trdeg ℂ (Poly m ⧸ Γ.ideal) = Algebra.trdeg ℂ (Poly n ⧸ V.ideal) :=
    le_antisymm (hupper.trans_eq htrdeg) hlower
  rw [← affine_dimension_eq_trdeg Γ, ← affine_dimension_eq_trdeg V] at heq
  exact_mod_cast heq

abbrev PrincipalCoordinateRing {n : ℕ} (V : AffineVariety n) (H : Poly n) :=
  Localization.Away (Ideal.Quotient.mk V.ideal H)

def principalCoordinateMap {n : ℕ} (V : AffineVariety n) (H : Poly n) :
    Poly n →ₐ[ℂ] PrincipalCoordinateRing V H :=
  (IsScalarTower.toAlgHom ℂ (Poly n ⧸ V.ideal) (PrincipalCoordinateRing V H)).comp
    (Ideal.Quotient.mkₐ ℂ V.ideal)

theorem principalCoordinateRing_isDomain {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) : IsDomain (PrincipalCoordinateRing V H) :=
  Localization.Away.isDomain (by
    intro h
    exact hH (Ideal.Quotient.eq_zero_iff_mem.mp h))

theorem principalCoordinateMap_ker {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) :
    RingHom.ker (principalCoordinateMap V H).toRingHom = V.ideal := by
  have hne : Ideal.Quotient.mk V.ideal H ≠ 0 :=
    fun h => hH (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hinj := IsLocalization.injective (PrincipalCoordinateRing V H)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hne)
  ext f
  change algebraMap (Poly n ⧸ V.ideal) (PrincipalCoordinateRing V H)
    (Ideal.Quotient.mk V.ideal f) = 0 ↔ f ∈ V.ideal
  rw [← map_zero (algebraMap (Poly n ⧸ V.ideal) (PrincipalCoordinateRing V H)), hinj.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

def coordinatePoint {n : ℕ} (V : AffineVariety n) (z : Point n) (hz : z ∈ V.points) :
    (Poly n ⧸ V.ideal) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval z) hz

def principalCoordinatePoint {n : ℕ} (V : AffineVariety n) (H : Poly n)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0) :
    PrincipalCoordinateRing V H →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk V.ideal H)
    (f := coordinatePoint V z hz) (isUnit_iff_ne_zero.mpr hzH)

theorem principalCoordinatePoint_map {n : ℕ} (V : AffineVariety n) (H : Poly n)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0) (f : Poly n) :
    principalCoordinatePoint V H z hz hzH (principalCoordinateMap V H f) =
      MvPolynomial.aeval z f := by
  simp only [principalCoordinateMap, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    principalCoordinatePoint, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

theorem principalCoordinateRing_trdeg {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) :
    Algebra.trdeg ℂ (PrincipalCoordinateRing V H) = Algebra.trdeg ℂ (Poly n ⧸ V.ideal) := by
  letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
  letI : FaithfulSMul (Poly n ⧸ V.ideal) (PrincipalCoordinateRing V H) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective
      (PrincipalCoordinateRing V H) (powers_le_nonZeroDivisors_of_noZeroDivisors
        (fun h => hH (Ideal.Quotient.eq_zero_iff_mem.mp h))))
  letI : Algebra.IsAlgebraic (Poly n ⧸ V.ideal) (PrincipalCoordinateRing V H) :=
    IsLocalization.isAlgebraic (PrincipalCoordinateRing V H)
      (Submonoid.powers (Ideal.Quotient.mk V.ideal H))
  have htower := trdeg_add_eq ℂ (Poly n ⧸ V.ideal) (A := PrincipalCoordinateRing V H)
  rw [trdeg_eq_zero (R := Poly n ⧸ V.ideal) (A := PrincipalCoordinateRing V H), add_zero] at htower
  exact htower.symm

def rootGraphMap {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Q : Ideal (AdjoinRoot q)) [Q.IsPrime] : Poly (n + e) →ₐ[ℂ] AdjoinRoot q ⧸ Q :=
  MvPolynomial.aeval (Fin.addCases
    (fun i => algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q ⧸ Q)
      (principalCoordinateMap V H (MvPolynomial.X i)))
    (fun i => Ideal.Quotient.mk Q (v i)))

def rootGraphVariety {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Q : Ideal (AdjoinRoot q)) [Q.IsPrime] : AffineVariety (n + e) :=
  kernelGraphVariety (rootGraphMap V H q v Q)

theorem rootGraphMap_base {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Q : Ideal (AdjoinRoot q)) [Q.IsPrime] (f : Poly n) :
    rootGraphMap V H q v Q (MvPolynomial.rename (Fin.castAdd e) f) =
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q ⧸ Q)
        (principalCoordinateMap V H f) := by
  have hm : (rootGraphMap V H q v Q).comp (MvPolynomial.rename (Fin.castAdd e)) =
      (IsScalarTower.toAlgHom ℂ (PrincipalCoordinateRing V H) (AdjoinRoot q ⧸ Q)).comp
        (principalCoordinateMap V H) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [rootGraphMap]
  exact DFunLike.congr_fun hm f

theorem rootGraphVariety_dimension {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal)
    (q : Polynomial (PrincipalCoordinateRing V H)) (hq : q.Monic)
    (v : Fin e → AdjoinRoot q) (Q : Ideal (AdjoinRoot q)) [Q.IsPrime]
    (hQ : Q ∈ minimalPrimes (AdjoinRoot q)) :
    (rootGraphVariety V H q v Q).dimension = V.dimension := by
  letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
  have hunder := monic_root_minimal_prime_under_eq_bot q hq Q hQ
  have hinj := quotient_algebraMap_injective_of_under_eq_bot Q hunder
  have hbase : RingHom.ker ((rootGraphMap V H q v Q).comp
      (MvPolynomial.rename (Fin.castAdd e))).toRingHom = V.ideal := by
    ext f
    change rootGraphMap V H q v Q (MvPolynomial.rename (Fin.castAdd e) f) = 0 ↔ _
    rw [rootGraphMap_base, ← map_zero (algebraMap (PrincipalCoordinateRing V H)
      (AdjoinRoot q ⧸ Q)), hinj.eq_iff]
    change f ∈ RingHom.ker (principalCoordinateMap V H).toRingHom ↔ f ∈ V.ideal
    rw [principalCoordinateMap_ker V H hH]
  exact kernelGraphVariety_dimension V (rootGraphMap V H q v Q)
    (MvPolynomial.rename (Fin.castAdd e)) hbase
    ((monic_root_component_trdeg (k := ℂ) q hq Q hQ).trans
      (principalCoordinateRing_trdeg V H hH))

theorem rootGraphVariety_point_of_hom {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Q : Ideal (AdjoinRoot q)) [Q.IsPrime]
    (z : Point n) (g : AdjoinRoot q →ₐ[ℂ] ℂ)
    (hbase : ∀ f : Poly n, g (algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
      (principalCoordinateMap V H f)) = MvPolynomial.aeval z f)
    (hQg : Q ≤ RingHom.ker g.toRingHom) :
    joinPoints z (fun i => g (v i)) ∈ (rootGraphVariety V H q v Q).points := by
  let gbar : (AdjoinRoot q ⧸ Q) →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Q g hQg
  have hp := kernelGraphVariety_point (rootGraphMap V H q v Q) gbar
  have heq : (fun i => gbar (rootGraphMap V H q v Q (MvPolynomial.X i))) =
      joinPoints z (fun i => g (v i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [rootGraphMap, MvPolynomial.aeval_X, Fin.addCases_left, gbar,
        ← Ideal.Quotient.mk_algebraMap, joinPoints]
      change g (algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (principalCoordinateMap V H (MvPolynomial.X j))) = z j
      simpa only [MvPolynomial.aeval_X, Fin.addCases_left] using hbase (MvPolynomial.X j)
    · simp only [rootGraphMap, MvPolynomial.aeval_X, Fin.addCases_right, gbar, joinPoints]
      rfl
  rw [heq] at hp
  exact hp

theorem rootGraphVariety_dominant {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal)
    (q : Polynomial (PrincipalCoordinateRing V H)) (hq : q.Monic)
    (v : Fin e → AdjoinRoot q) (Q : Ideal (AdjoinRoot q)) [Q.IsPrime]
    (hQ : Q ∈ minimalPrimes (AdjoinRoot q))
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0) :
    ∃ d : Point e, joinPoints z d ∈ (rootGraphVariety V H q v Q).points := by
  letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
  obtain ⟨g, hgbase, hgQ⟩ := monic_root_component_point q hq Q hQ
    (principalCoordinatePoint V H z hz hzH)
  refine ⟨fun i => g (v i), rootGraphVariety_point_of_hom V H q v Q z g ?_ hgQ⟩
  intro f
  rw [hgbase, principalCoordinatePoint_map]

/-- Every specialized root belongs to at least one actual prime-kernel
incidence. -/
theorem rootGraphVariety_root_coverage {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0)
    (t : ℂ) (ht : q.eval₂ (principalCoordinatePoint V H z hz hzH) t = 0) :
    ∃ (Q : Ideal (AdjoinRoot q)) (hQprime : Q.IsPrime),
      Q ∈ minimalPrimes (AdjoinRoot q) ∧
        joinPoints z (fun i => AdjoinRoot.liftAlgHom q
          (principalCoordinatePoint V H z hz hzH) t ht (v i)) ∈
          (@rootGraphVariety n e V H q v Q hQprime).points := by
  let g := AdjoinRoot.liftAlgHom q (principalCoordinatePoint V H z hz hzH) t ht
  letI : (RingHom.ker g.toRingHom).IsPrime := RingHom.ker_isPrime g.toRingHom
  obtain ⟨Q, hQ, hQg⟩ := Ideal.exists_minimalPrimes_le
    (show (⊥ : Ideal (AdjoinRoot q)) ≤ RingHom.ker g.toRingHom from bot_le)
  letI : Q.IsPrime := hQ.isPrime
  refine ⟨Q, inferInstance, hQ, rootGraphVariety_point_of_hom V H q v Q z g ?_ hQg⟩
  intro f
  simp only [g, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]
  exact principalCoordinatePoint_map V H z hz hzH f

theorem kernelGraphVariety_coordinate_eq {m : ℕ} {T : Type} [CommRing T]
    [IsDomain T] [Algebra ℂ T] (φ : Poly m →ₐ[ℂ] T) (i : Fin m) (c : ℂ)
    (hφ : φ (MvPolynomial.X i) = algebraMap ℂ T c)
    (w : Point m) (hw : w ∈ (kernelGraphVariety φ).points) : w i = c := by
  have hf : MvPolynomial.X i - MvPolynomial.C c ∈ (kernelGraphVariety φ).ideal := by
    change φ (MvPolynomial.X i - MvPolynomial.C c) = 0
    rw [map_sub, hφ, MvPolynomial.algHom_C, sub_self]
  have heval := hw _ hf
  simpa only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero,
    Algebra.algebraMap_self, RingHom.id_apply] using heval

theorem rootGraphVariety_normalized {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Q : Ideal (AdjoinRoot q)) [Q.IsPrime] (a : Fin e) (hva : v a = 1)
    (w : Point (n + e)) (hw : w ∈ (rootGraphVariety V H q v Q).points) :
    secondPoint w a = 1 := by
  exact kernelGraphVariety_coordinate_eq (rootGraphMap V H q v Q) (Fin.natAdd n a) 1
    (by simp [rootGraphMap, hva]) w hw

theorem rootGraphVariety_point_containment {n e : ℕ} (V : AffineVariety n)
    [V.ideal.IsPrime] (H : Poly n) (hH : H ∉ V.ideal)
    (q : Polynomial (PrincipalCoordinateRing V H)) (hq : q.Monic)
    (v : Fin e → AdjoinRoot q) (Q : Ideal (AdjoinRoot q)) [Q.IsPrime]
    (w : Point (n + e)) (hw : w ∈ (rootGraphVariety V H q v Q).points) :
    firstPoint w ∈ V.points := by
  intro f hf
  have hmap : principalCoordinateMap V H f = 0 := by
    change f ∈ RingHom.ker (principalCoordinateMap V H).toRingHom
    rwa [principalCoordinateMap_ker V H hH]
  have hf' : MvPolynomial.rename (Fin.castAdd e) f ∈ (rootGraphVariety V H q v Q).ideal := by
    change rootGraphMap V H q v Q (MvPolynomial.rename (Fin.castAdd e) f) = 0
    rw [rootGraphMap_base, hmap, map_zero]
  have h := hw _ hf'
  rw [MvPolynomial.aeval_rename] at h
  exact h

/-- Independent common equations separate the members of a pure finite
family at each point of the Jacobian open. -/
theorem pure_family_unique_at_minor {m k : ℕ} (F : AffineFamily.Family m)
    (hk : k ≤ m) (hF : AffineFamily.IsPure F k) (E : List (Poly m))
    (hE : ∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal)
    (x : Point m) (hx : x ∈ (AffineFamily.locus F).points)
    (hm : ∃ M ∈ TrackA.jacobianMinors E (m - k), MvPolynomial.eval x M ≠ 0) :
    ∀ Γ ∈ F, ∀ Δ ∈ F, x ∈ Γ.points → x ∈ Δ.points → Γ = Δ := by
  exact (TrackA.request_pure_family_jacobian_germ F k hk hF E hE x hx hm).2.2.2

/-- A finite family of dominant incidences with mutually disjoint fibers
contains at most as many members as the common fiber has points. -/
theorem dominant_family_card_le_fiber {n e N : ℕ}
    (F : Finset (AffineVariety (n + e))) (z : Point n) (T : Set (Point e))
    (hT : T.Finite) (hN : T.ncard ≤ N)
    (hdominant : ∀ Γ ∈ F, ∃ v, joinPoints z v ∈ Γ.points)
    (hcontained : ∀ Γ ∈ F, ∀ v, joinPoints z v ∈ Γ.points → v ∈ T)
    (hunique : ∀ Γ ∈ F, ∀ Δ ∈ F, ∀ v,
      joinPoints z v ∈ Γ.points → joinPoints z v ∈ Δ.points → Γ = Δ) : F.card ≤ N := by
  classical
  choose d hd using fun Γ : F => hdominant Γ.val Γ.property
  have hdinj : Function.Injective d := by
    intro Γ Δ hEq
    apply Subtype.ext
    apply hunique Γ.val Γ.property Δ.val Δ.property (d Γ) (hd Γ)
    rw [hEq]
    exact hd Δ
  have hsubset : Set.range d ⊆ T := by
    rintro v ⟨Γ, rfl⟩
    exact hcontained Γ.val Γ.property (d Γ) (hd Γ)
  have hcard : F.card = (Set.range d).ncard := by
    rw [Set.ncard_range_of_injective hdinj, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcard]
  exact (Set.ncard_le_ncard hsubset hT).trans hN

def rootGraphFamily {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q) :
    AffineFamily.Family (n + e) :=
  let F := (Ideal.finite_minimalPrimes_of_isNoetherianRing (AdjoinRoot q) ⊥).toFinset
  F.attach.image fun Q => @rootGraphVariety n e V H q v Q.val
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing (AdjoinRoot q) ⊥).mem_toFinset.mp
      Q.property).isPrime

theorem mem_rootGraphFamily {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Γ : AffineVariety (n + e)) :
    Γ ∈ rootGraphFamily V H q v ↔
      ∃ (Q : Ideal (AdjoinRoot q)) (hQprime : Q.IsPrime),
        Q ∈ minimalPrimes (AdjoinRoot q) ∧ Γ = @rootGraphVariety n e V H q v Q hQprime := by
  classical
  let hf := Ideal.finite_minimalPrimes_of_isNoetherianRing (AdjoinRoot q) (⊥ : Ideal (AdjoinRoot q))
  constructor
  · intro hΓ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hΓ
    have hQmin := hf.mem_toFinset.mp Q.property
    exact ⟨Q.val, hQmin.isPrime, hQmin, rfl⟩
  · rintro ⟨Q, hQprime, hQmin, rfl⟩
    refine Finset.mem_image.mpr ⟨⟨Q, hf.mem_toFinset.mpr hQmin⟩, Finset.mem_attach _ _, ?_⟩
    rfl

theorem rootGraphFamily_pure {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal)
    (q : Polynomial (PrincipalCoordinateRing V H)) (hq : q.Monic)
    (v : Fin e → AdjoinRoot q) : AffineFamily.IsPure (rootGraphFamily V H q v) V.dimension := by
  intro Γ hΓ
  obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
  letI : Q.IsPrime := hQprime
  exact ⟨kernelGraphVariety_irreducible (rootGraphMap V H q v Q),
    rootGraphVariety_dimension V H hH q hq v Q hQ⟩

theorem rootGraphFamily_dominant {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal)
    (q : Polynomial (PrincipalCoordinateRing V H)) (hq : q.Monic)
    (v : Fin e → AdjoinRoot q) (z : Point n) (hz : z ∈ V.points)
    (hzH : MvPolynomial.eval z H ≠ 0) :
    ∀ Γ ∈ rootGraphFamily V H q v, ∃ d, joinPoints z d ∈ Γ.points := by
  intro Γ hΓ
  obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
  letI : Q.IsPrime := hQprime
  exact rootGraphVariety_dominant V H hH q hq v Q hQ z hz hzH

theorem rootGraphFamily_root_coverage {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0)
    (t : ℂ) (ht : q.eval₂ (principalCoordinatePoint V H z hz hzH) t = 0) :
    ∃ Γ ∈ rootGraphFamily V H q v,
      joinPoints z (fun i => AdjoinRoot.liftAlgHom q
        (principalCoordinatePoint V H z hz hzH) t ht (v i)) ∈ Γ.points := by
  obtain ⟨Q, hQprime, hQ, hp⟩ := rootGraphVariety_root_coverage V H q v z hz hzH t ht
  letI : Q.IsPrime := hQprime
  refine ⟨rootGraphVariety V H q v Q, ?_, hp⟩
  exact (mem_rootGraphFamily V H q v _).mpr ⟨Q, hQprime, hQ, rfl⟩

theorem rootGraphVariety_section_nonzero {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal)
    (q : Polynomial (PrincipalCoordinateRing V H)) (hq : q.Monic)
    (v : Fin e → AdjoinRoot q) (Q : Ideal (AdjoinRoot q)) [Q.IsPrime]
    (hQ : Q ∈ minimalPrimes (AdjoinRoot q)) :
    MvPolynomial.rename (Fin.castAdd e) H ∉ (rootGraphVariety V H q v Q).ideal := by
  letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
  have hinj := quotient_algebraMap_injective_of_under_eq_bot Q
    (monic_root_minimal_prime_under_eq_bot q hq Q hQ)
  intro hmem
  change rootGraphMap V H q v Q (MvPolynomial.rename (Fin.castAdd e) H) = 0 at hmem
  rw [rootGraphMap_base, ← map_zero (algebraMap (PrincipalCoordinateRing V H)
    (AdjoinRoot q ⧸ Q)), hinj.eq_iff] at hmem
  have hHmem : H ∈ RingHom.ker (principalCoordinateMap V H).toRingHom := hmem
  rw [principalCoordinateMap_ker V H hH] at hHmem
  exact hH hHmem

theorem map_ring_inverse_of_isUnit {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (hr : IsUnit r) :
    f (Ring.inverse r) = Ring.inverse (f r) := by
  apply (hr.map f).mul_left_cancel
  rw [← map_mul, Ring.mul_inverse_cancel r hr, map_one,
    Ring.mul_inverse_cancel (f r) (hr.map f)]

def principalCarrierMap {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) : PrincipalCoordinateRing V H →ₐ[ℂ] CarrierField V :=
  IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk V.ideal H)
    (f := IsScalarTower.toAlgHom ℂ (Poly n ⧸ V.ideal) (CarrierField V))
    (isUnit_iff_ne_zero.mpr (by
      intro h
      exact hH ((coordinateMap_eq_zero_iff V H).mp h)))

theorem principalCarrierMap_apply {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (f : Poly n) :
    principalCarrierMap V H hH (principalCoordinateMap V H f) = coordinateMap V f := by
  simp only [principalCarrierMap, principalCoordinateMap, AlgHom.comp_apply,
    IsScalarTower.toAlgHom_apply, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

theorem principalCarrierMap_injective {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) : Function.Injective (principalCarrierMap V H hH) := by
  have hlocal := IsLocalization.injective (PrincipalCoordinateRing V H)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (show Ideal.Quotient.mk V.ideal H ≠ 0 from
        fun h => hH (Ideal.Quotient.eq_zero_iff_mem.mp h)))
  have hfrac := IsFractionRing.injective (Poly n ⧸ V.ideal) (CarrierField V)
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Ideal.Quotient.mk V.ideal H))
    (principalCarrierMap V H hH).toRingHom).mpr
  intro x y
  simp only [principalCarrierMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
    IsScalarTower.toAlgHom_apply]
  exact hlocal.eq_iff.trans hfrac.eq_iff.symm

theorem principalCoordinateMap_isUnit_of_dvd {n : ℕ} (V : AffineVariety n)
    (H δ : Poly n) (hδ : δ ∣ H) : IsUnit (principalCoordinateMap V H δ) := by
  exact IsLocalization.Away.isUnit_of_dvd (S := PrincipalCoordinateRing V H)
    (Ideal.Quotient.mk V.ideal H) (map_dvd (Ideal.Quotient.mk V.ideal) hδ)

namespace ParameterFraction

def localPolynomial {n D : ℕ} {V : AffineVariety n} (F : ParameterFraction V D) (H : Poly n) :
    Polynomial (PrincipalCoordinateRing V H) :=
  F.numerator.map (principalCoordinateMap V H).toRingHom *
    Polynomial.C (Ring.inverse (principalCoordinateMap V H F.denominator))

theorem map_localPolynomial {n D : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]
    (F : ParameterFraction V D) (H : Poly n) (hH : H ∉ V.ideal)
    (hden : F.denominator ∣ H) :
    (F.localPolynomial H).map (principalCarrierMap V H hH).toRingHom = F.value := by
  have hunit := principalCoordinateMap_isUnit_of_dvd V H F.denominator hden
  have hcomp : (principalCarrierMap V H hH).toRingHom.comp
      (principalCoordinateMap V H).toRingHom = coordinateMap V :=
    RingHom.ext (principalCarrierMap_apply V H hH)
  have hinv : principalCarrierMap V H hH (Ring.inverse (principalCoordinateMap V H F.denominator)) =
      (coordinateMap V F.denominator)⁻¹ := by
    have hi := map_ring_inverse_of_isUnit (principalCarrierMap V H hH).toRingHom _ hunit
    change principalCarrierMap V H hH (Ring.inverse (principalCoordinateMap V H F.denominator)) =
      Ring.inverse (principalCarrierMap V H hH (principalCoordinateMap V H F.denominator)) at hi
    rwa [principalCarrierMap_apply, Ring.inverse_eq_inv] at hi
  rw [localPolynomial, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, hcomp]
  change F.numerator.map (coordinateMap V) *
    Polynomial.C (principalCarrierMap V H hH (Ring.inverse (principalCoordinateMap V H F.denominator))) = F.value
  rw [hinv]
  rfl

theorem localPolynomial_monic {n D : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]
    (F : ParameterFraction V D) (H : Poly n) (hH : H ∉ V.ideal)
    (hden : F.denominator ∣ H) (hm : F.value.Monic) : (F.localPolynomial H).Monic := by
  apply Polynomial.monic_of_injective (principalCarrierMap_injective V H hH)
  rwa [F.map_localPolynomial H hH hden]

theorem localPolynomial_degree {n D : ℕ} {V : AffineVariety n} [V.ideal.IsPrime]
    (F : ParameterFraction V D) (H : Poly n) (hH : H ∉ V.ideal)
    (hden : F.denominator ∣ H) : (F.localPolynomial H).natDegree = F.value.natDegree := by
  rw [← F.map_localPolynomial H hH hden]
  exact (Polynomial.natDegree_map_eq_of_injective (principalCarrierMap_injective V H hH) _).symm

theorem localPolynomial_point {n D : ℕ} {V : AffineVariety n}
    (F : ParameterFraction V D) (H : Poly n) (hden : F.denominator ∣ H)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0) :
    (F.localPolynomial H).map (principalCoordinatePoint V H z hz hzH).toRingHom =
      F.numerator.map (MvPolynomial.aeval z).toRingHom *
        Polynomial.C (MvPolynomial.aeval z F.denominator)⁻¹ := by
  have hunit := principalCoordinateMap_isUnit_of_dvd V H F.denominator hden
  have hcomp : (principalCoordinatePoint V H z hz hzH).toRingHom.comp
      (principalCoordinateMap V H).toRingHom = (MvPolynomial.aeval z).toRingHom :=
    RingHom.ext (principalCoordinatePoint_map V H z hz hzH)
  have hinv : principalCoordinatePoint V H z hz hzH (Ring.inverse (principalCoordinateMap V H F.denominator)) =
      (MvPolynomial.aeval z F.denominator)⁻¹ := by
    have hi := map_ring_inverse_of_isUnit (principalCoordinatePoint V H z hz hzH).toRingHom _ hunit
    change principalCoordinatePoint V H z hz hzH (Ring.inverse (principalCoordinateMap V H F.denominator)) =
      Ring.inverse (principalCoordinatePoint V H z hz hzH (principalCoordinateMap V H F.denominator)) at hi
    rwa [principalCoordinatePoint_map, Ring.inverse_eq_inv] at hi
  rw [localPolynomial, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, hcomp]
  change F.numerator.map (MvPolynomial.aeval z).toRingHom *
    Polynomial.C (principalCoordinatePoint V H z hz hzH (Ring.inverse (principalCoordinateMap V H F.denominator))) = _
  rw [hinv]

end ParameterFraction

def rootEquationPolynomial {n e : ℕ} (R : Polynomial (Poly n)) (b : Fin e) : Poly (n + e) :=
  R.eval₂ (MvPolynomial.rename (Fin.castAdd e)).toRingHom (MvPolynomial.X (Fin.natAdd n b))

theorem eval_rootEquationPolynomial {n e : ℕ} (R : Polynomial (Poly n)) (b : Fin e)
    (w : Point (n + e)) :
    MvPolynomial.aeval w (rootEquationPolynomial R b) =
      R.eval₂ (MvPolynomial.aeval (firstPoint w)).toRingHom (secondPoint w b) := by
  change (MvPolynomial.aeval w).toRingHom (rootEquationPolynomial R b) = _
  rw [rootEquationPolynomial, Polynomial.hom_eval₂]
  have hcomp : (MvPolynomial.aeval (R := ℂ) w).toRingHom.comp
      (MvPolynomial.rename (R := ℂ) (Fin.castAdd e)).toRingHom =
      (MvPolynomial.aeval (R := ℂ) (firstPoint w)).toRingHom := by
    apply RingHom.ext
    intro f
    change MvPolynomial.aeval w (MvPolynomial.rename (Fin.castAdd e) f) =
      MvPolynomial.aeval (firstPoint w) f
    exact MvPolynomial.aeval_rename (Fin.castAdd e) w f
  rw [hcomp]
  have hcoord : (MvPolynomial.aeval (R := ℂ) w).toRingHom (MvPolynomial.X (Fin.natAdd n b)) = secondPoint w b := by
    change MvPolynomial.aeval w (MvPolynomial.X (Fin.natAdd n b)) = _
    rw [MvPolynomial.aeval_X]
    rfl
  rw [hcoord]

theorem rootGraphVariety_root_condition {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Q : Ideal (AdjoinRoot q)) [Q.IsPrime] (R : Polynomial (Poly n)) (b : Fin e)
    (hR : R.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
      (principalCoordinateMap V H).toRingHom) (v b) = 0)
    (w : Point (n + e)) (hw : w ∈ (rootGraphVariety V H q v Q).points) :
    R.eval₂ (MvPolynomial.aeval (firstPoint w)).toRingHom (secondPoint w b) = 0 := by
  have hcomp : (rootGraphMap V H q v Q).toRingHom.comp
      (MvPolynomial.rename (Fin.castAdd e)).toRingHom =
      (Ideal.Quotient.mk Q).comp ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
        (principalCoordinateMap V H).toRingHom) := by
    apply RingHom.ext
    intro f
    change rootGraphMap V H q v Q (MvPolynomial.rename (Fin.castAdd e) f) = _
    rw [rootGraphMap_base]
    rfl
  have hmem : rootEquationPolynomial R b ∈ (rootGraphVariety V H q v Q).ideal := by
    change (rootGraphMap V H q v Q).toRingHom (rootEquationPolynomial R b) = 0
    rw [rootEquationPolynomial, Polynomial.hom_eval₂, hcomp]
    have hcoord : (rootGraphMap V H q v Q).toRingHom (MvPolynomial.X (Fin.natAdd n b)) =
        Ideal.Quotient.mk Q (v b) := by
      change MvPolynomial.aeval _ (MvPolynomial.X (Fin.natAdd n b)) = _
      rw [MvPolynomial.aeval_X]
      simp only [Fin.addCases_right]
    rw [hcoord]
    rw [← Polynomial.hom_eval₂, hR, map_zero]
  have hx := hw _ hmem
  rwa [eval_rootEquationPolynomial] at hx

def graphEquationPolynomial {n e : ℕ} (δ B A : Poly n) (b i : Fin e) : Poly (n + e) :=
  MvPolynomial.rename (Fin.castAdd e) δ * MvPolynomial.X (Fin.natAdd n i) -
    MvPolynomial.rename (Fin.castAdd e) B -
      MvPolynomial.rename (Fin.castAdd e) A * MvPolynomial.X (Fin.natAdd n b)

theorem rootGraphVariety_graph_coordinate {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Q : Ideal (AdjoinRoot q)) [Q.IsPrime] (δ B A : Poly n) (b i : Fin e)
    (hv : algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (principalCoordinateMap V H δ) * v i =
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H B) +
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H A) * v b)
    (w : Point (n + e)) (hw : w ∈ (rootGraphVariety V H q v Q).points) :
    MvPolynomial.aeval (firstPoint w) δ * secondPoint w i =
      MvPolynomial.aeval (firstPoint w) B +
        MvPolynomial.aeval (firstPoint w) A * secondPoint w b := by
  have hmem : graphEquationPolynomial δ B A b i ∈ (rootGraphVariety V H q v Q).ideal := by
    change rootGraphMap V H q v Q (graphEquationPolynomial δ B A b i) = 0
    have h := congrArg (Ideal.Quotient.mk Q) hv
    simp only [map_mul, map_add, Ideal.Quotient.mk_algebraMap] at h
    simp only [graphEquationPolynomial, map_sub, map_mul]
    simp only [rootGraphMap_base]
    simp only [rootGraphMap, MvPolynomial.aeval_X, Fin.addCases_right]
    linear_combination h
  have h := hw _ hmem
  simp only [graphEquationPolynomial, map_sub, map_mul, MvPolynomial.aeval_rename,
    MvPolynomial.aeval_X] at h
  change MvPolynomial.aeval (firstPoint w) δ * secondPoint w i -
    MvPolynomial.aeval (firstPoint w) B -
      MvPolynomial.aeval (firstPoint w) A * secondPoint w b = 0 at h
  linear_combination h

theorem graph_root_fiber_bound {n e : ℕ} (Γ : AffineVariety (n + e))
    (z : Point n) (δ : ℂ) (hδ : δ ≠ 0) (B A : Fin e → ℂ) (b : Fin e)
    (r : Polynomial ℂ) (hr : r ≠ 0)
    (hgraph : ∀ d, joinPoints z d ∈ Γ.points → ∀ i,
      δ * d i = B i + A i * d b)
    (hroot : ∀ d, joinPoints z d ∈ Γ.points → r.eval (d b) = 0) :
    {d : Point e | joinPoints z d ∈ Γ.points}.Finite ∧
      {d : Point e | joinPoints z d ∈ Γ.points}.ncard ≤ r.natDegree := by
  let F := {d : Point e | joinPoints z d ∈ Γ.points}
  let f : Point e → ℂ := fun d => d b
  have hfin := (complex_root_fiber r hr).1
  have hsubset : f '' F ⊆ {t : ℂ | r.eval t = 0} := by
    rintro t ⟨d, hd, rfl⟩
    exact hroot d hd
  have hinj : Set.InjOn f F := by
    intro d hd d' hd' heq
    funext i
    apply mul_left_cancel₀ hδ
    rw [hgraph d hd i, hgraph d' hd' i, show d b = d' b from heq]
  refine ⟨(hfin.subset hsubset).of_finite_image hinj, ?_⟩
  have hcard := (Set.ncard_le_ncard hsubset hfin).trans (complex_root_fiber r hr).2.1
  rwa [hinj.ncard_image] at hcard

theorem localPolynomial_root_relation {n D : ℕ} {V : AffineVariety n}
    (F : ParameterFraction V D) (H : Poly n) (hden : F.denominator ∣ H) :
    F.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H)
      (AdjoinRoot (F.localPolynomial H))).comp (principalCoordinateMap V H).toRingHom)
        (AdjoinRoot.root (F.localPolynomial H)) = 0 := by
  have hunit := principalCoordinateMap_isUnit_of_dvd V H F.denominator hden
  have hroot := AdjoinRoot.eval₂_root (F.localPolynomial H)
  rw [← AdjoinRoot.algebraMap_eq, ParameterFraction.localPolynomial, Polynomial.eval₂_mul,
    Polynomial.eval₂_map, Polynomial.eval₂_C] at hroot
  exact (IsUnit.mul_left_eq_zero
    (hunit.ringInverse.map (algebraMap (PrincipalCoordinateRing V H)
      (AdjoinRoot (F.localPolynomial H))))).mp hroot

def affineRootDirection {n e : ℕ} (V : AffineVariety n) (H δ : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (B A : Fin e → Poly n) : Fin e → AdjoinRoot q :=
  fun i => algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
      (principalCoordinateMap V H (B i) * Ring.inverse (principalCoordinateMap V H δ)) +
    algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
      (principalCoordinateMap V H (A i) * Ring.inverse (principalCoordinateMap V H δ)) * AdjoinRoot.root q

theorem affineRootDirection_cleared {n e : ℕ} (V : AffineVariety n) (H δ : Poly n)
    (hδ : δ ∣ H) (q : Polynomial (PrincipalCoordinateRing V H)) (B A : Fin e → Poly n) (i : Fin e) :
    algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H δ) *
      affineRootDirection V H δ q B A i =
    algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (B i)) +
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (A i)) *
        AdjoinRoot.root q := by
  have hunit := principalCoordinateMap_isUnit_of_dvd V H δ hδ
  have hcancel : algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
      (principalCoordinateMap V H δ) * algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (Ring.inverse (principalCoordinateMap V H δ)) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hunit, map_one]
  dsimp only [affineRootDirection]
  simp only [map_mul]
  calc
    _ = algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (B i)) *
          (algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H δ) *
            algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (Ring.inverse (principalCoordinateMap V H δ))) +
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (A i)) *
          (algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H δ) *
            algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (Ring.inverse (principalCoordinateMap V H δ))) *
          AdjoinRoot.root q := by ring
    _ = _ := by rw [hcancel]; ring

theorem affineRootDirection_root_coordinate {n e : ℕ} (V : AffineVariety n) (H δ : Poly n)
    (hδ : δ ∣ H) (q : Polynomial (PrincipalCoordinateRing V H)) (B A : Fin e → Poly n)
    (b : Fin e) (hB : B b = 0) (hA : A b = δ) :
    affineRootDirection V H δ q B A b = AdjoinRoot.root q := by
  have hunit := principalCoordinateMap_isUnit_of_dvd V H δ hδ
  simp only [affineRootDirection, hB, hA, map_zero, zero_mul, zero_add,
    Ring.mul_inverse_cancel _ hunit, map_one, one_mul]

theorem affineRootDirection_normalized {n e : ℕ} (V : AffineVariety n) (H δ : Poly n)
    (hδ : δ ∣ H) (q : Polynomial (PrincipalCoordinateRing V H)) (B A : Fin e → Poly n)
    (a : Fin e) (hB : B a = δ) (hA : A a = 0) : affineRootDirection V H δ q B A a = 1 := by
  have hunit := principalCoordinateMap_isUnit_of_dvd V H δ hδ
  simp only [affineRootDirection, hB, hA, map_zero, zero_mul, add_zero,
    Ring.mul_inverse_cancel _ hunit, map_one]

/-- The actual prime-kernel root graph has uniformly finite fibers; the free
normalized coordinate injects each fiber into the roots of the cleared equation. -/
theorem affine_root_graph_finite_fiber {n e D : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (F : ParameterFraction V D) (H δ : Poly n) (hFden : F.denominator ∣ H) (hδ : δ ∣ H)
    (B A : Fin e → Poly n) (b : Fin e) (hB : B b = 0) (hA : A b = δ)
    (Q : Ideal (AdjoinRoot (F.localPolynomial H))) [Q.IsPrime]
    (z : Point n) (hδz : MvPolynomial.aeval z δ ≠ 0)
    (hFz : F.numerator.map (MvPolynomial.aeval z).toRingHom ≠ 0) :
    let v := affineRootDirection V H δ (F.localPolynomial H) B A
    let Γ := rootGraphVariety V H (F.localPolynomial H) v Q
    {d : Point e | joinPoints z d ∈ Γ.points}.Finite ∧
      {d : Point e | joinPoints z d ∈ Γ.points}.ncard ≤
        (F.numerator.map (MvPolynomial.aeval z).toRingHom).natDegree := by
  let q := F.localPolynomial H
  let v := affineRootDirection V H δ q B A
  let Γ := rootGraphVariety V H q v Q
  have hvb : v b = AdjoinRoot.root q := affineRootDirection_root_coordinate V H δ hδ q B A b hB hA
  apply graph_root_fiber_bound Γ z (MvPolynomial.aeval z δ) hδz
    (fun i => MvPolynomial.aeval z (B i)) (fun i => MvPolynomial.aeval z (A i)) b
    (F.numerator.map (MvPolynomial.aeval z).toRingHom) hFz
  · intro d hd i
    have hv := affineRootDirection_cleared V H δ hδ q B A i
    rw [← hvb] at hv
    have h := rootGraphVariety_graph_coordinate V H q v Q δ (B i) (A i) b i hv (joinPoints z d) hd
    have hfirst : firstPoint (joinPoints z d) = z := by ext j; simp [firstPoint, joinPoints]
    rw [hfirst] at h
    simpa [secondPoint, joinPoints] using h
  · intro d hd
    have hroot : F.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
        (principalCoordinateMap V H).toRingHom) (v b) = 0 := by
      rw [hvb]
      exact localPolynomial_root_relation F H hFden
    have h := rootGraphVariety_root_condition V H q v Q F.numerator b hroot (joinPoints z d) hd
    have hfirst : firstPoint (joinPoints z d) = z := by ext j; simp [firstPoint, joinPoints]
    rw [hfirst] at h
    simpa [Polynomial.eval_map, secondPoint, joinPoints] using h

def basePointProjection (n e : ℕ) : Point (n + e) →ₗ[ℂ] Point n where
  toFun := firstPoint
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem differential_base_rename {n e : ℕ} (f : Poly n) (w d : Point (n + e)) :
    differential (MvPolynomial.rename (Fin.castAdd e) f) w d =
      differential f (firstPoint w) (firstPoint d) := by
  have hline : polynomialLine w d (MvPolynomial.rename (Fin.castAdd e) f) =
      polynomialLine (firstPoint w) (firstPoint d) f := by
    have hhom : (polynomialLine w d).comp (MvPolynomial.rename (Fin.castAdd e)) =
        polynomialLine (firstPoint w) (firstPoint d) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.rename_X, polynomialLine,
        MvPolynomial.aeval_X]
      rfl
    exact DFunLike.congr_fun hhom f
  rw [← polynomialLine_derivative_zero, hline, polynomialLine_derivative_zero]

theorem differential_add_apply {n : ℕ} (f g : Poly n) (x d : Point n) :
    differential (f + g) x d = differential f x d + differential g x d := by
  simp [differential_apply_sum, map_add, add_mul, Finset.sum_add_distrib]

theorem differential_sub_apply {n : ℕ} (f g : Poly n) (x d : Point n) :
    differential (f - g) x d = differential f x d - differential g x d := by
  simp [differential_apply_sum, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem differential_graphEquation_vertical {n e : ℕ} (δ B A : Poly n)
    (b i : Fin e) (w d : Point (n + e)) (hd : firstPoint d = 0) :
    differential (graphEquationPolynomial δ B A b i) w d =
      MvPolynomial.aeval (firstPoint w) δ * secondPoint d i -
        MvPolynomial.aeval (firstPoint w) A * secondPoint d b := by
  simp only [graphEquationPolynomial, differential_sub_apply, differential_mul_apply,
    differential_base_rename, hd, map_zero, mul_zero, add_zero, differential_X_apply,
    MvPolynomial.aeval_rename]
  change MvPolynomial.aeval (firstPoint w) δ * secondPoint d i - 0 -
    MvPolynomial.aeval (firstPoint w) A * secondPoint d b = _
  ring

theorem differential_rootEquation_vertical {n e : ℕ} (R : Polynomial (Poly n))
    (b : Fin e) (w d : Point (n + e)) (hd : firstPoint d = 0) :
    differential (rootEquationPolynomial R b) w d =
      R.derivative.eval₂ (MvPolynomial.aeval (firstPoint w)).toRingHom (secondPoint w b) *
        secondPoint d b := by
  induction R using Polynomial.induction_on with
  | C f =>
    simp only [rootEquationPolynomial, Polynomial.eval₂_C,
      Polynomial.derivative_C, Polynomial.eval₂_zero, zero_mul]
    change differential (MvPolynomial.rename (Fin.castAdd e) f) w d = 0
    rw [differential_base_rename, hd, map_zero]
  | add R S hR hS =>
    simp only [rootEquationPolynomial, Polynomial.eval₂_add] at *
    rw [differential_add_apply, hR, hS, Polynomial.derivative_add,
      Polynomial.eval₂_add, add_mul]
  | monomial k f ih =>
    have hstep : Polynomial.C f * Polynomial.X ^ (k + 1) =
        (Polynomial.C f * Polynomial.X ^ k) * Polynomial.X := by rw [pow_succ, mul_assoc]
    rw [hstep]
    have heq : rootEquationPolynomial ((Polynomial.C f * Polynomial.X ^ k) * Polynomial.X) b =
        rootEquationPolynomial (Polynomial.C f * Polynomial.X ^ k) b *
          MvPolynomial.X (Fin.natAdd n b) := by
      simp only [rootEquationPolynomial, Polynomial.eval₂_mul, Polynomial.eval₂_X]
    rw [heq]
    rw [differential_mul_apply, differential_X_apply, ih, eval_rootEquationPolynomial]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, MvPolynomial.aeval_X,
      secondPoint]
    ring

theorem rootEquationPolynomial_mem_rootGraph {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Q : Ideal (AdjoinRoot q)) [Q.IsPrime] (R : Polynomial (Poly n)) (b : Fin e)
    (hR : R.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
      (principalCoordinateMap V H).toRingHom) (v b) = 0) :
    rootEquationPolynomial R b ∈ (rootGraphVariety V H q v Q).ideal := by
  rw [← AffineVariety.vanishingIdeal_points]
  intro w hw
  rw [eval_rootEquationPolynomial]
  exact rootGraphVariety_root_condition V H q v Q R b hR w hw

theorem graphEquationPolynomial_mem_rootGraph {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (Q : Ideal (AdjoinRoot q)) [Q.IsPrime] (δ B A : Poly n) (b i : Fin e)
    (hv : algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (principalCoordinateMap V H δ) * v i =
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H B) +
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H A) * v b) :
    graphEquationPolynomial δ B A b i ∈ (rootGraphVariety V H q v Q).ideal := by
  rw [← AffineVariety.vanishingIdeal_points]
  intro w hw
  have h := rootGraphVariety_graph_coordinate V H q v Q δ B A b i hv w hw
  simp only [graphEquationPolynomial, map_sub, map_mul, MvPolynomial.aeval_rename,
    MvPolynomial.aeval_X]
  change MvPolynomial.aeval (firstPoint w) δ * secondPoint w i -
    MvPolynomial.aeval (firstPoint w) B -
      MvPolynomial.aeval (firstPoint w) A * secondPoint w b = 0
  linear_combination h

theorem evaluatedJacobian_ker_iff {m : ℕ} (E : List (Poly m)) (x d : Point m) :
    d ∈ LinearMap.ker (TrackA.evaluatedJacobian E x).mulVecLin ↔
      ∀ f ∈ E, differential f x d = 0 := by
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff]
  have hget : (∀ i : Fin E.length, differential (E.get i) x d = 0) ↔
      ∀ f ∈ E, differential f x d = 0 := by
    constructor
    · intro h f hf
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hf
      exact h i
    · intro h i
      exact h _ (List.get_mem _ _)
  rw [← hget]
  simp [TrackA.evaluatedJacobian, TrackA.jacobian, Matrix.mulVec, dotProduct,
    differential, MvPolynomial.aeval_eq_eval]

/-- An equation kernel with no vertical vectors has the expected dimension;
the frozen Jacobian germ theorem then identifies the incidence tangent. -/
theorem smooth_tangent_projection_of_equation_kernel {n e : ℕ}
    (V : AffineVariety n) (Γ : AffineVariety (n + e))
    (hV : V.IsIrreducible) (hΓ : Γ.IsIrreducible)
    (hdim : Γ.dimension = V.dimension) (E : List (Poly (n + e)))
    (hlen : E.length = n + e - V.dimension) (hE : ∀ f ∈ E, f ∈ Γ.ideal)
    (w : Point (n + e)) (hw : w ∈ Γ.points) (hbase : firstPoint w ∈ V.points)
    (hsmooth : V.IsSmoothAt (firstPoint w))
    (hproj : ∀ d ∈ LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin,
      firstPoint d ∈ V.tangentSpace (firstPoint w))
    (hvertical : ∀ d ∈ LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin,
      firstPoint d = 0 → d = 0) :
    Γ.IsSmoothAt w ∧ Γ.tangentSpace w =
      LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin ∧
      (Γ.tangentSpace w).map (basePointProjection n e) =
      V.tangentSpace (firstPoint w) := by
  let A := TrackA.evaluatedJacobian E w
  let K := LinearMap.ker A.mulVecLin
  let π := basePointProjection n e
  let πK : K →ₗ[ℂ] V.tangentSpace (firstPoint w) :=
    (π.comp K.subtype).codRestrict _ (fun d => hproj d.val d.property)
  have hπK : Function.Injective πK := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro d hd
    apply Subtype.ext
    apply hvertical d.val d.property
    exact congrArg Subtype.val hd
  have hVdim : Module.finrank ℂ (V.tangentSpace (firstPoint w)) = V.dimension :=
    hsmooth.2.trans (V.localDimension_eq_dimension _ hV hbase)
  have hKdim : Module.finrank ℂ K ≤ V.dimension := by
    rw [← hVdim]
    exact LinearMap.finrank_le_finrank_of_injective hπK
  have hcodim : V.dimension ≤ n + e := by
    exact (Bridges.affine_dimension_le V).trans (Nat.le_add_right _ _)
  have hA : A.rank = n + e - V.dimension := by
    have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    change A.rank + Module.finrank ℂ K = Module.finrank ℂ (Point (n + e)) at hrn
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
    have hu := A.rank_le_height
    have hu' := hu.trans hlen.le
    omega
  obtain ⟨rows, cols, hdet⟩ := TrackA.matrix_rank_minor A hA
  let m := Matrix.det ((TrackA.jacobian E).submatrix rows cols)
  have hm : m ∈ TrackA.jacobianMinors E (n + e - V.dimension) := ⟨rows, cols, rfl⟩
  have hmw : MvPolynomial.eval w m ≠ 0 := by
    have he : (MvPolynomial.eval w).mapMatrix ((TrackA.jacobian E).submatrix rows cols) =
        A.submatrix rows cols := by ext i j; rfl
    change MvPolynomial.eval w ((TrackA.jacobian E).submatrix rows cols).det ≠ 0
    rw [(MvPolynomial.eval w).map_det, he]
    exact hdet
  have hΓsmooth := smooth_of_jacobian_minor Γ hΓ V.dimension hdim E hE m hm w hw hmw
  have htan : Γ.tangentSpace w ≤ K := by
    intro d hd
    apply (evaluatedJacobian_ker_iff E w d).mpr
    intro f hf
    rw [AffineVariety.tangentSpace, Submodule.mem_iInf] at hd
    exact hd ⟨f, hE f hf⟩
  have hmap : (Γ.tangentSpace w).map π ≤ V.tangentSpace (firstPoint w) := by
    rintro d ⟨u, hu, rfl⟩
    exact hproj u (htan hu)
  let f := π.comp (Γ.tangentSpace w).subtype
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro d hd
    exact Subtype.ext (hvertical d.val (htan d.property) hd)
  have hmapdim : Module.finrank ℂ ((Γ.tangentSpace w).map π) = V.dimension := by
    have hr := LinearMap.finrank_range_of_inj hf
    rw [LinearMap.range_comp, Submodule.range_subtype] at hr
    rw [hr, hΓsmooth.2, Γ.localDimension_eq_dimension _ hΓ hw, hdim]
  have htandim : Module.finrank ℂ (Γ.tangentSpace w) = V.dimension := by
    rw [hΓsmooth.2, Γ.localDimension_eq_dimension _ hΓ hw, hdim]
  have heq : Γ.tangentSpace w = K :=
    Submodule.eq_of_le_of_finrank_le htan (by rw [htandim]; exact hKdim)
  exact ⟨hΓsmooth, heq, Submodule.eq_of_le_of_finrank_le hmap (by rw [hmapdim, hVdim])⟩


def rootGraphEquations {n e c : ℕ} (g : Fin c → Poly n) (R : Polynomial (Poly n))
    (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e) : List (Poly (n + e)) :=
  List.ofFn (fun i => MvPolynomial.rename (Fin.castAdd e) (g i)) ++
    [rootEquationPolynomial R b] ++
      ((Finset.univ.erase b).toList.map fun i => graphEquationPolynomial δ (B i) (A i) b i)

theorem rootGraphEquations_base_mem {n e c : ℕ} (g : Fin c → Poly n)
    (R : Polynomial (Poly n)) (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e) (i : Fin c) :
    MvPolynomial.rename (Fin.castAdd e) (g i) ∈ rootGraphEquations g R δ B A b := by
  simp only [rootGraphEquations, List.mem_append, List.mem_ofFn]
  exact Or.inl (Or.inl ⟨i, rfl⟩)

theorem rootGraphEquations_root_mem {n e c : ℕ} (g : Fin c → Poly n)
    (R : Polynomial (Poly n)) (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e) :
    rootEquationPolynomial R b ∈ rootGraphEquations g R δ B A b := by
  simp [rootGraphEquations]

theorem rootGraphEquations_graph_mem {n e c : ℕ} (g : Fin c → Poly n)
    (R : Polynomial (Poly n)) (δ : Poly n) (B A : Fin e → Poly n) (b i : Fin e)
    (hi : i ≠ b) : graphEquationPolynomial δ (B i) (A i) b i ∈ rootGraphEquations g R δ B A b := by
  simp only [rootGraphEquations, List.mem_append, List.mem_map, Finset.mem_toList,
    Finset.mem_erase, Finset.mem_univ, and_true]
  exact Or.inr ⟨i, hi, rfl⟩

theorem rootGraphEquations_length {n e c : ℕ} (g : Fin c → Poly n)
    (R : Polynomial (Poly n)) (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e) :
    (rootGraphEquations g R δ B A b).length = c + e := by
  simp only [rootGraphEquations, List.length_append, List.length_ofFn, List.length_singleton,
    List.length_map, Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ b),
    Finset.card_univ, Fintype.card_fin]
  have := b.isLt
  omega

theorem root_graph_equation_kernel_vertical {n e c : ℕ} (g : Fin c → Poly n)
    (R : Polynomial (Poly n)) (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e)
    (w : Point (n + e)) (hδ : MvPolynomial.aeval (firstPoint w) δ ≠ 0)
    (hR : R.derivative.eval₂ (MvPolynomial.aeval (firstPoint w)).toRingHom (secondPoint w b) ≠ 0)
    (d : Point (n + e))
    (hd : d ∈ LinearMap.ker (TrackA.evaluatedJacobian (rootGraphEquations g R δ B A b) w).mulVecLin)
    (hbase : firstPoint d = 0) : d = 0 := by
  have hd' := (evaluatedJacobian_ker_iff _ w d).mp hd
  have hb := hd' _ (rootGraphEquations_root_mem g R δ B A b)
  rw [differential_rootEquation_vertical R b w d hbase] at hb
  have hbzero : secondPoint d b = 0 := (mul_eq_zero.mp hb).resolve_left hR
  have hsecond : secondPoint d = 0 := by
    funext i
    by_cases hi : i = b
    · simpa only [hi, Pi.zero_apply] using hbzero
    · have h := hd' _ (rootGraphEquations_graph_mem g R δ B A b i hi)
      rw [differential_graphEquation_vertical δ (B i) (A i) b i w d hbase, hbzero,
        mul_zero, sub_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hδ
  funext i
  refine Fin.addCases (fun j => congrFun hbase j) (fun j => congrFun hsecond j) i

theorem root_graph_equation_kernel_projection {n e c : ℕ}
    (V : AffineVariety n) (g : Fin c → Poly n) (R : Polynomial (Poly n))
    (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e) (w : Point (n + e))
    (htan : V.tangentSpace (firstPoint w) = ⨅ i : Fin c, LinearMap.ker (differential (g i) (firstPoint w)))
    (d : Point (n + e))
    (hd : d ∈ LinearMap.ker (TrackA.evaluatedJacobian (rootGraphEquations g R δ B A b) w).mulVecLin) :
    firstPoint d ∈ V.tangentSpace (firstPoint w) := by
  rw [htan, Submodule.mem_iInf]
  intro i
  have h := (evaluatedJacobian_ker_iff _ w d).mp hd _ (rootGraphEquations_base_mem g R δ B A b i)
  rwa [differential_base_rename] at h

theorem baseEquation_mem_rootGraph {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (q : Polynomial (PrincipalCoordinateRing V H))
    (v : Fin e → AdjoinRoot q) (Q : Ideal (AdjoinRoot q)) [Q.IsPrime]
    (f : Poly n) (hf : f ∈ V.ideal) :
    MvPolynomial.rename (Fin.castAdd e) f ∈ (rootGraphVariety V H q v Q).ideal := by
  change rootGraphMap V H q v Q (MvPolynomial.rename (Fin.castAdd e) f) = 0
  rw [rootGraphMap_base]
  have hz : principalCoordinateMap V H f = 0 := by
    change f ∈ RingHom.ker (principalCoordinateMap V H).toRingHom
    rwa [principalCoordinateMap_ker V H hH]
  rw [hz, map_zero]

theorem rootGraphEquations_mem_ideal {n e c : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (q : Polynomial (PrincipalCoordinateRing V H))
    (v : Fin e → AdjoinRoot q) (Q : Ideal (AdjoinRoot q)) [Q.IsPrime]
    (g : Fin c → Poly n) (hg : ∀ i, g i ∈ V.ideal) (R : Polynomial (Poly n))
    (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e)
    (hR : R.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
      (principalCoordinateMap V H).toRingHom) (v b) = 0)
    (hgraph : ∀ i, algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (principalCoordinateMap V H δ) * v i =
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (B i)) +
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (A i)) * v b) :
    ∀ f ∈ rootGraphEquations g R δ B A b, f ∈ (rootGraphVariety V H q v Q).ideal := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
      exact baseEquation_mem_rootGraph V H hH q v Q _ (hg i)
    · have heq := List.mem_singleton.mp hf
      subst f
      exact rootEquationPolynomial_mem_rootGraph V H q v Q R b hR
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    exact graphEquationPolynomial_mem_rootGraph V H q v Q δ (B i) (A i) b i (hgraph i)


theorem rootGraphVariety_smooth_tangent {n e c : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (hcodim : V.dimension + c = n) (H : Poly n) (hH : H ∉ V.ideal)
    (q : Polynomial (PrincipalCoordinateRing V H)) (hq : q.Monic)
    (v : Fin e → AdjoinRoot q) (Q : Ideal (AdjoinRoot q)) [Q.IsPrime]
    (hQ : Q ∈ minimalPrimes (AdjoinRoot q))
    (g : Fin c → Poly n) (hg : ∀ i, g i ∈ V.ideal) (R : Polynomial (Poly n))
    (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e)
    (hR : R.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
      (principalCoordinateMap V H).toRingHom) (v b) = 0)
    (hgraph : ∀ i, algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (principalCoordinateMap V H δ) * v i =
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (B i)) +
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (A i)) * v b)
    (w : Point (n + e)) (hw : w ∈ (rootGraphVariety V H q v Q).points)
    (hsmooth : V.IsSmoothAt (firstPoint w))
    (htan : V.tangentSpace (firstPoint w) = ⨅ i : Fin c, LinearMap.ker (differential (g i) (firstPoint w)))
    (hδ : MvPolynomial.aeval (firstPoint w) δ ≠ 0)
    (hderiv : R.derivative.eval₂ (MvPolynomial.aeval (firstPoint w)).toRingHom (secondPoint w b) ≠ 0) :
    let Γ := rootGraphVariety V H q v Q
    Γ.IsSmoothAt w ∧ Γ.tangentSpace w =
      LinearMap.ker (TrackA.evaluatedJacobian (rootGraphEquations g R δ B A b) w).mulVecLin ∧
      (Γ.tangentSpace w).map (basePointProjection n e) =
      V.tangentSpace (firstPoint w) := by
  letI : V.ideal.IsPrime := hV
  let Γ := rootGraphVariety V H q v Q
  let E := rootGraphEquations g R δ B A b
  apply smooth_tangent_projection_of_equation_kernel V Γ hV
    (kernelGraphVariety_irreducible (rootGraphMap V H q v Q))
    (rootGraphVariety_dimension V H hH q hq v Q hQ) E
  · rw [rootGraphEquations_length]
    have := b.isLt
    omega
  · exact rootGraphEquations_mem_ideal V H hH q v Q g hg R δ B A b hR hgraph
  · exact hw
  · exact rootGraphVariety_point_containment V H hH q hq v Q w hw
  · exact hsmooth
  · exact root_graph_equation_kernel_projection V g R δ B A b w htan
  · exact root_graph_equation_kernel_vertical g R δ B A b w hδ hderiv

theorem differential_rootEquation_horizontal {n e : ℕ} (R : Polynomial (Poly n))
    (b : Fin e) (w d : Point (n + e)) (hd : secondPoint d = 0) :
    differential (rootEquationPolynomial R b) w d =
      differential (R.eval (MvPolynomial.C (secondPoint w b))) (firstPoint w) (firstPoint d) := by
  have hline : polynomialLine w d (rootEquationPolynomial R b) =
      polynomialLine (firstPoint w) (firstPoint d) (R.eval (MvPolynomial.C (secondPoint w b))) := by
    apply Polynomial.funext
    intro t
    change Polynomial.aeval t (polynomialLine w d (rootEquationPolynomial R b)) =
      Polynomial.aeval t (polynomialLine (firstPoint w) (firstPoint d)
        (R.eval (MvPolynomial.C (secondPoint w b))))
    rw [eval_polynomialLine, eval_rootEquationPolynomial, eval_polynomialLine,
      eval_parameterPolynomial]
    have hfirst : firstPoint (w + t • d) = firstPoint w + t • firstPoint d := rfl
    have hsecond : secondPoint (w + t • d) = secondPoint w := by
      change secondPoint w + t • secondPoint d = secondPoint w
      rw [hd, smul_zero, add_zero]
    rw [hfirst, hsecond]
  rw [← polynomialLine_derivative_zero, hline, polynomialLine_derivative_zero]

theorem differential_graphEquation_horizontal {n e : ℕ} (δ B A : Poly n)
    (b i : Fin e) (w d : Point (n + e)) (hd : secondPoint d = 0) :
    differential (graphEquationPolynomial δ B A b i) w d =
      -differential (B + MvPolynomial.C (secondPoint w b) * A -
        MvPolynomial.C (secondPoint w i) * δ) (firstPoint w) (firstPoint d) := by
  have hcoord (j : Fin e) : d (Fin.natAdd n j) = 0 := congrFun hd j
  have hC (c : ℂ) : differential (MvPolynomial.C c : Poly n) (firstPoint w) (firstPoint d) = 0 := by
    simp [differential_apply_sum]
  simp only [graphEquationPolynomial, differential_sub_apply, differential_mul_apply,
    differential_base_rename, differential_X_apply, hcoord, mul_zero, zero_add,
    MvPolynomial.aeval_X, differential_add_apply, hC, MvPolynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, add_zero]
  change secondPoint w i * differential δ (firstPoint w) (firstPoint d) -
      differential B (firstPoint w) (firstPoint d) -
      secondPoint w b * differential A (firstPoint w) (firstPoint d) = _
  ring

def horizontalKernelPolynomial {e : ℕ} (C : SkewCoordinates e) (a i j : Fin e) :
    Fin (skewDim e + e) → Poly (skewDim e + e) :=
  Fin.addCases
    (fun m => MvPolynomial.C ((C.decode.symm (coordinateSkewPair e i j)) m) -
      MvPolynomial.X (Fin.natAdd (skewDim e) j) *
        MvPolynomial.C ((C.decode.symm (coordinateSkewPair e i a)) m) -
      MvPolynomial.X (Fin.natAdd (skewDim e) i) *
        MvPolynomial.C ((C.decode.symm (coordinateSkewPair e a j)) m))
    (fun _ => 0)

theorem eval_horizontalKernelPolynomial {e : ℕ} (C : SkewCoordinates e) (a i j : Fin e)
    (w : Point (skewDim e + e)) :
    (fun m => MvPolynomial.aeval w (horizontalKernelPolynomial C a i j m)) =
      joinPoints (C.decode.symm (normalizedKernelPair a (secondPoint w) i j)) 0 := by
  funext m
  refine Fin.addCases (fun l => ?_) (fun l => ?_) m
  · simp only [horizontalKernelPolynomial, Fin.addCases_left, map_sub, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
      joinPoints]
    let α := (LinearMap.proj l : Point (skewDim e) →ₗ[ℂ] ℂ).comp C.decode.symm.toLinearMap
    change _ = α (normalizedKernelPair a (secondPoint w) i j)
    rw [normalizedKernelPair_expansion, normal_map_sub, normal_map_sub, α.map_smul, α.map_smul]
    dsimp [α]
    rfl
  · simp [horizontalKernelPolynomial, joinPoints]

/-- Tangency on a principal open extends to an ideal-preserving derivation;
its direction coordinates are fixed, so polynomial Taylor expansion integrates it. -/
theorem horizontal_kernel_translation {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (hΓ : Γ.IsIrreducible)
    (H : Poly (skewDim e))
    (hH : MvPolynomial.rename (Fin.castAdd e) H ∉ Γ.ideal) (a i j : Fin e)
    (htan : ∀ w ∈ rulingPoints Γ H,
      joinPoints (C.decode.symm (normalizedKernelPair a (secondPoint w) i j)) 0 ∈ Γ.tangentSpace w)
    (z : Point (skewDim e)) (v : Point e) (hz : joinPoints z v ∈ Γ.points) (t : ℂ) :
    joinPoints (z + t • C.decode.symm (normalizedKernelPair a v i j)) v ∈ Γ.points := by
  let b := horizontalKernelPolynomial C a i j
  let H' := MvPolynomial.rename (Fin.castAdd e) H
  have hstable : ∀ f ∈ Γ.ideal, vectorDerivation b f ∈ Γ.ideal := by
    apply tangent_vectorDerivation_preserves_ideal Γ hΓ H' hH b
    intro w hw hwH
    rw [eval_horizontalKernelPolynomial]
    apply htan w
    refine ⟨hw, ?_⟩
    change MvPolynomial.aeval (fun l : Fin (skewDim e) => w (Fin.castAdd e l)) H ≠ 0
    convert hwH using 1 <;> simp [H', MvPolynomial.aeval_rename, firstPoint] <;> rfl
  let d := joinPoints (C.decode.symm (normalizedKernelPair a v i j)) (0 : Point e)
  have hb : ∀ s : ℂ, ∀ m,
      MvPolynomial.aeval (joinPoints z v + s • d) (b m) = d m := by
    intro s m
    have hsecond : secondPoint (joinPoints z v + s • d) = v := by
      ext l
      simp [secondPoint, joinPoints, d]
    have he := congrFun (eval_horizontalKernelPolynomial C a i j (joinPoints z v + s • d)) m
    rw [hsecond] at he
    exact he
  have h := translation_of_vectorDerivation_stable Γ b hstable (joinPoints z v) d hz hb t
  have heq : joinPoints z v + t • d =
      joinPoints (z + t • C.decode.symm (normalizedKernelPair a v i j)) v := by
    ext m
    refine Fin.addCases (fun l => ?_) (fun l => ?_) m <;> simp [joinPoints, d]
  rwa [heq] at h

def horizontalTranslationSpace {n e : ℕ} (Γ : AffineVariety (n + e)) (v : Point e) :
    Submodule ℂ (Point n) where
  carrier := {d | ∀ z, joinPoints z v ∈ Γ.points → ∀ t : ℂ, joinPoints (z + t • d) v ∈ Γ.points}
  zero_mem' := by intro z hz t; simpa using hz
  add_mem' := by
    intro d u hd hu z hz t
    have h := hu (z + t • d) (hd z hz t) t
    have heq : z + t • (d + u) = (z + t • d) + t • u := by rw [smul_add, add_assoc]
    rwa [heq]
  smul_mem' := by
    intro s d hd z hz t
    have h := hd z hz (t * s)
    simpa only [smul_smul] using h

theorem full_horizontal_kernel_translation {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (hΓ : Γ.IsIrreducible)
    (H : Poly (skewDim e)) (hH : MvPolynomial.rename (Fin.castAdd e) H ∉ Γ.ideal)
    (a : Fin e)
    (htan : ∀ w ∈ rulingPoints Γ H, ∀ i j : Fin e,
      joinPoints (C.decode.symm (normalizedKernelPair a (secondPoint w) i j)) 0 ∈ Γ.tangentSpace w)
    (v : Point e) (hva : v a = 1) (d : Point (skewDim e))
    (hd : alternatingEvaluation v (C.decode d) = 0) :
    d ∈ horizontalTranslationSpace Γ v := by
  have hspan : LinearMap.ker (alternatingEvaluation v) ≤
      (horizontalTranslationSpace Γ v).comap C.decode.symm.toLinearMap := by
    rw [normalized_skew_kernel_span a v hva]
    apply Submodule.span_le.mpr
    rintro D ⟨⟨i,j⟩, rfl⟩
    intro z hz t
    exact horizontal_kernel_translation C Γ hΓ H hH a i j (fun w hw => htan w hw i j) z v hz t
  have h := hspan (show C.decode d ∈ LinearMap.ker (alternatingEvaluation v) from hd)
  change C.decode.symm (C.decode d) ∈ horizontalTranslationSpace Γ v at h
  simpa using h


theorem evaluationFlat_graphParameter_iff {e : ℕ} (C : SkewCoordinates e)
    (z y : Point (skewDim e)) (v : Point e) (hv : v ≠ 0) :
    y ∈ evaluationFlat C (graphParameter C z v hv) ↔
      alternatingEvaluation v (C.decode y) = alternatingEvaluation v (C.decode z) := by
  obtain ⟨s, hs⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (graphVector C z v) (graphVector_ne_zero C z v hv)
  have hfirst : firstPoint (graphParameter C z v hv).rep = (s : ℂ) • v := by
    rw [graphParameter, ← hs]
    ext i
    simp only [firstPoint, graphVector, joinPoints, Units.smul_def, Pi.smul_apply,
      Fin.addCases_left, smul_eq_mul]
  have hsecond : secondPoint (graphParameter C z v hv).rep =
      pointOfCovector ((s : ℂ) • alternatingEvaluation v (C.decode z)) := by
    rw [graphParameter, ← hs]
    ext i
    simp only [secondPoint, graphVector, joinPoints, Units.smul_def, Pi.smul_apply,
      Fin.addCases_right, pointOfCovector, alternatingEvaluation, LinearMap.smul_apply,
      smul_eq_mul]
    rfl
  change (C.decode y).val (firstPoint (graphParameter C z v hv).rep) =
    covectorOfPoint (secondPoint (graphParameter C z v hv).rep) ↔ _
  rw [hfirst, hsecond, covector_point_inverse, map_smul]
  change (s : ℂ) • alternatingEvaluation v (C.decode y) =
    (s : ℂ) • alternatingEvaluation v (C.decode z) ↔ _
  constructor
  · intro h
    have h' := congrArg (fun u : Module.Dual ℂ (Point e) => ((s : ℂ)⁻¹) • u) h
    simpa only [smul_smul, inv_mul_cancel₀ (Units.ne_zero s), one_smul] using h'
  · intro h
    rw [h]

theorem graphParameter_eq_of_evaluation_eq {e : ℕ} (C : SkewCoordinates e)
    (z y : Point (skewDim e)) (v : Point e) (hv : v ≠ 0)
    (h : alternatingEvaluation v (C.decode y) = alternatingEvaluation v (C.decode z)) :
    graphParameter C y v hv = graphParameter C z v hv := by
  have heq : graphVector C y v = graphVector C z v := by
    change joinPoints v (pointOfCovector (alternatingEvaluation v (C.decode y))) =
      joinPoints v (pointOfCovector (alternatingEvaluation v (C.decode z)))
    rw [h]
  unfold graphParameter
  congr 1

theorem contained_flat_of_horizontal_translations {e : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (hcontain : ∀ w ∈ Γ.points, firstPoint w ∈ V.points) (a : Fin e)
    (htranslate : ∀ v : Point e, v a = 1 → ∀ d : Point (skewDim e),
      alternatingEvaluation v (C.decode d) = 0 → d ∈ horizontalTranslationSpace Γ v)
    (z : Point (skewDim e)) (v : Point e) (hz : joinPoints z v ∈ Γ.points)
    (hva : v a = 1) (hv : v ≠ 0) :
    evaluationFlat C (graphParameter C z v hv) ⊆ V.points := by
  intro y hy
  have heval := (evaluationFlat_graphParameter_iff C z y v hv).mp hy
  have hker : alternatingEvaluation v (C.decode (y - z)) = 0 := by
    rw [map_sub, map_sub, heval, sub_self]
  have hyΓ := htranslate v hva (y - z) hker z hz 1
  have heq : z + (1 : ℂ) • (y - z) = y := by simp
  rw [heq] at hyΓ
  have h := hcontain (joinPoints y v) hyΓ
  have hfirst : firstPoint (n := skewDim e) (m := e) (joinPoints y v) = y := by
    ext l
    simp [firstPoint, joinPoints]
  rwa [hfirst] at h

theorem full_parameter_fibers_of_horizontal_translations {e : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e)
    (hnormal : ∀ w ∈ Γ.points, secondPoint w a = 1)
    (htranslate : ∀ v : Point e, v a = 1 → ∀ d : Point (skewDim e),
      alternatingEvaluation v (C.decode d) = 0 → d ∈ horizontalTranslationSpace Γ v)
    (p : ProjectivePoint (e + e)) (hp : p ∈ parameterImage C Γ H)
    (y : Point (skewDim e)) (hy : y ∈ workingPoints V H) :
    y ∈ evaluationFlat C p ↔ ∃ v, joinPoints y v ∈ rulingPoints Γ H ∧
      ∃ hv : v ≠ 0, graphParameter C y v hv = p := by
  obtain ⟨z, v, hz, hv, hparam⟩ := hp
  have hva : v a = 1 := by simpa [secondPoint, joinPoints] using hnormal _ hz.1
  constructor
  · intro hflat
    have heval := (evaluationFlat_graphParameter_iff C z y v hv).mp (hparam ▸ hflat)
    have hker : alternatingEvaluation v (C.decode (y - z)) = 0 := by
      rw [map_sub, map_sub, heval, sub_self]
    have hyΓ := htranslate v hva (y - z) hker z hz.1 1
    have heq : z + (1 : ℂ) • (y - z) = y := by simp
    rw [heq] at hyΓ
    refine ⟨v, ⟨hyΓ, ?_⟩, hv, (graphParameter_eq_of_evaluation_eq C z y v hv heval).trans hparam⟩
    have hfirst : firstPoint (n := skewDim e) (m := e) (joinPoints y v) = y := by
      ext l
      simp [firstPoint, joinPoints]
    rw [hfirst]
    exact hy.2
  · rintro ⟨u, hu, hu0, huparam⟩
    rw [← huparam]
    exact (evaluationFlat_graphParameter_iff C y y u hu0).mpr rfl


/-- The two cleared horizontal tests put the literal vector (K_v,0) in the
block equation kernel. Smoothness has already identified that kernel with
the tangent of each actual prime incidence. -/
theorem horizontal_tangent_of_tests {e c : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (g : Fin c → Poly (skewDim e)) (W : Fin e → Fin e → Poly (skewDim e))
    (R : Polynomial (Poly (skewDim e))) (a b : Fin e)
    (w : Point (skewDim e + e))
    (htan : Γ.tangentSpace w = LinearMap.ker
      (TrackA.evaluatedJacobian (rootGraphEquations g R (W a b)
        (fun l => W l b) (fun l => W a l) b) w).mulVecLin)
    (hbase : V.tangentSpace (firstPoint w) =
      ⨅ l : Fin c, LinearMap.ker (differential (g l) (firstPoint w)))
    (hδ : MvPolynomial.aeval (firstPoint w) (W a b) ≠ 0)
    (hgraph : ∀ l, MvPolynomial.aeval (firstPoint w) (W l b) +
      secondPoint w b * MvPolynomial.aeval (firstPoint w) (W a l) =
        MvPolynomial.aeval (firstPoint w) (W a b) * secondPoint w l)
    (i j : Fin e)
    (hkernel : C.decode.symm (normalizedKernelPair a (secondPoint w) i j) ∈
      V.tangentSpace (firstPoint w))
    (hfirst : ∀ l, (firstHorizontalTest C W a b i j l).eval₂
      (MvPolynomial.aeval (firstPoint w)).toRingHom (secondPoint w b) = 0)
    (hsecond : (secondHorizontalTest C W a b i j R).eval₂
      (MvPolynomial.aeval (firstPoint w)).toRingHom (secondPoint w b) = 0) :
    joinPoints (C.decode.symm (normalizedKernelPair a (secondPoint w) i j)) 0 ∈ Γ.tangentSpace w := by
  let d := C.decode.symm (normalizedKernelPair a (secondPoint w) i j)
  let u := joinPoints d (0 : Point e)
  have hufirst : firstPoint u = d := by ext l; simp [u, firstPoint, joinPoints]
  have husecond : secondPoint u = 0 := by ext l; simp [u, secondPoint, joinPoints]
  have hg : ∀ l : Fin c, differential (g l) (firstPoint w) d = 0 := by
    rw [hbase, Submodule.mem_iInf] at hkernel
    exact hkernel
  have hF (l : Fin e) : differential (W l b + MvPolynomial.C (secondPoint w b) * W a l -
      MvPolynomial.C (secondPoint w l) * W a b) (firstPoint w) d = 0 := by
    have h := hfirst l
    rw [eval_firstHorizontalTest C W a b i j l (firstPoint w) (secondPoint w) hgraph] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hδ)
  have hS : differential (R.eval (MvPolynomial.C (secondPoint w b))) (firstPoint w) d = 0 := by
    have h := hsecond
    rw [eval_secondHorizontalTest C W a b i j R (firstPoint w) (secondPoint w) hgraph] at h
    exact (mul_eq_zero.mp h).resolve_left hδ
  rw [htan]
  apply (evaluatedJacobian_ker_iff _ w u).mpr
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hf
      rw [differential_base_rename, hufirst]
      exact hg l
    · have heq := List.mem_singleton.mp hf
      subst f
      rw [differential_rootEquation_horizontal R b w u husecond, hufirst]
      exact hS
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
    rw [differential_graphEquation_horizontal (W a b) (W l b) (W a l) b l w u husecond,
      hufirst, hF l, neg_zero]

theorem jacobian_minor_of_kernel_bound {m : ℕ} (E : List (Poly m)) (w : Point m)
    (k : ℕ) (hk : k ≤ m) (hlen : E.length = m - k)
    (hker : Module.finrank ℂ (LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin) ≤ k) :
    ∃ M ∈ TrackA.jacobianMinors E (m - k), MvPolynomial.eval w M ≠ 0 := by
  let A := TrackA.evaluatedJacobian E w
  change Module.finrank ℂ (LinearMap.ker A.mulVecLin) ≤ k at hker
  have hrank : A.rank = m - k := by
    have hr := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    change A.rank + Module.finrank ℂ (LinearMap.ker A.mulVecLin) = Module.finrank ℂ (Point m) at hr
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr
    have hu := A.rank_le_height.trans hlen.le
    omega
  obtain ⟨rows, cols, hdet⟩ := TrackA.matrix_rank_minor A hrank
  let M := Matrix.det ((TrackA.jacobian E).submatrix rows cols)
  refine ⟨M, ⟨rows, cols, rfl⟩, ?_⟩
  have he : (MvPolynomial.eval w).mapMatrix ((TrackA.jacobian E).submatrix rows cols) =
      A.submatrix rows cols := by ext i j; rfl
  change MvPolynomial.eval w ((TrackA.jacobian E).submatrix rows cols).det ≠ 0
  rw [(MvPolynomial.eval w).map_det, he]
  exact hdet

theorem equation_kernel_finrank_le_of_projection {n e : ℕ}
    (E : List (Poly (n + e))) (w : Point (n + e)) (T : Submodule ℂ (Point n))
    (hproj : ∀ d ∈ LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin, firstPoint d ∈ T)
    (hvertical : ∀ d ∈ LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin, firstPoint d = 0 → d = 0) :
    Module.finrank ℂ (LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin) ≤ Module.finrank ℂ T := by
  let K := LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin
  let f : K →ₗ[ℂ] T := ((basePointProjection n e).comp K.subtype).codRestrict T
    (fun d => hproj d.val d.property)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro d hd
    exact Subtype.ext (hvertical d.val d.property (congrArg Subtype.val hd))
  exact LinearMap.finrank_le_finrank_of_injective hf


theorem rootGraphFamily_finite_fiber {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (q : Polynomial (PrincipalCoordinateRing V H)) (v : Fin e → AdjoinRoot q)
    (R : Polynomial (Poly n)) (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e)
    (hR : R.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
      (principalCoordinateMap V H).toRingHom) (v b) = 0)
    (hgraph : ∀ i, algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (principalCoordinateMap V H δ) * v i =
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (B i)) +
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (A i)) * v b)
    (z : Point n) (hδ : MvPolynomial.aeval z δ ≠ 0)
    (hRz : R.map (MvPolynomial.aeval z).toRingHom ≠ 0) :
    let F := rootGraphFamily V H q v
    {d : Point e | joinPoints z d ∈ (AffineFamily.locus F).points}.Finite ∧
      {d : Point e | joinPoints z d ∈ (AffineFamily.locus F).points}.ncard ≤
        (R.map (MvPolynomial.aeval z).toRingHom).natDegree := by
  let F := rootGraphFamily V H q v
  have hfirst (d : Point e) : firstPoint (joinPoints z d) = z := by ext i; simp [firstPoint, joinPoints]
  have hsecond (d : Point e) : secondPoint (joinPoints z d) = d := by ext i; simp [secondPoint, joinPoints]
  apply graph_root_fiber_bound (AffineFamily.locus F) z (MvPolynomial.aeval z δ) hδ
    (fun i => MvPolynomial.aeval z (B i)) (fun i => MvPolynomial.aeval z (A i)) b
    (R.map (MvPolynomial.aeval z).toRingHom) hRz
  · intro d hd i
    rw [AffineFamily.points_locus] at hd
    obtain ⟨Γ, hΓ, hdΓ⟩ := (by simpa only [Set.mem_iUnion, exists_prop] using hd :
      ∃ Γ ∈ F, joinPoints z d ∈ Γ.points)
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    letI : Q.IsPrime := hQprime
    have h := rootGraphVariety_graph_coordinate V H q v Q δ (B i) (A i) b i (hgraph i)
      (joinPoints z d) hdΓ
    rwa [hfirst, hsecond] at h
  · intro d hd
    rw [AffineFamily.points_locus] at hd
    obtain ⟨Γ, hΓ, hdΓ⟩ := (by simpa only [Set.mem_iUnion, exists_prop] using hd :
      ∃ Γ ∈ F, joinPoints z d ∈ Γ.points)
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    letI : Q.IsPrime := hQprime
    have h := rootGraphVariety_root_condition V H q v Q R b hR (joinPoints z d) hdΓ
    rw [hfirst, hsecond] at h
    simpa only [Polynomial.eval_map] using h

theorem rootGraphFamily_card_le_degree {n e c : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (hcodim : V.dimension + c = n) (H : Poly n) (hH : H ∉ V.ideal)
    (q : Polynomial (PrincipalCoordinateRing V H)) (hq : q.Monic) (v : Fin e → AdjoinRoot q)
    (g : Fin c → Poly n) (hg : ∀ i, g i ∈ V.ideal) (R : Polynomial (Poly n))
    (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e)
    (hR : R.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
      (principalCoordinateMap V H).toRingHom) (v b) = 0)
    (hgraph : ∀ i, algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (principalCoordinateMap V H δ) * v i =
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (B i)) +
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (A i)) * v b)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0)
    (hsmooth : V.IsSmoothAt z)
    (htan : V.tangentSpace z = ⨅ i : Fin c, LinearMap.ker (differential (g i) z))
    (hδ : MvPolynomial.aeval z δ ≠ 0) (hRz : R.map (MvPolynomial.aeval z).toRingHom ≠ 0)
    (hderiv : ∀ d : Point e, joinPoints z d ∈ (AffineFamily.locus (rootGraphFamily V H q v)).points →
      R.derivative.eval₂ (MvPolynomial.aeval z).toRingHom (d b) ≠ 0) :
    (rootGraphFamily V H q v).card ≤ (R.map (MvPolynomial.aeval z).toRingHom).natDegree := by
  letI : V.ideal.IsPrime := hV
  let F := rootGraphFamily V H q v
  let E := rootGraphEquations g R δ B A b
  let T := {d : Point e | joinPoints z d ∈ (AffineFamily.locus F).points}
  obtain ⟨hT, hTcard⟩ := rootGraphFamily_finite_fiber V H q v R δ B A b hR hgraph z hδ hRz
  have hE : ∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal := by
    intro f hf
    rw [← AffineVariety.vanishingIdeal_points]
    intro w hw
    rw [AffineFamily.points_locus] at hw
    obtain ⟨Γ, hΓ, hwΓ⟩ := (by simpa only [Set.mem_iUnion, exists_prop] using hw : ∃ Γ ∈ F, w ∈ Γ.points)
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    letI : Q.IsPrime := hQprime
    exact hwΓ _ (rootGraphEquations_mem_ideal V H hH q v Q g hg R δ B A b hR hgraph f hf)
  have hk : V.dimension ≤ n + e := (Bridges.affine_dimension_le V).trans (Nat.le_add_right _ _)
  have hlen : E.length = n + e - V.dimension := by rw [rootGraphEquations_length]; omega
  apply dominant_family_card_le_fiber F z T hT hTcard
  · exact rootGraphFamily_dominant V H hH q hq v z hz hzH
  · intro Γ hΓ d hd
    change joinPoints z d ∈ (AffineFamily.locus F).points
    rw [AffineFamily.points_locus]
    simpa only [Set.mem_iUnion, exists_prop] using (show ∃ Γ ∈ F, joinPoints z d ∈ Γ.points from ⟨Γ, hΓ, hd⟩)
  · intro Γ hΓ Δ hΔ d hdΓ hdΔ
    let x := joinPoints z d
    have hx : x ∈ (AffineFamily.locus F).points := by
      rw [AffineFamily.points_locus]
      simpa only [Set.mem_iUnion, exists_prop] using (show ∃ Γ ∈ F, x ∈ Γ.points from ⟨Γ, hΓ, hdΓ⟩)
    have hxfirst : firstPoint x = z := by ext i; simp [x, firstPoint, joinPoints]
    have hxsecond : secondPoint x = d := by ext i; simp [x, secondPoint, joinPoints]
    have ht : V.tangentSpace (firstPoint x) =
        ⨅ i : Fin c, LinearMap.ker (differential (g i) (firstPoint x)) := by rwa [hxfirst]
    have hproj := root_graph_equation_kernel_projection V g R δ B A b x ht
    have hvert := root_graph_equation_kernel_vertical g R δ B A b x
      (by rwa [hxfirst]) (by rw [hxfirst, hxsecond]; exact hderiv d hx)
    have hK := equation_kernel_finrank_le_of_projection E x (V.tangentSpace (firstPoint x)) hproj hvert
    have hVdim : Module.finrank ℂ (V.tangentSpace (firstPoint x)) = V.dimension := by
      rw [hxfirst, hsmooth.2, V.localDimension_eq_dimension z hV hz]
    rw [hVdim] at hK
    obtain ⟨M, hM, hMx⟩ := jacobian_minor_of_kernel_bound E x V.dimension hk hlen hK
    exact pure_family_unique_at_minor F hk (rootGraphFamily_pure V H hH q hq v) E hE x hx
      ⟨M, hM, hMx⟩ Γ hΓ Δ hΔ hdΓ hdΔ


theorem linear_coordinate_sum {n : ℕ} (α : Point n →ₗ[ℂ] ℂ) (x : Point n) :
    (∑ m : Fin n, α (Pi.single m 1) * x m) = α x := by
  have hx : (∑ m : Fin n, x m • Pi.single m (1 : ℂ)) = x := by
    simpa using (Pi.basisFun ℂ (Fin n)).sum_repr x
  calc
    _ = α (∑ m : Fin n, x m • Pi.single m (1 : ℂ)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = α x := congrArg α hx

def graphVectorPolynomial {e : ℕ} (C : SkewCoordinates e) :
    Fin (e + e) → Poly (skewDim e + e) :=
  Fin.addCases (fun i => MvPolynomial.X (Fin.natAdd (skewDim e) i))
    (fun j => ∑ i : Fin e, MvPolynomial.X (Fin.natAdd (skewDim e) i) *
      ∑ m : Fin (skewDim e),
        MvPolynomial.C ((C.decode (Pi.single m 1)).val (Pi.single i 1) (Pi.single j 1)) *
          MvPolynomial.X (Fin.castAdd e m))

theorem eval_graphVectorPolynomial {e : ℕ} (C : SkewCoordinates e)
    (w : Point (skewDim e + e)) :
    polynomialPointMap (graphVectorPolynomial C) w = graphVector C (firstPoint w) (secondPoint w) := by
  have hcoord (i j : Fin e) :
      (∑ m : Fin (skewDim e), (C.decode (Pi.single m 1)).val (Pi.single i 1) (Pi.single j 1) *
        firstPoint w m) = (C.decode (firstPoint w)).val (Pi.single i 1) (Pi.single j 1) := by
    let α : Point (skewDim e) →ₗ[ℂ] ℂ :=
      { toFun := fun z => (C.decode z).val (Pi.single i 1) (Pi.single j 1)
        map_add' := by intro z u; rw [C.decode.map_add]; rfl
        map_smul' := by intro s z; rw [C.decode.map_smul]; rfl }
    exact linear_coordinate_sum α (firstPoint w)
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [polynomialPointMap, graphVectorPolynomial, Fin.addCases_left,
      MvPolynomial.aeval_X, graphVector, joinPoints]
    rfl
  · simp only [polynomialPointMap, graphVectorPolynomial, Fin.addCases_right, map_sum, map_mul,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      graphVector, joinPoints, pointOfCovector]
    change (∑ j : Fin e, secondPoint w j *
      ∑ m : Fin (skewDim e), (C.decode (Pi.single m 1)).val (Pi.single j 1) (Pi.single i 1) *
        firstPoint w m) = (C.decode (firstPoint w)).val (secondPoint w) (Pi.single i 1)
    simp_rw [hcoord]
    have hv : (∑ j : Fin e, secondPoint w j • Pi.single j (1 : ℂ)) = secondPoint w := by
      simpa using (Pi.basisFun ℂ (Fin e)).sum_repr (secondPoint w)
    calc
      _ = (C.decode (firstPoint w)).val (∑ j : Fin e, secondPoint w j • Pi.single j (1 : ℂ))
          (Pi.single i 1) := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      _ = _ := by rw [hv]

theorem parameterImage_eq_polynomialParameterImage {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    parameterImage C Γ H = polynomialParameterImage Γ (MvPolynomial.rename (Fin.castAdd e) H)
      (graphVectorPolynomial C) := by
  ext p
  constructor
  · rintro ⟨z, v, hz, hv, hp⟩
    let w := joinPoints z v
    have hfirst : firstPoint w = z := by ext i; simp [w, firstPoint, joinPoints]
    have hsecond : secondPoint w = v := by ext i; simp [w, secondPoint, joinPoints]
    have hpmap : polynomialPointMap (graphVectorPolynomial C) w = graphVector C z v := by
      rw [eval_graphVectorPolynomial, hfirst, hsecond]
    refine ⟨w, hz.1, ?_, ?_, ?_⟩
    · convert hz.2 using 1 <;> simp [MvPolynomial.aeval_rename, w, firstPoint, joinPoints] <;> rfl
    · rw [hpmap]
      exact graphVector_ne_zero C z v hv
    · apply Eq.trans ?_ hp
      exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
        ⟨1, by simpa only [one_smul] using hpmap.symm⟩
  · rintro ⟨w, hw, hwH, hw0, hp⟩
    have hv : secondPoint w ≠ 0 := by
      intro hv
      rw [eval_graphVectorPolynomial, hv] at hw0
      apply hw0
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [graphVector, joinPoints, Fin.addCases_left, Fin.addCases_right,
          pointOfCovector, map_zero, LinearMap.zero_apply, Pi.zero_apply]
    refine ⟨firstPoint w, secondPoint w, ⟨?_, ?_⟩, hv, ?_⟩
    · rw [joinPoints_eta]
      exact hw
    · rw [joinPoints_eta]
      convert hwH using 1 <;> simp [MvPolynomial.aeval_rename, firstPoint] <;> rfl
    · apply Eq.trans ?_ hp
      exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
        ⟨1, by simpa only [one_smul] using eval_graphVectorPolynomial C w⟩

theorem parameterClosure_irreducible_of_normalized {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (hΓ : Γ.IsIrreducible) (H : Poly (skewDim e))
    (hH : MvPolynomial.rename (Fin.castAdd e) H ∉ Γ.ideal) (a : Fin e)
    (hnormal : ∀ w ∈ Γ.points, secondPoint w a = 1) :
    (parameterClosure C Γ H).IsIrreducible := by
  rw [parameterClosure, parameterImage_eq_polynomialParameterImage]
  apply polynomialParameter_closure_irreducible Γ hΓ _ hH (graphVectorPolynomial C)
  intro w hw
  rw [eval_graphVectorPolynomial]
  apply graphVector_ne_zero
  intro hv
  have h := hnormal w hw
  rw [hv, Pi.zero_apply] at h
  exact zero_ne_one h


/-- Horizontal tangency integrates to the two flat-fiber properties in the
frozen ruling predicate. All remaining fields describe the actual incidence. -/
theorem rulingIncidence_of_horizontal_tangency {e : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (j N : ℕ)
    (hV : V.IsIrreducible) (hΓ : Γ.IsIrreducible) (hH : H ∉ V.ideal)
    (hΓH : MvPolynomial.rename (Fin.castAdd e) H ∉ Γ.ideal)
    (hj : j ≤ 1) (hN : 1 ≤ N) (hdim : Γ.dimension = V.dimension + j)
    (hnormal : ∀ w ∈ Γ.points, secondPoint w a = 1)
    (hcontain : ∀ w ∈ Γ.points, firstPoint w ∈ V.points)
    (hdominant : ∀ z ∈ workingPoints V H, (directionFiber Γ z).Nonempty)
    (hsmooth : ∀ w ∈ rulingPoints Γ H, Γ.IsSmoothAt w ∧ V.IsSmoothAt (firstPoint w) ∧
      (Γ.tangentSpace w).map (pointProjection e) = V.tangentSpace (firstPoint w))
    (hfinite : j = 0 → ∀ z ∈ workingPoints V H,
      (directionFiber Γ z).Finite ∧ (directionFiber Γ z).ncard ≤ N)
    (hline : j = 1 → ∀ z ∈ workingPoints V H, IsAffineLine (directionFiber Γ z))
    (hcodim : j = 1 → V.dimension + 1 = skewDim e)
    (htan : ∀ w ∈ rulingPoints Γ H, ∀ i l : Fin e,
      joinPoints (C.decode.symm (normalizedKernelPair a (secondPoint w) i l)) 0 ∈ Γ.tangentSpace w) :
    IsRulingIncidence C V Γ H a j N := by
  have htranslate := full_horizontal_kernel_translation C Γ hΓ H hΓH a htan
  refine
    { variety_irreducible := hV
      incidence_irreducible := hΓ
      nonzero_section := hH
      fiber_cases := hj
      bound_positive := hN
      incidence_dimension := hdim
      normalized := hnormal
      point_containment := hcontain
      dominant := hdominant
      smooth := hsmooth
      finite_fiber := hfinite
      line_fiber := hline
      codimension_one := hcodim
      actual_flats := ?_
      full_parameter_fibers := ?_ }
  · intro z v hz hv
    have hva : v a = 1 := by simpa [secondPoint, joinPoints] using hnormal _ hz.1
    exact contained_flat_of_horizontal_translations C V Γ hcontain a htranslate z v hz.1 hva hv
  · exact full_parameter_fibers_of_horizontal_translations C V Γ H a hnormal htranslate


theorem polynomial_trdeg_over_base (R : Type) [CommRing R] [IsDomain R] [Algebra ℂ R] :
    Algebra.trdeg ℂ (Polynomial R) = Algebra.trdeg ℂ R + 1 := by
  have h := trdeg_add_eq ℂ R (A := Polynomial R)
  rw [Polynomial.trdeg_of_isDomain] at h
  exact h.symm

def lineGraphMap {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (v : Fin e → Polynomial (PrincipalCoordinateRing V H)) :
    Poly (n + e) →ₐ[ℂ] Polynomial (PrincipalCoordinateRing V H) :=
  MvPolynomial.aeval (Fin.addCases
    (fun i => Polynomial.C (principalCoordinateMap V H (MvPolynomial.X i))) v)

theorem lineGraphMap_base {n e : ℕ} (V : AffineVariety n) (H : Poly n)
    (v : Fin e → Polynomial (PrincipalCoordinateRing V H)) (f : Poly n) :
    lineGraphMap V H v (MvPolynomial.rename (Fin.castAdd e) f) =
      Polynomial.C (principalCoordinateMap V H f) := by
  have hm : (lineGraphMap V H v).comp (MvPolynomial.rename (Fin.castAdd e)) =
      (Polynomial.CAlgHom (R := ℂ) (A := PrincipalCoordinateRing V H)).comp (principalCoordinateMap V H) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [lineGraphMap]
  exact DFunLike.congr_fun hm f

def lineGraphVariety {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H)) :
    AffineVariety (n + e) := by
  letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
  exact kernelGraphVariety (lineGraphMap V H v)

theorem lineGraphVariety_irreducible {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H)) :
    (lineGraphVariety V H hH v).IsIrreducible := by
  letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
  exact kernelGraphVariety_irreducible (lineGraphMap V H v)

set_option backward.isDefEq.respectTransparency false in
theorem polynomial_graph_dimension {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal)
    (φ : Poly (n + e) →ₐ[ℂ] Polynomial (PrincipalCoordinateRing V H))
    (hφ : ∀ f : Poly n, φ (MvPolynomial.rename (Fin.castAdd e) f) =
      Polynomial.C (principalCoordinateMap V H f)) (b : Fin e)
    (hb : φ (MvPolynomial.X (Fin.natAdd n b)) = Polynomial.X) :
    letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
    (kernelGraphVariety φ).dimension = V.dimension + 1 := by
  letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
  let Γ := kernelGraphVariety φ
  letI : Γ.ideal.IsPrime := kernelGraphVariety_irreducible φ
  let ι : Poly n →ₐ[ℂ] Poly (n + e) := MvPolynomial.rename (Fin.castAdd e)
  have hcomap : Γ.ideal.comap ι.toRingHom = V.ideal := by
    ext f
    change φ (MvPolynomial.rename (Fin.castAdd e) f) = 0 ↔ f ∈ V.ideal
    rw [hφ, ← map_zero (Polynomial.C : PrincipalCoordinateRing V H →+* _), Polynomial.C_injective.eq_iff]
    change f ∈ RingHom.ker (principalCoordinateMap V H).toRingHom ↔ f ∈ V.ideal
    rw [principalCoordinateMap_ker V H hH]
  let B : (Poly n ⧸ V.ideal) →ₐ[ℂ] (Poly (n + e) ⧸ Γ.ideal) :=
    Ideal.quotientMapₐ Γ.ideal ι (le_of_eq hcomap.symm)
  let x := Ideal.Quotient.mk Γ.ideal (MvPolynomial.X (Fin.natAdd n b))
  let J : Polynomial (Poly n ⧸ V.ideal) →ₐ[ℂ] (Poly (n + e) ⧸ Γ.ideal) :=
    { toRingHom := Polynomial.eval₂RingHom B.toRingHom x
      commutes' := by
        intro c
        change Polynomial.eval₂ B.toRingHom x (Polynomial.C (algebraMap ℂ (Poly n ⧸ V.ideal) c)) = _
        rw [Polynomial.eval₂_C]
        exact B.commutes c }
  let ψ := Ideal.kerLiftAlg φ
  let r := algebraMap (Poly n ⧸ V.ideal) (PrincipalCoordinateRing V H)
  have hcomp : ψ.toRingHom.comp J.toRingHom = Polynomial.mapRingHom r := by
    apply Polynomial.ringHom_ext
    · intro s
      change ψ (Polynomial.eval₂ B.toRingHom x (Polynomial.C s)) = Polynomial.map r (Polynomial.C s)
      rw [Polynomial.eval₂_C, Polynomial.map_C]
      refine Quotient.inductionOn' s ?_
      intro f
      change φ (MvPolynomial.rename (Fin.castAdd e) f) =
        Polynomial.C (algebraMap (Poly n ⧸ V.ideal) (PrincipalCoordinateRing V H)
          (Ideal.Quotient.mk V.ideal f))
      rw [hφ]
      rfl
    · change ψ (Polynomial.eval₂ B.toRingHom x Polynomial.X) = Polynomial.map r Polynomial.X
      rw [Polynomial.eval₂_X, Polynomial.map_X]
      change φ (MvPolynomial.X (Fin.natAdd n b)) = Polynomial.X
      exact hb
  have hr : Function.Injective r := IsLocalization.injective (PrincipalCoordinateRing V H)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (fun h => hH (Ideal.Quotient.eq_zero_iff_mem.mp h)))
  have hJ : Function.Injective J := by
    intro p q hpq
    apply Polynomial.map_injective r hr
    change Polynomial.mapRingHom r p = Polynomial.mapRingHom r q
    rw [← hcomp]
    exact congrArg ψ hpq
  have hlo : Algebra.trdeg ℂ (Polynomial (Poly n ⧸ V.ideal)) ≤
      Algebra.trdeg ℂ (Poly (n + e) ⧸ Γ.ideal) := trdeg_le_of_injective J hJ
  have hhi := trdeg_le_of_injective ψ (Ideal.kerLiftAlg_injective φ)
  rw [polynomial_trdeg_over_base] at hlo hhi
  rw [principalCoordinateRing_trdeg V H hH] at hhi
  have heq : Algebra.trdeg ℂ (Poly (n + e) ⧸ Γ.ideal) =
      Algebra.trdeg ℂ (Poly n ⧸ V.ideal) + 1 := le_antisymm hhi hlo
  rw [← affine_dimension_eq_trdeg Γ, ← affine_dimension_eq_trdeg V] at heq
  exact_mod_cast heq

theorem lineGraphVariety_dimension {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H))
    (b : Fin e) (hb : v b = Polynomial.X) :
    (lineGraphVariety V H hH v).dimension = V.dimension + 1 := by
  apply polynomial_graph_dimension V H hH (lineGraphMap V H v) (lineGraphMap_base V H v) b
  simpa only [lineGraphMap, MvPolynomial.aeval_X, Fin.addCases_right] using hb

def polynomialCoordinatePoint {n : ℕ} (V : AffineVariety n) (H : Poly n)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0) (t : ℂ) :
    Polynomial (PrincipalCoordinateRing V H) →ₐ[ℂ] ℂ :=
  { toRingHom := Polynomial.eval₂RingHom (principalCoordinatePoint V H z hz hzH).toRingHom t
    commutes' := by intro c; simp }

theorem polynomialCoordinatePoint_C {n : ℕ} (V : AffineVariety n) (H : Poly n)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0) (t : ℂ)
    (r : PrincipalCoordinateRing V H) :
    polynomialCoordinatePoint V H z hz hzH t (Polynomial.C r) =
      principalCoordinatePoint V H z hz hzH r := by
  change Polynomial.eval₂ (principalCoordinatePoint V H z hz hzH).toRingHom t (Polynomial.C r) = _
  rw [Polynomial.eval₂_C]
  rfl

theorem polynomialCoordinatePoint_X {n : ℕ} (V : AffineVariety n) (H : Poly n)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0) (t : ℂ) :
    polynomialCoordinatePoint V H z hz hzH t Polynomial.X = t := by
  change Polynomial.eval₂ (principalCoordinatePoint V H z hz hzH).toRingHom t Polynomial.X = t
  rw [Polynomial.eval₂_X]

theorem lineGraphVariety_point_of_hom {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H))
    (z : Point n) (g : Polynomial (PrincipalCoordinateRing V H) →ₐ[ℂ] ℂ)
    (hbase : ∀ f : Poly n, g (Polynomial.C (principalCoordinateMap V H f)) = MvPolynomial.aeval z f) :
    joinPoints z (fun i => g (v i)) ∈ (lineGraphVariety V H hH v).points := by
  letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
  have hp := kernelGraphVariety_point (lineGraphMap V H v) g
  have heq : (fun i => g (lineGraphMap V H v (MvPolynomial.X i))) = joinPoints z (fun i => g (v i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [lineGraphMap, MvPolynomial.aeval_X, Fin.addCases_left, joinPoints]
      simpa only [MvPolynomial.aeval_X] using hbase (MvPolynomial.X j)
    · simp [lineGraphMap, joinPoints]
  rw [heq] at hp
  exact hp

theorem lineGraphVariety_point {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H))
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0) (t : ℂ) :
    joinPoints z (fun i => polynomialCoordinatePoint V H z hz hzH t (v i)) ∈
      (lineGraphVariety V H hH v).points := by
  apply lineGraphVariety_point_of_hom V H hH v z (polynomialCoordinatePoint V H z hz hzH t)
  intro f
  rw [polynomialCoordinatePoint_C]
  exact principalCoordinatePoint_map V H z hz hzH f

theorem baseEquation_mem_lineGraph {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H))
    (f : Poly n) (hf : f ∈ V.ideal) :
    MvPolynomial.rename (Fin.castAdd e) f ∈ (lineGraphVariety V H hH v).ideal := by
  change lineGraphMap V H v (MvPolynomial.rename (Fin.castAdd e) f) = 0
  rw [lineGraphMap_base]
  have hz : principalCoordinateMap V H f = 0 := by
    change f ∈ RingHom.ker (principalCoordinateMap V H).toRingHom
    rwa [principalCoordinateMap_ker V H hH]
  rw [hz, Polynomial.C_0]

theorem lineGraphVariety_point_containment {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H))
    (w : Point (n + e)) (hw : w ∈ (lineGraphVariety V H hH v).points) : firstPoint w ∈ V.points := by
  intro f hf
  have h := hw _ (baseEquation_mem_lineGraph V H hH v f hf)
  rw [MvPolynomial.aeval_rename] at h
  exact h

theorem lineGraphVariety_normalized {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H))
    (a : Fin e) (ha : v a = 1) (w : Point (n + e)) (hw : w ∈ (lineGraphVariety V H hH v).points) :
    secondPoint w a = 1 := by
  letI : IsDomain (PrincipalCoordinateRing V H) := principalCoordinateRing_isDomain V H hH
  exact kernelGraphVariety_coordinate_eq (lineGraphMap V H v) (Fin.natAdd n a) 1
    (by simp [lineGraphMap, ha]) w hw

theorem graphEquation_mem_lineGraph {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H))
    (δ B A : Poly n) (b i : Fin e)
    (hv : Polynomial.C (principalCoordinateMap V H δ) * v i =
      Polynomial.C (principalCoordinateMap V H B) + Polynomial.C (principalCoordinateMap V H A) * v b) :
    graphEquationPolynomial δ B A b i ∈ (lineGraphVariety V H hH v).ideal := by
  change lineGraphMap V H v (graphEquationPolynomial δ B A b i) = 0
  simp only [graphEquationPolynomial, map_sub, map_mul, lineGraphMap_base]
  simp only [lineGraphMap, MvPolynomial.aeval_X, Fin.addCases_right]
  linear_combination hv

theorem lineGraphVariety_graph_coordinate {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H))
    (δ B A : Poly n) (b i : Fin e)
    (hv : Polynomial.C (principalCoordinateMap V H δ) * v i =
      Polynomial.C (principalCoordinateMap V H B) + Polynomial.C (principalCoordinateMap V H A) * v b)
    (w : Point (n + e)) (hw : w ∈ (lineGraphVariety V H hH v).points) :
    MvPolynomial.aeval (firstPoint w) δ * secondPoint w i =
      MvPolynomial.aeval (firstPoint w) B + MvPolynomial.aeval (firstPoint w) A * secondPoint w b := by
  have h := hw _ (graphEquation_mem_lineGraph V H hH v δ B A b i hv)
  simp only [graphEquationPolynomial, map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X] at h
  change MvPolynomial.aeval (firstPoint w) δ * secondPoint w i -
    MvPolynomial.aeval (firstPoint w) B - MvPolynomial.aeval (firstPoint w) A * secondPoint w b = 0 at h
  linear_combination h

def affineLineDirection {n e : ℕ} (V : AffineVariety n) (H δ : Poly n) (B A : Fin e → Poly n) :
    Fin e → Polynomial (PrincipalCoordinateRing V H) :=
  fun i => Polynomial.C (principalCoordinateMap V H (B i) * Ring.inverse (principalCoordinateMap V H δ)) +
    Polynomial.C (principalCoordinateMap V H (A i) * Ring.inverse (principalCoordinateMap V H δ)) * Polynomial.X

theorem affineLineDirection_cleared {n e : ℕ} (V : AffineVariety n) (H δ : Poly n)
    (hδ : δ ∣ H) (B A : Fin e → Poly n) (i : Fin e) :
    Polynomial.C (principalCoordinateMap V H δ) * affineLineDirection V H δ B A i =
      Polynomial.C (principalCoordinateMap V H (B i)) + Polynomial.C (principalCoordinateMap V H (A i)) * Polynomial.X := by
  have hu := principalCoordinateMap_isUnit_of_dvd V H δ hδ
  have hc : Polynomial.C (principalCoordinateMap V H δ) *
      Polynomial.C (Ring.inverse (principalCoordinateMap V H δ)) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hu, map_one]
  simp only [affineLineDirection, map_mul]
  calc
    _ = Polynomial.C (principalCoordinateMap V H (B i)) *
        (Polynomial.C (principalCoordinateMap V H δ) * Polynomial.C (Ring.inverse (principalCoordinateMap V H δ))) +
      Polynomial.C (principalCoordinateMap V H (A i)) *
        (Polynomial.C (principalCoordinateMap V H δ) * Polynomial.C (Ring.inverse (principalCoordinateMap V H δ))) * Polynomial.X := by ring
    _ = _ := by rw [hc]; ring

theorem affineLineDirection_root_coordinate {n e : ℕ} (V : AffineVariety n) (H δ : Poly n)
    (hδ : δ ∣ H) (B A : Fin e → Poly n) (b : Fin e) (hB : B b = 0) (hA : A b = δ) :
    affineLineDirection V H δ B A b = Polynomial.X := by
  have hu := principalCoordinateMap_isUnit_of_dvd V H δ hδ
  simp [affineLineDirection, hB, hA, Ring.mul_inverse_cancel _ hu]

theorem affineLineDirection_normalized {n e : ℕ} (V : AffineVariety n) (H δ : Poly n)
    (hδ : δ ∣ H) (B A : Fin e → Poly n) (a : Fin e) (hB : B a = δ) (hA : A a = 0) :
    affineLineDirection V H δ B A a = 1 := by
  have hu := principalCoordinateMap_isUnit_of_dvd V H δ hδ
  simp [affineLineDirection, hB, hA, Ring.mul_inverse_cancel _ hu]


theorem affine_line_graph_solution_coverage {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (δ : Poly n) (hδ : δ ∣ H) (B A : Fin e → Poly n)
    (b : Fin e) (hB : B b = 0) (hA : A b = δ)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0)
    (hδz : MvPolynomial.aeval z δ ≠ 0) (d : Point e)
    (hd : ∀ i, MvPolynomial.aeval z δ * d i =
      MvPolynomial.aeval z (B i) + MvPolynomial.aeval z (A i) * d b) :
    joinPoints z d ∈ (lineGraphVariety V H hH (affineLineDirection V H δ B A)).points := by
  let v := affineLineDirection V H δ B A
  let g := polynomialCoordinatePoint V H z hz hzH (d b)
  have hvb : v b = Polynomial.X := affineLineDirection_root_coordinate V H δ hδ B A b hB hA
  have hgX : g Polynomial.X = d b := polynomialCoordinatePoint_X V H z hz hzH _
  have hbase (f : Poly n) : g (Polynomial.C (principalCoordinateMap V H f)) = MvPolynomial.aeval z f := by
    rw [polynomialCoordinatePoint_C]
    exact principalCoordinatePoint_map V H z hz hzH f
  have hpoint := lineGraphVariety_point V H hH v z hz hzH (d b)
  have heq : (fun i => g (v i)) = d := by
    funext i
    apply mul_left_cancel₀ hδz
    have h := congrArg g (affineLineDirection_cleared V H δ hδ B A i)
    simp only [map_mul, map_add, hbase, hgX] at h
    exact h.trans (hd i).symm
  rwa [heq] at hpoint

theorem affine_line_graph_fiber {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (δ : Poly n) (hδ : δ ∣ H) (B A : Fin e → Poly n)
    (b : Fin e) (hB : B b = 0) (hA : A b = δ)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0)
    (hδz : MvPolynomial.aeval z δ ≠ 0) :
    {d : Point e | joinPoints z d ∈ (lineGraphVariety V H hH (affineLineDirection V H δ B A)).points} =
      {d : Point e | ∀ i, MvPolynomial.aeval z δ * d i =
        MvPolynomial.aeval z (B i) + MvPolynomial.aeval z (A i) * d b} := by
  ext d
  constructor
  · intro hd i
    have hvb := affineLineDirection_root_coordinate V H δ hδ B A b hB hA
    have hclear := affineLineDirection_cleared V H δ hδ B A i
    rw [← hvb] at hclear
    have h := lineGraphVariety_graph_coordinate V H hH (affineLineDirection V H δ B A)
      δ (B i) (A i) b i hclear (joinPoints z d) hd
    have hfirst : firstPoint (joinPoints z d) = z := by ext j; simp [firstPoint, joinPoints]
    have hsecond : secondPoint (joinPoints z d) = d := by ext j; simp [secondPoint, joinPoints]
    rwa [hfirst, hsecond] at h
  · intro hd
    exact affine_line_graph_solution_coverage V H hH δ hδ B A b hB hA z hz hzH hδz d hd

theorem graph_solution_set_isAffineLine {e : ℕ} (δ : ℂ) (hδ : δ ≠ 0)
    (B A : Point e) (b : Fin e) (hB : B b = 0) (hA : A b = δ) :
    IsAffineLine {d : Point e | ∀ i, δ * d i = B i + A i * d b} := by
  let u : Point e := fun i => B i / δ
  let v : Point e := fun i => A i / δ
  have hvb : v b = 1 := by dsimp [v]; rw [hA, div_self hδ]
  have hv : v ≠ 0 := by
    intro h
    have hz := congrFun h b
    rw [hvb, Pi.zero_apply] at hz
    exact one_ne_zero hz
  refine ⟨u, v, hv, ?_⟩
  ext d
  constructor
  · intro hd
    refine ⟨d b, ?_⟩
    funext i
    change d i = B i / δ + d b * (A i / δ)
    field_simp
    linear_combination hd i
  · rintro ⟨t, rfl⟩ i
    change δ * (B i / δ + t * (A i / δ)) = B i + A i * (B b / δ + t * (A b / δ))
    rw [hB, hA, zero_div, div_self hδ, zero_add, mul_one]
    field_simp

theorem affine_line_graph_line_fiber {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (δ : Poly n) (hδ : δ ∣ H) (B A : Fin e → Poly n)
    (b : Fin e) (hB : B b = 0) (hA : A b = δ)
    (z : Point n) (hz : z ∈ V.points) (hzH : MvPolynomial.eval z H ≠ 0)
    (hδz : MvPolynomial.aeval z δ ≠ 0) :
    IsAffineLine {d : Point e | joinPoints z d ∈
      (lineGraphVariety V H hH (affineLineDirection V H δ B A)).points} := by
  rw [affine_line_graph_fiber V H hH δ hδ B A b hB hA z hz hzH hδz]
  exact graph_solution_set_isAffineLine _ hδz _ _ b (by simp [hB]) (by simp [hA])

theorem lineGraphVariety_section_nonzero {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H)) :
    MvPolynomial.rename (Fin.castAdd e) H ∉ (lineGraphVariety V H hH v).ideal := by
  intro hmem
  change lineGraphMap V H v (MvPolynomial.rename (Fin.castAdd e) H) = 0 at hmem
  rw [lineGraphMap_base, ← map_zero (Polynomial.C : PrincipalCoordinateRing V H →+* _),
    Polynomial.C_injective.eq_iff] at hmem
  have hHmem : H ∈ RingHom.ker (principalCoordinateMap V H).toRingHom := hmem
  rw [principalCoordinateMap_ker V H hH] at hHmem
  exact hH hHmem

theorem smooth_line_tangent_projection_of_equation_kernel {n e : ℕ}
    (V : AffineVariety n) (Γ : AffineVariety (n + e))
    (hV : V.IsIrreducible) (hΓ : Γ.IsIrreducible)
    (hdim : Γ.dimension = V.dimension + 1) (E : List (Poly (n + e)))
    (hlen : E.length = n + e - (V.dimension + 1)) (hE : ∀ f ∈ E, f ∈ Γ.ideal)
    (b : Fin e) (w : Point (n + e)) (hw : w ∈ Γ.points) (hbase : firstPoint w ∈ V.points)
    (hsmooth : V.IsSmoothAt (firstPoint w))
    (hproj : ∀ d ∈ LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin,
      firstPoint d ∈ V.tangentSpace (firstPoint w))
    (hvertical : ∀ d ∈ LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin,
      firstPoint d = 0 → secondPoint d b = 0 → d = 0) :
    Γ.IsSmoothAt w ∧ Γ.tangentSpace w =
      LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin ∧
      (Γ.tangentSpace w).map (basePointProjection n e) = V.tangentSpace (firstPoint w) := by
  let K := LinearMap.ker (TrackA.evaluatedJacobian E w).mulVecLin
  let π := basePointProjection n e
  let T := V.tangentSpace (firstPoint w)
  let πK : K →ₗ[ℂ] T := (π.comp K.subtype).codRestrict T (fun d => hproj d.val d.property)
  let β : Point (n + e) →ₗ[ℂ] ℂ := LinearMap.proj (Fin.natAdd n b)
  let F := πK.prod (β.comp K.subtype)
  have hF : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro d hd
    apply Subtype.ext
    apply hvertical d.val d.property
    · exact congrArg Subtype.val (congrArg Prod.fst hd)
    · exact congrArg Prod.snd hd
  have hTdim : Module.finrank ℂ T = V.dimension :=
    hsmooth.2.trans (V.localDimension_eq_dimension _ hV hbase)
  have hKdim : Module.finrank ℂ K ≤ V.dimension + 1 := by
    have h := LinearMap.finrank_le_finrank_of_injective hF
    simpa only [Module.finrank_prod, Module.finrank_self, hTdim] using h
  have hk : V.dimension + 1 ≤ n + e := by
    rw [← hdim]
    exact Bridges.affine_dimension_le Γ
  obtain ⟨m, hm, hmw⟩ := jacobian_minor_of_kernel_bound E w (V.dimension + 1) hk hlen hKdim
  have hΓsmooth := smooth_of_jacobian_minor Γ hΓ (V.dimension + 1) hdim E hE m hm w hw hmw
  have htan : Γ.tangentSpace w ≤ K := by
    intro d hd
    apply (evaluatedJacobian_ker_iff E w d).mpr
    intro f hf
    rw [AffineVariety.tangentSpace, Submodule.mem_iInf] at hd
    exact hd ⟨f, hE f hf⟩
  have htandim : Module.finrank ℂ (Γ.tangentSpace w) = V.dimension + 1 := by
    rw [hΓsmooth.2, Γ.localDimension_eq_dimension _ hΓ hw, hdim]
  have heq : Γ.tangentSpace w = K :=
    Submodule.eq_of_le_of_finrank_le htan (by rw [htandim]; exact hKdim)
  have hmap : (Γ.tangentSpace w).map π ≤ T := by
    rintro d ⟨u, hu, rfl⟩
    exact hproj u (htan hu)
  let q := π.comp (Γ.tangentSpace w).subtype
  let r := (β.comp (Γ.tangentSpace w).subtype).comp (LinearMap.ker q).subtype
  have hr : Function.Injective r := by
    intro d d' hd
    apply Subtype.ext
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hvertical (d.val.val - d'.val.val)
      (K.sub_mem (htan d.val.property) (htan d'.val.property))
    · change firstPoint d.val.val - firstPoint d'.val.val = 0
      have hd0 : firstPoint d.val.val = 0 := LinearMap.mem_ker.mp d.property
      have hd'0 : firstPoint d'.val.val = 0 := LinearMap.mem_ker.mp d'.property
      rw [hd0, hd'0, sub_self]
    · change d.val.val (Fin.natAdd n b) - d'.val.val (Fin.natAdd n b) = 0
      exact sub_eq_zero.mpr hd
  have hkerdim : Module.finrank ℂ (LinearMap.ker q) ≤ 1 := by
    simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective hr
  have hrank := LinearMap.finrank_range_add_finrank_ker q
  change Module.finrank ℂ (LinearMap.range (π.comp (Γ.tangentSpace w).subtype)) +
    Module.finrank ℂ (LinearMap.ker q) = Module.finrank ℂ (Γ.tangentSpace w) at hrank
  rw [LinearMap.range_comp, Submodule.range_subtype, htandim] at hrank
  have hmapdim : V.dimension ≤ Module.finrank ℂ ((Γ.tangentSpace w).map π) := by omega
  exact ⟨hΓsmooth, heq, Submodule.eq_of_le_of_finrank_le hmap (by rw [hTdim]; exact hmapdim)⟩

def lineGraphEquations {n e c : ℕ} (g : Fin c → Poly n) (δ : Poly n)
    (B A : Fin e → Poly n) (b : Fin e) : List (Poly (n + e)) :=
  List.ofFn (fun i => MvPolynomial.rename (Fin.castAdd e) (g i)) ++
    ((Finset.univ.erase b).toList.map fun i => graphEquationPolynomial δ (B i) (A i) b i)

theorem lineGraphEquations_base_mem {n e c : ℕ} (g : Fin c → Poly n) (δ : Poly n)
    (B A : Fin e → Poly n) (b : Fin e) (i : Fin c) :
    MvPolynomial.rename (Fin.castAdd e) (g i) ∈ lineGraphEquations g δ B A b := by
  simp only [lineGraphEquations, List.mem_append, List.mem_ofFn]
  exact Or.inl ⟨i, rfl⟩

theorem lineGraphEquations_graph_mem {n e c : ℕ} (g : Fin c → Poly n) (δ : Poly n)
    (B A : Fin e → Poly n) (b i : Fin e) (hi : i ≠ b) :
    graphEquationPolynomial δ (B i) (A i) b i ∈ lineGraphEquations g δ B A b := by
  simp only [lineGraphEquations, List.mem_append, List.mem_map, Finset.mem_toList,
    Finset.mem_erase, Finset.mem_univ, and_true]
  exact Or.inr ⟨i, hi, rfl⟩

theorem lineGraphEquations_length {n e c : ℕ} (g : Fin c → Poly n) (δ : Poly n)
    (B A : Fin e → Poly n) (b : Fin e) : (lineGraphEquations g δ B A b).length = c + e - 1 := by
  simp only [lineGraphEquations, List.length_append, List.length_ofFn, List.length_map,
    Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin]
  have := b.isLt
  omega

theorem line_graph_equation_kernel_vertical {n e c : ℕ} (g : Fin c → Poly n)
    (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e) (w : Point (n + e))
    (hδ : MvPolynomial.aeval (firstPoint w) δ ≠ 0) (d : Point (n + e))
    (hd : d ∈ LinearMap.ker (TrackA.evaluatedJacobian (lineGraphEquations g δ B A b) w).mulVecLin)
    (hbase : firstPoint d = 0) (hb : secondPoint d b = 0) : d = 0 := by
  have hd' := (evaluatedJacobian_ker_iff _ w d).mp hd
  have hsecond : secondPoint d = 0 := by
    funext i
    by_cases hi : i = b
    · simpa only [hi, Pi.zero_apply] using hb
    · have h := hd' _ (lineGraphEquations_graph_mem g δ B A b i hi)
      rw [differential_graphEquation_vertical δ (B i) (A i) b i w d hbase, hb,
        mul_zero, sub_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hδ
  funext i
  refine Fin.addCases (fun j => congrFun hbase j) (fun j => congrFun hsecond j) i

theorem line_graph_equation_kernel_projection {n e c : ℕ} (V : AffineVariety n)
    (g : Fin c → Poly n) (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e) (w : Point (n + e))
    (htan : V.tangentSpace (firstPoint w) = ⨅ i : Fin c, LinearMap.ker (differential (g i) (firstPoint w)))
    (d : Point (n + e))
    (hd : d ∈ LinearMap.ker (TrackA.evaluatedJacobian (lineGraphEquations g δ B A b) w).mulVecLin) :
    firstPoint d ∈ V.tangentSpace (firstPoint w) := by
  rw [htan, Submodule.mem_iInf]
  intro i
  have h := (evaluatedJacobian_ker_iff _ w d).mp hd _ (lineGraphEquations_base_mem g δ B A b i)
  rwa [differential_base_rename] at h

theorem lineGraphEquations_mem_ideal {n e c : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (H : Poly n) (hH : H ∉ V.ideal) (v : Fin e → Polynomial (PrincipalCoordinateRing V H))
    (g : Fin c → Poly n) (hg : ∀ i, g i ∈ V.ideal) (δ : Poly n) (B A : Fin e → Poly n) (b : Fin e)
    (hgraph : ∀ i, Polynomial.C (principalCoordinateMap V H δ) * v i =
      Polynomial.C (principalCoordinateMap V H (B i)) + Polynomial.C (principalCoordinateMap V H (A i)) * v b) :
    ∀ f ∈ lineGraphEquations g δ B A b, f ∈ (lineGraphVariety V H hH v).ideal := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact baseEquation_mem_lineGraph V H hH v _ (hg i)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    exact graphEquation_mem_lineGraph V H hH v δ (B i) (A i) b i (hgraph i)


theorem lineGraphVariety_smooth_tangent {n e c : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (hcodim : V.dimension + c = n) (H : Poly n) (hH : H ∉ V.ideal)
    (v : Fin e → Polynomial (PrincipalCoordinateRing V H)) (b : Fin e) (hb : v b = Polynomial.X)
    (g : Fin c → Poly n) (hg : ∀ i, g i ∈ V.ideal) (δ : Poly n) (B A : Fin e → Poly n)
    (hgraph : ∀ i, Polynomial.C (principalCoordinateMap V H δ) * v i =
      Polynomial.C (principalCoordinateMap V H (B i)) + Polynomial.C (principalCoordinateMap V H (A i)) * v b)
    (w : Point (n + e)) (hw : w ∈ (lineGraphVariety V H hH v).points)
    (hsmooth : V.IsSmoothAt (firstPoint w))
    (htan : V.tangentSpace (firstPoint w) = ⨅ i : Fin c, LinearMap.ker (differential (g i) (firstPoint w)))
    (hδ : MvPolynomial.aeval (firstPoint w) δ ≠ 0) :
    let Γ := lineGraphVariety V H hH v
    Γ.IsSmoothAt w ∧ Γ.tangentSpace w =
      LinearMap.ker (TrackA.evaluatedJacobian (lineGraphEquations g δ B A b) w).mulVecLin ∧
      (Γ.tangentSpace w).map (basePointProjection n e) = V.tangentSpace (firstPoint w) := by
  let Γ := lineGraphVariety V H hH v
  let E := lineGraphEquations g δ B A b
  apply smooth_line_tangent_projection_of_equation_kernel V Γ
    (show V.IsIrreducible from (inferInstance : V.ideal.IsPrime))
    (lineGraphVariety_irreducible V H hH v) (lineGraphVariety_dimension V H hH v b hb) E
  · rw [lineGraphEquations_length]
    have := b.isLt
    omega
  · exact lineGraphEquations_mem_ideal V H hH v g hg δ B A b hgraph
  · exact hw
  · exact lineGraphVariety_point_containment V H hH v w hw
  · exact hsmooth
  · exact line_graph_equation_kernel_projection V g δ B A b w htan
  · exact line_graph_equation_kernel_vertical g δ B A b w hδ

theorem line_horizontal_tangent_of_tests {e c : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (g : Fin c → Poly (skewDim e)) (W : Fin e → Fin e → Poly (skewDim e)) (a b : Fin e)
    (w : Point (skewDim e + e))
    (htan : Γ.tangentSpace w = LinearMap.ker
      (TrackA.evaluatedJacobian (lineGraphEquations g (W a b) (fun l => W l b) (fun l => W a l) b) w).mulVecLin)
    (hbase : V.tangentSpace (firstPoint w) = ⨅ l : Fin c, LinearMap.ker (differential (g l) (firstPoint w)))
    (hδ : MvPolynomial.aeval (firstPoint w) (W a b) ≠ 0)
    (hgraph : ∀ l, MvPolynomial.aeval (firstPoint w) (W l b) +
      secondPoint w b * MvPolynomial.aeval (firstPoint w) (W a l) =
        MvPolynomial.aeval (firstPoint w) (W a b) * secondPoint w l)
    (i j : Fin e)
    (hkernel : C.decode.symm (normalizedKernelPair a (secondPoint w) i j) ∈ V.tangentSpace (firstPoint w))
    (hfirst : ∀ l, (firstHorizontalTest C W a b i j l).eval₂
      (MvPolynomial.aeval (firstPoint w)).toRingHom (secondPoint w b) = 0) :
    joinPoints (C.decode.symm (normalizedKernelPair a (secondPoint w) i j)) 0 ∈ Γ.tangentSpace w := by
  let d := C.decode.symm (normalizedKernelPair a (secondPoint w) i j)
  let u := joinPoints d (0 : Point e)
  have hufirst : firstPoint u = d := by ext l; simp [u, firstPoint, joinPoints]
  have husecond : secondPoint u = 0 := by ext l; simp [u, secondPoint, joinPoints]
  have hg : ∀ l : Fin c, differential (g l) (firstPoint w) d = 0 := by
    rw [hbase, Submodule.mem_iInf] at hkernel
    exact hkernel
  have hF (l : Fin e) : differential (W l b + MvPolynomial.C (secondPoint w b) * W a l -
      MvPolynomial.C (secondPoint w l) * W a b) (firstPoint w) d = 0 := by
    have h := hfirst l
    rw [eval_firstHorizontalTest C W a b i j l (firstPoint w) (secondPoint w) hgraph] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hδ)
  rw [htan]
  apply (evaluatedJacobian_ker_iff _ w u).mpr
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hf
    rw [differential_base_rename, hufirst]
    exact hg l
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
    rw [differential_graphEquation_horizontal (W a b) (W l b) (W a l) b l w u husecond,
      hufirst, hF l, neg_zero]

theorem codimension_one_of_proportional_differentials {n c : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hcodim : V.dimension + c = n) (hc : 0 < c)
    (g : Fin c → Poly n) (x : Point n) (hx : x ∈ V.points) (hsmooth : V.IsSmoothAt x)
    (htan : V.tangentSpace x = ⨅ i : Fin c, LinearMap.ker (differential (g i) x))
    (α : Point n →ₗ[ℂ] ℂ) (s : Fin c → ℂ) (hprop : ∀ i, differential (g i) x = s i • α) : c = 1 := by
  have hker : LinearMap.ker α ≤ V.tangentSpace x := by
    intro d hd
    rw [htan, Submodule.mem_iInf]
    intro i
    rw [LinearMap.mem_ker, hprop i, LinearMap.smul_apply, LinearMap.mem_ker.mp hd, smul_zero]
  have hTdim : Module.finrank ℂ (V.tangentSpace x) = V.dimension :=
    hsmooth.2.trans (V.localDimension_eq_dimension x hV hx)
  have hKdim : Module.finrank ℂ (LinearMap.ker α) ≤ V.dimension := by
    rw [← hTdim]
    exact Submodule.finrank_mono hker
  have hRdim : Module.finrank ℂ (LinearMap.range α) ≤ 1 := by
    simpa only [Module.finrank_self] using Submodule.finrank_le (LinearMap.range α)
  have hdim := LinearMap.finrank_range_add_finrank_ker α
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  omega

theorem differential_proportional_of_normalPolynomial {e c : ℕ} (C : SkewCoordinates e)
    (g : Fin c → Poly (skewDim e)) (f : Poly (skewDim e)) (x : Point (skewDim e)) (s : Fin c → ℂ)
    (hprop : ∀ l i j, MvPolynomial.aeval x (normalPolynomial C (g l) i j) =
      s l * MvPolynomial.aeval x (normalPolynomial C f i j)) :
    ∀ l, differential (g l) x = s l • differential f x := by
  intro l
  have hrel : (differential (g l) x).comp C.decode.symm.toLinearMap =
      s l • ((differential f x).comp C.decode.symm.toLinearMap) := by
    apply normalCoordinates_injective e
    funext i j
    change normalCoordinates ((differential (g l) x).comp C.decode.symm.toLinearMap) i j =
      s l * normalCoordinates ((differential f x).comp C.decode.symm.toLinearMap) i j
    rw [← eval_normalPolynomial, ← eval_normalPolynomial]
    exact hprop l i j
  apply LinearMap.ext
  intro d
  have h := LinearMap.congr_fun hrel (C.decode d)
  change differential (g l) x (C.decode.symm (C.decode d)) =
    s l • differential f x (C.decode.symm (C.decode d)) at h
  rw [C.decode.symm_apply_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
theorem line_chart_codimension_one {e c : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (hV : V.IsIrreducible) (hcodim : V.dimension + c = skewDim e) (hc : 0 < c)
    (g : Fin c → Poly (skewDim e)) (f : Poly (skewDim e)) (x : Point (skewDim e))
    (hx : x ∈ V.points) (hsmooth : V.IsSmoothAt x)
    (htan : V.tangentSpace x = ⨅ i : Fin c, LinearMap.ker (differential (g i) x)) (a b : Fin e)
    (hδ : MvPolynomial.aeval x (normalPolynomial C f a b) ≠ 0)
    (hself : ∀ i j, directionResidualConstant
      (fun k l => MvPolynomial.aeval x (normalPolynomial C f k l))
      (fun k l => MvPolynomial.aeval x (normalPolynomial C f k l)) a b i j = 0)
    (hzero : ∀ t : Fin c, ∀ i j, directionResidualConstant
      (fun k l => MvPolynomial.aeval x (normalPolynomial C f k l))
      (fun k l => MvPolynomial.aeval x (normalPolynomial C (g t) k l)) a b i j = 0)
    (hlinear : ∀ t : Fin c, ∀ i j, directionResidualLinear
      (fun k l => MvPolynomial.aeval x (normalPolynomial C f k l))
      (fun k l => MvPolynomial.aeval x (normalPolynomial C (g t) k l)) a b i j = 0) : c = 1 := by
  let s : Fin c → ℂ := fun l => MvPolynomial.aeval x (normalPolynomial C (g l) a b) /
    MvPolynomial.aeval x (normalPolynomial C f a b)
  apply codimension_one_of_proportional_differentials V hV hcodim hc g x hx hsmooth htan
    (differential f x) s
  apply differential_proportional_of_normalPolynomial C g f x s
  intro l i j
  change MvPolynomial.aeval x (normalPolynomial C (g l) i j) =
    (MvPolynomial.aeval x (normalPolynomial C (g l) a b) /
      MvPolynomial.aeval x (normalPolynomial C f a b)) * MvPolynomial.aeval x (normalPolynomial C f i j)
  exact direction_line_normals_proportional (K := ℂ)
    (fun k l => MvPolynomial.aeval x (normalPolynomial C f k l))
    (fun k j => MvPolynomial.aeval x (normalPolynomial C (g l) k j))
    a b hδ hself (hzero l) (hlinear l) i j


theorem eval_nonzero_of_dvd {n : ℕ} (f H : Poly n) (hf : f ∣ H) (z : Point n)
    (hH : MvPolynomial.aeval z H ≠ 0) : MvPolynomial.aeval z f ≠ 0 := by
  obtain ⟨q, rfl⟩ := hf
  rw [map_mul] at hH
  exact (mul_ne_zero_iff.mp hH).1

theorem exists_principal_open_point {n : ℕ} (V : AffineVariety n) (H : Poly n)
    (hH : H ∉ V.ideal) : ∃ z ∈ V.points, MvPolynomial.aeval z H ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hH
  rw [← V.vanishingIdeal_points]
  exact hn

theorem map_coordinate_zero_at_point {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (p : Polynomial (Poly n)) (hp : p.map (coordinateMap V) = 0)
    (z : Point n) (hz : z ∈ V.points) : p.map (MvPolynomial.aeval z).toRingHom = 0 := by
  ext r
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  have h := congrArg (fun q : Polynomial (CarrierField V) => q.coeff r) hp
  rw [Polynomial.coeff_map, Polynomial.coeff_zero] at h
  exact hz _ ((coordinateMap_eq_zero_iff V _).mp h)

theorem eval_parameter_zero_at_point {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (p : Polynomial (Poly n)) (hp : p.map (coordinateMap V) = 0)
    (z : Point n) (hz : z ∈ V.points) (t : ℂ) : p.eval₂ (MvPolynomial.aeval z).toRingHom t = 0 := by
  have h := map_coordinate_zero_at_point V p hp z hz
  have he : p.eval₂ (MvPolynomial.aeval z).toRingHom t =
      (p.map (MvPolynomial.aeval z).toRingHom).eval t := (Polynomial.eval_map _ _).symm
  rw [he, h, Polynomial.eval_zero]

theorem residual_mapped_zero_at_point {n e : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (W U : Fin e → Fin e → Poly n) (a b i j : Fin e)
    (hzero : (residualParameterPolynomial W U a b i j).map (coordinateMap V) = 0)
    (z : Point n) (hz : z ∈ V.points) :
    directionResidualConstant (fun k l => MvPolynomial.aeval z (W k l))
      (fun k l => MvPolynomial.aeval z (U k l)) a b i j = 0 ∧
    directionResidualLinear (fun k l => MvPolynomial.aeval z (W k l))
      (fun k l => MvPolynomial.aeval z (U k l)) a b i j = 0 := by
  have h0 := eval_parameter_zero_at_point V _ hzero z hz 0
  have h1 := eval_parameter_zero_at_point V _ hzero z hz 1
  rw [eval_residualParameterPolynomial, zero_mul, add_zero] at h0
  rw [eval_residualParameterPolynomial, one_mul, h0, zero_add] at h1
  exact ⟨h0, h1⟩

theorem directionGraph_of_cleared_equations {e : ℕ} (W : Fin e → Fin e → ℂ)
    (a b : Fin e) (hδ : W a b ≠ 0) (v : Point e)
    (hgraph : ∀ i, W a b * v i = W i b + W a i * v b) : v = directionGraph W a b (v b) := by
  funext i
  dsimp [directionGraph]
  apply (eq_div_iff hδ).mpr
  have h := hgraph i
  linear_combination h

theorem normalized_kernel_tangent_of_constraints {e c : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (g : Fin c → Poly (skewDim e)) (x : Point (skewDim e))
    (htan : V.tangentSpace x = ⨅ l : Fin c, LinearMap.ker (differential (g l) x))
    (a : Fin e) (v : Point e) (hva : v a = 1)
    (hconstraints : ∀ l, SkewChartConstraints (fun i j => MvPolynomial.aeval x (normalPolynomial C (g l) i j)) a v)
    (i j : Fin e) : C.decode.symm (normalizedKernelPair a v i j) ∈ V.tangentSpace x := by
  rw [htan, Submodule.mem_iInf]
  intro l
  let α := (differential (g l) x).comp C.decode.symm.toLinearMap
  have hc : SkewChartConstraints (normalCoordinates α) a v := by
    simpa only [eval_normalPolynomial] using hconstraints l
  have hker := (annihilates_skew_kernel_iff α a v hva).mpr hc
  have hd : normalizedKernelPair a v i j ∈ LinearMap.ker (alternatingEvaluation v) :=
    normalizedDirectionPullback_eval_zero a v hva (coordinateSkewPair e i j)
  exact hker hd


theorem point_mem_cut_iff {n : ℕ} (V : AffineVariety n) (f : Poly n) (x : Point n) :
    x ∈ (V.cut f).points ↔ x ∈ V.points ∧ MvPolynomial.aeval x f = 0 := by
  have hle : V.ideal ⊔ Ideal.span {f} ≤ (V.cut f).ideal := Ideal.le_radical
  constructor
  · intro hx
    refine ⟨fun g hg => hx g (hle ((le_sup_left : V.ideal ≤ V.ideal ⊔ Ideal.span {f}) hg)), ?_⟩
    exact hx f (hle ((le_sup_right : Ideal.span {f} ≤ V.ideal ⊔ Ideal.span {f})
      (Ideal.subset_span (Set.mem_singleton f))))
  · rintro ⟨hx, hf⟩
    have hker : V.ideal ⊔ Ideal.span {f} ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
      apply sup_le
      · exact hx
      · apply Ideal.span_le.mpr
        intro g hg
        have heq := Set.mem_singleton_iff.mp hg
        subst g
        exact hf
    intro g hg
    obtain ⟨r, hr⟩ := Ideal.mem_radical_iff.mp hg
    have hz : MvPolynomial.aeval x g ^ r = 0 := by
      rw [← map_pow]
      exact hker hr
    exact eq_zero_of_pow_eq_zero hz

theorem rulingIncidence_restrict_bound {e : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H G : Poly (skewDim e)) (a : Fin e) (j M N : ℕ)
    (F : IsRulingIncidence C V Γ H a j M) (hHG : H ∣ G) (hG : G ∉ V.ideal)
    (hMN : M ≤ N) (hN : 1 ≤ N) : IsRulingIncidence C V Γ G a j N := by
  have hworking : workingPoints V G ⊆ workingPoints V H := by
    intro z hz
    exact ⟨hz.1, eval_nonzero_of_dvd H G hHG z hz.2⟩
  have hruling : rulingPoints Γ G ⊆ rulingPoints Γ H := by
    intro w hw
    exact ⟨hw.1, eval_nonzero_of_dvd H G hHG (firstPoint w) hw.2⟩
  have himage : parameterImage C Γ G ⊆ parameterImage C Γ H := by
    rintro p ⟨z,v,hz,hv,hp⟩
    exact ⟨z,v,hruling hz,hv,hp⟩
  refine
    { variety_irreducible := F.variety_irreducible
      incidence_irreducible := F.incidence_irreducible
      nonzero_section := hG
      fiber_cases := F.fiber_cases
      bound_positive := hN
      incidence_dimension := F.incidence_dimension
      normalized := F.normalized
      point_containment := F.point_containment
      dominant := fun z hz => F.dominant z (hworking hz)
      smooth := fun w hw => F.smooth w (hruling hw)
      finite_fiber := fun hj z hz => ⟨(F.finite_fiber hj z (hworking hz)).1,
        (F.finite_fiber hj z (hworking hz)).2.trans hMN⟩
      line_fiber := fun hj z hz => F.line_fiber hj z (hworking hz)
      codimension_one := F.codimension_one
      actual_flats := fun z v hz hv => F.actual_flats z v (hruling hz) hv
      full_parameter_fibers := ?_ }
  intro p hp z hz
  have h := F.full_parameter_fibers p (himage hp) z (hworking hz)
  constructor
  · intro hflat
    obtain ⟨v,hv,hv0,hp⟩ := h.mp hflat
    refine ⟨v, ⟨hv.1, ?_⟩, hv0, hp⟩
    have hfirst : firstPoint (joinPoints z v) = z := by ext i; simp [firstPoint,joinPoints]
    rw [hfirst]
    exact hz.2
  · rintro ⟨v,hv,hv0,hp⟩
    exact h.mpr ⟨v,hruling hv,hv0,hp⟩

theorem ruling_lifted_section_nonzero {e : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (j N : ℕ) (F : IsRulingIncidence C V Γ H a j N) :
    MvPolynomial.rename (Fin.castAdd e) H ∉ Γ.ideal := by
  obtain ⟨z,hz,hzH⟩ := exists_principal_open_point V H F.nonzero_section
  obtain ⟨v,hv⟩ := F.dominant z ⟨hz,hzH⟩
  intro hmem
  have hx : joinPoints z v ∈ Γ.points := hv
  have he := hx _ hmem
  rw [MvPolynomial.aeval_rename] at he
  change MvPolynomial.aeval (firstPoint (joinPoints z v)) H = 0 at he
  have hfirst : firstPoint (joinPoints z v) = z := by ext i; simp [firstPoint,joinPoints]
  rw [hfirst] at he
  exact hzH he

theorem ruling_parameter_closure_irreducible {e : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (j N : ℕ) (F : IsRulingIncidence C V Γ H a j N) :
    (parameterClosure C Γ H).IsIrreducible :=
  parameterClosure_irreducible_of_normalized C Γ F.incidence_irreducible H
    (ruling_lifted_section_nonzero C V Γ H a j N F) a F.normalized

structure ControlledChart {e : ℕ} (C : SkewCoordinates e) (V : AffineVariety (skewDim e))
    (a : Fin e) (M : ℕ) (L : ℝ) where
  exceptional : Poly (skewDim e)
  section_nonzero : exceptional ∉ V.ideal
  section_degree : (exceptional.totalDegree : ℝ) ≤ L
  size : ℕ
  size_bound : size ≤ M
  incidences : Fin size → AffineVariety (skewDim e + e)
  fiber_dimensions : Fin size → ℕ
  properties : ∀ i, IsRulingIncidence C V (incidences i) exceptional a (fiber_dimensions i) M
  coverage : ∀ p ∈ affineParameters e, firstPoint p.rep a ≠ 0 → evaluationFlat C p ⊆ V.points →
    evaluationFlat C p ⊆ (V.cut exceptional).points ∨ ∃ i, p ∈ parameterImage C (incidences i) exceptional

theorem controlled_chart_union {e : ℕ} (C : SkewCoordinates e) (V : AffineVariety (skewDim e))
    (hV : V.IsIrreducible) (M : ℕ) (L : ℝ) (F : ∀ a : Fin e, ControlledChart C V a M L) :
    Nonempty (ControlledRulings C V ((e + 1) * M + 1) ((e : ℝ) * L)) := by
  letI : V.ideal.IsPrime := hV
  let H := ∏ a : Fin e, (F a).exceptional
  have hH : H ∉ V.ideal := by
    intro hmem
    have hz := (coordinateMap_eq_zero_iff V H).mpr hmem
    have hproper (a : Fin e) : coordinateMap V (F a).exceptional ≠ 0 := by
      intro ha
      exact (F a).section_nonzero ((coordinateMap_eq_zero_iff V _).mp ha)
    dsimp [H] at hz
    rw [map_prod] at hz
    exact (Finset.prod_ne_zero_iff.mpr (fun a ha => hproper a)) hz
  have hHdeg : (H.totalDegree : ℝ) ≤ (e : ℝ) * L := by
    have hnat := MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin e)) (fun a => (F a).exceptional)
    have hreal : (H.totalDegree : ℝ) ≤ ∑ a : Fin e, ((F a).exceptional.totalDegree : ℝ) := by exact_mod_cast hnat
    apply hreal.trans
    have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin e))) => (F a).section_degree)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs
  have hdiv (a : Fin e) : (F a).exceptional ∣ H := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
  let I := Σ a : Fin e, Fin (F a).size
  let s := Fintype.card I
  let η : Fin s ≃ I := (Fintype.equivFin I).symm
  let N := (e + 1) * M + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hMN : M ≤ N := by dsimp [N]; nlinarith
  have hs : s ≤ N := by
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin e))) => (F a).size_bound)
    have hcard : s ≤ e * M := by simpa [s,I,Fintype.card_sigma] using hsum
    dsimp [N]
    nlinarith
  have hprops (i : Fin s) : IsRulingIncidence C V ((F (η i).1).incidences (η i).2)
      H (η i).1 ((F (η i).1).fiber_dimensions (η i).2) N :=
    rulingIncidence_restrict_bound C V _ _ H _ _ M N ((F (η i).1).properties (η i).2)
      (hdiv (η i).1) hH hMN hN
  refine ⟨
    { exceptional := H
      section_nonzero := hH
      section_degree := hHdeg
      size := s
      size_bound := hs
      incidences := fun i => (F (η i).1).incidences (η i).2
      charts := fun i => (η i).1
      fiber_dimensions := fun i => (F (η i).1).fiber_dimensions (η i).2
      properties := hprops
      parameter_irreducible := ?_
      coverage := ?_ }⟩
  · intro i
    exact ruling_parameter_closure_irreducible C V _ H _ _ N (hprops i)
  · intro p hp hflat
    by_cases hcut : evaluationFlat C p ⊆ (V.cut H).points
    · exact Or.inl hcut
    have hpoint : ∃ z ∈ evaluationFlat C p, MvPolynomial.aeval z H ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hcut
      intro z hz
      exact (point_mem_cut_iff V H z).mpr ⟨hflat hz, hn z hz⟩
    obtain ⟨z,hz,hzH⟩ := hpoint
    have ha : ∃ a : Fin e, firstPoint p.rep a ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hp.2
      exact funext hn
    obtain ⟨a,ha⟩ := ha
    have hzHa := eval_nonzero_of_dvd (F a).exceptional H (hdiv a) z hzH
    rcases (F a).coverage p hp ha hflat with hbad | hgood
    · exact (hzHa ((point_mem_cut_iff V (F a).exceptional z).mp (hbad hz)).2).elim
    · obtain ⟨k,hk⟩ := hgood
      let i := η.symm ⟨a,k⟩
      have hη : η i = ⟨a,k⟩ := η.apply_symm_apply _
      have hfull := ((F a).properties k).full_parameter_fibers p hk z ⟨hflat hz,hzHa⟩
      obtain ⟨v,hv,hv0,hparam⟩ := hfull.mp hz
      refine Or.inr ⟨i, ?_⟩
      change p ∈ parameterImage C ((F (η i).1).incidences (η i).2) H
      rw [hη]
      refine ⟨z,v,⟨hv.1,?_⟩,hv0,hparam⟩
      have hfirst : firstPoint (joinPoints z v) = z := by ext j; simp [firstPoint,joinPoints]
      rw [hfirst]
      exact hzH


set_option maxHeartbeats 2400000 in
theorem all_zero_controlled_chart {e c D : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) [V.ideal.IsPrime] (hV : V.IsIrreducible) (hcodim : V.dimension + c = skewDim e)
    (g : Fin c → Poly (skewDim e)) (first : Fin c)
    (hg : ∀ i, g i ∈ V.ideal ∧ (g i).totalDegree ≤ D)
    (H0 : Poly (skewDim e)) (hH0 : H0 ∉ V.ideal) (hH0deg : H0.totalDegree ≤ D)
    (hregular : ∀ z ∈ V.points, MvPolynomial.eval z H0 ≠ 0 →
      V.IsSmoothAt z ∧ V.tangentSpace z = ⨅ i : Fin c, LinearMap.ker (differential (g i) z))
    (a b : Fin e) (hδ : normalPolynomial C (g first) a b ∉ V.ideal)
    (hresidual : ∀ l i j, (residualParameterPolynomial (normalPolynomial C (g first))
      (normalPolynomial C (g l)) a b i j).map (coordinateMap V) = 0)
    (hfirst : ∀ i j l, (firstHorizontalTest C (normalPolynomial C (g first)) a b i j l).map
      (coordinateMap V) = 0) : Nonempty (ControlledChart C V a 2 (2 * (D : ℝ))) := by
  letI : V.ideal.IsPrime := hV
  let W := normalPolynomial C (g first)
  let δ := W a b
  let H := H0 * δ
  have hH : H ∉ V.ideal := by
    intro hm
    rcases hV.mem_or_mem hm with h | h
    · exact hH0 h
    · exact hδ h
  have hδdiv : δ ∣ H := ⟨H0, by dsimp [H]; ring⟩
  have hH0div : H0 ∣ H := ⟨δ,rfl⟩
  have hHdeg : (H.totalDegree : ℝ) ≤ 2 * (D : ℝ) := by
    have hδdeg : δ.totalDegree ≤ D :=
      (normalPolynomial_degree_le C (g first) D (hg first).2 a b).trans (Nat.sub_le _ _)
    have hdeg := (MvPolynomial.totalDegree_mul H0 δ).trans (Nat.add_le_add hH0deg hδdeg)
    have hdeg' : H.totalDegree ≤ 2 * D := by simpa only [two_mul] using hdeg
    exact_mod_cast hdeg'
  let B : Fin e → Poly (skewDim e) := fun i => W i b
  let A : Fin e → Poly (skewDim e) := fun i => W a i
  let v := affineLineDirection V H δ B A
  let Γ := lineGraphVariety V H hH v
  have hBb : B b = 0 := normalPolynomial_self C (g first) b
  have hAb : A b = δ := rfl
  have hBa : B a = δ := rfl
  have hAa : A a = 0 := normalPolynomial_self C (g first) a
  have hvb : v b = Polynomial.X := affineLineDirection_root_coordinate V H δ hδdiv B A b hBb hAb
  have hva : v a = 1 := affineLineDirection_normalized V H δ hδdiv B A a hBa hAa
  have hgraph (i : Fin e) : Polynomial.C (principalCoordinateMap V H δ) * v i =
      Polynomial.C (principalCoordinateMap V H (B i)) + Polynomial.C (principalCoordinateMap V H (A i)) * v b := by
    rw [hvb]
    exact affineLineDirection_cleared V H δ hδdiv B A i
  have hnorm : ∀ w ∈ Γ.points, secondPoint w a = 1 :=
    lineGraphVariety_normalized V H hH v a hva
  have hcontain : ∀ w ∈ Γ.points, firstPoint w ∈ V.points := lineGraphVariety_point_containment V H hH v
  have hreg (z : Point (skewDim e)) (hz : z ∈ V.points) (hzH : MvPolynomial.aeval z H ≠ 0) :=
    hregular z hz (by simpa only [MvPolynomial.aeval_eq_eval] using eval_nonzero_of_dvd H0 H hH0div z hzH)
  have hres (z : Point (skewDim e)) (hz : z ∈ V.points) (l : Fin c) (i j : Fin e) :=
    residual_mapped_zero_at_point V W (normalPolynomial C (g l)) a b i j (hresidual l i j) z hz
  have hpoint_graph (w : Point (skewDim e + e)) (hw : w ∈ Γ.points) (i : Fin e) :
      MvPolynomial.aeval (firstPoint w) δ * secondPoint w i =
        MvPolynomial.aeval (firstPoint w) (B i) + MvPolynomial.aeval (firstPoint w) (A i) * secondPoint w b :=
    lineGraphVariety_graph_coordinate V H hH v δ (B i) (A i) b i (hgraph i) w hw
  have hsm (w : Point (skewDim e + e)) (hw : w ∈ rulingPoints Γ H) :=
    lineGraphVariety_smooth_tangent V hcodim H hH v b hvb g (fun i => (hg i).1) δ B A hgraph w hw.1
      (hreg (firstPoint w) (hcontain w hw.1) hw.2).1
      (hreg (firstPoint w) (hcontain w hw.1) hw.2).2
      (eval_nonzero_of_dvd δ H hδdiv (firstPoint w) hw.2)
  have hhorizontal : ∀ w ∈ rulingPoints Γ H, ∀ i j : Fin e,
      joinPoints (C.decode.symm (normalizedKernelPair a (secondPoint w) i j)) 0 ∈ Γ.tangentSpace w := by
    intro w hw i j
    let x := firstPoint w
    let u := secondPoint w
    have hx := hcontain w hw.1
    have hpivot := eval_nonzero_of_dvd δ H hδdiv x hw.2
    have hvalgraph (l : Fin e) : MvPolynomial.aeval x δ * u l =
        MvPolynomial.aeval x (W l b) + MvPolynomial.aeval x (W a l) * u b := hpoint_graph w hw.1 l
    have hugraph : u = directionGraph (fun k l => MvPolynomial.aeval x (W k l)) a b (u b) :=
      directionGraph_of_cleared_equations _ a b hpivot u hvalgraph
    have hconstraints (l : Fin c) : SkewChartConstraints
        (fun k m => MvPolynomial.aeval x (normalPolynomial C (g l) k m)) a u := by
      rw [hugraph]
      apply (directionGraph_constraints_iff (K := ℂ) _ _ a b hpivot (u b)).mpr
      intro k m
      rw [(hres x hx l k m).1, (hres x hx l k m).2, mul_zero, add_zero]
    have hk := normalized_kernel_tangent_of_constraints C V g x (hreg x hx hw.2).2 a u
      (hnorm w hw.1) hconstraints i j
    have hrelation (l : Fin e) : MvPolynomial.aeval x (W l b) +
        u b * MvPolynomial.aeval x (W a l) = MvPolynomial.aeval x δ * u l := by
      have h := hvalgraph l
      linear_combination -h
    exact line_horizontal_tangent_of_tests C V Γ g W a b w (hsm w hw).2.1 (hreg x hx hw.2).2
      hpivot hrelation i j hk (fun l => eval_parameter_zero_at_point V _ (hfirst i j l) x hx (u b))
  obtain ⟨z,hz,hzH⟩ := exists_principal_open_point V H hH
  have hc : 0 < c := by have := first.isLt; omega
  have hc1 : c = 1 := line_chart_codimension_one C V hV hcodim hc g (g first) z hz
    (hreg z hz hzH).1 (hreg z hz hzH).2 a b (eval_nonzero_of_dvd δ H hδdiv z hzH)
    (fun i j => (hres z hz first i j).1) (fun l i j => (hres z hz l i j).1)
    (fun l i j => (hres z hz l i j).2)
  have hprops : IsRulingIncidence C V Γ H a 1 2 := by
    apply rulingIncidence_of_horizontal_tangency C V Γ H a 1 2 hV
      (lineGraphVariety_irreducible V H hH v) hH (lineGraphVariety_section_nonzero V H hH v)
      (by decide) (by decide) (lineGraphVariety_dimension V H hH v b hvb) hnorm hcontain
    · intro x hx
      refine ⟨fun l => polynomialCoordinatePoint V H x hx.1
        (by simpa only [MvPolynomial.aeval_eq_eval] using hx.2) 0 (v l), ?_⟩
      exact lineGraphVariety_point V H hH v x hx.1 (by simpa only [MvPolynomial.aeval_eq_eval] using hx.2) 0
    · intro w hw
      exact ⟨(hsm w hw).1, (hreg (firstPoint w) (hcontain w hw.1) hw.2).1, (hsm w hw).2.2⟩
    · intro h
      omega
    · intro h x hx
      exact affine_line_graph_line_fiber V H hH δ hδdiv B A b hBb hAb x hx.1
        (by simpa only [MvPolynomial.aeval_eq_eval] using hx.2) (eval_nonzero_of_dvd δ H hδdiv x hx.2)
    · intro h
      rwa [← hc1]
    · exact hhorizontal
  refine ⟨
    { exceptional := H
      section_nonzero := hH
      section_degree := hHdeg
      size := 1
      size_bound := by decide
      incidences := fun _ => Γ
      fiber_dimensions := fun _ => 1
      properties := fun _ => hprops
      coverage := ?_ }⟩
  intro p hp ha hflat
  by_cases hcut : evaluationFlat C p ⊆ (V.cut H).points
  · exact Or.inl hcut
  have hpoint : ∃ x ∈ evaluationFlat C p, MvPolynomial.aeval x H ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hcut
    intro x hx
    exact (point_mem_cut_iff V H x).mpr ⟨hflat hx,hn x hx⟩
  obtain ⟨x,hx,hxH⟩ := hpoint
  let s := firstPoint p.rep a
  let u : Point e := s⁻¹ • firstPoint p.rep
  have hs : s ≠ 0 := ha
  have hua : u a = 1 := by change s⁻¹ * s = 1; exact inv_mul_cancel₀ hs
  have hu : u ≠ 0 := by intro h; have he := congrFun h a; rw [hua,Pi.zero_apply] at he; exact one_ne_zero he
  have hscale : firstPoint p.rep = s • u := by dsimp [u]; rw [smul_smul,mul_inv_cancel₀ hs,one_smul]
  have hcstr := contained_flat_normal_constraints C p V hflat x hx (g first) (hg first).1 u a hua s hscale
  have hpivot := eval_nonzero_of_dvd δ H hδdiv x hxH
  have hsolve (i : Fin e) : MvPolynomial.aeval x δ * u i =
      MvPolynomial.aeval x (B i) + MvPolynomial.aeval x (A i) * u b := by
    have he := hcstr i b
    linear_combination -he
  have hxΓ := affine_line_graph_solution_coverage V H hH δ hδdiv B A b hBb hAb x (hflat hx)
    (by simpa only [MvPolynomial.aeval_eq_eval] using hxH) hpivot u hsolve
  have hvec : graphVector C x (firstPoint p.rep) = p.rep := by
    change joinPoints (firstPoint p.rep) (pointOfCovector ((C.decode x).val (firstPoint p.rep))) = p.rep
    rw [show (C.decode x).val (firstPoint p.rep) = covectorOfPoint (secondPoint p.rep) from hx,
      point_covector_inverse, joinPoints_eta]
  have hvecu : s⁻¹ • p.rep = graphVector C x u := by
    rw [← hvec]
    change s⁻¹ • joinPoints (firstPoint p.rep) (pointOfCovector ((C.decode x).val (firstPoint p.rep))) =
      joinPoints u (pointOfCovector ((C.decode x).val u))
    dsimp [u]
    rw [map_smul, pointOfCovector_smul, joinPoints_smul]
  have hparam : graphParameter C x u hu = p := by
    rw [← p.mk_rep]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨s⁻¹,hvecu⟩
  refine Or.inr ⟨0, x,u,⟨hxΓ,?_⟩,hu,hparam⟩
  have hpx : firstPoint (joinPoints x u) = x := by ext i; simp [firstPoint,joinPoints]
  rw [hpx]
  exact hxH


theorem first_normal_polynomial_nonzero {e c : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (hV : V.IsIrreducible) (hcodim : V.dimension + c = skewDim e)
    (g : Fin c → Poly (skewDim e)) (first : Fin c) (H0 : Poly (skewDim e)) (hH0 : H0 ∉ V.ideal)
    (hregular : ∀ z ∈ V.points, MvPolynomial.eval z H0 ≠ 0 →
      V.IsSmoothAt z ∧ V.tangentSpace z = ⨅ i : Fin c, LinearMap.ker (differential (g i) z)) :
    ∃ i j, normalPolynomial C (g first) i j ∉ V.ideal := by
  obtain ⟨x,hx,hxH⟩ := exists_principal_open_point V H0 hH0
  obtain ⟨hsm,htan⟩ := hregular x hx (by simpa only [MvPolynomial.aeval_eq_eval] using hxH)
  let J : Point (skewDim e) →ₗ[ℂ] Point c := LinearMap.pi (fun i => differential (g i) x)
  have hker : LinearMap.ker J = V.tangentSpace x := by
    rw [htan]
    ext d
    simp only [LinearMap.mem_ker, Submodule.mem_iInf, funext_iff]
    rfl
  have hdim := LinearMap.finrank_range_add_finrank_ker J
  rw [hker, hsm.2, V.localDimension_eq_dimension x hV hx] at hdim
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  have htop : LinearMap.range J = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  obtain ⟨d,hd⟩ := LinearMap.range_eq_top.mp htop (Pi.single first (1 : ℂ))
  have hrow : differential (g first) x d = 1 := by
    have h := congrFun hd first
    simpa [J] using h
  by_contra hn
  push_neg at hn
  let α := (differential (g first) x).comp C.decode.symm.toLinearMap
  have hα : α = 0 := by
    apply normalCoordinates_injective e
    funext i j
    have hz := hx _ (hn i j)
    rw [eval_normalPolynomial] at hz
    simpa only [normalCoordinates, LinearMap.zero_apply] using hz
  have hzero := LinearMap.congr_fun hα (C.decode d)
  change differential (g first) x (C.decode.symm (C.decode d)) = 0 at hzero
  rw [C.decode.symm_apply_apply, hrow] at hzero
  exact one_ne_zero hzero

theorem empty_controlled_chart {e D : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (hV : V.IsIrreducible)
    (f : Poly (skewDim e)) (hf : f ∈ V.ideal) (hfdeg : f.totalDegree ≤ D)
    (H0 : Poly (skewDim e)) (hH0 : H0 ∉ V.ideal) (hH0deg : H0.totalDegree ≤ D)
    (a i j : Fin e) (hproper : normalPolynomial C f i j ∉ V.ideal)
    (hrow : ∀ b, normalPolynomial C f a b ∈ V.ideal) :
    Nonempty (ControlledChart C V a 2 (2 * (D : ℝ))) := by
  let W := normalPolynomial C f
  let H := H0 * W i j
  have hH : H ∉ V.ideal := by
    intro hm
    rcases hV.mem_or_mem hm with h | h
    · exact hH0 h
    · exact hproper h
  have hdeg : (H.totalDegree : ℝ) ≤ 2 * (D : ℝ) := by
    have hW := (normalPolynomial_degree_le C f D hfdeg i j).trans (Nat.sub_le _ _)
    have hnat : H.totalDegree ≤ 2 * D := by
      have h := (MvPolynomial.totalDegree_mul H0 (W i j)).trans (Nat.add_le_add hH0deg hW)
      simpa only [two_mul] using h
    exact_mod_cast hnat
  refine ⟨
    { exceptional := H
      section_nonzero := hH
      section_degree := hdeg
      size := 0
      size_bound := by decide
      incidences := fun i => Fin.elim0 i
      fiber_dimensions := fun i => Fin.elim0 i
      properties := fun i => Fin.elim0 i
      coverage := ?_ }⟩
  intro p hp ha hflat
  refine Or.inl ?_
  intro x hx
  let s := firstPoint p.rep a
  let v : Point e := s⁻¹ • firstPoint p.rep
  have hs : s ≠ 0 := ha
  have hva : v a = 1 := by change s⁻¹ * s = 1; exact inv_mul_cancel₀ hs
  have hscale : firstPoint p.rep = s • v := by dsimp [v]; rw [smul_smul,mul_inv_cancel₀ hs,one_smul]
  have hc := contained_flat_normal_constraints C p V hflat x hx f hf v a hva s hscale
  have hrowzero (b : Fin e) : MvPolynomial.aeval x (W a b) = 0 := (hflat hx) _ (hrow b)
  have hzero : MvPolynomial.aeval x (W i j) = 0 := by
    have h := hc i j
    change MvPolynomial.aeval x (W i j) =
      v i * MvPolynomial.aeval x (W a j) - v j * MvPolynomial.aeval x (W a i) at h
    rw [hrowzero j,hrowzero i,mul_zero,mul_zero,sub_self] at h
    exact h
  apply (point_mem_cut_iff V H x).mpr
  refine ⟨hflat hx,?_⟩
  simp only [H,map_mul,hzero,mul_zero]

def ControlledChart.mono {e : ℕ} {C : SkewCoordinates e} {V : AffineVariety (skewDim e)}
    {a : Fin e} {M N : ℕ} {L L' : ℝ} (F : ControlledChart C V a M L)
    (hMN : M ≤ N) (hN : 1 ≤ N) (hLL' : L ≤ L') : ControlledChart C V a N L' :=
  { exceptional := F.exceptional
    section_nonzero := F.section_nonzero
    section_degree := F.section_degree.trans hLL'
    size := F.size
    size_bound := F.size_bound.trans hMN
    incidences := F.incidences
    fiber_dimensions := F.fiber_dimensions
    properties := fun i => rulingIncidence_restrict_bound C V _ _ _ a _ M N (F.properties i)
      dvd_rfl F.section_nonzero hMN hN
    coverage := F.coverage }

def ControlledRulings.widen {e : ℕ} {C : SkewCoordinates e} {V : AffineVariety (skewDim e)}
    {M N : ℕ} {L L' : ℝ} (F : ControlledRulings C V M L)
    (hMN : M ≤ N) (hN : 1 ≤ N) (hLL' : L ≤ L') : ControlledRulings C V N L' :=
  { exceptional := F.exceptional
    section_nonzero := F.section_nonzero
    section_degree := F.section_degree.trans hLL'
    size := F.size
    size_bound := F.size_bound.trans hMN
    incidences := F.incidences
    charts := F.charts
    fiber_dimensions := F.fiber_dimensions
    properties := fun i => rulingIncidence_restrict_bound C V _ _ _ _ _ M N (F.properties i)
      dvd_rfl F.section_nonzero hMN hN
    parameter_irreducible := F.parameter_irreducible
    coverage := F.coverage }


theorem parameter_fraction_local_product {n D E J : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (F : ParameterFraction V D) (G : ParameterFraction V E) (T : ParameterFraction V J)
    (H : Poly n) (hH : H ∉ V.ideal)
    (hF : F.denominator ∣ H) (hG : G.denominator ∣ H) (hT : T.denominator ∣ H)
    (hproduct : G.value = F.value * T.value) :
    G.localPolynomial H = F.localPolynomial H * T.localPolynomial H := by
  apply Polynomial.map_injective (principalCarrierMap V H hH).toRingHom (principalCarrierMap_injective V H hH)
  rw [Polynomial.map_mul, G.map_localPolynomial H hH hG, F.map_localPolynomial H hH hF,
    T.map_localPolynomial H hH hT]
  exact hproduct

theorem parameter_fraction_divisible_root_relation {n D E J : ℕ}
    (V : AffineVariety n) [V.ideal.IsPrime]
    (F : ParameterFraction V D) (G : ParameterFraction V E) (T : ParameterFraction V J)
    (H : Poly n) (hH : H ∉ V.ideal)
    (hF : F.denominator ∣ H) (hG : G.denominator ∣ H) (hT : T.denominator ∣ H)
    (hproduct : G.value = F.value * T.value) :
    G.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H)
      (AdjoinRoot (F.localPolynomial H))).comp (principalCoordinateMap V H).toRingHom)
        (AdjoinRoot.root (F.localPolynomial H)) = 0 := by
  have hloc := parameter_fraction_local_product V F G T H hH hF hG hT hproduct
  have hroot := AdjoinRoot.eval₂_root (F.localPolynomial H)
  rw [← AdjoinRoot.algebraMap_eq] at hroot
  have hGroot : (G.localPolynomial H).eval₂
      (algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot (F.localPolynomial H)))
      (AdjoinRoot.root (F.localPolynomial H)) = 0 := by
    rw [hloc, Polynomial.eval₂_mul, hroot, zero_mul]
  have hGroot' : G.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H)
      (AdjoinRoot (F.localPolynomial H))).comp (principalCoordinateMap V H).toRingHom)
        (AdjoinRoot.root (F.localPolynomial H)) *
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot (F.localPolynomial H))
        (Ring.inverse (principalCoordinateMap V H G.denominator)) = 0 := by
    have hGexp : G.localPolynomial H =
        G.numerator.map (principalCoordinateMap V H).toRingHom *
          Polynomial.C (Ring.inverse (principalCoordinateMap V H G.denominator)) := rfl
    have h := hGroot
    rw [hGexp, Polynomial.eval₂_mul, Polynomial.eval₂_map, Polynomial.eval₂_C] at h
    exact h
  have hu := principalCoordinateMap_isUnit_of_dvd V H G.denominator hG
  have hunit : IsUnit (algebraMap (PrincipalCoordinateRing V H)
      (AdjoinRoot (F.localPolynomial H))
        (Ring.inverse (principalCoordinateMap V H G.denominator))) :=
    (hu.ringInverse.map _)
  have hinv : algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot (F.localPolynomial H))
      (Ring.inverse (principalCoordinateMap V H G.denominator)) *
      Ring.inverse (algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot (F.localPolynomial H))
        (Ring.inverse (principalCoordinateMap V H G.denominator))) = 1 :=
    Ring.mul_inverse_cancel _ hunit
  have hzero : (G.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H)
      (AdjoinRoot (F.localPolynomial H))).comp (principalCoordinateMap V H).toRingHom)
        (AdjoinRoot.root (F.localPolynomial H)) *
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot (F.localPolynomial H))
        (Ring.inverse (principalCoordinateMap V H G.denominator))) *
      Ring.inverse (algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot (F.localPolynomial H))
        (Ring.inverse (principalCoordinateMap V H G.denominator))) = 0 := by
    rw [hGroot', zero_mul]
  rw [mul_assoc, hinv, mul_one] at hzero
  exact hzero

theorem polynomial_zero_on_flat_open {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (H q : Poly (skewDim e)) (z : Point (skewDim e))
    (hz : z ∈ evaluationFlat C p) (hzH : MvPolynomial.aeval z H ≠ 0)
    (hq : ∀ x ∈ evaluationFlat C p, MvPolynomial.aeval x H ≠ 0 → MvPolynomial.aeval x q = 0) :
    ∀ x ∈ evaluationFlat C p, MvPolynomial.aeval x q = 0 := by
  let I := MvPolynomial.vanishingIdeal ℂ (evaluationFlat C p)
  letI : I.IsPrime := evaluationFlat_closure_irreducible C p hp
  have hprod : H * q ∈ I := by
    intro x hx
    rw [map_mul]
    by_cases hxH : MvPolynomial.aeval x H = 0
    · rw [hxH, zero_mul]
    · rw [hq x hx hxH, mul_zero]
  have hH : H ∉ I := fun h => hzH (h z hz)
  have hqI : q ∈ I := ((inferInstance : I.IsPrime).mem_or_mem hprod).resolve_left hH
  exact hqI


theorem ambient_map_coefficientBound {n D : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (Q : Polynomial (Poly n)) (hQ : AmbientCoefficientBound D Q) :
    CoefficientBound V D (Q.map (coordinateMap V)) := by
  intro r
  rw [Polynomial.coeff_map]
  exact FractionBound.polynomial _ _ (hQ r)

theorem normalPolynomial_le_of_bound {e D : ℕ} (C : SkewCoordinates e)
    (f : Poly (skewDim e)) (hf : f.totalDegree ≤ D) (i j : Fin e) :
    (normalPolynomial C f i j).totalDegree ≤ D := by
  exact (normalPolynomial_degree_le C f D hf i j).trans (Nat.sub_le _ _)


theorem residual_map_bound {n e D : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
    (w u : Fin e → Fin e → Poly n) (hw : ∀ i j, (w i j).totalDegree ≤ D)
    (hu : ∀ i j, (u i j).totalDegree ≤ D) (a b i j : Fin e) :
    CoefficientBound V (2 * D)
      ((residualParameterPolynomial w u a b i j).map (coordinateMap V)) ∧
      (((residualParameterPolynomial w u a b i j).map (coordinateMap V)).natDegree ≤ 1) := by
  refine ⟨ambient_map_coefficientBound V _ (residualParameterPolynomial_coefficients w u hw hu a b i j), ?_⟩
  exact (Polynomial.natDegree_map_le.trans (residualParameterPolynomial_degree w u a b i j))

theorem first_map_bound {e D : ℕ} (V : AffineVariety (skewDim e)) [V.ideal.IsPrime]
    (C : SkewCoordinates e) (w : Fin e → Fin e → Poly (skewDim e))
    (hw : ∀ i j, (w i j).totalDegree ≤ D) (a b i j l : Fin e) :
    CoefficientBound V (3 * D)
      ((firstHorizontalTest C w a b i j l).map (coordinateMap V)) ∧
      (((firstHorizontalTest C w a b i j l).map (coordinateMap V)).natDegree ≤ 2) := by
  refine ⟨ambient_map_coefficientBound V _ (firstHorizontalTest_coefficients C w hw a b i j l), ?_⟩
  exact (Polynomial.natDegree_map_le.trans (firstHorizontalTest_degree C w a b i j l))


theorem bounded_family_gcd_of_iso (m d : ℕ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ {n : ℕ} (V : AffineVariety n) [V.ideal.IsPrime]
      {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin m)
      (D : ℕ) (f : ι → Polynomial (CarrierField V)),
      (∀ i, CoefficientBound V D (f i)) → (∀ i, (f i).natDegree ≤ d) →
      ∃ (P : Polynomial (CarrierField V)) (U Q : ι → Polynomial (CarrierField V)),
        (P = 0 ∨ P.Monic) ∧ P.natDegree ≤ d ∧
        (∀ i, (U i).natDegree ≤ m * d ^ 2) ∧ (∀ i, (Q i).natDegree ≤ d) ∧
        CoefficientBound V (B * D) P ∧
        (∀ i, CoefficientBound V (B * D) (U i)) ∧
        (∀ i, CoefficientBound V (B * D) (Q i)) ∧
        (∀ i, f i = P * Q i) ∧ P = ∑ i, f i * U i := by
  obtain ⟨B, hB, hraw⟩ := bounded_family_gcd m d
  refine ⟨B, hB, ?_⟩
  intro n V inst ι _ _ e D f hb hd
  let f' : Fin m → Polynomial (CarrierField V) := fun j => f (e.symm j)
  have hfb : ∀ j, CoefficientBound V D (f' j) := fun j => hb _
  have hfd : ∀ j, (f' j).natDegree ≤ d := fun j => hd _
  obtain ⟨P, U', Q', hmono, hPd, hUd, hQd, hPb, hUb, hQb, hquot, heq⟩ :=
    hraw V D f' hfb hfd
  let U : ι → Polynomial (CarrierField V) := fun i => U' (e i)
  let Q : ι → Polynomial (CarrierField V) := fun i => Q' (e i)
  refine ⟨P, U, Q, hmono, hPd, fun i => hUd _, fun i => hQd _, hPb,
    fun i => hUb _, fun i => hQb _, ?_, ?_⟩
  · intro i
    have h := hquot (e i)
    simp only [f', U, Q, Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h ⊢
    exact h
  · have hsum : (∑ i, f i * U i) = ∑ j, f' j * U' j := by
      apply Fintype.sum_equiv e
      intro i
      simp only [f', U, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    rw [hsum]
    exact heq

def primaryIdx (e c : ℕ) : Type := (Fin c × Fin e × Fin e) ⊕ (Fin e × Fin e × Fin e)

instance primaryIdx_fintype (e c : ℕ) : Fintype (primaryIdx e c) := by
  unfold primaryIdx
  infer_instance

instance primaryIdx_decEq (e c : ℕ) : DecidableEq (primaryIdx e c) := by
  unfold primaryIdx
  infer_instance

def primaryPoly {e c : ℕ} (C : SkewCoordinates e) (V : AffineVariety (skewDim e))
    [V.ideal.IsPrime] (g : Fin c → Poly (skewDim e)) (first : Fin c)
    (a b : Fin e) : primaryIdx e c → Polynomial (CarrierField V)
  | Sum.inl (l, i, j) =>
    (residualParameterPolynomial (normalPolynomial C (g first))
      (normalPolynomial C (g l)) a b i j).map (coordinateMap V)
  | Sum.inr (i, j, l) =>
    (firstHorizontalTest C (normalPolynomial C (g first)) a b i j l).map (coordinateMap V)

theorem primaryPoly_bound {e c D : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) [V.ideal.IsPrime]
    (g : Fin c → Poly (skewDim e)) (first : Fin c)
    (hg : ∀ i, (g i).totalDegree ≤ D) (a b : Fin e) :
    ∀ i : primaryIdx e c,
      CoefficientBound V (3 * D) (primaryPoly C V g first a b i) ∧
      ((primaryPoly C V g first a b i).natDegree ≤ 2) := by
  intro i
  cases i with
  | inl h =>
    obtain ⟨l, i, j⟩ := h
    have hw : ∀ p q, ((normalPolynomial C (g first)) p q).totalDegree ≤ D :=
      fun p q => normalPolynomial_le_of_bound C _ (hg first) p q
    have hu : ∀ p q, ((normalPolynomial C (g l)) p q).totalDegree ≤ D :=
      fun p q => normalPolynomial_le_of_bound C _ (hg l) p q
    obtain ⟨hbound, hdeg⟩ := residual_map_bound V _ _ hw hu a b i j
    refine ⟨hbound.mono (by omega), hdeg.trans (by decide)⟩
  | inr h =>
    obtain ⟨i, j, l⟩ := h
    have hw : ∀ p q, ((normalPolynomial C (g first)) p q).totalDegree ≤ D :=
      fun p q => normalPolynomial_le_of_bound C _ (hg first) p q
    exact first_map_bound V C _ hw a b i j l


theorem primary_gcd_uniform (e : ℕ) :
    ∃ Bmax mMax : ℕ, 1 ≤ Bmax ∧ 1 ≤ mMax ∧
      ∀ (c : ℕ), c ≤ skewDim e →
        Fintype.card (primaryIdx e c) ≤ mMax ∧
        ∀ {D : ℕ} (C : SkewCoordinates e) (V : AffineVariety (skewDim e)) [V.ideal.IsPrime]
          (g : Fin c → Poly (skewDim e)) (first : Fin c)
          (hg : ∀ i, (g i).totalDegree ≤ D) (a b : Fin e),
          ∃ (P : Polynomial (CarrierField V)) (U Q : primaryIdx e c → Polynomial (CarrierField V)),
            (P = 0 ∨ P.Monic) ∧ P.natDegree ≤ 2 ∧
            (∀ i, (U i).natDegree ≤ mMax * 4) ∧ (∀ i, (Q i).natDegree ≤ 2) ∧
            CoefficientBound V (Bmax * (3 * D)) P ∧
            (∀ i, CoefficientBound V (Bmax * (3 * D)) (U i)) ∧
            (∀ i, CoefficientBound V (Bmax * (3 * D)) (Q i)) ∧
            (∀ i, primaryPoly C V g first a b i = P * Q i) ∧
            P = ∑ i, primaryPoly C V g first a b i * U i := by
  classical
  let N := skewDim e
  have hN : ∀ c : ℕ, c ≤ N → Fintype.card (primaryIdx e c) ≤ Fintype.card (primaryIdx e N) := by
    intro c hc
    unfold primaryIdx
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    nlinarith
  choose B hB using fun (c : Fin (N + 1)) =>
    bounded_family_gcd_of_iso (Fintype.card (primaryIdx e (c.val))) 2
  let Bmax := Finset.sup (Finset.univ : Finset (Fin (N + 1))) (fun c => B c)
  have hBmax1 : 1 ≤ Bmax := by
    have h0 : (⟨0, by omega⟩ : Fin (N + 1)) ∈ (Finset.univ : Finset (Fin (N + 1))) :=
      Finset.mem_univ _
    have hle := Finset.le_sup (s := (Finset.univ : Finset (Fin (N + 1)))) (f := fun c => B c) h0
    obtain ⟨hb1, _⟩ := hB ⟨0, by omega⟩
    omega
  let mMax := max 1 (Fintype.card (primaryIdx e N))
  have hmMax1 : 1 ≤ mMax := le_max_left _ _
  have hmN : ∀ c : ℕ, c ≤ N → Fintype.card (primaryIdx e c) ≤ mMax := by
    intro c hc
    exact (hN c hc).trans (le_max_right _ _)
  refine ⟨Bmax, mMax, hBmax1, hmMax1, ?_⟩
  intro c hc
  refine ⟨hmN c hc, ?_⟩
  intro D C V inst g first hg a b
  let cFin : Fin (N + 1) := ⟨c, by omega⟩
  obtain ⟨hBc1, hBc⟩ := hB cFin
  have hBm : B cFin ≤ Bmax := Finset.le_sup (Finset.mem_univ cFin)
  have hequiv : primaryIdx e c ≃ Fin (Fintype.card (primaryIdx e c)) :=
    Fintype.equivFin _
  obtain ⟨P, U, Q, hmono, hPd, hUd, hQd, hPb, hUb, hQb, hquot, heq⟩ :=
    hBc V hequiv (3 * D) (primaryPoly C V g first a b)
      (fun i => (primaryPoly_bound C V g first hg a b i).1)
      (fun i => (primaryPoly_bound C V g first hg a b i).2)
  refine ⟨P, U, Q, hmono, hPd, ?_, hQd, ?_, ?_, ?_, hquot, heq⟩
  · intro i
    exact (hUd i).trans (Nat.mul_le_mul_right 4 (hmN c hc))
  · exact hPb.mono (Nat.mul_le_mul_right _ hBm)
  · intro i
    exact (hUb i).mono (Nat.mul_le_mul_right _ hBm)
  · intro i
    exact (hQb i).mono (Nat.mul_le_mul_right _ hBm)

def secondIdx (e : ℕ) : Type := Option (Fin e × Fin e)

instance secondIdx_fintype (e : ℕ) : Fintype (secondIdx e) := by
  unfold secondIdx
  infer_instance

instance secondIdx_decEq (e : ℕ) : DecidableEq (secondIdx e) := by
  unfold secondIdx
  infer_instance

theorem separable_of_dvd_of_separable {K : Type*} [Field K]
    {P G : Polynomial K} (hG : G.Separable) (hdiv : P ∣ G) : P.Separable := by
  obtain ⟨a, b, hab⟩ := hG
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨a * Q + b * Q.derivative, b * Q, ?_⟩
  have hderiv : (P * Q).derivative = P.derivative * Q + P * Q.derivative :=
    Polynomial.derivative_mul
  calc (a * Q + b * Q.derivative) * P + b * Q * P.derivative
      = a * (P * Q) + b * (P.derivative * Q + P * Q.derivative) := by ring
    _ = a * G + b * (P * Q).derivative := by rw [hQ, hderiv]
    _ = 1 := by
      have hGderiv : (P * Q).derivative = G.derivative := by rw [← hQ]
      rw [hGderiv]
      exact hab

theorem primary_nonzero_of_hyp {e c : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) [V.ideal.IsPrime]
    (g : Fin c → Poly (skewDim e)) (first : Fin c) (a b : Fin e) :
    ((∃ l i j, (residualParameterPolynomial (normalPolynomial C (g first))
        (normalPolynomial C (g l)) a b i j).map (coordinateMap V) ≠ 0) ∨
      (∃ i j l, (firstHorizontalTest C (normalPolynomial C (g first)) a b i j l).map
        (coordinateMap V) ≠ 0)) →
    ∃ i : primaryIdx e c, primaryPoly C V g first a b i ≠ 0 := by
  rintro (⟨l, i, j, h⟩ | ⟨i, j, l, h⟩)
  · exact ⟨Sum.inl (l, i, j), h⟩
  · exact ⟨Sum.inr (i, j, l), h⟩

def secondPoly {e : ℕ} (C : SkewCoordinates e) (V : AffineVariety (skewDim e))
    [V.ideal.IsPrime] (W : Fin e → Fin e → Poly (skewDim e)) (a b : Fin e)
    (QG : Polynomial (Poly (skewDim e))) (G : Polynomial (CarrierField V)) :
    secondIdx e → Polynomial (CarrierField V)
  | none => G
  | some (i, j) => (secondHorizontalTest C W a b i j QG).map (coordinateMap V)

theorem secondPoly_bound {e D DG E : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) [V.ideal.IsPrime]
    (W : Fin e → Fin e → Poly (skewDim e)) (hw : ∀ i j, (W i j).totalDegree ≤ D)
    (a b : Fin e) (QG : Polynomial (Poly (skewDim e)))
    (hQG : AmbientCoefficientBound E QG) (hQdeg : QG.natDegree ≤ 2)
    (G : Polynomial (CarrierField V))
    (hGbound : CoefficientBound V DG G) (hGdeg : G.natDegree ≤ 2)
    (D2 : ℕ) (hD2 : D + E ≤ D2) (hG2 : DG ≤ D2) :
    ∀ i : secondIdx e,
      CoefficientBound V D2 (secondPoly C V W a b QG G i) ∧
      ((secondPoly C V W a b QG G i).natDegree ≤ 3) := by
  intro i
  cases i with
  | none =>
    simp only [secondPoly]
    refine ⟨hGbound.mono hG2, hGdeg.trans (by decide)⟩
  | some h =>
    obtain ⟨i, j⟩ := h
    simp only [secondPoly]
    have hbound : AmbientCoefficientBound (D + E)
        (secondHorizontalTest C W a b i j QG) :=
      secondHorizontalTest_coefficients C W hw a b i j QG hQG
    have hdeg : (secondHorizontalTest C W a b i j QG).natDegree ≤ 3 := by
      have h1 := secondHorizontalTest_degree C W a b i j QG
      omega
    refine ⟨(ambient_map_coefficientBound V _ hbound).mono hD2, ?_⟩
    exact (Polynomial.natDegree_map_le.trans hdeg)

set_option maxHeartbeats 2400000 in
theorem nonzero_combined_chart (e : ℕ) :
    ∃ Broot : ℕ, 2 ≤ Broot ∧
      ∀ (C : SkewCoordinates e) (V : AffineVariety (skewDim e)) [V.ideal.IsPrime]
        (c D : ℕ), V.IsIrreducible → V.dimension + c = skewDim e →
        ∀ (g : Fin c → Poly (skewDim e)) (first : Fin c),
          (∀ i, g i ∈ V.ideal ∧ (g i).totalDegree ≤ D) →
          ∀ H0 : Poly (skewDim e), H0 ∉ V.ideal → H0.totalDegree ≤ D →
            (∀ z ∈ V.points, MvPolynomial.eval z H0 ≠ 0 →
              V.IsSmoothAt z ∧ V.tangentSpace z = ⨅ i : Fin c, LinearMap.ker (differential (g i) z)) →
            ∀ a b : Fin e, normalPolynomial C (g first) a b ∉ V.ideal →
              ((∃ l i j, (residualParameterPolynomial (normalPolynomial C (g first))
                (normalPolynomial C (g l)) a b i j).map (coordinateMap V) ≠ 0) ∨
              (∃ i j l, (firstHorizontalTest C (normalPolynomial C (g first)) a b i j l).map
                (coordinateMap V) ≠ 0)) →
              Nonempty (ControlledChart C V a Broot ((Broot : ℝ) * (D : ℝ))) := by
  classical
  obtain ⟨Bmax, mMax, hBmax, hmMax, hPrimary⟩ := primary_gcd_uniform e
  obtain ⟨Msr, hMsr, hSr⟩ := bounded_simple_root_fraction 2
  obtain ⟨B2, hB2, hB2raw⟩ := bounded_family_gcd_of_iso (Fintype.card (secondIdx e)) 3
  let m2 := Fintype.card (secondIdx e)
  let K_HG := 9 * Bmax * Msr
  let K_FG := 9 * Bmax * Msr
  let K_HF2 := Msr * B2 * (1 + 9 * Bmax * Msr)
  let K_F2 := Msr * B2 * (1 + 9 * Bmax * Msr)
  let K_P1 := 9 * Bmax
  let K_U1 := mMax * (mMax * 4 + 1) * Bmax * 3
  let K_Q1 := mMax * 9 * Bmax
  let K_U2 := m2 * (m2 * 9 + 1) * B2 * (1 + 9 * Bmax * Msr)
  let K_Q2 := m2 * 4 * B2 * (1 + 9 * Bmax * Msr)
  let K_S1 := 3 * 4 ^ 3 * (9 * Bmax)
  let K_S1den := 3 * K_S1
  let K_G2 := 10 * (9 * Bmax)
  let K_S2 := 3 * 4 ^ 5 * K_G2
  let K_S2den := 5 * K_S2
  let Broot := 2 + (1 + 1 + K_HG + K_FG + K_HF2 + K_F2 + K_P1 + K_U1 + K_Q1 + K_U2 + K_Q2 + K_S1den + K_S2den)
  have hBroot2 : 2 ≤ Broot := by dsimp [Broot]; omega
  refine ⟨Broot, hBroot2, ?_⟩
  intro C V inst c D hV hcodim g first hg H0 hH0 hH0deg hreg a b hδ hnonzero
  have hc_le : c ≤ skewDim e := by omega
  obtain ⟨hmCard, hP1raw⟩ := hPrimary c hc_le
  obtain ⟨P1, U1, Q1, hP1mono, hP1deg, hU1deg, hQ1deg, hP1bound, hU1bound, hQ1bound, hP1quot, hP1bez⟩ :=
    hP1raw (C := C) (V := V) g first (fun i => (hg i).2) a b
  obtain ⟨ine, hine⟩ := primary_nonzero_of_hyp C V g first a b hnonzero
  have hP1ne : P1 ≠ 0 := by
    intro h0
    have hall : ∀ i, primaryPoly C V g first a b i = 0 := by
      intro i
      rw [hP1quot i, h0, zero_mul]
    exact hine (hall ine)
  have hP1monic : P1.Monic := hP1mono.resolve_left hP1ne
  obtain ⟨G, hGmonic, hGsep, hGdeg, hGbound, hGdiv, hP1div⟩ :=
    CoefficientBound.quadratic_squarefree P1 hP1monic hP1deg hP1bound
  have hGne : G ≠ 0 := hGmonic.ne_zero
  have hP1common : CoefficientBound V (9 * Bmax * D) P1 := by
    apply hP1bound.mono
    calc Bmax * (3 * D) = 3 * (Bmax * D) := by ring
      _ ≤ 9 * (Bmax * D) := Nat.mul_le_mul_right _ (by decide)
      _ = 9 * Bmax * D := by ring
  have hGcommon : CoefficientBound V (9 * Bmax * D) G :=
    hGbound.mono (le_of_eq (by ring))
  let S1 := P1 / G
  have hS1eq : P1 = G * S1 := (EuclideanDomain.mul_div_cancel' hGne hGdiv).symm
  have hS1deg : S1.natDegree ≤ 2 := by
    have hdiv : S1 ∣ P1 := ⟨G, by rw [hS1eq, mul_comm]⟩
    exact (Polynomial.natDegree_le_of_dvd hdiv hP1ne).trans hP1deg
  have hS1bound : CoefficientBound V (K_S1 * D) S1 := by
    have hq := hP1common.quotient hGcommon 2 hP1deg
    apply hq.mono
    dsimp [K_S1]
    exact le_of_eq (by ring)
  have hG2bound : CoefficientBound V (K_G2 * D) (G ^ 2) := by
    rw [pow_two]
    exact (hGcommon.mul hGcommon 2 hGdeg hGdeg).mono
      (le_of_eq (by dsimp [K_G2]; ring))
  have hG2deg : (G ^ 2).natDegree ≤ 4 := by
    rw [pow_two]
    calc (G * G).natDegree ≤ G.natDegree + G.natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 2 + 2 := Nat.add_le_add hGdeg hGdeg
      _ = 4 := by decide
  let S2 := (G ^ 2) / P1
  have hS2eq : G ^ 2 = P1 * S2 := (EuclideanDomain.mul_div_cancel' hP1ne hP1div).symm
  have hS2deg : S2.natDegree ≤ 4 := by
    have hdiv : S2 ∣ G ^ 2 := ⟨P1, by rw [hS2eq, mul_comm]⟩
    have hG2ne : G ^ 2 ≠ 0 := pow_ne_zero 2 hGne
    exact (Polynomial.natDegree_le_of_dvd hdiv hG2ne).trans hG2deg
  have hS2bound : CoefficientBound V (K_S2 * D) S2 := by
    have hP1common2 : CoefficientBound V (K_G2 * D) P1 := by
      apply hP1common.mono
      dsimp [K_G2]
      calc 9 * Bmax * D = 1 * (9 * Bmax * D) := by ring
        _ ≤ 10 * (9 * Bmax * D) := Nat.mul_le_mul_right _ (by decide)
        _ = 10 * (9 * Bmax) * D := by ring
    have hq := hG2bound.quotient hP1common2 4 hG2deg
    apply hq.mono
    dsimp [K_S2, K_G2]
    exact le_of_eq (by ring)
  obtain ⟨S1F, hS1Fval, hS1Fdeg⟩ :=
    parameterFraction_of_coefficients V S1 hS1bound 2 hS1deg
  obtain ⟨S2F, hS2Fval, hS2Fdeg⟩ :=
    parameterFraction_of_coefficients V S2 hS2bound 4 hS2deg
  obtain ⟨HG, FG, hHG, hHGdeg, hFGval, hFGdeg, hFGgood⟩ :=
    hSr (V := V) _ G hGbound hGdeg hGmonic hGsep
  let W := normalPolynomial C (g first)
  have hw : ∀ i j, (W i j).totalDegree ≤ D :=
    fun i j => normalPolynomial_le_of_bound C _ ((hg first).2) i j
  have hQG : AmbientCoefficientBound (Msr * (3 * (Bmax * (3 * D)))) FG.numerator :=
    FG.numerator_degree
  have hQdeg : FG.numerator.natDegree ≤ 2 := hFGdeg.trans hGdeg
  have hDG : CoefficientBound V (3 * (Bmax * (3 * D))) G := hGbound
  have hD2 : D + Msr * (3 * (Bmax * (3 * D))) ≤ D + Msr * (3 * (Bmax * (3 * D))) := le_rfl
  have hG2 : 3 * (Bmax * (3 * D)) ≤ D + Msr * (3 * (Bmax * (3 * D))) := by
    nlinarith [hMsr, hBmax]
  have hsecondBound : ∀ i : secondIdx e,
      CoefficientBound V (D + Msr * (3 * (Bmax * (3 * D))))
        (secondPoly C V W a b FG.numerator G i) ∧
      ((secondPoly C V W a b FG.numerator G i).natDegree ≤ 3) :=
    secondPoly_bound C V W hw a b FG.numerator hQG hQdeg G hDG hGdeg
      (D + Msr * (3 * (Bmax * (3 * D)))) hD2 hG2
  have hequiv2 : secondIdx e ≃ Fin (Fintype.card (secondIdx e)) := Fintype.equivFin _
  obtain ⟨P2, U2, Q2, hP2mono, hP2deg3, hU2deg, hQ2deg, hP2bound, hU2bound, hQ2bound, hP2quot, hP2bez⟩ :=
    hB2raw V hequiv2 (D + Msr * (3 * (Bmax * (3 * D))))
      (secondPoly C V W a b FG.numerator G)
      (fun i => (hsecondBound i).1) (fun i => (hsecondBound i).2)
  have hGne : G ≠ 0 := hGmonic.ne_zero
  have hP2ne : P2 ≠ 0 := by
    intro h0
    have hG0 : G = 0 := by
      have h := hP2quot (none : secondIdx e)
      simp only [secondPoly] at h
      rw [h0, zero_mul] at h
      exact h
    exact hGne hG0
  have hP2monic : P2.Monic := hP2mono.resolve_left hP2ne
  have hP2deg2 : P2.natDegree ≤ 2 := by
    have hdiv : P2 ∣ G := by
      have h := hP2quot (none : secondIdx e)
      simp only [secondPoly] at h
      exact ⟨Q2 none, h⟩
    exact (Polynomial.natDegree_le_of_dvd hdiv hGne).trans hGdeg
  have hP2sep : P2.Separable :=
    separable_of_dvd_of_separable hGsep (by
      have h := hP2quot (none : secondIdx e)
      simp only [secondPoly] at h
      exact ⟨Q2 none, h⟩)
  obtain ⟨HF2, F2, hHF2, hHF2deg, hF2val, hF2deg, hF2good⟩ :=
    hSr (V := V) _ P2 hP2bound hP2deg2 hP2monic hP2sep
  obtain ⟨P1F, hP1Fval, hP1Fdeg⟩ :=
    parameterFraction_of_coefficients V P1 hP1bound 2 hP1deg
  choose U1F hU1F using fun i =>
    parameterFraction_of_coefficients V (U1 i) (hU1bound i) (mMax * 4) (hU1deg i)
  choose Q1F hQ1F using fun i =>
    parameterFraction_of_coefficients V (Q1 i) (hQ1bound i) 2 (hQ1deg i)
  choose U2F hU2F using fun j =>
    parameterFraction_of_coefficients V (U2 j) (hU2bound j)
      (Fintype.card (secondIdx e) * 9) (hU2deg j)
  choose Q2F hQ2F using fun j =>
    parameterFraction_of_coefficients V (Q2 j) (hQ2bound j) 3 (hQ2deg j)
  let H := H0 * W a b * HG * HF2 * FG.denominator * F2.denominator * P1F.denominator *
    S1F.denominator * S2F.denominator *
    (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
    (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator))
  have hH0' : coordinateMap V H0 ≠ 0 := fun h => hH0 ((coordinateMap_eq_zero_iff V H0).mp h)
  have hW' : coordinateMap V (W a b) ≠ 0 := fun h => hδ ((coordinateMap_eq_zero_iff V _).mp h)
  have hHG' : coordinateMap V HG ≠ 0 := fun h => hHG ((coordinateMap_eq_zero_iff V HG).mp h)
  have hHF2' : coordinateMap V HF2 ≠ 0 := fun h => hHF2 ((coordinateMap_eq_zero_iff V HF2).mp h)
  have hFG' : coordinateMap V FG.denominator ≠ 0 :=
    fun h => FG.denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)
  have hF2' : coordinateMap V F2.denominator ≠ 0 :=
    fun h => F2.denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)
  have hP1' : coordinateMap V P1F.denominator ≠ 0 :=
    fun h => P1F.denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)
  have hU1' : ∀ i, coordinateMap V (U1F i).denominator ≠ 0 := fun i h =>
    (U1F i).denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)
  have hQ1' : ∀ i, coordinateMap V (Q1F i).denominator ≠ 0 := fun i h =>
    (Q1F i).denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)
  have hU2' : ∀ j, coordinateMap V (U2F j).denominator ≠ 0 := fun j h =>
    (U2F j).denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)
  have hQ2' : ∀ j, coordinateMap V (Q2F j).denominator ≠ 0 := fun j h =>
    (Q2F j).denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)
  have hS1' : coordinateMap V S1F.denominator ≠ 0 :=
    fun h => S1F.denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)
  have hS2' : coordinateMap V S2F.denominator ≠ 0 :=
    fun h => S2F.denominator_proper ((coordinateMap_eq_zero_iff V _).mp h)
  have hH : H ∉ V.ideal := by
    intro hmem
    have hz := (coordinateMap_eq_zero_iff V H).mpr hmem
    dsimp [H] at hz
    simp only [map_mul, map_prod, Finset.prod_mul_distrib] at hz
    have hprod1U : (∏ i : primaryIdx e c, coordinateMap V (U1F i).denominator) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hU1' i)
    have hprod1Q : (∏ i : primaryIdx e c, coordinateMap V (Q1F i).denominator) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hQ1' i)
    have hprod2U : (∏ j : secondIdx e, coordinateMap V (U2F j).denominator) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hU2' j)
    have hprod2Q : (∏ j : secondIdx e, coordinateMap V (Q2F j).denominator) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hQ2' j)
    have hprod1 := mul_ne_zero hprod1U hprod1Q
    have hprod2 := mul_ne_zero hprod2U hprod2Q
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hH0' hW') hHG') hHF2') hFG') hF2') hP1') hS1') hS2') hprod1) hprod2) hz
  have hHdeg_nat : H.totalDegree ≤ Broot * D := by
    have h0 : H0.totalDegree ≤ 1 * D := by simpa using hH0deg
    have hWdeg : (W a b).totalDegree ≤ 1 * D := by simpa using hw a b
    have hHGdeg' : HG.totalDegree ≤ K_HG * D := by
      dsimp [K_HG]
      have h := hHGdeg
      calc HG.totalDegree ≤ Msr * (3 * (Bmax * (3 * D))) := h
        _ = 9 * Bmax * Msr * D := by ring
        _ = (9 * Bmax * Msr) * D := by ring
    have hFGdeg' : FG.denominator.totalDegree ≤ K_FG * D := by
      dsimp [K_FG]
      have h := FG.denominator_degree
      have hE : Msr * (3 * (Bmax * (3 * D))) = 9 * Bmax * Msr * D := by ring
      calc FG.denominator.totalDegree ≤ Msr * (3 * (Bmax * (3 * D))) := h
        _ = 9 * Bmax * Msr * D := by ring
        _ = (9 * Bmax * Msr) * D := by ring
    have hHF2deg' : HF2.totalDegree ≤ K_HF2 * D := by
      dsimp [K_HF2]
      have h := hHF2deg
      calc HF2.totalDegree ≤ Msr * (B2 * (D + Msr * (3 * (Bmax * (3 * D))))) := h
        _ = Msr * B2 * (1 + 9 * Bmax * Msr) * D := by ring
    have hF2deg' : F2.denominator.totalDegree ≤ K_F2 * D := by
      dsimp [K_F2]
      have h := F2.denominator_degree
      have hE : Msr * (B2 * (D + Msr * (3 * (Bmax * (3 * D))))) =
          Msr * B2 * (1 + 9 * Bmax * Msr) * D := by ring
      calc F2.denominator.totalDegree ≤ Msr * (B2 * (D + Msr * (3 * (Bmax * (3 * D))))) := h
        _ = Msr * B2 * (1 + 9 * Bmax * Msr) * D := by ring
        _ = (Msr * B2 * (1 + 9 * Bmax * Msr)) * D := by ring
    have hP1deg' : P1F.denominator.totalDegree ≤ K_P1 * D := by
      dsimp [K_P1]
      have h := P1F.denominator_degree
      calc P1F.denominator.totalDegree ≤ 3 * (Bmax * (3 * D)) := h
        _ = 9 * Bmax * D := by ring
        _ = (9 * Bmax) * D := by ring
    have hS1deg' : S1F.denominator.totalDegree ≤ K_S1den * D := by
      have h := S1F.denominator_degree
      calc S1F.denominator.totalDegree ≤ 3 * (K_S1 * D) := h
        _ = K_S1den * D := by dsimp [K_S1den]; ring
    have hS2deg' : S2F.denominator.totalDegree ≤ K_S2den * D := by
      have h := S2F.denominator_degree
      calc S2F.denominator.totalDegree ≤ 5 * (K_S2 * D) := h
        _ = K_S2den * D := by dsimp [K_S2den]; ring
    have hU1deg' : ∀ i : primaryIdx e c,
        (U1F i).denominator.totalDegree ≤ ((mMax * 4 + 1) * (Bmax * (3 * D))) := fun i =>
      (U1F i).denominator_degree
    have hQ1deg' : ∀ i : primaryIdx e c,
        (Q1F i).denominator.totalDegree ≤ 3 * (Bmax * (3 * D)) := fun i =>
      (Q1F i).denominator_degree
    have hU2deg'' : ∀ j : secondIdx e,
        (U2F j).denominator.totalDegree ≤
          (m2 * 9 + 1) * (B2 * (D + Msr * (3 * (Bmax * (3 * D))))) := fun j =>
      (U2F j).denominator_degree
    have hQ2deg' : ∀ j : secondIdx e,
        (Q2F j).denominator.totalDegree ≤ 4 * (B2 * (D + Msr * (3 * (Bmax * (3 * D))))) := fun j =>
      (Q2F j).denominator_degree
    have hprod1U : (∏ i : primaryIdx e c, (U1F i).denominator).totalDegree ≤ K_U1 * D := by
      calc (∏ i : primaryIdx e c, (U1F i).denominator).totalDegree
          ≤ ∑ i : primaryIdx e c, ((U1F i).denominator.totalDegree) :=
          MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ _i : primaryIdx e c, ((mMax * 4 + 1) * (Bmax * (3 * D))) :=
          Finset.sum_le_sum (fun i _ => hU1deg' i)
        _ = Fintype.card (primaryIdx e c) * ((mMax * 4 + 1) * (Bmax * (3 * D))) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ mMax * ((mMax * 4 + 1) * (Bmax * (3 * D))) :=
          Nat.mul_le_mul_right _ hmCard
        _ = K_U1 * D := by dsimp [K_U1]; ring
    have hprod1Q : (∏ i : primaryIdx e c, (Q1F i).denominator).totalDegree ≤ K_Q1 * D := by
      calc (∏ i : primaryIdx e c, (Q1F i).denominator).totalDegree
          ≤ ∑ i : primaryIdx e c, ((Q1F i).denominator.totalDegree) :=
          MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ _i : primaryIdx e c, (3 * (Bmax * (3 * D))) :=
          Finset.sum_le_sum (fun i _ => hQ1deg' i)
        _ = Fintype.card (primaryIdx e c) * (3 * (Bmax * (3 * D))) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ mMax * (3 * (Bmax * (3 * D))) :=
          Nat.mul_le_mul_right _ hmCard
        _ = K_Q1 * D := by dsimp [K_Q1]; ring
    have hprod2U : (∏ j : secondIdx e, (U2F j).denominator).totalDegree ≤ K_U2 * D := by
      calc (∏ j : secondIdx e, (U2F j).denominator).totalDegree
          ≤ ∑ j : secondIdx e, ((U2F j).denominator.totalDegree) :=
          MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ _j : secondIdx e, ((m2 * 9 + 1) * (B2 * (D + Msr * (3 * (Bmax * (3 * D)))))) :=
          Finset.sum_le_sum (fun j _ => hU2deg'' j)
        _ = m2 * ((m2 * 9 + 1) * (B2 * (D + Msr * (3 * (Bmax * (3 * D)))))) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m2]
        _ = K_U2 * D := by dsimp [K_U2, m2]; ring
    have hprod2Q : (∏ j : secondIdx e, (Q2F j).denominator).totalDegree ≤ K_Q2 * D := by
      calc (∏ j : secondIdx e, (Q2F j).denominator).totalDegree
          ≤ ∑ j : secondIdx e, ((Q2F j).denominator.totalDegree) :=
          MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ _j : secondIdx e, (4 * (B2 * (D + Msr * (3 * (Bmax * (3 * D)))))) :=
          Finset.sum_le_sum (fun j _ => hQ2deg' j)
        _ = m2 * (4 * (B2 * (D + Msr * (3 * (Bmax * (3 * D)))))) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m2]
        _ = K_Q2 * D := by dsimp [K_Q2, m2]; ring
    have hprod1 : (∏ i : primaryIdx e c,
        ((U1F i).denominator * (Q1F i).denominator)).totalDegree ≤ (K_U1 + K_Q1) * D := by
      have hEq : (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) =
          (∏ i : primaryIdx e c, (U1F i).denominator) *
          (∏ i : primaryIdx e c, (Q1F i).denominator) := Finset.prod_mul_distrib
      calc (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)).totalDegree
          = ((∏ i : primaryIdx e c, (U1F i).denominator) *
            (∏ i : primaryIdx e c, (Q1F i).denominator)).totalDegree := by rw [hEq]
        _ ≤ (∏ i : primaryIdx e c, (U1F i).denominator).totalDegree +
            (∏ i : primaryIdx e c, (Q1F i).denominator).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ K_U1 * D + K_Q1 * D := Nat.add_le_add hprod1U hprod1Q
        _ = (K_U1 + K_Q1) * D := by ring
    have hprod2 : (∏ j : secondIdx e,
        ((U2F j).denominator * (Q2F j).denominator)).totalDegree ≤ (K_U2 + K_Q2) * D := by
      have hEq : (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)) =
          (∏ j : secondIdx e, (U2F j).denominator) *
          (∏ j : secondIdx e, (Q2F j).denominator) := Finset.prod_mul_distrib
      calc (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)).totalDegree
          = ((∏ j : secondIdx e, (U2F j).denominator) *
            (∏ j : secondIdx e, (Q2F j).denominator)).totalDegree := by rw [hEq]
        _ ≤ (∏ j : secondIdx e, (U2F j).denominator).totalDegree +
            (∏ j : secondIdx e, (Q2F j).denominator).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ K_U2 * D + K_Q2 * D := Nat.add_le_add hprod2U hprod2Q
        _ = (K_U2 + K_Q2) * D := by ring
    have hHle : H.totalDegree ≤
        (1 + 1 + K_HG + K_FG + K_HF2 + K_F2 + K_P1 + K_S1den + K_S2den + (K_U1 + K_Q1) + (K_U2 + K_Q2)) * D := by
      have h1 : H.totalDegree ≤ H0.totalDegree + (W a b).totalDegree + HG.totalDegree +
          HF2.totalDegree + FG.denominator.totalDegree + F2.denominator.totalDegree +
          P1F.denominator.totalDegree + S1F.denominator.totalDegree + S2F.denominator.totalDegree +
          (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)).totalDegree +
          (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)).totalDegree := by
        dsimp [H]
        have hp1 : (H0 * W a b).totalDegree ≤ H0.totalDegree + (W a b).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        have hp2 : (H0 * W a b * HG).totalDegree ≤
            H0.totalDegree + (W a b).totalDegree + HG.totalDegree :=
          (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp1 le_rfl)
        have hp3 : (H0 * W a b * HG * HF2).totalDegree ≤
            H0.totalDegree + (W a b).totalDegree + HG.totalDegree + HF2.totalDegree :=
          (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp2 le_rfl)
        have hp4 : (H0 * W a b * HG * HF2 * FG.denominator).totalDegree ≤
            H0.totalDegree + (W a b).totalDegree + HG.totalDegree + HF2.totalDegree +
              FG.denominator.totalDegree :=
          (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp3 le_rfl)
        have hp5 : (H0 * W a b * HG * HF2 * FG.denominator * F2.denominator).totalDegree ≤
            H0.totalDegree + (W a b).totalDegree + HG.totalDegree + HF2.totalDegree +
              FG.denominator.totalDegree + F2.denominator.totalDegree :=
          (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp4 le_rfl)
        have hp6 : (H0 * W a b * HG * HF2 * FG.denominator * F2.denominator *
            P1F.denominator).totalDegree ≤
            H0.totalDegree + (W a b).totalDegree + HG.totalDegree + HF2.totalDegree +
              FG.denominator.totalDegree + F2.denominator.totalDegree +
              P1F.denominator.totalDegree :=
          (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp5 le_rfl)
        have hp7 : (H0 * W a b * HG * HF2 * FG.denominator * F2.denominator *
            P1F.denominator * S1F.denominator).totalDegree ≤
            H0.totalDegree + (W a b).totalDegree + HG.totalDegree + HF2.totalDegree +
              FG.denominator.totalDegree + F2.denominator.totalDegree +
              P1F.denominator.totalDegree + S1F.denominator.totalDegree :=
          (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp6 le_rfl)
        have hp8 : (H0 * W a b * HG * HF2 * FG.denominator * F2.denominator *
            P1F.denominator * S1F.denominator * S2F.denominator).totalDegree ≤
            H0.totalDegree + (W a b).totalDegree + HG.totalDegree + HF2.totalDegree +
              FG.denominator.totalDegree + F2.denominator.totalDegree +
              P1F.denominator.totalDegree + S1F.denominator.totalDegree +
              S2F.denominator.totalDegree :=
          (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp7 le_rfl)
        have hp9 : (H0 * W a b * HG * HF2 * FG.denominator * F2.denominator *
            P1F.denominator * S1F.denominator * S2F.denominator *
            (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator))).totalDegree ≤
            H0.totalDegree + (W a b).totalDegree + HG.totalDegree + HF2.totalDegree +
              FG.denominator.totalDegree + F2.denominator.totalDegree +
              P1F.denominator.totalDegree + S1F.denominator.totalDegree +
              S2F.denominator.totalDegree +
              (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)).totalDegree :=
          (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp8 le_rfl)
        exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp9 le_rfl)
      calc H.totalDegree ≤ H0.totalDegree + (W a b).totalDegree + HG.totalDegree +
          HF2.totalDegree + FG.denominator.totalDegree + F2.denominator.totalDegree +
          P1F.denominator.totalDegree + S1F.denominator.totalDegree + S2F.denominator.totalDegree +
          (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)).totalDegree +
          (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)).totalDegree := h1
        _ ≤ 1 * D + 1 * D + K_HG * D + K_HF2 * D + K_FG * D + K_F2 * D + K_P1 * D +
          K_S1den * D + K_S2den * D +
          (K_U1 + K_Q1) * D + (K_U2 + K_Q2) * D :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
            (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h0 hWdeg) hHGdeg') hHF2deg') hFGdeg')
            hF2deg') hP1deg') hS1deg') hS2deg') hprod1) hprod2
        _ = (1 + 1 + K_HG + K_FG + K_HF2 + K_F2 + K_P1 + K_S1den + K_S2den + (K_U1 + K_Q1) + (K_U2 + K_Q2)) * D := by ring
    calc H.totalDegree ≤ (1 + 1 + K_HG + K_FG + K_HF2 + K_F2 + K_P1 + K_S1den + K_S2den + (K_U1 + K_Q1) + (K_U2 + K_Q2)) * D := hHle
      _ ≤ Broot * D := Nat.mul_le_mul_right D (by dsimp [Broot]; omega)
  have hHdeg : (H.totalDegree : ℝ) ≤ (Broot : ℝ) * (D : ℝ) := by
    exact_mod_cast hHdeg_nat
  have hHdvd : W a b ∣ H := by
    refine ⟨H0 * HG * HF2 * FG.denominator * F2.denominator * P1F.denominator *
      S1F.denominator * S2F.denominator *
      (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
      (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), ?_⟩
    dsimp [H]
    ring
  have hFGdvd : FG.denominator ∣ H := by
    refine ⟨H0 * W a b * HG * HF2 * F2.denominator * P1F.denominator *
      S1F.denominator * S2F.denominator *
      (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
      (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), ?_⟩
    dsimp [H]
    ring
  have hF2dvd : F2.denominator ∣ H := by
    refine ⟨H0 * W a b * HG * HF2 * FG.denominator * P1F.denominator *
      S1F.denominator * S2F.denominator *
      (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
      (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), ?_⟩
    dsimp [H]
    ring
  have hH0dvd : H0 ∣ H := by
    refine ⟨W a b * HG * HF2 * FG.denominator * F2.denominator * P1F.denominator *
      S1F.denominator * S2F.denominator *
      (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
      (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), ?_⟩
    dsimp [H]
    ring
  let δ := W a b
  let Bf : Fin e → Poly (skewDim e) := fun i => W i b
  let Af : Fin e → Poly (skewDim e) := fun i => W a i
  have hBb : Bf b = 0 := normalPolynomial_self C (g first) b
  have hAb : Af b = δ := rfl
  have hBa : Bf a = δ := rfl
  have hAa : Af a = 0 := normalPolynomial_self C (g first) a
  have hqmonic : (F2.localPolynomial H).Monic :=
    F2.localPolynomial_monic H hH hF2dvd (by rw [hF2val]; exact hP2monic)
  have hqdeg : (F2.localPolynomial H).natDegree ≤ 2 := by
    rw [F2.localPolynomial_degree H hH hF2dvd, hF2val]
    exact hP2deg2
  let q := F2.localPolynomial H
  let v := affineRootDirection V H δ q Bf Af
  have hvb : v b = AdjoinRoot.root q :=
    affineRootDirection_root_coordinate V H δ hHdvd q Bf Af b hBb hAb
  have hva : v a = 1 :=
    affineRootDirection_normalized V H δ hHdvd q Bf Af a hBa hAa
  have hgraph : ∀ i, algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
      (principalCoordinateMap V H δ) * v i =
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (Bf i)) +
      algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (Af i)) *
        AdjoinRoot.root q := by
    intro i
    exact affineRootDirection_cleared V H δ hHdvd q Bf Af i
    -- v i defined with root q, but h has AdjoinRoot.root q? need to rewrite hva? actually h is about v i, with root q on RHS? check: cleared gives ... * v i = ... + ... * root q, which matches after rw hvb? Wait hvb is v b = root, not v i. Hmm need to keep root, not v b. Actually hgraph expects ... * v i = ... + ... * v b? No, expects ... * v i = ... + ... * root? Let's check signature: hgraph for rootGraphVariety needs ... * v i = ... + ... * v b? No, for rootGraphVariety with q, v, hgraph should be ... * v i = ... + ... * v b? Wait rootGraphVariety_graph_coordinate expects hv : algebraMap ... δ * v i = ... + ... * v b? Actually earlier hgraph for root case: `algebraMap ... δ * v i = ... + ... * v b`? Let's check: In rootGraphVariety_graph_coordinate, hv is `algebraMap ... δ * v i = ... + ... * v b`? No, that lemma's hv is `algebraMap ... δ * v i = ... + ... * v b`? Let's see: It takes `hv : algebraMap ... δ * v i = ... + ... * v b`? Actually from earlier read (lines 4298-4301): `hv : algebraMap ... δ * v i = ... + ... * v b`? No, it says `... * v i = ... + ... * v b`? Wait it says `... * v i = ... + ... * v b`? Let's re-read: Lines 4298-4301: `hv : algebraMap ... δ * v i = algebraMap ... B + algebraMap ... A * v b`. Yes, with v b (not root). Good. Our v b = root (via hvb), so hgraph with v b is equivalent to with root (since v b = root). Our `affineRootDirection_cleared` gives `... * v i = ... + ... * root q` (with root, not v b)? Actually cleared gives `... * v i = ... + ... * root q`? Let's check: affineRootDirection_cleared states `... * v i = ... + ... * AdjoinRoot.root q` (with root). Good. Since v b = root, this matches required hv with v b (since v b = root, rewriting gives same). Good. So hgraph holds via cleared directly (no need rw hvb). Actually cleared already has root, which equals v b via hvb, so to match required form with v b, need to rw ←hvb? Let's see: Required hv is `... * v i = ... + ... * v b`. Cleared gives `... * v i = ... + ... * root`. Since v b = root (hvb), then `... * v b = ... * root` via congr, so cleared with root rewrites to required with v b via `rw [←hvb]`? Actually cleared has root on RHS, required has v b, since v b = root, then `... * v b = ... * root` via `rw [hvb]`. So to get required from cleared, `rw [hvb]`? Cleared: `... = ... + ... * root`. Required: `... = ... + ... * v b`. Since v b = root, then `... * v b = ... * root` via `rw [hvb]`. So required follows from cleared via `rw [hvb]`? Actually cleared RHS has `* root`, required RHS has `* v b`. Since `v b = root`, then `* v b = * root` via `rw [hvb]`. Good. So `have hgraph i := affineRootDirection_cleared ... i` already gives required? No, cleared gives with root, required needs with v b. Since they are equal via hvb, we can convert. Simpler: Keep hgraph as with root (for rootEquation? Actually rootGraphEquations_mem_ideal needs hgraph with v b? Let's check its signature: It takes `hgraph : ∀ i, algebraMap ... δ * v i = ... + ... * v b` (with v b). Good. So need with v b. Good, so from cleared (with root) plus hvb, get with v b via `rw [←hvb]`? Since cleared has root, to get v b, replace root with v b via `←hvb` (since hvb : v b = root, so ←hvb : root = v b). Good. So `rw [←hvb] at h`? Actually `h := cleared`, which has root, then `rw [←hvb] at h` turns root into v b. Good.

-- cleaned

-- cleaned

-- cleaned

-- cleaned



  let F := rootGraphFamily V H q v
  have hFpure : AffineFamily.IsPure F V.dimension := rootGraphFamily_pure V H hH q hqmonic v
  have hFdom : ∀ z ∈ workingPoints V H, ∀ Γ ∈ F, ∃ d, joinPoints z d ∈ Γ.points := fun z hz Γ hΓ =>
    rootGraphFamily_dominant V H hH q hqmonic v z hz.1 (by simpa using hz.2) Γ hΓ
  have hFnorm : ∀ Γ ∈ F, ∀ w ∈ Γ.points, secondPoint w a = 1 := by
    intro Γ hΓ w hw
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    exact rootGraphVariety_normalized V H q v Q a hva w hw
  have hFcont : ∀ Γ ∈ F, ∀ w ∈ Γ.points, firstPoint w ∈ V.points := by
    intro Γ hΓ w hw
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    exact rootGraphVariety_point_containment V H hH q hqmonic v Q w hw
  have hFdim : ∀ Γ ∈ F, Γ.dimension = V.dimension := by
    intro Γ hΓ
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    exact rootGraphVariety_dimension V H hH q hqmonic v Q hQ
  have hHnonzero : ∀ x : Point (skewDim e), MvPolynomial.aeval x H ≠ 0 →
      MvPolynomial.aeval x H0 ≠ 0 ∧ MvPolynomial.aeval x (W a b) ≠ 0 ∧
      MvPolynomial.aeval x HG ≠ 0 ∧ MvPolynomial.aeval x HF2 ≠ 0 ∧
      MvPolynomial.aeval x FG.denominator ≠ 0 ∧ MvPolynomial.aeval x F2.denominator ≠ 0 ∧
      MvPolynomial.aeval x P1F.denominator ≠ 0 ∧
      MvPolynomial.aeval x S1F.denominator ≠ 0 ∧ MvPolynomial.aeval x S2F.denominator ≠ 0 ∧
      (∀ i : primaryIdx e c, MvPolynomial.aeval x (U1F i).denominator ≠ 0 ∧
        MvPolynomial.aeval x (Q1F i).denominator ≠ 0) ∧
      (∀ j : secondIdx e, MvPolynomial.aeval x (U2F j).denominator ≠ 0 ∧
        MvPolynomial.aeval x (Q2F j).denominator ≠ 0) := by
    intro x hx
    have hHGdvd : HG ∣ H := ⟨H0 * W a b * HF2 * FG.denominator * F2.denominator * P1F.denominator *
      S1F.denominator * S2F.denominator *
      (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
      (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), by dsimp [H]; ring⟩
    have hHF2dvd : HF2 ∣ H := ⟨H0 * W a b * HG * FG.denominator * F2.denominator * P1F.denominator *
      S1F.denominator * S2F.denominator *
      (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
      (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), by dsimp [H]; ring⟩
    have hP1dvd : P1F.denominator ∣ H := ⟨H0 * W a b * HG * HF2 * FG.denominator * F2.denominator *
      S1F.denominator * S2F.denominator *
      (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
      (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), by dsimp [H]; ring⟩
    have hS1dvd : S1F.denominator ∣ H := ⟨H0 * W a b * HG * HF2 * FG.denominator * F2.denominator *
      P1F.denominator * S2F.denominator *
      (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
      (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), by dsimp [H]; ring⟩
    have hS2dvd : S2F.denominator ∣ H := ⟨H0 * W a b * HG * HF2 * FG.denominator * F2.denominator *
      P1F.denominator * S1F.denominator *
      (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) *
      (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), by dsimp [H]; ring⟩
    have hU1dvd : ∀ i : primaryIdx e c, (U1F i).denominator ∣ H := by
      intro i
      have hprod : (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) ∣ H :=
        ⟨H0 * W a b * HG * HF2 * FG.denominator * F2.denominator * P1F.denominator *
          S1F.denominator * S2F.denominator *
          (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), by dsimp [H]; ring⟩
      have hmem : ((U1F i).denominator * (Q1F i).denominator) ∣
          (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have hU : (U1F i).denominator ∣ ((U1F i).denominator * (Q1F i).denominator) :=
        ⟨(Q1F i).denominator, rfl⟩
      exact dvd_trans (dvd_trans hU hmem) hprod
    have hQ1dvd : ∀ i : primaryIdx e c, (Q1F i).denominator ∣ H := by
      intro i
      have hprod : (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) ∣ H :=
        ⟨H0 * W a b * HG * HF2 * FG.denominator * F2.denominator * P1F.denominator *
          S1F.denominator * S2F.denominator *
          (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)), by dsimp [H]; ring⟩
      have hmem : ((U1F i).denominator * (Q1F i).denominator) ∣
          (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)) :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have hQ : (Q1F i).denominator ∣ ((U1F i).denominator * (Q1F i).denominator) :=
        ⟨(U1F i).denominator, by ring⟩
      exact dvd_trans (dvd_trans hQ hmem) hprod
    have hU2dvd : ∀ j : secondIdx e, (U2F j).denominator ∣ H := by
      intro j
      have hprod : (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)) ∣ H :=
        ⟨H0 * W a b * HG * HF2 * FG.denominator * F2.denominator * P1F.denominator *
          S1F.denominator * S2F.denominator *
          (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)), by dsimp [H]; ring⟩
      have hmem : ((U2F j).denominator * (Q2F j).denominator) ∣
          (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)) :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      have hU : (U2F j).denominator ∣ ((U2F j).denominator * (Q2F j).denominator) :=
        ⟨(Q2F j).denominator, rfl⟩
      exact dvd_trans (dvd_trans hU hmem) hprod
    have hQ2dvd : ∀ j : secondIdx e, (Q2F j).denominator ∣ H := by
      intro j
      have hprod : (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)) ∣ H :=
        ⟨H0 * W a b * HG * HF2 * FG.denominator * F2.denominator * P1F.denominator *
          S1F.denominator * S2F.denominator *
          (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)), by dsimp [H]; ring⟩
      have hmem : ((U2F j).denominator * (Q2F j).denominator) ∣
          (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)) :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      have hQ : (Q2F j).denominator ∣ ((U2F j).denominator * (Q2F j).denominator) :=
        ⟨(U2F j).denominator, by ring⟩
      exact dvd_trans (dvd_trans hQ hmem) hprod
    refine ⟨eval_nonzero_of_dvd H0 H hH0dvd x hx, eval_nonzero_of_dvd _ H hHdvd x hx,
      eval_nonzero_of_dvd _ H hHGdvd x hx, eval_nonzero_of_dvd _ H hHF2dvd x hx,
      eval_nonzero_of_dvd _ H hFGdvd x hx, eval_nonzero_of_dvd _ H hF2dvd x hx,
      eval_nonzero_of_dvd _ H hP1dvd x hx,
      eval_nonzero_of_dvd _ H hS1dvd x hx, eval_nonzero_of_dvd _ H hS2dvd x hx, ?_, ?_⟩
    · intro i
      exact ⟨eval_nonzero_of_dvd _ H (hU1dvd i) x hx, eval_nonzero_of_dvd _ H (hQ1dvd i) x hx⟩
    · intro j
      exact ⟨eval_nonzero_of_dvd _ H (hU2dvd j) x hx, eval_nonzero_of_dvd _ H (hQ2dvd j) x hx⟩
  have hR : F2.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
      (principalCoordinateMap V H).toRingHom) (v b) = 0 := by
    rw [hvb]
    exact localPolynomial_root_relation F2 H hF2dvd
  have hsmoothBase : ∀ Γ ∈ F, ∀ w ∈ rulingPoints Γ H,
      V.IsSmoothAt (firstPoint w) ∧
      V.tangentSpace (firstPoint w) = ⨅ i : Fin c, LinearMap.ker (differential (g i) (firstPoint w)) := by
    intro Γ hΓ w hw
    obtain ⟨hwΓ, hwH⟩ := hw
    have hxV : firstPoint w ∈ V.points := hFcont Γ hΓ w hwΓ
    have hxH0 : MvPolynomial.aeval (firstPoint w) H0 ≠ 0 :=
      (hHnonzero (firstPoint w) hwH).1
    have hxH0eval : MvPolynomial.eval (firstPoint w) H0 ≠ 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using hxH0
    exact hreg (firstPoint w) hxV hxH0eval
  have hR : F2.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
      (principalCoordinateMap V H).toRingHom) (v b) = 0 := by
    rw [hvb]
    exact localPolynomial_root_relation F2 H hF2dvd
  have hsmooth : ∀ Γ ∈ F, ∀ w ∈ rulingPoints Γ H, Γ.IsSmoothAt w := by
    intro Γ hΓ w hw
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    obtain ⟨hwΓ, hwH⟩ := hw
    have hxV : firstPoint w ∈ V.points := hFcont _ hΓ _ hwΓ
    have hxH : MvPolynomial.aeval (firstPoint w) H ≠ 0 := hwH
    have hxH0 : MvPolynomial.aeval (firstPoint w) H0 ≠ 0 := (hHnonzero _ hxH).1
    have hxW : MvPolynomial.aeval (firstPoint w) (W a b) ≠ 0 :=
      (hHnonzero _ hxH).2.1
    have hxHG : MvPolynomial.aeval (firstPoint w) HG ≠ 0 :=
      (hHnonzero _ hxH).2.2.1
    have hxHF2 : MvPolynomial.aeval (firstPoint w) HF2 ≠ 0 :=
      (hHnonzero _ hxH).2.2.2.1
    obtain ⟨hsm, htan⟩ := hsmoothBase _ hΓ w ⟨hwΓ, hwH⟩
    have hgraphVb : ∀ i, algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (principalCoordinateMap V H δ) * v i =
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (Bf i)) +
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (Af i)) *
          v b := by
      intro i
      simpa [hvb] using hgraph i
    have hRvb : F2.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
        (principalCoordinateMap V H).toRingHom) (v b) = 0 := hR
    have hroot : F2.numerator.eval₂ (MvPolynomial.aeval (firstPoint w)).toRingHom
        (secondPoint w b) = 0 := by
      have h := rootGraphVariety_root_condition V H q v Q F2.numerator b hRvb w hwΓ
      simpa using h
    have hderiv : (F2.numerator.map (MvPolynomial.aeval (firstPoint w)).toRingHom).derivative.eval
        (secondPoint w b) ≠ 0 := by
      have hgood := hF2good (firstPoint w) hxV (by
        have h := (hHnonzero (firstPoint w) hwH).2.2.2.1
        simpa using h)
      have hdeg : (F2.numerator.map (MvPolynomial.aeval (firstPoint w)).toRingHom).natDegree =
          P2.natDegree := by
        have h1 := F2.specialized_degree (by rw [hF2val]; exact hP2monic) (by rw [hF2val]; exact hF2deg)
          (firstPoint w) hxV (by
          have h := (hHnonzero (firstPoint w) hwH).2.2.2.2.2.1
          simpa using h)
        simpa [hF2val] using h1
      have hrootEval : (F2.numerator.map (MvPolynomial.aeval (firstPoint w)).toRingHom).eval
          (secondPoint w b) = 0 := by
        simpa [Polynomial.eval_map] using hroot
      exact hgood.2.2.2 _ hrootEval
    have hsmth := rootGraphVariety_smooth_tangent (V := V) (hV := hV) (hcodim := hcodim)
      (H := H) (hH := hH) (q := q) (hq := hqmonic) (v := v) (Q := Q) (hQ := hQ)
      (g := g) (hg := fun i => (hg i).1) (R := F2.numerator) (δ := δ) (B := Bf) (A := Af) (b := b)
      (hR := hR) (hgraph := hgraphVb) (w := w) (hw := hwΓ)
      (hsmooth := hsm) (htan := htan) (hδ := hxW)
      (hderiv := by simpa [Polynomial.derivative_map, Polynomial.eval_map] using hderiv)
    exact hsmth.1
  -- Primary test fraction packages at uniform budget.
  have hwAll : ∀ l : Fin c, ∀ p q : Fin e,
      ((normalPolynomial C (g l)) p q).totalDegree ≤ D :=
    fun l p q => normalPolynomial_le_of_bound C _ ((hg l).2) p q
  have hle_res : 2 * D ≤ (mMax * 4 + 1) * (Bmax * (3 * D)) := by
    calc 2 * D ≤ 3 * D := Nat.mul_le_mul_right D (by decide)
      _ = 1 * (1 * (3 * D)) := by ring
      _ ≤ (mMax * 4 + 1) * (Bmax * (3 * D)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ hBmax)
  have hle_first : 3 * D ≤ (mMax * 4 + 1) * (Bmax * (3 * D)) := by
    calc 3 * D = 1 * (1 * (3 * D)) := by ring
      _ ≤ (mMax * 4 + 1) * (Bmax * (3 * D)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ hBmax)
  have hle_Q1 : (2 + 1) * (Bmax * (3 * D))
      ≤ (mMax * 4 + 1) * (Bmax * (3 * D)) :=
    Nat.mul_le_mul_right _ (by omega)
  let mPrim := Fintype.card (primaryIdx e c)
  let ePrim : primaryIdx e c ≃ Fin mPrim := Fintype.equivFin _
  set Fprim : Fin mPrim → ParameterFraction V ((mMax * 4 + 1) * (Bmax * (3 * D))) :=
    fun j => match ePrim.symm j with
      | Sum.inl (l, i, j) =>
        (ParameterFraction.ofPolynomial
          (residualParameterPolynomial (normalPolynomial C (g first))
            (normalPolynomial C (g l)) a b i j)
          (residualParameterPolynomial_coefficients _ _ (hwAll first) (hwAll l) a b i j)).mono
        hle_res
      | Sum.inr (i, j, l) =>
        (ParameterFraction.ofPolynomial
          (firstHorizontalTest C (normalPolynomial C (g first)) a b i j l)
          (firstHorizontalTest_coefficients C (normalPolynomial C (g first))
            (hwAll first) a b i j l)).mono
        hle_first
    with hFprim
  set Qprim : Fin mPrim → ParameterFraction V ((mMax * 4 + 1) * (Bmax * (3 * D))) :=
    fun j => ((Q1F (ePrim.symm j)).mono hle_Q1) with hQprim
  set Uprim : Fin mPrim → ParameterFraction V ((mMax * 4 + 1) * (Bmax * (3 * D))) :=
    fun j => U1F (ePrim.symm j) with hUprim
  have hFprimVal : ∀ j : Fin mPrim, (Fprim j).value
      = primaryPoly C V g first a b (ePrim.symm j) := by
    intro j
    obtain ⟨i, rfl⟩ := ePrim.surjective j
    simp only [hFprim, Equiv.symm_apply_apply]
    cases i with
    | inl h =>
      obtain ⟨l, i, j⟩ := h
      simp only [ParameterFraction.value_mono, ParameterFraction.value_ofPolynomial,
        primaryPoly]
    | inr h =>
      obtain ⟨i, j, l⟩ := h
      simp only [ParameterFraction.value_mono, ParameterFraction.value_ofPolynomial,
        primaryPoly]
  have hQprimVal : ∀ j : Fin mPrim, (Qprim j).value = Q1 (ePrim.symm j) := by
    intro j
    obtain ⟨i, rfl⟩ := ePrim.surjective j
    simp only [hQprim, Equiv.symm_apply_apply, ParameterFraction.value_mono]
    exact (hQ1F _).1
  have hUprimVal : ∀ j : Fin mPrim, (Uprim j).value = U1 (ePrim.symm j) := by
    intro j
    obtain ⟨i, rfl⟩ := ePrim.surjective j
    simp only [hUprim, Equiv.symm_apply_apply]
    exact (hU1F _).1
  have hprimQuot : ∀ j : Fin mPrim,
      (Fprim j).value = P1F.value * (Qprim j).value := by
    intro j
    rw [hFprimVal j, hQprimVal j, hP1Fval]
    exact hP1quot _
  have hbezPrim : P1F.value
      = ∑ j : Fin mPrim, (Fprim j).value * (Uprim j).value := by
    rw [hP1Fval, hP1bez]
    apply Fintype.sum_equiv ePrim
    intro i
    simp only [Equiv.symm_apply_apply, hFprimVal, hUprimVal]
  have hm2c : 1 ≤ Fintype.card (secondIdx e) :=
    Fintype.card_pos_iff.mpr ⟨none⟩
  have hle_Q2 : (3 + 1) * (B2 * (D + Msr * (3 * (Bmax * (3 * D)))))
      ≤ (Fintype.card (secondIdx e) * 9 + 1) * (B2 * (D + Msr * (3 * (Bmax * (3 * D))))) := by
    apply Nat.mul_le_mul_right
    calc 3 + 1 ≤ 1 * 9 + 1 := by decide
      _ ≤ Fintype.card (secondIdx e) * 9 + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right 9 hm2c) 1
  let mSec := Fintype.card (secondIdx e)
  let eSec : secondIdx e ≃ Fin mSec := Fintype.equivFin _
  set Fsec : Fin mSec → ParameterFraction V (D + Msr * (3 * (Bmax * (3 * D)))) :=
    fun j => match eSec.symm j with
      | none => FG.mono (Nat.le_add_left _ _)
      | some (i, j) =>
        ParameterFraction.ofPolynomial
          (secondHorizontalTest C W a b i j FG.numerator)
          (secondHorizontalTest_coefficients C W hw a b i j FG.numerator hQG)
    with hFsec
  set Qsec : Fin mSec → ParameterFraction V
      ((Fintype.card (secondIdx e) * 9 + 1) * (B2 * (D + Msr * (3 * (Bmax * (3 * D)))))) :=
    fun j => ((Q2F (eSec.symm j)).mono hle_Q2) with hQsec
  set Usec : Fin mSec → ParameterFraction V
      ((Fintype.card (secondIdx e) * 9 + 1) * (B2 * (D + Msr * (3 * (Bmax * (3 * D)))))) :=
    fun j => U2F (eSec.symm j) with hUsec
  have hFsecVal : ∀ j : Fin mSec, (Fsec j).value
      = secondPoly C V W a b FG.numerator G (eSec.symm j) := by
    intro j
    obtain ⟨i, rfl⟩ := eSec.surjective j
    simp only [hFsec, Equiv.symm_apply_apply]
    cases i with
    | none =>
      simp only [ParameterFraction.value_mono, hFGval, secondPoly]
    | some h =>
      obtain ⟨i, j⟩ := h
      simp only [ParameterFraction.value_ofPolynomial, secondPoly]
  have hQsecVal : ∀ j : Fin mSec, (Qsec j).value = Q2 (eSec.symm j) := by
    intro j
    obtain ⟨i, rfl⟩ := eSec.surjective j
    simp only [hQsec, Equiv.symm_apply_apply, ParameterFraction.value_mono]
    exact (hQ2F _).1
  have hUsecVal : ∀ j : Fin mSec, (Usec j).value = U2 (eSec.symm j) := by
    intro j
    obtain ⟨i, rfl⟩ := eSec.surjective j
    simp only [hUsec, Equiv.symm_apply_apply]
    exact (hU2F _).1
  have hsecQuot : ∀ j : Fin mSec,
      (Fsec j).value = F2.value * (Qsec j).value := by
    intro j
    rw [hFsecVal j, hQsecVal j, hF2val]
    exact hP2quot _
  have hbezSec : F2.value
      = ∑ j : Fin mSec, (Fsec j).value * (Usec j).value := by
    rw [hF2val, hP2bez]
    apply Fintype.sum_equiv eSec
    intro i
    simp only [Equiv.symm_apply_apply, hFsecVal, hUsecVal]
  have hS1prod : P1F.value = (FG.mul S1F).value := by
    rw [ParameterFraction.value_mul, hFGval, hS1Fval, hP1Fval]
    exact hS1eq
  have hS2prod : (FG.mul FG).value = (P1F.mul S2F).value := by
    rw [ParameterFraction.value_mul, ParameterFraction.value_mul,
      hFGval, hP1Fval, hS2Fval, ← pow_two]
    exact hS2eq
  have hFsecEval : ∀ (x : Point (skewDim e)) (t : ℂ) (i : secondIdx e),
      (Fsec (eSec i)).eval x t
      = (match i with
        | none => FG.eval x t
        | some (p, q) => (secondHorizontalTest C W a b p q FG.numerator).eval₂
          (MvPolynomial.aeval x).toRingHom t) := by
    intro x t i
    simp only [hFsec, Equiv.symm_apply_apply]
    cases i with
    | none => simp only [ParameterFraction.eval_mono]
    | some h =>
      obtain ⟨p, q⟩ := h
      simp only [ParameterFraction.eval, ParameterFraction.ofPolynomial, map_one,
        div_one]
  have hFprimEval : ∀ (x : Point (skewDim e)) (t : ℂ) (i : primaryIdx e c),
      (Fprim (ePrim i)).eval x t
      = (match i with
        | Sum.inl (l, i, j) => (residualParameterPolynomial (normalPolynomial C (g first))
            (normalPolynomial C (g l)) a b i j).eval₂ (MvPolynomial.aeval x).toRingHom t
        | Sum.inr (i, j, l) => (firstHorizontalTest C (normalPolynomial C (g first)) a b i j l).eval₂
            (MvPolynomial.aeval x).toRingHom t) := by
    intro x t i
    simp only [hFprim, Equiv.symm_apply_apply]
    cases i with
    | inl h =>
      obtain ⟨l, i, j⟩ := h
      simp only [ParameterFraction.eval_mono]
      simp only [ParameterFraction.eval, ParameterFraction.ofPolynomial, map_one,
        div_one]
    | inr h =>
      obtain ⟨i, j, l⟩ := h
      simp only [ParameterFraction.eval_mono]
      simp only [ParameterFraction.eval, ParameterFraction.ofPolynomial, map_one,
        div_one]
  have htanTransfer : ∀ (x : Point (skewDim e)) (t : ℂ),
      x ∈ V.points → MvPolynomial.aeval x H ≠ 0 → F2.eval x t = 0 →
      (∀ l i j, (residualParameterPolynomial (normalPolynomial C (g first))
        (normalPolynomial C (g l)) a b i j).eval₂
        (MvPolynomial.aeval x).toRingHom t = 0) ∧
      (∀ i j l, (firstHorizontalTest C (normalPolynomial C (g first)) a b i j l).eval₂
        (MvPolynomial.aeval x).toRingHom t = 0) ∧
      FG.numerator.eval₂ (MvPolynomial.aeval x).toRingHom t = 0 ∧
      (∀ i j, (secondHorizontalTest C W a b i j FG.numerator).eval₂
        (MvPolynomial.aeval x).toRingHom t = 0) := by
    intro x t hx hxH hF2root
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero x hxH
    have hsec := (ParameterFraction.common_roots_of_gcd_identities
      Fsec F2 Qsec Usec hsecQuot hbezSec x hx t
      (fun j => by
        obtain ⟨i, rfl⟩ := eSec.surjective j
        simp only [hFsec, Equiv.symm_apply_apply]
        cases i with
        | none => exact hFGx
        | some h =>
          obtain ⟨i, j⟩ := h
          show MvPolynomial.aeval x 1 ≠ 0
          rw [map_one]
          exact one_ne_zero)
      hF2x
      (fun j => by
        obtain ⟨i, rfl⟩ := eSec.surjective j
        simp only [hQsec, Equiv.symm_apply_apply]
        exact (hUQ2x _).2)
      (fun j => by
        obtain ⟨i, rfl⟩ := eSec.surjective j
        simp only [hUsec, Equiv.symm_apply_apply]
        exact (hUQ2x _).1)).mp hF2root
    have hGroot : FG.eval x t = 0 := by
      have h := hsec (eSec none)
      rw [hFsecEval x t none] at h
      simpa using h
    have hFGnum0 : FG.numerator.eval₂ (MvPolynomial.aeval x).toRingHom t = 0 := by
      have hdiv : FG.numerator.eval₂ (MvPolynomial.aeval x).toRingHom t
          / MvPolynomial.aeval x FG.denominator = 0 := hGroot
      exact (div_eq_zero_iff.mp hdiv).resolve_right hFGx
    have hsecond0 : ∀ i j : Fin e, (secondHorizontalTest C W a b i j FG.numerator).eval₂
        (MvPolynomial.aeval x).toRingHom t = 0 := by
      intro i j
      have h := hsec (eSec (some (i, j)))
      rw [hFsecEval x t (some (i, j))] at h
      simpa [ParameterFraction.eval, ParameterFraction.ofPolynomial] using h
    have hP1root : P1F.eval x t = 0 := by
      have heq := ParameterFraction.eval_eq_of_value_eq P1F (FG.mul S1F) hS1prod
        x hx t hP1x
        (by simpa only [ParameterFraction.mul, map_mul] using mul_ne_zero hFGx hS1x)
      rw [heq, ParameterFraction.eval_mul, hGroot, zero_mul]
    have hprim := (ParameterFraction.common_roots_of_gcd_identities
      Fprim P1F Qprim Uprim hprimQuot hbezPrim x hx t
      (fun j => by
        obtain ⟨i, rfl⟩ := ePrim.surjective j
        simp only [hFprim, Equiv.symm_apply_apply]
        cases i with
        | inl h =>
          obtain ⟨l, i, j⟩ := h
          show MvPolynomial.aeval x 1 ≠ 0
          rw [map_one]
          exact one_ne_zero
        | inr h =>
          obtain ⟨i, j, l⟩ := h
          show MvPolynomial.aeval x 1 ≠ 0
          rw [map_one]
          exact one_ne_zero)
      hP1x
      (fun j => by
        obtain ⟨i, rfl⟩ := ePrim.surjective j
        simp only [hQprim, Equiv.symm_apply_apply]
        exact (hUQ1x _).2)
      (fun j => by
        obtain ⟨i, rfl⟩ := ePrim.surjective j
        simp only [hUprim, Equiv.symm_apply_apply]
        exact (hUQ1x _).1)).mp hP1root
    constructor
    · intro l i j
      have h := hprim (ePrim (Sum.inl (l, i, j)))
      rw [hFprimEval x t (Sum.inl (l, i, j))] at h
      simpa using h
    · constructor
      · intro i j l
        have h := hprim (ePrim (Sum.inr (i, j, l)))
        rw [hFprimEval x t (Sum.inr (i, j, l))] at h
        simpa using h
      · exact ⟨hFGnum0, hsecond0⟩
  have hdenFprim : ∀ (x : Point (skewDim e)) (_ : MvPolynomial.aeval x H ≠ 0)
      (j : Fin mPrim), MvPolynomial.aeval x ((Fprim j).denominator) ≠ 0 := by
    intro x hxH j
    obtain ⟨i, rfl⟩ := ePrim.surjective j
    simp only [hFprim, Equiv.symm_apply_apply]
    cases i with
    | inl h =>
      obtain ⟨l, i, j⟩ := h
      show MvPolynomial.aeval x 1 ≠ 0
      rw [map_one]
      exact one_ne_zero
    | inr h =>
      obtain ⟨i, j, l⟩ := h
      show MvPolynomial.aeval x 1 ≠ 0
      rw [map_one]
      exact one_ne_zero
  have hdenQprim : ∀ (x : Point (skewDim e)) (hxH : MvPolynomial.aeval x H ≠ 0)
      (j : Fin mPrim), MvPolynomial.aeval x ((Qprim j).denominator) ≠ 0 := by
    intro x hxH j
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero x hxH
    obtain ⟨i, rfl⟩ := ePrim.surjective j
    simp only [hQprim, Equiv.symm_apply_apply]
    exact (hUQ1x _).2
  have hdenUprim : ∀ (x : Point (skewDim e)) (hxH : MvPolynomial.aeval x H ≠ 0)
      (j : Fin mPrim), MvPolynomial.aeval x ((Uprim j).denominator) ≠ 0 := by
    intro x hxH j
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero x hxH
    obtain ⟨i, rfl⟩ := ePrim.surjective j
    simp only [hUprim, Equiv.symm_apply_apply]
    exact (hUQ1x _).1
  have hdenFsec : ∀ (x : Point (skewDim e)) (_ : MvPolynomial.aeval x H ≠ 0)
      (j : Fin mSec), MvPolynomial.aeval x ((Fsec j).denominator) ≠ 0 := by
    intro x hxH j
    obtain ⟨i, rfl⟩ := eSec.surjective j
    simp only [hFsec, Equiv.symm_apply_apply]
    cases i with
    | none =>
      obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
        hHnonzero x hxH
      exact hFGx
    | some h =>
      obtain ⟨i, j⟩ := h
      show MvPolynomial.aeval x 1 ≠ 0
      rw [map_one]
      exact one_ne_zero
  have hdenQsec : ∀ (x : Point (skewDim e)) (hxH : MvPolynomial.aeval x H ≠ 0)
      (j : Fin mSec), MvPolynomial.aeval x ((Qsec j).denominator) ≠ 0 := by
    intro x hxH j
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero x hxH
    obtain ⟨i, rfl⟩ := eSec.surjective j
    simp only [hQsec, Equiv.symm_apply_apply]
    exact (hUQ2x _).2
  have hdenUsec : ∀ (x : Point (skewDim e)) (hxH : MvPolynomial.aeval x H ≠ 0)
      (j : Fin mSec), MvPolynomial.aeval x ((Usec j).denominator) ≠ 0 := by
    intro x hxH j
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero x hxH
    obtain ⟨i, rfl⟩ := eSec.surjective j
    simp only [hUsec, Equiv.symm_apply_apply]
    exact (hUQ2x _).1
  have hcovPrim2P1 : ∀ (x : Point (skewDim e)) (t : ℂ),
      x ∈ V.points → MvPolynomial.aeval x H ≠ 0 →
      (∀ l i j, (residualParameterPolynomial (normalPolynomial C (g first))
        (normalPolynomial C (g l)) a b i j).eval₂
        (MvPolynomial.aeval x).toRingHom t = 0) →
      (∀ i j l, (firstHorizontalTest C (normalPolynomial C (g first)) a b i j l).eval₂
        (MvPolynomial.aeval x).toRingHom t = 0) →
      P1F.eval x t = 0 := by
    intro x t hx hxH hres hfirst
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero x hxH
    apply (ParameterFraction.common_roots_of_gcd_identities
      Fprim P1F Qprim Uprim hprimQuot hbezPrim x hx t
      (fun j => hdenFprim x hxH j) hP1x
      (fun j => hdenQprim x hxH j) (fun j => hdenUprim x hxH j)).mpr
    intro j
    obtain ⟨i, rfl⟩ := ePrim.surjective j
    rw [hFprimEval x t i]
    cases i with
    | inl h =>
      obtain ⟨l, i, j⟩ := h
      exact hres l i j
    | inr h =>
      obtain ⟨i, j, l⟩ := h
      exact hfirst i j l
  have hS2toG : ∀ (x : Point (skewDim e)) (t : ℂ),
      x ∈ V.points → MvPolynomial.aeval x H ≠ 0 → P1F.eval x t = 0 →
      FG.numerator.eval₂ (MvPolynomial.aeval x).toRingHom t = 0 := by
    intro x t hx hxH hP1root
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero x hxH
    have heq := ParameterFraction.eval_eq_of_value_eq (FG.mul FG) (P1F.mul S2F) hS2prod
      x hx t
      (by simpa only [ParameterFraction.mul, map_mul] using mul_ne_zero hFGx hFGx)
      (by simpa only [ParameterFraction.mul, map_mul] using mul_ne_zero hP1x hS2x)
    rw [ParameterFraction.eval_mul, ParameterFraction.eval_mul, hP1root, zero_mul] at heq
    have hFG0 : FG.eval x t = 0 := by
      by_contra hne
      exact (mul_ne_zero hne hne) heq
    have hnum : FG.numerator.eval₂ (MvPolynomial.aeval x).toRingHom t
        / MvPolynomial.aeval x FG.denominator = 0 := hFG0
    exact (div_eq_zero_iff.mp hnum).resolve_right hFGx
  have hsecToF2 : ∀ (x : Point (skewDim e)) (t : ℂ),
      x ∈ V.points → MvPolynomial.aeval x H ≠ 0 →
      (∀ j : Fin mSec, (Fsec j).eval x t = 0) → F2.eval x t = 0 := by
    intro x t hx hxH hall
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero x hxH
    exact (ParameterFraction.common_roots_of_gcd_identities
      Fsec F2 Qsec Usec hsecQuot hbezSec x hx t
      (fun j => hdenFsec x hxH j) hF2x
      (fun j => hdenQsec x hxH j) (fun j => hdenUsec x hxH j)).mpr hall
  have hGdiv2 : G = P2 * Q2 none := by
    simpa only [secondPoly] using hP2quot none
  have hGprod : FG.value = F2.value * (Q2F none).value := by
    rw [hFGval, hF2val, (hQ2F none).1]
    exact hGdiv2
  have hR_FG : FG.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
      (principalCoordinateMap V H).toRingHom) (v b) = 0 := by
    have hQnone : (Q2F none).denominator ∣ H := by
      have hprod : (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)) ∣ H :=
        ⟨H0 * W a b * HG * HF2 * FG.denominator * F2.denominator * P1F.denominator *
          S1F.denominator * S2F.denominator *
          (∏ i : primaryIdx e c, ((U1F i).denominator * (Q1F i).denominator)), by dsimp [H]; ring⟩
      have hmem : ((U2F none).denominator * (Q2F none).denominator) ∣
          (∏ j : secondIdx e, ((U2F j).denominator * (Q2F j).denominator)) :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ none)
      have hQ : (Q2F none).denominator ∣ ((U2F none).denominator * (Q2F none).denominator) :=
        ⟨(U2F none).denominator, by ring⟩
      exact dvd_trans (dvd_trans hQ hmem) hprod
    have hrel := parameter_fraction_divisible_root_relation V F2 FG (Q2F none) H hH
      hF2dvd hFGdvd hQnone hGprod
    rw [hvb]
    exact hrel
  have hsmoothFG : ∀ Γ ∈ F, ∀ w ∈ rulingPoints Γ H,
      Γ.IsSmoothAt w ∧ V.IsSmoothAt (firstPoint w) ∧
      Γ.tangentSpace w =
        LinearMap.ker (TrackA.evaluatedJacobian
          (rootGraphEquations g FG.numerator δ Bf Af b) w).mulVecLin ∧
      (Γ.tangentSpace w).map (pointProjection e) =
        V.tangentSpace (firstPoint w) := by
    intro Γ hΓ w hw
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    obtain ⟨hwΓ, hwH⟩ := hw
    have hxV : firstPoint w ∈ V.points := hFcont _ hΓ _ hwΓ
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero _ hwH
    obtain ⟨hsm, htanV⟩ := hsmoothBase _ hΓ w ⟨hwΓ, hwH⟩
    have hgraphVb : ∀ i, algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)
        (principalCoordinateMap V H δ) * v i =
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (Bf i)) +
        algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q) (principalCoordinateMap V H (Af i)) *
          v b := by
      intro i
      simpa [hvb] using hgraph i
    have hrootFG : FG.numerator.eval₂ (MvPolynomial.aeval (firstPoint w)).toRingHom
        (secondPoint w b) = 0 := by
      have h := rootGraphVariety_root_condition V H q v Q FG.numerator b hR_FG w hwΓ
      simpa using h
    have hderivFG : (FG.numerator.map (MvPolynomial.aeval (firstPoint w)).toRingHom).derivative.eval
        (secondPoint w b) ≠ 0 := by
      have hgood := hFGgood (firstPoint w) hxV hHGx
      have hdeg : (FG.numerator.map (MvPolynomial.aeval (firstPoint w)).toRingHom).natDegree =
          G.natDegree := by
        have h1 := FG.specialized_degree (by rw [hFGval]; exact hGmonic) (by rw [hFGval]; exact hFGdeg)
          (firstPoint w) hxV hFGx
        simpa [hFGval] using h1
      have hrootEval : (FG.numerator.map (MvPolynomial.aeval (firstPoint w)).toRingHom).eval
          (secondPoint w b) = 0 := by
        simpa [Polynomial.eval_map] using hrootFG
      exact hgood.2.2.2 _ hrootEval
    have hsmth := rootGraphVariety_smooth_tangent (V := V) (hV := hV) (hcodim := hcodim)
      (H := H) (hH := hH) (q := q) (hq := hqmonic) (v := v) (Q := Q) (hQ := hQ)
      (g := g) (hg := fun i => (hg i).1) (R := FG.numerator) (δ := δ) (B := Bf) (A := Af) (b := b)
      (hR := hR_FG) (hgraph := hgraphVb) (w := w) (hw := hwΓ)
      (hsmooth := hsm) (htan := htanV) (hδ := hWx)
      (hderiv := by simpa [Polynomial.derivative_map, Polynomial.eval_map] using hderivFG)
    exact ⟨hsmth.1, hsm, hsmth.2.1, hsmth.2.2⟩
  have htan : ∀ Γ ∈ F, ∀ w ∈ rulingPoints Γ H, ∀ i l : Fin e,
      joinPoints (C.decode.symm (normalizedKernelPair a (secondPoint w) i l)) 0
        ∈ Γ.tangentSpace w := by
    intro Γ hΓ w hw i l
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    obtain ⟨hwΓ, hwH⟩ := hw
    have hxV : firstPoint w ∈ V.points := hFcont _ hΓ _ hwΓ
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero _ hwH
    obtain ⟨hsmW, hsmV, hkerV, hprojV⟩ := hsmoothFG _ hΓ w ⟨hwΓ, hwH⟩
    obtain ⟨hsmV2, htanEq⟩ := hsmoothBase _ hΓ w ⟨hwΓ, hwH⟩
    have hroot2 : F2.numerator.eval₂ (MvPolynomial.aeval (firstPoint w)).toRingHom
        (secondPoint w b) = 0 := by
      have hRvb : F2.numerator.eval₂ ((algebraMap (PrincipalCoordinateRing V H) (AdjoinRoot q)).comp
          (principalCoordinateMap V H).toRingHom) (v b) = 0 := hR
      have h := rootGraphVariety_root_condition V H q v Q F2.numerator b hRvb w hwΓ
      simpa using h
    have hF2eval0 : F2.eval (firstPoint w) (secondPoint w b) = 0 := by
      show F2.numerator.eval₂ (MvPolynomial.aeval (firstPoint w)).toRingHom (secondPoint w b)
        / MvPolynomial.aeval (firstPoint w) F2.denominator = 0
      rw [hroot2, zero_div]
    obtain ⟨hres, hfirst, hFGnum, hsecond⟩ :=
      htanTransfer (firstPoint w) (secondPoint w b) hxV hwH hF2eval0
    have hpivot : MvPolynomial.aeval (firstPoint w) (W a b) ≠ 0 :=
      eval_nonzero_of_dvd _ H hHdvd _ hwH
    have hptgraph (m : Fin e) : MvPolynomial.aeval (firstPoint w) δ * secondPoint w m =
        MvPolynomial.aeval (firstPoint w) (Bf m) +
        MvPolynomial.aeval (firstPoint w) (Af m) * secondPoint w b :=
      rootGraphVariety_graph_coordinate V H q v Q δ (Bf m) (Af m) b m
        (by simpa [hvb] using hgraph m) w hwΓ
    have hvalgraph (m : Fin e) : MvPolynomial.aeval (firstPoint w) (W a b) * secondPoint w m =
        MvPolynomial.aeval (firstPoint w) (W m b) +
        MvPolynomial.aeval (firstPoint w) (W a m) * secondPoint w b :=
      hptgraph m
    have hugraph : secondPoint w = directionGraph
        (fun k l => MvPolynomial.aeval (firstPoint w) (W k l)) a b (secondPoint w b) :=
      directionGraph_of_cleared_equations _ a b hpivot _ hvalgraph
    have hconstraints (l : Fin c) : SkewChartConstraints
        (fun k m => MvPolynomial.aeval (firstPoint w) (normalPolynomial C (g l) k m))
        a (secondPoint w) := by
      rw [hugraph]
      apply (directionGraph_constraints_iff (K := ℂ) _ _ a b hpivot (secondPoint w b)).mpr
      intro k m
      have h := hres l k m
      rw [eval_residualParameterPolynomial] at h
      exact h
    have hkernel := normalized_kernel_tangent_of_constraints C V g (firstPoint w)
      htanEq a (secondPoint w) (hFnorm _ hΓ _ hwΓ) hconstraints i l
    have hgraphH : ∀ m : Fin e, MvPolynomial.aeval (firstPoint w) (W m b) +
        secondPoint w b * MvPolynomial.aeval (firstPoint w) (W a m) =
        MvPolynomial.aeval (firstPoint w) (W a b) * secondPoint w m := by
      intro m
      linear_combination -hvalgraph m
    exact horizontal_tangent_of_tests C V _ g W FG.numerator a b w hkerV htanEq hpivot
      hgraphH i l hkernel (fun m => hfirst i l m) (hsecond i l)
  have hlocFin : ∀ z : Point (skewDim e), z ∈ V.points →
      MvPolynomial.aeval z H ≠ 0 →
      ({d : Point e | joinPoints z d ∈ (AffineFamily.locus F).points}.Finite ∧
        {d : Point e | joinPoints z d ∈ (AffineFamily.locus F).points}.ncard ≤ 2) := by
    intro z hz hzH
    obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
      hHnonzero z hzH
    have hRz : FG.numerator.map (MvPolynomial.aeval z).toRingHom ≠ 0 :=
      FG.specialized_nonzero (by rw [hFGval]; exact hGmonic) z hz hFGx
    obtain ⟨hfin, hcard⟩ := rootGraphFamily_finite_fiber V H q v FG.numerator δ Bf Af b
      hR_FG (fun i => by simpa [hvb] using hgraph i) z hWx hRz
    refine ⟨hfin, ?_⟩
    have hdeg : (FG.numerator.map (MvPolynomial.aeval z).toRingHom).natDegree =
        G.natDegree := by
      have h1 := FG.specialized_degree (by rw [hFGval]; exact hGmonic) (by rw [hFGval]; exact hFGdeg)
        z hz hFGx
      simpa [hFGval] using h1
    calc {d : Point e | joinPoints z d ∈ (AffineFamily.locus F).points}.ncard
        ≤ (FG.numerator.map (MvPolynomial.aeval z).toRingHom).natDegree := hcard
      _ = G.natDegree := hdeg
      _ ≤ 2 := hGdeg
  have hfinGamma : ∀ Γ ∈ F, ∀ z ∈ workingPoints V H,
      (directionFiber Γ z).Finite ∧ (directionFiber Γ z).ncard ≤ Broot := by
    intro Γ hΓ z hz
    obtain ⟨hzV, hzH⟩ := hz
    obtain ⟨hfin, hcard⟩ := hlocFin z hzV hzH
    have hsub : directionFiber Γ z
        ⊆ {d : Point e | joinPoints z d ∈ (AffineFamily.locus F).points} := by
      intro d hd
      rw [AffineFamily.points_locus]
      exact Set.mem_biUnion hΓ hd
    refine ⟨hfin.subset hsub, ?_⟩
    calc (directionFiber Γ z).ncard ≤ _ := Set.ncard_le_ncard hsub hfin
      _ ≤ 2 := hcard
      _ ≤ Broot := hBroot2
  have hdomGamma : ∀ Γ ∈ F, ∀ z ∈ workingPoints V H, (directionFiber Γ z).Nonempty := by
    intro Γ hΓ z hz
    obtain ⟨d, hd⟩ := hFdom z hz Γ hΓ
    exact ⟨d, hd⟩
  have hprops : ∀ Γ ∈ F, IsRulingIncidence C V Γ H a 0 Broot := by
    intro Γ hΓ
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    exact rulingIncidence_of_horizontal_tangency C V _ H a 0 Broot hV
      (hFpure _ hΓ).1 hH
      (rootGraphVariety_section_nonzero V H hH q hqmonic v Q hQ)
      (by decide) (by omega)
      (by have h := hFdim _ hΓ; omega) (hFnorm _ hΓ) (hFcont _ hΓ)
      (fun z hz => hdomGamma _ hΓ z hz)
      (fun w hw => let t := hsmoothFG _ hΓ w hw; ⟨t.1, t.2.1, t.2.2.2⟩)
      (fun _ => hfinGamma _ hΓ)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (htan _ hΓ)
  obtain ⟨z0, hzv0, hzH0aeval⟩ := exists_principal_open_point V H hH
  have hzH0 : MvPolynomial.eval z0 H ≠ 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using hzH0aeval
  obtain ⟨hH0z0, hWz0, hHGz0, hHF2z0, hFGz0, hF2z0, hP1z0, hS1z0, hS2z0, hUQ1z0, hUQ2z0⟩ :=
    hHnonzero z0 hzH0aeval
  have hzH0eval : MvPolynomial.eval z0 H0 ≠ 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using hH0z0
  obtain ⟨hsmz0, htnz0⟩ := hreg z0 hzv0 hzH0eval
  have hRz0 : FG.numerator.map (MvPolynomial.aeval z0).toRingHom ≠ 0 :=
    FG.specialized_nonzero (by rw [hFGval]; exact hGmonic) z0 hzv0 hFGz0
  have hderiv0 : ∀ d : Point e, joinPoints z0 d ∈ (AffineFamily.locus F).points →
      FG.numerator.derivative.eval₂ (MvPolynomial.aeval z0).toRingHom (d b) ≠ 0 := by
    intro d hd
    rw [AffineFamily.points_locus] at hd
    obtain ⟨Γ, hΓ, hdΓ⟩ := (by simpa only [Set.mem_iUnion, exists_prop] using hd :
      ∃ Γ ∈ F, joinPoints z0 d ∈ Γ.points)
    obtain ⟨Q, hQprime, hQ, rfl⟩ := (mem_rootGraphFamily V H q v Γ).mp hΓ
    have hxfirst : firstPoint (joinPoints z0 d) = z0 := by ext i; simp [firstPoint, joinPoints]
    have hxsecond : secondPoint (joinPoints z0 d) = d := by ext i; simp [secondPoint, joinPoints]
    have hroot0 : FG.numerator.eval₂ (MvPolynomial.aeval z0).toRingHom (d b) = 0 := by
      have h := rootGraphVariety_root_condition V H q v Q FG.numerator b hR_FG
        (joinPoints z0 d) hdΓ
      rw [hxfirst, hxsecond] at h
      exact h
    have hgood := hFGgood z0 hzv0 hHGz0
    have hrootEval : (FG.numerator.map (MvPolynomial.aeval z0).toRingHom).eval (d b) = 0 := by
      simpa [Polynomial.eval_map] using hroot0
    have hder := hgood.2.2.2 _ hrootEval
    simpa [Polynomial.derivative_map, Polynomial.eval_map] using hder
  have hcard : F.card
      ≤ (FG.numerator.map (MvPolynomial.aeval z0).toRingHom).natDegree :=
    rootGraphFamily_card_le_degree V hV hcodim H hH q hqmonic v g (fun i => (hg i).1)
      FG.numerator δ Bf Af b hR_FG (fun i => by simpa [hvb] using hgraph i) z0 hzv0 hzH0
      hsmz0 htnz0 (eval_nonzero_of_dvd δ H hHdvd z0 hzH0aeval) hRz0 hderiv0
  have hdeg0 : (FG.numerator.map (MvPolynomial.aeval z0).toRingHom).natDegree ≤ 2 := by
    have h1 := FG.specialized_degree (by rw [hFGval]; exact hGmonic) (by rw [hFGval]; exact hFGdeg)
      z0 hzv0 hFGz0
    have h2 : (FG.numerator.map (MvPolynomial.aeval z0).toRingHom).natDegree = G.natDegree := by
      simpa [hFGval] using h1
    rw [h2]
    exact hGdeg
  have hle : F.card ≤ Broot := by
    calc F.card ≤ (FG.numerator.map (MvPolynomial.aeval z0).toRingHom).natDegree := hcard
      _ ≤ 2 := hdeg0
      _ ≤ Broot := hBroot2
  have hcoverage : ∀ p ∈ affineParameters e, firstPoint p.rep a ≠ 0 → evaluationFlat C p ⊆ V.points →
      evaluationFlat C p ⊆ (V.cut H).points ∨
        ∃ i : Fin F.card, p ∈ parameterImage C ((F.equivFin.symm i).val) H := by
    intro p hp ha hflat
    by_cases hcut : evaluationFlat C p ⊆ (V.cut H).points
    · exact Or.inl hcut
    · have hpoint : ∃ x ∈ evaluationFlat C p, MvPolynomial.aeval x H ≠ 0 := by
        by_contra hn
        push_neg at hn
        apply hcut
        intro x hx
        exact (point_mem_cut_iff V H x).mpr ⟨hflat hx, hn x hx⟩
      obtain ⟨x, hx, hxH⟩ := hpoint
      have hxV : x ∈ V.points := hflat hx
      obtain ⟨hH0x, hWx, hHGx, hHF2x, hFGx, hF2x, hP1x, hS1x, hS2x, hUQ1x, hUQ2x⟩ :=
        hHnonzero x hxH
      have hxHeval : MvPolynomial.eval x H ≠ 0 := by
        simpa only [MvPolynomial.aeval_eq_eval] using hxH
      let s := firstPoint p.rep a
      let u : Point e := s⁻¹ • firstPoint p.rep
      have hs : s ≠ 0 := ha
      have hua : u a = 1 := by change s⁻¹ * s = 1; exact inv_mul_cancel₀ hs
      have hu : u ≠ 0 := by
        intro h
        have he := congrFun h a
        rw [hua, Pi.zero_apply] at he
        exact one_ne_zero he
      have hscale : firstPoint p.rep = s • u := by
        dsimp [u]
        rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
      have hwflat := contained_flat_normal_constraints C p V hflat x hx (g first) (hg first).1
        u a hua s hscale
      have hpivotW : MvPolynomial.aeval x (W a b) ≠ 0 :=
        eval_nonzero_of_dvd _ H hHdvd x hxH
      have hq0away : ∀ y ∈ evaluationFlat C p, MvPolynomial.aeval y H ≠ 0 →
          MvPolynomial.aeval y (FG.numerator.eval (MvPolynomial.C (u b))) = 0 := by
        intro y hy hyH
        have hyV : y ∈ V.points := hflat hy
        have hresy : ∀ l i j, (residualParameterPolynomial (normalPolynomial C (g first))
            (normalPolynomial C (g l)) a b i j).eval₂
            (MvPolynomial.aeval y).toRingHom (u b) = 0 :=
          fun l i j => contained_flat_residualParameterPolynomial C p V hflat (g first) (g l)
            (hg first).1 (hg l).1 y hy u a hua s hscale b i j
            (eval_nonzero_of_dvd _ H hHdvd y hyH)
        have hfirsty : ∀ i j l, (firstHorizontalTest C (normalPolynomial C (g first)) a b i j l).eval₂
            (MvPolynomial.aeval y).toRingHom (u b) = 0 :=
          fun i j l => contained_flat_firstHorizontalTest C p V hflat (g first) (hg first).1
            y hy u a hua s hscale b i j l
        have hP1y := hcovPrim2P1 y (u b) hyV hyH hresy hfirsty
        have hGy := hS2toG y (u b) hyV hyH hP1y
        rw [eval_parameterPolynomial]
        exact hGy
      have hGnumx : FG.numerator.eval₂ (MvPolynomial.aeval x).toRingHom (u b) = 0 := by
        have h := hq0away x hx hxH
        rw [eval_parameterPolynomial] at h
        exact h
      have hQext : ∀ y ∈ evaluationFlat C p, FG.numerator.eval₂
          (MvPolynomial.aeval y).toRingHom (u b) = 0 := by
        intro y hy
        have h := polynomial_zero_on_flat_open C p hp H
          (FG.numerator.eval (MvPolynomial.C (u b))) x hx hxH hq0away y hy
        rw [eval_parameterPolynomial] at h
        exact h
      have hsecondFlat : ∀ i j : Fin e, (secondHorizontalTest C W a b i j FG.numerator).eval₂
          (MvPolynomial.aeval x).toRingHom (u b) = 0 :=
        fun i j => contained_flat_secondHorizontalTest C p V hflat (g first) (hg first).1
          x hx u a hua s hscale b i j FG.numerator hQext
      have hFGe0x : FG.eval x (u b) = 0 := by
        show FG.numerator.eval₂ (MvPolynomial.aeval x).toRingHom (u b)
          / MvPolynomial.aeval x FG.denominator = 0
        rw [hGnumx]
        exact zero_div _
      have hall : ∀ j : Fin mSec, (Fsec j).eval x (u b) = 0 := by
        intro j
        obtain ⟨i, rfl⟩ := eSec.surjective j
        rw [hFsecEval x (u b) i]
        cases i with
        | none => exact hFGe0x
        | some h =>
          obtain ⟨i, j⟩ := h
          exact hsecondFlat i j
      have hF2ev0 : F2.eval x (u b) = 0 := hsecToF2 x (u b) hxV hxH hall
      have hF2num0 : F2.numerator.eval₂ (MvPolynomial.aeval x).toRingHom (u b) = 0 := by
        have hdiv : F2.numerator.eval₂ (MvPolynomial.aeval x).toRingHom (u b)
            / MvPolynomial.aeval x F2.denominator = 0 := hF2ev0
        exact (div_eq_zero_iff.mp hdiv).resolve_right hF2x
      have hqroot : q.eval₂ (principalCoordinatePoint V H x hxV hxHeval) (u b) = 0 := by
        have hloc := F2.localPolynomial_point H hF2dvd x hxV hxHeval
        have hnum0 : (F2.numerator.map (MvPolynomial.aeval x).toRingHom).eval (u b) = 0 := by
          rw [Polynomial.eval_map]
          exact hF2num0
        have h := congrArg (fun Q : Polynomial ℂ => Q.eval (u b)) hloc
        rw [Polynomial.eval_map, Polynomial.eval_mul, Polynomial.eval_C, hnum0,
          zero_mul] at h
        exact h
      obtain ⟨Γ, hΓ, hpt⟩ := rootGraphFamily_root_coverage V H q v x hxV hxHeval (u b) hqroot
      have hwflatW : SkewChartConstraints (fun k m => MvPolynomial.aeval x (W k m)) a u :=
        hwflat
      have hueqW : ∀ i, MvPolynomial.aeval x (W a b) * u i =
          MvPolynomial.aeval x (W i b) + MvPolynomial.aeval x (W a i) * u b := by
        intro i
        have h := hwflatW i b
        linear_combination -h
      have hdlift : ∀ i, MvPolynomial.aeval x δ *
          AdjoinRoot.liftAlgHom q (principalCoordinatePoint V H x hxV hxHeval) (u b) hqroot (v i) =
          MvPolynomial.aeval x (Bf i) + MvPolynomial.aeval x (Af i) * u b := by
        intro i
        have h := congrArg (AdjoinRoot.liftAlgHom q
          (principalCoordinatePoint V H x hxV hxHeval) (u b) hqroot) (hgraph i)
        simpa [AdjoinRoot.liftAlgHom_of, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_root,
          principalCoordinatePoint_map, map_mul, map_add] using h
      have hdliftW : ∀ i, MvPolynomial.aeval x (W a b) *
          AdjoinRoot.liftAlgHom q (principalCoordinatePoint V H x hxV hxHeval) (u b) hqroot (v i) =
          MvPolynomial.aeval x (W i b) + MvPolynomial.aeval x (W a i) * u b :=
        fun i => hdlift i
      have huv : u = fun i => AdjoinRoot.liftAlgHom q
          (principalCoordinatePoint V H x hxV hxHeval) (u b) hqroot (v i) := by
        funext i
        apply mul_left_cancel₀ hpivotW
        rw [hueqW i, hdliftW i]
      have hptu : joinPoints x u ∈ Γ.points := by
        rw [huv]
        exact hpt
      have hvec : graphVector C x (firstPoint p.rep) = p.rep := by
        change joinPoints (firstPoint p.rep) (pointOfCovector ((C.decode x).val (firstPoint p.rep))) = p.rep
        rw [show (C.decode x).val (firstPoint p.rep) = covectorOfPoint (secondPoint p.rep) from hx,
          point_covector_inverse, joinPoints_eta]
      have hvecu : s⁻¹ • p.rep = graphVector C x u := by
        rw [← hvec]
        change s⁻¹ • joinPoints (firstPoint p.rep) (pointOfCovector ((C.decode x).val (firstPoint p.rep))) =
          joinPoints u (pointOfCovector ((C.decode x).val u))
        dsimp [u]
        rw [map_smul, pointOfCovector_smul, joinPoints_smul]
      have hparam : graphParameter C x u hu = p := by
        rw [← p.mk_rep]
        exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨s⁻¹, hvecu⟩
      refine Or.inr ⟨F.equivFin ⟨Γ, hΓ⟩, x, u, ?_, hu, hparam⟩
      simp only [Equiv.symm_apply_apply]
      refine ⟨hptu, ?_⟩
      have hpx : firstPoint (joinPoints x u) = x := by ext i; simp [firstPoint, joinPoints]
      rw [hpx]
      exact hxH
  refine ⟨H, hH, hHdeg, F.card, hle,
    fun i => ((F.equivFin.symm i).val), fun _ => 0,
    fun i => hprops _ (F.equivFin.symm i).property, hcoverage⟩


end
end DistinctDistances.TrackB.MBRec
