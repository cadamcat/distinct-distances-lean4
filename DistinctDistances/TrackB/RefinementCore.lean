import DistinctDistances.TrackB.EquationPrefixes
import DistinctDistances.TrackB.RefinementHelpers

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

theorem nonzero_equation_positive {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (q : Poly n) (hq : q ≠ 0) (hqV : q ∈ V.ideal) : 0 < q.totalDegree := by
  by_contra hpos
  have hdeg : q.totalDegree = 0 := by omega
  have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  have ha : q.coeff 0 ≠ 0 := by
    intro hz
    apply hq
    rw [heq, hz, MvPolynomial.C_0]
  have hunit : IsUnit (MvPolynomial.C (q.coeff 0) : Poly n) :=
    (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
  exact hV.ne_top (V.ideal.eq_top_of_isUnit_mem (heq ▸ hqV) hunit)

theorem equationPrefixIdeal_le_variety {n c : ℕ} (g : Fin c → Poly n)
    (V : AffineVariety n) (hvanish : ∀ i, g i ∈ V.ideal) (p : ℕ) :
    equationPrefixIdeal g p ≤ V.ideal := by
  apply (equationPrefixIdeal_le_span g p).trans
  apply Ideal.span_le.mpr
  rintro q ⟨i, rfl⟩
  exact hvanish i

/-- B30: avoiding the preceding prefix's relevant primes extends its dimension property. -/
theorem regular_prefix_extension {n c : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (hc : c ≤ n) (g : Fin c → Poly n) (p : ℕ) (hp : p < c)
    (hreg : ∀ r ≤ p, ∀ W : AffineVariety n,
      W.IsComponentOf (equationPrefixIdeal g r) → V.Subvariety W → W.dimension + r = n)
    (q : Poly n)
    (havoid : ∀ Q : Ideal (Poly n), Q ∈ (equationPrefixIdeal g p).minimalPrimes →
      Q ≤ V.ideal → q ∉ Q) :
    ∀ r ≤ p + 1, ∀ W : AffineVariety n,
      W.IsComponentOf (equationPrefixIdeal (Function.update g ⟨p, hp⟩ q) r) →
      V.Subvariety W → W.dimension + r = n := by
  classical
  let g' := Function.update g ⟨p, hp⟩ q
  have hsame : ∀ r ≤ p, equationPrefixIdeal g' r = equationPrefixIdeal g r := by
    intro r hr
    apply equationPrefixIdeal_congr
    intro i hi
    have hne : i ≠ ⟨p, hp⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
    simp [g', Function.update_of_ne hne]
  intro r hr W hW hVW
  by_cases hrp : r ≤ p
  · apply hreg r hrp W
    · simpa only [← hsame r hrp] using hW
    · exact hVW
  · have hre : r = p + 1 := by omega
    subst r
    have hnew : equationPrefixIdeal g' (p + 1) = equationPrefixIdeal g p ⊔ Ideal.span {q} := by
      rw [equationPrefixIdeal_succ g' p hp, hsame p le_rfl]
      simp [g']
    have hW' : W.IsComponentOf (equationPrefixIdeal g p ⊔ Ideal.span {q}) := by
      change W.IsComponentOf (equationPrefixIdeal g' (p + 1)) at hW
      rw [hnew] at hW
      exact hW
    letI : W.ideal.IsPrime := hW.isPrime
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hW'.le)
    let U : AffineVariety n := ⟨Q, hQ.isPrime.isRadical⟩
    have hVU : V.Subvariety U := hQW.trans hVW
    have hUdim : U.dimension + p = n := hreg p le_rfl U hQ hVU
    have hqnot : q ∉ Q := havoid Q hQ hVU
    have hsup : Q ⊔ Ideal.span {q} ≤ W.ideal :=
      sup_le hQW (le_sup_right.trans hW'.le)
    have hpre : equationPrefixIdeal g p ⊔ Ideal.span {q} ≤ Q ⊔ Ideal.span {q} :=
      sup_le_sup hQ.le le_rfl
    have hWcut : W.IsComponentOf (U.ideal ⊔ Ideal.span {q}) := by
      refine ⟨⟨hW.isPrime, hsup⟩, ?_⟩
      intro J hJ hJW
      exact hW'.2 ⟨hJ.1, hpre.trans hJ.2⟩ hJW
    letI : Q.IsPrime := hQ.isPrime
    have hdim : U.dimension = (n - p - 1) + 1 := by omega
    have hcut := OAI.QuarticPowerFree.proper_cut_component_dimension U.ideal W.ideal
      q hqnot hWcut hdim
    change W.dimension = n - p - 1 at hcut
    omega

/-- B30, concentration.tex:1051–1056. A bounded constant combination avoids all
prefix components containing V; the original prefix dimensions rule out containment. -/
theorem bounded_prefix_extension {n c : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (hdim : V.dimension + c = n) (f g : Fin c → Poly n) (d : Fin c → ℕ)
    (hd : Monotone d) (hdegree : ∀ j, (f j).totalDegree ≤ d j)
    (hfV : ∀ j, f j ∈ V.ideal) (hgV : ∀ j, g j ∈ V.ideal)
    (hcomp : V.IsComponentOf (Ideal.span (Set.range f)))
    (p : ℕ) (hp : p < c)
    (hreg : ∀ r ≤ p, ∀ W : AffineVariety n,
      W.IsComponentOf (equationPrefixIdeal g r) → V.Subvariety W → W.dimension + r = n) :
    ∃ q : Poly n, 0 < q.totalDegree ∧ q ∈ V.ideal ∧ q.totalDegree ≤ d ⟨p, hp⟩ ∧
      ∀ Q : Ideal (Poly n), Q ∈ (equationPrefixIdeal g p).minimalPrimes →
        Q ≤ V.ideal → q ∉ Q := by
  classical
  let T := (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n)
    (equationPrefixIdeal g p)).toFinset
  let S := T.filter (fun Q => Q ≤ V.ideal)
  have hmem : ∀ Q : Ideal (Poly n), Q ∈ S ↔
      Q ∈ (equationPrefixIdeal g p).minimalPrimes ∧ Q ≤ V.ideal := by
    intro Q
    simp [S, T]
  have horig := regular_prefix_dimensions f V hV hcomp hdim
  have hproper : ∀ Q ∈ S, ∃ j : Fin c, j.val ≤ p ∧ f j ∉ Q := by
    intro Q hQS
    obtain ⟨hQ, hQV⟩ := (hmem Q).mp hQS
    let UQ : AffineVariety n := ⟨Q, hQ.isPrime.isRadical⟩
    have hQdim : UQ.dimension + p = n := hreg p le_rfl UQ hQ hQV
    by_contra hno
    push_neg at hno
    have hfle : equationPrefixIdeal f (p + 1) ≤ Q := by
      apply Ideal.span_le.mpr
      rintro z ⟨i, rfl⟩
      change (if i.val < p + 1 then f i else 0) ∈ _
      split
      · exact hno i (by omega)
      · exact Ideal.zero_mem _
    letI : Q.IsPrime := hQ.isPrime
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hfle
    let U : AffineVariety n := ⟨P, hP.isPrime.isRadical⟩
    have hUdim : U.dimension + (p + 1) = n :=
      horig (p + 1) (by omega) U hP (hPQ.trans hQV)
    have hmono : UQ.dimension ≤ U.dimension := affine_dimension_mono U UQ hPQ
    omega
  obtain ⟨a, ha⟩ := constantPrefixCombination_avoid f ⟨p, hp⟩ S hproper
  let q := constantPrefixCombination f ⟨p, hp⟩ a
  have hbounds := constantPrefixCombination_bounds V f d hd hdegree hfV ⟨p, hp⟩ a
  have hqavoid : ∀ Q, Q ∈ (equationPrefixIdeal g p).minimalPrimes → Q ≤ V.ideal → q ∉ Q := by
    intro Q hQ hQV
    exact ha Q ((hmem Q).mpr ⟨hQ, hQV⟩)
  letI : V.ideal.IsPrime := hV
  obtain ⟨Q, hQ, hQV⟩ := Ideal.exists_minimalPrimes_le (equationPrefixIdeal_le_variety g V hgV p)
  have hqne : q ≠ 0 := by
    intro hz
    exact hqavoid Q hQ hQV (hz ▸ Ideal.zero_mem Q)
  refine ⟨q, nonzero_equation_positive V hV q hqne hbounds.2, hbounds.2, hbounds.1, hqavoid⟩

/-- B30: replace the first equation by a least-degree equation and extend it using
bounded constant combinations. The full replacement has the required prefix dimensions. -/
theorem replacement_equations_exists {n c : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (hc : 0 < c) (hdim : V.dimension + c = n) (f : Fin c → Poly n) (d : Fin c → ℕ)
    (hd : Monotone d) (hdegree : ∀ j, (f j).totalDegree ≤ d j)
    (hfpos : ∀ j, 0 < (f j).totalDegree) (hfV : ∀ j, f j ∈ V.ideal)
    (hcomp : V.IsComponentOf (Ideal.span (Set.range f))) :
    ∃ g : Fin c → Poly n,
      (∀ j, 0 < (g j).totalDegree ∧ g j ∈ V.ideal ∧ (g j).totalDegree ≤ d j) ∧
      (∀ q : Poly n, q ≠ 0 → q ∈ V.ideal → (g ⟨0, hc⟩).totalDegree ≤ q.totalDegree) ∧
      ∀ p ≤ c, ∀ W : AffineVariety n,
        W.IsComponentOf (equationPrefixIdeal g p) → V.Subvariety W → W.dimension + p = n := by
  classical
  have hseed : f ⟨0, hc⟩ ≠ 0 := by
    intro hz
    have := hfpos ⟨0, hc⟩
    rw [hz, MvPolynomial.totalDegree_zero] at this
    omega
  obtain ⟨q, hqne, hqV, hqpos, hqmin⟩ := least_degree_equation V hV _ hseed (hfV ⟨0, hc⟩)
  have hqdegree : ∀ j : Fin c, q.totalDegree ≤ d j := by
    intro j
    exact (hqmin (f ⟨0, hc⟩) hseed (hfV ⟨0, hc⟩)).trans
      ((hdegree ⟨0, hc⟩).trans (hd (by change 0 ≤ j.val; exact Nat.zero_le _)))
  have hex : ∀ p, 0 < p → p ≤ c → ∃ g : Fin c → Poly n,
      g ⟨0, hc⟩ = q ∧
      (∀ j, 0 < (g j).totalDegree ∧ g j ∈ V.ideal ∧ (g j).totalDegree ≤ d j) ∧
      ∀ r ≤ p, ∀ W : AffineVariety n,
        W.IsComponentOf (equationPrefixIdeal g r) → V.Subvariety W → W.dimension + r = n := by
    intro p
    induction p with
    | zero => intro hp; omega
    | succ p ih =>
      intro hppos hpc
      by_cases hp0 : p = 0
      · subst p
        let g : Fin c → Poly n := fun _ => q
        refine ⟨g, rfl, (fun j => ⟨hqpos, hqV, hqdegree j⟩), ?_⟩
        intro r hr W hW hVW
        by_cases hr0 : r = 0
        · subst r
          have hlower := prefix_component_dimension_lower g 0 (by omega) W hW
          have hupper := Bridges.affine_dimension_le W
          omega
        · have hr1 : r = 1 := by omega
          subst r
          have hideal : equationPrefixIdeal g 1 = Ideal.span {q} := by
            rw [show 1 = 0 + 1 by rfl, equationPrefixIdeal_succ g 0 hc, equationPrefixIdeal_zero]
            simp [g]
          have hwhole : (AffineVariety.whole : AffineVariety n).ideal = ⊥ :=
            Ideal.radical_bot_of_isReduced
          have hcut : W.IsComponentOf ((AffineVariety.whole : AffineVariety n).ideal ⊔ Ideal.span {q}) := by
            simpa [hwhole, hideal] using hW
          have hqnot : q ∉ (AffineVariety.whole : AffineVariety n).ideal := by
            simpa [hwhole] using hqne
          haveI : (AffineVariety.whole : AffineVariety n).ideal.IsPrime := by
            rw [hwhole]
            infer_instance
          haveI : W.ideal.IsPrime := hW.isPrime
          have hdimwhole : (AffineVariety.whole : AffineVariety n).dimension = (n - 1) + 1 := by
            rw [Bridges.affine_whole_dimension]
            omega
          have hcutdim := OAI.QuarticPowerFree.proper_cut_component_dimension
            (AffineVariety.whole : AffineVariety n).ideal W.ideal q hqnot hcut hdimwhole
          change W.dimension = n - 1 at hcutdim
          omega
      · obtain ⟨g, hgfirst, hgbounds, hgreg⟩ := ih (by omega) (by omega)
        have hp : p < c := by omega
        obtain ⟨q', hq'pos, hq'V, hq'deg, hq'avoid⟩ := bounded_prefix_extension V hV hdim
          f g d hd hdegree hfV (fun j => (hgbounds j).2.1) hcomp p hp hgreg
        let g' := Function.update g ⟨p, hp⟩ q'
        refine ⟨g', ?_, ?_, regular_prefix_extension V hV (by omega) g p hp hgreg q' hq'avoid⟩
        · have hne : (⟨0, hc⟩ : Fin c) ≠ ⟨p, hp⟩ := by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega
          simpa [g', Function.update_of_ne hne] using hgfirst
        · intro j
          by_cases hje : j = ⟨p, hp⟩
          · subst j
            simpa [g'] using And.intro hq'pos (And.intro hq'V hq'deg)
          · simpa [g', Function.update_of_ne hje] using hgbounds j
  obtain ⟨g, hgfirst, hgbounds, hgreg⟩ := hex c hc le_rfl
  refine ⟨g, hgbounds, ?_, hgreg⟩
  rw [hgfirst]
  exact hqmin

end
end DistinctDistances.TrackB
