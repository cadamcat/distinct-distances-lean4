import DistinctDistances.TrackA.ProjectiveSectionSupport
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Finiteness.Ideal

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- Fractions representing one function on their patches agree in the
prime coordinate ring. The two denominators may vanish elsewhere. -/
theorem cone_fraction_cross_mem {n : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (s : NonzeroConePoint V → ℂ) (a b c d : Poly n)
    (hb : b ∉ V.ideal) (hd : d ∉ V.ideal)
    (ha : ∀ x, MvPolynomial.eval x.val b ≠ 0 →
      s x * MvPolynomial.eval x.val b = MvPolynomial.eval x.val a)
    (hc : ∀ x, MvPolynomial.eval x.val d ≠ 0 →
      s x * MvPolynomial.eval x.val d = MvPolynomial.eval x.val c) :
    a*d-c*b ∈ V.ideal := by
  have hprod : (b*d)*(a*d-c*b) ∈ V.ideal := by
    rw [← V.vanishingIdeal_points]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro x ⟨hx0, hxV⟩
    have hxcone := (ProjectiveVariety.mem_points_mk_iff V x hx0).mp hxV
    let y : NonzeroConePoint V := ⟨x, hx0, hxcone⟩
    change MvPolynomial.aeval x ((b*d)*(a*d-c*b)) = 0
    simp only [map_mul, map_sub, MvPolynomial.aeval_eq_eval]
    by_cases hbx : MvPolynomial.eval x b = 0
    · rw [hbx]; ring
    by_cases hdx : MvPolynomial.eval x d = 0
    · rw [hdx]; ring
    have hya := ha y hbx
    have hyc := hc y hdx
    change s y * MvPolynomial.eval x b = MvPolynomial.eval x a at hya
    change s y * MvPolynomial.eval x d = MvPolynomial.eval x c at hyc
    rw [← hya, ← hyc]
    ring
  rcases hV.mem_or_mem hprod with hbd | hcross
  · exact False.elim ((hV.mem_or_mem hbd).elim hb hd)
  · exact hcross

/-- Denominators that turn a fixed fraction a/b into a polynomial class. -/
def fractionDenominatorIdeal {n : ℕ} (V : ProjectiveVariety n) (a b : Poly n) :
    Ideal (Poly n) := (Ideal.span {b} ⊔ V.ideal).colon (Ideal.span {a})

theorem mem_fractionDenominatorIdeal_iff {n : ℕ} (V : ProjectiveVariety n)
    (a b f : Poly n) :
    f ∈ fractionDenominatorIdeal V a b ↔ ∃ c : Poly n, f*a-c*b ∈ V.ideal := by
  rw [fractionDenominatorIdeal, Ideal.mem_colon_span_singleton,
    Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨c, g, hg, hcg⟩
    refine ⟨c, ?_⟩
    have heq : f*a-c*b = g := by rw [← hcg]; ring
    rwa [heq]
  · rintro ⟨c, hc⟩
    exact ⟨c, f*a-c*b, hc, by ring⟩

theorem ideal_le_fractionDenominatorIdeal {n : ℕ} (V : ProjectiveVariety n)
    (a b : Poly n) : V.ideal ≤ fractionDenominatorIdeal V a b := by
  intro f hf
  apply (mem_fractionDenominatorIdeal_iff V a b f).mpr
  exact ⟨0, by simpa using V.ideal.mul_mem_right a hf⟩

/-- Local regularity supplies a denominator not vanishing at each
nonzero cone point, so the denominator ideal has no other zeros. -/
theorem regularSection_denominator_zeroLocus {n D : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (s : regularSectionSpace V D) (a b : Poly n)
    (hb : b ∉ V.ideal)
    (ha : ∀ x, MvPolynomial.eval x.val b ≠ 0 →
      s.val x * MvPolynomial.eval x.val b = MvPolynomial.eval x.val a) :
    MvPolynomial.zeroLocus ℂ (fractionDenominatorIdeal V a b) ⊆ {0} := by
  intro x hx
  apply Set.mem_singleton_iff.mpr
  by_contra hx0
  have hxcone : x ∈ V.affineCone.points :=
    fun f hf => hx f (ideal_le_fractionDenominatorIdeal V a b hf)
  let y : NonzeroConePoint V := ⟨x, hx0, hxcone⟩
  have hs : IsRegularHomogeneousSection V D s.val := s.property
  obtain ⟨q, c, d, _, _, hd, hc⟩ := hs y
  have hdI : d ∉ V.ideal := by
    intro hdI
    exact hd (by simpa only [MvPolynomial.aeval_eq_eval] using hxcone d hdI)
  have hcross := cone_fraction_cross_mem V hV s.val a b c d hb hdI ha hc
  have hdJ : d ∈ fractionDenominatorIdeal V a b := by
    apply (mem_fractionDenominatorIdeal_iff V a b d).mpr
    refine ⟨c, ?_⟩
    simpa only [mul_comm d a] using hcross
  exact hd (by simpa only [MvPolynomial.aeval_eq_eval] using hx d hdJ)

/-- Nullstellensatz gives a power of the irrelevant ideal inside the
denominator ideal, without a finite-section or degree-bound assumption. -/
theorem regularSection_denominator_irrelevant_power {n D : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (s : regularSectionSpace V D) (a b : Poly n)
    (hb : b ∉ V.ideal)
    (ha : ∀ x, MvPolynomial.eval x.val b ≠ 0 →
      s.val x * MvPolynomial.eval x.val b = MvPolynomial.eval x.val a) :
    ∃ N : ℕ, MvPolynomial.idealOfVars (Fin n) ℂ ^ N ≤ fractionDenominatorIdeal V a b := by
  have hzero := regularSection_denominator_zeroLocus V hV s a b hb ha
  have hrad : MvPolynomial.idealOfVars (Fin n) ℂ ≤
      (fractionDenominatorIdeal V a b).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
    apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    intro x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp (hzero hx)
    simp [hx0]
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (MvPolynomial.idealOfVars_fg (Fin n) ℂ)

/-- A sufficiently high homogeneous polynomial lies in the denominator
ideal; this is membership in an actual irrelevant-ideal power. -/
theorem homogeneous_mem_denominator_of_power {n : ℕ} (V : ProjectiveVariety n)
    (a b : Poly n) (N M : ℕ)
    (hN : MvPolynomial.idealOfVars (Fin n) ℂ ^ N ≤ fractionDenominatorIdeal V a b)
    (hNM : N ≤ M) (f : Poly n) (hf : f.IsHomogeneous M) :
    f ∈ fractionDenominatorIdeal V a b := by
  apply hN
  apply (MvPolynomial.mem_pow_idealOfVars_iff N f).mpr
  intro e he
  have hweight := hf (Finsupp.mem_support_iff.mp he)
  have hdegree : e.degree = M := by
    have hweight' : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) e = M := by
      simpa only [Pi.one_def] using hweight
    rw [← Finsupp.degree_eq_weight_one] at hweight'
    exact hweight'
  exact hdegree ▸ hNM

/-- Taking the component of a product by a fixed homogeneous factor
amounts to taking the corresponding component of its other factor. -/
theorem homogeneousComponent_mul_homogeneous {n q M : ℕ} (b c : Poly n)
    (hb : b.IsHomogeneous q) :
    MvPolynomial.homogeneousComponent (M+q) (b*c) =
      b * MvPolynomial.homogeneousComponent M c := by
  calc
    _ = MvPolynomial.homogeneousComponent (M+q)
        (b * ∑ i ∈ Finset.range (c.totalDegree+1), MvPolynomial.homogeneousComponent i c) := by
      rw [MvPolynomial.sum_homogeneousComponent]
    _ = ∑ i ∈ Finset.range (c.totalDegree+1),
        MvPolynomial.homogeneousComponent (M+q) (b * MvPolynomial.homogeneousComponent i c) := by
      rw [Finset.mul_sum, map_sum]
    _ = ∑ i ∈ Finset.range (c.totalDegree+1),
        if M = i then b * MvPolynomial.homogeneousComponent i c else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [MvPolynomial.homogeneousComponent_of_mem
        (hb.mul (MvPolynomial.homogeneousComponent_isHomogeneous i c))]
      have heq : M+q = q+i ↔ M = i := by omega
      simp only [heq]
    _ = _ := by
      by_cases hM : M < c.totalDegree+1
      · simp [hM]
      · have hcomp : MvPolynomial.homogeneousComponent M c = 0 :=
          MvPolynomial.homogeneousComponent_eq_zero M c (by omega)
        simp [hM, hcomp]

/-- Division modulo a homogeneous ideal preserves the homogeneous degree
required by the local section model. -/
theorem homogeneous_fraction_division {n q D M : ℕ} (V : ProjectiveVariety n)
    (a b f c : Poly n) (ha : a.IsHomogeneous (q+D)) (hb : b.IsHomogeneous q)
    (hf : f.IsHomogeneous M) (hc : f*a-c*b ∈ V.ideal) :
    ∃ g : Poly n, g.IsHomogeneous (M+D) ∧ f*a-g*b ∈ V.ideal := by
  refine ⟨MvPolynomial.homogeneousComponent (M+D) c,
    MvPolynomial.homogeneousComponent_isHomogeneous (M+D) c, ?_⟩
  have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem V.isHomogeneous hc (M+D+q)
  have hfa : (f*a).IsHomogeneous (M+D+q) := by
    convert hf.mul ha using 1 <;> omega
  rw [map_sub, MvPolynomial.homogeneousComponent_eq_self hfa,
    mul_comm c b, homogeneousComponent_mul_homogeneous b c hb] at hcomp
  simpa only [mul_comm b (MvPolynomial.homogeneousComponent (M+D) c)] using hcomp

/-- The polynomial quotient identity extends through zeros of the fixed
denominator by using the section's local fraction at that point. -/
theorem regularSection_multiply_of_quotient_relation {n D : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (s : regularSectionSpace V D) (a b f g : Poly n)
    (hb : b ∉ V.ideal)
    (ha : ∀ x, MvPolynomial.eval x.val b ≠ 0 →
      s.val x * MvPolynomial.eval x.val b = MvPolynomial.eval x.val a)
    (hrel : f*a-g*b ∈ V.ideal) :
    ∀ x, s.val x * MvPolynomial.eval x.val f = MvPolynomial.eval x.val g := by
  intro x
  have hs : IsRegularHomogeneousSection V D s.val := s.property
  obtain ⟨q, c, d, _, _, hd, hc⟩ := hs x
  have hdI : d ∉ V.ideal := by
    intro hdI
    exact hd (by simpa only [MvPolynomial.aeval_eq_eval] using x.property.2 d hdI)
  have hcross := cone_fraction_cross_mem V hV s.val a b c d hb hdI ha hc
  have hprod : (f*c-g*d)*b ∈ V.ideal := by
    convert V.ideal.sub_mem (V.ideal.mul_mem_left d hrel) (V.ideal.mul_mem_left f hcross) using 1 <;> ring
  have hlocal : f*c-g*d ∈ V.ideal := (hV.mem_or_mem hprod).resolve_right hb
  have heval : MvPolynomial.eval x.val f * MvPolynomial.eval x.val c =
      MvPolynomial.eval x.val g * MvPolynomial.eval x.val d := by
    have hz := x.property.2 (f*c-g*d) hlocal
    simpa only [map_sub, map_mul, MvPolynomial.aeval_eq_eval, sub_eq_zero] using hz
  apply mul_right_cancel₀ hd
  calc
    (s.val x * MvPolynomial.eval x.val f) * MvPolynomial.eval x.val d =
        MvPolynomial.eval x.val f * (s.val x * MvPolynomial.eval x.val d) := by ring
    _ = MvPolynomial.eval x.val f * MvPolynomial.eval x.val c := by rw [hc x hd]
    _ = _ := heval

/-- Each locally regular homogeneous section multiplies all sufficiently
high-degree homogeneous restrictions into homogeneous polynomial
restrictions of the expected degree. No section finiteness is assumed. -/
theorem regularSection_eventually_polynomial_multiplication {n D : ℕ}
    (V : ProjectiveVariety n) (hV : V.IsIrreducible) (s : regularSectionSpace V D) :
    ∃ N : ℕ, ∀ M, N ≤ M → ∀ f : Poly n, f.IsHomogeneous M →
      ∃ g : Poly n, g.IsHomogeneous (M+D) ∧
        ∀ x, s.val x * MvPolynomial.eval x.val f = MvPolynomial.eval x.val g := by
  obtain ⟨p, hp⟩ := ProjectiveFamily.irreducible_points_nonempty V hV
  let x : NonzeroConePoint V := ⟨p.rep, p.rep_nonzero,
    (ProjectiveVariety.mem_points_mk_iff V p.rep p.rep_nonzero).mp (by simpa using hp)⟩
  have hs : IsRegularHomogeneousSection V D s.val := s.property
  obtain ⟨q, a, b, ha, hb, hbx, he⟩ := hs x
  have hbI : b ∉ V.ideal := by
    intro hbI
    exact hbx (by simpa only [MvPolynomial.aeval_eq_eval] using x.property.2 b hbI)
  obtain ⟨N, hN⟩ := regularSection_denominator_irrelevant_power V hV s a b hbI he
  refine ⟨N, ?_⟩
  intro M hM f hf
  obtain ⟨c, hc⟩ := (mem_fractionDenominatorIdeal_iff V a b f).mp
    (homogeneous_mem_denominator_of_power V a b N M hN hM f hf)
  obtain ⟨g, hg, hfg⟩ := homogeneous_fraction_division V a b f c ha hb hf hc
  exact ⟨g, hg, regularSection_multiply_of_quotient_relation V hV s a b f g hbI he hfg⟩

end
end DistinctDistances.TrackA
