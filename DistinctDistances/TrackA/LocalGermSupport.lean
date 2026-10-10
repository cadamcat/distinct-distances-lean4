import DistinctDistances.TrackA.Definitions
import Mathlib.Topology.Algebra.MvPolynomial

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical Topology

/-- Membership in the actual point localization has a polynomial
clearing denominator which does not vanish at the original point. -/
theorem localizedIdeal_membership_denominator {n : ℕ} (I : Ideal (Poly n))
    (x : Point n) (f : Poly n)
    (hf : algebraMap (Poly n) (PointLocalRing x) f ∈ localizedIdeal I x) :
    ∃ g : Poly n, MvPolynomial.eval x g ≠ 0 ∧ g*f ∈ I := by
  obtain ⟨g, hg, hgf⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (pointIdeal x).primeCompl
      (PointLocalRing x) I f).mp hf
  refine ⟨g, ?_, hgf⟩
  have hg' : g ∉ pointIdeal x := hg
  simpa only [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff,
    MvPolynomial.aeval_eq_eval] using hg'

/-- A localized inclusion gives one actual principal open on which the
corresponding zero-locus inclusion holds. -/
theorem localizedIdeal_le_principal_open {n : ℕ} (I J : Ideal (Poly n))
    (x : Point n) (hIJ : localizedIdeal I x ≤ localizedIdeal J x) :
    ∃ g : Poly n, MvPolynomial.eval x g ≠ 0 ∧ ∀ y : Point n,
      MvPolynomial.eval y g ≠ 0 →
        y ∈ MvPolynomial.zeroLocus ℂ J → y ∈ MvPolynomial.zeroLocus ℂ I := by
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
  have hgen (f : s) : ∃ g : Poly n, MvPolynomial.eval x g ≠ 0 ∧ g*f.val ∈ J := by
    apply localizedIdeal_membership_denominator J x f.val
    apply hIJ
    apply Ideal.mem_map_of_mem
    rw [← hs]
    exact Ideal.subset_span f.property
  choose denominators hden using hgen
  let g : Poly n := ∏ f : s, denominators f
  have hg (y : Point n) : MvPolynomial.eval y g =
      ∏ f : s, MvPolynomial.eval y (denominators f) := by simp only [g, map_prod]
  refine ⟨g, ?_, ?_⟩
  · rw [hg]
    exact Finset.prod_ne_zero_iff.mpr (fun f _ => (hden f).1)
  · intro y hgy hy
    rw [← hs, MvPolynomial.zeroLocus_span]
    intro f hf
    let i : s := ⟨f, hf⟩
    have hdi : MvPolynomial.eval y (denominators i) ≠ 0 := by
      rw [hg] at hgy
      exact Finset.prod_ne_zero_iff.mp hgy i (Finset.mem_univ i)
    have hzero : MvPolynomial.eval y (denominators i * f) = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using hy _ (hden i).2
    rw [map_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hdi

/-- Equality of the actual localized ideals implies equality of the
original reduced carriers in the Euclidean neighborhood filter. -/
theorem sameGermAt_of_localizedIdeal_eq {n : ℕ} (V W : AffineVariety n)
    (x : Point n) (h : localizedIdeal V.ideal x = localizedIdeal W.ideal x) :
    SameGermAt V W x := by
  obtain ⟨g, hg, hWV⟩ := localizedIdeal_le_principal_open V.ideal W.ideal x h.le
  obtain ⟨f, hf, hVW⟩ := localizedIdeal_le_principal_open W.ideal V.ideal x h.symm.le
  have hnear : ∀ᶠ y : Point n in nhds x, MvPolynomial.eval y (g*f) ≠ 0 := by
    exact (isOpen_ne.preimage (MvPolynomial.continuous_eval (g*f))).mem_nhds
      (by
        change MvPolynomial.eval x (g*f) ≠ 0
        rw [map_mul]
        exact mul_ne_zero hg hf)
  filter_upwards [hnear] with y hy
  have hy' := mul_ne_zero_iff.mp (show MvPolynomial.eval y g * MvPolynomial.eval y f ≠ 0
    by simpa only [map_mul] using hy)
  exact ⟨hVW y hy'.2, hWV y hy'.1⟩

/-- Prime ideals through the original point are unchanged on contraction
from its localization. -/
theorem localizedPrime_contraction {n : ℕ} (P : Ideal (Poly n)) (hP : P.IsPrime)
    (x : Point n) (hx : x ∈ MvPolynomial.zeroLocus ℂ P) :
    (localizedIdeal P x).comap (algebraMap (Poly n) (PointLocalRing x)) = P := by
  ext f
  constructor
  · intro hf
    obtain ⟨g, hg, hgf⟩ := localizedIdeal_membership_denominator P x f hf
    have hnot : g ∉ P := by
      intro hgP
      exact hg (by simpa only [MvPolynomial.aeval_eq_eval] using hx g hgP)
    exact (hP.mem_or_mem hgf).resolve_left hnot
  · intro hf
    exact Ideal.mem_map_of_mem _ hf

/-- Equal actual localized component ideals give equal original
irreducible varieties, even before choosing a principal neighborhood. -/
theorem affineVariety_eq_of_localizedIdeal_eq {n : ℕ} (V W : AffineVariety n)
    (hV : V.IsIrreducible) (hW : W.IsIrreducible) (x : Point n)
    (hxV : x ∈ V.points) (hxW : x ∈ W.points)
    (h : localizedIdeal V.ideal x = localizedIdeal W.ideal x) : V = W := by
  apply AffineVariety.ext
  calc
    V.ideal = (localizedIdeal V.ideal x).comap (algebraMap (Poly n) (PointLocalRing x)) :=
      (localizedPrime_contraction V.ideal hV x hxV).symm
    _ = (localizedIdeal W.ideal x).comap (algebraMap (Poly n) (PointLocalRing x)) := by rw [h]
    _ = W.ideal := localizedPrime_contraction W.ideal hW x hxW

end
end DistinctDistances.TrackA
