import DistinctDistances.TrackA.Definitions

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open OAI.QuarticPowerFree

def pooling_cut_components {n : ℕ} (V : AffineVariety n) (f : Poly n) :
    AffineFamily.Family n :=
  Finset.univ.image (fun W : (V.cut f).Component => W.variety)

theorem pooling_cut_components_mem {n : ℕ} (V W : AffineVariety n) (f : Poly n)
    (hW : W ∈ pooling_cut_components V f) :
    W.IsComponentOf (V.ideal ⊔ Ideal.span {f}) := by
  obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hW
  have hp := P.property
  change P.val ∈ (V.ideal ⊔ Ideal.span {f}).radical.minimalPrimes at hp
  rwa [Ideal.radical_minimalPrimes] at hp

theorem pooling_cut_components_pure {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (f : Poly n) (hf : f ∉ V.ideal) (k : ℕ) (hdim : V.dimension = k+1) :
    AffineFamily.IsPure (pooling_cut_components V f) k := by
  letI : V.ideal.IsPrime := hV
  intro W hW
  have hp := pooling_cut_components_mem V W f hW
  letI : W.ideal.IsPrime := hp.isPrime
  exact ⟨hp.isPrime, proper_cut_component_dimension V.ideal W.ideal f hf hp hdim⟩

set_option maxHeartbeats 800000 in
theorem pooling_cut_components_degree {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (f : Poly n) (hf : f ∉ V.ideal) (k : ℕ) (hdim : V.dimension = k+1) :
    AffineFamily.degree (pooling_cut_components V f) ≤ (f.totalDegree : ℚ) * V.degree := by
  letI : V.ideal.IsPrime := hV
  let F := pooling_cut_components V f
  have h := proper_cut_sum_affineDegree_le V.ideal f hf hdim
    (fun W : F => W.val.ideal)
    (fun W => pooling_cut_components_mem V W.val f W.property)
    (by intro W Z he; exact Subtype.ext (AffineVariety.ext he))
  change (∑ W ∈ F, W.degree) ≤ _
  rw [← Finset.sum_coe_sort F]
  exact h

theorem pooling_cut_point {n : ℕ} (V : AffineVariety n) (f : Poly n) (x : Point n)
    (hx : x ∈ V.points) (hf : MvPolynomial.eval x f = 0) :
    ∃ W ∈ pooling_cut_components V f, x ∈ W.points := by
  have hcut : x ∈ (V.cut f).points := by
    rw [AffineVariety.cut, AffineVariety.points_ofIdeal]
    have hspan : Ideal.span {f} ≤ MvPolynomial.vanishingIdeal ℂ {x} := by
      apply Ideal.span_le.mpr
      rintro g rfl
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x g).mpr
        (by simpa only [MvPolynomial.aeval_eq_eval] using hf)
    have hV : V.ideal ≤ MvPolynomial.vanishingIdeal ℂ {x} := by
      intro g hg
      exact fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hx g hg
    intro g hg
    exact (sup_le hV hspan hg) x (Set.mem_singleton x)
  have hIx : (V.cut f).ideal ≤ MvPolynomial.vanishingIdeal ℂ {x} := by
    intro g hg
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x g).mpr (hcut g hg)
  obtain ⟨P, hP, hPx⟩ := Ideal.exists_minimalPrimes_le hIx
  let W : (V.cut f).Component := ⟨P, hP⟩
  refine ⟨W.variety, Finset.mem_image.mpr ⟨W, Finset.mem_univ _, rfl⟩, ?_⟩
  intro g hg
  exact (hPx hg) x rfl

end
end DistinctDistances.TrackA
