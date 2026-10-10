import DistinctDistances.TrackA.RelativePointIsolationSupport
import DistinctDistances.TrackA.PoolingCutSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- The isolated original support count on one original irreducible carrier,
proved by successive actual proper cuts of the original equations. -/
theorem relative_irreducible_point_bound {n u : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hdim : V.dimension = u)
    (E : Set (Poly n)) (L : ℕ) (hL : 1 ≤ L) (hE : ∀ f ∈ E, f.totalDegree ≤ L)
    (S : Finset (Point n))
    (hS : ∀ x ∈ S, pointIdeal x ∈ (V.ideal ⊔ Ideal.span E).minimalPrimes) :
    (S.card : ℚ) ≤ V.degree * (L : ℚ)^u := by
  induction u generalizing V S with
  | zero =>
    obtain ⟨z, hz, hdegree⟩ := zeroDim_irreducible_data V hV hdim
    have hsub : S ⊆ {z} := by
      intro x hx
      have h := relative_isolated_point_mem V E x (hS x hx)
      rw [hz, Set.mem_singleton_iff] at h
      simpa using h
    have hc := Finset.card_le_card hsub
    rw [hdegree, pow_zero, mul_one]
    exact_mod_cast hc
  | succ u ih =>
    have hdegree : (0 : ℚ) ≤ V.degree := zero_le_one.trans (V.one_le_degree hV.ne_top)
    by_cases hempty : S = ∅
    · subst S
      simpa using mul_nonneg hdegree (pow_nonneg (Nat.cast_nonneg L) (u+1))
    obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨f, hfE, hfV⟩ := relative_isolated_proper_equation V hV hdim E x0 (hS x0 hx0)
    let F := pooling_cut_components V f
    have hF : AffineFamily.IsPure F u := pooling_cut_components_pure V hV f hfV u hdim
    let T (W : AffineVariety n) := S.filter (fun (x : Point n) => x ∈ W.points)
    have hbound : ∀ W ∈ F, ((T W).card : ℚ) ≤ W.degree * (L : ℚ)^u := by
      intro W hW
      apply ih W (hF W hW).1 (hF W hW).2 (T W)
      intro x hx
      obtain ⟨hxS, hxW⟩ := Finset.mem_filter.mp hx
      exact relative_isolated_point_transfer V W E x
        (le_sup_left.trans (pooling_cut_components_mem V W f hW).le) hxW (hS x hxS)
    have hcover : S ⊆ F.biUnion T := by
      intro x hx
      have hxV := relative_isolated_point_mem V E x (hS x hx)
      have hfx : MvPolynomial.eval x f = 0 := by
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).mp
          ((hS x hx).le (Ideal.mem_sup_right (Ideal.subset_span hfE)))
      obtain ⟨W, hW, hxW⟩ := pooling_cut_point V f x hxV hfx
      exact Finset.mem_biUnion.mpr ⟨W, hW, Finset.mem_filter.mpr ⟨hx, hxW⟩⟩
    have hcount : S.card ≤ ∑ W ∈ F, (T W).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have hcut : AffineFamily.degree F ≤ (f.totalDegree : ℚ) * V.degree :=
      pooling_cut_components_degree V hV f hfV u hdim
    have hfdegree : (f.totalDegree : ℚ) ≤ L := by exact_mod_cast hE f hfE
    calc
      (S.card : ℚ) ≤ ∑ W ∈ F, ((T W).card : ℚ) := by exact_mod_cast hcount
      _ ≤ ∑ W ∈ F, W.degree * (L : ℚ)^u := Finset.sum_le_sum hbound
      _ = AffineFamily.degree F * (L : ℚ)^u := by rw [← Finset.sum_mul]; rfl
      _ ≤ ((f.totalDegree : ℚ) * V.degree) * (L : ℚ)^u :=
        mul_le_mul_of_nonneg_right hcut (pow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ ((L : ℚ) * V.degree) * (L : ℚ)^u :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfdegree hdegree)
          (pow_nonneg (Nat.cast_nonneg _) _)
      _ = V.degree * (L : ℚ)^(u+1) := by rw [pow_succ]; ring

/-- The same isolated-support bound on an original reduced pure carrier,
using its actual minimal components and the original shared degree. -/
theorem relative_pure_point_bound {n u : ℕ} (V : AffineVariety n)
    (hV : V.IsPure u) (E : Set (Poly n)) (L : ℕ) (hL : 1 ≤ L)
    (hE : ∀ f ∈ E, f.totalDegree ≤ L) (S : Finset (Point n))
    (hS : ∀ x ∈ S, pointIdeal x ∈ (V.ideal ⊔ Ideal.span E).minimalPrimes) :
    (S.card : ℚ) ≤ V.degree * (L : ℚ)^u := by
  let F : AffineFamily.Family n := Finset.univ.image (fun c : V.Component => c.variety)
  have hF : AffineFamily.IsPure F u := by
    intro W hW
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨c.irreducible, hV c⟩
  have hlocus : V = AffineFamily.locus F := by
    apply (AffineVariety.points_eq_iff _ _).mp
    rw [AffineVariety.points_components, AffineFamily.points_locus]
    ext x
    constructor
    · intro hx
      obtain ⟨c, hxc⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion₂.mpr ⟨c.variety, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, hxc⟩
    · intro hx
      obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hW
      exact Set.mem_iUnion.mpr ⟨c, hxW⟩
  have hdegree : V.degree = AffineFamily.degree F := by
    rw [hlocus]
    exact AffineFamily.degree_locus F u hF
  let T (W : AffineVariety n) := S.filter (fun (x : Point n) => x ∈ W.points)
  have hbound : ∀ W ∈ F, ((T W).card : ℚ) ≤ W.degree * (L : ℚ)^u := by
    intro W hW
    apply relative_irreducible_point_bound W (hF W hW).1 (hF W hW).2 E L hL hE (T W)
    intro x hx
    obtain ⟨hxS, hxW⟩ := Finset.mem_filter.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hW
    exact relative_isolated_point_transfer V c.variety E x c.property.le hxW (hS x hxS)
  have hcover : S ⊆ F.biUnion T := by
    intro x hx
    have hxV := relative_isolated_point_mem V E x (hS x hx)
    rw [hlocus, AffineFamily.points_locus] at hxV
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hxV
    exact Finset.mem_biUnion.mpr ⟨W, hW, Finset.mem_filter.mpr ⟨hx, hxW⟩⟩
  have hcount : S.card ≤ ∑ W ∈ F, (T W).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  calc
    (S.card : ℚ) ≤ ∑ W ∈ F, ((T W).card : ℚ) := by exact_mod_cast hcount
    _ ≤ ∑ W ∈ F, W.degree * (L : ℚ)^u := Finset.sum_le_sum hbound
    _ = V.degree * (L : ℚ)^u := by rw [← Finset.sum_mul, hdegree]; rfl

end
end DistinctDistances.TrackA
