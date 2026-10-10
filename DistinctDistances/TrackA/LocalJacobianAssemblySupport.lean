import DistinctDistances.TrackA.LocalTangentSupport
import DistinctDistances.TrackA.RegularityAlgebraSupport
import DistinctDistances.TrackA.GenericFiberFamilySupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical Topology

/-- The ideal of polynomials with zero value and zero directional first
jet at the actual complex point. -/
def directionalJetIdeal {n : ℕ} (x v : Point n) : Ideal (Poly n) where
  carrier := {f | MvPolynomial.eval x f = 0 ∧ derivativeEvaluation x v f = 0}
  zero_mem' := by constructor <;> exact map_zero _
  add_mem' hf hg := by
    constructor
    · rw [map_add, hf.1, hg.1, add_zero]
    · rw [map_add, hf.2, hg.2, add_zero]
  smul_mem' a f hf := by
    constructor
    · simpa only [smul_eq_mul, map_mul, hf.1, mul_zero]
    · rw [smul_eq_mul, derivativeEvaluation_apply, differential_mul_apply,
        hf.1, ← derivativeEvaluation_apply, hf.2, mul_zero, zero_mul, add_zero]

/-- A literal localized generating system determines the original
component tangent space from its evaluated Jacobian. -/
theorem tangentSpace_eq_kernel_of_localized_span {n q : ℕ} (V : AffineVariety n)
    (x : Point n) (hx : x ∈ V.points) (f : Fin q → Poly n)
    (hf : ∀ i, f i ∈ V.ideal)
    (hlocal : localizedIdeal V.ideal x = localizedIdeal (Ideal.span (Set.range f)) x) :
    V.tangentSpace x = LinearMap.ker
      (Matrix.mulVecLin (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i)))) := by
  ext v
  have hmatrix : v ∈ LinearMap.ker
      (Matrix.mulVecLin (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i)))) ↔
      ∀ i, derivativeEvaluation x v (f i) = 0 := by
    rw [LinearMap.mem_ker]
    change (fun i => ∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j (f i)) * v j) = 0 ↔ _
    simp only [funext_iff, Pi.zero_apply, derivativeEvaluation_apply, differential,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      MvPolynomial.aeval_eq_eval, smul_eq_mul]
  rw [hmatrix]
  constructor
  · intro hv i
    change v ∈ ⨅ f : V.ideal, LinearMap.ker (differential f.val x) at hv
    rw [Submodule.mem_iInf] at hv
    exact derivativeEvaluation_apply x v (f i) |>.trans (LinearMap.mem_ker.mp (hv ⟨f i, hf i⟩))
  · intro hv
    have hspan : Ideal.span (Set.range f) ≤ directionalJetIdeal x v := by
      apply Ideal.span_le.mpr
      rintro p ⟨i, rfl⟩
      exact ⟨by simpa only [MvPolynomial.aeval_eq_eval] using hx (f i) (hf i), hv i⟩
    change v ∈ ⨅ p : V.ideal, LinearMap.ker (differential p.val x)
    rw [Submodule.mem_iInf]
    intro p
    rw [LinearMap.mem_ker, ← derivativeEvaluation_apply]
    obtain ⟨g, hg, hgp⟩ := localizedIdeal_membership_denominator
      (Ideal.span (Set.range f)) x p.val (by
        rw [← hlocal]
        exact Ideal.mem_map_of_mem _ p.property)
    have hjet := hspan hgp
    have hpzero : MvPolynomial.eval x p.val = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using hx p.val p.property
    have hd : derivativeEvaluation x v (g*p.val) = 0 := hjet.2
    rw [derivativeEvaluation_apply, differential_mul_apply, hpzero, zero_mul, add_zero,
      ← derivativeEvaluation_apply] at hd
    exact (mul_eq_zero.mp hd).resolve_left hg

/-- An independent codimension Jacobian and literal local generators
compute the actual tangent dimension without a smoothness assumption. -/
theorem tangentSpace_finrank_of_localized_span {n k : ℕ} (hk : k ≤ n)
    (V : AffineVariety n) (x : Point n) (hx : x ∈ V.points)
    (f : Fin (n-k) → Poly n) (cols : Fin (n-k) ↪ Fin n)
    (hf : ∀ i, f i ∈ V.ideal)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (cols j) (f i))) ≠ 0)
    (hlocal : localizedIdeal V.ideal x = localizedIdeal (Ideal.span (Set.range f)) x) :
    Module.finrank ℂ (V.tangentSpace x) = k := by
  let A : Matrix (Fin (n-k)) (Fin n) ℂ :=
    fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))
  have hlower : n-k ≤ A.rank := by
    have h := Matrix.rank_submatrix_le A id cols
    have hminor : (A.submatrix id cols).rank = n-k := by
      simpa only [Fintype.card_fin] using
        (Matrix.rank_of_det_ne_zero (A := A.submatrix id cols) hdet)
    omega
  have hupper : A.rank ≤ n-k := by simpa using Matrix.rank_le_card_height A
  have hnullity := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change A.rank + Module.finrank ℂ (LinearMap.ker A.mulVecLin) =
    Module.finrank ℂ (Point n) at hnullity
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hnullity
  have hkern : Module.finrank ℂ (LinearMap.ker A.mulVecLin) = k := by omega
  rwa [← tangentSpace_eq_kernel_of_localized_span V x hx f hf hlocal] at hkern

/-- A component missing the point is absent in some Euclidean
neighborhood, witnessed by one original equation. -/
theorem affineVariety_eventually_not_mem {n : ℕ} (V : AffineVariety n)
    (x : Point n) (hx : x ∉ V.points) : ∀ᶠ y : Point n in nhds x, y ∉ V.points := by
  have hnot : ¬ ∀ f ∈ V.ideal, MvPolynomial.eval x f = 0 := by
    simpa only [AffineVariety.points, MvPolynomial.mem_zeroLocus_iff,
      MvPolynomial.aeval_eq_eval] using hx
  push Not at hnot
  obtain ⟨f, hf, hfx⟩ := hnot
  have hnear : ∀ᶠ y : Point n in nhds x, MvPolynomial.eval y f ≠ 0 :=
    (isOpen_ne.preimage (MvPolynomial.continuous_eval f)).mem_nhds hfx
  filter_upwards [hnear] with y hy
  intro hyV
  exact hy (by simpa only [MvPolynomial.aeval_eq_eval] using hyV f hf)

/-- Reduce the original pure-family germ theorem to the one-component
local Jacobian ideal theorem. The original dimension comparison is reused
as a frozen input; no regularity bound or germ theorem is used. -/
theorem pure_family_jacobian_germ_of_local_criterion {n : ℕ}
    (hcriterion : ∀ (k : ℕ), k ≤ n → ∀ (V : AffineVariety n), V.IsIrreducible →
      V.dimension = k → ∀ (x : Point n), x ∈ V.points →
      ∀ (f : Fin (n-k) → Poly n) (cols : Fin (n-k) ↪ Fin n),
        (∀ i, f i ∈ V.ideal) →
        Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (cols j) (f i))) ≠ 0 →
        localizedIdeal V.ideal x = localizedIdeal (Ideal.span (Set.range f)) x)
    (F : AffineFamily.Family n) (k : ℕ) (hk : k ≤ n)
    (hF : AffineFamily.IsPure F k) (E : List (Poly n))
    (hE : ∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal)
    (x : Point n) (hx : x ∈ (AffineFamily.locus F).points)
    (hm : ∃ m ∈ jacobianMinors E (n-k), MvPolynomial.eval x m ≠ 0) :
    SameGermAt (equationLocus E) (AffineFamily.locus F) x ∧
      (equationLocus E).IsSmoothAt x ∧ (equationLocus E).localDimension x = k ∧
      ∀ V ∈ F, ∀ W ∈ F, x ∈ V → x ∈ W → V = W := by
  obtain ⟨m, ⟨rows, cols, rfl⟩, hdet⟩ := hm
  let f : Fin (n-k) → Poly n := fun i => E.get (rows i)
  have hdet' : Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (cols j) (f i))) ≠ 0 := by
    exact ((MvPolynomial.eval x).map_det ((jacobian E).submatrix rows cols)).symm ▸ hdet
  have hf (V : AffineVariety n) (hV : V ∈ F) (i : Fin (n-k)) : f i ∈ V.ideal :=
    affineFamily_locus_ideal_le F V hV (hE _ (List.get_mem E (rows i)))
  have hlocal (V : AffineVariety n) (hV : V ∈ F) (hxV : x ∈ V.points) :
      localizedIdeal V.ideal x = localizedIdeal (Ideal.span (Set.range f)) x :=
    hcriterion k hk V (hF V hV).1 (hF V hV).2 x hxV f cols (hf V hV) hdet'
  have hxF : ∃ V ∈ F, x ∈ V.points := by
    rw [AffineFamily.points_locus] at hx
    obtain ⟨V, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hV, hxV⟩ := Set.mem_iUnion.mp hx
    exact ⟨V, hV, hxV⟩
  obtain ⟨V, hV, hxV⟩ := hxF
  have hJE : Ideal.span (Set.range f) ≤ (equationLocus E).ideal := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact Ideal.le_radical (Ideal.subset_span (List.get_mem E (rows i)))
  have hEV : (equationLocus E).ideal ≤ V.ideal := by
    calc
      _ ≤ V.ideal.radical := Ideal.radical_mono (Ideal.span_le.mpr
        (fun p hp => affineFamily_locus_ideal_le F V hV (hE p hp)))
      _ = V.ideal := V.isRadical.radical
  have hlocEV : localizedIdeal (equationLocus E).ideal x = localizedIdeal V.ideal x := by
    apply le_antisymm (Ideal.map_mono hEV)
    change localizedIdeal V.ideal x ≤ localizedIdeal (equationLocus E).ideal x
    rw [hlocal V hV hxV]
    exact Ideal.map_mono hJE
  have hxE : x ∈ (equationLocus E).points := by
    change x ∈ (AffineVariety.ofIdeal (Ideal.span {f | f ∈ E})).points
    rw [AffineVariety.points_ofIdeal, MvPolynomial.zeroLocus_span]
    intro p hp
    exact hx p (hE p hp)
  have hdimV : V.localDimension x = k :=
    (AffineVariety.localDimension_eq_dimension V x (hF V hV).1 hxV).trans (hF V hV).2
  have hdimE : (equationLocus E).localDimension x = k :=
    (localDimension_eq_of_localizedIdeal_eq (equationLocus E) V x hlocEV).trans hdimV
  have htangent : Module.finrank ℂ ((equationLocus E).tangentSpace x) = k := by
    rw [tangentSpace_eq_of_localizedIdeal_eq (equationLocus E) V x hxE hxV hlocEV]
    exact tangentSpace_finrank_of_localized_span hk V x hxV f cols (hf V hV) hdet'
      (hlocal V hV hxV)
  have hfamily : SameGermAt V (AffineFamily.locus F) x := by
    have hmem : ∀ W : F, ∀ᶠ y : Point n in nhds x, y ∈ W.val.points → y ∈ V.points := by
      intro W
      by_cases hxW : x ∈ W.val.points
      · have hlocWV : localizedIdeal W.val.ideal x = localizedIdeal V.ideal x :=
          (hlocal W.val W.property hxW).trans (hlocal V hV hxV).symm
        exact (sameGermAt_of_localizedIdeal_eq W.val V x hlocWV).mono (fun y h => h.mp)
      · exact (affineVariety_eventually_not_mem W.val x hxW).mono (fun y h hy => (h hy).elim)
    filter_upwards [Filter.eventually_all.mpr hmem] with y hy
    constructor
    · intro hyV
      change y ∈ (AffineFamily.locus F).points
      rw [AffineFamily.points_locus]
      exact Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨hV, hyV⟩⟩
    · intro hyF
      change y ∈ (AffineFamily.locus F).points at hyF
      rw [AffineFamily.points_locus] at hyF
      obtain ⟨W, hyF⟩ := Set.mem_iUnion.mp hyF
      obtain ⟨hW, hyW⟩ := Set.mem_iUnion.mp hyF
      exact hy ⟨W, hW⟩ hyW
  refine ⟨?_, ⟨hxE, htangent.trans hdimE.symm⟩, hdimE, ?_⟩
  · filter_upwards [sameGermAt_of_localizedIdeal_eq (equationLocus E) V x hlocEV, hfamily]
      with y hEV hVF
    exact hEV.trans hVF
  · intro W hW U hU hxW hxU
    exact affineVariety_eq_of_localizedIdeal_eq W U (hF W hW).1 (hF U hU).1 x hxW hxU
      ((hlocal W hW hxW).trans (hlocal U hU hxU).symm)

end
end DistinctDistances.TrackA
