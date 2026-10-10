import DistinctDistances.TrackE.CommonLabelEnvelope
import DistinctDistances.TrackE.CommonImageInputs
import DistinctDistances.TrackD.RationalImages
import DistinctDistances.TrackA.PoolingSupport
import DistinctDistances.TrackD.ProductGeometry
import DistinctDistances.TrackD.ProductTangents
import DistinctDistances.Foundations.GenericFiber

/-! Helpers for lane m-e-label (items 185-186). -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Every member of the envelope components is irreducible. -/
theorem envelopeComponents_irreducible {n : ℕ} (T : Set (Point n)) (L : ℕ)
    (V : AffineVariety n) (hV : V ∈ Bridges.envelopeComponents T L) :
    V.IsIrreducible := by
  obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hV
  exact W.irreducible

/-- Nonnegativity of the equal-dimension lower bound. -/
theorem commonEqualDimLower_nonneg {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (i j : ℕ) :
    0 ≤ commonEqualDimLower M i j := by
  unfold commonEqualDimLower
  split_ifs with hj0
  · unfold TrackD.cutScale TrackD.testDeg
    exact (mul_pos (regime.B_pos i) (Real.exp_pos _)).le
  · exact sq_nonneg _

end
end DistinctDistances.SparseCones

/-! Cylinder points and injectivity (item 186, easy conjuncts). -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Evaluation of the fixed-coordinate generator at a product point. -/
theorem cyl_eval_fixed (i₀ : Fin d) (x v : Point d) :
    MvPolynomial.eval (TrackD.productPoint x v)
      (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1) = v i₀ - 1 := by
  rw [map_sub, MvPolynomial.eval_X, map_one]
  congr 1
  show (TrackD.productPoint x v) (finSumFinEquiv (Sum.inr i₀)) = v i₀
  unfold TrackD.productPoint TrackD.pairPt
  rw [Function.comp_apply, Equiv.symm_apply_apply]
  rfl

/-- Evaluation of a second-block variable at a product point. -/
theorem productPoint_eval_inr (x v : Point d) (j : Fin d) :
    (TrackD.productPoint x v) (finSumFinEquiv (Sum.inr j)) = v j := by
  unfold TrackD.productPoint TrackD.pairPt
  rw [Function.comp_apply, Equiv.symm_apply_apply]
  rfl

end
end DistinctDistances.SparseCones

/-! Parametrized label cylinders (item 186 infrastructure).

`cylIdeal i₀ X T` fixes the `i₀`-th second-block coordinate to 1 and the
second-block coordinates in `T` (all `≠ i₀`) to 0, on top of the source
ideal. `T = ∅` is the full label cylinder. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Second-block indices other than `i₀`: the potentially free variables. -/
abbrev CylFree (d : ℕ) (i₀ : Fin d) := { j : Fin d // j ≠ i₀ }

/-- The cylinder ideal with the variables in `T` fixed to 0. -/
def cylIdeal (i₀ : Fin d) (X : AffineVariety d) (T : Finset (CylFree d i₀)) :
    Ideal (Poly (d + d)) :=
  Ideal.span (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
    {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1} ∪
    ((fun s : CylFree d i₀ => MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))) '' ↑T))

/-- The corresponding variety. -/
def cylVar (i₀ : Fin d) (X : AffineVariety d) (T : Finset (CylFree d i₀)) :
    AffineVariety (d + d) :=
  AffineVariety.ofIdeal (cylIdeal i₀ X T)

/-- Points of a parametrized cylinder. -/
theorem cylVar_points (i₀ : Fin d) (X : AffineVariety d) (T : Finset (CylFree d i₀))
    (x v : Point d) :
    TrackD.productPoint x v ∈ cylVar i₀ X T ↔
      x ∈ X ∧ v i₀ = 1 ∧ ∀ s ∈ T, v s.val = 0 := by
  have hpts : TrackD.productPoint x v ∈ (cylVar i₀ X T).points ↔
      x ∈ X ∧ v i₀ = 1 ∧ ∀ s ∈ T, v s.val = 0 := by
    unfold cylVar cylIdeal
    rw [AffineVariety.points_ofIdeal, MvPolynomial.mem_zeroLocus_iff]
    constructor
    · intro h
      have hsrc : ∀ f ∈ X.ideal, MvPolynomial.eval x f = 0 := by
        intro f hf
        have hmem : commonSourcePolynomial f ∈ Ideal.span
            (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
              {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1} ∪
              ((fun s : CylFree d i₀ =>
                MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))) '' ↑T)) :=
          Ideal.subset_span (Or.inl (Or.inl ⟨f, hf, rfl⟩))
        have hz := h _ hmem
        rw [MvPolynomial.aeval_eq_eval, eval_common_source_polynomial] at hz
        exact hz
      have hfix : v i₀ = 1 := by
        have hmem : MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1 ∈ Ideal.span
            (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
              {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1} ∪
              ((fun s : CylFree d i₀ =>
                MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))) '' ↑T)) :=
          Ideal.subset_span (Or.inl (Or.inr rfl))
        have hz := h _ hmem
        rw [MvPolynomial.aeval_eq_eval, cyl_eval_fixed] at hz
        exact sub_eq_zero.mp hz
      have hT : ∀ s ∈ T, v s.val = 0 := by
        intro s hs
        have hmem : MvPolynomial.X (finSumFinEquiv (Sum.inr s.val)) ∈ Ideal.span
            (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
              {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1} ∪
              ((fun s : CylFree d i₀ =>
                MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))) '' ↑T)) :=
          Ideal.subset_span (Or.inr ⟨s, Finset.mem_coe.mpr hs, rfl⟩)
        have hz := h _ hmem
        rw [MvPolynomial.aeval_eq_eval] at hz
        have hev : MvPolynomial.eval (TrackD.productPoint x v)
            (MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))) = v s.val := by
          rw [MvPolynomial.eval_X]
          exact productPoint_eval_inr x v s.val
        rw [hev] at hz
        exact hz
      have hx : x ∈ X := by
        show x ∈ MvPolynomial.zeroLocus ℂ X.ideal
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro f hf
        rw [MvPolynomial.aeval_eq_eval]
        exact hsrc f hf
      exact ⟨hx, hfix, hT⟩
    · rintro ⟨hx, hv, hT⟩
      have hx' : ∀ f ∈ X.ideal, (MvPolynomial.aeval (TrackD.productPoint x v))
          (commonSourcePolynomial f) = 0 := by
        intro f hf
        have hfx : x ∈ MvPolynomial.zeroLocus ℂ X.ideal := hx
        have hz := (MvPolynomial.mem_zeroLocus_iff).mp hfx f hf
        rw [MvPolynomial.aeval_eq_eval, eval_common_source_polynomial]
        rw [MvPolynomial.aeval_eq_eval] at hz
        exact hz
      have hfix' : (MvPolynomial.aeval (TrackD.productPoint x v))
          ((MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1 : Poly (d + d))) = 0 := by
        rw [MvPolynomial.aeval_eq_eval, cyl_eval_fixed, hv, sub_self]
      have hT' : ∀ s ∈ T, (MvPolynomial.aeval (TrackD.productPoint x v))
          ((MvPolynomial.X (finSumFinEquiv (Sum.inr s.val)) : Poly (d + d))) = 0 := by
        intro s hs
        rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_X,
          productPoint_eval_inr, hT s hs]
      intro g hg
      have hle : Ideal.span (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
          {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1} ∪
          ((fun s : CylFree d i₀ =>
            MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))) '' ↑T)) ≤
          RingHom.ker (MvPolynomial.aeval (TrackD.productPoint x v)).toRingHom := by
        rw [Ideal.span_le]
        intro g hg
        show (MvPolynomial.aeval (TrackD.productPoint x v)).toRingHom g = 0
        rw [Set.mem_union] at hg
        cases hg with
        | inl h =>
          rw [Set.mem_union] at h
          cases h with
          | inl h =>
            obtain ⟨f, hf, rfl⟩ := h
            exact hx' f hf
          | inr h =>
            have hgg : g = (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1 :
                Poly (d + d)) := Set.mem_singleton_iff.mp h
            rw [hgg]
            exact hfix'
        | inr h =>
          obtain ⟨s, hs, rfl⟩ := h
          have hs' : s ∈ T := Finset.mem_coe.mp hs
          exact hT' s hs'
      exact (RingHom.mem_ker).mp (hle hg)
  exact hpts

end
end DistinctDistances.SparseCones

/-! The quotient map for parametrized cylinders (item 186 core). -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Free second-block variables: those in `CylFree` not fixed by `T`. -/
abbrev CylFreeRem (d : ℕ) (i₀ : Fin d) (T : Finset (CylFree d i₀)) :=
  { s : CylFree d i₀ // s ∉ T }

/-- Value of the quotient map on a generator. -/
def cylPhiVal (i₀ : Fin d) (X : AffineVariety d) (T : Finset (CylFree d i₀))
    (k : Fin (d + d)) : MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal) :=
  Sum.elim (fun j => MvPolynomial.C (Ideal.Quotient.mk _ (MvPolynomial.X j)))
    (fun j => if heq : j = i₀ then 1
      else if hT : (⟨j, heq⟩ : CylFree d i₀) ∈ T then 0
      else MvPolynomial.X ⟨⟨j, heq⟩, hT⟩)
    (finSumFinEquiv.symm k)

/-- The quotient map onto polynomials in the free variables over `ℂ[X]`. -/
def cylPhi (i₀ : Fin d) (X : AffineVariety d) (T : Finset (CylFree d i₀)) :
    Poly (d + d) →ₐ[ℂ]
      MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal) :=
  MvPolynomial.aeval (cylPhiVal i₀ X T)

/-- First-block generators map to constants. -/
theorem cylPhiVal_inl (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (j : Fin d) :
    cylPhiVal i₀ X T (finSumFinEquiv (Sum.inl j)) =
      MvPolynomial.C (Ideal.Quotient.mk _ (MvPolynomial.X j)) := by
  unfold cylPhiVal
  rw [Equiv.symm_apply_apply, Sum.elim_inl]

/-- The fixed generator maps to 1. -/
theorem cylPhiVal_inr_eq (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) :
    cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr i₀)) = 1 := by
  unfold cylPhiVal
  rw [Equiv.symm_apply_apply, Sum.elim_inr, dif_pos rfl]

/-- A fixed-to-zero generator maps to 0. -/
theorem cylPhiVal_inr_mem (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (s : CylFree d i₀) (hs : s ∈ T) :
    cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr s.val)) = 0 := by
  unfold cylPhiVal
  rw [Equiv.symm_apply_apply, Sum.elim_inr, dif_neg s.property]
  exact dif_pos hs

/-- A free generator maps to its indeterminate. -/
theorem cylPhiVal_inr_free (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (s : CylFree d i₀) (hs : s ∉ T) :
    cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr s.val)) =
      MvPolynomial.X ⟨s, hs⟩ := by
  unfold cylPhiVal
  rw [Equiv.symm_apply_apply, Sum.elim_inr, dif_neg s.property]
  exact dif_neg hs

/-- The quotient map sends source polynomials to constants. -/
theorem cylPhi_src (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (f : Poly d) :
    cylPhi i₀ X T (commonSourcePolynomial f) =
      MvPolynomial.C (Ideal.Quotient.mk _ f) := by
  have hren_add : ∀ p q : Poly d, commonSourcePolynomial (p + q) =
      commonSourcePolynomial p + commonSourcePolynomial q := by
    intro p q
    simp only [commonSourcePolynomial, MvPolynomial.rename_eq_aeval, map_add]
  have hren_mul_X : ∀ (p : Poly d) (n : Fin d),
      commonSourcePolynomial (p * MvPolynomial.X n) =
        commonSourcePolynomial p * commonSourcePolynomial (MvPolynomial.X n) := by
    intro p n
    simp only [commonSourcePolynomial, MvPolynomial.rename_eq_aeval, map_add, map_mul]
  have hscalar : ∀ a : ℂ, (algebraMap ℂ
      (MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal))) a =
      MvPolynomial.C (algebraMap ℂ (Poly d ⧸ X.ideal) a) := by
    intro a
    rw [IsScalarTower.algebraMap_eq ℂ (Poly d ⧸ X.ideal) _, MvPolynomial.algebraMap_eq]
    rfl
  show cylPhi i₀ X T (commonSourcePolynomial f) = _
  induction f using MvPolynomial.induction_on with
  | C a =>
    unfold commonSourcePolynomial
    rw [MvPolynomial.rename_C]
    show cylPhi i₀ X T (MvPolynomial.C a) = _
    unfold cylPhi
    rw [MvPolynomial.aeval_C]
    have eR : (Ideal.Quotient.mk (X.ideal : Ideal (Poly d))) (MvPolynomial.C a) =
        algebraMap ℂ (Poly d ⧸ X.ideal) a := by
      rw [← MvPolynomial.algebraMap_eq]
      rfl
    rw [eR]
    exact hscalar a
  | add p q hp hq =>
    rw [hren_add, map_add, hp, hq]
    simp only [map_add]
  | mul_X p n hp =>
    rw [hren_mul_X, map_mul, hp]
    simp only [map_mul]
    congr 1
    have eX : commonSourcePolynomial (MvPolynomial.X n) =
        MvPolynomial.X (finSumFinEquiv (Sum.inl n)) := MvPolynomial.rename_X _ _
    rw [eX]
    unfold cylPhi
    rw [MvPolynomial.aeval_X, cylPhiVal_inl]

/-- The quotient map is surjective. -/
theorem cylPhi_surjective (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) :
    Function.Surjective (cylPhi i₀ X T) := by
  intro t
  induction t using MvPolynomial.induction_on with
  | C r =>
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨commonSourcePolynomial f, cylPhi_src i₀ X T f⟩
  | add p q hp hq =>
    obtain ⟨gp, hgp⟩ := hp
    obtain ⟨gq, hgq⟩ := hq
    exact ⟨gp + gq, by rw [map_add, hgp, hgq]⟩
  | mul_X p s hp =>
    obtain ⟨g, hg⟩ := hp
    refine ⟨g * MvPolynomial.X (finSumFinEquiv (Sum.inr s.val.val)), ?_⟩
    rw [map_mul, hg]
    congr 1
    show cylPhi i₀ X T (MvPolynomial.X (finSumFinEquiv (Sum.inr s.val.val))) = _
    unfold cylPhi
    rw [MvPolynomial.aeval_X]
    exact cylPhiVal_inr_free i₀ X T s.val s.property

/-- Splitting a product over `Fin (d+d)` along `finSumFinEquiv`. -/
theorem prod_split_e {M : Type} [CommMonoid M] (f : Fin (d + d) → M) :
    ∏ k, f k = (∏ j : Fin d, f (finSumFinEquiv (Sum.inl j))) *
      (∏ j : Fin d, f (finSumFinEquiv (Sum.inr j))) := by
  have hR : (∏ k : Fin (d + d), f k)
      = ∏ y : Fin d ⊕ Fin d, f (finSumFinEquiv y) := by
    apply Fintype.prod_equiv finSumFinEquiv.symm
    intro k
    simp
  rw [hR, Fintype.prod_sum_type]

/-- Splitting a `Finsupp.prod` over `Fin (d+d)`. -/
theorem finsupp_prod_split {M N : Type} [Zero M] [CommMonoid N]
    (ν : Fin (d + d) →₀ M) (gval : Fin (d + d) → M → N)
    (h1 : ∀ i ∈ (Finset.univ : Finset (Fin (d + d))), gval i 0 = 1) :
    ν.prod gval =
      (∏ j : Fin d, gval (finSumFinEquiv (Sum.inl j)) (ν (finSumFinEquiv (Sum.inl j)))) *
      (∏ j : Fin d, gval (finSumFinEquiv (Sum.inr j)) (ν (finSumFinEquiv (Sum.inr j)))) := by
  have hU : ν.prod gval = ∏ k : Fin (d + d), gval k (ν k) := by
    rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ h1]
  rw [hU]
  exact prod_split_e _

/-- First-block monomial part of an exponent. -/
def cylFirst (ν : Fin (d + d) →₀ ℕ) : Poly d :=
  ∏ j : Fin d, MvPolynomial.X j ^ (ν (finSumFinEquiv (Sum.inl j)))

/-- Quotient of a scalar. -/
theorem mk_C_eq (X : AffineVariety d) (a : ℂ) :
    Ideal.Quotient.mk (X.ideal : Ideal (Poly d)) (MvPolynomial.C a) =
      algebraMap ℂ (Poly d ⧸ X.ideal) a := by
  rw [← MvPolynomial.algebraMap_eq]
  rfl

/-- Scalar tower for the target. -/
theorem target_scalar_eq (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (a : ℂ) :
    (algebraMap ℂ (MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal))) a =
      MvPolynomial.C (algebraMap ℂ (Poly d ⧸ X.ideal) a) := by
  rw [IsScalarTower.algebraMap_eq ℂ (Poly d ⧸ X.ideal) _, MvPolynomial.algebraMap_eq]
  rfl

/-- The quotient map on monomials, split form. -/
theorem cylPhi_monomial (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (ν : Fin (d + d) →₀ ℕ) (c : ℂ) :
    cylPhi i₀ X T (MvPolynomial.monomial ν c) =
      MvPolynomial.C (Ideal.Quotient.mk _
        (MvPolynomial.C c * cylFirst ν)) *
        (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
          (ν (finSumFinEquiv (Sum.inr j)))) := by
  have hinner : algebraMap ℂ (Poly d ⧸ X.ideal) c * Ideal.Quotient.mk _ (cylFirst ν)
      = Ideal.Quotient.mk _ (MvPolynomial.C c * cylFirst ν) := by
    rw [map_mul, mk_C_eq]
  have hS : (algebraMap ℂ
        (MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal))) c *
      MvPolynomial.C (Ideal.Quotient.mk _ (cylFirst ν)) =
      MvPolynomial.C (Ideal.Quotient.mk _
        (MvPolynomial.C c * cylFirst ν)) := by
    rw [target_scalar_eq, ← map_mul, hinner]
  have hP1 : (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inl j)) ^
      (ν (finSumFinEquiv (Sum.inl j))))
      = MvPolynomial.C (Ideal.Quotient.mk _ (cylFirst ν)) := by
    simp only [cylPhiVal_inl, ← map_pow, ← map_prod, cylFirst]
  unfold cylPhi
  rw [MvPolynomial.aeval_monomial]
  rw [finsupp_prod_split _ _ (fun i _ => pow_zero _)]
  rw [hP1, ← mul_assoc, hS]

/-- Free-exponent pattern of a second-block exponent. -/
def cylMExp (i₀ : Fin d) (T : Finset (CylFree d i₀)) (ν : Fin (d + d) →₀ ℕ) :
    CylFreeRem d i₀ T →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun s => ν (finSumFinEquiv (Sum.inr s.val.val)))
    (fun _ _ => Finset.mem_univ _)

/-- Reindexing free second-block factors to `σT` factors. -/
theorem sigma_prod_eq {M : Type} [CommMonoid M]
    {i₀ : Fin d} {T : Finset (CylFree d i₀)}
    (F : CylFreeRem d i₀ T → M) (G : Fin d → M)
    (hG0 : G i₀ = 1)
    (hGT : ∀ s ∈ T, G s.val = 1)
    (hFG : ∀ s : CylFreeRem d i₀ T, F s = G s.val.val) :
    ∏ s, F s = ∏ j, G j := by
  classical
  set img : Finset (Fin d) :=
    Finset.image (fun s : CylFreeRem d i₀ T => s.val.val) Finset.univ with himgdef
  have hmaps : ∀ a : CylFreeRem d i₀ T, ∀ _ : a ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
      (fun s : CylFreeRem d i₀ T => s.val.val) a ∈ img := by
    intro a _
    rw [himgdef]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hinj : ∀ a₁ : CylFreeRem d i₀ T, ∀ _ : a₁ ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
      ∀ a₂ : CylFreeRem d i₀ T, ∀ _ : a₂ ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
      (fun s : CylFreeRem d i₀ T => s.val.val) a₁ =
        (fun s : CylFreeRem d i₀ T => s.val.val) a₂ → a₁ = a₂ := by
    intro a₁ _ a₂ _ hab
    have h1 : a₁.val = a₂.val := Subtype.val_injective hab
    exact Subtype.ext h1
  have hsurj : ∀ b ∈ img, ∃ a, ∃ _ : a ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
      (fun s : CylFreeRem d i₀ T => s.val.val) a = b := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp (himgdef ▸ hb)
    exact ⟨a, ha, hab⟩
  have hval : ∀ a : CylFreeRem d i₀ T, ∀ _ : a ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
      F a = G ((fun s : CylFreeRem d i₀ T => s.val.val) a) :=
    fun a _ => hFG a
  have hB : (∏ s, F s) = ∏ j ∈ img, G j :=
    Finset.prod_bij (fun s _ => s.val.val) hmaps hinj hsurj hval
  have hA : (∏ j, G j) = ∏ j ∈ img, G j := by
    apply (Finset.prod_subset (Finset.subset_univ _) _).symm
    intro j _ hj
    by_cases heq : j = i₀
    · rw [heq]; exact hG0
    · have hmem : (⟨j, heq⟩ : CylFree d i₀) ∈ T := by
        by_contra hcon
        have hhit : j ∈ img := by
          rw [himgdef]
          exact Finset.mem_image_of_mem _
            (Finset.mem_univ (⟨⟨j, heq⟩, hcon⟩ : CylFreeRem d i₀ T))
        exact hj hhit
      have := hGT _ hmem
      simpa using this
  rw [hB, ← hA]

/-- Second-block product for a live exponent is a `σT`-monomial. -/
theorem free_part_eq (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (ν : Fin (d + d) →₀ ℕ)
    (hlive : ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0) :
    (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
      (ν (finSumFinEquiv (Sum.inr j))))
    = MvPolynomial.monomial (cylMExp i₀ T ν) 1 := by
  have hG0 : cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr i₀)) ^
      (ν (finSumFinEquiv (Sum.inr i₀))) = 1 := by
    rw [cylPhiVal_inr_eq, one_pow]
  have hGT : ∀ s ∈ T, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr s.val)) ^
      (ν (finSumFinEquiv (Sum.inr s.val))) = 1 := by
    intro s hs
    rw [cylPhiVal_inr_mem _ _ _ _ hs, hlive s hs, pow_zero]
  have hFG : ∀ s : CylFreeRem d i₀ T,
      MvPolynomial.X s ^ (ν (finSumFinEquiv (Sum.inr s.val.val)))
      = cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr s.val.val)) ^
        (ν (finSumFinEquiv (Sum.inr s.val.val))) := by
    intro s
    rw [cylPhiVal_inr_free _ _ _ _ s.property]
  have hreidx : (∏ s : CylFreeRem d i₀ T,
        MvPolynomial.X s ^ (ν (finSumFinEquiv (Sum.inr s.val.val))))
      = ∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
        (ν (finSumFinEquiv (Sum.inr j))) :=
    sigma_prod_eq
      (fun s : CylFreeRem d i₀ T =>
        MvPolynomial.X s ^ (ν (finSumFinEquiv (Sum.inr s.val.val))))
      (fun j : Fin d => cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
        (ν (finSumFinEquiv (Sum.inr j)))) hG0 hGT hFG
  rw [← hreidx]
  have hexp : ∀ s : CylFreeRem d i₀ T,
      ν (finSumFinEquiv (Sum.inr s.val.val)) = cylMExp i₀ T ν s := by
    intro s
    simp only [cylMExp, Finsupp.onFinset_apply]
  simp only [hexp]
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  apply (Finset.prod_subset (Finset.subset_univ _) _).symm
  intro s _ hs
  have h0 : cylMExp i₀ T ν s = 0 :=
    Finsupp.notMem_support_iff.mp hs
  rw [h0, pow_zero]

/-- Second-block product for a dead exponent vanishes. -/
theorem dead_part_eq (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (ν : Fin (d + d) →₀ ℕ)
    (hdead : ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0) :
    (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
      (ν (finSumFinEquiv (Sum.inr j)))) = 0 := by
  obtain ⟨s, hs, hne⟩ := hdead
  apply Finset.prod_eq_zero (Finset.mem_univ s.val)
  rw [cylPhiVal_inr_mem _ _ _ _ hs]
  exact zero_pow hne

/-- First-block product is a renamed source monomial part. -/
theorem first_prod_eq (ν : Fin (d + d) →₀ ℕ) :
    (∏ j : Fin d, MvPolynomial.X (finSumFinEquiv (Sum.inl j)) ^
      (ν (finSumFinEquiv (Sum.inl j)))) =
      commonSourcePolynomial (cylFirst ν) := by
  unfold cylFirst commonSourcePolynomial
  rw [MvPolynomial.rename_eq_aeval, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [map_pow, MvPolynomial.aeval_X]
  rfl

/-- Monomials split into first/second-block products. -/
theorem monomial_split (ν : Fin (d + d) →₀ ℕ) (c : ℂ) :
    MvPolynomial.monomial ν c = MvPolynomial.C c *
      ((∏ j : Fin d, MvPolynomial.X (finSumFinEquiv (Sum.inl j)) ^
        (ν (finSumFinEquiv (Sum.inl j)))) *
      (∏ j : Fin d, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
        (ν (finSumFinEquiv (Sum.inr j))))) := by
  rw [MvPolynomial.monomial_eq]
  congr 1
  exact finsupp_prod_split _ _ (fun i _ => pow_zero _)

/-- Second-block product factors off the fixed part (rebuilding). -/
theorem second_part_eq (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (ν : Fin (d + d) →₀ ℕ)
    (hlive : ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0)
    (m₀ : CylFreeRem d i₀ T →₀ ℕ) (hm : cylMExp i₀ T ν = m₀) :
    ((∏ j : Fin d, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
      (ν (finSumFinEquiv (Sum.inr j))) : Poly (d + d)))
    = MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) ^ (ν (finSumFinEquiv (Sum.inr i₀))) *
      (∏ s : CylFreeRem d i₀ T, MvPolynomial.X (finSumFinEquiv (Sum.inr s.val.val)) ^ (m₀ s)) := by
  classical
  set fixedFin : Finset (Fin d) := T.image (fun s => s.val) with hfixeddef
  set freeFin : Finset (Fin d) := Finset.univ.erase i₀ \ fixedFin with hfreedef
  have hfixed_sub : fixedFin ⊆ Finset.univ.erase i₀ := by
    intro j hj
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp (hfixeddef ▸ hj)
    rw [Finset.mem_erase]
    exact ⟨s.property, Finset.mem_univ _⟩
  have hpart : Finset.univ.erase i₀ = fixedFin ∪ freeFin := by
    rw [hfreedef]
    exact (Finset.union_sdiff_of_subset hfixed_sub).symm
  have hdisj : Disjoint fixedFin freeFin := by
    rw [hfreedef]
    exact Finset.disjoint_sdiff
  have h1 : ((∏ j : Fin d, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
      (ν (finSumFinEquiv (Sum.inr j))) : Poly (d + d)))
      = MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) ^ (ν (finSumFinEquiv (Sum.inr i₀))) *
        ∏ j ∈ Finset.univ.erase i₀, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
          (ν (finSumFinEquiv (Sum.inr j))) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)).symm
  have hfixed1 : ((∏ j ∈ fixedFin, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
      (ν (finSumFinEquiv (Sum.inr j))) : Poly (d + d))) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hfixeddef ▸ hj)
    rw [hlive s hs, pow_zero]
  have hsplit : ((∏ j ∈ Finset.univ.erase i₀, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
      (ν (finSumFinEquiv (Sum.inr j))) : Poly (d + d)))
      = (∏ s : CylFreeRem d i₀ T, MvPolynomial.X (finSumFinEquiv (Sum.inr s.val.val)) ^ (m₀ s)) := by
    have hfree : ((∏ j ∈ freeFin, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
        (ν (finSumFinEquiv (Sum.inr j))) : Poly (d + d)))
        = ∏ s : CylFreeRem d i₀ T, MvPolynomial.X (finSumFinEquiv (Sum.inr s.val.val)) ^ (m₀ s) := by
      have hmaps : ∀ a : CylFreeRem d i₀ T, ∀ _ : a ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
          (fun s : CylFreeRem d i₀ T => s.val.val) a ∈ freeFin := by
        intro s _
        have hne : s.val.val ≠ i₀ := s.val.property
        have hnfixed : s.val.val ∉ fixedFin := by
          intro hcon
          obtain ⟨s', hs', heq⟩ := Finset.mem_image.mp (hfixeddef ▸ hcon)
          have heq2 : s.val = s' := Subtype.ext heq.symm
          rw [← heq2] at hs'
          exact s.property hs'
        rw [hfreedef]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩, hnfixed⟩
      have hinj : ∀ a₁ : CylFreeRem d i₀ T, ∀ _ : a₁ ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
          ∀ a₂ : CylFreeRem d i₀ T, ∀ _ : a₂ ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
          (fun s : CylFreeRem d i₀ T => s.val.val) a₁ =
            (fun s : CylFreeRem d i₀ T => s.val.val) a₂ → a₁ = a₂ := by
        intro a₁ _ a₂ _ hab
        have h1 : a₁.val = a₂.val := Subtype.val_injective hab
        exact Subtype.ext h1
      have hsurj : ∀ b ∈ freeFin, ∃ a, ∃ _ : a ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
          (fun s : CylFreeRem d i₀ T => s.val.val) a = b := by
        intro j hj
        have hjne : j ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hj).1).1
        have hjnfixed : j ∉ fixedFin := (Finset.mem_sdiff.mp hj).2
        have hT : (⟨j, hjne⟩ : CylFree d i₀) ∉ T := by
          intro hcon
          apply hjnfixed
          rw [hfixeddef]
          exact Finset.mem_image_of_mem _ hcon
        exact ⟨⟨⟨j, hjne⟩, hT⟩, Finset.mem_univ _, rfl⟩
      have hval : ∀ a : CylFreeRem d i₀ T, ∀ _ : a ∈ (Finset.univ : Finset (CylFreeRem d i₀ T)),
          (MvPolynomial.X (finSumFinEquiv (Sum.inr a.val.val)) ^ (m₀ a) : Poly (d + d))
          = MvPolynomial.X (finSumFinEquiv (Sum.inr a.val.val)) ^
            (ν (finSumFinEquiv (Sum.inr a.val.val))) := by
        intro s _
        have hexp : m₀ s = ν (finSumFinEquiv (Sum.inr s.val.val)) := by
          rw [← hm]
          simp only [cylMExp, Finsupp.onFinset_apply]
        rw [hexp]
      have hbij := Finset.prod_bij (f :=
          fun s : CylFreeRem d i₀ T =>
            (MvPolynomial.X (finSumFinEquiv (Sum.inr s.val.val)) ^ (m₀ s) : Poly (d + d)))
        (g := fun j : Fin d =>
          (MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^ (ν (finSumFinEquiv (Sum.inr j))) : Poly (d + d)))
        (fun s : CylFreeRem d i₀ T => fun _ => s.val.val)
        hmaps hinj hsurj hval
      -- hbij : ∏_{univ σT} X^{m₀} = ∏_{freeFin} X^{ν}. Goal is reverse.
      exact hbij.symm
    have hunion : Finset.univ.erase i₀ = fixedFin ∪ freeFin := hpart
    calc (∏ j ∈ Finset.univ.erase i₀, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
          (ν (finSumFinEquiv (Sum.inr j))) : Poly (d + d))
        = (∏ j ∈ fixedFin, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
            (ν (finSumFinEquiv (Sum.inr j)))) *
          (∏ j ∈ freeFin, MvPolynomial.X (finSumFinEquiv (Sum.inr j)) ^
            (ν (finSumFinEquiv (Sum.inr j)))) := by
          rw [hunion, Finset.prod_union hdisj]
      _ = 1 * (∏ s : CylFreeRem d i₀ T, MvPolynomial.X (finSumFinEquiv (Sum.inr s.val.val)) ^ (m₀ s)) := by
          rw [hfixed1, hfree]
      _ = ∏ s : CylFreeRem d i₀ T, MvPolynomial.X (finSumFinEquiv (Sum.inr s.val.val)) ^ (m₀ s) := by
          rw [one_mul]
  rw [h1, hsplit]

/-- Source rename preserves multiplication. -/
theorem rename_src_mul (p q : Poly d) :
    commonSourcePolynomial (p * q) =
      commonSourcePolynomial p * commonSourcePolynomial q := by
  simp only [commonSourcePolynomial, MvPolynomial.rename_eq_aeval, map_mul]

/-- Source rename preserves scalars. -/
theorem rename_src_C (a : ℂ) :
    commonSourcePolynomial (MvPolynomial.C a) = (MvPolynomial.C a : Poly (d + d)) := by
  unfold commonSourcePolynomial
  rw [MvPolynomial.rename_C]

/-- Source rename preserves sums. -/
theorem rename_src_sum {ι : Type} (s : Finset ι) (f : ι → Poly d) :
    commonSourcePolynomial (∑ i ∈ s, f i) = ∑ i ∈ s, commonSourcePolynomial (f i) := by
  simp only [commonSourcePolynomial, MvPolynomial.rename_eq_aeval, map_sum]

/-- A dead monomial lies in the cylinder ideal (fixed-variable factor). -/
theorem cylDead_mem (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (g : Poly (d + d)) :
    ∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
      ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0),
      MvPolynomial.monomial ν (g.coeff ν) ∈ cylIdeal i₀ X T := by
  classical
  apply Ideal.sum_mem
  intro ν hν
  have hdead : ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0 :=
    (Finset.mem_filter.mp hν).2
  obtain ⟨s, hs, hne⟩ := hdead
  -- factor out X_{e(inr s.val)} (in the ideal) from the monomial
  have hXmem : MvPolynomial.X (finSumFinEquiv (Sum.inr s.val)) ∈ cylIdeal i₀ X T := by
    unfold cylIdeal
    exact Ideal.subset_span (Or.inr ⟨s, Finset.mem_coe.mpr hs, rfl⟩)
  -- monomial = X_k * (rest), with X_k ∈ ideal
  obtain ⟨q, hq⟩ := MvPolynomial.X_dvd_monomial.mpr
    (Or.inr hne : (g.coeff ν) = 0 ∨ ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0)
  rw [hq]
  exact Ideal.mul_mem_right _ _ hXmem

/-- R-coefficient sums over live fibers vanish. -/
theorem cylRcoeff_vanish (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (g : Poly (d + d))
    (hgPhi : cylPhi i₀ X T g = 0) (m₀ : CylFreeRem d i₀ T →₀ ℕ) :
    ∑ ν ∈ g.support.filter (fun ν =>
      (∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0) ∧ cylMExp i₀ T ν = m₀),
      Ideal.Quotient.mk (X.ideal : Ideal (Poly d)) (MvPolynomial.C (g.coeff ν) * cylFirst ν) = 0 := by
  classical
  have hsum0 : (∑ ν ∈ g.support, MvPolynomial.C (Ideal.Quotient.mk _
        (MvPolynomial.C (g.coeff ν) * cylFirst ν)) *
      (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
        (ν (finSumFinEquiv (Sum.inr j))))) = 0 := by
    have e : (∑ ν ∈ g.support, MvPolynomial.C (Ideal.Quotient.mk _
          (MvPolynomial.C (g.coeff ν) * cylFirst ν)) *
        (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
          (ν (finSumFinEquiv (Sum.inr j)))))
        = cylPhi i₀ X T g := by
      simp only [← cylPhi_monomial]
      rw [← map_sum, ← MvPolynomial.as_sum g]
    rw [e]
    exact hgPhi
  have hlc : (∑ ν ∈ g.support, MvPolynomial.lcoeff _ m₀
      (MvPolynomial.C (Ideal.Quotient.mk _
        (MvPolynomial.C (g.coeff ν) * cylFirst ν)) *
        (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
          (ν (finSumFinEquiv (Sum.inr j)))))) = 0 := by
    have hcongr := congrArg (MvPolynomial.lcoeff _ m₀) hsum0
    simpa using hcongr
  have hterm : ∀ ν ∈ g.support, MvPolynomial.lcoeff _ m₀
      (MvPolynomial.C (Ideal.Quotient.mk _
        (MvPolynomial.C (g.coeff ν) * cylFirst ν)) *
        (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
          (ν (finSumFinEquiv (Sum.inr j)))))
      = if ((∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0) ∧ cylMExp i₀ T ν = m₀)
        then Ideal.Quotient.mk _
          (MvPolynomial.C (g.coeff ν) * cylFirst ν) else 0 := by
    intro ν _
    by_cases hlive : ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0
    · by_cases hmatch : cylMExp i₀ T ν = m₀
      · rw [if_pos ⟨hlive, hmatch⟩]
        have eP : (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
            (ν (finSumFinEquiv (Sum.inr j))))
            = MvPolynomial.monomial m₀ 1 := by
          rw [← hmatch]
          exact free_part_eq _ _ _ _ hlive
        rw [eP, ← MvPolynomial.smul_eq_C_mul, map_smul]
        have e1 : MvPolynomial.lcoeff (Poly d ⧸ X.ideal) m₀
            (MvPolynomial.monomial m₀ (1 : Poly d ⧸ X.ideal)) = 1 := by
          rw [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]
          simp
        rw [e1, smul_eq_mul, mul_one]
      · rw [if_neg (fun h => hmatch h.2)]
        have eP : (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
            (ν (finSumFinEquiv (Sum.inr j))))
            = MvPolynomial.monomial (cylMExp i₀ T ν) 1 :=
          free_part_eq _ _ _ _ hlive
        rw [eP, ← MvPolynomial.smul_eq_C_mul, map_smul]
        have e0 : MvPolynomial.lcoeff (Poly d ⧸ X.ideal) m₀
            (MvPolynomial.monomial (cylMExp i₀ T ν) (1 : Poly d ⧸ X.ideal)) = 0 := by
          rw [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]
          simp [hmatch]
        rw [e0, smul_eq_mul, mul_zero]
    · rw [if_neg (fun h => hlive h.1)]
      have eP : (∏ j : Fin d, cylPhiVal i₀ X T (finSumFinEquiv (Sum.inr j)) ^
          (ν (finSumFinEquiv (Sum.inr j)))) = 0 := by
        apply dead_part_eq
        push_neg at hlive
        exact hlive
      rw [eP, mul_zero]
      exact map_zero _
  rw [Finset.sum_congr rfl (fun ν hν => hterm ν hν)] at hlc
  rw [← Finset.sum_filter] at hlc
  exact hlc

/-- A live fiber's monomial sum lies in the cylinder ideal. -/
theorem cylGroup_mem (i₀ : Fin d) (X : AffineVariety d)
    (T : Finset (CylFree d i₀)) (g : Poly (d + d))
    (hgPhi : cylPhi i₀ X T g = 0) (m₀ : CylFreeRem d i₀ T →₀ ℕ) :
    ∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
      (∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0) ∧ cylMExp i₀ T ν = m₀),
      MvPolynomial.monomial ν (g.coeff ν) ∈ cylIdeal i₀ X T := by
  classical
  set Grp := g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
    (∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0) ∧ cylMExp i₀ T ν = m₀) with hGrpdef
  set u : Poly (d + d) := MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) with hudef
  have hmem : ∀ ν ∈ Grp, (∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0) ∧
      cylMExp i₀ T ν = m₀ := fun ν hν => (Finset.mem_filter.mp hν).2
  -- A and its vanishing
  set A : Poly d := ∑ ν ∈ Grp, MvPolynomial.C (g.coeff ν) * cylFirst ν with hAdef
  have hRvan : ∑ ν ∈ Grp, Ideal.Quotient.mk (X.ideal : Ideal (Poly d))
      (MvPolynomial.C (g.coeff ν) * cylFirst ν) = 0 :=
    cylRcoeff_vanish _ _ _ _ hgPhi _
  have hmkA : Ideal.Quotient.mk (X.ideal : Ideal (Poly d)) A = 0 := by
    rw [hAdef, map_sum]
    exact hRvan
  have hAX : A ∈ X.ideal := Ideal.Quotient.eq_zero_iff_mem.mp hmkA
  -- R in the ideal
  set R : Poly (d + d) := commonSourcePolynomial A with hRdef
  have hRmem : R ∈ cylIdeal i₀ X T := by
    have himg : commonSourcePolynomial A ∈ commonSourcePolynomial '' (X.ideal : Set (Poly d)) :=
      ⟨A, hAX, rfl⟩
    unfold cylIdeal
    exact Ideal.subset_span (Or.inl (Or.inl himg))
  -- H
  set H : Poly (d + d) := ∑ ν ∈ Grp, commonSourcePolynomial
      (MvPolynomial.C (g.coeff ν) * cylFirst ν) *
      u ^ (ν (finSumFinEquiv (Sum.inr i₀))) with hHdef
  -- G = H * W
  have hGW : (∑ ν ∈ Grp, MvPolynomial.monomial ν (g.coeff ν)) = H *
      (∏ s : CylFreeRem d i₀ T, MvPolynomial.X (finSumFinEquiv (Sum.inr s.val.val)) ^ (m₀ s)) := by
    rw [hHdef, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν hν
    have hlive := (hmem ν hν).1
    have hmatch := (hmem ν hν).2
    rw [monomial_split, first_prod_eq,
      second_part_eq i₀ X T ν hlive m₀ hmatch]
    have eC : commonSourcePolynomial (MvPolynomial.C (g.coeff ν) * cylFirst ν)
        = MvPolynomial.C (g.coeff ν) * commonSourcePolynomial (cylFirst ν) := by
      rw [rename_src_mul, rename_src_C]
    rw [eC]
    ring
  -- H - R is a multiple of (u - 1)
  have hHR : H - R = (u - 1) * (∑ ν ∈ Grp, commonSourcePolynomial
      (MvPolynomial.C (g.coeff ν) * cylFirst ν) *
      (∑ i ∈ Finset.range (ν (finSumFinEquiv (Sum.inr i₀))), u ^ i)) := by
    have hRexp : R = ∑ ν ∈ Grp, commonSourcePolynomial
        (MvPolynomial.C (g.coeff ν) * cylFirst ν) * 1 := by
      rw [hRdef, hAdef, rename_src_sum]
      apply Finset.sum_congr rfl
      intro ν _
      rw [mul_one]
    rw [hHdef, hRexp, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    -- per-term geometric identity
    have egeom : u ^ (ν (finSumFinEquiv (Sum.inr i₀))) - 1
        = (u - 1) * (∑ i ∈ Finset.range (ν (finSumFinEquiv (Sum.inr i₀))), u ^ i) := by
      have hgeom := geom_sum₂_mul u (1 : Poly (d + d)) (ν (finSumFinEquiv (Sum.inr i₀)))
      simpa [mul_comm] using hgeom.symm
    calc commonSourcePolynomial (MvPolynomial.C (g.coeff ν) * cylFirst ν) *
            u ^ (ν (finSumFinEquiv (Sum.inr i₀))) -
          commonSourcePolynomial (MvPolynomial.C (g.coeff ν) * cylFirst ν) * 1
        = commonSourcePolynomial (MvPolynomial.C (g.coeff ν) * cylFirst ν) *
            (u ^ (ν (finSumFinEquiv (Sum.inr i₀))) - 1) := by ring
      _ = commonSourcePolynomial (MvPolynomial.C (g.coeff ν) * cylFirst ν) *
            ((u - 1) * (∑ i ∈ Finset.range (ν (finSumFinEquiv (Sum.inr i₀))), u ^ i)) := by
          rw [egeom]
      _ = (u - 1) * (commonSourcePolynomial (MvPolynomial.C (g.coeff ν) * cylFirst ν) *
            (∑ i ∈ Finset.range (ν (finSumFinEquiv (Sum.inr i₀))), u ^ i)) := by ring
  -- H ∈ ideal
  have hHmem : H ∈ cylIdeal i₀ X T := by
    have hU1 : u - 1 ∈ cylIdeal i₀ X T := by
      unfold cylIdeal
      exact Ideal.subset_span (Or.inl (Or.inr rfl))
    have hmem2 : H - R ∈ cylIdeal i₀ X T := by
      rw [hHR]
      exact Ideal.mul_mem_right _ _ hU1
    have hHeq : H = R + (H - R) := by abel
    rw [hHeq]
    exact Ideal.add_mem _ hRmem hmem2
  -- conclude
  rw [hGW]
  exact Ideal.mul_mem_right _ _ hHmem

/-- The kernel equals the cylinder ideal. -/
theorem cylKer_eq (i₀ : Fin d) (X : AffineVariety d) (T : Finset (CylFree d i₀)) :
    RingHom.ker (cylPhi i₀ X T).toRingHom = cylIdeal i₀ X T := by
  apply le_antisymm
  · -- ker ⊆ span: partition into dead and live fibers
    intro g hg
    have hgPhi : cylPhi i₀ X T g = 0 := RingHom.mem_ker.mp hg
    show g ∈ Ideal.span _
    -- split support into dead / live
    have hsplit : (∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0),
          MvPolynomial.monomial ν (g.coeff ν)) +
        (∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0),
          MvPolynomial.monomial ν (g.coeff ν)) = g := by
      have hU : g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0) ∪
          g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0) = g.support := by
        ext ν
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hmem, -⟩ | ⟨hmem, -⟩) <;> exact hmem
        · intro hmem
          by_cases hd : (∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0)
          · exact Or.inl ⟨hmem, hd⟩
          · right
            refine ⟨hmem, ?_⟩
            intro s hs
            by_contra hne
            exact hd ⟨s, hs, hne⟩
      have hD : Disjoint (g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0))
          (g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0)) := by
        rw [Finset.disjoint_left]
        intro ν hD hL
        obtain ⟨-, hd⟩ := Finset.mem_filter.mp hD
        obtain ⟨-, hl⟩ := Finset.mem_filter.mp hL
        obtain ⟨s, hs, hne⟩ := hd
        exact hne (hl s hs)
      calc (∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
              ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0),
              MvPolynomial.monomial ν (g.coeff ν)) +
            (∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
              ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0),
              MvPolynomial.monomial ν (g.coeff ν))
          = ∑ ν ∈ (g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
              ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0) ∪
            g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
              ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0)),
            MvPolynomial.monomial ν (g.coeff ν) := (Finset.sum_union hD).symm
        _ = ∑ ν ∈ g.support, MvPolynomial.monomial ν (g.coeff ν) := by rw [hU]
        _ = g := (MvPolynomial.as_sum g).symm
    -- dead part in ideal
    have hdead : (∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0),
          MvPolynomial.monomial ν (g.coeff ν)) ∈ cylIdeal i₀ X T :=
      cylDead_mem _ _ _ _
    -- live part in ideal via fibers
    have hlive : (∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0),
          MvPolynomial.monomial ν (g.coeff ν)) ∈ cylIdeal i₀ X T := by
      -- partition live by m_ν values
      set L := g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
        ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0) with hLdef
      set Img := L.image (fun ν => cylMExp i₀ T ν) with hImgdef
      have hfib : (∑ ν ∈ L, MvPolynomial.monomial ν (g.coeff ν))
          = ∑ m₀ ∈ Img, ∑ ν ∈ L.filter (fun ν => cylMExp i₀ T ν = m₀),
            MvPolynomial.monomial ν (g.coeff ν) := by
        have hmaps : ∀ i ∈ L, (fun ν => cylMExp i₀ T ν) i ∈ Img := by
          intro i hi
          rw [hImgdef]
          exact Finset.mem_image_of_mem _ hi
        have hfw := Finset.sum_fiberwise_of_maps_to hmaps
          (fun ν => MvPolynomial.monomial ν (g.coeff ν))
        -- hfw : ∑_{m₀∈Img} ∑_{ν∈L, m=m₀} = ∑_{ν∈L}. symm to match goal.
        exact hfw.symm
      rw [hfib]
      apply Ideal.sum_mem
      intro m₀ _
      -- fiber = live group for m₀
      have hfibeq : L.filter (fun ν => cylMExp i₀ T ν = m₀)
          = g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
            (∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0) ∧ cylMExp i₀ T ν = m₀) := by
        rw [hLdef, Finset.filter_filter]
      rw [hfibeq]
      exact cylGroup_mem _ _ _ _ hgPhi _
    -- assemble
    have hg_eq : g = (∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∃ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) ≠ 0),
          MvPolynomial.monomial ν (g.coeff ν)) +
        (∑ ν ∈ g.support.filter (fun ν : Fin (d + d) →₀ ℕ =>
          ∀ s ∈ T, ν (finSumFinEquiv (Sum.inr s.val)) = 0),
          MvPolynomial.monomial ν (g.coeff ν)) := hsplit.symm
    rw [hg_eq]
    exact Ideal.add_mem _ hdead hlive
  · -- span ⊆ ker: generators map to zero
    unfold cylIdeal
    rw [Ideal.span_le]
    intro g hg
    show (cylPhi i₀ X T).toRingHom g = 0
    rw [Set.mem_union] at hg
    cases hg with
    | inl h =>
      rw [Set.mem_union] at h
      cases h with
      | inl h =>
        obtain ⟨f, hf, rfl⟩ := h
        have e0 : Ideal.Quotient.mk (X.ideal : Ideal (Poly d)) f = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hf
        have e1 : (cylPhi i₀ X T).toRingHom (commonSourcePolynomial f)
            = MvPolynomial.C (Ideal.Quotient.mk _ f) := cylPhi_src _ _ _ _
        rw [e1, e0, map_zero]
      | inr h =>
        have hgg : g = (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1 : Poly (d + d)) :=
          Set.mem_singleton_iff.mp h
        rw [hgg]
        have e1 : (cylPhi i₀ X T).toRingHom
            (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀))) = 1 := by
          show cylPhi i₀ X T _ = 1
          unfold cylPhi
          rw [MvPolynomial.aeval_X]
          exact cylPhiVal_inr_eq _ _ _
        rw [map_sub, e1, map_one, sub_self]
    | inr h =>
      obtain ⟨s, hs, rfl⟩ := h
      have hs' : s ∈ T := Finset.mem_coe.mp hs
      have e0 : (cylPhi i₀ X T).toRingHom
          (MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))) = 0 := by
        show cylPhi i₀ X T _ = 0
        unfold cylPhi
        rw [MvPolynomial.aeval_X]
        exact cylPhiVal_inr_mem _ _ _ _ hs'
      exact e0

/-- Parametrized cylinders over irreducible carriers are prime. -/
theorem cylIdeal_prime (i₀ : Fin d) (X : AffineVariety d) (hX : X.IsIrreducible)
    (T : Finset (CylFree d i₀)) : (cylIdeal i₀ X T).IsPrime := by
  haveI : IsDomain (Poly d ⧸ X.ideal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hX
  have hker : RingHom.ker (cylPhi i₀ X T).toRingHom = cylIdeal i₀ X T :=
    cylKer_eq _ _ _
  rw [← hker]
  exact RingHom.ker_isPrime _

/-- The source carriers have `d-1` free second-block variables. -/
theorem card_CylFree (i₀ : Fin d) : Fintype.card (CylFree d i₀) = d - 1 := by
  classical
  have h1 : (Finset.univ.erase i₀).card = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have e : CylFree d i₀ ≃ ↥(Finset.univ.erase i₀ : Finset (Fin d)) := by
    refine ⟨fun j => ⟨j.val, ?_⟩, fun j => ⟨j.val, ?_⟩, fun j => ?_, fun j => ?_⟩
    · rw [Finset.mem_erase]
      exact ⟨j.property, Finset.mem_univ _⟩
    · have hj := j.property
      rw [Finset.mem_erase] at hj
      exact hj.1
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  rw [Fintype.card_congr e, Fintype.card_coe]
  exact h1

/-- Free-variable count in terms of fixed count. -/
theorem card_CylFreeRem (i₀ : Fin d) (T : Finset (CylFree d i₀)) :
    Fintype.card (CylFreeRem d i₀ T) = (d - 1) - T.card := by
  classical
  -- σT ≃ ↥(univ \ T)
  have e : CylFreeRem d i₀ T ≃ ↥(Finset.univ \ T : Finset (CylFree d i₀)) := by
    refine ⟨fun s => ⟨s.val, ?_⟩, fun s => ⟨s.val, ?_⟩, fun s => ?_, fun s => ?_⟩
    · rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, s.property⟩
    · have hs := s.property
      rw [Finset.mem_sdiff] at hs
      exact hs.2
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_sdiff,
    Finset.inter_univ, Finset.card_univ, card_CylFree]

/-- Dimension of a parametrized cylinder via the transcendence tower. -/
theorem cylVar_dimension (i₀ : Fin d) (X : AffineVariety d) (hX : X.IsIrreducible)
    (T : Finset (CylFree d i₀)) :
    (cylVar i₀ X T).dimension = X.dimension + Fintype.card (CylFreeRem d i₀ T) := by
  haveI : X.ideal.IsPrime := hX
  haveI : IsDomain (Poly d ⧸ X.ideal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hX
  have hprime := cylIdeal_prime i₀ X hX T
  have hker := cylKer_eq i₀ X T
  have hrad : (cylVar i₀ X T).ideal = cylIdeal i₀ X T := by
    have h1 : (cylVar i₀ X T).ideal = (cylIdeal i₀ X T).radical := rfl
    rw [h1]
    exact hprime.isRadical.radical
  have hE : (Poly (d + d) ⧸ RingHom.ker (cylPhi i₀ X T).toRingHom) ≃ₐ[ℂ]
      MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal) :=
    Ideal.quotientKerAlgEquivOfSurjective (cylPhi_surjective _ _ _)
  haveI hF1 := (faithfulSMul_iff_algebraMap_injective ℂ (Poly d ⧸ X.ideal)).mpr
    (algebraMap ℂ (Poly d ⧸ X.ideal)).injective
  haveI hF2 : FaithfulSMul (Poly d ⧸ X.ideal)
      (MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [MvPolynomial.algebraMap_eq]
      exact MvPolynomial.C_injective _ _)
  have htower := trdeg_add_eq ℂ (Poly d ⧸ X.ideal)
    (A := MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal))
  have htop : Algebra.trdeg (Poly d ⧸ X.ideal)
      (MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal))
      = Fintype.card (CylFreeRem d i₀ T) := by
    have h := MvPolynomial.trdeg_of_isDomain (S := Poly d ⧸ X.ideal)
      (ι := CylFreeRem d i₀ T)
    simpa [Cardinal.mk_fintype] using h
  -- assemble in Cardinals, then descend to ℕ
  have hdimX : (OAI.QuarticPowerFree.affineDimension X.ideal : Cardinal) =
      Algebra.trdeg ℂ (Poly d ⧸ X.ideal) :=
    GenericFiber.affineDimension_eq_trdeg _
  have hdimC : (OAI.QuarticPowerFree.affineDimension (cylIdeal i₀ X T) : Cardinal) =
      Algebra.trdeg ℂ (Poly d ⧸ X.ideal) + Fintype.card (CylFreeRem d i₀ T) := by
    have e1 : (OAI.QuarticPowerFree.affineDimension (cylIdeal i₀ X T) : Cardinal)
        = Algebra.trdeg ℂ (Poly (d + d) ⧸ cylIdeal i₀ X T) :=
      GenericFiber.affineDimension_eq_trdeg _
    rw [e1, ← hker]
    have htr : Algebra.trdeg ℂ (Poly (d + d) ⧸ RingHom.ker (cylPhi i₀ X T).toRingHom)
        = Algebra.trdeg ℂ (MvPolynomial (CylFreeRem d i₀ T) (Poly d ⧸ X.ideal)) := by
      with_unfolding_all exact hE.trdeg_eq
    rw [htr, ← htower, htop]
  have hfin : OAI.QuarticPowerFree.affineDimension (cylIdeal i₀ X T)
      = OAI.QuarticPowerFree.affineDimension X.ideal +
        Fintype.card (CylFreeRem d i₀ T) := by
    have hC : ((OAI.QuarticPowerFree.affineDimension (cylIdeal i₀ X T)) : Cardinal)
        = ((OAI.QuarticPowerFree.affineDimension X.ideal) : Cardinal) +
          ((Fintype.card (CylFreeRem d i₀ T)) : Cardinal) := by
      rw [hdimC, hdimX]
    exact_mod_cast hC
  -- conclude via hrad
  have eDim : (cylVar i₀ X T).dimension
      = OAI.QuarticPowerFree.affineDimension (cylIdeal i₀ X T) := by
    show OAI.QuarticPowerFree.affineDimension (cylVar i₀ X T).ideal = _
    rw [hrad]
  have eX : X.dimension = OAI.QuarticPowerFree.affineDimension X.ideal := rfl
  rw [eDim, eX]
  exact hfin

end
end DistinctDistances.SparseCones

/-! Base section: fixing all free variables (item 186 degree base). -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Substitution fixing second-block coordinates (`i₀ ↦ 1`, others `↦ 0`). -/
def cylSubstVal (i₀ : Fin d) (k : Fin (d + d)) : Poly d :=
  Sum.elim (fun j => MvPolynomial.X j)
    (fun j => MvPolynomial.C (if j = i₀ then 1 else 0)) (finSumFinEquiv.symm k)

/-- The substitution map. -/
def cylSubst (i₀ : Fin d) : Poly (d + d) →ₐ[ℂ] Poly d :=
  MvPolynomial.aeval (cylSubstVal i₀)

/-- Substitution fixes first-block variables. -/
theorem cylSubst_inl (i₀ : Fin d) (j : Fin d) :
    cylSubst i₀ (MvPolynomial.X (finSumFinEquiv (Sum.inl j))) =
      MvPolynomial.X j := by
  unfold cylSubst cylSubstVal
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply, Sum.elim_inl]

/-- Substitution evaluates second-block variables to constants. -/
theorem cylSubst_inr (i₀ : Fin d) (j : Fin d) :
    cylSubst i₀ (MvPolynomial.X (finSumFinEquiv (Sum.inr j))) =
      MvPolynomial.C (if j = i₀ then 1 else 0) := by
  unfold cylSubst cylSubstVal
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply, Sum.elim_inr]

/-- Source rename preserves addition. -/
theorem rename_src_add (p q : Poly d) :
    commonSourcePolynomial (p + q) =
      commonSourcePolynomial p + commonSourcePolynomial q := by
  simp only [commonSourcePolynomial, MvPolynomial.rename_eq_aeval, map_add]

/-- Substitution is the identity on source polynomials. -/
theorem cylSubst_rename (i₀ : Fin d) (f : Poly d) :
    cylSubst i₀ (commonSourcePolynomial f) = f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    show cylSubst i₀ (commonSourcePolynomial (MvPolynomial.C a)) = _
    unfold commonSourcePolynomial
    rw [MvPolynomial.rename_C]
    show cylSubst i₀ (MvPolynomial.C a) = _
    unfold cylSubst
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    rw [rename_src_add, map_add, hp, hq]
  | mul_X p n hp =>
    rw [rename_src_mul, map_mul, hp]
    congr 1
    unfold commonSourcePolynomial
    rw [MvPolynomial.rename_X]
    exact cylSubst_inl _ _

/-- First-block index inclusion, with clean typing. -/
abbrev inlMap (d : ℕ) : Fin d → Fin (d + d) := fun k => finSumFinEquiv (Sum.inl k)

/-- The source embedding as evaluation equals renaming. -/
theorem aeval_rename_eq (x : Poly d) :
    (MvPolynomial.aeval (fun k => MvPolynomial.X (inlMap d k)) x : Poly (d + d))
    = MvPolynomial.rename (inlMap d) x := by
  simp only [MvPolynomial.rename_eq_aeval]
  rfl

/-- Quotient-level backward map (source classes to cylinder classes). -/
def cylBackQ (i₀ : Fin d) (X : AffineVariety d) :
    (Poly d ⧸ X.ideal) →ₐ[ℂ] (Poly (d + d) ⧸ (cylVar i₀ X Finset.univ).ideal) :=
  have hle : X.ideal ≤ Ideal.comap
      (MvPolynomial.aeval (fun k => MvPolynomial.X (inlMap d k)) :
        Poly d →ₐ[ℂ] Poly (d + d))
      (cylVar i₀ X Finset.univ).ideal := by
    intro x hx
    have e := aeval_rename_eq x
    have hmem : MvPolynomial.aeval (fun k => MvPolynomial.X (inlMap d k)) x ∈
        cylIdeal i₀ X Finset.univ := by
      rw [e]
      have himg : MvPolynomial.rename (inlMap d) x ∈
          MvPolynomial.rename (inlMap d) '' (X.ideal : Set (Poly d)) :=
        ⟨x, hx, rfl⟩
      unfold cylIdeal
      exact Ideal.subset_span (Or.inl (Or.inl himg))
    -- cylIdeal ≤ (cylVar).ideal since ofIdeal takes radical
    have hle2 : cylIdeal i₀ X Finset.univ ≤ (cylVar i₀ X Finset.univ).ideal := by
      unfold cylVar
      exact Ideal.le_radical
    exact hle2 hmem
  Ideal.quotientMapₐ _ _ hle

/-- Substitution does not increase total degree. -/
theorem cylSubst_totalDegree_le (i₀ : Fin d) (g : Poly (d + d)) :
    (cylSubst i₀ g).totalDegree ≤ g.totalDegree := by
  classical
  have hdeg1 : ∀ k : Fin (d + d), (cylSubstVal i₀ k).totalDegree ≤ 1 := by
    intro k
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective k
    cases y with
    | inl j =>
      unfold cylSubstVal
      rw [Equiv.symm_apply_apply, Sum.elim_inl]
      exact (MvPolynomial.totalDegree_X _).le
    | inr j =>
      unfold cylSubstVal
      rw [Equiv.symm_apply_apply, Sum.elim_inr, MvPolynomial.totalDegree_C]
      exact zero_le_one
  -- per-monomial bound
  have hmono : ∀ ν ∈ g.support, ∀ c : ℂ,
      (cylSubst i₀ (MvPolynomial.monomial ν c)).totalDegree ≤
        (MvPolynomial.monomial ν c).totalDegree := by
    intro ν _ c
    by_cases hc : c = 0
    · simp [hc]
    · unfold cylSubst
      rw [MvPolynomial.aeval_monomial]
      have hdeg : (algebraMap ℂ (Poly d) c *
          ν.prod (fun i k => cylSubstVal i₀ i ^ k)).totalDegree ≤
          ν.sum (fun _ e => e) := by
        have e0 : (algebraMap ℂ (Poly d) c).totalDegree = 0 := by
          rw [MvPolynomial.algebraMap_eq]
          exact MvPolynomial.totalDegree_C _
        have eP : (ν.prod (fun i k => cylSubstVal i₀ i ^ k)).totalDegree ≤
            ν.sum (fun _ e => e) := by
          have eP1 : ν.prod (fun i k => cylSubstVal i₀ i ^ k)
              = ∏ i ∈ ν.support, cylSubstVal i₀ i ^ (ν i) := rfl
          rw [eP1]
          refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
          have hle : ∀ i ∈ ν.support,
              (cylSubstVal i₀ i ^ (ν i)).totalDegree ≤ ν i := by
            intro i _
            calc (cylSubstVal i₀ i ^ (ν i)).totalDegree
                ≤ (ν i) * (cylSubstVal i₀ i).totalDegree :=
                  MvPolynomial.totalDegree_pow _ _
              _ ≤ (ν i) * 1 :=
                  mul_le_mul_of_nonneg_left (hdeg1 i) (Nat.zero_le _)
              _ = ν i := mul_one _
          calc ∑ i ∈ ν.support, (cylSubstVal i₀ i ^ (ν i)).totalDegree
              ≤ ∑ i ∈ ν.support, ν i := Finset.sum_le_sum hle
            _ = ν.sum (fun _ e => e) := rfl
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [e0, zero_add]
        exact eP
      have hmono_eq : (MvPolynomial.monomial ν c).totalDegree
          = ν.sum (fun _ e => e) :=
        MvPolynomial.totalDegree_monomial _ hc
      rw [hmono_eq]
      exact hdeg
  -- assemble
  have hfin : (cylSubst i₀ g).totalDegree ≤ g.totalDegree := by
    conv_lhs => rw [MvPolynomial.as_sum g]
    rw [map_sum]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    apply Finset.sup_le
    intro ν hν
    refine (hmono ν hν _).trans ?_
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    exact MvPolynomial.le_totalDegree hν
  exact hfin

/-- The quotient map factors through substitution (`T = univ` base). -/
theorem cylPhi_univ_eq (i₀ : Fin d) (X : AffineVariety d) (g : Poly (d + d)) :
    cylPhi i₀ X Finset.univ g =
      MvPolynomial.C (Ideal.Quotient.mk _ (cylSubst i₀ g)) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    show cylPhi i₀ X Finset.univ (MvPolynomial.C a) = _
    unfold cylPhi
    rw [MvPolynomial.aeval_C]
    -- LHS algebraMap; RHS C(mk(S(C a))) with S(C a) = C a.
    have eS : cylSubst i₀ (MvPolynomial.C a) = MvPolynomial.C a := by
      unfold cylSubst
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    rw [eS, mk_C_eq, target_scalar_eq]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p n hp =>
    have eX : cylPhi i₀ X Finset.univ (MvPolynomial.X n)
        = MvPolynomial.C (Ideal.Quotient.mk _ (cylSubst i₀ (MvPolynomial.X n))) := by
      obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective n
      cases y with
      | inl j =>
        show cylPhi i₀ X Finset.univ (MvPolynomial.X (finSumFinEquiv (Sum.inl j))) = _
        unfold cylPhi
        rw [MvPolynomial.aeval_X]
        rw [cylPhiVal_inl]
        -- RHS C(mk(S(X))) with S(X) = X_j
        have eS : cylSubst i₀ (MvPolynomial.X (finSumFinEquiv (Sum.inl j))) =
            MvPolynomial.X j := cylSubst_inl _ _
        rw [eS]
      | inr j =>
        show cylPhi i₀ X Finset.univ (MvPolynomial.X (finSumFinEquiv (Sum.inr j))) =
          MvPolynomial.C (Ideal.Quotient.mk _ (cylSubst i₀ (MvPolynomial.X (finSumFinEquiv (Sum.inr j)))))
        unfold cylPhi
        rw [MvPolynomial.aeval_X]
        by_cases heq : j = i₀
        · rw [heq]
          rw [cylPhiVal_inr_eq]
          have eS : cylSubst i₀ (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀))) =
              MvPolynomial.C 1 := by
            rw [cylSubst_inr]
            simp
          rw [eS]
          simp [mk_C_eq]
        · have ePhi : cylPhiVal i₀ X Finset.univ (finSumFinEquiv (Sum.inr j)) = 0 := by
            have hmem : (⟨j, heq⟩ : CylFree d i₀) ∈ (Finset.univ : Finset (CylFree d i₀)) :=
              Finset.mem_univ _
            unfold cylPhiVal
            rw [Equiv.symm_apply_apply, Sum.elim_inr]
            simp [heq, hmem]
          rw [ePhi]
          have eS : cylSubst i₀ (MvPolynomial.X (finSumFinEquiv (Sum.inr j))) =
              MvPolynomial.C 0 := by
            rw [cylSubst_inr]
            simp [heq]
          rw [eS]
          simp [mk_C_eq]
    simp only [map_mul, hp, eX]

/-- Computation of the backward map on generators. -/
theorem cylBackQ_mk (i₀ : Fin d) (X : AffineVariety d) (f : Poly d) :
    cylBackQ i₀ X (Ideal.Quotient.mkₐ ℂ X.ideal f) =
      Ideal.Quotient.mkₐ ℂ (cylVar i₀ X Finset.univ).ideal
        (MvPolynomial.aeval (fun k => MvPolynomial.X (inlMap d k)) f) := by
  rfl

/-- Backward restriction map (source Hilbert space to cylinder Hilbert space). -/
def cylBack (i₀ : Fin d) (X : AffineVariety d) (D : ℕ) :
    X.restrictionSpace D →ₗ[ℂ] (cylVar i₀ X Finset.univ).restrictionSpace D where
  toFun x := ⟨cylBackQ i₀ X x.val, by
    obtain ⟨f, hf, heq⟩ := x.property
    -- BwdQ x.val = BwdQ (mk f) = mk (aeval f); aeval f has degree via rename
    have e1 : cylBackQ i₀ X x.val
        = Ideal.Quotient.mkₐ ℂ (cylVar i₀ X Finset.univ).ideal
          (MvPolynomial.aeval (fun k => MvPolynomial.X (inlMap d k)) f) := by
      rw [← heq]
      exact cylBackQ_mk _ _ _
    rw [e1]
    -- mk (aeval f) ∈ restr; convert aeval to rename, then degree + mem_map.
    rw [aeval_rename_eq]
    refine ⟨MvPolynomial.rename (inlMap d) f, ?_, rfl⟩
    simp only [SetLike.mem_coe, OAI.QuarticPowerFree.mem_totalSpace] at hf ⊢
    exact (MvPolynomial.totalDegree_rename_le _ _).trans hf⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    show cylBackQ i₀ X (x.val + y.val) = _
    rw [map_add]
    rfl
  map_smul' := by
    intro c x
    apply Subtype.ext
    show cylBackQ i₀ X (c • x.val) = _
    rw [map_smul]
    rfl

/-! Cylinder ideals vs varieties, base degree, and the section chain (item 186 degree).

The base-section block above is still open, so these continue in the same
namespace. -/

/-- The parametrized cylinder's ideal is the (prime) cylinder ideal. -/
theorem cylVar_ideal_eq (i₀ : Fin d) (X : AffineVariety d) (hX : X.IsIrreducible)
    (T : Finset (CylFree d i₀)) :
    (cylVar i₀ X T).ideal = cylIdeal i₀ X T := by
  have hprime := cylIdeal_prime i₀ X hX T
  have h1 : (cylVar i₀ X T).ideal = (cylIdeal i₀ X T).radical := rfl
  rw [h1]
  exact hprime.isRadical.radical

/-- The substitution descends to the base-section quotient. -/
def cylFwdQ (i₀ : Fin d) (X : AffineVariety d) :
    (Poly (d + d) ⧸ (cylVar i₀ X Finset.univ).ideal) →ₐ[ℂ] (Poly d ⧸ X.ideal) := by
  have hgen : cylIdeal i₀ X Finset.univ ≤ Ideal.comap (cylSubst i₀) X.ideal := by
    unfold cylIdeal
    rw [Ideal.span_le]
    intro g hg
    rw [Set.mem_union] at hg
    cases hg with
    | inl h =>
      rw [Set.mem_union] at h
      cases h with
      | inl h =>
        obtain ⟨f, hf, rfl⟩ := h
        show cylSubst i₀ (commonSourcePolynomial f) ∈ X.ideal
        rw [cylSubst_rename]
        exact hf
      | inr h =>
        have hgg : g = MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1 :=
          Set.mem_singleton_iff.mp h
        rw [hgg]
        show cylSubst i₀ _ ∈ X.ideal
        have e1 : cylSubst i₀ (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)))
            = 1 := by
          rw [cylSubst_inr, if_pos rfl]
          exact map_one _
        rw [map_sub, e1, map_one, sub_self]
        exact Ideal.zero_mem _
    | inr h =>
      obtain ⟨s, hs, rfl⟩ := h
      show cylSubst i₀ _ ∈ X.ideal
      have e0 : cylSubst i₀ (MvPolynomial.X (finSumFinEquiv (Sum.inr s.val)))
          = 0 := by
        rw [cylSubst_inr, if_neg s.property]
        exact map_zero _
      rw [e0]
      exact Ideal.zero_mem _
  have hle : (cylVar i₀ X Finset.univ).ideal ≤ Ideal.comap (cylSubst i₀) X.ideal := by
    intro g hg
    have hrad : g ∈ (cylIdeal i₀ X Finset.univ).radical := by
      have e : (cylVar i₀ X Finset.univ).ideal
          = (cylIdeal i₀ X Finset.univ).radical := rfl
      rw [e] at hg
      exact hg
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
    have hmem : (cylSubst i₀ g) ^ n ∈ X.ideal := by
      have h2 : cylSubst i₀ (g ^ n) ∈ X.ideal := hgen hn
      rwa [map_pow] at h2
    have hmemr : cylSubst i₀ g ∈ X.ideal.radical :=
      Ideal.mem_radical_iff.mpr ⟨n, hmem⟩
    rwa [X.isRadical.radical] at hmemr
  exact Ideal.quotientMapₐ _ _ hle

/-- Computation of the forward map on generators. -/
theorem cylFwdQ_mk (i₀ : Fin d) (X : AffineVariety d) (g : Poly (d + d)) :
    cylFwdQ i₀ X (Ideal.Quotient.mkₐ ℂ (cylVar i₀ X Finset.univ).ideal g) =
      Ideal.Quotient.mkₐ ℂ X.ideal (cylSubst i₀ g) := by
  rfl

/-- Forward restriction map (cylinder Hilbert space to source Hilbert space). -/
def cylFwd (i₀ : Fin d) (X : AffineVariety d) (D : ℕ) :
    (cylVar i₀ X Finset.univ).restrictionSpace D →ₗ[ℂ] X.restrictionSpace D where
  toFun y := ⟨cylFwdQ i₀ X y.val, by
    obtain ⟨g, hg, heq⟩ := y.property
    have e1 : cylFwdQ i₀ X y.val
        = Ideal.Quotient.mkₐ ℂ X.ideal (cylSubst i₀ g) := by
      rw [← heq]
      exact cylFwdQ_mk _ _ _
    rw [e1]
    refine ⟨cylSubst i₀ g, ?_, rfl⟩
    simp only [SetLike.mem_coe, OAI.QuarticPowerFree.mem_totalSpace] at hg ⊢
    exact (cylSubst_totalDegree_le _ _).trans hg⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    show cylFwdQ i₀ X (x.val + y.val) = _
    rw [map_add]
    rfl
  map_smul' := by
    intro c x
    apply Subtype.ext
    show cylFwdQ i₀ X (c • x.val) = _
    rw [map_smul]
    rfl

/-- The two restriction maps are mutually inverse (forward after backward). -/
theorem cylFwdBack_id (i₀ : Fin d) (X : AffineVariety d) (D : ℕ)
    (x : X.restrictionSpace D) :
    cylFwd i₀ X D (cylBack i₀ X D x) = x := by
  obtain ⟨f, hf, heq⟩ := x.property
  apply Subtype.ext
  show cylFwdQ i₀ X (cylBackQ i₀ X x.val) = x.val
  have eB : cylBackQ i₀ X x.val = Ideal.Quotient.mkₐ ℂ
      (cylVar i₀ X Finset.univ).ideal
      (MvPolynomial.aeval (fun k => MvPolynomial.X (inlMap d k)) f) := by
    rw [← heq]
    exact cylBackQ_mk _ _ _
  rw [eB, cylFwdQ_mk, aeval_rename_eq]
  show (Ideal.Quotient.mkₐ ℂ X.ideal) (cylSubst i₀ (commonSourcePolynomial f)) = _
  rw [cylSubst_rename]
  exact heq

/-- Quotient classes with difference in the ideal are equal. -/
theorem mkA_eq_of_sub_mem {m : ℕ} (I : Ideal (Poly m)) (a b : Poly m)
    (h : a - b ∈ I) :
    Ideal.Quotient.mkₐ ℂ I a = Ideal.Quotient.mkₐ ℂ I b := by
  have h0 : Ideal.Quotient.mk I (a - b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
  have e : Ideal.Quotient.mkₐ ℂ I a - Ideal.Quotient.mkₐ ℂ I b = 0 := by
    rw [← map_sub]
    exact h0
  exact sub_eq_zero.mp e

/-- The two restriction maps are mutually inverse (backward after forward). -/
theorem cylBackFwd_id (i₀ : Fin d) (X : AffineVariety d) (D : ℕ)
    (y : (cylVar i₀ X Finset.univ).restrictionSpace D) :
    cylBack i₀ X D (cylFwd i₀ X D y) = y := by
  obtain ⟨g, hg, heq⟩ := y.property
  apply Subtype.ext
  show cylBackQ i₀ X (cylFwdQ i₀ X y.val) = y.val
  have eF : cylFwdQ i₀ X y.val
      = Ideal.Quotient.mkₐ ℂ X.ideal (cylSubst i₀ g) := by
    rw [← heq]
    exact cylFwdQ_mk _ _ _
  rw [eF, cylBackQ_mk]
  have hdiff : MvPolynomial.aeval (fun k => MvPolynomial.X (inlMap d k))
      (cylSubst i₀ g) - g ∈ (cylVar i₀ X Finset.univ).ideal := by
    have hle2 : cylIdeal i₀ X Finset.univ ≤ (cylVar i₀ X Finset.univ).ideal := by
      unfold cylVar
      exact Ideal.le_radical
    apply hle2
    have hker : RingHom.ker (cylPhi i₀ X Finset.univ).toRingHom
        = cylIdeal i₀ X Finset.univ := cylKer_eq _ _ _
    have hmem : MvPolynomial.aeval (fun k => MvPolynomial.X (inlMap d k))
        (cylSubst i₀ g) - g ∈ RingHom.ker (cylPhi i₀ X Finset.univ).toRingHom := by
      rw [RingHom.mem_ker, map_sub]
      have e1 : (cylPhi i₀ X Finset.univ).toRingHom
          (MvPolynomial.aeval (fun k => MvPolynomial.X (inlMap d k)) (cylSubst i₀ g))
          = MvPolynomial.C (Ideal.Quotient.mk _ (cylSubst i₀ g)) := by
        rw [aeval_rename_eq]
        exact cylPhi_src _ _ _ _
      rw [e1]
      have e2 : (cylPhi i₀ X Finset.univ).toRingHom g
          = MvPolynomial.C (Ideal.Quotient.mk _ (cylSubst i₀ g)) :=
        cylPhi_univ_eq _ _ _
      rw [e2, sub_self]
    rwa [hker] at hmem
  have hmk := mkA_eq_of_sub_mem _ _ _ hdiff
  rw [hmk]
  exact heq

/-- The base section and the source have the same Hilbert function. -/
theorem cylBase_hilbert_eq (i₀ : Fin d) (X : AffineVariety d) (D : ℕ) :
    X.hilbert D = (cylVar i₀ X Finset.univ).hilbert D := by
  have hBack_inj : Function.Injective ⇑(cylBack i₀ X D) :=
    Function.LeftInverse.injective (fun x => cylFwdBack_id i₀ X D x)
  have hFwd_inj : Function.Injective ⇑(cylFwd i₀ X D) :=
    Function.LeftInverse.injective (fun y => cylBackFwd_id i₀ X D y)
  have h1 := LinearMap.finrank_le_finrank_of_injective hBack_inj
  have h2 := LinearMap.finrank_le_finrank_of_injective hFwd_inj
  show Module.finrank ℂ ↥(X.restrictionSpace D) =
    Module.finrank ℂ ↥((cylVar i₀ X Finset.univ).restrictionSpace D)
  exact le_antisymm h1 h2

/-- Base degree: the fully-fixed section has the source degree. -/
theorem cylBase_degree (i₀ : Fin d) (X : AffineVariety d) (hX : X.IsIrreducible) :
    OAI.QuarticPowerFree.affineDegree (cylIdeal i₀ X Finset.univ) =
      OAI.QuarticPowerFree.affineDegree X.ideal := by
  have hrad := cylVar_ideal_eq i₀ X hX Finset.univ
  have hP : (cylVar i₀ X Finset.univ).hilbertPolynomial = X.hilbertPolynomial := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [X.hilbert_eventually,
      (cylVar i₀ X Finset.univ).hilbert_eventually] with D hXD hCD
    rw [← hXD, ← hCD]
    exact_mod_cast (cylBase_hilbert_eq i₀ X D).symm
  rw [← hrad]
  show (cylVar i₀ X Finset.univ).degree = X.degree
  have hdim : (cylVar i₀ X Finset.univ).dimension = X.dimension := by
    show (cylVar i₀ X Finset.univ).hilbertPolynomial.natDegree
      = X.hilbertPolynomial.natDegree
    rw [hP]
  have hdeg_eq : ∀ {m : ℕ} (V : AffineVariety m), V.degree =
      ((V.dimension.factorial : ℕ) : ℚ) * V.hilbertPolynomial.coeff V.dimension :=
    fun _ => rfl
  rw [hdeg_eq, hdeg_eq, hP, hdim]

/-- Cutting by a free variable: the section ideal contains the cut. -/
theorem cylCut_le (i₀ : Fin d) (X : AffineVariety d) (T : Finset (CylFree d i₀))
    (s : CylFree d i₀) :
    cylIdeal i₀ X T ⊔ Ideal.span {MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))} ≤
      cylIdeal i₀ X (insert s T) := by
  unfold cylIdeal
  refine sup_le ?_ ?_
  · rw [Ideal.span_le]
    intro g hg
    rw [Set.mem_union] at hg
    cases hg with
    | inl h =>
      rw [Set.mem_union] at h
      cases h with
      | inl h => exact Ideal.subset_span (Or.inl (Or.inl h))
      | inr h => exact Ideal.subset_span (Or.inl (Or.inr h))
    | inr h =>
      obtain ⟨t, ht, rfl⟩ := h
      exact Ideal.subset_span (Or.inr ⟨t,
        Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp ht)), rfl⟩)
  · rw [Ideal.span_le]
    intro g hg
    have hgg : g = MvPolynomial.X (finSumFinEquiv (Sum.inr s.val)) :=
      Set.mem_singleton_iff.mp hg
    rw [hgg]
    exact Ideal.subset_span (Or.inr ⟨s,
      Finset.mem_coe.mpr (Finset.mem_insert_self s T), rfl⟩)

/-- A free-variable generator is not in the parametrized cylinder ideal. -/
theorem cylCut_mem_ne (i₀ : Fin d) (X : AffineVariety d) (hX : X.IsIrreducible)
    (T : Finset (CylFree d i₀)) (s : CylFree d i₀) (hs : s ∉ T) :
    MvPolynomial.X (finSumFinEquiv (Sum.inr s.val)) ∉ (cylVar i₀ X T).ideal := by
  haveI : IsDomain (Poly d ⧸ X.ideal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hX
  rw [cylVar_ideal_eq i₀ X hX T]
  intro hcon
  have hker := cylKer_eq i₀ X T
  have hPhi : cylPhi i₀ X T (MvPolynomial.X (finSumFinEquiv (Sum.inr s.val)))
      = MvPolynomial.X ⟨s, hs⟩ := by
    unfold cylPhi
    rw [MvPolynomial.aeval_X]
    exact cylPhiVal_inr_free i₀ X T s hs
  have h0 : cylPhi i₀ X T (MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))) = 0 := by
    have hmem : MvPolynomial.X (finSumFinEquiv (Sum.inr s.val)) ∈
        RingHom.ker (cylPhi i₀ X T).toRingHom := by
      rw [hker]
      exact hcon
    exact RingHom.mem_ker.mp hmem
  rw [hPhi] at h0
  exact MvPolynomial.X_ne_zero _ h0

/-- Fixing one more variable drops the free-variable count by one. -/
theorem cylRem_card_insert (i₀ : Fin d) (T : Finset (CylFree d i₀))
    (s : CylFree d i₀) (hs : s ∉ T) :
    Fintype.card (CylFreeRem d i₀ (insert s T)) + 1
      = Fintype.card (CylFreeRem d i₀ T) := by
  have hle : T.card + 1 ≤ d - 1 := by
    have h1 : (insert s T).card ≤ (Finset.univ : Finset (CylFree d i₀)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_insert_of_notMem hs, Finset.card_univ, card_CylFree] at h1
    exact h1
  rw [card_CylFreeRem, card_CylFreeRem, Finset.card_insert_of_notMem hs]
  omega

/-- One hyperplane section does not increase the degree. -/
theorem cylSection_step_degree_le (i₀ : Fin d) (X : AffineVariety d)
    (hX : X.IsIrreducible) (T : Finset (CylFree d i₀)) (s : CylFree d i₀)
    (hs : s ∉ T) :
    (cylVar i₀ X (insert s T)).degree ≤ (cylVar i₀ X T).degree := by
  classical
  have hPT : (cylVar i₀ X T).ideal = cylIdeal i₀ X T := cylVar_ideal_eq i₀ X hX T
  have hPW : (cylVar i₀ X (insert s T)).ideal = cylIdeal i₀ X (insert s T) :=
    cylVar_ideal_eq i₀ X hX _
  haveI hIprime : (cylIdeal i₀ X T).IsPrime := cylIdeal_prime i₀ X hX T
  haveI hWvprime : (cylVar i₀ X (insert s T)).ideal.IsPrime := hPW ▸
    cylIdeal_prime i₀ X hX (insert s T)
  have hf : MvPolynomial.X (finSumFinEquiv (Sum.inr s.val)) ∉ cylIdeal i₀ X T := by
    have hcon := cylCut_mem_ne i₀ X hX T s hs
    rwa [hPT] at hcon
  have hdimT := cylVar_dimension i₀ X hX T
  have hdimW := cylVar_dimension i₀ X hX (insert s T)
  have hcard := cylRem_card_insert i₀ T s hs
  have hdimEq : (cylVar i₀ X T).dimension
      = (cylVar i₀ X (insert s T)).dimension + 1 := by
    rw [hdimT, hdimW]
    omega
  have hcut_le : cylIdeal i₀ X T ⊔
      Ideal.span {MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))} ≤
      cylIdeal i₀ X (insert s T) := cylCut_le i₀ X T s
  rw [← hPW] at hcut_le
  obtain ⟨Q, hQmin, hQsub⟩ := Ideal.exists_minimalPrimes_le hcut_le
  haveI hQprime : Q.IsPrime := hQmin.isPrime
  have hdT : OAI.QuarticPowerFree.affineDimension (cylIdeal i₀ X T)
      = (cylVar i₀ X (insert s T)).dimension + 1 := by
    rw [← hPT]
    exact hdimEq
  have hQdim : OAI.QuarticPowerFree.affineDimension Q
      = (cylVar i₀ X (insert s T)).dimension :=
    OAI.QuarticPowerFree.proper_cut_component_dimension
      (cylIdeal i₀ X T) Q _ hf hQmin hdT
  have hBez := OAI.QuarticPowerFree.proper_cut_sum_affineDegree_le
    (cylIdeal i₀ X T)
    (MvPolynomial.X (finSumFinEquiv (Sum.inr s.val))) hf hdT
    (fun _ : Unit => Q) (fun _ => hQmin) (fun a b _ => Subsingleton.elim a b)
  have hQle : OAI.QuarticPowerFree.affineDegree Q ≤
      OAI.QuarticPowerFree.affineDegree (cylIdeal i₀ X T) := by
    simpa [MvPolynomial.totalDegree_X] using hBez
  set Z : AffineVariety (d + d) := ⟨Q, hQmin.isPrime.isRadical⟩ with hZdef
  have hdimZ : Z.dimension = (cylVar i₀ X (insert s T)).dimension := hQdim
  have hWZ : (cylVar i₀ X (insert s T)).Subvariety Z := hQsub
  have hhilb : ∀ D, (cylVar i₀ X (insert s T)).hilbert D ≤ Z.hilbert D :=
    fun D => AffineVariety.hilbert_mono _ _ hWZ D
  have hcoeff : (cylVar i₀ X (insert s T)).hilbertPolynomial.coeff
        ((cylVar i₀ X (insert s T)).dimension)
      ≤ Z.hilbertPolynomial.coeff ((cylVar i₀ X (insert s T)).dimension) := by
    refine OAI.QuarticPowerFree.coeff_le_of_eventually_nat_eval_le _ _
      ((cylVar i₀ X (insert s T)).dimension) ?_ ?_ ?_
    · exact le_rfl
    · exact hdimZ.le
    · filter_upwards [(cylVar i₀ X (insert s T)).hilbert_eventually,
        Z.hilbert_eventually] with D hWD hZD
      rw [← hWD, ← hZD]
      exact_mod_cast hhilb D
  have hdegWQ : (cylVar i₀ X (insert s T)).degree ≤ Z.degree := by
    have hdeg_eq : ∀ {m : ℕ} (V : AffineVariety m), V.degree =
        ((V.dimension.factorial : ℕ) : ℚ) * V.hilbertPolynomial.coeff V.dimension :=
      fun _ => rfl
    have hmul := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _ :
      (0 : ℚ) ≤ ((((cylVar i₀ X (insert s T)).dimension.factorial : ℕ)) : ℚ))
    rw [hdeg_eq, hdeg_eq, hdimZ]
    exact hmul
  calc (cylVar i₀ X (insert s T)).degree ≤ Z.degree := hdegWQ
    _ = OAI.QuarticPowerFree.affineDegree Q := rfl
    _ ≤ OAI.QuarticPowerFree.affineDegree (cylIdeal i₀ X T) := hQle
    _ = (cylVar i₀ X T).degree := by rw [← hPT]

/-- Chaining sections from the full cylinder down to the base. -/
theorem cylChain_degree_le (i₀ : Fin d) (X : AffineVariety d)
    (hX : X.IsIrreducible) :
    (cylVar i₀ X Finset.univ).degree ≤ (cylVar i₀ X ∅).degree := by
  classical
  have key : ∀ (S : Finset (CylFree d i₀)) (T : Finset (CylFree d i₀)),
      T ⊆ Finset.univ → Finset.univ \ T = S →
      (cylVar i₀ X Finset.univ).degree ≤ (cylVar i₀ X T).degree := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro T hT hS
      have hTeq : T = Finset.univ := by
        have h1 : Finset.univ ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp hS
        exact Finset.Subset.antisymm hT h1
      rw [hTeq]
    | insert a S ha ih =>
      intro T hT hS
      have haU : a ∈ (Finset.univ : Finset (CylFree d i₀)) :=
        (Finset.mem_sdiff.mp (by rw [hS]; exact Finset.mem_insert_self a S)).1
      have haT : a ∉ T := by
        intro hcon
        have h1 : a ∉ Finset.univ \ T :=
          fun hmem => (Finset.mem_sdiff.mp hmem).2 hcon
        rw [hS] at h1
        exact h1 (Finset.mem_insert_self a S)
      have hT'sub : insert a T ⊆ Finset.univ := Finset.insert_subset haU hT
      have hS' : Finset.univ \ insert a T = S := by
        ext y
        constructor
        · intro hy
          have hyU : y ∈ Finset.univ := (Finset.mem_sdiff.mp hy).1
          have hyT : y ∉ insert a T := (Finset.mem_sdiff.mp hy).2
          have hyT' : y ∈ Finset.univ \ T := Finset.mem_sdiff.mpr ⟨hyU,
            fun h => hyT (Finset.mem_insert_of_mem h)⟩
          rw [hS] at hyT'
          have hyne : y ≠ a := by
            intro heq
            apply hyT
            rw [heq]
            exact Finset.mem_insert_self a T
          obtain heq | hmem := Finset.mem_insert.mp hyT'
          · exact absurd heq hyne
          · exact hmem
        · intro hyS
          have hyU : y ∈ Finset.univ := Finset.mem_univ y
          have hyT : y ∉ T := by
            intro hcon
            have h1 : y ∉ Finset.univ \ T :=
              fun hmem => (Finset.mem_sdiff.mp hmem).2 hcon
            rw [hS] at h1
            exact h1 (Finset.mem_insert_of_mem hyS)
          have hyT' : y ∉ insert a T := by
            intro hmem
            obtain rfl | hmemT := Finset.mem_insert.mp hmem
            · exact ha hyS
            · exact hyT hmemT
          exact Finset.mem_sdiff.mpr ⟨hyU, hyT'⟩
      have hIH := ih (insert a T) hT'sub hS'
      have hstep := cylSection_step_degree_le i₀ X hX T a haT
      exact hIH.trans hstep
  have hS : Finset.univ \ (∅ : Finset (CylFree d i₀)) = Finset.univ :=
    Finset.sdiff_empty
  exact key _ _ (Finset.subset_univ _) hS
