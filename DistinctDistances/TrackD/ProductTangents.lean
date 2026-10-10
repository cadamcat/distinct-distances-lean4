import DistinctDistances.TrackD.ProductGeometry
import DistinctDistances.TrackD.GenericTangent

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

def productLinearEquiv : (Point d × Point d) ≃ₗ[ℂ] Point (d + d) where
  toFun p := productPoint p.1 p.2
  invFun p := (productLeft p, productRight p)
  left_inv p := by
    apply Prod.ext
    · funext i
      change pairPt p.1 p.2 (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = p.1 i
      rw [Equiv.symm_apply_apply]
      rfl
    · funext i
      change pairPt p.1 p.2 (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) = p.2 i
      rw [Equiv.symm_apply_apply]
      rfl
  right_inv := productPoint_left_right
  map_add' p q := by
    funext i
    change Sum.elim (p.1 + q.1) (p.2 + q.2) (finSumFinEquiv.symm i) =
      Sum.elim p.1 p.2 (finSumFinEquiv.symm i) + Sum.elim q.1 q.2 (finSumFinEquiv.symm i)
    cases finSumFinEquiv.symm i <;> rfl
  map_smul' c p := by
    funext i
    change Sum.elim (c • p.1) (c • p.2) (finSumFinEquiv.symm i) =
      c * Sum.elim p.1 p.2 (finSumFinEquiv.symm i)
    cases finSumFinEquiv.symm i <;> rfl

theorem pairFixRight_pderiv (f : PairPoly d) (y : Point d) (i : Fin d) :
    MvPolynomial.pderiv i (pairFixRight f y) =
      pairFixRight (MvPolynomial.pderiv (Sum.inl i) f) y := by
  exact (MvPolynomial.aeval_sumElim_pderiv_inl f y i).symm

theorem pairFixLeft_pderiv (f : PairPoly d) (x : Point d) (i : Fin d) :
    MvPolynomial.pderiv i (pairFixLeft f x) =
      pairFixLeft (MvPolynomial.pderiv (Sum.inr i) f) x := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [pairFixLeft]
  | add f g hf hg => simp_all [pairFixLeft]
  | mul_X f j hf =>
    simp only [pairFixLeft, map_mul, MvPolynomial.aeval_X, Derivation.leibniz,
      MvPolynomial.pderiv_X, map_add, smul_eq_mul] at *
    cases j <;> simp_all [Pi.single_apply]

@[simp] theorem pairFixRight_rename_inl (f : Poly d) (y : Point d) :
    pairFixRight (MvPolynomial.rename Sum.inl f) y = f := by
  simp only [pairFixRight, MvPolynomial.aeval_rename, Function.comp_def, Sum.elim_inl]
  simp

@[simp] theorem pairFixLeft_rename_inr (f : Poly d) (x : Point d) :
    pairFixLeft (MvPolynomial.rename Sum.inr f) x = f := by
  simp only [pairFixLeft, MvPolynomial.aeval_rename, Function.comp_def, Sum.elim_inr]
  simp

@[simp] theorem pairFixLeft_rename_inl (f : Poly d) (x : Point d) :
    pairFixLeft (MvPolynomial.rename Sum.inl f) x = MvPolynomial.C (MvPolynomial.eval x f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [pairFixLeft]
  | add f g hf hg => simp_all [pairFixLeft]
  | mul_X f i hf => simp_all [pairFixLeft]

@[simp] theorem pairFixRight_rename_inr (f : Poly d) (y : Point d) :
    pairFixRight (MvPolynomial.rename Sum.inr f) y = MvPolynomial.C (MvPolynomial.eval y f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [pairFixRight]
  | add f g hf hg => simp_all [pairFixRight]
  | mul_X f i hf => simp_all [pairFixRight]

@[simp] theorem differential_C (c : ℂ) (x : Point d) : differential (MvPolynomial.C c) x = 0 := by
  ext v
  simp [differential]

/-- Polynomial differentiation on the product splits into its two partial
restrictions. This holds at every point, without a smoothness hypothesis. -/
theorem differential_product (f : Poly (d + d)) (x y v w : Point d) :
    differential f (productPoint x y) (productPoint v w) =
      differential (pairFixRight (MvPolynomial.rename finSumFinEquiv.symm f) y) x v +
      differential (pairFixLeft (MvPolynomial.rename finSumFinEquiv.symm f) x) y w := by
  let F : PairPoly d := MvPolynomial.rename finSumFinEquiv.symm f
  have hderiv (j : Fin d ⊕ Fin d) :
      MvPolynomial.eval (pairPt x y) (MvPolynomial.pderiv j F) =
        MvPolynomial.eval (productPoint x y)
          (MvPolynomial.pderiv (finSumFinEquiv j) f) := by
    have hp := MvPolynomial.pderiv_rename finSumFinEquiv.symm.injective
      (finSumFinEquiv j) f
    simpa only [Equiv.symm_apply_apply, F, eval_product_rename] using
      congrArg (MvPolynomial.eval (pairPt x y)) hp
  have hleft (i : Fin d) :
      MvPolynomial.eval x (MvPolynomial.pderiv i (pairFixRight F y)) =
        MvPolynomial.eval (productPoint x y)
          (MvPolynomial.pderiv (finSumFinEquiv (Sum.inl i)) f) := by
    rw [pairFixRight_pderiv, eval_pairFixRight]
    exact hderiv (Sum.inl i)
  have hright (i : Fin d) :
      MvPolynomial.eval y (MvPolynomial.pderiv i (pairFixLeft F x)) =
        MvPolynomial.eval (productPoint x y)
          (MvPolynomial.pderiv (finSumFinEquiv (Sum.inr i)) f) := by
    rw [pairFixLeft_pderiv, eval_pairFixLeft]
    exact hderiv (Sum.inr i)
  change differential f (productPoint x y) (productPoint v w) =
    differential (pairFixRight F y) x v + differential (pairFixLeft F x) y w
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  change (∑ i : Fin (d + d), MvPolynomial.eval (productPoint x y)
      (MvPolynomial.pderiv i f) * productPoint v w i) =
    (∑ i : Fin d, MvPolynomial.eval x (MvPolynomial.pderiv i (pairFixRight F y)) * v i) +
      ∑ i : Fin d, MvPolynomial.eval y (MvPolynomial.pderiv i (pairFixLeft F x)) * w i
  simp_rw [hleft, hright]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fintype.sum_sum_type, productPoint, Function.comp_apply,
    Equiv.symm_apply_apply, pairPt, Sum.elim_inl, Sum.elim_inr]

theorem product_tangent_space (X Y : AffineVariety d) (x y : Point d)
    (hx : x ∈ X) (hy : y ∈ Y) :
    ((X.tangentSpace x).prod (Y.tangentSpace y)).map productLinearEquiv.toLinearMap =
      (productVariety X Y).tangentSpace (productPoint x y) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨⟨v, w⟩, hmem, rfl⟩ := Submodule.mem_map.mp hp
    rcases hmem with ⟨hv, hw⟩
    simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    intro f
    have hf (a : Point d) (ha : a ∈ X) (b : Point d) (hb : b ∈ Y) :
        MvPolynomial.eval (productPoint a b) f.val = 0 :=
      f.property (productPoint a b) ⟨a, ha, b, hb, rfl⟩
    have hleft : pairFixRight (MvPolynomial.rename finSumFinEquiv.symm f.val) y ∈ X.ideal :=
      (mem_ideal_iff_eval_zero X _).mpr (by
        intro a ha
        simpa using hf a ha y hy)
    have hright : pairFixLeft (MvPolynomial.rename finSumFinEquiv.symm f.val) x ∈ Y.ideal :=
      (mem_ideal_iff_eval_zero Y _).mpr (by
        intro b hb
        simpa using hf x hx b hb)
    have hv0 : differential (pairFixRight (MvPolynomial.rename finSumFinEquiv.symm f.val) y) x v = 0 :=
      (Submodule.mem_iInf _).mp hv ⟨_, hleft⟩
    have hw0 : differential (pairFixLeft (MvPolynomial.rename finSumFinEquiv.symm f.val) x) y w = 0 :=
      (Submodule.mem_iInf _).mp hw ⟨_, hright⟩
    change differential f.val (productPoint x y) (productPoint v w) = 0
    rw [differential_product]
    rw [hv0, hw0, add_zero]
  · intro p hp
    let v := productLeft p
    let w := productRight p
    have hpvw : productPoint v w = p := productPoint_left_right p
    refine Submodule.mem_map.mpr ⟨(v, w), ?_, ?_⟩
    · change v ∈ X.tangentSpace x ∧ w ∈ Y.tangentSpace y
      constructor
      · simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker]
        intro f
        let F : Poly (d + d) := MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) f.val
        have hF : F ∈ (productVariety X Y).ideal := by
          intro q hq
          obtain ⟨a, ha, b, hb, rfl⟩ := hq
          change MvPolynomial.eval (productPoint a b)
            (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) f.val) = 0
          rw [eval_product_left_rename]
          exact ha f.val f.property
        have hh := (Submodule.mem_iInf _).mp hp ⟨F, hF⟩
        change differential F (productPoint x y) p = 0 at hh
        rw [← hpvw, differential_product] at hh
        have hrename : MvPolynomial.rename finSumFinEquiv.symm F = MvPolynomial.rename Sum.inl f.val := by
          have hfun : finSumFinEquiv.symm ∘ (fun i : Fin d => finSumFinEquiv (Sum.inl i)) =
              (Sum.inl : Fin d → Fin d ⊕ Fin d) := by
            funext i
            exact Equiv.symm_apply_apply finSumFinEquiv (Sum.inl i)
          dsimp only [F]
          rw [MvPolynomial.rename_rename, hfun]
        rw [hrename, pairFixRight_rename_inl, pairFixLeft_rename_inl,
          differential_C, LinearMap.zero_apply, add_zero] at hh
        exact hh
      · simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker]
        intro f
        let F : Poly (d + d) := MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inr i)) f.val
        have hF : F ∈ (productVariety X Y).ideal := by
          intro q hq
          obtain ⟨a, ha, b, hb, rfl⟩ := hq
          change MvPolynomial.eval (productPoint a b)
            (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inr i)) f.val) = 0
          rw [eval_product_right_rename]
          exact hb f.val f.property
        have hh := (Submodule.mem_iInf _).mp hp ⟨F, hF⟩
        change differential F (productPoint x y) p = 0 at hh
        rw [← hpvw, differential_product] at hh
        have hrename : MvPolynomial.rename finSumFinEquiv.symm F = MvPolynomial.rename Sum.inr f.val := by
          have hfun : finSumFinEquiv.symm ∘ (fun i : Fin d => finSumFinEquiv (Sum.inr i)) =
              (Sum.inr : Fin d → Fin d ⊕ Fin d) := by
            funext i
            exact Equiv.symm_apply_apply finSumFinEquiv (Sum.inr i)
          dsimp only [F]
          rw [MvPolynomial.rename_rename, hfun]
        rw [hrename, pairFixRight_rename_inr, pairFixLeft_rename_inr,
          differential_C, LinearMap.zero_apply, zero_add] at hh
        exact hh
    · exact hpvw

def prodSubmoduleEquiv (U V : Submodule ℂ (Point d)) : U.prod V ≃ₗ[ℂ] U × V where
  toFun p := (⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2⟩)
  invFun p := ⟨(p.1.val, p.2.val), p.1.property, p.2.property⟩
  left_inv p := by rfl
  right_inv p := by rfl
  map_add' p q := by rfl
  map_smul' c p := by rfl

theorem product_tangent_finrank (X Y : AffineVariety d) (x y : Point d)
    (hx : x ∈ X) (hy : y ∈ Y) :
    Module.finrank ℂ ((productVariety X Y).tangentSpace (productPoint x y)) =
      Module.finrank ℂ (X.tangentSpace x) + Module.finrank ℂ (Y.tangentSpace y) := by
  rw [← product_tangent_space X Y x y hx hy, LinearEquiv.finrank_map_eq]
  exact (prodSubmoduleEquiv (X.tangentSpace x) (Y.tangentSpace y)).finrank_eq.trans
    Module.finrank_prod

theorem ForGeneralPoint.on_product {X Y : AffineVariety d}
    {Q : Point (d + d) → Prop} (h : ForGeneralPoint (productVariety X Y) Q) :
    ForGeneralPair X Y (fun x y => Q (productPoint x y)) := by
  obtain ⟨g, ⟨p, hp, hgp⟩, hQ⟩ := h
  have hp' : productLeft p ∈ X ∧ productRight p ∈ Y := by
    change p ∈ (productVariety X Y).points at hp
    rw [productVariety_points] at hp
    exact hp
  refine ⟨MvPolynomial.rename finSumFinEquiv.symm g,
    ⟨productLeft p, hp'.1, productRight p, hp'.2, ?_⟩, ?_⟩
  · simpa only [eval_product_rename, productPoint_left_right] using hgp
  · intro x hx y hy hn
    apply hQ (productPoint x y)
    · exact AffineVariety.subset_closure _ ⟨x, hx, y, hy, rfl⟩
    · simpa only [eval_product_rename] using hn

/-- Product dimension from the shared generic-tangent theorem and the exact
product tangent calculation; no separate dimension model is introduced. -/
theorem product_dimension (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible) :
    (productVariety X Y).dimension = X.dimension + Y.dimension := by
  have hdx := (general_tangent_finrank X hX).on_left (irreducible_points_nonempty Y hY)
  have hdy := (general_tangent_finrank Y hY).on_right (irreducible_points_nonempty X hX)
  have hdprod := (general_tangent_finrank (productVariety X Y)
    (productVariety_irreducible X Y hX hY)).on_product
  obtain ⟨x, hx, y, hy, ⟨hdx, hdy⟩, hdprod⟩ := ((hdx.and hX hY hdy).and hX hY hdprod).exists
  rw [← hdprod, product_tangent_finrank X Y x y hx hy, hdx, hdy]

end
end DistinctDistances.TrackD
