import DistinctDistances.TrackD.RationalFieldEmbedding
import DistinctDistances.TrackD.TangentRankSpecialization

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

private def quotientNumeratorJacobian {n m : ℕ}
    (f : Fin m → Poly n) (g : Poly n) : Matrix (Fin m) (Fin n) (Poly n) :=
  Matrix.of fun i j => g * MvPolynomial.pderiv j (f i) -
    f i * MvPolynomial.pderiv j g

private def rowStack {r m n : ℕ} {R : Type*}
    (A : Matrix (Fin r) (Fin n) R) (B : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin (r + m)) (Fin n) R :=
  (Matrix.of fun i j =>
    Sum.elim (fun k => A k j) (fun k => B k j) i).reindex
      finSumFinEquiv (Equiv.refl (Fin n))

private def sumPiEquiv {r m : ℕ} (K : Type*) [Semiring K] :
    (Fin r ⊕ Fin m → K) ≃ₗ[K] ((Fin r → K) × (Fin m → K)) where
  toFun v := (v ∘ Sum.inl, v ∘ Sum.inr)
  invFun v := Sum.elim v.1 v.2
  left_inv v := by
    funext i
    cases i <;> rfl
  right_inv v := by
    rcases v with ⟨v, w⟩
    rfl
  map_add' v w := by
    ext i <;> rfl
  map_smul' c v := by
    ext i <;> rfl

private theorem rowStack_map {n r m : ℕ} {R S : Type*}
    [NonAssocSemiring R] [NonAssocSemiring S] (ψ : R →+* S)
    (A : Matrix (Fin r) (Fin n) R) (B : Matrix (Fin m) (Fin n) R) :
    (rowStack A B).map ψ = rowStack (A.map ψ) (B.map ψ) := by
  ext i j
  cases h : finSumFinEquiv.symm i <;>
    simp [rowStack, h, Matrix.reindex_apply, Matrix.map_apply]

private theorem rowStack_rank {K : Type*} [Field K] {n r m : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (B : Matrix (Fin m) (Fin n) K) :
    (rowStack A B).rank = Module.finrank K
      (LinearMap.range (A.mulVecLin.prod B.mulVecLin)) := by
  let S0 : Matrix (Fin r ⊕ Fin m) (Fin n) K :=
    Matrix.of fun i j => Sum.elim (fun k => A k j) (fun k => B k j) i
  let e := sumPiEquiv (r := r) (m := m) K
  have hrow : rowStack A B = S0.reindex finSumFinEquiv (Equiv.refl (Fin n)) := rfl
  have hcomp : e.toLinearMap.comp S0.mulVecLin = A.mulVecLin.prod B.mulVecLin := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · funext i
      simp [S0, e, sumPiEquiv, Matrix.of_apply, Matrix.mulVec, dotProduct]
    · funext i
      simp [S0, e, sumPiEquiv, Matrix.of_apply, Matrix.mulVec, dotProduct]
  have hrange : LinearMap.range (A.mulVecLin.prod B.mulVecLin) =
      (LinearMap.range S0.mulVecLin).map e.toLinearMap := by
    rw [← hcomp, LinearMap.range_comp]
  calc
    (rowStack A B).rank = S0.rank := by rw [hrow, Matrix.rank_reindex]
    _ = Module.finrank K (LinearMap.range S0.mulVecLin) := rfl
    _ = Module.finrank K (LinearMap.range (A.mulVecLin.prod B.mulVecLin)) := by
      rw [hrange]
      exact (Submodule.equivMapOfInjective e.toLinearMap e.injective _).finrank_eq

private theorem finrank_map_smul_ne_zero {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : Submodule K V) (L : V →ₗ[K] W) (c : K) (hc : c ≠ 0) :
    Module.finrank K (S.map (c • L)) = Module.finrank K (S.map L) := by
  have heq : S.map (c • L) = S.map L := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨c • v, S.smul_mem _ hv, ?_⟩
      simp [smul_smul, hc]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨c⁻¹ • v, S.smul_mem _ hv, ?_⟩
      simp [smul_smul, hc]
  rw [heq]

private theorem fieldRationalDifferential_eq_quotientNumerator {n m : ℕ}
    (K : Type*) [Field K] [Algebra ℂ K] (φ : Poly n →ₐ[ℂ] K)
    (f : Fin m → Poly n) (g : Poly n) (hg : φ g ≠ 0) :
    fieldRationalDifferential K φ f g =
      (φ g)⁻¹ ^ 2 • ((quotientNumeratorJacobian f g).map φ).mulVecLin := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [fieldRationalDifferential, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]
  change (φ g)⁻¹ *
      (∑ j : Fin n, φ (MvPolynomial.pderiv j (f i)) * v j) -
    (φ (f i) / (φ g) ^ 2) *
      (∑ j : Fin n, φ (MvPolynomial.pderiv j g) * v j) =
    (φ g)⁻¹ ^ 2 *
      (∑ j : Fin n, φ (g * MvPolynomial.pderiv j (f i) -
        f i * MvPolynomial.pderiv j g) * v j)
  have hsum :
      (∑ j : Fin n, (φ g * φ (MvPolynomial.pderiv j (f i)) -
        φ (f i) * φ (MvPolynomial.pderiv j g)) * v j) =
        φ g * (∑ j : Fin n, φ (MvPolynomial.pderiv j (f i)) * v j) -
          φ (f i) * (∑ j : Fin n, φ (MvPolynomial.pderiv j g) * v j) := by
    calc
      _ = ∑ j : Fin n,
          (φ g * φ (MvPolynomial.pderiv j (f i)) * v j -
            φ (f i) * φ (MvPolynomial.pderiv j g) * v j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = (∑ j : Fin n, φ g * φ (MvPolynomial.pderiv j (f i)) * v j) -
          ∑ j : Fin n, φ (f i) * φ (MvPolynomial.pderiv j g) * v j := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ j : Fin n, φ g * (φ (MvPolynomial.pderiv j (f i)) * v j)) -
          ∑ j : Fin n, φ (f i) * (φ (MvPolynomial.pderiv j g) * v j) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro j hj
            ring
          · apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = φ g * (∑ j : Fin n, φ (MvPolynomial.pderiv j (f i)) * v j) -
          φ (f i) * (∑ j : Fin n, φ (MvPolynomial.pderiv j g) * v j) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  have hnum : ∑ j : Fin n,
      φ (g * MvPolynomial.pderiv j (f i) - f i * MvPolynomial.pderiv j g) * v j =
        ∑ j : Fin n, (φ g * φ (MvPolynomial.pderiv j (f i)) -
          φ (f i) * φ (MvPolynomial.pderiv j g)) * v j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [map_sub, map_mul]
  rw [hnum, hsum]
  field_simp [hg]

private theorem rationalDifferential_eq_fieldRationalDifferential {n m : ℕ}
    (f : Fin m → Poly n) (g : Poly n) (x : Point n) :
    rationalDifferential f g x =
      fieldRationalDifferential ℂ (MvPolynomial.aeval x) f g := by
  ext v i
  simp [rationalDifferential, fieldRationalDifferential, differential,
    LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]

private def tangentRankPadding {R : Type*} [Zero R] {r c : ℕ}
    (M : Matrix (Fin r) (Fin c) R) :
    Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) R :=
  Matrix.fromBlocks 0 M 0 0

private theorem tangentRankPadding_map {R S : Type*} [NonAssocSemiring R]
    [NonAssocSemiring S] {r c : ℕ} (ψ : R →+* S)
    (M : Matrix (Fin r) (Fin c) R) :
    (tangentRankPadding M).map ψ = tangentRankPadding (M.map ψ) := by
  ext i j
  cases i <;> cases j <;> simp [tangentRankPadding, Matrix.fromBlocks]

private def tangentRankPaddingColumnMap {K : Type*} [Semiring K] {r c : ℕ} :
    (Fin r → K) →ₗ[K] (Fin r ⊕ Fin c → K) where
  toFun v := Sum.elim v (fun _ => 0)
  map_add' v w := by funext i; cases i <;> simp
  map_smul' a v := by funext i; cases i <;> simp

private theorem tangentRankPadding_rank {K : Type*} [Field K] {r c : ℕ}
    (M : Matrix (Fin r) (Fin c) K) : (tangentRankPadding M).rank = M.rank := by
  let e := tangentRankPaddingColumnMap (K := K) (r := r) (c := c)
  have he : Function.Injective e := by
    intro v w h
    funext i
    exact congrFun h (Sum.inl i)
  have hcols (j : Fin c) : (tangentRankPadding M).col (Sum.inr j) = e (M.col j) := by
    funext i
    cases i <;> simp [e, tangentRankPadding, tangentRankPaddingColumnMap,
      Matrix.fromBlocks]
  have hzero (j : Fin r) : (tangentRankPadding M).col (Sum.inl j) = 0 := by
    funext i
    cases i <;> simp [tangentRankPadding, Matrix.fromBlocks]
  have hspan :
      Submodule.span K (Set.range (tangentRankPadding M).col) =
        (Submodule.span K (Set.range M.col)).map e := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro v ⟨i, rfl⟩
      cases i with
      | inl i => rw [hzero]; exact Submodule.zero_mem _
      | inr i => rw [hcols]; exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.map_span]
      apply Submodule.span_le.2
      rintro v ⟨w, hw, rfl⟩
      rcases hw with ⟨j, rfl⟩
      rw [← hcols j]
      exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  calc
    (tangentRankPadding M).rank =
        Module.finrank K (Submodule.span K (Set.range (tangentRankPadding M).col)) :=
      Matrix.rank_eq_finrank_span_cols _
    _ = Module.finrank K ((Submodule.span K (Set.range M.col)).map e) := by rw [hspan]
    _ = Module.finrank K (Submodule.span K (Set.range M.col)) :=
      (Submodule.equivMapOfInjective e he _).finrank_eq.symm
    _ = M.rank := (Matrix.rank_eq_finrank_span_cols M).symm

private theorem tangentRankNormalBlock {K : Type*} [Field K] (k l : ℕ) :
    (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) K)
      0 0 (0 : Matrix (Fin l) (Fin l) K)).rank = k := by
  let B : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) K :=
    Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) K) 0 0 0
  have hlower : k ≤ B.rank := by
    have hsub : B.submatrix Sum.inl Sum.inl = 1 := by
      ext i j
      simp [B]
    calc
      k = (1 : Matrix (Fin k) (Fin k) K).rank := by simp
      _ = (B.submatrix Sum.inl Sum.inl).rank := by rw [hsub]
      _ ≤ B.rank := Matrix.rank_submatrix_le B Sum.inl Sum.inl
  have hrows : Function.support B.row ⊆
      ((Finset.univ.image Sum.inl : Finset (Fin k ⊕ Fin l)) : Set (Fin k ⊕ Fin l)) := by
    intro i hi
    simp only [Function.mem_support] at hi
    cases i with
    | inl i => exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    | inr i =>
      exfalso
      apply hi
      funext j
      cases j <;> simp [B, Matrix.fromBlocks]
  have hupper : B.rank ≤ k := by
    calc
      B.rank ≤ (Finset.univ.image Sum.inl).card := Matrix.rank_le_card_of_support_subset B _ hrows
      _ = k := by rw [Finset.card_image_of_injective _ Sum.inl_injective]; simp
  exact Nat.le_antisymm hupper hlower

/-- Matrix rank is preserved by an injective homomorphism of fields. -/
private theorem tangent_matrix_rank_map {E K : Type*} [Field E] [Field K]
    (η : E →+* K) (hη : Function.Injective η) {r c : ℕ}
    (M : Matrix (Fin r) (Fin c) E) : (M.map η).rank = M.rank := by
  let P := tangentRankPadding M
  let ι := Fin r ⊕ Fin c
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form P
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have hVdetMap : η V.det = (V.map η).det := RingHom.map_det η V
  have hUdetMap : η U.det = (U.map η).det := RingHom.map_det η U
  have hVmap : IsUnit (V.map η).det := hVdetMap ▸ hVdet.map η
  have hUmap : IsUnit (U.map η).det := hUdetMap ▸ hUdet.map η
  have hnormalMap : (V.map η) * (P.map η) * (U.map η) =
      (Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) K)
        0 0 (0 : Matrix (Fin (Fintype.card ι - P.rank))
          (Fin (Fintype.card ι - P.rank)) K)).submatrix e e := by
    have h := congrArg (fun A : Matrix ι ι E => A.map η) hnormal
    have hblock : ((Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) E)
        0 0 (0 : Matrix (Fin (Fintype.card ι - P.rank))
          (Fin (Fintype.card ι - P.rank)) E)).submatrix e e).map η =
        (Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) K)
          0 0 (0 : Matrix (Fin (Fintype.card ι - P.rank))
            (Fin (Fintype.card ι - P.rank)) K)).submatrix e e := by
      ext i j
      cases hi : e i <;> cases hj : e j <;>
        simp [Matrix.map_apply, Matrix.submatrix_apply, Matrix.fromBlocks,
          Matrix.one_apply, hi, hj]
    calc
      _ = ((Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) E)
          0 0 (0 : Matrix (Fin (Fintype.card ι - P.rank))
            (Fin (Fintype.card ι - P.rank)) E)).submatrix e e).map η := by
            simpa only [Matrix.map_mul] using h
      _ = _ := hblock
  have hpad : (P.map η).rank = P.rank := by
    have hpres : ((V.map η) * (P.map η) * (U.map η)).rank = (P.map η).rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det (U.map η)
        ((V.map η) * (P.map η)) hUmap]
      exact Matrix.rank_mul_eq_right_of_isUnit_det (V.map η) (P.map η) hVmap
    calc
      (P.map η).rank =
          ((Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) K)
            0 0 (0 : Matrix (Fin (Fintype.card ι - P.rank))
              (Fin (Fintype.card ι - P.rank)) K)).submatrix e e).rank := by
              calc
                _ = ((V.map η) * (P.map η) * (U.map η)).rank := hpres.symm
                _ = _ := by rw [hnormalMap]
      _ = P.rank := by
        rw [Matrix.rank_submatrix]
        exact tangentRankNormalBlock _ _
  have hpadE : P.rank = M.rank := tangentRankPadding_rank M
  have hpaddingMap : P.map η = tangentRankPadding (M.map η) :=
    tangentRankPadding_map η M
  have hpadK : (P.map η).rank = (M.map η).rank := by
    rw [hpaddingMap]
    exact tangentRankPadding_rank (M.map η)
  exact hpadK.symm.trans (hpad.trans hpadE)

/-- `secants.tex:63–81`: the target tangent equations pulled into the source
function field have dimension equal to the actual image dimension.
Implementation package: finite equations, generic matrix rank, and extension
of scalars between the two genuine coordinate function fields. -/
theorem rational_image_field_tangent_finrank {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (f : Fin m → Poly n) (g : Poly n) (hg : g ∉ X.ideal)
    (K : Type*) [Field K] [Algebra ℂ K]
    [Algebra (Poly n ⧸ X.ideal) K] [IsScalarTower ℂ (Poly n ⧸ X.ideal) K]
    [IsFractionRing (Poly n ⧸ X.ideal) K] :
    Module.finrank K (fieldTangent (rationalImage X f g).ideal K
      (rationalFieldPullback K (coordinateFieldMap X.ideal K) f g)) =
        (rationalImage X f g).dimension := by
  let Y := rationalImage X f g
  letI : Y.ideal.IsPrime := rational_image_irreducible X hX f g hg
  let E := FractionRing (Poly m ⧸ Y.ideal)
  have hη := rational_function_field_embedding X hX f g hg E K
  obtain ⟨η, hη⟩ := hη
  let φE : Poly m →ₐ[ℂ] E := coordinateFieldMap Y.ideal E
  let φK : Poly m →ₐ[ℂ] K := rationalFieldPullback K
    (coordinateFieldMap X.ideal K) f g
  have hcomp : η.comp φE = φK := by
    apply AlgHom.ext
    intro q
    exact hη q
  obtain ⟨F, hF⟩ := Y.ideal.fg_of_isNoetherianRing
  let eF : F ≃ Fin F.card := Fintype.equivFinOfCardEq (by simp)
  let p : Fin F.card → Poly m := fun i => (eF.symm i).val
  have hrange : Set.range p = (F : Set (Poly m)) := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact (eF.symm i).property
    · intro hq
      refine ⟨eF ⟨q, hq⟩, ?_⟩
      simp [p]
  have hp : Ideal.span (Set.range p) = Y.ideal := by rw [hrange, hF]
  let A : Matrix (Fin F.card) (Fin m) (Poly m) := idealJacobian p
  let AE := A.map φE
  let AK := A.map φK
  have hφEK : ∀ q ∈ Y.ideal, φE q = 0 := by
    intro q hq
    have hker : RingHom.ker φE = Y.ideal := coordinateFieldMap_kernel Y.ideal E
    have hqker : q ∈ RingHom.ker φE := by rw [hker]; exact hq
    exact RingHom.mem_ker.mp hqker
  have hφKK : ∀ q ∈ Y.ideal, φK q = 0 := by
    intro q hq
    have hker : RingHom.ker φK = Y.ideal :=
      rationalFieldPullback_kernel X hX K f g hg
    have hqker : q ∈ RingHom.ker φK := by rw [hker]; exact hq
    exact RingHom.mem_ker.mp hqker
  have hkerE : LinearMap.ker (AE.mulVecLin) = fieldTangent Y.ideal E φE :=
    idealJacobian_kernel Y.ideal p hp E φE hφEK
  have hkerK : LinearMap.ker (AK.mulVecLin) = fieldTangent Y.ideal K φK :=
    idealJacobian_kernel Y.ideal p hp K φK hφKK
  have hmap : AK = AE.map η.toRingHom := by
    ext i j
    have hentry := congrArg
      (fun ψ : Poly m →ₐ[ℂ] K => ψ (MvPolynomial.pderiv j (p i))) hcomp
    change φK (MvPolynomial.pderiv j (p i)) =
      η (φE (MvPolynomial.pderiv j (p i)))
    exact hentry.symm
  have hrankExt : AK.rank = AE.rank := by
    rw [hmap]
    exact tangent_matrix_rank_map η.toRingHom η.injective AE
  have hgen : ForGeneralPoint Y (fun x =>
      (A.map (MvPolynomial.eval x)).rank = AE.rank) := by
    simpa [AE, φE] using polynomial_matrix_generic_rank Y
      (rational_image_irreducible X hX f g hg) E A
  have hY : Y.IsIrreducible := rational_image_irreducible X hX f g hg
  obtain ⟨x, hx, hgenx⟩ := (hgen.and hY (general_tangent_finrank Y hY)).exists
  have hkerx : LinearMap.ker ((A.map (MvPolynomial.eval x)).mulVecLin) =
      Y.tangentSpace x := by
    let φx : Poly m →ₐ[ℂ] ℂ := MvPolynomial.aeval x
    have hφx : ∀ q ∈ Y.ideal, φx q = 0 := by
      intro q hq
      have heval := (mem_ideal_iff_eval_zero Y q).mp hq x hx
      simpa [φx] using heval
    have h := idealJacobian_kernel Y.ideal p hp ℂ φx hφx
    exact h.trans (fieldTangent_at_point Y x)
  have hnullx := ((A.map (MvPolynomial.eval x)).mulVecLin).finrank_range_add_finrank_ker
  have hdimx : Module.finrank ℂ (Y.tangentSpace x) = Y.dimension := hgenx.2
  have hrankx : Module.finrank ℂ (LinearMap.range
      ((A.map (MvPolynomial.eval x)).mulVecLin)) =
      (A.map (MvPolynomial.eval x)).rank := rfl
  have hnullx' : (A.map (MvPolynomial.eval x)).rank + Y.dimension = m := by
    have hcard : Module.finrank ℂ (Fin m → ℂ) = m := by simp
    rw [hkerx, hdimx, hrankx, hcard] at hnullx
    exact hnullx
  have hnullE := AE.mulVecLin.finrank_range_add_finrank_ker
  have hrankE : Module.finrank E (LinearMap.range AE.mulVecLin) = AE.rank := rfl
  have hcardE : Module.finrank E (Fin m → E) = m := by simp
  have hnullE' : AE.rank + Module.finrank E (fieldTangent Y.ideal E φE) = m := by
    rw [hrankE, hcardE, hkerE] at hnullE
    exact hnullE
  have hdimE : Module.finrank E (fieldTangent Y.ideal E φE) = Y.dimension := by
    rw [hgenx.1] at hnullx'
    omega
  have hnullK := AK.mulVecLin.finrank_range_add_finrank_ker
  have hrankK : Module.finrank K (LinearMap.range AK.mulVecLin) = AK.rank := rfl
  have hcardK : Module.finrank K (Fin m → K) = m := by simp
  have hnullK' : AK.rank + Module.finrank K (fieldTangent Y.ideal K φK) = m := by
    rw [hrankK, hcardK, hkerK] at hnullK
    exact hnullK
  have hfin : Module.finrank K (fieldTangent Y.ideal K φK) = Y.dimension := by
    omega
  simpa [Y, φK] using hfin

/-- `secants.tex:63–81`: the rank of the rational differential restricted to the
source tangent is its function-field rank on a principal open. Implementation
package: source-generator Jacobian and the cleared quotient-rule matrix,
followed by the stacked-map rank identity and generic matrix specialization. -/
theorem rational_differential_generic_finrank {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (f : Fin m → Poly n) (g : Poly n) (hg : g ∉ X.ideal)
    (K : Type*) [Field K] [Algebra ℂ K]
    [Algebra (Poly n ⧸ X.ideal) K] [IsScalarTower ℂ (Poly n ⧸ X.ideal) K]
    [IsFractionRing (Poly n ⧸ X.ideal) K] :
    ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0 ∧
      Module.finrank ℂ ((X.tangentSpace x).map (rationalDifferential f g x)) =
        Module.finrank K
          ((fieldTangent X.ideal K (coordinateFieldMap X.ideal K)).map
            (fieldRationalDifferential K (coordinateFieldMap X.ideal K) f g))) := by
  obtain ⟨E, hE⟩ := X.ideal.fg_of_isNoetherianRing
  let eE : E ≃ Fin E.card := Fintype.equivFinOfCardEq (by simp)
  let p : Fin E.card → Poly n := fun i => (eE.symm i).val
  have hrange : Set.range p = (E : Set (Poly n)) := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact (eE.symm i).property
    · intro hq
      refine ⟨eE ⟨q, hq⟩, ?_⟩
      simp [p]
  have hp : Ideal.span (Set.range p) = X.ideal := by
    rw [hrange, hE]
  let A : Matrix (Fin E.card) (Fin n) (Poly n) := idealJacobian p
  let B : Matrix (Fin m) (Fin n) (Poly n) := quotientNumeratorJacobian f g
  let S := rowStack A B
  let φ : Poly n →ₐ[ℂ] K := coordinateFieldMap X.ideal K
  have hφK : ∀ q ∈ X.ideal, φ q = 0 := by
    intro q hq
    have hker : RingHom.ker φ = X.ideal := coordinateFieldMap_kernel X.ideal K
    have hqker : q ∈ RingHom.ker φ := by rw [hker]; exact hq
    exact RingHom.mem_ker.mp hqker
  have hφg : φ g ≠ 0 := by
    intro hzero
    apply hg
    have hker : RingHom.ker φ = X.ideal := coordinateFieldMap_kernel X.ideal K
    have hqker : g ∈ RingHom.ker φ := RingHom.mem_ker.mpr hzero
    rw [hker] at hqker
    exact hqker
  have hAkerK : LinearMap.ker ((A.map φ).mulVecLin) = fieldTangent X.ideal K φ :=
    idealJacobian_kernel X.ideal p hp K φ hφK
  have hdiffK : fieldRationalDifferential K φ f g =
      (φ g)⁻¹ ^ 2 • (B.map φ).mulVecLin := by
    simpa [B] using fieldRationalDifferential_eq_quotientNumerator K φ f g hφg
  let AK := A.map φ
  let BK := B.map φ
  have hstackRankK : (S.map φ).rank = Module.finrank K
      (LinearMap.range (AK.mulVecLin.prod BK.mulVecLin)) := by
    calc
      (S.map φ).rank = (rowStack AK BK).rank := by
        have hmap := rowStack_map φ.toRingHom A B
        simpa [S, AK, BK] using congrArg (fun M => M.rank) hmap
      _ = Module.finrank K (LinearMap.range (AK.mulVecLin.prod BK.mulVecLin)) :=
        rowStack_rank AK BK
  have hsumK : Module.finrank K ((LinearMap.ker AK.mulVecLin).map BK.mulVecLin) + AK.rank =
      (S.map φ).rank := by
    change Module.finrank K ((LinearMap.ker AK.mulVecLin).map BK.mulVecLin) +
      Module.finrank K (LinearMap.range AK.mulVecLin) = (S.map φ).rank
    calc
      _ = Module.finrank K (LinearMap.range (AK.mulVecLin.prod BK.mulVecLin)) :=
        finrank_map_kernel_add_range K (Fin n → K) (Fin E.card → K) (Fin m → K)
          AK.mulVecLin BK.mulVecLin
      _ = (S.map φ).rank := hstackRankK.symm
  have hscaleK : Module.finrank K ((LinearMap.ker AK.mulVecLin).map
      ((φ g)⁻¹ ^ 2 • BK.mulVecLin)) =
        Module.finrank K ((LinearMap.ker AK.mulVecLin).map BK.mulVecLin) :=
    finrank_map_smul_ne_zero (LinearMap.ker AK.mulVecLin) BK.mulVecLin
      ((φ g)⁻¹ ^ 2) (pow_ne_zero _ (inv_ne_zero hφg))
  have hformulaK : Module.finrank K ((fieldTangent X.ideal K φ).map
      (fieldRationalDifferential K φ f g)) = (S.map φ).rank - AK.rank := by
    rw [← hAkerK, hdiffK, hscaleK]
    omega
  have hgOpen : ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0) := by
    have hne : ∃ x ∈ X, MvPolynomial.eval x g ≠ 0 := by
      by_contra hn
      apply hg
      apply (mem_ideal_iff_eval_zero X g).mpr
      intro x hx
      by_contra hzero
      exact hn ⟨x, hx, hzero⟩
    exact ⟨g, hne, fun _ _ h => h⟩
  have hAgen : ForGeneralPoint X (fun x =>
      (A.map (MvPolynomial.eval x)).rank = AK.rank) := by
    simpa [AK, φ] using polynomial_matrix_generic_rank X hX K A
  have hSgen : ForGeneralPoint X (fun x =>
      (S.map (MvPolynomial.eval x)).rank = (S.map φ).rank) := by
    simpa [φ] using polynomial_matrix_generic_rank X hX K S
  have hAS := hAgen.and hX hSgen
  have hgood := hgOpen.and hX hAS
  exact hgood.mono (by
    intro x hx h
    rcases h with ⟨hgx, hAeq, hSeq⟩
    let φx : Poly n →ₐ[ℂ] ℂ := MvPolynomial.aeval x
    have hφx : ∀ q ∈ X.ideal, φx q = 0 := by
      intro q hq
      have heval := (mem_ideal_iff_eval_zero X q).mp hq x hx
      simpa [φx] using heval
    have hAkerx : LinearMap.ker ((A.map (MvPolynomial.eval x)).mulVecLin) =
        X.tangentSpace x := by
      have hker := idealJacobian_kernel X.ideal p hp ℂ φx hφx
      have hpoint := hker.trans (fieldTangent_at_point X x)
      simpa [φx] using hpoint
    have hdiffx : rationalDifferential f g x =
        (MvPolynomial.eval x g)⁻¹ ^ 2 •
          (B.map (MvPolynomial.eval x)).mulVecLin := by
      calc
        rationalDifferential f g x =
            fieldRationalDifferential ℂ (MvPolynomial.aeval x) f g :=
          rationalDifferential_eq_fieldRationalDifferential f g x
        _ = (MvPolynomial.eval x g)⁻¹ ^ 2 •
            (B.map (MvPolynomial.eval x)).mulVecLin := by
          simpa [B] using fieldRationalDifferential_eq_quotientNumerator ℂ
            (MvPolynomial.aeval x) f g (by simpa using hgx)
    let Ax := A.map (MvPolynomial.eval x)
    let Bx := B.map (MvPolynomial.eval x)
    have hstackRankx : (S.map (MvPolynomial.eval x)).rank = Module.finrank ℂ
        (LinearMap.range (Ax.mulVecLin.prod Bx.mulVecLin)) := by
      calc
        (S.map (MvPolynomial.eval x)).rank = (rowStack Ax Bx).rank := by
          have hmap := rowStack_map (MvPolynomial.eval x) A B
          simpa [S, Ax, Bx] using congrArg (fun M => M.rank) hmap
        _ = Module.finrank ℂ (LinearMap.range (Ax.mulVecLin.prod Bx.mulVecLin)) :=
          rowStack_rank Ax Bx
    have hsumx : Module.finrank ℂ ((LinearMap.ker Ax.mulVecLin).map Bx.mulVecLin) + Ax.rank =
        (S.map (MvPolynomial.eval x)).rank := by
      change Module.finrank ℂ ((LinearMap.ker Ax.mulVecLin).map Bx.mulVecLin) +
        Module.finrank ℂ (LinearMap.range Ax.mulVecLin) = (S.map (MvPolynomial.eval x)).rank
      calc
        _ = Module.finrank ℂ (LinearMap.range (Ax.mulVecLin.prod Bx.mulVecLin)) :=
          finrank_map_kernel_add_range ℂ (Fin n → ℂ) (Fin E.card → ℂ) (Fin m → ℂ)
            Ax.mulVecLin Bx.mulVecLin
        _ = (S.map (MvPolynomial.eval x)).rank := hstackRankx.symm
    have hscaleX : Module.finrank ℂ ((LinearMap.ker Ax.mulVecLin).map
        ((MvPolynomial.eval x g)⁻¹ ^ 2 • Bx.mulVecLin)) =
          Module.finrank ℂ ((LinearMap.ker Ax.mulVecLin).map Bx.mulVecLin) :=
      finrank_map_smul_ne_zero (LinearMap.ker Ax.mulVecLin) Bx.mulVecLin
        ((MvPolynomial.eval x g)⁻¹ ^ 2)
        (pow_ne_zero _ (inv_ne_zero hgx))
    have hformulaX : Module.finrank ℂ ((X.tangentSpace x).map (rationalDifferential f g x)) =
        (S.map (MvPolynomial.eval x)).rank - Ax.rank := by
      rw [← hAkerx, hdiffx, hscaleX]
      omega
    refine ⟨hgx, ?_⟩
    calc
      Module.finrank ℂ ((X.tangentSpace x).map (rationalDifferential f g x)) =
          (S.map (MvPolynomial.eval x)).rank - Ax.rank := hformulaX
      _ = (S.map φ).rank - AK.rank := by rw [hSeq, hAeq]
      _ = Module.finrank K ((fieldTangent X.ideal K φ).map
          (fieldRationalDifferential K φ f g)) := hformulaK.symm)

end
end DistinctDistances.TrackD
