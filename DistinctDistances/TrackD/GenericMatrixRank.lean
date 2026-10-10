import DistinctDistances.TrackD.GenericCotangent
import DistinctDistances.TrackD.RationalFunctionField
import Mathlib.LinearAlgebra.Matrix.Rank

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

private def rankPadding {R : Type*} [Zero R] {r c : ℕ}
    (M : Matrix (Fin r) (Fin c) R) :
    Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) R :=
  Matrix.fromBlocks 0 M 0 0

private theorem map_rankPadding {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    {r c : ℕ} (f : R →+* S) (M : Matrix (Fin r) (Fin c) R) :
    (rankPadding M).map f = rankPadding (M.map f) := by
  ext i j
  cases i <;> cases j <;> simp [rankPadding, Matrix.fromBlocks]

private def rankPaddingColumnMap {K : Type*} [Semiring K] {r c : ℕ} :
    (Fin r → K) →ₗ[K] (Fin r ⊕ Fin c → K) where
  toFun v := Sum.elim v (fun _ => 0)
  map_add' v w := by funext i; cases i <;> simp
  map_smul' a v := by funext i; cases i <;> simp

private theorem rank_rankPadding {K : Type*} [Field K] {r c : ℕ}
    (M : Matrix (Fin r) (Fin c) K) : (rankPadding M).rank = M.rank := by
  let e := rankPaddingColumnMap (K := K) (r := r) (c := c)
  have he : Function.Injective e := by
    intro v w h
    funext i
    have hi := congrFun h (Sum.inl i)
    exact hi
  have hcols (j : Fin c) : (rankPadding M).col (Sum.inr j) = e (M.col j) := by
    funext i
    cases i <;> simp [e, rankPadding, rankPaddingColumnMap, Matrix.fromBlocks]
  have hzero (j : Fin r) : (rankPadding M).col (Sum.inl j) = 0 := by
    funext i
    cases i <;> simp [rankPadding, Matrix.fromBlocks]
  have hspan :
      Submodule.span K (Set.range (rankPadding M).col) =
        (Submodule.span K (Set.range M.col)).map e := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro v ⟨i, rfl⟩
      cases i with
      | inl i =>
        rw [hzero]
        exact Submodule.zero_mem _
      | inr i =>
        rw [hcols]
        exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.map_span]
      apply Submodule.span_le.2
      rintro v ⟨w, hw, rfl⟩
      rcases hw with ⟨j, rfl⟩
      rw [← hcols j]
      exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  calc
    (rankPadding M).rank = Module.finrank K (Submodule.span K (Set.range (rankPadding M).col)) :=
      Matrix.rank_eq_finrank_span_cols _
    _ = Module.finrank K ((Submodule.span K (Set.range M.col)).map e) := by rw [hspan]
    _ = Module.finrank K (Submodule.span K (Set.range M.col)) :=
      (Submodule.equivMapOfInjective e he _).finrank_eq.symm
    _ = M.rank := (Matrix.rank_eq_finrank_span_cols M).symm

private theorem rank_normalBlock {K : Type*} [Field K] (k l : ℕ) :
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
      B.rank ≤ (Finset.univ.image Sum.inl).card :=
        Matrix.rank_le_card_of_support_subset B _ hrows
      _ = k := by
        rw [Finset.card_image_of_injective _ Sum.inl_injective]
        simp
  exact Nat.le_antisymm hupper hlower

/-- A polynomial matrix has its coordinate-function-field rank on a principal
open of an irreducible carrier (`secants.tex:63–81`). Implementation package:
finite denominator clearing in a rank normal form, after padding a rectangular
matrix by zero rows and columns if necessary. -/
theorem polynomial_matrix_generic_rank {n r c : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (Poly n ⧸ X.ideal) K]
    [IsScalarTower ℂ (Poly n ⧸ X.ideal) K] [IsFractionRing (Poly n ⧸ X.ideal) K]
    (M : Matrix (Fin r) (Fin c) (Poly n)) :
    ForGeneralPoint X (fun x =>
      (M.map (MvPolynomial.eval x)).rank =
        (M.map (coordinateFieldMap X.ideal K)).rank) := by
  let ι := Fin r ⊕ Fin c
  let φ : Poly n →+* K := (coordinateFieldMap X.ideal K).toRingHom
  let P : Matrix ι ι (Poly n) := rankPadding M
  let PK : Matrix ι ι K := P.map φ
  have hPKpad : P.map φ = rankPadding (M.map φ) := by
    ext i j
    cases i <;> cases j <;> simp [P, rankPadding, Matrix.fromBlocks]
  have hPKrank : PK.rank = (M.map φ).rank := by
    dsimp only [PK]
    change (P.map φ).rank = (M.map φ).rank
    rw [hPKpad]
    exact rank_rankPadding _
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form PK
  obtain ⟨qV, av, hqV, hav⟩ := polynomial_common_denominator X.ideal K
    (Finset.univ : Finset (ι × ι)) (fun ij => V ij.1 ij.2)
  obtain ⟨qU, au, hqU, hau⟩ := polynomial_common_denominator X.ideal K
    (Finset.univ : Finset (ι × ι)) (fun ij => U ij.1 ij.2)
  let VP : Matrix ι ι (Poly n) := Matrix.of fun i j => av (i, j)
  let UP : Matrix ι ι (Poly n) := Matrix.of fun i j => au (i, j)
  have hvmap : VP.map φ = φ qV • V := by
    ext i j
    change φ (av (i, j)) = φ qV * V i j
    exact hav (i, j) (Finset.mem_univ _)
  have humap : UP.map φ = φ qU • U := by
    ext i j
    change φ (au (i, j)) = φ qU * U i j
    exact hau (i, j) (Finset.mem_univ _)
  let Dpoly : Matrix ι ι (Poly n) :=
    (Matrix.fromBlocks (1 : Matrix (Fin PK.rank) (Fin PK.rank) (Poly n))
      0 0 0).submatrix e e
  let Dfield : Matrix ι ι K :=
    (Matrix.fromBlocks (1 : Matrix (Fin PK.rank) (Fin PK.rank) K)
      0 0 0).submatrix e e
  have hDmap : Dpoly.map φ = Dfield := by
    ext i j
    cases hi : e i <;> cases hj : e j <;>
      simp [Dpoly, Dfield, hi, hj, Matrix.fromBlocks, Matrix.one_apply]
  have hclear : (VP.map φ) * PK * (UP.map φ) = (φ qV * φ qU) • Dfield := by
    calc
      (VP.map φ) * PK * (UP.map φ) =
          (φ qV * φ qU) • (V * PK * U) := by
        rw [hvmap, humap]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        congr 1
        ring
      _ = (φ qV * φ qU) • Dfield := by rw [hnormal]
  let H : Matrix ι ι (Poly n) := VP * P * UP - (qV * qU) • Dpoly
  have hleft : (VP * P * UP).map φ = (VP.map φ) * PK * (UP.map φ) := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have hright : ((qV * qU) • Dpoly).map φ = (φ qV * φ qU) • Dfield := by
    calc
      ((qV * qU) • Dpoly).map φ = φ (qV * qU) • Dpoly.map φ := by
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      _ = (φ qV * φ qU) • Dfield := by rw [map_mul, hDmap]
  have hHentry (i j : ι) : φ (H i j) = 0 := by
    change φ ((VP * P * UP) i j - ((qV * qU) • Dpoly) i j) = 0
    rw [map_sub]
    have hleftij : φ ((VP * P * UP) i j) =
        ((VP.map φ) * PK * (UP.map φ)) i j := by
      have h := congrArg (fun A : Matrix ι ι K => A i j) hleft
      simpa using h
    have hrightij : φ (((qV * qU) • Dpoly) i j) =
        ((φ qV * φ qU) • Dfield) i j := by
      have h := congrArg (fun A : Matrix ι ι K => A i j) hright
      simpa using h
    rw [hleftij, hrightij]
    exact sub_eq_zero.mpr (congrArg (fun A : Matrix ι ι K => A i j) hclear)
  have hker : RingHom.ker φ = X.ideal := coordinateFieldMap_kernel X.ideal K
  let G : Poly n := qV * qU * VP.det * UP.det
  have hvdet : φ VP.det ≠ 0 := by
    have hdet : φ VP.det = (VP.map φ).det := RingHom.map_det φ VP
    rw [hdet, hvmap, Matrix.det_smul]
    have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
    exact mul_ne_zero (pow_ne_zero _ hqV) hVdet.ne_zero
  have hudet : φ UP.det ≠ 0 := by
    have hdet : φ UP.det = (UP.map φ).det := RingHom.map_det φ UP
    rw [hdet, humap, Matrix.det_smul]
    have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
    exact mul_ne_zero (pow_ne_zero _ hqU) hUdet.ne_zero
  have hGφ : φ G ≠ 0 := by
    dsimp [G]
    simp only [map_mul]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hqV hqU) hvdet) hudet
  have hGnot : G ∉ X.ideal := by
    intro hG
    have hGker : G ∈ RingHom.ker φ := by rw [hker]; exact hG
    exact hGφ (RingHom.mem_ker.mp hGker)
  have hGexists : ∃ x ∈ X, MvPolynomial.eval x G ≠ 0 := by
    by_contra hn
    apply hGnot
    apply (mem_ideal_iff_eval_zero X G).mpr
    intro x hx
    by_contra hne
    exact hn ⟨x, hx, hne⟩
  refine ⟨G, hGexists, ?_⟩
  intro x hx hGx
  have hGx' : MvPolynomial.eval x qV * MvPolynomial.eval x qU *
      MvPolynomial.eval x VP.det * MvPolynomial.eval x UP.det ≠ 0 := by
    simpa [G, map_mul] using hGx
  rcases mul_ne_zero_iff.mp hGx' with ⟨hGx'', hUPxdet⟩
  rcases mul_ne_zero_iff.mp hGx'' with ⟨hGx''', hVPxdet⟩
  rcases mul_ne_zero_iff.mp hGx''' with ⟨hqVx, hqUx⟩
  have hVPdetx : (VP.map (MvPolynomial.eval x)).det ≠ 0 := by
    have hdet : MvPolynomial.eval x VP.det = (VP.map (MvPolynomial.eval x)).det :=
      RingHom.map_det (MvPolynomial.eval x) VP
    rw [← hdet]
    exact hVPxdet
  have hUPdetx : (UP.map (MvPolynomial.eval x)).det ≠ 0 := by
    have hdet : MvPolynomial.eval x UP.det = (UP.map (MvPolynomial.eval x)).det :=
      RingHom.map_det (MvPolynomial.eval x) UP
    rw [← hdet]
    exact hUPxdet
  have hHpoint : H.map (MvPolynomial.eval x) = 0 := by
    ext i j
    have hHij : H i j ∈ X.ideal := by
      rw [← hker]
      exact RingHom.mem_ker.mpr (hHentry i j)
    exact (mem_ideal_iff_eval_zero X (H i j)).mp hHij x hx
  have hEvalLeft : (VP * P * UP).map (MvPolynomial.eval x) =
      (VP.map (MvPolynomial.eval x)) * (P.map (MvPolynomial.eval x)) *
        (UP.map (MvPolynomial.eval x)) := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have hsmul : ((qV * qU) • Dpoly).map (MvPolynomial.eval x) =
      (MvPolynomial.eval x qV * MvPolynomial.eval x qU) •
        (Dpoly.map (MvPolynomial.eval x)) := by
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hpoint : (VP.map (MvPolynomial.eval x)) * (P.map (MvPolynomial.eval x)) *
      (UP.map (MvPolynomial.eval x)) =
        (MvPolynomial.eval x qV * MvPolynomial.eval x qU) •
          (Dpoly.map (MvPolynomial.eval x)) := by
    ext i j
    have hzero : MvPolynomial.eval x (H i j) = 0 := by
      have h := congrArg (fun A : Matrix ι ι ℂ => A i j) hHpoint
      simpa using h
    dsimp only [H] at hzero
    rw [Matrix.sub_apply, map_sub] at hzero
    have hleftij : MvPolynomial.eval x ((VP * P * UP) i j) =
        ((VP.map (MvPolynomial.eval x)) * (P.map (MvPolynomial.eval x)) *
          (UP.map (MvPolynomial.eval x))) i j := by
      have h := congrArg (fun A : Matrix ι ι ℂ => A i j) hEvalLeft
      simpa using h
    have hrightij : MvPolynomial.eval x (((qV * qU) • Dpoly) i j) =
        ((MvPolynomial.eval x qV * MvPolynomial.eval x qU) •
          (Dpoly.map (MvPolynomial.eval x))) i j := by
      have h := congrArg (fun A : Matrix ι ι ℂ => A i j) hsmul
      simpa using h
    rw [hleftij, hrightij] at hzero
    exact sub_eq_zero.mp hzero
  have hDmapxrank : (Dpoly.map (MvPolynomial.eval x)).rank = PK.rank := by
    have hDmapx : Dpoly.map (MvPolynomial.eval x) =
        (Matrix.fromBlocks (1 : Matrix (Fin PK.rank) (Fin PK.rank) ℂ)
          0 0 0).submatrix e e := by
      ext i j
      cases hi : e i <;> cases hj : e j <;>
        simp [Dpoly, hi, hj, Matrix.fromBlocks, Matrix.one_apply]
    calc
      (Dpoly.map (MvPolynomial.eval x)).rank =
          (Matrix.fromBlocks (1 : Matrix (Fin PK.rank) (Fin PK.rank) ℂ)
            0 0 0).rank := by rw [hDmapx, Matrix.rank_submatrix]
      _ = PK.rank := rank_normalBlock _ _
  have hsmulrank :
      (((MvPolynomial.eval x qV * MvPolynomial.eval x qU) •
        (Dpoly.map (MvPolynomial.eval x))).rank) = PK.rank := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors]
    · exact hDmapxrank
    · exact mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hqVx hqUx)
  have hmulrank :
      ((VP.map (MvPolynomial.eval x)) * (P.map (MvPolynomial.eval x)) *
        (UP.map (MvPolynomial.eval x))).rank = (P.map (MvPolynomial.eval x)).rank := by
    rw [Matrix.mul_assoc,
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hVPdetx,
      Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hUPdetx]
  calc
    (M.map (MvPolynomial.eval x)).rank = (P.map (MvPolynomial.eval x)).rank := by
      rw [map_rankPadding]
      exact (rank_rankPadding _).symm
    _ = PK.rank := by rw [← hmulrank, hpoint, hsmulrank]
    _ = (M.map φ).rank := hPKrank

end
end DistinctDistances.TrackD
