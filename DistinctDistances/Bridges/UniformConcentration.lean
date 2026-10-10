import DistinctDistances.TrackB.UniformCompletion
import DistinctDistances.TrackB.ConcentrationForms
import DistinctDistances.TrackE.SkewPoint
import DistinctDistances.TrackE.PairFlats
import DistinctDistances.TrackD.ProductTangents
import DistinctDistances.Bridges.AmbientHilbert
import DistinctDistances.Bridges.ProjectiveEnvelope
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Coordinate bridge from track E's skew-matrix parameters and varieties to the
projective parameter and evaluation-flat model used by track B.
-/

namespace DistinctDistances.Bridges

open scoped BigOperators
open Classical
open LinearMap (BilinForm)
noncomputable section

private theorem card_skewIdx_bridge (e : ℕ) :
    Fintype.card (SkewIdx e) = e.choose 2 := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ b : Fin e, (∑ a : Fin e, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter]
    rw [show (Finset.univ.filter fun a : Fin e => a < b) = Finset.Iio b by ext; simp]
    simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) e, Finset.sum_range_id, Nat.choose_two_right]

private def skewMatrices (e : ℕ) : Submodule ℂ (Matrix (Fin e) (Fin e) ℂ) where
  carrier := {M | M.transpose = -M}
  zero_mem' := by simp
  add_mem' := by
    intro M N hM hN
    change M.transpose = -M at hM
    change N.transpose = -N at hN
    change (M + N).transpose = -(M + N)
    rw [Matrix.transpose_add, hM, hN, neg_add]
  smul_mem' := by
    intro c M hM
    change M.transpose = -M at hM
    change (c • M).transpose = -(c • M)
    rw [Matrix.transpose_smul, hM, smul_neg]

private def skewEntriesEquiv (e : ℕ) :
    (SkewIdx e → ℂ) ≃ₗ[ℂ] skewMatrices e where
  toFun z := ⟨skewMatrix z, by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hji
    · simp [skewMatrix, hij, lt_asymm hij]
    · subst j
      simp [skewMatrix]
    · simp [skewMatrix, hji, not_lt_of_gt hji]
  ⟩
  invFun M ij := M.1 ij.1.1 ij.1.2
  left_inv z := by
    funext ij
    simp [skewMatrix, ij.2]
  right_inv M := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with hij | hij | hji
    · simp [skewMatrix, hij]
    · subst j
      have hdiag := congrFun (congrFun M.2 i) i
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at hdiag
      have hsum : M.1 i i + M.1 i i = 0 := by
        calc
          M.1 i i + M.1 i i = M.1 i i + (-M.1 i i) := by rw [hdiag.symm]
          _ = 0 := add_neg_cancel _
      have htwo : (2 : ℂ) * M.1 i i = 0 := by
        simpa only [two_mul] using hsum
      have hzero : M.1 i i = 0 :=
        (mul_eq_zero.mp htwo).resolve_left (by norm_num)
      simp [skewMatrix, hzero]
    · have h := congrFun (congrFun M.2 i) j
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
      simp [skewMatrix, hji, not_lt_of_gt hji, h]
  map_add' z w := by
    apply Subtype.ext
    ext i j
    by_cases h : i < j
    · simp [skewMatrix, h]
    · by_cases h' : j < i
      · simp [skewMatrix, h, h'] <;> ring
      · simp [skewMatrix, h, h'] <;> ring
  map_smul' c z := by
    apply Subtype.ext
    ext i j
    by_cases h : i < j
    · simp [skewMatrix, h]
    · by_cases h' : j < i
      · simp [skewMatrix, h, h']
      · simp [skewMatrix, h, h'] <;> ring

private theorem bilinearToMatrix_flip (e : ℕ)
    (B : BilinForm ℂ (Fin e → ℂ)) :
    (B.flip).toMatrix' = B.toMatrix'.transpose := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix'_apply, LinearMap.flip_apply,
    Matrix.transpose_apply]

private def skewMatricesEquivAlternating (e : ℕ) :
    skewMatrices e ≃ₗ[ℂ] TrackB.alternatingForms (U := Point e) where
  toFun M := ⟨Matrix.toBilin' (-M.1), by
    have hN : (-M.1).transpose = -(-M.1) := by
      have hM : M.1.transpose = -M.1 := M.2
      rw [Matrix.transpose_neg, hM]
    apply (LinearMap.isAlt_iff_eq_neg_flip).2
    apply LinearMap.BilinForm.toMatrix'.injective
    calc
      (Matrix.toBilin' (-M.1)).toMatrix' =
          -((Matrix.toBilin' (-M.1)).flip.toMatrix') := by
        rw [bilinearToMatrix_flip, LinearMap.BilinForm.toMatrix'_toBilin']
        simp [hN]
      _ = (-(Matrix.toBilin' (-M.1)).flip).toMatrix' := by simp
  ⟩
  invFun B := ⟨-B.1.toMatrix', by
    have hB := (LinearMap.isAlt_iff_eq_neg_flip).1 B.2
    have hmat : B.1.toMatrix' = -B.1.toMatrix'.transpose := by
      calc
        B.1.toMatrix' = (-B.1.flip).toMatrix' := congrArg
          LinearMap.BilinForm.toMatrix' hB
        _ = -(B.1.flip.toMatrix') := by simp
        _ = -B.1.toMatrix'.transpose := by rw [bilinearToMatrix_flip]
    have hskew : B.1.toMatrix'.transpose = -B.1.toMatrix' := by
      simpa only [neg_neg] using (congrArg Neg.neg hmat).symm
    change (-B.1.toMatrix').transpose = -(-B.1.toMatrix')
    rw [Matrix.transpose_neg, hskew]
  ⟩
  left_inv M := by
    apply Subtype.ext
    simp
  right_inv B := by
    apply Subtype.ext
    simp
  map_add' M N := by
    apply Subtype.ext
    change Matrix.toBilin' (-(M.1 + N.1)) =
      Matrix.toBilin' (-M.1) + Matrix.toBilin' (-N.1)
    rw [neg_add, map_add]
  map_smul' c M := by
    apply Subtype.ext
    change Matrix.toBilin' (-(c • M.1)) = c • Matrix.toBilin' (-M.1)
    rw [← smul_neg, map_smul]

private def pointSkewEquiv (e : ℕ) :
    Point (e.choose 2) ≃ₗ[ℂ] (SkewIdx e → ℂ) where
  toFun x ij := x (Fin.cast (card_skewIdx_bridge e) (Fintype.equivFin (SkewIdx e) ij))
  invFun z i := z ((Fintype.equivFin (SkewIdx e)).symm
    (Fin.cast (card_skewIdx_bridge e).symm i))
  left_inv x := by
    funext i
    change x (Fin.cast (card_skewIdx_bridge e)
      (Fintype.equivFin (SkewIdx e)
        ((Fintype.equivFin (SkewIdx e)).symm
          (Fin.cast (card_skewIdx_bridge e).symm i)))) = x i
    simp only [Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_refl, Fin.cast_eq_self]
  right_inv z := by
    funext ij
    change z ((Fintype.equivFin (SkewIdx e)).symm
      (Fin.cast (card_skewIdx_bridge e).symm
        (Fin.cast (card_skewIdx_bridge e) (Fintype.equivFin (SkewIdx e) ij)))) = z ij
    simp only [Fin.cast_cast, Fin.cast_refl, Fin.cast_eq_self,
      Equiv.symm_apply_apply]
  map_add' x y := by
    funext ij
    rfl
  map_smul' c x := by
    funext ij
    rfl

/-- The skew coordinates that make track B's evaluation flat agree with
track E's `skewMatrix` after `skewToPoint`; the minus sign is absorbed in the
bilinear form convention. -/
def uniformConcentrationCoordinates (e : ℕ) : TrackB.SkewCoordinates e where
  decode := (pointSkewEquiv e).trans
    ((skewEntriesEquiv e).trans (skewMatricesEquivAlternating e))

private def coordinateSkewMatrix (e : ℕ) (x : Point (e.choose 2)) :
    Matrix (Fin e) (Fin e) ℂ := skewMatrix (pointSkewEquiv e x)

private theorem matrixBilin_skew {e : ℕ} (M : Matrix (Fin e) (Fin e) ℂ)
    (hM : M.transpose = -M) (v w : Point e) :
    Matrix.toBilin' (-M) v w = dotProduct (M.mulVec v) w := by
  rw [Matrix.toBilin'_apply', ← hM]
  exact (Matrix.dotProduct_transpose_mulVec M v w).trans (dotProduct_comm _ _)

private theorem covectorOfPoint_apply (e : ℕ) (y w : Point e) :
    TrackB.covectorOfPoint y w = dotProduct y w := by
  simp [TrackB.covectorOfPoint, dotProduct]

private theorem uniformCoordinates_decode_eval (e : ℕ) (x : Point (e.choose 2))
    (v w : Point e) :
    ((uniformConcentrationCoordinates e).decode x).1 v w =
      dotProduct ((coordinateSkewMatrix e x).mulVec v) w := by
  have hM : (coordinateSkewMatrix e x).transpose = -coordinateSkewMatrix e x := by
    exact (skewEntriesEquiv e (pointSkewEquiv e x)).property
  change Matrix.toBilin' (-coordinateSkewMatrix e x) v w = _
  exact matrixBilin_skew (coordinateSkewMatrix e x) hM v w

private theorem firstPoint_joinPoints (e : ℕ) (v y : Point e) :
    TrackB.firstPoint (TrackB.joinPoints v y) = v := by
  funext i
  change Fin.addCases v y (Fin.castAdd e i) = v i
  exact Fin.addCases_left i

private theorem secondPoint_joinPoints (e : ℕ) (v y : Point e) :
    TrackB.secondPoint (TrackB.joinPoints v y) = y := by
  funext i
  change Fin.addCases v y (Fin.natAdd e i) = y i
  exact Fin.addCases_right i

private theorem firstPoint_smul {e : ℕ} (c : ℂ) (w : Point (e + e)) :
    TrackB.firstPoint (c • w) = c • TrackB.firstPoint w := by
  rfl

private theorem secondPoint_smul {e : ℕ} (c : ℂ) (w : Point (e + e)) :
    TrackB.secondPoint (c • w) = c • TrackB.secondPoint w := by
  rfl

private theorem joinPoints_ne_zero (e : ℕ) (v y : Point e) (hv : v ≠ 0) :
    TrackB.joinPoints v y ≠ 0 := by
  intro h
  apply hv
  have hfirst := congrArg TrackB.firstPoint h
  calc
    v = TrackB.firstPoint (TrackB.joinPoints v y) := (firstPoint_joinPoints e v y).symm
    _ = TrackB.firstPoint 0 := hfirst
    _ = 0 := rfl

private def requestPairProjective (e : ℕ) (l : Point e × Point e) (hv : l.1 ≠ 0) :
    ProjectivePoint (e + e) :=
  Projectivization.mk ℂ (TrackB.joinPoints l.1 l.2)
    (joinPoints_ne_zero e l.1 l.2 hv)

private theorem requestPairProjective_injOn {e : ℕ}
    (Λ : Finset (Point e × Point e))
    (hNZ : ∀ l ∈ Λ, l.1 ≠ 0)
    (hprop : ∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ c : ℂ, l' = c • l → l' = l) :
    ∀ (l) (hl : l ∈ Λ) (l') (hl' : l' ∈ Λ),
      requestPairProjective e l (hNZ l hl) =
        requestPairProjective e l' (hNZ l' hl') → l = l' := by
  intro l hl l' hl' hp
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _
    (joinPoints_ne_zero e l.1 l.2 (hNZ l hl))
    (joinPoints_ne_zero e l'.1 l'.2 (hNZ l' hl'))).mp hp
  change (c : ℂ) • TrackB.joinPoints l'.1 l'.2 =
    TrackB.joinPoints l.1 l.2 at hc
  have hfirst := congrArg TrackB.firstPoint hc
  have hsecond := congrArg TrackB.secondPoint hc
  have hfirst_smul : TrackB.firstPoint ((c : ℂ) • TrackB.joinPoints l'.1 l'.2) =
      (c : ℂ) • l'.1 := by
    rw [firstPoint_smul, firstPoint_joinPoints]
  have hsecond_smul : TrackB.secondPoint ((c : ℂ) • TrackB.joinPoints l'.1 l'.2) =
      (c : ℂ) • l'.2 := by
    rw [secondPoint_smul, secondPoint_joinPoints]
  have hfst : l.1 = (c : ℂ) • l'.1 := by
    calc
      l.1 = TrackB.firstPoint (TrackB.joinPoints l.1 l.2) :=
        (firstPoint_joinPoints e l.1 l.2).symm
      _ = TrackB.firstPoint ((c : ℂ) • TrackB.joinPoints l'.1 l'.2) := hfirst.symm
      _ = (c : ℂ) • l'.1 := hfirst_smul
  have hsnd : l.2 = (c : ℂ) • l'.2 := by
    calc
      l.2 = TrackB.secondPoint (TrackB.joinPoints l.1 l.2) :=
        (secondPoint_joinPoints e l.1 l.2).symm
      _ = TrackB.secondPoint ((c : ℂ) • TrackB.joinPoints l'.1 l'.2) := hsecond.symm
      _ = (c : ℂ) • l'.2 := hsecond_smul
  have hpair : l = (c : ℂ) • l' := Prod.ext hfst hsnd
  exact hprop l' hl' l hl c hpair

private theorem parameterValue_joinPoints {e : ℕ} (v y : Point e) :
    TrackB.parameterValue (TrackB.joinPoints v y) = ∑ i, y i * v i := by
  rw [TrackB.parameterValue, firstPoint_joinPoints, secondPoint_joinPoints]
  simp [TrackB.covectorOfPoint, LinearMap.proj_apply]

private theorem parameterValue_smul {e : ℕ} (c : ℂ) (w : Point (e + e)) :
    TrackB.parameterValue (c • w) = c ^ 2 * TrackB.parameterValue w := by
  change TrackB.covectorOfPoint (TrackB.secondPoint (c • w))
      (TrackB.firstPoint (c • w)) =
    c ^ 2 * TrackB.covectorOfPoint (TrackB.secondPoint w) (TrackB.firstPoint w)
  rw [secondPoint_smul, firstPoint_smul]
  rw [covectorOfPoint_apply, covectorOfPoint_apply]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem requestPairProjective_mem_affineParameters {e : ℕ}
    (l : Point e × Point e) (hv : l.1 ≠ 0)
    (hquad : ∑ i, l.2 i * l.1 i = 0) :
    requestPairProjective e l hv ∈ TrackB.affineParameters e := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (TrackB.joinPoints l.1 l.2) (joinPoints_ne_zero e l.1 l.2 hv)
  change (c : ℂ) • TrackB.joinPoints l.1 l.2 =
    (requestPairProjective e l hv).rep at hc
  change TrackB.parameterValue (requestPairProjective e l hv).rep = 0 ∧
    TrackB.firstPoint (requestPairProjective e l hv).rep ≠ 0
  constructor
  · rw [← hc, parameterValue_smul, parameterValue_joinPoints, hquad]
    simp
  · have hfirst : TrackB.firstPoint (requestPairProjective e l hv).rep =
        (c : ℂ) • l.1 := by
      rw [← hc, firstPoint_smul, firstPoint_joinPoints]
    rw [hfirst]
    exact smul_ne_zero (Units.ne_zero c) hv

private theorem decode_eval_functional_iff {e : ℕ} (x : Point (e.choose 2))
    (v y : Point e) :
    ((uniformConcentrationCoordinates e).decode x).1 v = TrackB.covectorOfPoint y ↔
      (coordinateSkewMatrix e x).mulVec v = y := by
  constructor
  · intro h
    funext i
    have hi := congrArg (fun f : Module.Dual ℂ (Point e) => f (Pi.single i 1)) h
    have hi' : dotProduct ((coordinateSkewMatrix e x).mulVec v) (Pi.single i 1) =
        dotProduct y (Pi.single i 1) := by
      simpa only [uniformCoordinates_decode_eval, covectorOfPoint_apply] using hi
    simpa only [dotProduct_single, mul_one] using hi'
  · intro h
    apply LinearMap.ext
    intro w
    rw [uniformCoordinates_decode_eval, h, covectorOfPoint_apply]

private theorem joinPoints_comp_finSumFinEquiv {e : ℕ} (v y : Point e) :
    TrackB.joinPoints v y ∘ finSumFinEquiv = Sum.elim v y := by
  funext i
  cases i with
  | inl i =>
      change Fin.addCases v y (Fin.castAdd e i) = v i
      exact Fin.addCases_left i
  | inr i =>
      change Fin.addCases v y (Fin.natAdd e i) = y i
      exact Fin.addCases_right i

private theorem eval_rename_pair {e : ℕ} (v y : Point e)
    (f : MvPolynomial (Fin e ⊕ Fin e) ℂ) :
    MvPolynomial.eval (TrackB.joinPoints v y) (MvPolynomial.rename finSumFinEquiv f) =
      MvPolynomial.eval (Sum.elim v y) f := by
  rw [MvPolynomial.eval_rename]
  rw [joinPoints_comp_finSumFinEquiv]

private def dualLinearPoly {n : ℕ} (φ : Module.Dual ℂ (Point n)) : Poly n :=
  ∑ i : Fin n, MvPolynomial.C (φ (Pi.single i 1)) * MvPolynomial.X i

private theorem eval_dualLinearPoly {n : ℕ} (φ : Module.Dual ℂ (Point n))
    (x : Point n) : MvPolynomial.eval x (dualLinearPoly φ) = φ x := by
  classical
  have hx : x = ∑ i : Fin n, x i • (Pi.single i 1) := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      simp [Pi.single_eq_of_ne hij.symm]
    · simp
  have hEval : MvPolynomial.eval x (dualLinearPoly φ) =
      ∑ i : Fin n, φ (Pi.single i 1) * x i := by
    simp [dualLinearPoly]
  have hφ : φ x = ∑ i : Fin n, x i * φ (Pi.single i 1) := by
    calc
      φ x = φ (∑ i : Fin n, x i • (Pi.single i 1)) := congrArg φ hx
      _ = ∑ i : Fin n, x i * φ (Pi.single i 1) := by simp [smul_eq_mul]
  calc
    MvPolynomial.eval x (dualLinearPoly φ) =
        ∑ i : Fin n, φ (Pi.single i 1) * x i := hEval
    _ = φ x := by
      rw [hφ]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem linearProjectivePlane_mem_iff {n : ℕ}
    (U : Submodule ℂ (Point n)) (p : ProjectivePoint n) :
    p ∈ (TrackB.linearProjectivePlane U).points ↔ p.rep ∈ U := by
  constructor
  · intro hp
    by_contra hnot
    obtain ⟨φ, hφrep, hφU⟩ := U.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    let T : Set (ProjectivePoint n) :=
      {q | ∃ x ∈ U, ∃ hx : x ≠ 0, Projectivization.mk ℂ x hx = q}
    let f : Poly n := dualLinearPoly φ
    have hf : f ∈ MvPolynomial.vanishingIdeal ℂ
        (ProjectiveVariety.nonzeroRepresentatives T) := by
      intro z hz
      obtain ⟨hz0, hzt⟩ := hz
      obtain ⟨x, hxU, hx0, hxproj⟩ := hzt
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ hz0 hx0).mp hxproj.symm
      change (c : ℂ) • x = z at hc
      have hφx : φ x = 0 := by
        have hmem : φ x ∈ U.map φ := ⟨x, hxU, rfl⟩
        rw [hφU] at hmem
        simpa using hmem
      have hφz : φ z = 0 := by
        rw [← hc]
        simp [hφx]
      simpa [f, eval_dualLinearPoly] using hφz
    change p ∈ (ProjectiveVariety.closure T).points at hp
    have hfp := hp p.rep p.rep_nonzero (Projectivization.mk_rep p) f hf
    have heval : MvPolynomial.eval p.rep f = φ p.rep := by
      exact eval_dualLinearPoly φ p.rep
    rw [MvPolynomial.aeval_eq_eval] at hfp
    rw [heval] at hfp
    exact hφrep hfp
  · intro hp
    change p ∈ ProjectiveVariety.closure
      {q | ∃ x ∈ U, ∃ hx : x ≠ 0, Projectivization.mk ℂ x hx = q}
    apply ProjectiveVariety.subset_closure
    exact ⟨p.rep, hp, p.rep_nonzero, Projectivization.mk_rep p⟩

private def pairJoinEquiv (e : ℕ) :
    (Point e × Point e) ≃ₗ[ℂ] Point (e + e) := TrackD.productLinearEquiv

private theorem pairJoinEquiv_apply {e : ℕ} (p : Point e × Point e) :
    pairJoinEquiv e p = TrackB.joinPoints p.1 p.2 := by
  funext i
  cases i using Fin.addCases with
  | left i =>
      change Sum.elim p.1 p.2 (finSumFinEquiv.symm (Fin.castAdd e i)) =
        Fin.addCases p.1 p.2 (Fin.castAdd e i)
      rw [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Fin.addCases_left]
  | right i =>
      change Sum.elim p.1 p.2 (finSumFinEquiv.symm (Fin.natAdd e i)) =
        Fin.addCases p.1 p.2 (Fin.natAdd e i)
      rw [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.addCases_right]

private theorem requestPolar_eq_quadratic {e : ℕ} (x x' : Point e × Point e) :
    (∑ i, (x.2 i * x'.1 i + x'.2 i * x.1 i)) =
      TrackB.parameterValue (TrackB.joinPoints (x.1 + x'.1) (x.2 + x'.2)) -
        TrackB.parameterValue (TrackB.joinPoints x.1 x.2) -
        TrackB.parameterValue (TrackB.joinPoints x'.1 x'.2) := by
  rw [parameterValue_joinPoints, parameterValue_joinPoints, parameterValue_joinPoints]
  simp only [Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem requestPairProjective_mem_plane_iff {e : ℕ}
    (l : Point e × Point e) (hv : l.1 ≠ 0) (U : Submodule ℂ (Point (e + e))) :
    requestPairProjective e l hv ∈ (TrackB.linearProjectivePlane U).points ↔
      TrackB.joinPoints l.1 l.2 ∈ U := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (TrackB.joinPoints l.1 l.2) (joinPoints_ne_zero e l.1 l.2 hv)
  change (c : ℂ) • TrackB.joinPoints l.1 l.2 =
    (requestPairProjective e l hv).rep at hc
  rw [linearProjectivePlane_mem_iff]
  constructor
  · intro hp
    have hscaled : (↑c⁻¹ : ℂ) • (requestPairProjective e l hv).rep ∈ U :=
      U.smul_mem (↑c⁻¹ : ℂ) hp
    have hjoin : TrackB.joinPoints l.1 l.2 ∈ U := by
      have hjoinEq : TrackB.joinPoints l.1 l.2 =
          (↑c⁻¹ : ℂ) • (requestPairProjective e l hv).rep := by
        calc
          TrackB.joinPoints l.1 l.2 = (↑c⁻¹ : ℂ) •
              ((↑c : ℂ) • TrackB.joinPoints l.1 l.2) := by simp [smul_smul]
          _ = (↑c⁻¹ : ℂ) • (requestPairProjective e l hv).rep := by rw [hc]
      rw [hjoinEq]
      exact hscaled
    exact hjoin
  · intro hl
    have hscaled : (↑c : ℂ) • TrackB.joinPoints l.1 l.2 ∈ U :=
      U.smul_mem (↑c : ℂ) hl
    simpa [hc] using hscaled

private theorem isotropicCap_filter_le {e : ℕ}
    (Λ : Finset (Point e × Point e)) (K : ℝ)
    (hcap : ∀ L : Submodule ℂ (Point e × Point e), Module.finrank ℂ L = e →
      (∀ x ∈ L, ∀ x' ∈ L,
        ∑ i, (x.2 i * x'.1 i + x'.2 i * x.1 i) = 0) →
      ((Λ.filter (· ∈ L)).card : ℝ) ≤ K)
    (U : Submodule ℂ (Point (e + e))) (hU : TrackB.IsMaximalIsotropic U) :
    ((Λ.filter fun x => pairJoinEquiv e x ∈ U).card : ℝ) ≤ K := by
  classical
  let L : Submodule ℂ (Point e × Point e) := U.comap (pairJoinEquiv e).toLinearMap
  have hL : L = U.map (pairJoinEquiv e).symm.toLinearMap := by
    ext x
    constructor
    · intro hx
      refine ⟨pairJoinEquiv e x, hx, ?_⟩
      simp
    · rintro ⟨u, hu, hux⟩
      have heq : pairJoinEquiv e x = u := by
        calc
          pairJoinEquiv e x = pairJoinEquiv e ((pairJoinEquiv e).symm u) :=
            congrArg (pairJoinEquiv e) hux.symm
          _ = u := (pairJoinEquiv e).apply_symm_apply u
      change pairJoinEquiv e x ∈ U
      rw [heq]
      exact hu
  have hdim : Module.finrank ℂ L = e := by
    rw [hL, LinearEquiv.finrank_map_eq (pairJoinEquiv e).symm U, hU.1]
  have hpolar : ∀ x ∈ L, ∀ x' ∈ L,
      ∑ i, (x.2 i * x'.1 i + x'.2 i * x.1 i) = 0 := by
    intro x hx x' hx'
    have hxU : pairJoinEquiv e x ∈ U := hx
    have hx'U : pairJoinEquiv e x' ∈ U := hx'
    have hsumU : pairJoinEquiv e (x + x') ∈ U := by
      rw [map_add]
      exact U.add_mem hxU hx'U
    have hqsum : TrackB.parameterValue (TrackB.joinPoints (x.1 + x'.1) (x.2 + x'.2)) = 0 := by
      simpa only [pairJoinEquiv_apply, Prod.fst_add, Prod.snd_add] using
        hU.2 (pairJoinEquiv e (x + x')) hsumU
    have hqx : TrackB.parameterValue (TrackB.joinPoints x.1 x.2) = 0 := by
      simpa only [pairJoinEquiv_apply] using hU.2 (pairJoinEquiv e x) hxU
    have hqx' : TrackB.parameterValue (TrackB.joinPoints x'.1 x'.2) = 0 := by
      simpa only [pairJoinEquiv_apply] using hU.2 (pairJoinEquiv e x') hx'U
    have hformula := requestPolar_eq_quadratic x x'
    rw [hqsum, hqx, hqx'] at hformula
    simpa using hformula
  exact hcap L hdim hpolar

private def reindexPoint {m n : ℕ} (idx : Fin m ≃ Fin n) (x : Point m) : Point n :=
  fun i => x (idx.symm i)

private def reindexAffineVariety {m n : ℕ} (idx : Fin m ≃ Fin n)
    (V : AffineVariety n) : AffineVariety m := by
  let r := MvPolynomial.renameEquiv ℂ idx
  exact ⟨V.ideal.comap (r : Poly m ≃+* Poly n), V.isRadical.comap _⟩

private theorem eval_reindex {m n : ℕ} (idx : Fin m ≃ Fin n)
    (x : Point m) (f : Poly m) :
    MvPolynomial.eval (reindexPoint idx x) (MvPolynomial.renameEquiv ℂ idx f) =
      MvPolynomial.eval x f := by
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
  simp [reindexPoint, Function.comp_def, Equiv.symm_apply_apply]

private theorem reindexAffineVariety_points {m n : ℕ} (idx : Fin m ≃ Fin n)
    (V : AffineVariety n) (x : Point m) :
    x ∈ (reindexAffineVariety idx V) ↔ reindexPoint idx x ∈ V := by
  change (∀ f ∈ (V.ideal.comap (MvPolynomial.renameEquiv ℂ idx : Poly m ≃+* Poly n)),
      MvPolynomial.eval x f = 0) ↔
    (∀ g ∈ V.ideal, MvPolynomial.eval (reindexPoint idx x) g = 0)
  constructor
  · intro hx g hg
    let f : Poly m := (MvPolynomial.renameEquiv ℂ idx).symm g
    have hf : f ∈ V.ideal.comap (MvPolynomial.renameEquiv ℂ idx : Poly m ≃+* Poly n) := by
      change MvPolynomial.renameEquiv ℂ idx f ∈ V.ideal
      have hfg : MvPolynomial.renameEquiv ℂ idx f = g := by
        simpa [f] using (MvPolynomial.renameEquiv ℂ idx).apply_symm_apply g
      rw [hfg]
      exact hg
    have hzero := hx f hf
    have heval : MvPolynomial.eval (reindexPoint idx x) g = MvPolynomial.eval x f := by
      have hfg : MvPolynomial.renameEquiv ℂ idx f = g := by simp [f]
      rw [← hfg]
      exact eval_reindex idx x f
    rw [heval, hzero]
  · intro hx f hf
    have hrename : MvPolynomial.renameEquiv ℂ idx f ∈ V.ideal := hf
    have hzero := hx (MvPolynomial.renameEquiv ℂ idx f) hrename
    have heval : MvPolynomial.eval (reindexPoint idx x)
        (MvPolynomial.renameEquiv ℂ idx f) = MvPolynomial.eval x f :=
      eval_reindex idx x f
    rw [heval] at hzero
    exact hzero

private theorem reindexAffineVariety_hilbert {m n : ℕ} (idx : Fin m ≃ Fin n)
    (V : AffineVariety n) (D : ℕ) :
    (reindexAffineVariety idx V).hilbert D = V.hilbert D := by
  classical
  let r := MvPolynomial.renameEquiv ℂ idx
  let W := reindexAffineVariety idx V
  let TB := OAI.QuarticPowerFree.totalSpace (σ := Fin m) (K := ℂ) D
  let TE := OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) D
  let qB : TB →ₗ[ℂ] (Poly m ⧸ W.ideal) :=
    (Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap.comp TB.subtype
  let qE : TB →ₗ[ℂ] (Poly n ⧸ V.ideal) :=
    (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap.comp
      (r.toLinearMap.comp TB.subtype)
  have hrangeB : LinearMap.range qB = W.restrictionSpace D := by
    change LinearMap.range qB =
      (TB.map (Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap)
    ext y
    change (∃ f : TB, qB f = y) ↔
      ∃ f : Poly m, f ∈ TB ∧ (Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap f = y
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f.val, f.property, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
  have hrangeE : LinearMap.range qE = V.restrictionSpace D := by
    change LinearMap.range qE =
      (TE.map (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap)
    ext y
    change (∃ f : TB, qE f = y) ↔
      ∃ g : Poly n, g ∈ TE ∧ (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap g = y
    constructor
    · rintro ⟨f, rfl⟩
      have hdegB : f.val.totalDegree ≤ D := OAI.QuarticPowerFree.mem_totalSpace.mp f.property
      have hdegE : (r f.val).totalDegree ≤ D := by
        change (MvPolynomial.renameEquiv ℂ idx f.val).totalDegree ≤ D
        rw [MvPolynomial.totalDegree_renameEquiv]
        exact hdegB
      exact ⟨r f.val, OAI.QuarticPowerFree.mem_totalSpace.mpr hdegE, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      have hdegE : g.totalDegree ≤ D := OAI.QuarticPowerFree.mem_totalSpace.mp hg
      have hdegB : (r.symm g).totalDegree ≤ D := by
        change ((MvPolynomial.renameEquiv ℂ idx).symm g).totalDegree ≤ D
        rw [MvPolynomial.renameEquiv_symm, MvPolynomial.totalDegree_renameEquiv]
        exact hdegE
      let f : TB := ⟨r.symm g, OAI.QuarticPowerFree.mem_totalSpace.mpr hdegB⟩
      refine ⟨f, ?_⟩
      change (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap (r (r.symm g)) =
        (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap g
      simp [f]
  have hker : LinearMap.ker qB = LinearMap.ker qE := by
    ext f
    change Ideal.Quotient.mk W.ideal f.val = 0 ↔
      Ideal.Quotient.mk V.ideal (r f.val) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  letI : Module.Finite ℂ TB := OAI.QuarticPowerFree.totalSpace_finite (n := m) (K := ℂ) D
  have hb := qB.finrank_range_add_finrank_ker
  have he := qE.finrank_range_add_finrank_ker
  rw [hker] at hb
  have hrank : Module.finrank ℂ (LinearMap.range qB) =
      Module.finrank ℂ (LinearMap.range qE) :=
    Nat.add_right_cancel (hb.trans he.symm)
  change Module.finrank ℂ (W.restrictionSpace D) = Module.finrank ℂ (V.restrictionSpace D)
  rw [← hrangeB, ← hrangeE]
  exact hrank

private theorem reindexAffineVariety_dimension_degree {m n : ℕ} (idx : Fin m ≃ Fin n)
    (V : AffineVariety n) :
    (reindexAffineVariety idx V).dimension = V.dimension ∧
      (reindexAffineVariety idx V).degree = V.degree := by
  let W := reindexAffineVariety idx V
  have hpoly : W.hilbertPolynomial = V.hilbertPolynomial := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [W.hilbert_eventually, V.hilbert_eventually] with D hW hV
    rw [← hW, ← hV]
    exact_mod_cast reindexAffineVariety_hilbert idx V D
  have hdim : W.dimension = V.dimension := by
    change W.hilbertPolynomial.natDegree = V.hilbertPolynomial.natDegree
    exact congrArg Polynomial.natDegree hpoly
  constructor
  · exact hdim
  · change ((W.dimension.factorial : ℚ) * W.hilbertPolynomial.coeff W.dimension) =
      ((V.dimension.factorial : ℚ) * V.hilbertPolynomial.coeff V.dimension)
    rw [hdim, hpoly]

private def pointReindexEquiv {m n : ℕ} (idx : Fin m ≃ Fin n) :
    Point m ≃ₗ[ℂ] Point n where
  toFun := reindexPoint idx
  invFun y i := y (idx i)
  left_inv x := by
    funext i
    simp [reindexPoint]
  right_inv y := by
    funext i
    simp [reindexPoint]
  map_add' x y := by
    funext i
    rfl
  map_smul' c x := by
    funext i
    rfl

private theorem skewToPoint_injective {e : ℕ} :
    Function.Injective (skewToPoint : (SkewIdx e → ℂ) → Point (Fintype.card (SkewIdx e))) := by
  intro z z' h
  funext ij
  have hi := congrFun h (Fintype.equivFin (SkewIdx e) ij)
  simpa [skewToPoint] using hi

private theorem bilinear_smul_left {e : ℕ} (C : TrackB.SkewCoordinates e)
    (x : Point (e.choose 2)) (v : Point e) (c : ℂ) :
    (C.decode x).1 (c • v) = c • (C.decode x).1 v := by
  ext w
  simp

private theorem covectorOfPoint_smul {e : ℕ} (y : Point e) (c : ℂ) :
    TrackB.covectorOfPoint (c • y) = c • TrackB.covectorOfPoint y := by
  apply LinearMap.ext
  intro w
  rw [covectorOfPoint_apply, LinearMap.smul_apply, covectorOfPoint_apply, smul_eq_mul]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem evaluationFlat_coordinate_iff {e : ℕ}
    (idx : Fin (e.choose 2) ≃ Fin (Fintype.card (SkewIdx e)))
    (hpoint : ∀ x : Point (e.choose 2),
      reindexPoint idx x = skewToPoint (pointSkewEquiv e x))
    (l : Point e × Point e) (hv : l.1 ≠ 0) (x : Point (e.choose 2)) :
    x ∈ TrackB.evaluationFlat (uniformConcentrationCoordinates e)
        (requestPairProjective e l hv) ↔
      reindexPoint idx x ∈ skewToPoint '' evalFlat l.1 l.2 := by
  let p := requestPairProjective e l hv
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (TrackB.joinPoints l.1 l.2) (joinPoints_ne_zero e l.1 l.2 hv)
  change (c : ℂ) • TrackB.joinPoints l.1 l.2 = p.rep at hc
  have himage : reindexPoint idx x ∈ skewToPoint '' evalFlat l.1 l.2 ↔
      (coordinateSkewMatrix e x).mulVec l.1 = l.2 := by
    constructor
    · rintro ⟨z, hz, hx⟩
      have hzcoord : z = pointSkewEquiv e x := by
        apply skewToPoint_injective
        calc
          skewToPoint z = reindexPoint idx x := hx
          _ = skewToPoint (pointSkewEquiv e x) := hpoint x
      change (skewMatrix z).mulVec l.1 = l.2 at hz
      simpa [coordinateSkewMatrix, hzcoord] using hz
    · intro hmat
      refine ⟨pointSkewEquiv e x, ?_, (hpoint x).symm⟩
      change (skewMatrix (pointSkewEquiv e x)).mulVec l.1 = l.2
      exact hmat
  constructor
  · intro hEval
    change ((uniformConcentrationCoordinates e).decode x).1
        (TrackB.firstPoint p.rep) = TrackB.covectorOfPoint (TrackB.secondPoint p.rep) at hEval
    rw [← hc, firstPoint_smul, firstPoint_joinPoints,
      secondPoint_smul, secondPoint_joinPoints] at hEval
    rw [bilinear_smul_left, covectorOfPoint_smul] at hEval
    have hraw : ((uniformConcentrationCoordinates e).decode x).1 l.1 =
        TrackB.covectorOfPoint l.2 := by
      calc
        _ = (↑c⁻¹ : ℂ) • ((↑c : ℂ) •
            ((uniformConcentrationCoordinates e).decode x).1 l.1) := by simp [smul_smul]
        _ = (↑c⁻¹ : ℂ) • ((↑c : ℂ) • TrackB.covectorOfPoint l.2) :=
          congrArg (fun f : Module.Dual ℂ (Point e) => (↑c⁻¹ : ℂ) • f) hEval
        _ = _ := by simp [smul_smul]
    exact himage.mpr ((decode_eval_functional_iff (x := x) (v := l.1) (y := l.2)).mp hraw)
  · intro him
    have hraw := (decode_eval_functional_iff (x := x) (v := l.1) (y := l.2)).mpr
      (himage.mp him)
    have hscaled : (c : ℂ) • (((uniformConcentrationCoordinates e).decode x).1 l.1) =
        (c : ℂ) • TrackB.covectorOfPoint l.2 := congrArg (fun f => (c : ℂ) • f) hraw
    have hvalue : ((uniformConcentrationCoordinates e).decode x).1 ((c : ℂ) • l.1) =
        TrackB.covectorOfPoint ((c : ℂ) • l.2) := by
      rw [bilinear_smul_left, covectorOfPoint_smul]
      exact hscaled
    change ((uniformConcentrationCoordinates e).decode x).1
        (TrackB.firstPoint p.rep) = TrackB.covectorOfPoint (TrackB.secondPoint p.rep)
    rw [← hc, firstPoint_smul, firstPoint_joinPoints,
      secondPoint_smul, secondPoint_joinPoints]
    exact hvalue

/-- Track B's projective statement in track E's skew-matrix coordinates. -/
theorem uniform_concentration_bridge {e : ℕ} (he : 3 ≤ e) :
    ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ), 1 ≤ A →
    ∀ Λ : Finset ((Fin e → ℂ) × (Fin e → ℂ)),
      (∀ l ∈ Λ, l.1 ≠ 0 ∧ ∑ i, l.2 i * l.1 i = 0) →
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ c : ℂ, l' = c • l → l' = l) →
      (∀ l ∈ Λ, ∃ (k : ℕ) (f : MvPolynomial (Fin e ⊕ Fin e) ℂ),
        1 ≤ k ∧ (k : ℝ) ≤ C₀ * A ∧ f.IsHomogeneous k ∧
        MvPolynomial.eval (Sum.elim l.1 l.2) f ≠ 0 ∧
        ∀ l' ∈ Λ, l' ≠ l → MvPolynomial.eval (Sum.elim l'.1 l'.2) f = 0) →
      (∀ L : Submodule ℂ ((Fin e → ℂ) × (Fin e → ℂ)), Module.finrank ℂ L = e →
        (∀ x ∈ L, ∀ x' ∈ L,
          ∑ i, (x.2 i * x'.1 i + x'.2 i * x.1 i) = 0) →
        ((Λ.filter (· ∈ L)).card : ℝ) ≤ C₀ * A ^ (e - 2)) →
      ∀ V : AffineVariety (Fintype.card (SkewIdx e)), V.IsIrreducible →
      ∀ h : ℕ, 1 ≤ h → h < e - 1 → V.dimension = Nat.choose (e - 1) 2 + h →
        ((Λ.card : ℝ) ≤ C₀ * A ^ (e - 1) ∨
          ∃ g : Poly (Fintype.card (SkewIdx e)), g ≠ 0 ∧
            (g.totalDegree : ℝ) ≤ C₀ * A ∧
            ∀ x ∈ V.points, MvPolynomial.eval x g = 0) →
        ((Λ.filter fun l => skewToPoint '' evalFlat l.1 l.2 ⊆ V.points).card : ℝ) ≤
          C * (V.degree : ℝ) * A ^ h := by
  intro C₀ hC₀
  obtain ⟨B, hB, hBmain⟩ := TrackB.uniform_concentration e he C₀ hC₀
  refine ⟨B, hB, ?_⟩
  intro A hA Λ hparams hprop hsep hcap V hV h h₁ hh hdim hcase
  let idx : Fin (e.choose 2) ≃ Fin (Fintype.card (SkewIdx e)) :=
    finCongr (card_skewIdx_bridge e).symm
  let Vb : AffineVariety (e.choose 2) := reindexAffineVariety idx V
  let C := uniformConcentrationCoordinates e
  have hpoint : ∀ x : Point (e.choose 2), reindexPoint idx x =
      skewToPoint (pointSkewEquiv e x) := by
    intro x
    funext i
    simp [reindexPoint, idx, skewToPoint, pointSkewEquiv]
  have hDimDeg := reindexAffineVariety_dimension_degree idx V
  have hVb : Vb.IsIrreducible := by
    letI : V.ideal.IsPrime := hV
    change (V.ideal.comap (MvPolynomial.renameEquiv ℂ idx).toRingEquiv).IsPrime
    exact Ideal.IsPrime.comap _
  have hdimB : Vb.dimension = Nat.choose (e - 1) 2 + h := hDimDeg.1.trans hdim
  have hchoose : Nat.choose e 2 = Nat.choose (e - 1) 2 + (e - 1) := by
    rw [Nat.choose_eq_choose_pred_add (by omega) (by omega)]
    simpa [Nat.add_comm]
  have hproper : Vb ≠ AffineVariety.whole := by
    intro hwhole
    have hdim' := hdimB
    rw [hwhole, affine_whole_dimension, hchoose] at hdim'
    omega
  have hNZ : ∀ l ∈ Λ, l.1 ≠ 0 := fun l hl => (hparams l hl).1
  let f : ↥Λ → ProjectivePoint (e + e) := fun a =>
    requestPairProjective e a.1 (hNZ a.1 a.2)
  let P : Finset (ProjectivePoint (e + e)) := Λ.attach.image f
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact requestPairProjective_injOn Λ hNZ hprop a.1 a.2 b.1 b.2 hab
  have hPcard : P.card = Λ.card := by
    dsimp [P]
    rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
  have hP : ∀ p ∈ P, p ∈ TrackB.affineParameters e := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact requestPairProjective_mem_affineParameters a.1 (hNZ a.1 a.2)
      (hparams a.1 a.2).2
  have hBsep : TrackB.HasSeparators P (C₀ * A) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨k, g, hk, hkD, hg, hgeval, hgzero⟩ := hsep a.1 a.2
    let gB := MvPolynomial.rename finSumFinEquiv g
    have hgB : gB.IsHomogeneous k := hg.rename_isHomogeneous
    have hEvalPair := eval_rename_pair a.1.1 a.1.2 g
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (TrackB.joinPoints a.1.1 a.1.2) (joinPoints_ne_zero e a.1.1 a.1.2
        (hNZ a.1 a.2))
    change (c : ℂ) • TrackB.joinPoints a.1.1 a.1.2 =
      (requestPairProjective e a.1 (hNZ a.1 a.2)).rep at hc
    have hEvalRep : MvPolynomial.eval
        (requestPairProjective e a.1 (hNZ a.1 a.2)).rep gB ≠ 0 := by
      rw [← hc, homogeneous_eval_smul gB hgB (c : ℂ) (TrackB.joinPoints a.1.1 a.1.2)]
      rw [hEvalPair]
      exact mul_ne_zero (pow_ne_zero k (Units.ne_zero c)) hgeval
    refine ⟨gB, k, hk, hkD, hgB, ?_, ?_⟩
    · simpa only [MvPolynomial.aeval_eq_eval] using hEvalRep
    · intro q hq hqp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
      have hba : b.1 ≠ a.1 := by
        intro hEq
        apply hqp
        exact congrArg f (Subtype.ext hEq)
      obtain ⟨c', hc'⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
        (TrackB.joinPoints b.1.1 b.1.2) (joinPoints_ne_zero e b.1.1 b.1.2
          (hNZ b.1 b.2))
      change (c' : ℂ) • TrackB.joinPoints b.1.1 b.1.2 =
        (requestPairProjective e b.1 (hNZ b.1 b.2)).rep at hc'
      have hzeroRep : MvPolynomial.eval
          (requestPairProjective e b.1 (hNZ b.1 b.2)).rep gB = 0 := by
        rw [← hc', homogeneous_eval_smul gB hgB (c' : ℂ) (TrackB.joinPoints b.1.1 b.1.2)]
        rw [eval_rename_pair, hgzero b.1 b.2 hba]
        simp
      simpa only [MvPolynomial.aeval_eq_eval] using hzeroRep
  have hBcap : TrackB.HasIsotropicCap P (C₀ * A ^ (e - 2)) := by
    intro U hU
    have hReqCap : ((Λ.filter fun l => pairJoinEquiv e l ∈ U).card : ℝ) ≤
        C₀ * A ^ (e - 2) := isotropicCap_filter_le Λ _ hcap U hU
    let Q : Finset (↥Λ) := Λ.attach.filter fun a =>
      f a ∈ (TrackB.linearProjectivePlane U).points
    have hplaneReq (a : ↥Λ) :
        f a ∈ (TrackB.linearProjectivePlane U).points ↔ pairJoinEquiv e a.1 ∈ U := by
      rw [requestPairProjective_mem_plane_iff]
      rw [pairJoinEquiv_apply]
    have hQimage : Q.image Subtype.val = Λ.filter (fun l => pairJoinEquiv e l ∈ U) := by
      apply Finset.ext
      intro l
      rw [Finset.mem_image]
      change (∃ a : ↥Λ, a ∈ Q ∧ a.1 = l) ↔
        l ∈ Λ.filter (fun x => pairJoinEquiv e x ∈ U)
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact Finset.mem_filter.mpr ⟨a.2,
          (hplaneReq a).mp (Finset.mem_filter.mp ha).2⟩
      · intro hl
        rcases Finset.mem_filter.mp hl with ⟨hlΛ, hUmem⟩
        let a : ↥Λ := ⟨l, hlΛ⟩
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,
          (hplaneReq a).mpr hUmem⟩, rfl⟩
    have hQcard : Q.card = (Λ.filter (fun l => pairJoinEquiv e l ∈ U)).card := by
      calc
        Q.card = (Q.image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ = (Λ.filter (fun l => pairJoinEquiv e l ∈ U)).card := congrArg Finset.card hQimage
    have hPplane : P.filter (fun p => p ∈ (TrackB.linearProjectivePlane U).points) = Q.image f := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hpP, hplane⟩
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpP
        exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hplane⟩, rfl⟩
      · intro hp
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
        rcases Finset.mem_filter.mp ha with ⟨haΛ, hplane⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, haΛ, rfl⟩, hplane⟩
    have hset : ((P : Set (ProjectivePoint (e + e))) ∩
        (TrackB.linearProjectivePlane U).points) =
          (P.filter (fun p => p ∈ (TrackB.linearProjectivePlane U).points) : Set _) := by
      ext p
      simp
    have hcount :
        ((P : Set (ProjectivePoint (e + e))) ∩
          (TrackB.linearProjectivePlane U).points).ncard =
        (Λ.filter (fun l => pairJoinEquiv e l ∈ U)).card := by
      rw [hset, Set.ncard_coe_finset, hPplane,
        Finset.card_image_of_injective _ hf, hQcard]
    rw [hcount]
    exact hReqCap
  have hflatSubset (a : ↥Λ) :
      (TrackB.evaluationFlat C (f a) ⊆ Vb.points) ↔
        (skewToPoint '' evalFlat a.1.1 a.1.2 ⊆ V.points) := by
    constructor
    · intro hBflat z hz
      obtain ⟨x, hx⟩ := (pointReindexEquiv idx).surjective z
      change reindexPoint idx x = z at hx
      have hImage : reindexPoint idx x ∈ skewToPoint '' evalFlat a.1.1 a.1.2 := by
        rw [hx]
        exact hz
      have hxFlat : x ∈ TrackB.evaluationFlat C (f a) :=
        (evaluationFlat_coordinate_iff idx hpoint a.1 (hNZ a.1 a.2) x).2 hImage
      have hxVb : x ∈ Vb := hBflat hxFlat
      have hxV : reindexPoint idx x ∈ V :=
        (reindexAffineVariety_points idx V x).mp hxVb
      rw [hx] at hxV
      exact hxV
    · intro hEflat
      intro x hxFlat
      have hImage := (evaluationFlat_coordinate_iff idx hpoint a.1 (hNZ a.1 a.2) x).mp hxFlat
      have hxV : reindexPoint idx x ∈ V := hEflat hImage
      exact (reindexAffineVariety_points idx V x).mpr hxV
  let goodA : Finset (↥Λ) := Λ.attach.filter fun a =>
    skewToPoint '' evalFlat a.1.1 a.1.2 ⊆ V.points
  let goodR : Finset ((Fin e → ℂ) × (Fin e → ℂ)) :=
    Λ.filter fun l => skewToPoint '' evalFlat l.1 l.2 ⊆ V.points
  have hgoodVal : goodA.image Subtype.val = goodR := by
    apply Finset.ext
    intro l
    rw [Finset.mem_image]
    change (∃ a : ↥Λ, a ∈ goodA ∧ a.1 = l) ↔ l ∈ goodR
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Finset.mem_filter.mpr ⟨a.2, (Finset.mem_filter.mp ha).2⟩
    · intro hl
      rcases Finset.mem_filter.mp hl with ⟨hlΛ, hgood⟩
      let a : ↥Λ := ⟨l, hlΛ⟩
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hgood⟩, rfl⟩
  have hgoodP :
      P.filter (fun p => TrackB.evaluationFlat C p ⊆ Vb.points) = goodA.image f := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hflat⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpP
      exact Finset.mem_image.mpr ⟨a,
        Finset.mem_filter.mpr ⟨ha, (hflatSubset a).mp hflat⟩, rfl⟩
    · intro hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      rcases Finset.mem_filter.mp ha with ⟨haΛ, hflat⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, haΛ, rfl⟩,
        (hflatSubset a).mpr hflat⟩
  have hfiltered : (P.filter (fun p => TrackB.evaluationFlat C p ⊆ Vb.points)).card = goodR.card := by
    rw [hgoodP]
    calc
      (goodA.image f).card = goodA.card := Finset.card_image_of_injective _ hf
      _ = (goodA.image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = goodR.card := congrArg Finset.card hgoodVal
  have hcountFlats : (TrackB.containedFlatCount C P Vb : ℝ) = (goodR.card : ℝ) := by
    unfold TrackB.containedFlatCount
    exact_mod_cast hfiltered
  have hhB : h + 2 ≤ e := by omega
  cases hcase with
  | inl hcardSample =>
      have hPsample : (P.card : ℝ) ≤ C₀ * A ^ (e - 1) := by
        rw [hPcard]
        exact hcardSample
      have hallowed : TrackB.AllowedCarrier true A C₀ Vb :=
        ⟨hVb, hproper, Or.inl rfl⟩
      have hbound := hBmain C A hA P true hP hBsep hBcap
        (by intro _; exact hPsample) Vb h hallowed h₁ hhB hdimB
      rw [← hcountFlats, ← hDimDeg.2]
      exact hbound
  | inr hhyp =>
      obtain ⟨g, hg0, hgdeg, hgvan⟩ := hhyp
      have hgIdeal : g ∈ V.ideal := by
        rw [← V.vanishingIdeal_points]
        exact hgvan
      let r := MvPolynomial.renameEquiv ℂ idx
      let gB := r.symm g
      have hgB0 : gB ≠ 0 := by
        intro hzero
        apply hg0
        have hrename := congrArg r hzero
        simpa [gB] using hrename
      have hgBmem : gB ∈ Vb.ideal := by
        change gB ∈ V.ideal.comap (MvPolynomial.renameEquiv ℂ idx).toRingEquiv
        change MvPolynomial.renameEquiv ℂ idx gB ∈ V.ideal
        have hrename : MvPolynomial.renameEquiv ℂ idx gB = g := by
          change r (r.symm g) = g
          exact r.apply_symm_apply g
        rw [hrename]
        exact hgIdeal
      have hgBdeg : (gB.totalDegree : ℝ) ≤ C₀ * A := by
        have hdeg : gB.totalDegree = g.totalDegree := by
          change ((MvPolynomial.renameEquiv ℂ idx).symm g).totalDegree = g.totalDegree
          rw [MvPolynomial.renameEquiv_symm, MvPolynomial.totalDegree_renameEquiv]
        rw [hdeg]
        exact hgdeg
      have hallowed : TrackB.AllowedCarrier false A C₀ Vb :=
        ⟨hVb, hproper, Or.inr ⟨gB, hgB0, hgBmem, hgBdeg⟩⟩
      have hbound := hBmain C A hA P false hP hBsep hBcap (by simp)
        Vb h hallowed h₁ hhB hdimB
      rw [← hcountFlats, ← hDimDeg.2]
      exact hbound

/-- `red:global-concentration`, reduction.tex:348–384: case (a) of track B's
concentration theorem, including the base and ambient dimensions, in skew-matrix coordinates. -/
theorem uniform_concentration_all_dimensions_bridge {e : ℕ} (he : 3 ≤ e) :
    ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ), 1 ≤ A →
    ∀ Λ : Finset ((Fin e → ℂ) × (Fin e → ℂ)),
      (∀ l ∈ Λ, l.1 ≠ 0 ∧ ∑ i, l.2 i * l.1 i = 0) →
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ c : ℂ, l' = c • l → l' = l) →
      (∀ l ∈ Λ, ∃ (k : ℕ) (f : MvPolynomial (Fin e ⊕ Fin e) ℂ),
        1 ≤ k ∧ (k : ℝ) ≤ C₀ * A ∧ f.IsHomogeneous k ∧
        MvPolynomial.eval (Sum.elim l.1 l.2) f ≠ 0 ∧
        ∀ l' ∈ Λ, l' ≠ l → MvPolynomial.eval (Sum.elim l'.1 l'.2) f = 0) →
      (∀ L : Submodule ℂ ((Fin e → ℂ) × (Fin e → ℂ)), Module.finrank ℂ L = e →
        (∀ x ∈ L, ∀ x' ∈ L,
          ∑ i, (x.2 i * x'.1 i + x'.2 i * x.1 i) = 0) →
        ((Λ.filter (· ∈ L)).card : ℝ) ≤ C₀ * A ^ (e - 2)) →
      ∀ V : AffineVariety (Fintype.card (SkewIdx e)), V.IsIrreducible →
      ∀ h : ℕ, h ≤ e - 1 → V.dimension = Nat.choose (e - 1) 2 + h →
        (Λ.card : ℝ) ≤ C₀ * A ^ (e - 1) →
        ((Λ.filter fun l => skewToPoint '' evalFlat l.1 l.2 ⊆ V.points).card : ℝ) ≤
          C * (V.degree : ℝ) * A ^ h := by
  intro C₀ hC₀
  obtain ⟨B, hB, hBmain⟩ := TrackB.uniform_concentration_all_dimensions e he C₀ hC₀
  refine ⟨B, hB, ?_⟩
  intro A hA Λ hparams hprop hsep hcap V hV h hh hdim hcardSample
  let idx : Fin (e.choose 2) ≃ Fin (Fintype.card (SkewIdx e)) :=
    finCongr (card_skewIdx_bridge e).symm
  let Vb : AffineVariety (e.choose 2) := reindexAffineVariety idx V
  let C := uniformConcentrationCoordinates e
  have hpoint : ∀ x : Point (e.choose 2), reindexPoint idx x =
      skewToPoint (pointSkewEquiv e x) := by
    intro x
    funext i
    simp [reindexPoint, idx, skewToPoint, pointSkewEquiv]
  have hDimDeg := reindexAffineVariety_dimension_degree idx V
  have hVb : Vb.IsIrreducible := by
    letI : V.ideal.IsPrime := hV
    change (V.ideal.comap (MvPolynomial.renameEquiv ℂ idx).toRingEquiv).IsPrime
    exact Ideal.IsPrime.comap _
  have hdimB : Vb.dimension = Nat.choose (e - 1) 2 + h := hDimDeg.1.trans hdim
  have hNZ : ∀ l ∈ Λ, l.1 ≠ 0 := fun l hl => (hparams l hl).1
  let f : ↥Λ → ProjectivePoint (e + e) := fun a =>
    requestPairProjective e a.1 (hNZ a.1 a.2)
  let P : Finset (ProjectivePoint (e + e)) := Λ.attach.image f
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact requestPairProjective_injOn Λ hNZ hprop a.1 a.2 b.1 b.2 hab
  have hPcard : P.card = Λ.card := by
    dsimp [P]
    rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
  have hP : ∀ p ∈ P, p ∈ TrackB.affineParameters e := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact requestPairProjective_mem_affineParameters a.1 (hNZ a.1 a.2)
      (hparams a.1 a.2).2
  have hBsep : TrackB.HasSeparators P (C₀ * A) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨k, g, hk, hkD, hg, hgeval, hgzero⟩ := hsep a.1 a.2
    let gB := MvPolynomial.rename finSumFinEquiv g
    have hgB : gB.IsHomogeneous k := hg.rename_isHomogeneous
    have hEvalPair := eval_rename_pair a.1.1 a.1.2 g
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (TrackB.joinPoints a.1.1 a.1.2) (joinPoints_ne_zero e a.1.1 a.1.2
        (hNZ a.1 a.2))
    change (c : ℂ) • TrackB.joinPoints a.1.1 a.1.2 =
      (requestPairProjective e a.1 (hNZ a.1 a.2)).rep at hc
    have hEvalRep : MvPolynomial.eval
        (requestPairProjective e a.1 (hNZ a.1 a.2)).rep gB ≠ 0 := by
      rw [← hc, homogeneous_eval_smul gB hgB (c : ℂ) (TrackB.joinPoints a.1.1 a.1.2)]
      rw [hEvalPair]
      exact mul_ne_zero (pow_ne_zero k (Units.ne_zero c)) hgeval
    refine ⟨gB, k, hk, hkD, hgB, ?_, ?_⟩
    · simpa only [MvPolynomial.aeval_eq_eval] using hEvalRep
    · intro q hq hqp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
      have hba : b.1 ≠ a.1 := by
        intro hEq
        apply hqp
        exact congrArg f (Subtype.ext hEq)
      obtain ⟨c', hc'⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
        (TrackB.joinPoints b.1.1 b.1.2) (joinPoints_ne_zero e b.1.1 b.1.2
          (hNZ b.1 b.2))
      change (c' : ℂ) • TrackB.joinPoints b.1.1 b.1.2 =
        (requestPairProjective e b.1 (hNZ b.1 b.2)).rep at hc'
      have hzeroRep : MvPolynomial.eval
          (requestPairProjective e b.1 (hNZ b.1 b.2)).rep gB = 0 := by
        rw [← hc', homogeneous_eval_smul gB hgB (c' : ℂ) (TrackB.joinPoints b.1.1 b.1.2)]
        rw [eval_rename_pair, hgzero b.1 b.2 hba]
        simp
      simpa only [MvPolynomial.aeval_eq_eval] using hzeroRep
  have hBcap : TrackB.HasIsotropicCap P (C₀ * A ^ (e - 2)) := by
    intro U hU
    have hReqCap : ((Λ.filter fun l => pairJoinEquiv e l ∈ U).card : ℝ) ≤
        C₀ * A ^ (e - 2) := isotropicCap_filter_le Λ _ hcap U hU
    let Q : Finset (↥Λ) := Λ.attach.filter fun a =>
      f a ∈ (TrackB.linearProjectivePlane U).points
    have hplaneReq (a : ↥Λ) :
        f a ∈ (TrackB.linearProjectivePlane U).points ↔ pairJoinEquiv e a.1 ∈ U := by
      rw [requestPairProjective_mem_plane_iff]
      rw [pairJoinEquiv_apply]
    have hQimage : Q.image Subtype.val = Λ.filter (fun l => pairJoinEquiv e l ∈ U) := by
      apply Finset.ext
      intro l
      rw [Finset.mem_image]
      change (∃ a : ↥Λ, a ∈ Q ∧ a.1 = l) ↔
        l ∈ Λ.filter (fun x => pairJoinEquiv e x ∈ U)
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact Finset.mem_filter.mpr ⟨a.2,
          (hplaneReq a).mp (Finset.mem_filter.mp ha).2⟩
      · intro hl
        rcases Finset.mem_filter.mp hl with ⟨hlΛ, hUmem⟩
        let a : ↥Λ := ⟨l, hlΛ⟩
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,
          (hplaneReq a).mpr hUmem⟩, rfl⟩
    have hQcard : Q.card = (Λ.filter (fun l => pairJoinEquiv e l ∈ U)).card := by
      calc
        Q.card = (Q.image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ = (Λ.filter (fun l => pairJoinEquiv e l ∈ U)).card := congrArg Finset.card hQimage
    have hPplane : P.filter (fun p => p ∈ (TrackB.linearProjectivePlane U).points) = Q.image f := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hpP, hplane⟩
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpP
        exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hplane⟩, rfl⟩
      · intro hp
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
        rcases Finset.mem_filter.mp ha with ⟨haΛ, hplane⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, haΛ, rfl⟩, hplane⟩
    have hset : ((P : Set (ProjectivePoint (e + e))) ∩
        (TrackB.linearProjectivePlane U).points) =
          (P.filter (fun p => p ∈ (TrackB.linearProjectivePlane U).points) : Set _) := by
      ext p
      simp
    have hcount :
        ((P : Set (ProjectivePoint (e + e))) ∩
          (TrackB.linearProjectivePlane U).points).ncard =
        (Λ.filter (fun l => pairJoinEquiv e l ∈ U)).card := by
      rw [hset, Set.ncard_coe_finset, hPplane,
        Finset.card_image_of_injective _ hf, hQcard]
    rw [hcount]
    exact hReqCap
  have hflatSubset (a : ↥Λ) :
      (TrackB.evaluationFlat C (f a) ⊆ Vb.points) ↔
        (skewToPoint '' evalFlat a.1.1 a.1.2 ⊆ V.points) := by
    constructor
    · intro hBflat z hz
      obtain ⟨x, hx⟩ := (pointReindexEquiv idx).surjective z
      change reindexPoint idx x = z at hx
      have hImage : reindexPoint idx x ∈ skewToPoint '' evalFlat a.1.1 a.1.2 := by
        rw [hx]
        exact hz
      have hxFlat : x ∈ TrackB.evaluationFlat C (f a) :=
        (evaluationFlat_coordinate_iff idx hpoint a.1 (hNZ a.1 a.2) x).2 hImage
      have hxVb : x ∈ Vb := hBflat hxFlat
      have hxV : reindexPoint idx x ∈ V :=
        (reindexAffineVariety_points idx V x).mp hxVb
      rw [hx] at hxV
      exact hxV
    · intro hEflat
      intro x hxFlat
      have hImage := (evaluationFlat_coordinate_iff idx hpoint a.1 (hNZ a.1 a.2) x).mp hxFlat
      have hxV : reindexPoint idx x ∈ V := hEflat hImage
      exact (reindexAffineVariety_points idx V x).mpr hxV
  let goodA : Finset (↥Λ) := Λ.attach.filter fun a =>
    skewToPoint '' evalFlat a.1.1 a.1.2 ⊆ V.points
  let goodR : Finset ((Fin e → ℂ) × (Fin e → ℂ)) :=
    Λ.filter fun l => skewToPoint '' evalFlat l.1 l.2 ⊆ V.points
  have hgoodVal : goodA.image Subtype.val = goodR := by
    apply Finset.ext
    intro l
    rw [Finset.mem_image]
    change (∃ a : ↥Λ, a ∈ goodA ∧ a.1 = l) ↔ l ∈ goodR
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Finset.mem_filter.mpr ⟨a.2, (Finset.mem_filter.mp ha).2⟩
    · intro hl
      rcases Finset.mem_filter.mp hl with ⟨hlΛ, hgood⟩
      let a : ↥Λ := ⟨l, hlΛ⟩
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hgood⟩, rfl⟩
  have hgoodP :
      P.filter (fun p => TrackB.evaluationFlat C p ⊆ Vb.points) = goodA.image f := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hflat⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpP
      exact Finset.mem_image.mpr ⟨a,
        Finset.mem_filter.mpr ⟨ha, (hflatSubset a).mp hflat⟩, rfl⟩
    · intro hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      rcases Finset.mem_filter.mp ha with ⟨haΛ, hflat⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, haΛ, rfl⟩,
        (hflatSubset a).mpr hflat⟩
  have hfiltered : (P.filter (fun p => TrackB.evaluationFlat C p ⊆ Vb.points)).card = goodR.card := by
    rw [hgoodP]
    calc
      (goodA.image f).card = goodA.card := Finset.card_image_of_injective _ hf
      _ = (goodA.image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = goodR.card := congrArg Finset.card hgoodVal
  have hcountFlats : (TrackB.containedFlatCount C P Vb : ℝ) = (goodR.card : ℝ) := by
    unfold TrackB.containedFlatCount
    exact_mod_cast hfiltered
  have hPsample : (P.card : ℝ) ≤ C₀ * A ^ (e - 1) := by
    rw [hPcard]
    exact hcardSample
  have hbound := hBmain C A hA P hP hBsep hBcap hPsample Vb h hVb hh hdimB
  rw [← hcountFlats, ← hDimDeg.2]
  exact hbound

end
end DistinctDistances.Bridges
