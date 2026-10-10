import DistinctDistances.TrackE.PairFlats
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Helpers for the ambient form of local concentration. -/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

def ambientSkewMatrixPoly (i j : Fin d) : MvPolynomial (SkewIdx d) ℂ :=
  if h : i < j then MvPolynomial.X ⟨(i, j), h⟩
  else if h : j < i then -MvPolynomial.X ⟨(j, i), h⟩ else 0

def ambientSection (p q : RPoint d) (Z : SkewIdx d → ℂ) :
    SkewIdx (d + 1) → ℂ := fun ij =>
  let hi : ij.1.1 ≠ Fin.last d :=
    Fin.ne_of_lt (lt_of_lt_of_le ij.2 (Fin.le_last _))
  if hj : ij.1.2 = Fin.last d then
    cplx (pairHalfDiff p q) (ij.1.1.castPred hi) -
      (skewMatrix Z).mulVec (cplx (pairMid p q)) (ij.1.1.castPred hi)
  else
    Z ⟨(ij.1.1.castPred hi, ij.1.2.castPred hj),
      (Fin.castPred_lt_castPred_iff (hi := hi) (hj := hj)).2 ij.2⟩

def ambientVarLift (p q : RPoint d) (ij : SkewIdx (d + 1)) :
    MvPolynomial (SkewIdx d) ℂ :=
  let hi : ij.1.1 ≠ Fin.last d :=
    Fin.ne_of_lt (lt_of_lt_of_le ij.2 (Fin.le_last _))
  if hj : ij.1.2 = Fin.last d then
    MvPolynomial.C (cplx (pairHalfDiff p q) (ij.1.1.castPred hi)) -
      ∑ j : Fin d, MvPolynomial.C (cplx (pairMid p q) j) *
        ambientSkewMatrixPoly (ij.1.1.castPred hi) j
  else
    MvPolynomial.X ⟨(ij.1.1.castPred hi, ij.1.2.castPred hj),
      (Fin.castPred_lt_castPred_iff (hi := hi) (hj := hj)).2 ij.2⟩

lemma zBlock_ambientSection (p q : RPoint d) (Z : SkewIdx d → ℂ) :
    zBlock (ambientSection p q Z) = Z := by
  funext ij
  simp [zBlock, ambientSection, Fin.castPred_castSucc]

lemma ambientSection_lastColumn (p q : RPoint d) (Z : SkewIdx d → ℂ)
    (i : Fin d) :
    ambientSection p q Z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩ =
      cplx (pairHalfDiff p q) i -
        (skewMatrix Z).mulVec (cplx (pairMid p q)) i := by
  simp [ambientSection]

lemma ambientSection_mem_pairFlat (p q : RPoint d) (Z : SkewIdx d → ℂ) :
    ambientSection p q Z ∈ pairFlat p q := by
  rw [mem_pairFlat_iff]
  rw [zBlock_ambientSection]
  ext i
  simp only [Pi.add_apply]
  rw [ambientSection_lastColumn]
  ring

lemma ambientSection_eq_of_mem_pairFlat (p q : RPoint d)
    (z : SkewIdx (d + 1) → ℂ) (hz : z ∈ pairFlat p q) :
    ambientSection p q (zBlock z) = z := by
  have hz' := (mem_pairFlat_iff p q z).mp hz
  funext ij
  let hi : ij.1.1 ≠ Fin.last d :=
    Fin.ne_of_lt (lt_of_lt_of_le ij.2 (Fin.le_last _))
  by_cases hj : ij.1.2 = Fin.last d
  · have heq := congrFun hz' (ij.1.1.castPred hi)
    have hidx : ij = ⟨((ij.1.1.castPred hi).castSucc, Fin.last d),
        Fin.castSucc_lt_last (ij.1.1.castPred hi)⟩ := by
      apply Subtype.ext
      exact Prod.ext (Fin.castSucc_castPred _ hi) hj
    have hsame :
        (⟨((ij.1.1.castPred hi).castSucc, Fin.last d),
          Fin.castSucc_lt_last (ij.1.1.castPred hi)⟩ : SkewIdx (d + 1)) =
        ⟨(ij.1.1, Fin.last d), lt_of_lt_of_le ij.2 (Fin.le_last _)⟩ := by
      apply Subtype.ext
      exact Prod.ext (Fin.castSucc_castPred _ hi) rfl
    rw [hidx]
    simp [ambientSection]
    rw [← congrArg z hsame]
    have hcoord := heq
    simp only [Pi.add_apply] at hcoord
    linear_combination -hcoord
  · have hleft : Fin.castSucc (ij.1.1.castPred hi) = ij.1.1 :=
      Fin.castSucc_castPred _ hi
    have hright : Fin.castSucc (ij.1.2.castPred hj) = ij.1.2 :=
      Fin.castSucc_castPred _ hj
    simp [ambientSection, hj, zBlock, hleft, hright]

lemma eval_ambientSkewMatrixPoly (Z : SkewIdx d → ℂ) (i j : Fin d) :
    MvPolynomial.eval Z (ambientSkewMatrixPoly i j) = skewMatrix Z i j := by
  by_cases hij : i < j
  · simp [ambientSkewMatrixPoly, skewMatrix, hij]
  · by_cases hji : j < i
    · simp [ambientSkewMatrixPoly, skewMatrix, hij, hji]
    · have hij' : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp [ambientSkewMatrixPoly, skewMatrix, hij, hji]

lemma eval_ambientVarLift (p q : RPoint d) (Z : SkewIdx d → ℂ)
    (ij : SkewIdx (d + 1)) :
    MvPolynomial.eval Z (ambientVarLift p q ij) = ambientSection p q Z ij := by
  let hi : ij.1.1 ≠ Fin.last d :=
    Fin.ne_of_lt (lt_of_lt_of_le ij.2 (Fin.le_last _))
  by_cases hj : ij.1.2 = Fin.last d
  · simp [ambientVarLift, ambientSection, hj, eval_ambientSkewMatrixPoly,
      Matrix.mulVec, dotProduct, mul_comm]
  · simp [ambientVarLift, ambientSection, hj, Fin.castPred_castSucc]

lemma ambientSkewMatrixPoly_degree (i j : Fin d) :
    (ambientSkewMatrixPoly i j).totalDegree ≤ 1 := by
  by_cases hij : i < j
  · simp [ambientSkewMatrixPoly, hij]
  · by_cases hji : j < i
    · simp [ambientSkewMatrixPoly, hij, hji]
    · simp [ambientSkewMatrixPoly, hij, hji]

lemma ambientLinearEntry_degree (p q : RPoint d) (i : Fin d) :
    (∑ j : Fin d, MvPolynomial.C (cplx (pairMid p q) j) *
      ambientSkewMatrixPoly i j).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  calc
    (MvPolynomial.C (cplx (pairMid p q) j) * ambientSkewMatrixPoly i j).totalDegree ≤
        (MvPolynomial.C (cplx (pairMid p q) j)).totalDegree +
          (ambientSkewMatrixPoly i j).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + 1 := add_le_add (by simp) (ambientSkewMatrixPoly_degree i j)
    _ = 1 := by norm_num

lemma ambientVarLift_degree (p q : RPoint d) (ij : SkewIdx (d + 1)) :
    (ambientVarLift p q ij).totalDegree ≤ 1 := by
  let hi : ij.1.1 ≠ Fin.last d :=
    Fin.ne_of_lt (lt_of_lt_of_le ij.2 (Fin.le_last _))
  by_cases hj : ij.1.2 = Fin.last d
  · simp only [ambientVarLift, hj]
    calc
      (MvPolynomial.C (cplx (pairHalfDiff p q) (ij.1.1.castPred hi)) -
          ∑ j : Fin d, MvPolynomial.C (cplx (pairMid p q) j) *
            ambientSkewMatrixPoly (ij.1.1.castPred hi) j).totalDegree ≤
          max 0 (∑ j : Fin d, MvPolynomial.C (cplx (pairMid p q) j) *
            ambientSkewMatrixPoly (ij.1.1.castPred hi) j).totalDegree :=
        (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) le_rfl)
      _ ≤ 1 := max_le (by omega) (ambientLinearEntry_degree p q _)
  · simp [ambientVarLift, hj]

lemma totalDegree_bind₁_le_of_vars_le_one {σ τ : Type*}
    (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (f : MvPolynomial σ ℂ) : (MvPolynomial.bind₁ g f).totalDegree ≤ f.totalDegree := by
  classical
  have hsum : MvPolynomial.bind₁ g f =
      ∑ m ∈ f.support, MvPolynomial.bind₁ g (MvPolynomial.monomial m (f.coeff m)) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
  rw [hsum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  rw [MvPolynomial.bind₁_monomial]
  by_cases hc : f.coeff m = 0
  · simp [hc]
  ·
    calc
      (MvPolynomial.C (f.coeff m) * ∏ i ∈ m.support, g i ^ m i).totalDegree ≤
          (MvPolynomial.C (f.coeff m)).totalDegree +
            (∏ i ∈ m.support, g i ^ m i).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + ∑ i ∈ m.support, (g i ^ m i).totalDegree :=
        add_le_add (by simp) (MvPolynomial.totalDegree_finsetProd _ _)
      _ ≤ ∑ i ∈ m.support, m i := by
        simp only [zero_add]
        apply Finset.sum_le_sum
        intro i hi
        simpa using (MvPolynomial.totalDegree_pow (g i) (m i)).trans
          (Nat.mul_le_mul_left (m i) (hg i))
      _ = m.sum fun _ e => e := by simp [Finsupp.sum]
      _ ≤ f.totalDegree := MvPolynomial.le_totalDegree hm

lemma ambientSection_eq_fun_eval (p q : RPoint d) (Z : SkewIdx d → ℂ)
    (f : MvPolynomial (SkewIdx (d + 1)) ℂ) :
    MvPolynomial.eval Z (MvPolynomial.bind₁ (ambientVarLift p q) f) =
      MvPolynomial.eval (ambientSection p q Z) f := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) Z
      (MvPolynomial.bind₁ (ambientVarLift p q) f) =
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (ambientSection p q Z) f
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply congrArg (fun h : SkewIdx (d + 1) → ℂ =>
    MvPolynomial.eval₂Hom (RingHom.id ℂ) h f)
  funext ij
  exact eval_ambientVarLift p q Z ij

end Reduction

end

end DistinctDistances
