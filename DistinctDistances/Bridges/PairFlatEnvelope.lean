import DistinctDistances.TrackE.SkewPoint
import OAI.NumberTheory.PowerFree.HilbertGrowth
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
Envelope components carrying the physical pair flats.

Each pair flat is the graph of an affine function of its free `Z`-block, a copy of
affine space of dimension `C(d, 2)`. The `D`-envelope of those graphs is the reduced
locus of its degree-at-most-`D` equations, so the irreducible components of that
locus are defined in degree `D` and cover it. A whole flat lies in one component,
and the free coordinates stay algebraically independent there, so the component
has dimension at least `C(d, 2)`.
-/

namespace DistinctDistances.Bridges

noncomputable section
open scoped BigOperators Classical Matrix
open Reduction

variable {d : ℕ}

lemma card_skewIdx (d : ℕ) : Fintype.card (SkewIdx d) = Nat.choose d 2 := by
  classical
  change Fintype.card {ij : Fin d × Fin d // ij.1 < ij.2} = Nat.choose d 2
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin d))

def skewEmbed (ij : SkewIdx d) : SkewIdx (d + 1) :=
  ⟨(ij.1.1.castSucc, ij.1.2.castSucc), by simpa using ij.2⟩

def zIndex (d : ℕ) (ij : SkewIdx d) : Fin (Nat.choose d 2) :=
  Fin.cast (card_skewIdx d) ((Fintype.equivFin (SkewIdx d)) ij)

def zCoord (d : ℕ) (a : Fin (Nat.choose d 2)) : Fin (Fintype.card (SkewIdx (d + 1))) :=
  Fintype.equivFin (SkewIdx (d + 1))
    (skewEmbed ((Fintype.equivFin (SkewIdx d)).symm (Fin.cast (card_skewIdx d).symm a)))

def pointZ (t : Point (Nat.choose d 2)) : SkewIdx d → ℂ :=
  fun ij => t (zIndex d ij)

def zPoint (Z : SkewIdx d → ℂ) : Point (Nat.choose d 2) :=
  fun a => Z ((Fintype.equivFin (SkewIdx d)).symm (Fin.cast (card_skewIdx d).symm a))

lemma pointZ_zPoint (Z : SkewIdx d → ℂ) : pointZ (zPoint Z) = Z := by
  funext ij
  simp only [pointZ, zPoint, zIndex]
  rw [Fin.leftInverse_cast (card_skewIdx d), Equiv.symm_apply_apply]

lemma zPoint_pointZ (t : Point (Nat.choose d 2)) : zPoint (pointZ t) = t := by
  funext a
  simp only [zPoint, pointZ, zIndex]
  rw [Equiv.apply_symm_apply, Fin.rightInverse_cast (card_skewIdx d)]

/-- `a.1.1` is not the last basis index when `a` records an entry of the last column. -/
lemma extendFirstNe {a : SkewIdx (d + 1)} (h : a.1.2 = Fin.last d) : a.1.1 ≠ Fin.last d :=
  ne_of_lt (show a.1.1 < Fin.last d by simpa [h] using a.2)

lemma extendElseNe (a : SkewIdx (d + 1)) : a.1.1 ≠ Fin.last d :=
  Fin.ne_of_lt (Fin.lt_of_lt_of_le a.2 (Fin.le_last _))

/-- Extend a `Z`-block by a last column to a skew form on `ℂ^{d+1}`. -/
def extendPairFlatCoordinates (Z : SkewIdx d → ℂ) (c : Fin d → ℂ) (a : SkewIdx (d + 1)) : ℂ :=
  if h : a.1.2 = Fin.last d then
    c (a.1.1.castPred (extendFirstNe h))
  else
    Z ⟨(a.1.1.castPred (extendElseNe a), a.1.2.castPred h),
      (Fin.castPred_lt_castPred_iff (hi := extendElseNe a) (hj := h)).2 a.2⟩

lemma zBlock_extendPairFlatCoordinates (Z : SkewIdx d → ℂ) (c : Fin d → ℂ) :
    zBlock (extendPairFlatCoordinates Z c) = Z := by
  funext ij
  have hlast : (ij.1.2.castSucc : Fin (d + 1)) ≠ Fin.last d := (Fin.castSucc_lt_last ij.1.2).ne
  rw [zBlock, extendPairFlatCoordinates, dite_eq_right hlast]
  apply congrArg Z
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    rw [Fin.coe_castPred, Fin.val_castSucc]
  · apply Fin.ext
    rw [Fin.coe_castPred, Fin.val_castSucc]

lemma lastColumn_extendPairFlatCoordinates (Z : SkewIdx d → ℂ) (c : Fin d → ℂ) (i : Fin d) :
    extendPairFlatCoordinates Z c ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩ = c i := by
  rw [extendPairFlatCoordinates, dite_eq_left rfl]
  apply congrArg c
  apply Fin.ext
  rw [Fin.coe_castPred, Fin.val_castSucc]

lemma eq_extend_zBlock_lastColumn (z : SkewIdx (d + 1) → ℂ) :
    extendPairFlatCoordinates (zBlock z)
      (fun i => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) = z := by
  funext a
  by_cases h : a.1.2 = Fin.last d
  · rw [extendPairFlatCoordinates, dite_eq_left h]
    apply congrArg z
    apply Subtype.ext
    apply Prod.ext
    · exact (Fin.castSucc_castPred a.1.1 (extendFirstNe h)).symm
    · exact h.symm
  · rw [extendPairFlatCoordinates, dite_eq_right h, zBlock]
    apply congrArg z
    apply Subtype.ext
    apply Prod.ext
    · exact (Fin.castSucc_castPred a.1.1 (extendElseNe a)).symm
    · exact (Fin.castSucc_castPred a.1.2 h).symm

def pairFlatLift (p q : RPoint d) (Z : SkewIdx d → ℂ) : SkewIdx (d + 1) → ℂ :=
  extendPairFlatCoordinates Z
    (cplx (pairHalfDiff p q) - (skewMatrix Z).mulVec (cplx (pairMid p q)))

lemma pairFlatLift_mem (p q : RPoint d) (Z : SkewIdx d → ℂ) :
    pairFlatLift p q Z ∈ pairFlat p q := by
  apply (mem_pairFlat_iff p q _).mpr
  unfold pairFlatLift
  rw [zBlock_extendPairFlatCoordinates]
  have hcols : (fun i : Fin d => extendPairFlatCoordinates Z
      (cplx (pairHalfDiff p q) - (skewMatrix Z).mulVec (cplx (pairMid p q)))
      ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) =
      cplx (pairHalfDiff p q) - (skewMatrix Z).mulVec (cplx (pairMid p q)) := by
    funext i
    exact lastColumn_extendPairFlatCoordinates Z _ i
  rw [hcols]
  funext i
  simp [Pi.add_apply, Pi.sub_apply]

lemma mem_eq_pairFlatLift (p q : RPoint d) {z : SkewIdx (d + 1) → ℂ} (hz : z ∈ pairFlat p q) :
    z = pairFlatLift p q (zBlock z) := by
  have hc : (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) =
      cplx (pairHalfDiff p q) - (skewMatrix (zBlock z)).mulVec (cplx (pairMid p q)) := by
    funext i
    have hi := congrFun ((mem_pairFlat_iff p q z).mp hz) i
    rw [Pi.add_apply, add_comm] at hi
    rw [Pi.sub_apply]
    exact eq_sub_of_add_eq hi
  calc
    z = extendPairFlatCoordinates (zBlock z)
        (fun i => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) :=
      (eq_extend_zBlock_lastColumn z).symm
    _ = extendPairFlatCoordinates (zBlock z)
        (cplx (pairHalfDiff p q) - (skewMatrix (zBlock z)).mulVec (cplx (pairMid p q))) :=
      congrArg _ hc
    _ = pairFlatLift p q (zBlock z) := rfl

def pairFlatPoint (p q : RPoint d) (t : Point (Nat.choose d 2)) :
    Point (Fintype.card (SkewIdx (d + 1))) :=
  skewToPoint (pairFlatLift p q (pointZ t))

lemma pairFlatPoint_zCoord (p q : RPoint d) (t : Point (Nat.choose d 2))
    (a : Fin (Nat.choose d 2)) :
    pairFlatPoint p q t (zCoord d a) = t a := by
  have hblock := congrFun
    (zBlock_extendPairFlatCoordinates (pointZ t)
      (cplx (pairHalfDiff p q) - (skewMatrix (pointZ t)).mulVec (cplx (pairMid p q))))
    ((Fintype.equivFin (SkewIdx d)).symm (Fin.cast (card_skewIdx d).symm a))
  simp only [zBlock] at hblock
  calc
    pairFlatPoint p q t (zCoord d a) =
        pairFlatLift p q (pointZ t) (skewEmbed
          ((Fintype.equivFin (SkewIdx d)).symm (Fin.cast (card_skewIdx d).symm a))) := by
      simp only [pairFlatPoint, skewToPoint, zCoord, Equiv.symm_apply_apply]
    _ = pointZ t ((Fintype.equivFin (SkewIdx d)).symm (Fin.cast (card_skewIdx d).symm a)) := hblock
    _ = t a := by
      simp only [pointZ, zIndex]
      rw [Equiv.apply_symm_apply, Fin.rightInverse_cast (card_skewIdx d)]

def skewMatrixPoly {m : ℕ} (Z : SkewIdx d → Poly m) : Matrix (Fin d) (Fin d) (Poly m) :=
  fun i j =>
    if h : i < j then Z ⟨(i, j), h⟩
    else if h' : j < i then -Z ⟨(j, i), h'⟩
    else 0

lemma aeval_skewMatrixPoly {m : ℕ} (t : Point m) (Z : SkewIdx d → Poly m) (i j : Fin d) :
    MvPolynomial.aeval t (skewMatrixPoly Z i j) =
      skewMatrix (fun ij => MvPolynomial.aeval t (Z ij)) i j := by
  unfold skewMatrixPoly skewMatrix
  split_ifs <;> simp

def extendPoly {m : ℕ} (Z : SkewIdx d → Poly m) (c : Fin d → Poly m) (a : SkewIdx (d + 1)) :
    Poly m :=
  if h : a.1.2 = Fin.last d then
    c (a.1.1.castPred (extendFirstNe h))
  else
    Z ⟨(a.1.1.castPred (extendElseNe a), a.1.2.castPred h),
      (Fin.castPred_lt_castPred_iff (hi := extendElseNe a) (hj := h)).2 a.2⟩

lemma aeval_extendPoly {m : ℕ} (t : Point m) (Z : SkewIdx d → Poly m) (c : Fin d → Poly m)
    (a : SkewIdx (d + 1)) :
    MvPolynomial.aeval t (extendPoly Z c a) =
      extendPairFlatCoordinates (fun ij => MvPolynomial.aeval t (Z ij))
        (fun i => MvPolynomial.aeval t (c i)) a := by
  unfold extendPoly extendPairFlatCoordinates
  split_ifs <;> rfl

def lastColumnPoly (p q : RPoint d) (i : Fin d) : Poly (Nat.choose d 2) :=
  MvPolynomial.C (cplx (pairHalfDiff p q) i) -
    ((skewMatrixPoly (fun ij => MvPolynomial.X (zIndex d ij))).mulVec
      (fun j => MvPolynomial.C (cplx (pairMid p q) j))) i

lemma aeval_lastColumnPoly (p q : RPoint d) (t : Point (Nat.choose d 2)) (i : Fin d) :
    MvPolynomial.aeval t (lastColumnPoly p q i) =
      (cplx (pairHalfDiff p q) -
        (skewMatrix (pointZ t)).mulVec (cplx (pairMid p q))) i := by
  have hrow : MvPolynomial.aeval t
      (((skewMatrixPoly (fun ij => MvPolynomial.X (zIndex d ij))).mulVec
        (fun j => MvPolynomial.C (cplx (pairMid p q) j))) i) =
      ((skewMatrix (pointZ t)).mulVec (cplx (pairMid p q))) i := by
    rw [Matrix.mulVec_apply_eq_sum, map_sum, Matrix.mulVec_apply_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_mul, MvPolynomial.aeval_C, aeval_skewMatrixPoly]
    have hfun : (fun ij =>
        MvPolynomial.aeval t (MvPolynomial.X (zIndex d ij) : Poly (Nat.choose d 2))) = pointZ t := by
      funext ij
      simp [pointZ, MvPolynomial.aeval_X]
    rw [hfun, Algebra.algebraMap_self_apply]
  rw [lastColumnPoly, map_sub, MvPolynomial.aeval_C, hrow, Pi.sub_apply,
    Algebra.algebraMap_self_apply]

def pairFlatCoordPoly (p q : RPoint d) (i : Fin (Fintype.card (SkewIdx (d + 1)))) :
    Poly (Nat.choose d 2) :=
  extendPoly (fun ij => MvPolynomial.X (zIndex d ij)) (lastColumnPoly p q)
    ((Fintype.equivFin (SkewIdx (d + 1))).symm i)

lemma aeval_pairFlatCoordPoly (p q : RPoint d) (t : Point (Nat.choose d 2))
    (i : Fin (Fintype.card (SkewIdx (d + 1)))) :
    MvPolynomial.aeval t (pairFlatCoordPoly p q i) = pairFlatPoint p q t i := by
  unfold pairFlatCoordPoly pairFlatPoint skewToPoint
  rw [aeval_extendPoly]
  refine congrArg₂ (fun Z c => extendPairFlatCoordinates Z c
      ((Fintype.equivFin (SkewIdx (d + 1))).symm i)) ?_ ?_
  · funext ij
    simp [pointZ, MvPolynomial.aeval_X]
  · funext j
    exact aeval_lastColumnPoly p q t j

lemma coordPoly_zCoord (p q : RPoint d) (a : Fin (Nat.choose d 2)) :
    pairFlatCoordPoly p q (zCoord d a) = MvPolynomial.X a := by
  apply MvPolynomial.funext
  intro t
  change MvPolynomial.aeval t (pairFlatCoordPoly p q (zCoord d a)) =
    MvPolynomial.aeval t (MvPolynomial.X a)
  rw [aeval_pairFlatCoordPoly, pairFlatPoint_zCoord, MvPolynomial.aeval_X]

def pairFlatPullback (p q : RPoint d) :
    Poly (Fintype.card (SkewIdx (d + 1))) →ₐ[ℂ] Poly (Nat.choose d 2) :=
  MvPolynomial.aeval (pairFlatCoordPoly p q)

lemma pairFlatPullback_rename (p q : RPoint d) :
    (pairFlatPullback p q).comp (MvPolynomial.rename (zCoord d)) =
      AlgHom.id ℂ (Poly (Nat.choose d 2)) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, pairFlatPullback,
    MvPolynomial.rename_X, MvPolynomial.aeval_X]
  exact coordPoly_zCoord p q a

lemma pairFlat_vanishingIdeal_eq_ker (p q : RPoint d) :
    MvPolynomial.vanishingIdeal ℂ (skewToPoint '' pairFlat p q) =
      RingHom.ker (pairFlatPullback p q).toRingHom := by
  ext f
  constructor
  · intro hf
    apply MvPolynomial.funext
    intro t
    change MvPolynomial.aeval t (pairFlatPullback p q f) = 0
    rw [pairFlatPullback, MvPolynomial.comp_aeval_apply]
    have hcoord : (fun i => MvPolynomial.aeval t (pairFlatCoordPoly p q i)) =
        pairFlatPoint p q t := by
      funext i
      exact aeval_pairFlatCoordPoly p q t i
    rw [hcoord]
    have hmem : pairFlatLift p q (pointZ t) ∈ pairFlat p q := pairFlatLift_mem p q (pointZ t)
    have hvan := (MvPolynomial.mem_vanishingIdeal_iff.mp hf)
      (skewToPoint (pairFlatLift p q (pointZ t))) ⟨_, hmem, rfl⟩
    simpa [pairFlatPoint] using hvan
  · intro hf x hx
    obtain ⟨z, hz, rfl⟩ := hx
    let t : Point (Nat.choose d 2) := zPoint (zBlock z)
    have ht : pairFlatPoint p q t = skewToPoint z := by
      rw [mem_eq_pairFlatLift p q hz, pairFlatPoint, pointZ_zPoint]
    rw [← ht]
    have h0 : MvPolynomial.aeval t (pairFlatPullback p q f) = 0 := by
      simpa [pairFlatPullback] using congrArg (MvPolynomial.aeval t) hf
    rw [pairFlatPullback, MvPolynomial.comp_aeval_apply] at h0
    have hcoord : (fun i => MvPolynomial.aeval t (pairFlatCoordPoly p q i)) =
        pairFlatPoint p q t := by
      funext i
      exact aeval_pairFlatCoordPoly p q t i
    rw [hcoord] at h0
    exact h0

lemma pairFlat_vanishingIdeal_prime (p q : RPoint d) :
    (MvPolynomial.vanishingIdeal ℂ (skewToPoint '' pairFlat p q)).IsPrime := by
  rw [pairFlat_vanishingIdeal_eq_ker]
  exact RingHom.ker_isPrime _

lemma zCoord_algebraicIndependent (p q : RPoint d)
    (I : Ideal (Poly (Fintype.card (SkewIdx (d + 1)))))
    (hI : I ≤ MvPolynomial.vanishingIdeal ℂ (skewToPoint '' pairFlat p q)) :
    AlgebraicIndependent ℂ
      (fun a : Fin (Nat.choose d 2) => Ideal.Quotient.mk I (MvPolynomial.X (zCoord d a))) := by
  rw [algebraicIndependent_iff]
  intro r hr
  have he : MvPolynomial.aeval
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (zCoord d a))) =
      (Ideal.Quotient.mkₐ ℂ I).comp (MvPolynomial.rename (zCoord d)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp
  rw [he] at hr
  have hmem : MvPolynomial.rename (zCoord d) r ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hr
  have hker : pairFlatPullback p q (MvPolynomial.rename (zCoord d) r) = 0 := by
    have hvan := hI hmem
    rw [pairFlat_vanishingIdeal_eq_ker] at hvan
    exact hvan
  have hid := congrArg (fun φ : Poly (Nat.choose d 2) →ₐ[ℂ] Poly (Nat.choose d 2) => φ r)
    (pairFlatPullback_rename p q)
  simpa [hker] using hid.symm

/-- The binomial polynomial `(T + k).choose k`, of degree `k`. -/
def chooseBinomial (k : ℕ) : Polynomial ℚ :=
  Polynomial.C ((k.factorial : ℚ)⁻¹) *
    (ascPochhammer ℚ k).comp (Polynomial.X + Polynomial.C 1)

lemma chooseBinomial_natDegree (k : ℕ) : (chooseBinomial k).natDegree = k := by
  rw [chooseBinomial, Polynomial.natDegree_C_mul, Polynomial.natDegree_comp,
    ascPochhammer_natDegree, Polynomial.natDegree_X_add_C, mul_one]
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))

lemma chooseBinomial_eval (k T : ℕ) :
    (chooseBinomial k).eval (T : ℚ) = ((T + k).choose k : ℚ) := by
  rw [chooseBinomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  have hinner : (Polynomial.X + Polynomial.C (1 : ℚ)).eval (T : ℚ) = ((T + 1 : ℕ) : ℚ) := by
    simp [Polynomial.eval_add, Polynomial.eval_X, Nat.cast_add]
  rw [hinner, ascPochhammer_nat_eq_natCast_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  exact inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) _

lemma affineDimension_ge_of_independent_coordinates {n h : ℕ} (V : AffineVariety n)
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent ℂ (fun a => Ideal.Quotient.mk V.ideal (MvPolynomial.X (j a)))) :
    h ≤ V.dimension := by
  have hdeg := OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds (chooseBinomial h)
    V.hilbertPolynomial
    (Filter.Eventually.of_forall fun T => by
      rw [chooseBinomial_eval]
      exact_mod_cast Nat.zero_le ((T + h).choose h))
    (by
      filter_upwards [V.hilbert_eventually] with T hT
      rw [chooseBinomial_eval, ← hT]
      exact_mod_cast OAI.QuarticPowerFree.independent_coordinates_hilbert_lower V.ideal j hj T)
  rw [chooseBinomial_natDegree] at hdeg
  simpa [AffineVariety.dimension, AffineVariety.hilbertPolynomial,
    OAI.QuarticPowerFree.affineDimension] using hdeg

def envelopeComponents {n : ℕ} (T : Set (Point n)) (D : ℕ) : AffineFamily.Family n :=
  Finset.univ.image (fun W : (envelope T D).Component => W.variety)

lemma subset_envelope {n : ℕ} (T : Set (Point n)) (D : ℕ) : T ⊆ (envelope T D).points := by
  have hspan : Ideal.span {f : Poly n | f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D} ≤
      MvPolynomial.vanishingIdeal ℂ T := by
    apply Ideal.span_le.mpr
    intro f hf
    exact hf.1
  rw [envelope, AffineVariety.points_ofIdeal]
  intro x hx f hf
  exact hspan hf x hx

lemma envelope_components_defined {n : ℕ} (T : Set (Point n)) (D : ℕ)
    (F : AffineFamily.Family n) (hF : F ⊆ envelopeComponents T D) :
    AffineFamily.ComponentsDefinedInDegree F D := by
  refine ⟨{f : Poly n | f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D},
    (fun f hf => hf.2), ?_⟩
  intro V hV
  obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp (hF hV)
  change W.val ∈ (Ideal.span {f : Poly n |
    f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D}).minimalPrimes
  simpa only [envelope, AffineVariety.ofIdeal, Ideal.radical_minimalPrimes] using W.property

lemma component_family_locus {n : ℕ} (V : AffineVariety n) :
    AffineFamily.locus (Finset.univ.image (fun W : V.Component => W.variety)) = V := by
  apply (AffineVariety.points_eq_iff _ _).mp
  rw [AffineFamily.points_locus, AffineVariety.points_components V]
  ext x
  simp

lemma pairFlat_in_component (p q : RPoint d) (E : AffineVariety (Fintype.card (SkewIdx (d + 1))))
    (hE : skewToPoint '' pairFlat p q ⊆ E.points) :
    ∃ C : E.Component, skewToPoint '' pairFlat p q ⊆ C.variety.points := by
  let S := skewToPoint '' pairFlat p q
  let I := MvPolynomial.vanishingIdeal ℂ S
  have hprime : I.IsPrime := pairFlat_vanishingIdeal_prime p q
  have hle : E.ideal ≤ I := by
    intro f hf x hx
    exact hE hx f hf
  obtain ⟨Q, hQ, hQI⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨⟨Q, hQ⟩, ?_⟩
  intro x hx f hf
  exact (MvPolynomial.mem_vanishingIdeal_iff.mp (hQI hf)) x hx

theorem pair_flat_envelope_carriers (d : ℕ) (W : Finset (RPoint d × RPoint d)) (D : ℕ) :
    ∃ F : AffineFamily.Family (Fintype.card (SkewIdx (d + 1))),
      (∀ V ∈ F, V.IsIrreducible) ∧ AffineFamily.ComponentsDefinedInDegree F D ∧
      AffineFamily.locus F = envelope (skewToPoint '' (⋃ x ∈ W, Reduction.pairFlat x.1 x.2)) D ∧
      ∀ x ∈ W, ∃ V ∈ F,
        skewToPoint '' Reduction.pairFlat x.1 x.2 ⊆ V.points ∧ Nat.choose d 2 ≤ V.dimension := by
  classical
  let T : Set (Point (Fintype.card (SkewIdx (d + 1)))) :=
    skewToPoint '' (⋃ x ∈ W, pairFlat x.1 x.2)
  let E := envelope T D
  let F : AffineFamily.Family (Fintype.card (SkewIdx (d + 1))) := envelopeComponents T D
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro V hV
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hV
    exact C.irreducible
  · exact envelope_components_defined T D F le_rfl
  · simpa [F, envelopeComponents, E] using component_family_locus E
  · intro x hx
    let S := skewToPoint '' pairFlat x.1 x.2
    have hST : S ⊆ T := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨w, Set.mem_iUnion₂.mpr ⟨x, hx, hw⟩, rfl⟩
    have hSE : S ⊆ E.points := hST.trans (subset_envelope T D)
    obtain ⟨C, hCS⟩ := pairFlat_in_component x.1 x.2 E hSE
    refine ⟨C.variety, Finset.mem_image_of_mem _ (Finset.mem_univ C), hCS, ?_⟩
    have hI : C.val ≤ MvPolynomial.vanishingIdeal ℂ S := by
      intro f hf z hz
      exact hCS hz f hf
    exact affineDimension_ge_of_independent_coordinates C.variety (zCoord d)
      (zCoord_algebraicIndependent x.1 x.2 C.val hI)

end
end DistinctDistances.Bridges
