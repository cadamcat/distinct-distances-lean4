import DistinctDistances.TrackE.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Sym.Card

/-!
# Pair flats and neighbour flats (`reduction.tex:308-344, 386-394`)

Skew forms on `ℂ^e` are coordinatized by their entries above the diagonal. The evaluation flat
`F_λ = {z : z v = y}` of `concentration.tex:24-28` is `evalFlat v y`. A pair `(p,q)` gives the
evaluation flat of the parameter `[(v₀,1) : (y₀, -v₀·y₀)]` in skew forms on `ℂ^{d+1}`
(`reduction.tex:327-342`); its points are the pairs `(Z,c)` with `Z v₀ + c = y₀`.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

/-- Coordinates of skew forms on `ℂ^e`: the entries `z_{ij}`, `i < j`. -/
abbrev SkewIdx (e : ℕ) := {ij : Fin e × Fin e // ij.1 < ij.2}

/-- The skew matrix with the given entries above the diagonal. -/
def skewMatrix {e : ℕ} (z : SkewIdx e → ℂ) : Matrix (Fin e) (Fin e) ℂ := fun i j =>
  if h : i < j then z ⟨(i, j), h⟩ else if h' : j < i then -z ⟨(j, i), h'⟩ else 0

private def skewMatrixOver {e : ℕ} {R : Type*} [Neg R] [Zero R]
    (z : SkewIdx e → R) : Matrix (Fin e) (Fin e) R := fun i j =>
  if h : i < j then z ⟨(i, j), h⟩ else if h' : j < i then -z ⟨(j, i), h'⟩ else 0

/-- conc:flat-model (`concentration.tex:24-28`): the evaluation flat `{z : z v = y}`. -/
def evalFlat {e : ℕ} (v y : Fin e → ℂ) : Set (SkewIdx e → ℂ) :=
  {z | (skewMatrix z).mulVec v = y}

namespace Reduction

variable {d : ℕ}

/-- `v₀ = (p+q)/2` (`reduction.tex:316`). -/
def pairMid (p q : RPoint d) : RPoint d := (1 / 2 : ℝ) • (p + q)

/-- `y₀ = (p-q)/2` (`reduction.tex:316`). -/
def pairHalfDiff (p q : RPoint d) : RPoint d := (1 / 2 : ℝ) • (p - q)

/-- The `v`-part `(v₀, 1)` of the global parameter (`reduction.tex:330`). -/
def pairParamV (p q : RPoint d) : Fin (d + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) (cplx (pairMid p q)) 1

/-- The `y`-part `(y₀, -v₀·y₀)` of the global parameter (`reduction.tex:330`). -/
def pairParamY (p q : RPoint d) : Fin (d + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) (cplx (pairHalfDiff p q))
    (-((inner ℝ (pairMid p q) (pairHalfDiff p q) : ℝ) : ℂ))

/-- red:u-pairflat (`reduction.tex:313-342`): the pair flat `F_{p,q}`, the evaluation flat of the
global parameter in skew forms on `ℂ^{d+1}`. -/
def pairFlat (p q : RPoint d) : Set (SkewIdx (d + 1) → ℂ) :=
  evalFlat (pairParamV p q) (pairParamY p q)

/-- The `Z`-block of a skew form on `ℂ^{d+1}`: forget the last column. -/
def zBlock (z : SkewIdx (d + 1) → ℂ) : SkewIdx d → ℂ := fun ij =>
  z ⟨(ij.1.1.castSucc, ij.1.2.castSucc), by simpa using ij.2⟩

private lemma skewMatrix_transpose (e : ℕ) (z : SkewIdx e → ℂ) :
    Matrix.transpose (skewMatrix z) = -skewMatrix z := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [skewMatrix, h, lt_asymm h]
  · subst j
    simp [skewMatrix]
  · simp [skewMatrix, h, lt_asymm h]

private lemma skewMatrix_quadratic_eq_zero (e : ℕ) (z : SkewIdx e → ℂ)
    (x : Fin e → ℂ) : x ⬝ᵥ (skewMatrix z).mulVec x = 0 := by
  have hs := Matrix.dotProduct_transpose_mulVec (skewMatrix z) x x
  rw [skewMatrix_transpose] at hs
  have hs' : -(x ⬝ᵥ (skewMatrix z).mulVec x) = x ⬝ᵥ (skewMatrix z).mulVec x := by
    simpa only [Matrix.neg_mulVec, dotProduct_neg] using hs
  have hsum : (x ⬝ᵥ (skewMatrix z).mulVec x) +
      (x ⬝ᵥ (skewMatrix z).mulVec x) = 0 := by
    have h0 : 0 = (x ⬝ᵥ (skewMatrix z).mulVec x) +
        (x ⬝ᵥ (skewMatrix z).mulVec x) := by
      simpa using congrArg (fun y : ℂ => y + (x ⬝ᵥ (skewMatrix z).mulVec x)) hs'
    exact h0.symm
  have h2 : (2 : ℂ) * (x ⬝ᵥ (skewMatrix z).mulVec x) = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

private lemma cplx_dot_inner {e : ℕ} (x y : RPoint e) :
    cplx x ⬝ᵥ cplx y = ((inner ℝ x y : ℝ) : ℂ) := by
  simp [dotProduct, cplx, PiLp.inner_apply, mul_comm]

private lemma skewMatrix_snoc_castSucc (z : SkewIdx (d + 1) → ℂ)
    (x : Fin d → ℂ) (i : Fin d) :
    (skewMatrix z).mulVec (Fin.snoc x (1 : ℂ)) i.castSucc =
      (skewMatrix (zBlock z)).mulVec x i +
        z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩ := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, skewMatrix, zBlock]

private lemma skewMatrix_snoc_last (e : ℕ) (z : SkewIdx (e + 1) → ℂ)
    (x : Fin e → ℂ) :
    (skewMatrix z).mulVec (Fin.snoc x (1 : ℂ)) (Fin.last e) =
      - (x ⬝ᵥ fun i : Fin e => z ⟨(i.castSucc, Fin.last e), Fin.castSucc_lt_last i⟩) := by
  have hlast (i : Fin e) : ¬ Fin.last e < i.castSucc := by
    exact not_lt_of_ge (Fin.le_last _)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, skewMatrix, mul_comm, hlast]

private def extendPairFlatCoordinates (Z : SkewIdx d → ℂ) (c : Fin d → ℂ) :
    SkewIdx (d + 1) → ℂ := fun a =>
  if h : a.1.2 = Fin.last d then
    let hfirst : a.1.1 ≠ Fin.last d := ne_of_lt (by simpa [h] using a.2)
    c (a.1.1.castPred hfirst)
  else
    let hj : a.1.2 ≠ Fin.last d := h
    let hi : a.1.1 ≠ Fin.last d := Fin.ne_of_lt (Fin.lt_of_lt_of_le a.2 (Fin.le_last _))
    Z ⟨(a.1.1.castPred hi, a.1.2.castPred hj),
      (Fin.castPred_lt_castPred_iff (hi := hi) (hj := hj)).2 a.2⟩

private lemma zBlock_extendPairFlatCoordinates (Z : SkewIdx d → ℂ) (c : Fin d → ℂ) :
    zBlock (extendPairFlatCoordinates Z c) = Z := by
  ext ij
  simp [zBlock, extendPairFlatCoordinates, Fin.castPred_castSucc]

private lemma lastColumn_extendPairFlatCoordinates (Z : SkewIdx d → ℂ)
    (c : Fin d → ℂ) (i : Fin d) :
    extendPairFlatCoordinates Z c ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩ = c i := by
  simp [extendPairFlatCoordinates, Fin.castPred_castSucc]

private lemma skewMatrix_update_mulVec_left (i j : Fin d) (hij : i < j)
    (x : Fin d → ℂ) :
    (skewMatrix (Function.update (0 : SkewIdx d → ℂ) ⟨(i, j), hij⟩ 1)).mulVec x i = x j := by
  have hrow :
      (skewMatrix (Function.update (0 : SkewIdx d → ℂ) ⟨(i, j), hij⟩ 1)) i = Pi.single j 1 := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [skewMatrix, Function.update, hij]
    · by_cases hki : k = i
      · subst k
        simp [skewMatrix, Function.update, hij, hkj]
      · simp [skewMatrix, Function.update, hij, hkj, hki, Ne.symm hki]
  simpa [Matrix.mulVec, hrow] using (single_one_dotProduct j x)

private lemma skewMatrix_update_mulVec_right (i j : Fin d) (hij : i < j)
    (x : Fin d → ℂ) :
    (skewMatrix (Function.update (0 : SkewIdx d → ℂ) ⟨(i, j), hij⟩ 1)).mulVec x j = -x i := by
  have hrow :
      (skewMatrix (Function.update (0 : SkewIdx d → ℂ) ⟨(i, j), hij⟩ 1)) j = -Pi.single i 1 := by
    funext k
    by_cases hki : k = i
    · subst k
      have hji : ¬ j < i := not_lt_of_gt hij
      simp [skewMatrix, Function.update, hij, hji]
    · by_cases hkj : k = j
      · subst k
        simp [skewMatrix, Function.update, hij, hki]
      · simp [skewMatrix, Function.update, hij, hki, hkj, Ne.symm hki, Ne.symm hkj]
  rw [Matrix.mulVec, hrow, neg_dotProduct, single_one_dotProduct]

/-- red:u-pairflat (`reduction.tex:313-316, 332-341`): `z ∈ F_{p,q}` iff `Z v₀ + c = y₀`, where
`Z` is the `Z`-block and `c` the last column. -/
theorem mem_pairFlat_iff (p q : RPoint d) (z : SkewIdx (d + 1) → ℂ) :
    z ∈ pairFlat p q ↔
      (skewMatrix (zBlock z)).mulVec (cplx (pairMid p q)) +
          (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) =
        cplx (pairHalfDiff p q) := by
  change (skewMatrix z).mulVec (Fin.snoc (cplx (pairMid p q)) 1) =
      Fin.snoc (cplx (pairHalfDiff p q))
        (-((inner ℝ (pairMid p q) (pairHalfDiff p q) : ℝ) : ℂ)) ↔
    (skewMatrix (zBlock z)).mulVec (cplx (pairMid p q)) +
        (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) =
      cplx (pairHalfDiff p q)
  constructor
  · intro h
    funext i
    have hi := congrFun h i.castSucc
    simpa [skewMatrix_snoc_castSucc] using hi
  · intro h
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · have hquad := skewMatrix_quadratic_eq_zero d (zBlock z) (cplx (pairMid p q))
      have hdot := congrArg (fun w : Fin d → ℂ => cplx (pairMid p q) ⬝ᵥ w) h
      have hcol :
          cplx (pairMid p q) ⬝ᵥ
              (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) =
            ((inner ℝ (pairMid p q) (pairHalfDiff p q) : ℝ) : ℂ) := by
        rw [dotProduct_add, hquad, zero_add] at hdot
        simpa [cplx_dot_inner] using hdot
      simp [skewMatrix_snoc_last, hcol]
    · have hi := congrFun h i
      simpa [skewMatrix_snoc_castSucc] using hi

/-- red:u-pairflat (`reduction.tex:318-320`): distinct pairs give distinct flats. Needs
`d ≥ 2`: for `d = 1` there are no nonzero skew `Z`, and the flat only records `y₀`. -/
theorem pairFlat_injective (hd : 2 ≤ d) {p q p' q' : RPoint d}
    (h : pairFlat p q = pairFlat p' q') :
    p = p' ∧ q = q' := by
  classical
  let m := pairMid p q
  let m' := pairMid p' q'
  let y := pairHalfDiff p q
  let y' := pairHalfDiff p' q'
  have hrel (A : SkewIdx d → ℂ) :
      (skewMatrix A).mulVec (cplx m') - (skewMatrix A).mulVec (cplx m) =
        cplx y' - cplx y := by
    let c := cplx y - (skewMatrix A).mulVec (cplx m)
    let z := extendPairFlatCoordinates A c
    have hbase : (skewMatrix A).mulVec (cplx m) + c = cplx y := by
      dsimp [c]
      abel
    have hz : z ∈ pairFlat p q := by
      apply (mem_pairFlat_iff p q z).mpr
      change (skewMatrix (zBlock z)).mulVec (cplx m) +
        (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) = cplx y
      change (skewMatrix (zBlock (extendPairFlatCoordinates A c))).mulVec (cplx m) +
        (fun i : Fin d => extendPairFlatCoordinates A c
          ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) = cplx y
      have hcols : (fun i : Fin d => extendPairFlatCoordinates A c
          ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) = c := by
        funext i
        exact lastColumn_extendPairFlatCoordinates A c i
      rw [zBlock_extendPairFlatCoordinates, hcols]
      exact hbase
    have hz' : z ∈ pairFlat p' q' := by
      rw [← h]
      exact hz
    have htarget := (mem_pairFlat_iff p' q' z).mp hz'
    have htarget' : (skewMatrix A).mulVec (cplx m') + c = cplx y' := by
      change (skewMatrix (zBlock (extendPairFlatCoordinates A c))).mulVec (cplx m') +
        (fun i : Fin d => extendPairFlatCoordinates A c
          ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) = cplx y' at htarget
      have hcols : (fun i : Fin d => extendPairFlatCoordinates A c
          ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) = c := by
        funext i
        exact lastColumn_extendPairFlatCoordinates A c i
      rw [zBlock_extendPairFlatCoordinates, hcols] at htarget
      exact htarget
    calc
      (skewMatrix A).mulVec (cplx m') - (skewMatrix A).mulVec (cplx m) =
          ((skewMatrix A).mulVec (cplx m') + c) -
            ((skewMatrix A).mulVec (cplx m) + c) := by abel
      _ = cplx y' - cplx y := by rw [htarget', hbase]
  have hyC : cplx y' = cplx y := by
    have hmat0 : skewMatrix (0 : SkewIdx d → ℂ) = 0 := by
      ext i j
      simp [skewMatrix]
    have hz := hrel (0 : SkewIdx d → ℂ)
    rw [hmat0] at hz
    simp only [Matrix.zero_mulVec, sub_self] at hz
    have hzero : cplx y' - cplx y = 0 := hz.symm
    exact (sub_eq_zero.mp hzero)
  have hyEq : y' = y := by
    ext i
    exact Complex.ofReal_injective (congrFun hyC i)
  have hmap : cplx (m' - m) = cplx m' - cplx m := by
    ext i
    simp [cplx]
  have hZdiff (A : SkewIdx d → ℂ) :
      (skewMatrix A).mulVec (cplx (m' - m)) = 0 := by
    have h := hrel A
    rw [hyEq] at h
    rw [hmap, Matrix.mulVec_sub]
    simpa using h
  have hmC : cplx (m' - m) = 0 := by
    ext j
    let k0 : Fin d := ⟨0, by omega⟩
    let k1 : Fin d := ⟨1, by omega⟩
    let k : Fin d := if j = k0 then k1 else k0
    have h01 : k1 ≠ k0 := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [k1, k0] at hv
    have hkj : k ≠ j := by
      by_cases hj : j = k0
      · simpa [k, hj] using h01
      · simpa [k, hj] using Ne.symm hj
    by_cases hlt : k < j
    · let A : SkewIdx d → ℂ := Function.update 0 ⟨(k, j), hlt⟩ 1
      have hcoord := congrFun (hZdiff A) k
      rw [skewMatrix_update_mulVec_left k j hlt] at hcoord
      simpa [A] using hcoord
    · have hjk : j < k := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hkj)
      let A : SkewIdx d → ℂ := Function.update 0 ⟨(j, k), hjk⟩ 1
      have hcoord := congrFun (hZdiff A) k
      rw [skewMatrix_update_mulVec_right j k hjk] at hcoord
      simpa [A] using hcoord
  have hmEq : m' = m := by
    have hdiff : m' - m = 0 := by
      ext i
      exact Complex.ofReal_injective (by simpa [cplx] using congrFun hmC i)
    exact sub_eq_zero.mp hdiff
  have hp : p = m + y := by
    dsimp [m, y, pairMid, pairHalfDiff]
    module
  have hp' : p' = m' + y' := by
    dsimp [m', y', pairMid, pairHalfDiff]
    module
  have hq : q = m - y := by
    dsimp [m, y, pairMid, pairHalfDiff]
    module
  have hq' : q' = m' - y' := by
    dsimp [m', y', pairMid, pairHalfDiff]
    module
  constructor
  · calc
      p = m + y := hp
      _ = m' + y' := by rw [hmEq, hyEq]
      _ = p' := hp'.symm
  · calc
      q = m - y := hq
      _ = m' - y' := by rw [hmEq, hyEq]
      _ = q' := hq'.symm

/-- red:u-neighbor (`reduction.tex:386-391`): inside `F_{p,q}`, the intersection with
`F_{p',q'}` is cut out in `Z`-coordinates by `Z(u+w) = u-w`, `u = p'-p`, `w = q'-q`. -/
theorem mem_pairFlat_inter_iff (p q p' q' : RPoint d) (z : SkewIdx (d + 1) → ℂ)
    (hz : z ∈ pairFlat p q) :
    z ∈ pairFlat p' q' ↔
      zBlock z ∈ evalFlat (cplx ((p' - p) + (q' - q))) (cplx ((p' - p) - (q' - q))) := by
  classical
  let Z := skewMatrix (zBlock z)
  let m := pairMid p q
  let m' := pairMid p' q'
  let y := pairHalfDiff p q
  let y' := pairHalfDiff p' q'
  let u := p' - p
  let w := q' - q
  have hbase := (mem_pairFlat_iff p q z).mp hz
  change Z.mulVec (cplx m) +
      (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) = cplx y at hbase
  rw [mem_pairFlat_iff p' q' z]
  change (Z.mulVec (cplx m') +
      (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) = cplx y') ↔
    Z.mulVec (cplx (u + w)) = cplx (u - w)
  have hm : m' - m = (1 / 2 : ℝ) • (u + w) := by
    dsimp [m, m', u, w, pairMid]
    module
  have hy : y' - y = (1 / 2 : ℝ) • (u - w) := by
    dsimp [y, y', u, w, pairHalfDiff]
    module
  have hmC : cplx (m' - m) = (1 / 2 : ℂ) • cplx (u + w) := by
    ext i
    simp [cplx, hm]
    ring
  have hyC : cplx (y' - y) = (1 / 2 : ℂ) • cplx (u - w) := by
    ext i
    simp [cplx, hy]
  have hmSubC : cplx (m' - m) = cplx m' - cplx m := by
    ext i
    simp [cplx]
  have hySubC : cplx (y' - y) = cplx y' - cplx y := by
    ext i
    simp [cplx]
  have hcancel {a b : Fin d → ℂ}
      (h : (1 / 2 : ℂ) • a = (1 / 2 : ℂ) • b) : a = b := by
    have h' := congrArg (fun x : Fin d → ℂ => (2 : ℂ) • x) h
    simpa [smul_smul] using h'
  constructor
  · intro hsecond
    have hlin : Z.mulVec (cplx m') - Z.mulVec (cplx m) = cplx y' - cplx y := by
      calc
        Z.mulVec (cplx m') - Z.mulVec (cplx m) =
            (Z.mulVec (cplx m') +
              (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩)) -
            (Z.mulVec (cplx m) +
              (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩)) := by abel
        _ = cplx y' - cplx y := by rw [hsecond, hbase]
    have hdiff : Z.mulVec (cplx (m' - m)) = cplx (y' - y) := by
      rw [hmSubC, hySubC, Matrix.mulVec_sub]
      exact hlin
    have hscaled : (1 / 2 : ℂ) • Z.mulVec (cplx (u + w)) =
        (1 / 2 : ℂ) • cplx (u - w) := by
      rw [hmC, hyC, Matrix.mulVec_smul] at hdiff
      exact hdiff
    exact hcancel hscaled
  · intro hEval
    have hscaled := congrArg (fun x : Fin d → ℂ => (1 / 2 : ℂ) • x) hEval
    have hdiff : Z.mulVec (cplx (m' - m)) = cplx (y' - y) := by
      rw [hmC, hyC, Matrix.mulVec_smul]
      exact hscaled
    have hlin : Z.mulVec (cplx m') - Z.mulVec (cplx m) = cplx y' - cplx y := by
      rw [hmSubC, hySubC, Matrix.mulVec_sub] at hdiff
      exact hdiff
    calc
      Z.mulVec (cplx m') +
          (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩) =
        (Z.mulVec (cplx m') - Z.mulVec (cplx m)) +
          (Z.mulVec (cplx m) +
            (fun i : Fin d => z ⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩)) := by abel
      _ = (cplx y' - cplx y) + cplx y := by rw [hlin, hbase]
      _ = cplx y' := by abel

/-- red:u-pairflat (`reduction.tex:318`, `reduction.tex:488`): a pair flat is an affine
`s₀`-flat, `s₀ = C(d,2)`, so its degree-`D` restriction rank is at most `C(D+s₀, s₀)`. -/
private lemma aeval_totalDegree_le_of_linearVars {σ τ : Type*} [DecidableEq σ] [Fintype σ]
    (φ : σ → MvPolynomial τ ℂ)
    (hφ : ∀ i, (φ i).totalDegree ≤ 1) (f : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval φ f).totalDegree ≤ f.totalDegree := by
  classical
  have hsum : MvPolynomial.aeval φ f =
      ∑ s ∈ f.support, MvPolynomial.aeval φ (MvPolynomial.monomial s (f.coeff s)) := by
    calc
      MvPolynomial.aeval φ f = MvPolynomial.aeval φ
          (∑ s ∈ f.support, MvPolynomial.monomial s (f.coeff s)) :=
            congrArg (MvPolynomial.aeval φ) (MvPolynomial.as_sum f)
      _ = ∑ s ∈ f.support, MvPolynomial.aeval φ (MvPolynomial.monomial s (f.coeff s)) := by
        rw [MvPolynomial.aeval_sum]
  calc
    (MvPolynomial.aeval φ f).totalDegree =
        (∑ s ∈ f.support, MvPolynomial.aeval φ (MvPolynomial.monomial s (f.coeff s))).totalDegree := by
          rw [hsum]
    _ ≤ f.totalDegree := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro s hs
      have hsD : s.sum (fun _ e => e) ≤ f.totalDegree := by
        exact MvPolynomial.le_totalDegree hs
      rw [MvPolynomial.aeval_monomial, Finsupp.prod]
      calc
        (MvPolynomial.C (f.coeff s) *
            ∏ i ∈ s.support, φ i ^ s i).totalDegree ≤
          (MvPolynomial.C (f.coeff s)).totalDegree +
            (∏ i ∈ s.support, φ i ^ s i).totalDegree := MvPolynomial.totalDegree_mul _ _
        _ ≤ 0 + ∑ i ∈ s.support, s i := by
          apply Nat.add_le_add
          · simp
          · calc
              (∏ i ∈ s.support, φ i ^ s i).totalDegree ≤
                  ∑ i ∈ s.support, (φ i ^ s i).totalDegree := by
                    exact MvPolynomial.totalDegree_finsetProd _ _
              _ ≤ ∑ i ∈ s.support, s i := by
                apply Finset.sum_le_sum
                intro i hi
                exact (MvPolynomial.totalDegree_pow (φ i) (s i)).trans
                  ((Nat.mul_le_mul_left (s i) (hφ i)).trans_eq (by simp))
              _ = s.sum (fun _ e => e) := by
                rw [Finsupp.sum_fintype _ _ (by simp)]
                exact Finset.sum_subset (Finset.subset_univ _) (by
                  intro i hi hnot
                  simp [Finsupp.notMem_support_iff.mp hnot])
        _ ≤ f.totalDegree := by
          rw [zero_add]
          rw [show (∑ i ∈ s.support, s i) = s.sum (fun _ e => e) by
            rw [Finsupp.sum_fintype _ _ (by simp)]
            exact Finset.sum_subset (Finset.subset_univ _) (by
              intro i hi hnot
              simp [Finsupp.notMem_support_iff.mp hnot])]
          exact hsD

private lemma finsupp_sum_id_eq_sum_self {σ : Type*} [Fintype σ] (f : σ →₀ ℕ) :
    f.sum (fun _ e => e) = f.sum (fun _ => id) := by
  rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  simp

private lemma finite_restrictTotalDegreeExponents (σ : Type*) [Fintype σ] (D : ℕ) :
    Finite {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} := by
  classical
  have hbounded : Finite {m : σ →₀ ℕ // ∀ a, m a ≤ D} :=
    ((Set.Finite.pi' fun _ => Set.finite_le_nat D).preimage
      DFunLike.coe_injective.injOn).to_subtype
  letI : Finite {m : σ →₀ ℕ // ∀ a, m a ≤ D} := hbounded
  refine Finite.of_injective (fun m : {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} =>
    (⟨m.1, fun a => ?_⟩ : {m : σ →₀ ℕ // ∀ a, m a ≤ D})) ?_
  · by_cases ha : m.1 a = 0
    · exact ha ▸ Nat.zero_le _
    · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr ha)).trans m.2
  · intro a b h
    apply Subtype.ext
    exact congrArg (fun x : {m : σ →₀ ℕ // ∀ a, m a ≤ D} => x.1) h

private lemma finrank_restrictTotalDegree_eq_choose (σ : Type*) [Fintype σ]
    [DecidableEq σ] (D : ℕ) :
    Module.finrank ℂ (MvPolynomial.restrictTotalDegree σ ℂ D) =
      Nat.choose (D + Fintype.card σ) (Fintype.card σ) := by
  classical
  let S : Set (σ →₀ ℕ) := {m | m.sum (fun _ e => e) ≤ D}
  have hfinite := finite_restrictTotalDegreeExponents σ D
  letI : Finite S := by
    change Finite {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D}
    exact hfinite
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} := Fintype.ofFinite _
  have hdim : Module.finrank ℂ (MvPolynomial.restrictTotalDegree σ ℂ D) =
      Fintype.card {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} := by
    change Module.finrank ℂ (MvPolynomial.restrictSupport ℂ S) = _
    rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℂ S)]
    rfl
  let E := {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D}
  let total (m : E) : Fin (D + 1) := ⟨m.1.sum (fun _ e => e), Nat.lt_succ_of_le m.2⟩
  let fiberEquiv (k : Fin (D + 1)) : {m : E // total m = k} ≃
      {m : σ →₀ ℕ // m.sum (fun _ => id) = k.val} := {
    toFun := fun m => ⟨m.1.1, by
      have h := congrArg Fin.val m.2
      exact (finsupp_sum_id_eq_sum_self m.1.1).symm.trans h⟩
    invFun := fun m => ⟨⟨m.1, by
      have hsum : m.1.sum (fun _ e => e) = k.val :=
        (finsupp_sum_id_eq_sum_self m.1).trans m.2
      rw [hsum]
      exact Nat.lt_succ_iff.mp k.isLt⟩, by
      apply Fin.ext
      have hsum : m.1.sum (fun _ e => e) = k.val :=
        (finsupp_sum_id_eq_sum_self m.1).trans m.2
      exact hsum⟩
    left_inv := by intro m; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro m; apply Subtype.ext; rfl
  }
  let F := (Equiv.sigmaFiberEquiv total).symm
  letI : Finite E := hfinite
  letI : Fintype E := Fintype.ofFinite E
  letI : ∀ k : Fin (D + 1), Fintype {m : E // total m = k} := fun _ => Fintype.ofFinite _
  have hcard : Fintype.card E = Nat.choose (D + Fintype.card σ) (Fintype.card σ) := by
    calc
      Fintype.card E = ∑ k : Fin (D + 1),
          Fintype.card {m : E // total m = k} := by
        rw [Fintype.card_congr F, Fintype.card_sigma]
      _ = ∑ k : Fin (D + 1), Nat.multichoose (Fintype.card σ) k.val := by
        congr 1
        funext k
        letI : Finite {P : σ →₀ ℕ // P.sum (fun _ => id) = k.val} := by
          apply Finite.of_injective (fiberEquiv k).symm
          exact Equiv.injective (fiberEquiv k).symm
        letI : Fintype {P : σ →₀ ℕ // P.sum (fun _ => id) = k.val} := Fintype.ofFinite _
        rw [Fintype.card_congr (fiberEquiv k)]
        rw [Fintype.card_congr (Sym.equivNatSum σ k.val).symm]
        simp [Sym.card_sym_eq_multichoose]
      _ = ∑ k ∈ Finset.range (D + 1), Nat.multichoose (Fintype.card σ) k := by
        rw [← Fin.sum_univ_eq_sum_range]
      _ = Nat.choose (D + Fintype.card σ) (Fintype.card σ) := by
        rw [Nat.sum_range_multichoose]
  rw [hdim]
  exact hcard

private def pairFlatSubstitution (p q : RPoint d) :
    SkewIdx (d + 1) → MvPolynomial (SkewIdx d) ℂ := fun a =>
  if hlast : a.1.2 = Fin.last d then
    let hi : a.1.1 ≠ Fin.last d := ne_of_lt (by simpa [hlast] using a.2)
    let i := a.1.1.castPred hi
    MvPolynomial.C (R := ℂ) (cplx (pairHalfDiff p q) i) -
      (skewMatrixOver (fun ij : SkewIdx d =>
        (MvPolynomial.X ij : MvPolynomial (SkewIdx d) ℂ))).mulVec
        (fun j => MvPolynomial.C (R := ℂ) (cplx (pairMid p q) j)) i
  else
    let hi : a.1.1 ≠ Fin.last d :=
      Fin.ne_of_lt (Fin.lt_of_lt_of_le a.2 (Fin.le_last _))
    let hj : a.1.2 ≠ Fin.last d := hlast
    MvPolynomial.X (⟨(a.1.1.castPred hi, a.1.2.castPred hj),
      (Fin.castPred_lt_castPred_iff (hi := hi) (hj := hj)).2 a.2⟩ : SkewIdx d)

private lemma pairFlatSubstitution_degree (p q : RPoint d) (a : SkewIdx (d + 1)) :
    (pairFlatSubstitution p q a).totalDegree ≤ 1 := by
  classical
  by_cases hlast : a.1.2 = Fin.last d
  · have hi : a.1.1 ≠ Fin.last d := ne_of_lt (by simpa [hlast] using a.2)
    let i := a.1.1.castPred hi
    have hentry (j : Fin d) :
        (skewMatrixOver (fun ij : SkewIdx d =>
          (MvPolynomial.X ij : MvPolynomial (SkewIdx d) ℂ)) i j).totalDegree ≤ 1 := by
      by_cases hij : i < j
      · simp [skewMatrixOver, hij]
      · by_cases hji : j < i
        · simp [skewMatrixOver, hij, hji, MvPolynomial.totalDegree_neg]
        · simp [skewMatrixOver, hij, hji]
    have hrow :
        ((skewMatrixOver (fun ij : SkewIdx d =>
          (MvPolynomial.X ij : MvPolynomial (SkewIdx d) ℂ))).mulVec
          (fun j => MvPolynomial.C (R := ℂ) (cplx (pairMid p q) j)) i).totalDegree ≤ 1 := by
      simp only [Matrix.mulVec, dotProduct]
      apply MvPolynomial.totalDegree_finsetSum_le
      intro j hj
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hentry j)
    rw [pairFlatSubstitution, dif_pos hlast]
    rw [sub_eq_add_neg]
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (by simp) (by simpa [MvPolynomial.totalDegree_neg, i] using hrow))
  · simp [pairFlatSubstitution, hlast]

private lemma pairFlatSubstitution_eval (p q : RPoint d)
    (z : {z : SkewIdx (d + 1) → ℂ // z ∈ pairFlat p q})
    (a : SkewIdx (d + 1)) :
    MvPolynomial.aeval (zBlock z.1) (pairFlatSubstitution p q a) = z.1 a := by
  classical
  by_cases hlast : a.1.2 = Fin.last d
  · have hi : a.1.1 ≠ Fin.last d := ne_of_lt (by simpa [hlast] using a.2)
    let i := a.1.1.castPred hi
    have hsub : (⟨(i.castSucc, Fin.last d), Fin.castSucc_lt_last i⟩ : SkewIdx (d + 1)) = a := by
      apply Subtype.ext
      apply Prod.ext
      · simp [i, Fin.castPred_castSucc]
      · exact hlast.symm
    have hmem := (mem_pairFlat_iff p q z.1).mp z.2
    have hrow :
        MvPolynomial.aeval (zBlock z.1)
          ((skewMatrixOver (fun ij : SkewIdx d =>
            (MvPolynomial.X ij : MvPolynomial (SkewIdx d) ℂ))).mulVec
            (fun j => MvPolynomial.C (R := ℂ) (cplx (pairMid p q) j)) i) =
          (skewMatrix (zBlock z.1)).mulVec (cplx (pairMid p q)) i := by
      let ev : MvPolynomial (SkewIdx d) ℂ →+* ℂ :=
        (MvPolynomial.aeval (zBlock z.1)).toRingHom
      change ev
          ((skewMatrixOver (fun ij : SkewIdx d =>
            (MvPolynomial.X ij : MvPolynomial (SkewIdx d) ℂ))).mulVec
            (fun j => MvPolynomial.C (R := ℂ) (cplx (pairMid p q) j)) i) = _
      rw [RingHom.map_mulVec]
      have hmatrix :
          (skewMatrixOver (fun ij : SkewIdx d =>
            (MvPolynomial.X ij : MvPolynomial (SkewIdx d) ℂ))).map ev =
            skewMatrix (zBlock z.1) := by
        ext x y
        by_cases hxy : x < y
        · simp [skewMatrixOver, skewMatrix, ev, hxy]
        · by_cases hyx : y < x
          · simp [skewMatrixOver, skewMatrix, ev, hxy, hyx]
          · simp [skewMatrixOver, skewMatrix, ev, hxy, hyx]
      rw [hmatrix]
      congr 1
      funext j
      simp [ev, MvPolynomial.aeval_C]
    have hcoord := congrFun hmem i
    have hcol : z.1 a = cplx (pairHalfDiff p q) i -
        ((skewMatrix (zBlock z.1)).mulVec (cplx (pairMid p q)) i) := by
      have hlastcol :
          (skewMatrix (zBlock z.1)).mulVec (cplx (pairMid p q)) i + z.1 a =
            cplx (pairHalfDiff p q) i := by
        simpa [hsub] using hcoord
      calc
        z.1 a = (z.1 a + (skewMatrix (zBlock z.1)).mulVec
            (cplx (pairMid p q)) i) -
              (skewMatrix (zBlock z.1)).mulVec (cplx (pairMid p q)) i := by abel
        _ = cplx (pairHalfDiff p q) i -
            (skewMatrix (zBlock z.1)).mulVec (cplx (pairMid p q)) i := by
          have hs : z.1 a + (skewMatrix (zBlock z.1)).mulVec
              (cplx (pairMid p q)) i = cplx (pairHalfDiff p q) i := by
            simpa [add_comm] using hlastcol
          exact congrArg (fun t : ℂ => t -
            (skewMatrix (zBlock z.1)).mulVec (cplx (pairMid p q)) i) hs
    rw [pairFlatSubstitution, dif_pos hlast, map_sub, MvPolynomial.aeval_C, hrow]
    exact hcol.symm
  · let hi : a.1.1 ≠ Fin.last d :=
      Fin.ne_of_lt (Fin.lt_of_lt_of_le a.2 (Fin.le_last _))
    let hj : a.1.2 ≠ Fin.last d := hlast
    let ij : SkewIdx d := ⟨(a.1.1.castPred hi, a.1.2.castPred hj),
      (Fin.castPred_lt_castPred_iff (hi := hi) (hj := hj)).2 a.2⟩
    have hidx : (ij.1.1.castSucc, ij.1.2.castSucc) = a.1 := by
      apply Prod.ext <;> simp [ij, Fin.castPred_castSucc]
    have hidx' : (⟨(ij.1.1.castSucc, ij.1.2.castSucc), by simpa using ij.2⟩ :
        SkewIdx (d + 1)) = a := by
      apply Subtype.ext
      exact hidx
    rw [pairFlatSubstitution, dif_neg hlast]
    rw [MvPolynomial.aeval_X]
    simpa [zBlock, ij] using congrArg (fun x : SkewIdx (d + 1) => z.1 x) hidx'

private lemma card_skewIdx (d : ℕ) : Fintype.card (SkewIdx d) = Nat.choose d 2 := by
  classical
  change Fintype.card {ij : Fin d × Fin d // ij.1 < ij.2} = Nat.choose d 2
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin d))

set_option maxHeartbeats 2000000 in
theorem restrictionRank_pairFlat_le (p q : RPoint d) (D : ℕ) :
    restrictionRank (pairFlat p q) D ≤ Nat.choose (D + Nat.choose d 2) (Nat.choose d 2) := by
  classical
  let σ := SkewIdx (d + 1)
  let τ := SkewIdx d
  let sub : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ :=
    MvPolynomial.aeval (pairFlatSubstitution p q)
  let L : MvPolynomial.restrictTotalDegree σ ℂ D →ₗ[ℂ]
      MvPolynomial.restrictTotalDegree τ ℂ D :=
    LinearMap.codRestrict _
      (sub.toLinearMap.comp (MvPolynomial.restrictTotalDegree σ ℂ D).subtype)
      (fun f => MvPolynomial.mem_restrictTotalDegree _ _ _ |>.mpr <|
        (aeval_totalDegree_le_of_linearVars (pairFlatSubstitution p q)
          (pairFlatSubstitution_degree p q) f.1).trans
          ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp f.2))
  let ev : MvPolynomial.restrictTotalDegree τ ℂ D →ₗ[ℂ] (pairFlat p q → ℂ) :=
    LinearMap.pi fun z : pairFlat p q =>
      (MvPolynomial.aeval (zBlock z.1)).toLinearMap.comp
        (MvPolynomial.restrictTotalDegree τ ℂ D).subtype
  have hfactor : restrictionMap (pairFlat p q) D = ev.comp L := by
    apply LinearMap.ext
    intro f
    funext z
    change MvPolynomial.aeval z.1 f.1 =
      MvPolynomial.aeval (zBlock z.1)
        (MvPolynomial.aeval (pairFlatSubstitution p q) f.1)
    rw [MvPolynomial.comp_aeval_apply]
    apply congrArg (fun g : σ → ℂ => MvPolynomial.aeval g f.1)
    funext i
    exact (pairFlatSubstitution_eval p q z i).symm
  have hrank : restrictionRank (pairFlat p q) D ≤
      Module.finrank ℂ (MvPolynomial.restrictTotalDegree τ ℂ D) := by
    rw [restrictionRank, hfactor]
    let S : Set (τ →₀ ℕ) := {m | m.sum (fun _ e => e) ≤ D}
    letI : Finite S := by
      change Finite {m : τ →₀ ℕ // m.sum (fun _ e => e) ≤ D}
      exact finite_restrictTotalDegreeExponents τ D
    letI : Fintype S := Fintype.ofFinite S
    letI : Module.Finite ℂ (MvPolynomial.restrictTotalDegree τ ℂ D) := by
      change Module.Finite ℂ (MvPolynomial.restrictSupport ℂ S)
      exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ S)
    letI : Module.Finite ℂ (LinearMap.range ev) := Module.Finite.range ev
    have hdimEv : Module.finrank ℂ (LinearMap.range ev) ≤
        Module.finrank ℂ (MvPolynomial.restrictTotalDegree τ ℂ D) :=
      LinearMap.finrank_range_le (R := ℂ)
        (M := MvPolynomial.restrictTotalDegree τ ℂ D) ev
    exact (Submodule.finrank_mono (LinearMap.range_comp_le_range L ev)).trans
      hdimEv
  calc
    restrictionRank (pairFlat p q) D ≤
        Module.finrank ℂ (MvPolynomial.restrictTotalDegree τ ℂ D) := hrank
    _ = Nat.choose (D + Nat.choose d 2) (Nat.choose d 2) := by
      rw [finrank_restrictTotalDegree_eq_choose, card_skewIdx]

end Reduction

end

end DistinctDistances
