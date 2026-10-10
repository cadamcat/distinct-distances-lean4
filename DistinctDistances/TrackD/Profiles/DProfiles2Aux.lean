import DistinctDistances.TrackD.Profiles.Partition
import DistinctDistances.TrackD.Profiles.PartitionPieceTolerance
import DistinctDistances.TrackA.Intersections
import OAI.NumberTheory.PowerFree.PointInterpolation

namespace DistinctDistances
namespace TrackD

theorem dprofiles2_componentLength_one_le {n : ℕ} (I : Ideal (Poly n))
    (V : AffineVariety n) (hV : V.IsIrreducible) (hcomp : V.IsComponentOf I) :
    (1 : ℕ∞) ≤ TrackA.componentLength I V hV := by
  classical
  letI : V.ideal.IsPrime := hV
  let R := Localization.AtPrime V.ideal
  let J : Ideal R := I.map (algebraMap (Poly n) R)
  have hIV : I ≤ V.ideal := hcomp.1.2
  have hJ : J ≤ IsLocalRing.maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := V.ideal)]
    exact Ideal.map_mono hIV
  have hJne : J ≠ ⊤ := by
    intro h
    have htop : IsLocalRing.maximalIdeal R = ⊤ := top_unique (by simpa [h] using hJ)
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top htop
  letI : Nontrivial (R ⧸ J) := Submodule.Quotient.nontrivial_iff.mpr hJne
  unfold TrackA.componentLength
  change (1 : ℕ∞) ≤ Module.length R (R ⧸ J)
  exact Order.one_le_iff_ne_zero.mpr (Module.length_pos.ne')

theorem dprofiles2_pointIdeal_injective {n : ℕ} :
    Function.Injective (pointIdeal (n := n)) := by
  classical
  intro x y hxy
  funext i
  have hxmem : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal x := by
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    subst z
    simp
  have hymem : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal y := by
    rw [← hxy]
    exact hxmem
  have hyvan : MvPolynomial.X i - MvPolynomial.C (x i) ∈
      MvPolynomial.vanishingIdeal ℂ {y} := by
    simpa [pointIdeal] using hymem
  have heval := MvPolynomial.mem_vanishingIdeal_iff.mp hyvan y (by simp)
  have hcoord : y i - x i = 0 := by simpa using heval
  exact (sub_eq_zero.mp hcoord).symm

noncomputable def dprofiles2ComponentFamily {n : ℕ} (I : Ideal (Poly n)) :
    Finset (AffineVariety n) := by
  classical
  letI : Fintype {Q : Ideal (Poly n) // Q ∈ I.minimalPrimes} :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n) I).fintype
  exact Finset.univ.image fun Q : {Q : Ideal (Poly n) // Q ∈ I.minimalPrimes} =>
    (⟨Q.1, Q.2.isPrime.isRadical⟩ : AffineVariety n)

theorem dprofiles2_mem_componentFamily {n : ℕ} (I : Ideal (Poly n))
    (Z : AffineVariety n) :
    Z ∈ dprofiles2ComponentFamily I ↔ Z.ideal ∈ I.minimalPrimes := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨Q, hQ, hZ⟩
    have hideal : Q.1 = Z.ideal := by
      cases hZ
      rfl
    simpa [hideal] using Q.2
  · intro hZ
    letI : Fintype {Q : Ideal (Poly n) // Q ∈ I.minimalPrimes} :=
      (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n) I).fintype
    refine Finset.mem_image.mpr ⟨⟨Z.ideal, hZ⟩, Finset.mem_univ _, ?_⟩
    apply AffineVariety.ext
    rfl

noncomputable def dprofiles2ComponentsMeeting {n : ℕ} (I : Ideal (Poly n))
    (S : Finset (Pt n)) : Finset (AffineVariety n) := by
  classical
  exact (dprofiles2ComponentFamily I).filter (fun Z => ∃ x ∈ S, toC x ∈ Z)

theorem dprofiles2_minimal_of_intermediate {n : ℕ} (I J : Ideal (Poly n))
    (P : Ideal (Poly n)) (hIJ : I ≤ J) (hJP : J ≤ P)
    (hP : P ∈ I.minimalPrimes) : P ∈ J.minimalPrimes := by
  change Minimal (fun Q : Ideal (Poly n) => Q.IsPrime ∧ J ≤ Q) P
  refine ⟨⟨hP.isPrime, hJP⟩, ?_⟩
  intro Q hQ hQP
  exact hP.2 ⟨hQ.1, hIJ.trans hQ.2⟩ hQP

private theorem dprofiles2_range_fin_succ {α : Type*} {n : ℕ}
    (f : Fin (n + 1) → α) :
    Set.range f = {f 0} ∪ Set.range (fun i : Fin n => f i.succ) := by
  ext z
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ i => exact Or.inr ⟨i, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨i.succ, rfl⟩

private theorem dprofiles2_cut_ideal_split {n m : ℕ} (V : AffineVariety n)
    (f : Fin (m + 1) → Poly n) :
    V.ideal ⊔ Ideal.span (Set.range f) =
      (V.ideal ⊔ Ideal.span {f 0}) ⊔ Ideal.span (Set.range (fun i : Fin m => f i.succ)) := by
  rw [dprofiles2_range_fin_succ f, Ideal.span_union]
  exact (sup_assoc _ _ _).symm

def dprofiles2PrefixCut {d j : ℕ} (π : CutPath d) (hj : j ≤ d)
    (i : Fin j) : Poly d :=
  π.cut ⟨i.val, i.isLt.trans_le hj⟩

private def dprofiles2FinPrefixEquiv {d j : ℕ} (hj : j ≤ d) :
    Fin j ≃ {i : Fin d // i.val < j} where
  toFun i := ⟨⟨i.val, i.isLt.trans_le hj⟩, i.isLt⟩
  invFun i := ⟨i.1.val, i.2⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv i := by apply Subtype.ext; apply Fin.ext; rfl

private theorem dprofiles2_prod_prefix {d j : ℕ} (hj : j ≤ d)
    (g : Fin d → ℝ) :
    (∏ i : Fin j, g ⟨i.val, i.isLt.trans_le hj⟩) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), g i := by
  let e := dprofiles2FinPrefixEquiv hj
  calc
    (∏ i : Fin j, g ⟨i.val, i.isLt.trans_le hj⟩) =
        ∏ i : Fin j, g (e i).1 := by rfl
    _ = ∏ i : {i : Fin d // i.val < j}, g i.1 := Equiv.prod_comp e (fun i => g i.1)
    _ = ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), g i := by
      symm
      exact Finset.prod_subtype (Finset.univ.filter (fun i : Fin d => i.val < j))
        (by intro i; simp) g

private def dprofiles2FinTailEquiv {d j : ℕ} (hj : j ≤ d) :
    Fin (d - j) ≃ {i : Fin d // j ≤ i.val} where
  toFun i := by
    have hsum : j + (d - j) = d := Nat.add_sub_of_le hj
    refine ⟨⟨j + i.val, ?_⟩, ?_⟩
    · exact (Nat.add_lt_add_left i.isLt j).trans_le (le_of_eq hsum)
    · exact Nat.le_add_right _ _
  invFun i := ⟨i.1.val - j, by omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv i := by apply Subtype.ext; apply Fin.ext; dsimp; omega

private theorem dprofiles2_prod_tail {d j : ℕ} (hj : j ≤ d)
    (g : Fin d → ℝ) :
    (∏ i : Fin (d - j), g ⟨j + i.val, by omega⟩) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val), g i := by
  let e := dprofiles2FinTailEquiv hj
  calc
    (∏ i : Fin (d - j), g ⟨j + i.val, by omega⟩) =
        ∏ i : Fin (d - j), g (e i).1 := by rfl
    _ = ∏ i : {i : Fin d // j ≤ i.val}, g i.1 := Equiv.prod_comp e (fun i => g i.1)
    _ = ∏ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ i.val), g i := by
      symm
      exact Finset.prod_subtype (Finset.univ.filter (fun i : Fin d => j ≤ i.val))
        (by intro i; simp) g

theorem dprofiles2_system_eq_prefix {d j : ℕ} (π : CutPath d) (hj : j ≤ d) :
    π.system j = Ideal.span (Set.range (dprofiles2PrefixCut π hj)) := by
  have hset :
      {p | ∃ i : Fin d, i.val < j ∧ π.cut i = p} =
        Set.range (dprofiles2PrefixCut π hj) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i.val, hi⟩, ?_⟩
      simp [dprofiles2PrefixCut]
    · rintro ⟨i, hi⟩
      refine ⟨⟨i.val, i.isLt.trans_le hj⟩, i.isLt, ?_⟩
      simpa [dprofiles2PrefixCut] using hi
  change Ideal.span {p | ∃ i : Fin d, i.val < j ∧ π.cut i = p} = _
  exact congrArg Ideal.span hset

theorem dprofiles2_cut_degree_pos {d : ℕ} (P : Finset (Pt d)) (X : Piece d)
    (θ ξ K : ℝ) (hX : PieceGood P θ ξ K X) (hpts : X.pts.Nonempty) (i : Fin d) :
    1 ≤ (X.path.cut i).totalDegree := by
  classical
  obtain ⟨x, hx⟩ := hpts
  have hsysPoint : X.path.system i.val ≤ pointIdeal (toC x) := by
    apply Ideal.span_le.mpr
    rintro p ⟨k, hk, rfl⟩
    change X.path.cut k ∈ MvPolynomial.vanishingIdeal ℂ {toC x}
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    have hyx : y = toC x := Set.mem_singleton_iff.mp hy
    subst y
    exact hX.vanish x hx k
  letI : (pointIdeal (toC x)).IsPrime := (pointIdeal_isMaximal (toC x)).isPrime
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le hsysPoint
  let Y : AffineVariety d := ⟨q, hq.isPrime.isRadical⟩
  have hYlocal : Y ∈ X.path.localCarriers i.val (toC x) := by
    constructor
    · change q ∈ (X.path.system i.val).minimalPrimes
      exact hq
    · intro p hp
      have hp' : p ∈ pointIdeal (toC x) := hqle hp
      change p ∈ MvPolynomial.vanishingIdeal ℂ {toC x} at hp'
      exact MvPolynomial.mem_vanishingIdeal_iff.mp hp' (toC x) (by simp)
  have hproper : X.path.cut i ∉ q := hX.proper x hx i Y hYlocal
  by_contra hdeg
  have hdeg0 : (X.path.cut i).totalDegree = 0 := by omega
  have hconst := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg0
  have hcoef : (X.path.cut i).coeff 0 = 0 := by
    have hEval := hX.vanish x hx i
    rw [hconst, MvPolynomial.eval_C] at hEval
    exact hEval
  have hcut0 : X.path.cut i = 0 := by
    rw [hconst, hcoef]
    exact MvPolynomial.C_0
  exact hproper (hcut0 ▸ Ideal.zero_mem q)

theorem dprofiles2_prefix_degree_product {d : ℕ} (P : Finset (Pt d)) (X : Piece d)
    (θ : ℝ)
    (hdeg : ∀ i, ((X.path.cut i).totalDegree : ℝ) ≤
      testDeg (cfgB P) X.width (X.path.time i + θ))
    (j : ℕ) (hj : j ≤ d) :
    (∏ i : Fin j, ((X.path.cut ⟨i.val, i.isLt.trans_le hj⟩).totalDegree : ℝ)) ≤
      eScale (cfgB P) X.width X.path.time j * Real.exp ((j : ℝ) * θ * X.width) := by
  classical
  have hterm (i : Fin d) :
      ((X.path.cut i).totalDegree : ℝ) ≤
        cutScale (cfgB P) X.width X.path.time i * Real.exp (θ * X.width) := by
    calc
      ((X.path.cut i).totalDegree : ℝ) ≤
          testDeg (cfgB P) X.width (X.path.time i + θ) := hdeg i
      _ = cutScale (cfgB P) X.width X.path.time i * Real.exp (θ * X.width) := by
        simp only [testDeg, cutScale]
        rw [show (X.path.time i + θ) * X.width =
          X.path.time i * X.width + θ * X.width by ring, Real.exp_add]
        ring
  have hprod :
      (∏ i : Fin j, ((X.path.cut ⟨i.val, i.isLt.trans_le hj⟩).totalDegree : ℝ)) ≤
        ∏ i : Fin j,
          (cutScale (cfgB P) X.width X.path.time ⟨i.val, i.isLt.trans_le hj⟩ *
            Real.exp (θ * X.width)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact Nat.cast_nonneg _
    · intro i hi
      exact hterm ⟨i.val, i.isLt.trans_le hj⟩
  calc
    _ ≤ ∏ i : Fin j,
        (cutScale (cfgB P) X.width X.path.time ⟨i.val, i.isLt.trans_le hj⟩ *
          Real.exp (θ * X.width)) := hprod
    _ = (∏ i : Fin j, cutScale (cfgB P) X.width X.path.time
          ⟨i.val, i.isLt.trans_le hj⟩) * Real.exp ((j : ℝ) * θ * X.width) := by
        rw [Finset.prod_mul_distrib]
        simp [Finset.prod_const, Finset.card_fin, Real.exp_nat_mul, mul_assoc]
    _ = eScale (cfgB P) X.width X.path.time j *
          Real.exp ((j : ℝ) * θ * X.width) := by
        rw [dprofiles2_prod_prefix hj]
        rfl

theorem dprofiles2_tail_degree_product {d : ℕ} (P : Finset (Pt d)) (X : Piece d)
    (θ : ℝ)
    (hdeg : ∀ i, ((X.path.cut i).totalDegree : ℝ) ≤
      testDeg (cfgB P) X.width (X.path.time i + θ))
    (j : ℕ) (hj : j ≤ d) :
    (∏ i : Fin (d - j),
      ((X.path.cut ⟨j + i.val, by omega⟩).totalDegree : ℝ)) ≤
      tailScale (cfgB P) X.width X.path.time j * Real.exp (((d - j : ℕ) : ℝ) * θ * X.width) := by
  classical
  have hterm (i : Fin d) :
      ((X.path.cut i).totalDegree : ℝ) ≤
        cutScale (cfgB P) X.width X.path.time i * Real.exp (θ * X.width) := by
    calc
      ((X.path.cut i).totalDegree : ℝ) ≤
          testDeg (cfgB P) X.width (X.path.time i + θ) := hdeg i
      _ = cutScale (cfgB P) X.width X.path.time i * Real.exp (θ * X.width) := by
        simp only [testDeg, cutScale]
        rw [show (X.path.time i + θ) * X.width =
          X.path.time i * X.width + θ * X.width by ring, Real.exp_add]
        ring
  have hprod :
      (∏ i : Fin (d - j), ((X.path.cut ⟨j + i.val, by omega⟩).totalDegree : ℝ)) ≤
        ∏ i : Fin (d - j),
          (cutScale (cfgB P) X.width X.path.time ⟨j + i.val, by omega⟩ *
            Real.exp (θ * X.width)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact Nat.cast_nonneg _
    · intro i hi
      exact hterm ⟨j + i.val, by omega⟩
  calc
    _ ≤ ∏ i : Fin (d - j),
        (cutScale (cfgB P) X.width X.path.time ⟨j + i.val, by omega⟩ *
          Real.exp (θ * X.width)) := hprod
    _ = (∏ i : Fin (d - j), cutScale (cfgB P) X.width X.path.time
          ⟨j + i.val, by omega⟩) *
          Real.exp (((d - j : ℕ) : ℝ) * θ * X.width) := by
        rw [Finset.prod_mul_distrib]
        simp [Finset.prod_const, Finset.card_fin, Real.exp_nat_mul, mul_assoc]
    _ = tailScale (cfgB P) X.width X.path.time j *
          Real.exp (((d - j : ℕ) : ℝ) * θ * X.width) := by
        rw [dprofiles2_prod_tail hj]
        rfl

def dprofiles2TailCut {d j : ℕ} (π : CutPath d) (hj : j ≤ d)
    (i : Fin (d - j)) : Poly d :=
  π.cut ⟨j + i.val, by omega⟩

theorem dprofiles2_final_point_minimal {d : ℕ} (P : Finset (Pt d)) (X : Piece d)
    (θ ξ K : ℝ) (hX : PieceGood P θ ξ K X) (x : Pt d) (hx : x ∈ X.pts)
    (j : ℕ) (hj : j ≤ d) (Z : AffineVariety d)
    (hZ : Z ∈ X.path.localCarriers j (toC x)) :
    pointIdeal (toC x) ∈
      (Z.ideal ⊔ Ideal.span (Set.range (dprofiles2TailCut X.path hj))).minimalPrimes := by
  classical
  let Ktail : Ideal (Poly d) :=
    Z.ideal ⊔ Ideal.span (Set.range (dprofiles2TailCut X.path hj))
  have hZmin : Z.ideal ∈ (X.path.system j).minimalPrimes := hZ.1
  have hZle : X.path.system j ≤ Z.ideal := hZmin.le
  have htailPoint : Ideal.span (Set.range (dprofiles2TailCut X.path hj)) ≤
      pointIdeal (toC x) := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    have heval : MvPolynomial.eval (toC x) (dprofiles2TailCut X.path hj i) = 0 :=
      hX.vanish x hx ⟨j + i.val, by omega⟩
    change dprofiles2TailCut X.path hj i ∈ MvPolynomial.vanishingIdeal ℂ {toC x}
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    have hyx : y = toC x := Set.mem_singleton_iff.mp hy
    subst y
    exact heval
  have hKtailPoint : Ktail ≤ pointIdeal (toC x) := sup_le (by
    intro p hp
    have hxZ : MvPolynomial.eval (toC x) p = 0 := hZ.2 p hp
    change p ∈ pointIdeal (toC x)
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    have hyx : y = toC x := Set.mem_singleton_iff.mp hy
    subst y
    exact hxZ) htailPoint
  have hsystemFinal : X.path.system d ≤ Ktail := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, hi, rfl⟩
    by_cases hij : i.val < j
    · have hp : X.path.cut i ∈ X.path.system j := by
        change X.path.cut i ∈ Ideal.span {q | ∃ k : Fin d, k.val < j ∧ X.path.cut k = q}
        exact Ideal.subset_span ⟨i, hij, rfl⟩
      exact Ideal.mem_sup_left (hZle hp)
    · have hjle : j ≤ i.val := by omega
      let k : Fin (d - j) := ⟨i.val - j, by omega⟩
      have heq : X.path.cut i = dprofiles2TailCut X.path hj k := by
        unfold dprofiles2TailCut
        congr 1
        apply Fin.ext
        dsimp [k]
        omega
      rw [heq]
      exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range.mpr ⟨k, rfl⟩))
  have hpointMax : (pointIdeal (toC x)).IsMaximal := pointIdeal_isMaximal _
  letI : (pointIdeal (toC x)).IsPrime := hpointMax.isPrime
  have hminimal : Ideal.IsMinimalPrime Ktail (pointIdeal (toC x)) := by
    change Minimal (fun J : Ideal (Poly d) => J.IsPrime ∧ Ktail ≤ J)
      (pointIdeal (toC x))
    refine ⟨⟨hpointMax.isPrime, hKtailPoint⟩, ?_⟩
    intro J hJ hJP
    have hsystemJ : X.path.system d ≤ J := hsystemFinal.trans hJ.2
    letI : J.IsPrime := hJ.1
    obtain ⟨q, hq, hqJ⟩ := Ideal.exists_minimalPrimes_le hsystemJ
    let W : AffineVariety d := ⟨q, hq.isPrime.isRadical⟩
    have hxW : toC x ∈ W := by
      intro p hp
      have hqpoint : q ≤ pointIdeal (toC x) := hqJ.trans hJP
      have hp' : p ∈ pointIdeal (toC x) := hqpoint hp
      change p ∈ MvPolynomial.vanishingIdeal ℂ {toC x} at hp'
      exact MvPolynomial.mem_vanishingIdeal_iff.mp hp' (toC x) (by simp)
    have hWlocal : W ∈ X.path.localCarriers d (toC x) := by
      constructor
      · change q ∈ (X.path.system d).minimalPrimes
        exact hq
      · exact hxW
    have hWdim := prof_partition_pure X x hx (hX.vanish x hx) (hX.proper x hx)
      d (by omega) W hWlocal
    letI : W.ideal.IsPrime := hWdim.1
    have hWdim0 : W.dimension = 0 := by simpa using hWdim.2
    have hWmax := OAI.QuarticPowerFree.zeroDim_isMaximal W.ideal hWdim0
    have hWpoint : W.ideal ≤ pointIdeal (toC x) := hqJ.trans hJP
    have hWeq : W.ideal = pointIdeal (toC x) :=
      hWmax.eq_of_le hpointMax.ne_top hWpoint
    have hpointJ : pointIdeal (toC x) ≤ J := by
      rw [← hWeq]
      exact hqJ
    exact hpointJ
  exact hminimal

set_option maxHeartbeats 500000 in
theorem dprofiles2_isolated_cut_product_bound {n m : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (f : Fin m → Poly n) (S : Finset (Pt n))
    (hvan : ∀ x ∈ S, ∀ i, MvPolynomial.eval (toC x) (f i) = 0)
    (hdeg : ∀ i, 1 ≤ (f i).totalDegree)
    (hiso : ∀ x ∈ S, pointIdeal (toC x) ∈
      (V.ideal ⊔ Ideal.span (Set.range f)).minimalPrimes) :
    (S.card : ℚ) ≤ V.degree * ∏ i, (f i).totalDegree := by
  classical
  revert V hV f S hvan hdeg hiso
  induction m with
  | zero =>
      intro V hV f S hvan hdeg hiso
      letI : V.ideal.IsPrime := hV
      have hVdeg : (1 : ℚ) ≤ V.degree := by
        change (1 : ℚ) ≤ OAI.QuarticPowerFree.affineDegree V.ideal
        exact OAI.QuarticPowerFree.one_le_affineDegree V.ideal hV.ne_top
      have hpointEq (x : Pt n) (hx : x ∈ S) : pointIdeal (toC x) = V.ideal := by
        have hxiso := hiso x hx
        have hempty : Set.range f = ∅ := by simp
        simpa [hempty, Ideal.minimalPrimes_eq_subsingleton_self] using hxiso
      have hScard : S.card ≤ 1 := Finset.card_le_one.mpr (by
        intro x hx y hy
        have hIdeals : pointIdeal (toC x) = pointIdeal (toC y) :=
          (hpointEq x hx).trans (hpointEq y hy).symm
        have hxyC : toC x = toC y := dprofiles2_pointIdeal_injective hIdeals
        ext i
        exact Complex.ofReal_injective (congrFun hxyC i))
      have hcardQ : (S.card : ℚ) ≤ 1 := by exact_mod_cast hScard
      simpa using hcardQ.trans hVdeg
  | succ m ih =>
      intro V hV f S hvan hdeg hiso
      have hVdeg : (1 : ℚ) ≤ V.degree := by
        change (1 : ℚ) ≤ OAI.QuarticPowerFree.affineDegree V.ideal
        exact OAI.QuarticPowerFree.one_le_affineDegree V.ideal hV.ne_top
      let f₀ : Poly n := f 0
      let ft : Fin m → Poly n := fun i => f i.succ
      let Iall : Ideal (Poly n) := V.ideal ⊔ Ideal.span (Set.range f)
      let I₁ : Ideal (Poly n) := V.ideal ⊔ Ideal.span {f₀}
      have hsplit : Iall = I₁ ⊔ Ideal.span (Set.range ft) := by
        dsimp [Iall, I₁, f₀, ft]
        exact dprofiles2_cut_ideal_split V f
      have hdeg₀ : 1 ≤ f₀.totalDegree := hdeg 0
      have hdegTail : ∀ i, 1 ≤ (ft i).totalDegree := fun i => hdeg i.succ
      have hvanTail : ∀ x ∈ S, ∀ i, MvPolynomial.eval (toC x) (ft i) = 0 := by
        intro x hx i
        exact hvan x hx i.succ
      by_cases hf₀ : f₀ ∈ V.ideal
      · have hI₁ : I₁ = V.ideal := by
          dsimp [I₁]
          rw [sup_eq_left.mpr (Ideal.span_le.mpr (by
            intro p hp
            simpa only [Set.mem_singleton_iff] using hp ▸ hf₀))]
        have hIall : Iall = V.ideal ⊔ Ideal.span (Set.range ft) := by
          rw [hsplit, hI₁]
        have hisoTail : ∀ x ∈ S, pointIdeal (toC x) ∈
            (V.ideal ⊔ Ideal.span (Set.range ft)).minimalPrimes := by
          intro x hx
          simpa [← hIall] using hiso x hx
        have hcard := ih V hV ft S hvanTail hdegTail hisoTail
        have hcardCast : (S.card : ℚ) ≤
            V.degree * ∏ i : Fin m, ((ft i).totalDegree : ℚ) := by
          simpa only [Nat.cast_prod] using hcard
        have hVnonneg : 0 ≤ V.degree := le_trans (by norm_num) hVdeg
        have htailNonneg : 0 ≤ ∏ i : Fin m, ((ft i).totalDegree : ℚ) := by positivity
        have hprod :
            (∏ i : Fin (m + 1), (f i).totalDegree) =
              f₀.totalDegree * ∏ i : Fin m, (ft i).totalDegree := by
          simp [f₀, ft, Fin.prod_univ_succ]
        calc
            (S.card : ℚ) ≤ V.degree * ∏ i : Fin m, ((ft i).totalDegree : ℚ) := hcardCast
          _ ≤ V.degree * ((f₀.totalDegree : ℚ) * ∏ i : Fin m, ((ft i).totalDegree : ℚ)) := by
            apply mul_le_mul_of_nonneg_left _ hVnonneg
            have hdeg₀Q : (1 : ℚ) ≤ (f₀.totalDegree : ℚ) := by exact_mod_cast hdeg₀
            simpa using mul_le_mul_of_nonneg_right hdeg₀Q htailNonneg
          _ = V.degree * (↑(∏ i : Fin (m + 1), (f i).totalDegree) : ℚ) := by
            rw [hprod]
            simp only [Nat.cast_mul, Nat.cast_prod]
      · by_cases hSempty : S = ∅
        · subst S
          simp
          positivity
        · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
          obtain ⟨x, hx⟩ := hSne
          have hIallPoint : Iall ≤ pointIdeal (toC x) := (hiso x hx).le
          have hVle : V.ideal ≤ pointIdeal (toC x) := le_trans le_sup_left hIallPoint
          have hVdimpos : 0 < V.dimension := by
            by_contra hn
            have hdim0 : V.dimension = 0 := by omega
            letI : V.ideal.IsPrime := hV
            have hVmax := OAI.QuarticPowerFree.zeroDim_isMaximal V.ideal hdim0
            have hptmax := pointIdeal_isMaximal (toC x)
            have hEq : V.ideal = pointIdeal (toC x) := hVmax.eq_of_le hptmax.ne_top hVle
            have hf₀Point : f₀ ∈ pointIdeal (toC x) := by
              have hspan : f₀ ∈ Iall := by
                dsimp [Iall]
                exact Ideal.mem_sup_right
                  (Ideal.subset_span (Set.mem_range.mpr ⟨0, rfl⟩))
              exact hIallPoint hspan
            exact hf₀ (hEq.symm ▸ hf₀Point)
          let k : ℕ := V.dimension - 1
          have hdimV : V.dimension = k + 1 := by dsimp [k]; omega
          let F₁ := dprofiles2ComponentsMeeting I₁ S
          have hF₁ : ∀ Q ∈ F₁, Q.IsComponentOf I₁ := by
            intro Q hQ
            dsimp [F₁, dprofiles2ComponentsMeeting] at hQ
            exact dprofiles2_mem_componentFamily I₁ Q |>.mp (Finset.mem_filter.mp hQ).1
          have hbez₁ := TrackA.fa_bezout_proper_degree V hV f₀ hf₀ F₁ hF₁ k hdimV
          let S_Q (Q : AffineVariety n) : Finset (Pt n) :=
            S.filter (fun x => toC x ∈ Q)
          have hScover : S ⊆ F₁.biUnion S_Q := by
            intro y hy
            have hIy : I₁ ≤ pointIdeal (toC y) := by
              calc
                I₁ ≤ I₁ ⊔ Ideal.span (Set.range ft) := le_sup_left
                _ = Iall := hsplit.symm
                _ ≤ pointIdeal (toC y) := (hiso y hy).le
            letI : (pointIdeal (toC y)).IsPrime := (pointIdeal_isMaximal (toC y)).isPrime
            obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le hIy
            let Q : AffineVariety n := ⟨q, hq.isPrime.isRadical⟩
            have hQfam : Q ∈ F₁ := by
              change Q ∈ (dprofiles2ComponentFamily I₁).filter
                (fun Z => ∃ x ∈ S, toC x ∈ Z)
              apply Finset.mem_filter.mpr
              refine ⟨dprofiles2_mem_componentFamily I₁ Q |>.mpr hq, ?_⟩
              exact ⟨y, hy, by
                intro p hp
                have hp' : p ∈ pointIdeal (toC y) := hqle hp
                exact MvPolynomial.mem_vanishingIdeal_iff.mp hp' (toC y) (by simp)⟩
            exact Finset.mem_biUnion.mpr ⟨Q, hQfam, Finset.mem_filter.mpr ⟨hy, by
              intro p hp
              have hp' : p ∈ pointIdeal (toC y) := hqle hp
              exact MvPolynomial.mem_vanishingIdeal_iff.mp hp' (toC y) (by simp)⟩⟩
          have hcardCover :
              (S.card : ℚ) ≤ ∑ Q ∈ F₁, ((S_Q Q).card : ℚ) := by
            calc
              (S.card : ℚ) ≤ ((F₁.biUnion S_Q).card : ℚ) := by
                exact_mod_cast Finset.card_le_card hScover
              _ ≤ ∑ Q ∈ F₁, ((S_Q Q).card : ℚ) := by exact_mod_cast Finset.card_biUnion_le
          have hsumIh :
              (∑ Q ∈ F₁, ((S_Q Q).card : ℚ)) ≤
                (∏ i : Fin m, ((ft i).totalDegree : ℚ)) * ∑ Q ∈ F₁, Q.degree := by
            calc
              _ ≤ ∑ Q ∈ F₁, Q.degree * ∏ i : Fin m, ((ft i).totalDegree : ℚ) := by
                apply Finset.sum_le_sum
                intro Q hQ
                have hQfilter : Q ∈ (dprofiles2ComponentFamily I₁).filter
                    (fun Z => ∃ x ∈ S, toC x ∈ Z) := by
                  dsimp [F₁, dprofiles2ComponentsMeeting] at hQ
                  exact hQ
                have hQprime : Q.IsIrreducible := (dprofiles2_mem_componentFamily I₁ Q |>.mp
                  (Finset.mem_filter.mp hQfilter).1).isPrime
                have hKQ :
                    Iall ≤ Q.ideal ⊔ Ideal.span (Set.range ft) := by
                  rw [hsplit]
                  exact sup_le ((dprofiles2_mem_componentFamily I₁ Q |>.mp
                    (Finset.mem_filter.mp hQfilter).1).le.trans le_sup_left) le_sup_right
                have hIsoQ : ∀ x ∈ S_Q Q, pointIdeal (toC x) ∈
                    (Q.ideal ⊔ Ideal.span (Set.range ft)).minimalPrimes := by
                  intro x hxQ
                  have hQvar : toC x ∈ Q := (Finset.mem_filter.mp hxQ).2
                  have hQle : Q.ideal ≤ pointIdeal (toC x) := by
                    intro p hp
                    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_iff]
                    intro y hy
                    have hyx : y = toC x := Set.mem_singleton_iff.mp hy
                    subst y
                    exact hQvar p hp
                  have htaille : Ideal.span (Set.range ft) ≤ pointIdeal (toC x) := by
                    apply Ideal.span_le.mpr
                    rintro p ⟨i, rfl⟩
                    change ft i ∈ MvPolynomial.vanishingIdeal ℂ {toC x}
                    rw [MvPolynomial.mem_vanishingIdeal_iff]
                    intro y hy
                    have hyx : y = toC x := Set.mem_singleton_iff.mp hy
                    subst y
                    exact hvan x (Finset.mem_filter.mp hxQ).1 i.succ
                  exact dprofiles2_minimal_of_intermediate Iall
                    (Q.ideal ⊔ Ideal.span (Set.range ft)) (pointIdeal (toC x))
                    hKQ (sup_le hQle htaille) (hiso x (Finset.mem_filter.mp hxQ).1)
                have hvanQ : ∀ x ∈ S_Q Q, ∀ i, MvPolynomial.eval (toC x) (ft i) = 0 := by
                  intro x hxQ i
                  exact hvan x (Finset.mem_filter.mp hxQ).1 i.succ
                have hdegQ : ∀ i, 1 ≤ (ft i).totalDegree := hdegTail
                have hIH := ih Q hQprime ft (S_Q Q) hvanQ hdegQ hIsoQ
                simpa only [Nat.cast_prod] using hIH
              _ = _ := by rw [← Finset.sum_mul]; ring
          have hsumdegree : (∑ Q ∈ F₁, Q.degree) ≤ f₀.totalDegree * V.degree := hbez₁
          have hprodTailNonneg : 0 ≤ ∏ i : Fin m, ((ft i).totalDegree : ℚ) := by positivity
          have hprod :
              (∏ i : Fin (m + 1), (f i).totalDegree) =
                f₀.totalDegree * ∏ i : Fin m, (ft i).totalDegree := by
            simp [f₀, ft, Fin.prod_univ_succ]
          calc
            (S.card : ℚ) ≤ _ := hcardCover.trans hsumIh
            _ ≤ (∏ i : Fin m, ((ft i).totalDegree : ℚ)) *
                (f₀.totalDegree * V.degree) :=
                  mul_le_mul_of_nonneg_left hsumdegree hprodTailNonneg
            _ = V.degree * (↑(∏ i : Fin (m + 1), (f i).totalDegree) : ℚ) := by
                  rw [hprod]
                  simp only [Nat.cast_mul, Nat.cast_prod]
                  ring


theorem dprofiles2_hilbertOfSet_image_le_card {α : Type*} {n : ℕ} (f : α → Point n)
    (S : Finset α) (D : ℕ) :
    hilbertOfSet (f '' (S : Set α)) D ≤ S.card := by
  classical
  let U := {x : α // x ∈ S}
  let T : Set (Point n) := f '' (S : Set α)
  let V : AffineVariety n := AffineVariety.closure T
  let I : Submodule ℂ (Poly n) := V.ideal.restrictScalars ℂ
  let ev : Poly n →ₐ[ℂ] (U → ℂ) :=
    AlgHom.pi fun x => MvPolynomial.aeval (fun i => f x.1 i)
  have hev (p : Poly n) (x : U) : ev p x = MvPolynomial.eval (f x.1) p := by
    simp [ev]
  have hevIdeal : I ≤ LinearMap.ker ev.toLinearMap := by
    intro p hp
    rw [LinearMap.mem_ker]
    have hpV : p ∈ V.ideal := by simpa [I] using hp
    change p ∈ MvPolynomial.vanishingIdeal ℂ T at hpV
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hpV
    ext x
    change ev p x = 0
    rw [hev]
    exact hpV (f x.1) ⟨x.1, x.2, rfl⟩
  let evQ₀ : Poly n ⧸ I →ₗ[ℂ] (U → ℂ) := I.liftQ ev.toLinearMap hevIdeal
  have hevQ₀inj : Function.Injective evQ₀ := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro q hq
      change q = 0
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective I q
      rw [LinearMap.mem_ker] at hq
      rw [Submodule.liftQ_apply] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      change p ∈ MvPolynomial.vanishingIdeal ℂ T
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have h := congrFun hq ⟨x, hx⟩
      change ev p ⟨x, hx⟩ = 0 at h
      rw [hev] at h
      exact h
    · exact bot_le
  let qEquiv : (Poly n ⧸ I) ≃ₗ[ℂ] (Poly n ⧸ V.ideal) :=
    Submodule.Quotient.restrictScalarsEquiv ℂ V.ideal
  let evQ : Poly n ⧸ V.ideal →ₗ[ℂ] (U → ℂ) := evQ₀.comp qEquiv.symm.toLinearMap
  have hevQinj : Function.Injective evQ := hevQ₀inj.comp qEquiv.symm.injective
  let evLin : V.restrictionSpace D →ₗ[ℂ] (U → ℂ) :=
    evQ.comp (Submodule.subtype (V.restrictionSpace D))
  have hevLinInj : Function.Injective evLin := by
    intro a b hab
    apply Subtype.ext
    exact hevQinj hab
  have hdim := LinearMap.finrank_le_finrank_of_injective hevLinInj
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  simpa [hilbertOfSet, V, T, U, AffineVariety.hilbert] using hdim

end TrackD
end DistinctDistances
