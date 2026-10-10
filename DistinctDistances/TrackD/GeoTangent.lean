import DistinctDistances.TrackD.Basic
import OAI.NumberTheory.PowerFree.HilbertGrowth
import OAI.NumberTheory.PowerFree.PointInterpolation

set_option maxHeartbeats 1000000

/-!
Generic tangent lemmas for `geo:generic-depth.tangent`.

For an irreducible variety `Z` of dimension `< d` we produce *one* point
`x0 ∈ Z` with a nonvanishing differential, and show every other variety is
either generically transverse to `Z` (witnessed by an explicit pair
polynomial built from ideal generators) or contained in the single flat
`x0 + tangentSpace Z x0`.  No smooth-point density or specialization
machinery is needed.
-/

namespace DistinctDistances
namespace TrackD
namespace GeoTangent

open Classical

variable {d : ℕ}

/-- Strict degree drop for a nonzero partial derivative (characteristic zero). -/
theorem totalDegree_pderiv_lt (f : Poly d) (j : Fin d)
    (hne : MvPolynomial.pderiv j f ≠ 0) :
    (MvPolynomial.pderiv j f).totalDegree < f.totalDegree := by
  have hmem : ∀ m ∈ (MvPolynomial.pderiv j f).support,
      m.sum (fun _ e => e) < f.totalDegree := by
    intro m hm
    have hcoeff : (MvPolynomial.pderiv j f).coeff m ≠ 0 :=
      Finsupp.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hcoeff
    have hfac : ((m j : ℂ) + 1) ≠ 0 := by
      have h1 : ((m j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      simpa [Nat.cast_add, Nat.cast_one] using h1
    have hg : f.coeff (m + Finsupp.single j 1) ≠ 0 := by
      intro hz
      exact hcoeff (by rw [hz, zero_mul])
    have hsupp : (m + Finsupp.single j 1) ∈ f.support :=
      Finsupp.mem_support_iff.mpr hg
    have hle := MvPolynomial.le_totalDegree hsupp
    have hsum : (m + Finsupp.single j 1).sum (fun _ e => e)
        = m.sum (fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl]
    omega
  have hT : 1 ≤ f.totalDegree := by
    have hsup0 : ∃ m, m ∈ (MvPolynomial.pderiv j f).support := by
      by_contra hc
      apply hne
      have hempty : (MvPolynomial.pderiv j f).support = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr (fun m hm => hc ⟨m, hm⟩)
      simpa using hempty
    obtain ⟨m, hm⟩ := hsup0
    have := hmem m hm
    omega
  have hle2 : (MvPolynomial.pderiv j f).support.sup (fun s => s.sum fun _ e => e)
      ≤ f.totalDegree - 1 := by
    apply Finset.sup_le_iff.mpr
    intro m hm
    have := hmem m hm
    omega
  have hsub : f.totalDegree - 1 < f.totalDegree := by omega
  unfold MvPolynomial.totalDegree
  exact lt_of_le_of_lt hle2 hsub

/-- If every partial derivative vanishes, the polynomial has total degree zero. -/
theorem totalDegree_eq_zero_of_pderiv_eq_zero (f : Poly d)
    (h : ∀ j, MvPolynomial.pderiv j f = 0) : f.totalDegree = 0 := by
  rcases eq_or_ne f.totalDegree 0 with h0 | hpos
  · exact h0
  · exfalso
    have hpos' : 0 < f.totalDegree := Nat.pos_of_ne_zero hpos
    have hsup : ∃ m ∈ f.support, 0 < m.sum (fun _ e => e) := by
      by_contra hc
      have hzero : f.totalDegree = 0 := by
        unfold MvPolynomial.totalDegree
        apply Nat.le_zero.mp
        apply Finset.sup_le_iff.mpr
        intro m hm
        by_contra hle
        exact hc ⟨m, hm, not_le.mp hle⟩
      omega
    obtain ⟨m, hm, hmsum⟩ := hsup
    have hm0 : m ≠ 0 := by
      intro hz
      simp [hz] at hmsum
    obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
      by_contra hc
      apply hm0
      apply Finsupp.ext
      intro j
      simp only [Finsupp.zero_apply]
      exact not_not.mp (fun hj => hc ⟨j, hj⟩)
    have hcoeff : f.coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
    have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr hj
    set s := m - Finsupp.single j 1 with hs
    have hadd : s + Finsupp.single j 1 = m := by
      ext i
      simp only [hs, Finsupp.add_apply]
      by_cases hij : i = j
      · subst hij
        simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj)]
      · simp [hij]
    have hsj : s j + 1 = m j := by
      have hsub : s j = m j - 1 := by
        simp [hs]
      omega
    have hzero : (MvPolynomial.pderiv j f).coeff s = 0 := by
      rw [h j]
      rfl
    rw [MvPolynomial.coeff_pderiv, hadd] at hzero
    have hfac : ((s j : ℂ) + 1) ≠ 0 := by
      have h1 : ((s j + 1 : ℕ) : ℂ) ≠ 0 := by
        rw [hsj]
        exact Nat.cast_ne_zero.mpr hj
      simpa [Nat.cast_add, Nat.cast_one] using h1
    rcases mul_eq_zero.mp hzero with h | h
    · exact hcoeff h
    · exact hfac h

/-- The whole affine space has dimension `d`. -/
theorem affineDimension_bot :
    OAI.QuarticPowerFree.affineDimension (⊥ : Ideal (Poly d)) = d := by
  classical
  apply le_antisymm
  · obtain ⟨j, hj, -⟩ := OAI.QuarticPowerFree.affineDimension_independent_coordinates
      (⊥ : Ideal (Poly d)) (by
        intro h
        have h1 : (1 : Poly d) ∈ (⊥ : Ideal (Poly d)) := by
          rw [h]
          trivial
        rw [Submodule.mem_bot] at h1
        exact one_ne_zero h1)
    have hcard := Fintype.card_le_of_injective j hj
    simpa using hcard
  · have hdim : OAI.QuarticPowerFree.affineDimension (⊥ : Ideal (Poly d))
        = (OAI.QuarticPowerFree.coordinateHilbert
          (⊥ : Ideal (MvPolynomial (Fin d) ℂ))).natDegree := rfl
    rw [hdim]
    have hRdeg : (Polynomial.C ((d.factorial : ℚ))⁻¹ * Polynomial.X ^ d :
        Polynomial ℚ).natDegree = d := by
      apply Polynomial.natDegree_C_mul_X_pow
      exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero d)
    conv_lhs => rw [← hRdeg]
    apply OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
    · filter_upwards with T
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C]
      positivity
    · have hev := OAI.QuarticPowerFree.coordinateHilbert_eventually
        (⊥ : Ideal (Poly d))
      have hinj : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal (Poly d))) :=
        (Ideal.Quotient.mk_bijective_iff_eq_bot _ |>.mpr rfl).1
      have hcomp : MvPolynomial.aeval
            (fun a : Fin d => Ideal.Quotient.mk (⊥ : Ideal (Poly d))
              (MvPolynomial.X a))
          = (Ideal.Quotient.mkₐ ℂ (⊥ : Ideal (Poly d))).comp
            (MvPolynomial.aeval MvPolynomial.X) := by
        apply MvPolynomial.algHom_ext
        intro a
        simp only [MvPolynomial.aeval_X, AlgHom.comp_apply,
          Ideal.Quotient.mkₐ_eq_mk]
      have hid2 : MvPolynomial.aeval (MvPolynomial.X : Fin d → Poly d)
          = AlgHom.id ℂ (Poly d) := MvPolynomial.aeval_X_left
      have hid : AlgebraicIndependent ℂ (fun a : Fin d =>
          Ideal.Quotient.mk (⊥ : Ideal (Poly d)) (MvPolynomial.X a)) := by
        show Function.Injective (MvPolynomial.aeval _)
        rw [hcomp, hid2, AlgHom.comp_id]
        have hfn : ⇑(Ideal.Quotient.mkₐ ℂ (⊥ : Ideal (Poly d)))
            = ⇑(Ideal.Quotient.mk (⊥ : Ideal (Poly d))) :=
          Ideal.Quotient.mkₐ_eq_mk ℂ _
        rw [hfn]
        exact hinj
      filter_upwards [hev] with T hT
      have hcho := OAI.QuarticPowerFree.independent_coordinates_hilbert_lower
        (⊥ : Ideal (Poly d)) (id : Fin d → Fin d) hid T
      have hcast : ((Polynomial.C ((d.factorial : ℚ))⁻¹ * Polynomial.X ^ d :
          Polynomial ℚ).eval (T : ℚ)) ≤ (((T + d).choose d : ℕ) : ℚ) := by
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C]
        have hposM : (0 : ℚ) < (d.factorial : ℚ) * (T.factorial : ℚ) := by
          apply mul_pos <;> exact_mod_cast Nat.factorial_pos _
        have hTd : d ≤ T + d := Nat.le_add_left _ _
        have hmul : ((T + d).choose d : ℚ) * ((d.factorial : ℚ) * (T.factorial : ℚ))
            = ((T + d).factorial : ℚ) := by
          have h := Nat.choose_mul_factorial_mul_factorial hTd
          rw [show T + d - d = T by omega, mul_assoc] at h
          exact_mod_cast h
        have hchoose : ((T + d).choose d : ℚ)
            = ((T + d).factorial : ℚ) / ((d.factorial : ℚ) * (T.factorial : ℚ)) := by
          rw [eq_div_iff (ne_of_gt hposM)]
          exact hmul
        have hfact : ((T + d).factorial : ℚ)
            = (T.factorial : ℚ) * ∏ i ∈ Finset.range d, ((T : ℚ) + 1 + i) := by
          have h1 : ∏ i ∈ Finset.range (T + d), ((i : ℚ) + 1)
              = ((T + d).factorial : ℚ) := by
            exact_mod_cast Finset.prod_range_add_one_eq_factorial (T + d)
          have h2 : ∏ i ∈ Finset.range T, ((i : ℚ) + 1)
              = (T.factorial : ℚ) := by
            exact_mod_cast Finset.prod_range_add_one_eq_factorial T
          rw [← h2, ← h1, Finset.prod_range_add (fun i : ℕ => ((i : ℚ) + 1)) T d]
          congr 1
          apply Finset.prod_congr rfl
          intro i _
          push_cast
          ring
        have hprod : ((T : ℚ)) ^ d
            ≤ ∏ i ∈ Finset.range d, ((T : ℚ) + 1 + i) := by
          calc ((T : ℚ)) ^ d = ∏ _i ∈ Finset.range d, (T : ℚ) := by
                rw [Finset.prod_const, Finset.card_range]
            _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
                (fun i _ => by
                  have h1 : (0 : ℚ) ≤ 1 + ((i : ℕ) : ℚ) := by positivity
                  have h2 : (T : ℚ) + (1 + ((i : ℕ) : ℚ))
                      = (T : ℚ) + 1 + ((i : ℕ) : ℚ) := by ring
                  rw [← h2]
                  exact le_add_of_nonneg_right h1)
        rw [hchoose, le_div_iff₀ hposM]
        have hne : ((d.factorial : ℚ)) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero d
        have hsimp : ((d.factorial : ℚ))⁻¹ * (T : ℚ) ^ d
            * ((d.factorial : ℚ) * T.factorial)
            = (T : ℚ) ^ d * T.factorial := by
          calc ((d.factorial : ℚ))⁻¹ * (T : ℚ) ^ d
                * ((d.factorial : ℚ) * T.factorial)
              = ((d.factorial : ℚ))⁻¹ * (d.factorial : ℚ)
                * ((T : ℚ) ^ d * T.factorial) := by ring
            _ = (T : ℚ) ^ d * T.factorial := by
                rw [inv_mul_cancel₀ hne, one_mul]
        rw [hsimp, hfact, mul_comm ((T : ℚ) ^ d) (T.factorial)]
        exact mul_le_mul_of_nonneg_left hprod (by positivity)
      exact le_trans hcast (le_trans (by exact_mod_cast hcho) (le_of_eq hT))

/-- Pair polynomial recording `differential f y (y - x)`. -/
noncomputable def pairDeriv (f : Poly d) : PairPoly d :=
  ∑ j : Fin d, MvPolynomial.rename Sum.inr (MvPolynomial.pderiv j f) *
    (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inl j))

theorem eval_pairDeriv (f : Poly d) (x y : Point d) :
    MvPolynomial.eval (pairPt x y) (pairDeriv f) = differential f y (y - x) := by
  unfold pairDeriv differential
  rw [MvPolynomial.eval_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hcomp : (pairPt x y ∘ Sum.inr) = y := rfl
  have hinr : pairPt x y (Sum.inr j) = y j := rfl
  have hinl : pairPt x y (Sum.inl j) = x j := rfl
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_rename, MvPolynomial.eval_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_X, hcomp, hinr, hinl,
    ← MvPolynomial.aeval_eq_eval, LinearMap.smul_apply, LinearMap.proj_apply,
    Pi.sub_apply, smul_eq_mul]

/-- Pair polynomial recording `differential f x (y - x)` (source version). -/
noncomputable def pairDerivSrc (f : Poly d) : PairPoly d :=
  ∑ j : Fin d, MvPolynomial.rename Sum.inl (MvPolynomial.pderiv j f) *
    (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inl j))

theorem eval_pairDerivSrc (f : Poly d) (x y : Point d) :
    MvPolynomial.eval (pairPt x y) (pairDerivSrc f) = differential f x (y - x) := by
  unfold pairDerivSrc differential
  rw [MvPolynomial.eval_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hcomp : (pairPt x y ∘ Sum.inl) = x := rfl
  have hinr : pairPt x y (Sum.inr j) = y j := rfl
  have hinl : pairPt x y (Sum.inl j) = x j := rfl
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_rename, MvPolynomial.eval_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_X, hcomp, hinr, hinl,
    ← MvPolynomial.aeval_eq_eval, LinearMap.smul_apply, LinearMap.proj_apply,
    Pi.sub_apply, smul_eq_mul]

theorem differential_add (f g : Poly d) (x v : Point d) :
    differential (f + g) x v = differential f x v + differential g x v := by
  simp only [differential, LinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Derivation.map_add _ f g, map_add, add_smul, LinearMap.add_apply]

theorem differential_mul (a b : Poly d) (x v : Point d) :
    differential (a * b) x v
      = MvPolynomial.aeval x a • differential b x v
        + MvPolynomial.aeval x b • differential a x v := by
  simp only [differential, LinearMap.sum_apply,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.pderiv_mul, map_add, add_smul]
  simp only [map_mul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- A variety of dimension `< d` has a point with nonvanishing differential. -/
theorem exists_diffNonzero (Z : AffineVariety d) (m : ℕ)
    (hZ : Z.IsIrreducible) (hdim : Z.dimension = m) (hlt : m < d)
    (hne : Z.points.Nonempty) :
    ∃ x0 ∈ Z.points, ∃ f0 ∈ Z.ideal, differential f0 x0 ≠ 0 := by
  classical
  have hdim' : OAI.QuarticPowerFree.affineDimension Z.ideal = m := hdim
  have htop : Z.ideal ≠ ⊤ := by
    intro htop
    have hempty : Z.points = ∅ := by
      rw [AffineVariety.points, htop, MvPolynomial.zeroLocus_top]
      rfl
    exact hne.ne_empty hempty
  have hbot : Z.ideal ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdim'
    rw [affineDimension_bot] at hdim'
    omega
  have hex : ∃ g ∈ Z.ideal, g ≠ 0 := by
    by_contra hc
    apply hbot
    rw [eq_bot_iff]
    intro g hg
    rw [Submodule.mem_bot]
    by_contra hne2
    exact hc ⟨g, hg, hne2⟩
  have hexn : ∃ n, ∃ g ∈ Z.ideal, g ≠ 0 ∧ g.totalDegree = n := by
    obtain ⟨g, hg, hg0⟩ := hex
    exact ⟨g.totalDegree, g, hg, hg0, rfl⟩
  obtain ⟨g, hgI, hg0, hgn⟩ := Nat.find_spec hexn
  have hmin : ∀ g' ∈ Z.ideal, g' ≠ 0 → Nat.find hexn ≤ g'.totalDegree := fun g' hg' hne' =>
    Nat.find_min' hexn ⟨g', hg', hne', rfl⟩
  have hconst : ∀ c : ℂ, MvPolynomial.C c ∈ Z.ideal → c = 0 := by
    intro c hc
    by_contra hcc
    have h1mem : (1 : Poly d) ∈ Z.ideal := by
      have hmem : MvPolynomial.C c⁻¹ • MvPolynomial.C c ∈ Z.ideal :=
        Submodule.smul_mem _ _ hc
      rwa [smul_eq_mul, ← map_mul, inv_mul_cancel₀ hcc, map_one] at hmem
    have hle : Ideal.span ({1} : Set (Poly d)) ≤ Z.ideal :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h1mem)
    rw [Ideal.span_singleton_one] at hle
    exact htop (top_unique hle)
  have hdeg0 : g.totalDegree ≠ 0 := by
    intro hz
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hz
    rw [hz] at hgI
    have hc0 : g.coeff 0 = 0 := hconst _ hgI
    rw [hz, hc0] at hg0
    exact hg0 (by simp)
  have hpart0 : ∃ j, MvPolynomial.pderiv j g ≠ 0 := by
    by_contra hc
    apply hdeg0
    apply totalDegree_eq_zero_of_pderiv_eq_zero
    intro j
    by_contra hj
    exact hc ⟨j, hj⟩
  have hpartout : ∃ j, MvPolynomial.pderiv j g ∉ Z.ideal := by
    by_contra hc
    obtain ⟨j0, hj0⟩ := hpart0
    have hmem : MvPolynomial.pderiv j0 g ∈ Z.ideal := by
      by_contra hmem
      exact hc ⟨j0, hmem⟩
    have hlt' := totalDegree_pderiv_lt g j0 hj0
    have hle := hmin _ hmem hj0
    omega
  obtain ⟨j, hjout⟩ := hpartout
  have hvan : MvPolynomial.pderiv j g ∉ MvPolynomial.vanishingIdeal ℂ Z.points := by
    rw [AffineVariety.vanishingIdeal_points]
    exact hjout
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hvan
  have hex2 : ∃ x0 ∈ Z.points,
      MvPolynomial.aeval x0 (MvPolynomial.pderiv j g) ≠ 0 := by
    by_contra hc2
    apply hvan
    intro x hx
    by_contra hne2
    exact hc2 ⟨x, hx, hne2⟩
  obtain ⟨x0, hx0, hx0ne⟩ := hex2
  refine ⟨x0, hx0, g, hgI, ?_⟩
  intro hzero
  apply hx0ne
  have hval : differential g x0 (Pi.single j 1)
      = MvPolynomial.aeval x0 (MvPolynomial.pderiv j g) := by
    have hsum : ∀ i : Fin d, (MvPolynomial.aeval x0 (MvPolynomial.pderiv i g))
          • ((LinearMap.proj i : (Point d) →ₗ[ℂ] ℂ)) (Pi.single j 1 : Point d)
        = if i = j then MvPolynomial.aeval x0 (MvPolynomial.pderiv j g) else 0 := by
      intro i
      rw [LinearMap.proj_apply]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        simp
      · rw [if_neg hij]
        simp [hij]
    simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply, hsum]
    rw [Finset.sum_eq_single j (fun b _ hbj => by rw [if_neg hbj])
      (fun hcon => by simp at hcon)]
    simp
  rw [hzero, LinearMap.zero_apply] at hval
  exact hval.symm

/-- Every variety is either generically transverse to `Z` or contained in the
tangent flat at `x0`.  No hypotheses on `Z` or `W` beyond `x0 ∈ Z`. -/
theorem perW (Z : AffineVariety d) (x0 : Point d) (hx0 : x0 ∈ Z.points)
    (W : AffineVariety d) :
    ForGeneralPair W Z (fun x y => y - x ∉ Z.tangentSpace y) ∨
      W.points ⊆ ↑(AffineSubspace.mk' x0 (Z.tangentSpace x0)) := by
  classical
  have hFG : Z.ideal.FG := Ideal.fg_of_isNoetherianRing Z.ideal
  obtain ⟨s, hs⟩ := hFG
  by_cases hex : ∃ x ∈ W.points, ∃ y ∈ Z.points, ∃ k ∈ s,
      MvPolynomial.eval (pairPt x y) (pairDeriv k) ≠ 0
  · obtain ⟨x, hx, y, hy, k, hks, hne⟩ := hex
    refine Or.inl ⟨pairDeriv k, ⟨x, hx, y, hy, hne⟩, ?_⟩
    intro x' hx' y' hy' hne'
    rw [eval_pairDeriv] at hne'
    intro hmem
    have hkmem : k ∈ Z.ideal := by
      have hks' : k ∈ Ideal.span (↑s : Set (Poly d)) := Ideal.subset_span hks
      rwa [hs] at hks'
    have hsub : Z.tangentSpace y' ≤ LinearMap.ker (differential k y') := by
      have hle := iInf_le (fun f : ↥Z.ideal => LinearMap.ker (differential ↑f y'))
        ⟨k, hkmem⟩
      show (⨅ f : ↥Z.ideal, LinearMap.ker (differential ↑f y')) ≤ _
      exact hle
    exact hne' (LinearMap.mem_ker.mp (hsub hmem))
  · have hall : ∀ x ∈ W.points, ∀ y ∈ Z.points, ∀ k ∈ s,
        MvPolynomial.eval (pairPt x y) (pairDeriv k) = 0 := by
      intro x hx y hy k hks
      by_contra hne2
      exact hex ⟨x, hx, y, hy, k, hks, hne2⟩
    refine Or.inr ?_
    intro w hw
    have hmem : w ∈ AffineSubspace.mk' x0 (Z.tangentSpace x0) := by
      rw [AffineSubspace.mem_mk']
      have hvsub : w -ᵥ x0 = w - x0 := rfl
      rw [hvsub]
      show (w - x0) ∈ (⨅ f : ↥Z.ideal, LinearMap.ker (differential ↑f x0))
      rw [Submodule.mem_iInf]
      intro f
      rw [LinearMap.mem_ker]
      set v : Point d := w - x0 with hv
      have hvan : ∀ f ∈ Ideal.span (↑s : Set (Poly d)),
          MvPolynomial.aeval x0 f = 0 := by
        intro f hf
        rw [hs] at hf
        have hmemI : f ∈ MvPolynomial.vanishingIdeal ℂ Z.points := by
          rw [AffineVariety.vanishingIdeal_points]
          exact hf
        rw [MvPolynomial.mem_vanishingIdeal_iff] at hmemI
        exact hmemI x0 hx0
      have hfi : f.val ∈ Ideal.span (↑s : Set (Poly d)) := by
        rw [hs]
        exact f.property
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hfi
      · intro x hx
        have h0 := hall w hw x0 hx0 x (Finset.mem_coe.mp hx)
        rw [eval_pairDeriv] at h0
        have hvv : v = -(x0 - w) := by rw [hv]; abel
        rw [hvv, map_neg, h0, neg_zero]
      · simp [differential]
      · intro x y hx hy ihx ihy
        rw [differential_add, ihx, ihy, add_zero]
      · intro a x hx ih
        have hxvan := hvan x hx
        rw [smul_eq_mul, differential_mul, ih, hxvan]
        simp
    exact hmem

/-- Source version: `Z` comes first and the tangent is evaluated at `x`. -/
theorem perW_source (Z : AffineVariety d) (x0 : Point d) (hx0 : x0 ∈ Z.points)
    (W : AffineVariety d) :
    ForGeneralPair Z W (fun x y => y - x ∉ Z.tangentSpace x) ∨
      W.points ⊆ ↑(AffineSubspace.mk' x0 (Z.tangentSpace x0)) := by
  classical
  have hFG : Z.ideal.FG := Ideal.fg_of_isNoetherianRing Z.ideal
  obtain ⟨s, hs⟩ := hFG
  by_cases hex : ∃ x ∈ Z.points, ∃ y ∈ W.points, ∃ k ∈ s,
      MvPolynomial.eval (pairPt x y) (pairDerivSrc k) ≠ 0
  · obtain ⟨x, hx, y, hy, k, hks, hne⟩ := hex
    refine Or.inl ⟨pairDerivSrc k, ⟨x, hx, y, hy, hne⟩, ?_⟩
    intro x' hx' y' hy' hne'
    rw [eval_pairDerivSrc] at hne'
    intro hmem
    have hkmem : k ∈ Z.ideal := by
      have hks' : k ∈ Ideal.span (↑s : Set (Poly d)) := Ideal.subset_span hks
      rwa [hs] at hks'
    have hsub : Z.tangentSpace x' ≤ LinearMap.ker (differential k x') := by
      have hle2 := iInf_le
        (fun f : ↥Z.ideal => LinearMap.ker (differential ↑f x')) ⟨k, hkmem⟩
      show (⨅ f : ↥Z.ideal, LinearMap.ker (differential ↑f x')) ≤ _
      exact hle2
    exact hne' (LinearMap.mem_ker.mp (hsub hmem))
  · have hall : ∀ x ∈ Z.points, ∀ y ∈ W.points, ∀ k ∈ s,
        MvPolynomial.eval (pairPt x y) (pairDerivSrc k) = 0 := by
      intro x hx y hy k hks
      by_contra hne2
      exact hex ⟨x, hx, y, hy, k, hks, hne2⟩
    refine Or.inr ?_
    intro w hw
    have hmem : w ∈ AffineSubspace.mk' x0 (Z.tangentSpace x0) := by
      rw [AffineSubspace.mem_mk']
      have hvsub : w -ᵥ x0 = w - x0 := rfl
      rw [hvsub]
      show (w - x0) ∈ (⨅ f : ↥Z.ideal, LinearMap.ker (differential ↑f x0))
      rw [Submodule.mem_iInf]
      intro f
      rw [LinearMap.mem_ker]
      have hvan : ∀ f ∈ Ideal.span (↑s : Set (Poly d)),
          MvPolynomial.aeval x0 f = 0 := by
        intro f hf
        rw [hs] at hf
        have hmemI : f ∈ MvPolynomial.vanishingIdeal ℂ Z.points := by
          rw [AffineVariety.vanishingIdeal_points]
          exact hf
        rw [MvPolynomial.mem_vanishingIdeal_iff] at hmemI
        exact hmemI x0 hx0
      have hfi : f.val ∈ Ideal.span (↑s : Set (Poly d)) := by
        rw [hs]
        exact f.property
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hfi
      · intro g hg
        have h0 := hall x0 hx0 w hw g (Finset.mem_coe.mp hg)
        rwa [eval_pairDerivSrc] at h0
      · simp [differential]
      · intro x y hx hy ihx ihy
        rw [differential_add, ihx, ihy, add_zero]
      · intro a x hx ih
        have hxvan := hvan x hx
        rw [smul_eq_mul, differential_mul, ih, hxvan]
        simp
    exact hmem

end GeoTangent
end TrackD
end DistinctDistances
