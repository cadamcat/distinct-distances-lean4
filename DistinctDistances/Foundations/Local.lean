import DistinctDistances.TrackA.ChartCarrierTransportSupport
import DistinctDistances.TrackA.LocalPolynomialComparisonSupport
import OAI.NumberTheory.PowerFree.GenericCuts
import OAI.NumberTheory.PowerFree.NormalMonomials
import OAI.NumberTheory.PowerFree.HilbertGrowth
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension
import OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension
import OAI.RingTheory.Multiplicity.LinearNormalizationDimension
import OAI.RingTheory.Multiplicity.LechHilbertSerre
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks
import DistinctDistances.Foundations.ALocaldimAux

/-! Public chart-invariance bridge over the original shared local model. -/

namespace DistinctDistances
noncomputable section

namespace AffineVariety
variable {n : ℕ}

theorem ideal_le_pointIdeal_of_mem {V : AffineVariety n} {x : Point n}
    (hx : x ∈ V) : V.ideal ≤ pointIdeal x := by
  classical
  have hxvan : ∀ f ∈ V.ideal, MvPolynomial.aeval x f = 0 := by
    change x ∈ MvPolynomial.zeroLocus ℂ V.ideal at hx
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    intro f hf
    simpa [MvPolynomial.aeval_eq_eval] using hx f hf
  intro f hf
  change f ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n))
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).2 (hxvan f hf)

/-- Global Hilbert dimension equals transcendence degree toNat. -/
theorem dimension_eq_trdeg_toNat (V : AffineVariety n) [V.ideal.IsPrime] :
    V.dimension = (Algebra.trdeg ℂ (Poly n ⧸ V.ideal)).toNat := by
  have h := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg (K := ℂ)
    V.ideal (OAI.QuarticPowerFree.coordinateHilbert V.ideal)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal)
  change ((OAI.QuarticPowerFree.coordinateHilbert V.ideal).natDegree : Cardinal) = _ at h
  have h2 := congrArg Cardinal.toNat h
  simpa [AffineVariety.dimension, OAI.QuarticPowerFree.affineDimension] using h2

/-- The residue field at a closed complex point has Krull dimension zero. -/
theorem krullDim_quotient_pointIdeal (x : Point n) :
    ringKrullDim (Poly n ⧸ pointIdeal x) = (0 : WithBot ℕ∞) := by
  classical
  have hker : RingHom.ker (MvPolynomial.aeval x : Poly n →ₐ[ℂ] ℂ).toRingHom
      = pointIdeal x := by
    ext f
    simp [pointIdeal, MvPolynomial.aeval_eq_eval]
  have hsurj : Function.Surjective
      (MvPolynomial.aeval x : Poly n →ₐ[ℂ] ℂ).toRingHom := by
    intro c
    exact ⟨MvPolynomial.C c, by simp⟩
  have e : (Poly n ⧸ pointIdeal x) ≃ₐ[ℂ] ℂ :=
    hker ▸ Ideal.quotientKerAlgEquivOfSurjective
      (f := (MvPolynomial.aeval x : Poly n →ₐ[ℂ] ℂ)) hsurj
  have h := e.ringKrullDim
  rw [ringKrullDim_eq_zero_of_field ℂ] at h
  exact h

/-- Local Krull dimension at a closed point of a prime equals global Krull dimension. -/
theorem krullDim_local_eq_global (V : AffineVariety n) (x : Point n)
    [hprime : V.ideal.IsPrime] (hle : V.ideal ≤ pointIdeal x) :
    ringKrullDim (PointLocalRing x ⧸ localizedIdeal V.ideal x) =
      ringKrullDim (Poly n ⧸ V.ideal) := by
  classical
  have : (pointIdeal x).IsPrime := (pointIdeal_isMaximal x).isPrime
  have hpair := OAI.PiExponentJets.W24.polynomial_prime_pair_local_dimension
    (k := ℂ) (σ := Fin n) V.ideal (pointIdeal x) hle
  have hres : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ pointIdeal x) = (0 : WithBot ℕ∞) :=
    krullDim_quotient_pointIdeal x
  rw [hres, add_zero] at hpair
  have heq : localizedIdeal V.ideal x =
      OAI.PiExponentSiegel.W23.parameterLocalizedIdeal V.ideal (pointIdeal x) := rfl
  rw [heq]
  exact hpair

/-- Global Hilbert dimension (as WithBot) equals Krull dimension of coordinate ring. -/
theorem dimension_cast_eq_krullDim (V : AffineVariety n) [V.ideal.IsPrime] :
    (V.dimension : WithBot ℕ∞) = ringKrullDim (Poly n ⧸ V.ideal) := by
  have hdim := dimension_eq_trdeg_toNat V
  have hkrull := OAI.PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg
    (k := ℂ) (B := (Poly n ⧸ V.ideal))
  rw [hdim, hkrull]

/-- Translated generators at x: e_i = X_i - C(x_i). -/
noncomputable def transGen (x : Point n) (i : Fin n) : Poly n :=
  MvPolynomial.X i - MvPolynomial.C (x i)

theorem totalDegree_transGen_le (x : Point n) (i : Fin n) :
    (transGen x i).totalDegree ≤ 1 := by
  unfold transGen
  calc (MvPolynomial.X i - MvPolynomial.C (x i)).totalDegree
      ≤ max (MvPolynomial.X i).totalDegree (MvPolynomial.C (x i)).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ 1 := by
        simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]

theorem transGen_mem_pointIdeal (x : Point n) (i : Fin n) :
    transGen x i ∈ pointIdeal x := by
  change transGen x i ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n))
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro y hy
  simp only [Set.mem_singleton_iff] at hy
  subst hy
  unfold transGen
  simp

theorem transAeval_surjective (x : Point n) :
    Function.Surjective (MvPolynomial.aeval (fun i => transGen x i) :
      Poly n →ₐ[ℂ] Poly n) := by
  classical
  have hX : ∀ i : Fin n, MvPolynomial.X i ∈
      (MvPolynomial.aeval (fun i => transGen x i) : Poly n →ₐ[ℂ] Poly n).range := by
    intro i
    refine ⟨MvPolynomial.X i + MvPolynomial.C (x i), ?_⟩
    simp [transGen, map_add]
  have hrange : (MvPolynomial.aeval (fun i => transGen x i) :
      Poly n →ₐ[ℂ] Poly n).range = ⊤ := by
    rw [eq_top_iff, ← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact hX i
  intro y
  have hy : y ∈ (MvPolynomial.aeval (fun i => transGen x i) :
    Poly n →ₐ[ℂ] Poly n).range := hrange ▸ Algebra.mem_top
  exact hy

theorem totalDegree_transMonomial_le (x : Point n) (d : Fin n →₀ ℕ) :
    ((∏ i ∈ d.support, (transGen x i) ^ (d i) : Poly n)).totalDegree ≤
      d.sum (fun _ e => e) := by
  calc ((∏ i ∈ d.support, (transGen x i) ^ (d i) : Poly n)).totalDegree
      ≤ ∑ i ∈ d.support, ((transGen x i) ^ (d i)).totalDegree :=
        MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, (d i) * 1 := by
        apply Finset.sum_le_sum
        intro i _
        calc ((transGen x i) ^ (d i)).totalDegree
            ≤ (d i) * (transGen x i).totalDegree := MvPolynomial.totalDegree_pow _ _
          _ ≤ (d i) * 1 := Nat.mul_le_mul_left _ (totalDegree_transGen_le x i)
    _ = d.sum (fun _ e => e) := by
        simp [Finsupp.sum]

theorem pointIdeal_finsetProd_pow (x : Point n) (d : Fin n →₀ ℕ)
    (s : Finset (Fin n)) :
    (∏ i ∈ s, pointIdeal x ^ (d i) : Ideal (Poly n)) =
      pointIdeal x ^ (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has, pow_add, ih]

theorem transMonomial_mem_pow (x : Point n) (d : Fin n →₀ ℕ) :
    (∏ i ∈ d.support, (transGen x i) ^ (d i) : Poly n) ∈
      pointIdeal x ^ (d.sum (fun _ e => e)) := by
  classical
  have hmem : ∀ i ∈ d.support, (transGen x i) ^ (d i) ∈ pointIdeal x ^ (d i) :=
    fun i _ => Ideal.pow_mem_pow (transGen_mem_pointIdeal x i) (d i)
  have hprod : (∏ i ∈ d.support, (transGen x i) ^ (d i) : Poly n) ∈
      ∏ i ∈ d.support, pointIdeal x ^ (d i) := Ideal.prod_mem_prod hmem
  have hpow : (∏ i ∈ d.support, pointIdeal x ^ (d i) : Ideal (Poly n)) =
      pointIdeal x ^ (∑ i ∈ d.support, d i) :=
    pointIdeal_finsetProd_pow x d d.support
  have hsum : (∑ i ∈ d.support, d i) = d.sum (fun _ e => e) := by
    simp [Finsupp.sum]
  rwa [hpow, hsum] at hprod

theorem transDecomp (x : Point n) (t : ℕ) (f : Poly n) :
    ∃ low high : Poly n, f = low + high ∧ low.totalDegree ≤ t ∧
      high ∈ pointIdeal x ^ (t + 1) := by
  classical
  obtain ⟨g, hg⟩ := transAeval_surjective x f
  let lowSet := g.support.filter (fun d => d.sum (fun _ e => e) ≤ t)
  let highSet := g.support.filter (fun d => t < d.sum (fun _ e => e))
  have hdisj : Disjoint lowSet highSet := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    simp only [lowSet, highSet, Finset.mem_filter] at hd1 hd2
    omega
  have hunion : lowSet ∪ highSet = g.support := by
    ext d
    simp only [lowSet, highSet, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
    · intro hm
      by_cases h : d.sum (fun _ e => e) ≤ t
      · exact Or.inl ⟨hm, h⟩
      · exact Or.inr ⟨hm, by omega⟩
  have hgEq : g = (∑ d ∈ lowSet, MvPolynomial.monomial d (g.coeff d)) +
      (∑ d ∈ highSet, MvPolynomial.monomial d (g.coeff d)) := by
    rw [← Finset.sum_union hdisj, hunion]
    exact MvPolynomial.as_sum g
  have haeval_eq : ∀ d : Fin n →₀ ℕ, ∀ c : ℂ,
      (MvPolynomial.aeval (fun i => transGen x i) : Poly n →ₐ[ℂ] Poly n)
        (MvPolynomial.monomial d c) =
        MvPolynomial.C c * (∏ i ∈ d.support, (transGen x i) ^ (d i)) := by
    intro d c
    rw [MvPolynomial.aeval_monomial]
    simp [Finsupp.prod]
  refine ⟨(MvPolynomial.aeval (fun i => transGen x i) :
      Poly n →ₐ[ℂ] Poly n) (∑ d ∈ lowSet, MvPolynomial.monomial d (g.coeff d)),
    (MvPolynomial.aeval (fun i => transGen x i) :
      Poly n →ₐ[ℂ] Poly n) (∑ d ∈ highSet, MvPolynomial.monomial d (g.coeff d)),
    by rw [← map_add, ← hgEq, hg], ?_, ?_⟩
  · rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro d hd
    simp only [lowSet, Finset.mem_filter] at hd
    rw [haeval_eq]
    calc (MvPolynomial.C (g.coeff d) *
        (∏ i ∈ d.support, (transGen x i) ^ (d i))).totalDegree
        ≤ (MvPolynomial.C (g.coeff d)).totalDegree +
          (∏ i ∈ d.support, (transGen x i) ^ (d i)).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + t := by
          apply Nat.add_le_add _ _
          · rw [MvPolynomial.totalDegree_C]
          · exact (totalDegree_transMonomial_le x d).trans hd.2
      _ = t := Nat.zero_add t
  · rw [map_sum]
    apply Ideal.sum_mem
    intro d hd
    simp only [highSet, Finset.mem_filter] at hd
    rw [haeval_eq]
    apply Ideal.mul_mem_left
    have hmem := transMonomial_mem_pow x d
    have hle : pointIdeal x ^ (d.sum (fun _ e => e)) ≤ pointIdeal x ^ (t + 1) :=
      Ideal.pow_le_pow_right (by omega : t + 1 ≤ d.sum (fun _ e => e))
    exact hle hmem

theorem finrank_quotient_le_hilbert (V : AffineVariety n) (x : Point n)
    (t : ℕ) :
    Module.finrank ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) ≤ V.hilbert t := by
  classical
  let K : Ideal (Poly n) := V.ideal ⊔ pointIdeal x ^ (t + 1)
  have hIK : V.ideal ≤ K := le_sup_left
  let q : (Poly n ⧸ V.ideal) →ₗ[ℂ] (Poly n ⧸ K) :=
    (Ideal.Quotient.factorₐ ℂ hIK).toLinearMap
  let f : V.restrictionSpace t →ₗ[ℂ] (Poly n ⧸ K) :=
    { toFun := fun y => q y.val
      map_add' := fun a b => q.map_add a.val b.val
      map_smul' := fun c a => q.map_smul c a.val }
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨low, high, hgh, hlow_deg, hhigh_mem⟩ := transDecomp x t g
    have hlow_mem : low ∈ OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t := by
      rwa [OAI.QuarticPowerFree.mem_totalSpace]
    have hsub : g - low ∈ K := by
      have h_eq : g - low = high := by linear_combination hgh
      rw [h_eq]
      exact Ideal.mem_sup_right hhigh_mem
    have himg : q ((Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap low) =
        Ideal.Quotient.mk K g := by
      have hQ : (Ideal.Quotient.factorₐ ℂ hIK)
          ((Ideal.Quotient.mkₐ ℂ V.ideal) low) =
          (Ideal.Quotient.mkₐ ℂ K) low := rfl
      have hQlin : q ((Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap low) =
          (Ideal.Quotient.mkₐ ℂ K) low := hQ
      rw [hQlin]
      show Ideal.Quotient.mk K low = Ideal.Quotient.mk K g
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      have h_neg : low - g = -(g - low) := by abel
      rw [h_neg]
      exact neg_mem hsub
    refine ⟨⟨(Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap low,
      ⟨low, hlow_mem, rfl⟩⟩, ?_⟩
    show q ((Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap low) = _
    rw [himg]
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

theorem isUnit_quotient_of_not_mem_pointIdeal (x : Point n)
    (K : Ideal (Poly n)) (t : ℕ) (hKsup : pointIdeal x ^ (t + 1) ≤ K)
    (b : Poly n) (hb : b ∉ pointIdeal x) :
    IsUnit (Ideal.Quotient.mk K b) := by
  classical
  have hp_max := pointIdeal_isMaximal x
  have hJ : K ⊔ Ideal.span {b} = ⊤ := by
    by_contra hne
    obtain ⟨m, hm_max, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpow_mem : pointIdeal x ^ (t + 1) ≤ m :=
      hKsup.trans (le_trans le_sup_left hle)
    have hp_le : pointIdeal x ≤ m := by
      intro a ha
      have hmem : a ^ (t + 1) ∈ m := hpow_mem (Ideal.pow_mem_pow ha _)
      exact hm_max.isPrime.mem_of_pow_mem _ hmem
    have hmp : m = pointIdeal x := (hp_max.eq_of_le hm_max.ne_top hp_le).symm
    have hbm : b ∈ m := hle (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton b)))
    rw [hmp] at hbm
    exact hb hbm
  have h1 : (1 : Poly n) ∈ K ⊔ Ideal.span {b} := by
    rw [hJ]
    exact Submodule.mem_top
  obtain ⟨k, hkK, y, hy, hky⟩ := Submodule.mem_sup.mp h1
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hy
  have hunit : Ideal.Quotient.mk K b * Ideal.Quotient.mk K r = 1 := by
    have h1eq : k + y = 1 := hky
    have hmk : Ideal.Quotient.mk K (k + y) = Ideal.Quotient.mk K 1 := by
      rw [h1eq]
    rw [map_add] at hmk
    have hkz : Ideal.Quotient.mk K k = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hkK
    rw [hkz, zero_add] at hmk
    rw [← hr] at hmk
    rw [map_mul] at hmk
    rw [mul_comm] at hmk
    simpa using hmk
  exact isUnit_iff_exists.mpr ⟨Ideal.Quotient.mk K r, hunit, by
    rw [mul_comm]; exact hunit⟩

theorem locQuotient_finrank_le (V : AffineVariety n) (x : Point n)
    (hle : V.ideal ≤ pointIdeal x) (t : ℕ) :
    Module.finrank ℂ (PointLocalRing x ⧸ localizedIdeal
      (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) ≤
      Module.finrank ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) := by
  classical
  let p : Ideal (Poly n) := pointIdeal x
  let K : Ideal (Poly n) := V.ideal ⊔ p ^ (t + 1)
  have hKsup : p ^ (t + 1) ≤ K := le_sup_right
  have hKle : K ≤ p := sup_le hle (Ideal.pow_le_self (by omega : t + 1 ≠ 0))
  let φ : Poly n →ₐ[ℂ] PointLocalRing x :=
    IsScalarTower.toAlgHom ℂ (Poly n) (PointLocalRing x)
  have hφK : ∀ a : Poly n, a ∈ K →
      (Ideal.Quotient.mkₐ ℂ (localizedIdeal K x)) (φ a) = 0 := by
    intro a ha
    show Ideal.Quotient.mk (localizedIdeal K x) (φ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let g : Poly n →ₐ[ℂ] (PointLocalRing x ⧸ localizedIdeal K x) :=
    (Ideal.Quotient.mkₐ ℂ (localizedIdeal K x)).comp φ
  let F : (Poly n ⧸ K) →ₐ[ℂ] (PointLocalRing x ⧸ localizedIdeal K x) :=
    Ideal.Quotient.liftₐ K g hφK
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (M := p.primeCompl)
      (S := PointLocalRing x) s
    have hb_notmem : (b : Poly n) ∉ p := b.property
    have hunit : IsUnit (Ideal.Quotient.mk K (b : Poly n)) :=
      isUnit_quotient_of_not_mem_pointIdeal x K t hKsup _ hb_notmem
    obtain ⟨u, hu⟩ := isUnit_iff_exists.mp hunit
    refine ⟨Ideal.Quotient.mk K a * u, ?_⟩
    have hFb : F (Ideal.Quotient.mk K (b : Poly n)) = g (b : Poly n) := rfl
    have hFa : F (Ideal.Quotient.mk K a) = g a := rfl
    have hsu : Ideal.Quotient.mk (localizedIdeal K x) s *
        Ideal.Quotient.mk (localizedIdeal K x) (φ (b : Poly n)) =
        Ideal.Quotient.mk (localizedIdeal K x) (φ a) := by
      have hhab : s * φ (b : Poly n) = φ a := hab
      have := congrArg (Ideal.Quotient.mk (localizedIdeal K x)) hhab
      rwa [map_mul] at this
    have hFu : g (b : Poly n) * F u = 1 := by
      have h1 : F (Ideal.Quotient.mk K (b : Poly n) * u) = 1 := by
        rw [hu.1]; simp
      rw [map_mul, hFb] at h1
      exact h1
    calc F (Ideal.Quotient.mk K a * u)
        = F (Ideal.Quotient.mk K a) * F u := map_mul _ _ _
      _ = g a * F u := by rw [hFa]
      _ = (Ideal.Quotient.mk _ s * g (b : Poly n)) * F u := by
            have : g a = Ideal.Quotient.mk _ s * g (b : Poly n) := by
              have h2 : g a = Ideal.Quotient.mk (localizedIdeal K x) (φ a) := rfl
              have h3 : g (b : Poly n) =
                  Ideal.Quotient.mk (localizedIdeal K x) (φ (b : Poly n)) := rfl
              rw [h2, h3, ← hsu]
            rw [this]
      _ = Ideal.Quotient.mk _ s * (g (b : Poly n) * F u) := by ring
      _ = Ideal.Quotient.mk _ s := by
            rw [hFu, mul_one]
  haveI hTSfin : Module.Finite ℂ
      ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t) :=
    OAI.QuarticPowerFree.totalSpace_finite t
  have hfin : Module.Finite ℂ (Poly n ⧸ K) := by
    have hsurj : Function.Surjective
        ((Ideal.Quotient.mkₐ ℂ K).toLinearMap.domRestrict
          (OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t)) := by
      intro y
      obtain ⟨gg, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨low, high, hgh, hlow_deg, hhigh_mem⟩ := transDecomp x t gg
      have hlow_mem : low ∈ OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t := by
        rwa [OAI.QuarticPowerFree.mem_totalSpace]
      have hsub : gg - low ∈ K := by
        have h_eq : gg - low = high := by linear_combination hgh
        rw [h_eq]
        exact hKsup hhigh_mem
      refine ⟨⟨low, hlow_mem⟩, ?_⟩
      show (Ideal.Quotient.mkₐ ℂ K) low = Ideal.Quotient.mk K gg
      have : Ideal.Quotient.mk K low = Ideal.Quotient.mk K gg := by
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
        have h_neg : low - gg = -(gg - low) := by abel
        rw [h_neg]
        exact neg_mem hsub
      simpa using this
    exact Module.Finite.of_surjective _ hsurj
  exact LinearMap.finrank_le_finrank_of_surjective (f := F.toLinearMap)
    (by simpa using hFsurj)

theorem length_le_finrank_of_finite {A : Type*} [CommRing A] [Algebra ℂ A]
    [IsNoetherianRing A] [IsArtinianRing A] [Module.Finite ℂ A] :
    Module.length A A ≤ (Module.finrank ℂ A : ℕ∞) := by
  classical
  have hFL : IsFiniteLength A A :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp hFL
  let cf : Submodule A A → Submodule ℂ A := fun p =>
    { carrier := p.carrier
      add_mem' := fun {a b} ha hb => p.add_mem ha hb
      zero_mem' := p.zero_mem
      smul_mem' := by
        intro c x hx
        rw [Algebra.smul_def]
        exact p.smul_mem _ hx }
  have hcf_rel : ∀ a b : Submodule A A, a ≤ b ↔ cf a ≤ cf b := by
    intro a b
    constructor
    · intro h x hx
      exact h hx
    · intro h x hx
      exact h hx
  suffices key : ∀ k, Module.length A ↥(s k) ≤ (Module.finrank ℂ ↥(cf (s k)) : ℕ∞) by
    have hlast : s.last = ⊤ := hs_top
    have htopL : Module.length A A = Module.length A ↥(s.last) := by
      rw [hlast]
      exact (Submodule.topEquiv.length_eq).symm
    have hcf_top : cf ⊤ = ⊤ := by
      apply SetLike.ext
      intro x
      constructor
      · intro _; trivial
      · intro _; trivial
    have htopF : Module.finrank ℂ A = Module.finrank ℂ ↥(cf (s.last)) := by
      rw [hlast, hcf_top]
      exact (Submodule.topEquiv.finrank_eq).symm
    rw [htopL, htopF]
    exact key _
  intro k
  induction k using Fin.induction with
  | zero =>
    have h0 : s.toFun 0 = ⊥ := hs_bot
    have hcf0 : cf ⊥ = ⊥ := by
      apply SetLike.ext
      intro x
      constructor
      · intro hx
        exact hx
      · intro hx
        exact hx
    rw [h0]
    have hcf0' : cf (⊥ : Submodule A A) = ⊥ := hcf0
    rw [hcf0']
    simp
  | succ i hi =>
    have hcov := s.step i
    have hltA : s.toFun i.castSucc < s.toFun i.succ := hcov.lt
    have hltC : cf (s.toFun i.castSucc) < cf (s.toFun i.succ) := by
      obtain ⟨hleA, hngeA⟩ := lt_iff_le_not_ge.mp hltA
      rw [lt_iff_le_not_ge]
      constructor
      · exact (hcf_rel _ _).mp hleA
      · intro hcon
        exact hngeA ((hcf_rel _ _).mpr hcon)
    let f : ↥(s.toFun i.castSucc) →ₗ[A] ↥(s.toFun i.succ) :=
      Submodule.inclusion hcov.le
    have key : IsSimpleModule A (↥(s.toFun i.succ) ⧸ LinearMap.range f) := by
      rwa [Submodule.range_inclusion, ← covBy_iff_quot_is_simple hcov.le]
    haveI := key
    let g : ↥(s.toFun i.succ) →ₗ[A] (↥(s.toFun i.succ) ⧸ LinearMap.range f) :=
      f.range.mkQ
    have hf_inj : Function.Injective f := Submodule.inclusion_injective _
    have hg_surj : Function.Surjective g := Submodule.mkQ_surjective _
    have hexact : Function.Exact (⇑f) (⇑g) := LinearMap.exact_map_mkQ_range f
    have hlen : Module.length A ↥(s.toFun i.succ) =
        Module.length A ↥(s.toFun i.castSucc) + 1 := by
      have h := Module.length_eq_add_of_exact f g hf_inj hg_surj hexact
      have h1 : Module.length A (↥(s.toFun i.succ) ⧸ LinearMap.range f) = 1 :=
        Module.length_eq_one A _
      rwa [h1] at h
    have hfrank_lt : Module.finrank ℂ ↥(cf (s.toFun i.castSucc)) <
        Module.finrank ℂ ↥(cf (s.toFun i.succ)) :=
      Submodule.finrank_lt_finrank_of_lt hltC
    have hi' := hi
    have hle2 : (Module.finrank ℂ ↥(cf (s.toFun i.castSucc)) : ℕ∞) + 1 ≤
        (Module.finrank ℂ ↥(cf (s.toFun i.succ)) : ℕ∞) := by
      have hnat : Module.finrank ℂ ↥(cf (s.toFun i.castSucc)) + 1 ≤
          Module.finrank ℂ ↥(cf (s.toFun i.succ)) :=
        Nat.succ_le_of_lt hfrank_lt
      have hcast : ((Module.finrank ℂ ↥(cf (s.toFun i.castSucc)) + 1 : ℕ) : ℕ∞) =
          (Module.finrank ℂ ↥(cf (s.toFun i.castSucc)) : ℕ∞) + 1 := by
        push_cast
        ring
      rw [← hcast]
      exact Nat.cast_le.mpr hnat
    rw [hlen]
    calc Module.length A ↥(s.toFun i.castSucc) + 1
        ≤ (Module.finrank ℂ ↥(cf (s.toFun i.castSucc)) : ℕ∞) + 1 := by
          gcongr
      _ ≤ (Module.finrank ℂ ↥(cf (s.toFun i.succ)) : ℕ∞) := hle2

theorem localHilbert_le_hilbert (V : AffineVariety n) (x : Point n) (hx : x ∈ V)
    (t : ℕ) :
    V.localHilbert x t ≤ ((V.hilbert t : ℕ) : ℕ∞) := by
  classical
  have hle : V.ideal ≤ pointIdeal x := ideal_le_pointIdeal_of_mem hx
  have hKsup : pointIdeal x ^ (t + 1) ≤ V.ideal ⊔ pointIdeal x ^ (t + 1) :=
    le_sup_right
  haveI hTSfin : Module.Finite ℂ
      ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t) :=
    OAI.QuarticPowerFree.totalSpace_finite t
  have hfinR : Module.Finite ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) := by
    have hsurj : Function.Surjective
        ((Ideal.Quotient.mkₐ ℂ (V.ideal ⊔ pointIdeal x ^ (t + 1))).toLinearMap.domRestrict
          (OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t)) := by
      intro y
      obtain ⟨gg, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨low, high, hgh, hlow_deg, hhigh_mem⟩ := transDecomp x t gg
      have hlow_mem : low ∈ OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t := by
        rwa [OAI.QuarticPowerFree.mem_totalSpace]
      have hsub : gg - low ∈ V.ideal ⊔ pointIdeal x ^ (t + 1) := by
        have h_eq : gg - low = high := by linear_combination hgh
        rw [h_eq]
        exact hKsup hhigh_mem
      refine ⟨⟨low, hlow_mem⟩, ?_⟩
      show (Ideal.Quotient.mkₐ ℂ (V.ideal ⊔ pointIdeal x ^ (t + 1))) low =
        Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) gg
      have : Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) low =
          Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) gg := by
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
        have h_neg : low - gg = -(gg - low) := by abel
        rw [h_neg]
        exact neg_mem hsub
      simpa using this
    exact Module.Finite.of_surjective _ hsurj
  let φ : Poly n →ₐ[ℂ] PointLocalRing x :=
    IsScalarTower.toAlgHom ℂ (Poly n) (PointLocalRing x)
  have hφK : ∀ a : Poly n, a ∈ V.ideal ⊔ pointIdeal x ^ (t + 1) →
      (Ideal.Quotient.mkₐ ℂ
        (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)) (φ a) = 0 := by
    intro a ha
    show Ideal.Quotient.mk (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
      (φ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let g : Poly n →ₐ[ℂ]
      (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    (Ideal.Quotient.mkₐ ℂ
      (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)).comp φ
  let F : (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) →ₐ[ℂ]
      (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    Ideal.Quotient.liftₐ (V.ideal ⊔ pointIdeal x ^ (t + 1)) g hφK
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (M := (pointIdeal x).primeCompl)
      (S := PointLocalRing x) s
    have hb_notmem : (b : Poly n) ∉ pointIdeal x := b.property
    have hunit : IsUnit
        (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) (b : Poly n)) :=
      isUnit_quotient_of_not_mem_pointIdeal x
        (V.ideal ⊔ pointIdeal x ^ (t + 1)) t hKsup _ hb_notmem
    obtain ⟨u, hu⟩ := isUnit_iff_exists.mp hunit
    refine ⟨Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) a * u, ?_⟩
    have hFb : F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) (b : Poly n)) =
        g (b : Poly n) := rfl
    have hFa : F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) a) = g a :=
      rfl
    have hsu : Ideal.Quotient.mk
          (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) s *
        Ideal.Quotient.mk
          (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) (φ (b : Poly n)) =
        Ideal.Quotient.mk
          (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) (φ a) := by
      have hhab : s * φ (b : Poly n) = φ a := hab
      have := congrArg
        (Ideal.Quotient.mk
          (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)) hhab
      rwa [map_mul] at this
    have hFu : g (b : Poly n) * F u = 1 := by
      have h1 : F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1))
          (b : Poly n) * u) = 1 := by
        rw [hu.1]; simp
      rw [map_mul, hFb] at h1
      exact h1
    calc F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) a * u)
        = F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) a) * F u :=
          map_mul _ _ _
      _ = g a * F u := by rw [hFa]
      _ = (Ideal.Quotient.mk _ s * g (b : Poly n)) * F u := by
            have : g a = Ideal.Quotient.mk _ s * g (b : Poly n) := by
              have h2 : g a = Ideal.Quotient.mk
                  (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) (φ a) :=
                rfl
              have h3 : g (b : Poly n) =
                  Ideal.Quotient.mk
                    (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
                    (φ (b : Poly n)) := rfl
              rw [h2, h3, ← hsu]
            rw [this]
      _ = Ideal.Quotient.mk _ s * (g (b : Poly n) * F u) := by ring
      _ = Ideal.Quotient.mk _ s := by
            rw [hFu, mul_one]
  haveI := hfinR
  have hfinS : Module.Finite ℂ
      (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    Module.Finite.of_surjective F.toLinearMap hFsurj
  haveI := hfinS
  have h_unfold : V.localHilbert x t =
      Module.length (PointLocalRing x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    rfl
  have h_alg_surj : Function.Surjective
      (algebraMap (PointLocalRing x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)) := by
    simpa only [Ideal.Quotient.algebraMap_eq] using
      (Ideal.Quotient.mk_surjective
        (I := localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x))
  have h_len_eq : Module.length (PointLocalRing x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) =
      Module.length
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    Module.length_eq_of_surjective h_alg_surj
  have h_le : Module.length
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) ≤
      Module.length ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) := by
    have h0 := Submodule.length_le_length_restrictScalars (ℂ)
      (⊤ : Submodule
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x))
    rwa [Module.length_top, Submodule.restrictScalars_top, Module.length_top] at h0
  have h_fin_eq : Module.length ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) =
      ((Module.finrank ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :
        ℕ) : ℕ∞) :=
    Module.length_eq_finrank ℂ _
  have h_loc_le_fin : V.localHilbert x t ≤
      ((Module.finrank ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :
        ℕ) : ℕ∞) := by
    calc V.localHilbert x t
        = Module.length (PointLocalRing x)
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
            h_unfold
      _ = Module.length
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
            h_len_eq
      _ ≤ Module.length ℂ
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
            h_le
      _ = ((Module.finrank ℂ
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :
          ℕ) : ℕ∞) := h_fin_eq
  have h_fin_le : Module.finrank ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) ≤
      Module.finrank ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) :=
    locQuotient_finrank_le V x hle t
  have h_glob : Module.finrank ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) ≤
      V.hilbert t :=
    finrank_quotient_le_hilbert V x t
  calc V.localHilbert x t
      ≤ ((Module.finrank ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :
        ℕ) : ℕ∞) := h_loc_le_fin
    _ ≤ ((Module.finrank ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) : ℕ) :
        ℕ∞) := by exact_mod_cast h_fin_le
    _ ≤ ((V.hilbert t : ℕ) : ℕ∞) := by exact_mod_cast h_glob

theorem localDimension_le_dimension (V : AffineVariety n) (x : Point n) (hx : x ∈ V) :
    V.localDimension x ≤ V.dimension := by
  classical
  obtain ⟨_, N1, hP⟩ := (V.localHilbert_eventually_polynomial x).choose_spec
  have hQev : ∀ᶠ D : ℕ in Filter.atTop,
      ((V.hilbert D : ℕ) : ℚ) = V.hilbertPolynomial.eval (D : ℚ) :=
    V.hilbert_eventually
  have hPnonneg : ∀ᶠ T : ℕ in Filter.atTop,
      0 ≤ (V.localHilbertPolynomial x).eval (T : ℚ) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N1, fun t ht => hP t ht⟩] with t ht
    obtain ⟨a, _, heval⟩ := ht
    have heval' : (V.localHilbertPolynomial x).eval (t : ℚ) = (a : ℚ) := heval
    rw [heval']
    positivity
  have hPle : ∀ᶠ T : ℕ in Filter.atTop,
      (V.localHilbertPolynomial x).eval (T : ℚ) ≤
        V.hilbertPolynomial.eval (T : ℚ) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N1, fun t ht => hP t ht⟩, hQev]
      with t ht hQt
    obtain ⟨a, ha, heval⟩ := ht
    have heval' : (V.localHilbertPolynomial x).eval (t : ℚ) = (a : ℚ) := heval
    have h_per : V.localHilbert x t ≤ ((V.hilbert t : ℕ) : ℕ∞) :=
      localHilbert_le_hilbert V x hx t
    rw [ha] at h_per
    have h_aH : a ≤ V.hilbert t := by exact_mod_cast h_per
    have h_aH_Q : (a : ℚ) ≤ ((V.hilbert t : ℕ) : ℚ) := by exact_mod_cast h_aH
    rw [heval', ← hQt]
    exact h_aH_Q
  have h_deg : (V.localHilbertPolynomial x).natDegree ≤
      V.hilbertPolynomial.natDegree :=
    OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _ hPnonneg hPle
  exact h_deg

/-- Maximal ideal of the point localization is the extended point ideal. -/
theorem maxIdeal_eq_localized_pointIdeal (x : Point n) :
    IsLocalRing.maximalIdeal (PointLocalRing x) =
      localizedIdeal (pointIdeal x) x := by
  have h := Localization.AtPrime.map_eq_maximalIdeal (R := Poly n)
    (I := pointIdeal x)
  exact h.symm

/-- Localized sup splits as sup of localizations (for the Hilbert bridge). -/
theorem localized_sup_pow_eq (V : AffineVariety n) (x : Point n) (t : ℕ) :
    localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t+1)) x =
      localizedIdeal V.ideal x ⊔
        (IsLocalRing.maximalIdeal (PointLocalRing x)) ^ (t+1) := by
  classical
  rw [maxIdeal_eq_localized_pointIdeal]
  rw [localizedIdeal, localizedIdeal, localizedIdeal]
  rw [Ideal.map_sup]
  congr 1
  rw [Ideal.map_pow]

/-- The quotient by the variety ideal is nontrivial at a point of the variety. -/
theorem quot_nontrivial_of_mem (V : AffineVariety n) (x : Point n) (hx : x ∈ V) :
    Nontrivial (PointLocalRing x ⧸ localizedIdeal V.ideal x) := by
  classical
  have hle : V.ideal ≤ pointIdeal x := ideal_le_pointIdeal_of_mem hx
  have hmax : ((pointIdeal x).map (algebraMap (Poly n) (PointLocalRing x))).IsMaximal := by
    infer_instance
  have hJle : localizedIdeal V.ideal x ≤
      (pointIdeal x).map (algebraMap (Poly n) (PointLocalRing x)) :=
    Ideal.map_mono hle
  have hJne : localizedIdeal V.ideal x ≠ ⊤ := by
    intro htop
    have htop' : (pointIdeal x).map (algebraMap (Poly n) (PointLocalRing x)) = ⊤ := by
      apply top_unique
      simpa [htop] using hJle
    exact hmax.ne_top htop'
  exact Ideal.Quotient.nontrivial_iff.mpr hJne

/-- The local ring of the variety at a point is local. -/
theorem quot_isLocalRing_of_mem (V : AffineVariety n) (x : Point n) (hx : x ∈ V) :
    IsLocalRing (PointLocalRing x ⧸ localizedIdeal V.ideal x) := by
  classical
  haveI := quot_nontrivial_of_mem V x hx
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- Local Hilbert length equals the quotient length by the imaged maximal power. -/
theorem localHilbert_eq_quotient_length (V : AffineVariety n) (x : Point n)
    (hx : x ∈ V) (t : ℕ) :
    V.localHilbert x t =
      Module.length (PointLocalRing x ⧸ localizedIdeal V.ideal x)
        ((PointLocalRing x ⧸ localizedIdeal V.ideal x) ⧸
          (Ideal.map (Ideal.Quotient.mk (localizedIdeal V.ideal x))
            (IsLocalRing.maximalIdeal (PointLocalRing x))) ^ (t+1)) := by
  classical
  unfold AffineVariety.localHilbert localLengthAt
  rw [localized_sup_pow_eq V x t]
  rw [OAI.Lech.FrobeniusGrowth.quotient_power_length]
  rw [sup_comm]

/-- Local Hilbert length equals Lech colength as an extended natural. -/
theorem localHilbert_eq_colength (V : AffineVariety n) (x : Point n)
    (hx : x ∈ V) (t : ℕ)
    [IsLocalRing (PointLocalRing x ⧸ localizedIdeal V.ideal x)] :
    V.localHilbert x t =
      ((OAI.Lech.colength (PointLocalRing x ⧸ localizedIdeal V.ideal x) (t+1) : ℕ) : ℕ∞) := by
  classical
  have hmax_eq : IsLocalRing.maximalIdeal
      (PointLocalRing x ⧸ localizedIdeal V.ideal x) =
      Ideal.map (Ideal.Quotient.mk (localizedIdeal V.ideal x))
        (IsLocalRing.maximalIdeal (PointLocalRing x)) := by
    have hle : V.ideal ≤ pointIdeal x := ideal_le_pointIdeal_of_mem hx
    have hmax_eq2 : IsLocalRing.maximalIdeal (PointLocalRing x) =
        localizedIdeal (pointIdeal x) x :=
      maxIdeal_eq_localized_pointIdeal x
    have hJle : localizedIdeal V.ideal x ≤ IsLocalRing.maximalIdeal (PointLocalRing x) := by
      rw [hmax_eq2]
      exact Ideal.map_mono hle
    have hmax_img : (Ideal.map (Ideal.Quotient.mk (localizedIdeal V.ideal x))
        (IsLocalRing.maximalIdeal (PointLocalRing x))).IsMaximal := by
      apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      rw [Ideal.mk_ker]
      exact hJle
    exact (IsLocalRing.eq_maximalIdeal hmax_img).symm
  rw [localHilbert_eq_quotient_length V x hx t]
  rw [OAI.Lech.colength_cast]
  rw [hmax_eq]

/-- Eventually, Lech colength (shifted by one) equals the local Hilbert polynomial. -/
theorem eventual_colength_eq_poly (V : AffineVariety n) (x : Point n)
    (hx : x ∈ V)
    [IsLocalRing (PointLocalRing x ⧸ localizedIdeal V.ideal x)] :
    ∀ᶠ t : ℕ in Filter.atTop,
      ((OAI.Lech.colength (PointLocalRing x ⧸ localizedIdeal V.ideal x) (t+1) : ℕ) : ℚ) =
        (V.localHilbertPolynomial x).eval (t : ℚ) := by
  classical
  obtain ⟨_, N, hN⟩ := (V.localHilbert_eventually_polynomial x).choose_spec
  filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun t ht => hN t ht⟩] with t ht
  obtain ⟨a, ha_len, ha_eval⟩ := ht
  have hcol : V.localHilbert x t =
      ((OAI.Lech.colength (PointLocalRing x ⧸ localizedIdeal V.ideal x) (t+1) : ℕ) : ℕ∞) :=
    localHilbert_eq_colength V x hx t
  rw [ha_len] at hcol
  have haC : a = OAI.Lech.colength (PointLocalRing x ⧸ localizedIdeal V.ideal x) (t+1) := by
    exact_mod_cast hcol
  have ha_eval' : (V.localHilbertPolynomial x).eval (t : ℚ) = (a : ℚ) := ha_eval
  rw [← haC]
  exact ha_eval'.symm

/-- Global transcendence basis size equals the affine dimension. -/
theorem global_independent_card_eq_dimension (V : AffineVariety n) (x : Point n) (hx : x ∈ V) :
    ∃ P : Polynomial ℚ, ∃ j : Fin P.natDegree → Fin n,
      Function.Injective j ∧
      AlgebraicIndependent ℂ
        (fun a => Ideal.Quotient.mk V.ideal (MvPolynomial.X (j a))) ∧
      P.natDegree = V.dimension ∧
      ∃ T₀ : ℕ, ∀ T ≥ T₀,
        (Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace T).map
          (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap) : ℚ) = P.eval (T : ℚ) := by
  classical
  have hne : V.ideal ≠ ⊤ := by
    intro htop
    have hxmem : x ∈ MvPolynomial.zeroLocus ℂ V.ideal := hx
    rw [htop] at hxmem
    have h1 : MvPolynomial.aeval x (1 : Poly n) = 0 := hxmem 1 (by simp)
    simpa using h1
  obtain ⟨P, j, hj_inj, hj_ind, _, T₀, hT⟩ :=
    OAI.QuarticPowerFree.coordinate_hilbert_degree_independent V.ideal hne
  have hPeq : P = V.hilbertPolynomial := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [Filter.eventually_atTop.mpr ⟨T₀, fun T hT' => hT T hT'⟩,
      OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal] with T h1 h2
    exact h1.symm.trans h2
  have hdim : P.natDegree = V.dimension := by
    rw [hPeq]
    rfl
  exact ⟨P, j, hj_inj, hj_ind, hdim, T₀, hT⟩

/-- Translated variables remain algebraically independent in the coordinate ring. -/
theorem translated_independent_in_quotient (V : AffineVariety n) (x : Point n)
    {k : ℕ} (j : Fin k → Fin n)
    (hj : AlgebraicIndependent ℂ
      (fun a => Ideal.Quotient.mk V.ideal (MvPolynomial.X (j a)))) :
    AlgebraicIndependent ℂ (fun a =>
      Ideal.Quotient.mk V.ideal
        (MvPolynomial.X (j a) - MvPolynomial.C (x (j a)))) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval] at hj ⊢
  have htau_inv :
      (MvPolynomial.aeval (fun a => MvPolynomial.X a + MvPolynomial.C (x (j a))) :
        MvPolynomial (Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin k) ℂ).comp
        (MvPolynomial.aeval (fun a => MvPolynomial.X a - MvPolynomial.C (x (j a)))) =
      AlgHom.id ℂ (MvPolynomial (Fin k) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      map_sub, map_add, MvPolynomial.algebraMap_eq, AlgHom.id_apply]
    abel
  have htau_inj : Function.Injective
      (MvPolynomial.aeval (fun a => MvPolynomial.X a - MvPolynomial.C (x (j a))) :
        MvPolynomial (Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin k) ℂ) := by
    have hcomp_inj : Function.Injective ⇑(
        (MvPolynomial.aeval (fun a => MvPolynomial.X a + MvPolynomial.C (x (j a))) :
          MvPolynomial (Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin k) ℂ).comp
        (MvPolynomial.aeval (fun a => MvPolynomial.X a - MvPolynomial.C (x (j a))))) := by
      rw [htau_inv]
      exact Function.injective_id
    have hcoe : ⇑(
        (MvPolynomial.aeval (fun a => MvPolynomial.X a + MvPolynomial.C (x (j a))) :
          MvPolynomial (Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin k) ℂ).comp
        (MvPolynomial.aeval (fun a => MvPolynomial.X a - MvPolynomial.C (x (j a))))) =
        (MvPolynomial.aeval (fun a => MvPolynomial.X a + MvPolynomial.C (x (j a))) :
          MvPolynomial (Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin k) ℂ) ∘
        (MvPolynomial.aeval (fun a => MvPolynomial.X a - MvPolynomial.C (x (j a)))) :=
      rfl
    rw [hcoe] at hcomp_inj
    exact Function.Injective.of_comp hcomp_inj
  have h_comp : MvPolynomial.aeval (fun a => Ideal.Quotient.mk V.ideal
      (MvPolynomial.X (j a) - MvPolynomial.C (x (j a)))) =
      (MvPolynomial.aeval (fun a => Ideal.Quotient.mk V.ideal
        (MvPolynomial.X (j a)))).comp
        (MvPolynomial.aeval (fun a => MvPolynomial.X a - MvPolynomial.C (x (j a)))) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_sub, MvPolynomial.aeval_C]
    congr 1
  have h_base_inj : Function.Injective
      (MvPolynomial.aeval (fun a => Ideal.Quotient.mk V.ideal
        (MvPolynomial.X (j a)))) := hj
  intro p q hpq
  rw [h_comp] at hpq
  have htau_eq := h_base_inj hpq
  exact htau_inj htau_eq

theorem localDimension_eq_dimension (V : AffineVariety n) (x : Point n)
    (hV : V.IsIrreducible) (hx : x ∈ V) : V.localDimension x = V.dimension := by
  classical
  haveI : V.ideal.IsPrime := hV
  haveI := quot_nontrivial_of_mem V x hx
  haveI := quot_isLocalRing_of_mem V x hx
  -- Carrier local ring and its Hilbert polynomial
  set A : Type := PointLocalRing x ⧸ localizedIdeal V.ideal x with hA
  set P : Polynomial ℚ := V.localHilbertPolynomial x with hP
  have hloc_dim : V.localDimension x = P.natDegree := rfl
  -- Unshifted eventual colength polynomial P' = P.comp (X − C 1)
  have hev_shift := eventual_colength_eq_poly V x hx
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev_shift
  set P' : Polynomial ℚ := P.comp (Polynomial.X - Polynomial.C (1 : ℚ)) with hP'
  have hP'_deg : P'.natDegree = P.natDegree := by
    rw [hP', Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
  have hA_event : ∀ᶠ N in Filter.atTop,
      ((OAI.Lech.colength A N : ℕ) : ℚ) = P'.eval (N : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨max (N₀ + 1) 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_trans (Nat.le_max_right _ _) hN
    have hN0k : N - 1 ≥ N₀ := by omega
    have hNk : N ≥ 1 := hN1
    have hev := hN₀ (N - 1) hN0k
    have hshift : (P.comp (Polynomial.X - Polynomial.C (1 : ℚ))).eval
        (N : ℚ) = P.eval (((N - 1 : ℕ) : ℚ)) := by
      rw [Polynomial.eval_comp]
      have hqeval : (Polynomial.X - Polynomial.C (1 : ℚ)).eval (N : ℚ) =
          (((N - 1 : ℕ) : ℚ)) := by
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        have hcast : (((N - 1 : ℕ) : ℚ)) = (N : ℚ) - (1 : ℚ) := by
          simpa using Nat.cast_sub hN1
        rw [hcast]
      rw [hqeval]
    have hcol : OAI.Lech.colength A N =
        OAI.Lech.colength A ((N - 1) + 1) := by
      have hN_eq : (N - 1) + 1 = N := Nat.sub_add_cancel hN1
      rw [hN_eq]
    rw [hcol, hP']
    have hev' : (((OAI.Lech.colength A ((N - 1) + 1) : ℕ) : ℚ)) =
        P.eval (((N - 1 : ℕ) : ℚ)) := by
      have hev2 := hev
      -- hev : ((colength ((N-1)+1) : ℕ):ℚ) = P.eval ((N-1 : ℕ):ℚ)? Actually
      -- eventual_colength_eq_poly gives colength (t+1) vs P.eval t with t = N-1.
      -- Here t+1 = (N-1)+1, t = N-1. Good, defeq.
      exact hev2
    calc ((OAI.Lech.colength A ((N - 1) + 1) : ℕ) : ℚ)
        = P.eval (((N - 1 : ℕ) : ℚ)) := hev'
      _ = (P.comp (Polynomial.X - Polynomial.C (1 : ℚ))).eval (N : ℚ) :=
          hshift.symm
  have hdim_le : OAI.Lech.dimension A ≤ P'.natDegree :=
    dimension_le_natDegree_of_eventual A P' hA_event
  -- V.dimension = Lech.dimension A via Krull bridges
  have hVdim_eq : V.dimension = OAI.Lech.dimension A := by
    have h1 := dimension_cast_eq_krullDim V
    have hle : V.ideal ≤ pointIdeal x := ideal_le_pointIdeal_of_mem hx
    have h2 := krullDim_local_eq_global V x hle
    have h3 := OAI.Lech.dimension_cast A
    have hcast_eq : ((V.dimension : ℕ) : WithBot ℕ∞) =
        ((OAI.Lech.dimension A : ℕ) : WithBot ℕ∞) := by
      rw [h1, ← h2, ← h3]
    exact_mod_cast hcast_eq
  have hlower : V.dimension ≤ V.localDimension x := by
    rw [hloc_dim, ← hP'_deg, hVdim_eq]
    exact hdim_le
  exact le_antisymm (localDimension_le_dimension V x hx) hlower

end AffineVariety

theorem ProjectiveVariety.multiplicity_chart {n : ℕ} (V : ProjectiveVariety (n+1))
    (p : ProjectivePoint (n+1)) (i : Fin (n+1)) (hi : p.rep i ≠ 0) :
    V.multiplicity p = (V.affineChart i).multiplicity (chartCoordinates i p) := by
  unfold ProjectiveVariety.multiplicity
  exact TrackA.multiplicity_eq_of_localHilbert_eq
    (V.affineChart (chartIndex p)) (chartCoordinates (chartIndex p) p)
    (V.affineChart i) (chartCoordinates i p)
    (fun t => TrackA.affineChart_localHilbert_eq V (chartIndex p) i p
      (chartIndex_nonzero p) hi t)

end
end DistinctDistances
