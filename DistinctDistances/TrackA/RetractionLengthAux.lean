import DistinctDistances.TrackA.PointPowerLengthSupport
import DistinctDistances.TrackA.Intersections
import DistinctDistances.TrackA.CurveHilbertSupport
import DistinctDistances.TrackA.ProjectionOrderSupport
import DistinctDistances.Bridges.ComplexLineModel
import OAI.NumberTheory.PowerFree.SurfaceCounting

/-! Transport of local Hilbert lengths along a
polynomial retraction pair (used for chart-deletion multiplicities). -/

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
open MvPolynomial

theorem pointIdeal_eq_comap_of_eval {n m : ℕ} (φ : Poly n →ₐ[ℂ] Poly m)
    (a : Point n) (y : Point m) (h : ∀ f, eval y (φ f) = eval a f) :
    pointIdeal a = (pointIdeal y).comap φ.toRingHom := by
  ext f
  change f ∈ vanishingIdeal ℂ ({a} : Set (Point n)) ↔
    φ f ∈ vanishingIdeal ℂ ({y} : Set (Point m))
  rw [mem_vanishingIdeal_singleton_iff, mem_vanishingIdeal_singleton_iff]
  change eval a f = 0 ↔ eval y (φ f) = 0
  rw [h]

/-- The localized carrier-plus-power ideal is carried by a local ring map
induced from a polynomial map preserving the carrier ideals and points. -/
theorem localized_hilbert_ideal_map_le {n m : ℕ} (Z : AffineVariety n) (W : AffineVariety m)
    (φ : Poly n →ₐ[ℂ] Poly m) (a : Point n) (y : Point m)
    (hφa : ∀ f, eval y (φ f) = eval a f) (hφZ : ∀ f ∈ Z.ideal, φ f ∈ W.ideal) (t : ℕ) :
    (localizedIdeal (Z.ideal ⊔ pointIdeal a ^ (t+1)) a).map
        (Localization.localRingHom (pointIdeal a) (pointIdeal y) φ.toRingHom
          (pointIdeal_eq_comap_of_eval φ a y hφa)) ≤
      localizedIdeal (W.ideal ⊔ pointIdeal y ^ (t+1)) y := by
  let Φ := Localization.localRingHom (pointIdeal a) (pointIdeal y) φ.toRingHom
    (pointIdeal_eq_comap_of_eval φ a y hφa)
  have hcomp : Φ.comp (algebraMap (Poly n) (PointLocalRing a)) =
      (algebraMap (Poly m) (PointLocalRing y)).comp φ.toRingHom :=
    RingHom.ext fun f => Localization.localRingHom_to_map (pointIdeal a) (pointIdeal y)
      φ.toRingHom (pointIdeal_eq_comap_of_eval φ a y hφa) f
  unfold localizedIdeal
  rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  apply Ideal.map_mono
  rw [Ideal.map_sup, Ideal.map_pow]
  apply sup_le_sup
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    exact hφZ f hf
  · apply Ideal.pow_right_mono
    rw [Ideal.map_le_iff_le_comap, pointIdeal_eq_comap_of_eval φ a y hφa]

/-- A retraction pair of polynomial maps, compatible with two reduced
carriers and two points, gives equal local Hilbert lengths. -/
theorem localHilbert_eq_of_retraction {n m : ℕ} (Z : AffineVariety n) (W : AffineVariety m)
    (φ : Poly n →ₐ[ℂ] Poly m) (ψ : Poly m →ₐ[ℂ] Poly n) (hφψ : ∀ g, φ (ψ g) = g)
    (a : Point n) (y : Point m)
    (hφa : ∀ f, eval y (φ f) = eval a f) (hψy : ∀ g, eval a (ψ g) = eval y g)
    (hφZ : ∀ f ∈ Z.ideal, φ f ∈ W.ideal) (hψW : ∀ g ∈ W.ideal, ψ g ∈ Z.ideal)
    (hret : ∀ f, ψ (φ f) - f ∈ Z.ideal) (t : ℕ) :
    Z.localHilbert a t = W.localHilbert y t := by
  let Ra := PointLocalRing a
  let Ry := PointLocalRing y
  let Ja := localizedIdeal (Z.ideal ⊔ pointIdeal a ^ (t+1)) a
  let Jy := localizedIdeal (W.ideal ⊔ pointIdeal y ^ (t+1)) y
  let Φ : Ra →+* Ry := Localization.localRingHom (pointIdeal a) (pointIdeal y) φ.toRingHom
    (pointIdeal_eq_comap_of_eval φ a y hφa)
  let Ψ : Ry →+* Ra := Localization.localRingHom (pointIdeal y) (pointIdeal a) ψ.toRingHom
    (pointIdeal_eq_comap_of_eval ψ y a hψy)
  have hΦ (f : Poly n) : Φ (algebraMap (Poly n) Ra f) = algebraMap (Poly m) Ry (φ f) :=
    Localization.localRingHom_to_map _ _ _ _ _
  have hΨ (g : Poly m) : Ψ (algebraMap (Poly m) Ry g) = algebraMap (Poly n) Ra (ψ g) :=
    Localization.localRingHom_to_map _ _ _ _ _
  have hΦJ : Ja ≤ Jy.comap Φ :=
    Ideal.map_le_iff_le_comap.mp (localized_hilbert_ideal_map_le Z W φ a y hφa hφZ t)
  have hΨJ : Jy ≤ Ja.comap Ψ :=
    Ideal.map_le_iff_le_comap.mp (localized_hilbert_ideal_map_le W Z ψ y a hψy hψW t)
  let Φq : Ra ⧸ Ja →+* Ry ⧸ Jy := Ideal.quotientMap Jy Φ hΦJ
  let Ψq : Ry ⧸ Jy →+* Ra ⧸ Ja := Ideal.quotientMap Ja Ψ hΨJ
  have hΦΨ : Φq.comp Ψq = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext (pointIdeal y).primeCompl
    refine RingHom.ext fun g => ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    change Φq (Ψq (Ideal.Quotient.mk Jy (algebraMap (Poly m) Ry g))) =
      Ideal.Quotient.mk Jy (algebraMap (Poly m) Ry g)
    rw [Ideal.quotientMap_mk, hΨ, Ideal.quotientMap_mk, hΦ, hφψ]
  have hΨΦ : Ψq.comp Φq = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext (pointIdeal a).primeCompl
    have hmem (f : Poly n) : algebraMap (Poly n) Ra (ψ (φ f)) - algebraMap (Poly n) Ra f ∈ Ja := by
      rw [← map_sub]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (hret f))
    refine RingHom.ext fun f => ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    change Ψq (Φq (Ideal.Quotient.mk Ja (algebraMap (Poly n) Ra f))) =
      Ideal.Quotient.mk Ja (algebraMap (Poly n) Ra f)
    rw [Ideal.quotientMap_mk, hΦ, Ideal.quotientMap_mk, hΨ]
    exact Ideal.Quotient.eq.mpr (hmem f)
  let e : (Ra ⧸ Ja) ≃+* (Ry ⧸ Jy) := RingEquiv.ofRingHom Φq Ψq hΦΨ hΨΦ
  have hsmul (c : ℂ) (x : Ra ⧸ Ja) : e (c • x) = c • e x := by
    have h1 : c • x = algebraMap ℂ (Ra ⧸ Ja) c * x := Algebra.smul_def c x
    have h2 : c • e x = algebraMap ℂ (Ry ⧸ Jy) c * e x := Algebra.smul_def c (e x)
    rw [h1, h2, map_mul]
    congr 1
    have hc : algebraMap ℂ (Ra ⧸ Ja) c =
        Ideal.Quotient.mk Ja (algebraMap (Poly n) Ra (MvPolynomial.C c)) := by
      rw [IsScalarTower.algebraMap_apply ℂ Ra (Ra ⧸ Ja),
        IsScalarTower.algebraMap_apply ℂ (Poly n) Ra]
      rfl
    have hc' : algebraMap ℂ (Ry ⧸ Jy) c =
        Ideal.Quotient.mk Jy (algebraMap (Poly m) Ry (MvPolynomial.C c)) := by
      rw [IsScalarTower.algebraMap_apply ℂ Ry (Ry ⧸ Jy),
        IsScalarTower.algebraMap_apply ℂ (Poly m) Ry]
      rfl
    rw [hc, hc']
    change Φq (Ideal.Quotient.mk Ja _) = _
    have hcomm := φ.commutes c
    simp only [MvPolynomial.algebraMap_eq] at hcomm
    rw [Ideal.quotientMap_mk, hΦ, hcomm]
  let eℂ : (Ra ⧸ Ja) ≃ₗ[ℂ] (Ry ⧸ Jy) :=
    { e.toAddEquiv with map_smul' := hsmul }
  unfold AffineVariety.localHilbert localLengthAt
  rw [point_local_length_eq_complex_length a, point_local_length_eq_complex_length y]
  exact eℂ.length_eq

/-- The reduced point variety. -/
def singletonPointVariety {n : ℕ} (x : Point n) : AffineVariety n :=
  ⟨pointIdeal x, (pointIdeal_isMaximal x).isPrime.isRadical⟩

theorem singletonPointVariety_injective {n : ℕ} :
    Function.Injective (singletonPointVariety (n := n)) := by
  intro x y h
  have hI : pointIdeal x = pointIdeal y := congrArg AffineVariety.ideal h
  funext i
  have hxi : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal x := by
    change MvPolynomial.X i - MvPolynomial.C (x i) ∈
      MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n))
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  have hyi : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal y := by
    rw [← hI]
    exact hxi
  have heval := (MvPolynomial.mem_vanishingIdeal_singleton_iff y _).mp hyi
  have heval' : y i - x i = 0 := by simpa using heval
  exact (sub_eq_zero.mp heval').symm

theorem singletonPointVariety_irreducible {n : ℕ} (x : Point n) :
    (singletonPointVariety x).IsIrreducible := (pointIdeal_isMaximal x).isPrime

theorem singletonPointVariety_degree {n : ℕ} (x : Point n) :
    (singletonPointVariety x).degree = 1 := by
  change OAI.QuarticPowerFree.affineDegree (pointIdeal x) = 1
  exact affine_point_degree_one x

theorem singletonPointVariety_dimension {n : ℕ} (x : Point n) :
    (singletonPointVariety x).dimension = 0 := by
  let I : Ideal (Poly n) := pointIdeal x
  let ev : Poly n →ₐ[ℂ] ℂ := MvPolynomial.aeval x
  have hI : I = RingHom.ker ev.toRingHom := by
    ext f
    change f ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n)) ↔
      f ∈ RingHom.ker ev.toRingHom
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, RingHom.mem_ker]
    rfl
  have hev : Function.Surjective ev := by
    intro c
    exact ⟨MvPolynomial.C c, by simp [ev]⟩
  let e : (Poly n ⧸ I) ≃ₐ[ℂ] ℂ := by
    rw [hI]
    exact Ideal.quotientKerAlgEquivOfSurjective hev
  have htrdeg : Algebra.trdeg ℂ (Poly n ⧸ I) = 0 := by
    letI : Algebra.IsAlgebraic ℂ (Poly n ⧸ I) := e.symm.isAlgebraic
    exact trdeg_eq_zero_iff.mpr ‹Algebra.IsAlgebraic ℂ (Poly n ⧸ I)›
  have hdim := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg I
    (OAI.QuarticPowerFree.coordinateHilbert I)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually I)
  have hnat : (OAI.QuarticPowerFree.coordinateHilbert I).natDegree = 0 := by
    exact_mod_cast hdim.trans htrdeg
  change OAI.QuarticPowerFree.affineDimension I = 0
  exact hnat

/-- Order-one analogue of `curve_hilbert_double_order_bound`. -/
theorem curve_hilbert_order_one_bound (R : Type*) [CommRing R] (m : Ideal R) (a : R)
    (ha : a ∈ m) (L : ℕ)
    (hlen : Module.length R (R ⧸ Ideal.span {a}) = (L : ℕ∞))
    (P : Polynomial ℚ) (hdeg : P.natDegree ≤ 1) (N : ℕ)
    (hP : ∀ t ≥ N, ∃ v : ℕ,
      Module.length R (R ⧸ m^(t+1)) = (v : ℕ∞) ∧ P.eval (t : ℚ) = (v : ℚ)) :
    P.coeff 1 ≤ (L : ℚ) := by
  have hlength (j : ℕ) : Module.length R (R ⧸ m^j) ≤ (j : ℕ∞)*(L : ℕ∞) := by
    have hpow : a^j ∈ m^j := Ideal.pow_mem_pow ha j
    have hsub : Ideal.span {a^j} ≤ m^j := Ideal.span_le.mpr (by
      intro b hb
      rcases Set.mem_singleton_iff.mp hb with rfl
      exact hpow)
    calc
      Module.length R (R ⧸ m^j) ≤ Module.length R (R ⧸ Ideal.span {a^j}) :=
        Module.length_le_of_surjective (Submodule.factor hsub) (Submodule.factor_surjective hsub)
      _ ≤ (j : ℕ∞) * Module.length R (R ⧸ Ideal.span {a}) :=
        curve_length_span_pow_le R a j
      _ = (j : ℕ∞)*(L : ℕ∞) := by rw [hlen]
  let P₁ : Polynomial ℚ := Polynomial.taylor (-1) P
  let Q : Polynomial ℚ := Polynomial.C (L : ℚ) * Polynomial.X
  have hP₁ : P₁.natDegree ≤ 1 := by simpa [P₁] using hdeg
  have hQ : Q.natDegree ≤ 1 := Polynomial.natDegree_mul_le.trans (by simp)
  have hle : ∀ᶠ j : ℕ in Filter.atTop, P₁.eval (j : ℚ) ≤ Q.eval (j : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N+1, ?_⟩
    intro j hj
    obtain ⟨v, hv, hvP⟩ := hP (j-1) (by omega)
    have hExp : j-1+1 = j := by omega
    rw [hExp] at hv
    have hb := hlength j
    rw [hv] at hb
    have hbQ : (v : ℚ) ≤ (j : ℚ)*(L : ℚ) := by exact_mod_cast hb
    have hcast : ((j-1 : ℕ) : ℚ) = (j : ℚ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ j)]
      push_cast
      rfl
    have heval : P₁.eval (j : ℚ) = P.eval ((j-1 : ℕ) : ℚ) := by
      simp only [P₁, Polynomial.taylor_eval]
      rw [hcast]
      congr 1
      ring
    rw [heval, hvP]
    simpa [Q, Polynomial.eval_mul, mul_comm] using hbQ
  have hc := OAI.QuarticPowerFree.coeff_le_of_eventually_nat_eval_le P₁ Q 1 hP₁ hQ hle
  dsimp [P₁, Q] at hc
  rw [OAI.QuarticPowerFree.coeff_taylor_high P (-1) 1 hdeg] at hc
  simpa using hc

set_option backward.isDefEq.respectTransparency.types false in
/-- A cut through a point of an irreducible curve has local length at least
the multiplicity there. -/
theorem curve_order_one_length {n : ℕ} (C : AffineVariety n)
    (hC : C.IsIrreducible) (hdim : C.dimension = 1) (p : Point n) (hp : p ∈ C.points)
    (f : Poly n) (hf : f ∉ C.ideal) (hfp : MvPolynomial.eval p f = 0) :
    ∃ length : ℕ, localLengthAt (C.ideal ⊔ Ideal.span {f}) p = (length : ℕ∞) ∧
      C.multiplicity p ≤ (length : ℚ) := by
  letI : CommRing (CarrierLocalRing C p) :=
    { __ := (inferInstance : Ring (CarrierLocalRing C p))
      mul_comm := fun a b => mul_comm a b }
  obtain ⟨length, hlength, _⟩ := fa_bezout_curve_length C hC hdim f hf p hp
  have hlen : Module.length (CarrierLocalRing C p)
      (CarrierLocalRing C p ⧸ Ideal.span {localClass C p f}) = (length : ℕ∞) := by
    rwa [curve_cut_length_carrier] at hlength
  have hfpoint : f ∈ pointIdeal p := by
    change f ∈ MvPolynomial.vanishingIdeal ℂ ({p} : Set (Point n))
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hfp
  have horder : localClass C p f ∈ carrierMaximalIdeal C p :=
    Ideal.mem_map_of_mem _ hfpoint
  have hdim' : C.localDimension p = 1 :=
    (C.localDimension_eq_dimension p hC hp).trans hdim
  have hdeg : (C.localHilbertPolynomial p).natDegree ≤ 1 := by
    simpa only [AffineVariety.localDimension] using hdim'.le
  obtain ⟨N, hN⟩ := (C.localHilbert_eventually_polynomial p).choose_spec.2
  have hvalues : ∀ t ≥ N, ∃ v : ℕ,
      Module.length (CarrierLocalRing C p)
        (CarrierLocalRing C p ⧸ carrierMaximalIdeal C p ^ (t+1)) = (v : ℕ∞) ∧
      (C.localHilbertPolynomial p).eval (t : ℚ) = (v : ℚ) := by
    intro t ht
    obtain ⟨v, hv, hPv⟩ := hN t ht
    exact ⟨v, (curve_localHilbert_carrier C p t).symm.trans hv, hPv⟩
  have hbound : (C.localHilbertPolynomial p).coeff 1 ≤ (length : ℚ) :=
    curve_hilbert_order_one_bound (CarrierLocalRing C p)
    (carrierMaximalIdeal C p) (localClass C p f) horder length hlen
    (C.localHilbertPolynomial p) hdeg N hvalues
  refine ⟨length, hlength, ?_⟩
  simpa [AffineVariety.multiplicity, hdim'] using hbound

/-- A point of a curve on a proper cut is a minimal prime of the cut. -/
theorem curve_cut_point_minimal {n : ℕ} (Y : AffineVariety n) (hY : Y.IsIrreducible)
    (hdim : Y.dimension = 1) (f : Poly n) (hf : f ∉ Y.ideal)
    (p : Point n) (hp : p ∈ Y.points) (hfp : MvPolynomial.eval p f = 0) :
    pointIdeal p ∈ (Y.ideal ⊔ Ideal.span {f}).minimalPrimes := by
  have hfpoint : f ∈ pointIdeal p := by
    change f ∈ MvPolynomial.vanishingIdeal ℂ ({p} : Set (Point n))
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hfp
  have hJpoint : Y.ideal ⊔ Ideal.span {f} ≤ pointIdeal p := by
    apply sup_le
    · intro g hg
      change g ∈ MvPolynomial.vanishingIdeal ℂ ({p} : Set (Point n))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact hp g hg
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfpoint)
  letI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
  obtain ⟨P, hPmin, hPpoint⟩ := Ideal.exists_minimalPrimes_le hJpoint
  let W : AffineVariety n := ⟨P, hPmin.isPrime.isRadical⟩
  have hWcomp : W.IsComponentOf (Y.ideal ⊔ Ideal.span {f}) := hPmin
  have hWdim : W.dimension = 0 :=
    fa_bezout_proper_dimension Y W hY f hf hWcomp 0 hdim
  letI : P.IsPrime := hPmin.isPrime
  have hPdim : OAI.QuarticPowerFree.affineDimension P = 0 := hWdim
  have hPmax : P.IsMaximal := OAI.QuarticPowerFree.zeroDim_isMaximal P hPdim
  have hPeq : P = pointIdeal p := hPmax.eq_of_le (pointIdeal_isMaximal p).ne_top hPpoint
  rw [← hPeq]
  exact hPmin

/-- Two points of an irreducible curve on a common degree-one cut have
total multiplicity at most the degree. -/
theorem curve_two_point_cut {n : ℕ} (Y : AffineVariety n) (hY : Y.IsIrreducible)
    (hdim : Y.dimension = 1) (f : Poly n) (hf : f ∉ Y.ideal) (hfdeg : f.totalDegree ≤ 1)
    (p q : Point n) (hpq : p ≠ q) (hp : p ∈ Y.points) (hq : q ∈ Y.points)
    (hfp : MvPolynomial.eval p f = 0) (hfq : MvPolynomial.eval q f = 0) :
    Y.multiplicity p + Y.multiplicity q ≤ Y.degree := by
  let Vp := singletonPointVariety p
  let Vq := singletonPointVariety q
  have hne : Vp ≠ Vq := fun h => hpq (singletonPointVariety_injective h)
  have hVirr (x : Point n) : (singletonPointVariety x).IsIrreducible := singletonPointVariety_irreducible x
  have hVdeg (x : Point n) : (singletonPointVariety x).degree = 1 := singletonPointVariety_degree x
  let F : AffineFamily.Family n := {Vp, Vq}
  have hF : ∀ W ∈ F, W.IsComponentOf (Y.ideal ⊔ Ideal.span {f}) := by
    intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · exact curve_cut_point_minimal Y hY hdim f hf p hp hfp
    · rw [Finset.mem_singleton.mp hW]
      exact curve_cut_point_minimal Y hY hdim f hf q hq hfq
  obtain ⟨m, hm, hbound⟩ := fa_bezout_weighted_cut Y hY 0 hdim f hf F hF
  have hlocal (x : Point n) (hx : singletonPointVariety x ∈ F) :
      localLengthAt (Y.ideal ⊔ Ideal.span {f}) x = (m (singletonPointVariety x) : ℕ∞) := by
    have hcomponent := hm (singletonPointVariety x) hx (hVirr x)
    change Module.length (Localization.AtPrime (pointIdeal x))
        (Localization.AtPrime (pointIdeal x) ⧸
          (Y.ideal ⊔ Ideal.span {f}).map
            (algebraMap (Poly n) (Localization.AtPrime (pointIdeal x)))) = _ at hcomponent
    change Module.length (Localization.AtPrime (pointIdeal x))
        (Localization.AtPrime (pointIdeal x) ⧸
          (Y.ideal ⊔ Ideal.span {f}).map
            (algebraMap (Poly n) (Localization.AtPrime (pointIdeal x)))) = _
    exact hcomponent
  have hmult (x : Point n) (hxY : x ∈ Y.points) (hfx : MvPolynomial.eval x f = 0)
      (hx : singletonPointVariety x ∈ F) :
      Y.multiplicity x ≤ (m (singletonPointVariety x) : ℚ) := by
    obtain ⟨len, hlen, hle⟩ := curve_order_one_length Y hY hdim x hxY f hf hfx
    have heq : len = m (singletonPointVariety x) := by
      have h := hlen.symm.trans (hlocal x hx)
      exact_mod_cast h
    rw [← heq]
    exact hle
  have hpF : Vp ∈ F := Finset.mem_insert_self _ _
  have hqF : Vq ∈ F := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hsum : (∑ W ∈ F, (m W : ℚ) * W.degree) = (m Vp : ℚ) + (m Vq : ℚ) := by
    rw [Finset.sum_pair hne, hVdeg p, hVdeg q]
    ring
  have hdegY : 0 ≤ Y.degree := (zero_le_one).trans (Y.one_le_degree hY.ne_top)
  have hfdegQ : (f.totalDegree : ℚ) ≤ 1 := by exact_mod_cast hfdeg
  have hcut : (f.totalDegree : ℚ) * Y.degree ≤ Y.degree := by
    nlinarith
  have h1 := hmult p hp hfp hpF
  have h2 := hmult q hq hfq hqF
  rw [hsum] at hbound
  linarith

/-- Two distinct points of an irreducible curve either lie on a degree-one
polynomial not vanishing on the curve, or the curve is their joining line. -/
theorem exists_linear_through_two_or_line {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1)
    (p q : Point n) (hpq : p ≠ q) :
    (∃ f : Poly n, f.totalDegree ≤ 1 ∧ f ∉ Y.ideal ∧
      MvPolynomial.eval p f = 0 ∧ MvPolynomial.eval q f = 0) ∨
    ∃ a v : Point n, v ≠ 0 ∧ Y.points = {z | ∃ t : ℂ, z = a + t • v} := by
  let u : Point n := q - p
  have hu : u ≠ 0 := by
    intro h
    exact hpq (sub_eq_zero.mp h).symm
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin n, u j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  have hdeg1 (a b : ℂ) (k : Fin n) :
      (MvPolynomial.C a * (MvPolynomial.X k - MvPolynomial.C b) : Poly n).totalDegree ≤ 1 := by
    calc
      _ ≤ (MvPolynomial.C a : Poly n).totalDegree +
          (MvPolynomial.X k - MvPolynomial.C b : Poly n).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 1 := Nat.add_le_add (by simp) (by
        simpa only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C, Nat.max_zero] using
          MvPolynomial.totalDegree_sub (MvPolynomial.X k : Poly n) (MvPolynomial.C b))
      _ = 1 := rfl
  by_cases hoff : ∃ z ∈ Y.points, ∃ j k : Fin n,
      u j * (z k - p k) - u k * (z j - p j) ≠ 0
  · left
    obtain ⟨z, hz, j, k, hjk⟩ := hoff
    let f : Poly n := MvPolynomial.C (u j) * (MvPolynomial.X k - MvPolynomial.C (p k)) -
      MvPolynomial.C (u k) * (MvPolynomial.X j - MvPolynomial.C (p j))
    have hfeval (x : Point n) :
        MvPolynomial.eval x f = u j * (x k - p k) - u k * (x j - p j) := by
      simp [f]
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (hdeg1 _ _ _) (hdeg1 _ _ _))
    · intro hfY
      apply hjk
      rw [← hfeval z]
      have h := hz f hfY
      simpa [MvPolynomial.aeval_eq_eval] using h
    · rw [hfeval]
      ring
    · rw [hfeval]
      simp only [u, Pi.sub_apply]
      ring
  · right
    push Not at hoff
    have hsub : Y.points ⊆ (Bridges.complexLine p u).points := by
      rw [Bridges.complexLine_points p u j₀ hj₀]
      intro z hz
      refine ⟨(u j₀)⁻¹ * (z j₀ - p j₀), ?_⟩
      funext k
      have h := hoff z hz j₀ k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h
    letI : (Bridges.complexLine p u).ideal.IsPrime := Bridges.complexLine_irreducible p u
    have hI := (AffineVariety.subvariety_iff_points_subset Y (Bridges.complexLine p u)).mpr hsub
    have he := OAI.QuarticPowerFree.prime_same_dimension_eq (Bridges.complexLine p u).ideal
      Y.ideal hI (Bridges.complexLine_dimension p u j₀ hj₀) hdim
    have hYL : Y = Bridges.complexLine p u := AffineVariety.ext he.symm
    exact ⟨p, u, hu, by rw [hYL, Bridges.complexLine_points p u j₀ hj₀]⟩

/-! ### Plane polar support: common zeros of coprime forms and a moving chart -/

/-- A prime containing a nonzero polynomial contains one of its prime factors. -/
theorem exists_prime_factor_mem {n : ℕ} (Q : Ideal (Poly n)) [hQ : Q.IsPrime] (f : Poly n)
    (hf0 : f ≠ 0) (hf : f ∈ Q) : ∃ π : Poly n, Prime π ∧ π ∣ f ∧ π ∈ Q := by
  revert hf0 hf
  refine UniqueFactorizationMonoid.induction_on_prime f ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx _ hxQ
    exact absurd (Ideal.eq_top_of_isUnit_mem Q hxQ hx) hQ.ne_top
  · intro a p ha hp ih _ hpa
    rcases hQ.mem_or_mem hpa with hpQ | haQ
    · exact ⟨p, hp, dvd_mul_right p a, hpQ⟩
    · obtain ⟨π, hπ, hπa, hπQ⟩ := ih ha haQ
      exact ⟨π, hπ, hπa.mul_left p, hπQ⟩

theorem totalDegree_pos_of_prime {n : ℕ} (π : Poly n) (hπ : Prime π) : 0 < π.totalDegree := by
  by_contra h
  have h0 : π.totalDegree = 0 := by omega
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
  apply hπ.not_isUnit
  rw [hc]
  apply IsUnit.map MvPolynomial.C
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  apply hπ.ne_zero
  rw [hc, hzero, map_zero]

/-- Components of two equations without a common factor have codimension two. -/
theorem coprime_minimalPrime_dimension {n : ℕ} (f g : Poly (n+1)) (hf0 : f ≠ 0)
    (hcop : ∀ d : Poly (n+1), d ∣ f → d ∣ g → IsUnit d)
    (Q : Ideal (Poly (n+1))) (hQ : Q ∈ (Ideal.span ({f, g} : Set (Poly (n+1)))).minimalPrimes)
    (k : ℕ) (hn : n = k + 1) :
    OAI.QuarticPowerFree.affineDimension Q = k := by
  letI : Q.IsPrime := hQ.isPrime
  have hfQ : f ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  have hgQ : g ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  obtain ⟨π, hπ, hπf, hπQ⟩ := exists_prime_factor_mem Q f hf0 hfQ
  have hπg : ¬ π ∣ g := fun h => hπ.not_isUnit (hcop π hπf h)
  have hprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  let V : AffineVariety (n+1) := ⟨Ideal.span {π}, hprime.isRadical⟩
  have hV : V.IsIrreducible := hprime
  have hVdim : V.dimension = k + 1 := by
    change OAI.QuarticPowerFree.affineDimension (Ideal.span {π}) = k+1
    rw [OAI.QuarticPowerFree.affineDimension_hypersurface π hπ.ne_zero
      (totalDegree_pos_of_prime π hπ), hn]
  have hgV : g ∉ V.ideal := fun h => hπg (Ideal.mem_span_singleton.mp h)
  have hle : V.ideal ⊔ Ideal.span {g} ≤ Q :=
    sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπQ))
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgQ))
  obtain ⟨Q', hQ', hQ'Q⟩ := Ideal.exists_minimalPrimes_le hle
  have hspan : Ideal.span ({f, g} : Set (Poly (n+1))) ≤ Q' := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · obtain ⟨c, hc⟩ := hπf
      apply hQ'.1.2
      apply Ideal.mem_sup_left
      rw [hc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
    · rw [Set.mem_singleton_iff.mp hx]
      exact hQ'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hQQ' : Q ≤ Q' := hQ.2 ⟨hQ'.1.1, hspan⟩ hQ'Q
  have heq : Q' = Q := le_antisymm hQ'Q hQQ'
  let W : AffineVariety (n+1) := ⟨Q, hQ.isPrime.isRadical⟩
  have hW : W.IsComponentOf (V.ideal ⊔ Ideal.span {g}) := by
    change Q ∈ _
    rw [← heq]
    exact hQ'
  exact fa_bezout_proper_dimension V W hV g hgV hW k hVdim

/-- A prime ideal with finitely many complex zeros is a point ideal. -/
theorem prime_eq_pointIdeal_of_finite_zeroLocus {n : ℕ} (Q : Ideal (Poly n)) [hQ : Q.IsPrime]
    (hfin : (MvPolynomial.zeroLocus ℂ Q).Finite) :
    ∃ x : Point n, Q = pointIdeal x := by
  have hrad : MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ Q) = Q :=
    (MvPolynomial.vanishingIdeal_zeroLocus_eq_radical Q).trans hQ.isRadical.radical
  by_contra hno
  push Not at hno
  have hout : ∀ x ∈ hfin.toFinset, ∃ h ∈ pointIdeal x, h ∉ Q := by
    intro x hx
    have hxZ : x ∈ MvPolynomial.zeroLocus ℂ Q := hfin.mem_toFinset.mp hx
    have hxQ : Q ≤ pointIdeal x := by
      intro f hf
      change f ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      rw [MvPolynomial.mem_zeroLocus_iff] at hxZ
      simpa [MvPolynomial.aeval_eq_eval] using hxZ f hf
    by_contra hcon
    push Not at hcon
    exact hno x (le_antisymm hxQ (fun h hh => hcon h hh))
  choose h hh hhQ using hout
  let P : Poly n := ∏ x ∈ hfin.toFinset.attach, h x.1 x.2
  have hPQ : P ∈ Q := by
    rw [← hrad, MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    rw [map_prod]
    apply Finset.prod_eq_zero (i := ⟨y, hfin.mem_toFinset.mpr hy⟩) (Finset.mem_attach _ _)
    have hy' := hh y (hfin.mem_toFinset.mpr hy)
    change h y _ ∈ MvPolynomial.vanishingIdeal ℂ ({y} : Set (Point n)) at hy'
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hy'
    simpa [MvPolynomial.aeval_eq_eval] using hy'
  obtain ⟨x, -, hx⟩ := hQ.prod_mem_iff.mp hPQ
  exact hhQ x.1 x.2 hx

/-- Projective common zeros of two ternary polynomials, read on representatives. -/
def projectiveCommonZeros (f g : Poly 3) : Set (ProjectivePoint 3) :=
  {p | MvPolynomial.eval p.rep f = 0 ∧ MvPolynomial.eval p.rep g = 0}

theorem homogeneous_eval_smul {n D : ℕ} (F : Poly n) (hF : F.IsHomogeneous D)
    (c : ℂ) (v : Point n) :
    MvPolynomial.eval (c • v) F = c^D * MvPolynomial.eval v F := by
  have h := homogeneous_aeval_scale F hF c v
  simp only [MvPolynomial.aeval_eq_eval] at h
  exact h

/-- Two homogeneous ternary forms without common factor have finitely many
projective common zeros: each zero line is a whole minimal prime. -/
theorem projectiveCommonZeros_finite (f g : Poly 3) (hf0 : f ≠ 0) (D E : ℕ)
    (hfh : f.IsHomogeneous D) (hgh : g.IsHomogeneous E)
    (hcop : ∀ d : Poly 3, d ∣ f → d ∣ g → IsUnit d) :
    (projectiveCommonZeros f g).Finite := by
  let I : Ideal (Poly 3) := Ideal.span ({f, g} : Set (Poly 3))
  have hmin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  let L : ProjectivePoint 3 → Ideal (Poly 3) := fun p => (Bridges.complexLine 0 p.rep).ideal
  have hmaps : Set.MapsTo L (projectiveCommonZeros f g) I.minimalPrimes := by
    intro p hp
    obtain ⟨j, hj⟩ : ∃ j, p.rep j ≠ 0 := by
      by_contra h
      push Not at h
      exact p.rep_nonzero (funext h)
    letI : (L p).IsPrime := Bridges.complexLine_irreducible 0 p.rep
    have hLdim : OAI.QuarticPowerFree.affineDimension (L p) = 0 + 1 :=
      Bridges.complexLine_dimension 0 p.rep j hj
    have hIL : I ≤ L p := by
      change I ≤ (Bridges.complexLine 0 p.rep).ideal
      rw [← AffineVariety.vanishingIdeal_points, Bridges.complexLine_points 0 p.rep j hj]
      apply Ideal.span_le.mpr
      intro q hq
      rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_iff]
      rintro z ⟨t, rfl⟩
      rcases hq with rfl | hq
      · simp only [zero_add, MvPolynomial.aeval_eq_eval]
        rw [homogeneous_eval_smul q hfh, hp.1, mul_zero]
      · rw [Set.mem_singleton_iff.mp hq]
        simp only [zero_add, MvPolynomial.aeval_eq_eval]
        rw [homogeneous_eval_smul g hgh, hp.2, mul_zero]
    obtain ⟨Q, hQ, hQL⟩ := Ideal.exists_minimalPrimes_le hIL
    letI : Q.IsPrime := hQ.isPrime
    have hQdim : OAI.QuarticPowerFree.affineDimension Q = 0 + 1 :=
      coprime_minimalPrime_dimension f g hf0 hcop Q hQ 1 rfl
    have hQeq : Q = L p := OAI.QuarticPowerFree.prime_same_dimension_eq Q (L p) hQL hQdim hLdim
    rw [← hQeq]
    exact hQ
  have hinj : Set.InjOn L (projectiveCommonZeros f g) := by
    intro p _ q _ hpq
    obtain ⟨j, hj⟩ : ∃ j, p.rep j ≠ 0 := by
      by_contra h
      push Not at h
      exact p.rep_nonzero (funext h)
    obtain ⟨k, hk⟩ : ∃ k, q.rep k ≠ 0 := by
      by_contra h
      push Not at h
      exact q.rep_nonzero (funext h)
    have hlines : Bridges.complexLine 0 p.rep = Bridges.complexLine 0 q.rep :=
      AffineVariety.ext hpq
    have hmem : q.rep ∈ (Bridges.complexLine 0 p.rep).points := by
      rw [hlines, Bridges.complexLine_points 0 q.rep k hk]
      exact ⟨1, by simp⟩
    rw [Bridges.complexLine_points 0 p.rep j hj] at hmem
    obtain ⟨t, ht⟩ := hmem
    rw [zero_add] at ht
    rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q]
    exact ((Projectivization.mk_eq_mk_iff' ℂ q.rep p.rep q.rep_nonzero p.rep_nonzero).mpr
      ⟨t, ht.symm⟩).symm
  exact Set.Finite.of_finite_image (hmin.subset hmaps.image_subset) hinj

/-- A finite family of nonzero ternary vectors avoids one member of the
linear forms `X₀ + t X₁ + t² X₂`. -/
theorem exists_avoiding_parameter (S : Finset (ProjectivePoint 3)) :
    ∃ t : ℂ, ∀ p ∈ S, p.rep 0 + t * p.rep 1 + t^2 * p.rep 2 ≠ 0 := by
  classical
  let P : ProjectivePoint 3 → Polynomial ℂ := fun p =>
    Polynomial.C (p.rep 0) + Polynomial.C (p.rep 1) * Polynomial.X +
      Polynomial.C (p.rep 2) * Polynomial.X^2
  have hP (p : ProjectivePoint 3) : P p ≠ 0 := by
    intro hzero
    apply p.rep_nonzero
    have h0 := congrArg (fun F => Polynomial.coeff F 0) hzero
    have h1 := congrArg (fun F => Polynomial.coeff F 1) hzero
    have h2 := congrArg (fun F => Polynomial.coeff F 2) hzero
    simp [P, Polynomial.coeff_X, Polynomial.coeff_X_pow] at h0 h1 h2
    funext k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  let Q : Polynomial ℂ := ∏ p ∈ S, P p
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p _ => hP p)
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset Q.roots.toFinset
  refine ⟨t, ?_⟩
  have hQt : Q.eval t ≠ 0 := by
    intro h
    apply ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    exact h
  intro p hp
  have hprod : ∏ q ∈ S, (P q).eval t ≠ 0 := by
    rwa [← Polynomial.eval_prod]
  have hpt := (Finset.prod_ne_zero_iff.mp hprod) p hp
  have hev : (P p).eval t = p.rep 0 + t * p.rep 1 + t^2 * p.rep 2 := by
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    ring
  rwa [hev] at hpt

/-- Affine substitution of the moving chart `X₀ + t X₁ + t² X₂ = 1`. -/
def polarChart (t : ℂ) : Fin 3 → Poly 2 :=
  ![1 - MvPolynomial.C t * MvPolynomial.X 0 - MvPolynomial.C (t^2) * MvPolynomial.X 1,
    MvPolynomial.X 0, MvPolynomial.X 1]

def polarLift (t : ℂ) (x : Point 2) : Point 3 :=
  ![1 - t * x 0 - t^2 * x 1, x 0, x 1]

theorem eval_polarChart (t : ℂ) (x : Point 2) (k : Fin 3) :
    MvPolynomial.eval x (polarChart t k) = polarLift t x k := by
  fin_cases k <;> simp [polarChart, polarLift]

theorem eval_aeval_polarChart (t : ℂ) (x : Point 2) (F : Poly 3) :
    MvPolynomial.eval x (MvPolynomial.aeval (polarChart t) F) =
      MvPolynomial.eval (polarLift t x) F := by
  rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
  have h : (fun k => MvPolynomial.aeval x (polarChart t k)) = polarLift t x := by
    funext k
    exact eval_polarChart t x k
  rw [h]
  rfl

theorem polarChart_degree (t : ℂ) (k : Fin 3) : (polarChart t k).totalDegree ≤ 1 := by
  have hX (j : Fin 2) : (MvPolynomial.X j : Poly 2).totalDegree ≤ 1 := by
    simp
  have hCX (c : ℂ) (j : Fin 2) :
      (MvPolynomial.C c * MvPolynomial.X j : Poly 2).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  fin_cases k
  · simp only [polarChart, Fin.zero_eta, Matrix.cons_val_zero]
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ (hCX _ _))
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ (hCX _ _))
    simp
  · simpa [polarChart] using hX 0
  · simpa [polarChart] using hX 1

theorem polarLift_ne_zero (t : ℂ) (x : Point 2) : polarLift t x ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [polarLift] at h0 h1 h2
  rw [h1, h2] at h0
  simp at h0

theorem polarLift_injective_mk (t : ℂ) (x y : Point 2)
    (h : Projectivization.mk ℂ (polarLift t x) (polarLift_ne_zero t x) =
      Projectivization.mk ℂ (polarLift t y) (polarLift_ne_zero t y)) : x = y := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [polarLift] at h0 h1 h2
  have hc1 : c = 1 := by
    rw [← h1, ← h2] at h0
    linear_combination h0
  subst hc1
  funext j
  fin_cases j
  · simp at h1
    exact h1.symm
  · simp at h2
    exact h2.symm

/-- The chart point of a projective point in the moving chart. -/
def polarPoint (t : ℂ) (p : ProjectivePoint 3) : Point 2 :=
  let ℓ := p.rep 0 + t * p.rep 1 + t^2 * p.rep 2
  ![p.rep 1 / ℓ, p.rep 2 / ℓ]

theorem polarLift_polarPoint (t : ℂ) (p : ProjectivePoint 3)
    (hℓ : p.rep 0 + t * p.rep 1 + t^2 * p.rep 2 ≠ 0) :
    polarLift t (polarPoint t p) = (p.rep 0 + t * p.rep 1 + t^2 * p.rep 2)⁻¹ • p.rep := by
  funext k
  fin_cases k
  · simp only [polarLift, polarPoint, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · simp [polarLift, polarPoint, div_eq_mul_inv, mul_comm]
  · simp [polarLift, polarPoint, div_eq_mul_inv, mul_comm]

theorem polarPoint_injOn (t : ℂ) (S : Finset (ProjectivePoint 3))
    (hS : ∀ p ∈ S, p.rep 0 + t * p.rep 1 + t^2 * p.rep 2 ≠ 0) :
    Set.InjOn (polarPoint t) (S : Set (ProjectivePoint 3)) := by
  intro p hp q hq hpq
  set ℓp := p.rep 0 + t * p.rep 1 + t^2 * p.rep 2 with hℓp
  set ℓq := q.rep 0 + t * q.rep 1 + t^2 * q.rep 2 with hℓq
  have hlp : polarLift t (polarPoint t p) = ℓp⁻¹ • p.rep := polarLift_polarPoint t p (hS p hp)
  have hlq : polarLift t (polarPoint t q) = ℓq⁻¹ • q.rep := polarLift_polarPoint t q (hS q hq)
  have hne : ℓp ≠ 0 := hS p hp
  have heq : ℓp⁻¹ • p.rep = ℓq⁻¹ • q.rep := by rw [← hlp, ← hlq, hpq]
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q]
  apply (Projectivization.mk_eq_mk_iff' ℂ p.rep q.rep p.rep_nonzero q.rep_nonzero).mpr
  refine ⟨ℓp * ℓq⁻¹, ?_⟩
  rw [mul_smul, ← heq, smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- Chart orders transfer to the moving chart. -/
theorem polar_moving_chart_order (t : ℂ) (F : Poly 3) (D : ℕ) (hF : F.IsHomogeneous D)
    (p : ProjectivePoint 3) (hℓ : p.rep 0 + t * p.rep 1 + t^2 * p.rep 2 ≠ 0)
    (i : Fin 3) (hi : p.rep i ≠ 0) (r : ℕ)
    (horder : OrderAtLeast (chartPullback i F) (chartCoordinates i p) r) :
    OrderAtLeast (MvPolynomial.aeval (polarChart t) F) (polarPoint t p) r := by
  have hlift := polarLift_polarPoint t p hℓ
  have heval (k : Fin 3) : MvPolynomial.eval (polarPoint t p) (polarChart t k) =
      (p.rep 0 + t * p.rep 1 + t^2 * p.rep 2)⁻¹ * p.rep k := by
    rw [eval_polarChart, hlift]
    rfl
  apply homogeneous_pullback_order (polarChart t) F hF (polarPoint t p) i
  · rw [heval]
    exact mul_ne_zero (inv_ne_zero hℓ) hi
  · have hpt : (fun j => MvPolynomial.eval (polarPoint t p) (polarChart t (i.succAbove j)) /
        MvPolynomial.eval (polarPoint t p) (polarChart t i)) = chartCoordinates i p := by
      funext j
      rw [heval, heval]
      simp only [chartCoordinates]
      field_simp
    rw [hpt]
    exact horder

theorem totalDegree_pos_of_eval_zero' {n : ℕ} (f : Poly n)
    (hf : f ≠ 0) (x : Point n) (hfx : MvPolynomial.eval x f = 0) :
    0 < f.totalDegree := by
  by_contra hnot
  have hz : f.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hconst := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
  rw [hconst, MvPolynomial.eval_C] at hfx
  apply hf
  rw [hconst, hfx, map_zero]

theorem not_isUnit_of_totalDegree_pos {n : ℕ} (f : Poly n) (h : 0 < f.totalDegree) :
    ¬ IsUnit f := by
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hf0 : f ≠ 0 := hu.ne_zero
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hg
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain hf0 hg0
  rw [hg, MvPolynomial.totalDegree_one] at hdeg
  omega

/-- A nonzero form stays nonzero in the moving chart. -/
theorem aeval_polarChart_ne_zero (t : ℂ) (F : Poly 3) (D : ℕ) (hF : F.IsHomogeneous D)
    (hF0 : F ≠ 0) : MvPolynomial.aeval (polarChart t) F ≠ 0 := by
  intro hzero
  apply hF0
  let ℓ : Poly 3 := MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1 +
    MvPolynomial.C (t^2) * MvPolynomial.X 2
  have hℓeval (w : Point 3) : MvPolynomial.eval w ℓ = w 0 + t * w 1 + t^2 * w 2 := by
    simp [ℓ]
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    have h1 := hℓeval ![1, 0, 0]
    rw [h, map_zero] at h1
    simp at h1
  have hprod : ℓ * F = 0 := by
    apply MvPolynomial.funext
    intro w
    simp only [map_mul, map_zero]
    by_cases hw : MvPolynomial.eval w ℓ = 0
    · rw [hw, zero_mul]
    · rw [hℓeval] at hw
      let c : ℂ := w 0 + t * w 1 + t^2 * w 2
      let y : Point 2 := ![w 1 / c, w 2 / c]
      have hwy : w = c • polarLift t y := by
        funext k
        fin_cases k
        · simp only [polarLift, y, c, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
            Matrix.cons_val_zero, Matrix.cons_val_one]
          field_simp
          ring
        · have hc : c ≠ 0 := hw
          show w 1 = c * (w 1 / c)
          field_simp
        · have hc : c ≠ 0 := hw
          show w 2 = c * (w 2 / c)
          field_simp
      have hy : MvPolynomial.eval (polarLift t y) F = 0 := by
        rw [← eval_aeval_polarChart, hzero, map_zero]
      rw [hwy, homogeneous_eval_smul F hF, hy, mul_zero, mul_zero]
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd h hℓ0
  · exact h

/-- Weighted plane Bézout for a form and a coprime polar-type companion, with
all high-multiplicity points moved into one affine chart. -/
theorem polar_budget_core (μ : ProjectivePoint 3 → ℚ) (f g : Poly 3) (a : ℕ)
    (hf0 : f ≠ 0) (ha : 1 ≤ a) (hfdeg : f.totalDegree = a) (hfhom : f.IsHomogeneous a)
    (hghom : g.IsHomogeneous (a-1)) (hgdeg : g.totalDegree ≤ a - 1)
    (hcop : ∀ d : Poly 3, d ∣ f → d ∣ g → IsUnit d)
    (S : Finset (ProjectivePoint 3))
    (hS : ∀ p ∈ S, ∃ m : ℕ, 2 ≤ m ∧ μ p = m ∧
      OrderAtLeast (chartPullback (chartIndex p) f) (chartCoordinates (chartIndex p) p) m ∧
      OrderAtLeast (chartPullback (chartIndex p) g) (chartCoordinates (chartIndex p) p) (m-1)) :
    ∑ p ∈ S, μ p * (μ p - 1) ≤ (a : ℚ) * ((a : ℚ) - 1) := by
  classical
  have haQ : (1 : ℚ) ≤ a := by exact_mod_cast ha
  by_cases hSe : S = ∅
  · rw [hSe, Finset.sum_empty]
    nlinarith
  obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
  choose! m hm2 hμ hford hgord using hS
  obtain ⟨t, ht⟩ := exists_avoiding_parameter S
  let u : Poly 2 := MvPolynomial.aeval (polarChart t) f
  let v : Poly 2 := MvPolynomial.aeval (polarChart t) g
  have huord (p) (hp : p ∈ S) : OrderAtLeast u (polarPoint t p) (m p) :=
    polar_moving_chart_order t f a hfhom p (ht p hp) (chartIndex p) (chartIndex_nonzero p) _
      (hford p hp)
  have hvord (p) (hp : p ∈ S) : OrderAtLeast v (polarPoint t p) (m p - 1) :=
    polar_moving_chart_order t g (a-1) hghom p (ht p hp) (chartIndex p) (chartIndex_nonzero p) _
      (hgord p hp)
  have hupt (p) (hp : p ∈ S) : u ∈ pointIdeal (polarPoint t p) :=
    Ideal.pow_le_self (by have := hm2 p hp; omega) (huord p hp)
  have hvpt (p) (hp : p ∈ S) : v ∈ pointIdeal (polarPoint t p) :=
    Ideal.pow_le_self (by have := hm2 p hp; omega) (hvord p hp)
  have hevalpt (q : Poly 2) (x : Point 2) (hq : q ∈ pointIdeal x) : MvPolynomial.eval x q = 0 := by
    change q ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point 2)) at hq
    rwa [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hq
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact not_isUnit_of_totalDegree_pos f (by omega) (hcop f dvd_rfl (dvd_zero f))
  have hu0 : u ≠ 0 := aeval_polarChart_ne_zero t f a hfhom hf0
  have hv0 : v ≠ 0 := aeval_polarChart_ne_zero t g (a-1) hghom hg0
  have hZfin := projectiveCommonZeros_finite f g hf0 a (a-1) hfhom hghom hcop
  let J : Ideal (Poly 2) := Ideal.span ({u, v} : Set (Poly 2))
  have hVfin : (MvPolynomial.zeroLocus ℂ J).Finite := by
    have hmaps : Set.MapsTo
        (fun y => Projectivization.mk ℂ (polarLift t y) (polarLift_ne_zero t y))
        (MvPolynomial.zeroLocus ℂ J) (projectiveCommonZeros f g) := by
      intro y hy
      rw [MvPolynomial.mem_zeroLocus_iff] at hy
      have hyu : MvPolynomial.eval (polarLift t y) f = 0 := by
        have h := hy u (Ideal.subset_span (by simp))
        rw [← eval_aeval_polarChart]
        exact h
      have hyv : MvPolynomial.eval (polarLift t y) g = 0 := by
        have h := hy v (Ideal.subset_span (by simp))
        rw [← eval_aeval_polarChart]
        exact h
      obtain ⟨c, hc⟩ :=
        Projectivization.exists_smul_eq_mk_rep ℂ (polarLift t y) (polarLift_ne_zero t y)
      refine ⟨?_, ?_⟩
      · change MvPolynomial.eval (Projectivization.mk ℂ _ _).rep f = 0
        rw [← hc, Units.smul_def, homogeneous_eval_smul f hfhom, hyu, mul_zero]
      · change MvPolynomial.eval (Projectivization.mk ℂ _ _).rep g = 0
        rw [← hc, Units.smul_def, homogeneous_eval_smul g hghom, hyv, mul_zero]
    exact Set.Finite.of_finite_image (hZfin.subset hmaps.image_subset)
      (fun y1 _ y2 _ h => polarLift_injective_mk t y1 y2 h)
  have hpmin (p) (hp : p ∈ S) : pointIdeal (polarPoint t p) ∈ J.minimalPrimes := by
    have hle : J ≤ pointIdeal (polarPoint t p) := by
      apply Ideal.span_le.mpr
      intro q hq
      rcases hq with rfl | hq
      · exact hupt p hp
      · rw [Set.mem_singleton_iff.mp hq]
        exact hvpt p hp
    letI : (pointIdeal (polarPoint t p)).IsPrime := (pointIdeal_isMaximal _).isPrime
    obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
    letI : Q.IsPrime := hQ.isPrime
    obtain ⟨y, hy⟩ := prime_eq_pointIdeal_of_finite_zeroLocus Q
      (hVfin.subset (MvPolynomial.zeroLocus_anti_mono hQ.1.2))
    have hQeq : Q = pointIdeal (polarPoint t p) := by
      rw [hy] at hQle ⊢
      exact (pointIdeal_isMaximal y).eq_of_le (pointIdeal_isMaximal _).ne_top hQle
    rw [← hQeq]
    exact hQ
  have hupos : 0 < u.totalDegree :=
    totalDegree_pos_of_eval_zero' u hu0 (polarPoint t p₀) (hevalpt u _ (hupt p₀ hp₀))
  have hvpos : 0 < v.totalDegree :=
    totalDegree_pos_of_eval_zero' v hv0 (polarPoint t p₀) (hevalpt v _ (hvpt p₀ hp₀))
  have hudeg : u.totalDegree ≤ a := hfdeg ▸
    OAI.QuarticPowerFree.totalDegree_linear_substitute_le (polarChart t) (polarChart_degree t) f
  have hvdeg : v.totalDegree ≤ a - 1 :=
    (OAI.QuarticPowerFree.totalDegree_linear_substitute_le (polarChart t)
      (polarChart_degree t) g).trans hgdeg
  let eqs : Fin 2 → Poly 2 := ![u, v]
  have hrange : Set.range eqs = {u, v} := by
    ext q
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff, eqs,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  let T : Finset (Point 2) := S.image (polarPoint t)
  let F : AffineFamily.Family 2 := T.image singletonPointVariety
  have hFpure : AffineFamily.IsPure F 0 := by
    intro U hU
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hU
    exact ⟨singletonPointVariety_irreducible x, singletonPointVariety_dimension x⟩
  have hcomponents : ∀ U ∈ F, U.IsComponentOf (Ideal.span (Set.range eqs)) := by
    intro U hU
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    change pointIdeal (polarPoint t p) ∈ (Ideal.span (Set.range eqs)).minimalPrimes
    rw [hrange]
    exact hpmin p hp
  have hdegree : ∀ j, 1 ≤ (eqs j).totalDegree := by
    intro j
    fin_cases j
    · exact hupos
    · exact hvpos
  obtain ⟨mm, hmm, hbezout⟩ :=
    fa_bezout_refined_two (by omega) eqs hdegree F hFpure hcomponents
  have hweightSum : (∑ U ∈ F, (mm U : ℚ) * U.degree) =
      ∑ x ∈ T, (mm (singletonPointVariety x) : ℚ) := by
    rw [Finset.sum_image (fun x _ y _ h => singletonPointVariety_injective h)]
    apply Finset.sum_congr rfl
    intro x _
    rw [singletonPointVariety_degree, mul_one]
  have hprod : ∏ j : Fin 2, ((eqs j).totalDegree : ℚ) =
      (u.totalDegree : ℚ) * (v.totalDegree : ℚ) := by
    simp [eqs, Fin.prod_univ_two]
  have hlocal (x : Point 2) (hx : x ∈ T) :
      localLengthAt (Ideal.span {u, v}) x = (mm (singletonPointVariety x) : ℕ∞) := by
    have h := hmm (singletonPointVariety x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (singletonPointVariety_irreducible x)
    rw [hrange] at h
    change Module.length (Localization.AtPrime (pointIdeal x))
      (Localization.AtPrime (pointIdeal x) ⧸
        (Ideal.span {u, v}).map (algebraMap (Poly 2) (Localization.AtPrime (pointIdeal x)))) = _ at h
    unfold localLengthAt localizedIdeal
    exact h
  have hpointLower (p) (hp : p ∈ S) :
      μ p * (μ p - 1) ≤ (mm (singletonPointVariety (polarPoint t p)) : ℚ) := by
    have hlen := fa_bezout_plane_local_orders u v (polarPoint t p) (m p) (m p - 1)
      (huord p hp) (hvord p hp)
    rw [hlocal _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)] at hlen
    have hnat : m p * (m p - 1) ≤ mm (singletonPointVariety (polarPoint t p)) := by
      exact_mod_cast hlen
    rw [hμ p hp]
    have h1 : 1 ≤ m p := by have := hm2 p hp; omega
    calc (m p : ℚ) * ((m p : ℚ) - 1) = ((m p * (m p - 1) : ℕ) : ℚ) := by
          rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one]
      _ ≤ _ := by exact_mod_cast hnat
  have himage : (∑ x ∈ T, (mm (singletonPointVariety x) : ℚ)) =
      ∑ p ∈ S, (mm (singletonPointVariety (polarPoint t p)) : ℚ) :=
    Finset.sum_image (fun p hp q hq h => polarPoint_injOn t S ht (Finset.mem_coe.mpr hp)
      (Finset.mem_coe.mpr hq) h)
  calc ∑ p ∈ S, μ p * (μ p - 1) ≤ ∑ p ∈ S, (mm (singletonPointVariety (polarPoint t p)) : ℚ) :=
        Finset.sum_le_sum hpointLower
    _ = ∑ U ∈ F, (mm U : ℚ) * U.degree := by rw [hweightSum, himage]
    _ ≤ ∏ j : Fin 2, ((eqs j).totalDegree : ℚ) := hbezout
    _ = (u.totalDegree : ℚ) * (v.totalDegree : ℚ) := hprod
    _ ≤ (a : ℚ) * ((a : ℚ) - 1) := by
        have h1 : (u.totalDegree : ℚ) ≤ a := by exact_mod_cast hudeg
        have hcast : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by
          rw [Nat.cast_sub ha, Nat.cast_one]
        have h2 : (v.totalDegree : ℚ) ≤ (a : ℚ) - 1 := by
          rw [← hcast]
          exact_mod_cast hvdeg
        have h3 : (0 : ℚ) ≤ v.totalDegree := Nat.cast_nonneg _
        nlinarith

end
end DistinctDistances.TrackA
