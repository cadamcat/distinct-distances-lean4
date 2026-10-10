import DistinctDistances.TrackA.Definitions
import DistinctDistances.TrackA.ADepthAux
import DistinctDistances.OAIInterface.PolynomialIsolation
import DistinctDistances.TrackA.PlaneLengthSupport
import DistinctDistances.TrackA.PointPowerLengthSupport
import DistinctDistances.TrackA.WeightedCutSupport
import DistinctDistances.TrackA.BezoutRefinedSupport
import DistinctDistances.TrackA.RelativePointBezoutSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- `FA.bezout.proper-dimension`, polynomial.tex:42–47. Direct OAI wrapper. -/
theorem fa_bezout_proper_dimension {n : ℕ} (V W : AffineVariety n)
    (hV : V.IsIrreducible) (f : Poly n) (hf : f ∉ V.ideal)
    (hW : W.IsComponentOf (V.ideal ⊔ Ideal.span {f})) (k : ℕ)
    (hdim : V.dimension = k+1) : W.dimension = k := by
  letI : V.ideal.IsPrime := hV
  letI : W.ideal.IsPrime := hW.isPrime
  exact OAI.QuarticPowerFree.proper_cut_component_dimension
    V.ideal W.ideal f hf hW hdim

/-- `FA.bezout.proper-degree`, polynomial.tex:42–49. Direct OAI degree-budget wrapper. -/
theorem fa_bezout_proper_degree {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (f : Poly n) (hf : f ∉ V.ideal)
    (F : AffineFamily.Family n) (hF : ∀ W ∈ F, W.IsComponentOf (V.ideal ⊔ Ideal.span {f}))
    (k : ℕ) (hdim : V.dimension = k+1) :
    AffineFamily.degree F ≤ (f.totalDegree : ℚ) * V.degree := by
  classical
  letI : V.ideal.IsPrime := hV
  have hQ : ∀ W : F, W.val.ideal ∈ (V.ideal ⊔ Ideal.span {f}).minimalPrimes := by
    intro W
    exact hF W.val W.property
  have hQi : Function.Injective (fun W : F => W.val.ideal) := by
    intro W₁ W₂ h
    apply Subtype.ext
    exact AffineVariety.ext h
  have hdegree :
      (∑ W : F, OAI.QuarticPowerFree.affineDegree W.val.ideal) ≤
        (f.totalDegree : ℚ) * OAI.QuarticPowerFree.affineDegree V.ideal :=
    OAI.QuarticPowerFree.proper_cut_sum_affineDegree_le
      V.ideal f hf hdim (fun W : F => W.val.ideal) hQ hQi
  have hsum :
      (∑ W ∈ F, OAI.QuarticPowerFree.affineDegree W.ideal) =
        ∑ W : F, OAI.QuarticPowerFree.affineDegree W.val.ideal := by
    rw [Finset.univ_eq_attach]
    exact (Finset.sum_attach F _).symm
  simpa only [AffineFamily.degree, AffineVariety.degree] using hsum.trans_le hdegree

/-- `FA.bezout.projective-cut`, polynomial.tex:42–62; concentration.tex:107–133. -/
private theorem projective_points_nonempty_of_irreducible {n : ℕ}
    (V : ProjectiveVariety n) (hV : V.IsIrreducible) : V.points.Nonempty := by
  classical
  by_contra hne
  have hcone : V.affineCone.points ⊆ ({0} : Set (Point n)) := by
    intro x hx
    by_contra hnot
    have hx0 : x ≠ 0 := by simpa using hnot
    have hproj : Projectivization.mk ℂ x hx0 ∈ V.points :=
      (ProjectiveVariety.mem_points_mk_iff V x hx0).2 hx
    exact hne ⟨Projectivization.mk ℂ x hx0, hproj⟩
  have hcoord : ∀ i : Fin n, MvPolynomial.X i ∈ V.ideal := by
    intro i
    change MvPolynomial.X i ∈ V.affineCone.ideal
    rw [← AffineVariety.vanishingIdeal_points V.affineCone,
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hx0 : x = 0 := by simpa using hcone hx
    subst x
    simp
  have hone : (1 : Poly n) ∈ V.ideal := by
    apply V.isSaturated
    intro i
    exact ⟨1, by simpa using hcoord i⟩
  exact hV.ne_top (V.ideal.eq_top_iff_one.mpr hone)

theorem fa_bezout_projective_cut {n : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (f : Poly n) (d : ℕ) (hhom : f.IsHomogeneous d)
    (hf : f ∉ V.ideal) (k : ℕ) (hdim : V.dimension = k+1)
    (F : ProjectiveFamily.Family n)
    (hF : ∀ W ∈ F, W.ideal ∈ (V.ideal ⊔ Ideal.span {f}).minimalPrimes) :
    (∀ W ∈ F, W.dimension = k) ∧ ProjectiveFamily.degree F ≤ (d : ℚ) * V.degree := by
  classical
  letI : V.ideal.IsPrime := hV
  have hVne : V.points.Nonempty := projective_points_nonempty_of_irreducible V hV
  have hVconeDim : V.affineCone.dimension = (k+1)+1 := by
    rw [ProjectiveVariety.dimension_cone V hVne, hdim]
  refine ⟨?_, ?_⟩
  · intro W hWF
    have hWcomp : W.affineCone.IsComponentOf
        (V.affineCone.ideal ⊔ Ideal.span {f}) := hF W hWF
    have hWconeDim : W.affineCone.dimension = k+1 :=
      fa_bezout_proper_dimension V.affineCone W.affineCone hV f hf hWcomp
        (k+1) hVconeDim
    have hWne : W.points.Nonempty :=
      projective_points_nonempty_of_irreducible W hWcomp.isPrime
    have hWcone := ProjectiveVariety.dimension_cone W hWne
    omega
  · have hQ : ∀ W : F, W.val.ideal ∈ (V.ideal ⊔ Ideal.span {f}).minimalPrimes := by
      intro W
      exact hF W.val W.property
    have hQi : Function.Injective (fun W : F => W.val.ideal) := by
      intro W₁ W₂ h
      apply Subtype.ext
      exact ProjectiveVariety.ext h
    have hdegreeCone :
        (∑ W : F, OAI.QuarticPowerFree.affineDegree W.val.ideal) ≤
          (f.totalDegree : ℚ) * OAI.QuarticPowerFree.affineDegree V.ideal :=
      OAI.QuarticPowerFree.proper_cut_sum_affineDegree_le V.ideal f hf hVconeDim
        (fun W : F => W.val.ideal) hQ hQi
    have hdegreeNonneg : (0 : ℚ) ≤ V.affineCone.degree :=
      (zero_le_one).trans (V.affineCone.one_le_degree hV.ne_top)
    have hdtotal : (f.totalDegree : ℚ) ≤ (d : ℚ) := by
      exact_mod_cast hhom.totalDegree_le
    have hdegreeCone' :
        (∑ W : F, OAI.QuarticPowerFree.affineDegree W.val.ideal) ≤
          (d : ℚ) * V.affineCone.degree := by
      calc
        _ ≤ (f.totalDegree : ℚ) * V.affineCone.degree := hdegreeCone
        _ ≤ (d : ℚ) * V.affineCone.degree := mul_le_mul_of_nonneg_right hdtotal hdegreeNonneg
    have hsum : ProjectiveFamily.degree F =
        ∑ W : F, OAI.QuarticPowerFree.affineDegree W.val.ideal := by
      calc
        ProjectiveFamily.degree F = ∑ W ∈ F, W.affineCone.degree := by
          unfold ProjectiveFamily.degree
          refine Finset.sum_congr rfl ?_
          intro W hW
          exact (ProjectiveVariety.degree_cone W).symm
        _ = ∑ W : F, W.val.affineCone.degree := by
          rw [Finset.univ_eq_attach]
          exact (Finset.sum_attach F _).symm
        _ = _ := rfl
    rw [← V.degree_cone]
    exact hsum ▸ hdegreeCone'

/-- `FA.bezout.zero-dimensional`, polynomial.tex:91–94,334–335. -/
theorem fa_bezout_zero_dimensional {n : ℕ} (V : AffineVariety n) (hV : V.IsPure 0) :
    V.points.Finite ∧ (V.points.ncard : ℚ) = V.degree := by
  classical
  let F : AffineFamily.Family n := Finset.univ.image
    (fun c : V.Component => c.variety)
  have hFp : AffineFamily.IsPure F 0 := by
    intro W hW
    rcases Finset.mem_image.mp hW with ⟨c, -, rfl⟩
    exact ⟨AffineVariety.Component.irreducible c, hV c⟩
  have hVarietyEq : V = AffineFamily.locus F := by
    apply (AffineVariety.points_eq_iff V (AffineFamily.locus F)).mp
    rw [AffineVariety.points_components, AffineFamily.points_locus]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨c, hx⟩
      refine ⟨c.variety, ?_, hx⟩
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
    · rintro ⟨W, hW, hx⟩
      rcases Finset.mem_image.mp hW with ⟨c, -, rfl⟩
      exact ⟨c, hx⟩
  have hdecomp : V.degree = AffineFamily.degree F := by
    calc
      V.degree = (AffineFamily.locus F).degree := congrArg AffineVariety.degree hVarietyEq
      _ = AffineFamily.degree F := AffineFamily.degree_locus F 0 hFp
  have hdata (W : F) : ∃ x : Point n, W.val.points = {x} ∧ W.val.degree = 1 := by
    exact zeroDim_irreducible_data W.val (hFp W.val W.property).1
      (hFp W.val W.property).2
  let pt : F → Point n := fun W => Classical.choose (hdata W)
  have hpt (W : F) : W.val.points = {pt W} ∧ W.val.degree = 1 :=
    Classical.choose_spec (hdata W)
  have hptInj : Function.Injective pt := by
    intro W₁ W₂ h
    apply Subtype.ext
    apply (AffineVariety.points_eq_iff W₁.val W₂.val).mp
    calc
      W₁.val.points = {pt W₁} := (hpt W₁).1
      _ = {pt W₂} := congrArg (fun x : Point n => ({x} : Set (Point n))) h
      _ = W₂.val.points := (hpt W₂).1.symm
  have hfamily : V.points = ⋃ W ∈ F, W.points :=
    (congrArg AffineVariety.points hVarietyEq).trans (AffineFamily.points_locus F)
  have hVpoints : V.points = Set.range pt := by
    rw [hfamily]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨W, hW, hx⟩
      refine ⟨⟨W, hW⟩, ?_⟩
      rw [(hpt ⟨W, hW⟩).1] at hx
      exact (Set.mem_singleton_iff.mp hx).symm
    · rintro ⟨W, rfl⟩
      exact ⟨W.val, W.property, by rw [(hpt W).1]; simp⟩
  have hfinite : V.points.Finite := by
    rw [hVpoints]
    exact Set.finite_range pt
  have hcard : (V.points.ncard : ℚ) = F.card := by
    rw [hVpoints, Set.ncard_range_of_injective hptInj]
    simp
  have hdegree : V.degree = (F.card : ℚ) := by
    rw [hdecomp]
    change AffineFamily.degree F = (F.card : ℚ)
    unfold AffineFamily.degree
    calc
      (∑ W ∈ F, W.degree) = ∑ W ∈ F, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro W hW
        exact (hpt ⟨W, hW⟩).2
      _ = F.card := by simp
  exact ⟨hfinite, hcard.trans hdegree.symm⟩

/-- Degree sum of the selected codimension-`c` components, without multiplicities. -/
theorem fa_bezout_components {n c : ℕ} (hc : c ≤ n) (f : Fin c → Poly n)
    (hdegree : ∀ i, 1 ≤ (f i).totalDegree) (F : AffineFamily.Family n)
    (hF : AffineFamily.IsPure F (n-c))
    (hcomponents : ∀ V ∈ F, V.IsComponentOf (Ideal.span (Set.range f))) :
    (∑ V ∈ F, V.degree) ≤ ∏ i, ((f i).totalDegree : ℚ) :=
  components_core n c hc f hdegree F hF hcomponents

/-- Local lengths for a pure family of components of two equations. -/
theorem fa_bezout_refined_two {n : ℕ} (hn : 2 ≤ n) (f : Fin 2 → Poly n)
    (hdegree : ∀ i, 1 ≤ (f i).totalDegree) (F : AffineFamily.Family n)
    (hF : AffineFamily.IsPure F (n-2))
    (hcomponents : ∀ V ∈ F, V.IsComponentOf (Ideal.span (Set.range f))) :
    ∃ m : AffineVariety n → ℕ,
      (∀ V ∈ F, ∀ hV : V.IsIrreducible,
        componentLength (Ideal.span (Set.range f)) V hV = (m V : ℕ∞)) ∧
      (∑ V ∈ F, (m V : ℚ) * V.degree) ≤ ∏ i, ((f i).totalDegree : ℚ) :=
  refined_two_core hn f hdegree F hF hcomponents

/-- `FA.bezout.weighted-cut`, polynomial.tex:49–62,924–935.
Reduced support degree alone does not bound these local quotient lengths. -/
theorem fa_bezout_weighted_cut {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (k : ℕ) (hdim : V.dimension = k+1) (f : Poly n) (hf : f ∉ V.ideal)
    (F : AffineFamily.Family n)
    (hF : ∀ W ∈ F, W.IsComponentOf (V.ideal ⊔ Ideal.span {f})) :
    ∃ m : AffineVariety n → ℕ,
      (∀ W ∈ F, ∀ hW : W.IsIrreducible,
        componentLength (V.ideal ⊔ Ideal.span {f}) W hW = (m W : ℕ∞)) ∧
      (∑ W ∈ F, (m W : ℚ) * W.degree) ≤ (f.totalDegree : ℚ) * V.degree := by
  exact weighted_cut_core V hV k hdim f hf F hF

/-- `FA.bezout.curve-length`, polynomial.tex:924–935. Weighted proper-cut consumer. -/
theorem fa_bezout_curve_length {n : ℕ} (C : AffineVariety n) (hC : C.IsIrreducible)
    (hdim : C.dimension = 1) (f : Poly n) (hf : f ∉ C.ideal) (p : Point n) (hp : p ∈ C.points) :
    ∃ length : ℕ, localLengthAt (C.ideal ⊔ Ideal.span {f}) p = (length : ℕ∞) ∧
      (length : ℚ) ≤ (f.totalDegree : ℚ) * C.degree := by
  classical
  by_cases hfp : MvPolynomial.eval p f = 0
  · let J : Ideal (Poly n) := C.ideal ⊔ Ideal.span {f}
    have hfpoint : f ∈ pointIdeal p := by
      change f ∈ MvPolynomial.vanishingIdeal ℂ ({p} : Set (Point n))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact hfp
    have hJpoint : J ≤ pointIdeal p := by
      apply sup_le
      · intro g hg
        change g ∈ MvPolynomial.vanishingIdeal ℂ ({p} : Set (Point n))
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
        exact hp g hg
      · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfpoint)
    letI : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
    obtain ⟨P, hPmin, hPpoint⟩ := Ideal.exists_minimalPrimes_le hJpoint
    let W : AffineVariety n := ⟨P, hPmin.isPrime.isRadical⟩
    have hWcomp : W.IsComponentOf J := hPmin
    have hWdim : W.dimension = 0 :=
      fa_bezout_proper_dimension C W hC f hf hWcomp 0 hdim
    letI : P.IsPrime := hPmin.isPrime
    have hPdim : OAI.QuarticPowerFree.affineDimension P = 0 := hWdim
    have hPmax : P.IsMaximal := OAI.QuarticPowerFree.zeroDim_isMaximal P hPdim
    have hPeq : P = pointIdeal p := hPmax.eq_of_le (pointIdeal_isMaximal p).ne_top hPpoint
    have hpointmin : pointIdeal p ∈ J.minimalPrimes := by
      rw [← hPeq]
      exact hPmin
    let Vp : AffineVariety n := ⟨pointIdeal p, (pointIdeal_isMaximal p).isPrime.isRadical⟩
    have hVp : Vp.IsIrreducible := (pointIdeal_isMaximal p).isPrime
    have hVpdegree : Vp.degree = 1 := by
      change OAI.QuarticPowerFree.affineDegree (pointIdeal p) = 1
      exact affine_point_degree_one p
    have hVpcomp : Vp.IsComponentOf J := hpointmin
    let F : AffineFamily.Family n := {Vp}
    have hF : ∀ W ∈ F, W.IsComponentOf (C.ideal ⊔ Ideal.span {f}) := by
      intro W hW
      have hW' : W = Vp := Finset.mem_singleton.mp hW
      subst W
      exact hVpcomp
    obtain ⟨m, hm, hbound⟩ := fa_bezout_weighted_cut C hC 0 hdim f hf F hF
    have hlength : localLengthAt J p = (m Vp : ℕ∞) := by
      have hcomponent := hm Vp (Finset.mem_singleton_self Vp) hVp
      change Module.length (Localization.AtPrime (pointIdeal p))
          (Localization.AtPrime (pointIdeal p) ⧸
            (C.ideal ⊔ Ideal.span {f}).map
              (algebraMap (Poly n) (Localization.AtPrime (pointIdeal p)))) = _ at hcomponent
      change Module.length (Localization.AtPrime (pointIdeal p))
          (Localization.AtPrime (pointIdeal p) ⧸
            (C.ideal ⊔ Ideal.span {f}).map
              (algebraMap (Poly n) (Localization.AtPrime (pointIdeal p)))) = _
      exact hcomponent
    have hmbound : (m Vp : ℚ) ≤ (f.totalDegree : ℚ) * C.degree := by
      simpa [F, hVpdegree] using hbound
    exact ⟨m Vp, hlength, hmbound⟩
  · have hfpoint : f ∉ pointIdeal p := by
      intro h
      change f ∈ MvPolynomial.vanishingIdeal ℂ ({p} : Set (Point n)) at h
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at h
      exact hfp h
    let A : Type := PointLocalRing p
    let K : Ideal A := localizedIdeal (C.ideal ⊔ Ideal.span {f}) p
    have hden : f ∈ (pointIdeal p).primeCompl := by
      simpa only [Ideal.mem_primeCompl_iff] using hfpoint
    have hfunit : IsUnit (algebraMap (Poly n) A f) :=
      IsLocalization.map_units A ⟨f, hden⟩
    have hfinK : algebraMap (Poly n) A f ∈ K := by
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    have hKtop : K = ⊤ := K.eq_top_of_isUnit_mem hfinK hfunit
    have hzero : localLengthAt (C.ideal ⊔ Ideal.span {f}) p = 0 := by
      change Module.length A (A ⧸ K) = 0
      rw [hKtop]
      exact Module.length_eq_zero
    have hCdegree : (0 : ℚ) ≤ C.degree :=
      (zero_le_one).trans (C.one_le_degree hC.ne_top)
    refine ⟨0, ?_, ?_⟩
    · simpa using hzero
    · exact mul_nonneg (Nat.cast_nonneg _) hCdegree

/-- `FA.bezout.relative-points`, polynomial.tex:49–62; depth.tex:185–204.
Isolated support points on a carrier are counted without identifying an
arbitrary non-CM local quotient length with intersection multiplicity. -/
theorem fa_bezout_relative_points {n : ℕ} (V : AffineVariety n) (u : ℕ)
    (hV : V.IsPure u) (E : Set (Poly n)) (L : ℕ) (hL : 1 ≤ L)
    (hE : ∀ f ∈ E, f.totalDegree ≤ L) (S : Finset (Point n))
    (hS : ∀ x ∈ S, pointIdeal x ∈ (V.ideal ⊔ Ideal.span E).minimalPrimes) :
    (S.card : ℚ) ≤ V.degree * (L : ℚ)^u := by
  exact relative_pure_point_bound V hV E L hL hE S hS

/-- `FA.bezout.plane-local-orders`, polynomial.tex:973–981; secants.tex:440–485. -/
theorem fa_bezout_plane_local_orders (f g : Poly 2) (p : Point 2) (r s : ℕ)
    (hf : OrderAtLeast f p r) (hg : OrderAtLeast g p s) :
    ((r*s : ℕ) : ℕ∞) ≤ localLengthAt (Ideal.span {f, g}) p := by
  by_cases hr0 : r = 0
  · subst r
    simp
  by_cases hs0 : s = 0
  · subst s
    simp
  let R := PointLocalRing p
  let m := IsLocalRing.maximalIdeal R
  let fR := algebraMap (Poly 2) R f
  let gR := algebraMap (Poly 2) R g
  have hf' : fR ∈ m^r := by
    dsimp [m, fR]
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal p) R,
      ← Ideal.map_pow (algebraMap (Poly 2) R) (pointIdeal p) r]
    exact Ideal.mem_map_of_mem _ (show f ∈ pointIdeal p^r from hf)
  have hg' : gR ∈ m^s := by
    dsimp [m, gR]
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal p) R,
      ← Ideal.map_pow (algebraMap (Poly 2) R) (pointIdeal p) s]
    exact Ideal.mem_map_of_mem _ (show g ∈ pointIdeal p^s from hg)
  have hcut := length_two_order_cut_bound R m fR gR r s (by omega) (by omega) hf' hg'
  have hlocal : localLengthAt (Ideal.span {f,g}) p =
      Module.length R (R ⧸ Ideal.span {fR,gR}) := by
    unfold localLengthAt localizedIdeal
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  rw [plane_point_power_length p, plane_point_power_length p,
    plane_point_power_length p, ← hlocal] at hcut
  rw [show r+s-1+1 = r+s by omega, show s-1+1 = s by omega,
    show r-1+1 = r by omega] at hcut
  by_cases htop : localLengthAt (Ideal.span {f,g}) p = ⊤
  · rw [htop]
    exact le_top
  lift localLengthAt (Ideal.span {f,g}) p to ℕ using htop with L hL
  have hcutQ : ((r+s).choose 2 : ℚ) ≤ (s.choose 2 : ℚ)+(r.choose 2 : ℚ)+(L : ℚ) := by
    exact_mod_cast hcut
  have hchoose : ((r+s).choose 2 : ℚ) =
      (s.choose 2 : ℚ)+(r.choose 2 : ℚ)+(r : ℚ)*(s : ℚ) := by
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    ring
  have hbound : (r : ℚ)*(s : ℚ) ≤ (L : ℚ) := by
    rw [hchoose] at hcutQ
    linarith
  exact_mod_cast hbound

/-- `poly:separators.physical`, polynomial.tex:66–72. Reuses the OAI separator. -/
theorem poly_separators_physical {n : ℕ} (P : Finset (EuclideanSpace ℝ (Fin n))) :
    ∀ p ∈ P, ∃ s : Poly n, s.totalDegree ≤ 2 * (OAI.ErdosDistinctDistances.distances P).card ∧
      MvPolynomial.eval (OAI.ErdosDistinctDistances.complexPoint p) s = 1 ∧
      ∀ q ∈ P, q ≠ p → MvPolynomial.eval (OAI.ErdosDistinctDistances.complexPoint q) s = 0 := by
  classical
  intro p hp
  refine ⟨OAI.ErdosDistinctDistances.physicalSeparator P p, ?_, ?_, ?_⟩
  · exact OAI.ErdosDistinctDistances.degree_physicalSeparator P p
  · exact OAI.ErdosDistinctDistances.eval_physicalSeparator_self P p
  · intro q hq hpq
    exact OAI.ErdosDistinctDistances.eval_physicalSeparator_ne hp hq hpq.symm

private noncomputable def componentFamily {n : ℕ} (V : AffineVariety n) :
    AffineFamily.Family n := by
  classical
  exact Finset.univ.image (fun c : V.Component => c.variety)

private theorem componentFamily_injective {n : ℕ} (V : AffineVariety n) :
    Function.Injective (fun c : V.Component => c.variety) := by
  intro c₁ c₂ h
  apply Subtype.ext
  exact congrArg AffineVariety.ideal h

private theorem componentFamily_pure {n u : ℕ} (V : AffineVariety n)
    (hV : V.IsPure u) : AffineFamily.IsPure (componentFamily V) u := by
  classical
  intro W hW
  rcases Finset.mem_image.mp hW with ⟨c, -, rfl⟩
  exact ⟨AffineVariety.Component.irreducible c, hV c⟩

private theorem componentFamily_locus {n : ℕ} (V : AffineVariety n) :
    V = AffineFamily.locus (componentFamily V) := by
  apply (AffineVariety.points_eq_iff _ _).mp
  rw [AffineVariety.points_components, AffineFamily.points_locus]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨c, hx⟩
    refine ⟨c.variety, ?_, hx⟩
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
  · rintro ⟨W, hW, hx⟩
    rcases Finset.mem_image.mp hW with ⟨c, -, rfl⟩
    exact ⟨c, hx⟩

private theorem componentFamily_degree {n u : ℕ} (V : AffineVariety n)
    (hV : V.IsPure u) : V.degree = AffineFamily.degree (componentFamily V) := by
  calc
    V.degree = (AffineFamily.locus (componentFamily V)).degree :=
      congrArg (fun X : AffineVariety n => X.degree) (componentFamily_locus V)
    _ = AffineFamily.degree (componentFamily V) :=
      AffineFamily.degree_locus _ _ (componentFamily_pure V hV)

private theorem affineVariety_dimension_le {n : ℕ} (V : AffineVariety n) :
    V.dimension ≤ n := by
  change V.hilbertPolynomial.natDegree ≤ n
  obtain ⟨Q, hQ, N, hQevent⟩ :=
    OAI.QuarticPowerFree.coordinate_hilbert_eventually_polynomial V.ideal
  have hevent : ∀ᶠ T : ℕ in Filter.atTop,
      Q.eval (T : ℚ) = V.hilbertPolynomial.eval (T : ℚ) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, hQevent⟩,
      OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal] with T hQT hVQ
    exact hQT.symm.trans hVQ
  have hEq : Q = V.hilbertPolynomial :=
    OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq Q _ hevent
  rw [← hEq]
  exact hQ

private theorem sample_filter_card_le_family_sum {n : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin n))) (V : AffineVariety n)
    (F : AffineFamily.Family n) (hpoints : V.points = ⋃ W ∈ F, W.points) :
    (P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V)).card ≤
      ∑ W ∈ F,
        (P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ W)).card := by
  classical
  let S := P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V)
  let T : AffineVariety n → Finset (EuclideanSpace ℝ (Fin n)) := fun W =>
    P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ W)
  have hsubset : S ⊆ F.biUnion T := by
    intro p hp
    change p ∈ P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V) at hp
    have hpV := (Finset.mem_filter.mp hp).2
    change OAI.ErdosDistinctDistances.complexPoint p ∈ V.points at hpV
    have hpU : OAI.ErdosDistinctDistances.complexPoint p ∈ ⋃ W ∈ F, W.points := by
      rw [hpoints] at hpV
      exact hpV
    rcases Set.mem_iUnion₂.mp hpU with ⟨W, hW, hpW⟩
    exact Finset.mem_biUnion.mpr ⟨W, hW, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp).1, hpW⟩⟩
  calc
    S.card ≤ (F.biUnion T).card := Finset.card_le_card hsubset
    _ ≤ ∑ W ∈ F, (T W).card := Finset.card_biUnion_le

private theorem irreducible_affineVariety_isPure {n u : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hdim : V.dimension = u) : V.IsPure u := by
  intro c
  letI : V.ideal.IsPrime := hV
  have hc : c.val = V.ideal := by
    simpa only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] using
      c.property
  have hvar : c.variety = V := by
    apply AffineVariety.ext
    exact hc
  simpa [hvar] using hdim

private theorem sample_bound_by_dimension (n u : ℕ) :
    ∀ (P : Finset (EuclideanSpace ℝ (Fin n))) (V : AffineVariety n), V.IsPure u →
      ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V)).card : ℚ) ≤
        (3 : ℚ)^u * V.degree *
          (1 + (OAI.ErdosDistinctDistances.distances P).card : ℚ)^u := by
  induction u with
  | zero =>
      intro P V hV
      classical
      let S := P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V)
      obtain ⟨hfinite, hzero⟩ := fa_bezout_zero_dimensional V hV
      have hcp : Function.Injective (OAI.ErdosDistinctDistances.complexPoint :
          EuclideanSpace ℝ (Fin n) → Point n) := by
        intro p q hpq
        ext i
        exact Complex.ofReal_injective (congrFun hpq i)
      have hsubset :
          OAI.ErdosDistinctDistances.complexPoint '' (S : Set (EuclideanSpace ℝ (Fin n))) ⊆
            V.points := by
        intro z hz
        rcases (Set.mem_image _ _ _).mp hz with ⟨p, hp, rfl⟩
        exact (Finset.mem_filter.mp hp).2
      have hImage :
          (OAI.ErdosDistinctDistances.complexPoint ''
            (S : Set (EuclideanSpace ℝ (Fin n)))).ncard = S.card := by
        rw [Set.ncard_image_of_injective (S : Set (EuclideanSpace ℝ (Fin n))) hcp,
          Set.ncard_coe_finset]
      have hcard : S.card ≤ V.points.ncard := by
        calc
          S.card = (OAI.ErdosDistinctDistances.complexPoint ''
              (S : Set (EuclideanSpace ℝ (Fin n)))).ncard := hImage.symm
          _ ≤ V.points.ncard := Set.ncard_le_ncard hsubset hfinite
      have hcardQ : (S.card : ℚ) ≤ V.degree := by
        have hq : (S.card : ℚ) ≤ (V.points.ncard : ℚ) := by exact_mod_cast hcard
        rw [hzero] at hq
        exact hq
      simpa [S] using hcardQ
  | succ k ih =>
      have hirred : ∀ (P : Finset (EuclideanSpace ℝ (Fin n))) (V : AffineVariety n),
          V.IsIrreducible → V.dimension = k+1 →
          ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V)).card : ℚ) ≤
            (3 : ℚ)^(k+1) * V.degree *
              (1 + (OAI.ErdosDistinctDistances.distances P).card : ℚ)^(k+1) := by
        intro P V hV hdim
        classical
        let S := P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V)
        by_cases hSempty : S = ∅
        · have hdeg1 : 1 ≤ V.degree := AffineVariety.one_le_degree V hV.ne_top
          have hdeg : 0 ≤ V.degree := (by norm_num : (0 : ℚ) ≤ 1).trans hdeg1
          have hnonneg :
              0 ≤ (3 : ℚ)^(k+1) * V.degree *
                (1 + (OAI.ErdosDistinctDistances.distances P).card : ℚ)^(k+1) := by
            positivity
          simpa [S, hSempty] using hnonneg
        · obtain ⟨p, hpS⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
          have hpP : p ∈ P := (Finset.mem_filter.mp hpS).1
          have hpV : OAI.ErdosDistinctDistances.complexPoint p ∈ V.points :=
            (Finset.mem_filter.mp hpS).2
          obtain ⟨s, hsdeg, hsone, hszero⟩ := poly_separators_physical P p hpP
          have hsnot : s ∉ V.ideal := by
            intro hsI
            have hz := (MvPolynomial.mem_zeroLocus_iff.mp hpV) s hsI
            rw [MvPolynomial.aeval_eq_eval, hsone] at hz
            exact one_ne_zero hz
          let Wfam := componentFamily (AffineVariety.cut V s)
          have hWcomp : ∀ W ∈ Wfam,
              W.IsComponentOf (V.ideal ⊔ Ideal.span {s}) := by
            intro W hW
            rcases Finset.mem_image.mp hW with ⟨c, -, rfl⟩
            change c.val ∈ (V.ideal ⊔ Ideal.span {s}).minimalPrimes
            simpa [AffineVariety.cut, AffineVariety.ofIdeal] using c.property
          have hWdim : ∀ W ∈ Wfam, W.dimension = k := by
            intro W hW
            exact fa_bezout_proper_dimension V W hV s hsnot (hWcomp W hW) k hdim
          have hWpure : AffineFamily.IsPure Wfam k := by
            intro W hW
            rcases Finset.mem_image.mp hW with ⟨c, -, rfl⟩
            exact ⟨AffineVariety.Component.irreducible c, hWdim _ hW⟩
          have hcutPure : (AffineVariety.cut V s).IsPure k := by
            intro c
            have hc : c.variety ∈ Wfam :=
              Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
            exact hWdim c.variety hc
          have hWdegree : AffineFamily.degree Wfam ≤ (s.totalDegree : ℚ) * V.degree :=
            fa_bezout_proper_degree V hV s hsnot Wfam hWcomp k hdim
          have hcutDegree : (AffineVariety.cut V s).degree ≤
              (s.totalDegree : ℚ) * V.degree := by
            calc
              (AffineVariety.cut V s).degree = AffineFamily.degree Wfam :=
                componentFamily_degree _ hcutPure
              _ ≤ (s.totalDegree : ℚ) * V.degree := hWdegree
          let T := P.filter
            (fun q => OAI.ErdosDistinctDistances.complexPoint q ∈ AffineVariety.cut V s)
          have hsubset : S ⊆ insert p T := by
            intro q hq
            by_cases hqp : q = p
            · subst q
              exact Finset.mem_insert_self p T
            · apply Finset.mem_insert.mpr
              right
              refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1, ?_⟩
              have hqV : OAI.ErdosDistinctDistances.complexPoint q ∈ V.points :=
                (Finset.mem_filter.mp hq).2
              have hqsep := hszero q (Finset.mem_filter.mp hq).1 hqp
              have hspan : Ideal.span {s} ≤
                  MvPolynomial.vanishingIdeal ℂ
                    {OAI.ErdosDistinctDistances.complexPoint q} := by
                apply Ideal.span_le.mpr
                intro f hf
                rcases Set.mem_singleton_iff.mp hf with rfl
                change f ∈ MvPolynomial.vanishingIdeal ℂ
                  ({OAI.ErdosDistinctDistances.complexPoint q} : Set (Point n))
                rw [MvPolynomial.mem_vanishingIdeal_iff]
                intro z hz
                have hzq : z = OAI.ErdosDistinctDistances.complexPoint q :=
                  Set.mem_singleton_iff.mp hz
                subst z
                simpa only [MvPolynomial.aeval_eq_eval] using hqsep
              have hqvan : OAI.ErdosDistinctDistances.complexPoint q ∈
                  MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ
                    {OAI.ErdosDistinctDistances.complexPoint q}) := by
                exact MvPolynomial.zeroLocus_vanishingIdeal_le
                  (V := {OAI.ErdosDistinctDistances.complexPoint q}) (by simp)
              have hqspan : OAI.ErdosDistinctDistances.complexPoint q ∈
                  MvPolynomial.zeroLocus ℂ (Ideal.span {s}) :=
                MvPolynomial.zeroLocus_anti_mono hspan hqvan
              have hqzero : OAI.ErdosDistinctDistances.complexPoint q ∈
                  MvPolynomial.zeroLocus ℂ (V.ideal ⊔ Ideal.span {s}) := by
                rw [MvPolynomial.mem_zeroLocus_iff]
                intro f hf
                rcases Submodule.mem_sup.mp hf with ⟨a, ha, b, hb, hab⟩
                rw [← hab, map_add]
                have h₁ := (MvPolynomial.mem_zeroLocus_iff.mp hqV) a ha
                have h₂ := (MvPolynomial.mem_zeroLocus_iff.mp hqspan) b hb
                simp [h₁, h₂]
              have hqcut : OAI.ErdosDistinctDistances.complexPoint q ∈
                  AffineVariety.cut V s := by
                change OAI.ErdosDistinctDistances.complexPoint q ∈
                  (AffineVariety.ofIdeal (V.ideal ⊔ Ideal.span {s})).points
                rw [AffineVariety.points_ofIdeal]
                exact hqzero
              exact hqcut
          have hcard : S.card ≤ T.card + 1 := by
            calc
              S.card ≤ (insert p T).card := Finset.card_le_card hsubset
              _ ≤ T.card + 1 := Finset.card_insert_le p T
          have hT : (T.card : ℚ) ≤ (3 : ℚ)^k *
              (AffineVariety.cut V s).degree *
                (1 + (OAI.ErdosDistinctDistances.distances P).card : ℚ)^k := by
            simpa [T] using ih P (AffineVariety.cut V s) hcutPure
          let M : ℚ := 1 + (OAI.ErdosDistinctDistances.distances P).card
          have hM : 1 ≤ M := by
            dsimp [M]
            exact le_add_of_nonneg_right (Nat.cast_nonneg _)
          have hdeg1 : 1 ≤ V.degree := AffineVariety.one_le_degree V hV.ne_top
          have hsdegQ : (s.totalDegree : ℚ) ≤ 2 * M := by
            have h : (s.totalDegree : ℚ) ≤
                2 * (OAI.ErdosDistinctDistances.distances P).card := by exact_mod_cast hsdeg
            dsimp [M]
            nlinarith
          have hunit : 1 ≤ (3 : ℚ)^k * V.degree * M^(k+1) := by
            have h₃ : (1 : ℚ) ≤ (3 : ℚ)^k := one_le_pow₀ (by norm_num)
            have hMpow : (1 : ℚ) ≤ M^(k+1) := one_le_pow₀ hM
            calc
              1 = 1 * 1 * 1 := by ring
              _ ≤ (3 : ℚ)^k * V.degree * M^(k+1) := by gcongr
          have hcutScaled :
              (3 : ℚ)^k * (AffineVariety.cut V s).degree * M^k ≤
                (3 : ℚ)^k * ((s.totalDegree : ℚ) * V.degree) * M^k := by
            have h₁ := mul_le_mul_of_nonneg_left hcutDegree (by positivity :
              0 ≤ (3 : ℚ)^k)
            have h₂ := mul_le_mul_of_nonneg_right h₁ (by positivity : 0 ≤ M^k)
            simpa [mul_assoc] using h₂
          have hsepScaled :
              (3 : ℚ)^k * ((s.totalDegree : ℚ) * V.degree) * M^k ≤
                (3 : ℚ)^k * ((2 * M) * V.degree) * M^k := by
            have h₁ := mul_le_mul_of_nonneg_right hsdegQ (by positivity : 0 ≤ V.degree)
            have h₂ := mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ (3 : ℚ)^k)
            have h₃ := mul_le_mul_of_nonneg_right h₂ (by positivity : 0 ≤ M^k)
            simpa [mul_assoc] using h₃
          have hrec :
              1 + (3 : ℚ)^k * (AffineVariety.cut V s).degree * M^k ≤
                (3 : ℚ)^(k+1) * V.degree * M^(k+1) := by
            calc
              _ ≤ 1 + (3 : ℚ)^k * ((s.totalDegree : ℚ) * V.degree) * M^k :=
                by simpa [add_comm] using add_le_add_left hcutScaled 1
              _ ≤ 1 + (3 : ℚ)^k * ((2 * M) * V.degree) * M^k :=
                by simpa [add_comm] using add_le_add_left hsepScaled 1
              _ = 1 + 2 * ((3 : ℚ)^k * V.degree * M^(k+1)) := by
                rw [pow_succ]
                ring
              _ ≤ 3 * ((3 : ℚ)^k * V.degree * M^(k+1)) := by linarith
              _ = (3 : ℚ)^(k+1) * V.degree * M^(k+1) := by
                rw [pow_succ]
                ring
          have hcardQ : (S.card : ℚ) ≤
              1 + (3 : ℚ)^k * (AffineVariety.cut V s).degree * M^k := by
            have hcast : (S.card : ℚ) ≤ (T.card : ℚ) + 1 := by exact_mod_cast hcard
            exact hcast.trans (by simpa [add_comm] using add_le_add_left hT 1)
          have hfinal := hcardQ.trans hrec
          simpa [S, M] using hfinal
      intro P V hV
      classical
      let F := componentFamily V
      have hF : AffineFamily.IsPure F (k+1) := componentFamily_pure V hV
      have hdeg : V.degree = AffineFamily.degree F := componentFamily_degree V hV
      have hpoints : V.points = ⋃ W ∈ F, W.points := by
        rw [componentFamily_locus V]
        exact AffineFamily.points_locus F
      have hcount := sample_filter_card_le_family_sum P V F hpoints
      let M : ℚ := 1 + (OAI.ErdosDistinctDistances.distances P).card
      have hcounts : ∀ W ∈ F,
          ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ W)).card : ℚ) ≤
            (3 : ℚ)^(k+1) * W.degree * M^(k+1) := by
        intro W hW
        have hWdata := hF W hW
        exact hirred P W hWdata.1 hWdata.2
      have hsum :
          ∑ W ∈ F,
            ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ W)).card : ℚ) ≤
          ∑ W ∈ F, (3 : ℚ)^(k+1) * W.degree * M^(k+1) :=
        Finset.sum_le_sum fun W hW => hcounts W hW
      have hsumEq :
          ∑ W ∈ F, (3 : ℚ)^(k+1) * W.degree * M^(k+1) =
            (3 : ℚ)^(k+1) * AffineFamily.degree F * M^(k+1) := by
        calc
          _ = ∑ W ∈ F, ((3 : ℚ)^(k+1) * M^(k+1)) * W.degree := by
            apply Finset.sum_congr rfl
            intro W hW
            ring
          _ = ((3 : ℚ)^(k+1) * M^(k+1)) *
              (∑ W ∈ F, W.degree) := by rw [← Finset.mul_sum]
          _ = (3 : ℚ)^(k+1) * AffineFamily.degree F * M^(k+1) := by
            simp only [AffineFamily.degree]
            ring
      have hcountQ :
          ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V)).card : ℚ) ≤
            ∑ W ∈ F,
              ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ W)).card : ℚ) :=
        by exact_mod_cast hcount
      calc
        _ ≤ _ := hcountQ
        _ ≤ _ := hsum
        _ = (3 : ℚ)^(k+1) * V.degree * M^(k+1) := by rw [hsumEq, ← hdeg]

/-- `poly:separators.sample-bound`, polynomial.tex:73–101; secants.tex:246–250. -/
theorem poly_separators_sample_bound (n : ℕ) :
    ∃ C : ℚ, 0 < C ∧ ∀ (P : Finset (EuclideanSpace ℝ (Fin n)))
      (V : AffineVariety n) (u : ℕ), V.IsPure u →
      ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V)).card : ℚ) ≤
        C * V.degree * (1 + (OAI.ErdosDistinctDistances.distances P).card : ℚ)^u := by
  classical
  refine ⟨(3 : ℚ)^n, by positivity, ?_⟩
  intro P V u hV
  let F := componentFamily V
  have hF : AffineFamily.IsPure F u := componentFamily_pure V hV
  have hdegree : V.degree = AffineFamily.degree F := componentFamily_degree V hV
  have hpoints : V.points = ⋃ W ∈ F, W.points := by
    rw [componentFamily_locus V]
    exact AffineFamily.points_locus F
  by_cases hFnonempty : F.Nonempty
  · obtain ⟨W, hW⟩ := hFnonempty
    have hWdata := hF W hW
    have hu : u ≤ n := hWdata.2.symm.trans_le (affineVariety_dimension_le W)
    let M : ℚ := 1 + (OAI.ErdosDistinctDistances.distances P).card
    have hbound := sample_bound_by_dimension n u P V hV
    have hboundM :
        ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V)).card : ℚ) ≤
          (3 : ℚ)^u * V.degree * M^u := by simpa [M] using hbound
    have hdegreeNonneg : 0 ≤ V.degree := by
      rw [hdegree, AffineFamily.degree]
      apply Finset.sum_nonneg
      intro W hW
      exact le_trans (by norm_num)
        (AffineVariety.one_le_degree W (hF W hW).1.ne_top)
    have hpow : (3 : ℚ)^u ≤ (3 : ℚ)^n := pow_le_pow_right₀ (by norm_num) hu
    have hscale :
        (3 : ℚ)^u * V.degree * M^u ≤ (3 : ℚ)^n * V.degree * M^u := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow hdegreeNonneg) (by positivity)
    calc
      _ ≤ (3 : ℚ)^u * V.degree * M^u := hboundM
      _ ≤ (3 : ℚ)^n * V.degree * M^u := hscale
      _ = (3 : ℚ)^n * V.degree *
          (1 + (OAI.ErdosDistinctDistances.distances P).card : ℚ)^u := by rfl
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hFnonempty
    have hVempty : V.points = ∅ := by
      rw [hpoints]
      simp [hFempty]
    have hSempty :
        P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ V) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hpV := (Finset.mem_filter.mp hp).2
      change OAI.ErdosDistinctDistances.complexPoint p ∈ V.points at hpV
      simp [hVempty] at hpV
    have hdegreeZero : V.degree = 0 := by
      rw [hdegree, AffineFamily.degree, hFempty]
      simp
    simp [hSempty, hdegreeZero]

/-- `poly:separators.isolation`, polynomial.tex:77–80,103–113. Direct OAI wrapper. -/
theorem poly_separators_isolation {n : ℕ} (P : Finset (EuclideanSpace ℝ (Fin n))) :
    ∃ E : Finset (Poly n),
      (∀ f ∈ E, f.totalDegree ≤ 2 * (1 + (OAI.ErdosDistinctDistances.distances P).card) + 1) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span (E : Set (Poly n))) =
        OAI.ErdosDistinctDistances.complexPoint '' (P : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  refine ⟨OAI.ErdosDistinctDistances.isolationPolynomials P, ?_, ?_⟩
  · intro f hf
    have h := OAI.ErdosDistinctDistances.degree_isolationPolynomials
      (f := f) (by simpa using hf)
    omega
  · ext z
    rw [MvPolynomial.zeroLocus_span]
    simpa only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe,
      MvPolynomial.aeval_eq_eval] using
      (OAI.ErdosDistinctDistances.isolation_zero_iff P z)

end
end DistinctDistances.TrackA
