import DistinctDistances.OAIInterface.DegreeBudgets

/-!
Reduced affine varieties over `ℂ`. Ambient points are coordinate functions,
not the Euclidean metric space used in `Challenge.lean`. Dimension and degree
are OAI's filtered Hilbert invariants; degree is rational-valued. Empty
varieties have the convention `dimension = 0`, so dimension statements that
require nonemptiness must carry it explicitly.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

abbrev Point (n : ℕ) := Fin n → ℂ
abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℂ

structure AffineVariety (n : ℕ) where
  ideal : Ideal (Poly n)
  isRadical : ideal.IsRadical

namespace AffineVariety

variable {n : ℕ}

@[ext] theorem ext {V W : AffineVariety n} (h : V.ideal = W.ideal) : V = W := by
  cases V
  cases W
  cases h
  rfl

def points (V : AffineVariety n) : Set (Point n) := MvPolynomial.zeroLocus ℂ V.ideal

instance : Membership (Point n) (AffineVariety n) := ⟨fun V x => x ∈ V.points⟩

/-- Reduced zero locus of a possibly nonradical defining ideal. -/
def ofIdeal (I : Ideal (Poly n)) : AffineVariety n := ⟨I.radical, I.radical_isRadical⟩

theorem vanishingIdeal_isRadical (T : Set (Point n)) :
    (MvPolynomial.vanishingIdeal ℂ T).IsRadical := by
  intro f hf x hx
  obtain ⟨r, hr⟩ := Ideal.mem_radical_iff.mp hf
  have hz : (MvPolynomial.aeval x f) ^ r = 0 := by
    simpa using hr x hx
  exact eq_zero_of_pow_eq_zero hz

/-- Zariski closure of an arbitrary set of complex points. -/
def closure (T : Set (Point n)) : AffineVariety n :=
  ⟨MvPolynomial.vanishingIdeal ℂ T, vanishingIdeal_isRadical T⟩

def empty : AffineVariety n := ofIdeal ⊤
def whole : AffineVariety n := ofIdeal ⊥

def IsIrreducible (V : AffineVariety n) : Prop := V.ideal.IsPrime

/-- Irreducible *component* of the equations, not just an irreducible subvariety. -/
def IsComponentOf (V : AffineVariety n) (I : Ideal (Poly n)) : Prop :=
  V.ideal ∈ I.minimalPrimes

abbrev Component (V : AffineVariety n) := {P : Ideal (Poly n) // P ∈ V.ideal.minimalPrimes}

def Component.variety {V : AffineVariety n} (W : V.Component) : AffineVariety n :=
  ⟨W.val, W.property.isPrime.isRadical⟩

theorem Component.irreducible {V : AffineVariety n} (W : V.Component) :
    W.variety.IsIrreducible := W.property.isPrime

noncomputable instance componentFinite (V : AffineVariety n) : Fintype V.Component :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n) V.ideal).fintype

/-- Direct reuse of OAI's affine Hilbert polynomial. -/
noncomputable abbrev hilbertPolynomial (V : AffineVariety n) : Polynomial ℚ :=
  OAI.QuarticPowerFree.coordinateHilbert V.ideal

noncomputable abbrev dimension (V : AffineVariety n) : ℕ :=
  OAI.QuarticPowerFree.affineDimension V.ideal

noncomputable abbrev degree (V : AffineVariety n) : ℚ :=
  OAI.QuarticPowerFree.affineDegree V.ideal

noncomputable abbrev restrictionSpace (V : AffineVariety n) (D : ℕ) :
    Submodule ℂ (Poly n ⧸ V.ideal) :=
  (OAI.QuarticPowerFree.totalSpace D).map (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap

instance restrictionSpace_finite (V : AffineVariety n) (D : ℕ) :
    Module.Finite ℂ (V.restrictionSpace D) := by
  letI := OAI.QuarticPowerFree.totalSpace_finite (n := n) (K := ℂ) D
  infer_instance

noncomputable def hilbert (V : AffineVariety n) (D : ℕ) : ℕ :=
  Module.finrank ℂ (V.restrictionSpace D)

def IsPure (V : AffineVariety n) (k : ℕ) : Prop :=
  ∀ W : V.Component, W.variety.dimension = k

def Subvariety (V W : AffineVariety n) : Prop := W.ideal ≤ V.ideal

def intersection (V W : AffineVariety n) : AffineVariety n := ofIdeal (V.ideal ⊔ W.ideal)

def union (V W : AffineVariety n) : AffineVariety n :=
  ⟨V.ideal ⊓ W.ideal, V.isRadical.inf W.isRadical⟩

def cut (V : AffineVariety n) (f : Poly n) : AffineVariety n :=
  ofIdeal (V.ideal ⊔ Ideal.span {f})

/-- The whole reduced locus is defined in degree `L`. -/
def DefinedInDegree (V : AffineVariety n) (L : ℕ) : Prop :=
  ∃ E : Set (Poly n), (∀ f ∈ E, f.totalDegree ≤ L) ∧
    (Ideal.span E).radical = V.ideal

@[simp] theorem vanishingIdeal_points (V : AffineVariety n) :
    MvPolynomial.vanishingIdeal ℂ V.points = V.ideal := by
  exact (MvPolynomial.vanishingIdeal_zeroLocus_eq_radical V.ideal).trans V.isRadical.radical

@[simp] theorem points_ofIdeal (I : Ideal (Poly n)) :
    (ofIdeal I).points = MvPolynomial.zeroLocus ℂ I := by
  apply le_antisymm
  · exact MvPolynomial.zeroLocus_anti_mono Ideal.le_radical
  · intro x hx f hf
    exact MvPolynomial.radical_le_vanishingIdeal_zeroLocus I hf x hx

theorem subset_closure (T : Set (Point n)) : T ⊆ (closure T).points :=
  MvPolynomial.zeroLocus_vanishingIdeal_le T

theorem subvariety_iff_points_subset (V W : AffineVariety n) :
    V.Subvariety W ↔ V.points ⊆ W.points := by
  constructor
  · exact MvPolynomial.zeroLocus_anti_mono
  · intro h
    have hi := MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) h
    simpa only [vanishingIdeal_points, Subvariety] using hi

theorem points_eq_iff (V W : AffineVariety n) : V.points = W.points ↔ V = W := by
  constructor
  · intro h
    apply ext
    simpa only [vanishingIdeal_points] using congrArg (MvPolynomial.vanishingIdeal ℂ) h
  · rintro rfl
    rfl

theorem points_components (V : AffineVariety n) :
    V.points = ⋃ W : V.Component, W.variety.points := by
  ext x
  constructor
  · intro hx
    have hle : V.ideal ≤ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n)) := by
      intro f hf
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).2 (hx f hf)
    obtain ⟨P, hP, hPx⟩ := Ideal.exists_minimalPrimes_le hle
    refine Set.mem_iUnion.mpr ⟨⟨P, hP⟩, ?_⟩
    change x ∈ MvPolynomial.zeroLocus ℂ P
    intro f hf
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).1 (hPx hf)
  · intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨W, hxW⟩ := hx
    change x ∈ MvPolynomial.zeroLocus ℂ W.val at hxW
    change x ∈ MvPolynomial.zeroLocus ℂ V.ideal
    have hrad : sInf V.ideal.minimalPrimes = V.ideal := by
      rw [Ideal.sInf_minimalPrimes, V.isRadical.radical]
    have hle : V.ideal ≤ W.val := by
      calc
        V.ideal = sInf V.ideal.minimalPrimes := hrad.symm
        _ ≤ W.val := sInf_le W.property
    intro f hf
    exact hxW f (hle hf)

theorem hilbert_eventually (V : AffineVariety n) :
    ∀ᶠ D : ℕ in Filter.atTop, (V.hilbert D : ℚ) = V.hilbertPolynomial.eval (D : ℚ) :=
  OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal

theorem one_le_degree (V : AffineVariety n) (hV : V.ideal ≠ ⊤) : 1 ≤ V.degree :=
  OAI.QuarticPowerFree.one_le_affineDegree V.ideal hV

theorem points_nonempty_of_isIrreducible (V : AffineVariety n)
    (hV : V.IsIrreducible) : V.points.Nonempty := by
  by_contra h
  have hEmpty : V.points = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have htop : V.ideal = ⊤ := by
    rw [← V.vanishingIdeal_points, hEmpty, MvPolynomial.vanishingIdeal_empty]
  exact hV.ne_top htop

theorem hilbert_mono (V W : AffineVariety n) (h : V.Subvariety W) (D : ℕ) :
    V.hilbert D ≤ W.hilbert D :=
  OAI.QuarticPowerFree.quotient_hilbert_le W.ideal V.ideal h D

end AffineVariety

/-- Polynomial restriction rank for arbitrary point sets (paper §3's `H_T`). -/
noncomputable def hilbertOfSet {n : ℕ} (T : Set (Point n)) (D : ℕ) : ℕ :=
  (AffineVariety.closure T).hilbert D

/-- Degree-`D` envelope, as the reduced locus of the bounded-degree equations. -/
def envelope {n : ℕ} (T : Set (Point n)) (D : ℕ) : AffineVariety n :=
  AffineVariety.ofIdeal (Ideal.span {f : Poly n |
    f ∈ MvPolynomial.vanishingIdeal ℂ T ∧ f.totalDegree ≤ D})

/-- polynomial.tex:26–34; a rank identity at the *same* degree. -/
theorem envelope_hilbert {n : ℕ} (T : Set (Point n)) (D : ℕ) :
    (envelope T D).hilbert D = hilbertOfSet T D := by
  classical
  let W := envelope T D
  let V := AffineVariety.closure T
  let I := MvPolynomial.vanishingIdeal ℂ T
  have hgen : Ideal.span {f : Poly n | f ∈ I ∧ f.totalDegree ≤ D} ≤ I :=
    Ideal.span_le.mpr fun _ hf => hf.1
  have hIrad : I.IsRadical := AffineVariety.vanishingIdeal_isRadical T
  have hle : W.ideal ≤ V.ideal := by
    change (Ideal.span {f : Poly n | f ∈ I ∧ f.totalDegree ≤ D}).radical ≤ I
    exact hIrad.radical_le_iff.mpr hgen
  let φ : (Poly n ⧸ W.ideal) →ₗ[ℂ] (Poly n ⧸ V.ideal) :=
    (Ideal.Quotient.factorₐ ℂ hle).toLinearMap
  have hφ_mk (p : Poly n) :
      φ ((Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap p) =
        (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap p := by
    simp [φ]
  let e : W.restrictionSpace D →ₗ[ℂ] V.restrictionSpace D :=
    { toFun := fun x => ⟨φ x.val, by
        rcases x.property with ⟨p, hp, hpx⟩
        refine ⟨p, hp, ?_⟩
        calc
          (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap p =
              φ ((Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap p) := (hφ_mk p).symm
          _ = φ x.val := congrArg φ hpx
      ⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact φ.map_add x.val y.val
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact φ.map_smul c x.val }
  have hzero : ∀ x : W.restrictionSpace D, e x = 0 → x = 0 := by
    intro x hx
    rcases x.property with ⟨p, hp, hpx⟩
    have hφzero : φ x.val = 0 := by
      simpa [e] using congrArg Subtype.val hx
    have hpzero : (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap p = 0 := by
      calc
        (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap p =
            φ ((Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap p) := (hφ_mk p).symm
        _ = φ x.val := congrArg φ hpx
        _ = 0 := hφzero
    have hpV : p ∈ V.ideal := Ideal.Quotient.eq_zero_iff_mem.mp hpzero
    have hpT : p ∈ I := by simpa [V, AffineVariety.closure, I] using hpV
    have hpdeg : p.totalDegree ≤ D := OAI.QuarticPowerFree.mem_totalSpace.mp hp
    have hpgen : p ∈ {f : Poly n | f ∈ I ∧ f.totalDegree ≤ D} := ⟨hpT, hpdeg⟩
    have hpW : p ∈ W.ideal := by
      change p ∈ (Ideal.span {f : Poly n | f ∈ I ∧ f.totalDegree ≤ D}).radical
      exact Ideal.le_radical (Ideal.subset_span hpgen)
    apply Subtype.ext
    calc
      x.val = (Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap p := hpx.symm
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpW
  have hinj : Function.Injective e := by
    intro x y hxy
    have heqzero : e (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hxy0 : x - y = 0 := hzero (x - y) heqzero
    exact sub_eq_zero.mp hxy0
  have hsurj : Function.Surjective e := by
    intro y
    obtain ⟨p, hp, hpy⟩ := y.property
    let x : W.restrictionSpace D :=
      ⟨(Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap p, ⟨p, hp, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    calc
      φ ((Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap p) =
          (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap p := hφ_mk p
      _ = y.val := hpy
  change Module.finrank ℂ (W.restrictionSpace D) = Module.finrank ℂ (V.restrictionSpace D)
  exact (LinearEquiv.ofBijective e ⟨hinj, hsurj⟩).finrank_eq

namespace AffineFamily

variable {n : ℕ}

abbrev Family (n : ℕ) := Finset (AffineVariety n)

/-- Each member appears once because the family is a `Finset`. -/
def IsPure (F : Family n) (k : ℕ) : Prop :=
  ∀ V ∈ F, V.IsIrreducible ∧ V.dimension = k

/-- Sum of component degrees, including all dimensions if the family is mixed. -/
noncomputable def degree (F : Family n) : ℚ := ∑ V ∈ F, V.degree

def locus (F : Family n) : AffineVariety n :=
  AffineVariety.ofIdeal (⨅ V ∈ F, V.ideal)

noncomputable def hilbert (F : Family n) (D : ℕ) : ℕ := (locus F).hilbert D

/-- Common equations; larger components of the common locus remain allowed. -/
def ComponentsDefinedInDegree (F : Family n) (L : ℕ) : Prop :=
  ∃ E : Set (Poly n), (∀ f ∈ E, f.totalDegree ≤ L) ∧
    ∀ V ∈ F, V.IsComponentOf (Ideal.span E)

theorem points_locus (F : Family n) :
    (locus F).points = ⋃ V ∈ F, V.points := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hnot
    have hnot' : ¬ ∃ V : AffineVariety n, ∃ (_ : V ∈ F), x ∈ V.points := by
      simpa only [Set.mem_iUnion] using hnot
    have hchoose : ∀ V ∈ F, ∃ f : Poly n, f ∈ V.ideal ∧ MvPolynomial.aeval x f ≠ 0 := by
      intro V hV
      have hVnot : x ∉ V.points := by
        intro hxV
        exact hnot' ⟨V, ⟨hV, hxV⟩⟩
      have hnotforall : ¬ ∀ f, f ∈ V.ideal → MvPolynomial.aeval x f = 0 := by
        simpa [AffineVariety.points, MvPolynomial.mem_zeroLocus_iff] using hVnot
      push Not at hnotforall
      exact hnotforall
    let g : AffineVariety n → Poly n := fun V =>
      if hV : V ∈ F then Classical.choose (hchoose V hV) else 1
    have hg : ∀ V, V ∈ F → g V ∈ V.ideal ∧ MvPolynomial.aeval x (g V) ≠ 0 := by
      intro V hV
      simpa [g, hV] using Classical.choose_spec (hchoose V hV)
    let p : Poly n := ∏ V ∈ F, g V
    have hp : p ∈ ⨅ V ∈ F, V.ideal := by
      simp only [Ideal.mem_iInf]
      intro V hV
      dsimp [p]
      rw [← Finset.mul_prod_erase F g hV]
      exact Ideal.mul_mem_right _ V.ideal (hg V hV).1
    have hpx : MvPolynomial.aeval x p ≠ 0 := by
      dsimp [p]
      rw [map_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro V hV
      exact (hg V hV).2
    have hxzero : MvPolynomial.aeval x p = 0 := by
      have hx' : ∀ q ∈ (⨅ V ∈ F, V.ideal), MvPolynomial.aeval x q = 0 := by
        simpa [locus, AffineVariety.points_ofIdeal] using hx
      exact hx' p hp
    exact hpx hxzero
  · intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨V, hV, hxV⟩ := hx
    have hle : (⨅ W ∈ F, W.ideal) ≤ V.ideal := iInf₂_le V hV
    have hxinf : x ∈ MvPolynomial.zeroLocus ℂ (⨅ W ∈ F, W.ideal) :=
      MvPolynomial.zeroLocus_anti_mono hle hxV
    simpa [locus, AffineVariety.points_ofIdeal] using hxinf

/-- Prime ideals of equal affine dimension cannot properly contain one another.
The zero-dimensional case follows from the degree bound for a principal cut. -/
private theorem prime_same_dimension_eq {n k : ℕ}
    (I J : Ideal (Poly n)) [I.IsPrime] [J.IsPrime]
    (hIJ : I ≤ J)
    (hI : OAI.QuarticPowerFree.affineDimension I = k)
    (hJ : OAI.QuarticPowerFree.affineDimension J = k) : I = J := by
  classical
  by_contra hne
  have hlt : I < J := lt_of_le_of_ne hIJ hne
  obtain ⟨p, hpJ, hpI⟩ := SetLike.exists_of_lt hlt
  have hcut : I ⊔ Ideal.span {p} ≤ J :=
    sup_le hIJ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpJ))
  let P := OAI.QuarticPowerFree.coordinateHilbert I
  let Q := OAI.QuarticPowerFree.coordinateHilbert (I ⊔ Ideal.span {p})
  have hP : ∀ᶠ T : ℕ in Filter.atTop,
      P.eval (T : ℚ) =
        (Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace T).map
          (Ideal.Quotient.mkₐ ℂ I).toLinearMap) : ℚ) := by
    exact (OAI.QuarticPowerFree.coordinateHilbert_eventually I).mono
      (fun _ h => h.symm)
  have hQ : ∀ᶠ T : ℕ in Filter.atTop,
      Q.eval (T : ℚ) =
        (Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace T).map
          (Ideal.Quotient.mkₐ ℂ (I ⊔ Ideal.span {p})).toLinearMap) : ℚ) := by
    exact (OAI.QuarticPowerFree.coordinateHilbert_eventually _).mono
      (fun _ h => h.symm)
  have hI' : P.natDegree = k := by
    simpa [P, OAI.QuarticPowerFree.affineDimension] using hI
  by_cases hk : k = 0
  · have hcutInfo := OAI.QuarticPowerFree.proper_cut_hilbert_polynomial
      I p hpI P Q hP hQ 0 (by rw [hI', hk]; omega)
    have hcoeffP : P.coeff 1 = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hI', hk]
      omega
    have hcoeffQ : Q.coeff 0 ≤ 0 := by
      simpa [hcoeffP] using hcutInfo.2
    have hcutDim : OAI.QuarticPowerFree.affineDimension
        (I ⊔ Ideal.span {p}) = 0 := by
      have hQdim : Q.natDegree = 0 := Nat.eq_zero_of_le_zero hcutInfo.1
      simpa [Q, OAI.QuarticPowerFree.affineDimension] using hQdim
    have hcutProper : I ⊔ Ideal.span {p} ≠ ⊤ := by
      intro htop
      have htopJ : (⊤ : Ideal (Poly n)) ≤ J := htop ▸ hcut
      exact Ideal.IsPrime.ne_top' (top_le_iff.mp htopJ)
    have hdegreeQ : OAI.QuarticPowerFree.affineDegree
        (I ⊔ Ideal.span {p}) = Q.coeff 0 := by
      simp [OAI.QuarticPowerFree.affineDegree, Q, hcutDim]
    have hpositive := OAI.QuarticPowerFree.one_le_affineDegree
      (I ⊔ Ideal.span {p}) hcutProper
    rw [hdegreeQ] at hpositive
    have : (1 : ℚ) ≤ 0 := hpositive.trans hcoeffQ
    norm_num at this
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let d := k - 1
    have hdegP : P.natDegree ≤ d + 1 := by
      rw [hI']
      omega
    have hcutInfo := OAI.QuarticPowerFree.proper_cut_hilbert_polynomial
      I p hpI P Q hP hQ d hdegP
    have hnon : ∀ᶠ T : ℕ in Filter.atTop,
        0 ≤ (OAI.QuarticPowerFree.coordinateHilbert J).eval (T : ℚ) := by
      filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually J] with T hT
      rw [← hT]
      positivity
    have hle : ∀ᶠ T : ℕ in Filter.atTop,
        (OAI.QuarticPowerFree.coordinateHilbert J).eval (T : ℚ) ≤ Q.eval (T : ℚ) := by
      filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually J,
        OAI.QuarticPowerFree.coordinateHilbert_eventually (I ⊔ Ideal.span {p})]
        with T hJT hQT
      rw [← hJT, ← hQT]
      exact_mod_cast OAI.QuarticPowerFree.quotient_hilbert_le
        (I ⊔ Ideal.span {p}) J hcut T
    have hdimJ : (OAI.QuarticPowerFree.coordinateHilbert J).natDegree ≤ d := by
      exact (OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _
        hnon hle).trans hcutInfo.1
    have hJ' : (OAI.QuarticPowerFree.coordinateHilbert J).natDegree = k := by
      simpa [OAI.QuarticPowerFree.affineDimension] using hJ
    have : k ≤ d := by omega
    dsimp [d] at this
    omega

/-- Public access to the existing equal-dimension prime-ideal comparison. -/
theorem prime_same_dimension_eq_of_le {n k : ℕ}
    (I J : Ideal (Poly n)) [I.IsPrime] [J.IsPrime]
    (hIJ : I ≤ J)
    (hI : OAI.QuarticPowerFree.affineDimension I = k)
    (hJ : OAI.QuarticPowerFree.affineDimension J = k) : I = J :=
  prime_same_dimension_eq I J hIJ hI hJ

private theorem locus_ideal_eq_iInf (F : Family n) :
    (locus F).ideal = ⨅ V ∈ F, V.ideal := by
  classical
  have hrad : (⨅ V ∈ F, V.ideal).IsRadical := by
    apply Ideal.isRadical_iInf
    intro V
    apply Ideal.isRadical_iInf
    intro _
    exact V.isRadical
  simpa [locus, AffineVariety.ofIdeal] using hrad.radical

/-- Restriction to all members detects a polynomial class on the family locus. -/
private theorem hilbert_locus_le_sum (F : Family n) (D : ℕ) :
    (locus F).hilbert D ≤ ∑ V ∈ F, V.hilbert D := by
  classical
  let ι : Type := {V : AffineVariety n // V ∈ F}
  letI : Fintype ι := Fintype.ofFinset F (fun _ => Iff.rfl)
  let J : Ideal (Poly n) := ⨅ V ∈ F, V.ideal
  have hW : (locus F).ideal = J := by
    simpa [J] using locus_ideal_eq_iInf F
  have hle (i : ι) : (locus F).ideal ≤ i.val.ideal := by
    rw [hW]
    change (⨅ V ∈ F, V.ideal) ≤ i.val.ideal
    exact iInf₂_le i.val i.property
  let φ (i : ι) :
      (Poly n ⧸ (locus F).ideal) →ₗ[ℂ] (Poly n ⧸ i.val.ideal) :=
    (Ideal.Quotient.factorₐ ℂ (hle i)).toLinearMap
  have hφ_mk (i : ι) (p : Poly n) :
      φ i ((Ideal.Quotient.mkₐ ℂ (locus F).ideal).toLinearMap p) =
        (Ideal.Quotient.mkₐ ℂ i.val.ideal).toLinearMap p := by
    simp [φ]
  let fᵢ (i : ι) : (locus F).restrictionSpace D →ₗ[ℂ] i.val.restrictionSpace D :=
    { toFun := fun x => ⟨φ i x.val, by
        rcases x.property with ⟨p, hp, hpx⟩
        refine ⟨p, hp, ?_⟩
        calc
          (Ideal.Quotient.mkₐ ℂ i.val.ideal).toLinearMap p = φ i
              ((Ideal.Quotient.mkₐ ℂ (locus F).ideal).toLinearMap p) :=
                (hφ_mk i p).symm
          _ = φ i x.val := congrArg (φ i) hpx
      ⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (φ i).map_add x.val y.val
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (φ i).map_smul c x.val }
  let f : (locus F).restrictionSpace D →ₗ[ℂ] ∀ i : ι, i.val.restrictionSpace D :=
    { toFun := fun x i => fᵢ i x
      map_add' := by
        intro x y
        funext i
        exact (fᵢ i).map_add x y
      map_smul' := by
        intro c x
        funext i
        exact (fᵢ i).map_smul c x }
  have hf : Function.Injective f := by
    intro x y hxy
    rcases x.property with ⟨p, hp, hpx⟩
    rcases y.property with ⟨q, hq, hqy⟩
    have hmem : p - q ∈ J := by
      change p - q ∈ (⨅ V ∈ F, V.ideal)
      simp only [Ideal.mem_iInf]
      intro V hV
      let i : ι := ⟨V, hV⟩
      have hi : φ i x.val = φ i y.val := by
        have h := congrArg (fun z => (z i).val) hxy
        exact h
      rw [← hpx, ← hqy, hφ_mk i p, hφ_mk i q] at hi
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem p q).mp hi
    have hmemW : p - q ∈ (locus F).ideal := by
      rw [hW]
      exact hmem
    apply Subtype.ext
    calc
      x.val = (Ideal.Quotient.mkₐ ℂ (locus F).ideal).toLinearMap p := hpx.symm
      _ = (Ideal.Quotient.mkₐ ℂ (locus F).ideal).toLinearMap q :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem p q).2 hmemW
      _ = y.val := hqy
  letI (i : ι) : Module.Free ℂ (i.val.restrictionSpace D) :=
    Module.Free.of_divisionRing ℂ (i.val.restrictionSpace D)
  have hfin : Module.finrank ℂ ((locus F).restrictionSpace D) ≤
      ∑ i : ι, Module.finrank ℂ (i.val.restrictionSpace D) := by
    simpa only [Module.finrank_pi_fintype] using
      (LinearMap.finrank_le_finrank_of_injective hf)
  change Module.finrank ℂ ((locus F).restrictionSpace D) ≤
    ∑ V ∈ F, Module.finrank ℂ (V.restrictionSpace D)
  rw [← Finset.sum_coe_sort (s := F)
    (f := fun V => Module.finrank ℂ (V.restrictionSpace D))]
  exact hfin

/-- Restrictions to the members detect each class on the finite union. -/
theorem hilbert_le_sum (F : Family n) (D : ℕ) :
    hilbert F D ≤ ∑ V ∈ F, V.hilbert D := hilbert_locus_le_sum F D

/-- The degree convention for a pure finite family agrees with OAI's invariant. -/
theorem degree_locus (F : Family n) (k : ℕ) (hF : IsPure F k) :
    (locus F).degree = degree F := by
  classical
  by_cases hFempty : F = ∅
  · subst F
    have htop : (locus (∅ : Family n)).ideal = ⊤ := by
      simp [locus, AffineVariety.ofIdeal]
    have hpoly : OAI.QuarticPowerFree.coordinateHilbert (⊤ : Ideal (Poly n)) = 0 := by
      apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
      filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually
        (⊤ : Ideal (Poly n))] with T hT
      have hzero : Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace T).map
          (Ideal.Quotient.mkₐ ℂ (⊤ : Ideal (Poly n))).toLinearMap) = 0 := by
        have hmk : (Ideal.Quotient.mkₐ ℂ (⊤ : Ideal (Poly n))).toLinearMap = 0 := by
          ext p
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)
        rw [hmk]
        simp
      rw [hzero] at hT
      simpa using hT.symm
    have hdegreeTop : OAI.QuarticPowerFree.affineDegree (⊤ : Ideal (Poly n)) = 0 := by
      simp [OAI.QuarticPowerFree.affineDegree, OAI.QuarticPowerFree.affineDimension, hpoly]
    simp only [degree, Finset.sum_empty]
    change OAI.QuarticPowerFree.affineDegree ((locus (∅ : Family n)).ideal) = 0
    rw [htop]
    exact hdegreeTop
  · let ι : Type := {V : AffineVariety n // V ∈ F}
    letI : Fintype ι := Fintype.ofFinset F (fun _ => Iff.rfl)
    have hι : Nonempty ι := by
      obtain ⟨V, hV⟩ := Finset.nonempty_iff_ne_empty.mpr hFempty
      exact ⟨⟨V, hV⟩⟩
    let J : Ideal (Poly n) := (locus F).ideal
    have hJ : J = ⨅ V ∈ F, V.ideal := by
      simpa [J] using (locus_ideal_eq_iInf F)
    let P : ι → Ideal (Poly n) := fun i => i.val.ideal
    have hPprime (i : ι) : (P i).IsPrime := (hF i.val i.property).1
    have hPdim (i : ι) : OAI.QuarticPowerFree.affineDimension (P i) = k := by
      simpa [P, AffineVariety.dimension] using (hF i.val i.property).2
    have hJP (i : ι) : J ≤ P i := by
      rw [hJ]
      exact iInf₂_le i.val i.property
    have hPinj : Function.Injective P := by
      intro i j hij
      apply Subtype.ext
      exact AffineVariety.ext hij
    have hmin (i : ι) : P i ∈ J.minimalPrimes := by
      letI : (P i).IsPrime := hPprime i
      obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le (hJP i)
      have hQprime : Q.IsPrime := hQ.isPrime
      letI : Q.IsPrime := hQprime
      have hcontained : ∃ j : ι, P j ≤ Q := by
        by_contra hn
        have hchoose : ∀ j : ι, ∃ a : Poly n, a ∈ P j ∧ a ∉ Q := by
          intro j
          by_contra hh
          have hle : P j ≤ Q := by
            intro a ha
            by_contra hna
            exact hh ⟨a, ha, hna⟩
          exact hn ⟨j, hle⟩
        choose a ha using hchoose
        have hprodJ : (∏ j : ι, a j) ∈ J := by
          rw [hJ]
          simp only [Ideal.mem_iInf]
          intro V hV
          let j : ι := ⟨V, hV⟩
          rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ j)]
          exact Ideal.mul_mem_right _ V.ideal (ha j).1
        have hprodNotQ : (∏ j : ι, a j) ∉ Q := by
          simp only [Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]
          exact fun j => (ha j).2
        exact hprodNotQ (hQ.le hprodJ)
      obtain ⟨j, hjQ⟩ := hcontained
      letI : (P j).IsPrime := hPprime j
      have hji : P j ≤ P i := hjQ.trans hQle
      have hsame := prime_same_dimension_eq (P j) (P i) hji (hPdim j) (hPdim i)
      have hji' : j = i := hPinj hsame
      subst j
      have hle : P i ≤ Q := by simpa using hjQ
      have hEq : P i = Q := le_antisymm hle hQle
      rw [hEq]
      exact hQ
    let PJ : Polynomial ℚ := OAI.QuarticPowerFree.coordinateHilbert J
    let Q : ι → Polynomial ℚ := fun i => OAI.QuarticPowerFree.coordinateHilbert (P i)
    let S : Polynomial ℚ := ∑ i : ι, Q i
    have hPJev : ∀ᶠ T : ℕ in Filter.atTop,
        ((locus F).hilbert T : ℚ) = PJ.eval (T : ℚ) := by
      simpa [PJ, J, AffineVariety.hilbertPolynomial] using
        (AffineVariety.hilbert_eventually (locus F))
    have hQev (i : ι) : ∀ᶠ T : ℕ in Filter.atTop,
        (i.val.hilbert T : ℚ) = (Q i).eval (T : ℚ) := by
      simpa [Q, P, AffineVariety.hilbertPolynomial] using
        (AffineVariety.hilbert_eventually i.val)
    have hUpperEval : ∀ᶠ T : ℕ in Filter.atTop,
        PJ.eval (T : ℚ) ≤ S.eval (T : ℚ) := by
      filter_upwards [hPJev, Filter.eventually_all.mpr hQev] with T hJev hQall
      calc
        PJ.eval (T : ℚ) = ((locus F).hilbert T : ℚ) := hJev.symm
        _ ≤ ∑ i : ι, (i.val.hilbert T : ℚ) := by
          have hrank := hilbert_locus_le_sum F T
          rw [← Finset.sum_coe_sort (s := F)
            (f := fun V => V.hilbert T)] at hrank
          exact_mod_cast hrank
        _ = ∑ i : ι, (Q i).eval (T : ℚ) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hQall i
        _ = S.eval (T : ℚ) := by simp [S, Polynomial.eval_finsetSum]
    have hSdegree : S.natDegree ≤ k := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      have hdim : (Q i).natDegree = k := by
        simpa [Q, P, OAI.QuarticPowerFree.affineDimension] using hPdim i
      exact hdim.le
    have hPJnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ PJ.eval (T : ℚ) := by
      filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually J] with T hT
      rw [← hT]
      positivity
    have hPJdegree_le : PJ.natDegree ≤ k := by
      exact (OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
        PJ S hPJnonneg hUpperEval).trans hSdegree
    have hsub (i : ι) : i.val.Subvariety (locus F) := by
      change (locus F).ideal ≤ i.val.ideal
      rw [locus_ideal_eq_iInf F]
      exact iInf₂_le i.val i.property
    have hmemberEval (i : ι) : ∀ᶠ T : ℕ in Filter.atTop,
        (Q i).eval (T : ℚ) ≤ PJ.eval (T : ℚ) := by
      filter_upwards [hQev i, hPJev] with T hQi hJev
      rw [← hQi, ← hJev]
      exact_mod_cast AffineVariety.hilbert_mono i.val (locus F) (hsub i) T
    have hmemberNonneg (i : ι) : ∀ᶠ T : ℕ in Filter.atTop,
        0 ≤ (Q i).eval (T : ℚ) := by
      filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually (P i)] with T hT
      rw [← hT]
      positivity
    obtain ⟨i₀⟩ := hι
    have hk_le_PJ : k ≤ PJ.natDegree := by
      have hle := OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
        (Q i₀) PJ (hmemberNonneg i₀) (hmemberEval i₀)
      have hdim : (Q i₀).natDegree = k := by
        simpa [Q, P, OAI.QuarticPowerFree.affineDimension] using hPdim i₀
      simpa [hdim] using hle
    have hPJdegree : PJ.natDegree = k := le_antisymm hPJdegree_le hk_le_PJ
    have hcoeffUpper : PJ.coeff k ≤ S.coeff k := by
      exact OAI.QuarticPowerFree.coeff_le_of_eventually_nat_eval_le
        PJ S k hPJdegree_le hSdegree hUpperEval
    have hD : ∀ᶠ T : ℕ in Filter.atTop,
        (Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace T).map
          (Ideal.Quotient.mkₐ ℂ J).toLinearMap) : ℚ) = PJ.eval (T : ℚ) := by
      exact OAI.QuarticPowerFree.coordinateHilbert_eventually J
    have hSeq (i : ι) : ∀ᶠ T : ℕ in Filter.atTop,
        (Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace T).map
          (Ideal.Quotient.mkₐ ℂ (P i)).toLinearMap) : ℚ) = (Q i).eval (T : ℚ) := by
      exact OAI.QuarticPowerFree.coordinateHilbert_eventually (P i)
    have hQdegree (i : ι) : (Q i).natDegree ≤ k := by
      have hdim : (Q i).natDegree = k := by
        simpa [Q, P, OAI.QuarticPowerFree.affineDimension] using hPdim i
      exact hdim.le
    have hcoeffLower := OAI.QuarticPowerFree.component_hilbert_coeff_sum_le
      J P hmin hPinj PJ Q hD hSeq hPJdegree_le hQdegree
    have hScoeff : S.coeff k = ∑ i : ι, (Q i).coeff k := by
      simp [S, Polynomial.finsetSum_coeff]
    have hcoeffLower' : ∑ i : ι, (Q i).coeff k ≤ PJ.coeff k := hcoeffLower
    have hcoeffPJ : PJ.coeff k = ∑ i : ι, (Q i).coeff k := by
      apply le_antisymm
      · rw [← hScoeff]
        exact hcoeffUpper
      · exact hcoeffLower'
    have hdegreeSum : degree F = (k.factorial : ℚ) * ∑ i : ι, (Q i).coeff k := by
      unfold degree
      rw [← Finset.sum_coe_sort (s := F) (f := fun V => V.degree)]
      rw [Finset.mul_sum]
      congr 1
      funext i
      change OAI.QuarticPowerFree.affineDegree (P i) = _
      have hdim : (Q i).natDegree = k := by
        simpa [Q, P, OAI.QuarticPowerFree.affineDimension] using hPdim i
      rw [OAI.QuarticPowerFree.affineDegree]
      simp [OAI.QuarticPowerFree.affineDimension, hdim, Q, P]
    have hdimLocus : (locus F).dimension = k := by
      change PJ.natDegree = k
      exact hPJdegree
    calc
      (locus F).degree = (k.factorial : ℚ) * PJ.coeff k := by
        change (OAI.QuarticPowerFree.affineDimension (locus F).ideal).factorial *
          (OAI.QuarticPowerFree.coordinateHilbert (locus F).ideal).coeff
            (OAI.QuarticPowerFree.affineDimension (locus F).ideal) = _
        rw [show OAI.QuarticPowerFree.affineDimension (locus F).ideal = k by
          simpa [AffineVariety.dimension] using hdimLocus]
      _ = (k.factorial : ℚ) * ∑ i : ι, (Q i).coeff k := by rw [hcoeffPJ]
      _ = degree F := hdegreeSum.symm

end AffineFamily

end

end DistinctDistances
