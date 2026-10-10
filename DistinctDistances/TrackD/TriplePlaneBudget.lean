import DistinctDistances.TrackA.Projection
import DistinctDistances.TrackD.TripleCore

/-! Plane-image multiplicity budgets in `secants.tex:479–485`.
Three standard affine charts suffice for the distinct-curve budget; a
constant factor of three is harmless for the frozen universal bound. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

theorem projective_irreducible_isPure {n : ℕ} (C : ProjectiveVariety n)
    (hC : C.IsIrreducible) (k : ℕ) (hdim : C.dimension = k) : C.IsPure k := by
  letI : C.ideal.IsPrime := hC
  intro W
  have hW : W.val.ideal ∈ C.ideal.minimalPrimes := W.property
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at hW
  have hI : W.val.ideal = C.ideal := by simpa using hW
  have heq : W.val = C := ProjectiveVariety.ext hI
  simpa [heq] using hdim

theorem projective_irreducible_degree_pos {n : ℕ} (C : ProjectiveVariety n)
    (hC : C.IsIrreducible) : 0 < C.degree := by
  have hdegree := C.affineCone.one_le_degree hC.ne_top
  rw [ProjectiveVariety.degree_cone] at hdegree
  linarith

theorem projective_multiplicity_pos_of_mem {n : ℕ} (C : ProjectiveVariety (n + 1))
    (p : ProjectivePoint (n + 1)) (hp : p ∈ C.points) : 0 < C.multiplicity p := by
  change 0 < (C.affineChart (chartIndex p)).multiplicity (chartCoordinates (chartIndex p) p)
  exact AffineVariety.multiplicity_pos _ _
    ((C.chart_mem_iff p (chartIndex p) (chartIndex_nonzero p)).mpr hp)

private theorem irreducible_subvariety_eq_of_pos_dimension_eq {n : ℕ}
    (V W : AffineVariety n) (hV : V.IsIrreducible) (hW : W.IsIrreducible)
    (hVW : V.Subvariety W) (hpos : 0 < W.dimension)
    (hdim : V.dimension = W.dimension) : V = W := by
  letI : V.ideal.IsPrime := hV
  by_contra hne
  have hstrict : W.ideal < V.ideal := lt_of_le_of_ne hVW (by
    intro heq
    exact hne (AffineVariety.ext heq.symm))
  obtain ⟨f, hfV, hfW⟩ := SetLike.exists_of_lt hstrict
  have hcut : W.ideal ⊔ Ideal.span {f} ≤ V.ideal := by
    apply sup_le hVW
    apply Ideal.span_le.mpr
    intro a ha
    have heq : a = f := Set.mem_singleton_iff.mp ha
    change a ∈ V.ideal
    rw [heq]
    exact hfV
  obtain ⟨J, hJ, hJV⟩ := Ideal.exists_minimalPrimes_le hcut
  let Z : AffineVariety n := ⟨J, hJ.isPrime.isRadical⟩
  letI : Z.ideal.IsPrime := hJ.isPrime
  have hcomp : Z.IsComponentOf (W.ideal ⊔ Ideal.span {f}) := hJ
  have hZd : Z.dimension = W.dimension - 1 :=
    TrackA.fa_bezout_proper_dimension W Z hW f hfW hcomp (W.dimension - 1) (by omega)
  have hle : V.dimension ≤ Z.dimension :=
    OAI.QuarticPowerFree.affineDimension_antitone Z.ideal V.ideal hJV
  omega

private theorem projective_curve_equation_not_mem {C D : ProjectiveVariety 3}
    (hC : C.IsIrreducible) (hD : D.IsIrreducible)
    (hdimC : C.dimension = 1) (hdimD : D.dimension = 1) (hne : C ≠ D)
    (fD : Poly 3) (hfD : D.ideal = Ideal.span {fD}) : fD ∉ C.ideal := by
  intro hf
  have hCne : C.points.Nonempty := ProjectiveFamily.irreducible_points_nonempty C hC
  have hDne : D.points.Nonempty := ProjectiveFamily.irreducible_points_nonempty D hD
  have hCdim : C.affineCone.dimension = 2 := by
    rw [ProjectiveVariety.dimension_cone C hCne, hdimC]
  have hDdim : D.affineCone.dimension = 2 := by
    rw [ProjectiveVariety.dimension_cone D hDne, hdimD]
  have hsub : C.affineCone.Subvariety D.affineCone := by
    change D.ideal ≤ C.ideal
    rw [hfD]
    exact Ideal.span_le.mpr (by
      intro q hq
      have hq' : q = fD := by simpa using hq
      rw [hq']
      exact hf)
  have heq := irreducible_subvariety_eq_of_pos_dimension_eq C.affineCone D.affineCone
    hC hD hsub (by rw [hDdim]; norm_num) (by rw [hCdim, hDdim])
  apply hne
  apply ProjectiveVariety.ext
  exact congrArg AffineVariety.ideal heq

private theorem projective_affineChart_irreducible {C : ProjectiveVariety 3}
    (hC : C.IsIrreducible) (i : Fin 3) (p : ProjectivePoint 3)
    (hp : p ∈ C.points) (hpi : p.rep i ≠ 0) :
    (C.affineChart i).IsIrreducible := by
  let ℓ : Poly 3 := MvPolynomial.X i
  have hℓhom : ℓ.IsHomogeneous 1 := by
    simpa [ℓ] using MvPolynomial.isHomogeneous_X ℂ i
  have hℓnot : ℓ ∉ C.ideal := by
    intro hℓ
    have hz := hp p.rep p.rep_nonzero (Projectivization.mk_rep p) ℓ hℓ
    exact hpi (by simpa [ℓ, MvPolynomial.aeval_eq_eval] using hz)
  let Z : AffineVariety 3 := TrackA.projectiveLinearSlice C ℓ
  have hZprime : Z.ideal.IsPrime :=
    TrackA.linearSlice_irreducible C hC ℓ hℓhom hℓnot
  have hZideal : Z.ideal = C.ideal ⊔ Ideal.span {ℓ - 1} :=
    TrackA.linearSlice_ideal C hC ℓ hℓhom hℓnot
  have hsurj : Function.Surjective (chartPullback i) := by
    intro q
    exact ⟨MvPolynomial.rename i.succAbove q, TrackA.chartPullback_rename i q⟩
  have hkerZ : RingHom.ker (chartPullback i).toRingHom ≤ Z.ideal := by
    intro q hq
    rw [← AffineVariety.vanishingIdeal_points Z, MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    have hydata : y ∈ C.affineCone.points ∧ MvPolynomial.eval y ℓ = 1 :=
      (TrackA.linearSlice_points C ℓ y).mp hy
    have hyi : y i = 1 := by simpa [ℓ] using hydata.2
    let x : Point 2 := fun j => y (i.succAbove j)
    have hvec : Fin.insertNth i 1 x = y := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
      · simp [x, hyi]
      · simp [x]
    have hqzero : chartPullback i q = 0 := RingHom.mem_ker.mp hq
    change MvPolynomial.eval y q = 0
    rw [← hvec, ← TrackA.chartPullback_eval i q x, hqzero]
    simp
  have hspanMap : (Ideal.span {ℓ - 1}).map (chartPullback i).toRingHom = ⊥ := by
    rw [Ideal.map_span, Set.image_singleton]
    simp [ℓ, chartPullback]
  have hchartIdeal : (C.affineChart i).ideal = Z.ideal.map (chartPullback i).toRingHom := by
    calc
      (C.affineChart i).ideal = C.ideal.map (chartPullback i).toRingHom :=
        TrackA.affineChart_ideal_exact C i
      _ = (C.ideal ⊔ Ideal.span {ℓ - 1}).map (chartPullback i).toRingHom := by
        rw [Ideal.map_sup, hspanMap]
        simp
      _ = Z.ideal.map (chartPullback i).toRingHom := by rw [← hZideal]
  letI : Z.ideal.IsPrime := hZprime
  change (C.affineChart i).ideal.IsPrime
  rw [hchartIdeal]
  exact Ideal.map_isPrime_of_surjective hsurj hkerZ

private def budgetPointVariety {n : ℕ} (x : Point n) : AffineVariety n :=
  ⟨pointIdeal x, (pointIdeal_isMaximal x).isPrime.isRadical⟩

private theorem budgetPointVariety_injective {n : ℕ} :
    Function.Injective (budgetPointVariety (n := n)) := by
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

private theorem budgetPointVariety_irreducible {n : ℕ} (x : Point n) :
    (budgetPointVariety x).IsIrreducible := (pointIdeal_isMaximal x).isPrime

private theorem budgetPointVariety_dimension {n : ℕ} (x : Point n) :
    (budgetPointVariety x).dimension = 0 := by
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

private theorem chartCoordinates_injective_on {i : Fin 3}
    {S : Finset (ProjectivePoint 3)}
    (hchart : ∀ p ∈ S, chartIndex p = i) :
    Set.InjOn (chartCoordinates i) (S : Set (ProjectivePoint 3)) := by
  intro p hp q hq hcoord
  have hpi : p.rep i ≠ 0 := by rw [← hchart p hp]; exact chartIndex_nonzero p
  have hqi : q.rep i ≠ 0 := by rw [← hchart q hq]; exact chartIndex_nonzero q
  let vp : Point 3 := (p.rep i)⁻¹ • p.rep
  let vq : Point 3 := (q.rep i)⁻¹ • q.rep
  have hnorm : vp = vq := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with hij | ⟨k, hk⟩
    · subst j
      simp [vp, vq, hpi, hqi]
    · subst j
      have h := congrFun hcoord k
      dsimp [chartCoordinates] at h
      dsimp [vp, vq, Pi.smul_apply, smul_eq_mul]
      simpa only [div_eq_mul_inv, mul_comm] using h
  have hpne : vp ≠ 0 := smul_ne_zero (inv_ne_zero hpi) p.rep_nonzero
  have hqne : vq ≠ 0 := smul_ne_zero (inv_ne_zero hqi) q.rep_nonzero
  have hmkp : Projectivization.mk ℂ vp hpne = p := by
    rw [← Projectivization.mk_rep p]
    exact (Projectivization.mk_eq_mk_iff' ℂ vp p.rep hpne p.rep_nonzero).2
      ⟨(p.rep i)⁻¹, by simp [vp]⟩
  have hmkq : Projectivization.mk ℂ vq hqne = q := by
    rw [← Projectivization.mk_rep q]
    exact (Projectivization.mk_eq_mk_iff' ℂ vq q.rep hqne q.rep_nonzero).2
      ⟨(q.rep i)⁻¹, by simp [vq]⟩
  have hmk : Projectivization.mk ℂ vp hpne = Projectivization.mk ℂ vq hqne := by
    apply (Projectivization.mk_eq_mk_iff' ℂ vp vq hpne hqne).2
    exact ⟨1, by simpa only [one_smul] using hnorm.symm⟩
  calc
    p = Projectivization.mk ℂ vp hpne := hmkp.symm
    _ = Projectivization.mk ℂ vq hqne := hmk
    _ = q := hmkq

private theorem totalDegree_pos_of_eval_zero {n : ℕ} (f : Poly n)
    (hf : f ≠ 0) (x : Point n) (hfx : MvPolynomial.eval x f = 0) :
    0 < f.totalDegree := by
  by_contra hnot
  have hz : f.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hconst := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
  rw [hconst, MvPolynomial.eval_C] at hfx
  apply hf
  rw [hconst, hfx, map_zero]

private theorem projective_chart_product_budget
    (C D : ProjectiveVariety 3) (hC : C.IsIrreducible) (hD : D.IsIrreducible)
    (hdimC : C.dimension = 1) (hdimD : D.dimension = 1) (hne : C ≠ D)
    (fC fD : Poly 3) (hfC : fC ≠ 0) (hfD : fD ≠ 0)
    (hhomC : fC.IsHomogeneous fC.totalDegree) (hhomD : fD.IsHomogeneous fD.totalDegree)
    (hCIdeal : C.ideal = Ideal.span {fC}) (hDIdeal : D.ideal = Ideal.span {fD})
    (hdegreeC : (fC.totalDegree : ℚ) = C.degree)
    (hdegreeD : (fD.totalDegree : ℚ) = D.degree)
    (i : Fin 3) (S : Finset (ProjectivePoint 3))
    (hchart : ∀ p ∈ S, chartIndex p = i)
    (hS : ∀ p ∈ S, p ∈ C.points ∧ p ∈ D.points) :
    ∑ p ∈ S, C.multiplicity p * D.multiplicity p ≤ C.degree * D.degree := by
  classical
  have hCdegreeNonneg := (projective_irreducible_degree_pos C hC).le
  have hDdegreeNonneg := (projective_irreducible_degree_pos D hD).le
  by_cases hSempty : S = ∅
  · simpa [hSempty] using mul_nonneg hCdegreeNonneg hDdegreeNonneg
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
  obtain ⟨p₀, hp₀⟩ := hSne
  have hpi (p : ProjectivePoint 3) (hp : p ∈ S) : p.rep i ≠ 0 := by
    rw [← hchart p hp]
    exact chartIndex_nonzero p
  have hXi : MvPolynomial.X i ∉ C.ideal := by
    intro h
    have heval := (hS p₀ hp₀).1 p₀.rep p₀.rep_nonzero (Projectivization.mk_rep p₀)
      (MvPolynomial.X i) h
    have heval' : MvPolynomial.eval p₀.rep (MvPolynomial.X i) = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using heval
    exact hpi p₀ hp₀ (by simpa using heval')
  let u : Poly 2 := chartPullback i fC
  let v : Poly 2 := chartPullback i fD
  let φ : Poly 3 →ₐ[ℂ] Poly 2 := chartPullback i
  let V : AffineVariety 2 := C.affineChart i
  let W : AffineVariety 2 := D.affineChart i
  obtain ⟨hu, hVIdeal⟩ := TrackA.principal_chart_equation C fC hfC hhomC hCIdeal i
  obtain ⟨hv, hWIdeal⟩ := TrackA.principal_chart_equation D fD hfD hhomD hDIdeal i
  have hVirr : V.IsIrreducible := projective_affineChart_irreducible
    hC i p₀ (hS p₀ hp₀).1 (hpi p₀ hp₀)
  have hVpoint₀ : chartCoordinates i p₀ ∈ V.points :=
    (C.chart_mem_iff p₀ i (hpi p₀ hp₀)).mpr (hS p₀ hp₀).1
  have huEval₀ : MvPolynomial.eval (chartCoordinates i p₀) u = 0 := by
    have humem : u ∈ V.ideal := by rw [hVIdeal]; exact Ideal.subset_span rfl
    exact hVpoint₀ u humem
  have hvEval₀ : MvPolynomial.eval (chartCoordinates i p₀) v = 0 := by
    have hvmem : v ∈ W.ideal := by rw [hWIdeal]; exact Ideal.subset_span rfl
    have hWpoint₀ : chartCoordinates i p₀ ∈ W.points :=
      (D.chart_mem_iff p₀ i (hpi p₀ hp₀)).mpr (hS p₀ hp₀).2
    exact hWpoint₀ v hvmem
  have huDegree : 0 < u.totalDegree := by
    exact totalDegree_pos_of_eval_zero u hu (chartCoordinates i p₀) huEval₀
  have hvDegree : 0 < v.totalDegree := by
    exact totalDegree_pos_of_eval_zero v hv (chartCoordinates i p₀) hvEval₀
  have hVdim : V.dimension = 1 := by
    change OAI.QuarticPowerFree.affineDimension V.ideal = 1
    rw [hVIdeal]
    exact OAI.QuarticPowerFree.affineDimension_hypersurface u hu huDegree
  have hVchartMap : V.ideal = C.ideal.map φ.toRingHom :=
    TrackA.affineChart_ideal_exact C i
  have hvNotV : v ∉ V.ideal := by
    intro hvV
    have hDnotC : fD ∉ C.ideal :=
      projective_curve_equation_not_mem hC hD hdimC hdimD hne fD hDIdeal
    have hvMap : v ∈ C.ideal.map φ.toRingHom := by rw [← hVchartMap]; exact hvV
    obtain ⟨a, haC, hmapa⟩ :=
      (Ideal.mem_map_iff_of_surjective φ.toRingHom (by
        intro q
        exact ⟨MvPolynomial.rename i.succAbove q, TrackA.chartPullback_rename i q⟩)).mp hvMap
    have hmapfD : φ.toRingHom fD = v := rfl
    have hker : fD - a ∈ RingHom.ker φ.toRingHom := by
      rw [RingHom.mem_ker, map_sub, hmapfD, hmapa, sub_self]
    let Z : AffineVariety 3 := TrackA.projectiveLinearSlice C (MvPolynomial.X i)
    have hℓhom : (MvPolynomial.X i).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℂ i
    have hZideal : Z.ideal = C.ideal ⊔ Ideal.span {MvPolynomial.X i - 1} :=
      TrackA.linearSlice_ideal C hC (MvPolynomial.X i) hℓhom hXi
    have hkerZ : RingHom.ker φ.toRingHom ≤ Z.ideal := by
      intro q hq
      rw [← AffineVariety.vanishingIdeal_points Z, MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      have hydata : y ∈ C.affineCone.points ∧ MvPolynomial.eval y (MvPolynomial.X i) = 1 :=
        (TrackA.linearSlice_points C (MvPolynomial.X i) y).mp hy
      have hyi : y i = 1 := by simpa using hydata.2
      let x : Point 2 := fun j => y (i.succAbove j)
      have hvec : Fin.insertNth i 1 x = y := by
        funext j
        rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, hk⟩
        · subst j; simp [x, hyi]
        · subst j; simp [x]
      have hqzero : φ q = 0 := RingHom.mem_ker.mp hq
      change MvPolynomial.eval y q = 0
      rw [← hvec, ← TrackA.chartPullback_eval i q x, hqzero]
      simp
    have hfslice : fD ∈ Z.ideal := by
      have hqa : fD - a ∈ Z.ideal := hkerZ hker
      have haZ : a ∈ Z.ideal := by
        rw [hZideal]
        exact (le_sup_left : C.ideal ≤ C.ideal ⊔ Ideal.span {MvPolynomial.X i - 1}) haC
      have hsum : (fD - a) + a ∈ Z.ideal := Z.ideal.add_mem hqa haZ
      simpa using hsum
    have hlin := (TrackA.homogeneous_mem_linearSlice_iff C hC
      (MvPolynomial.X i) fD hℓhom hXi hhomD).mp hfslice
    exact hDnotC hlin

  let eqs : Fin 2 → Poly 2 := fun j => if j.val = 0 then u else v
  have hrange : Set.range eqs = {u, v} := by
    ext q
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [eqs]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · refine ⟨⟨0, by omega⟩, ?_⟩
        simp [eqs]
      · refine ⟨⟨1, by omega⟩, ?_⟩
        simp [eqs]
  let J : Ideal (Poly 2) := Ideal.span (Set.range eqs)
  have hJsystem : J = Ideal.span {u, v} := by
    change Ideal.span (Set.range eqs) = Ideal.span {u, v}
    rw [hrange]
  have hJpair : J = V.ideal ⊔ Ideal.span {v} := by
    rw [hJsystem, Ideal.span_insert, ← hVIdeal]
  have hpointMinimal (p : ProjectivePoint 3) (hp : p ∈ S) :
      pointIdeal (chartCoordinates i p) ∈ J.minimalPrimes := by
    let x : Point 2 := chartCoordinates i p
    have hxV : x ∈ V.points := (C.chart_mem_iff p i (hpi p hp)).mpr (hS p hp).1
    have hxW : x ∈ W.points := (D.chart_mem_iff p i (hpi p hp)).mpr (hS p hp).2
    have humem : u ∈ V.ideal := by rw [hVIdeal]; exact Ideal.subset_span rfl
    have hvmem : v ∈ W.ideal := by rw [hWIdeal]; exact Ideal.subset_span rfl
    have hux : MvPolynomial.eval x u = 0 := hxV u humem
    have hvx : MvPolynomial.eval x v = 0 := hxW v hvmem
    have hJle : J ≤ pointIdeal x := by
      rw [hJsystem]
      apply Ideal.span_le.mpr
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x u).2 hux
      · exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x v).2 hvx
    letI : (pointIdeal x).IsPrime := (pointIdeal_isMaximal x).isPrime
    obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le hJle
    let Z : AffineVariety 2 := ⟨Q, hQmin.isPrime.isRadical⟩
    have hZcomp : Z.IsComponentOf (V.ideal ⊔ Ideal.span {v}) := by
      change Q ∈ (V.ideal ⊔ Ideal.span {v}).minimalPrimes
      rw [← hJpair]
      exact hQmin
    have hZdim : Z.dimension = 0 :=
      TrackA.fa_bezout_proper_dimension V Z hVirr v hvNotV hZcomp 0 hVdim
    letI : Q.IsPrime := hQmin.isPrime
    have hQdim : OAI.QuarticPowerFree.affineDimension Q = 0 := hZdim
    have hQmax : Q.IsMaximal := OAI.QuarticPowerFree.zeroDim_isMaximal Q hQdim
    have hQeq : Q = pointIdeal x :=
      hQmax.eq_of_le (pointIdeal_isMaximal x).ne_top hQle
    rw [← hQeq]
    exact hQmin

  let T : Finset (Point 2) := S.image (chartCoordinates i)
  let F : AffineFamily.Family 2 := T.image budgetPointVariety
  have hFpure : AffineFamily.IsPure F 0 := by
    intro U hU
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hU
    exact ⟨budgetPointVariety_irreducible x, budgetPointVariety_dimension x⟩
  have hcomponents : ∀ U ∈ F, U.IsComponentOf J := by
    intro U hU
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact hpointMinimal p hp
  have hdegree : ∀ j, 1 ≤ (eqs j).totalDegree := by
    intro j
    by_cases hj : j.val = 0
    · have hj0 : j = 0 := Fin.ext hj
      subst j
      simpa [eqs] using (Nat.succ_le_of_lt huDegree)
    · have hj' : j.val = 1 := by omega
      have hj1 : j = 1 := Fin.ext hj'
      subst j
      simpa [eqs] using (Nat.succ_le_of_lt hvDegree)
  obtain ⟨m, hm, hbezout⟩ :=
    TrackA.fa_bezout_refined_two (by omega) eqs hdegree F hFpure hcomponents
  have hweightSum : (∑ U ∈ F, (m U : ℚ) * U.degree) =
      ∑ x ∈ T, (m (budgetPointVariety x) : ℚ) := by
    change (∑ U ∈ T.image budgetPointVariety, (m U : ℚ) * U.degree) = _
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro x hx
      have hd : (budgetPointVariety x).degree = 1 := by
        change OAI.QuarticPowerFree.affineDegree (pointIdeal x) = 1
        exact TrackA.affine_point_degree_one x
      rw [hd]
      ring
    · exact fun x hx y hy heq => budgetPointVariety_injective heq
  have hdegProd : ∏ j : Fin 2, ((eqs j).totalDegree : ℚ) =
      (u.totalDegree : ℚ) * (v.totalDegree : ℚ) := by
    simp [eqs, Fin.prod_univ_two]
  have hdegreeBudget : (∑ x ∈ T, (m (budgetPointVariety x) : ℚ)) ≤
      (u.totalDegree : ℚ) * (v.totalDegree : ℚ) := by
    calc
      _ = ∑ U ∈ F, (m U : ℚ) * U.degree := hweightSum.symm
      _ ≤ ∏ j : Fin 2, ((eqs j).totalDegree : ℚ) := hbezout
      _ = _ := hdegProd
  have hlocal (x : Point 2) (hx : x ∈ T) :
      localLengthAt (Ideal.span {u, v}) x = (m (budgetPointVariety x) : ℕ∞) := by
    have hFmem : budgetPointVariety x ∈ F := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have h := hm (budgetPointVariety x) hFmem (budgetPointVariety_irreducible x)
    rw [hrange] at h
    change Module.length (Localization.AtPrime (pointIdeal x))
      (Localization.AtPrime (pointIdeal x) ⧸
        (Ideal.span {u, v}).map (algebraMap (Poly 2) (Localization.AtPrime (pointIdeal x)))) = _ at h
    unfold localLengthAt localizedIdeal
    exact h
  have hpointLower (p : ProjectivePoint 3) (hp : p ∈ S) :
      C.multiplicity p * D.multiplicity p ≤
        (m (budgetPointVariety (chartCoordinates i p)) : ℚ) := by
    let x : Point 2 := chartCoordinates i p
    have hxT : x ∈ T := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hxV : x ∈ V.points := (C.chart_mem_iff p i (hpi p hp)).mpr (hS p hp).1
    have hxW : x ∈ W.points := (D.chart_mem_iff p i (hpi p hp)).mpr (hS p hp).2
    obtain ⟨r, hr⟩ := TrackA.multiplicity_eq_nat V x hxV
    obtain ⟨s, hs⟩ := TrackA.multiplicity_eq_nat W x hxW
    have hCmult : C.multiplicity p = (r : ℚ) :=
      (ProjectiveVariety.multiplicity_chart C p i (hpi p hp)).trans hr
    have hDmult : D.multiplicity p = (s : ℚ) :=
      (ProjectiveVariety.multiplicity_chart D p i (hpi p hp)).trans hs
    have hordC : TrackA.OrderAtLeast u x r :=
      (TrackA.poly_hypersurface_order V u hu hVIdeal x r).2 (by rw [← hr])
    have hordD : TrackA.OrderAtLeast v x s :=
      (TrackA.poly_hypersurface_order W v hv hWIdeal x s).2 (by rw [← hs])
    have hlen := TrackA.fa_bezout_plane_local_orders u v x r s hordC hordD
    have hnat : r * s ≤ m (budgetPointVariety x) := by
      rw [hlocal x hxT] at hlen
      exact_mod_cast hlen
    rw [hCmult, hDmult]
    exact_mod_cast hnat
  have himageM :
      (∑ x ∈ T, (m (budgetPointVariety x) : ℚ)) =
        ∑ p ∈ S, (m (budgetPointVariety (chartCoordinates i p)) : ℚ) := by
    change (∑ x ∈ S.image (chartCoordinates i),
        (m (budgetPointVariety x) : ℚ)) = _
    rw [Finset.sum_image]
    intro p hp q hq heq
    exact chartCoordinates_injective_on hchart hp hq heq
  calc
    (∑ p ∈ S, C.multiplicity p * D.multiplicity p) ≤
        ∑ p ∈ S, (m (budgetPointVariety (chartCoordinates i p)) : ℚ) :=
      Finset.sum_le_sum (fun p hp => hpointLower p hp)
    _ = ∑ x ∈ T, (m (budgetPointVariety x) : ℚ) := himageM.symm
    _ ≤ (u.totalDegree : ℚ) * (v.totalDegree : ℚ) := hdegreeBudget
    _ ≤ C.degree * D.degree := by
      have hdu : (u.totalDegree : ℚ) ≤ C.degree := by
        calc
          _ ≤ (fC.totalDegree : ℚ) := by
            exact_mod_cast (TrackA.chartPullback_degree i fC)
          _ = C.degree := hdegreeC
      have hdv : (v.totalDegree : ℚ) ≤ D.degree := by
        calc
          _ ≤ (fD.totalDegree : ℚ) := by
            exact_mod_cast (TrackA.chartPullback_degree i fD)
          _ = D.degree := hdegreeD
      calc
        _ ≤ C.degree * (v.totalDegree : ℚ) :=
          mul_le_mul_of_nonneg_right hdu (by exact_mod_cast Nat.zero_le v.totalDegree)
        _ ≤ C.degree * D.degree :=
          mul_le_mul_of_nonneg_left hdv (projective_irreducible_degree_pos C hC).le

/-- Implementation package for `secants.tex:479–481`, supplied by `FA.bezout`.
Partition the sample by `chartIndex`, use the reduced plane-curve equations
given by `poly_polar_choice`, and dehomogenize in each chart. The local-order
bound and refined Bézout bound give the product-degree budget in each of
the three charts. The canonical chart definition of projective multiplicity
avoids any chart-invariance assumption. Distinct prime curve ideals ensure
the two chart equations have no common component on a chart containing
an intersection point. -/
theorem projective_plane_multiplicity_product_budget
    (C D : ProjectiveVariety 3) (hC : C.IsIrreducible) (hD : D.IsIrreducible)
    (hdimC : C.dimension = 1) (hdimD : D.dimension = 1) (hne : C ≠ D)
    (S : Finset (ProjectivePoint 3))
    (hS : ∀ p ∈ S, p ∈ C.points ∧ p ∈ D.points) :
    ∑ p ∈ S, C.multiplicity p * D.multiplicity p ≤ 3 * C.degree * D.degree := by
  obtain ⟨fC, polarC, weightsC, hfC, _, hhomC, hCIdeal, hdegreeC, _, _, _, _⟩ :=
    TrackA.poly_polar_choice C (projective_irreducible_isPure C hC 1 hdimC)
      (ProjectiveFamily.irreducible_points_nonempty C hC)
  obtain ⟨fD, polarD, weightsD, hfD, _, hhomD, hDIdeal, hdegreeD, _, _, _, _⟩ :=
    TrackA.poly_polar_choice D (projective_irreducible_isPure D hD 1 hdimD)
      (ProjectiveFamily.irreducible_points_nonempty D hD)
  let Sᵢ : Fin 3 → Finset (ProjectivePoint 3) := fun i =>
    S.filter (fun p => chartIndex p = i)
  have hmap : ∀ p ∈ S, chartIndex p ∈ Finset.univ := fun _ _ => Finset.mem_univ _
  have hpartition : (∑ p ∈ S, C.multiplicity p * D.multiplicity p) =
      ∑ i ∈ Finset.univ, ∑ p ∈ Sᵢ i, C.multiplicity p * D.multiplicity p := by
    simpa [Sᵢ] using (Finset.sum_fiberwise_of_maps_to hmap
      (fun p => C.multiplicity p * D.multiplicity p)).symm
  have hchartBudget (i : Fin 3) :
      (∑ p ∈ Sᵢ i, C.multiplicity p * D.multiplicity p) ≤ C.degree * D.degree := by
    apply projective_chart_product_budget C D hC hD hdimC hdimD hne fC fD
      hfC hfD hhomC hhomD hCIdeal hDIdeal hdegreeC hdegreeD i (Sᵢ i)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp
      exact hS p (Finset.mem_filter.mp hp).1
  calc
    (∑ p ∈ S, C.multiplicity p * D.multiplicity p) =
        ∑ i ∈ Finset.univ, ∑ p ∈ Sᵢ i, C.multiplicity p * D.multiplicity p := hpartition
    _ ≤ ∑ i ∈ Finset.univ, C.degree * D.degree :=
      Finset.sum_le_sum (fun i hi => hchartBudget i)
    _ = 3 * C.degree * D.degree := by simp; ring

/-- The coincident-image budget comes directly from the frozen polar bound.
Only points of multiplicity at least two are included, as required by validity. -/
theorem projective_plane_polar_square_budget
    (C : ProjectiveVariety 3) (hC : C.IsIrreducible) (hdim : C.dimension = 1)
    (S : Finset (ProjectivePoint 3)) (hS : ∀ p ∈ S, 2 ≤ C.multiplicity p) :
    ∑ p ∈ S, C.multiplicity p ^ 2 ≤ 2 * C.degree ^ 2 := by
  obtain ⟨T, hT, _, hbudget⟩ := TrackA.poly_polar C
    (projective_irreducible_isPure C hC 1 hdim)
  have hsub : S ⊆ T := by intro p hp; exact (hT p).mpr (hS p hp)
  have hsum : ∑ p ∈ S, C.multiplicity p ^ 2 ≤ ∑ p ∈ T, C.multiplicity p ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro p hp hnot; exact sq_nonneg _)
  have hdegree := (projective_irreducible_degree_pos C hC).le
  apply hsum.trans (hbudget.trans ?_)
  nlinarith

theorem projective_plane_product_budget_pullback {α : Type*}
    (Pc : Finset α) (z : α → ProjectivePoint 3) (hz : Set.InjOn z (Pc : Set α))
    (C D : ProjectiveVariety 3) (hC : C.IsIrreducible) (hD : D.IsIrreducible)
    (hdimC : C.dimension = 1) (hdimD : D.dimension = 1) (hne : C ≠ D)
    (hpoints : ∀ p ∈ Pc, z p ∈ C.points ∧ z p ∈ D.points) :
    ∑ p ∈ Pc, C.multiplicity (z p) * D.multiplicity (z p) ≤ 3 * C.degree * D.degree := by
  have hsum : (∑ q ∈ Pc.image z, C.multiplicity q * D.multiplicity q) =
      ∑ p ∈ Pc, C.multiplicity (z p) * D.multiplicity (z p) := by
    rw [Finset.sum_image]
    intro p hp q hq heq
    exact hz hp hq heq
  rw [← hsum]
  apply projective_plane_multiplicity_product_budget C D hC hD hdimC hdimD hne
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact hpoints p hp

theorem projective_plane_polar_budget_pullback {α : Type*}
    (Pc : Finset α) (z : α → ProjectivePoint 3) (hz : Set.InjOn z (Pc : Set α))
    (C : ProjectiveVariety 3) (hC : C.IsIrreducible) (hdim : C.dimension = 1)
    (hbranches : ∀ p ∈ Pc, 2 ≤ C.multiplicity (z p)) :
    ∑ p ∈ Pc, C.multiplicity (z p) ^ 2 ≤ 2 * C.degree ^ 2 := by
  have hsum : (∑ q ∈ Pc.image z, C.multiplicity q ^ 2) =
      ∑ p ∈ Pc, C.multiplicity (z p) ^ 2 := by
    rw [Finset.sum_image]
    intro p hp q hq heq
    exact hz hp hq heq
  rw [← hsum]
  apply projective_plane_polar_square_budget C hC hdim
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact hbranches p hp

end
end DistinctDistances.TrackD
