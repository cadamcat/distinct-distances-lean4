import DistinctDistances.TrackD.Profiles.PartitionIsolation

/-! Lemma-sized partition packages.
These are the finite algebraic steps, rather than the multiscale or tree
construction itself. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

private theorem partition_vanishingIdeal_toC_finset (S : Finset (Pt d)) :
    MvPolynomial.vanishingIdeal ℂ (toC '' (S : Set (Pt d))) =
      Finset.inf S (fun x => pointIdeal (toC x)) := by
  classical
  ext f
  simp [pointIdeal, Finset.inf_eq_iInf, MvPolynomial.mem_vanishingIdeal_iff]

private theorem partition_pointIdeal_injective :
    Function.Injective (pointIdeal (n := d)) := by
  classical
  intro x y h
  funext i
  have hx : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal x := by
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    simp
  have hy : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal y := by
    rw [← h]
    exact hx
  have hy' : MvPolynomial.X i - MvPolynomial.C (x i) ∈
      MvPolynomial.vanishingIdeal ℂ {y} := by
    simpa [pointIdeal] using hy
  have heval := MvPolynomial.mem_vanishingIdeal_iff.mp hy' y (by simp)
  have hcoord : y i - x i = 0 := by simpa using heval
  exact (sub_eq_zero.mp hcoord).symm

/-- `profiles.tex:100–111, 116`: an exact finite zero locus makes every listed
point an isolated component of the original equation ideal. -/
theorem partition_exact_isolation_core (S : Finset (Pt d)) (E : Set (Poly d))
    (L : ℕ) (hdegree : ∀ f ∈ E, f.totalDegree ≤ L)
    (hisolate : MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (S : Set (Pt d))) :
    CoreIsolated S L := by
  classical
  let J : Ideal (Poly d) := Ideal.span E
  have hrad : J.radical = Finset.inf S (fun y => pointIdeal (toC y)) := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) J, hisolate]
    exact partition_vanishingIdeal_toC_finset S
  refine ⟨E, hdegree, ?_⟩
  intro x hx
  have hJx : J ≤ pointIdeal (toC x) := by
    calc
      J ≤ J.radical := Ideal.le_radical
      _ = Finset.inf S (fun y => pointIdeal (toC y)) := hrad
      _ ≤ pointIdeal (toC x) := Finset.inf_le hx
  have hminimal : pointIdeal (toC x) ∈ J.minimalPrimes := by
    change Minimal (fun Q : Ideal (Poly d) => Q.IsPrime ∧ J ≤ Q) (pointIdeal (toC x))
    refine ⟨⟨(pointIdeal_isMaximal (toC x)).isPrime, hJx⟩, ?_⟩
    intro Q hQ hQx
    have hradQ : J.radical ≤ Q := by
      calc
        J.radical ≤ Q.radical := Ideal.radical_mono hQ.2
        _ = Q := hQ.1.isRadical.radical
    have hinf : Finset.inf S (fun y => pointIdeal (toC y)) ≤ Q := by
      rw [← hrad]
      exact hradQ
    obtain ⟨y, hyS, hpyQ⟩ := hQ.1.inf_le'.mp hinf
    have hpyx : pointIdeal (toC y) = pointIdeal (toC x) :=
      (pointIdeal_isMaximal (toC y)).eq_of_le
        (pointIdeal_isMaximal (toC x)).ne_top (hpyQ.trans hQx)
    have hCyCx : toC y = toC x := partition_pointIdeal_injective hpyx
    have hyx : y = x := by
      ext i
      exact Complex.ofReal_injective (congrFun hCyCx i)
    subst y
    exact hpyQ
  simpa [J] using hminimal

private theorem partition_pointIdeal_dimension (x : Point d) :
    OAI.QuarticPowerFree.affineDimension (pointIdeal x) = 0 := by
  let I : Ideal (Poly d) := pointIdeal x
  let ev : Poly d →ₐ[ℂ] ℂ := MvPolynomial.aeval x
  have hI : I = RingHom.ker ev.toRingHom := by
    ext f
    change f ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point d)) ↔
      f ∈ RingHom.ker ev.toRingHom
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, RingHom.mem_ker]
    rfl
  have hev : Function.Surjective ev := by
    intro c
    exact ⟨MvPolynomial.C c, by simp [ev]⟩
  let e : (Poly d ⧸ I) ≃ₐ[ℂ] ℂ := by
    rw [hI]
    exact Ideal.quotientKerAlgEquivOfSurjective hev
  have htrdeg : Algebra.trdeg ℂ (Poly d ⧸ I) = 0 := by
    letI : Algebra.IsAlgebraic ℂ (Poly d ⧸ I) := e.symm.isAlgebraic
    exact trdeg_eq_zero_iff.mpr ‹Algebra.IsAlgebraic ℂ (Poly d ⧸ I)›
  have hdim := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg I
    (OAI.QuarticPowerFree.coordinateHilbert I)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually I)
  have hnat : (OAI.QuarticPowerFree.coordinateHilbert I).natDegree = 0 := by
    exact_mod_cast hdim.trans htrdeg
  change OAI.QuarticPowerFree.affineDimension I = 0
  exact hnat

private theorem partitionPackages_system_succ (π : CutPath d) (k : ℕ) (hk : k < d) :
    π.system (k + 1) = π.system k ⊔ Ideal.span {π.cut ⟨k, hk⟩} := by
  classical
  let p := π.cut ⟨k, hk⟩
  have hset :
      {f | ∃ i : Fin d, i.val < k + 1 ∧ π.cut i = f} =
        {f | ∃ i : Fin d, i.val < k ∧ π.cut i = f} ∪ {p} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hik, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hik with hi | hi
      · exact Or.inl ⟨i, hi, rfl⟩
      · right
        have hidx : i = ⟨k, hk⟩ := Fin.ext hi
        simpa [p, hidx]
    · rintro (⟨i, hik, rfl⟩ | rfl)
      · exact ⟨i, Nat.lt_succ_of_lt hik, rfl⟩
      · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
  change Ideal.span {f | ∃ i : Fin d, i.val < k + 1 ∧ π.cut i = f} = _
  rw [hset, Ideal.span_union]
  rfl

/-- `profiles.tex:151–156`: some isolation equation is proper on each
positive-dimensional irreducible local carrier. -/
theorem partition_isolation_carrier_witness (S : Finset (Pt d)) (E : Set (Poly d))
    (hisolate : MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (S : Set (Pt d)))
    (Z : AffineVariety d) (hZ : Z.IsIrreducible) (hdim : 0 < Z.dimension) :
    ∃ f ∈ E, f ∉ Z.ideal := by
  classical
  by_contra hbad
  push Not at hbad
  have hJZ : Ideal.span E ≤ Z.ideal := Ideal.span_le.mpr hbad
  have hpoints : Z.points ⊆ toC '' (S : Set (Pt d)) := by
    intro y hy
    change y ∈ MvPolynomial.zeroLocus ℂ Z.ideal at hy
    have hyJ : y ∈ MvPolynomial.zeroLocus ℂ (Ideal.span E) :=
      MvPolynomial.zeroLocus_anti_mono hJZ hy
    rw [hisolate] at hyJ
    exact hyJ
  have hinf : Finset.inf S (fun x => pointIdeal (toC x)) ≤ Z.ideal := by
    calc
      Finset.inf S (fun x => pointIdeal (toC x)) =
          MvPolynomial.vanishingIdeal ℂ (toC '' (S : Set (Pt d))) :=
        (partition_vanishingIdeal_toC_finset S).symm
      _ ≤ MvPolynomial.vanishingIdeal ℂ Z.points :=
        MvPolynomial.vanishingIdeal_anti_mono hpoints
      _ = Z.ideal := AffineVariety.vanishingIdeal_points Z
  obtain ⟨x, hxS, hxZ⟩ := hZ.inf_le'.mp hinf
  have hxMax : (pointIdeal (toC x)).IsMaximal := pointIdeal_isMaximal _
  have hZeq : Z.ideal = pointIdeal (toC x) :=
    hxMax.eq_of_le hZ.ne_top hxZ |>.symm
  have hZdim : Z.dimension = 0 := by
    change OAI.QuarticPowerFree.affineDimension Z.ideal = 0
    rw [hZeq]
    exact partition_pointIdeal_dimension (toC x)
  omega

/-- `profiles.tex:33–37, 66–67, 151–156`: purity after a proper prefix uses
only that prefix. The unfilled cuts of the path carry no hypotheses. -/
theorem partition_prefix_pure (π : CutPath d) (j : ℕ) (hj : j ≤ d) (x : Point d)
    (hvan : ∀ i : Fin d, i.val < j → MvPolynomial.eval x (π.cut i) = 0)
    (hproper : ∀ i : Fin d, i.val < j →
      ∀ Z ∈ π.localCarriers i.val x, π.cut i ∉ Z.ideal) :
    ∀ Z ∈ π.localCarriers j x, Z.IsIrreducible ∧ Z.dimension = d - j := by
  classical
  have hmain : ∀ k, k ≤ j → ∀ Z ∈ π.localCarriers k x,
      Z.IsIrreducible ∧ Z.dimension = d - k := by
    intro k
    induction k with
    | zero =>
        intro hk Z hZ
        have hsys : π.system 0 = ⊥ := by simp [CutPath.system]
        have hZmin : Z.ideal ∈ (π.system 0).minimalPrimes := hZ.1
        rw [hsys] at hZmin
        have hZeq : Z.ideal = ⊥ := by
          rw [Ideal.minimalPrimes_eq_subsingleton_self] at hZmin
          simpa using hZmin
        refine ⟨?_, ?_⟩
        · change Z.ideal.IsPrime
          rw [hZeq]
          infer_instance
        · change OAI.QuarticPowerFree.affineDimension Z.ideal = d
          rw [hZeq]
          have hwhole := DistinctDistances.Bridges.affine_whole_dimension d
          change OAI.QuarticPowerFree.affineDimension
            ((⊥ : Ideal (Poly d)).radical) = d at hwhole
          rw [Ideal.radical_bot_of_isReduced] at hwhole
          exact hwhole
    | succ k ih =>
        intro hk Z hZ
        have hkd : k < d := by omega
        let i : Fin d := ⟨k, hkd⟩
        have hZmin : Z.ideal ∈ (π.system (k + 1)).minimalPrimes := hZ.1
        letI : Z.ideal.IsPrime := hZmin.isPrime
        have hprev : π.system k ≤ Z.ideal := by
          calc
            π.system k ≤ π.system k ⊔ Ideal.span {π.cut i} := le_sup_left
            _ = π.system (k + 1) := (partitionPackages_system_succ π k hkd).symm
            _ ≤ Z.ideal := hZmin.le
        obtain ⟨Q, hQ, hQZ⟩ := Ideal.exists_minimalPrimes_le hprev
        let Y : AffineVariety d := ⟨Q, hQ.isPrime.isRadical⟩
        have hxZ : x ∈ Z := hZ.2
        have hxY : x ∈ Y := by
          change x ∈ MvPolynomial.zeroLocus ℂ Q
          apply MvPolynomial.zeroLocus_anti_mono hQZ
          exact hxZ
        have hYlocal : Y ∈ π.localCarriers k x := by
          constructor
          · change Q ∈ (π.system k).minimalPrimes
            exact hQ
          · exact hxY
        have hdimY : Y.dimension = d - k := ih (by omega) Y hYlocal |>.2
        have hproperCut : π.cut i ∉ Q := by
          exact hproper i (by dsimp [i]; omega) Y hYlocal
        have hZcut : Z.ideal ∈
            (Q ⊔ Ideal.span {π.cut i}).minimalPrimes := by
          change Minimal (fun J : Ideal (Poly d) =>
            J.IsPrime ∧ Q ⊔ Ideal.span {π.cut i} ≤ J) Z.ideal
          refine ⟨⟨hZmin.isPrime, ?_⟩, ?_⟩
          · apply sup_le hQZ
            apply Ideal.span_le.mpr
            intro f hf
            have hfeq : f = π.cut i := by
              simpa only [Set.mem_singleton_iff] using hf
            have hcutmem : π.cut i ∈ π.system (k + 1) := by
              rw [partitionPackages_system_succ π k hkd]
              exact Ideal.mem_sup_right (Ideal.subset_span rfl)
            rw [hfeq]
            exact hZmin.le hcutmem
          · intro J hJ hJZ
            have hsystemJ : π.system (k + 1) ≤ J := by
              rw [partitionPackages_system_succ π k hkd]
              exact sup_le (hQ.le.trans (le_sup_left.trans hJ.2))
                (Ideal.span_le.mpr (by
                  intro f hf
                  have hfeq : f = π.cut i := by
                    simpa only [Set.mem_singleton_iff] using hf
                  rw [hfeq]
                  exact hJ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))))
            exact hZmin.2 ⟨hJ.1, hsystemJ⟩ hJZ
        letI : Q.IsPrime := hQ.isPrime
        have hdimcut := OAI.QuarticPowerFree.proper_cut_component_dimension
          Q Z.ideal (π.cut i) hproperCut hZcut (by
            have hdimY' : OAI.QuarticPowerFree.affineDimension Q =
                (d - (k + 1)) + 1 := by
              change Y.dimension = (d - (k + 1)) + 1
              rw [hdimY]
              omega
            exact hdimY')
        refine ⟨hZmin.isPrime, ?_⟩
        change OAI.QuarticPowerFree.affineDimension Z.ideal = d - (k + 1)
        exact hdimcut
  intro Z hZ
  exact hmain j le_rfl Z hZ

/-- `profiles.tex:151–156`: finish a proper prefix by generic combinations
of the isolation equations, all recorded at the final testing time. -/
private theorem partitionPackages_prefix_system_eq (π π' : CutPath d) (j : ℕ)
    (hcuts : ∀ i : Fin d, i.val < j → π.cut i = π'.cut i) :
    π.system j = π'.system j := by
  unfold CutPath.system
  congr 1
  ext f
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (hcuts i hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, hcuts i hi⟩

private theorem partitionPackages_prefix_carriers_eq (π π' : CutPath d) (j : ℕ)
    (hcuts : ∀ i : Fin d, i.val < j → π.cut i = π'.cut i) (x : Point d) :
    π.localCarriers j x = π'.localCarriers j x := by
  unfold CutPath.localCarriers CutPath.IsCarrier
  rw [partitionPackages_prefix_system_eq π π' j hcuts]

private theorem partitionPackages_extend_prefix (π : CutPath d) (j : ℕ) (hj : j < d)
    (S T : Finset (Pt d)) (g : Poly d) (b : ℝ)
    (hcap : T ⊆ π.captured j S g)
    (hvan : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      MvPolynomial.eval (toC x) (π.cut i) = 0)
    (hproper : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      ∀ Z ∈ π.localCarriers i.val (toC x), π.cut i ∉ Z.ideal)
    (hmono : ∀ i k : Fin d, i.val < j → k.val < j → i ≤ k → π.time i ≤ π.time k)
    (hfinal : ∀ i : Fin d, i.val < j → π.time i ≤ b) :
    ∃ π' : CutPath d,
      (∀ i : Fin d, i.val < j → π'.cut i = π.cut i ∧ π'.time i = π.time i) ∧
      π'.cut ⟨j, hj⟩ = g ∧ π'.time ⟨j, hj⟩ = b ∧
      (∀ x ∈ T, ∀ i : Fin d, i.val < j + 1 →
        MvPolynomial.eval (toC x) (π'.cut i) = 0) ∧
      (∀ x ∈ T, ∀ i : Fin d, i.val < j + 1 →
        ∀ Z ∈ π'.localCarriers i.val (toC x), π'.cut i ∉ Z.ideal) ∧
      (∀ i k : Fin d, i.val < j + 1 → k.val < j + 1 → i ≤ k →
        π'.time i ≤ π'.time k) ∧
      ∀ i : Fin d, i.val < j + 1 → π'.time i ≤ b := by
  classical
  let index : Fin d := ⟨j, hj⟩
  let π' : CutPath d := ⟨Function.update π.cut index g, Function.update π.time index b⟩
  have hprefix : ∀ i : Fin d, i.val < j → π'.cut i = π.cut i ∧ π'.time i = π.time i := by
    intro i hi
    have hne : i ≠ index := by
      intro h
      have := congrArg Fin.val h
      dsimp [index] at this
      omega
    simp [π', hne]
  have hcut : π'.cut index = g := by simp [π']
  have htime : π'.time index = b := by simp [π']
  have hsys : ∀ k ≤ j, ∀ x : Point d, π'.localCarriers k x = π.localCarriers k x := by
    intro k hk x
    exact partitionPackages_prefix_carriers_eq π' π k
      (fun i hi => (hprefix i (by omega)).1) x
  have hpoint : ∀ x ∈ T, x ∈ S ∧ MvPolynomial.eval (toC x) g = 0 ∧
      ∀ Z ∈ π.localCarriers j (toC x), g ∉ Z.ideal := by
    intro x hx
    exact Finset.mem_filter.mp (hcap hx)
  refine ⟨π', hprefix, hcut, htime, ?_, ?_, ?_, ?_⟩
  · intro x hx i hi
    by_cases hij : i.val < j
    · rw [(hprefix i hij).1]
      exact hvan x (hpoint x hx).1 i hij
    · have hieq : i = index := Fin.ext (by dsimp [index]; omega)
      rw [hieq, hcut]
      exact (hpoint x hx).2.1
  · intro x hx i hi Z hZ
    by_cases hij : i.val < j
    · rw [(hprefix i hij).1]
      exact hproper x (hpoint x hx).1 i hij Z ((hsys i.val (by omega) (toC x)) ▸ hZ)
    · have hieq : i = index := Fin.ext (by dsimp [index]; omega)
      rw [hieq, hcut]
      have hZj : Z ∈ π.localCarriers j (toC x) := by
        rw [hieq] at hZ
        exact (hsys j le_rfl (toC x)) ▸ hZ
      exact (hpoint x hx).2.2 Z hZj
  · intro i k hi hk hik
    by_cases hkj : k.val < j
    · have hij : i.val < j := by change i.val ≤ k.val at hik; omega
      rw [(hprefix i hij).2, (hprefix k hkj).2]
      exact hmono i k hij hkj hik
    · have hkeq : k = index := Fin.ext (by dsimp [index]; omega)
      rw [hkeq, htime]
      by_cases hij : i.val < j
      · rw [(hprefix i hij).2]
        exact hfinal i hij
      · have hieq : i = index := Fin.ext (by dsimp [index]; omega)
        rw [hieq, htime]
  · intro i hi
    by_cases hij : i.val < j
    · rw [(hprefix i hij).2]
      exact hfinal i hij
    · have hieq : i = index := Fin.ext (by dsimp [index]; omega)
      rw [hieq, htime]

/- This extension helper is local because `PartitionPrefixes` is downstream of
this package in the import graph. -/
theorem partition_finish_prefix (S S₀ : Finset (Pt d)) (hsubset : S ⊆ S₀)
    (E : Set (Poly d)) (L : ℕ)
    (hdegree : ∀ f ∈ E, f.totalDegree ≤ L)
    (hisolate : MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (S₀ : Set (Pt d)))
    (π : CutPath d) (j : ℕ) (hj : j ≤ d) (b : ℝ)
    (hvan : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      MvPolynomial.eval (toC x) (π.cut i) = 0)
    (hproper : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      ∀ Z ∈ π.localCarriers i.val (toC x), π.cut i ∉ Z.ideal)
    (hmono : ∀ i k : Fin d, i.val < j → k.val < j → i ≤ k → π.time i ≤ π.time k)
    (hfinal : ∀ i : Fin d, i.val < j → π.time i ≤ b) :
    ∃ π' : CutPath d,
      (∀ i : Fin d, i.val < j → π'.cut i = π.cut i ∧ π'.time i = π.time i) ∧
      (∀ i : Fin d, j ≤ i.val → (π'.cut i).totalDegree ≤ L ∧ π'.time i = b) ∧
      Monotone π'.time ∧
    (∀ x ∈ S, ∀ i, MvPolynomial.eval (toC x) (π'.cut i) = 0) ∧
      ∀ x ∈ S, π'.ProperAt (toC x) := by
  classical
  have hEvan : ∀ x ∈ S, ∀ f ∈ E, MvPolynomial.eval (toC x) f = 0 := by
    intro x hx f hf
    have hxS₀ : x ∈ S₀ := hsubset hx
    have hxzero : toC x ∈ MvPolynomial.zeroLocus ℂ (Ideal.span E) := by
      rw [hisolate]
      exact ⟨x, hxS₀, rfl⟩
    rw [MvPolynomial.zeroLocus_span] at hxzero
    exact hxzero f hf
  have hbuild : ∀ n, ∀ k, d - k = n → j ≤ k → k ≤ d →
      ∀ ρ : CutPath d,
        (∀ i : Fin d, i.val < j →
          ρ.cut i = π.cut i ∧ ρ.time i = π.time i) →
        (∀ i : Fin d, j ≤ i.val → i.val < k →
          (ρ.cut i).totalDegree ≤ L ∧ ρ.time i = b) →
        (∀ x ∈ S, ∀ i : Fin d, i.val < k →
          MvPolynomial.eval (toC x) (ρ.cut i) = 0) →
        (∀ x ∈ S, ∀ i : Fin d, i.val < k →
          ∀ Z ∈ ρ.localCarriers i.val (toC x), ρ.cut i ∉ Z.ideal) →
        (∀ i l : Fin d, i.val < k → l.val < k → i ≤ l →
          ρ.time i ≤ ρ.time l) →
        (∀ i : Fin d, i.val < k → ρ.time i ≤ b) →
        ∃ ρ' : CutPath d,
          (∀ i : Fin d, i.val < j →
            ρ'.cut i = π.cut i ∧ ρ'.time i = π.time i) ∧
          (∀ i : Fin d, j ≤ i.val →
            (ρ'.cut i).totalDegree ≤ L ∧ ρ'.time i = b) ∧
          Monotone ρ'.time ∧
          (∀ x ∈ S, ∀ i, MvPolynomial.eval (toC x) (ρ'.cut i) = 0) ∧
          ∀ x ∈ S, ρ'.ProperAt (toC x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hrem hjk hkd ρ hprefix hfilled hvan hproper hmono htime
      by_cases hk : k = d
      · subst k
        refine ⟨ρ, hprefix, ?_, ?_, ?_, ?_⟩
        · intro i hi
          exact hfilled i hi i.isLt
        · intro i l hil
          exact hmono i l i.isLt l.isLt hil
        · intro x hx i
          exact hvan x hx i i.isLt
        · intro x hx
          intro i Z hZ
          exact hproper x hx i i.isLt Z hZ
      · have hklt : k < d := by omega
        let i : Fin d := ⟨k, hklt⟩
        have hpure : ∀ x ∈ S, ∀ Z ∈ ρ.localCarriers k (toC x),
            Z.IsIrreducible ∧ Z.dimension = d - k := by
          intro x hx
          exact partition_prefix_pure ρ k (by omega) (toC x)
            (hvan x hx) (hproper x hx)
        let carriers : Finset (AffineVariety d) := by
          let I : Ideal (Poly d) := ρ.system k
          letI : Fintype {Q : Ideal (Poly d) // Q ∈ I.minimalPrimes} :=
            (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly d) I).fintype
          exact (Finset.univ.image
              (fun Q : {Q : Ideal (Poly d) // Q ∈ I.minimalPrimes} =>
                (⟨Q.1, Q.2.isPrime.isRadical⟩ : AffineVariety d))).filter
            (fun Z => ∃ x ∈ S, Z ∈ ρ.localCarriers k (toC x))
        have hcarriers : ∀ Z ∈ carriers,
            ∃ f ∈ E, f ∉ Z.ideal := by
          intro Z hZ
          have hZ' : ∃ x ∈ S, Z ∈ ρ.localCarriers k (toC x) := by
            simpa [carriers] using (Finset.mem_filter.mp hZ).2
          obtain ⟨x, hx, hZx⟩ := hZ'
          have hp := hpure x hx Z hZx
          have hdim : 0 < Z.dimension := by
            rw [hp.2]
            omega
          exact partition_isolation_carrier_witness S₀ E hisolate Z hp.1 hdim
        obtain ⟨g, hgdegree, hgspan, hgproper, hgvan⟩ :=
          partition_generic_finishing_cut E L hdegree carriers hcarriers
        have hcap : S ⊆ ρ.captured k S g := by
          intro x hx
          apply Finset.mem_filter.mpr
          refine ⟨hx, hgvan (toC x) (fun f hf => hEvan x hx f hf), ?_⟩
          intro Z hZ
          apply hgproper
          have hZmin : Z.ideal ∈ (ρ.system k).minimalPrimes := hZ.1
          let I : Ideal (Poly d) := ρ.system k
          letI : Fintype {Q : Ideal (Poly d) // Q ∈ I.minimalPrimes} :=
            (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly d) I).fintype
          apply Finset.mem_filter.mpr
          refine ⟨?_, ⟨x, hx, hZ⟩⟩
          apply Finset.mem_image.mpr
          refine ⟨⟨Z.ideal, ?_⟩, Finset.mem_univ _, ?_⟩
          · simpa [I] using hZmin
          · apply AffineVariety.ext
            rfl
        obtain ⟨ρ', hstepPrefix, hcut, hcutTime, hstepVan, hstepProper,
          hstepMono, hstepTime⟩ :=
          partitionPackages_extend_prefix ρ k hklt S S g b hcap hvan hproper hmono htime
        have hprefix' : ∀ q : Fin d, q.val < j →
            ρ'.cut q = π.cut q ∧ ρ'.time q = π.time q := by
          intro q hq
          have hqk : q.val < k := by omega
          obtain ⟨hcutq, htimeq⟩ := hstepPrefix q hqk
          obtain ⟨hcutOrig, htimeOrig⟩ := hprefix q hq
          exact ⟨hcutq.trans hcutOrig, htimeq.trans htimeOrig⟩
        have hfilled' : ∀ q : Fin d, j ≤ q.val → q.val < k + 1 →
            (ρ'.cut q).totalDegree ≤ L ∧ ρ'.time q = b := by
          intro q hqj hq
          by_cases hqk : q.val < k
          · rw [(hstepPrefix q hqk).1, (hstepPrefix q hqk).2]
            exact hfilled q hqj hqk
          · have hqi : q = i := Fin.ext (by dsimp [i]; omega)
            subst q
            rw [hcut, hcutTime]
            exact ⟨hgdegree, rfl⟩
        have hsmall : d - (k + 1) < n := by omega
        exact ih (d - (k + 1)) hsmall (k + 1) rfl (by omega) (by omega)
          ρ' hprefix' hfilled' hstepVan hstepProper hstepMono hstepTime
  obtain ⟨π', hprefix', hfilled', hmono', hvan', hproper'⟩ :=
    hbuild (d - j) j rfl le_rfl hj π
      (by intro i hi; exact ⟨rfl, rfl⟩)
      (by intro i hij hi; omega)
      hvan hproper hmono hfinal
  exact ⟨π', hprefix', hfilled', hmono', hvan', hproper'⟩

/-- `profiles.tex:134–166`: finite geometric threshold weights. For the
finitary partition the number of grid events is fixed before the sample. -/
theorem partition_threshold_hierarchy (K : ℕ) (u : ℝ) (hu : 0 < u) :
    ∃ a : Fin K → ℝ,
      (∀ i, u ≤ a i) ∧
      (∀ i, (∑ k ∈ Finset.univ.filter (fun k : Fin K => i < k), a k) ≤ a i / 9) ∧
      (∑ i, a i) ≤ u * (10 : ℝ) ^ K := by
  classical
  let a : Fin K → ℝ := fun i => u * (10 : ℝ) ^ i.rev.val
  refine ⟨a, ?_, ?_, ?_⟩
  · intro i
    have hp : (1 : ℝ) ≤ (10 : ℝ) ^ i.rev.val := one_le_pow₀ (by norm_num)
    exact le_mul_of_one_le_right hu.le hp
  · intro i
    let n := i.rev.val
    have hsum :
        (∑ k ∈ Finset.univ.filter (fun k : Fin K => i < k),
            (10 : ℝ) ^ k.rev.val) =
          ∑ r ∈ Finset.range n, (10 : ℝ) ^ r := by
      refine Finset.sum_bij (fun k _ => k.rev.val) ?_ ?_ ?_ ?_
      · intro k hk
        have hik : i < k := (Finset.mem_filter.mp hk).2
        exact Finset.mem_range.mpr (Fin.rev_strictAnti hik)
      · intro k₁ hk₁ k₂ hk₂ h
        have hrev : k₁.rev = k₂.rev := Fin.ext h
        exact Fin.rev_injective hrev
      · intro r hr
        have hrK : r < K := (Finset.mem_range.mp hr).trans i.rev.isLt
        let rFin : Fin K := ⟨r, hrK⟩
        let k : Fin K := Fin.rev rFin
        refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · apply Fin.lt_rev_iff.mpr
          exact Fin.lt_def.mpr (Finset.mem_range.mp hr)
        · simp [k, rFin]
      · intro k hk
        rfl
    have hgeom :
        (∑ r ∈ Finset.range n, (10 : ℝ) ^ r) = ((10 : ℝ) ^ n - 1) / 9 := by
      rw [geom_sum_eq (by norm_num : (10 : ℝ) ≠ 1)]
      norm_num
    have hpow : (0 : ℝ) < (10 : ℝ) ^ n := pow_pos (by norm_num) n
    have hgeom_le :
        (∑ r ∈ Finset.range n, (10 : ℝ) ^ r) ≤ (10 : ℝ) ^ n / 9 := by
      rw [hgeom]
      nlinarith
    calc
      (∑ k ∈ Finset.univ.filter (fun k : Fin K => i < k), a k) =
          u * ∑ r ∈ Finset.range n, (10 : ℝ) ^ r := by
        simp only [a]
        rw [← Finset.mul_sum, hsum]
      _ ≤ u * ((10 : ℝ) ^ n / 9) := mul_le_mul_of_nonneg_left hgeom_le hu.le
      _ = a i / 9 := by simp [a, n]; ring
  · have hrev :
        (∑ i : Fin K, (10 : ℝ) ^ i.rev.val) =
          ∑ i : Fin K, (10 : ℝ) ^ i.val := by
      exact Fintype.sum_bijective (fun i : Fin K => i.rev) Fin.rev_bijective _ _
        (fun i => rfl)
    have hrange :
        (∑ i : Fin K, (10 : ℝ) ^ i.val) =
          ∑ r ∈ Finset.range K, (10 : ℝ) ^ r :=
      Fin.sum_univ_eq_sum_range (fun r => (10 : ℝ) ^ r) K
    have hgeom :
        (∑ r ∈ Finset.range K, (10 : ℝ) ^ r) = ((10 : ℝ) ^ K - 1) / 9 := by
      rw [geom_sum_eq (by norm_num : (10 : ℝ) ≠ 1)]
      norm_num
    have hfrac : ((10 : ℝ) ^ K - 1) / 9 ≤ (10 : ℝ) ^ K := by
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 10 by norm_num) K]
    calc
      (∑ i, a i) = u * ∑ i : Fin K, (10 : ℝ) ^ i.rev.val := by
        simp only [a]
        rw [← Finset.mul_sum]
      _ = u * ∑ r ∈ Finset.range K, (10 : ℝ) ^ r := by rw [hrev, hrange]
      _ = u * (((10 : ℝ) ^ K - 1) / 9) := by rw [hgeom]
      _ ≤ u * (10 : ℝ) ^ K := mul_le_mul_of_nonneg_left hfrac hu.le

end
end DistinctDistances.TrackD
