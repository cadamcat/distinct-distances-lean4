import DistinctDistances.TrackD.Profiles.PartitionPackages
import DistinctDistances.TrackA.ADepthAux

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- `profiles.tex:207–215`: d proper cuts isolate each counted point as a
zero-dimensional component, so their common degree bound is a core bound. -/
theorem partition_completed_path_core (S : Finset (Pt d)) (π : CutPath d) (L : ℕ)
    (hvan : ∀ x ∈ S, ∀ i, MvPolynomial.eval (toC x) (π.cut i) = 0)
    (hproper : ∀ x ∈ S, π.ProperAt (toC x))
    (hdegree : ∀ i, (π.cut i).totalDegree ≤ L) : CoreIsolated S L := by
  classical
  -- equation set is the range of cuts
  let F : Set (Poly d) := Set.range π.cut
  have hFdeg : ∀ f ∈ F, f.totalDegree ≤ L := by
    rintro f ⟨i, rfl⟩
    exact hdegree i
  have hSys : π.system d = Ideal.span F := by
    unfold CutPath.system F
    congr 1
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, Fin.is_lt i, rfl⟩
  refine ⟨F, hFdeg, ?_⟩
  intro x hx
  -- span is contained in the point ideal
  have hSpanLe : Ideal.span F ≤ pointIdeal (toC x) := by
    rw [← hSys]
    apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨i, hi, rfl⟩ := hf
    have hvan' := hvan x hx i
    have hmem : π.cut i ∈ pointIdeal (toC x) := by
      rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      have hyx : y = toC x := Set.mem_singleton_iff.mp hy
      subst hyx
      exact hvan'
    exact hmem
  letI : (pointIdeal (toC x)).IsPrime :=
    (pointIdeal_isMaximal (toC x)).isPrime
  obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le hSpanLe
  -- Q gives a local carrier of the full system through toC x
  have hQprime : Q.IsPrime := hQmin.isPrime
  let Z : AffineVariety d := ⟨Q, hQprime.isRadical⟩
  have hZcarrier : π.IsCarrier d Z := by
    show Q ∈ (π.system d).minimalPrimes
    rw [hSys]
    exact hQmin
  have hxZ : toC x ∈ Z := by
    show toC x ∈ MvPolynomial.zeroLocus ℂ Q
    intro f hf
    have hfP : f ∈ pointIdeal (toC x) := hQle hf
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_iff] at hfP
    exact hfP (toC x) (Set.mem_singleton (toC x))
  have hZlocal : Z ∈ π.localCarriers d (toC x) := ⟨hZcarrier, hxZ⟩
  -- prefix purity at j = d forces dimension zero
  have hvan_pre : ∀ i : Fin d, i.val < d →
      MvPolynomial.eval (toC x) (π.cut i) = 0 := fun i _ => hvan x hx i
  have hproper_pre : ∀ i : Fin d, i.val < d →
      ∀ Y ∈ π.localCarriers i.val (toC x), π.cut i ∉ Y.ideal := by
    intro i _ Y hY
    exact hproper x hx i Y hY
  have hdim := (partition_prefix_pure π d le_rfl (toC x) hvan_pre hproper_pre
    Z hZlocal).2
  have hirr : Z.IsIrreducible := hQprime
  have hdim0 : Z.dimension = 0 := by
    have : Z.dimension = d - d := hdim
    omega
  obtain ⟨z, hzpts, _⟩ := TrackA.zeroDim_irreducible_data Z hirr hdim0
  have hzx : toC x = z := by
    have hmem : toC x ∈ ({z} : Set (Point d)) := by
      rw [← hzpts]
      exact hxZ
    exact Set.mem_singleton_iff.mp hmem
  subst hzx
  -- radical identification forces Q = pointIdeal
  have hZero : MvPolynomial.zeroLocus ℂ Q = {toC x} := hzpts
  have hRad : MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ Q)
      = Q.radical :=
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) Q
  have hQeq : Q = pointIdeal (toC x) := by
    have h1 : MvPolynomial.vanishingIdeal ℂ ({toC x} : Set (Point d))
        = Q.radical := by
      rw [← hZero]
      exact hRad
    have h2 : Q.radical = Q := hQprime.isRadical.radical
    rw [pointIdeal]
    rw [h1, h2]
  rw [hQeq] at hQmin
  exact hQmin

/-- `profiles.tex:100–116`: exactly isolate the union of the second-operation
batches by isolated-point interpolation followed by products of equations. -/
theorem partition_interpolated_batch_union (bs : Finset (Finset (Pt d))) (L : ℕ)
    (hL : 1 ≤ L) (hcore : ∀ T ∈ bs, CoreIsolated T L) :
    ∃ E : Set (Poly d),
      (∀ f ∈ E, f.totalDegree ≤ bs.card * (d * (L - 1) + 1)) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' ((bs.biUnion id) : Set (Pt d)) := by
  classical
  -- per-batch exact equations via interpolation
  have hPer : ∀ T : Finset (Pt d), T ∈ bs →
      ∃ Eq : Finset (Poly d),
        (∀ f ∈ Eq, f.totalDegree ≤ d * (L - 1) + 1) ∧
        MvPolynomial.zeroLocus ℂ (Ideal.span (Eq : Set (Poly d)))
          = ((T.image toC : Finset (Point d)) : Set (Point d)) := by
    intro T hT
    obtain ⟨F, hFdeg, hFiso⟩ := hcore T hT
    have hIso : TrackA.IsolatedPoints F (T.image toC) := by
      intro y hy
      obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hy
      exact hFiso x hxT
    obtain ⟨Eq, hEqdeg, hEqzero⟩ :=
      TrackA.poly_interpolation_isolation d L hL F hFdeg (T.image toC) hIso
    exact ⟨Eq, hEqdeg, hEqzero⟩
  choose eqs heqs using hPer
  -- assemble over the subtype index
  let Eidx : ↥bs → Set (Poly d) :=
    fun i => ((eqs i.val i.property : Finset (Poly d)) : Set (Poly d))
  let Lidx : ↥bs → ℕ := fun _ => d * (L - 1) + 1
  have hDeg : ∀ i, ∀ f ∈ Eidx i, f.totalDegree ≤ Lidx i := by
    intro i f hf
    have h := (heqs i.val i.property).1 f
    simpa [Eidx, Lidx] using h (Finset.mem_coe.mp hf)
  obtain ⟨Funion, hFdeg, hFzero⟩ :=
    partition_union_isolation Eidx Lidx hDeg
  have hSum : ∑ _i : ↥bs, Lidx _i = bs.card * (d * (L - 1) + 1) := by
    simp only [Lidx, Finset.sum_const, smul_eq_mul, Finset.card_univ,
      Fintype.card_coe]
  refine ⟨Funion, ?_, ?_⟩
  · intro f hf
    have h := hFdeg f hf
    rwa [hSum] at h
  · rw [hFzero]
    -- union of per-batch loci equals image of biUnion
    have hEach : ∀ i : ↥bs, MvPolynomial.zeroLocus ℂ (Ideal.span (Eidx i))
        = toC '' (↑(i.val) : Set (Pt d)) := by
      intro i
      have h := (heqs i.val i.property).2
      rw [Finset.coe_image] at h
      simpa [Eidx] using h
    calc ⋃ i, MvPolynomial.zeroLocus ℂ (Ideal.span (Eidx i))
        = ⋃ i : ↥bs, toC '' (↑(i.val) : Set (Pt d)) := by
          apply Set.iUnion_congr
          intro i
          exact hEach i
      _ = toC '' ⋃ i : ↥bs, (↑(i.val) : Set (Pt d)) := by
          rw [Set.image_iUnion]
      _ = toC '' ((bs.biUnion id) : Set (Pt d)) := by
          congr 1
          ext x
          simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_biUnion, id_eq]
          constructor
          · rintro ⟨⟨T, hT⟩, hx⟩
            exact ⟨T, hT, hx⟩
          · rintro ⟨T, hT, hx⟩
            exact ⟨⟨T, hT⟩, hx⟩

end
end DistinctDistances.TrackD
