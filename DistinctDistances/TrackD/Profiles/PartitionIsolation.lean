import DistinctDistances.TrackD.Profiles.Defs
import DistinctDistances.TrackA.Interpolation

/-! Exact isolation and generic finishing cuts for the multiscale partition,
`profiles.tex:100–116, 151–156`. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- Products with one equation from each system cut out their union. The degree
bound is the sum of the individual bounds, including overlapping point lists. -/
theorem partition_union_isolation {d : ℕ} {ι : Type*} [Fintype ι]
    (E : ι → Set (Poly d)) (L : ι → ℕ)
    (hdegree : ∀ i, ∀ f ∈ E i, f.totalDegree ≤ L i) :
    ∃ F : Set (Poly d),
      (∀ f ∈ F, f.totalDegree ≤ ∑ i, L i) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span F) =
        ⋃ i, MvPolynomial.zeroLocus ℂ (Ideal.span (E i)) := by
  classical
  let F : Set (Poly d) :=
    Set.range (fun p : ∀ i, {f : Poly d // f ∈ E i} => ∏ i, (p i).val)
  refine ⟨F, ?_, ?_⟩
  · rintro f ⟨p, rfl⟩
    calc
      _ ≤ ∑ i, ((p i).val).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ i, L i := Finset.sum_le_sum (fun i hi => hdegree i _ (p i).property)
  · ext x
    rw [MvPolynomial.zeroLocus_span]
    constructor
    · intro hx
      by_contra hn
      have hw : ∀ i, ∃ f ∈ E i, MvPolynomial.eval x f ≠ 0 := by
        intro i
        have hxi : x ∉ MvPolynomial.zeroLocus ℂ (Ideal.span (E i)) := by
          intro h
          exact hn (Set.mem_iUnion.mpr ⟨i, h⟩)
        rw [MvPolynomial.zeroLocus_span] at hxi
        change ¬ (∀ f ∈ E i, MvPolynomial.eval x f = 0) at hxi
        push Not at hxi
        exact hxi
      choose p hp hpx using hw
      let choices : ∀ i, {f : Poly d // f ∈ E i} := fun i => ⟨p i, hp i⟩
      have hprod := hx (∏ i, p i) (show (∏ i, p i) ∈ F from ⟨choices, rfl⟩)
      have hnonzero : MvPolynomial.eval x (∏ i, p i) ≠ 0 := by
        rw [map_prod]
        exact Finset.prod_ne_zero_iff.mpr (fun i hi => hpx i)
      exact hnonzero hprod
    · intro hx f hf
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨p, rfl⟩ := hf
      rw [MvPolynomial.zeroLocus_span] at hi
      have hzero : MvPolynomial.eval x (p i).val = 0 := hi _ (p i).property
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

/-- The linear span of bounded isolation equations has a member proper on every
one of finitely many carriers, once each carrier has a witness. -/
theorem partition_generic_finishing_cut {d : ℕ} (E : Set (Poly d)) (L : ℕ)
    (hdegree : ∀ f ∈ E, f.totalDegree ≤ L)
    (carriers : Finset (AffineVariety d))
    (hwitness : ∀ Z ∈ carriers, ∃ f ∈ E, f ∉ Z.ideal) :
    ∃ g : Poly d, g.totalDegree ≤ L ∧ g ∈ Submodule.span ℂ E ∧
      (∀ Z ∈ carriers, g ∉ Z.ideal) ∧
      ∀ x : Point d, (∀ f ∈ E, MvPolynomial.eval x f = 0) →
        MvPolynomial.eval x g = 0 := by
  classical
  let U := Submodule.span ℂ E
  let V : carriers → Submodule ℂ U := fun Z =>
    (Z.val.ideal.restrictScalars ℂ).comap U.subtype
  have hV : ∀ Z, V Z ≠ ⊤ := by
    intro Z heq
    obtain ⟨f, hf, hfZ⟩ := hwitness Z.val Z.property
    let fU : U := ⟨f, Submodule.subset_span hf⟩
    have h : fU ∈ V Z := heq.symm ▸ Submodule.mem_top
    exact hfZ h
  obtain ⟨g, hg⟩ := Submodule.exists_forall_notMem_of_forall_ne_top V hV
  refine ⟨g.val, ?_, g.property, (fun Z hZ => hg ⟨Z, hZ⟩), ?_⟩
  · have hU : U ≤ OAI.QuarticPowerFree.totalSpace L := by
      apply Submodule.span_le.mpr
      intro f hf
      exact OAI.QuarticPowerFree.mem_totalSpace.mpr (hdegree f hf)
    exact OAI.QuarticPowerFree.mem_totalSpace.mp (hU g.property)
  · intro x hx
    have hU : U ≤ (MvPolynomial.aeval x).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      intro f hf
      exact hx f hf
    exact hU g.property

end
end DistinctDistances.TrackD
