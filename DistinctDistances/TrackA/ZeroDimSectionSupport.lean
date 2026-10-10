import DistinctDistances.TrackA.ProjectiveSectionSupport
import DistinctDistances.TrackA.RegularSectionConstantSupport
import DistinctDistances.TrackA.ProjectiveChartSupport
import DistinctDistances.TrackA.ProjectiveChartRankSupport
import DistinctDistances.TrackA.ADepthAux

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ProjectiveLinearForms (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin n) ℂ 1

private def projectiveLinearFormEval {n : ℕ} (x : Point n) :
    ProjectiveLinearForms n →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval x).toLinearMap.comp
    (MvPolynomial.homogeneousSubmodule (Fin n) ℂ 1).subtype

@[simp] private theorem projectiveLinearFormEval_apply {n : ℕ} (x : Point n)
    (ℓ : ProjectiveLinearForms n) :
    projectiveLinearFormEval x ℓ = MvPolynomial.eval x ℓ.val := by
  simp [projectiveLinearFormEval, MvPolynomial.aeval_eq_eval]

private theorem projectiveLinearFormEval_ker_ne_top {n : ℕ} (x : Point n) (hx : x ≠ 0) :
    LinearMap.ker (projectiveLinearFormEval x) ≠ ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    have hall : ∀ i : Fin n, x i = 0 := by
      intro i
      by_contra hxi
      exact h ⟨i, hxi⟩
    exact hx (funext hall)
  let f : ProjectiveLinearForms n :=
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩
  have hf : f ∉ LinearMap.ker (projectiveLinearFormEval x) := by
    intro h
    have hzero := LinearMap.mem_ker.mp h
    have hxi : x i = 0 := by
      simpa [f] using hzero
    exact hi hxi
  intro htop
  have hmem : f ∈ LinearMap.ker (projectiveLinearFormEval x) := by
    rw [htop]
    exact Submodule.mem_top
  exact hf hmem

/-- An irreducible zero-dimensional projective variety has at most one
projective point. Normalize any two proposed points in a linear chart; its
affine slice is an irreducible zero-dimensional affine variety. -/
theorem projective_zeroDim_points_subsingleton {n : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (hdim : V.dimension = 0) : V.points.Subsingleton := by
  intro p hp q hq
  let bad : Fin 2 → Submodule ℂ (ProjectiveLinearForms n) := fun i =>
    if i = 0 then LinearMap.ker (projectiveLinearFormEval p.rep)
    else LinearMap.ker (projectiveLinearFormEval q.rep)
  have hbad : ∀ i, bad i ≠ ⊤ := by
    intro i
    fin_cases i
    · simpa [bad] using projectiveLinearFormEval_ker_ne_top p.rep p.rep_nonzero
    · simpa [bad] using projectiveLinearFormEval_ker_ne_top q.rep q.rep_nonzero
  obtain ⟨ℓ, hℓ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  have hℓp : MvPolynomial.eval p.rep ℓ.val ≠ 0 := by
    intro hz
    have hmem : ℓ ∈ LinearMap.ker (projectiveLinearFormEval p.rep) := by
      apply LinearMap.mem_ker.mpr
      simpa only [projectiveLinearFormEval_apply] using hz
    exact hℓ 0 (by simpa [bad] using hmem)
  have hℓq : MvPolynomial.eval q.rep ℓ.val ≠ 0 := by
    intro hz
    have hmem : ℓ ∈ LinearMap.ker (projectiveLinearFormEval q.rep) := by
      apply LinearMap.mem_ker.mpr
      simpa only [projectiveLinearFormEval_apply] using hz
    exact hℓ 1 (by simpa [bad] using hmem)
  have hpCone : p.rep ∈ V.affineCone.points :=
    (ProjectiveVariety.mem_points_mk_iff V p.rep p.rep_nonzero).mp (by simpa using hp)
  have hqCone : q.rep ∈ V.affineCone.points :=
    (ProjectiveVariety.mem_points_mk_iff V q.rep q.rep_nonzero).mp (by simpa using hq)
  have hℓV : ℓ.val ∉ V.ideal := by
    intro hmem
    exact hℓp (by simpa only [MvPolynomial.aeval_eq_eval] using hpCone ℓ.val hmem)
  let A := projectiveLinearSlice V ℓ.val
  have hAirr : A.IsIrreducible :=
    linearSlice_irreducible V hV ℓ.val ℓ.property hℓV
  have hAdim : A.dimension = 0 := by
    dsimp [A]
    rw [linearSlice_dimension V hV ℓ.val ℓ.property hℓV]
    exact hdim
  let cp : ℂ := (MvPolynomial.eval p.rep ℓ.val)⁻¹
  let cq : ℂ := (MvPolynomial.eval q.rep ℓ.val)⁻¹
  have hcp : cp ≠ 0 := inv_ne_zero hℓp
  have hcq : cq ≠ 0 := inv_ne_zero hℓq
  let yp : Point n := cp • p.rep
  let yq : Point n := cq • q.rep
  have hyp0 : yp ≠ 0 := smul_ne_zero hcp p.rep_nonzero
  have hyq0 : yq ≠ 0 := smul_ne_zero hcq q.rep_nonzero
  have hypA : yp ∈ A.points := by
    rw [linearSlice_points]
    refine ⟨cone_smul_mem V p.rep hpCone cp, ?_⟩
    change MvPolynomial.eval (cp • p.rep) ℓ.val = 1
    rw [Bridges.homogeneous_eval_smul ℓ.val ℓ.property]
    simp [cp, hℓp]
  have hyqA : yq ∈ A.points := by
    rw [linearSlice_points]
    refine ⟨cone_smul_mem V q.rep hqCone cq, ?_⟩
    change MvPolynomial.eval (cq • q.rep) ℓ.val = 1
    rw [Bridges.homogeneous_eval_smul ℓ.val ℓ.property]
    simp [cq, hℓq]
  obtain ⟨z, hAz, _⟩ := zeroDim_irreducible_data A hAirr hAdim
  have hypz : yp = z := by
    have hz : yp ∈ ({z} : Set (Point n)) := by rw [← hAz]; exact hypA
    exact Set.mem_singleton_iff.mp hz
  have hyqz : yq = z := by
    have hz : yq ∈ ({z} : Set (Point n)) := by rw [← hAz]; exact hyqA
    exact Set.mem_singleton_iff.mp hz
  have hpY : Projectivization.mk ℂ yp hyp0 = p := by
    calc
      Projectivization.mk ℂ yp hyp0 = Projectivization.mk ℂ p.rep p.rep_nonzero := by
        apply (Projectivization.mk_eq_mk_iff' ℂ yp p.rep hyp0 p.rep_nonzero).2
        exact ⟨cp, rfl⟩
      _ = p := by simp
  have hqY : Projectivization.mk ℂ yq hyq0 = q := by
    calc
      Projectivization.mk ℂ yq hyq0 = Projectivization.mk ℂ q.rep q.rep_nonzero := by
        apply (Projectivization.mk_eq_mk_iff' ℂ yq q.rep hyq0 q.rep_nonzero).2
        exact ⟨cq, rfl⟩
      _ = q := by simp
  have hypq : yp = yq := hypz.trans hyqz.symm
  have hprojYQ : Projectivization.mk ℂ yp hyp0 = Projectivization.mk ℂ yq hyq0 := by
    apply (Projectivization.mk_eq_mk_iff' ℂ yp yq hyp0 hyq0).2
    exact ⟨1, by simpa [hypq]⟩
  calc
    p = Projectivization.mk ℂ yp hyp0 := hpY.symm
    _ = Projectivization.mk ℂ yq hyq0 := hprojYQ
    _ = q := hqY

private def chosenProjectivePoint {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) (V : F) : ProjectivePoint n :=
  Classical.choose (ProjectiveFamily.irreducible_points_nonempty V.val (hF V.val V.property))

private theorem chosenProjectivePoint_mem {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) (V : F) : chosenProjectivePoint F hF V ∈ V.val.points :=
  Classical.choose_spec (ProjectiveFamily.irreducible_points_nonempty V.val (hF V.val V.property))

private def chosenProjectiveConePoint {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) (V : F) : NonzeroConePoint V.val := by
  let p := chosenProjectivePoint F hF V
  have hp := chosenProjectivePoint_mem F hF V
  exact ⟨p.rep, p.rep_nonzero,
    (ProjectiveVariety.mem_points_mk_iff V.val p.rep p.rep_nonzero).mp (by simpa using hp)⟩

/-- Evaluation at one representative per irreducible zero-fold component
detects every degree-D section; the degree-D scaling rule descends values
from every nonzero cone representative to the selected one. -/
theorem regularSection_zeroDim_evaluation {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ProjectiveFamily.IsPure F 0) (D : ℕ) :
    ∃ ev : regularSectionSpace (ProjectiveFamily.locus F) D →ₗ[ℂ] (F → ℂ),
      Function.Injective ev := by
  have hirr : ∀ V ∈ F, V.IsIrreducible := fun V hV => (hF V hV).1
  let pF : (V : F) → NonzeroConePoint (ProjectiveFamily.locus F) := fun V =>
    nonzeroConeInclusion (ProjectiveFamily.locus F) V.val
      (projective_family_member_subvariety F V.val V.property)
      (chosenProjectiveConePoint F hirr V)
  let ev : regularSectionSpace (ProjectiveFamily.locus F) D →ₗ[ℂ] (F → ℂ) :=
    LinearMap.pi (fun V => (LinearMap.proj (pF V)).comp
      (regularSectionSpace (ProjectiveFamily.locus F) D).subtype)
  refine ⟨ev, ?_⟩
  intro s t he
  apply Subtype.ext
  funext x
  have hpX : Projectivization.mk ℂ x.val x.property.1 ∈ (ProjectiveFamily.locus F).points :=
    (ProjectiveVariety.mem_points_mk_iff _ x.val x.property.1).2 x.property.2
  rw [ProjectiveFamily.points_locus] at hpX
  simp only [Set.mem_iUnion] at hpX
  obtain ⟨V, hV, hpXV⟩ := hpX
  let v : F := ⟨V, hV⟩
  let p := chosenProjectivePoint F hirr v
  have hpV : p ∈ V.points := chosenProjectivePoint_mem F hirr v
  have hpX' : Projectivization.mk ℂ x.val x.property.1 ∈ V.points := hpXV
  have hproj : Projectivization.mk ℂ x.val x.property.1 = p :=
    projective_zeroDim_points_subsingleton V (hirr V hV) (hF V hV).2 hpX' hpV
  have hproj' : Projectivization.mk ℂ x.val x.property.1 =
      Projectivization.mk ℂ p.rep p.rep_nonzero := by simpa using hproj
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ x.val p.rep x.property.1 p.rep_nonzero).mp hproj'
  have hcn : c ≠ 0 := by
    intro hczero
    apply x.property.1
    calc
      x.val = c • p.rep := hc.symm
      _ = 0 := by simp [hczero]
  have hxRep : nonzeroConeScale (ProjectiveFamily.locus F) c hcn (pF v) = x := by
    apply Subtype.ext
    change c • p.rep = x.val
    exact hc
  have hev : s.val (pF v) = t.val (pF v) := by
    have h := congrFun he v
    change s.val (pF v) = t.val (pF v) at h
    exact h
  have hs := regularSection_scaling (ProjectiveFamily.locus F) D s (pF v) c hcn
  have ht := regularSection_scaling (ProjectiveFamily.locus F) D t (pF v) c hcn
  calc
    s.val x = s.val (nonzeroConeScale (ProjectiveFamily.locus F) c hcn (pF v)) :=
      congrArg s.val hxRep.symm
    _ = c^D * s.val (pF v) := hs
    _ = c^D * t.val (pF v) := by rw [hev]
    _ = t.val (nonzeroConeScale (ProjectiveFamily.locus F) c hcn (pF v)) := ht.symm
    _ = t.val x := congrArg t.val hxRep

/-- The actual zero-fold section space is finite-dimensional because the
evaluation injection lands in a finite product, independently of any
numerical finrank bound. -/
theorem regularSection_zeroDim_finite {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ProjectiveFamily.IsPure F 0) (D : ℕ) :
    Module.Finite ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) := by
  obtain ⟨ev, hev⟩ := regularSection_zeroDim_evaluation F hF D
  exact Module.Finite.of_injective ev hev

theorem regularSection_zeroDim_le_card {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ProjectiveFamily.IsPure F 0) (D : ℕ) :
    Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) ≤ F.card := by
  obtain ⟨ev, hev⟩ := regularSection_zeroDim_evaluation F hF D
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
    LinearMap.finrank_le_finrank_of_injective hev

theorem projective_zeroDim_family_degree_eq_card {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ProjectiveFamily.IsPure F 0) :
    ProjectiveFamily.degree F = (F.card : ℚ) := by
  obtain ⟨ℓ, hℓ, havoid⟩ := exists_common_linear_chart F
    (fun V hV => (hF V hV).1)
  have hdegree (V : ProjectiveVariety n) (hV : V ∈ F) : V.degree = 1 := by
    let A := projectiveLinearSlice V ℓ
    have hAirr : A.IsIrreducible := linearSlice_irreducible V (hF V hV).1 ℓ hℓ (havoid V hV)
    have hAdim : A.dimension = 0 := by
      dsimp [A]
      rw [linearSlice_dimension V (hF V hV).1 ℓ hℓ (havoid V hV)]
      exact (hF V hV).2
    obtain ⟨_, _, hAdegree⟩ := zeroDim_irreducible_data A hAirr hAdim
    calc
      V.degree = A.degree := (linearSlice_degree V (hF V hV).1 ℓ hℓ (havoid V hV)).symm
      _ = 1 := hAdegree
  calc
    ProjectiveFamily.degree F = ∑ V ∈ F, (1 : ℚ) := by
      unfold ProjectiveFamily.degree
      apply Finset.sum_congr rfl
      intro V hV
      exact hdegree V hV
    _ = (F.card : ℚ) := by simp

/-- Numerical point-count bound for degree-D regular sections. -/
theorem regularSection_zeroDim_bound {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ProjectiveFamily.IsPure F 0) (D : ℕ) :
    (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) : ℚ) ≤
      ProjectiveFamily.degree F := by
  calc
    (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) : ℚ) ≤
        (F.card : ℚ) := by exact_mod_cast regularSection_zeroDim_le_card F hF D
    _ = ProjectiveFamily.degree F := (projective_zeroDim_family_degree_eq_card F hF).symm

end
end DistinctDistances.TrackA
