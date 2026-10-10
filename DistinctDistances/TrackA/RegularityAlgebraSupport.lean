import DistinctDistances.TrackA.Definitions
import OAI.NumberTheory.PowerFree.GenericCuts
import Mathlib.LinearAlgebra.Matrix.Rank

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- A finite list spans every bounded equation of the entire family. -/
theorem bounded_equation_list {n : ℕ} (F : AffineFamily.Family n) (D : ℕ) :
    ∃ E : List (Poly n),
      (∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal ∧ f.totalDegree ≤ D) ∧
      ∀ f : Poly n, f ∈ (AffineFamily.locus F).ideal → f.totalDegree ≤ D →
        f ∈ Submodule.span ℂ {f | f ∈ E} := by
  let U := OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) D ⊓
    (AffineFamily.locus F).ideal.restrictScalars ℂ
  letI := OAI.QuarticPowerFree.totalSpace_finite (n := n) (K := ℂ) D
  letI : FiniteDimensional ℂ U := FiniteDimensional.of_injective
    (Submodule.inclusion (show U ≤ OAI.QuarticPowerFree.totalSpace D from inf_le_left))
    (Submodule.inclusion_injective _)
  have hspan : Submodule.span ℂ (U : Set (Poly n)) = U := Submodule.span_eq U
  letI : FiniteDimensional ℂ (Submodule.span ℂ (U : Set (Poly n))) := hspan.symm ▸
    (inferInstance : FiniteDimensional ℂ U)
  obtain ⟨s, hs, _, hsp, _⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ
    (U : Set (Poly n))
  refine ⟨s.toList, ?_, ?_⟩
  · intro f hf
    have hU := hs (by simpa using hf)
    exact ⟨hU.2, OAI.QuarticPowerFree.mem_totalSpace.mp hU.1⟩
  · intro f hf hd
    have hU : f ∈ U := ⟨OAI.QuarticPowerFree.mem_totalSpace.mpr hd, hf⟩
    have he : {f : Poly n | f ∈ s.toList} = (s : Set (Poly n)) := by ext; simp
    rw [he, hsp, hspan]
    exact hU

def derivativeEvaluation {n : ℕ} (x v : Point n) : Poly n →ₗ[ℂ] ℂ :=
  ∑ i : Fin n, v i • ((MvPolynomial.aeval x).toLinearMap.comp
    (MvPolynomial.pderiv i).toLinearMap)

theorem derivativeEvaluation_apply {n : ℕ} (x v : Point n) (f : Poly n) :
    derivativeEvaluation x v f = differential f x v := by
  simp [derivativeEvaluation, differential, mul_comm]

def evaluatedJacobian {n : ℕ} (E : List (Poly n)) (x : Point n) :
    Matrix (Fin E.length) (Fin n) ℂ :=
  fun i j => MvPolynomial.eval x (jacobian E i j)

theorem evaluatedJacobian_kernel {n : ℕ} (F : AffineFamily.Family n)
    (D : ℕ) (E : List (Poly n))
    (hE : ∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal ∧ f.totalDegree ≤ D)
    (hspan : ∀ f : Poly n, f ∈ (AffineFamily.locus F).ideal → f.totalDegree ≤ D →
      f ∈ Submodule.span ℂ {f | f ∈ E}) (x : Point n) :
    LinearMap.ker (evaluatedJacobian E x).mulVecLin = boundedJacobianKernel F D x := by
  ext v
  have hmatrix : v ∈ LinearMap.ker (evaluatedJacobian E x).mulVecLin ↔
      ∀ f ∈ E, differential f x v = 0 := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff]
    have hget : (∀ i : Fin E.length, differential (E.get i) x v = 0) ↔
        ∀ f ∈ E, differential f x v = 0 := by
      constructor
      · intro h f hf
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hf
        exact h i
      · intro h i
        exact h _ (List.get_mem _ _)
    rw [← hget]
    simp [evaluatedJacobian, jacobian, Matrix.mulVec, dotProduct, differential,
      MvPolynomial.aeval_eq_eval]
  rw [hmatrix]
  change (∀ f ∈ E, differential f x v = 0) ↔
    v ∈ ⨅ f : {f : Poly n // f ∈ (AffineFamily.locus F).ideal ∧ f.totalDegree ≤ D},
      LinearMap.ker (differential f.val x)
  rw [Submodule.mem_iInf]
  constructor
  · intro hv f
    rw [LinearMap.mem_ker, ← derivativeEvaluation_apply]
    have hle : Submodule.span ℂ {f : Poly n | f ∈ E} ≤
        LinearMap.ker (derivativeEvaluation x v) := by
      apply Submodule.span_le.mpr
      intro f hf
      change derivativeEvaluation x v f = 0
      rw [derivativeEvaluation_apply]
      exact hv f hf
    exact hle (hspan f.val f.property.1 f.property.2)
  · intro hv f hf
    exact hv ⟨f, hE f hf⟩

/-- Rank selects an actual square minor, using the original OAI row selection. -/
theorem matrix_rank_minor {a n q : ℕ} (A : Matrix (Fin a) (Fin n) ℂ)
    (hrank : A.rank = q) :
    ∃ (rows : Fin q ↪ Fin a) (cols : Fin q ↪ Fin n),
      Matrix.det (A.submatrix rows cols) ≠ 0 := by
  obtain ⟨κ, r, hr, hspan, hli⟩ := exists_linearIndependent' ℂ A.row
  letI := Fintype.ofInjective r hr
  have hcard : Fintype.card κ = q := by
    rw [← hrank, Matrix.rank_eq_finrank_span_row, ← hspan,
      finrank_span_eq_card hli]
  let e : Fin q ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let rows : Fin q ↪ Fin a := ⟨r ∘ e, hr.comp e.injective⟩
  let B : Matrix (Fin q) (Fin n) ℂ := A.submatrix rows id
  have hBli : LinearIndependent ℂ B.row := hli.comp e e.injective
  have hB : B.rank = q := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hBli]
    simp
  have htop : Submodule.span ℂ (Set.range B.transpose.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, Matrix.rank_transpose, hB]
    simp
  obtain ⟨c, hc, hdet⟩ := OAI.QuarticPowerFree.exists_nonsingular_rows_of_span_eq_top
    B.transpose htop
  refine ⟨rows, ⟨c, hc⟩, ?_⟩
  have heq : (fun i j => B.transpose (c i) j) = (A.submatrix rows c).transpose := rfl
  rw [heq, Matrix.det_transpose] at hdet
  exact hdet

theorem generic_rank_detected_by_minor {n : ℕ} (F : AffineFamily.Family n)
    (V : AffineVariety n) (k D : ℕ) (hk : k ≤ n)
    (E : List (Poly n))
    (hE : ∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal ∧ f.totalDegree ≤ D)
    (hspan : ∀ f : Poly n, f ∈ (AffineFamily.locus F).ideal → f.totalDegree ≤ D →
      f ∈ Submodule.span ℂ {f | f ∈ E}) (hrank : GenericJacobianRank F V D k) :
    ∃ m ∈ jacobianMinors E (n-k), m ∉ V.ideal := by
  obtain ⟨g, hg, hgeneric⟩ := hrank
  have hex : ∃ x ∈ V.points, MvPolynomial.eval x g ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hg
    rw [← V.vanishingIdeal_points]
    intro x hx
    simpa [MvPolynomial.aeval_eq_eval] using hn x hx
  obtain ⟨x, hx, hxg⟩ := hex
  have hdim := hgeneric x hx hxg
  let A := evaluatedJacobian E x
  have hA : A.rank = n-k := by
    have he := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    change A.rank + Module.finrank ℂ (LinearMap.ker A.mulVecLin) =
      Module.finrank ℂ (Point n) at he
    rw [evaluatedJacobian_kernel F D E hE hspan x, hdim] at he
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
    omega
  obtain ⟨rows, cols, hdet⟩ := matrix_rank_minor A hA
  let m := Matrix.det ((jacobian E).submatrix rows cols)
  have hmeval : MvPolynomial.eval x m ≠ 0 := by
    have he : (MvPolynomial.eval x).mapMatrix ((jacobian E).submatrix rows cols) =
        A.submatrix rows cols := by ext i j; rfl
    change MvPolynomial.eval x ((jacobian E).submatrix rows cols).det ≠ 0
    rw [(MvPolynomial.eval x).map_det, he]
    exact hdet
  refine ⟨m, ⟨rows, cols, rfl⟩, ?_⟩
  intro hm
  apply hmeval
  have hz := (MvPolynomial.mem_zeroLocus_iff.mp hx) m hm
  simpa [MvPolynomial.aeval_eq_eval] using hz

theorem jacobian_minor_totalDegree {n : ℕ} (E : List (Poly n)) (D q : ℕ)
    (hE : ∀ f ∈ E, f.totalDegree ≤ D) (m : Poly n) (hm : m ∈ jacobianMinors E q) :
    m.totalDegree ≤ q*(D-1) := by
  obtain ⟨rows, cols, rfl⟩ := hm
  have h := OAI.QuarticPowerFree.jacobian_minor_degree
    (fun i : Fin q => E.get (rows i)) cols D
    (fun i => hE _ (List.get_mem _ _))
  have he : (jacobian E).submatrix rows cols =
      (fun i j => MvPolynomial.pderiv (cols j) (E.get (rows i)) :
        Matrix (Fin q) (Fin q) (Poly n)) := by ext i j; rfl
  rw [he]
  simpa only [Fintype.card_fin] using h

/-- Finite avoidance takes place inside the space of the actual minors. -/
theorem choose_jacobian_certificate {n : ℕ} (good : AffineFamily.Family n)
    (E : List (Poly n)) (k D : ℕ) (hk : k ≤ n)
    (hE : ∀ f ∈ E, f.totalDegree ≤ D)
    (hwitness : ∀ V ∈ good, ∃ m ∈ jacobianMinors E (n-k), m ∉ V.ideal) :
    ∃ g : Poly n, g.totalDegree ≤ n*D ∧
      g ∈ Submodule.span ℂ (jacobianMinors E (n-k)) ∧ ∀ V ∈ good, g ∉ V.ideal := by
  let U := Submodule.span ℂ (jacobianMinors E (n-k))
  let bad (V : good) : Submodule ℂ U := (V.val.ideal.restrictScalars ℂ).comap U.subtype
  have hbad (V : good) : bad V ≠ ⊤ := by
    obtain ⟨m, hm, hnot⟩ := hwitness V.val V.property
    let mU : U := ⟨m, Submodule.subset_span hm⟩
    intro he
    have hmem : mU ∈ bad V := he.symm ▸ Submodule.mem_top
    exact hnot hmem
  obtain ⟨g, hg⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  have hle : U ≤ OAI.QuarticPowerFree.totalSpace (n*D) := by
    apply Submodule.span_le.mpr
    intro m hm
    apply OAI.QuarticPowerFree.mem_totalSpace.mpr
    exact (jacobian_minor_totalDegree E D (n-k) hE m hm).trans
      (Nat.mul_le_mul (Nat.sub_le n k) (Nat.sub_le D 1))
  exact ⟨g.val, OAI.QuarticPowerFree.mem_totalSpace.mp (hle g.property),
    g.property, fun V hV => hg ⟨V, hV⟩⟩

theorem nonzero_certificate_detects_minor {n : ℕ} (E : List (Poly n)) (q : ℕ)
    (g : Poly n) (hg : g ∈ Submodule.span ℂ (jacobianMinors E q))
    (x : Point n) (hxg : MvPolynomial.eval x g ≠ 0) :
    ∃ m ∈ jacobianMinors E q, MvPolynomial.eval x m ≠ 0 := by
  by_contra hn
  push Not at hn
  have hle : Submodule.span ℂ (jacobianMinors E q) ≤
      LinearMap.ker (MvPolynomial.aeval x).toLinearMap := by
    apply Submodule.span_le.mpr
    intro m hm
    change MvPolynomial.aeval x m = 0
    simpa [MvPolynomial.aeval_eq_eval] using hn m hm
  apply hxg
  simpa [LinearMap.mem_ker, MvPolynomial.aeval_eq_eval] using hle hg

end
end DistinctDistances.TrackA
