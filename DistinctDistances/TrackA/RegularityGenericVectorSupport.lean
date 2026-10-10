import DistinctDistances.TrackA.RegularityAlgebraSupport
import DistinctDistances.TrackA.RegularityBaseSupport
import DistinctDistances.TrackA.Requests

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- A minor of any size up to the rank over the actual fiber field. -/
theorem regularity_matrix_le_rank_minor {a n q : ℕ} {Ω : Type*} [Field Ω]
    (A : Matrix (Fin a) (Fin n) Ω) (hrank : q ≤ A.rank) :
    ∃ (rows : Fin q ↪ Fin a) (cols : Fin q ↪ Fin n),
      Matrix.det (A.submatrix rows cols) ≠ 0 := by
  obtain ⟨κ, r, hr, hspan, hli⟩ := exists_linearIndependent' Ω A.row
  letI := Fintype.ofInjective r hr
  have hcard : Fintype.card κ = A.rank := by
    rw [Matrix.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  let e : Fin A.rank ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let rows : Fin q ↪ Fin a :=
    ⟨fun i => r (e (Fin.castLE hrank i)), hr.comp (e.injective.comp (Fin.castLE_injective _))⟩
  let B : Matrix (Fin q) (Fin n) Ω := A.submatrix rows id
  have hBli : LinearIndependent Ω B.row :=
    (hli.comp e e.injective).comp (Fin.castLE hrank) (Fin.castLE_injective _)
  have hB : B.rank = q := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hBli]
    simp
  have htop : Submodule.span Ω (Set.range B.transpose.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, Matrix.rank_transpose, hB]
    simp
  obtain ⟨c, hc, hdet⟩ := OAI.QuarticPowerFree.exists_nonsingular_rows_of_span_eq_top
    B.transpose htop
  refine ⟨rows, ⟨c, hc⟩, ?_⟩
  have heq : (fun i j => B.transpose (c i) j) = (A.submatrix rows c).transpose := rfl
  rw [heq, Matrix.det_transpose] at hdet
  exact hdet

/-- Converse minor certificate. The frozen germ theorem supplies the
lower tangent dimension; the minor supplies the upper kernel dimension. -/
theorem regularity_generic_rank_of_minor {n : ℕ} (F : AffineFamily.Family n)
    (V : AffineVariety n) (hV : V ∈ F) (k D : ℕ) (hk : k ≤ n)
    (hF : AffineFamily.IsPure F k) (E : List (Poly n))
    (hE : ∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal ∧ f.totalDegree ≤ D)
    (hspan : ∀ f : Poly n, f ∈ (AffineFamily.locus F).ideal → f.totalDegree ≤ D →
      f ∈ Submodule.span ℂ {f | f ∈ E})
    (m : Poly n) (hm : m ∈ jacobianMinors E (n-k)) (hnot : m ∉ V.ideal) :
    GenericJacobianRank F V D k := by
  refine ⟨m, hnot, ?_⟩
  intro x hx hxg
  have hxf : x ∈ (AffineFamily.locus F).points :=
    fun f hf => hx f (affineFamily_locus_ideal_le F V hV hf)
  obtain ⟨_, hsmooth, hlocal, _⟩ := request_pure_family_jacobian_germ F k hk hF E
    (fun f hf => (hE f hf).1) x hxf ⟨m, hm, hxg⟩
  have htangent : (equationLocus E).tangentSpace x ≤ boundedJacobianKernel F D x := by
    intro v hv
    rw [boundedJacobianKernel, Submodule.mem_iInf]
    intro f
    have hspanle : Submodule.span ℂ {f : Poly n | f ∈ E} ≤
        (equationLocus E).ideal.restrictScalars ℂ := by
      apply Submodule.span_le.mpr
      intro p hp
      exact Ideal.le_radical (Ideal.subset_span hp)
    have hf : f.val ∈ (equationLocus E).ideal := hspanle (hspan _ f.property.1 f.property.2)
    change v ∈ ⨅ f : (equationLocus E).ideal, LinearMap.ker (differential f.val x) at hv
    rw [Submodule.mem_iInf] at hv
    exact hv ⟨f.val, hf⟩
  have hlow : k ≤ Module.finrank ℂ (boundedJacobianKernel F D x) := by
    have hdim : Module.finrank ℂ ((equationLocus E).tangentSpace x) = k :=
      hsmooth.2.trans hlocal
    rw [← hdim]
    exact Submodule.finrank_mono htangent
  obtain ⟨rows, cols, rfl⟩ := hm
  let A := evaluatedJacobian E x
  have hdet : (A.submatrix rows cols).det ≠ 0 := by
    have he : (MvPolynomial.eval x).mapMatrix ((jacobian E).submatrix rows cols) =
        A.submatrix rows cols := by ext i j; rfl
    rwa [(MvPolynomial.eval x).map_det, he] at hxg
  have hrank : n-k ≤ A.rank := by
    have h := Matrix.rank_submatrix_le A rows cols
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h
    exact h
  have hdim := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change A.rank + Module.finrank ℂ (LinearMap.ker A.mulVecLin) =
    Module.finrank ℂ (Point n) at hdim
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  have hlowker : k ≤ Module.finrank ℂ (LinearMap.ker A.mulVecLin) := by
    rw [evaluatedJacobian_kernel F D E hE hspan x]
    exact hlow
  have heq : Module.finrank ℂ (LinearMap.ker A.mulVecLin) = k := by omega
  rwa [evaluatedJacobian_kernel F D E hE hspan x] at heq

/-- Rank failure at a generic sheet leaves a nonzero vector which kills
both bounded family equations and all base-coordinate differentials. -/
theorem regularity_bad_generic_sheet_vector {n k : ℕ} (F : AffineFamily.Family n)
    (hF : AffineFamily.IsPure F k) (hk : k ≤ n) (D : ℕ)
    (V : AffineVariety n) (hV : V ∈ F) (hbad : ¬ GenericJacobianRank F V D k)
    (φ : AffineProjection n k)
    (Ω : Type*) [Field Ω] [Algebra ℂ Ω] (t : Fin k → Ω)
    (x : affineFiberOver V φ t) :
    ∃ v : FieldPoint n Ω, v ≠ 0 ∧
      (∀ j, fieldDirectionalDerivative x.val v
        (MvPolynomial.map (algebraMap ℂ Ω) (φ.pullback (MvPolynomial.X j))) = 0) ∧
      ∀ f : Poly n, f ∈ (AffineFamily.locus F).ideal → f.totalDegree ≤ D →
        fieldDirectionalDerivative x.val v (MvPolynomial.map (algebraMap ℂ Ω) f) = 0 := by
  obtain ⟨E, hE, hspan⟩ := bounded_equation_list F D
  let A : Matrix (Fin E.length) (Fin n) Ω :=
    fun i j => MvPolynomial.aeval x.val (MvPolynomial.pderiv j (E.get i))
  have hrank : A.rank < n-k := by
    by_contra h
    have hge : n-k ≤ A.rank := Nat.le_of_not_gt h
    obtain ⟨rows, cols, hdet⟩ := regularity_matrix_le_rank_minor A hge
    let m := ((jacobian E).submatrix rows cols).det
    have hm : m ∈ jacobianMinors E (n-k) := ⟨rows, cols, rfl⟩
    have hmeval : MvPolynomial.aeval x.val m ≠ 0 := by
      have he : MvPolynomial.aeval x.val m = (A.submatrix rows cols).det :=
        OAI.QuarticPowerFree.aeval_jacobian_det x.val cols (fun i => E.get (rows i))
      rw [he]
      exact hdet
    have hnot : m ∉ V.ideal := by
      intro hmV
      exact hmeval (x.property.1 m hmV)
    exact hbad (regularity_generic_rank_of_minor F V hV k D hk hF E hE hspan m hm hnot)
  let B : (Fin n → Ω) →ₗ[Ω] (Fin k → Ω) := LinearMap.pi
    (fun j => ∑ i : Fin n,
      MvPolynomial.aeval x.val (MvPolynomial.pderiv i (φ.pullback (MvPolynomial.X j))) •
        LinearMap.proj i)
  have hA := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hB := LinearMap.finrank_range_add_finrank_ker B
  have hBrange : Module.finrank Ω (LinearMap.range B) ≤ k := by
    simpa using Submodule.finrank_le (LinearMap.range B)
  have hinf : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B ≠ ⊥ := by
    intro hzero
    have hdis : Disjoint (LinearMap.ker A.mulVecLin) (LinearMap.ker B) :=
      disjoint_iff.mpr hzero
    have hdim := Submodule.finrank_add_finrank_le_of_disjoint hdis
    change A.rank + _ = _ at hA
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hA hB hdim
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  refine ⟨v, hv0, ?_, ?_⟩
  · intro j
    have hvB := congrFun (LinearMap.mem_ker.mp hv.2) j
    rw [fieldDirectionalDerivative_map]
    simpa only [B, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, mul_comm, Pi.zero_apply] using hvB
  · intro f hf hd
    let T : Poly n →ₗ[ℂ] Ω :=
      ((fieldDirectionalDerivative x.val v).restrictScalars ℂ).comp
        (MvPolynomial.mapAlgHom (Algebra.ofId ℂ Ω)).toLinearMap
    have hzero : ∀ i : Fin E.length, T (E.get i) = 0 := by
      intro i
      have hi := congrFun (LinearMap.mem_ker.mp hv.1) i
      change fieldDirectionalDerivative x.val v (MvPolynomial.map (algebraMap ℂ Ω) (E.get i)) = 0
      rw [fieldDirectionalDerivative_map]
      change (∑ j, A i j * v j) = 0 at hi
      simpa only [A, mul_comm] using hi
    have hle : Submodule.span ℂ {f : Poly n | f ∈ E} ≤ LinearMap.ker T := by
      apply Submodule.span_le.mpr
      intro f hf
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hf
      exact hzero i
    exact hle (hspan f hf hd)

end
end DistinctDistances.TrackA
