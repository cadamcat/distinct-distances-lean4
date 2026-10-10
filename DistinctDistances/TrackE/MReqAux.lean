import DistinctDistances.TrackA.CommonRadialSourceOpenSupport
import DistinctDistances.TrackA.AffineCutHilbertSupport
import DistinctDistances.Foundations.Projection
import DistinctDistances.Foundations.Projective
import DistinctDistances.Foundations.Affine
import DistinctDistances.Foundations.Local
import DistinctDistances.Foundations.PointLocal
import DistinctDistances.TrackD.Profiles.JacobianGeometry
import DistinctDistances.TrackA.LocalTangentSupport
import DistinctDistances.TrackA.PoolingSupport
import DistinctDistances.TrackA.ADepthAux
import DistinctDistances.TrackA.Requests

/-! Helpers for lane `m-req` (track E requests to track A).

Only Foundations/TrackA/OAI material: no TrackE imports (no cycles).
Owned Request files import this module for the lemmas below.
-/

namespace DistinctDistances.MReqAux

open scoped Classical BigOperators Matrix

noncomputable section

/-- Each radial coordinate `X i - C (p i)` has total degree at most one. -/
theorem radialCoordinate_totalDegree_le {n : ℕ} (p : Point n) (i : Fin n) :
    (TrackA.radialCoordinate p i).totalDegree ≤ 1 := by
  unfold TrackA.radialCoordinate
  calc (MvPolynomial.X i - MvPolynomial.C (p i) : Poly n).totalDegree
      ≤ max (MvPolynomial.X i : Poly n).totalDegree
        (MvPolynomial.C (p i) : Poly n).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ 1 := by simp

/-- The radial pullback `g(X) = f(X - p)` does not raise total degree. -/
theorem radialDirectionPullback_totalDegree_le {n : ℕ} (p : Point n) (f : Poly n) :
    (TrackA.radialDirectionPullback p f).totalDegree ≤ f.totalDegree := by
  unfold TrackA.radialDirectionPullback
  exact OAI.QuarticPowerFree.totalDegree_linear_substitute_le _
    (fun i => radialCoordinate_totalDegree_le p i) _

/-- The finite intersection of a projective family's ideals lies in its locus ideal. -/
theorem projective_biInf_le_locus {d : ℕ} (F : ProjectiveFamily.Family d) :
    (⨅ C ∈ F, C.ideal) ≤ (ProjectiveFamily.locus F).ideal := by
  intro f hf
  have hfC : ∀ C : ProjectiveVariety d, C ∈ F → f ∈ C.ideal := by
    simpa only [Ideal.mem_iInf] using hf
  rw [← (ProjectiveFamily.locus F).vanishingIdeal_points]
  show f ∈ MvPolynomial.vanishingIdeal ℂ _
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro v ⟨hv0, hpL⟩
  have hpU : Projectivization.mk ℂ v hv0 ∈ ⋃ C ∈ F, C.points := by
    rwa [ProjectiveFamily.points_locus] at hpL
  simp only [Set.mem_iUnion] at hpU
  obtain ⟨C, hCF, hCp⟩ := hpU
  have hcone : v ∈ C.affineCone.points :=
    (ProjectiveVariety.mem_points_mk_iff C v hv0).mp hCp
  exact MvPolynomial.mem_zeroLocus_iff.mp hcone f (hfC C hCF)

/-- Prime avoidance for a finite projective family: a prime containing the
finite intersection contains one member. -/
theorem exists_projective_ideal_le_of_biInf_le {d : ℕ}
    (F : ProjectiveFamily.Family d) (W : ProjectiveVariety d)
    (hW : W.IsIrreducible) (hle : (⨅ C ∈ F, C.ideal) ≤ W.ideal) :
    ∃ C ∈ F, C.ideal ≤ W.ideal := by
  classical
  by_contra hcon
  push_neg at hcon
  have hwit : ∀ C : ProjectiveVariety d, ∃ f : Poly d,
      (C ∈ F → f ∈ C.ideal ∧ f ∉ W.ideal) ∧ (C ∉ F → f = 1) := by
    intro C
    by_cases hC : C ∈ F
    · have hle := hcon C hC
      have hex : ∃ f : Poly d, f ∈ C.ideal ∧ f ∉ W.ideal := by
        by_contra hcon2
        push_neg at hcon2
        exact hle (fun f hf => hcon2 f hf)
      obtain ⟨f, hfC, hfnW⟩ := hex
      exact ⟨f, fun _ => ⟨hfC, hfnW⟩, fun hn => (hn hC).elim⟩
    · exact ⟨1, fun hm => (hC hm).elim, fun _ => rfl⟩
  choose wit hwitC hwit1 using hwit
  have hmem : ∀ C ∈ F, wit C ∈ C.ideal := fun C hC => ((hwitC C) hC).1
  have hnot : ∀ C ∈ F, wit C ∉ W.ideal := fun C hC => ((hwitC C) hC).2
  have hgInf : (∏ C ∈ F, wit C) ∈ (⨅ C ∈ F, C.ideal) := by
    simp only [Ideal.mem_iInf]
    intro C hC
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem wit hC
    rw [hr, mul_comm, ← smul_eq_mul]
    exact Submodule.smul_mem _ _ (hmem C hC)
  have hgW : (∏ C ∈ F, wit C) ∈ W.ideal := hle hgInf
  have key : ∀ s : Finset (ProjectiveVariety d),
      (∏ C ∈ s, wit C) ∈ W.ideal → ∃ C0 ∈ s, wit C0 ∈ W.ideal := by
    intro s
    induction s using Finset.induction
    case empty =>
      intro h
      rw [Finset.prod_empty] at h
      exact (hW.ne_top ((Ideal.eq_top_iff_one W.ideal).mpr h)).elim
    case insert a s has ih =>
      intro h
      rw [Finset.prod_insert has] at h
      rcases hW.mem_or_mem h with ha | hs
      · exact ⟨a, Finset.mem_insert_self a s, ha⟩
      · obtain ⟨C0, hC0, hC0W⟩ := ih hs
        exact ⟨C0, Finset.mem_insert_of_mem hC0, hC0W⟩
  obtain ⟨C0, hC0, hC0W⟩ := key F hgW
  exact hnot C0 hC0 hC0W

/-- Inclusion of projective ideals gives inclusion of affine-cone dimensions. -/
theorem projective_cone_dimension_mono {d : ℕ} (C W : ProjectiveVariety d)
    (h : C.ideal ≤ W.ideal) : (W.affineCone).dimension ≤ (C.affineCone).dimension := by
  have hmono := TrackA.affine_hilbert_degree_mono C.ideal W.ideal h
  have eW : (W.affineCone).dimension =
      (OAI.QuarticPowerFree.coordinateHilbert W.ideal).natDegree := rfl
  have eC : (C.affineCone).dimension =
      (OAI.QuarticPowerFree.coordinateHilbert C.ideal).natDegree := rfl
  rw [eW, eC]
  exact hmono

/-- Equal cone dimensions force equal prime ideals. -/
theorem projective_ideal_eq_of_cone_dim_eq {d : ℕ} (C W : ProjectiveVariety d)
    (hC : C.IsIrreducible) (hW : W.IsIrreducible)
    (hle : C.ideal ≤ W.ideal)
    (hdim : (W.affineCone).dimension = (C.affineCone).dimension) :
    C.ideal = W.ideal := by
  haveI : C.ideal.IsPrime := hC
  haveI : W.ideal.IsPrime := hW
  have hCk : OAI.QuarticPowerFree.affineDimension C.ideal = (C.affineCone).dimension :=
    rfl
  have hW0 : OAI.QuarticPowerFree.affineDimension W.ideal = (W.affineCone).dimension :=
    rfl
  rw [hdim] at hW0
  exact AffineFamily.prime_same_dimension_eq_of_le C.ideal W.ideal hle hCk hW0

/-- Square bridge: independent rows force a nonzero determinant. -/
theorem det_ne_zero_of_linearIndependent_rows {r : ℕ} (S : Matrix (Fin r) (Fin r) ℂ)
    (h : LinearIndependent ℂ S.row) : S.det ≠ 0 := by
  classical
  by_contra h0
  obtain ⟨v, hv0, hvrel⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hrel : ∑ j, v j • S.row j = 0 := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    show (∑ j, v j * S j k) = 0
    rw [← Matrix.vecMul_apply_eq_sum, hvrel]
    rfl
  have hdep : ¬ LinearIndependent ℂ S.row := by
    rw [Fintype.not_linearIndependent_iff]
    exact ⟨v, hrel, i, by simpa using hi⟩
  exact hdep h

/-- Independent index selection from a finite spanning family. -/
theorem exists_independent_index_select {m : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (v : Fin m → V) (r : ℕ)
    (hr : Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = r) :
    ∃ a : Fin r → Fin m, LinearIndependent ℂ (v ∘ a) := by
  classical
  haveI := Module.Finite.span_of_finite ℂ (Set.finite_range v)
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range v)
  rw [hr] at hex
  obtain ⟨g, hgmem, _, hgind⟩ := hex
  choose a ha using (fun i => Set.mem_range.mp (hgmem i))
  refine ⟨a, ?_⟩
  have hga : v ∘ a = g := funext ha
  rwa [hga]

/-- A rank-`r` complex matrix has an `r × r` nonsingular submatrix. -/
theorem exists_nonsingular_submatrix_of_rank {m d : ℕ} (M : Matrix (Fin m) (Fin d) ℂ)
    (r : ℕ) (hrank : M.rank = r) :
    ∃ (rows : Fin r → Fin m) (cols : Fin r ↪ Fin d),
      Matrix.det (M.submatrix rows cols) ≠ 0 := by
  classical
  have hspan_row : Module.finrank ℂ (Submodule.span ℂ (Set.range (Mᵀ).col)) = r := by
    rw [← Matrix.range_mulVecLin]
    calc Module.finrank ℂ (LinearMap.range (Mᵀ).mulVecLin) = (Mᵀ).rank := rfl
      _ = M.rank := Matrix.rank_transpose M
      _ = r := hrank
  obtain ⟨rows, hrows_ind⟩ := exists_independent_index_select ((Mᵀ).col) r hspan_row
  set N : Matrix (Fin r) (Fin d) ℂ := M.submatrix rows (fun j => j) with hN
  have hNrow : N.row = (Mᵀ).col ∘ rows := by
    rw [hN]
    rfl
  have hNind : LinearIndependent ℂ N.row := by
    rw [hNrow]
    exact hrows_ind
  have hNrank : N.rank = r := by
    have h := hNind.rank_matrix
    simpa using h
  have hspan_col : Module.finrank ℂ (Submodule.span ℂ (Set.range (Nᵀ).row)) = r := by
    rw [Matrix.row_transpose, ← Matrix.range_mulVecLin]
    calc Module.finrank ℂ (LinearMap.range N.mulVecLin) = N.rank := rfl
      _ = r := hNrank
  obtain ⟨b, hb_ind⟩ := exists_independent_index_select ((Nᵀ).row) r hspan_col
  have hb_inj : Function.Injective b := by
    intro i₁ i₂ h12
    apply hb_ind.injective
    exact congrArg (Nᵀ).row h12
  set cols : Fin r ↪ Fin d := ⟨b, hb_inj⟩ with hcols
  refine ⟨rows, cols, ?_⟩
  have hSTind : LinearIndependent ℂ ((M.submatrix rows cols)ᵀ).row := by
    have hST : ((M.submatrix rows cols)ᵀ).row = (Nᵀ).row ∘ b := by
      rw [hN]
      rfl
    rw [hST]
    exact hb_ind
  have hdetT := det_ne_zero_of_linearIndependent_rows _ hSTind
  rwa [Matrix.det_transpose] at hdetT

/-- Smoothness and local dimension transfer from an irreducible carrier to the
equation locus with the same tangent kernel (`Request.smooth_equation_locus_of_carrier`). -/
theorem smooth_locus_of_tangent_kernel {d : ℕ} (F : Finset (Poly d))
    (Z : AffineVariety d) (q : Point d) (hZ : Z.IsIrreducible)
    (hq : q ∈ Z) (hsmooth : Z.IsSmoothAt q)
    (hF : ∀ f ∈ F, f ∈ Z.ideal) (hker : Z.tangentSpace q = TrackD.jacKer F q) :
    (AffineVariety.ofIdeal (Ideal.span (F : Set (Poly d)))).IsSmoothAt q ∧
      (AffineVariety.ofIdeal (Ideal.span (F : Set (Poly d)))).localDimension q =
        Z.localDimension q := by
  classical
  set W : AffineVariety d := AffineVariety.ofIdeal (Ideal.span (F : Set (Poly d))) with hW
  obtain ⟨hqmem, hfin⟩ := hsmooth
  have hdimloc : Z.localDimension q = Z.dimension :=
    AffineVariety.localDimension_eq_dimension Z q hZ hq
  have hkle : Z.dimension ≤ d := TrackA.pooling_dimension_le_ambient Z hZ
  set E : List (Poly d) := F.toList with hE
  have hEF : E.toFinset = F := by
    rw [hE]
    exact Finset.toList_toFinset F
  have hkerM : LinearMap.ker (TrackD.evaluatedJacobian E q).mulVecLin =
      TrackD.jacKer F q := by
    rw [← hEF]
    exact TrackD.evaluatedJacobian_kernel E q
  have hfinJ : Module.finrank ℂ (TrackD.jacKer F q) = Z.dimension := by
    rw [← hker, ← hdimloc]
    exact hfin
  have hrank : (TrackD.evaluatedJacobian E q).rank = d - Z.dimension := by
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (TrackD.evaluatedJacobian E q).mulVecLin
    rw [hkerM, hfinJ] at hrn
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
    show Module.finrank ℂ
      (LinearMap.range (TrackD.evaluatedJacobian E q).mulVecLin) = _
    omega
  obtain ⟨rows, cols, hdet⟩ := exists_nonsingular_submatrix_of_rank
    (TrackD.evaluatedJacobian E q) (d - Z.dimension) hrank
  set f : Fin (d - Z.dimension) → Poly d := fun i => E.get (rows i) with hf_def
  have hfinF : ∀ i, f i ∈ (F : Set (Poly d)) := by
    intro i
    rw [hf_def]
    show E.get (rows i) ∈ (F : Set (Poly d))
    rw [← hEF, Finset.mem_coe]
    exact List.mem_toFinset.mpr (List.get_mem E (rows i))
  have hfmem : ∀ i, f i ∈ Z.ideal := fun i => hF _ (Finset.mem_coe.mp (hfinF i))
  have hdet' : Matrix.det
      (fun i j => MvPolynomial.eval q (MvPolynomial.pderiv (cols j) (f i))) ≠ 0 := by
    show Matrix.det
      (fun i j => MvPolynomial.eval q (MvPolynomial.pderiv (cols j) (E.get (rows i)))) ≠ 0
    exact hdet
  have hloc : localizedIdeal Z.ideal q =
      localizedIdeal (Ideal.span (Set.range f)) q :=
    TrackA.request_irreducible_local_jacobian_ideal Z.dimension hkle Z hZ rfl q hq
      f cols hfmem hdet'
  have hspan_le : Ideal.span (Set.range f) ≤ Ideal.span (F : Set (Poly d)) :=
    Ideal.span_mono (by rintro p ⟨i, rfl⟩; exact hfinF i)
  have hWideal : W.ideal = (Ideal.span (F : Set (Poly d))).radical := by
    rw [hW]
    rfl
  have hWZ : W.ideal ≤ Z.ideal := by
    rw [hWideal]
    calc (Ideal.span (F : Set (Poly d))).radical ≤ Z.ideal.radical :=
          Ideal.radical_mono
            (Ideal.span_le.mpr (fun p hp => hF p (Finset.mem_coe.mp hp)))
      _ = Z.ideal := Z.isRadical.radical
  have hqW : q ∈ W.points := MvPolynomial.zeroLocus_anti_mono hWZ hq
  have hlocW : localizedIdeal W.ideal q = localizedIdeal Z.ideal q := by
    apply le_antisymm
    · exact Ideal.map_mono hWZ
    · calc localizedIdeal Z.ideal q
          = localizedIdeal (Ideal.span (Set.range f)) q := hloc
        _ ≤ localizedIdeal (Ideal.span (F : Set (Poly d))) q :=
            Ideal.map_mono hspan_le
        _ ≤ localizedIdeal W.ideal q := by
            apply Ideal.map_mono
            rw [hWideal]
            exact Ideal.le_radical
  have hdimW : W.localDimension q = Z.localDimension q :=
    TrackA.localDimension_eq_of_localizedIdeal_eq W Z q hlocW
  have htanW : W.tangentSpace q = Z.tangentSpace q :=
    TrackA.tangentSpace_eq_of_localizedIdeal_eq W Z q hqW hq hlocW
  refine ⟨⟨hqW, ?_⟩, hdimW⟩
  rw [htanW, hdimW]
  exact hfin

/-- Injection of the linear equations on the original tangent isolates a point
of the whole equation ideal (`Request.common_linear_section_isolated`).
Zero tangent forces every intermediate prime to be zero-dimensional, hence the
point ideal, via the tangent-dimension bound and zero-dimensional rigidity. -/
theorem linear_section_isolated_of_tangent_inj {d k : ℕ}
    (Z : AffineVariety (d + d)) (hZ : Z.IsIrreducible)
    (E : Fin (2 * k) → Poly (d + d)) (hlin : ∀ i, (E i).totalDegree ≤ 1)
    (z : Point (d + d)) (hz : z ∈ Z)
    (hzero : ∀ i, MvPolynomial.eval z (E i) = 0)
    (hinj : Function.Injective ((LinearMap.pi (fun i => differential (E i) z)).domRestrict
      (Z.tangentSpace z))) :
    pointIdeal z ∈ (Z.ideal ⊔ Ideal.span (Set.range E)).minimalPrimes := by
  classical
  have hPprime : (pointIdeal z).IsPrime := (pointIdeal_isMaximal z).isPrime
  have hZle : Z.ideal ≤ pointIdeal z := AffineVariety.ideal_le_pointIdeal_of_mem hz
  have hEle : Ideal.span (Set.range E) ≤ pointIdeal z := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    show E i ∈ MvPolynomial.vanishingIdeal ℂ {z}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simpa using hzero i
  have hJle : Z.ideal ⊔ Ideal.span (Set.range E) ≤ pointIdeal z :=
    sup_le hZle hEle
  refine ⟨⟨hPprime, hJle⟩, ?_⟩
  intro Q hQ hQPle
  obtain ⟨hQprime, hJQ⟩ := hQ
  haveI : Q.IsPrime := hQprime
  set V : AffineVariety (d + d) := ⟨Q, hQprime.isRadical⟩ with hV
  have hVQ : V.ideal = Q := by rw [hV]
  have hVirr : V.IsIrreducible := by rw [hV]; exact hQprime
  have hZQ : Z.ideal ≤ Q :=
    le_sup_left.trans hJQ
  have hEQ : ∀ i, E i ∈ Q := by
    intro i
    have hle2 : Ideal.span (Set.range E)
        ≤ Z.ideal ⊔ Ideal.span (Set.range E) := le_sup_right
    exact hJQ (hle2 (Ideal.subset_span ⟨i, rfl⟩))
  have hzV : z ∈ V.points := by
    rw [hV]
    show z ∈ MvPolynomial.zeroLocus ℂ Q
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro f hf
    have hmem : f ∈ pointIdeal z := hQPle hf
    simpa only [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff,
      MvPolynomial.aeval_eq_eval] using hmem
  have htan0 : V.tangentSpace z = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    simp only [AffineVariety.tangentSpace, Submodule.mem_iInf] at hv
    have hvT : v ∈ Z.tangentSpace z := by
      show v ∈ ⨅ f : Z.ideal, LinearMap.ker (differential f.val z)
      rw [Submodule.mem_iInf]
      intro f
      exact hv ⟨f.val, by rw [hVQ]; exact hZQ f.property⟩
    have hE : ∀ i, differential (E i) z v = 0 := by
      intro i
      have hmem : v ∈ LinearMap.ker (differential (E i) z) :=
        hv ⟨E i, by rw [hVQ]; exact hEQ i⟩
      exact LinearMap.mem_ker.mp hmem
    have hPhi : ((LinearMap.pi (fun i => differential (E i) z)).domRestrict
        (Z.tangentSpace z)) ⟨v, hvT⟩ = 0 := by
      funext i
      show differential (E i) z v = 0
      exact hE i
    have hv0 : (⟨v, hvT⟩ : Z.tangentSpace z) = 0 :=
      hinj (by rw [hPhi, map_zero])
    have hvv : v = 0 := congrArg Subtype.val hv0
    simpa using hvv
  have hdim0 : V.dimension = 0 := by
    have hle := TrackD.tangent_finrank_ge_dimension V hVirr z hzV
    rw [htan0] at hle
    have hfr0 : Module.finrank ℂ ↥(⊥ : Submodule ℂ (Point (d + d))) = 0 :=
      Module.finrank_zero_of_subsingleton
    rw [hfr0] at hle
    exact Nat.le_zero.mp hle
  obtain ⟨x0, hx0pts, -⟩ := TrackA.zeroDim_irreducible_data V hVirr hdim0
  rw [hx0pts] at hzV
  have hzx0 : z = x0 := Set.mem_singleton_iff.mp hzV
  have hVPts : V.points = {z} := by
    rw [← hzx0] at hx0pts
    exact hx0pts
  have hQeq : Q = pointIdeal z := by
    have h1 : Q = MvPolynomial.vanishingIdeal ℂ V.points := by
      rw [← hVQ]
      exact V.vanishingIdeal_points.symm
    rw [h1, hVPts]
    rfl
  exact le_of_eq hQeq.symm

end

end DistinctDistances.MReqAux
