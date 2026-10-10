import DistinctDistances.TrackB.IncidenceDensity

/-!
Support for B09 (`compactIncidence_geometry`): the pair and triple ruling maps as actual
polynomial maps to projective space, their literal fibres, and their image geometry from
the shared constant-fibre image-dimension theorem. All objects are those of Foundations
and the frozen Track B model; nothing here changes a definition.
-/

namespace DistinctDistances.TrackB

namespace RulingMaps

set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem firstPoint_joinPoints {n m : ℕ} (z : Point n) (v : Point m) :
    firstPoint (joinPoints z v) = z := by
  funext i
  exact Fin.addCases_left (m := n) (n := m) (motive := fun _ => ℂ) (left := z) (right := v) i

theorem secondPoint_joinPoints {n m : ℕ} (z : Point n) (v : Point m) :
    secondPoint (joinPoints z v) = v := by
  funext i
  exact Fin.addCases_right (m := n) (n := m) (motive := fun _ => ℂ) (left := z) (right := v) i

theorem mk_congr {n : ℕ} {v w : Point n} (h : v = w) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw := by
  subst h
  rfl

theorem firstPoint_graphVector {e : ℕ} (C : SkewCoordinates e) (z : Point (skewDim e))
    (v : Point e) : firstPoint (graphVector C z v) = v := by
  ext i
  simp [firstPoint, graphVector, joinPoints]

theorem firstPoint_smul {n m : ℕ} (c : ℂ) (w : Point (n + m)) :
    firstPoint (c • w) = c • firstPoint w := by
  funext i
  rfl

/-- Pair coordinates `v ⊗ (v, zv)` as polynomials in `(z, v)`. -/
def rulingPairPolynomials {e : ℕ} (C : SkewCoordinates e) :
    Fin (e * (e + e)) → Poly (skewDim e + e) :=
  fun k => MvPolynomial.X (Fin.natAdd (skewDim e) (finProdFinEquiv.symm k).1) *
    rulingGraphPolynomials C (finProdFinEquiv.symm k).2

/-- Triple coordinates `v ⊗ (v, zv) ⊗ (1, z)` as polynomials in `(z, v)`. -/
def rulingTriplePolynomials {e : ℕ} (C : SkewCoordinates e) :
    Fin ((e * (e + e)) * (skewDim e + 1)) → Poly (skewDim e + e) :=
  fun k => rulingPairPolynomials C (finProdFinEquiv.symm k).1 *
    (Fin.cons (MvPolynomial.C 1 : Poly (skewDim e + e))
      (fun i : Fin (skewDim e) => MvPolynomial.X (Fin.castAdd e i)) :
      Fin (skewDim e + 1) → Poly (skewDim e + e)) (finProdFinEquiv.symm k).2

theorem eval_rulingPairPolynomials {e : ℕ} (C : SkewCoordinates e)
    (w : Point (skewDim e + e)) :
    (fun k => MvPolynomial.aeval w (rulingPairPolynomials C k)) =
      segreVector (secondPoint w) (graphVector C (firstPoint w) (secondPoint w)) := by
  funext k
  have hgraph := congrFun (eval_rulingGraphPolynomials C w) (finProdFinEquiv.symm k).2
  simpa only [rulingPairPolynomials, map_mul, MvPolynomial.aeval_X, segreVector,
    secondPoint] using congrArg (fun a : ℂ => w (Fin.natAdd (skewDim e)
      (finProdFinEquiv.symm k).1) * a) hgraph

theorem eval_rulingTriplePolynomials {e : ℕ} (C : SkewCoordinates e)
    (w : Point (skewDim e + e)) :
    (fun k => MvPolynomial.aeval w (rulingTriplePolynomials C k)) =
      segreVector (segreVector (secondPoint w) (graphVector C (firstPoint w) (secondPoint w)))
        (Fin.cons 1 (firstPoint w)) := by
  funext k
  let a := (finProdFinEquiv.symm k).1
  let b := (finProdFinEquiv.symm k).2
  change MvPolynomial.aeval w (rulingPairPolynomials C a *
    (Fin.cons (MvPolynomial.C 1 : Poly (skewDim e + e))
      (fun i : Fin (skewDim e) => MvPolynomial.X (Fin.castAdd e i)) :
      Fin (skewDim e + 1) → Poly (skewDim e + e)) b) = _
  rw [map_mul, congrFun (eval_rulingPairPolynomials C w) a]
  have hlast : MvPolynomial.aeval w
      ((Fin.cons (MvPolynomial.C 1 : Poly (skewDim e + e))
        (fun i : Fin (skewDim e) => MvPolynomial.X (Fin.castAdd e i)) :
        Fin (skewDim e + 1) → Poly (skewDim e + e)) b) =
      (Fin.cons (1 : ℂ) (firstPoint (n := skewDim e) (m := e) w) :
        Point (skewDim e + 1)) b := by
    cases b using Fin.cases <;> simp [firstPoint]
  rw [hlast]
  rfl

/-! ### Projective helper facts -/

theorem aeval_smul_of_isHomogeneous {n D : ℕ} {f : Poly n} (hf : f.IsHomogeneous D) (c : ℂ)
    (x : Point n) : MvPolynomial.aeval (c • x) f = c ^ D * MvPolynomial.aeval x f := by
  have h := GenericFiber.aeval_scale_of_isWeightedHomogeneous (R := ℂ) (w := 1) hf x c
  have hfun : (fun s => c ^ (1 : Fin n → ℕ) s * x s) = c • x := by
    funext s
    simp
  rw [hfun] at h
  exact h

theorem mem_points_of_homogeneous {n : ℕ} (W : ProjectiveVariety n) (x : ProjectivePoint n)
    (h : ∀ D, ∀ f ∈ W.ideal, f.IsHomogeneous D → MvPolynomial.aeval x.rep f = 0) :
    x ∈ W.points := by
  rw [← Projectivization.mk_rep x, ProjectiveVariety.mem_points_mk_iff]
  intro f hf
  rw [← MvPolynomial.sum_homogeneousComponent f, map_sum]
  apply Finset.sum_eq_zero
  intro D _
  exact h D _ (MvPolynomial.homogeneousComponent_mem_of_mem W.isHomogeneous hf D)
    (MvPolynomial.homogeneousComponent_isHomogeneous D f)

theorem segreVector_apply {N1 N2 : ℕ} (u : Point N1) (y : Point N2) (k1 : Fin N1) (k2 : Fin N2) :
    segreVector u y (finProdFinEquiv (k1, k2)) = u k1 * y k2 := by
  simp [segreVector]

/-- The Segre image of a set of pairs. -/
def segreSet {N1 N2 : ℕ} (S : Set (ProjectivePoint N1 × ProjectivePoint N2)) :
    Set (ProjectivePoint (N1 * N2)) :=
  {u | ∃ w ∈ S, segrePoint w.1 w.2 = u}

theorem segre_rep_eq {N1 N2 : ℕ} (w : ProjectivePoint N1 × ProjectivePoint N2)
    (v : Point (N1 * N2)) (hv : v ≠ 0)
    (hwv : segrePoint w.1 w.2 = Projectivization.mk ℂ v hv) :
    ∃ c : ℂ, v = segreVector (c • w.1.rep) w.2.rep := by
  have h : Projectivization.mk ℂ v hv = Projectivization.mk ℂ (segreVector w.1.rep w.2.rep)
      (segreVector_ne_zero _ _ w.1.rep_nonzero w.2.rep_nonzero) := hwv.symm
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ hv _).mp h
  refine ⟨c, ?_⟩
  rw [← hc]
  funext k
  simp [segreVector, mul_assoc]

/-- Equations of the second factor pass to the closure of a Segre set. -/
theorem segre_second_mem {N1 N2 : ℕ} (S : Set (ProjectivePoint N1 × ProjectivePoint N2))
    (Z : ProjectiveVariety N2) (hS : ∀ w ∈ S, w.2 ∈ Z.points)
    (b : ProjectivePoint N1) (x : ProjectivePoint N2)
    (hx : segrePoint b x ∈ (ProjectiveVariety.closure (segreSet S)).points) : x ∈ Z.points := by
  obtain ⟨k1, hk1⟩ : ∃ k1, b.rep k1 ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact b.rep_nonzero (funext hh)
  apply mem_points_of_homogeneous
  intro D f hf hfh
  let g : Poly (N1 * N2) :=
    MvPolynomial.aeval (fun k2 => (MvPolynomial.X (finProdFinEquiv (k1, k2)) : Poly (N1 * N2))) f
  have hg : ∀ (u : Point N1) (y : Point N2),
      MvPolynomial.aeval (segreVector u y) g = u k1 ^ D * MvPolynomial.aeval y f := by
    intro u y
    rw [GenericFiber.eval_aeval]
    have hfun : (fun k2 => MvPolynomial.aeval (segreVector u y)
        (MvPolynomial.X (finProdFinEquiv (k1, k2)) : Poly (N1 * N2))) = u k1 • y := by
      funext k2
      simp [segreVector_apply]
    rw [hfun, aeval_smul_of_isHomogeneous hfh]
  have hgmem : g ∈ (ProjectiveVariety.closure (segreSet S)).ideal := by
    change g ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives (segreSet S))
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro v ⟨hv, w, hwS, hwv⟩
    obtain ⟨c, rfl⟩ := segre_rep_eq w v hv hwv
    rw [hg]
    have h2 : MvPolynomial.aeval w.2.rep f = 0 :=
      (hS w hwS) w.2.rep w.2.rep_nonzero (Projectivization.mk_rep _) f hf
    rw [h2, mul_zero]
  have := hx (segreVector b.rep x.rep) (segreVector_ne_zero _ _ b.rep_nonzero x.rep_nonzero) rfl
    g hgmem
  rw [hg] at this
  exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hk1)

/-- Equations of the first factor pass to the closure of a Segre set. -/
theorem segre_first_mem {N1 N2 : ℕ} (S : Set (ProjectivePoint N1 × ProjectivePoint N2))
    (W : ProjectiveVariety N1) (hS : ∀ w ∈ S, w.1 ∈ W.points)
    (b : ProjectivePoint N1) (x : ProjectivePoint N2)
    (hx : segrePoint b x ∈ (ProjectiveVariety.closure (segreSet S)).points) : b ∈ W.points := by
  obtain ⟨k2, hk2⟩ : ∃ k2, x.rep k2 ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact x.rep_nonzero (funext hh)
  apply mem_points_of_homogeneous
  intro D f hf hfh
  let g : Poly (N1 * N2) :=
    MvPolynomial.aeval (fun k1 => (MvPolynomial.X (finProdFinEquiv (k1, k2)) : Poly (N1 * N2))) f
  have hg : ∀ (u : Point N1) (y : Point N2),
      MvPolynomial.aeval (segreVector u y) g = y k2 ^ D * MvPolynomial.aeval u f := by
    intro u y
    rw [GenericFiber.eval_aeval]
    have hfun : (fun k1 => MvPolynomial.aeval (segreVector u y)
        (MvPolynomial.X (finProdFinEquiv (k1, k2)) : Poly (N1 * N2))) = y k2 • u := by
      funext k1
      simp [segreVector_apply, mul_comm]
    rw [hfun, aeval_smul_of_isHomogeneous hfh]
  have hgmem : g ∈ (ProjectiveVariety.closure (segreSet S)).ideal := by
    change g ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives (segreSet S))
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro v ⟨hv, w, hwS, hwv⟩
    obtain ⟨c, rfl⟩ := segre_rep_eq w v hv hwv
    rw [hg, aeval_smul_of_isHomogeneous hfh]
    have h1 : MvPolynomial.aeval w.1.rep f = 0 :=
      (hS w hwS) w.1.rep w.1.rep_nonzero (Projectivization.mk_rep _) f hf
    rw [h1, mul_zero, mul_zero]
  have := hx (segreVector b.rep x.rep) (segreVector_ne_zero _ _ b.rep_nonzero x.rep_nonzero) rfl
    g hgmem
  rw [hg] at this
  exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hk2)

theorem tripleClosure_eq_segreSet {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) :
    tripleClosure T = ProjectiveVariety.closure
      (segreSet ((fun w => (segrePoint w.1.1 w.1.2, w.2)) '' T)) := by
  unfold tripleClosure
  congr 1
  ext u
  constructor
  · rintro ⟨p, q, x, hT, rfl⟩
    exact ⟨_, ⟨((p, q), x), hT, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨⟨⟨p, q⟩, x⟩, hT, rfl⟩, rfl⟩
    exact ⟨p, q, x, hT, rfl⟩

/-- A nonempty principal open is dense in the projective closure. -/
theorem projectiveClosure_principal_open {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (H : Poly n) (hH : H ∉ V.ideal) :
    (projectiveClosure V).points ⊆ (ProjectiveVariety.closure
      (affineEmbedding '' {z | z ∈ V.points ∧ MvPolynomial.aeval z H ≠ 0})).points := by
  apply projective_closure_subset
  rintro _ ⟨z, hz, rfl⟩
  apply mem_points_of_homogeneous
  intro D f hf hfh
  let q : Poly n := MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X : Fin (n + 1) → Poly n) f
  have hq : ∀ y : Point n, MvPolynomial.aeval y q =
      MvPolynomial.aeval (Fin.cons 1 y : Point (n + 1)) f := by
    intro y
    rw [GenericFiber.eval_aeval]
    refine congrArg (fun φ => MvPolynomial.aeval φ f) ?_
    funext i
    cases i using Fin.cases <;> simp
  have hqV : q ∈ V.ideal := by
    apply principal_open_vanishing V hV H q hH
    intro y hy hyH
    rw [hq]
    exact hf (Fin.cons 1 y) ⟨consOne_ne_zero y, y, ⟨hy, hyH⟩, rfl⟩
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (Fin.cons 1 z : Point (n + 1))
    (consOne_ne_zero z)
  change MvPolynomial.aeval (Projectivization.mk ℂ (Fin.cons 1 z : Point (n + 1)) _).rep f = 0
  rw [← hc, Units.smul_def, aeval_smul_of_isHomogeneous hfh, ← hq, hz q hqV, mul_zero]

/-! ### Elimination: projections from Segre products are closed -/

/-- Finitely many homogeneous generators of a homogeneous ideal. -/
theorem exists_homogeneous_generators {n : ℕ} (I : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ)) :
    ∃ (τ : Type) (_ : Fintype τ) (f : τ → Poly n) (δ : τ → ℕ),
      (∀ i, f i ∈ I) ∧ (∀ i, (f i).IsHomogeneous (δ i)) ∧ I ≤ Ideal.span (Set.range f) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  let τ := Σ g : s, Fin (g.1.totalDegree + 1)
  refine ⟨τ, inferInstance, fun i => MvPolynomial.homogeneousComponent i.2 i.1.1,
    fun i => i.2, ?_, ?_, ?_⟩
  · intro i
    have hg : i.1.1 ∈ I := by
      rw [← hs]
      exact Submodule.subset_span i.1.2
    exact MvPolynomial.homogeneousComponent_mem_of_mem hI hg _
  · intro i
    exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
  · rw [← hs]
    apply Submodule.span_le.mpr
    intro g hg
    rw [← MvPolynomial.sum_homogeneousComponent g]
    apply Ideal.sum_mem
    intro d hd
    apply Ideal.subset_span
    exact ⟨⟨⟨g, hg⟩, ⟨d, Finset.mem_range.mp hd⟩⟩, rfl⟩

theorem homogeneousComponent_mul_of_isHomogeneous {n : ℕ} {q : Poly n} {δ D : ℕ}
    (hq : q.IsHomogeneous δ) (hδ : δ ≤ D) (c : Poly n) :
    MvPolynomial.homogeneousComponent D (c * q) =
      MvPolynomial.homogeneousComponent (D - δ) c * q := by
  classical
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent c]
  rw [Finset.sum_mul, map_sum]
  have hterm : ∀ k, MvPolynomial.homogeneousComponent D
      (MvPolynomial.homogeneousComponent k c * q) =
      if k + δ = D then MvPolynomial.homogeneousComponent k c * q else 0 := by
    intro k
    have hmem : MvPolynomial.homogeneousComponent k c * q ∈
        MvPolynomial.homogeneousSubmodule (Fin n) ℂ (k + δ) :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        ((MvPolynomial.homogeneousComponent_isHomogeneous k c).mul hq)
    rw [MvPolynomial.homogeneousComponent_of_mem hmem]
    by_cases h : k + δ = D
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  by_cases hmem : D - δ ∈ Finset.range (c.totalDegree + 1)
  · rw [Finset.sum_eq_single (D - δ)]
    · intro k hk hne
      exact absurd (by have := (Finset.mem_filter.mp hk).2; omega) hne
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨hmem, by omega⟩) hnot
  · rw [Finset.sum_eq_zero]
    · have hz : MvPolynomial.homogeneousComponent (D - δ) c = 0 := by
        apply MvPolynomial.homogeneousComponent_eq_zero
        rw [Finset.mem_range] at hmem
        omega
      rw [hz, zero_mul]
    · intro k hk
      exfalso
      have h1 := (Finset.mem_filter.mp hk).2
      have h2 := (Finset.mem_filter.mp hk).1
      apply hmem
      rwa [show D - δ = k by omega]

/-- Substitution `Z_{(k1,k2)} ↦ x_{k2} Y_{k1}`. -/
def segreSlice {N1 N2 : ℕ} (x : Point N2) : Poly (N1 * N2) →ₐ[ℂ] Poly N1 :=
  MvPolynomial.aeval (fun k => MvPolynomial.C (x (finProdFinEquiv.symm k).2) *
    MvPolynomial.X (finProdFinEquiv.symm k).1)

theorem eval_segreSlice {N1 N2 : ℕ} (x : Point N2) (b : Point N1) (f : Poly (N1 * N2)) :
    MvPolynomial.aeval b (segreSlice x f) = MvPolynomial.aeval (segreVector b x) f := by
  rw [segreSlice, GenericFiber.eval_aeval]
  refine congrArg (fun φ => MvPolynomial.aeval φ f) ?_
  funext k
  simp [segreVector, mul_comm]

theorem segreSlice_isHomogeneous {N1 N2 : ℕ} (x : Point N2) {f : Poly (N1 * N2)} {δ : ℕ}
    (hf : f.IsHomogeneous δ) : (segreSlice (N1 := N1) x f).IsHomogeneous δ := by
  have h := hf.aeval (fun k => (MvPolynomial.C (x (finProdFinEquiv.symm k).2) *
    MvPolynomial.X (finProdFinEquiv.symm k).1 : Poly N1))
    (fun k => MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa [segreSlice] using h

/-- The symbolic version of `segreSlice`, with the second factor as indeterminates. -/
def segreSym {N1 N2 : ℕ} : Poly (N1 * N2) →ₐ[ℂ] MvPolynomial (Fin N1) (Poly N2) :=
  MvPolynomial.aeval (fun k => MvPolynomial.C (MvPolynomial.X (finProdFinEquiv.symm k).2) *
    MvPolynomial.X (finProdFinEquiv.symm k).1)

theorem map_segreSym {N1 N2 : ℕ} (x : Point N2) (f : Poly (N1 * N2)) :
    MvPolynomial.map (MvPolynomial.aeval x).toRingHom (segreSym (N1 := N1) f) =
      segreSlice x f := by
  have hhom : (MvPolynomial.mapAlgHom (MvPolynomial.aeval x)).comp (segreSym (N1 := N1)) =
      segreSlice x := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [segreSym, segreSlice]
  exact congrArg (fun F : Poly (N1 * N2) →ₐ[ℂ] Poly N1 => F f) hhom

theorem map_lift {N1 N2 : ℕ} (x : Point N2) (c : Poly N1) :
    MvPolynomial.map (MvPolynomial.aeval x).toRingHom
      (MvPolynomial.map (algebraMap ℂ (Poly N2)) c) = c := by
  rw [MvPolynomial.map_map]
  have : ((MvPolynomial.aeval x).toRingHom.comp (algebraMap ℂ (Poly N2))) = RingHom.id ℂ := by
    ext r
    simp
  rw [this, MvPolynomial.map_id]

/-- Exponents of total degree `D` in `N1` variables, as a finite set. -/
def degFinset (N1 D : ℕ) : Finset (Fin N1 →₀ ℕ) :=
  ((Finset.univ : Finset (Fin N1 → Fin (D + 1))).image
    (fun f => Finsupp.equivFunOnFinite.symm (fun i => (f i : ℕ)))).filter
      (fun α => α.degree = D)

theorem le_degree_of {N1 : ℕ} (α : Fin N1 →₀ ℕ) (i : Fin N1) : α i ≤ α.degree := by
  classical
  by_cases hi : i ∈ α.support
  · exact Finset.single_le_sum (f := fun j => α j) (fun j _ => Nat.zero_le _) hi
  · rw [Finsupp.notMem_support_iff.mp hi]
    exact Nat.zero_le _

theorem mem_degFinset {N1 D : ℕ} {α : Fin N1 →₀ ℕ} : α ∈ degFinset N1 D ↔ α.degree = D := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨fun i => ⟨α i, Nat.lt_succ_of_le (h ▸ le_degree_of α i)⟩, Finset.mem_univ _, ?_⟩, h⟩
    ext i
    simp

theorem degree_eq_sum_univ {N1 : ℕ} (α : Fin N1 →₀ ℕ) : α.degree = ∑ i, α i := by
  classical
  change ∑ i ∈ α.support, α i = _
  exact Finset.sum_subset (Finset.subset_univ _)
    (fun i _ hi => Finsupp.notMem_support_iff.mp hi)

theorem eval_homogeneous_sum {N1 D : ℕ} (P : Poly N1) (hP : P.IsHomogeneous D) (b : Point N1) :
    ∑ β : degFinset N1 D, P.coeff β.1 * ∏ k ∈ β.1.support, b k ^ β.1 k =
      MvPolynomial.aeval b P := by
  classical
  have hae : MvPolynomial.eval b P = MvPolynomial.aeval b P := by
    rw [← MvPolynomial.coe_aeval_eq_eval]
    rfl
  rw [← hae, MvPolynomial.eval_eq,
    Finset.sum_coe_sort (degFinset N1 D) (fun β => P.coeff β * ∏ k ∈ β.support, b k ^ β k)]
  symm
  apply Finset.sum_subset
  · intro d hd
    apply mem_degFinset.mpr
    have h := hP (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.degree_eq_weight_one]
    exact h
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul]

/-- Projective elimination: the projection to the second factor of a closed subset of a
Segre product is closed. The proof is the projective Nullstellensatz together with a
determinant certificate. -/
theorem segre_projection_closed {N1 N2 : ℕ} (K : ProjectiveVariety (N1 * N2))
    (x0 : ProjectivePoint N2)
    (hx0 : x0 ∈ (ProjectiveVariety.closure
      {x : ProjectivePoint N2 | ∃ b : ProjectivePoint N1, segrePoint b x ∈ K.points}).points) :
    ∃ b : ProjectivePoint N1, segrePoint b x0 ∈ K.points := by
  classical
  by_contra hno
  obtain ⟨τ, _, fg, δ, hfgK, hfgH, hspan⟩ := exists_homogeneous_generators K.ideal K.isHomogeneous
  let J : Ideal (Poly N1) := Ideal.span (Set.range (fun i => segreSlice x0.rep (fg i)))
  have hvanK : ∀ b : Point N1, (∀ i, MvPolynomial.aeval b (segreSlice x0.rep (fg i)) = 0) →
      ∀ f ∈ K.ideal, MvPolynomial.aeval (segreVector b x0.rep) f = 0 := by
    intro b hb f hf
    have hle : Ideal.span (Set.range fg) ≤
        RingHom.ker (MvPolynomial.aeval (segreVector b x0.rep) : Poly (N1 * N2) →ₐ[ℂ] ℂ) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, ← eval_segreSlice]
      exact hb i
    exact hle (hspan hf)
  have hzero : ∀ b ∈ MvPolynomial.zeroLocus ℂ J, b = 0 := by
    intro b hb
    by_contra hb0
    apply hno
    refine ⟨Projectivization.mk ℂ b hb0, ?_⟩
    have hseg : segrePoint (Projectivization.mk ℂ b hb0) x0 =
        Projectivization.mk ℂ (segreVector b x0.rep)
          (segreVector_ne_zero _ _ hb0 x0.rep_nonzero) := by
      conv_lhs => rw [← Projectivization.mk_rep x0]
      rw [segrePoint_mk]
    rw [hseg, ProjectiveVariety.mem_points_mk_iff]
    intro f hf
    exact hvanK b (fun i => hb _ (Ideal.subset_span ⟨i, rfl⟩)) f hf
  have hXrad : ∀ i : Fin N1, ∃ r : ℕ, (MvPolynomial.X i : Poly N1) ^ r ∈ J := by
    intro i
    have hmem : (MvPolynomial.X i : Poly N1) ∈ J.radical := by
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
        MvPolynomial.mem_vanishingIdeal_iff]
      intro b hb
      rw [hzero b hb]
      simp
    exact Ideal.mem_radical_iff.mp hmem
  choose rr hrr using hXrad
  let Nm : ℕ := (∑ i, rr i) + 1
  have hXNm : ∀ i, (MvPolynomial.X i : Poly N1) ^ Nm ∈ J := by
    intro i
    have hle : rr i ≤ Nm := by
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (rr j)) (Finset.mem_univ i)
      omega
    rw [show Nm = rr i + (Nm - rr i) by omega, pow_add]
    exact J.mul_mem_right _ (hrr i)
  let D : ℕ := N1 * Nm + (∑ i, δ i) + 1
  have hδD : ∀ i, δ i ≤ D := by
    intro i
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (δ j)) (Finset.mem_univ i)
    omega
  have hmono : ∀ α : Fin N1 →₀ ℕ, α.degree = D → MvPolynomial.monomial α (1 : ℂ) ∈ J := by
    intro α hα
    obtain ⟨i, hi⟩ : ∃ i, Nm ≤ α i := by
      by_contra hh
      push_neg at hh
      have h1 : α.degree ≤ N1 * (Nm - 1) := by
        rw [degree_eq_sum_univ]
        calc ∑ i, α i ≤ ∑ _i : Fin N1, (Nm - 1) :=
              Finset.sum_le_sum (fun i _ => by have := hh i; omega)
          _ = N1 * (Nm - 1) := by simp
      have h2 : N1 * (Nm - 1) ≤ N1 * Nm := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      omega
    have hsplit : MvPolynomial.monomial α (1 : ℂ) =
        (MvPolynomial.X i) ^ Nm * MvPolynomial.monomial (α - Finsupp.single i Nm) 1 := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
      congr 1
      rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)]
    rw [hsplit]
    exact J.mul_mem_right _ (hXNm i)
  have hcert : ∀ α : degFinset N1 D, ∃ c : τ → Poly N1,
      (∀ i, (c i).IsHomogeneous (D - δ i)) ∧
      MvPolynomial.monomial α.1 (1 : ℂ) = ∑ i, c i * segreSlice x0.rep (fg i) := by
    intro α
    have hmem := hmono α.1 (mem_degFinset.mp α.2)
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
    refine ⟨fun i => MvPolynomial.homogeneousComponent (D - δ i) (c i),
      fun i => MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩
    have h1 : MvPolynomial.homogeneousComponent D (MvPolynomial.monomial α.1 (1 : ℂ)) =
        MvPolynomial.monomial α.1 1 := by
      have hm : MvPolynomial.monomial α.1 (1 : ℂ) ∈ MvPolynomial.homogeneousSubmodule (Fin N1) ℂ D :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_monomial _ (mem_degFinset.mp α.2))
      rw [MvPolynomial.homogeneousComponent_of_mem hm, if_pos rfl]
    rw [← h1, ← hc, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact homogeneousComponent_mul_of_isHomogeneous
      (segreSlice_isHomogeneous x0.rep (hfgH i)) (hδD i) (c i)
  choose c hcH hcEq using hcert
  let Psym : degFinset N1 D → MvPolynomial (Fin N1) (Poly N2) := fun α =>
    ∑ i, MvPolynomial.map (algebraMap ℂ (Poly N2)) (c α i) * segreSym (fg i)
  let M : Matrix (degFinset N1 D) (degFinset N1 D) (Poly N2) := fun α β => (Psym α).coeff β.1
  have hspec : ∀ (x : Point N2) (α β : degFinset N1 D),
      MvPolynomial.aeval x (M α β) = (∑ i, c α i * segreSlice x (fg i)).coeff β.1 := by
    intro x α β
    have hmap : MvPolynomial.map (MvPolynomial.aeval x).toRingHom (Psym α) =
        ∑ i, c α i * segreSlice x (fg i) := by
      simp only [Psym, map_sum, map_mul, map_lift, map_segreSym]
    rw [← hmap, MvPolynomial.coeff_map]
    rfl
  have hdetx : ∀ x : Point N2, MvPolynomial.aeval x M.det =
      (Matrix.of fun α β : degFinset N1 D =>
        (∑ i, c α i * segreSlice x (fg i)).coeff β.1).det := by
    intro x
    rw [AlgHom.map_det]
    congr 1
    ext α β
    exact hspec x α β
  have hGvan : M.det ∈ (ProjectiveVariety.closure
      {x : ProjectivePoint N2 | ∃ b : ProjectivePoint N1, segrePoint b x ∈ K.points}).ideal := by
    change M.det ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives _)
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro v ⟨hv, b', hb'⟩
    have hseg : segrePoint b' (Projectivization.mk ℂ v hv) =
        Projectivization.mk ℂ (segreVector b'.rep v)
          (segreVector_ne_zero _ _ b'.rep_nonzero hv) := by
      conv_lhs => rw [← Projectivization.mk_rep b']
      rw [segrePoint_mk]
    rw [hseg] at hb'
    have hK : ∀ f ∈ K.ideal, MvPolynomial.aeval (segreVector b'.rep v) f = 0 :=
      fun f hf => hb' _ _ rfl f hf
    rw [hdetx, ← Matrix.exists_mulVec_eq_zero_iff]
    obtain ⟨k0, hk0⟩ : ∃ k0, b'.rep k0 ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact b'.rep_nonzero (funext hh)
    refine ⟨fun β => ∏ k ∈ β.1.support, b'.rep k ^ β.1 k, ?_, ?_⟩
    · intro h0
      have hβ0 : Finsupp.single k0 D ∈ degFinset N1 D := by
        apply mem_degFinset.mpr
        simp
      have := congrFun h0 ⟨Finsupp.single k0 D, hβ0⟩
      have hD0 : D ≠ 0 := by omega
      simp [Finsupp.support_single_ne_zero _ hD0] at this
      exact hk0 this
    · funext α
      show ∑ β : degFinset N1 D, (∑ i, c α i * segreSlice v (fg i)).coeff β.1 *
        ∏ k ∈ β.1.support, b'.rep k ^ β.1 k = 0
      have hPhom : (∑ i, c α i * segreSlice v (fg i)).IsHomogeneous D := by
        apply MvPolynomial.IsHomogeneous.sum
        intro i _
        have := (hcH α i).mul (segreSlice_isHomogeneous v (hfgH i))
        rwa [Nat.sub_add_cancel (hδD i)] at this
      rw [eval_homogeneous_sum _ hPhom, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_mul, eval_segreSlice, hK _ (hfgK i), mul_zero]
  have hG1 : MvPolynomial.aeval x0.rep M.det = 1 := by
    rw [hdetx]
    have hone : (Matrix.of fun α β : degFinset N1 D =>
        (∑ i, c α i * segreSlice x0.rep (fg i)).coeff β.1) = 1 := by
      ext α β
      rw [Matrix.of_apply, ← hcEq α, MvPolynomial.coeff_monomial, Matrix.one_apply]
      by_cases h : α = β
      · subst h
        simp
      · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg h]
    rw [hone, Matrix.det_one]
  have := hx0 x0.rep x0.rep_nonzero (Projectivization.mk_rep _) _ hGvan
  rw [hG1] at this
  exact one_ne_zero this

/-- The literal ruling graph in the triple Segre space (same set as `rulingTripleImage`). -/
def tripleSet {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) : Set (ProjectivePoint ((e * (e + e)) * (skewDim e + 1))) :=
  {x | ∃ z v, joinPoints z v ∈ rulingPoints Γ H ∧ ∃ hv : v ≠ 0,
    x = segrePoint (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv))
      (affineEmbedding z)}

section Ruling

variable {e j N : ℕ} (C : SkewCoordinates e)
  (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e)) (a : Fin e) (R : IsRulingIncidence C V Γ H a j N)

include R

theorem secondPoint_ne_zero (w : Point (skewDim e + e)) (hw : w ∈ Γ.points) :
    secondPoint w ≠ 0 := by
  intro hzero
  have h := R.normalized w hw
  rw [hzero] at h
  exact zero_ne_one h

theorem rulingPairPolynomials_nonzero (w : Point (skewDim e + e)) (hw : w ∈ Γ.points) :
    (fun k => MvPolynomial.aeval w (rulingPairPolynomials C k)) ≠ 0 := by
  have hv := secondPoint_ne_zero C V Γ H a R w hw
  rw [eval_rulingPairPolynomials]
  exact segreVector_ne_zero _ _ hv (graphVector_ne_zero C _ _ hv)

theorem rulingTriplePolynomials_nonzero (w : Point (skewDim e + e)) (hw : w ∈ Γ.points) :
    (fun k => MvPolynomial.aeval w (rulingTriplePolynomials C k)) ≠ 0 := by
  have hp := rulingPairPolynomials_nonzero C V Γ H a R w hw
  rw [eval_rulingPairPolynomials] at hp
  rw [eval_rulingTriplePolynomials]
  exact segreVector_ne_zero _ _ hp (consOne_ne_zero _)

theorem rulingPoints_of_mem (w : Point (skewDim e + e)) (hw : w ∈ Γ.points)
    (hwH : MvPolynomial.aeval w (rulingOpenPolynomial H) ≠ 0) :
    joinPoints (firstPoint w) (secondPoint w) ∈ rulingPoints Γ H := by
  rw [joinPoints_eta]
  exact ⟨hw, by simpa only [eval_rulingOpenPolynomial] using hwH⟩

theorem rulingPair_polynomial_image :
    polynomialProjectiveImage Γ (rulingOpenPolynomial H) (rulingPairPolynomials C) =
      {b | ∃ d p, (d, p) ∈ liftedParameterPairs C Γ H ∧ segrePoint d p = b} := by
  ext b
  constructor
  · rintro ⟨w, hw, hwH, hF, rfl⟩
    have hv := secondPoint_ne_zero C V Γ H a R w hw
    refine ⟨Projectivization.mk ℂ (secondPoint w) hv,
      graphParameter C (firstPoint w) (secondPoint w) hv,
      ⟨firstPoint w, secondPoint w, rulingPoints_of_mem C V Γ H a R w hw hwH, hv, rfl, rfl⟩, ?_⟩
    rw [graphParameter, segrePoint_mk]
    exact mk_congr (eval_rulingPairPolynomials C w).symm _ _
  · rintro ⟨d, p, ⟨z, v, hzv, hv, hd, hp⟩, rfl⟩
    simp only at hd hp
    subst hd hp
    refine ⟨joinPoints z v, hzv.1, ?_, rulingPairPolynomials_nonzero C V Γ H a R _ hzv.1, ?_⟩
    · rw [eval_rulingOpenPolynomial]
      exact hzv.2
    · rw [graphParameter, segrePoint_mk]
      apply mk_congr
      rw [eval_rulingPairPolynomials, firstPoint_joinPoints, secondPoint_joinPoints]

theorem pair_mk_eq_iff (w w0 : Point (skewDim e + e)) (hw : w ∈ Γ.points)
    (hw0 : w0 ∈ Γ.points)
    (hF : (fun k => MvPolynomial.aeval w (rulingPairPolynomials C k)) ≠ 0)
    (hF0 : (fun k => MvPolynomial.aeval w0 (rulingPairPolynomials C k)) ≠ 0)
    (hG : (fun i => MvPolynomial.aeval w (rulingGraphPolynomials C i)) ≠ 0)
    (hG0 : (fun i => MvPolynomial.aeval w0 (rulingGraphPolynomials C i)) ≠ 0) :
    Projectivization.mk ℂ _ hF = Projectivization.mk ℂ _ hF0 ↔
      Projectivization.mk ℂ _ hG = Projectivization.mk ℂ _ hG0 := by
  have hv := secondPoint_ne_zero C V Γ H a R w hw
  have hv0 := secondPoint_ne_zero C V Γ H a R w0 hw0
  have hgv := graphVector_ne_zero C (firstPoint w) (secondPoint w) hv
  have hgv0 := graphVector_ne_zero C (firstPoint w0) (secondPoint w0) hv0
  have e1 : Projectivization.mk ℂ _ hF = segrePoint (Projectivization.mk ℂ _ hv)
      (Projectivization.mk ℂ _ hgv) := by
    rw [segrePoint_mk]
    exact mk_congr (eval_rulingPairPolynomials C w) _ _
  have e0 : Projectivization.mk ℂ _ hF0 = segrePoint (Projectivization.mk ℂ _ hv0)
      (Projectivization.mk ℂ _ hgv0) := by
    rw [segrePoint_mk]
    exact mk_congr (eval_rulingPairPolynomials C w0) _ _
  have g1 : Projectivization.mk ℂ _ hG = Projectivization.mk ℂ _ hgv :=
    mk_congr (eval_rulingGraphPolynomials C w) _ _
  have g0 : Projectivization.mk ℂ _ hG0 = Projectivization.mk ℂ _ hgv0 :=
    mk_congr (eval_rulingGraphPolynomials C w0) _ _
  rw [e1, e0, g1, g0]
  constructor
  · intro h
    have hpair := @segrePoint_injective e (e + e)
      (Projectivization.mk ℂ _ hv, Projectivization.mk ℂ _ hgv)
      (Projectivization.mk ℂ _ hv0, Projectivization.mk ℂ _ hgv0) h
    exact congrArg Prod.snd hpair
  · intro h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ hgv hgv0).mp h
    have hvv : c • secondPoint w0 = secondPoint w := by
      have := congrArg firstPoint hc
      rwa [firstPoint_smul, firstPoint_graphVector, firstPoint_graphVector] at this
    have hmk : Projectivization.mk ℂ _ hv = Projectivization.mk ℂ _ hv0 :=
      ((Projectivization.mk_eq_mk_iff' ℂ _ _ hv hv0).mpr ⟨c, hvv⟩)
    rw [hmk, h]

theorem rulingPair_polynomial_fiber {b : ProjectivePoint (e * (e + e))}
    (hb : b ∈ polynomialProjectiveImage Γ (rulingOpenPolynomial H) (rulingPairPolynomials C)) :
    ∃ p ∈ parameterImage C Γ H,
      polynomialProjectiveFiber Γ (rulingOpenPolynomial H) (rulingPairPolynomials C) b =
        polynomialProjectiveFiber Γ (rulingOpenPolynomial H) (rulingGraphPolynomials C) p := by
  obtain ⟨w0, hw0, hw0H, hF0, rfl⟩ := hb
  have hG0 := rulingGraphPolynomials_nonzero C V Γ H a R w0 hw0
  refine ⟨Projectivization.mk ℂ _ hG0, ?_, ?_⟩
  · rw [← ruling_polynomial_projective_image C V Γ H a R]
    exact ⟨w0, hw0, hw0H, hG0, rfl⟩
  · ext w
    constructor
    · rintro ⟨hw, hwH, hF, heq⟩
      have hG := rulingGraphPolynomials_nonzero C V Γ H a R w hw
      exact ⟨hw, hwH, hG,
        (pair_mk_eq_iff C V Γ H a R w w0 hw hw0 hF hF0 hG hG0).mp heq⟩
    · rintro ⟨hw, hwH, hG, heq⟩
      have hF := rulingPairPolynomials_nonzero C V Γ H a R w hw
      exact ⟨hw, hwH, hF,
        (pair_mk_eq_iff C V Γ H a R w w0 hw hw0 hF hF0 hG hG0).mpr heq⟩

theorem rulingTriple_polynomial_image :
    polynomialProjectiveImage Γ (rulingOpenPolynomial H) (rulingTriplePolynomials C) =
      tripleSet C Γ H := by
  ext b
  constructor
  · rintro ⟨w, hw, hwH, hF, rfl⟩
    have hv := secondPoint_ne_zero C V Γ H a R w hw
    refine ⟨firstPoint w, secondPoint w, rulingPoints_of_mem C V Γ H a R w hw hwH, hv, ?_⟩
    rw [graphParameter, segrePoint_mk, affineEmbedding, segrePoint_mk]
    exact mk_congr (eval_rulingTriplePolynomials C w) _ _
  · rintro ⟨z, v, hzv, hv, rfl⟩
    refine ⟨joinPoints z v, hzv.1, ?_, rulingTriplePolynomials_nonzero C V Γ H a R _ hzv.1, ?_⟩
    · rw [eval_rulingOpenPolynomial]
      exact hzv.2
    · rw [graphParameter, segrePoint_mk, affineEmbedding, segrePoint_mk]
      apply mk_congr
      rw [eval_rulingTriplePolynomials, firstPoint_joinPoints, secondPoint_joinPoints]

theorem triple_mk_eq (w w0 : Point (skewDim e + e)) (hw : w ∈ Γ.points)
    (hw0 : w0 ∈ Γ.points)
    (hF : (fun k => MvPolynomial.aeval w (rulingTriplePolynomials C k)) ≠ 0)
    (hF0 : (fun k => MvPolynomial.aeval w0 (rulingTriplePolynomials C k)) ≠ 0)
    (heq : Projectivization.mk ℂ _ hF = Projectivization.mk ℂ _ hF0) : w = w0 := by
  have hv := secondPoint_ne_zero C V Γ H a R w hw
  have hv0 := secondPoint_ne_zero C V Γ H a R w0 hw0
  have hgv := graphVector_ne_zero C (firstPoint w) (secondPoint w) hv
  have hgv0 := graphVector_ne_zero C (firstPoint w0) (secondPoint w0) hv0
  have e1 : Projectivization.mk ℂ _ hF = segrePoint (segrePoint (Projectivization.mk ℂ _ hv)
      (Projectivization.mk ℂ _ hgv)) (Projectivization.mk ℂ _ (consOne_ne_zero (firstPoint w))) := by
    rw [segrePoint_mk, segrePoint_mk] <;> exact mk_congr (eval_rulingTriplePolynomials C w) _ _
  have e0 : Projectivization.mk ℂ _ hF0 = segrePoint (segrePoint (Projectivization.mk ℂ _ hv0)
      (Projectivization.mk ℂ _ hgv0))
        (Projectivization.mk ℂ _ (consOne_ne_zero (firstPoint w0))) := by
    rw [segrePoint_mk, segrePoint_mk] <;> exact mk_congr (eval_rulingTriplePolynomials C w0) _ _
  rw [e1, e0] at heq
  have h1 := @segrePoint_injective (e * (e + e)) (skewDim e + 1) (_, _) (_, _) heq
  obtain ⟨h12, h3⟩ := Prod.ext_iff.mp h1
  have h2 := @segrePoint_injective e (e + e) (_, _) (_, _) h12
  obtain ⟨hdir, _⟩ := Prod.ext_iff.mp h2
  -- the affine point
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ (consOne_ne_zero (firstPoint w))
    (consOne_ne_zero (firstPoint w0))).mp h3
  have hc1 : c = 1 := by
    have := congrFun hc 0
    simpa using this
  subst hc1
  have hz : firstPoint w = firstPoint w0 := by
    funext i
    have := congrFun hc i.succ
    simpa using this.symm
  -- the normalised direction
  obtain ⟨d, hd⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ hv hv0).mp hdir
  have hd1 : d = 1 := by
    have := congrFun hd a
    simp only [Pi.smul_apply, smul_eq_mul, R.normalized w hw, R.normalized w0 hw0] at this
    simpa using this
  subst hd1
  have hvv : secondPoint w = secondPoint w0 := by
    rw [← hd, one_smul]
  rw [← joinPoints_eta w, ← joinPoints_eta w0, hz, hvv]

theorem rulingTriple_polynomial_fiber
    {b : ProjectivePoint ((e * (e + e)) * (skewDim e + 1))}
    (hb : b ∈ polynomialProjectiveImage Γ (rulingOpenPolynomial H) (rulingTriplePolynomials C)) :
    ∃ w ∈ Γ.points, MvPolynomial.aeval w (rulingOpenPolynomial H) ≠ 0 ∧
      polynomialProjectiveFiber Γ (rulingOpenPolynomial H) (rulingTriplePolynomials C) b =
        {w} := by
  obtain ⟨w0, hw0, hw0H, hF0, rfl⟩ := hb
  refine ⟨w0, hw0, hw0H, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, _, hF, heq⟩
    exact triple_mk_eq C V Γ H a R w w0 hw hw0 hF hF0 heq
  · rintro rfl
    exact ⟨hw0, hw0H, hF0, rfl⟩

variable {h : ℕ}

theorem ruling_pair_image_geometry (hd : V.dimension = flatDim e + h) :
    (pairClosure (liftedParameterPairs C Γ H)).IsIrreducible ∧
      (pairClosure (liftedParameterPairs C Γ H)).dimension = h + j := by
  have hirr := polynomialProjectiveImage_irreducible Γ R.incidence_irreducible
    (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R)
    (rulingPairPolynomials C) (fun w hw _ => rulingPairPolynomials_nonzero C V Γ H a R w hw)
  have hdim := Request.polynomial_projective_image_dimension Γ R.incidence_irreducible
    (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R)
    (rulingPairPolynomials C) (fun w hw _ => rulingPairPolynomials_nonzero C V Γ H a R w hw)
    (d := flatDim e) (by
      intro b hb
      obtain ⟨p, hp, hfiber⟩ := rulingPair_polynomial_fiber C V Γ H a R hb
      have hp' : p ∈ polynomialProjectiveImage Γ (rulingOpenPolynomial H)
          (rulingGraphPolynomials C) := by
        rw [ruling_polynomial_projective_image C V Γ H a R]
        exact hp
      rw [hfiber]
      exact ruling_polynomial_projective_fiber_dimension C V Γ H a R p hp')
  rw [rulingPair_polynomial_image C V Γ H a R] at hirr hdim
  change (pairClosure (liftedParameterPairs C Γ H)).IsIrreducible at hirr
  change Γ.dimension = (pairClosure (liftedParameterPairs C Γ H)).dimension + flatDim e at hdim
  refine ⟨hirr, ?_⟩
  rw [R.incidence_dimension, hd] at hdim
  omega

theorem ruling_triple_image_geometry (hd : V.dimension = flatDim e + h) :
    (ProjectiveVariety.closure (tripleSet C Γ H)).IsIrreducible ∧
    (ProjectiveVariety.closure (tripleSet C Γ H)).dimension = flatDim e + h + j := by
  have hirr := polynomialProjectiveImage_irreducible Γ R.incidence_irreducible
    (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R)
    (rulingTriplePolynomials C) (fun w hw _ => rulingTriplePolynomials_nonzero C V Γ H a R w hw)
  have hdim := Request.polynomial_projective_image_dimension Γ R.incidence_irreducible
    (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R)
    (rulingTriplePolynomials C) (fun w hw _ => rulingTriplePolynomials_nonzero C V Γ H a R w hw)
    (d := 0) (by
      intro b hb
      obtain ⟨w, _, hwg, hfiber⟩ := rulingTriple_polynomial_fiber C V Γ H a R hb
      let φ : Point 0 →ₗ[ℂ] Point (skewDim e + e) := 0
      have hφ : Function.Injective φ := fun _ _ _ => Subsingleton.elim _ _
      have hset : {x | ∃ t : Point 0, x = w + φ t ∧
          MvPolynomial.aeval x (rulingOpenPolynomial H) ≠ 0} =
          ({w} : Set (Point (skewDim e + e))) := by
        ext x
        constructor
        · rintro ⟨t, hx, _⟩
          apply Set.mem_singleton_iff.mpr
          simpa only [φ, LinearMap.zero_apply, add_zero] using hx
        · intro hx
          have hx' : x = w := Set.mem_singleton_iff.mp hx
          subst x
          exact ⟨0, by simp [φ], hwg⟩
      have hzero := Request.affine_linear_principal_open_dimension w φ hφ
        (rulingOpenPolynomial H) 0 (by simpa [φ] using hwg)
      rw [hset] at hzero
      rw [hfiber]
      exact hzero)
  rw [rulingTriple_polynomial_image C V Γ H a R] at hirr hdim
  refine ⟨hirr, ?_⟩
  rw [R.incidence_dimension, hd, Nat.add_zero] at hdim
  exact hdim.symm

/-- B09's point image: every point of the projective carrier lies under the compact
incidence, by projective elimination, graph density and dominance. -/
theorem ruling_incidence_point_image :
    incidencePointImage C Γ H = (projectiveClosure V).points := by
  apply Set.Subset.antisymm
  · rintro x ⟨d, p, hx⟩
    let Z := projectiveClosure V
    let TZ : Set ((ProjectivePoint e × ProjectivePoint (e + e)) ×
        ProjectivePoint (skewDim e + 1)) := {w | w.2 ∈ Z.points}
    let W := tripleClosure TZ
    have hGraph : ∀ z v, joinPoints z v ∈ rulingPoints Γ H → ∀ hv : v ≠ 0,
        segrePoint (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv))
          (affineEmbedding z) ∈ W.points := by
      intro z v hw hv
      have hz : z ∈ V.points := firstPoint_joinPoints z v ▸ R.point_containment _ hw.1
      have hZ : affineEmbedding z ∈ Z.points :=
        ProjectiveVariety.subset_closure _ ⟨z, hz, rfl⟩
      exact ProjectiveVariety.subset_closure _
        ⟨Projectivization.mk ℂ v hv, graphParameter C z v hv, affineEmbedding z, hZ, rfl⟩
    have hXW : (compactIncidence C Γ H).points ⊆ W.points :=
      compact_incidence_subset_of_ruling_graph C V Γ H a R W hGraph
    have hxW := hXW hx
    change segrePoint (segrePoint d p) x ∈ (tripleClosure TZ).points at hxW
    rw [tripleClosure_eq_segreSet] at hxW
    exact segre_second_mem _ Z (by rintro _ ⟨w, hw, rfl⟩; exact hw) _ x hxW
  · intro x hx
    let I' : Set (ProjectivePoint (skewDim e + 1)) :=
      {x | ∃ b : ProjectivePoint (e * (e + e)), segrePoint b x ∈ (compactIncidence C Γ H).points}
    have hΩ : affineEmbedding '' workingPoints V H ⊆ I' := by
      rintro x ⟨z, hz, rfl⟩
      obtain ⟨v, hvΓ⟩ := R.dominant z hz
      have hv : v ≠ 0 := by
        intro hzero
        have h := R.normalized (joinPoints z v) hvΓ
        rw [secondPoint_joinPoints, hzero] at h
        exact zero_ne_one h
      have hw : joinPoints z v ∈ rulingPoints Γ H :=
        ⟨hvΓ, (firstPoint_joinPoints z v).symm ▸ hz.2⟩
      have hlift : (Projectivization.mk ℂ v hv, graphParameter C z v hv) ∈
          liftedParameterPairs C Γ H := ⟨z, v, hw, hv, rfl, rfl⟩
      have hbase : (Projectivization.mk ℂ v hv, graphParameter C z v hv) ∈
          liftedParameterBase C Γ H := ProjectiveVariety.subset_closure _
            ⟨Projectivization.mk ℂ v hv, graphParameter C z v hv, hlift, rfl⟩
      exact ⟨segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv),
        ProjectiveVariety.subset_closure _
          ⟨Projectivization.mk ℂ v hv, graphParameter C z v hv, affineEmbedding z,
            ⟨hbase, graph_incidenceCondition C z v hv⟩, rfl⟩⟩
    have hx' := projectiveClosure_principal_open V R.variety_irreducible H R.nonzero_section hx
    have hx'' : x ∈ (ProjectiveVariety.closure I').points :=
      projective_closure_subset _ _ (hΩ.trans (ProjectiveVariety.subset_closure _)) hx'
    obtain ⟨b, hb⟩ := segre_projection_closed (compactIncidence C Γ H) x hx''
    have hb' : segrePoint b x ∈ (ProjectiveVariety.closure (segreSet
        ((fun w => (segrePoint w.1.1 w.1.2, w.2)) '' incidenceTriples C Γ H))).points := by
      rw [← tripleClosure_eq_segreSet]
      exact hb
    have hbW : b ∈ (pairClosure (liftedParameterPairs C Γ H)).points :=
      segre_first_mem _ _ (by rintro _ ⟨w, hw, rfl⟩; exact hw.1) b x hb'
    obtain ⟨k, hk⟩ : ∃ k, b.rep k ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact b.rep_nonzero (funext hh)
    obtain ⟨hd, hp, heq⟩ := pairClosure_pivot_reconstruction (liftedParameterPairs C Γ H)
      b.rep b.rep_nonzero (by rw [Projectivization.mk_rep]; exact hbW)
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      (by rw [Prod.mk.eta, Equiv.apply_symm_apply]; exact hk)
    refine ⟨Projectivization.mk ℂ _ hd, Projectivization.mk ℂ _ hp, ?_⟩
    rw [heq, Projectivization.mk_rep]
    exact hb

end Ruling

end

end RulingMaps

end DistinctDistances.TrackB
