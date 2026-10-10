import DistinctDistances.Foundations.DegreeFacts
import DistinctDistances.TrackB.RulingMapsAux
import DistinctDistances.TrackB.FlatIdentificationSupport
import DistinctDistances.TrackB.NullProjectiveSupport
import DistinctDistances.TrackB.ParameterImageSupport
import DistinctDistances.TrackE.RequestsWideFlat
import DistinctDistances.TrackA.AlgebraicFieldFiberSupport

/-!
Helpers for B11 (`conc:deg-fiber-degree`, concentration.tex:662–688).

* Degrees in the shared model: a projectivized nonzero linear space has degree one, a finite
  point set has degree its cardinality, and a projective line together with finitely many points
  has degree one (affine Hilbert sandwich).
* Point fibres of the parameter closure: a parameter whose flat contains `z` is a graph parameter.
-/

namespace DistinctDistances.TrackB.B11

noncomputable section
open scoped BigOperators

/-! ### Linear functionals and linear subspaces -/

def dualPoly {n : ℕ} (φ : Module.Dual ℂ (Point n)) : Poly n :=
  ∑ i : Fin n, MvPolynomial.C (φ (Pi.single i 1)) * MvPolynomial.X i

theorem aeval_dualPoly {n : ℕ} (φ : Module.Dual ℂ (Point n)) (x : Point n) :
    MvPolynomial.aeval x (dualPoly φ) = φ x := by
  have hx : x = ∑ i : Fin n, x i • (Pi.single i (1 : ℂ) : Point n) := by
    simpa using ((Pi.basisFun ℂ (Fin n)).sum_repr x).symm
  conv_rhs => rw [hx]
  simp only [dualPoly, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    map_smul, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A linear subspace is Zariski closed. -/
theorem zeroLocus_vanishingIdeal_submodule {n : ℕ} (L : Submodule ℂ (Point n)) :
    MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ (L : Set (Point n))) = L := by
  apply Set.Subset.antisymm _ (MvPolynomial.zeroLocus_vanishingIdeal_le _)
  intro x hx
  by_contra hnot
  obtain ⟨φ, hφx, hφL⟩ := L.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hf : dualPoly φ ∈ MvPolynomial.vanishingIdeal ℂ (L : Set (Point n)) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    rw [aeval_dualPoly]
    have hmem : φ y ∈ L.map φ := ⟨y, hy, rfl⟩
    rw [hφL] at hmem
    simpa using hmem
  have h := (MvPolynomial.mem_zeroLocus_iff.mp hx) _ hf
  rw [aeval_dualPoly] at h
  exact hφx h

theorem linearProjectivePlane_mem_iff {n : ℕ} (L : Submodule ℂ (Point n))
    (p : ProjectivePoint n) :
    p ∈ (linearProjectivePlane L).points ↔ p.rep ∈ L := by
  constructor
  · intro hp
    by_contra hnot
    obtain ⟨φ, hφrep, hφL⟩ := L.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    let T : Set (ProjectivePoint n) :=
      {q | ∃ x ∈ L, ∃ hx : x ≠ 0, Projectivization.mk ℂ x hx = q}
    have hf : dualPoly φ ∈ ProjectiveVariety.vanishingIdeal T := by
      apply MvPolynomial.mem_vanishingIdeal_iff.mpr
      rintro w ⟨hw0, x, hxL, hx0, hxw⟩
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ hw0 hx0).mp hxw.symm
      change (c : ℂ) • x = w at hc
      have hφx : φ x = 0 := by
        have hmem : φ x ∈ L.map φ := ⟨x, hxL, rfl⟩
        rw [hφL] at hmem
        simpa using hmem
      rw [aeval_dualPoly, ← hc]
      simp [hφx]
    have hfp := hp p.rep p.rep_nonzero (Projectivization.mk_rep p)
    have h := (MvPolynomial.mem_zeroLocus_iff.mp hfp) _ hf
    rw [aeval_dualPoly] at h
    exact hφrep h
  · intro hp
    apply ProjectiveVariety.subset_closure
    exact ⟨p.rep, hp, p.rep_nonzero, Projectivization.mk_rep p⟩

theorem mk_mem_linearProjectivePlane {n : ℕ} (L : Submodule ℂ (Point n)) (x : Point n)
    (hx : x ≠ 0) : Projectivization.mk ℂ x hx ∈ (linearProjectivePlane L).points ↔ x ∈ L := by
  rw [linearProjectivePlane_mem_iff]
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  rw [← hc]
  constructor
  · intro h
    have := L.smul_mem ((c⁻¹ : ℂˣ) : ℂ) h
    simpa [smul_smul] using this
  · intro h
    exact L.smul_mem _ h

/-- An injective linear parametrization of a subspace. -/
theorem submodule_parametrization {n : ℕ} (L : Submodule ℂ (Point n)) :
    ∃ φ : Point (Module.finrank ℂ L) →ₗ[ℂ] Point n, Function.Injective φ ∧
      (L : Set (Point n)) = {x | ∃ t, x = 0 + φ t} := by
  let b := Module.finBasis ℂ L
  let φ : Point (Module.finrank ℂ L) →ₗ[ℂ] Point n := L.subtype.comp b.equivFun.symm.toLinearMap
  refine ⟨φ, Subtype.val_injective.comp b.equivFun.symm.injective, ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
    simp [φ]
  · rintro ⟨t, rfl⟩
    rw [zero_add]
    exact (b.equivFun.symm t).2

theorem closure_submodule_points {n : ℕ} (L : Submodule ℂ (Point n)) :
    (AffineVariety.closure (L : Set (Point n))).points = L :=
  zeroLocus_vanishingIdeal_submodule L

theorem closure_submodule_irreducible {n : ℕ} (L : Submodule ℂ (Point n)) :
    (AffineVariety.closure (L : Set (Point n))).IsIrreducible := by
  obtain ⟨φ, _, hset⟩ := submodule_parametrization L
  change (MvPolynomial.vanishingIdeal ℂ (L : Set (Point n))).IsPrime
  rw [hset]
  exact vanishingIdeal_affineLinearImage_prime 0 φ

theorem closure_submodule_dimension {n : ℕ} (L : Submodule ℂ (Point n)) :
    (AffineVariety.closure (L : Set (Point n))).dimension = Module.finrank ℂ L := by
  obtain ⟨φ, hφ, hset⟩ := submodule_parametrization L
  have h := Request.affine_linear_principal_open_dimension 0 φ hφ (1 : Poly n) 0 (by simp)
  have hset' : {x : Point n | ∃ t, x = 0 + φ t ∧ MvPolynomial.aeval x (1 : Poly n) ≠ 0} =
      (L : Set (Point n)) := by
    rw [hset]
    ext x
    simp
  rw [hset'] at h
  exact h

theorem closure_submodule_degree {n : ℕ} (L : Submodule ℂ (Point n)) :
    (AffineVariety.closure (L : Set (Point n))).degree = 1 := by
  apply Request.affine_flat_degree_one _ (closure_submodule_irreducible L)
  refine ⟨L.toAffineSubspace, ?_⟩
  rw [closure_submodule_points]
  rfl

theorem linearProjectivePlane_affineCone {n : ℕ} (L : Submodule ℂ (Point n)) (hL : L ≠ ⊥) :
    (linearProjectivePlane L).affineCone = AffineVariety.closure (L : Set (Point n)) := by
  apply AffineVariety.ext
  change (linearProjectivePlane L).ideal = MvPolynomial.vanishingIdeal ℂ (L : Set (Point n))
  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  exact linearProjectivePlane_cone_ideal L ⟨x, hxL, hx0⟩

theorem linearProjectivePlane_points_nonempty {n : ℕ} (L : Submodule ℂ (Point n))
    (hL : L ≠ ⊥) : (linearProjectivePlane L).points.Nonempty := by
  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  exact ⟨Projectivization.mk ℂ x hx0, (mk_mem_linearProjectivePlane L x hx0).mpr hxL⟩

theorem linearProjectivePlane_irreducible {n : ℕ} (L : Submodule ℂ (Point n)) (hL : L ≠ ⊥) :
    (linearProjectivePlane L).IsIrreducible := by
  have h := closure_submodule_irreducible L
  rw [← linearProjectivePlane_affineCone L hL] at h
  exact h

theorem linearProjectivePlane_dimension {n : ℕ} (L : Submodule ℂ (Point n)) (hL : L ≠ ⊥) :
    (linearProjectivePlane L).dimension + 1 = Module.finrank ℂ L := by
  rw [← ProjectiveVariety.dimension_cone _ (linearProjectivePlane_points_nonempty L hL),
    linearProjectivePlane_affineCone L hL, closure_submodule_dimension]

theorem linearProjectivePlane_degree {n : ℕ} (L : Submodule ℂ (Point n)) (hL : L ≠ ⊥) :
    (linearProjectivePlane L).degree = 1 := by
  rw [← ProjectiveVariety.degree_cone, linearProjectivePlane_affineCone L hL,
    closure_submodule_degree]

/-! ### Points as projective varieties -/

/-- The projective point `p` as a linear projective plane. -/
def pointVariety {n : ℕ} (p : ProjectivePoint n) : ProjectiveVariety n :=
  linearProjectivePlane (ℂ ∙ p.rep)

theorem span_rep_ne_bot {n : ℕ} (p : ProjectivePoint n) : (ℂ ∙ p.rep) ≠ ⊥ := by
  simpa using p.rep_nonzero

theorem pointVariety_mem_iff {n : ℕ} (p q : ProjectivePoint n) :
    q ∈ (pointVariety p).points ↔ q = p := by
  rw [pointVariety, linearProjectivePlane_mem_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact q.rep_nonzero (by simpa using hc.symm)
    rw [← Projectivization.mk_rep q, ← Projectivization.mk_rep p]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ q.rep_nonzero p.rep_nonzero).mpr ⟨c, hc⟩
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

theorem pointVariety_points {n : ℕ} (p : ProjectivePoint n) :
    (pointVariety p).points = {p} := by
  ext q
  exact pointVariety_mem_iff p q

theorem pointVariety_irreducible {n : ℕ} (p : ProjectivePoint n) :
    (pointVariety p).IsIrreducible :=
  linearProjectivePlane_irreducible _ (span_rep_ne_bot p)

theorem pointVariety_dimension {n : ℕ} (p : ProjectivePoint n) :
    (pointVariety p).dimension = 0 := by
  have h := linearProjectivePlane_dimension _ (span_rep_ne_bot p)
  rw [finrank_span_singleton p.rep_nonzero] at h
  change (pointVariety p).dimension + 1 = 1 at h
  omega

theorem pointVariety_degree {n : ℕ} (p : ProjectivePoint n) : (pointVariety p).degree = 1 :=
  linearProjectivePlane_degree _ (span_rep_ne_bot p)

theorem pointVariety_injective {n : ℕ} : Function.Injective (pointVariety (n := n)) := by
  intro p q h
  have hp : p ∈ (pointVariety p).points := (pointVariety_mem_iff p p).mpr rfl
  rw [h, pointVariety_mem_iff] at hp
  exact hp

theorem pointVariety_affineCone_dimension {n : ℕ} (p : ProjectivePoint n) :
    (pointVariety p).affineCone.dimension = 1 := by
  rw [ProjectiveVariety.dimension_cone _ ⟨p, (pointVariety_mem_iff p p).mpr rfl⟩,
    pointVariety_dimension]

/-- A finite set of projective points has degree its cardinality. -/
theorem closure_finset_degree {n : ℕ} (T : Finset (ProjectivePoint n)) :
    (ProjectiveVariety.closure (T : Set (ProjectivePoint n))).degree = T.card := by
  classical
  let F : ProjectiveFamily.Family n := T.image pointVariety
  have hpure : ProjectiveFamily.IsPure F 0 := by
    intro V hV
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨pointVariety_irreducible p, pointVariety_dimension p⟩
  have hunion : (⋃ V ∈ F, V.points) = (T : Set (ProjectivePoint n)) := by
    ext q
    simp only [Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨V, hV, hqV⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hV
      rw [pointVariety_mem_iff] at hqV
      exact hqV ▸ hp
    · intro hq
      exact ⟨pointVariety q, Finset.mem_image_of_mem _ hq, (pointVariety_mem_iff q q).mpr rfl⟩
  have hlocus : ProjectiveFamily.locus F = ProjectiveVariety.closure (T : Set _) := by
    change ProjectiveVariety.closure (⋃ V ∈ F, V.points) = _
    rw [hunion]
  rw [← hlocus, ProjectiveFamily.degree_locus F 0 hpure]
  change ∑ V ∈ T.image pointVariety, V.degree = _
  rw [Finset.sum_image (fun p _ q _ h => pointVariety_injective h)]
  simp [pointVariety_degree]

/-! ### A projective line together with finitely many points -/

theorem vanishingIdeal_union {n : ℕ} (S S' : Set (ProjectivePoint n)) :
    ProjectiveVariety.vanishingIdeal (S ∪ S') =
      ProjectiveVariety.vanishingIdeal S ⊓ ProjectiveVariety.vanishingIdeal S' := by
  ext f
  simp only [ProjectiveVariety.vanishingIdeal, Submodule.mem_inf,
    MvPolynomial.mem_vanishingIdeal_iff, ProjectiveVariety.nonzeroRepresentatives,
    Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun x ⟨hx, hS⟩ => h x ⟨hx, Or.inl hS⟩, fun x ⟨hx, hS⟩ => h x ⟨hx, Or.inr hS⟩⟩
  · rintro ⟨h1, h2⟩ x ⟨hx, hS | hS⟩
    · exact h1 x ⟨hx, hS⟩
    · exact h2 x ⟨hx, hS⟩

theorem vanishingIdeal_finset {n : ℕ} (T : Finset (ProjectivePoint n)) :
    ProjectiveVariety.vanishingIdeal (T : Set (ProjectivePoint n)) =
      ⨅ p ∈ T, (pointVariety p).ideal := by
  ext f
  simp only [Submodule.mem_iInf]
  constructor
  · intro hf p hp
    rw [← ProjectiveVariety.vanishingIdeal_points (pointVariety p), pointVariety_points]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro x ⟨hx, hxp⟩
    rw [Set.mem_singleton_iff] at hxp
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hf) x ⟨hx, by rw [hxp]; exact hp⟩
  · intro hf
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro x ⟨hx, hxT⟩
    have hp := hf _ hxT
    have hxp : Projectivization.mk ℂ x hx ∈ (pointVariety (Projectivization.mk ℂ x hx)).points :=
      (pointVariety_mem_iff _ _).mpr rfl
    rw [ProjectiveVariety.mem_points_mk_iff] at hxp
    exact (MvPolynomial.mem_zeroLocus_iff.mp hxp) f hp

theorem sum_insert_le_of_nonneg {α : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (g : α → ℕ) : ∑ x ∈ insert a s, g x ≤ g a + ∑ x ∈ s, g x := by
  by_cases ha : a ∈ s
  · rw [Finset.insert_eq_of_mem ha]
    omega
  · rw [Finset.sum_insert ha]

/-- **Line plus points.** If `A` closes up to a projective line, adding finitely many points
does not change the degree. -/
theorem closure_union_finset_degree {n : ℕ} (A : Set (ProjectivePoint n))
    (L : Submodule ℂ (Point n)) (hL : Module.finrank ℂ L = 2)
    (hA : ProjectiveVariety.closure A = linearProjectivePlane L)
    (T : Finset (ProjectivePoint n)) :
    (ProjectiveVariety.closure (A ∪ (T : Set (ProjectivePoint n)))).degree = 1 := by
  classical
  have hLne : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hL
    omega
  let W := ProjectiveVariety.closure (A ∪ (T : Set (ProjectivePoint n)))
  let Lc := (linearProjectivePlane L).affineCone
  let Pc : ProjectivePoint n → AffineVariety n := fun p => (pointVariety p).affineCone
  let F : AffineFamily.Family n := insert Lc (T.image Pc)
  have hWideal : W.ideal = Lc.ideal ⊓ ⨅ p ∈ T, (Pc p).ideal := by
    change ProjectiveVariety.vanishingIdeal (A ∪ (T : Set (ProjectivePoint n))) = _
    rw [vanishingIdeal_union, vanishingIdeal_finset]
    congr 1
    change ProjectiveVariety.vanishingIdeal A = (linearProjectivePlane L).ideal
    rw [← hA]
    rfl
  have hFinf : (⨅ V ∈ F, V.ideal) = W.ideal := by
    rw [hWideal]
    ext f
    simp only [Submodule.mem_iInf, Submodule.mem_inf, F, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro h
      exact ⟨h Lc (Or.inl rfl), fun p hp => h (Pc p) (Or.inr ⟨p, hp, rfl⟩)⟩
    · rintro ⟨h1, h2⟩ V (rfl | ⟨p, hp, rfl⟩)
      · exact h1
      · exact h2 p hp
  have hrad : (⨅ V ∈ F, V.ideal).IsRadical := by
    apply Ideal.isRadical_iInf
    intro V
    apply Ideal.isRadical_iInf
    intro _
    exact V.isRadical
  have hWc : W.affineCone = AffineFamily.locus F := by
    apply AffineVariety.ext
    change W.ideal = (⨅ V ∈ F, V.ideal).radical
    rw [hrad.radical, hFinf]
  -- Hilbert sandwich
  have hlow : ∀ D, Lc.hilbert D ≤ W.affineCone.hilbert D := by
    intro D
    apply AffineVariety.hilbert_mono
    change W.ideal ≤ Lc.ideal
    rw [hWideal]
    exact inf_le_left
  have hup : ∀ D, W.affineCone.hilbert D ≤ Lc.hilbert D + ∑ p ∈ T, (Pc p).hilbert D := by
    intro D
    have h1 := AffineFamily.hilbert_le_sum F D
    rw [AffineFamily.hilbert, ← hWc] at h1
    refine h1.trans ((sum_insert_le_of_nonneg _ _ _).trans ?_)
    apply Nat.add_le_add_left
    exact Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
  -- polynomials
  let PW := W.affineCone.hilbertPolynomial
  let PL := Lc.hilbertPolynomial
  let PT := ∑ p ∈ T, (Pc p).hilbertPolynomial
  have hPL : PL.natDegree = 2 := by
    show (linearProjectivePlane L).affineCone.dimension = 2
    rw [linearProjectivePlane_affineCone L hLne, closure_submodule_dimension, hL]
  have hPT : PT.natDegree ≤ 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro p _
    exact (pointVariety_affineCone_dimension p).le
  have hevT : ∀ᶠ D : ℕ in Filter.atTop, ∀ p ∈ T,
      ((Pc p).hilbert D : ℚ) = (Pc p).hilbertPolynomial.eval (D : ℚ) :=
    (Filter.eventually_all_finset T).mpr (fun p _ => (Pc p).hilbert_eventually)
  have hΔ0 : ∀ᶠ D : ℕ in Filter.atTop, 0 ≤ (PW - PL).eval (D : ℚ) := by
    filter_upwards [W.affineCone.hilbert_eventually, Lc.hilbert_eventually] with D hW hL'
    rw [Polynomial.eval_sub, ← hW, ← hL', sub_nonneg]
    exact_mod_cast hlow D
  have hΔle : ∀ᶠ D : ℕ in Filter.atTop, (PW - PL).eval (D : ℚ) ≤ PT.eval (D : ℚ) := by
    filter_upwards [W.affineCone.hilbert_eventually, Lc.hilbert_eventually, hevT]
      with D hW hL' hT
    rw [Polynomial.eval_sub, ← hW, ← hL', Polynomial.eval_finset_sum,
      ← Finset.sum_congr rfl hT, sub_le_iff_le_add']
    exact_mod_cast hup D
  have hΔ : (PW - PL).natDegree ≤ 1 :=
    (OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _ hΔ0 hΔle).trans hPT
  have hPW : PW = PL + (PW - PL) := by ring
  have hcoeff : PW.coeff 2 = PL.coeff 2 := by
    rw [hPW, Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hΔ (by norm_num)), add_zero]
  have hdegW : PW.natDegree = 2 := by
    rw [hPW, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega), hPL]
  have hLdeg : Lc.degree = 1 := by
    show (linearProjectivePlane L).affineCone.degree = 1
    rw [linearProjectivePlane_affineCone L hLne, closure_submodule_degree]
  rw [← ProjectiveVariety.degree_cone]
  change OAI.QuarticPowerFree.affineDegree W.ideal = 1
  change OAI.QuarticPowerFree.affineDegree Lc.ideal = 1 at hLdeg
  unfold OAI.QuarticPowerFree.affineDegree at hLdeg ⊢
  unfold OAI.QuarticPowerFree.affineDimension at hLdeg ⊢
  change ((PW.natDegree).factorial : ℚ) * PW.coeff PW.natDegree = 1
  change ((PL.natDegree).factorial : ℚ) * PL.coeff PL.natDegree = 1 at hLdeg
  rw [hdegW, hcoeff]
  rw [hPL] at hLdeg
  exact hLdeg

/-! ### Point fibres of parameters -/

section Fibres

variable {e : ℕ} (C : SkewCoordinates e)

theorem covectorOfPoint_smul (c : ℂ) (y : Point e) :
    covectorOfPoint (c • y) = c • covectorOfPoint y :=
  (pointCovectorLinear e).map_smul c y

theorem secondPoint_smul {n m : ℕ} (c : ℂ) (w : Point (n + m)) :
    secondPoint (c • w) = c • secondPoint w := by
  funext i
  rfl

theorem secondPoint_graphVector (z : Point (skewDim e)) (v : Point e) :
    secondPoint (graphVector C z v) = pointOfCovector ((C.decode z).val v) := by
  simp [graphVector, RulingMaps.secondPoint_joinPoints]

/-- Flat membership is unchanged by rescaling the representative. -/
theorem flat_smul_iff (z : Point (skewDim e)) (c : ℂ) (hc : c ≠ 0) (w : Point (e + e)) :
    (C.decode z).val (firstPoint (c • w)) = covectorOfPoint (secondPoint (c • w)) ↔
      (C.decode z).val (firstPoint w) = covectorOfPoint (secondPoint w) := by
  rw [RulingMaps.firstPoint_smul, secondPoint_smul, covectorOfPoint_smul, map_smul]
  constructor
  · intro h
    have := congrArg (fun y => c⁻¹ • y) h
    simpa [smul_smul, inv_mul_cancel₀ hc] using this
  · intro h
    rw [h]

theorem flat_rep_iff (z : Point (skewDim e)) (w : Point (e + e)) (hw : w ≠ 0) :
    z ∈ evaluationFlat C (Projectivization.mk ℂ w hw) ↔
      (C.decode z).val (firstPoint w) = covectorOfPoint (secondPoint w) := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ w hw
  change (C.decode z).val (firstPoint (Projectivization.mk ℂ w hw).rep) =
    covectorOfPoint (secondPoint (Projectivization.mk ℂ w hw).rep) ↔ _
  rw [← hc, Units.smul_def]
  exact flat_smul_iff C z c c.ne_zero w

/-- A vector satisfying the flat equation is the graph vector of its first block. -/
theorem graphVector_of_flat (z : Point (skewDim e)) (w : Point (e + e))
    (h : (C.decode z).val (firstPoint w) = covectorOfPoint (secondPoint w)) :
    graphVector C z (firstPoint w) = w := by
  rw [graphVector, h, point_covector_inverse, joinPoints_eta]

theorem first_ne_zero_of_flat (z : Point (skewDim e)) (w : Point (e + e)) (hw : w ≠ 0)
    (h : (C.decode z).val (firstPoint w) = covectorOfPoint (secondPoint w)) :
    firstPoint w ≠ 0 := by
  intro h0
  have hsec : secondPoint w = 0 := by
    rw [← point_covector_inverse (secondPoint w), ← h, h0, map_zero]
    rfl
  apply hw
  funext k
  refine Fin.addCases (fun l => ?_) (fun l => ?_) k
  · exact congrFun h0 l
  · exact congrFun hsec l

theorem eq_graphParameter_of_flat (z : Point (skewDim e)) (p : ProjectivePoint (e + e))
    (hz : z ∈ evaluationFlat C p) :
    ∃ hv : firstPoint p.rep ≠ 0, p = graphParameter C z (firstPoint p.rep) hv := by
  have hz' : (C.decode z).val (firstPoint p.rep) = covectorOfPoint (secondPoint p.rep) := hz
  refine ⟨first_ne_zero_of_flat C z p.rep p.rep_nonzero hz', ?_⟩
  conv_lhs => rw [← Projectivization.mk_rep p]
  exact RulingMaps.mk_congr (graphVector_of_flat C z p.rep hz').symm _ _

theorem mem_flat_graphParameter (z : Point (skewDim e)) (v : Point e) (hv : v ≠ 0) :
    z ∈ evaluationFlat C (graphParameter C z v hv) := by
  rw [graphParameter, flat_rep_iff, RulingMaps.firstPoint_graphVector, secondPoint_graphVector,
    covector_point_inverse]

theorem graphParameter_injective (z : Point (skewDim e)) (a : Fin e) (v w : Point e)
    (hv : v ≠ 0) (hw : w ≠ 0) (hva : v a = 1) (hwa : w a = 1)
    (h : graphParameter C z v hv = graphParameter C z w hw) : v = w := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ (graphVector_ne_zero C z v hv)
    (graphVector_ne_zero C z w hw)).mp h
  have hfirst := congrArg firstPoint hc
  rw [RulingMaps.firstPoint_smul, RulingMaps.firstPoint_graphVector,
    RulingMaps.firstPoint_graphVector] at hfirst
  have hca : c = 1 := by
    have := congrFun hfirst a
    simpa [hva, hwa] using this
  rw [hca, one_smul] at hfirst
  exact hfirst.symm

end Fibres

/-! ### Generic cardinality of the direction fibres -/

section Count

variable {e : ℕ} (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))

theorem aeval_rename_castAdd (w : Point (skewDim e + e)) (f : Poly (skewDim e)) :
    MvPolynomial.aeval w (MvPolynomial.rename (Fin.castAdd e) f) =
      MvPolynomial.aeval (firstPoint w) f := by
  rw [MvPolynomial.aeval_rename]
  rfl

theorem base_le_comap (hcont : ∀ w ∈ Γ.points, firstPoint w ∈ V) :
    V.ideal ≤ Γ.ideal.comap (MvPolynomial.rename (Fin.castAdd e) :
      Poly (skewDim e) →ₐ[ℂ] Poly (skewDim e + e)) := by
  intro f hf
  rw [Ideal.mem_comap, ← Γ.vanishingIdeal_points]
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  intro w hw
  rw [aeval_rename_castAdd]
  exact (MvPolynomial.mem_zeroLocus_iff.mp (hcont w hw)) f hf

/-- Restriction of base coordinates to the incidence. -/
def baseMap (hcont : ∀ w ∈ Γ.points, firstPoint w ∈ V) :
    (Poly (skewDim e) ⧸ V.ideal) →ₐ[ℂ] (Poly (skewDim e + e) ⧸ Γ.ideal) :=
  Ideal.quotientMapₐ Γ.ideal (MvPolynomial.rename (Fin.castAdd e)) (base_le_comap V Γ hcont)

theorem baseMap_mk (hcont : ∀ w ∈ Γ.points, firstPoint w ∈ V) (f : Poly (skewDim e)) :
    baseMap V Γ hcont (Ideal.Quotient.mk V.ideal f) =
      Ideal.Quotient.mk Γ.ideal (MvPolynomial.rename (Fin.castAdd e) f) := rfl

theorem baseMap_injective (hV : V.IsIrreducible) (H : Poly (skewDim e)) (hH : H ∉ V.ideal)
    (hcont : ∀ w ∈ Γ.points, firstPoint w ∈ V)
    (hdom : ∀ z ∈ workingPoints V H, (directionFiber Γ z).Nonempty) :
    Function.Injective (baseMap V Γ hcont) := by
  rw [injective_iff_map_eq_zero]
  intro r h12
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [baseMap_mk, Ideal.Quotient.eq_zero_iff_mem] at h12
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hfH : f * H ∈ V.ideal := by
    rw [← V.vanishingIdeal_points]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro z hz
    rw [map_mul]
    by_cases hHz : MvPolynomial.aeval z H = 0
    · rw [hHz, mul_zero]
    · obtain ⟨v, hv⟩ := hdom z ⟨hz, hHz⟩
      have hw : joinPoints z v ∈ Γ.points := hv
      have h0 := (MvPolynomial.mem_zeroLocus_iff.mp hw) _ h12
      rw [aeval_rename_castAdd, RulingMaps.firstPoint_joinPoints] at h0
      rw [h0, zero_mul]
  exact ((hV.mem_or_mem hfH).resolve_right hH)

/-- **Generic fibre count.** For an equidimensional dominant incidence, the direction fibres over
a nonempty principal open of `V` are finite of one constant cardinality. -/
theorem generic_direction_count (hV : V.IsIrreducible) (hΓ : Γ.IsIrreducible)
    (H : Poly (skewDim e)) (hH : H ∉ V.ideal)
    (hcont : ∀ w ∈ Γ.points, firstPoint w ∈ V)
    (hdom : ∀ z ∈ workingPoints V H, (directionFiber Γ z).Nonempty)
    (hdim : Γ.dimension = V.dimension) :
    ∃ g : Poly (skewDim e), g ∉ V.ideal ∧ ∃ r : ℕ, ∀ z ∈ V.points,
      MvPolynomial.aeval z g ≠ 0 →
        (directionFiber Γ z).Finite ∧ (directionFiber Γ z).ncard = r := by
  classical
  letI : V.ideal.IsPrime := hV
  letI : Γ.ideal.IsPrime := hΓ
  let R := Poly (skewDim e) ⧸ V.ideal
  let B := Poly (skewDim e + e) ⧸ Γ.ideal
  let φ := baseMap V Γ hcont
  letI : Algebra R B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ R B := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  have hinj : Function.Injective (algebraMap R B) := baseMap_injective V Γ hV H hH hcont hdom
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hinj
  haveI : FaithfulSMul ℂ R :=
    (faithfulSMul_iff_algebraMap_injective ℂ R).mpr (algebraMap ℂ R).injective
  haveI : FaithfulSMul ℂ B :=
    (faithfulSMul_iff_algebraMap_injective ℂ B).mpr (algebraMap ℂ B).injective
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℂ R).injective
  haveI : Module.IsTorsionFree R B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Algebra.FiniteType R B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R B
  have hR : Algebra.trdeg ℂ R = (V.dimension : Cardinal) :=
    (GenericFiber.affineDimension_eq_trdeg V.ideal).symm
  have hB : Algebra.trdeg ℂ B = (V.dimension : Cardinal) := by
    rw [← hdim]
    exact (GenericFiber.affineDimension_eq_trdeg Γ.ideal).symm
  haveI : Algebra.IsAlgebraic R B :=
    TrackA.algebraic_of_equal_finite_trdeg ℂ R B V.dimension hR hB
  obtain ⟨g, hg, r, _, hcount⟩ := TrackA.algebraic_finiteType_field_hom_fibers R B
  obtain ⟨g0, rfl⟩ := Ideal.Quotient.mk_surjective g
  refine ⟨g0, fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mpr h), r, ?_⟩
  intro z hz hgz
  have hzle : V.ideal ≤ RingHom.ker (MvPolynomial.aeval z : Poly (skewDim e) →ₐ[ℂ] ℂ).toRingHom :=
    fun f hf => (MvPolynomial.mem_zeroLocus_iff.mp hz) f hf
  let evz : R →+* ℂ := Ideal.Quotient.lift V.ideal
    (MvPolynomial.aeval z : Poly (skewDim e) →ₐ[ℂ] ℂ).toRingHom hzle
  letI : Algebra R ℂ := evz.toAlgebra
  have hevz : ∀ f, algebraMap R ℂ (Ideal.Quotient.mk V.ideal f) = MvPolynomial.aeval z f :=
    fun f => rfl
  haveI : IsScalarTower ℂ R ℂ := IsScalarTower.of_algebraMap_eq (R := ℂ) (S := R) (A := ℂ)
    (fun c => by
    have h1 : algebraMap ℂ R c = Ideal.Quotient.mk V.ideal (MvPolynomial.C c) := rfl
    rw [h1, hevz, MvPolynomial.aeval_C]
    )
  obtain ⟨hfinite, hcard⟩ := hcount ℂ (by rw [hevz]; exact hgz)
  -- the bijection between `R`-points of `B` and the direction fibre
  let pt : (B →ₐ[R] ℂ) → Point (skewDim e + e) := fun ψ k =>
    ψ (Ideal.Quotient.mk Γ.ideal (MvPolynomial.X k))
  have hpt_eval : ∀ ψ : B →ₐ[R] ℂ, ∀ f : Poly (skewDim e + e),
      ψ (Ideal.Quotient.mk Γ.ideal f) = MvPolynomial.aeval (pt ψ) f := by
    intro ψ f
    have he : (MvPolynomial.aeval (pt ψ) : Poly (skewDim e + e) →ₐ[ℂ] ℂ) =
        ((ψ.restrictScalars ℂ).comp (Ideal.Quotient.mkₐ ℂ Γ.ideal)) := by
      apply MvPolynomial.algHom_ext
      intro k
      simp [pt]
      rfl
    rw [he]
    rfl
  have hpt_first : ∀ ψ : B →ₐ[R] ℂ, firstPoint (pt ψ) = z := by
    intro ψ
    funext i
    have h1 := ψ.commutes (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))
    change ψ (φ (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))) = _ at h1
    rw [baseMap_mk, hevz, MvPolynomial.rename_X, MvPolynomial.aeval_X] at h1
    exact h1
  have hpt_mem : ∀ ψ : B →ₐ[R] ℂ, pt ψ ∈ Γ.points := by
    intro ψ
    apply MvPolynomial.mem_zeroLocus_iff.mpr
    intro f hf
    rw [← hpt_eval, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  let Ψ : (B →ₐ[R] ℂ) → directionFiber Γ z := fun ψ =>
    ⟨secondPoint (pt ψ), by
      change joinPoints z (secondPoint (pt ψ)) ∈ Γ.points
      rw [← hpt_first ψ, joinPoints_eta]
      exact hpt_mem ψ⟩
  have hΨinj : Function.Injective Ψ := by
    intro ψ1 ψ2 h
    have hsec : secondPoint (pt ψ1) = secondPoint (pt ψ2) := congrArg Subtype.val h
    have hpt : pt ψ1 = pt ψ2 := by
      rw [← joinPoints_eta (pt ψ1), ← joinPoints_eta (pt ψ2), hpt_first, hpt_first, hsec]
    apply AlgHom.ext
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hpt_eval, hpt_eval, hpt]
  have hΨsurj : Function.Surjective Ψ := by
    rintro ⟨v, hv⟩
    let w : Point (skewDim e + e) := joinPoints z v
    have hw : w ∈ Γ.points := hv
    let ψ0 : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Γ.ideal (MvPolynomial.aeval w)
      (fun f hf => (MvPolynomial.mem_zeroLocus_iff.mp hw) f hf)
    let ψ : B →ₐ[R] ℂ :=
      { ψ0.toRingHom with
        commutes' := by
          intro r
          obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
          change ψ0 (φ (Ideal.Quotient.mk V.ideal f)) = _
          rw [baseMap_mk, hevz]
          change MvPolynomial.aeval w (MvPolynomial.rename (Fin.castAdd e) f) = _
          rw [aeval_rename_castAdd, RulingMaps.firstPoint_joinPoints] }
    refine ⟨ψ, ?_⟩
    apply Subtype.ext
    change secondPoint (pt ψ) = v
    have hptw : pt ψ = w := by
      funext k
      change MvPolynomial.aeval w (MvPolynomial.X k) = w k
      exact MvPolynomial.aeval_X w k
    rw [hptw, RulingMaps.secondPoint_joinPoints]
  have hbij : Function.Bijective Ψ := ⟨hΨinj, hΨsurj⟩
  haveI := hfinite
  haveI : Finite (directionFiber Γ z) := Finite.of_surjective Ψ hΨsurj
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, ← Nat.card_eq_of_bijective Ψ hbij, hcard]

end Count

end

end DistinctDistances.TrackB.B11
