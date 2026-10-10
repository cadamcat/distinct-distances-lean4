import DistinctDistances.Foundations.Projective
import DistinctDistances.TrackA.ProjectiveChartSupport
import DistinctDistances.TrackA.PointPowerLengthSupport
import DistinctDistances.TrackA.ChartIdealSupport
import DistinctDistances.TrackA.ProjectiveChartRankSupport
import DistinctDistances.Foundations.Local
import DistinctDistances.Foundations.Projection
import DistinctDistances.TrackA.AlgebraicFieldFiberSupport
import DistinctDistances.Foundations.GenericFiber
import DistinctDistances.TrackA.ProjectionSourceSupport
import DistinctDistances.TrackA.RetractionLengthAux
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import OAI.NumberTheory.PowerFree.ResidueBounds
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PointProjection

theorem finSuccEquiv_rename {n : ℕ} (f : Poly n) :
    MvPolynomial.finSuccEquiv ℂ n (MvPolynomial.rename Fin.succ f) = Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf, MvPolynomial.finSuccEquiv_X_succ]

theorem cons_degree {n : ℕ} (d : Fin n →₀ ℕ) (j : ℕ) :
    (d.cons j).degree = j + d.degree := by
  simp only [Finsupp.degree_eq_weight_one, Finsupp.weight_apply,
    smul_eq_mul, mul_one, Finsupp.sum_cons]

theorem homogeneous_component_mem {n : ℕ} (I : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (f : Poly n) (hf : f ∈ I) (D : ℕ) : MvPolynomial.homogeneousComponent D f ∈ I := by
  have hh := hI D hf
  change GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) D f ∈ I at hh
  rw [GradedRing.proj_apply] at hh
  change (MvPolynomial.decomposition.decompose' f D : Poly n) ∈ I at hh
  rwa [MvPolynomial.decomposition.decompose'_apply] at hh

/-- The coefficient in the eliminated variable commutes with total
homogeneous projection, with the corresponding degree shift. -/
theorem coeff_homogeneousComponent {n : ℕ} (f : Poly (n+1)) (j d : ℕ) :
    (MvPolynomial.finSuccEquiv ℂ n (MvPolynomial.homogeneousComponent (j+d) f)).coeff j =
      MvPolynomial.homogeneousComponent d ((MvPolynomial.finSuccEquiv ℂ n f).coeff j) := by
  ext a
  rw [MvPolynomial.finSuccEquiv_coeff_coeff,
    MvPolynomial.coeff_homogeneousComponent,
    MvPolynomial.coeff_homogeneousComponent,
    MvPolynomial.finSuccEquiv_coeff_coeff, cons_degree]
  simp only [Nat.add_left_cancel_iff]

theorem homogeneousComponent_degree_le {n : ℕ} (f : Poly (n+1))
    (j D : ℕ) (hf : (MvPolynomial.finSuccEquiv ℂ n f).degree ≤ j) :
    (MvPolynomial.finSuccEquiv ℂ n (MvPolynomial.homogeneousComponent D f)).degree ≤ j := by
  rw [Polynomial.degree_le_iff_coeff_zero] at hf ⊢
  intro i hi
  ext a
  rw [MvPolynomial.finSuccEquiv_coeff_coeff,
    MvPolynomial.coeff_homogeneousComponent]
  have hzero : f.coeff (a.cons i) = 0 := by
    rw [← MvPolynomial.finSuccEquiv_coeff_coeff]
    rw [hf i hi]
    rfl
  simp [hzero]

/-- Eliminate the coordinate along the center's line, retaining equations
whose degree in that coordinate is at most `j`. -/
def partialElimination {n : ℕ} (I : Ideal (Poly (n+1))) (j : ℕ) : Ideal (Poly n) :=
  (I.map (MvPolynomial.finSuccEquiv ℂ n).toRingHom).leadingCoeffNth j

/-- The stable elimination ideal is the ideal of leading coefficients. -/
def stableElimination {n : ℕ} (I : Ideal (Poly (n+1))) : Ideal (Poly n) :=
  (I.map (MvPolynomial.finSuccEquiv ℂ n).toRingHom).leadingCoeff

theorem partialElimination_zero {n : ℕ} (I : Ideal (Poly (n+1))) :
    partialElimination I 0 = I.comap (MvPolynomial.rename Fin.succ) := by
  ext f
  rw [partialElimination, Ideal.mem_leadingCoeffNth_zero, Ideal.mem_comap]
  rw [Ideal.mem_map_iff_of_surjective (MvPolynomial.finSuccEquiv ℂ n).toRingHom
    (MvPolynomial.finSuccEquiv ℂ n).surjective]
  constructor
  · rintro ⟨g, hg, heq⟩
    change MvPolynomial.finSuccEquiv ℂ n g = Polynomial.C f at heq
    have hg' : g = MvPolynomial.rename Fin.succ f := by
      apply (MvPolynomial.finSuccEquiv ℂ n).injective
      exact heq.trans (finSuccEquiv_rename f).symm
    rwa [hg'] at hg
  · intro hf
    exact ⟨MvPolynomial.rename Fin.succ f, hf, finSuccEquiv_rename f⟩

theorem mem_partialElimination_iff {n : ℕ} (I : Ideal (Poly (n+1)))
    (j : ℕ) (f : Poly n) : f ∈ partialElimination I j ↔
      ∃ g ∈ I, (MvPolynomial.finSuccEquiv ℂ n g).degree ≤ j ∧
        (MvPolynomial.finSuccEquiv ℂ n g).coeff j = f := by
  change f ∈ (I.map (MvPolynomial.finSuccEquiv ℂ n).toRingHom).leadingCoeffNth j ↔ _
  simp only [Ideal.leadingCoeffNth, Ideal.degreeLE, Submodule.mem_map,
    Submodule.mem_inf, Polynomial.mem_degreeLE, Ideal.mem_ofPolynomial,
    Polynomial.lcoeff_apply]
  constructor
  · rintro ⟨F, ⟨hFdeg, hFI⟩, hFcoeff⟩
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (MvPolynomial.finSuccEquiv ℂ n).surjective).mp hFI
    exact ⟨g, hg, hFdeg, hFcoeff⟩
  · rintro ⟨g, hg, hdeg, hcoeff⟩
    exact ⟨MvPolynomial.finSuccEquiv ℂ n g,
      ⟨hdeg, Ideal.mem_map_of_mem _ hg⟩, hcoeff⟩

theorem partialElimination_mono {n : ℕ} (I : Ideal (Poly (n+1))) :
    Monotone (partialElimination I) := by
  intro i j hij
  exact Ideal.leadingCoeffNth_mono _ hij

theorem partialElimination_le_stable {n : ℕ} (I : Ideal (Poly (n+1))) (j : ℕ) :
    partialElimination I j ≤ stableElimination I :=
  le_iSup (fun j => partialElimination I j) j

/-- Each partial elimination ideal is homogeneous in the remaining
coordinates. -/
theorem partialElimination_homogeneous {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (j : ℕ) :
    (partialElimination I j).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
  rw [Ideal.isHomogeneous_iff_forall_subset]
  intro d f hf
  change GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) d f ∈ partialElimination I j
  rw [GradedRing.proj_apply]
  change (MvPolynomial.decomposition.decompose' f d : Poly n) ∈ partialElimination I j
  rw [MvPolynomial.decomposition.decompose'_apply]
  obtain ⟨g, hg, hdeg, hcoeff⟩ := (mem_partialElimination_iff I j f).mp hf
  apply (mem_partialElimination_iff I j _).mpr
  exact ⟨MvPolynomial.homogeneousComponent (j+d) g,
    homogeneous_component_mem I hI g hg (j+d),
    homogeneousComponent_degree_le g j (j+d) hdeg,
    by rw [coeff_homogeneousComponent, hcoeff]⟩

/-- A homogeneous leading coefficient has a homogeneous original
equation as a witness, of exactly the shifted total degree. -/
theorem homogeneous_partialElimination_witness {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (j d : ℕ) (f : Poly n) (hf : f ∈ partialElimination I j)
    (hhom : f.IsHomogeneous d) :
    ∃ g ∈ I, g.IsHomogeneous (j+d) ∧
      (MvPolynomial.finSuccEquiv ℂ n g).degree ≤ j ∧
      (MvPolynomial.finSuccEquiv ℂ n g).coeff j = f := by
  obtain ⟨g, hg, hdeg, hcoeff⟩ := (mem_partialElimination_iff I j f).mp hf
  refine ⟨MvPolynomial.homogeneousComponent (j+d) g, ?_,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _,
    homogeneousComponent_degree_le g j (j+d) hdeg, ?_⟩
  · exact homogeneous_component_mem I hI g hg (j+d)
  · rw [coeff_homogeneousComponent, hcoeff,
      MvPolynomial.homogeneousComponent_eq_self hhom]

theorem stableElimination_eq_iSup {n : ℕ} (I : Ideal (Poly (n+1))) :
    stableElimination I = ⨆ j, partialElimination I j := rfl

theorem stableElimination_homogeneous {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ)) :
    (stableElimination I).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
  rw [stableElimination_eq_iSup]
  exact Ideal.IsHomogeneous.iSup (partialElimination_homogeneous I hI)

/-- Noetherianity makes the partial elimination ideals constant after a
finite number of steps. -/
theorem partialElimination_stabilizes {n : ℕ} (I : Ideal (Poly (n+1))) :
    ∃ s : ℕ, ∀ j : ℕ, s ≤ j → partialElimination I j = stableElimination I := by
  let chain : ℕ →o Submodule (Poly n) (Poly n) :=
    ⟨partialElimination I, partialElimination_mono I⟩
  obtain ⟨s, hs⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (Poly n) (Poly n)) chain
  have hstable : stableElimination I = partialElimination I s := by
    rw [stableElimination_eq_iSup]
    apply le_antisymm
    · apply iSup_le
      intro j
      by_cases hj : j ≤ s
      · exact partialElimination_mono I hj
      · exact le_of_eq ((hs j (by omega)).symm)
    · exact le_iSup (partialElimination I) s
  exact ⟨s, fun j hj => (hs j hj).symm.trans hstable.symm⟩

theorem finrank_map_add_finrank_inf_ker {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (A : Submodule K V) [Module.Finite K A] (f : V →ₗ[K] W) :
    Module.finrank K (A.map f) + Module.finrank K ↥(A ⊓ LinearMap.ker f) =
      Module.finrank K A := by
  have h := (f.domRestrict A).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he : (LinearMap.ker f).comap A.subtype =
      (A ⊓ LinearMap.ker f).comap A.subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.coe_subtype,
      and_iff_right x.property]
  rw [he, (Submodule.comapSubtypeEquivOfLe
    (show A ⊓ LinearMap.ker f ≤ A from inf_le_left)).finrank_eq] at h
  exact h

/-- Total-degree sections, filtered by the degree in the center
coordinate. This filtration has finite-dimensional terms. -/
def homogeneousBound (n D : ℕ) (j : WithBot ℕ) : Submodule ℂ (Poly (n+1)) :=
  MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D ⊓
    (((Polynomial.degreeLE (Poly n) j).restrictScalars ℂ).comap
      (MvPolynomial.finSuccEquiv ℂ n).toLinearMap)

theorem mem_homogeneousBound {n D : ℕ} {j : WithBot ℕ} {f : Poly (n+1)} :
    f ∈ homogeneousBound n D j ↔
      f.IsHomogeneous D ∧ (MvPolynomial.finSuccEquiv ℂ n f).degree ≤ j := by
  simp only [homogeneousBound, Submodule.mem_inf, Submodule.mem_comap,
    Submodule.restrictScalars_mem, MvPolynomial.mem_homogeneousSubmodule,
    Polynomial.mem_degreeLE, AlgEquiv.toLinearMap_apply]

instance homogeneousBound_finite (n D : ℕ) (j : WithBot ℕ) :
    Module.Finite ℂ (homogeneousBound n D j) :=
  Module.Finite.of_injective (Submodule.inclusion (show homogeneousBound n D j ≤
    MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D from inf_le_left))
      (Submodule.inclusion_injective _)

theorem homogeneousBound_mono (n D : ℕ) {i j : WithBot ℕ} (hij : i ≤ j) :
    homogeneousBound n D i ≤ homogeneousBound n D j := by
  intro f hf
  rw [mem_homogeneousBound] at hf ⊢
  exact ⟨hf.1, hf.2.trans hij⟩

theorem homogeneousBound_bot (n D : ℕ) : homogeneousBound n D ⊥ = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  have hz : MvPolynomial.finSuccEquiv ℂ n f = 0 :=
    Polynomial.degree_eq_bot.mp (le_bot_iff.mp (mem_homogeneousBound.mp hf).2)
  exact (MvPolynomial.finSuccEquiv ℂ n).injective (by simpa using hz)

def coefficient (n j : ℕ) : Poly (n+1) →ₗ[ℂ] Poly n :=
  ((Polynomial.lcoeff (Poly n) j).restrictScalars ℂ).comp
    (MvPolynomial.finSuccEquiv ℂ n).toLinearMap

theorem coefficient_apply {n j : ℕ} (f : Poly (n+1)) :
    coefficient n j f = (MvPolynomial.finSuccEquiv ℂ n f).coeff j := rfl

def centerLift {n : ℕ} (j : ℕ) (f : Poly n) : Poly (n+1) :=
  MvPolynomial.X 0 ^ j * MvPolynomial.rename Fin.succ f

theorem finSuccEquiv_centerLift {n : ℕ} (j : ℕ) (f : Poly n) :
    MvPolynomial.finSuccEquiv ℂ n (centerLift j f) = Polynomial.monomial j f := by
  rw [centerLift, map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero,
    finSuccEquiv_rename, mul_comm, Polynomial.C_mul_X_pow_eq_monomial]

theorem centerLift_homogeneous {n d : ℕ} (j : ℕ) (f : Poly n)
    (hf : f.IsHomogeneous d) : (centerLift j f).IsHomogeneous (j+d) := by
  have hh := (MvPolynomial.isHomogeneous_X ℂ (0 : Fin (n+1))).pow j
  have hh' : (MvPolynomial.X (0 : Fin (n+1)) ^ j : Poly (n+1)).IsHomogeneous j := by
    simpa using hh
  exact hh'.mul hf.rename_isHomogeneous

theorem centerLift_mem_bound {n d : ℕ} (j : ℕ) (f : Poly n)
    (hf : f.IsHomogeneous d) : centerLift j f ∈ homogeneousBound n (j+d) j := by
  rw [mem_homogeneousBound]
  exact ⟨centerLift_homogeneous j f hf, by
    rw [finSuccEquiv_centerLift]
    exact Polynomial.degree_monomial_le _ _⟩

theorem coefficient_bound_map {n D j : ℕ} (hj : j ≤ D) :
    (homogeneousBound n D j).map (coefficient n j) =
      MvPolynomial.homogeneousSubmodule (Fin n) ℂ (D-j) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact (mem_homogeneousBound.mp hg).1.finSuccEquiv_coeff_isHomogeneous
      j (D-j) (Nat.add_sub_of_le hj)
  · intro hf
    have hfhom := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hf
    refine ⟨centerLift j f, ?_, ?_⟩
    · change centerLift j f ∈ homogeneousBound n D j
      simpa only [Nat.add_sub_of_le hj] using centerLift_mem_bound j f hfhom
    · rw [coefficient_apply, finSuccEquiv_centerLift, Polynomial.coeff_monomial]
      simp

theorem coefficient_ideal_bound_map {n D j : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (hj : j ≤ D) :
    (homogeneousBound n D j ⊓ I.restrictScalars ℂ).map (coefficient n j) =
      MvPolynomial.homogeneousSubmodule (Fin n) ℂ (D-j) ⊓
        (partialElimination I j).restrictScalars ℂ := by
  ext f
  constructor
  · rintro ⟨g, ⟨hg, hgI⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← coefficient_bound_map hj]
      exact Submodule.mem_map.mpr ⟨g, hg, rfl⟩
    · exact (mem_partialElimination_iff I j _).mpr
        ⟨g, hgI, (mem_homogeneousBound.mp hg).2, rfl⟩
  · rintro ⟨hfhom, hfI⟩
    obtain ⟨g, hgI, hhom, hdeg, hcoeff⟩ := homogeneous_partialElimination_witness
      I hI j (D-j) f hfI ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hfhom)
    refine ⟨g, ⟨?_, hgI⟩, hcoeff⟩
    change g ∈ homogeneousBound n D j
    rw [mem_homogeneousBound]
    exact ⟨by simpa only [Nat.add_sub_of_le hj] using hhom, hdeg⟩

theorem coefficient_bound_ker_succ (n D j : ℕ) :
    homogeneousBound n D ((j+1 : ℕ) : WithBot ℕ) ⊓ LinearMap.ker (coefficient n (j+1)) =
      homogeneousBound n D j := by
  ext f
  constructor
  · rintro ⟨hf, hz⟩
    change f ∈ homogeneousBound n D ((j+1 : ℕ) : WithBot ℕ) at hf
    rw [mem_homogeneousBound] at hf ⊢
    refine ⟨hf.1, (Polynomial.degree_le_iff_coeff_zero _ _).mpr ?_⟩
    intro i hi
    have hji : j < i := by exact_mod_cast hi
    by_cases he : i = j+1
    · subst i
      exact LinearMap.mem_ker.mp hz
    · exact (Polynomial.degree_le_iff_coeff_zero _ _).mp hf.2 i
        (by exact_mod_cast (show j+1 < i by omega))
  · intro hf
    refine ⟨homogeneousBound_mono n D (by exact_mod_cast Nat.le_succ j) hf, ?_⟩
    change coefficient n (j+1) f = 0
    rw [coefficient_apply]
    exact Polynomial.coeff_eq_zero_of_degree_lt
      ((mem_homogeneousBound.mp hf).2.trans_lt (by exact_mod_cast Nat.lt_succ_self j))

theorem coefficient_bound_ker_zero (n D : ℕ) :
    homogeneousBound n D 0 ⊓ LinearMap.ker (coefficient n 0) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro f ⟨hf, hz⟩
  have hconst := Polynomial.eq_C_of_degree_le_zero (mem_homogeneousBound.mp hf).2
  have hcoeff : (MvPolynomial.finSuccEquiv ℂ n f).coeff 0 = 0 := LinearMap.mem_ker.mp hz
  have heq : MvPolynomial.finSuccEquiv ℂ n f = 0 := by
    rw [hconst, hcoeff, Polynomial.C_0]
  exact (MvPolynomial.finSuccEquiv ℂ n).injective (by simpa using heq)

def quotientBound {n : ℕ} (I : Ideal (Poly (n+1))) (D : ℕ) (j : WithBot ℕ) :
    Submodule ℂ (Poly (n+1) ⧸ I) :=
  (homogeneousBound n D j).map (Ideal.Quotient.mkₐ ℂ I).toLinearMap

instance quotientBound_finite {n : ℕ} (I : Ideal (Poly (n+1)))
    (D : ℕ) (j : WithBot ℕ) : Module.Finite ℂ (quotientBound I D j) := by
  unfold quotientBound
  infer_instance

theorem quotientBound_finrank_add {n : ℕ} (I : Ideal (Poly (n+1)))
    (D : ℕ) (j : WithBot ℕ) :
    Module.finrank ℂ (quotientBound I D j) +
      Module.finrank ℂ ↥(homogeneousBound n D j ⊓ I.restrictScalars ℂ) =
        Module.finrank ℂ (homogeneousBound n D j) := by
  have h := finrank_map_add_finrank_inf_ker (homogeneousBound n D j)
    (Ideal.Quotient.mkₐ ℂ I).toLinearMap
  have hker : LinearMap.ker (Ideal.Quotient.mkₐ ℂ I).toLinearMap = I.restrictScalars ℂ := by
    ext f
    exact Ideal.Quotient.eq_zero_iff_mem
  rwa [hker] at h

theorem quotientSection_finrank_add {n : ℕ} (I : Ideal (Poly n)) (D : ℕ) :
    Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection I D) +
      Module.finrank ℂ ↥(MvPolynomial.homogeneousSubmodule (Fin n) ℂ D ⊓ I.restrictScalars ℂ) =
        Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin n) ℂ D) := by
  have h := finrank_map_add_finrank_inf_ker (MvPolynomial.homogeneousSubmodule (Fin n) ℂ D)
    (Ideal.Quotient.mkₐ ℂ I).toLinearMap
  have hker : LinearMap.ker (Ideal.Quotient.mkₐ ℂ I).toLinearMap = I.restrictScalars ℂ := by
    ext f
    exact Ideal.Quotient.eq_zero_iff_mem
  rwa [hker] at h

theorem quotientBound_finrank_zero {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ)) (D : ℕ) :
    Module.finrank ℂ (quotientBound I D 0) =
      Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection (partialElimination I 0) D) := by
  have hbound := finrank_map_add_finrank_inf_ker (homogeneousBound n D 0) (coefficient n 0)
  have hm : (homogeneousBound n D 0).map (coefficient n 0) =
      MvPolynomial.homogeneousSubmodule (Fin n) ℂ D := by
    simpa only [Nat.cast_zero, Nat.sub_zero] using
      (coefficient_bound_map (n := n) (Nat.zero_le D))
  have hmdim := congrArg (fun A : Submodule ℂ (Poly n) => Module.finrank ℂ A) hm
  have hkdim := congrArg (fun A : Submodule ℂ (Poly (n+1)) => Module.finrank ℂ A)
    (coefficient_bound_ker_zero n D)
  rw [hmdim, hkdim, finrank_bot, add_zero] at hbound
  have hideal := finrank_map_add_finrank_inf_ker
    (homogeneousBound n D 0 ⊓ I.restrictScalars ℂ) (coefficient n 0)
  have hmI : (homogeneousBound n D 0 ⊓ I.restrictScalars ℂ).map (coefficient n 0) =
      MvPolynomial.homogeneousSubmodule (Fin n) ℂ D ⊓
        (partialElimination I 0).restrictScalars ℂ := by
    simpa only [Nat.cast_zero, Nat.sub_zero] using
      coefficient_ideal_bound_map I hI (Nat.zero_le D)
  have hmIdim := congrArg (fun A : Submodule ℂ (Poly n) => Module.finrank ℂ A) hmI
  rw [hmIdim] at hideal
  have hk : (homogeneousBound n D 0 ⊓ I.restrictScalars ℂ) ⊓
      LinearMap.ker (coefficient n 0) = ⊥ := by
    calc
      _ = (homogeneousBound n D 0 ⊓ LinearMap.ker (coefficient n 0)) ⊓
          I.restrictScalars ℂ := by ac_rfl
      _ = ⊥ := by rw [coefficient_bound_ker_zero, bot_inf_eq]
  have hkIdim := congrArg (fun A : Submodule ℂ (Poly (n+1)) => Module.finrank ℂ A) hk
  rw [hkIdim, finrank_bot, add_zero] at hideal
  have hq := quotientBound_finrank_add I D 0
  have htarget := quotientSection_finrank_add (partialElimination I 0) D
  have heq : Module.finrank ℂ (quotientBound I D 0) +
      Module.finrank ℂ ↥(homogeneousBound n D 0 ⊓ I.restrictScalars ℂ) =
      Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection (partialElimination I 0) D) +
      Module.finrank ℂ ↥(homogeneousBound n D 0 ⊓ I.restrictScalars ℂ) := by
    calc
      _ = Module.finrank ℂ (homogeneousBound n D 0) := hq
      _ = Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin n) ℂ D) := hbound.symm
      _ = _ := htarget.symm.trans (congrArg (fun a : ℕ =>
        Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection (partialElimination I 0) D) + a) hideal)
  exact Nat.add_right_cancel heq

theorem quotientBound_finrank_succ {n D j : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (hj : j+1 ≤ D) :
    Module.finrank ℂ (quotientBound I D ((j+1 : ℕ) : WithBot ℕ)) =
      Module.finrank ℂ (quotientBound I D j) +
        Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection
          (partialElimination I (j+1)) (D-(j+1))) := by
  have hbound := finrank_map_add_finrank_inf_ker (homogeneousBound n D ((j+1 : ℕ) : WithBot ℕ))
    (coefficient n (j+1))
  have hmdim := congrArg (fun A : Submodule ℂ (Poly n) => Module.finrank ℂ A)
    (coefficient_bound_map (n := n) hj)
  have hkdim := congrArg (fun A : Submodule ℂ (Poly (n+1)) => Module.finrank ℂ A)
    (coefficient_bound_ker_succ n D j)
  rw [hmdim, hkdim] at hbound
  have hideal := finrank_map_add_finrank_inf_ker
    (homogeneousBound n D ((j+1 : ℕ) : WithBot ℕ) ⊓ I.restrictScalars ℂ) (coefficient n (j+1))
  have hmIdim := congrArg (fun A : Submodule ℂ (Poly n) => Module.finrank ℂ A)
    (coefficient_ideal_bound_map I hI hj)
  rw [hmIdim] at hideal
  have hk : (homogeneousBound n D ((j+1 : ℕ) : WithBot ℕ) ⊓ I.restrictScalars ℂ) ⊓
      LinearMap.ker (coefficient n (j+1)) = homogeneousBound n D j ⊓ I.restrictScalars ℂ := by
    calc
      _ = (homogeneousBound n D ((j+1 : ℕ) : WithBot ℕ) ⊓ LinearMap.ker (coefficient n (j+1))) ⊓
          I.restrictScalars ℂ := by ac_rfl
      _ = _ := by rw [coefficient_bound_ker_succ]
  have hkIdim := congrArg (fun A : Submodule ℂ (Poly (n+1)) => Module.finrank ℂ A) hk
  rw [hkIdim] at hideal
  have hq0 := quotientBound_finrank_add I D j
  have hq1 := quotientBound_finrank_add I D ((j+1 : ℕ) : WithBot ℕ)
  have htarget := quotientSection_finrank_add (partialElimination I (j+1)) (D-(j+1))
  apply Nat.add_right_cancel (m := Module.finrank ℂ ↥(homogeneousBound n D ((j+1 : ℕ) : WithBot ℕ) ⊓ I.restrictScalars ℂ))
  calc
    _ = Module.finrank ℂ (homogeneousBound n D ((j+1 : ℕ) : WithBot ℕ)) := hq1
    _ = Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin n) ℂ (D-(j+1))) +
        Module.finrank ℂ (homogeneousBound n D j) := hbound.symm
    _ = (Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection (partialElimination I (j+1)) (D-(j+1))) +
          Module.finrank ℂ ↥(MvPolynomial.homogeneousSubmodule (Fin n) ℂ (D-(j+1)) ⊓ (partialElimination I (j+1)).restrictScalars ℂ)) +
        (Module.finrank ℂ (quotientBound I D j) + Module.finrank ℂ ↥(homogeneousBound n D j ⊓ I.restrictScalars ℂ)) := by
      exact congrArg₂ (fun a b : ℕ => a+b) htarget.symm hq0.symm
    _ = (Module.finrank ℂ (quotientBound I D j) +
          Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection (partialElimination I (j+1)) (D-(j+1)))) +
        (Module.finrank ℂ ↥(MvPolynomial.homogeneousSubmodule (Fin n) ℂ (D-(j+1)) ⊓ (partialElimination I (j+1)).restrictScalars ℂ) +
          Module.finrank ℂ ↥(homogeneousBound n D j ⊓ I.restrictScalars ℂ)) := by ac_rfl
    _ = _ := congrArg (fun a : ℕ =>
      (Module.finrank ℂ (quotientBound I D j) +
        Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection (partialElimination I (j+1)) (D-(j+1)))) + a) hideal

theorem homogeneousBound_full (n D : ℕ) :
    homogeneousBound n D (D : WithBot ℕ) =
      MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D := by
  apply le_antisymm inf_le_left
  intro f hf
  apply mem_homogeneousBound.mpr
  have hhom := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hf
  refine ⟨hhom, ?_⟩
  apply Polynomial.degree_le_natDegree.trans
  rw [MvPolynomial.natDegree_finSuccEquiv]
  exact_mod_cast (MvPolynomial.degreeOf_le_totalDegree f 0).trans hhom.totalDegree_le

theorem quotientBound_finrank_sum {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (D j : ℕ) (hj : j ≤ D) :
    Module.finrank ℂ (quotientBound I D (j : WithBot ℕ)) =
      ∑ i ∈ Finset.range (j+1), Module.finrank ℂ
        (OAI.PiExponentJets.W64.quotientSection (partialElimination I i) (D-i)) := by
  induction j with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero]
    convert quotientBound_finrank_zero I hI D using 1
  | succ j ih =>
    rw [quotientBound_finrank_succ I hI hj, ih (by omega)]
    rw [Finset.sum_range_succ (n := j+1)]

/-- Exact homogeneous Hilbert decomposition for projection from a
coordinate point. The stable tail retains the scheme multiplicities. -/
theorem hilbert_partialElimination {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ)) (D : ℕ) :
    Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection I D) =
      ∑ i ∈ Finset.range (D+1), Module.finrank ℂ
        (OAI.PiExponentJets.W64.quotientSection (partialElimination I i) (D-i)) := by
  have h := quotientBound_finrank_sum I hI D D le_rfl
  unfold quotientBound at h
  rw [homogeneousBound_full] at h
  exact h

theorem hilbert_stableElimination {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (s : ℕ) (hs : ∀ j, s ≤ j → partialElimination I j = stableElimination I)
    (D : ℕ) (hD : s ≤ D) :
    Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection I D) =
      (∑ i ∈ Finset.range s, Module.finrank ℂ
        (OAI.PiExponentJets.W64.quotientSection (partialElimination I i) (D-i))) +
      ∑ i ∈ Finset.range (D-s+1), Module.finrank ℂ
        (OAI.PiExponentJets.W64.quotientSection (stableElimination I) i) := by
  rw [hilbert_partialElimination I hI D]
  have heq : D+1 = s+(D-s+1) := by omega
  rw [heq, Finset.sum_range_add]
  congr 1
  calc
    _ = ∑ i ∈ Finset.range (D-s+1), Module.finrank ℂ
        (OAI.PiExponentJets.W64.quotientSection (stableElimination I) (D-s+1-1-i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hs (s+i) (Nat.le_add_right s i)]
      have hindex : D-(s+i) = D-s+1-1-i := by omega
      rw [hindex]
    _ = _ := Finset.sum_range_reflect (fun i => Module.finrank ℂ
      (OAI.PiExponentJets.W64.quotientSection (stableElimination I) i)) (D-s+1)

theorem chartPullback_zero_eq_eval {n : ℕ} (F : Poly (n+1)) :
    chartPullback 0 F = (MvPolynomial.finSuccEquiv ℂ n F).eval 1 := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [chartPullback, MvPolynomial.finSuccEquiv_apply]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, Polynomial.eval_mul, hf]
    apply congrArg (fun c => (MvPolynomial.finSuccEquiv ℂ n f).eval 1 * c)
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [chartPullback, MvPolynomial.finSuccEquiv_X_zero]
    · simp [chartPullback, MvPolynomial.finSuccEquiv_X_succ]

theorem chartPullback_zero_rename {n : ℕ} (f : Poly n) :
    chartPullback 0 (MvPolynomial.rename Fin.succ f) = f := by
  rw [chartPullback_zero_eq_eval, finSuccEquiv_rename, Polynomial.eval_C]

theorem chartHomogenize_mem {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (F : Poly (n+1)) (hF : F ∈ I) (D : ℕ) :
    chartHomogenize (MvPolynomial.X 0) D F ∈ I := by
  unfold chartHomogenize
  apply I.sum_mem
  intro i hi
  exact I.mul_mem_left _ (homogeneous_component_mem I hI F hF i)

theorem chartHomogenize_chartPullback {n : ℕ} (F : Poly (n+1)) (D : ℕ)
    (hD : F.totalDegree ≤ D) :
    chartPullback 0 (chartHomogenize (MvPolynomial.X 0) D F) = chartPullback 0 F := by
  have hx : chartPullback (0 : Fin (n+1)) (MvPolynomial.X 0) = 1 := by simp [chartPullback]
  simp only [chartHomogenize, map_sum, map_mul, map_pow, hx, one_pow, one_mul]
  rw [← map_sum, chart_components_sum F hD]

/-- Every member of the literal chart ideal lifts to a homogeneous
member of the original ideal, after increasing its degree if needed. -/
theorem chart_ideal_homogeneous_lift {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (f : Poly n) (hf : f ∈ I.map (chartPullback 0).toRingHom) :
    ∃ D : ℕ, ∃ F ∈ I, F.IsHomogeneous D ∧ chartPullback 0 F = f := by
  have hsurj : Function.Surjective (chartPullback (0 : Fin (n+1))) :=
    fun f => ⟨MvPolynomial.rename Fin.succ f, chartPullback_zero_rename f⟩
  obtain ⟨F, hF, hFf⟩ := (Ideal.mem_map_iff_of_surjective (chartPullback 0).toRingHom hsurj).mp hf
  refine ⟨F.totalDegree, chartHomogenize (MvPolynomial.X 0) F.totalDegree F,
    chartHomogenize_mem I hI F hF _,
    chartHomogenize_homogeneous _ _ (MvPolynomial.isHomogeneous_X ℂ 0), ?_⟩
  exact (chartHomogenize_chartPullback F _ le_rfl).trans hFf

theorem chart_homogeneous_sum_coeff {n D : ℕ} (F : Poly (n+1))
    (hF : F.IsHomogeneous D) :
    chartPullback 0 F = ∑ i ∈ Finset.range (D+1), (MvPolynomial.finSuccEquiv ℂ n F).coeff i := by
  have hdeg : (MvPolynomial.finSuccEquiv ℂ n F).natDegree ≤ D := by
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree F 0).trans hF.totalDegree_le
  rw [chartPullback_zero_eq_eval, Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hdeg))
  intro i hi hnot
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
    have hh := Finset.mem_range.not.mp hnot
    omega)

theorem chart_homogeneous_component {n D : ℕ} (F : Poly (n+1))
    (hF : F.IsHomogeneous D) (d : ℕ) (hd : d ≤ D) :
    MvPolynomial.homogeneousComponent d (chartPullback 0 F) =
      (MvPolynomial.finSuccEquiv ℂ n F).coeff (D-d) := by
  rw [chart_homogeneous_sum_coeff F hF, map_sum]
  rw [Finset.sum_eq_single (D-d)]
  · apply MvPolynomial.homogeneousComponent_eq_self
    exact hF.finSuccEquiv_coeff_isHomogeneous (D-d) d (Nat.sub_add_cancel hd)
  · intro i hi hne
    have hiD : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hhom := hF.finSuccEquiv_coeff_isHomogeneous i (D-i) (Nat.add_sub_of_le hiD)
    rw [MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hhom)]
    exact if_neg (by omega)
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

theorem chart_homogeneous_component_above {n D : ℕ} (F : Poly (n+1))
    (hF : F.IsHomogeneous D) (d : ℕ) (hd : D < d) :
    MvPolynomial.homogeneousComponent d (chartPullback 0 F) = 0 := by
  rw [chart_homogeneous_sum_coeff F hF, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hiD : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hhom := hF.finSuccEquiv_coeff_isHomogeneous i (D-i) (Nat.add_sub_of_le hiD)
  rw [MvPolynomial.homogeneousComponent_of_mem
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hhom)]
  exact if_neg (by omega)

theorem chart_low_components_zero {n j d : ℕ} (F : Poly (n+1))
    (hF : F.IsHomogeneous (j+d)) (hdeg : (MvPolynomial.finSuccEquiv ℂ n F).degree ≤ j) :
    ∀ i < d, MvPolynomial.homogeneousComponent i (chartPullback 0 F) = 0 := by
  intro i hi
  rw [chart_homogeneous_component F hF i (by omega)]
  exact Polynomial.coeff_eq_zero_of_degree_lt
    (hdeg.trans_lt (by exact_mod_cast (show j < j+d-i by omega)))

/-- Lowest homogeneous terms of chart-ideal members belong to the
stable elimination ideal. This statement retains the original ideal. -/
theorem initial_component_mem_stable {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (f : Poly n) (hf : f ∈ I.map (chartPullback 0).toRingHom) (d : ℕ)
    (hlow : ∀ i < d, MvPolynomial.homogeneousComponent i f = 0) :
    MvPolynomial.homogeneousComponent d f ∈ stableElimination I := by
  obtain ⟨D, F, hFI, hF, hchart⟩ := chart_ideal_homogeneous_lift I hI f hf
  by_cases hd : d ≤ D
  · have hdeg : (MvPolynomial.finSuccEquiv ℂ n F).degree ≤ D-d := by
      apply (Polynomial.degree_le_iff_coeff_zero _ _).mpr
      intro i hi
      have hgt : D-d < i := by exact_mod_cast hi
      by_cases hiD : i ≤ D
      · have hcomp := chart_homogeneous_component F hF (D-i) (Nat.sub_le D i)
        rw [Nat.sub_sub_self hiD, hchart] at hcomp
        exact hcomp.symm.trans (hlow (D-i) (by omega))
      · have hfull : F ∈ homogeneousBound n D (D : WithBot ℕ) := by
          rw [homogeneousBound_full, MvPolynomial.mem_homogeneousSubmodule]
          exact hF
        exact Polynomial.coeff_eq_zero_of_degree_lt
          ((mem_homogeneousBound.mp hfull).2.trans_lt (by exact_mod_cast (show D < i by omega)))
    apply partialElimination_le_stable I (D-d)
    apply (mem_partialElimination_iff I (D-d) _).mpr
    exact ⟨F, hFI, hdeg, (chart_homogeneous_component F hF d hd).symm.trans
      (congrArg (MvPolynomial.homogeneousComponent d) hchart)⟩
  · rw [← hchart, chart_homogeneous_component_above F hF d (by omega)]
    exact (stableElimination I).zero_mem

/-- Stabilization gives a uniform homogeneous lift for each initial
term, with original total degree `s+d`. -/
theorem stable_component_lift {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (s : ℕ) (hs : partialElimination I s = stableElimination I)
    (d : ℕ) (f : Poly n) (hf : f ∈ stableElimination I) (hhom : f.IsHomogeneous d) :
    ∃ F ∈ I, F.IsHomogeneous (s+d) ∧
      MvPolynomial.homogeneousComponent d (chartPullback 0 F) = f ∧
      ∀ i < d, MvPolynomial.homogeneousComponent i (chartPullback 0 F) = 0 := by
  have hf' : f ∈ partialElimination I s := by rwa [hs]
  obtain ⟨F, hFI, hF, hdeg, hcoeff⟩ := homogeneous_partialElimination_witness I hI s d f hf' hhom
  refine ⟨F, hFI, hF, ?_, chart_low_components_zero F hF hdeg⟩
  rw [chart_homogeneous_component F hF d (by omega), Nat.add_sub_cancel, hcoeff]

theorem mem_vars_pow_iff_components {n : ℕ} (f : Poly n) (t : ℕ) :
    f ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ t ↔
      ∀ d < t, MvPolynomial.homogeneousComponent d f = 0 := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro hf d hd
    ext a
    rw [MvPolynomial.coeff_homogeneousComponent]
    by_cases ha : a.degree = d
    · rw [ite_eq_left ha, hf a (by omega)]
      rfl
    · rw [ite_eq_right ha]
      rfl
  · intro hf a ha
    have hcoeff := congrArg (fun p : Poly n => p.coeff a) (hf a.degree ha)
    simpa only [MvPolynomial.coeff_homogeneousComponent, ite_true,
      MvPolynomial.coeff_zero, Finsupp.zero_apply] using hcoeff

theorem raise_homogeneous_chart {n e D : ℕ} (F : Poly (n+1))
    (hF : F.IsHomogeneous e) (he : e ≤ D) :
    (MvPolynomial.X 0 ^ (D-e) * F).IsHomogeneous D ∧
      chartPullback 0 (MvPolynomial.X 0 ^ (D-e) * F) = chartPullback 0 F := by
  constructor
  · simpa only [Nat.one_mul, Nat.sub_add_cancel he] using
      ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin (n+1))).pow (D-e)).mul hF
  · have hx : chartPullback (0 : Fin (n+1)) (MvPolynomial.X 0) = 1 := by simp [chartPullback]
    simp only [map_mul, map_pow, hx, one_pow, one_mul]

/-- Stable leading coefficients give uniform lifts of all finite
local jets of the original chart ideal. -/
theorem chart_jet_homogeneous_lift {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (s : ℕ) (hs : partialElimination I s = stableElimination I) (D : ℕ) :
    ∀ t : ℕ, s+t ≤ D → ∀ f : Poly n, f ∈ I.map (chartPullback 0).toRingHom →
      ∃ F ∈ I, F.IsHomogeneous D ∧
        ∀ i ≤ t, MvPolynomial.homogeneousComponent i (chartPullback 0 F) =
          MvPolynomial.homogeneousComponent i f := by
  intro t
  induction t with
  | zero =>
    intro hD f hf
    have hinit := initial_component_mem_stable I hI f hf 0 (by intro i hi; omega)
    obtain ⟨G, hGI, hG, hcomp, hlow⟩ := stable_component_lift I hI s hs 0
      (MvPolynomial.homogeneousComponent 0 f) hinit
      (MvPolynomial.homogeneousComponent_isHomogeneous _ _)
    have hraise := raise_homogeneous_chart G hG hD
    refine ⟨MvPolynomial.X 0 ^ (D-(s+0)) * G, I.mul_mem_left _ hGI,
      hraise.1, ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    rw [hi0, hraise.2, hcomp]
  | succ t ih =>
    intro hD f hf
    obtain ⟨F, hFI, hF, hprev⟩ := ih (by omega) f hf
    let g := f-chartPullback 0 F
    have hg : g ∈ I.map (chartPullback 0).toRingHom :=
      (I.map (chartPullback 0).toRingHom).sub_mem hf (Ideal.mem_map_of_mem _ hFI)
    have hglow : ∀ i < t+1, MvPolynomial.homogeneousComponent i g = 0 := by
      intro i hi
      change MvPolynomial.homogeneousComponent i (f-chartPullback 0 F) = 0
      rw [map_sub, hprev i (by omega), sub_self]
    have hinit := initial_component_mem_stable I hI g hg (t+1) hglow
    obtain ⟨G, hGI, hG, hcomp, hlow⟩ := stable_component_lift I hI s hs (t+1)
      (MvPolynomial.homogeneousComponent (t+1) g) hinit
      (MvPolynomial.homogeneousComponent_isHomogeneous _ _)
    have hraise := raise_homogeneous_chart G hG hD
    refine ⟨F + MvPolynomial.X 0 ^ (D-(s+(t+1))) * G,
      I.add_mem hFI (I.mul_mem_left _ hGI), hF.add hraise.1, ?_⟩
    intro i hi
    rw [map_add, hraise.2, map_add]
    by_cases hit : i ≤ t
    · rw [hlow i (by omega), add_zero, hprev i hit]
    · have hieq : i = t+1 := by omega
      rw [hieq, hcomp]
      change MvPolynomial.homogeneousComponent (t+1) (chartPullback 0 F) +
        MvPolynomial.homogeneousComponent (t+1) (f-chartPullback 0 F) =
          MvPolynomial.homogeneousComponent (t+1) f
      rw [map_sub]
      ring

theorem chart_mem_vars_pow_iff_xDegree {n D : ℕ} (F : Poly (n+1))
    (hF : F.IsHomogeneous D) (t : ℕ) (ht : t ≤ D) :
    chartPullback 0 F ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ t ↔
      (MvPolynomial.finSuccEquiv ℂ n F).degree ≤ D-t := by
  rw [mem_vars_pow_iff_components]
  constructor
  · intro hlow
    apply (Polynomial.degree_le_iff_coeff_zero _ _).mpr
    intro i hi
    have hgt : D-t < i := by exact_mod_cast hi
    by_cases hiD : i ≤ D
    · have hc := chart_homogeneous_component F hF (D-i) (Nat.sub_le D i)
      rw [Nat.sub_sub_self hiD] at hc
      exact hc.symm.trans (hlow (D-i) (by omega))
    · have hfull : F ∈ homogeneousBound n D (D : WithBot ℕ) := by
        rw [homogeneousBound_full, MvPolynomial.mem_homogeneousSubmodule]
        exact hF
      exact Polynomial.coeff_eq_zero_of_degree_lt
        ((mem_homogeneousBound.mp hfull).2.trans_lt (by exact_mod_cast (show D < i by omega)))
  · intro hdeg i hi
    rw [chart_homogeneous_component F hF i (by omega)]
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (hdeg.trans_lt (by exact_mod_cast (show D-t < D-i by omega)))

theorem chartPullback_centerLift {n : ℕ} (j : ℕ) (f : Poly n) :
    chartPullback 0 (centerLift j f) = f := by
  have hx : chartPullback (0 : Fin (n+1)) (MvPolynomial.X 0) = 1 := by simp [chartPullback]
  simp only [centerLift, map_mul, map_pow, hx, one_pow,
    chartPullback_zero_rename, one_mul]

/-- The original homogeneous section maps onto every truncated chart
quotient once its degree reaches the jet order. -/
theorem chart_jet_section_surjective {n D t : ℕ} (J : Ideal (Poly n)) (ht : t ≤ D) :
    Function.Surjective (fun F : MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D =>
      Ideal.Quotient.mk (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))
        (chartPullback 0 F.val)) := by
  intro z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  let F : Poly (n+1) := ∑ a ∈ f.support,
    if a.degree ≤ t then centerLift (D-a.degree) (MvPolynomial.monomial a (f.coeff a)) else 0
  have hF : F.IsHomogeneous D := by
    apply MvPolynomial.IsHomogeneous.sum
    intro a ha
    by_cases hat : a.degree ≤ t
    · rw [ite_eq_left hat]
      have haD : a.degree ≤ D := hat.trans ht
      have hmono : (MvPolynomial.monomial a (f.coeff a) : Poly n).IsHomogeneous a.degree := by
        apply MvPolynomial.isHomogeneous_monomial
        simp [Finsupp.degree_eq_weight_one]
      simpa only [Nat.sub_add_cancel haD] using centerLift_homogeneous (D-a.degree)
        (MvPolynomial.monomial a (f.coeff a)) hmono
    · rw [ite_eq_right hat]
      exact MvPolynomial.isHomogeneous_zero _ _ _
  refine ⟨⟨F, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hF⟩, ?_⟩
  change Ideal.Quotient.mk (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))
    (chartPullback 0 F) = _
  dsimp only [F]
  simp only [map_sum]
  conv_rhs => rw [← f.support_sum_monomial_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hat : a.degree ≤ t
  · rw [ite_eq_left hat, chartPullback_centerLift]
  · rw [ite_eq_right hat, map_zero, map_zero]
    symm
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (le_sup_right : MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1) ≤
      J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))
    exact (MvPolynomial.monomial_mem_pow_idealOfVars_iff (t+1) a
      (Finsupp.mem_support_iff.mp ha)).mpr (by omega)

def chartJetMap {n : ℕ} (J : Ideal (Poly n)) (t : ℕ) :
    Poly (n+1) →ₗ[ℂ] (Poly n ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) :=
  (Ideal.Quotient.mkₐ ℂ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))).toLinearMap.comp
    (chartPullback 0).toLinearMap

theorem chart_jet_section_kernel {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (s : ℕ) (hs : partialElimination I s = stableElimination I) (D t : ℕ)
    (hD : s+t+1 ≤ D) :
    MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D ⊓
      LinearMap.ker (chartJetMap (I.map (chartPullback 0).toRingHom) t) =
      homogeneousBound n D ((D-(t+1) : ℕ) : WithBot ℕ) ⊔
        (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D ⊓ I.restrictScalars ℂ) := by
  ext F
  constructor
  · rintro ⟨hF, hker⟩
    have hFhom := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hF
    have hmem : chartPullback 0 F ∈ I.map (chartPullback 0).toRingHom ⊔
        MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact LinearMap.mem_ker.mp hker
    obtain ⟨g, hg, h, hh, hsum⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨G, hGI, hGhom, hjet⟩ := chart_jet_homogeneous_lift I hI s hs D t
      (by omega) g hg
    have hres : chartPullback 0 (F-G) ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1) := by
      rw [mem_vars_pow_iff_components]
      intro i hi
      rw [map_sub, map_sub, ← hsum, map_add,
        (mem_vars_pow_iff_components h (t+1)).mp hh i hi, add_zero,
        hjet i (by omega), sub_self]
    have hbound : F-G ∈ homogeneousBound n D ((D-(t+1) : ℕ) : WithBot ℕ) := by
      apply mem_homogeneousBound.mpr
      exact ⟨hFhom.sub hGhom, (chart_mem_vars_pow_iff_xDegree (F-G)
        (hFhom.sub hGhom) (t+1) (by omega)).mp hres⟩
    apply Submodule.mem_sup.mpr
    exact ⟨F-G, hbound, G, ⟨hGhom, hGI⟩, sub_add_cancel F G⟩
  · intro hF
    obtain ⟨B, hB, C, ⟨hChom, hCI⟩, hsum⟩ := Submodule.mem_sup.mp hF
    rw [← hsum]
    refine ⟨?_, ?_⟩
    · exact (mem_homogeneousBound.mp hB).1.add hChom
    · apply LinearMap.mem_ker.mpr
      change Ideal.Quotient.mk (I.map (chartPullback 0).toRingHom ⊔
        MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1)) (chartPullback 0 (B+C)) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [map_add]
      apply Ideal.add_mem
      · apply (le_sup_right : MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1) ≤
          I.map (chartPullback 0).toRingHom ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))
        exact (chart_mem_vars_pow_iff_xDegree B (mem_homogeneousBound.mp hB).1
          (t+1) (by omega)).mpr (mem_homogeneousBound.mp hB).2
      · exact (le_sup_left : I.map (chartPullback 0).toRingHom ≤
          I.map (chartPullback 0).toRingHom ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))
          (Ideal.mem_map_of_mem _ hCI)

theorem hilbert_eq_quotientBound_add_jets {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (s : ℕ) (hs : partialElimination I s = stableElimination I) (D t : ℕ)
    (hD : s+t+1 ≤ D) :
    Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection I D) =
      Module.finrank ℂ (quotientBound I D ((D-(t+1) : ℕ) : WithBot ℕ)) +
        Module.finrank ℂ (Poly n ⧸ (I.map (chartPullback 0).toRingHom ⊔
          MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) := by
  let H := MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ D
  let B := homogeneousBound n D ((D-(t+1) : ℕ) : WithBot ℕ)
  let C := H ⊓ I.restrictScalars ℂ
  let W := B ⊓ I.restrictScalars ℂ
  let J := I.map (chartPullback 0).toRingHom
  let q := chartJetMap J t
  letI : Module.Finite ℂ C := Module.Finite.of_injective
    (Submodule.inclusion (show C ≤ H from inf_le_left)) (Submodule.inclusion_injective _)
  have hB : B ≤ H := inf_le_left
  have hmap : H.map q = ⊤ := by
    apply eq_top_iff.mpr
    intro z hz
    obtain ⟨F, hFz⟩ := chart_jet_section_surjective J (show t ≤ D by omega) z
    exact Submodule.mem_map.mpr ⟨F, F.property, hFz⟩
  have hker : H ⊓ LinearMap.ker q = B ⊔ C := chart_jet_section_kernel I hI s hs D t hD
  have hjet := finrank_map_add_finrank_inf_ker H q
  have hmapdim := congrArg (fun A : Submodule ℂ
      (Poly n ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) => Module.finrank ℂ A) hmap
  have hkerdim := congrArg (fun A : Submodule ℂ (Poly (n+1)) => Module.finrank ℂ A) hker
  rw [hmapdim, hkerdim, finrank_top] at hjet
  have hHC := quotientSection_finrank_add I D
  have hBW := quotientBound_finrank_add I D ((D-(t+1) : ℕ) : WithBot ℕ)
  have hBC := B.finrank_sup_add_finrank_inf_eq C
  have hBCinf : B ⊓ C = W := by
    change B ⊓ (H ⊓ I.restrictScalars ℂ) = B ⊓ I.restrictScalars ℂ
    rw [← inf_assoc, inf_eq_left.mpr hB]
  have hBCinfdim := congrArg (fun A : Submodule ℂ (Poly (n+1)) => Module.finrank ℂ A) hBCinf
  rw [hBCinfdim] at hBC
  have heq : Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection I D) +
      (Module.finrank ℂ C + Module.finrank ℂ W) =
      (Module.finrank ℂ (quotientBound I D ((D-(t+1) : ℕ) : WithBot ℕ)) +
        Module.finrank ℂ (Poly n ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1)))) +
      (Module.finrank ℂ C + Module.finrank ℂ W) := by
    calc
      _ = (Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection I D) +
          Module.finrank ℂ C) + Module.finrank ℂ W := by ac_rfl
      _ = Module.finrank ℂ H + Module.finrank ℂ W := congrArg (fun a : ℕ => a+Module.finrank ℂ W) hHC
      _ = (Module.finrank ℂ (Poly n ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) +
          Module.finrank ℂ ↥(B ⊔ C)) + Module.finrank ℂ W :=
        congrArg (fun a : ℕ => a+Module.finrank ℂ W) hjet.symm
      _ = Module.finrank ℂ (Poly n ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) +
          (Module.finrank ℂ ↥(B ⊔ C) + Module.finrank ℂ W) := by ac_rfl
      _ = Module.finrank ℂ (Poly n ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) +
          (Module.finrank ℂ B + Module.finrank ℂ C) :=
        congrArg (fun a : ℕ => Module.finrank ℂ
          (Poly n ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) + a) hBC
      _ = Module.finrank ℂ (Poly n ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) +
          ((Module.finrank ℂ (quotientBound I D ((D-(t+1) : ℕ) : WithBot ℕ)) +
            Module.finrank ℂ W) + Module.finrank ℂ C) :=
        congrArg (fun a : ℕ => Module.finrank ℂ
          (Poly n ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) +
          (a+Module.finrank ℂ C)) hBW.symm
      _ = _ := by ac_rfl
  exact Nat.add_right_cancel heq

theorem partialElimination_eq_stable_of_ge {n : ℕ} (I : Ideal (Poly (n+1)))
    (s : ℕ) (hs : partialElimination I s = stableElimination I) (i : ℕ) (hi : s ≤ i) :
    partialElimination I i = stableElimination I := by
  apply le_antisymm (partialElimination_le_stable I i)
  rw [← hs]
  exact partialElimination_mono I hi

/-- The stable elimination algebra has exactly the cumulative Hilbert
function of the original center's local polynomial jets. -/
theorem stableElimination_cumulative_eq_jets {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (s : ℕ) (hs : partialElimination I s = stableElimination I) (t : ℕ) :
    Module.finrank ℂ (Poly n ⧸ (I.map (chartPullback 0).toRingHom ⊔
      MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) =
      ∑ i ∈ Finset.range (t+1), Module.finrank ℂ
        (OAI.PiExponentJets.W64.quotientSection (stableElimination I) i) := by
  let D := s+t+1
  have hsrc := hilbert_stableElimination I hI (s+1)
    (fun i hi => partialElimination_eq_stable_of_ge I s hs i (by omega)) D (by omega)
  have htail : D-(s+1)+1 = t+1 := by omega
  rw [htail] at hsrc
  have hbound := quotientBound_finrank_sum I hI D s (by omega)
  have hglobal : Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection I D) =
      Module.finrank ℂ (quotientBound I D (s : WithBot ℕ)) +
      ∑ i ∈ Finset.range (t+1), Module.finrank ℂ
        (OAI.PiExponentJets.W64.quotientSection (stableElimination I) i) := by
    exact hsrc.trans (congrArg (fun a : ℕ => a + ∑ i ∈ Finset.range (t+1),
      Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection (stableElimination I) i)) hbound.symm)
  have hjet := hilbert_eq_quotientBound_add_jets I hI s hs D t (by omega)
  have hindex : ((D-(t+1) : ℕ) : WithBot ℕ) = (s : WithBot ℕ) := by
    congr 1
    omega
  have hindexdim := congrArg (fun j : WithBot ℕ => Module.finrank ℂ (quotientBound I D j)) hindex
  rw [hindexdim] at hjet
  exact Nat.add_left_cancel (hjet.symm.trans hglobal)

/-- Localizing a point-power jet quotient commutes with imposing an
arbitrary original ideal. -/
def pointIdealJetEquiv {n : ℕ} (p : Point n) (t : ℕ) (K : Ideal (Poly n)) :
    (Poly n ⧸ (pointIdeal p ^ t ⊔ K)) ≃ₐ[ℂ]
      (PointLocalRing p ⧸ (IsLocalRing.maximalIdeal (PointLocalRing p) ^ t ⊔
        K.map (algebraMap (Poly n) (PointLocalRing p)))) := by
  let I := pointIdeal p ^ t
  let J := IsLocalRing.maximalIdeal (PointLocalRing p) ^ t
  let e : (Poly n ⧸ I) ≃ₐ[ℂ] (PointLocalRing p ⧸ J) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow (pointIdeal p) (PointLocalRing p) t).restrictScalars ℂ
  letI : CommRing (PointLocalRing p ⧸ J) :=
    { __ := (inferInstance : Ring (PointLocalRing p ⧸ J)),
      mul_comm := fun a b => mul_comm a b }
  let K' := K.map (algebraMap (Poly n) (PointLocalRing p))
  have hmaps : K'.map (Ideal.Quotient.mk J) = (K.map (Ideal.Quotient.mk I)).map e.toRingHom := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  let eq : ((Poly n ⧸ I) ⧸ K.map (Ideal.Quotient.mk I)) ≃ₐ[ℂ]
      ((PointLocalRing p ⧸ J) ⧸ K'.map (Ideal.Quotient.mk J)) :=
    Ideal.quotientEquivAlg _ _ e hmaps
  let e₁ := DoubleQuot.quotQuotEquivQuotSupₐ ℂ I K
  let e₂ := DoubleQuot.quotQuotEquivQuotSupₐ ℂ J K'
  exact e₁.symm.trans (eq.trans e₂)

theorem localLength_origin_jet_eq_finrank {n : ℕ} (K : Ideal (Poly n)) (t : ℕ) :
    localLengthAt (K ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1)) (0 : Point n) =
      (Module.finrank ℂ (Poly n ⧸ (K ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) : ℕ∞) := by
  let J := IsLocalRing.maximalIdeal (PointLocalRing (0 : Point n)) ^ (t+1)
  let K' := K.map (algebraMap (Poly n) (PointLocalRing (0 : Point n)))
  let e : (Poly n ⧸ (K ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) ≃ₐ[ℂ]
      (PointLocalRing (0 : Point n) ⧸ (K' ⊔ J)) := by
    have e₀ := pointIdealJetEquiv (0 : Point n) (t+1) K
    have hsource : K ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1) =
        pointIdeal (0 : Point n) ^ (t+1) ⊔ K := by rw [pointIdeal_origin_eq_vars]; exact sup_comm _ _
    exact (Ideal.quotientEquivAlgOfEq ℂ hsource).trans
      (e₀.trans (Ideal.quotientEquivAlgOfEq ℂ (sup_comm _ _)))
  let H := MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ t
  let q := (chartJetMap K t).domRestrict H
  letI : Module.Finite ℂ (Poly n ⧸ (K ⊔ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1))) :=
    Module.Finite.of_surjective q (chart_jet_section_surjective K le_rfl)
  letI : Module.Finite ℂ (PointLocalRing (0 : Point n) ⧸ (K' ⊔ J)) := e.toLinearEquiv.finiteDimensional
  have hvars : (MvPolynomial.idealOfVars (Fin n) ℂ).map
      (algebraMap (Poly n) (PointLocalRing (0 : Point n))) =
        IsLocalRing.maximalIdeal (PointLocalRing (0 : Point n)) := by
    rw [← pointIdeal_origin_eq_vars, IsLocalization.AtPrime.map_eq_maximalIdeal]
  unfold localLengthAt localizedIdeal
  rw [Ideal.map_sup, Ideal.map_pow, hvars,
    point_local_length_eq_complex_length (0 : Point n), Module.length_eq_finrank]
  exact congrArg (fun a : ℕ => (a : ℕ∞)) e.toLinearEquiv.finrank_eq.symm

/-- The actual affine chart, including its scheme ideal, has the stable
elimination algebra's cumulative Hilbert function at the coordinate origin. -/
theorem affineChart_localHilbert {n : ℕ} (X : ProjectiveVariety (n+1))
    (s : ℕ) (hs : partialElimination X.ideal s = stableElimination X.ideal) (t : ℕ) :
    (X.affineChart 0).localHilbert (0 : Point n) t =
      ((∑ i ∈ Finset.range (t+1), Module.finrank ℂ
        (OAI.PiExponentJets.W64.quotientSection (stableElimination X.ideal) i)) : ℕ∞) := by
  unfold AffineVariety.localHilbert
  rw [affineChart_ideal_exact, pointIdeal_origin_eq_vars,
    localLength_origin_jet_eq_finrank,
    stableElimination_cumulative_eq_jets X.ideal X.isHomogeneous s hs]
  simp only [Nat.cast_sum]

theorem chartHomogenize_rename {n D : ℕ} (f : Poly n) (hf : f.totalDegree ≤ D) :
    chartPullback 0 (chartHomogenize (MvPolynomial.X (0 : Fin (n+1))) D
      (MvPolynomial.rename Fin.succ f)) = f := by
  simp only [chartHomogenize, map_sum, map_mul, map_pow]
  have hX0 : chartPullback (0 : Fin (n+1)) (MvPolynomial.X 0) = 1 := by
    simp [chartPullback]
  rw [hX0]
  simp only [one_pow, one_mul]
  rw [← map_sum, chart_components_sum _
    ((MvPolynomial.totalDegree_rename_le _ _).trans hf), chartPullback_zero_rename]

theorem homogeneous_chart_mem_iff {n D : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (h0 : MvPolynomial.X (0 : Fin (n+1)) ∉ X.ideal)
    (F : Poly (n+1)) (hF : F.IsHomogeneous D) :
    chartPullback 0 F ∈ (X.affineChart 0).ideal ↔ F ∈ X.ideal := by
  constructor
  · intro hf
    apply (homogeneous_mem_linearSlice_iff X hX (MvPolynomial.X 0) F
      (MvPolynomial.isHomogeneous_X ℂ 0) h0 hF).mp
    rw [← AffineVariety.vanishingIdeal_points]
    intro x hx
    obtain ⟨hxcone, hx0⟩ := (linearSlice_points X (MvPolynomial.X 0) x).mp hx
    have hx0' : x 0 = 1 := by simpa using hx0
    have hc := chart_points_from_cone X 0 x hxcone hx0'
    have hz := hc (chartPullback 0 F) hf
    have hins : Fin.insertNth (0 : Fin (n+1)) (1 : ℂ)
        (fun j => x ((0 : Fin (n+1)).succAbove j)) = x := by
      ext j
      cases j using Fin.cases <;> simp [hx0']
    simpa only [MvPolynomial.aeval_eq_eval, chartPullback_eval, hins] using hz
  · intro hf
    rw [affineChart_ideal_exact]
    exact Ideal.mem_map_of_mem (chartPullback 0).toRingHom hf

/-- Deleting the fixed coordinate in a nonempty coordinate chart preserves
the literal finite restriction ranks, hence the original Hilbert polynomial. -/
theorem affineChart_hilbert {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (h0 : MvPolynomial.X (0 : Fin (n+1)) ∉ X.ideal) (D : ℕ) :
    (X.affineChart 0).hilbert D = X.hilbert D := by
  let A := X.affineChart 0
  let Q : (Poly (n+1) ⧸ X.ideal) →ₐ[ℂ] (Poly n ⧸ A.ideal) :=
    Ideal.Quotient.liftₐ X.ideal ((Ideal.Quotient.mkₐ ℂ A.ideal).comp (chartPullback 0))
      (by intro f hf; apply Ideal.Quotient.eq_zero_iff_mem.mpr
          rw [affineChart_ideal_exact]; exact Ideal.mem_map_of_mem _ hf)
  let e : X.restrictionSpace D →ₗ[ℂ] A.restrictionSpace D :=
    { toFun := fun x => ⟨Q x.val, by
        obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
        apply Submodule.mem_map.mpr
        refine ⟨chartPullback 0 f, OAI.QuarticPowerFree.mem_totalSpace.mpr ?_, ?_⟩
        · exact (OAI.QuarticPowerFree.totalDegree_linear_substitute_le
            (Fin.insertNth 0 (MvPolynomial.C 1) MvPolynomial.X) (by
              intro j
              cases j using Fin.cases <;> simp) f).trans hf.totalDegree_le
        · change Ideal.Quotient.mk A.ideal (chartPullback 0 f) = Q x.val
          change Ideal.Quotient.mk X.ideal f = x.val at hfx
          rw [← hfx]
          rfl⟩
      map_add' x y := Subtype.ext (Q.map_add _ _)
      map_smul' c x := Subtype.ext (Q.toLinearMap.map_smul c _) }
  have hzero (x : X.restrictionSpace D) (hx : e x = 0) : x = 0 := by
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
    change Ideal.Quotient.mk X.ideal f = x.val at hfx
    have hq : Q x.val = 0 := congrArg Subtype.val hx
    rw [← hfx] at hq
    have hfA : chartPullback 0 f ∈ A.ideal := Ideal.Quotient.eq_zero_iff_mem.mp hq
    have hfX := (homogeneous_chart_mem_iff X hX h0 f hf).mp hfA
    apply Subtype.ext
    rw [← hfx]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hfX
  have hinj : Function.Injective e := by
    intro x y hxy
    exact sub_eq_zero.mp (hzero (x-y) (by rw [map_sub, hxy, sub_self]))
  have hsurj : Function.Surjective e := by
    intro y
    obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.mp y.property
    let g := chartHomogenize (MvPolynomial.X (0 : Fin (n+1))) D
      (MvPolynomial.rename Fin.succ f)
    have hg : g.IsHomogeneous D :=
      chartHomogenize_homogeneous _ _ (MvPolynomial.isHomogeneous_X ℂ 0)
    have hgf : chartPullback 0 g = f := by
      simp only [g, chartHomogenize, map_sum, map_mul, map_pow]
      have hX0 : chartPullback (0 : Fin (n+1)) (MvPolynomial.X 0) = 1 := by
        simp [chartPullback]
      rw [hX0]
      simp only [one_pow, one_mul]
      rw [← map_sum, chart_components_sum _
        ((MvPolynomial.totalDegree_rename_le _ _).trans
          (OAI.QuarticPowerFree.mem_totalSpace.mp hf)), chartPullback_zero_rename]
    refine ⟨⟨Ideal.Quotient.mk X.ideal g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk A.ideal (chartPullback 0 g) = y.val
    rw [hgf]
    exact hfy
  exact (LinearEquiv.ofBijective e ⟨hinj, hsurj⟩).finrank_eq.symm

theorem affineChart_hilbertPolynomial {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (h0 : MvPolynomial.X (0 : Fin (n+1)) ∉ X.ideal) :
    (X.affineChart 0).hilbertPolynomial = X.hilbertPolynomial := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  obtain ⟨N, hN⟩ := X.hilbert_eventually
  filter_upwards [(X.affineChart 0).hilbert_eventually,
    Filter.eventually_gt_atTop N] with D hA hD
  exact hA.symm.trans ((congrArg (fun a : ℕ => (a : ℚ))
    (affineChart_hilbert X hX h0 D)).trans (hN D hD))

theorem affineChart_dimension {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (h0 : MvPolynomial.X (0 : Fin (n+1)) ∉ X.ideal) :
    (X.affineChart 0).dimension = X.dimension := by
  change (X.affineChart 0).hilbertPolynomial.natDegree = X.hilbertPolynomial.natDegree
  rw [affineChart_hilbertPolynomial X hX h0]

theorem affineChart_irreducible {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (h0 : MvPolynomial.X (0 : Fin (n+1)) ∉ X.ideal) :
    (X.affineChart 0).IsIrreducible := by
  have hmem (f : Poly n) : f ∈ (X.affineChart 0).ideal ↔
      MvPolynomial.rename Fin.succ f ∈
        (projectiveLinearSlice X (MvPolynomial.X 0)).ideal := by
    rw [chartHomogenize_mem_iff X hX (MvPolynomial.X 0) _
      (MvPolynomial.isHomogeneous_X ℂ 0) h0
      (MvPolynomial.totalDegree_rename_le Fin.succ f),
      ← homogeneous_chart_mem_iff X hX h0 _
        (chartHomogenize_homogeneous _ _ (MvPolynomial.isHomogeneous_X ℂ 0)),
      chartHomogenize_rename f le_rfl]
  have heq : (X.affineChart 0).ideal =
      (projectiveLinearSlice X (MvPolynomial.X 0)).ideal.comap
        (MvPolynomial.rename Fin.succ).toRingHom := by
    ext f
    exact hmem f
  rw [AffineVariety.IsIrreducible, heq]
  letI : (projectiveLinearSlice X (MvPolynomial.X 0)).ideal.IsPrime :=
    linearSlice_irreducible X hX (MvPolynomial.X 0) (MvPolynomial.isHomogeneous_X ℂ 0) h0
  infer_instance

theorem localHilbertPolynomial_zero_off {n : ℕ} (A : AffineVariety n)
    (x : Point n) (hx : x ∉ A.points) : A.localHilbertPolynomial x = 0 := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  obtain ⟨N, hN⟩ := (A.localHilbert_eventually_polynomial x).choose_spec.2
  filter_upwards [Filter.eventually_atTop.mpr ⟨N, hN⟩] with t ht
  obtain ⟨a, ha, he⟩ := ht
  rw [localHilbert_zero_off A x hx t] at ha
  have ha0 : a = 0 := by exact_mod_cast ha.symm
  change (A.localHilbertPolynomial x).eval (t : ℚ) = _ at he
  simpa [ha0] using he

theorem affineChart_origin_local_degree_le {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) :
    ((X.affineChart 0).localHilbertPolynomial (0 : Point n)).natDegree ≤ X.dimension := by
  by_cases hx : (0 : Point n) ∈ (X.affineChart 0).points
  · have h0 : MvPolynomial.X (0 : Fin (n+1)) ∉ X.ideal := by
      intro hf
      have hg : chartPullback 0 (MvPolynomial.X 0) ∈ (X.affineChart 0).ideal := by
        rw [affineChart_ideal_exact]
        exact Ideal.mem_map_of_mem _ hf
      have hz := hx _ hg
      simpa [chartPullback] using hz
    change (X.affineChart 0).localDimension (0 : Point n) ≤ X.dimension
    rw [AffineVariety.localDimension_eq_dimension _ _
      (affineChart_irreducible X hX h0) hx, affineChart_dimension X hX h0]
  · rw [localHilbertPolynomial_zero_off _ _ hx]
    simp

theorem affineChart_origin_multiplicity_coeff {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (k : ℕ) (hdim : X.dimension = k) :
    (X.affineChart 0).multiplicity (0 : Point n) =
      (k.factorial : ℚ) * ((X.affineChart 0).localHilbertPolynomial (0 : Point n)).coeff k := by
  by_cases hx : (0 : Point n) ∈ (X.affineChart 0).points
  · have h0 : MvPolynomial.X (0 : Fin (n+1)) ∉ X.ideal := by
      intro hf
      have hg : chartPullback 0 (MvPolynomial.X 0) ∈ (X.affineChart 0).ideal := by
        rw [affineChart_ideal_exact]
        exact Ideal.mem_map_of_mem _ hf
      have hz := hx _ hg
      simpa [chartPullback] using hz
    have hd := AffineVariety.localDimension_eq_dimension _ _
      (affineChart_irreducible X hX h0) hx
    rw [affineChart_dimension X hX h0, hdim] at hd
    rw [AffineVariety.multiplicity, hd]
  · rw [AffineVariety.multiplicity_eq_zero_off _ _ hx,
      localHilbertPolynomial_zero_off _ _ hx]
    simp

/-- The exact projection Hilbert decomposition, expressed in the original
global and local Hilbert polynomials. No reduced exceptional model is used. -/
theorem projection_hilbertPolynomial {n : ℕ} (X : ProjectiveVariety (n+1))
    (s : ℕ) (hs : partialElimination X.ideal s = stableElimination X.ideal) :
    X.hilbertPolynomial =
      (∑ i ∈ Finset.range s, OAI.PiExponentJets.W64.shiftHilbertPolynomial
        (OAI.PiExponentJets.W22.actualHP (partialElimination X.ideal i)
          (partialElimination_homogeneous X.ideal X.isHomogeneous i)) i) +
      OAI.PiExponentJets.W64.shiftHilbertPolynomial
        ((X.affineChart 0).localHilbertPolynomial (0 : Point n)) s := by
  let N : ℕ → ℕ := fun i => (OAI.PiExponentJets.W22.actualHP_eventually
    (partialElimination X.ideal i)
    (partialElimination_homogeneous X.ideal X.isHomogeneous i)).choose
  have hN (i d : ℕ) (hd : N i < d) :
      (Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection
        (partialElimination X.ideal i) d) : ℚ) =
      (OAI.PiExponentJets.W22.actualHP (partialElimination X.ideal i)
        (partialElimination_homogeneous X.ideal X.isHomogeneous i)).eval (d : ℚ) :=
    (OAI.PiExponentJets.W22.actualHP_eventually _ _).choose_spec d hd
  obtain ⟨M, hM⟩ := ((X.affineChart 0).localHilbert_eventually_polynomial
    (0 : Point n)).choose_spec.2
  apply OAI.PiExponentJets.W22.actualHP_unique X.ideal X.isHomogeneous _
    (s + M + (Finset.range s).sup N)
  intro D hD
  have hsD : s ≤ D := by omega
  have hglobal := hilbert_stableElimination X.ideal X.isHomogeneous s
    (fun i hi => partialElimination_eq_stable_of_ge X.ideal s hs i hi) D hsD
  obtain ⟨a, ha, he⟩ := hM (D-s) (by omega)
  rw [affineChart_localHilbert X s hs] at ha
  have ha' : (∑ i ∈ Finset.range (D-s+1), Module.finrank ℂ
      (OAI.PiExponentJets.W64.quotientSection (stableElimination X.ideal) i)) = a := by
    exact_mod_cast ha
  have hglobalQ := congrArg (fun d : ℕ => (d : ℚ)) hglobal
  rw [Nat.cast_add, Nat.cast_sum, ha'] at hglobalQ
  rw [hglobalQ, Polynomial.eval_add, Polynomial.eval_finsetSum,
    OAI.PiExponentJets.W64.shiftHilbertPolynomial_eval _ s D hsD]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hiN : N i ≤ (Finset.range s).sup N := Finset.le_sup hi
    have his : i < s := Finset.mem_range.mp hi
    rw [OAI.PiExponentJets.W64.shiftHilbertPolynomial_eval _ i D (by omega)]
    exact hN i (D-i) (by omega)
  · exact he.symm

/-- Degree separates into the finitely many partial elimination
multiplicities and the original Hilbert--Samuel multiplicity at the center. -/
theorem projection_multiplicity_decomposition {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (k : ℕ) (hdim : X.dimension = k)
    (himage : (OAI.PiExponentJets.W22.actualHP (partialElimination X.ideal 0)
      (partialElimination_homogeneous X.ideal X.isHomogeneous 0)).natDegree = k)
    (s : ℕ) (hs : partialElimination X.ideal s = stableElimination X.ideal) :
    X.degree = (∑ i ∈ Finset.range s,
      OAI.PiExponentJets.W22.actualMultiplicity (partialElimination X.ideal i)
        (partialElimination_homogeneous X.ideal X.isHomogeneous i) k) +
      (X.affineChart 0).multiplicity (0 : Point n) := by
  have hpartial (i : ℕ) : (OAI.PiExponentJets.W22.actualHP
      (partialElimination X.ideal i)
      (partialElimination_homogeneous X.ideal X.isHomogeneous i)).natDegree ≤ k := by
    rw [← himage]
    exact OAI.PiExponentJets.W22.actualHP_natDegree_antitone
      (partialElimination_homogeneous X.ideal X.isHomogeneous 0)
      (partialElimination_homogeneous X.ideal X.isHomogeneous i)
      (partialElimination_mono X.ideal (Nat.zero_le i))
  have hlocal : ((X.affineChart 0).localHilbertPolynomial (0 : Point n)).natDegree ≤ k := by
    rw [← hdim]
    exact affineChart_origin_local_degree_le X hX
  have hc := congrArg (fun P : Polynomial ℚ => P.coeff k)
    (projection_hilbertPolynomial X s hs)
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff] at hc
  have hc' : X.hilbertPolynomial.coeff k =
      (∑ i ∈ Finset.range s, (OAI.PiExponentJets.W22.actualHP
        (partialElimination X.ideal i)
        (partialElimination_homogeneous X.ideal X.isHomogeneous i)).coeff k) +
      ((X.affineChart 0).localHilbertPolynomial (0 : Point n)).coeff k := by
    simpa only [OAI.PiExponentJets.W64.shiftHilbertPolynomial_top_coeff _ _ k (hpartial _),
      OAI.PiExponentJets.W64.shiftHilbertPolynomial_top_coeff _ _ k hlocal] using hc
  unfold ProjectiveVariety.degree OAI.PiExponentJets.W22.actualMultiplicity
  rw [hdim, hc', add_mul, Finset.sum_mul,
    affineChart_origin_multiplicity_coeff X hX k hdim]
  ring

theorem partialElimination_zero_isPrime {n : ℕ} (I : Ideal (Poly (n+1)))
    (hI : I.IsPrime) : (partialElimination I 0).IsPrime := by
  rw [partialElimination_zero]
  letI := hI
  infer_instance

/-- A proper homogeneous quotient of a prime loses its top-degree term.
The zero-dimensional quotient case is included. -/
theorem actualMultiplicity_zero_of_prime_lt {n : ℕ} (P J : Ideal (Poly n))
    (hP : P.IsPrime)
    (hPh : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (hJh : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (hPJ : P < J) (k : ℕ) (hk : 1 ≤ k)
    (hdegree : (OAI.PiExponentJets.W22.actualHP P hPh).natDegree = k) :
    OAI.PiExponentJets.W22.actualMultiplicity J hJh k = 0 := by
  obtain ⟨g, hgJ, hgP⟩ : ∃ g : Poly n, g ∈ J ∧ g ∉ P := by
    by_contra h
    push_neg at h
    exact hPJ.ne (le_antisymm hPJ.le (fun g hg => h g hg))
  obtain ⟨d, hd, hfP⟩ : ∃ d ∈ Finset.range (g.totalDegree+1),
      MvPolynomial.homogeneousComponent d g ∉ P := by
    by_contra h
    push_neg at h
    apply hgP
    rw [← MvPolynomial.sum_homogeneousComponent g]
    exact Ideal.sum_mem P (fun d hd => h d hd)
  let f := MvPolynomial.homogeneousComponent d g
  have hfJ : f ∈ J := homogeneous_component_mem J hJh g hgJ d
  have hfhom : f.IsHomogeneous d := MvPolynomial.homogeneousComponent_isHomogeneous d g
  have hfne : f ≠ 0 := by
    intro hf
    apply hfP
    change f ∈ P
    rw [hf]
    exact P.zero_mem
  by_cases hd0 : d = 0
  · have htd : f.totalDegree = 0 := Nat.eq_zero_of_le_zero (by simpa [hd0] using hfhom.totalDegree_le)
    have hfc : f = MvPolynomial.C f.constantCoeff :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
    have hc : f.constantCoeff ≠ 0 := by
      intro hz
      apply hfne
      rw [hfc, hz, map_zero]
    have huC : IsUnit (MvPolynomial.C f.constantCoeff : Poly n) :=
      (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
    have hu : IsUnit f := hfc.symm ▸ huC
    have hJtop : J = ⊤ := Ideal.eq_top_of_isUnit_mem J hfJ hu
    simpa only [hJtop] using
      OAI.PiExponentJets.W22.actualMultiplicity_top (hJtop ▸ hJh) k
  · letI := hP
    have hks : k = (k-1)+1 := by omega
    have hcutdegree := (OAI.PiExponentJets.W22.actualHP_prime_cut_degree_multiplicity
      P hPh f hfhom hfP (by omega) (k-1) (hdegree.trans hks)).1
    have hle : Ideal.span {f} ⊔ P ≤ J := sup_le
      (Ideal.span_le.mpr (by rintro a rfl; exact hfJ)) hPJ.le
    have hJdegree := OAI.PiExponentJets.W22.actualHP_natDegree_antitone
      (OAI.PiExponentJets.W22.primeCut_isHomogeneous P hPh f hfhom) hJh hle
    rw [hcutdegree] at hJdegree
    unfold OAI.PiExponentJets.W22.actualMultiplicity
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- The first strict partial elimination ideal is the only integer still
to identify with the geometric generic fiber count. -/
theorem projection_degree_of_elimination_threshold {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (k : ℕ) (hk : 1 ≤ k) (hdim : X.dimension = k)
    (himage : (OAI.PiExponentJets.W22.actualHP (partialElimination X.ideal 0)
      (partialElimination_homogeneous X.ideal X.isHomogeneous 0)).natDegree = k)
    (s r : ℕ) (hs : partialElimination X.ideal s = stableElimination X.ideal)
    (hrs : r ≤ s)
    (hr : ∀ i : ℕ, partialElimination X.ideal i = partialElimination X.ideal 0 ↔ i < r) :
    (r : ℚ) * OAI.PiExponentJets.W22.actualMultiplicity (partialElimination X.ideal 0)
      (partialElimination_homogeneous X.ideal X.isHomogeneous 0) k =
      X.degree - (X.affineChart 0).multiplicity (0 : Point n) := by
  have htail (i : ℕ) (hi : r ≤ i) :
      OAI.PiExponentJets.W22.actualMultiplicity (partialElimination X.ideal i)
        (partialElimination_homogeneous X.ideal X.isHomogeneous i) k = 0 := by
    apply actualMultiplicity_zero_of_prime_lt _ _ (partialElimination_zero_isPrime X.ideal hX)
      (partialElimination_homogeneous X.ideal X.isHomogeneous 0)
      (partialElimination_homogeneous X.ideal X.isHomogeneous i) _ k hk himage
    exact lt_of_le_of_ne (partialElimination_mono X.ideal (Nat.zero_le i))
      (Ne.symm (by intro he; have := (hr i).mp he; omega))
  have hhead (i : ℕ) (hi : i < r) :
      OAI.PiExponentJets.W22.actualMultiplicity (partialElimination X.ideal i)
        (partialElimination_homogeneous X.ideal X.isHomogeneous i) k =
      OAI.PiExponentJets.W22.actualMultiplicity (partialElimination X.ideal 0)
        (partialElimination_homogeneous X.ideal X.isHomogeneous 0) k :=
    OAI.PiExponentJets.W22.actualMultiplicity_congr _ _ ((hr i).mpr hi) k
  have hsum : (∑ i ∈ Finset.range s,
      OAI.PiExponentJets.W22.actualMultiplicity (partialElimination X.ideal i)
        (partialElimination_homogeneous X.ideal X.isHomogeneous i) k) =
      (r : ℚ) * OAI.PiExponentJets.W22.actualMultiplicity (partialElimination X.ideal 0)
        (partialElimination_homogeneous X.ideal X.isHomogeneous 0) k := by
    rw [show s = r+(s-r) by omega, Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range (s-r),
        OAI.PiExponentJets.W22.actualMultiplicity (partialElimination X.ideal (r+i))
          (partialElimination_homogeneous X.ideal X.isHomogeneous (r+i)) k) = 0 :=
      Finset.sum_eq_zero (fun i _ => htail (r+i) (by omega))
    rw [hz, add_zero]
    calc
      _ = ∑ _i ∈ Finset.range r,
          OAI.PiExponentJets.W22.actualMultiplicity (partialElimination X.ideal 0)
            (partialElimination_homogeneous X.ideal X.isHomogeneous 0) k :=
        Finset.sum_congr rfl (fun i hi => hhead i (Finset.mem_range.mp hi))
      _ = _ := by simp
  have hdeg := projection_multiplicity_decomposition X hX k hdim himage s hs
  rw [hsum] at hdeg
  linarith

/-- For a genuine nonconstant cone map, the original projective image
ideal is the contraction of the original homogeneous source ideal. -/
theorem projectiveImage_ideal {a b : ℕ} (X : ProjectiveVariety a)
    (hX : X.IsIrreducible) (φ : LinearProjection a b)
    (hactual : ∃ x ∈ X.affineCone.points, φ x ≠ 0) :
    (projectiveImage φ X).ideal = X.ideal.comap
      (AffineProjection.pullback (⟨φ, 0⟩ : AffineProjection a b)).toRingHom := by
  let ψ : AffineProjection a b := ⟨φ, 0⟩
  have hψ (x : Point a) (f : Poly b) :
      MvPolynomial.eval x (ψ.pullback f) = MvPolynomial.eval (φ x) f := by
    simpa only [ψ, AffineProjection.apply, add_zero, MvPolynomial.aeval_eq_eval] using
      ψ.eval_pullback x f
  obtain ⟨x0, hx0, hxφ⟩ := hactual
  obtain ⟨j, hj⟩ : ∃ j : Fin b, φ x0 j ≠ 0 := by
    by_contra h
    push Not at h
    exact hxφ (funext h)
  let ℓ := ψ.pullback (MvPolynomial.X j)
  have hℓ : ℓ ∉ X.ideal := by
    intro hf
    apply hj
    have hz := hx0 ℓ hf
    change MvPolynomial.eval x0 (ψ.pullback (MvPolynomial.X j)) = 0 at hz
    simpa only [hψ, MvPolynomial.eval_X] using hz
  apply le_antisymm
  · intro f hf
    change ψ.pullback f ∈ X.ideal
    have hprod : ℓ * ψ.pullback f ∈ X.ideal := by
      change ℓ * ψ.pullback f ∈ X.affineCone.ideal
      rw [← AffineVariety.vanishingIdeal_points]
      intro x hx
      change MvPolynomial.eval x (ℓ * ψ.pullback f) = 0
      rw [map_mul, hψ x f]
      by_cases hφx : φ x = 0
      · have hz : MvPolynomial.eval x ℓ = 0 := by
          rw [hψ x (MvPolynomial.X j), MvPolynomial.eval_X, hφx]
          rfl
        rw [hz, zero_mul]
      · have hxne : x ≠ 0 := by intro he; exact hφx (he ▸ φ.map_zero)
        have hxproj := (ProjectiveVariety.mem_points_mk_iff X x hxne).mpr hx
        have him : Projectivization.mk ℂ (φ x) hφx ∈ (projectiveImage φ X).points :=
          ProjectiveVariety.subset_closure _ ⟨x, hxne, hxproj, hφx, rfl⟩
        have hz := him (φ x) hφx rfl f hf
        rw [show MvPolynomial.eval (φ x) f = 0 from hz, mul_zero]
    exact (hX.mem_or_mem hprod).resolve_left hℓ
  · intro f hf
    change ψ.pullback f ∈ X.ideal at hf
    change f ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives {p | ∃ x : Point a, ∃ hx : x ≠ 0,
        Projectivization.mk ℂ x hx ∈ X ∧ ∃ hφ : φ x ≠ 0,
          Projectivization.mk ℂ (φ x) hφ = p})
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro w ⟨hw, x, hx, hxX, hφ, he⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ w (φ x) hw hφ).mp he.symm
    have hxcone := (ProjectiveVariety.mem_points_mk_iff X x hx).mp hxX
    have hz := (cone_smul_mem X x hxcone c) (ψ.pullback f) hf
    change MvPolynomial.eval (c • x) (ψ.pullback f) = 0 at hz
    rw [hψ, φ.map_smul, hc] at hz
    exact hz

def coordinateProjection (n : ℕ) : LinearProjection (n+1) n where
  toFun := Fin.tail
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinateProjection_pullback (n : ℕ) :
    AffineProjection.pullback (⟨coordinateProjection n, 0⟩ : AffineProjection (n+1) n) =
      MvPolynomial.rename Fin.succ := by
  ext j
  simp [AffineProjection.pullback, linearCoordinate, coordinateProjection, Fin.tail,
    Pi.single_apply]

theorem coordinateImage_ideal {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible)
    (hactual : ∃ x ∈ X.affineCone.points, coordinateProjection n x ≠ 0) :
    (projectiveImage (coordinateProjection n) X).ideal = partialElimination X.ideal 0 := by
  rw [projectiveImage_ideal X hX _ hactual, coordinateProjection_pullback,
    partialElimination_zero]
  rfl

theorem projectiveImage_actual {a b : ℕ} (X : ProjectiveVariety a)
    (φ : LinearProjection a b) (g : Poly b) (hg : g ∉ (projectiveImage φ X).ideal) :
    ∃ x ∈ X.affineCone.points, φ x ≠ 0 := by
  by_contra hactual
  apply hg
  change g ∈ MvPolynomial.vanishingIdeal ℂ
    (ProjectiveVariety.nonzeroRepresentatives {p | ∃ x : Point a, ∃ hx : x ≠ 0,
      Projectivization.mk ℂ x hx ∈ X ∧ ∃ hφ : φ x ≠ 0,
        Projectivization.mk ℂ (φ x) hφ = p})
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro w ⟨hw, x, hx, hxX, hφ, he⟩
  exact False.elim (hactual ⟨x,
    (ProjectiveVariety.mem_points_mk_iff X x hx).mp hxX, hφ⟩)

/-- Coordinate form of the frozen theorem, with the geometric fiber
degree identification isolated as the remaining premise. -/
theorem coordinate_degree_of_elimination_threshold {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (k : ℕ) (hk : 1 ≤ k) (hdim : X.dimension = k)
    (himage : (projectiveImage (coordinateProjection n) X).dimension = k)
    (hactual : ∃ x ∈ X.affineCone.points, coordinateProjection n x ≠ 0)
    (s r : ℕ) (hs : partialElimination X.ideal s = stableElimination X.ideal)
    (hrs : r ≤ s)
    (hr : ∀ i : ℕ, partialElimination X.ideal i = partialElimination X.ideal 0 ↔ i < r) :
    (r : ℚ) * (projectiveImage (coordinateProjection n) X).degree =
      X.degree - (X.affineChart 0).multiplicity (0 : Point n) := by
  let Y := projectiveImage (coordinateProjection n) X
  have hI := coordinateImage_ideal X hX hactual
  have hP := OAI.PiExponentJets.W22.actualHP_congr Y.isHomogeneous
    (partialElimination_homogeneous X.ideal X.isHomogeneous 0) hI
  have hdimP : (OAI.PiExponentJets.W22.actualHP (partialElimination X.ideal 0)
      (partialElimination_homogeneous X.ideal X.isHomogeneous 0)).natDegree = k := by
    rw [← hP]
    exact himage
  have hdeg : Y.degree = OAI.PiExponentJets.W22.actualMultiplicity
      (partialElimination X.ideal 0)
      (partialElimination_homogeneous X.ideal X.isHomogeneous 0) k := by
    unfold ProjectiveVariety.degree
    rw [himage]
    exact OAI.PiExponentJets.W22.actualMultiplicity_congr _ _ hI k
  rw [show (projectiveImage (coordinateProjection n) X).degree = _ from hdeg]
  exact projection_degree_of_elimination_threshold X hX k hk hdim hdimP s r hs hrs hr

/-- Algebraic domain fibers on a principal base open have the actual
unlocalized module rank. -/
theorem algebraic_field_hom_fibers_rank (R B : Type*)
    [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B]
    [Algebra.IsAlgebraic R B] [Module.IsTorsionFree R B] :
    ∃ g : R, g ≠ 0 ∧ 0 < Module.finrank R B ∧
      ∀ (K : Type*) [Field K] [Algebra R K] [IsAlgClosed K],
        algebraMap R K g ≠ 0 → Finite (B →ₐ[R] K) ∧ Nat.card (B →ₐ[R] K) = Module.finrank R B := by
  obtain ⟨g, hg, hf, he⟩ := algebraic_finiteType_finite_etale_base_open R B
  let Rg := Localization (Submonoid.powers g)
  let Bg := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))
  have hM : Submonoid.powers g ≤ nonZeroDivisors R := Submonoid.powers_le.mpr
    (mem_nonZeroDivisors_of_ne_zero hg)
  have hMB : Algebra.algebraMapSubmonoid B (Submonoid.powers g) ≤ nonZeroDivisors B :=
    Submonoid.map_le_of_le_comap _ (hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective R B)))
  haveI : IsDomain Rg := IsLocalization.isDomain_of_le_nonZeroDivisors Rg hM
  haveI : IsDomain Bg := IsLocalization.isDomain_of_le_nonZeroDivisors Bg hMB
  haveI : Module.IsTorsionFree Rg Bg := Module.IsTorsionFree.of_isLocalization R B hM
  haveI : IsLocalization.Away (algebraMap R B g) Bg := by
    change IsLocalization (Submonoid.powers (algebraMap R B g)) Bg
    rw [show Submonoid.powers (algebraMap R B g) =
      Algebra.algebraMapSubmonoid B (Submonoid.powers g) by
      simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]]
    infer_instance
  haveI : Module.Finite Rg Bg := hf
  haveI : Algebra.Etale Rg Bg := he
  haveI : FaithfulSMul R Rg := (faithfulSMul_iff_algebraMap_injective R Rg).mpr
    (IsLocalization.injective Rg hM)
  have hbc : IsBaseChange Rg (IsScalarTower.toAlgHom R B Bg).toLinearMap :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers g) Rg B Bg).symm.out
  have hfr : Module.finrank Rg Bg = Module.finrank R B := hbc.finrank_eq
  refine ⟨g, hg, by rw [← hfr]; exact Module.finrank_pos, ?_⟩
  intro K _ _ _ hgK
  let hunit : IsUnit (algebraMap R K g) := isUnit_iff_ne_zero.mpr hgK
  letI : Algebra Rg K := (IsLocalization.Away.lift (S := Rg) g hunit).toAlgebra
  haveI : IsScalarTower R Rg K := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq g hunit a).symm
  obtain ⟨_, hfinite, hcard⟩ := finite_etale_domain_field_hom_count Rg Bg K
  let e := localized_base_field_hom_equiv R B Rg Bg K g hgK
  letI := hfinite
  exact ⟨Finite.of_equiv _ e, (Nat.card_congr e.symm).trans (hcard.trans hfr)⟩

theorem monogenic_fraction_adjoin (R F A L : Type*)
    [CommRing R] [Field F] [CommRing A] [Field L]
    [Algebra R A] [Algebra R F] [Algebra A L] [Algebra R L] [Algebra F L]
    [IsScalarTower R A L] [IsScalarTower R F L]
    [IsFractionRing R F] [IsFractionRing A L]
    (a : A) (ha : Algebra.adjoin R ({a} : Set A) = ⊤) :
    IntermediateField.adjoin F ({algebraMap A L a} : Set L) = ⊤ := by
  let S := IntermediateField.adjoin F ({algebraMap A L a} : Set L)
  let ι : A →ₐ[R] L := IsScalarTower.toAlgHom R A L
  have hsub : Algebra.adjoin R ({a} : Set A) ≤
      (S.toSubalgebra.restrictScalars R).comap ι := by
    apply Algebra.adjoin_le
    rintro x rfl
    exact IntermediateField.subset_adjoin F _ (Set.mem_singleton _)
  have hA (x : A) : algebraMap A L x ∈ S := by
    exact hsub (ha.symm ▸ (show x ∈ (⊤ : Subalgebra R A) from trivial))
  apply top_unique
  intro z _
  obtain ⟨x, y, _, hxy⟩ := IsFractionRing.div_surjective A z
  rw [← hxy]
  exact S.div_mem (hA x) (hA y)

theorem monogenic_fraction_minpoly_rank (R F A L : Type*)
    [CommRing R] [Field F] [CommRing A] [Field L]
    [Algebra R A] [Algebra R F] [Algebra A L] [Algebra R L] [Algebra F L]
    [IsScalarTower R A L] [IsScalarTower R F L]
    [IsFractionRing R F] [IsFractionRing A L]
    (a : A) (ha : Algebra.adjoin R ({a} : Set A) = ⊤)
    (hi : IsIntegral F (algebraMap A L a)) :
    (minpoly F (algebraMap A L a)).natDegree = Module.finrank R A := by
  have h := IntermediateField.adjoin.finrank hi
  rw [monogenic_fraction_adjoin R F A L a ha] at h
  rw [(IntermediateField.topEquiv : (⊤ : IntermediateField F L) ≃ₐ[F] L).toLinearEquiv.finrank_eq] at h
  exact h.symm.trans (IsFractionRing.finrank_eq R F A L)

theorem monogenic_minimal_relation (R F A L : Type*)
    [CommRing R] [IsDomain R] [Field F] [CommRing A] [IsDomain A] [Field L]
    [Algebra R A] [Algebra R F] [Algebra A L] [Algebra R L] [Algebra F L]
    [IsScalarTower R A L] [IsScalarTower R F L]
    [IsFractionRing R F] [IsFractionRing A L]
    (a : A) (ha : Algebra.adjoin R ({a} : Set A) = ⊤)
    (hi : IsIntegral F (algebraMap A L a)) :
    ∃ p : Polynomial R, Polynomial.aeval a p = 0 ∧
      p.natDegree = Module.finrank R A ∧ p.coeff (Module.finrank R A) ≠ 0 := by
  let q := minpoly F (algebraMap A L a)
  let p := IsLocalization.integerNormalization (nonZeroDivisors R) q
  have hroot : Polynomial.aeval (algebraMap A L a) p = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors R) q
      (minpoly.aeval F (algebraMap A L a))
  have hrootA : Polynomial.aeval a p = 0 := by
    apply IsFractionRing.injective A L
    rw [map_zero]
    have he := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R A L) a p
    change Polynomial.aeval (algebraMap A L a) p = algebraMap A L (Polynomial.aeval a p) at he
    exact he.symm.trans hroot
  obtain ⟨c, hc, hp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hdeg : p.natDegree = q.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R F), hp,
      Polynomial.natDegree_smul q hc0]
  have hrank : p.natDegree = Module.finrank R A := hdeg.trans
    (monogenic_fraction_minpoly_rank R F A L a ha hi)
  have hp0 : p ≠ 0 := by
    exact mt (IsLocalization.integerNormalization_eq_zero_iff le_rfl q).mp (minpoly.ne_zero hi)
  refine ⟨p, hrootA, hrank, ?_⟩
  rw [← hrank]
  rw [Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hp0

theorem monogenic_relation_rank_le (R F A L : Type*)
    [CommRing R] [IsDomain R] [Field F] [CommRing A] [IsDomain A] [Field L]
    [Algebra R A] [Algebra R F] [Algebra A L] [Algebra R L] [Algebra F L]
    [IsScalarTower R A L] [IsScalarTower R F L]
    [IsFractionRing R F] [IsFractionRing A L]
    (a : A) (ha : Algebra.adjoin R ({a} : Set A) = ⊤)
    (hi : IsIntegral F (algebraMap A L a))
    (p : Polynomial R) (hp : p ≠ 0) (hroot : Polynomial.aeval a p = 0) :
    Module.finrank R A ≤ p.natDegree := by
  rw [← monogenic_fraction_minpoly_rank R F A L a ha hi]
  let q := p.map (algebraMap R F)
  have hq : q ≠ 0 := by
    exact fun hz => hp ((Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F))
      (hz.trans (Polynomial.map_zero _).symm))
  have hrootL : Polynomial.aeval (algebraMap A L a) q = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    have he := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R A L) a p
    change Polynomial.aeval (algebraMap A L a) p = algebraMap A L (Polynomial.aeval a p) at he
    rw [he, hroot, map_zero]
  have hd := minpoly.degree_le_of_ne_zero F (algebraMap A L a) hq hrootL
  have hn := Polynomial.natDegree_le_natDegree hd
  rwa [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R F)] at hn


theorem monogenic_algebraic_rank_relations (R A : Type*)
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [FaithfulSMul R A] [Algebra.IsAlgebraic R A]
    (a : A) (ha : Algebra.adjoin R ({a} : Set A) = ⊤) :
    (∃ p : Polynomial R, Polynomial.aeval a p = 0 ∧
      p.natDegree = Module.finrank R A ∧ p.coeff (Module.finrank R A) ≠ 0) ∧
    (∀ p : Polynomial R, p ≠ 0 → Polynomial.aeval a p = 0 →
      Module.finrank R A ≤ p.natDegree) := by
  let F := FractionRing R
  let L := Localization.AtPrime (⊥ : Ideal A)
  haveI : IsFractionRing A L := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  letI : Field L := IsFractionRing.toField A
  haveI : FaithfulSMul R L := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R A L]
    exact (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective R A)
  letI := FractionRing.liftAlgebra R L
  haveI : Algebra.IsAlgebraic R L := (IsFractionRing.isAlgebraic_iff' R A L).mp inferInstance
  haveI : Algebra.IsAlgebraic F L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := F)).mp inferInstance
  have hi : IsIntegral F (algebraMap A L a) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := F) (algebraMap A L a)).isIntegral
  exact ⟨monogenic_minimal_relation R F A L a ha hi,
    fun p hp hroot => monogenic_relation_rank_le R F A L a ha hi p hp hroot⟩


abbrev CoordinateBase {n : ℕ} (X : ProjectiveVariety (n+1)) :=
  Poly n ⧸ partialElimination X.ideal 0

abbrev CoordinateAlgebra {n : ℕ} (X : ProjectiveVariety (n+1)) := Poly (n+1) ⧸ X.ideal

def coordinateInclusion {n : ℕ} (X : ProjectiveVariety (n+1)) :
    CoordinateBase X →ₐ[ℂ] CoordinateAlgebra X :=
  Ideal.Quotient.liftₐ (partialElimination X.ideal 0)
    ((Ideal.Quotient.mkₐ ℂ X.ideal).comp (MvPolynomial.rename Fin.succ)) (by
      intro f hf
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rwa [partialElimination_zero, Ideal.mem_comap] at hf)

theorem coordinateInclusion_mk {n : ℕ} (X : ProjectiveVariety (n+1)) (f : Poly n) :
    coordinateInclusion X (Ideal.Quotient.mk (partialElimination X.ideal 0) f) =
      Ideal.Quotient.mk X.ideal (MvPolynomial.rename Fin.succ f) := rfl

theorem coordinateInclusion_injective {n : ℕ} (X : ProjectiveVariety (n+1)) :
    Function.Injective (coordinateInclusion X) := by
  apply (RingHom.injective_iff_ker_eq_bot (coordinateInclusion X).toRingHom).mpr
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change coordinateInclusion X (Ideal.Quotient.mk (partialElimination X.ideal 0) f) = 0 at hx
  rw [coordinateInclusion_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rwa [partialElimination_zero, Ideal.mem_comap]

abbrev coordinateAlgebra {n : ℕ} (X : ProjectiveVariety (n+1)) :
    Algebra (CoordinateBase X) (CoordinateAlgebra X) :=
  (coordinateInclusion X).toRingHom.toAlgebra

def coordinateRank {n : ℕ} (X : ProjectiveVariety (n+1)) : ℕ :=
  letI := coordinateAlgebra X
  letI : Module (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toModule
  Module.finrank (CoordinateBase X) (CoordinateAlgebra X)

def coordinateGenerator {n : ℕ} (X : ProjectiveVariety (n+1)) : CoordinateAlgebra X :=
  Ideal.Quotient.mk X.ideal (MvPolynomial.X 0)

theorem coordinateAlgebra_adjoin {n : ℕ} (X : ProjectiveVariety (n+1)) :
    letI := coordinateAlgebra X
    Algebra.adjoin (CoordinateBase X) ({coordinateGenerator X} : Set (CoordinateAlgebra X)) = ⊤ := by
  letI := coordinateAlgebra X
  let S := Algebra.adjoin (CoordinateBase X) ({coordinateGenerator X} : Set (CoordinateAlgebra X))
  have hbase (f : Poly n) : Ideal.Quotient.mk X.ideal (MvPolynomial.rename Fin.succ f) ∈ S := by
    change algebraMap (CoordinateBase X) (CoordinateAlgebra X)
      (Ideal.Quotient.mk (partialElimination X.ideal 0) f) ∈ S
    exact S.algebraMap_mem _
  have hgen : coordinateGenerator X ∈ S := Algebra.subset_adjoin (Set.mem_singleton _)
  have hall (F : Poly (n+1)) : Ideal.Quotient.mk X.ideal F ∈ S := by
    induction F using MvPolynomial.induction_on with
    | C c => simpa using hbase (MvPolynomial.C c)
    | add f g hf hg => simpa only [map_add] using S.add_mem hf hg
    | mul_X f j hf =>
      rw [map_mul]
      apply S.mul_mem hf
      cases j using Fin.cases with
      | zero => exact hgen
      | succ j => simpa using hbase (MvPolynomial.X j)
  apply top_unique
  intro z _
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact hall F

theorem coordinateGenerator_eval {n : ℕ} (X : ProjectiveVariety (n+1)) (F : Poly (n+1)) :
    letI := coordinateAlgebra X
    letI : Module (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toModule
    letI : SMul (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toSMul
    Polynomial.aeval (coordinateGenerator X)
      ((MvPolynomial.finSuccEquiv ℂ n F).map (Ideal.Quotient.mk (partialElimination X.ideal 0))) =
      Ideal.Quotient.mk X.ideal F := by
  letI := coordinateAlgebra X
  letI : Module (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toModule
  letI : SMul (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toSMul
  have hc : (algebraMap (CoordinateBase X) (CoordinateAlgebra X)).comp
      (Ideal.Quotient.mk (partialElimination X.ideal 0)) =
      (Ideal.Quotient.mk X.ideal).comp (MvPolynomial.rename Fin.succ).toRingHom := by
    apply RingHom.ext
    intro f
    exact coordinateInclusion_mk X f
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hc]
  have hvar (j : Fin (n+1)) : Polynomial.eval₂
      ((Ideal.Quotient.mk X.ideal).comp (MvPolynomial.rename Fin.succ).toRingHom)
      (coordinateGenerator X) (MvPolynomial.finSuccEquiv ℂ n (MvPolynomial.X j)) =
      Ideal.Quotient.mk X.ideal (MvPolynomial.X j) := by
    cases j using Fin.cases with
    | zero => simp only [MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval₂_X,
        coordinateGenerator]
    | succ j => simp [MvPolynomial.finSuccEquiv_X_succ]
  induction F using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.finSuccEquiv_apply]
  | add f g hf hg => simp only [map_add, Polynomial.eval₂_add, hf, hg]
  | mul_X f j hf =>
    rw [map_mul, Polynomial.eval₂_mul, hf, hvar, map_mul]

set_option maxHeartbeats 800000 in
theorem partialElimination_eq_zero_iff_rank {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible)
    (halg : letI := coordinateAlgebra X
      Algebra.IsAlgebraic (CoordinateBase X) (CoordinateAlgebra X)) (j : ℕ) :
    letI := coordinateAlgebra X
    letI : Module (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toModule
    letI : SMul (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toSMul
    partialElimination X.ideal j = partialElimination X.ideal 0 ↔
      j < Module.finrank (CoordinateBase X) (CoordinateAlgebra X) := by
  let R := CoordinateBase X
  let A := CoordinateAlgebra X
  letI : X.ideal.IsPrime := hX
  letI : (partialElimination X.ideal 0).IsPrime := partialElimination_zero_isPrime X.ideal hX
  letI := coordinateAlgebra X
  letI : Module R A := (coordinateAlgebra X).toModule
  letI : SMul R A := (coordinateAlgebra X).toSMul
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr
    (coordinateInclusion_injective X)
  haveI : Algebra.IsAlgebraic R A := halg
  let a := coordinateGenerator X
  let r := Module.finrank R A
  have ha : Algebra.adjoin R ({a} : Set A) = ⊤ := coordinateAlgebra_adjoin X
  obtain ⟨hminimal, hbound⟩ := monogenic_algebraic_rank_relations R A a ha
  change partialElimination X.ideal j = partialElimination X.ideal 0 ↔ j < r
  constructor
  · intro heq
    by_contra hj
    have hrj : r ≤ j := by omega
    obtain ⟨p, hp, hpdeg, hpcoeff⟩ := hminimal
    obtain ⟨q, hqmap, hqdeg⟩ := Polynomial.exists_natDegree_eq_of_mem_lifts
      (Polynomial.mem_lifts_of_surjective
        (Ideal.Quotient.mk_surjective (I := partialElimination X.ideal 0)) p)
    let G := (MvPolynomial.finSuccEquiv ℂ n).symm q
    have hGq : MvPolynomial.finSuccEquiv ℂ n G = q :=
      (MvPolynomial.finSuccEquiv ℂ n).apply_symm_apply q
    have hGI : G ∈ X.ideal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← coordinateGenerator_eval X G, hGq, hqmap]
      exact hp
    have hqrank : q.natDegree = r := hqdeg.trans hpdeg
    have hcoeff : q.coeff r ∈ partialElimination X.ideal r :=
      (mem_partialElimination_iff X.ideal r _).mpr ⟨G, hGI, by
        rw [hGq]
        exact Polynomial.degree_le_of_natDegree_le hqrank.le, by rw [hGq]⟩
    have hcoeff0 : q.coeff r ∈ partialElimination X.ideal 0 := by
      rw [← heq]
      exact partialElimination_mono X.ideal hrj hcoeff
    have hecoeff := congrArg (fun f : Polynomial R => f.coeff r) hqmap
    rw [Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem.mpr hcoeff0] at hecoeff
    exact hpcoeff hecoeff.symm
  · intro hj
    apply le_antisymm _ (partialElimination_mono X.ideal (Nat.zero_le j))
    intro f hf
    by_contra hf0
    obtain ⟨G, hGI, hGdeg, hGcoeff⟩ := (mem_partialElimination_iff X.ideal j f).mp hf
    let q := (MvPolynomial.finSuccEquiv ℂ n G).map (Ideal.Quotient.mk (partialElimination X.ideal 0))
    have hqne : q ≠ 0 := by
      intro hz
      have hc := congrArg (fun f : Polynomial R => f.coeff j) hz
      rw [Polynomial.coeff_map, hGcoeff, Polynomial.coeff_zero] at hc
      exact hf0 (Ideal.Quotient.eq_zero_iff_mem.mp hc)
    have hroot : Polynomial.aeval a q = 0 :=
      (coordinateGenerator_eval X G).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hGI)
    have hrank := hbound q hqne hroot
    have hqdeg : q.natDegree ≤ j :=
      (Polynomial.natDegree_map_le).trans (Polynomial.natDegree_le_of_degree_le hGdeg)
    exact (Nat.not_le_of_gt hj) (hrank.trans hqdeg)

set_option maxHeartbeats 800000 in
theorem coordinateAlgebra_scalarTower {n : ℕ} (X : ProjectiveVariety (n+1)) :
    letI := coordinateAlgebra X
    letI : Module (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toModule
    letI : SMul (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toSMul
    IsScalarTower ℂ (CoordinateBase X) (CoordinateAlgebra X) := by
  letI := coordinateAlgebra X
  letI : Module (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toModule
  letI : SMul (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toSMul
  exact IsScalarTower.of_algebraMap_eq (R := ℂ) (S := CoordinateBase X)
    (A := CoordinateAlgebra X) fun c => (coordinateInclusion X).commutes c |>.symm

theorem coordinateAlgebra_isAlgebraic {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (k : ℕ) (hdim : X.dimension = k)
    (himage : (projectiveImage (coordinateProjection n) X).dimension = k)
    (hactual : ∃ x ∈ X.affineCone.points, coordinateProjection n x ≠ 0) :
    letI := coordinateAlgebra X
    Algebra.IsAlgebraic (CoordinateBase X) (CoordinateAlgebra X) := by
  let R := CoordinateBase X
  let A := CoordinateAlgebra X
  let Y := projectiveImage (coordinateProjection n) X
  letI : X.ideal.IsPrime := hX
  letI : (partialElimination X.ideal 0).IsPrime := partialElimination_zero_isPrime X.ideal hX
  letI := coordinateAlgebra X
  letI : Module R A := (coordinateAlgebra X).toModule
  letI : SMul R A := (coordinateAlgebra X).toSMul
  haveI : IsScalarTower ℂ R A := coordinateAlgebra_scalarTower X
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr
    (coordinateInclusion_injective X)
  have hI : Y.ideal = partialElimination X.ideal 0 := coordinateImage_ideal X hX hactual
  have hY : Y.IsIrreducible := by
    change Y.ideal.IsPrime
    rw [hI]
    infer_instance
  letI : Y.ideal.IsPrime := hY
  have hR : Algebra.trdeg ℂ R = ((k+1 : ℕ) : Cardinal) := by
    change Algebra.trdeg ℂ (Poly n ⧸ partialElimination X.ideal 0) = _
    rw [← hI, ← GenericFiber.affineDimension_eq_trdeg]
    change ((Y.affineCone.dimension : ℕ) : Cardinal) = _
    rw [ProjectiveVariety.dimension_cone Y (ProjectiveFamily.irreducible_points_nonempty Y hY), himage]
  have hA : Algebra.trdeg ℂ A = ((k+1 : ℕ) : Cardinal) := by
    change Algebra.trdeg ℂ (Poly (n+1) ⧸ X.ideal) = _
    rw [← GenericFiber.affineDimension_eq_trdeg]
    change ((X.affineCone.dimension : ℕ) : Cardinal) = _
    rw [ProjectiveVariety.dimension_cone X (ProjectiveFamily.irreducible_points_nonempty X hX), hdim]
  exact algebraic_of_equal_finite_trdeg ℂ R A (k+1) hR hA

def coneFiberProjectiveEquiv {a b : ℕ} (X : ProjectiveVariety a)
    (φ : LinearProjection a b) (y : Point b) (hy : y ≠ 0) :
    {x : Point a // x ∈ X.affineCone.points ∧ φ x = y} ≃
      projectiveFiber φ X (Projectivization.mk ℂ y hy) := by
  let toProj (x : {x : Point a // x ∈ X.affineCone.points ∧ φ x = y}) :
      projectiveFiber φ X (Projectivization.mk ℂ y hy) := by
    have hx : x.1 ≠ 0 := by intro h; exact hy (x.2.2.symm.trans (by rw [h, map_zero]))
    let q := Projectivization.mk ℂ x.1 hx
    refine ⟨q, (ProjectiveVariety.mem_points_mk_iff X x.1 hx).mpr x.2.1, ?_⟩
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x.1 hx
    change (u : ℂ) • x.1 = q.rep at hu
    have hφ : φ q.rep = (u : ℂ) • y := by rw [← hu, map_smul, x.2.2]
    have hφne : φ q.rep ≠ 0 := by rw [hφ]; exact smul_ne_zero (Units.ne_zero u) hy
    refine ⟨hφne, ?_⟩
    change Projectivization.mk ℂ (φ q.rep) hφne = Projectivization.mk ℂ y hy
    exact (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr ⟨u, hφ.symm⟩
  apply Equiv.ofBijective toProj
  constructor
  · intro x w h
    have hm := congrArg Subtype.val h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ x.1 w.1 _ _).mp hm
    have hcy : c • y = y := by
      simpa only [map_smul, w.2.2, x.2.2] using congrArg φ hc
    have hc1 : c = 1 := smul_left_injective ℂ hy (hcy.trans (one_smul ℂ y).symm)
    apply Subtype.ext
    rw [hc1, one_smul] at hc
    exact hc.symm
  · intro q
    obtain ⟨hqX, hφq, hmap⟩ := q.2
    change Projectivization.mk ℂ (φ q.1.rep) hφq = Projectivization.mk ℂ y hy at hmap
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ y (φ q.1.rep) hy hφq).mp hmap.symm
    have hc0 : c ≠ 0 := by intro hz; rw [hz, zero_smul] at hc; exact hy hc.symm
    have hqcone : q.1.rep ∈ X.affineCone.points :=
      (ProjectiveVariety.mem_points_mk_iff X q.1.rep q.1.rep_nonzero).mp
        (by simpa only [Projectivization.mk_rep] using hqX)
    let x : {x : Point a // x ∈ X.affineCone.points ∧ φ x = y} :=
      ⟨c • q.1.rep, cone_smul_mem X q.1.rep hqcone c, by rw [map_smul, hc]⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change Projectivization.mk ℂ (c • q.1.rep) _ = q.1
    exact ((Projectivization.mk_eq_mk_iff' ℂ _ q.1.rep _ q.1.rep_nonzero).mpr
      ⟨c, rfl⟩).trans (Projectivization.mk_rep q.1)

def coordinateBasePoint {n : ℕ} (X : ProjectiveVariety (n+1)) (y : Point n)
    (hy : ∀ f ∈ partialElimination X.ideal 0, MvPolynomial.aeval y f = 0) :
    CoordinateBase X →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (partialElimination X.ideal 0) (MvPolynomial.aeval y) hy

def coordinateHomEquivFiber {n : ℕ} (X : ProjectiveVariety (n+1)) (y : Point n)
    (hy : ∀ f ∈ partialElimination X.ideal 0, MvPolynomial.aeval y f = 0) :
    letI := coordinateAlgebra X
    letI : Module (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toModule
    letI : SMul (CoordinateBase X) (CoordinateAlgebra X) := (coordinateAlgebra X).toSMul
    letI := (coordinateBasePoint X y hy).toRingHom.toAlgebra
    letI : Module (CoordinateBase X) ℂ := (coordinateBasePoint X y hy).toRingHom.toAlgebra.toModule
    letI : SMul (CoordinateBase X) ℂ := (coordinateBasePoint X y hy).toRingHom.toAlgebra.toSMul
    (CoordinateAlgebra X →ₐ[CoordinateBase X] ℂ) ≃
      {x : Point (n+1) // x ∈ X.affineCone.points ∧ coordinateProjection n x = y} := by
  let R := CoordinateBase X
  let A := CoordinateAlgebra X
  letI := coordinateAlgebra X
  letI : Module R A := (coordinateAlgebra X).toModule
  letI : SMul R A := (coordinateAlgebra X).toSMul
  haveI : IsScalarTower ℂ R A := coordinateAlgebra_scalarTower X
  letI := (coordinateBasePoint X y hy).toRingHom.toAlgebra
  letI : Module R ℂ := (coordinateBasePoint X y hy).toRingHom.toAlgebra.toModule
  letI : SMul R ℂ := (coordinateBasePoint X y hy).toRingHom.toAlgebra.toSMul
  haveI : IsScalarTower ℂ R ℂ := IsScalarTower.of_algHom (coordinateBasePoint X y hy)
  let point (h : A →ₐ[R] ℂ) : Point (n+1) :=
    fun i => h (Ideal.Quotient.mk X.ideal (MvPolynomial.X i))
  have hpoint (h : A →ₐ[R] ℂ) : MvPolynomial.aeval (point h) =
      (h.restrictScalars ℂ).comp (Ideal.Quotient.mkₐ ℂ X.ideal) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  let fromPoint (x : {x : Point (n+1) // x ∈ X.affineCone.points ∧ coordinateProjection n x = y}) :
      A →ₐ[R] ℂ :=
    { __ := (Ideal.Quotient.liftₐ X.ideal (MvPolynomial.aeval x.1) x.2.1).toRingHom
      commutes' r := by
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
        change (Ideal.Quotient.liftₐ X.ideal (MvPolynomial.aeval x.1) x.2.1)
          (coordinateInclusion X (Ideal.Quotient.mk (partialElimination X.ideal 0) f)) =
          coordinateBasePoint X y hy (Ideal.Quotient.mk (partialElimination X.ideal 0) f)
        rw [coordinateInclusion_mk]
        simp only [coordinateBasePoint, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
          ]
        change MvPolynomial.eval x.1 (MvPolynomial.rename Fin.succ f) = MvPolynomial.eval y f
        rw [MvPolynomial.eval_rename]
        have htail : (fun j => x.1 j.succ) = y := x.2.2
        change x.1 ∘ Fin.succ = y at htail
        rw [htail] }
  refine
    { toFun := fun h => ⟨point h, ?_⟩
      invFun := fromPoint
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro f hf
      change f ∈ X.ideal at hf
      change MvPolynomial.aeval (point h) f = 0
      rw [hpoint, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
    · funext j
      change h (Ideal.Quotient.mk X.ideal (MvPolynomial.X j.succ)) = y j
      have hc := h.commutes (Ideal.Quotient.mk (partialElimination X.ideal 0) (MvPolynomial.X j))
      change h (coordinateInclusion X (Ideal.Quotient.mk (partialElimination X.ideal 0)
        (MvPolynomial.X j))) = MvPolynomial.aeval y (MvPolynomial.X j) at hc
      simpa only [coordinateInclusion_mk, MvPolynomial.rename_X, MvPolynomial.aeval_X] using hc
  · intro h
    apply AlgHom.ext
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    change (Ideal.Quotient.liftₐ X.ideal (MvPolynomial.aeval (point h)) _)
      (Ideal.Quotient.mk X.ideal f) = _
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, hpoint]
    rfl
  · intro x
    apply Subtype.ext
    funext i
    change (Ideal.Quotient.liftₐ X.ideal (MvPolynomial.aeval x.1) x.2.1)
      (Ideal.Quotient.mk X.ideal (MvPolynomial.X i)) = x.1 i
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact MvPolynomial.aeval_X x.1 i

theorem coordinate_genericDegree_eq_rank {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (k : ℕ) (hdim : X.dimension = k)
    (himage : (projectiveImage (coordinateProjection n) X).dimension = k) (r : ℕ)
    (hr : GenericallyFiniteProjectiveDegree (coordinateProjection n) X r) :
    coordinateRank X = r := by
  obtain ⟨_, G, D, hGhom, hGnot, hGfib⟩ := hr
  have hactual := projectiveImage_actual X (coordinateProjection n) G hGnot
  let R := CoordinateBase X
  let A := CoordinateAlgebra X
  let Y := projectiveImage (coordinateProjection n) X
  letI : X.ideal.IsPrime := hX
  letI : (partialElimination X.ideal 0).IsPrime := partialElimination_zero_isPrime X.ideal hX
  letI := coordinateAlgebra X
  letI : Module R A := (coordinateAlgebra X).toModule
  letI : SMul R A := (coordinateAlgebra X).toSMul
  haveI : IsScalarTower ℂ R A := coordinateAlgebra_scalarTower X
  haveI : Module.IsTorsionFree R A := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (coordinateInclusion_injective X)
  haveI : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R A
  haveI : Algebra.IsAlgebraic R A := coordinateAlgebra_isAlgebraic X hX k hdim himage hactual
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℂ R).injective
  obtain ⟨g, hg, _, hcount⟩ := algebraic_field_hom_fibers_rank R A
  obtain ⟨H, hH⟩ := Ideal.Quotient.mk_surjective g
  have hHnot : H ∉ partialElimination X.ideal 0 := by
    intro h
    exact hg (hH.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  have hI : Y.ideal = partialElimination X.ideal 0 := coordinateImage_ideal X hX hactual
  have hY : Y.IsIrreducible := by
    change Y.ideal.IsPrime
    rw [hI]
    infer_instance
  have hHY : H ∉ Y.ideal := by rwa [hI]
  obtain ⟨q, hq⟩ := ProjectiveFamily.irreducible_points_nonempty Y hY
  obtain ⟨j, hj⟩ := exists_nonzero_coordinate q
  have hqcone : q.rep ∈ Y.affineCone.points :=
    (ProjectiveVariety.mem_points_mk_iff Y q.rep q.rep_nonzero).mp
      (by simpa only [Projectivization.mk_rep] using hq)
  have hjY : MvPolynomial.X j ∉ Y.ideal := by
    intro h
    exact hj (by simpa only [MvPolynomial.aeval_X] using hqcone (MvPolynomial.X j) h)
  have hFnot : H * G * MvPolynomial.X j ∉ Y.ideal := by
    intro h
    rcases hY.mem_or_mem h with hHG | hj
    · exact (hY.mem_or_mem hHG).elim hHY hGnot
    · exact hjY hj
  obtain ⟨y, hyY, hyF⟩ : ∃ y ∈ Y.affineCone.points,
      MvPolynomial.eval y (H * G * MvPolynomial.X j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hFnot
    change H * G * MvPolynomial.X j ∈ Y.affineCone.ideal
    rw [← AffineVariety.vanishingIdeal_points]
    intro y hy
    simpa only [MvPolynomial.aeval_eq_eval] using h y hy
  have hyHGj : (MvPolynomial.eval y H * MvPolynomial.eval y G) * y j ≠ 0 := by
    simpa only [map_mul, MvPolynomial.eval_X] using hyF
  have hyH : MvPolynomial.eval y H ≠ 0 := (mul_ne_zero_iff.mp
    (mul_ne_zero_iff.mp hyHGj).1).1
  have hyG : MvPolynomial.eval y G ≠ 0 := (mul_ne_zero_iff.mp
    (mul_ne_zero_iff.mp hyHGj).1).2
  have hy0 : y ≠ 0 := by
    intro h
    exact (mul_ne_zero_iff.mp hyHGj).2 (congrFun h j)
  have hy : ∀ f ∈ partialElimination X.ideal 0, MvPolynomial.aeval y f = 0 := by
    intro f hf
    exact hyY f (by change f ∈ Y.ideal; rwa [hI])
  letI := (coordinateBasePoint X y hy).toRingHom.toAlgebra
  letI : Module R ℂ := (coordinateBasePoint X y hy).toRingHom.toAlgebra.toModule
  letI : SMul R ℂ := (coordinateBasePoint X y hy).toRingHom.toAlgebra.toSMul
  have hgval : algebraMap R ℂ g ≠ 0 := by
    change coordinateBasePoint X y hy g ≠ 0
    rw [← hH]
    exact hyH
  obtain ⟨hfinite, hcard⟩ := hcount ℂ hgval
  letI := hfinite
  let e := (coordinateHomEquivFiber X y hy).trans
    (coneFiberProjectiveEquiv X (coordinateProjection n) y hy0)
  haveI : Finite (projectiveFiber (coordinateProjection n) X (Projectivization.mk ℂ y hy0)) :=
    Finite.of_equiv _ e
  have hprojcount : (projectiveFiber (coordinateProjection n) X
      (Projectivization.mk ℂ y hy0)).ncard = coordinateRank X :=
    (Nat.card_congr e.symm).trans hcard
  have hyproj : Projectivization.mk ℂ y hy0 ∈ Y.points :=
    (ProjectiveVariety.mem_points_mk_iff Y y hy0).mpr hyY
  have hyGrep : MvPolynomial.eval (Projectivization.mk ℂ y hy0).rep G ≠ 0 := by
    exact fun h => hyG ((Bridges.homogeneous_eval_zero_mk_iff G hGhom y hy0).mp h)
  exact hprojcount.symm.trans (hGfib _ hyproj hyGrep).2

/-- The complete point-projection degree formula in literal coordinate
projection, using the supplied geometric fiber degree. -/
theorem coordinate_projection_point {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (k : ℕ) (hk : 1 ≤ k) (hdim : X.dimension = k)
    (himage : (projectiveImage (coordinateProjection n) X).dimension = k) (r : ℕ)
    (hr : GenericallyFiniteProjectiveDegree (coordinateProjection n) X r) :
    (r : ℚ) * (projectiveImage (coordinateProjection n) X).degree =
      X.degree - (X.affineChart 0).multiplicity (0 : Point n) := by
  have hrank := coordinate_genericDegree_eq_rank X hX k hdim himage r hr
  obtain ⟨_, G, _, _, hG, _⟩ := hr
  have hactual := projectiveImage_actual X (coordinateProjection n) G hG
  have halg := coordinateAlgebra_isAlgebraic X hX k hdim himage hactual
  obtain ⟨s, hs⟩ := partialElimination_stabilizes X.ideal
  apply coordinate_degree_of_elimination_threshold X hX k hk hdim himage hactual (max s r) r
    (hs (max s r) (le_max_left s r)) (le_max_right s r)
  intro i
  have ht := partialElimination_eq_zero_iff_rank X hX halg i
  change partialElimination X.ideal i = partialElimination X.ideal 0 ↔ i < coordinateRank X at ht
  rwa [hrank] at ht

theorem linearPullback_eval {a b : ℕ} (φ : LinearProjection a b)
    (x : Point a) (f : Poly b) :
    MvPolynomial.eval x (linearPullback φ f) = MvPolynomial.eval (φ x) f := by
  change MvPolynomial.aeval x (MvPolynomial.aeval (linearCoordinate φ) f) = _
  rw [MvPolynomial.comp_aeval_apply]
  have h : (fun j => MvPolynomial.aeval x (linearCoordinate φ j)) = φ x := by
    funext j
    exact TrackA.linearCoordinate_eval φ x j
  rw [h, MvPolynomial.aeval_eq_eval]

theorem linearPullback_eq_affine {a b : ℕ} (φ : LinearProjection a b) :
    linearPullback φ =
      AffineProjection.pullback (⟨φ, 0⟩ : AffineProjection a b) := by
  ext j
  simp [linearPullback, AffineProjection.pullback]

theorem linearPullback_homogeneous {a b d : ℕ} (φ : LinearProjection a b)
    (f : Poly b) (hf : f.IsHomogeneous d) : (linearPullback φ f).IsHomogeneous d := by
  change (MvPolynomial.aeval (linearCoordinate φ) f).IsHomogeneous d
  simpa only [one_mul] using hf.aeval (linearCoordinate φ)
    (TrackA.linearCoordinate_homogeneous φ)

def polynomialLinearEquiv {n : ℕ} (e : Point n ≃ₗ[ℂ] Point n) :
    Poly n ≃ₐ[ℂ] Poly n where
  __ := linearPullback e.toLinearMap
  invFun := linearPullback e.symm.toLinearMap
  left_inv f := by
    apply MvPolynomial.funext
    intro x
    change MvPolynomial.eval x (linearPullback e.symm.toLinearMap
      (linearPullback e.toLinearMap f)) = MvPolynomial.eval x f
    rw [linearPullback_eval, linearPullback_eval]
    simp only [LinearEquiv.coe_coe, e.apply_symm_apply]
  right_inv f := by
    apply MvPolynomial.funext
    intro x
    change MvPolynomial.eval x (linearPullback e.toLinearMap
      (linearPullback e.symm.toLinearMap f)) = MvPolynomial.eval x f
    rw [linearPullback_eval, linearPullback_eval]
    simp only [LinearEquiv.coe_coe, e.symm_apply_apply]

@[simp] theorem polynomialLinearEquiv_apply {n : ℕ} (e : Point n ≃ₗ[ℂ] Point n)
    (f : Poly n) : polynomialLinearEquiv e f = linearPullback e.toLinearMap f := rfl

@[simp] theorem polynomialLinearEquiv_symm_apply {n : ℕ} (e : Point n ≃ₗ[ℂ] Point n)
    (f : Poly n) : (polynomialLinearEquiv e).symm f = linearPullback e.symm.toLinearMap f := rfl

theorem linearEquiv_image_ideal {n : ℕ} (X : ProjectiveVariety n)
    (hX : X.IsIrreducible) (e : Point n ≃ₗ[ℂ] Point n) :
    (projectiveImage e.toLinearMap X).ideal =
      X.ideal.comap (polynomialLinearEquiv e).toRingHom := by
  obtain ⟨q, hq⟩ := ProjectiveFamily.irreducible_points_nonempty X hX
  have hx := (ProjectiveVariety.mem_points_mk_iff X q.rep q.rep_nonzero).mp
    (by simpa only [Projectivization.mk_rep] using hq)
  have he : e q.rep ≠ 0 := fun h => q.rep_nonzero (e.injective (h.trans e.map_zero.symm))
  change (projectiveImage e.toLinearMap X).ideal = X.ideal.comap (linearPullback e.toLinearMap).toRingHom
  simpa only [← linearPullback_eq_affine] using
    projectiveImage_ideal X hX e.toLinearMap ⟨q.rep, hx, he⟩

theorem linearEquiv_image_irreducible {n : ℕ} (X : ProjectiveVariety n)
    (hX : X.IsIrreducible) (e : Point n ≃ₗ[ℂ] Point n) :
    (projectiveImage e.toLinearMap X).IsIrreducible := by
  change (projectiveImage e.toLinearMap X).ideal.IsPrime
  rw [linearEquiv_image_ideal X hX e]
  letI : X.ideal.IsPrime := hX
  infer_instance

theorem linearPullback_symm {n : ℕ} (e : Point n ≃ₗ[ℂ] Point n) (f : Poly n) :
    linearPullback e.toLinearMap (linearPullback e.symm.toLinearMap f) = f := by
  simpa only [polynomialLinearEquiv_apply, polynomialLinearEquiv_symm_apply] using
    (polynomialLinearEquiv e).apply_symm_apply f

theorem linearPullback_aeval {a b : ℕ} (φ : LinearProjection a b)
    (x : Point a) (f : Poly b) :
    MvPolynomial.aeval x (linearPullback φ f) = MvPolynomial.aeval (φ x) f := by
  change MvPolynomial.eval x (linearPullback φ f) = MvPolynomial.eval (φ x) f
  exact linearPullback_eval φ x f

theorem polynomialEquiv_zeroLocus_comap {n : ℕ} (I : Ideal (Poly n))
    (P : Poly n ≃ₐ[ℂ] Poly n) (x y : Point n)
    (heval : ∀ f, MvPolynomial.aeval x (P f) = MvPolynomial.aeval y f) :
    y ∈ MvPolynomial.zeroLocus ℂ (I.comap P.toRingHom) ↔
      x ∈ MvPolynomial.zeroLocus ℂ I := by
  constructor
  · intro hx f hf
    have hg : P.symm f ∈ I.comap P.toRingHom := by
      change P (P.symm f) ∈ I
      rw [P.apply_symm_apply]
      exact hf
    calc
      MvPolynomial.aeval x f = MvPolynomial.aeval x (P (P.symm f)) :=
        congrArg (fun g : Poly n => MvPolynomial.aeval x g) (P.apply_symm_apply f).symm
      _ = MvPolynomial.aeval y (P.symm f) := heval _
      _ = 0 := hx _ hg
  · intro hx f hf
    exact (heval f).symm.trans (hx _ hf)

theorem linearEquiv_zeroLocus_comap {n : ℕ} (I : Ideal (Poly n))
    (e : Point n ≃ₗ[ℂ] Point n) (x : Point n) :
    e x ∈ MvPolynomial.zeroLocus ℂ (I.comap (linearPullback e.toLinearMap).toRingHom) ↔
      x ∈ MvPolynomial.zeroLocus ℂ I :=
  polynomialEquiv_zeroLocus_comap I (polynomialLinearEquiv e) x (e x)
    (linearPullback_aeval e.toLinearMap x)

theorem linearEquiv_cone_mem {n : ℕ} (X : ProjectiveVariety n)
    (hX : X.IsIrreducible) (e : Point n ≃ₗ[ℂ] Point n) (x : Point n) :
    e x ∈ (projectiveImage e.toLinearMap X).affineCone.points ↔ x ∈ X.affineCone.points := by
  have hI := linearEquiv_image_ideal X hX e
  change (projectiveImage e.toLinearMap X).ideal =
    X.ideal.comap (linearPullback e.toLinearMap).toRingHom at hI
  change e x ∈ MvPolynomial.zeroLocus ℂ (projectiveImage e.toLinearMap X).ideal ↔
    x ∈ MvPolynomial.zeroLocus ℂ X.ideal
  rw [hI]
  exact linearEquiv_zeroLocus_comap X.ideal e x

def projectionCoordinates {n : ℕ} (i : Fin (n+1)) (φ : LinearProjection (n+1) n) :
    Point (n+1) →ₗ[ℂ] Point (n+1) where
  toFun x := Fin.cons (x i) (φ x)
  map_add' _ _ := by ext j; cases j using Fin.cases <;> simp
  map_smul' _ _ := by ext j; cases j using Fin.cases <;> simp

theorem projectionCoordinates_injective {n : ℕ} (p : ProjectivePoint (n+1))
    (i : Fin (n+1)) (hi : p.rep i ≠ 0) (φ : LinearProjection (n+1) n)
    (hkernel : LinearMap.ker φ = p.submodule) :
    Function.Injective (projectionCoordinates i φ) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  change Fin.cons (α := fun _ => ℂ) (x i) (φ x) = 0 at hx
  have hxi : x i = 0 := by
    simpa only [Fin.cons_zero, Pi.zero_apply]
      using congrFun hx (0 : Fin (n+1))
  have hφx : φ x = 0 := by
    funext j
    simpa only [Fin.cons_succ, Pi.zero_apply]
      using congrFun hx j.succ
  have hspan : x ∈ ℂ ∙ p.rep := by
    rw [← Projectivization.submodule_eq, ← hkernel]
    exact hφx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  have hc0 : c = 0 := by
    have hz : c * p.rep i = 0 := by
      simpa only [Pi.smul_apply, smul_eq_mul, hxi] using congrFun hc i
    exact (mul_eq_zero.mp hz).resolve_right hi
  change x = 0
  rw [← hc, hc0, zero_smul]

def projectionCoordinateEquiv {n : ℕ} (p : ProjectivePoint (n+1))
    (i : Fin (n+1)) (hi : p.rep i ≠ 0) (φ : LinearProjection (n+1) n)
    (hkernel : LinearMap.ker φ = p.submodule) : Point (n+1) ≃ₗ[ℂ] Point (n+1) :=
  LinearEquiv.ofBijective (projectionCoordinates i φ)
    ⟨projectionCoordinates_injective p i hi φ hkernel,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (projectionCoordinates_injective p i hi φ hkernel)⟩

theorem linearEquiv_image_hilbert {n : ℕ} (X : ProjectiveVariety n)
    (hX : X.IsIrreducible) (e : Point n ≃ₗ[ℂ] Point n) (D : ℕ) :
    (projectiveImage e.toLinearMap X).hilbert D = X.hilbert D := by
  let Y := projectiveImage e.toLinearMap X
  let P := polynomialLinearEquiv e
  have hI : X.ideal = Y.ideal.map P.toRingHom := by
    rw [linearEquiv_image_ideal X hX e]
    exact (Ideal.map_comap_of_surjective P.toRingHom P.surjective X.ideal).symm
  let Q := Ideal.quotientEquivAlg Y.ideal X.ideal P hI
  have hmap : (Y.restrictionSpace D).map Q.toLinearMap = X.restrictionSpace D := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨f, hf, hfz⟩ := Submodule.mem_map.mp hz
      refine Submodule.mem_map.mpr ⟨P f, linearPullback_homogeneous e.toLinearMap f hf, ?_⟩
      change Ideal.Quotient.mk X.ideal (P f) = Q z
      rw [← hfz]
      rfl
    · rintro ⟨f, hf, rfl⟩
      refine Submodule.mem_map.mpr ⟨Ideal.Quotient.mk Y.ideal (P.symm f), ?_, ?_⟩
      · exact Submodule.mem_map.mpr ⟨P.symm f,
          linearPullback_homogeneous e.symm.toLinearMap f hf, rfl⟩
      · change Ideal.Quotient.mk X.ideal (P (P.symm f)) = Ideal.Quotient.mk X.ideal f
        rw [P.apply_symm_apply]
  exact (Q.toLinearEquiv.ofSubmodules _ _ hmap).finrank_eq

theorem linearEquiv_image_hilbertPolynomial {n : ℕ} (X : ProjectiveVariety n)
    (hX : X.IsIrreducible) (e : Point n ≃ₗ[ℂ] Point n) :
    (projectiveImage e.toLinearMap X).hilbertPolynomial = X.hilbertPolynomial := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  obtain ⟨NX, hNX⟩ := X.hilbert_eventually
  obtain ⟨NY, hNY⟩ := (projectiveImage e.toLinearMap X).hilbert_eventually
  filter_upwards [Filter.eventually_gt_atTop (max NX NY)] with D hD
  rw [← hNX D (lt_of_le_of_lt (le_max_left _ _) hD),
    ← hNY D (lt_of_le_of_lt (le_max_right _ _) hD), linearEquiv_image_hilbert X hX e]

theorem linearEquiv_image_dimension {n : ℕ} (X : ProjectiveVariety n)
    (hX : X.IsIrreducible) (e : Point n ≃ₗ[ℂ] Point n) :
    (projectiveImage e.toLinearMap X).dimension = X.dimension := by
  unfold ProjectiveVariety.dimension
  rw [linearEquiv_image_hilbertPolynomial X hX e]

theorem linearEquiv_image_degree {n : ℕ} (X : ProjectiveVariety n)
    (hX : X.IsIrreducible) (e : Point n ≃ₗ[ℂ] Point n) :
    (projectiveImage e.toLinearMap X).degree = X.degree := by
  change (projectiveImage e.toLinearMap X).hilbertPolynomial.coeff
      (projectiveImage e.toLinearMap X).dimension *
      ((projectiveImage e.toLinearMap X).dimension.factorial : ℚ) =
    X.hilbertPolynomial.coeff X.dimension * (X.dimension.factorial : ℚ)
  rw [linearEquiv_image_hilbertPolynomial X hX e, linearEquiv_image_dimension X hX e]

theorem linearEquiv_projectiveImage_comp {a b : ℕ} (X : ProjectiveVariety a)
    (hX : X.IsIrreducible) (e : Point a ≃ₗ[ℂ] Point a)
    (ψ φ : LinearProjection a b) (hcomp : ∀ x, ψ (e x) = φ x)
    (hactual : ∃ x ∈ X.affineCone.points, φ x ≠ 0) :
    projectiveImage ψ (projectiveImage e.toLinearMap X) = projectiveImage φ X := by
  let Y := projectiveImage e.toLinearMap X
  have hY := linearEquiv_image_irreducible X hX e
  have hactualY : ∃ x ∈ Y.affineCone.points, ψ x ≠ 0 := by
    obtain ⟨x, hx, hφx⟩ := hactual
    exact ⟨e x, (linearEquiv_cone_mem X hX e x).mpr hx, by rwa [hcomp]⟩
  have hpb : (polynomialLinearEquiv e).toRingHom.comp
      (linearPullback ψ).toRingHom = (linearPullback φ).toRingHom := by
    apply RingHom.ext
    intro f
    apply MvPolynomial.funext
    intro x
    change MvPolynomial.eval x (linearPullback e.toLinearMap (linearPullback ψ f)) =
      MvPolynomial.eval x (linearPullback φ f)
    rw [linearPullback_eval, linearPullback_eval, linearPullback_eval]
    change MvPolynomial.eval (ψ (e x)) f = _
    rw [hcomp]
  apply ProjectiveVariety.ext
  rw [projectiveImage_ideal Y hY ψ hactualY,
    projectiveImage_ideal X hX φ hactual, ← linearPullback_eq_affine,
    ← linearPullback_eq_affine, linearEquiv_image_ideal X hX e,
    Ideal.comap_comap, hpb]

def linearEquiv_coneFiberEquiv {a b : ℕ} (X : ProjectiveVariety a)
    (hX : X.IsIrreducible) (e : Point a ≃ₗ[ℂ] Point a)
    (ψ φ : LinearProjection a b) (hcomp : ∀ x, ψ (e x) = φ x) (y : Point b) :
    {x : Point a // x ∈ X.affineCone.points ∧ φ x = y} ≃
      {x : Point a // x ∈ (projectiveImage e.toLinearMap X).affineCone.points ∧ ψ x = y} where
  toFun x := ⟨e x.1, (linearEquiv_cone_mem X hX e x.1).mpr x.2.1,
    (hcomp x.1).trans x.2.2⟩
  invFun x := ⟨e.symm x.1,
    (linearEquiv_cone_mem X hX e (e.symm x.1)).mp (by simpa only [e.apply_symm_apply] using x.2.1),
    by rw [← hcomp, e.apply_symm_apply]; exact x.2.2⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.1

def linearEquiv_projectiveFiberEquiv {a b : ℕ} (X : ProjectiveVariety a)
    (hX : X.IsIrreducible) (e : Point a ≃ₗ[ℂ] Point a)
    (ψ φ : LinearProjection a b) (hcomp : ∀ x, ψ (e x) = φ x) (z : ProjectivePoint b) :
    projectiveFiber φ X z ≃ projectiveFiber ψ (projectiveImage e.toLinearMap X) z := by
  simpa only [Projectivization.mk_rep] using
    (coneFiberProjectiveEquiv X φ z.rep z.rep_nonzero).symm.trans
      ((linearEquiv_coneFiberEquiv X hX e ψ φ hcomp z.rep).trans
        (coneFiberProjectiveEquiv (projectiveImage e.toLinearMap X) ψ z.rep z.rep_nonzero))

theorem linearEquiv_genericDegree {a b : ℕ} (X : ProjectiveVariety a)
    (hX : X.IsIrreducible) (e : Point a ≃ₗ[ℂ] Point a)
    (ψ φ : LinearProjection a b) (hcomp : ∀ x, ψ (e x) = φ x) (r : ℕ)
    (hr : GenericallyFiniteProjectiveDegree φ X r) :
    GenericallyFiniteProjectiveDegree ψ (projectiveImage e.toLinearMap X) r := by
  obtain ⟨hrpos, G, D, hhom, hGnot, hGfib⟩ := hr
  have hactual := projectiveImage_actual X φ G hGnot
  have himage := linearEquiv_projectiveImage_comp X hX e ψ φ hcomp hactual
  refine ⟨hrpos, G, D, hhom, by rwa [himage], ?_⟩
  intro z hz hG
  rw [himage] at hz
  obtain ⟨hfin, hcard⟩ := hGfib z hz hG
  letI := hfin.to_subtype
  let E := linearEquiv_projectiveFiberEquiv X hX e ψ φ hcomp z
  haveI : Finite (projectiveFiber ψ (projectiveImage e.toLinearMap X) z) :=
    Finite.of_equiv _ E
  exact ⟨Set.toFinite _, (Nat.card_congr E.symm).trans hcard⟩

theorem chartPoint_mem_iff {n : ℕ} (X : ProjectiveVariety (n+1))
    (i : Fin (n+1)) (z : Point n) :
    z ∈ (X.affineChart i).points ↔ Fin.insertNth i 1 z ∈ X.affineCone.points := by
  constructor
  · intro hz f hf
    have hmap : chartPullback i f ∈ (X.affineChart i).ideal := by
      rw [affineChart_ideal_exact]
      exact Ideal.mem_map_of_mem _ hf
    have he := hz _ hmap
    change MvPolynomial.eval z (chartPullback i f) = 0 at he
    simpa only [chartPullback_eval, MvPolynomial.aeval_eq_eval] using he
  · intro hz
    simpa only [Fin.insertNth_apply_succAbove] using
      chart_points_from_cone X i (Fin.insertNth i 1 z) hz (by simp)

def chartForwardPullback {n : ℕ} (i : Fin (n+1)) (φ : LinearProjection (n+1) n) :
    Poly n →ₐ[ℂ] Poly n := (chartPullback i).comp (linearPullback φ)

def chartInversePullback {n : ℕ} (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) : Poly n →ₐ[ℂ] Poly n :=
  (chartPullback 0).comp ((linearPullback e.symm.toLinearMap).comp
    (MvPolynomial.rename i.succAbove))

theorem chartForwardPullback_eval {n : ℕ} (i : Fin (n+1))
    (φ : LinearProjection (n+1) n) (z : Point n) (f : Poly n) :
    MvPolynomial.eval z (chartForwardPullback i φ f) =
      MvPolynomial.eval (φ (Fin.insertNth i 1 z)) f := by
  change MvPolynomial.eval z (chartPullback i (linearPullback φ f)) = _
  rw [chartPullback_eval, linearPullback_eval]

theorem chartInversePullback_eval {n : ℕ} (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (w : Point n) (f : Poly n) :
    MvPolynomial.eval w (chartInversePullback i e f) =
      MvPolynomial.eval (fun j => e.symm (Fin.cons 1 w) (i.succAbove j)) f := by
  change MvPolynomial.eval w (chartPullback 0
    (linearPullback e.symm.toLinearMap (MvPolynomial.rename i.succAbove f))) = _
  rw [chartPullback_eval, Fin.insertNth_zero', linearPullback_eval, MvPolynomial.eval_rename]
  rfl

theorem chartTransport_inverse_normalization {n : ℕ} (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (φ : LinearProjection (n+1) n)
    (he : ∀ x, e x = Fin.cons (x i) (φ x)) (w : Point n) :
    Fin.insertNth i 1 (fun j => e.symm (Fin.cons 1 w) (i.succAbove j)) =
      e.symm (Fin.cons 1 w) := by
  have h := congrFun (he (e.symm (Fin.cons 1 w))) 0
  rw [e.apply_symm_apply] at h
  change 1 = e.symm (Fin.cons 1 w) i at h
  exact Fin.insertNth_eq_iff.mpr ⟨h, rfl⟩

theorem chartTransport_forward_normalization {n : ℕ} (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (φ : LinearProjection (n+1) n)
    (he : ∀ x, e x = Fin.cons (x i) (φ x)) (z : Point n) :
    e (Fin.insertNth i 1 z) = Fin.cons 1 (φ (Fin.insertNth i 1 z)) := by
  rw [he]
  simp only [Fin.insertNth_apply_same]

theorem chartTransport_forward_inverse {n : ℕ} (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (φ : LinearProjection (n+1) n)
    (he : ∀ x, e x = Fin.cons (x i) (φ x)) (w : Point n) :
    φ (Fin.insertNth i 1 (fun j => e.symm (Fin.cons 1 w) (i.succAbove j))) = w := by
  rw [chartTransport_inverse_normalization i e φ he]
  have h := congrArg Fin.tail (he (e.symm (Fin.cons 1 w)))
  simpa only [e.apply_symm_apply, Fin.tail_cons] using h.symm

theorem chartTransport_inverse_forward {n : ℕ} (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (φ : LinearProjection (n+1) n)
    (he : ∀ x, e x = Fin.cons (x i) (φ x)) (z : Point n) :
    (fun j => e.symm (Fin.cons 1 (φ (Fin.insertNth i 1 z))) (i.succAbove j)) = z := by
  rw [← chartTransport_forward_normalization i e φ he, e.symm_apply_apply]
  funext j
  exact Fin.insertNth_apply_succAbove (α := fun _ => ℂ) i 1 z j

theorem chartInverse_forward {n : ℕ} (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (φ : LinearProjection (n+1) n)
    (he : ∀ x, e x = Fin.cons (x i) (φ x)) (f : Poly n) :
    chartInversePullback i e (chartForwardPullback i φ f) = f := by
  apply MvPolynomial.funext
  intro w
  rw [chartInversePullback_eval, chartForwardPullback_eval,
    chartTransport_forward_inverse i e φ he]

theorem chartForward_inverse {n : ℕ} (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (φ : LinearProjection (n+1) n)
    (he : ∀ x, e x = Fin.cons (x i) (φ x)) (f : Poly n) :
    chartForwardPullback i φ (chartInversePullback i e f) = f := by
  apply MvPolynomial.funext
  intro z
  rw [chartForwardPullback_eval, chartInversePullback_eval,
    chartTransport_inverse_forward i e φ he]

theorem chartForwardPullback_mem {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (φ : LinearProjection (n+1) n)
    (he : ∀ x, e x = Fin.cons (x i) (φ x)) (f : Poly n)
    (hf : f ∈ ((projectiveImage e.toLinearMap X).affineChart 0).ideal) :
    chartForwardPullback i φ f ∈ (X.affineChart i).ideal := by
  rw [← AffineVariety.vanishingIdeal_points]
  intro z hz
  change MvPolynomial.eval z (chartForwardPullback i φ f) = 0
  rw [chartForwardPullback_eval]
  have hx := (chartPoint_mem_iff X i z).mp hz
  have hy := (linearEquiv_cone_mem X hX e _).mpr hx
  rw [chartTransport_forward_normalization i e φ he] at hy
  have hw := (chartPoint_mem_iff (projectiveImage e.toLinearMap X) 0
    (φ (Fin.insertNth i 1 z))).mpr (by simpa only [Fin.insertNth_zero'] using hy)
  exact hw f hf

theorem chartInversePullback_mem {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (φ : LinearProjection (n+1) n)
    (he : ∀ x, e x = Fin.cons (x i) (φ x)) (f : Poly n)
    (hf : f ∈ (X.affineChart i).ideal) :
    chartInversePullback i e f ∈ ((projectiveImage e.toLinearMap X).affineChart 0).ideal := by
  rw [← AffineVariety.vanishingIdeal_points]
  intro w hw
  change MvPolynomial.eval w (chartInversePullback i e f) = 0
  rw [chartInversePullback_eval]
  have hy := (chartPoint_mem_iff (projectiveImage e.toLinearMap X) 0 w).mp hw
  rw [Fin.insertNth_zero'] at hy
  have hx := (linearEquiv_cone_mem X hX e (e.symm (Fin.cons 1 w))).mp
    (by simpa only [e.apply_symm_apply] using hy)
  have hz := (chartPoint_mem_iff X i
    (fun j => e.symm (Fin.cons 1 w) (i.succAbove j))).mpr
    (by rwa [chartTransport_inverse_normalization i e φ he])
  exact hz f hf

theorem chartTransport_multiplicity {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (i : Fin (n+1))
    (e : Point (n+1) ≃ₗ[ℂ] Point (n+1)) (φ : LinearProjection (n+1) n)
    (he : ∀ x, e x = Fin.cons (x i) (φ x)) (a : Point n)
    (ha : φ (Fin.insertNth i 1 a) = 0) :
    (X.affineChart i).multiplicity a =
      ((projectiveImage e.toLinearMap X).affineChart 0).multiplicity (0 : Point n) := by
  have hinv : (fun j => e.symm (Fin.cons 1 (0 : Point n)) (i.succAbove j)) = a := by
    simpa only [ha] using chartTransport_inverse_forward i e φ he a
  apply multiplicity_eq_of_localHilbert_eq
  intro t
  apply localHilbert_eq_of_retraction (X.affineChart i)
    ((projectiveImage e.toLinearMap X).affineChart 0)
    (chartInversePullback i e) (chartForwardPullback i φ)
    (chartInverse_forward i e φ he) a 0
  · intro f
    rw [chartInversePullback_eval, hinv]
  · intro f
    rw [chartForwardPullback_eval, ha]
  · exact chartInversePullback_mem X hX i e φ he
  · exact chartForwardPullback_mem X hX i e φ he
  · intro f
    rw [chartForward_inverse i e φ he, sub_self]
    exact Ideal.zero_mem _

theorem normalized_chartCoordinates {n : ℕ} (p : ProjectivePoint (n+1))
    (i : Fin (n+1)) (hi : p.rep i ≠ 0) :
    Fin.insertNth i 1 (chartCoordinates i p) = (p.rep i)⁻¹ • p.rep := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
  · simp [hi]
  · simp [chartCoordinates, div_eq_mul_inv, mul_comm]

/-- Transport the coordinate theorem through the linear coordinate change
whose first coordinate is the chosen affine-chart coordinate. -/
theorem arbitrary_projection_point {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (k : ℕ) (hk : 1 ≤ k) (hdim : X.dimension = k)
    (p : ProjectivePoint (n+1)) (φ : LinearProjection (n+1) n)
    (hkernel : LinearMap.ker φ = p.submodule)
    (himage : (projectiveImage φ X).dimension = k) (r : ℕ)
    (hr : GenericallyFiniteProjectiveDegree φ X r) :
    (r : ℚ) * (projectiveImage φ X).degree = X.degree - X.multiplicity p := by
  let i := chartIndex p
  have hi : p.rep i ≠ 0 := chartIndex_nonzero p
  let e := projectionCoordinateEquiv p i hi φ hkernel
  let Y := projectiveImage e.toLinearMap X
  have he (x : Point (n+1)) : e x = Fin.cons (x i) (φ x) := rfl
  have hcomp (x : Point (n+1)) : coordinateProjection n (e x) = φ x := by
    change Fin.tail (Fin.cons (α := fun _ => ℂ) (x i) (φ x)) = φ x
    exact Fin.tail_cons (α := fun _ => ℂ) (x i) (φ x)
  have hactual : ∃ x ∈ X.affineCone.points, φ x ≠ 0 := by
    obtain ⟨_, G, _, _, hG, _⟩ := hr
    exact projectiveImage_actual X φ G hG
  have hIm : projectiveImage (coordinateProjection n) Y = projectiveImage φ X :=
    linearEquiv_projectiveImage_comp X hX e (coordinateProjection n) φ hcomp hactual
  have hpker : φ p.rep = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hkernel, Projectivization.submodule_eq]
    exact Submodule.mem_span_singleton_self p.rep
  have hcenter : φ (Fin.insertNth i 1 (chartCoordinates i p)) = 0 := by
    rw [normalized_chartCoordinates p i hi, map_smul, hpker, smul_zero]
  have hmult : X.multiplicity p = (Y.affineChart 0).multiplicity (0 : Point n) :=
    chartTransport_multiplicity X hX i e φ he (chartCoordinates i p) hcenter
  have hformula := coordinate_projection_point Y
    (linearEquiv_image_irreducible X hX e) k hk
    ((linearEquiv_image_dimension X hX e).trans hdim)
    (by rwa [hIm]) r (linearEquiv_genericDegree X hX e (coordinateProjection n) φ hcomp r hr)
  rw [hIm, linearEquiv_image_degree X hX e, ← hmult] at hformula
  exact hformula

end PointProjection
end
end DistinctDistances.TrackA
