import DistinctDistances.TrackA.HomogeneousNormalizationSupport
import DistinctDistances.OAIInterface.FiniteGradedQuotient

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra
universe u v

/-- Once every sufficiently high homogeneous piece lies in the linear
parameter ideal, the lower pieces generate over the parameter algebra.
This is the degree induction used with the fixed homogenizing coordinate. -/
theorem graded_linear_parameters_span_low_degrees
    {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
    (G : ℕ → Submodule K A) [GradedAlgebra G]
    {s : ℕ} (z : Fin s → A) (hz : ∀ i, z i ∈ G 1) (c : ℕ)
    (hc : ∀ n, c ≤ n → ∀ a ∈ G n, a ∈ Ideal.span (Set.range z)) :
    Submodule.span (Algebra.adjoin K (Set.range z))
      (((Finset.range (c+1)).sup G : Submodule K A) : Set A) = ⊤ := by
  let B := Algebra.adjoin K (Set.range z)
  let U := (Finset.range (c+1)).sup G
  let M := Submodule.span B (U : Set A)
  have hgrades : ∀ n, ∀ a ∈ G n, a ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      by_cases hn : n ≤ c
      · apply Submodule.subset_span
        exact (Finset.le_sup (f := G) (Finset.mem_range.mpr (by omega))) ha
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        obtain ⟨b, hb, hsum⟩ := OAI.Lech.LinearNormalization.homogeneous_span_coefficients
          G z hz ha (hc (m+1) (by omega) a ha)
        rw [← hsum]
        apply Submodule.sum_mem
        intro i _
        have hzB : z i ∈ B := Algebra.subset_adjoin (Set.mem_range_self i)
        have ht := M.smul_mem (⟨z i, hzB⟩ : B) (ih m (by omega) (b i) (hb i))
        change z i * b i ∈ M at ht
        simpa only [mul_comm] using ht
  apply eq_top_iff.mpr
  intro a _
  rw [← sum_support_decompose G a]
  exact M.sum_mem fun n _ => hgrades n _ (decompose G a n).property

/-- Finite homogeneous pieces and the degree induction make the actual
polynomial parameter map finite. -/
theorem graded_finite_of_high_degrees_in_parameter_ideal
    {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
    (G : ℕ → Submodule K A) [GradedAlgebra G]
    [∀ n, Module.Finite K (G n)]
    {s : ℕ} (z : Fin s → A) (hz : ∀ i, z i ∈ G 1) (c : ℕ)
    (hc : ∀ n, c ≤ n → ∀ a ∈ G n, a ∈ Ideal.span (Set.range z)) :
    (MvPolynomial.aeval (R := K) z).Finite := by
  let B := Algebra.adjoin K (Set.range z)
  let U := (Finset.range (c+1)).sup G
  have hU : U.FG := Submodule.fg_finset_sup _ _
    (fun n _ => Module.Finite.iff_fg.mp inferInstance)
  have hM : (Submodule.span B (U : Set A)).FG := hU.span
  have htop : Submodule.span B (U : Set A) = ⊤ :=
    graded_linear_parameters_span_low_degrees G z hz c hc
  let : Module.Finite B A := ⟨by rwa [htop] at hM⟩
  let g := MvPolynomial.aeval (R := K) z
  have hgB : g.range = B := (Algebra.adjoin_range_eq_range_aeval K z).symm
  have hv : g.range.val.Finite := by
    rw [hgB]
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact hv.comp (AlgHom.Finite.of_surjective _ g.rangeRestrict_surjective)

/-- A finite quotient by the degree-one parameters supplies the high
degree bound through the original OAI finite-grading theorem. -/
theorem graded_finite_of_parameter_quotient_finite
    {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
    (G : ℕ → Submodule K A) [GradedAlgebra G]
    [∀ n, Module.Finite K (G n)]
    {s : ℕ} (z : Fin s → A) (hz : ∀ i, z i ∈ G 1)
    [Module.Finite K (A ⧸ Ideal.span (Set.range z))] :
    (MvPolynomial.aeval (R := K) z).Finite := by
  let J := Ideal.span (Set.range z)
  let q : A →ₗ[K] A ⧸ J := J.mkQ.restrictScalars K
  have hJ : J.IsHomogeneous G := Ideal.homogeneous_span G _
    (by rintro _ ⟨i, rfl⟩; exact ⟨1, hz i⟩)
  have hker : q.ker.IsHomogeneous G := by
    rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
    exact hJ
  let H := OAI.Lech.Grading.imagePiece G q
  let : Decomposition H := OAI.Lech.Grading.imageDecomposition G q J.mkQ_surjective hker
  obtain ⟨c, hc⟩ := OAI.Lech.LinearNormalization.finite_grading_bounded H
  apply graded_finite_of_high_degrees_in_parameter_ideal G z hz c
  intro n hn a ha
  have hqa : q a ∈ H n := ⟨a, ha, rfl⟩
  rw [hc n hn] at hqa
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q a = 0
  simpa using hqa

/-- The finite-generation bridge for the literal homogeneous coordinate
quotient; parameters need not be independent and the ideal need not be reduced. -/
theorem homogeneous_quotient_finite_of_linear_parameter_quotient {n s : ℕ}
    (I : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (z : Fin s → Poly n ⧸ I) (hz : ∀ i, z i ∈ OAI.PiExponentJets.W64.quotientSection I 1)
    [Module.Finite ℂ ((Poly n ⧸ I) ⧸ Ideal.span (Set.range z))] :
    (MvPolynomial.aeval (R := ℂ) z).Finite := by
  let : GradedAlgebra (OAI.PiExponentJets.W64.quotientSection I) := homogeneousQuotientGrading I hI
  exact graded_finite_of_parameter_quotient_finite
    (OAI.PiExponentJets.W64.quotientSection I) z hz

/-- Killing all parameters of a finite polynomial map leaves a finite
ground-field algebra. This uses the actual map and does not require
integrality certificates for individual generators. -/
theorem finite_ground_of_killed_finite_parameters
    {K : Type u} [Field K] {A Q : Type v} [CommRing A] [CommRing Q]
    [Algebra K A] [Algebra K Q] {s : ℕ} (z : Fin s → A)
    (hf : (MvPolynomial.aeval (R := K) z).Finite)
    (q : A →ₐ[K] Q) (hq : Function.Surjective q) (hz : ∀ i, q (z i) = 0) :
    Module.Finite K Q := by
  let ε : MvPolynomial (Fin s) K →ₐ[K] K := MvPolynomial.aeval (fun _ => (0 : K))
  let ι : K →ₐ[K] Q := Algebra.ofId K Q
  have he : q.comp (MvPolynomial.aeval (R := K) z) = ι.comp ε := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, hz, ε, ι, map_zero]
  have hh := (AlgHom.Finite.of_surjective q hq).comp hf
  rw [he] at hh
  have hι : (algebraMap K Q).Finite := AlgHom.Finite.of_comp_finite hh
  exact RingHom.finite_algebraMap.mp hι

/-- A finite normalization modulo one fixed degree-one coordinate lifts
to a finite map retaining that coordinate. The parameters are the
literal supplied lifts, so this applies with the original X0. -/
theorem graded_finite_lift_with_fixed_coordinate
    {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
    (G : ℕ → Submodule K A) [GradedAlgebra G]
    [∀ n, Module.Finite K (G n)]
    (t : A) (ht : t ∈ G 1) {s : ℕ} (z : Fin s → A) (hz : ∀ i, z i ∈ G 1)
    (hf : (MvPolynomial.aeval (R := K)
      (fun i => Ideal.Quotient.mk (Ideal.span {t}) (z i))).Finite) :
    (MvPolynomial.aeval (R := K) (Fin.cons t z)).Finite := by
  let Jt := Ideal.span ({t} : Set A)
  let w : Fin (s+1) → A := Fin.cons t z
  let J := Ideal.span (Set.range w)
  have hle : Jt ≤ J := Ideal.span_le.mpr (by
    intro a ha
    have hat : a = t := Set.mem_singleton_iff.mp ha
    subst a
    exact Ideal.subset_span ⟨0, rfl⟩)
  let q : (A ⧸ Jt) →ₐ[K] (A ⧸ J) := Ideal.Quotient.liftₐ Jt
    (Ideal.Quotient.mkₐ K J) (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha))
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨Ideal.Quotient.mk Jt b, rfl⟩
  have hqz (i : Fin s) : q (Ideal.Quotient.mk Jt (z i)) = 0 := by
    change Ideal.Quotient.mk J (z i) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span ⟨i.succ, rfl⟩)
  let : Module.Finite K (A ⧸ J) := finite_ground_of_killed_finite_parameters
    (fun i => Ideal.Quotient.mk Jt (z i)) hf q hq hqz
  apply graded_finite_of_parameter_quotient_finite G w
  intro i
  cases i using Fin.cases with
  | zero => exact ht
  | succ i => exact hz i

/-- The actual homogeneous coordinate quotient admits the fixed-coordinate
lift without any reducedness hypothesis on its infinity quotient. -/
theorem homogeneous_quotient_finite_lift_with_fixed_coordinate {n s : ℕ}
    (I : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (t : Poly n ⧸ I) (ht : t ∈ OAI.PiExponentJets.W64.quotientSection I 1)
    (z : Fin s → Poly n ⧸ I)
    (hz : ∀ i, z i ∈ OAI.PiExponentJets.W64.quotientSection I 1)
    (hf : RingHom.Finite (MvPolynomial.eval₂Hom (algebraMap ℂ _)
      (fun i => Ideal.Quotient.mk (Ideal.span {t}) (z i)))) :
    (MvPolynomial.aeval (R := ℂ) (Fin.cons t z)).Finite := by
  let : GradedAlgebra (OAI.PiExponentJets.W64.quotientSection I) := homogeneousQuotientGrading I hI
  exact graded_finite_lift_with_fixed_coordinate
    (OAI.PiExponentJets.W64.quotientSection I) t ht z hz hf

/-- Specializing the retained coordinate to one preserves finiteness
over the remaining polynomial parameters. -/
theorem finite_parameters_specialize_fixed_coordinate_one
    {K : Type u} [Field K] {A Q : Type v} [CommRing A] [CommRing Q]
    [Algebra K A] [Algebra K Q] (t : A) {s : ℕ} (z : Fin s → A)
    (hf : (MvPolynomial.aeval (R := K) (Fin.cons t z)).Finite)
    (q : A →ₐ[K] Q) (hq : Function.Surjective q) (ht : q t = 1) :
    (MvPolynomial.aeval (R := K) (fun i => q (z i))).Finite := by
  let ε : MvPolynomial (Fin (s+1)) K →ₐ[K] MvPolynomial (Fin s) K :=
    MvPolynomial.aeval (Fin.cons 1 MvPolynomial.X)
  let f := MvPolynomial.aeval (R := K) (fun i => q (z i))
  have he : q.comp (MvPolynomial.aeval (R := K) (Fin.cons t z)) = f.comp ε := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp [ε, f, ht]
    | succ i => simp [ε, f]
  have hh := (AlgHom.Finite.of_surjective q hq).comp hf
  rw [he] at hh
  exact AlgHom.Finite.of_comp_finite hh

/-- Finite parameters on a coordinate cut lift through its actual
surjection. The kernel condition identifies the retained coordinate;
it avoids changing the cut's nonreduced quotient structure. -/
theorem graded_finite_parameters_lift_through_coordinate_cut
    {K : Type u} [Field K] {A Q : Type v} [CommRing A] [CommRing Q]
    [Algebra K A] [Algebra K Q]
    (G : ℕ → Submodule K A) [GradedAlgebra G]
    [∀ n, Module.Finite K (G n)]
    (t : A) (ht : t ∈ G 1) {s : ℕ} (z : Fin s → A) (hz : ∀ i, z i ∈ G 1)
    (q : A →ₐ[K] Q) (hq : Function.Surjective q)
    (hker : RingHom.ker q.toRingHom ≤ Ideal.span {t})
    (hf : (MvPolynomial.aeval (R := K) (fun i => q (z i))).Finite) :
    (MvPolynomial.aeval (R := K) (Fin.cons t z)).Finite := by
  let w : Fin (s+1) → A := Fin.cons t z
  let J := Ideal.span (Set.range w)
  let p := Ideal.Quotient.mkₐ K J
  have hle : Ideal.span ({t} : Set A) ≤ J := Ideal.span_le.mpr (by
    intro a ha
    have hat : a = t := Set.mem_singleton_iff.mp ha
    subst a
    exact Ideal.subset_span ⟨0, rfl⟩)
  have hqp : RingHom.ker q.toRingHom ≤ RingHom.ker p.toRingHom := by
    change RingHom.ker q.toRingHom ≤ RingHom.ker (Ideal.Quotient.mk J)
    rw [Ideal.mk_ker]
    exact hker.trans hle
  let qbar := AlgHom.liftOfSurjective q hq p hqp
  have hqbar : Function.Surjective qbar :=
    AlgHom.liftOfSurjective_surjective q hq p hqp (Ideal.Quotient.mkₐ_surjective K J)
  have hkill (i : Fin s) : qbar (q (z i)) = 0 := by
    rw [AlgHom.liftOfSurjective_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i.succ, rfl⟩)
  let : Module.Finite K (A ⧸ J) := finite_ground_of_killed_finite_parameters
    (fun i => q (z i)) hf qbar hqbar hkill
  apply graded_finite_of_parameter_quotient_finite G w
  intro i
  cases i using Fin.cases with
  | zero => exact ht
  | succ i => exact hz i

end
end DistinctDistances.TrackA
