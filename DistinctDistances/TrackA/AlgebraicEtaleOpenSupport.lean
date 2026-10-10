import DistinctDistances.TrackA.AffineEtaleOpenSupport
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- Equal finite transcendence degrees make the actual function field
extension algebraic. Used for dimension-preserving radial projection. -/
theorem algebraic_of_equal_finite_trdeg (k K L : Type) [Field k]
    [CommRing K] [IsDomain K] [CommRing L] [IsDomain L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FaithfulSMul k K] [FaithfulSMul K L]
    (d : ℕ) (hK : Algebra.trdeg k K = d) (hL : Algebra.trdeg k L = d) :
    Algebra.IsAlgebraic K L := by
  apply trdeg_eq_zero_iff.mp
  have h := trdeg_add_eq k K (A := L)
  rw [hK, hL, add_comm] at h
  exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).mp
    (by simpa using h)

/-- Generic etaleness needs algebraicity, without requiring that the
unshrunk source be finite over the base. -/
theorem algebraic_domain_generic_etale (R B : Type*) [CommRing R] [IsDomain R]
    [CharZero R] [CommRing B] [IsDomain B] [Algebra R B]
    [Algebra.IsAlgebraic R B] [Module.IsTorsionFree R B] :
    Algebra.IsEtaleAt R (⊥ : Ideal B) := by
  let L := Localization.AtPrime (⊥ : Ideal B)
  haveI : IsFractionRing B L := by
    simpa [Ideal.primeCompl_bot] using
      Localization.isLocalization (M := (⊥ : Ideal B).primeCompl)
  letI : Field L := IsFractionRing.toField B
  haveI : FaithfulSMul R L := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq R B L]
    exact (IsFractionRing.injective B L).comp (FaithfulSMul.algebraMap_injective R B)
  letI := FractionRing.liftAlgebra R L
  haveI : Algebra.IsAlgebraic R L :=
    (IsFractionRing.isAlgebraic_iff' R B L).mp inferInstance
  haveI : Algebra.IsAlgebraic (FractionRing R) L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := FractionRing R)).mp inferInstance
  haveI : Algebra.FormallyEtale (FractionRing R) L :=
    Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale R (FractionRing R) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  exact Algebra.FormallyEtale.comp R (FractionRing R) L

/-- A finite-type algebraic domain map in characteristic zero is etale
over a nonzero principal base open. The source map remains unchanged. -/
theorem algebraic_domain_etale_base_open (R B : Type*) [CommRing R] [IsDomain R]
    [CharZero R] [IsNoetherianRing R] [CommRing B] [IsDomain B] [Algebra R B]
    [Algebra.FiniteType R B] [Algebra.IsAlgebraic R B] [Module.IsTorsionFree R B] :
    ∃ g : R, g ≠ 0 ∧ Algebra.Etale R (Localization.Away (algebraMap R B g)) := by
  haveI : Algebra.FinitePresentation R B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.IsEtaleAt R (⊥ : Ideal B) := algebraic_domain_generic_etale R B
  obtain ⟨b, hb, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal B)
  have hb0 : b ≠ 0 := by simpa only [Ideal.mem_bot] using hb
  obtain ⟨g, hg, c, hgc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) b).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hb0)
  refine ⟨g, hg, Algebra.basicOpen_subset_etaleLocus_iff_etale.mp ?_⟩
  have hbe : (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ Algebra.etaleLocus R B :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr he
  rw [hgc]
  intro q hq
  exact hbe ((PrimeSpectrum.basicOpen_mul_le_left b c) hq)

/-- A common integral multiplier for the original finite generators
makes their base localization module-finite. -/
theorem finiteType_finite_away_of_integral_generators (R B : Type*)
    [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (s : Finset B) (hs : Algebra.adjoin R (s : Set B) = ⊤)
    (c : R) (hc : ∀ b ∈ s, IsIntegral R (c • b)) :
    Module.Finite (Localization (Submonoid.powers c))
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers c))) := by
  let Rc := Localization (Submonoid.powers c)
  let Bc := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers c))
  haveI : IsLocalization.Away (algebraMap R B c) Bc := by
    change IsLocalization (Submonoid.powers (algebraMap R B c)) Bc
    rw [show Submonoid.powers (algebraMap R B c) =
      Algebra.algebraMapSubmonoid B (Submonoid.powers c) by
      simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]]
    infer_instance
  let ci : Rc := IsLocalization.Away.invSelf c
  have hci : algebraMap R Rc c * ci = 1 := IsLocalization.Away.mul_invSelf c
  have hgen (b : B) (hb : b ∈ s) : IsIntegral Rc (algebraMap B Bc b) := by
    have hi : IsIntegral Rc (algebraMap B Bc (c • b)) :=
      ((hc b hb).map (IsScalarTower.toAlgHom R B Bc)).tower_top
    have hi' := hi.smul ci
    have heq : ci • algebraMap B Bc (c • b) = algebraMap B Bc b := by
      simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R B Bc,
        IsScalarTower.algebraMap_apply R Rc Bc]
      rw [← mul_assoc, ← map_mul, mul_comm ci, hci, map_one, one_mul]
    rwa [heq] at hi'
  have hall (b : B) : IsIntegral Rc (algebraMap B Bc b) := by
    have hb : b ∈ Algebra.adjoin R (s : Set B) := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem b hb => exact hgen b hb
    | algebraMap r =>
        rw [← IsScalarTower.algebraMap_apply R B Bc, IsScalarTower.algebraMap_apply R Rc Bc]
        exact isIntegral_algebraMap
    | add a b _ _ ha hb => simpa only [map_add] using ha.add hb
    | mul a b _ _ ha hb => simpa only [map_mul] using ha.mul hb
  haveI : Algebra.IsIntegral Rc Bc := by
    constructor
    intro b
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (algebraMap R B c) b
    have hi := (hall a).smul (ci ^ n)
    have heq : ci ^ n • algebraMap B Bc a = b := by
      rw [← ha, Algebra.smul_def, mul_comm, mul_assoc]
      conv_rhs => rw [← mul_one b]
      congr 1
      rw [← IsScalarTower.algebraMap_apply R B Bc, IsScalarTower.algebraMap_apply R Rc Bc,
        ← map_pow, ← map_mul, ← mul_pow, hci, one_pow, map_one]
    rwa [heq] at hi
  haveI : Algebra.FinitePresentation B Bc :=
    IsLocalization.Away.finitePresentation (algebraMap R B c)
  haveI : Algebra.FiniteType R Bc := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R B) (inferInstance : Algebra.FiniteType B Bc)
  haveI : Algebra.FiniteType Rc Bc := Algebra.FiniteType.of_restrictScalars_finiteType R Rc Bc
  exact Algebra.IsIntegral.finite

/-- The same principal base open makes an algebraic finite-type domain
map both module-finite and etale, including maps that are not finite
before shrinking. This is the algebraic input for a radial target chart. -/
theorem algebraic_finiteType_finite_etale_base_open (R B : Type*)
    [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B]
    [Algebra.IsAlgebraic R B] [Module.IsTorsionFree R B] :
    ∃ g : R, g ≠ 0 ∧
      Module.Finite (Localization (Submonoid.powers g))
        (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))) ∧
      Algebra.Etale (Localization (Submonoid.powers g))
        (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))) := by
  obtain ⟨e, he, hetale⟩ := algebraic_domain_etale_base_open R B
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R B)
  obtain ⟨c, hc, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples R s
  let g := e * c
  let Rg := Localization (Submonoid.powers g)
  let Bg := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))
  haveI : IsLocalization.Away (algebraMap R B g) Bg := by
    change IsLocalization (Submonoid.powers (algebraMap R B g)) Bg
    rw [show Submonoid.powers (algebraMap R B g) =
      Algebra.algebraMapSubmonoid B (Submonoid.powers g) by
      simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]]
    infer_instance
  have hfinite : Module.Finite Rg Bg :=
    finiteType_finite_away_of_integral_generators R B s hs g (by
      intro b hb
      simpa only [g, mul_smul] using (hint b hb).smul e)
  haveI : Algebra.FinitePresentation R B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hgEtale : Algebra.Etale R (Localization.Away (algebraMap R B g)) := by
    apply Algebra.basicOpen_subset_etaleLocus_iff_etale.mp
    have heopen : (PrimeSpectrum.basicOpen (algebraMap R B e) : Set (PrimeSpectrum B)) ⊆
        Algebra.etaleLocus R B := Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hetale
    intro q hq
    apply heopen
    change algebraMap R B e ∉ q.asIdeal
    have hq' : algebraMap R B g ∉ q.asIdeal := hq
    dsimp only [g] at hq'
    rw [map_mul] at hq'
    exact fun heq => hq' (q.asIdeal.mul_mem_right _ heq)
  haveI : Algebra.Etale R (Localization.Away (algebraMap R B g)) := hgEtale
  haveI : Algebra.Etale R Bg := Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R B g))
      (Localization.Away (algebraMap R B g)) Bg).restrictScalars R)
  haveI : Algebra.Etale R Rg := Algebra.Etale.of_isLocalizationAway g
  exact ⟨g, mul_ne_zero he hc, hfinite, Algebra.Etale.of_restrictScalars R Rg Bg⟩

end
end DistinctDistances.TrackA
