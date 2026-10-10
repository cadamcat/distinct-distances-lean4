import DistinctDistances.TrackA.LocalHilbertCarrierSupport
import DistinctDistances.OAIInterface.LocalHilbertSerre

/-!
Local intersection length uses exactly OAI's ambient polynomial localization.
Hilbert–Samuel multiplicity at a point is a different invariant from the
ordinary local quotient length, which is infinite on positive-dimensional
carriers. The sequence below retains extended lengths until a polynomial
with finite natural values is supplied by the existence theorem.
-/

namespace DistinctDistances

noncomputable section

namespace AffineVariety

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency.types false in
/-- Existence of the cumulative Hilbert–Samuel polynomial, including zero off `V`.
This geometric bridge is new work, not an OAI theorem claimed as available. -/
theorem localHilbert_eventually_polynomial (V : AffineVariety n) (x : Point n) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ N : ℕ, ∀ t ≥ N,
      ∃ a : ℕ, V.localHilbert x t = (a : ℕ∞) ∧ P.eval (t : ℚ) = (a : ℚ) := by
  classical
  by_cases hx : x ∈ V.points
  · letI := TrackA.carrierLocalRing_noetherian V x
    letI := TrackA.carrierMaximalIdeal_isMaximal V x hx
    obtain ⟨P, hP⟩ := OAI.Lech.IdealGraded.eventuallyPolynomial_length
      (R := TrackA.CarrierLocalRing V x) (TrackA.carrierMaximalIdeal V x)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hP
    let Q : Polynomial ℚ := P.comp (Polynomial.X + Polynomial.C 1)
    have hQ (t : ℕ) (ht : N ≤ t) :
        Q.eval (t : ℚ) = ((V.localHilbert x t).toNat : ℚ) := by
      calc
        Q.eval (t : ℚ) = P.eval ((t+1 : ℕ) : ℚ) := by simp [Q]
        _ = ((Module.length (TrackA.CarrierLocalRing V x)
            (TrackA.CarrierLocalRing V x ⧸ TrackA.carrierMaximalIdeal V x^(t+1))).toNat : ℚ) :=
          (hN (t+1) (by omega)).symm
        _ = ((V.localHilbert x t).toNat : ℚ) := by
          rw [TrackA.curve_localHilbert_carrier]
    refine ⟨Q, TrackA.localHilbert_polynomial_degree_le V x Q
      (Filter.eventually_atTop.2 ⟨N, hQ⟩), N, ?_⟩
    intro t ht
    obtain ⟨a, ha, _⟩ := TrackA.localHilbert_finite_value V x t
    refine ⟨a, ha, ?_⟩
    simpa only [ha, ENat.toNat_natCast] using hQ t ht
  · refine ⟨0, by simp, 0, ?_⟩
    intro t _
    exact ⟨0, TrackA.localHilbert_zero_off V x hx t, by simp⟩

noncomputable def localHilbertPolynomial (V : AffineVariety n) (x : Point n) : Polynomial ℚ :=
  (localHilbert_eventually_polynomial V x).choose

/-- Local dimension; for a mixed-dimensional union this need not be `V.dimension`. -/
noncomputable def localDimension (V : AffineVariety n) (x : Point n) : ℕ :=
  (V.localHilbertPolynomial x).natDegree

/-- Hilbert–Samuel multiplicity, not a quotient length. -/
noncomputable def multiplicity (V : AffineVariety n) (x : Point n) : ℚ :=
  (V.localDimension x).factorial * (V.localHilbertPolynomial x).coeff (V.localDimension x)

theorem multiplicity_pos (V : AffineVariety n) (x : Point n) (hx : x ∈ V) :
    0 < V.multiplicity x := by
  classical
  have hxvan : ∀ f ∈ V.ideal, MvPolynomial.aeval x f = 0 := by
    change x ∈ MvPolynomial.zeroLocus ℂ V.ideal at hx
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    intro f hf
    simpa [MvPolynomial.aeval_eq_eval] using hx f hf
  have hVle : V.ideal ≤ pointIdeal x := by
    intro f hf
    change f ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n))
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).2 (hxvan f hf)
  have hlength_pos (t : ℕ) : 0 < V.localHilbert x t := by
    have hpow : pointIdeal x ^ (t + 1) ≤ pointIdeal x :=
      Ideal.pow_le_self (by omega)
    have hsum : V.ideal ⊔ pointIdeal x ^ (t + 1) ≤ pointIdeal x := sup_le hVle hpow
    have hlocal_le : localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x ≤
        (pointIdeal x).map (algebraMap (Poly n) (PointLocalRing x)) :=
      Ideal.map_mono hsum
    have hmax : ((pointIdeal x).map
        (algebraMap (Poly n) (PointLocalRing x))).IsMaximal := by
      infer_instance
    have hlocal_ne : localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x ≠ ⊤ := by
      intro htop
      have hMtop : (pointIdeal x).map (algebraMap (Poly n) (PointLocalRing x)) = ⊤ := by
        apply top_unique
        simpa [htop] using hlocal_le
      exact hmax.ne_top hMtop
    have hquot : Nontrivial
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
      Ideal.Quotient.nontrivial_iff.mpr hlocal_ne
    change 0 < Module.length (PointLocalRing x)
      (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
    exact Module.length_pos_iff.mpr hquot
  let P : Polynomial ℚ := V.localHilbertPolynomial x
  obtain ⟨N, hN⟩ := (V.localHilbert_eventually_polynomial x).choose_spec.2
  have hPeval_pos (t : ℕ) (ht : N ≤ t) : 0 < P.eval (t : ℚ) := by
    obtain ⟨a, ha, heval⟩ := hN t ht
    have ha_pos : 0 < a := by
      have hpos : (0 : ℕ∞) < (a : ℕ∞) := by
        rw [← ha]
        exact hlength_pos t
      exact_mod_cast hpos
    have heval' : P.eval (t : ℚ) = (a : ℚ) := by
      simpa [P, AffineVariety.localHilbertPolynomial] using heval
    rw [heval']
    exact_mod_cast ha_pos
  have hlead_pos : 0 < P.leadingCoeff := by
    by_cases hdeg0 : P.natDegree = 0
    · have hconst := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
      have hpos := hPeval_pos N le_rfl
      rw [hconst] at hpos ⊢
      simpa [Polynomial.leadingCoeff] using hpos
    · have hdeg : 0 < P.degree :=
        Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg0)
      by_contra hnot
      have hnonpos : P.leadingCoeff ≤ 0 := le_of_not_gt hnot
      have hbot := P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hnonpos
      have hneg : ∀ᶠ t : ℚ in Filter.atTop, P.eval t < 0 :=
        hbot.eventually_lt_atBot 0
      have hnegNat : ∀ᶠ t : ℕ in Filter.atTop, P.eval (t : ℚ) < 0 :=
        tendsto_natCast_atTop_atTop.eventually hneg
      have hfalse : ∀ᶠ t : ℕ in Filter.atTop, False :=
        (Filter.eventually_atTop.mpr ⟨N, fun t ht => hPeval_pos t ht⟩).and hnegNat |>.mono
          (fun _ ⟨hpos, hneg⟩ => (not_lt_of_ge hpos.le) hneg)
      obtain ⟨t, ht⟩ := hfalse.exists
      exact ht
  have hcoeff_pos : 0 < P.coeff P.natDegree := by
    change 0 < P.coeff P.natDegree at hlead_pos
    exact hlead_pos
  have hfactorial_pos : (0 : ℚ) < (P.natDegree.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos P.natDegree
  change 0 < (P.natDegree.factorial : ℚ) * P.coeff P.natDegree
  exact mul_pos hfactorial_pos hcoeff_pos

theorem multiplicity_eq_zero_off (V : AffineVariety n) (x : Point n) (hx : x ∉ V) :
    V.multiplicity x = 0 := by
  classical
  have hx' : x ∉ V.points := hx
  have hnotforall : ¬ ∀ f, f ∈ V.ideal → MvPolynomial.aeval x f = 0 := by
    simpa [AffineVariety.points, MvPolynomial.mem_zeroLocus_iff] using hx'
  push Not at hnotforall
  obtain ⟨f, hf, hfx⟩ := hnotforall
  have hfnot : f ∉ pointIdeal x := by
    intro h
    change f ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n)) at h
    exact hfx ((MvPolynomial.mem_vanishingIdeal_singleton_iff x f).1 h)
  have hlocal_top (t : ℕ) :
      localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t+1)) x = ⊤ := by
    exact Ideal.eq_top_of_isUnit_mem
      (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t+1)) x)
      (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hf))
      ((IsLocalization.AtPrime.isUnit_to_map_iff (PointLocalRing x) (pointIdeal x) f).2 hfnot)
  have hlocal_zero (t : ℕ) : V.localHilbert x t = 0 := by
    unfold localHilbert localLengthAt
    rw [hlocal_top]
    simp
  have hpoly : V.localHilbertPolynomial x = 0 := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    obtain ⟨N, hN⟩ := (V.localHilbert_eventually_polynomial x).choose_spec.2
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun t ht => hN t ht⟩] with t ht
    obtain ⟨a, ha, heval⟩ := ht
    rw [hlocal_zero t] at ha
    have hcast : (a : ℚ) = 0 := by exact_mod_cast ha.symm
    have heval' : (V.localHilbertPolynomial x).eval (t : ℚ) = (a : ℚ) := by
      simpa [AffineVariety.localHilbertPolynomial] using heval
    simpa using heval'.trans hcast
  simp [multiplicity, localDimension, hpoly]

end AffineVariety

/-- Direct OAI reuse for an isolated component of a bounded-degree system. -/
theorem isolatedPoint_length_le {n : ℕ} {J : Type*}
    (f : J → Poly n) (D : ℕ) (hdegree : ∀ j, (f j).totalDegree ≤ D)
    (x : Point n) (hminimal : pointIdeal x ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (hheight : (pointIdeal x).height = (n : ℕ∞)) :
    localLengthAt (Ideal.span (Set.range f)) x ≤ ((D^n : ℕ) : ℕ∞) :=
  OAI.PiExponent.localIsolatedBezout ℂ n f D n hdegree (pointIdeal x) hminimal hheight le_rfl

open scoped BigOperators

/-- Algebraic first derivative at a complex point. -/
noncomputable def differential {n : ℕ} (f : Poly n) (x : Point n) : Point n →ₗ[ℂ] ℂ :=
  ∑ i : Fin n, (MvPolynomial.aeval x (MvPolynomial.pderiv i f)) • LinearMap.proj i

def AffineVariety.tangentSpace {n : ℕ} (V : AffineVariety n) (x : Point n) :
    Submodule ℂ (Point n) :=
  ⨅ f : V.ideal, LinearMap.ker (differential f.val x)

def AffineVariety.IsSmoothAt {n : ℕ} (V : AffineVariety n) (x : Point n) : Prop :=
  x ∈ V ∧ Module.finrank ℂ (V.tangentSpace x) = V.localDimension x

/-- Dehomogenization in the chart `X_i = 1`. -/
def chartPullback {n : ℕ} (i : Fin (n+1)) : Poly (n+1) →ₐ[ℂ] Poly n :=
  MvPolynomial.aeval (Fin.insertNth i (MvPolynomial.C 1) MvPolynomial.X)

def ProjectiveVariety.affineChart {n : ℕ} (V : ProjectiveVariety (n+1))
    (i : Fin (n+1)) : AffineVariety n :=
  AffineVariety.ofIdeal (V.ideal.map (chartPullback i).toRingHom)

def chartCoordinates {n : ℕ} (i : Fin (n+1)) (p : ProjectivePoint (n+1)) : Point n :=
  fun j => p.rep (i.succAbove j) / p.rep i

theorem exists_nonzero_coordinate {n : ℕ} (p : ProjectivePoint n) :
    ∃ i : Fin n, p.rep i ≠ 0 := by
  by_contra h
  apply p.rep_nonzero
  funext i
  exact not_not.mp (fun hi => h ⟨i, hi⟩)

def chartIndex {n : ℕ} (p : ProjectivePoint n) : Fin n :=
  (exists_nonzero_coordinate p).choose

theorem chartIndex_nonzero {n : ℕ} (p : ProjectivePoint n) : p.rep (chartIndex p) ≠ 0 :=
  (exists_nonzero_coordinate p).choose_spec

/-- Projective point multiplicity is computed in an actual affine chart. -/
def ProjectiveVariety.multiplicity {n : ℕ} (V : ProjectiveVariety (n+1))
    (p : ProjectivePoint (n+1)) : ℚ :=
  (V.affineChart (chartIndex p)).multiplicity (chartCoordinates (chartIndex p) p)

theorem ProjectiveVariety.chart_mem_iff {n : ℕ} (V : ProjectiveVariety (n+1))
    (p : ProjectivePoint (n+1)) (i : Fin (n+1)) (hi : p.rep i ≠ 0) :
    chartCoordinates i p ∈ V.affineChart i ↔ p ∈ V := by
  let q : Point (n+1) := Fin.insertNth i 1 (chartCoordinates i p)
  have hq : q ≠ 0 := by
    intro h
    have hzero := congrFun h i
    simpa [q] using hzero
  have hscale : q = (p.rep i)⁻¹ • p.rep := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with hij | ⟨k, hk⟩
    · subst j
      simp [q, hi]
    · subst j
      simp [q, chartCoordinates, div_eq_mul_inv, mul_comm]
  have hproj : Projectivization.mk ℂ q hq = p := by
    rw [← Projectivization.mk_rep p]
    exact (Projectivization.mk_eq_mk_iff' ℂ q p.rep hq p.rep_nonzero).2
      ⟨(p.rep i)⁻¹, hscale.symm⟩
  have hchart : chartCoordinates i p ∈ V.affineChart i ↔ q ∈ V.affineCone.points := by
    change chartCoordinates i p ∈
      (AffineVariety.ofIdeal (V.ideal.map (chartPullback i).toRingHom)).points ↔ _
    rw [AffineVariety.points_ofIdeal]
    calc
      chartCoordinates i p ∈
          MvPolynomial.zeroLocus ℂ (V.ideal.map (chartPullback i).toRingHom) ↔
          V.ideal.map (chartPullback i).toRingHom ≤
            RingHom.ker (MvPolynomial.aeval (chartCoordinates i p)).toRingHom := by
        change (∀ f ∈ V.ideal.map (chartPullback i).toRingHom,
            MvPolynomial.aeval (chartCoordinates i p) f = 0) ↔
          ∀ f, f ∈ V.ideal.map (chartPullback i).toRingHom →
            (MvPolynomial.aeval (chartCoordinates i p)).toRingHom f = 0
        exact Iff.rfl
      _ ↔ V.ideal ≤ Ideal.comap (chartPullback i).toRingHom
          (RingHom.ker (MvPolynomial.aeval (chartCoordinates i p)).toRingHom) :=
        Ideal.map_le_iff_le_comap
      _ ↔ q ∈ V.affineCone.points := by
        simp only [SetLike.le_def, Ideal.mem_comap, RingHom.mem_ker,
          AffineVariety.points, ProjectiveVariety.affineCone,
          MvPolynomial.mem_zeroLocus_iff]
        have heval (f : Poly (n+1)) :
            MvPolynomial.aeval (chartCoordinates i p) (chartPullback i f) =
              MvPolynomial.aeval q f := by
          rw [chartPullback, MvPolynomial.comp_aeval_apply]
          apply congrArg (fun z : Point (n+1) => MvPolynomial.eval z f)
          funext j
          rcases Fin.eq_self_or_eq_succAbove i j with hij | ⟨k, hk⟩
          · subst j
            simp [q]
          · subst j
            simp [q]
        constructor
        · intro h f hf
          rw [← heval f]
          exact h (x := f) hf
        · intro h f hf
          change MvPolynomial.aeval (chartCoordinates i p) (chartPullback i f) = 0
          rw [heval f]
          exact h f hf
  constructor
  · intro hx
    have hqV := hchart.mp hx
    have hpq : Projectivization.mk ℂ q hq ∈ V :=
      (ProjectiveVariety.mem_points_mk_iff V q hq).2 hqV
    rw [hproj] at hpq
    exact hpq
  · intro hp
    have hpq : Projectivization.mk ℂ q hq ∈ V := hproj.symm ▸ hp
    exact hchart.mpr ((ProjectiveVariety.mem_points_mk_iff V q hq).mp hpq)

end

end DistinctDistances
