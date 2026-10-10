import DistinctDistances.TrackA.Compression
import DistinctDistances.TrackA.Intersections
import DistinctDistances.TrackA.CurveHilbertSupport
import DistinctDistances.TrackA.HypersurfaceOrderSupport
import DistinctDistances.TrackA.TangentHyperplaneSupport
import DistinctDistances.TrackA.MultiplicityIntegralitySupport
import DistinctDistances.TrackA.PolarChartSupport
import DistinctDistances.TrackA.ChartIdealSupport
import DistinctDistances.TrackA.PlaneEquationSupport
import DistinctDistances.TrackA.ProjectionSourceSupport
import DistinctDistances.TrackA.RadialFiberSupport
import DistinctDistances.TrackA.Requests
import DistinctDistances.TrackA.RetractionLengthAux
import DistinctDistances.TrackA.HypersurfaceFiberAux
import DistinctDistances.TrackA.PointProjectionAux

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- `poly:projection.hypersurface-order`, polynomial.tex:730–740,896–899.
The principal ideal equals the reduced variety ideal, so repeated factors are excluded. -/
theorem poly_hypersurface_order {n : ℕ} (V : AffineVariety n) (f : Poly n)
    (hf : f ≠ 0) (hV : V.ideal = Ideal.span {f}) (p : Point n) (r : ℕ) :
    OrderAtLeast f p r ↔ (r : ℚ) ≤ V.multiplicity p := by
  exact hypersurface_order_core V f hf hV p r

/-- `poly:projection.local-comparison`, polynomial.tex:844–874.
Grade lead: finite rank-one local algebra and Artin–Rees leading-coefficient comparison. -/
theorem poly_projection_local_comparison {n m : ℕ} (X : AffineVariety n)
    (hX : X.IsIrreducible) (φ : AffineProjection n m) (hfinite : FiniteAffineProjection φ X)
    (hbirational : φ.GenericallyFiniteOfDegree X 1) (p : Point n) (hp : p ∈ X.points)
    (hfiber : φ.fiber X (φ.apply p) = {p}) :
    X.multiplicity p ≤ (φ.image X).multiplicity (φ.apply p) := by
  have hy : φ.apply p ∈ (φ.image X).points := by
    intro F hF
    rw [← φ.eval_pullback]
    exact hp (φ.pullback F) hF
  have hd : X.localDimension p = (φ.image X).localDimension (φ.apply p) := by
    rw [AffineVariety.localDimension_eq_dimension X p hX hp,
      AffineVariety.localDimension_eq_dimension (φ.image X) (φ.apply p)
        (φ.image_irreducible X hX) hy,
      hyp_finite_image_dimension X hX φ hfinite]
  obtain ⟨c, hc⟩ := hyp_projection_localHilbert_bound X hX φ hfinite hbirational p
  exact hyp_multiplicity_le_of_shift X p (φ.image X) (φ.apply p) hd c hc

/-- `poly:projection.point-projective`, polynomial.tex:742–750,766–812.
Exact singular-center formula, with a genuine rank-one projection kernel. -/
theorem poly_projection_point_projective {n : ℕ} (X : ProjectiveVariety (n+1))
    (hX : X.IsIrreducible) (k : ℕ) (hk : 1 ≤ k) (hdim : X.dimension = k)
    (p : ProjectivePoint (n+1)) (φ : LinearProjection (n+1) n)
    (hsurjective : Function.Surjective φ) (hkernel : LinearMap.ker φ = p.submodule)
    (himage : (projectiveImage φ X).dimension = k) (r : ℕ)
    (hr : GenericallyFiniteProjectiveDegree φ X r) :
    (r : ℚ) * (projectiveImage φ X).degree = X.degree - X.multiplicity p := by
  exact PointProjection.arbitrary_projection_point X hX k hk hdim p φ hkernel himage r hr

/-- `poly:projection.radial`, polynomial.tex:742–750,762–763;
depth.tex:120–132; sparse-cones.tex:629–643. Affine consumer form. -/
theorem poly_projection_radial {n : ℕ} (X : AffineVariety n) (hX : X.IsIrreducible)
    (k : ℕ) (hk : 1 ≤ k) (hdim : X.dimension = k) (p : Point n)
    (himage : (radialImage p X).dimension = k) (r : ℕ)
    (hr : GenericallyFiniteRadialDegree p X r) :
    (r : ℚ) * (radialImage p X).degree = X.degree - X.multiplicity p := by
  have hactual := radial_actual_of_generic X p hr
  have hne := X.points_nonempty_of_isIrreducible hX
  have hIm := radial_projective_image X p hactual
  have hdegree := radial_generic_projective_degree X hX hdim p himage hr
  have hformula := poly_projection_point_projective (projectiveClosure X)
    (projectiveClosure_isIrreducible X hX) k hk
    ((projectiveClosure_dimension X hne).trans hdim) (affineEmbedding p)
    (radialLinearProjection p) (radialLinearProjection_surjective p)
    (radialLinearProjection_kernel p) (by rwa [hIm]) r hdegree
  rwa [hIm, projectiveClosure_degree, projectiveClosure_multiplicity] at hformula

/-- `poly:projection.order-test`, polynomial.tex:888–900.
Affine pullback of a projected hypersurface; the zero-dimensional case is included. -/
theorem poly_projection_order_test {n : ℕ} (X : AffineVariety n) (hX : X.IsIrreducible)
    (hproper : X.ideal ≠ ⊥) (S : Finset (Point n)) (hS : ∀ p ∈ S, p ∈ X.points)
    (x : Point n) (hx : x ∉ X.points) :
    ∃ f : Poly n, (f.totalDegree : ℚ) ≤ X.degree ∧ MvPolynomial.eval x f ≠ 0 ∧
      ∀ p ∈ S, ∀ r : ℕ, (r : ℚ) ≤ X.multiplicity p → OrderAtLeast f p r := by
  obtain ⟨φ, hfinite, hgeneric, hxout, hfibers⟩ :=
    hyp_affine_birational_projection X hX rfl
      (Nat.le_of_lt (proper_affine_dimension_lt X hX hproper)) S hS x hx
  obtain ⟨F, hF, hYideal, hFdegree⟩ :=
    hyp_affine_projection_equation X hX rfl φ hfinite
  let f : Poly n := φ.pullback F
  have hfdegree : f.totalDegree ≤ F.totalDegree := hyp_affine_pullback_degree φ F
  refine ⟨f, ?_, ?_, ?_⟩
  · calc
      (f.totalDegree : ℚ) ≤ F.totalDegree := by exact_mod_cast hfdegree
      _ ≤ X.degree := hFdegree
  · change MvPolynomial.aeval x (φ.pullback F) ≠ 0
    rw [φ.eval_pullback]
    intro hzero
    apply hxout
    have hle : (φ.image X).ideal ≤ RingHom.ker (MvPolynomial.aeval (φ.apply x)).toRingHom := by
      rw [hYideal]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hzero)
    exact hle
  · intro p hp r hr
    have hcompare := poly_projection_local_comparison X hX φ hfinite hgeneric p
      (hS p hp) (hfibers p hp)
    have horder : OrderAtLeast F (φ.apply p) r :=
      (poly_hypersurface_order (φ.image X) F hF hYideal (φ.apply p) r).mpr
        (hr.trans hcompare)
    exact hyp_affine_pullback_order φ F p r horder

/-- `poly:high-multiplicity`, polynomial.tex:877–902; depth.tex:112–118. -/
theorem poly_high_multiplicity {n : ℕ} (X : AffineVariety n) (hX : X.IsIrreducible)
    (hproper : X.ideal ≠ ⊥) (S : Finset (Point n))
    (hS : ∀ p ∈ S, p ∈ X.points ∧ X.degree / 2 < X.multiplicity p)
    (x : Point n) (hx : x ∉ X.points) :
    ∃ g : Poly n, g.totalDegree ≤ 2*(n+1) ∧
      (∀ p ∈ S, MvPolynomial.eval p g = 0) ∧ MvPolynomial.eval x g ≠ 0 := by
  by_cases hempty : S = ∅
  · subst S
    exact ⟨1, by simp, by simp, by simp⟩
  have hdegpos : 0 ≤ X.degree :=
    (by decide : (0 : ℚ) ≤ 1).trans (X.one_le_degree hX.ne_top)
  let r := Nat.floor (X.degree / 2) + 1
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hrabove : X.degree / 2 < (r : ℚ) := by
    simpa only [r, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (X.degree / 2)
  have hrbelow (p : Point n) (hp : p ∈ S) : (r : ℚ) ≤ X.multiplicity p := by
    obtain ⟨a, ha⟩ := multiplicity_eq_nat X p (hS p hp).1
    have hlt : Nat.floor (X.degree / 2) < a :=
      (Nat.floor_lt (by linarith : 0 ≤ X.degree / 2)).mpr (by
        rw [← ha]
        exact (hS p hp).2)
    rw [ha]
    exact_mod_cast (show r ≤ a by dsimp [r]; omega)
  obtain ⟨f, hfdegree, hfx, hforder⟩ :=
    poly_projection_order_test X hX hproper S (fun p hp => (hS p hp).1) x hx
  obtain ⟨g, hgdegree, hgzero, hgx⟩ := poly_compression S x f f.totalDegree r hr le_rfl
    (fun p hp => hforder p hp r (hrbelow p hp)) hfx
  have hEr : f.totalDegree ≤ 2*r := by
    have hcast : (f.totalDegree : ℚ) ≤ 2*(r : ℚ) := by linarith
    exact_mod_cast hcast
  have hbound : r*g.totalDegree ≤ r*(2*(n+1)) := by
    calc
      r*g.totalDegree ≤ (n+1)*f.totalDegree := hgdegree
      _ ≤ (n+1)*(2*r) := Nat.mul_le_mul_left (n+1) hEr
      _ = r*(2*(n+1)) := by ring
  refine ⟨g, ?_, hgzero, hgx⟩
  nlinarith

/-- `poly:tangent-projection.hyperplane`, polynomial.tex:917–922. -/
theorem poly_tangent_hyperplane {n : ℕ} (C X : AffineVariety n)
    (hC : C.IsIrreducible) (hdim : C.dimension = 1) (hCX : C.Subvariety X)
    (p z : Point n) (hp : p ∈ C.points) (hsmooth : X.IsSmoothAt p)
    (hz : z ∈ C.points) (htransverse : z-p ∉ X.tangentSpace p) :
    ∃ f : Poly n, f.totalDegree ≤ 1 ∧ MvPolynomial.eval z f ≠ 0 ∧
      localClass C p f ∈ carrierMaximalIdeal C p ^ 2 := by
  exact tangent_hyperplane_core C X hCX p z hp htransverse

/-- `poly:tangent-projection.local-length`, polynomial.tex:924–933.
Grade lead: reduced curve CM length and the Hilbert–Samuel leading coefficient. -/
theorem poly_curve_double_order_length {n : ℕ} (C : AffineVariety n)
    (hC : C.IsIrreducible) (hdim : C.dimension = 1) (p : Point n) (hp : p ∈ C.points)
    (f : Poly n) (hf : f ∉ C.ideal)
    (horder : localClass C p f ∈ carrierMaximalIdeal C p ^ 2) :
    ∃ length : ℕ, localLengthAt (C.ideal ⊔ Ideal.span {f}) p = (length : ℕ∞) ∧
      2 * C.multiplicity p ≤ (length : ℚ) := by
  exact curve_double_order_length_core C hC hdim p hp f hf horder

/-- `poly:tangent-projection`, polynomial.tex:904–938; sparse-cones.tex:629–643. -/
theorem poly_tangent_projection {n : ℕ} (C X : AffineVariety n)
    (hC : C.IsIrreducible) (hdim : C.dimension = 1) (hCX : C.Subvariety X)
    (p : Point n) (hp : p ∈ C.points) (hsmooth : X.IsSmoothAt p)
    (hz : ∃ z ∈ C.points, z-p ∉ X.tangentSpace p) :
    C.multiplicity p ≤ C.degree / 2 ∧
      ∀ r : ℕ, GenericallyFiniteRadialDegree p C r → (radialImage p C).dimension = 1 →
        C.degree / 2 ≤ (r : ℚ) * (radialImage p C).degree := by
  obtain ⟨z, hzpts, hztan⟩ := hz
  obtain ⟨f, hfdeg, hzf, hforder⟩ :=
    poly_tangent_hyperplane C X hC hdim hCX p z hp hsmooth hzpts hztan
  have hfideal : f ∉ C.ideal := by
    intro hfC
    have hzzero : MvPolynomial.eval z f = 0 := by
      have hz_aeval : MvPolynomial.aeval z f = 0 := hzpts f hfC
      rwa [MvPolynomial.aeval_eq_eval] at hz_aeval
    exact hzf hzzero
  obtain ⟨len1, hlen1eq, hlen1le⟩ :=
    poly_curve_double_order_length C hC hdim p hp f hfideal hforder
  obtain ⟨len2, hlen2eq, hlen2le⟩ :=
    fa_bezout_curve_length C hC hdim f hfideal p hp
  have hlen_eq : len1 = len2 := by
    have hext : (len1 : ℕ∞) = (len2 : ℕ∞) := by rw [← hlen1eq, hlen2eq]
    exact WithTop.coe_inj.mp hext
  subst hlen_eq
  have hdeg1 : (f.totalDegree : ℚ) ≤ 1 := by exact_mod_cast hfdeg
  have hdeg_nonneg : 0 ≤ C.degree := by
    have hprime : C.ideal.IsPrime := hC
    exact le_trans (by decide : (0 : ℚ) ≤ 1) (AffineVariety.one_le_degree C hprime.ne_top)
  have hmult_le : C.multiplicity p ≤ C.degree / 2 := by
    have h1 : 2 * C.multiplicity p ≤ (len1 : ℚ) := hlen1le
    have h2 : (len1 : ℚ) ≤ C.degree := by
      calc
        (len1 : ℚ) ≤ (f.totalDegree : ℚ) * C.degree := hlen2le
        _ ≤ 1 * C.degree := by
          apply mul_le_mul_of_nonneg_right hdeg1 hdeg_nonneg
        _ = C.degree := one_mul C.degree
    linarith
  refine ⟨hmult_le, ?_⟩
  intro r hr himage
  have hrad := poly_projection_radial C hC 1 le_rfl hdim p himage r hr
  rw [hrad]
  linarith

/-- `poly:polar.choice`, polynomial.tex:951–973.
The polar has no common nonunit divisor with the squarefree curve equation. -/
theorem poly_polar_choice (C : ProjectiveVariety 3) (hC : C.IsPure 1)
    (hne : C.points.Nonempty) :
    ∃ (f g : Poly 3) (weights : Fin 3 → ℂ), f ≠ 0 ∧ 1 ≤ f.totalDegree ∧
      f.IsHomogeneous f.totalDegree ∧ C.ideal = Ideal.span {f} ∧
      (f.totalDegree : ℚ) = C.degree ∧
      g = ∑ i, MvPolynomial.C (weights i) * MvPolynomial.pderiv i f ∧
      g.totalDegree ≤ f.totalDegree - 1 ∧
      (∀ d : Poly 3, d ∣ f → d ∣ g → IsUnit d) ∧
      ∀ p ∈ C.points, ∀ (i : Fin 3) (hi : p.rep i ≠ 0) (r : ℕ),
        (r : ℚ) ≤ C.multiplicity p →
        OrderAtLeast (chartPullback i g) (chartCoordinates i p) (r-1) := by
  obtain ⟨f, hf, hhom, hideal⟩ := request_plane_curve_equation C hC hne
  obtain ⟨hdegree, hdeg, hsquare⟩ := projective_equation_invariants C hne f hf hideal
  obtain ⟨w, hw⟩ := exists_coprime_firstPolar f hf hsquare
  refine ⟨f, firstPolar f w, w, hf, hdegree, hhom, hideal, hdeg, ?_,
    firstPolar_degree f w, hw, ?_⟩
  · change (∑ i, w i • MvPolynomial.pderiv i f) = _
    simp only [MvPolynomial.smul_eq_C_mul]
  · intro p hp i hi r hr
    obtain ⟨hchart0, hchartideal⟩ := principal_chart_equation C f hf hhom hideal i
    have horder : OrderAtLeast (chartPullback i f) (chartCoordinates i p) r :=
      (poly_hypersurface_order (C.affineChart i) (chartPullback i f) hchart0 hchartideal
        (chartCoordinates i p) r).mpr (by rwa [← C.multiplicity_chart p i hi])
    exact firstPolar_chart_order f f.totalDegree hhom w i (chartCoordinates i p) r horder

/-- `poly:polar`, polynomial.tex:940–987; secants.tex:397–413,440–485.
All projective high-multiplicity points, including infinity, appear in S. -/
theorem poly_polar (C : ProjectiveVariety 3) (hC : C.IsPure 1) :
    ∃ S : Finset (ProjectivePoint 3),
      (∀ p, p ∈ S ↔ 2 ≤ C.multiplicity p) ∧
      (∑ p ∈ S, C.multiplicity p * (C.multiplicity p - 1)) ≤ C.degree * (C.degree - 1) ∧
      (∑ p ∈ S, C.multiplicity p ^ 2) ≤ 2 * C.degree * (C.degree - 1) := by
  classical
  have hzero_off (p : ProjectivePoint 3) (hp : p ∉ C.points) : C.multiplicity p = 0 := by
    change (C.affineChart (chartIndex p)).multiplicity (chartCoordinates (chartIndex p) p) = 0
    apply AffineVariety.multiplicity_eq_zero_off
    intro h
    exact hp ((C.chart_mem_iff p (chartIndex p) (chartIndex_nonzero p)).mp h)
  by_cases hne : C.points.Nonempty
  swap
  · have hEmpty : C.points = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hI : C.ideal = ⊤ := by
      rw [← C.vanishingIdeal_points]
      simp [ProjectiveVariety.vanishingIdeal, ProjectiveVariety.nonzeroRepresentatives, hEmpty,
        MvPolynomial.vanishingIdeal_empty]
    have htopHom := C.isHomogeneous
    rw [hI] at htopHom
    have hdeg : C.degree = 0 := by
      change OAI.PiExponentJets.W22.actualMultiplicity C.ideal C.isHomogeneous C.dimension = 0
      rw [OAI.PiExponentJets.W22.actualMultiplicity_congr C.isHomogeneous htopHom hI,
        OAI.PiExponentJets.W22.actualMultiplicity_top htopHom]
    refine ⟨∅, ?_, ?_, ?_⟩
    · intro p
      have h0 := hzero_off p (by rw [hEmpty]; exact Set.notMem_empty p)
      simp [h0]
    · simp [hdeg]
    · simp [hdeg]
  obtain ⟨f, g, w, hf0, hfdeg1, hfhom, hideal, hdeg, hg, hgdeg, hcop, hgorder⟩ :=
    poly_polar_choice C hC hne
  set a := f.totalDegree with ha
  have hghom : g.IsHomogeneous (a - 1) := by
    rw [hg]
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    exact (hfhom.pderiv).C_mul _
  have hforder (p : ProjectivePoint 3) (hp : p ∈ C.points) (i : Fin 3) (hi : p.rep i ≠ 0)
      (r : ℕ) (hr : (r : ℚ) ≤ C.multiplicity p) :
      OrderAtLeast (chartPullback i f) (chartCoordinates i p) r := by
    obtain ⟨hchart0, hchartideal⟩ := principal_chart_equation C f hf0 hfhom hideal i
    exact (poly_hypersurface_order (C.affineChart i) (chartPullback i f) hchart0 hchartideal
      (chartCoordinates i p) r).mpr (by rwa [← C.multiplicity_chart p i hi])
  have hmem (p : ProjectivePoint 3) (h : 2 ≤ C.multiplicity p) : p ∈ C.points := by
    by_contra hp
    rw [hzero_off p hp] at h
    norm_num at h
  have hzeros (p : ProjectivePoint 3) (h : 2 ≤ C.multiplicity p) :
      p ∈ projectiveCommonZeros f g := by
    have hp := hmem p h
    refine ⟨?_, ?_⟩
    · have hrep := hp p.rep p.rep_nonzero (Projectivization.mk_rep p)
      have hfm : f ∈ C.ideal := by rw [hideal]; exact Ideal.subset_span rfl
      simpa only [MvPolynomial.aeval_eq_eval] using hrep f hfm
    · have hi : p.rep (chartIndex p) ≠ 0 := chartIndex_nonzero p
      have hord := hgorder p hp (chartIndex p) hi 2 (by exact_mod_cast h)
      have hpt : chartPullback (chartIndex p) g ∈ pointIdeal (chartCoordinates (chartIndex p) p) :=
        Ideal.pow_le_self (by norm_num) hord
      change chartPullback (chartIndex p) g ∈
        MvPolynomial.vanishingIdeal ℂ ({chartCoordinates (chartIndex p) p} : Set (Point 2)) at hpt
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hpt
      change MvPolynomial.eval _ (chartPullback (chartIndex p) g) = 0 at hpt
      rw [chartPullback_eval] at hpt
      have hins : Fin.insertNth (chartIndex p) 1 (chartCoordinates (chartIndex p) p) =
          (p.rep (chartIndex p))⁻¹ • p.rep := by
        funext j
        rcases Fin.eq_self_or_eq_succAbove (chartIndex p) j with hj | ⟨k, hk⟩
        · subst hj
          simp [hi]
        · subst hk
          simp [chartCoordinates, div_eq_mul_inv, mul_comm]
      rw [hins, homogeneous_eval_smul g hghom] at hpt
      exact (mul_eq_zero.mp hpt).resolve_left (pow_ne_zero _ (inv_ne_zero hi))
  have hfinZ := projectiveCommonZeros_finite f g hf0 a (a-1) hfhom hghom hcop
  have hfinS : {p : ProjectivePoint 3 | 2 ≤ C.multiplicity p}.Finite :=
    hfinZ.subset (fun p hp => hzeros p hp)
  let S := hfinS.toFinset
  have hSmem (p : ProjectivePoint 3) : p ∈ S ↔ 2 ≤ C.multiplicity p := hfinS.mem_toFinset
  have hmain : ∑ p ∈ S, C.multiplicity p * (C.multiplicity p - 1) ≤
      (a : ℚ) * ((a : ℚ) - 1) := by
    apply polar_budget_core C.multiplicity f g a hf0 hfdeg1 rfl hfhom hghom hgdeg hcop S
    intro p hpS
    have h2 := (hSmem p).mp hpS
    have hp := hmem p h2
    obtain ⟨m, hm⟩ := multiplicity_eq_nat (C.affineChart (chartIndex p))
      (chartCoordinates (chartIndex p) p)
      ((C.chart_mem_iff p (chartIndex p) (chartIndex_nonzero p)).mpr hp)
    have hmC : C.multiplicity p = m := hm
    refine ⟨m, ?_, hmC, ?_, ?_⟩
    · have h2' : (2 : ℚ) ≤ m := hmC ▸ h2
      exact_mod_cast h2'
    · exact hforder p hp _ (chartIndex_nonzero p) m (by rw [hmC])
    · exact hgorder p hp _ (chartIndex_nonzero p) m (by rw [hmC])
  rw [← hdeg]
  refine ⟨S, hSmem, hmain, ?_⟩
  calc ∑ p ∈ S, C.multiplicity p ^ 2 ≤
        ∑ p ∈ S, 2 * (C.multiplicity p * (C.multiplicity p - 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have h2 := (hSmem p).mp hp
        nlinarith
    _ = 2 * ∑ p ∈ S, C.multiplicity p * (C.multiplicity p - 1) := by rw [Finset.mul_sum]
    _ ≤ 2 * ((a : ℚ) * ((a : ℚ) - 1)) := by linarith
    _ = 2 * (a : ℚ) * ((a : ℚ) - 1) := by ring

end
end DistinctDistances.TrackA
