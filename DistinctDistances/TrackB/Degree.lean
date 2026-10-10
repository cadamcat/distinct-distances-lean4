import DistinctDistances.TrackB.MixedHilbert
import DistinctDistances.TrackB.TangentLineSupport
import DistinctDistances.TrackB.ParameterImageSupport
import DistinctDistances.TrackB.IncidenceDensity
import DistinctDistances.TrackB.RulingPolynomialImages
import DistinctDistances.TrackB.NullFieldSupport
import DistinctDistances.TrackB.NullProjectiveSupport
import DistinctDistances.TrackB.NullConeRigidity
import DistinctDistances.TrackB.FlatEndpointSupport
import DistinctDistances.TrackB.ParameterBaseGeometry
import DistinctDistances.TrackB.MixedDegreeRequests
import DistinctDistances.TrackB.PencilPolynomialOpen
import DistinctDistances.TrackB.ParameterDifferentialSupport
import DistinctDistances.TrackB.RulingMapsAux
import DistinctDistances.TrackB.BoundaryParameterAux
import DistinctDistances.TrackB.TangentQuotientSupport
import DistinctDistances.TrackB.RulingTangentSupport
import DistinctDistances.TrackB.RulingGoodOpen
import DistinctDistances.TrackB.PointIntegralSupport
import DistinctDistances.TrackB.PointIntegralAux
import DistinctDistances.TrackB.TripleRankParts
import DistinctDistances.TrackB.TripleRankRoute

namespace DistinctDistances.TrackB

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LinearMap (BilinForm)

def pointParameterFiber {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) (z : Point (skewDim e)) :
    ProjectiveVariety (e + e) :=
  ProjectiveVariety.closure {p | p ∈ parameterClosure C Γ H ∧ z ∈ evaluationFlat C p}

def HasGenericPointFiberDegree {e : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (d : ℚ) : Prop :=
  ∃ g : Poly (skewDim e), g ∉ V.ideal ∧ ∀ z ∈ workingPoints V H,
    MvPolynomial.aeval z g ≠ 0 → (pointParameterFiber C Γ H z).degree = d

def rulingTripleImage {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    Set (ProjectivePoint ((e * (e + e)) * (skewDim e + 1))) :=
  {x | ∃ z v, joinPoints z v ∈ rulingPoints Γ H ∧ ∃ hv : v ≠ 0,
    x = segrePoint (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv))
      (affineEmbedding z)}

abbrev TangentQuotient {e : ℕ} (p : ProjectivePoint (e + e)) :=
  Point e ⧸ Submodule.span ℂ {firstPoint p.rep}

/-- The actual image of the projective tangent in the paper's (alpha,beta) coordinates. -/
def parameterTangent {e : ℕ} (C : SkewCoordinates e) (Y : ProjectiveVariety (e + e))
    (p : ProjectivePoint (e + e)) (z0 : Point (skewDim e)) :
    Submodule ℂ (TangentQuotient p × Module.Dual ℂ (TangentQuotient p)) :=
  Submodule.span ℂ {x | ∃ dv : Point e, ∃ dy : Module.Dual ℂ (Point e),
    joinPoints dv (pointOfCovector dy) ∈ Y.affineCone.tangentSpace p.rep ∧
    x.1 = (Submodule.span ℂ {firstPoint p.rep}).mkQ dv ∧
    ∀ w : Point e, x.2 ((Submodule.span ℂ {firstPoint p.rep}).mkQ w) =
      dy w - (C.decode z0).val dv w}

/-- The paper's span of quotient coordinates is the image of one actual linear
map on the cone tangent. This supplies rank and lifting statements for B22. -/
theorem parameterTangent_eq_map {e : ℕ} (C : SkewCoordinates e)
    (Y : ProjectiveVariety (e + e)) (hQ : Y.points ⊆ parameterQuadric e)
    (p : ProjectivePoint (e + e)) (hpY : p ∈ Y.points)
    (z0 : Point (skewDim e)) (hz0 : z0 ∈ evaluationFlat C p) :
    parameterTangent C Y p z0 =
      (Y.affineCone.tangentSpace p.rep).map (tangentCoordinateLinear C p z0) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨dv, dy, hu, hx, hbeta⟩
    let u := joinPoints dv (pointOfCovector dy)
    have hfirst : firstPoint u = dv := by ext i; simp [u, firstPoint, joinPoints]
    have hsecond : covectorOfPoint (secondPoint u) = dy := by
      have hs : secondPoint u = pointOfCovector dy := by
        funext i
        exact Fin.addCases_right (m := e) (n := e) (motive := fun _ => ℂ)
          (left := dv) (right := pointOfCovector dy) i
      rw [hs, covector_point_inverse]
    refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
    apply Prod.ext
    · rw [tangentCoordinateLinear_first, hfirst]
      exact hx.symm
    · apply LinearMap.ext
      intro q
      obtain ⟨w, rfl⟩ := (Submodule.span ℂ {firstPoint p.rep}).mkQ_surjective q
      rw [tangentCoordinateLinear_second C p z0 u
        (parameter_quadric_tangent_annihilates C Y hQ p hpY z0 hz0 u hu) w,
        hfirst, hsecond]
      exact (hbeta w).symm
  · rintro x ⟨u, hu, rfl⟩
    apply Submodule.subset_span
    refine ⟨firstPoint u, covectorOfPoint (secondPoint u), ?_,
      tangentCoordinateLinear_first C p z0 u, ?_⟩
    · rwa [point_covector_inverse, joinPoints_eta]
    · exact tangentCoordinateLinear_second C p z0 u
        (parameter_quadric_tangent_annihilates C Y hQ p hpY z0 hz0 u hu)

/-- B21's coordinate kernel before projective quotienting. -/
theorem tangent_coordinate_kernel {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (z0 : Point (skewDim e)) (hz0 : z0 ∈ evaluationFlat C p)
    (dv : Point e) (dy : Module.Dual ℂ (Point e)) :
    ((Submodule.span ℂ {firstPoint p.rep}).mkQ dv = 0 ∧
      ∀ w, dy w - (C.decode z0).val dv w = 0) ↔
      ∃ t : ℂ, dv = t • firstPoint p.rep ∧ dy = t • covectorOfPoint (secondPoint p.rep) := by
  let S := Submodule.span ℂ {firstPoint p.rep}
  let D := (C.decode z0).val
  let y := covectorOfPoint (secondPoint p.rep)
  have heval : D (firstPoint p.rep) = y := hz0
  constructor
  · rintro ⟨hq, hdiff⟩
    have hmemKer : dv ∈ LinearMap.ker (S.mkQ) := LinearMap.mem_ker.mpr hq
    have hmem : dv ∈ S := by simpa [S, Submodule.ker_mkQ] using hmemKer
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨t, ht.symm, ?_⟩
    apply LinearMap.ext
    intro w
    calc
      dy w = D dv w := sub_eq_zero.mp (hdiff w)
      _ = D (t • firstPoint p.rep) w := by rw [ht.symm]
      _ = t • y w := by
        rw [LinearMap.map_smul, LinearMap.smul_apply, heval]
  · rintro ⟨t, rfl, rfl⟩
    constructor
    · have hmem : t • firstPoint p.rep ∈ S :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have hmemKer : t • firstPoint p.rep ∈ LinearMap.ker (S.mkQ) :=
        (Submodule.ker_mkQ S).symm ▸ hmem
      exact LinearMap.mem_ker.mp hmemKer
    · intro w
      simp [D, y, LinearMap.map_smul, LinearMap.smul_apply, heval]

/-- The actual coordinate kernel on the cone tangent is the radial line. -/
theorem tangentCoordinateLinear_zero_iff {e : ℕ} (C : SkewCoordinates e)
    (Y : ProjectiveVariety (e + e)) (hQ : Y.points ⊆ parameterQuadric e)
    (p : ProjectivePoint (e + e)) (hpY : p ∈ Y.points) (hp : p ∈ affineParameters e)
    (z0 : Point (skewDim e)) (hz0 : z0 ∈ evaluationFlat C p)
    (u : Point (e + e)) (hu : u ∈ Y.affineCone.tangentSpace p.rep) :
    tangentCoordinateLinear C p z0 u = 0 ↔ u ∈ Submodule.span ℂ {p.rep} := by
  constructor
  · intro hzero
    have ha : (Submodule.span ℂ {firstPoint p.rep}).mkQ (firstPoint u) = 0 := by
      simpa only [tangentCoordinateLinear_first, Prod.fst_zero] using congrArg Prod.fst hzero
    have hb : ∀ w, covectorOfPoint (secondPoint u) w - (C.decode z0).val (firstPoint u) w = 0 := by
      intro w
      have hs := tangentCoordinateLinear_second C p z0 u
        (parameter_quadric_tangent_annihilates C Y hQ p hpY z0 hz0 u hu) w
      rw [hzero] at hs
      exact hs.symm.trans (by simp)
    obtain ⟨t, hv, hy⟩ := (tangent_coordinate_kernel C p hp z0 hz0
      (firstPoint u) (covectorOfPoint (secondPoint u))).mp ⟨ha, hb⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨t, ?_⟩
    have heq : u = t • p.rep := by
      calc
        u = joinPoints (firstPoint u) (pointOfCovector (covectorOfPoint (secondPoint u))) := by
          rw [point_covector_inverse, joinPoints_eta]
        _ = joinPoints (t • firstPoint p.rep)
            (pointOfCovector (t • covectorOfPoint (secondPoint p.rep))) := by rw [hv, hy]
        _ = t • p.rep := by rw [pointOfCovector_smul, point_covector_inverse,
          joinPoints_smul, joinPoints_eta]
    exact heq.symm
  · intro hu
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hu
    rw [← ht, map_smul]
    suffices tangentCoordinateLinear C p z0 p.rep = 0 by rw [this, smul_zero]
    apply Prod.ext
    · rw [tangentCoordinateLinear_first]
      apply LinearMap.mem_ker.mp
      simpa only [Submodule.ker_mkQ] using
        (Submodule.mem_span_singleton_self (firstPoint p.rep))
    · change (covectorOfPoint (secondPoint p.rep) - (C.decode z0).val (firstPoint p.rep)).comp
        (directionQuotientSection (firstPoint p.rep)) = 0
      rw [hz0, sub_self, LinearMap.zero_comp]

/-- Normalization removes precisely the radial kernel, giving every parameter
coordinate a unique lift and preserving the chart tangent rank. -/
theorem parameterTangent_normalized_chart {e : ℕ} (C : SkewCoordinates e)
    (Y : ProjectiveVariety (e + e)) (hQ : Y.points ⊆ parameterQuadric e)
    (p : ProjectivePoint (e + e)) (hpY : p ∈ Y.points) (hp : p ∈ affineParameters e)
    (z0 : Point (skewDim e)) (hz0 : z0 ∈ evaluationFlat C p)
    (a : Fin e) (ha : firstPoint p.rep a ≠ 0)
    (T : Submodule ℂ (Point (e + e)))
    (hcone : Y.affineCone.tangentSpace p.rep = T ⊔ Submodule.span ℂ {p.rep})
    (hzero : ∀ u ∈ T, firstPoint u a = 0) :
    parameterTangent C Y p z0 = T.map (tangentCoordinateLinear C p z0) ∧
      Module.finrank ℂ (parameterTangent C Y p z0) = Module.finrank ℂ T := by
  let L := tangentCoordinateLinear C p z0
  have hradmem : p.rep ∈ Y.affineCone.tangentSpace p.rep := by
    rw [hcone]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hrad : L p.rep = 0 :=
    (tangentCoordinateLinear_zero_iff C Y hQ p hpY hp z0 hz0 p.rep hradmem).mpr
      (Submodule.mem_span_singleton_self _)
  have himage : parameterTangent C Y p z0 = T.map L := by
    rw [parameterTangent_eq_map C Y hQ p hpY z0 hz0, hcone, Submodule.map_sup,
      Submodule.map_span, Set.image_singleton, hrad]
    simp [L]
  refine ⟨himage, ?_⟩
  let f := L.comp T.subtype
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro u hu
    have hucone : (u : Point (e + e)) ∈ Y.affineCone.tangentSpace p.rep := by
      rw [hcone]
      exact Submodule.mem_sup_left u.property
    have huL : L u = 0 := LinearMap.mem_ker.mp hu
    have hurad := (tangentCoordinateLinear_zero_iff C Y hQ p hpY hp z0 hz0 u hucone).mp huL
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hurad
    have ht0 : t = 0 := by
      have hc := hzero u u.property
      rw [← ht] at hc
      have hm : t * firstPoint p.rep a = 0 := by simpa [firstPoint, Pi.smul_apply, smul_eq_mul] using hc
      exact (mul_eq_zero.mp hm).resolve_right ha
    have hu0 : (u : Point (e + e)) = 0 := by rw [← ht, ht0, zero_smul]
    change u = 0
    apply Subtype.ext
    simpa only [Submodule.coe_zero] using hu0
  have hrange : LinearMap.range f = T.map L := by
    ext x
    simp [f, Submodule.mem_map]
  rw [himage, ← hrange]
  exact LinearMap.finrank_range_of_inj hf

/-- B21, conc:deg-tangent-coordinates, surjectivity onto U⊕U*. -/
theorem quadric_tangent_coordinates {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (z0 : Point (skewDim e)) (hz0 : z0 ∈ evaluationFlat C p) :
    parameterTangent C (ProjectiveVariety.closure (parameterQuadric e)) p z0 = ⊤ := by
  apply top_unique
  intro x hx
  let S := Submodule.span ℂ {firstPoint p.rep}
  obtain ⟨dv, hdv⟩ := LinearMap.mem_range.mp (show x.1 ∈ LinearMap.range S.mkQ by
    rw [S.range_mkQ]
    trivial)
  have hleft : (x.1, (0 : Module.Dual ℂ (TangentQuotient p))) ∈
      parameterTangent C (ProjectiveVariety.closure (parameterQuadric e)) p z0 := by
    apply Submodule.subset_span
    refine ⟨dv, (C.decode z0).val dv,
      graph_direction_mem_quadric_tangent C p hp z0 hz0 dv, hdv.symm, ?_⟩
    intro w
    simp
  let dy : Module.Dual ℂ (Point e) := x.2.comp S.mkQ
  have hvzero : S.mkQ (firstPoint p.rep) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact Submodule.mem_span_singleton_self _
  have hdy : dy (firstPoint p.rep) = 0 := by
    simp [dy, hvzero]
  have hright : ((0 : TangentQuotient p), x.2) ∈
      parameterTangent C (ProjectiveVariety.closure (parameterQuadric e)) p z0 := by
    apply Submodule.subset_span
    refine ⟨0, dy, vertical_direction_mem_quadric_tangent p hp dy hdy, ?_, ?_⟩
    · simp
    · intro w
      simp [dy, S]
  simpa using Submodule.add_mem
    (parameterTangent C (ProjectiveVariety.closure (parameterQuadric e)) p z0) hleft hright

/-- B21's quadratic value in the chosen coordinate image. -/
theorem tangent_coordinate_quadratic {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (z0 : Point (skewDim e))
    (dv : Point e) (dy : Module.Dual ℂ (Point e))
    (beta : Module.Dual ℂ (TangentQuotient p))
    (hbeta : ∀ w, beta ((Submodule.span ℂ {firstPoint p.rep}).mkQ w) =
      dy w - (C.decode z0).val dv w) :
    beta ((Submodule.span ℂ {firstPoint p.rep}).mkQ dv) = dy dv := by
  rw [hbeta dv]
  have hzero : ((C.decode z0).val dv) dv = 0 := (C.decode z0).property dv
  simp [hzero, LinearMap.sub_apply]

/-- the quotient coordinate beta descends because the tangent satisfies
the differentiated quadric equation. Nullness then gives dy(dv)=0. -/
theorem parameterTangent_null_implies_cone_null {e : ℕ} (C : SkewCoordinates e)
    (Y : ProjectiveVariety (e + e)) (hQ : Y.points ⊆ parameterQuadric e)
    (p : ProjectivePoint (e + e)) (hpY : p ∈ Y.points) (hp : p ∈ affineParameters e)
    (z0 : Point (skewDim e)) (hz0 : z0 ∈ evaluationFlat C p)
    (hnull : ∀ x : parameterTangent C Y p z0, x.1.2 x.1.1 = 0) :
    ∀ v ∈ Y.affineCone.tangentSpace p.rep, parameterValue v = 0 := by
  intro v hv
  let dv : Point e := firstPoint v
  let dy : Module.Dual ℂ (Point e) := covectorOfPoint (secondPoint v)
  have hmem : tangentCoordinateLinear C p z0 v ∈ parameterTangent C Y p z0 := by
    rw [parameterTangent_eq_map C Y hQ p hpY z0 hz0]
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  let x : parameterTangent C Y p z0 := ⟨tangentCoordinateLinear C p z0 v, hmem⟩
  have hxnull := hnull x
  dsimp only [x] at hxnull
  have hfst : (tangentCoordinateLinear C p z0 v).1 =
      (Submodule.span ℂ {firstPoint p.rep}).mkQ dv := by
    simp only [tangentCoordinateLinear_first]
    rfl
  have hsnd : ∀ w, (tangentCoordinateLinear C p z0 v).2 ((Submodule.span ℂ {firstPoint p.rep}).mkQ w) =
      dy w - (C.decode z0).val dv w := by
    intro w
    rw [tangentCoordinateLinear_second C p z0 v
      (parameter_quadric_tangent_annihilates C Y hQ p hpY z0 hz0 v hv) w]
  have hquad := tangent_coordinate_quadratic C p z0 dv dy
    (tangentCoordinateLinear C p z0 v).2 hsnd
  rw [hfst] at hxnull
  rw [hxnull] at hquad
  change parameterValue v = 0
  exact hquad.symm

/-- B26/B27's geometric rigidity interface. The common-constant/coordinate bridge must
connect the actual generic tangent hypothesis to AlgebraicNullRigidity's proved lemmas. -/
theorem null_tangent_parameter_linear {e : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (Y : ProjectiveVariety (e + e)) (hY : Y.IsIrreducible) (hdim : Y.dimension = e - 1)
    (hQ : Y.points ⊆ parameterQuadric e)
    (hnull : ∃ (g : Poly (e + e)) (D : ℕ), g.IsHomogeneous D ∧ g ∉ Y.ideal ∧
      ∀ p ∈ Y.points, MvPolynomial.aeval p.rep g ≠ 0 → p ∈ affineParameters e ∧
        ∀ z0 ∈ evaluationFlat C p,
          Module.finrank ℂ (parameterTangent C Y p z0) = e - 1 ∧
          ∀ x : parameterTangent C Y p z0, x.1.2 x.1.1 = 0) :
    ∃ L : Submodule ℂ (Point (e + e)), IsMaximalIsotropic L ∧ Y = linearProjectivePlane L := by
  classical
  obtain ⟨g, D, hhom, hg, hparam⟩ := hnull
  obtain ⟨p, hp⟩ := ProjectiveFamily.irreducible_points_nonempty Y hY
  obtain ⟨k, hk⟩ := exists_nonzero_coordinate p
  have hpcone : p.rep ∈ Y.affineCone.points := by
    apply (Y.mem_points_mk_iff p.rep p.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using hp
  have hXk : MvPolynomial.X k ∉ Y.ideal := by
    intro h
    exact hk (by simpa using hpcone (MvPolynomial.X k) h)
  let G := g * MvPolynomial.X k
  have hG : G ∉ Y.ideal := by
    intro h
    exact hXk ((hY.mem_or_mem h).resolve_left hg)
  have hGhom : G.IsHomogeneous (D + 1) := hhom.mul (MvPolynomial.isHomogeneous_X ℂ k)
  have hrep : ∀ p ∈ Y.points, MvPolynomial.aeval p.rep G ≠ 0 →
      ∀ v ∈ Y.affineCone.tangentSpace p.rep, parameterValue v = 0 := by
    intro p hp hpg
    have hgp : MvPolynomial.aeval p.rep g ≠ 0 := by
      dsimp only [G] at hpg
      rw [map_mul] at hpg
      exact (mul_ne_zero_iff.mp hpg).1
    obtain ⟨hpaff, hnullp⟩ := hparam p hp hgp
    obtain ⟨b, ψ, hψ, hset⟩ := evaluationFlat_affine_coordinates C p hpaff
    have hb : b ∈ evaluationFlat C p := by rw [hset]; exact ⟨0, by simp⟩
    exact parameterTangent_null_implies_cone_null C Y hQ p hp hpaff b hb (hnullp b hb).2
  have hcone := projective_null_tangent_open Y G (by omega) hGhom hrep
  letI : Y.ideal.IsPrime := hY
  let K := FractionRing (Poly (e + e) ⧸ Y.ideal)
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  let X : AffineVariety (e + e) := ⟨Y.ideal, Y.isRadical⟩
  let φ := TrackD.coordinateFieldMap Y.ideal K
  have hconeDim : X.dimension = e := by
    change Y.affineCone.dimension = e
    rw [Y.dimension_cone (ProjectiveFamily.irreducible_points_nonempty Y hY), hdim]
    omega
  obtain ⟨ι, δ, hcoords, hcomm, hconstants⟩ :=
    Request.affine_separating_coordinate_derivations X hY hconeDim K
  have hdiag (δ' : Derivation ℂ K K) : splitParameterForm K e
      (fun l => δ' (φ (MvPolynomial.X l))) (fun l => δ' (φ (MvPolynomial.X l))) = 0 :=
    generic_null_tangent_derivation X hY G hG hcone K δ'
  have hpair : ∀ i j, splitParameterForm K e
      (fun l => δ i (φ (MvPolynomial.X l))) (fun l => δ j (φ (MvPolynomial.X l))) = 0 := by
    intro i j
    let B := splitParameterForm K e
    let vi : Fin (e + e) → K := fun l => δ i (φ (MvPolynomial.X l))
    let vj : Fin (e + e) → K := fun l => δ j (φ (MvPolynomial.X l))
    have hi : B vi vi = 0 := hdiag (δ i)
    have hj : B vj vj = 0 := hdiag (δ j)
    have hadd : B (vi + vj) (vi + vj) = 0 := by
      have hvadd : (fun l => (δ i + δ j) (φ (MvPolynomial.X l))) = vi + vj := by
        funext l
        rfl
      have h := hdiag (δ i + δ j)
      rw [hvadd] at h
      exact h
    have hsym : B vj vi = B vi vj := (splitParameterForm_symm K e).eq _ _
    have htwice : B vi vj + B vi vj = 0 := by
      simpa only [map_add, LinearMap.add_apply, hi, hj, hsym, zero_add, add_zero] using hadd
    have hz : (2 : K) * B vi vj = 0 := by linear_combination htwice
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  exact null_cone_coordinate_linear (by omega) Y hY hdim K ι δ hcomm hcoords hconstants hpair


/-- The geometric rank argument at a good actual ruling source point. -/
theorem ruling_good_source_pencil_singular {e j N : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (he : 3 ≤ e)
    (R : IsRulingIncidence C V Γ H a j N)
    (z : Point (skewDim e)) (v : Point e) (hw : joinPoints z v ∈ rulingPoints Γ H)
    (hv : v ≠ 0) (p : ProjectivePoint (e + e)) (hp : graphParameter C z v hv = p)
    (hdiff : (Γ.tangentSpace (joinPoints z v)).map (rulingGraphDifferential C (joinPoints z v)) =
      (TrackD.rationalImage Γ (rulingGraphPolynomials C) 1).tangentSpace (graphVector C z v))
    (htrank : Module.finrank ℂ
      ((TrackD.rationalImage Γ (rulingGraphPolynomials C) 1).tangentSpace (graphVector C z v)) = e - 1)
    (hvrank : Module.finrank ℂ (V.tangentSpace z) + 1 = skewDim e)
    (z0 : Point (skewDim e)) (hz0 : z0 ∈ evaluationFlat C p)
    (B : BilinForm ℂ (TangentQuotient p))
    (hB : ∀ x w : Point e, (C.decode (z - z0)).val x w =
      B ((Submodule.span ℂ {firstPoint p.rep}).mkQ x)
        ((Submodule.span ℂ {firstPoint p.rep}).mkQ w)) :
    Module.finrank ℂ (parameterTangent C (parameterClosure C Γ H) p z0) = e - 1 ∧
      ¬ Function.Bijective (skewPencil
        (parameterTangent C (parameterClosure C Γ H) p z0) B) := by
  subst p
  let F := rulingGraphPolynomials C
  let W := TrackD.rationalImage Γ F 1
  let Y := parameterClosure C Γ H
  let p := graphParameter C z v hv
  let y := graphVector C z v
  let T := W.tangentSpace y
  let Θ := parameterTangent C Y p z0
  have hwfirst : firstPoint (joinPoints z v) = z := by
    funext i
    exact Fin.addCases_left (m := skewDim e) (n := e) (motive := fun _ => ℂ) (left := z) (right := v) i
  have hwsecond : secondPoint (joinPoints z v) = v := by
    funext i
    exact Fin.addCases_right (m := skewDim e) (n := e) (motive := fun _ => ℂ) (left := z) (right := v) i
  have hva : v a = 1 := hwsecond ▸ R.normalized (joinPoints z v) hw.1
  have hnorm : ∀ w ∈ Γ.points, MvPolynomial.aeval w (F (Fin.castAdd e a)) = 1 := by
    intro w hwm
    simpa only [F, rulingGraphPolynomials, Fin.addCases_left, MvPolynomial.aeval_X, secondPoint] using
      R.normalized w hwm
  have hEval : (fun i => MvPolynomial.aeval (joinPoints z v) (F i)) = y := by
    change (fun i => MvPolynomial.aeval (joinPoints z v) (rulingGraphPolynomials C i)) = graphVector C z v
    rw [eval_rulingGraphPolynomials, hwfirst, hwsecond]
  have hyW : y ∈ W.points := by
    have h := TrackD.rationalPoint_mem_image Γ F 1 (joinPoints z v) hw.1 (by simp)
    have hy : TrackD.rationalPoint F 1 (joinPoints z v) = y := by
      funext i
      simp only [TrackD.rationalPoint, map_one, div_one]
      exact congrFun hEval i
    exact hy ▸ h
  obtain ⟨_, _, hWnorm⟩ := normalized_polynomial_image_geometry Γ R.incidence_irreducible
    (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R) F
    (Fin.castAdd e a) hnorm
  have hpY : p ∈ Y.points := ProjectiveVariety.subset_closure _ ⟨z, v, hw, hv, rfl⟩
  have hpaff : p ∈ affineParameters e := graphParameter_mem_affine C z v hv
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep ℂ y (graphVector_ne_zero C z v hv)
  have hrep : p.rep = (t : ℂ) • y := by simpa only [p, y, graphParameter, Units.smul_def] using ht.symm
  have hcone0 : Y.affineCone.tangentSpace y = T ⊔ Submodule.span ℂ {y} := by
    have h := Request.normalized_polynomial_image_tangent Γ R.incidence_irreducible
      (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R) F
      (Fin.castAdd e a) hnorm y hyW
    dsimp only [F] at h
    rw [ruling_polynomial_projective_image C V Γ H a R] at h
    exact h
  have hcone : Y.affineCone.tangentSpace p.rep = T ⊔ Submodule.span ℂ {p.rep} := by
    rw [hrep, projective_cone_tangent_scaling Y y (t : ℂ) t.ne_zero,
      Submodule.span_singleton_smul_eq t.isUnit y]
    exact hcone0
  have hcoord : firstPoint p.rep a ≠ 0 := by
    change p.rep (Fin.castAdd e a) ≠ 0
    rw [hrep]
    simpa only [Pi.smul_apply, smul_eq_mul, y, graphVector, joinPoints,
      Fin.addCases_left, hva, mul_one] using t.ne_zero
  have hzero : ∀ u ∈ T, firstPoint u a = 0 := by
    intro u hu
    exact normalized_coordinate_tangent W (Fin.castAdd e a) 1 hWnorm y hyW u hu
  obtain ⟨himage, hθrank⟩ := parameterTangent_normalized_chart C Y
    (parameterClosure_subset_quadric C Γ H) p hpY hpaff z0 hz0 a hcoord T hcone hzero
  refine ⟨hθrank.trans htrank, ?_⟩
  let S := (V.tangentSpace z).map C.decode.toLinearMap
  let A := S.map (alternatingEvaluation v)
  have hSrank : Module.finrank ℂ S + 1 = skewDim e := by
    rw [show Module.finrank ℂ S = Module.finrank ℂ (V.tangentSpace z) from
      C.decode.finrank_map_eq _]
    exact hvrank
  have hker : LinearMap.ker (alternatingEvaluation v) ≤ S := by
    intro D hD
    have hDv : (C.decode (C.decode.symm D)).val v = 0 := by
      rw [C.decode.apply_symm_apply]
      change alternatingEvaluation v D = 0
      exact LinearMap.mem_ker.mp hD
    refine Submodule.mem_map.mpr ⟨C.decode.symm D,
      ruling_evaluation_kernel_tangent C V Γ H a R z v hw hv _ hDv, ?_⟩
    exact C.decode.apply_symm_apply D
  have hArank := alternating_hyperplane_evaluation_rank he v hv S hSrank hker
  change Module.finrank ℂ A + 1 = e - 1 at hArank
  have hQrank : Module.finrank ℂ (TangentQuotient p) = e - 1 := by
    rw [Submodule.finrank_quotient, finrank_span_singleton hpaff.2, Module.finrank_fin_fun]
  have hAlower : Module.finrank ℂ A < Module.finrank ℂ (TangentQuotient p) := by
    rw [hQrank]
    omega
  apply skewPencil_singular_of_covector_image (firstPoint p.rep) Θ B A hAlower
  intro x
  have hxT : (x : TangentQuotient p × Module.Dual ℂ (TangentQuotient p)) ∈
      T.map (tangentCoordinateLinear C p z0) := himage ▸ x.property
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.mp hxT
  have humap : u ∈ (Γ.tangentSpace (joinPoints z v)).map (rulingGraphDifferential C (joinPoints z v)) :=
    hdiff ▸ hu
  obtain ⟨δ, hδ, hδu⟩ := Submodule.mem_map.mp humap
  let dz := firstPoint δ
  let dv := secondPoint δ
  have hdz : dz ∈ V.tangentSpace z := by
    have hs := (R.smooth (joinPoints z v) hw).2.2
    rw [hwfirst] at hs
    rw [← hs]
    exact Submodule.mem_map.mpr ⟨δ, hδ, rfl⟩
  have hufirst : firstPoint u = dv := by
    rw [← hδu, ← joinPoints_eta δ, rulingGraphDifferential_coordinates]
    funext i
    exact Fin.addCases_left (m := e) (n := e) (motive := fun _ => ℂ) (left := _) (right := _) i
  have husecond : covectorOfPoint (secondPoint u) = (C.decode dz).val v + (C.decode z).val dv := by
    rw [← hδu, ← joinPoints_eta δ, rulingGraphDifferential_coordinates]
    have hs : secondPoint (joinPoints (secondPoint δ)
        (pointOfCovector ((C.decode (firstPoint δ)).val v + (C.decode z).val (secondPoint δ)))) =
        pointOfCovector ((C.decode (firstPoint δ)).val v + (C.decode z).val (secondPoint δ)) := by
      funext i
      exact Fin.addCases_right (m := e) (n := e) (motive := fun _ => ℂ) (left := _) (right := _) i
    rw [hs, covector_point_inverse]
  have hucone : u ∈ Y.affineCone.tangentSpace p.rep := by
    rw [hcone]
    exact Submodule.mem_sup_left hu
  have hα : x.val.1 = (Submodule.span ℂ {firstPoint p.rep}).mkQ dv := by
    rw [← hux, tangentCoordinateLinear_first, hufirst]
  have hβ (w : Point e) : x.val.2 ((Submodule.span ℂ {firstPoint p.rep}).mkQ w) =
      (C.decode dz).val v w + (C.decode z).val dv w - (C.decode z0).val dv w := by
    rw [← hux, tangentCoordinateLinear_second C p z0 u
      (parameter_quadric_tangent_annihilates C Y (parameterClosure_subset_quadric C Γ H)
        p hpY z0 hz0 u hucone) w, hufirst, husecond, LinearMap.add_apply]
  refine Submodule.mem_map.mpr ⟨C.decode dz, Submodule.mem_map.mpr ⟨dz, hdz, rfl⟩, ?_⟩
  apply LinearMap.ext
  intro w
  change (C.decode dz).val v w = x.val.2 ((Submodule.span ℂ {firstPoint p.rep}).mkQ w) -
    B x.val.1 ((Submodule.span ℂ {firstPoint p.rep}).mkQ w)
  rw [hβ, hα, ← hB]
  simp only [map_sub, Submodule.coe_sub, LinearMap.sub_apply]
  ring

section Ruling

variable {e h j N : ℕ} (C : SkewCoordinates e)
  (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e)) (a : Fin e)
  (he : 3 ≤ e) (hh : 1 ≤ h ∧ h + 2 ≤ e) (hd : V.dimension = flatDim e + h)
  (R : IsRulingIncidence C V Γ H a j N)

include he hh hd R

/-- B01, conc:degree.dimension, from the actual parameter image and full flat fibers. -/
theorem parameterClosure_dimension : (parameterClosure C Γ H).dimension = h + j := by
  have himage := Request.polynomial_projective_image_dimension Γ R.incidence_irreducible
    (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R)
    (rulingGraphPolynomials C)
    (fun w hw _ => rulingGraphPolynomials_nonzero C V Γ H a R w hw)
    (fun p hp => ruling_polynomial_projective_fiber_dimension C V Γ H a R p hp)
  rw [ruling_polynomial_projective_image C V Γ H a R, ← parameterClosure] at himage
  rw [R.incidence_dimension, hd] at himage
  omega

/-- B09's density assertion, with the actual graph embedded in the compact incidence. -/
theorem dense_ruling_incidence :
    ProjectiveVariety.closure (rulingTripleImage C Γ H) = compactIncidence C Γ H := by
  let W := ProjectiveVariety.closure (rulingTripleImage C Γ H)
  have hGraph : ∀ z v, joinPoints z v ∈ rulingPoints Γ H → ∀ hv : v ≠ 0,
      segrePoint (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv))
        (affineEmbedding z) ∈ W.points := by
    intro z v hw hv
    exact ProjectiveVariety.subset_closure _ ⟨z, v, hw, hv, rfl⟩
  have hback : (compactIncidence C Γ H).points ⊆ W.points :=
    compact_incidence_subset_of_ruling_graph C V Γ H a R W hGraph
  have hforward : W.points ⊆ (compactIncidence C Γ H).points := by
    apply projective_closure_subset
    rintro q ⟨z, v, hw, hv, rfl⟩
    have hlift : (Projectivization.mk ℂ v hv, graphParameter C z v hv) ∈
        liftedParameterPairs C Γ H := ⟨z, v, hw, hv, rfl, rfl⟩
    have hbase : (Projectivization.mk ℂ v hv, graphParameter C z v hv) ∈
        liftedParameterBase C Γ H :=
      ProjectiveVariety.subset_closure _
        ⟨Projectivization.mk ℂ v hv, graphParameter C z v hv, hlift, rfl⟩
    exact ProjectiveVariety.subset_closure _
      ⟨Projectivization.mk ℂ v hv, graphParameter C z v hv, affineEmbedding z,
        ⟨hbase, graph_incidenceCondition C z v hv⟩, rfl⟩
  apply ProjectiveVariety.ext
  change W.ideal = (compactIncidence C Γ H).ideal
  rw [← W.vanishingIdeal_points, ← (compactIncidence C Γ H).vanishingIdeal_points]
  exact congrArg ProjectiveVariety.vanishingIdeal (Set.Subset.antisymm hforward hback)

/-- B09, conc:deg-dense-incidence. Singular parameter bases are included. -/
theorem compactIncidence_geometry :
    (pairClosure (liftedParameterPairs C Γ H)).IsIrreducible ∧
    (pairClosure (liftedParameterPairs C Γ H)).dimension = h + j ∧
    (compactIncidence C Γ H).IsIrreducible ∧
    (compactIncidence C Γ H).dimension = flatDim e + h + j ∧
    incidencePointImage C Γ H = (projectiveClosure V).points := by
  obtain ⟨hpi, hpd⟩ := RulingMaps.ruling_pair_image_geometry C V Γ H a R hd
  obtain ⟨hti, htd⟩ := RulingMaps.ruling_triple_image_geometry C V Γ H a R hd
  have hT : rulingTripleImage C Γ H = RulingMaps.tripleSet C Γ H := rfl
  have hK : compactIncidence C Γ H = ProjectiveVariety.closure (RulingMaps.tripleSet C Γ H) := by
    rw [← hT]
    exact (dense_ruling_incidence C V Γ H a he hh hd R).symm
  refine ⟨hpi, hpd, hK ▸ hti, hK ▸ htd, RulingMaps.ruling_incidence_point_image C V Γ H a R⟩

/-- B11, conc:deg-fiber-degree. Smooth ruling fibers supply multiplicity one. -/
theorem generic_point_fiber_degree :
    ∃ d : ℚ, 0 < d ∧ d ≤ (N : ℚ) ∧ (j = 1 → d = 1) ∧
      HasGenericPointFiberDegree C V Γ H d :=
  B11.generic_point_fiber_degree_aux C a V Γ H hh.1 hd R
    (parameterClosure_dimension C V Γ H a he hh hd R)

namespace HilbertDegree

omit he hh hd R in
theorem pairDegree_add_swap (s t : ℕ) :
    HilbertMulti.pairDegree s t + HilbertMulti.pairDegree t s =
      HilbertMulti.pairDegree (s + t) (s + t) := by
  ext i
  fin_cases i <;> simp [HilbertMulti.pairDegree, Nat.add_comm]

def diagonalMonomial {n m : ℕ} (s t : ℕ) (i : Fin n) (k : Fin m) : Poly (n + m) :=
  MvPolynomial.X (Fin.castAdd m i) ^ t * MvPolynomial.X (Fin.natAdd n k) ^ s

omit he hh hd R in
theorem diagonalMonomial_weighted {n m : ℕ} (s t : ℕ) (i : Fin n) (k : Fin m) :
    (diagonalMonomial s t i k).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) (HilbertMulti.pairDegree t s) := by
  have h := (MvPolynomial.isWeightedHomogeneous_X ℂ
    (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) (Fin.castAdd m i)).pow t |>.mul
    ((MvPolynomial.isWeightedHomogeneous_X ℂ
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) (Fin.natAdd n k)).pow s)
  have hg : t • HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m) (Fin.castAdd m i) +
      s • HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m) (Fin.natAdd n k) =
      HilbertMulti.pairDegree t s := by
    ext j
    fin_cases j <;>
      simp [HilbertMulti.blockWeight, HilbertMulti.pairBlocks,
        HilbertMulti.pairDegree, Finsupp.smul_single]
  simpa only [hg, diagonalMonomial] using h

/-- Multiply each restriction section into a diagonal section. -/
noncomputable def diagonalMultiply {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) (i : Fin n) (k : Fin m) :
    pairSection T s t →ₗ[ℂ] pairSection T (s + t) (s + t) := by
  let I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T)
  refine
    { toFun := fun x => ⟨x.1 * Ideal.Quotient.mk I (diagonalMonomial s t i k), ?_⟩
      map_add' := fun x y => ?_
      map_smul' := fun c x => ?_ }
  · obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I f = x.1 at hfx
    have hp : f.IsWeightedHomogeneous
        (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) (HilbertMulti.pairDegree s t) := by
      rw [← MvPolynomial.mem_weightedHomogeneousSubmodule, HilbertMulti.pairBlockPiece]
      exact hf
    have hprod : (f * diagonalMonomial s t i k).IsWeightedHomogeneous
        (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))
        (HilbertMulti.pairDegree (s + t) (s + t)) := by
      simpa only [pairDegree_add_swap] using hp.mul (diagonalMonomial_weighted s t i k)
    apply Submodule.mem_map.mpr
    refine ⟨f * diagonalMonomial s t i k, ?_, ?_⟩
    · rw [← HilbertMulti.pairBlockPiece]
      exact hprod
    · change Ideal.Quotient.mk I (f * diagonalMonomial s t i k) = _
      rw [map_mul, hfx]
  · apply Subtype.ext
    exact add_mul _ _ _
  · apply Subtype.ext
    exact smul_mul_assoc _ _ _

noncomputable def diagonalFamily {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) :
    pairSection T s t →ₗ[ℂ] (Fin n × Fin m → pairSection T (s + t) (s + t)) :=
  LinearMap.pi (fun ik => diagonalMultiply T s t ik.1 ik.2)

omit he hh hd R in
theorem diagonalFamily_injective {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) :
    Function.Injective (diagonalFamily T s t) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  have hx0 := LinearMap.mem_ker.mp hx
  let I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T)
  obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
  change Ideal.Quotient.mk I f = x.1 at hfx
  have hfI : f ∈ I := by
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro w hw
    obtain ⟨u, v, hu, hv, hmem, rfl⟩ := hw
    have hu' : ∃ i, u i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hu
      funext i
      exact h i
    have hv' : ∃ k, v k ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv
      funext k
      exact h k
    obtain ⟨i, hi⟩ := hu'
    obtain ⟨k, hk⟩ := hv'
    have hcoord := congrArg Subtype.val (congrFun hx0 (i, k))
    change x.1 * Ideal.Quotient.mk I (diagonalMonomial s t i k) = 0 at hcoord
    rw [← hfx, ← map_mul] at hcoord
    have hvan := (MvPolynomial.mem_vanishingIdeal_iff.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hcoord)) (joinPoints u v) ⟨u, v, hu, hv, hmem, rfl⟩
    rw [map_mul] at hvan
    have hmono : MvPolynomial.aeval (joinPoints u v) (diagonalMonomial s t i k) ≠ 0 := by
      simpa [diagonalMonomial, joinPoints] using
        mul_ne_zero (pow_ne_zero t hi) (pow_ne_zero s hk)
    exact (mul_eq_zero.mp hvan).resolve_right hmono
  apply Subtype.ext
  change x.1 = 0
  rw [← hfx]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hfI

omit he hh hd R in
/-- An arbitrary pair restriction rank is bounded by a finite product of diagonal ranks. -/
theorem pairHilbert_le_diagonal {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) :
    pairHilbert T s t ≤ (n * m) * pairHilbert T (s + t) (s + t) := by
  have h := LinearMap.finrank_le_finrank_of_injective (diagonalFamily_injective T s t)
  simpa [pairHilbert, Module.finrank_pi_fintype] using h

def segrePullback {n m : ℕ} : Poly (n * m) →ₐ[ℂ] Poly (n + m) :=
  MvPolynomial.aeval (fun ij =>
    MvPolynomial.X (Fin.castAdd m (finProdFinEquiv.symm ij).1) *
      MvPolynomial.X (Fin.natAdd n (finProdFinEquiv.symm ij).2))

omit he hh hd R in
theorem eval_segrePullback {n m : ℕ} (x : Point n) (y : Point m) (f : Poly (n * m)) :
    MvPolynomial.aeval (joinPoints x y) (segrePullback f) =
      MvPolynomial.aeval (segreVector x y) f := by
  have h : (MvPolynomial.aeval (joinPoints x y)).comp segrePullback =
      MvPolynomial.aeval (segreVector x y) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [segrePullback, segreVector, joinPoints]
  exact DFunLike.congr_fun h f

omit he hh hd R in
theorem segrePoint_mk_hilb {n m : ℕ} (x : Point n) (y : Point m)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    segrePoint (Projectivization.mk ℂ x hx) (Projectivization.mk ℂ y hy) =
      Projectivization.mk ℂ (segreVector x y) (segreVector_ne_zero x y hx hy) := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  obtain ⟨v, hv⟩ := Projectivization.exists_smul_eq_mk_rep ℂ y hy
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(u : ℂ) * (v : ℂ), ?_⟩
  change ((u : ℂ) * (v : ℂ)) • segreVector x y =
    segreVector (Projectivization.mk ℂ x hx).rep (Projectivization.mk ℂ y hy).rep
  have hu' : (Projectivization.mk ℂ x hx).rep = (u : ℂ) • x := by
    simpa only [Units.smul_def] using hu.symm
  have hv' : (Projectivization.mk ℂ y hy).rep = (v : ℂ) • y := by
    simpa only [Units.smul_def] using hv.symm
  rw [hu', hv']
  ext k
  simp only [segreVector, Pi.smul_apply, smul_eq_mul]
  ring

omit he hh hd R in
theorem castAdd_eq_castAdd_hilb {n m : ℕ} (i k : Fin n) :
    Fin.castAdd m i = Fin.castAdd m k ↔ i = k := by
  simp only [Fin.ext_iff]
  rfl

omit he hh hd R in
theorem natAdd_eq_natAdd_hilb {n m : ℕ} (j k : Fin m) :
    Fin.natAdd n j = Fin.natAdd n k ↔ j = k := by
  simp only [Fin.ext_iff]
  change n + j.val = n + k.val ↔ j.val = k.val
  omega

omit he hh hd R in
theorem castAdd_ne_natAdd_hilb {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro heq
  have hv := congrArg Fin.val heq
  change i.val = n + j.val at hv
  have hit := i.isLt
  omega

omit he hh hd R in
theorem single_castAdd_left_sum {n m : ℕ} (i : Fin n) :
    (∑ k : Fin n, (Finsupp.single (Fin.castAdd m i) (1 : ℕ)) (Fin.castAdd m k)) = 1 := by
  classical
  simp [Finsupp.single_apply, castAdd_eq_castAdd_hilb]

omit he hh hd R in
theorem single_natAdd_right_sum {n m : ℕ} (j : Fin m) :
    (∑ k : Fin m, (Finsupp.single (Fin.natAdd n j) (1 : ℕ)) (Fin.natAdd n k)) = 1 := by
  classical
  simp [Finsupp.single_apply, natAdd_eq_natAdd_hilb]

omit he hh hd R in
theorem single_castAdd_right_sum {n m : ℕ} (i : Fin n) :
    (∑ k : Fin m, (Finsupp.single (Fin.castAdd m i) (1 : ℕ)) (Fin.natAdd n k)) = 0 := by
  classical
  simp [Finsupp.single_apply, castAdd_ne_natAdd_hilb]

omit he hh hd R in
theorem single_natAdd_left_sum {n m : ℕ} (j : Fin m) :
    (∑ k : Fin n, (Finsupp.single (Fin.natAdd n j) (1 : ℕ)) (Fin.castAdd m k)) = 0 := by
  classical
  simp [Finsupp.single_apply, Ne.symm (castAdd_ne_natAdd_hilb _ j)]

omit he hh hd R in
theorem diagonalMonomial_lift {n m : ℕ} (q : ℕ) (d : Fin (n + m) →₀ ℕ)
    (hleft : (∑ i : Fin n, d (Fin.castAdd m i)) = q)
    (hright : (∑ j : Fin m, d (Fin.natAdd n j)) = q) :
    ∃ f : Poly (n * m), f.IsHomogeneous q ∧
      segrePullback f = MvPolynomial.monomial d (1 : ℂ) := by
  classical
  induction q generalizing d with
  | zero =>
    have hd : d = 0 := by
      ext k
      cases k using Fin.addCases with
      | left i =>
        have hh := Finset.single_le_sum (fun j _ => Nat.zero_le (d (Fin.castAdd m j)))
          (Finset.mem_univ i)
        rw [hleft] at hh
        simp only [Finsupp.zero_apply]
        omega
      | right j =>
        have hh := Finset.single_le_sum (fun i _ => Nat.zero_le (d (Fin.natAdd n i)))
          (Finset.mem_univ j)
        rw [hright] at hh
        simp only [Finsupp.zero_apply]
        omega
    refine ⟨1, MvPolynomial.isHomogeneous_one _ _, ?_⟩
    simp [hd]
  | succ q ih =>
    obtain ⟨i, hi⟩ : ∃ i : Fin n, 0 < d (Fin.castAdd m i) := by
      by_contra h
      push Not at h
      have hz : (∑ i : Fin n, d (Fin.castAdd m i)) = 0 :=
        Finset.sum_eq_zero (fun i _ => Nat.le_zero.mp (h i))
      omega
    obtain ⟨j, hj⟩ : ∃ j : Fin m, 0 < d (Fin.natAdd n j) := by
      by_contra h
      push Not at h
      have hz : (∑ j : Fin m, d (Fin.natAdd n j)) = 0 :=
        Finset.sum_eq_zero (fun j _ => Nat.le_zero.mp (h j))
      omega
    let a := Fin.castAdd m i
    let b := Fin.natAdd n j
    let d' := d - Finsupp.single a 1 - Finsupp.single b 1
    have hab : a ≠ b := by
      intro heq
      have hv := congrArg Fin.val heq
      change i.val = n + j.val at hv
      have hit : i.val < n := i.isLt
      omega
    have hd : d' + Finsupp.single a 1 + Finsupp.single b 1 = d := by
      ext k
      simp only [d', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hka hkb <;> subst_vars <;> simp_all [a, b] <;> omega
    have hl : (∑ i : Fin n, d' (Fin.castAdd m i)) = q := by
      have hsum := congrArg (fun e : Fin (n + m) →₀ ℕ => ∑ k : Fin n, e (Fin.castAdd m k)) hd
      simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hsum
      dsimp only [a, b] at hsum
      rw [single_castAdd_left_sum, single_natAdd_left_sum, hleft] at hsum
      omega
    have hr : (∑ j : Fin m, d' (Fin.natAdd n j)) = q := by
      have hsum := congrArg (fun e : Fin (n + m) →₀ ℕ => ∑ k : Fin m, e (Fin.natAdd n k)) hd
      simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hsum
      dsimp only [a, b] at hsum
      rw [single_castAdd_right_sum, single_natAdd_right_sum, hright] at hsum
      omega
    obtain ⟨f, hf, hfe⟩ := ih d' hl hr
    refine ⟨f * MvPolynomial.X (finProdFinEquiv (i, j)), ?_, ?_⟩
    · simpa only [Nat.succ_eq_add_one] using hf.mul (MvPolynomial.isHomogeneous_X ℂ _)
    · rw [map_mul, hfe]
      simp only [segrePullback, MvPolynomial.aeval_X, Equiv.symm_apply_apply]
      rw [← hd]
      simp only [MvPolynomial.monomial_add_single, pow_one]
      simp only [a, b]
      ring

omit he hh hd R in
theorem diagonal_lift {n m : ℕ} (q : ℕ) (f : Poly (n + m))
    (hf : f ∈ MvPolynomial.restrictSupport ℂ {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = q ∧
        (∑ j : Fin m, d (Fin.natAdd n j)) = q}) :
    ∃ g : Poly (n * m), g.IsHomogeneous q ∧ segrePullback g = f := by
  classical
  have hs : (f.support : Set (Fin (n + m) →₀ ℕ)) ⊆
      {d | (∑ i : Fin n, d (Fin.castAdd m i)) = q ∧
        (∑ j : Fin m, d (Fin.natAdd n j)) = q} := hf
  have hex : ∀ d ∈ f.support, ∃ g : Poly (n * m), g.IsHomogeneous q ∧
      segrePullback g = MvPolynomial.monomial d (f.coeff d) := by
    intro d hd
    obtain ⟨g, hg, heq⟩ := diagonalMonomial_lift q d (hs hd).1 (hs hd).2
    refine ⟨f.coeff d • g, (MvPolynomial.homogeneousSubmodule _ ℂ q).smul_mem _ hg, ?_⟩
    rw [map_smul, heq]
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  choose g hg hge using hex
  refine ⟨∑ d : f.support, g d d.2, ?_, ?_⟩
  · exact (MvPolynomial.homogeneousSubmodule _ ℂ q).sum_mem (fun d _ => hg d d.2)
  · simp only [map_sum, hge]
    exact (Finset.sum_coe_sort f.support
      (fun d => MvPolynomial.monomial d (f.coeff d))).trans f.as_sum.symm

noncomputable def segreQuotient {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) :
    (Poly (n * m) ⧸ (pairClosure T).ideal) →ₐ[ℂ]
      (Poly (n + m) ⧸ MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (closedPairs T))) := by
  let I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (closedPairs T))
  refine Ideal.Quotient.liftₐ (pairClosure T).ideal
    ((Ideal.Quotient.mkₐ ℂ I).comp segrePullback) ?_
  intro f hf
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro w ⟨x, y, hx, hy, hmem, rfl⟩
  change MvPolynomial.aeval (joinPoints x y) (segrePullback (n := n) (m := m) f) = 0
  rw [eval_segrePullback x y f]
  have hp : Projectivization.mk ℂ (segreVector x y) (segreVector_ne_zero x y hx hy) ∈
      (pairClosure T).points := by
    rw [← segrePoint_mk_hilb x y hx hy]
    exact hmem
  exact ((ProjectiveVariety.mem_points_mk_iff _ _ _).mp hp) f hf

omit he hh hd R in
theorem segreQuotient_mk {n m : ℕ} (T : Set (ProjectivePoint n × ProjectivePoint m))
    (f : Poly (n * m)) :
    segreQuotient T (Ideal.Quotient.mk (pairClosure T).ideal f) =
      Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (closedPairs T)))
        (segrePullback (n := n) (m := m) f) := by
  simp only [segreQuotient, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

omit he hh hd R in
theorem pairHilbert_diagonal_le {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (q : ℕ) :
    pairHilbert (closedPairs T) q q ≤ (pairClosure T).hilbert q := by
  let V := pairClosure T
  let φ := (segreQuotient T).toLinearMap
  have hinc : pairSection (closedPairs T) q q ≤ (V.restrictionSpace q).map φ := by
    intro x hx
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp hx
    obtain ⟨g, hg, hgf⟩ := diagonal_lift q f hf
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk V.ideal g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
    change segreQuotient T (Ideal.Quotient.mk (pairClosure T).ideal g) = x
    rw [segreQuotient_mk, hgf]
    exact hfx
  exact (Submodule.finrank_mono hinc).trans (Submodule.finrank_map_le φ (V.restrictionSpace q))

noncomputable def rayPolynomial (u : Fin 2 → ℚ) (P : BaseHilbertPolynomial) : Polynomial ℚ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (u i) * Polynomial.X) P

omit he hh hd R in
theorem eval_rayPolynomial (u : Fin 2 → ℚ) (P : BaseHilbertPolynomial) (x : ℚ) :
    (rayPolynomial u P).eval x = MvPolynomial.eval (fun i => u i * x) P := by
  have heq : (Polynomial.evalRingHom x).comp
      (MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (u i) * Polynomial.X)) =
      MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i => u i * x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp
  exact DFunLike.congr_fun heq P

omit he hh hd R in
theorem coeff_rayPolynomial (u : Fin 2 → ℚ) (P : BaseHilbertPolynomial) (k : ℕ) :
    (rayPolynomial u P).coeff k = MvPolynomial.eval u (MvPolynomial.homogeneousComponent k P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [rayPolynomial, map_add, Polynomial.coeff_add] using congrArg₂ (· + ·) hP hQ
  | monomial d c =>
    have hdeg : d.degree = d 0 + d 1 := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    have hm : rayPolynomial u (MvPolynomial.monomial d c) =
        Polynomial.C (c * u 0 ^ d 0 * u 1 ^ d 1) * Polynomial.X ^ (d 0 + d 1) := by
      simp only [rayPolynomial, MvPolynomial.eval₂Hom_monomial]
      rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
      simp only [mul_pow, ← Polynomial.C_pow, pow_add, Polynomial.C_mul]
      ring
    rw [hm, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    simp only [hdeg]
    split_ifs with hk
    · rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
        Fin.prod_univ_two]
      ring
    · simp

omit he hh hd R in
theorem totalDegree_le_of_growth (P : BaseHilbertPolynomial) (Q : Polynomial ℚ)
    (c : ℚ) (N : ℕ)
    (hPnonneg : ∀ s t : ℕ, N ≤ s → N ≤ t →
      0 ≤ MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P)
    (hbound : ∀ s t : ℕ, N ≤ s → N ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P ≤
        c * Q.eval ((s + t : ℕ) : ℚ)) :
    P.totalDegree ≤ Q.natDegree := by
  classical
  have hray (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
      (rayPolynomial (Fin.cons (a : ℚ) (fun _ : Fin 1 => (b : ℚ))) P).natDegree ≤ Q.natDegree := by
    let u : Fin 2 → ℚ := Fin.cons (a : ℚ) (fun _ : Fin 1 => (b : ℚ))
    let p := rayPolynomial u P
    let q := Polynomial.C c * Q.comp (Polynomial.C ((a + b : ℕ) : ℚ) * Polynomial.X)
    change p.natDegree ≤ Q.natDegree
    have heval (n : ℕ) : p.eval (n : ℚ) =
        MvPolynomial.eval (Fin.cons ((a * n : ℕ) : ℚ) (fun _ : Fin 1 => ((b * n : ℕ) : ℚ))) P := by
      rw [eval_rayPolynomial]
      apply congrArg (fun v : Fin 2 → ℚ => MvPolynomial.eval v P)
      ext i
      fin_cases i <;> simp [u, Nat.cast_mul]
    have han (n : ℕ) (hn : N ≤ n) : N ≤ a * n :=
      hn.trans (by simpa using Nat.mul_le_mul_right n ha)
    have hbn (n : ℕ) (hn : N ≤ n) : N ≤ b * n :=
      hn.trans (by simpa using Nat.mul_le_mul_right n hb)
    by_cases hp : p = 0
    · simp only [hp, Polynomial.natDegree_zero, Nat.zero_le]
    · have hpos : 0 < p.leadingCoeff := lt_of_le_of_ne
        (OAI.PiExponentJets.W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg p N
          (fun n hn => by rw [heval]; exact hPnonneg _ _ (han n hn) (hbn n hn)))
        (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hp))
      have hdeg := OAI.PiExponentJets.W24.natDegree_le_of_eventual_polynomial_le p q hpos N
        (fun n hn => by
          rw [heval]
          simpa [q, Polynomial.eval_comp, Nat.cast_add, Nat.cast_mul, add_mul] using
            hbound (a * n) (b * n) (han n hn) (hbn n hn))
      have hcompdeg : (Q.comp (Polynomial.C ((a + b : ℕ) : ℚ) * Polynomial.X)).natDegree ≤
          Q.natDegree := by
        simpa using OAI.PiExponentJets.W24.natDegree_affine_comp_le Q ((a + b : ℕ) : ℚ) 0
      exact hdeg.trans ((Polynomial.natDegree_C_mul_le _ _).trans hcompdeg)
  have hcomp (k : ℕ) (hk : Q.natDegree < k) : MvPolynomial.homogeneousComponent k P = 0 := by
    let S : Set ℚ := {x | ∃ a : ℕ, 1 ≤ a ∧ x = (a : ℚ)}
    have hS : S.Infinite := by
      have hmap : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℚ)) := by
        intro n m heq
        exact Nat.add_right_cancel (Nat.cast_injective heq)
      apply (Set.infinite_range_of_injective hmap).mono
      rintro _ ⟨n, rfl⟩
      exact ⟨n + 1, by omega, rfl⟩
    apply MvPolynomial.funext_set (fun _ : Fin 2 => S) (fun _ => hS)
    intro u hu
    obtain ⟨a, ha, hau⟩ := hu 0 (Set.mem_univ _)
    obtain ⟨b, hb, hbu⟩ := hu 1 (Set.mem_univ _)
    have hu' : u = Fin.cons (a : ℚ) (fun _ : Fin 1 => (b : ℚ)) := by
      ext i
      fin_cases i
      · exact hau
      · exact hbu
    rw [hu', ← coeff_rayPolynomial]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hray a b ha hb) hk)).trans
      (by simp)
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro d hd
  have hc : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  by_contra h
  have heq := congrArg (fun f : BaseHilbertPolynomial => f.coeff d) (hcomp d.degree (by
    change Q.natDegree < d.sum (fun _ e => e)
    exact Nat.lt_of_not_ge h))
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos rfl, MvPolynomial.coeff_zero] at heq
  exact hc heq

end HilbertDegree

/-- B13.3's degree bound on the actual base polynomial, needed by the finite identity. -/
theorem parameterBaseHilbert_degree : (parameterBaseHilbert C Γ H).totalDegree ≤ h + j := by
  classical
  let T := liftedParameterPairs C Γ H
  let W := pairClosure T
  let P := parameterBaseHilbert C Γ H
  obtain ⟨NP, hP⟩ := (parameterBaseHilbert_eventually_polynomial C Γ H).choose_spec
  have hPeval (s t : ℕ) (hs : NP ≤ s) (ht : NP ≤ t) :
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P =
        (pairHilbert (liftedParameterBase C Γ H) s t : ℚ) := by
    simpa only [P, parameterBaseHilbert] using hP s t hs ht
  obtain ⟨NW, hW⟩ := W.hilbert_eventually
  have hdim : W.hilbertPolynomial.natDegree = h + j :=
    (compactIncidence_geometry C V Γ H a he hh hd R).2.1
  refine (HilbertDegree.totalDegree_le_of_growth P W.hilbertPolynomial
    ((e * (e + e) : ℕ) : ℚ) (NP + NW + 1) ?_ ?_).trans_eq hdim
  · intro s t hs ht
    rw [hPeval s t (by omega) (by omega)]
    positivity
  · intro s t hs ht
    rw [hPeval s t (by omega) (by omega), ← hW (s + t) (by omega)]
    have hdiag := HilbertDegree.pairHilbert_le_diagonal (closedPairs T) s t
    have hordinary := HilbertDegree.pairHilbert_diagonal_le T (s + t)
    have hbound := hdiag.trans (Nat.mul_le_mul_left (e * (e + e)) hordinary)
    exact_mod_cast hbound

omit he hh hd R in
/-- Actual eventual multigraded ranks determine their rational polynomial uniquely. -/
theorem hilbertPolynomial_unique {k : ℕ} (P Q : MvPolynomial (Fin k) ℚ) (N : ℕ)
    (hPQ : ∀ d : Fin k → ℕ, (∀ i, N ≤ d i) →
      MvPolynomial.eval (fun i => (d i : ℚ)) P =
        MvPolynomial.eval (fun i => (d i : ℚ)) Q) : P = Q := by
  let S : Set ℚ := Set.range (fun n : ℕ => ((n + N : ℕ) : ℚ))
  have hS : S.Infinite := by
    apply Set.infinite_range_of_injective
    intro n m h
    exact Nat.add_right_cancel (Nat.cast_injective h)
  apply MvPolynomial.funext_set (fun _ : Fin k => S) (fun _ => hS)
  intro x hx
  have hex (i : Fin k) : ∃ n : ℕ, ((n + N : ℕ) : ℚ) = x i :=
    hx i (Set.mem_univ i)
  choose d hd using hex
  have h := hPQ (fun i => d i + N) (fun i => Nat.le_add_left N (d i))
  simpa only [hd] using h

omit he hh hd R in
/-- The remaining incidence assertion is an eventual equality of actual restriction ranks. -/
theorem incidence_hilbert_identity_of_eventual_rank
    (hRank : ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s → N ≤ t → N ≤ u →
      (tripleHilbert (incidenceTriples C Γ H) s t u : ℚ) =
        MvPolynomial.eval
          (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ))))
          (koszulIncidenceHilbert e (parameterBaseHilbert C Γ H))) :
    compactIncidenceHilbert C Γ H =
      koszulIncidenceHilbert e (parameterBaseHilbert C Γ H) := by
  obtain ⟨NC, hC⟩ := (compactIncidenceHilbert_eventually_polynomial C Γ H).choose_spec
  obtain ⟨NR, hR⟩ := hRank
  apply hilbertPolynomial_unique _ _ (NC + NR)
  intro d hd
  have heval : (fun i : Fin 3 => (d i : ℚ)) =
      Fin.cons (d 0 : ℚ) (Fin.cons (d 1 : ℚ) (fun _ : Fin 1 => (d 2 : ℚ))) := by
    ext i
    fin_cases i <;> rfl
  rw [heval]
  have hNC (i : Fin 3) : NC ≤ d i := (Nat.le_add_right NC NR).trans (hd i)
  have hNR (i : Fin 3) : NR ≤ d i := (Nat.le_add_left NR NC).trans (hd i)
  have hc := hC (d 0) (d 1) (d 2) (hNC 0) (hNC 1) (hNC 2)
  have hr := hR (d 0) (d 1) (d 2) (hNR 0) (hNR 1) (hNR 2)
  simpa only [compactIncidenceHilbert] using hc.trans hr

namespace IncidenceSections

set_option backward.isDefEq.respectTransparency false

omit he hh hd R in
theorem directionCoordinates_joint_regular {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m))
    (z : Poly (n + m) ⧸ MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T))
    (hz : ∀ i : Fin n,
      Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T))
        (MvPolynomial.X (Fin.castAdd m i)) * z = 0) : z = 0 := by
  classical
  let I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro w ⟨x, y, hx, hy, hmem, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  have hf := hz i
  rw [← map_mul] at hf
  have hroot := MvPolynomial.mem_vanishingIdeal_iff.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp hf) (joinPoints x y) ⟨x, y, hx, hy, hmem, rfl⟩
  rw [map_mul, MvPolynomial.aeval_X] at hroot
  have hroot' : x i * MvPolynomial.aeval (joinPoints x y) f = 0 := by
    simpa [joinPoints] using hroot
  exact (mul_eq_zero.mp hroot').resolve_left hi

omit he hh hd R in
theorem closed_pair_parameter_minors {n : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint (n + n)))
    (hT : ∀ p q, (p, q) ∈ T → ∃ t : ℂ, firstPoint q.rep = t • p.rep)
    (i j : Fin n) :
    Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (closedPairs T)))
        (MvPolynomial.X (Fin.castAdd (n + n) i)) *
      Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (closedPairs T)))
        (MvPolynomial.X (Fin.natAdd n (Fin.castAdd n j))) =
    Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (closedPairs T)))
        (MvPolynomial.X (Fin.castAdd (n + n) j)) *
      Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (closedPairs T)))
        (MvPolynomial.X (Fin.natAdd n (Fin.castAdd n i))) := by
  let F : Poly (n * (n + n)) :=
    MvPolynomial.X (finProdFinEquiv (i, Fin.castAdd n j)) -
      MvPolynomial.X (finProdFinEquiv (j, Fin.castAdd n i))
  have hF : F ∈ (pairClosure T).ideal := by
    change F ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives {w | ∃ p q, (p, q) ∈ T ∧ segrePoint p q = w})
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro w ⟨hw, hwmem⟩
    obtain ⟨p, q, hpq, heq⟩ := hwmem
    obtain ⟨t, ht⟩ := hT p q hpq
    have hpoint : Projectivization.mk ℂ w hw =
        Projectivization.mk ℂ (segreVector p.rep q.rep)
          (segreVector_ne_zero _ _ p.rep_nonzero q.rep_nonzero) := heq.symm
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hpoint
    rw [← hc]
    have hi := congrFun ht i
    have hj := congrFun ht j
    simp only [firstPoint, Pi.smul_apply, smul_eq_mul] at hi hj
    simp only [F, map_sub, MvPolynomial.aeval_X, Pi.smul_apply, smul_eq_mul,
      segreVector, Equiv.symm_apply_apply]
    rw [hi, hj]
    ring
  have hzero := congrArg (HilbertDegree.segreQuotient T)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hF)
  rw [HilbertDegree.segreQuotient_mk, map_zero] at hzero
  have h := hzero
  simp only [F, HilbertDegree.segrePullback, map_sub, MvPolynomial.aeval_X,
    Equiv.symm_apply_apply, map_mul, sub_eq_zero] at h
  exact h

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local instance : AddRightCancelMonoid (Fin 2 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 2 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

omit he hh hd R in
/-- Positive direction degree admits homogeneous coefficients after extracting direction variables. -/
theorem positive_pair_polynomial_decomposition {n m : ℕ} (s t : ℕ) (hs : 1 ≤ s)
    (f : Poly (n + m))
    (hf : f ∈ MvPolynomial.restrictSupport ℂ {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
        (∑ j : Fin m, d (Fin.natAdd n j)) = t}) :
    ∃ g : Fin n → Poly (n + m),
      (∀ i, g i ∈ MvPolynomial.restrictSupport ℂ {d : Fin (n + m) →₀ ℕ |
        (∑ i : Fin n, d (Fin.castAdd m i)) = s - 1 ∧
          (∑ j : Fin m, d (Fin.natAdd n j)) = t}) ∧
        f = ∑ i, MvPolynomial.X (Fin.castAdd m i) * g i := by
  classical
  let P := MvPolynomial (Fin (n + m)) ℂ
  let d : Fin n → P := fun i => MvPolynomial.X (Fin.castAdd m i)
  let I : Ideal P := Ideal.span (Set.range d)
  have himage : Set.range d =
      MvPolynomial.X '' Set.range (Fin.castAdd m : Fin n → Fin (n + m)) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨j, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hfI : f ∈ I := by
    dsimp only [I]
    rw [himage]
    apply MvPolynomial.mem_ideal_span_X_image.mpr
    intro a ha
    have hsupport : (f.support : Set (Fin (n + m) →₀ ℕ)) ⊆
        {a | (∑ i : Fin n, a (Fin.castAdd m i)) = s ∧
          (∑ j : Fin m, a (Fin.natAdd n j)) = t} := hf
    obtain ⟨i, hi⟩ : ∃ i : Fin n, a (Fin.castAdd m i) ≠ 0 := by
      by_contra h
      push Not at h
      have hz : (∑ i : Fin n, a (Fin.castAdd m i)) = 0 := Finset.sum_eq_zero (fun i _ => h i)
      have hleft := (hsupport ha).1
      omega
    exact ⟨Fin.castAdd m i, ⟨i, rfl⟩, hi⟩
  let D := Fintype.linearCombination P d
  have hrange : LinearMap.range D = I := Fintype.range_linearCombination P d
  have hfRange : f ∈ LinearMap.range D := by rw [hrange]; exact hfI
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hfRange
  let w := HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)
  let Φ := MvPolynomial.weightedHomogeneousSubmodule ℂ w
  let β := HilbertMulti.pairDegree (s - 1) t
  let α := HilbertMulti.pairDegree 1 0
  let γ := HilbertMulti.pairDegree s t
  have hγ : γ = β + α := by
    ext j
    fin_cases j <;> simp [γ, β, α, HilbertMulti.pairDegree] <;> omega
  have hhom : f ∈ Φ γ := by
    dsimp only [Φ, w, γ]
    rw [HilbertMulti.pairBlockPiece n m s t]
    exact hf
  have hd (i : Fin n) : d i ∈ Φ α := by
    have h := MvPolynomial.isWeightedHomogeneous_X ℂ w (Fin.castAdd m i)
    have hw : w (Fin.castAdd m i) = α := by
      ext j
      fin_cases j <;> simp [w, α, HilbertMulti.blockWeight, HilbertMulti.pairBlocks,
        HilbertMulti.pairDegree]
    dsimp only [Φ]
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    simpa only [hw, d] using h
  let g : Fin n → P := fun i => DirectSum.decompose Φ (c i) β
  refine ⟨g, ?_, ?_⟩
  · intro i
    rw [← HilbertMulti.pairBlockPiece]
    exact (DirectSum.decompose Φ (c i) β).property
  · calc
      f = (DirectSum.decompose Φ f γ : P) :=
        (DirectSum.decompose_of_mem_same Φ hhom).symm
      _ = (DirectSum.decompose Φ (D c) γ : P) := by rw [hc]
      _ = ∑ i, (DirectSum.decompose Φ (c i * d i) γ : P) := by
        simp only [D, Fintype.linearCombination_apply, smul_eq_mul, DirectSum.decompose_sum,
          DirectSum.sum_apply, Submodule.coe_sum]
      _ = ∑ i, MvPolynomial.X (Fin.castAdd m i) * g i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hγ, DirectSum.coe_decompose_mul_add_of_right_mem Φ (hd i)]
        exact mul_comm _ _

omit he hh hd R in
theorem lifted_pairs_parallel (p : ProjectivePoint e) (q : ProjectivePoint (e + e))
    (hpq : (p, q) ∈ liftedParameterPairs C Γ H) :
    ∃ t : ℂ, firstPoint q.rep = t • p.rep := by
  obtain ⟨z, v, hmem, hv, rfl, rfl⟩ := hpq
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (graphVector C z v) (graphVector_ne_zero C z v hv)
  have ha' : (Projectivization.mk ℂ v hv).rep = (a : ℂ) • v := by
    simpa only [Units.smul_def] using ha.symm
  have hb' : (graphParameter C z v hv).rep = (b : ℂ) • graphVector C z v := by
    simpa only [graphParameter, Units.smul_def] using hb.symm
  refine ⟨(b : ℂ) * (↑a⁻¹ : ℂ), ?_⟩
  funext i
  simp [firstPoint, hb', ha', graphVector, joinPoints, Pi.smul_apply, smul_eq_mul, mul_assoc]

omit he hh hd R in
theorem lifted_pairs_orthogonal (p : ProjectivePoint e) (q : ProjectivePoint (e + e))
    (hpq : (p, q) ∈ liftedParameterPairs C Γ H) :
    covectorOfPoint (secondPoint q.rep) p.rep = 0 := by
  have hparallel := lifted_pairs_parallel C Γ H p q hpq
  obtain ⟨z, v, hmem, hv, rfl, rfl⟩ := hpq
  obtain ⟨t, ht⟩ := hparallel
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (graphVector C z v) (graphVector_ne_zero C z v hv)
  have hb' : (graphParameter C z v hv).rep = (b : ℂ) • graphVector C z v := by
    simpa only [graphParameter, Units.smul_def] using hb.symm
  have hfirst : firstPoint (graphParameter C z v hv).rep = (b : ℂ) • v := by
    ext i
    simp [firstPoint, hb', graphVector, joinPoints, Pi.smul_apply, smul_eq_mul]
  have hfirstne : firstPoint (graphParameter C z v hv).rep ≠ 0 := by
    rw [hfirst]
    exact smul_ne_zero b.ne_zero hv
  have hinc : ∃ d : ProjectivePoint e, incidenceCondition C d (graphParameter C z v hv)
      (affineEmbedding z) := by
    change graphParameter C z v hv ∈ {p | ∃ d, incidenceCondition C d p (affineEmbedding z)}
    rw [full_point_fiber C z]
    exact ⟨v, hv, rfl⟩
  obtain ⟨d, u, hu, hy, hpoint⟩ := hinc
  have hyfirst : covectorOfPoint (secondPoint (graphParameter C z v hv).rep)
      (firstPoint (graphParameter C z v hv).rep) = 0 := by
    rw [hu, map_smul, hy, smul_zero]
  have htne : t ≠ 0 := by
    intro htzero
    apply hfirstne
    rw [ht, htzero, zero_smul]
  rw [ht, map_smul] at hyfirst
  exact (smul_eq_zero.mp hyfirst).resolve_left htne

omit he hh hd R in
theorem closed_pair_orthogonal_relation {n : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint (n + n)))
    (hT : ∀ p q, (p, q) ∈ T → covectorOfPoint (secondPoint q.rep) p.rep = 0) :
    (∑ i : Fin n,
      Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (closedPairs T)))
          (MvPolynomial.X (Fin.castAdd (n + n) i)) *
        Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (closedPairs T)))
          (MvPolynomial.X (Fin.natAdd n (Fin.natAdd n i)))) = 0 := by
  let F : Poly (n * (n + n)) :=
    ∑ i : Fin n, MvPolynomial.X (finProdFinEquiv (i, Fin.natAdd n i))
  have hF : F ∈ (pairClosure T).ideal := by
    change F ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives {w | ∃ p q, (p, q) ∈ T ∧ segrePoint p q = w})
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro w ⟨hw, hwmem⟩
    obtain ⟨p, q, hpq, heq⟩ := hwmem
    have hy := hT p q hpq
    have hpoint : Projectivization.mk ℂ w hw =
        Projectivization.mk ℂ (segreVector p.rep q.rep)
          (segreVector_ne_zero _ _ p.rep_nonzero q.rep_nonzero) := heq.symm
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hpoint
    rw [← hc]
    have hy' : (∑ i : Fin n, q.rep (Fin.natAdd n i) * p.rep i) = 0 := by
      simpa [covectorOfPoint, secondPoint, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, smul_eq_mul] using hy
    simp only [F, map_sum, MvPolynomial.aeval_X, Pi.smul_apply, smul_eq_mul,
      segreVector, Equiv.symm_apply_apply]
    calc
      (∑ i, c * (p.rep i * q.rep (Fin.natAdd n i))) =
          c * ∑ i, q.rep (Fin.natAdd n i) * p.rep i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hy', mul_zero]
  have hzero := congrArg (HilbertDegree.segreQuotient T)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hF)
  rw [HilbertDegree.segreQuotient_mk, map_zero] at hzero
  simpa only [F, HilbertDegree.segrePullback, map_sum, MvPolynomial.aeval_X,
    Equiv.symm_apply_apply, map_mul] using hzero

omit he hh hd R in
/-- The negative-degree parameter scalar exists on the actual base's direction ideal. -/
theorem parameter_scalarRatio_exists :
    let I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H))
    let A := MvPolynomial (Fin (e + (e + e))) ℂ ⧸ I
    let d : Fin e → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X (Fin.castAdd (e + e) i))
    let v : Fin e → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X (Fin.natAdd e (Fin.castAdd e i)))
    ∃ τ : LinearMap.range (Fintype.linearCombination A d) →ₗ[A] A,
      ∀ c : Fin e → A,
        τ ⟨Fintype.linearCombination A d c, ⟨c, rfl⟩⟩ = Fintype.linearCombination A v c := by
  dsimp only
  apply IncidenceLocal.scalarRatio_on_directionIdeal
  · intro i j
    unfold liftedParameterBase
    exact closed_pair_parameter_minors (liftedParameterPairs C Γ H)
      (lifted_pairs_parallel C Γ H) i j
  · intro z hz
    exact directionCoordinates_joint_regular (liftedParameterBase C Γ H) z hz

omit he hh hd R in
set_option maxHeartbeats 1500000 in
/-- The actual parameter coordinates define the three-term complex used before exterior powers. -/
theorem parameter_complex_exists :
    let I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H))
    let A := MvPolynomial (Fin (e + (e + e))) ℂ ⧸ I
    let d : Fin e → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X (Fin.castAdd (e + e) i))
    let v : Fin e → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X (Fin.natAdd e (Fin.castAdd e i)))
    let y : Fin e → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X (Fin.natAdd e (Fin.natAdd e i)))
    let D := Fintype.linearCombination A d
    ∃ τ : LinearMap.range D →ₗ[A] A,
      ∃ δ : A →ₗ[A] (LinearMap.range D × (Fin e → A)),
        ∃ ψ : (LinearMap.range D × (Fin e → A)) →ₗ[A] A,
          Function.Injective δ ∧ ψ.comp δ = 0 ∧
            (∀ z, (δ z).1 = 0 ∧ ∀ i, (δ z).2 i = d i * z) ∧
            (∀ x, ψ x = τ x.1 + Fintype.linearCombination A y x.2) ∧
            (∀ c : Fin e → A, τ ⟨D c, ⟨c, rfl⟩⟩ = Fintype.linearCombination A v c) := by
  let I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H))
  let A := MvPolynomial (Fin (e + (e + e))) ℂ ⧸ I
  let d : Fin e → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X (Fin.castAdd (e + e) i))
  let v : Fin e → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X (Fin.natAdd e (Fin.castAdd e i)))
  let y : Fin e → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X (Fin.natAdd e (Fin.natAdd e i)))
  let D := Fintype.linearCombination A d
  obtain ⟨τ, hτ⟩ := parameter_scalarRatio_exists C Γ H
  let δ : A →ₗ[A] (LinearMap.range D × (Fin e → A)) :=
    { toFun := fun z => (0, fun i => d i * z)
      map_add' := by
        intro z w
        apply Prod.ext
        · simp
        · funext i
          exact mul_add _ _ _
      map_smul' := by
        intro c z
        apply Prod.ext
        · simp
        · funext i
          change d i * (c * z) = c * (d i * z)
          ring }
  let ψ : (LinearMap.range D × (Fin e → A)) →ₗ[A] A :=
    τ.coprod (Fintype.linearCombination A y)
  have horth : (∑ i, d i * y i) = 0 := by
    unfold d y I liftedParameterBase
    exact closed_pair_orthogonal_relation (liftedParameterPairs C Γ H)
      (lifted_pairs_orthogonal C Γ H)
  refine ⟨τ, δ, ψ, ?_, ?_, ?_, ?_, hτ⟩
  · intro z w heq
    have hzero : z - w = 0 := by
      apply directionCoordinates_joint_regular (liftedParameterBase C Γ H)
      intro i
      have h := congrArg (fun x : LinearMap.range D × (Fin e → A) => x.2 i) heq
      change d i * z = d i * w at h
      change d i * (z - w) = 0
      rw [mul_sub, h, sub_self]
    exact sub_eq_zero.mp hzero
  · apply LinearMap.ext
    intro z
    change τ 0 + Fintype.linearCombination A y (fun i => d i * z) = 0
    rw [map_zero, zero_add]
    simp only [Fintype.linearCombination_apply, smul_eq_mul]
    calc
      (∑ i, d i * z * y i) = (∑ i, d i * y i) * z := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [horth, zero_mul]
  · intro z
    exact ⟨rfl, fun _ => rfl⟩
  · intro x
    rfl

end IncidenceSections

#print axioms IncidenceLocal.scalarRatio_coordinate_range
#print axioms IncidenceSections.parameter_complex_exists
#print axioms IncidenceSections.parameter_scalarRatio_exists
#print axioms IncidenceSections.positive_pair_polynomial_decomposition

namespace KoszulEval

omit he hh hd R in
/-- Evaluation of the shifted base polynomial at a triple point. -/
theorem shiftedBaseHilbert_eval (H : BaseHilbertPolynomial) (da dell : ℤ)
    (v : Fin 3 → ℚ) :
    MvPolynomial.eval v (shiftedBaseHilbert H da dell) =
      MvPolynomial.eval (fun i : Fin 2 => ![v 0 + (da : ℚ), v 1 + (dell : ℚ)] i) H := by
  unfold shiftedBaseHilbert
  show MvPolynomial.eval₂Hom _ _ _ = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  have hpt : (fun i : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℚ) v
      (if i = 0 then MvPolynomial.X (0 : Fin 3) + MvPolynomial.C (da : ℚ)
      else MvPolynomial.X (1 : Fin 3) + MvPolynomial.C (dell : ℚ))) =
      (fun i : Fin 2 => ![v 0 + (da : ℚ), v 1 + (dell : ℚ)] i) := by
    funext i
    fin_cases i <;> simp
  rw [hpt, show MvPolynomial.eval₂Hom (RingHom.id ℚ)
      (fun i : Fin 2 => ![v 0 + (da : ℚ), v 1 + (dell : ℚ)] i) =
      MvPolynomial.eval (fun i : Fin 2 => ![v 0 + (da : ℚ), v 1 + (dell : ℚ)] i)
      from rfl]

omit he hh hd R in
/-- A shifted product of consecutive values is a descending factorial. -/
theorem prod_range_add_eq_descFactorial (w n : ℕ) :
    ∏ k ∈ Finset.range n, ((w + n - k : ℕ) : ℚ) =
      (((w + n).descFactorial n : ℕ) : ℚ) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Nat.descFactorial_succ]
    have hterm : ((w + (n + 1) - n : ℕ) : ℚ) = ((w + 1 : ℕ) : ℚ) := by
      congr 1
      omega
    have hprod : ∏ k ∈ Finset.range n, ((w + (n + 1) - k : ℕ) : ℚ) =
        ∏ k ∈ Finset.range n, ((((w + 1) + n - k : ℕ)) : ℚ) := by
      apply Finset.prod_congr rfl
      intro k hk
      congr 1
      omega
    rw [hterm, hprod, ih]
    have hcast : ((((w + (n + 1) - n) * (w + (n + 1)).descFactorial n : ℕ)) : ℚ) =
        ((w + 1 : ℕ) : ℚ) * ((((w + 1) + n).descFactorial n : ℕ) : ℚ) := by
      have h1 : w + (n + 1) - n = w + 1 := by omega
      have h2 : w + (n + 1) = (w + 1) + n := by omega
      rw [h1, h2]
      push_cast
      ring
    rw [hcast]
    ring

omit he hh hd R in
/-- Evaluation of the rational projective binomial factor is a binomial count. -/
theorem shiftedProjectiveHilbert_eval (n m u : ℕ) (hm : m ≤ u)
    (s t : ℚ) :
    MvPolynomial.eval (Fin.cons s (Fin.cons t (fun _ : Fin 1 => (u : ℚ))))
      (shiftedProjectiveHilbert n m) =
      ((Nat.choose (u - m + n) n : ℕ) : ℚ) := by
  unfold shiftedProjectiveHilbert
  have hfac : ∀ k ∈ Finset.range n,
      MvPolynomial.eval (Fin.cons s (Fin.cons t (fun _ : Fin 1 => (u : ℚ))))
        (MvPolynomial.X (2 : Fin 3) + MvPolynomial.C ((n : ℚ) - (m : ℚ) - (k : ℚ))) =
        (((u - m + n - k : ℕ)) : ℚ) := by
    intro k hk
    have hkN : k < n := Finset.mem_range.mp hk
    rw [map_add, MvPolynomial.eval_X, MvPolynomial.eval_C]
    have hpoint : (Fin.cons (α := fun _ => ℚ) s
        (Fin.cons (α := fun _ => ℚ) t (fun _ : Fin 1 => (u : ℚ)))) (2 : Fin 3) =
        (u : ℚ) := by
      rfl
    rw [hpoint]
    have hcast : (u : ℚ) + ((n : ℚ) - (m : ℚ) - (k : ℚ)) =
        (((u - m + n - k : ℕ)) : ℚ) := by
      have h1 : (u : ℚ) - (m : ℚ) = (((u - m : ℕ)) : ℚ) := by
        rw [Nat.cast_sub hm]
      have h2 : u - m + n - k = (u - m) + (n - k) := by omega
      rw [h2]
      have h3 : (n : ℚ) - (k : ℚ) = (((n - k : ℕ)) : ℚ) := by
        rw [Nat.cast_sub (Nat.le_of_lt hkN)]
      have h4 : (((u - m + (n - k) : ℕ)) : ℚ) =
          (((u - m : ℕ)) : ℚ) + (((n - k : ℕ)) : ℚ) := by
        rw [Nat.cast_add]
      rw [h4, ← h1, ← h3]
      ring
    exact hcast
  rw [map_mul, MvPolynomial.eval_C, map_prod,
    Finset.prod_congr rfl (fun k hk => hfac k hk)]
  rw [prod_range_add_eq_descFactorial (u - m) n]
  have hfact : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hdesc : (((u - m + n).descFactorial n : ℕ) : ℚ) =
      ((Nat.choose (u - m + n) n : ℕ) : ℚ) * (n.factorial : ℚ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  rw [hdesc]
  field_simp

omit he hh hd R in
/-- Evaluation of one exterior-power piece at a triple point. -/
theorem exteriorHilbertTerm_eval (e m : ℕ) (H : BaseHilbertPolynomial)
    (v : Fin 3 → ℚ) :
    MvPolynomial.eval v (exteriorHilbertTerm e m H) =
      ∑ delta ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
        ∑ l ∈ Finset.range (m + 1), ∑ beta ∈ Finset.range (m + 1),
          if delta + k + l + beta = m then
            ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)) *
              MvPolynomial.eval (fun i : Fin 2 =>
                ![v 0 + (-((k + 2 * l + beta : ℕ) : ℤ) : ℚ),
                  v 1 + ((beta : ℕ) : ℚ)] i) H
          else 0 := by
  unfold exteriorHilbertTerm
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro delta _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro beta _
  split_ifs with hc
  · rw [map_mul, MvPolynomial.eval_C, shiftedBaseHilbert_eval]
    congr 1
  · exact map_zero _

omit he hh hd R in
/-- Evaluation of the Koszul transform at a triple point. -/
theorem koszulIncidenceHilbert_eval (e : ℕ) (H : BaseHilbertPolynomial)
    (v : Fin 3 → ℚ) :
    MvPolynomial.eval v (koszulIncidenceHilbert e H) =
      ∑ m ∈ Finset.range e, (-1 : ℚ) ^ m *
        (∑ delta ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
          ∑ l ∈ Finset.range (m + 1), ∑ beta ∈ Finset.range (m + 1),
            if delta + k + l + beta = m then
              ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)) *
                MvPolynomial.eval (fun i : Fin 2 =>
                  ![v 0 + (-((k + 2 * l + beta : ℕ) : ℤ) : ℚ),
                    v 1 + ((beta : ℕ) : ℚ)] i) H
            else 0) *
        MvPolynomial.eval v (shiftedProjectiveHilbert (e.choose 2) m) := by
  unfold koszulIncidenceHilbert
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [map_mul, MvPolynomial.eval_C, exteriorHilbertTerm_eval, mul_assoc]

omit he hh hd R in
/-- Evaluation of the Koszul transform at a natural triple point. -/
theorem koszulIncidenceHilbert_eval_at (e : ℕ) (H : BaseHilbertPolynomial)
    (s t u : ℕ) :
    MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ))))
      (koszulIncidenceHilbert e H) =
      ∑ m ∈ Finset.range e, (-1 : ℚ) ^ m *
        (∑ delta ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
          ∑ l ∈ Finset.range (m + 1), ∑ beta ∈ Finset.range (m + 1),
            if delta + k + l + beta = m then
              ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)) *
                MvPolynomial.eval (fun i : Fin 2 =>
                  ![(s : ℚ) + (-((k + 2 * l + beta : ℕ) : ℤ) : ℚ),
                    (t : ℚ) + ((beta : ℕ) : ℚ)] i) H
            else 0) *
        MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ))))
          (shiftedProjectiveHilbert (e.choose 2) m) := by
  have hv0 : (Fin.cons (α := fun _ => ℚ) (s : ℚ)
      (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ)))) 0 = (s : ℚ) := rfl
  have hv1 : (Fin.cons (α := fun _ => ℚ) (s : ℚ)
      (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ)))) 1 = (t : ℚ) := rfl
  rw [koszulIncidenceHilbert_eval]
  simp only [hv0, hv1]

omit he hh hd R in
/-- For large arguments the Koszul transform evaluates to base ranks. -/
theorem koszul_eval_eq_pair_ranks {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (s t u : ℕ) (NP : ℕ)
    (hP : ∀ a b : ℕ, NP ≤ a → NP ≤ b →
      MvPolynomial.eval (Fin.cons (a : ℚ) (fun _ : Fin 1 => (b : ℚ)))
        (parameterBaseHilbert C Γ H) = ((pairHilbert (liftedParameterBase C Γ H) a b : ℕ) : ℚ))
    (hs : NP + 2 * e ≤ s) (ht : NP ≤ t) (hu : e ≤ u) :
    MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ))))
      (koszulIncidenceHilbert e (parameterBaseHilbert C Γ H)) =
      ∑ m ∈ Finset.range e, (-1 : ℚ) ^ m *
        (∑ delta ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
          ∑ l ∈ Finset.range (m + 1), ∑ beta ∈ Finset.range (m + 1),
            if delta + k + l + beta = m then
              ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)) *
                ((pairHilbert (liftedParameterBase C Γ H) (s - k - 2 * l - beta) (t + beta) : ℕ) : ℚ)
            else 0) *
        ((Nat.choose (u - m + e.choose 2) (e.choose 2) : ℕ) : ℚ) := by
  rw [koszulIncidenceHilbert_eval_at]
  apply Finset.sum_congr rfl
  intro m hm
  have hme : m < e := Finset.mem_range.mp hm
  have hmu : m ≤ u := le_trans (Nat.le_of_lt hme) hu
  rw [shiftedProjectiveHilbert_eval _ _ _ hmu]
  have hE3 : (∑ delta ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
        ∑ l ∈ Finset.range (m + 1), ∑ beta ∈ Finset.range (m + 1),
          if delta + k + l + beta = m then
            ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)) *
              MvPolynomial.eval (fun i : Fin 2 =>
                ![(s : ℚ) + (-((k + 2 * l + beta : ℕ) : ℤ) : ℚ),
                  (t : ℚ) + ((beta : ℕ) : ℚ)] i)
              (parameterBaseHilbert C Γ H)
          else 0) =
      (∑ delta ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
        ∑ l ∈ Finset.range (m + 1), ∑ beta ∈ Finset.range (m + 1),
          if delta + k + l + beta = m then
            ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)) *
              ((pairHilbert (liftedParameterBase C Γ H) (s - k - 2 * l - beta) (t + beta) : ℕ) : ℚ)
          else 0) := by
    apply Finset.sum_congr rfl
    intro delta _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro beta _
    split_ifs with hc
    · have hshift : (fun i : Fin 2 =>
            ![(s : ℚ) + (-((k + 2 * l + beta : ℕ) : ℤ) : ℚ),
              (t : ℚ) + ((beta : ℕ) : ℚ)] i) =
          Fin.cons ((((s - k - 2 * l - beta : ℕ)) : ℚ))
            (fun _ : Fin 1 => ((((t + beta : ℕ)) : ℚ))) := by
        ext i
        fin_cases i
        · show (s : ℚ) + (-((k + 2 * l + beta : ℕ) : ℤ) : ℚ) =
              (((s - k - 2 * l - beta : ℕ)) : ℚ)
          have hle : k + 2 * l + beta ≤ s := by omega
          have hq : (-((k + 2 * l + beta : ℕ) : ℤ) : ℚ) =
              -((((k + 2 * l + beta : ℕ))) : ℚ) := by
            push_cast
            ring
          have hsub : s - k - 2 * l - beta = s - (k + 2 * l + beta) := by omega
          rw [hq, hsub, Nat.cast_sub hle]
          ring
        · show (t : ℚ) + ((beta : ℕ) : ℚ) = (((t + beta : ℕ)) : ℚ)
          rw [Nat.cast_add]
      have hNPs : NP ≤ s - k - 2 * l - beta := by omega
      have hNPt : NP ≤ t + beta := by omega
      congr 1
      rw [hshift]
      exact hP _ _ hNPs hNPt
    · rfl
  rw [hE3]

end KoszulEval

namespace FiberEquations

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local instance : AddRightCancelMonoid (Fin 2 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 2 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

local instance : AddRightCancelMonoid (Fin 3 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 3 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

omit V Γ H a he hh hd R h j N in
/-- Fiber equation for chart `i0` and test covector index `w`.
Tridegree `(1,1,1)`. Structure constants follow `rulingGraphPolynomials`
(ParameterImageSupport.lean:19-55). -/
def fiberPolynomial {e : ℕ} (C : SkewCoordinates e) (i0 w : Fin e) :
    Poly (e + (e + e) + (skewDim e + 1)) :=
  MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.castAdd e i0))) *
    (∑ k : Fin (skewDim e), ∑ l : Fin e,
      MvPolynomial.C ((((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single w 1))) *
        MvPolynomial.X (Fin.natAdd (e + (e + e)) (Fin.succ k)) *
        MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l))) -
  MvPolynomial.X (Fin.natAdd (e + (e + e)) (0 : Fin (skewDim e + 1))) *
    MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.natAdd e w))) *
    MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i0))

omit V Γ H a he hh hd R h j N in
/-- Evaluation at a joined representative triple, by `Pi.basisFun.sum_repr`
expansion exactly as in `eval_rulingGraphPolynomials`. -/
theorem eval_fiberPolynomial {e : ℕ} (C : SkewCoordinates e)
    (i0 w : Fin e) (d_rep : Point e) (p_rep : Point (e + e))
    (x_rep : Point (skewDim e + 1)) :
    MvPolynomial.aeval (joinPoints (joinPoints d_rep p_rep) x_rep)
        (fiberPolynomial C i0 w) =
      (firstPoint p_rep i0) *
        (((C.decode (Fin.tail x_rep)).val d_rep) (Pi.single w 1)) -
      (x_rep 0) * ((covectorOfPoint (secondPoint p_rep)) (Pi.single w 1)) *
        (d_rep i0) := by
  classical
  have hdir : ∀ l : Fin e, MvPolynomial.aeval (joinPoints (joinPoints d_rep p_rep) x_rep)
      (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l)) :
        Poly (e + (e + e) + (skewDim e + 1))) =
      d_rep l := by
    intro l
    simp [joinPoints, Fin.addCases_left, Fin.addCases_right]
  have hV : MvPolynomial.aeval (joinPoints (joinPoints d_rep p_rep) x_rep)
      (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.castAdd e i0))) :
        Poly (e + (e + e) + (skewDim e + 1))) =
      firstPoint p_rep i0 := by
    simp [joinPoints, firstPoint, Fin.addCases_left, Fin.addCases_right]
  have hQ : MvPolynomial.aeval (joinPoints (joinPoints d_rep p_rep) x_rep)
      (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.natAdd e w))) :
        Poly (e + (e + e) + (skewDim e + 1))) =
      (secondPoint p_rep) w := by
    simp [joinPoints, secondPoint, Fin.addCases_left, Fin.addCases_right]
  have hX0 : MvPolynomial.aeval (joinPoints (joinPoints d_rep p_rep) x_rep)
      (MvPolynomial.X (Fin.natAdd (e + (e + e)) (0 : Fin (skewDim e + 1))) :
        Poly (e + (e + e) + (skewDim e + 1))) =
      x_rep 0 := by
    simp [joinPoints, Fin.addCases_left, Fin.addCases_right]
  have htail : ∀ k : Fin (skewDim e), MvPolynomial.aeval
      (joinPoints (joinPoints d_rep p_rep) x_rep)
      (MvPolynomial.X (Fin.natAdd (e + (e + e)) (Fin.succ k)) :
        Poly (e + (e + e) + (skewDim e + 1))) =
      (Fin.tail x_rep) k := by
    intro k
    have htk : (Fin.tail x_rep) k = x_rep k.succ := rfl
    simp [joinPoints, Fin.addCases_left, Fin.addCases_right, htk]
  have hz : Fin.tail x_rep =
      ∑ k : Fin (skewDim e), (Fin.tail x_rep k) • (Pi.single k (1 : ℂ) : Point (skewDim e)) := by
    simpa using ((Pi.basisFun ℂ (Fin (skewDim e))).sum_repr (Fin.tail x_rep)).symm
  have hd : d_rep = ∑ l : Fin e, (d_rep l) • (Pi.single l (1 : ℂ) : Point e) := by
    simpa using ((Pi.basisFun ℂ (Fin e)).sum_repr d_rep).symm
  have heval : (((C.decode (Fin.tail x_rep)).val d_rep) (Pi.single w 1)) =
      ∑ k : Fin (skewDim e), ∑ l : Fin e,
        (((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single w 1)) *
          (Fin.tail x_rep k) * (d_rep l) := by
    conv_lhs => rw [hz, hd]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hcov : (covectorOfPoint (secondPoint p_rep)) (Pi.single w 1) =
      (secondPoint p_rep) w := by
    simp [covectorOfPoint, Pi.single_apply]
  unfold fiberPolynomial
  simpa only [map_sub, map_mul, map_sum, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    hdir, hV, hQ, hX0, htail, hcov, Algebra.algebraMap_self,
    RingHom.id_apply, ← heval]

omit V a he hh hd R h j N in
/-- The fiber equations vanish on the actual incidence triples.
From `incidenceCondition_mk_iff` + `mem_span_singleton`: write `x0 = c*t`,
`D.val d = c * y` with `v = t*d`; then
`v_i0 * (c*y_w) - (c*t)*y_w*d_i0 = 0` by ring. No case split on `t`
(`t = 0` gives `v_i0 = 0`, `x0 = 0`). -/
theorem fiberPolynomial_mem_vanishingIdeal {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (i0 w : Fin e) :
    fiberPolynomial C i0 w ∈ MvPolynomial.vanishingIdeal ℂ
      (tripleRepresentatives (incidenceTriples C Γ H)) := by
  classical
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro w_rep ⟨xd, xp, xx, hxd, hxp, hxx, hmem, rfl⟩
  obtain ⟨_, hinc⟩ := hmem
  rw [incidenceCondition_mk_iff C xd xp xx hxd hxp hxx] at hinc
  obtain ⟨t, hfirst, _, hfiber⟩ := hinc
  change homogeneousEvaluation xd (xx 0, C.decode (Fin.tail xx)) ∈
    Submodule.span ℂ {(t, covectorOfPoint (secondPoint xp))} at hfiber
  rw [Submodule.mem_span_singleton] at hfiber
  obtain ⟨c, hc⟩ := hfiber
  have hxx0 : xx 0 = c * t := by
    have h := congrArg Prod.fst hc
    change c * t = xx 0 at h
    exact h.symm
  have hD : c • (covectorOfPoint (secondPoint xp)) =
      (C.decode (Fin.tail xx)).val xd := by
    have h := congrArg Prod.snd hc
    simpa [homogeneousEvaluation, alternatingEvaluation] using h
  have hvi0 : firstPoint xp i0 = t * xd i0 := by
    have h := congrFun hfirst i0
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have hDw : (((C.decode (Fin.tail xx)).val xd) (Pi.single w 1)) =
      c * ((covectorOfPoint (secondPoint xp)) (Pi.single w 1)) := by
    have h := congrArg (fun f : Module.Dual ℂ (Point e) => f (Pi.single w 1)) hD
    simpa [LinearMap.smul_apply, smul_eq_mul] using h.symm
  rw [eval_fiberPolynomial C i0 w xd xp xx, hvi0, hDw, hxx0]
  ring

omit V Γ H a he hh hd R h j N in
/-- Tridegree of the fiber equations, for the multigraded colon machinery.
Follows `HilbertDegree.diagonalMonomial_weighted`. -/
theorem fiberPolynomial_weighted {e : ℕ} (C : SkewCoordinates e) (i0 w : Fin e) :
    (fiberPolynomial C i0 w).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (HilbertMulti.tripleDegree 1 1 1) := by
  classical
  have wdir : ∀ l : Fin e,
      HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))
        (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l)) =
      HilbertMulti.tripleDegree 1 0 0 := by
    intro l
    ext j
    fin_cases j <;>
      simp [HilbertMulti.blockWeight, HilbertMulti.tripleBlocks, HilbertMulti.tripleDegree]
  have wpar : ∀ i : Fin (e + e),
      HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))
        (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i)) =
      HilbertMulti.tripleDegree 0 1 0 := by
    intro i
    ext j
    fin_cases j <;>
      simp [HilbertMulti.blockWeight, HilbertMulti.tripleBlocks, HilbertMulti.tripleDegree]
  have wpt : ∀ k : Fin (skewDim e + 1),
      HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))
        (Fin.natAdd (e + (e + e)) k) =
      HilbertMulti.tripleDegree 0 0 1 := by
    intro k
    ext j
    fin_cases j <;>
      simp [HilbertMulti.blockWeight, HilbertMulti.tripleBlocks, HilbertMulti.tripleDegree]
  have hadd1 : HilbertMulti.tripleDegree 0 0 1 + HilbertMulti.tripleDegree 1 0 0 =
      HilbertMulti.tripleDegree 1 0 1 := by
    ext j
    fin_cases j <;>
      simp [HilbertMulti.tripleDegree]
  have hadd2 : HilbertMulti.tripleDegree 0 1 0 + HilbertMulti.tripleDegree 1 0 1 =
      HilbertMulti.tripleDegree 1 1 1 := by
    ext j
    fin_cases j <;>
      simp [HilbertMulti.tripleDegree]
  have hadd3 : HilbertMulti.tripleDegree 0 0 1 + HilbertMulti.tripleDegree 0 1 0 =
      HilbertMulti.tripleDegree 0 1 1 := by
    ext j
    fin_cases j <;>
      simp [HilbertMulti.tripleDegree]
  have hadd4 : HilbertMulti.tripleDegree 0 1 1 + HilbertMulti.tripleDegree 1 0 0 =
      HilbertMulti.tripleDegree 1 1 1 := by
    ext j
    fin_cases j <;>
      simp [HilbertMulti.tripleDegree]
  have hXdir : ∀ l : Fin e, (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l)) :
      Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (HilbertMulti.tripleDegree 1 0 0) := by
    intro l
    have h := MvPolynomial.isWeightedHomogeneous_X ℂ
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l))
    rwa [wdir l] at h
  have hXpar : ∀ i : Fin (e + e), (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i)) :
      Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (HilbertMulti.tripleDegree 0 1 0) := by
    intro i
    have h := MvPolynomial.isWeightedHomogeneous_X ℂ
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))
    rwa [wpar i] at h
  have hXpt : ∀ k : Fin (skewDim e + 1), (MvPolynomial.X (Fin.natAdd (e + (e + e)) k) :
      Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (HilbertMulti.tripleDegree 0 0 1) := by
    intro k
    have h := MvPolynomial.isWeightedHomogeneous_X ℂ
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (Fin.natAdd (e + (e + e)) k)
    rwa [wpt k] at h
  have hterm : ∀ k : Fin (skewDim e), ∀ l : Fin e,
      (MvPolynomial.C ((((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single w 1))) *
        MvPolynomial.X (Fin.natAdd (e + (e + e)) (Fin.succ k)) *
        MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l)) :
        Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (HilbertMulti.tripleDegree 1 0 1) := by
    intro k l
    have hC := MvPolynomial.isWeightedHomogeneous_C
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      ((((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single w 1)))
    have h := ((hC.mul (hXpt (Fin.succ k))).mul (hXdir l))
    simpa [hadd1, zero_add] using h
  have hS : (∑ k : Fin (skewDim e), ∑ l : Fin e,
      MvPolynomial.C ((((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single w 1))) *
        MvPolynomial.X (Fin.natAdd (e + (e + e)) (Fin.succ k)) *
        MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l)) :
      Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (HilbertMulti.tripleDegree 1 0 1) :=
    MvPolynomial.IsWeightedHomogeneous.sum _ _ _
      (fun k _ => MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun l _ => hterm k l))
  have hT1 : (MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.castAdd e i0))) *
      (∑ k : Fin (skewDim e), ∑ l : Fin e,
        MvPolynomial.C ((((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single w 1))) *
          MvPolynomial.X (Fin.natAdd (e + (e + e)) (Fin.succ k)) *
          MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l))) :
      Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (HilbertMulti.tripleDegree 1 1 1) := by
    have h := (hXpar (Fin.castAdd e i0)).mul hS
    simpa [hadd2] using h
  have hT2 : (MvPolynomial.X (Fin.natAdd (e + (e + e)) (0 : Fin (skewDim e + 1))) *
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.natAdd e (Fin.natAdd e w))) *
      MvPolynomial.X (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i0)) :
      Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (HilbertMulti.tripleDegree 1 1 1) := by
    have h := ((hXpt 0).mul (hXpar (Fin.natAdd e w))).mul (hXdir i0)
    simpa [hadd3, hadd4] using h
  unfold fiberPolynomial
  exact hT1.sub hT2

omit V a he hh hd R h j N in
/-- Pair relations pull back into the triple ideal, via the projection
`w.1 ∈ liftedParameterBase` in `incidenceTriples`. -/
theorem pairIdeal_map_le_tripleIdeal {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    Ideal.map (MvPolynomial.rename
      (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
      (MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H))) ≤
    MvPolynomial.vanishingIdeal ℂ
      (tripleRepresentatives (incidenceTriples C Γ H)) := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hgJ
  show MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) g ∈
    MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives (incidenceTriples C Γ H))
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro w_rep ⟨xd, xp, xx, hxd, hxp, hxx, hmem, rfl⟩
  obtain ⟨hbase, hinc⟩ := hmem
  have hbase' : (Projectivization.mk ℂ xd hxd, Projectivization.mk ℂ xp hxp) ∈
      liftedParameterBase C Γ H := hbase
  have hpair : joinPoints xd xp ∈ pairRepresentatives (liftedParameterBase C Γ H) :=
    ⟨xd, xp, hxd, hxp, hbase', rfl⟩
  have hg0 : MvPolynomial.aeval (joinPoints xd xp) g = 0 :=
    MvPolynomial.mem_vanishingIdeal_iff.mp hgJ _ hpair
  have hcomp : (joinPoints (joinPoints xd xp) xx) ∘
      (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) =
      joinPoints xd xp := by
    funext j
    simp [Function.comp_apply, joinPoints, Fin.addCases_left]
  calc MvPolynomial.aeval (joinPoints (joinPoints xd xp) xx)
        (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) g)
      = MvPolynomial.aeval
        ((joinPoints (joinPoints xd xp) xx) ∘ (Fin.castAdd (skewDim e + 1))) g := by
        rw [MvPolynomial.aeval_rename]
    _ = MvPolynomial.aeval (joinPoints xd xp) g := by rw [hcomp]
    _ = 0 := hg0

omit C V Γ H a he hh hd R h j N in
/-- Point monomial products are single monomials (bridge for support arguments). -/
theorem rprod_pt_eq_monomial (q : Fin (skewDim e + 1) →₀ ℕ) (t : Finset (Fin (skewDim e + 1))) :
    (∏ k ∈ t, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ q k : Poly (e + (e + e) + (skewDim e + 1))) =
      MvPolynomial.monomial (∑ k ∈ t, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) 1 := by
  classical
  induction t using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, MvPolynomial.monomial_zero', map_one]
  | @insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, ih,
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, mul_one]

omit C V Γ H a he hh hd R h j N in
theorem rpt_injective : Function.Injective (Fin.natAdd (e + (e + e)) : Fin (skewDim e + 1) → Fin (e + (e + e) + (skewDim e + 1))) := by
  intro k1 k2 h
  have hv := congrArg Fin.val h
  have e1 : (Fin.natAdd (e + (e + e)) k1).val = (e + (e + e)) + k1.val := rfl
  have e2 : (Fin.natAdd (e + (e + e)) k2).val = (e + (e + e)) + k2.val := rfl
  rw [e1, e2] at hv
  have hve : k1.val = k2.val := by omega
  exact Fin.ext hve

omit C V Γ H a he hh hd R h j N in
theorem rf0_injective : Function.Injective (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) :=
  Fin.castAdd_injective (e + (e + e)) (skewDim e + 1)

omit C V Γ H a he hh hd R h j N in
theorem rpt_notmem_range_rf0 (k0 : Fin (skewDim e + 1)) :
    Fin.natAdd (e + (e + e)) k0 ∉ Set.range (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) := by
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have e1 : (Fin.natAdd (e + (e + e)) k0).val = (e + (e + e)) + k0.val := rfl
  have e2 : (Fin.castAdd (skewDim e + 1) i).val = i.val := rfl
  rw [e1, e2] at hv
  have hi2 := i.2
  omega

omit C V Γ H a he hh hd R h j N in
theorem rmapDomain_pt_eq_zero (a : Fin (e + (e + e)) →₀ ℕ) (k0 : Fin (skewDim e + 1)) :
    (a.mapDomain (Fin.castAdd (skewDim e + 1))) (Fin.natAdd (e + (e + e)) k0) = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (rpt_notmem_range_rf0 k0)

omit C V Γ H a he hh hd R h j N in
theorem rptSum_eval (q : Fin (skewDim e + 1) →₀ ℕ) (k0 : Fin (skewDim e + 1)) :
    (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (Fin.natAdd (e + (e + e)) k0) = q k0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single k0]
  · simp [Finsupp.single_apply]
  · intro k _ hk
    simp only [Finsupp.single_apply]
    rw [ite_eq_right]
    intro hkk
    apply hk
    exact rpt_injective hkk
  · intro h
    exact absurd (Finset.mem_univ k0) h

omit C V Γ H a he hh hd R h j N in
theorem rsupp_third_eq (g : Poly (e + (e + e))) (q : Fin (skewDim e + 1) →₀ ℕ)
    (d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ)
    (hd : d ∈ ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) g) *
      (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ q k : Poly (e + (e + e) + (skewDim e + 1)))).support)
    (k0 : Fin (skewDim e + 1)) : d (Fin.natAdd (e + (e + e)) k0) = q k0 := by
  classical
  have hmq : (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ q k : Poly (e + (e + e) + (skewDim e + 1))) =
      MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) 1 :=
    rprod_pt_eq_monomial q Finset.univ
  have hmem := MvPolynomial.support_mul _ _ hd
  rw [Finset.mem_add] at hmem
  obtain ⟨d1, hd1, d2, hd2, rfl⟩ := hmem
  have hd1mem : d1 ∈ (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) g).support := hd1
  rw [MvPolynomial.support_rename_of_injective rf0_injective] at hd1mem
  rw [Finset.mem_image] at hd1mem
  obtain ⟨a, _, rfl⟩ := hd1mem
  have hd2mem : d2 ∈ (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ)).support := by
    rw [← hmq]
    exact hd2
  have hd2eq : d2 = ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k) :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd2mem)
  rw [Finsupp.add_apply, rmapDomain_pt_eq_zero, hd2eq, rptSum_eval, zero_add]

omit C V Γ H a he hh hd R h j N in
/-- Injectivity core for the pullback comparison map: a vanishing
point-monomial combination has all pair coefficients zero. -/
theorem rcore_inj (u : ℕ) [Fintype ↥{q : Fin (skewDim e + 1) →₀ ℕ | q.degree = u}]
    (g : ↥{q : Fin (skewDim e + 1) →₀ ℕ | q.degree = u} → Poly (e + (e + e)))
    (hsum : (∑ q ∈ Finset.univ, (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q)) *
      (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))) = 0) :
    ∀ q, g q = 0 := by
  classical
  intro q0
  have hT0 : (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q0)) *
      (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q0.val) k) : Poly (e + (e + e) + (skewDim e + 1))) = 0 := by
    by_contra hTne
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hTne
    have hdq0 : ∀ k0 : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) k0) = (q0.val) k0 :=
      rsupp_third_eq (g q0) (q0.val) d hd
    have hcoeff : ∀ q : ↥{q : Fin (skewDim e + 1) →₀ ℕ | q.degree = u}, q ≠ q0 →
        ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q)) *
          (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))).coeff d = 0 := by
      intro q hq
      have hdis : d ∉ ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q)) *
          (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))).support := by
        intro hmem
        apply hq
        apply Subtype.ext
        apply Finsupp.ext
        intro k0
        have h1 := rsupp_third_eq (g q) (q.val) d hmem k0
        have h2 := hdq0 k0
        rw [h1] at h2
        exact h2
      exact MvPolynomial.notMem_support_iff.mp hdis
    have hsumcoeff : ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q0)) *
        (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q0.val) k) : Poly (e + (e + e) + (skewDim e + 1)))).coeff d =
        (0 : Poly (e + (e + e) + (skewDim e + 1))).coeff d := by
      have h1 : (∑ q ∈ Finset.univ, (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q)) *
          (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))).coeff d =
          (0 : Poly (e + (e + e) + (skewDim e + 1))).coeff d :=
        congrArg (fun p : Poly (e + (e + e) + (skewDim e + 1)) => p.coeff d) hsum
      rw [MvPolynomial.coeff_sum] at h1
      have hsingle : (∑ q ∈ Finset.univ, ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q)) *
          (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))).coeff d) =
          ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q0)) *
            (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q0.val) k) : Poly (e + (e + e) + (skewDim e + 1)))).coeff d :=
        Finset.sum_eq_single q0 (fun q _ hq => hcoeff q hq) (fun h => absurd (Finset.mem_univ q0) h)
      rw [hsingle] at h1
      exact h1
    have hne : ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q0)) *
        (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q0.val) k) : Poly (e + (e + e) + (skewDim e + 1)))).coeff d ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hz : (0 : Poly (e + (e + e) + (skewDim e + 1))).coeff d = 0 := by simp
    rw [hz] at hsumcoeff
    exact hne hsumcoeff
  have hmq0 : (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ ((q0.val) k) : Poly (e + (e + e) + (skewDim e + 1))) ≠ 0 := by
    rw [rprod_pt_eq_monomial _ Finset.univ]
    intro h
    have hc := congrArg (fun p : Poly (e + (e + e) + (skewDim e + 1)) => p.coeff (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) ((q0.val) k))) h
    rw [MvPolynomial.coeff_monomial] at hc
    simp at hc
  have hren0 : MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q0) = 0 := by
    have h := mul_eq_zero.mp hT0
    rcases h with h | h
    · exact h
    · exact absurd h hmq0
  have hinj := MvPolynomial.rename_injective (R := ℂ) (Fin.castAdd (skewDim e + 1)) rf0_injective
  have h0 : MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (g q0) = MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) 0 := by
    rw [map_zero]
    exact hren0
  have hfin : g q0 = 0 := hinj h0
  exact hfin

omit C V Γ H a he hh hd R h j N in
/-- Pair part of a triple exponent (unconstrained). -/
def rspair (d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ) : Fin (e + (e + e)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => d (Fin.castAdd (skewDim e + 1) i))

omit C V Γ H a he hh hd R h j N in
/-- Point part of a triple exponent (unconstrained). -/
def rspt (d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ) : Fin (skewDim e + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => d (Fin.natAdd (e + (e + e)) k))

omit C V Γ H a he hh hd R h j N in
theorem rssplit_eq (d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ) :
    d = (rspair d).mapDomain (Fin.castAdd (skewDim e + 1)) +
      (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) ((rspt d) k)) := by
  apply Finsupp.ext
  intro j
  cases j using Fin.addCases with
  | left i =>
    rw [Finsupp.add_apply]
    have h1 : ((rspair d).mapDomain (Fin.castAdd (skewDim e + 1))) (Fin.castAdd (skewDim e + 1) i) =
        (rspair d) i :=
      Finsupp.mapDomain_apply_of_injective (Fin.castAdd_injective _ _) _ _
    have h2 : (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) ((rspt d) k))
        (Fin.castAdd (skewDim e + 1) i) = 0 := by
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [Finsupp.single_apply]
      rw [ite_eq_right]
      intro hkk
      have hmem : Fin.natAdd (e + (e + e)) k ∈
          Set.range (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) :=
        ⟨i, hkk.symm⟩
      exact absurd hmem (rpt_notmem_range_rf0 k)
    rw [h1, h2, add_zero]
    rfl
  | right k =>
    rw [Finsupp.add_apply]
    have h1 : ((rspair d).mapDomain (Fin.castAdd (skewDim e + 1))) (Fin.natAdd (e + (e + e)) k) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (rpt_notmem_range_rf0 k)
    have h2 : (∑ k' ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k') ((rspt d) k'))
        (Fin.natAdd (e + (e + e)) k) = (rspt d) k := by
      rw [Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single k]
      · simp [Finsupp.single_apply]
      · intro k' _ hk'
        simp only [Finsupp.single_apply]
        rw [ite_eq_right]
        intro hkk
        apply hk'
        exact rpt_injective hkk
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [h1, h2, zero_add]
    rfl

omit C V Γ H a he hh hd R h j N in
theorem rsmono_factor (d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ) (r : ℂ) :
    MvPolynomial.monomial d r =
      (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (MvPolynomial.monomial (rspair d) r)) *
      (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) ((rspt d) k)) (1 : ℂ)) := by
  conv_lhs => rw [rssplit_eq d, ← mul_one r, ← MvPolynomial.monomial_mul_monomial, ← MvPolynomial.rename_monomial]

omit C V Γ H a he hh hd R h j N in
/-- General point-monomial splitting (no degree constraints; total indexer). -/
theorem rsplit_general (K : Poly (e + (e + e) + (skewDim e + 1))) :
    K = ∑ q ∈ K.support.image (fun d => rspt d),
      (MvPolynomial.rename (Fin.castAdd (skewDim e + 1))
        (∑ d ∈ K.support with rspt d = q, MvPolynomial.monomial (rspair d) (K.coeff d))) *
      (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ)) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum K]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ => rspt d)
    (fun d hd => Finset.mem_image_of_mem _ hd)]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨_, hdpt⟩ := Finset.mem_filter.mp hd
  have hfact : MvPolynomial.monomial d (K.coeff d) =
      (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (MvPolynomial.monomial (rspair d) (K.coeff d))) *
      (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) ((rspt d) k)) (1 : ℂ)) :=
    rsmono_factor d (K.coeff d)
  rw [hfact, hdpt]

omit C V Γ H a he hh hd R h j N in
/-- Single-sum coefficient isolation (uniform; cases contained). -/
theorem rsiso_single (F : Finset (Fin (skewDim e + 1) →₀ ℕ))
    (G : (Fin (skewDim e + 1) →₀ ℕ) → Poly (e + (e + e)))
    (hG0 : ∀ q ∉ F, G q = 0)
    (d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ)
    (q0 : Fin (skewDim e + 1) →₀ ℕ)
    (hd_pt : ∀ k0 : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) k0) = q0 k0) :
    (∑ q ∈ F, ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G q)) *
      (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ))).coeff d) =
    (((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G q0)) *
      (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q0 k)) (1 : ℂ))).coeff d) := by
  classical
  have hsupp : ∀ (G : Poly (e + (e + e))) (q : Fin (skewDim e + 1) →₀ ℕ)
      (d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ),
      d ∈ ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) G) *
        (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ))).support →
      ∀ k0 : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) k0) = q k0 := by
    intro G q d hd k0
    have hbr : (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ) :
        Poly (e + (e + e) + (skewDim e + 1))) =
        (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ q k : Poly (e + (e + e) + (skewDim e + 1))) :=
      (rprod_pt_eq_monomial q Finset.univ).symm
    have hd' : d ∈ ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) G) *
        (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ q k : Poly (e + (e + e) + (skewDim e + 1)))).support := by
      rwa [hbr] at hd
    exact rsupp_third_eq G q d hd' k0
  have hvan : ∀ q ∈ F, q ≠ q0 →
      (((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G q)) *
        (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ))).coeff d) = 0 := by
    intro q _ hq
    have hdis : d ∉ ((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G q)) *
        (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ))).support := by
      intro hmem
      apply hq
      have hpt : ∀ k0 : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) k0) = q k0 := hsupp _ _ _ hmem
      apply Finsupp.ext
      intro k0
      have h1 := hpt k0
      have h2 := hd_pt k0
      rw [h1] at h2
      exact h2
    exact MvPolynomial.notMem_support_iff.mp hdis
  by_cases hmem : q0 ∈ F
  · exact Finset.sum_eq_single q0 (fun q hqmem hq => hvan q hqmem hq) (fun h => absurd (hmem) h)
  · have hsum0 : (∑ q ∈ F, (((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G q)) *
        (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ))).coeff d)) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      apply hvan q hq
      intro heq
      rw [heq] at hq
      exact hmem hq
    have hterm0 : (((MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G q0)) *
        (MvPolynomial.monomial (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q0 k)) (1 : ℂ))).coeff d) = 0 := by
      have hG0 : G q0 = 0 := hG0 _ hmem
      rw [hG0, map_zero, zero_mul]
      simp
    rw [hsum0, hterm0]

omit C V Γ H a he hh hd R h j N in
/-- Pair-monomial homogeneity from block sums (for pullback section membership). -/
theorem rmono_pair_homog {s t : ℕ} (a : Fin (e + (e + e)) →₀ ℕ) (c : ℂ)
    (h0 : (∑ i : Fin e, a (Fin.castAdd (e + e) i)) = s)
    (h1 : (∑ i : Fin (e + e), a (Fin.natAdd e i)) = t) :
    (MvPolynomial.monomial a c).IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) (HilbertMulti.pairDegree s t) := by
  classical
  have hX : ∀ i : Fin (e + (e + e)),
      (MvPolynomial.X i : Poly (e + (e + e))).IsWeightedHomogeneous
        (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)))
        (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) i) :=
    fun i => MvPolynomial.isWeightedHomogeneous_X ℂ _ _
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i => (MvPolynomial.X i : Poly (e + (e + e))) ^ a i)
    (fun i => a i • HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) i)
    (fun i _ => (hX i).pow (a i))
  have hC := MvPolynomial.isWeightedHomogeneous_C
    (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) c
  have h := hC.mul hprod
  have hdeg : (∑ i ∈ Finset.univ, a i • HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) i) =
      HilbertMulti.pairDegree s t := by
    ext j
    fin_cases j <;> simp only [Fin.mk_zero, Fin.mk_one]
    · have hrhs : (HilbertMulti.pairDegree s t) 0 = s := by simp [HilbertMulti.pairDegree]
      rw [hrhs, Finsupp.finsetSum_apply, Fin.sum_univ_add]
      have hleft : (∑ i : Fin e, (a (Fin.castAdd (e + e) i) •
          HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) (Fin.castAdd (e + e) i)) 0) =
          ∑ i : Fin e, a (Fin.castAdd (e + e) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finsupp.smul_apply]
        have hw : HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) (Fin.castAdd (e + e) i) 0 = 1 := by
          simp only [HilbertMulti.blockWeight, HilbertMulti.pairBlocks, Finsupp.single_apply,
            Fin.addCases_left, eq_self_iff_true, one_ne_zero, if_true, if_false]
        rw [hw, smul_eq_mul, mul_one]
      have hright : (∑ i : Fin (e + e), (a (Fin.natAdd e i) •
          HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) (Fin.natAdd e i)) 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [Finsupp.smul_apply]
        have hw : HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) (Fin.natAdd e i) 0 = 0 := by
          simp only [HilbertMulti.blockWeight, HilbertMulti.pairBlocks, Finsupp.single_apply,
            Fin.addCases_right, eq_self_iff_true, one_ne_zero, if_true, if_false]
          try decide
        rw [hw, smul_zero]
      rw [hleft, hright, add_zero]
      exact h0
    · have hrhs : (HilbertMulti.pairDegree s t) 1 = t := by simp [HilbertMulti.pairDegree]
      rw [hrhs, Finsupp.finsetSum_apply, Fin.sum_univ_add]
      have hleft : (∑ i : Fin e, (a (Fin.castAdd (e + e) i) •
          HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) (Fin.castAdd (e + e) i)) 1) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [Finsupp.smul_apply]
        have hw : HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) (Fin.castAdd (e + e) i) 1 = 0 := by
          simp only [HilbertMulti.blockWeight, HilbertMulti.pairBlocks, Finsupp.single_apply,
            Fin.addCases_left, eq_self_iff_true, one_ne_zero, if_true, if_false]
          try decide
        rw [hw, smul_zero]
      have hright : (∑ i : Fin (e + e), (a (Fin.natAdd e i) •
          HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) (Fin.natAdd e i)) 1) =
          ∑ i : Fin (e + e), a (Fin.natAdd e i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finsupp.smul_apply]
        have hw : HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)) (Fin.natAdd e i) 1 = 1 := by
          simp only [HilbertMulti.blockWeight, HilbertMulti.pairBlocks, Finsupp.single_apply,
            Fin.addCases_right, eq_self_iff_true, one_ne_zero, if_true, if_false]
        rw [hw, smul_eq_mul, mul_one]
      rw [hleft, hright, zero_add]
      exact h1
  rw [hdeg, zero_add] at h
  have hmono : MvPolynomial.monomial a c =
      MvPolynomial.C c * ∏ i ∈ Finset.univ, MvPolynomial.X i ^ a i := by
    rw [MvPolynomial.monomial_eq]
    congr 1
    rw [Finsupp.prod]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    simp at hi
    rw [hi, pow_zero]
  rw [hmono]
  exact h

omit V a he hh hd R h j N in
/-- Fiber coefficients of a pullback-ideal element lie in the pair ideal.
For `P` in the rename-pullback of the pair vanishing ideal, each point-fiber
piece `∑_{d : rspt d = q0} monomial (rspair d) (P.coeff d)` lies in the pair
ideal. Proved by comparing the `rsplit_general` decomposition of `P` with the
one obtained from a finite ideal-membership expression, via per-coefficient
isolation (`rsiso_single`) and grafted-exponent computation. -/
theorem rpullback_fiber_ideal
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (P : Poly (e + (e + e) + (skewDim e + 1)))
    (hPmem : P ∈ Ideal.map (MvPolynomial.rename
      (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
      (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H))))
    (q0 : Fin (skewDim e + 1) →₀ ℕ) :
    (∑ d ∈ P.support with rspt d = q0, MvPolynomial.monomial (rspair d) (P.coeff d)) ∈
      MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H)) := by
  classical
  obtain ⟨T, G0, hcof, hG0J, hPeq⟩ : ∃ (T : Finset (Poly (e + (e + e) + (skewDim e + 1))))
      (G0 : Poly (e + (e + e) + (skewDim e + 1)) → Poly (e + (e + e)))
      (hcof : Poly (e + (e + e) + (skewDim e + 1)) → Poly (e + (e + e) + (skewDim e + 1))),
      (∀ t ∈ T, G0 t ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H))) ∧
      P = ∑ t ∈ T, MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (G0 t) * hcof t := by
    have hspan : P ∈ Submodule.span (Poly (e + (e + e) + (skewDim e + 1)))
        (⇑(MvPolynomial.rename (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))) ''
          ↑(MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))) := hPmem
    obtain ⟨c, hcSupp, hcSum⟩ := Submodule.mem_span_set.mp hspan
    have hpre : ∀ t : Poly (e + (e + e) + (skewDim e + 1)), ∃ g : Poly (e + (e + e)),
        (t ∈ c.support → g ∈ MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H))) ∧
        (t ∈ c.support → MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) g = t) := by
      intro t
      by_cases ht : t ∈ c.support
      · obtain ⟨g, hgJ, hgr⟩ := hcSupp ht
        exact ⟨g, fun _ => hgJ, fun _ => hgr⟩
      · exact ⟨0, fun h => absurd h ht, fun h => absurd h ht⟩
    choose G0 hG0J hG0ren using hpre
    refine ⟨c.support, G0, fun t => c t, fun t ht => hG0J t ht, ?_⟩
    have hsum : (∑ t ∈ c.support, (c t) • t) = P := hcSum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hG0ren t ht, smul_eq_mul, mul_comm]
  have hPA := rsplit_general P
  have hGA0 : ∀ q : Fin (skewDim e + 1) →₀ ℕ,
      q ∉ P.support.image (fun d => rspt d) →
      (∑ d ∈ P.support with rspt d = q, MvPolynomial.monomial (rspair d) (P.coeff d)) = 0 := by
    intro q hq
    have hempty : P.support.filter (fun d => rspt d = q) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd heq
      exact hq (heq ▸ Finset.mem_image_of_mem _ hd)
    rw [hempty, Finset.sum_empty]
  have hGt0 : ∀ t ∈ T, ∀ q : Fin (skewDim e + 1) →₀ ℕ,
      q ∉ (hcof t).support.image (fun d => rspt d) →
      (∑ d ∈ (hcof t).support with rspt d = q,
        MvPolynomial.monomial (rspair d) ((hcof t).coeff d)) = 0 := by
    intro t ht q hq
    have hempty : (hcof t).support.filter (fun d => rspt d = q) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd heq
      exact hq (heq ▸ Finset.mem_image_of_mem _ hd)
    rw [hempty, Finset.sum_empty]
  have hcompGen : ∀ (G : Poly (e + (e + e))) (q1 : Fin (skewDim e + 1) →₀ ℕ)
      (a : Fin (e + (e + e)) →₀ ℕ),
      ((MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) G) *
        MvPolynomial.monomial
          (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ)).coeff
        (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
          ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) =
        G.coeff a := by
    intro G q1 a
    rw [MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain _ rf0_injective,
      mul_one]
  have hIsoA : ∀ (q1 : Fin (skewDim e + 1) →₀ ℕ)
      (dd : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ)
      (_ : ∀ k0 : Fin (skewDim e + 1), dd (Fin.natAdd (e + (e + e)) k0) = q1 k0),
      P.coeff dd =
        ((MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (∑ d ∈ P.support with rspt d = q1, MvPolynomial.monomial (rspair d) (P.coeff d))) *
          MvPolynomial.monomial
            (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ)).coeff dd := by
    intro q1 dd hd
    have h1 : P.coeff dd =
        ∑ q ∈ P.support.image (fun d => rspt d),
          ((MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
            (∑ d ∈ P.support with rspt d = q, MvPolynomial.monomial (rspair d) (P.coeff d))) *
            MvPolynomial.monomial
              (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ)).coeff dd := by
      conv_lhs => rw [hPA]
      rw [MvPolynomial.coeff_sum]
    rw [h1]
    exact rsiso_single _ _ hGA0 dd q1 hd
  have hPsum : ∀ dd : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ,
      P.coeff dd =
        ∑ t ∈ T, ((MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (G0 t) * hcof t)).coeff dd := by
    intro dd
    conv_lhs => rw [hPeq]
    rw [MvPolynomial.coeff_sum]
  have hIsoD : ∀ t ∈ T, ∀ (q1 : Fin (skewDim e + 1) →₀ ℕ)
      (dd : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ)
      (_ : ∀ k0 : Fin (skewDim e + 1), dd (Fin.natAdd (e + (e + e)) k0) = q1 k0),
      ((MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
        (G0 t) * hcof t)).coeff dd =
        ((MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
            MvPolynomial.monomial (rspair d) ((hcof t).coeff d)))) *
          MvPolynomial.monomial
            (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ)).coeff dd := by
    intro t ht q1 dd hd
    have hsplit := rsplit_general (hcof t)
    have hdist : MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (G0 t) * hcof t =
        ∑ q ∈ (hcof t).support.image (fun d => rspt d),
          MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
            (G0 t) *
            (MvPolynomial.rename
              (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
              (∑ d ∈ (hcof t).support with rspt d = q,
                MvPolynomial.monomial (rspair d) ((hcof t).coeff d)) *
              MvPolynomial.monomial
                (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ)) := by
      conv_lhs => rw [hsplit]
      rw [Finset.mul_sum]
    have hmerge : ∀ q : Fin (skewDim e + 1) →₀ ℕ,
        MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (G0 t) *
          (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
            (∑ d ∈ (hcof t).support with rspt d = q,
              MvPolynomial.monomial (rspair d) ((hcof t).coeff d)) *
            MvPolynomial.monomial
              (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ)) =
          MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
            (G0 t * (∑ d ∈ (hcof t).support with rspt d = q,
              MvPolynomial.monomial (rspair d) ((hcof t).coeff d))) *
            MvPolynomial.monomial
              (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ) := by
      intro q
      rw [← mul_assoc, ← map_mul]
    have hGt0' : ∀ q : Fin (skewDim e + 1) →₀ ℕ,
        q ∉ (hcof t).support.image (fun d => rspt d) →
        G0 t * (∑ d ∈ (hcof t).support with rspt d = q,
          MvPolynomial.monomial (rspair d) ((hcof t).coeff d)) = 0 := by
      intro q hq
      rw [hGt0 t ht q hq, mul_zero]
    have e1 : ((MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
        (G0 t) * hcof t)).coeff dd =
        ∑ q ∈ (hcof t).support.image (fun d => rspt d),
          ((MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
            (G0 t * (∑ d ∈ (hcof t).support with rspt d = q,
              MvPolynomial.monomial (rspair d) ((hcof t).coeff d)))) *
            MvPolynomial.monomial
              (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ)).coeff dd := by
      rw [hdist, MvPolynomial.coeff_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [hmerge q]
    exact e1.trans (rsiso_single _ _ hGt0' dd q1 hd)
  have hGDsplit : ∀ q1 : Fin (skewDim e + 1) →₀ ℕ,
      MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
        (∑ t ∈ T, G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
          MvPolynomial.monomial (rspair d) ((hcof t).coeff d))) *
        MvPolynomial.monomial
          (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ) =
        ∑ t ∈ T, MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
            MvPolynomial.monomial (rspair d) ((hcof t).coeff d))) *
          MvPolynomial.monomial
            (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ) := by
    intro q1
    rw [map_sum, Finset.sum_mul]
  have hEq : ∀ (q1 : Fin (skewDim e + 1) →₀ ℕ) (a : Fin (e + (e + e)) →₀ ℕ),
      (∑ d ∈ P.support with rspt d = q1, MvPolynomial.monomial (rspair d) (P.coeff d)).coeff a =
      (∑ t ∈ T, G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
        MvPolynomial.monomial (rspair d) ((hcof t).coeff d))).coeff a := by
    intro q1 a
    have hd_pt : ∀ k0 : Fin (skewDim e + 1),
        (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
          ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k))
          (Fin.natAdd (e + (e + e)) k0) = q1 k0 := by
      intro k0
      rw [Finsupp.add_apply, rmapDomain_pt_eq_zero, rptSum_eval, zero_add]
    have e1 : ∑ t ∈ T, ((MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
        (G0 t) * hcof t)).coeff
        (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
          ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) =
        ∑ t ∈ T, ((MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
            MvPolynomial.monomial (rspair d) ((hcof t).coeff d)))) *
          MvPolynomial.monomial
            (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ)).coeff
          (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
            ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) :=
      Finset.sum_congr rfl (fun t ht => hIsoD t ht q1 _ hd_pt)
    have e2 : ∑ t ∈ T, ((MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
        (G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
          MvPolynomial.monomial (rspair d) ((hcof t).coeff d)))) *
        MvPolynomial.monomial
          (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ)).coeff
        (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
          ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) =
        ((MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (∑ t ∈ T, G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
            MvPolynomial.monomial (rspair d) ((hcof t).coeff d)))) *
          MvPolynomial.monomial
            (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ)).coeff
          (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
            ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) := by
      rw [hGDsplit q1, MvPolynomial.coeff_sum]
    calc (∑ d ∈ P.support with rspt d = q1, MvPolynomial.monomial (rspair d) (P.coeff d)).coeff a
        = ((MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (∑ d ∈ P.support with rspt d = q1, MvPolynomial.monomial (rspair d) (P.coeff d))) *
          MvPolynomial.monomial
            (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ)).coeff
          (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
            ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) :=
          (hcompGen _ q1 a).symm
      _ = P.coeff
          (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
            ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) :=
          (hIsoA q1 _ hd_pt).symm
      _ = ∑ t ∈ T, ((MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (G0 t) * hcof t)).coeff
          (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
            ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) :=
          hPsum _
      _ = ∑ t ∈ T, ((MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
            MvPolynomial.monomial (rspair d) ((hcof t).coeff d)))) *
          MvPolynomial.monomial
            (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ)).coeff
          (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
            ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) := e1
      _ = ((MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (∑ t ∈ T, G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
            MvPolynomial.monomial (rspair d) ((hcof t).coeff d)))) *
          MvPolynomial.monomial
            (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) (1 : ℂ)).coeff
          (Finsupp.mapDomain (Fin.castAdd (skewDim e + 1)) a +
            ∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q1 k)) := e2
      _ = (∑ t ∈ T, G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
          MvPolynomial.monomial (rspair d) ((hcof t).coeff d))).coeff a :=
          hcompGen _ q1 a
  have hGAeqGD : ∀ q1 : Fin (skewDim e + 1) →₀ ℕ,
      (∑ d ∈ P.support with rspt d = q1, MvPolynomial.monomial (rspair d) (P.coeff d)) =
      (∑ t ∈ T, G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
        MvPolynomial.monomial (rspair d) ((hcof t).coeff d))) := by
    intro q1
    apply MvPolynomial.ext
    intro a
    exact hEq q1 a
  have hGDJ : ∀ q1 : Fin (skewDim e + 1) →₀ ℕ,
      (∑ t ∈ T, G0 t * (∑ d ∈ (hcof t).support with rspt d = q1,
        MvPolynomial.monomial (rspair d) ((hcof t).coeff d))) ∈
      MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H)) := by
    intro q1
    apply Ideal.sum_mem
    intro t ht
    exact Ideal.mul_mem_right _ _ (hG0J t ht)
  rw [hGAeqGD q0]
  exact hGDJ q0


omit V a he hh hd R h j N in
/-- Pullback of the pair ideal has product ranks: base ranks times point monomials.
This is the `m = 0` term of `triple_rank_identity` (base quotient tensored with
the free point polynomial ring). The pullback ideal involves only the first two
blocks, so the third block stays free. -/
theorem pairPullback_section_product {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (s t u : ℕ) :
    Module.finrank ℂ (HilbertMulti.sectionSpace
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (Ideal.map (MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H))))
      (HilbertMulti.tripleDegree s t u)) =
    pairHilbert (liftedParameterBase C Γ H) s t * (skewDim e + 1).multichoose u := by
  classical
  -- Pair and triple ambient pieces and their quotient identification.
  have hPairSpace : HilbertMulti.sectionSpace
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)))
      (MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H)))
      (HilbertMulti.pairDegree s t) = pairSection (liftedParameterBase C Γ H) s t := by
    rw [HilbertMulti.sectionSpace, HilbertMulti.pairBlockPiece]
    rfl
  -- Rank identities for pair and pullback triple sections.
  have hPairRank : pairHilbert (liftedParameterBase C Γ H) s t +
      Module.finrank ℂ (sectionKernel
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) =
      Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) :=
    pairSection_finrank_eq _ _ _
  have hTripleRank : Module.finrank ℂ (HilbertMulti.sectionSpace
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        (HilbertMulti.tripleDegree s t u)) +
      Module.finrank ℂ (sectionKernel
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) =
      Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
        {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) := by
    haveI := finite_tripleExponents (n := e) (m := e + e) (o := skewDim e + 1)
      (s := s) (t := t) (u := u)
    have hspace : HilbertMulti.sectionSpace
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        (HilbertMulti.tripleDegree s t u) =
        (MvPolynomial.restrictSupport ℂ
          {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
            (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
            (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}).map
          (Ideal.Quotient.mkₐ ℂ (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))).toLinearMap := by
      rw [HilbertMulti.sectionSpace, HilbertMulti.tripleBlockPiece]
    rw [hspace]
    exact section_finrank_eq _ _
  -- Ambient product and kernel product.
  have hAmbient : Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
        {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) =
      Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
        (skewDim e + 1).multichoose u := by
    rw [ambientTripleCount, ambientPairCount]
  have hKernelProduct : Module.finrank ℂ (sectionKernel
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) =
      Module.finrank ℂ (sectionKernel
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
        (skewDim e + 1).multichoose u := by
    have hRenameHom : ∀ (g : Poly (e + (e + e))) (d : Fin 2 →₀ ℕ),
        g.IsWeightedHomogeneous
          (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) d →
        (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) g).IsWeightedHomogeneous
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
          (HilbertMulti.tripleDegree (d 0) (d 1) 0) := by
      intro g d hg
      refine MvPolynomial.IsWeightedHomogeneous.induction_on
        (motive := fun p _ => (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) p).IsWeightedHomogeneous
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
          (HilbertMulti.tripleDegree (d 0) (d 1) 0))
        ?_ ?_ ?_ hg
      · simpa only [map_zero] using MvPolynomial.isWeightedHomogeneous_zero ℂ
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
          (HilbertMulti.tripleDegree (d 0) (d 1) 0)
      · intro p q hp hq ihp ihq
        simpa only [map_add] using ihp.add ihq
      · intro a r ha
        rw [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_monomial]
        have hs : (∑ i ∈ a.support, a i • HilbertMulti.blockWeight
            (HilbertMulti.pairBlocks e (e + e)) i) = d := by
          simpa only [Finsupp.weight_apply, Finsupp.sum] using ha
        have hX : ∀ i : Fin (e + (e + e)),
            (MvPolynomial.X (Fin.castAdd (skewDim e + 1) i) :
              Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
              (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
              (HilbertMulti.tripleDegree
                (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 0)
                (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 1) 0) := by
          intro i
          have h := MvPolynomial.isWeightedHomogeneous_X ℂ
            (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
            (Fin.castAdd (skewDim e + 1) i)
          have hEq : HilbertMulti.blockWeight
              (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))
              (Fin.castAdd (skewDim e + 1) i) =
              HilbertMulti.tripleDegree
                (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 0)
                (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 1) 0 := by
            cases i using Fin.addCases with
            | left j =>
              ext k
              fin_cases k <;>
                simp [HilbertMulti.blockWeight, HilbertMulti.tripleBlocks,
                  HilbertMulti.tripleDegree, HilbertMulti.pairBlocks,
                  Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right]
            | right j =>
              ext k
              fin_cases k <;>
                simp [HilbertMulti.blockWeight, HilbertMulti.tripleBlocks,
                  HilbertMulti.tripleDegree, HilbertMulti.pairBlocks,
                  Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right]
          rwa [hEq] at h
        have hprod := MvPolynomial.IsWeightedHomogeneous.prod a.support
          (fun i => (MvPolynomial.X (Fin.castAdd (skewDim e + 1) i) :
            Poly (e + (e + e) + (skewDim e + 1))) ^ a i)
          (fun i => a i • HilbertMulti.tripleDegree
            (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 0)
            (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 1) 0)
          (fun i _ => (hX i).pow (a i))
        have hC := MvPolynomial.isWeightedHomogeneous_C
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) r
        have h := hC.mul hprod
        have hDeg : (∑ i ∈ a.support, a i • HilbertMulti.tripleDegree
            (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 0)
            (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 1) 0) =
            HilbertMulti.tripleDegree (d 0) (d 1) 0 := by
          have h0' : ((∑ i ∈ a.support, a i • HilbertMulti.blockWeight
              (HilbertMulti.pairBlocks e (e + e)) i) 0) = d 0 :=
            congrArg (· 0) hs
          have h1' : ((∑ i ∈ a.support, a i • HilbertMulti.blockWeight
              (HilbertMulti.pairBlocks e (e + e)) i) 1) = d 1 :=
            congrArg (· 1) hs
          ext k
          fin_cases k
          · simpa [HilbertMulti.tripleDegree, HilbertMulti.blockWeight,
              HilbertMulti.pairBlocks, HilbertMulti.tripleBlocks,
              Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right] using h0'
          · simpa [HilbertMulti.tripleDegree, HilbertMulti.blockWeight,
              HilbertMulti.pairBlocks, HilbertMulti.tripleBlocks,
              Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right] using h1'
          · simp [HilbertMulti.tripleDegree, HilbertMulti.blockWeight,
              HilbertMulti.pairBlocks, HilbertMulti.tripleBlocks,
              Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right]
        simpa only [Finsupp.prod, MvPolynomial.algebraMap_eq, zero_add, hDeg,
          Function.comp_apply] using h
    have hPtX : ∀ k : Fin (skewDim e + 1),
        (MvPolynomial.X (Fin.natAdd (e + (e + e)) k) :
          Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
          (HilbertMulti.tripleDegree 0 0 1) := by
      intro k
      have wpt : HilbertMulti.blockWeight
          (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))
          (Fin.natAdd (e + (e + e)) k) =
          HilbertMulti.tripleDegree 0 0 1 := by
        ext j
        fin_cases j <;>
          simp [HilbertMulti.blockWeight, HilbertMulti.tripleBlocks,
            HilbertMulti.tripleDegree]
      have h := MvPolynomial.isWeightedHomogeneous_X ℂ
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
        (Fin.natAdd (e + (e + e)) k)
      rwa [wpt] at h
    have hAddSTU : HilbertMulti.tripleDegree s t 0 + HilbertMulti.tripleDegree 0 0 u =
        HilbertMulti.tripleDegree s t u := by
      ext j
      fin_cases j <;>
        simp [HilbertMulti.tripleDegree, add_zero, zero_add]
    have hPtMono : ∀ (q : Fin (skewDim e + 1) →₀ ℕ) (hq : q.degree = u),
        (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
          q k : Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
          (HilbertMulti.tripleDegree 0 0 u) := by
      intro q hq
      have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
        (fun k => (MvPolynomial.X (Fin.natAdd (e + (e + e)) k) :
          Poly (e + (e + e) + (skewDim e + 1))) ^ q k)
        (fun k => q k • HilbertMulti.tripleDegree 0 0 1)
        (fun k _ => (hPtX k).pow (q k))
      have hDegPt : (∑ k ∈ Finset.univ, q k • HilbertMulti.tripleDegree 0 0 1) =
          HilbertMulti.tripleDegree 0 0 u := by
        ext j
        fin_cases j
        · simp [HilbertMulti.tripleDegree, HilbertMulti.blockWeight,
            HilbertMulti.pairBlocks, HilbertMulti.tripleBlocks,
            Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right]
        · simp [HilbertMulti.tripleDegree, HilbertMulti.blockWeight,
            HilbertMulti.pairBlocks, HilbertMulti.tripleBlocks,
            Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right]
        · simpa [HilbertMulti.tripleDegree, HilbertMulti.blockWeight,
            HilbertMulti.pairBlocks, HilbertMulti.tripleBlocks,
            Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right,
            Finsupp.degree_eq_sum, smul_eq_mul, mul_one] using hq
      rw [hDegPt] at hprod
      exact hprod
    have hJhom : (MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H))).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule ℂ
          (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)))) :=
      pairRepresentatives_blockHomogeneous (liftedParameterBase C Γ H)
    have hIpullHom : (Ideal.map (MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule ℂ
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))) := by
      obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists
        (MvPolynomial.weightedHomogeneousSubmodule ℂ
          (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))))
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))).mp hJhom
      rw [hS, Ideal.map_span]
      apply Ideal.homogeneous_span
      rintro q ⟨p, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨d, hd⟩ := z.property
      exact ⟨_, hRenameHom _ _ hd⟩
    have hsPt : {d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u}.Finite :=
      Finsupp.finite_of_degree_eq u
    letI := hsPt.fintype
    have hPtCardNat : Nat.card {d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u} =
        (skewDim e + 1).multichoose u := by
      rw [OAI.PiExponentJets.W64.card_exponents_degree]
      simp
    let Psi : (∀ _ : ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u},
        ↥(sectionKernel
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))
          {d : Fin (e + (e + e)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
            (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t})) →ₗ[ℂ]
        ↥(sectionKernel
          (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))
          {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
            (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
            (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) := {
      toFun := fun f => ⟨⟨∑ q ∈ Finset.univ,
        (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (((f q).val).val) : Poly (e + (e + e) + (skewDim e + 1))) *
        (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
          ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1))), by
            have hAddGen : HilbertMulti.tripleDegree ((HilbertMulti.pairDegree s t) 0)
                ((HilbertMulti.pairDegree s t) 1) 0 + HilbertMulti.tripleDegree 0 0 u =
                HilbertMulti.tripleDegree s t u := by
              ext j
              fin_cases j <;>
                simp [HilbertMulti.tripleDegree, HilbertMulti.pairDegree, add_zero, zero_add]
            have hEach : ∀ q : ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u},
                ((MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
                  (((f q).val).val) : Poly (e + (e + e) + (skewDim e + 1))) *
                (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
                  ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))).IsWeightedHomogeneous
                  (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
                  (HilbertMulti.tripleDegree s t u) := by
              intro q
              have hPairHom : ((((f q).val).val)).IsWeightedHomogeneous
                  (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)))
                  (HilbertMulti.pairDegree s t) := by
                rw [← MvPolynomial.mem_weightedHomogeneousSubmodule, HilbertMulti.pairBlockPiece]
                exact (f q).val.property
              have hRen0 := hRenameHom _ _ hPairHom
              have hPt := hPtMono q.val q.property
              have hMul := hRen0.mul hPt
              rwa [hAddGen] at hMul
            have hSumHom : (∑ q ∈ Finset.univ,
                (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
                  (((f q).val).val) : Poly (e + (e + e) + (skewDim e + 1))) *
                (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
                  ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))).IsWeightedHomogeneous
                (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
                (HilbertMulti.tripleDegree s t u) :=
              MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun q _ => hEach q)
            rw [← HilbertMulti.tripleBlockPiece]
            exact hSumHom⟩, by
            have hSumIdeal : (∑ q ∈ Finset.univ,
                (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
                  (((f q).val).val) : Poly (e + (e + e) + (skewDim e + 1))) *
                (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
                  ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))) ∈
                Ideal.map (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                  (MvPolynomial.vanishingIdeal ℂ
                    (pairRepresentatives (liftedParameterBase C Γ H))) := by
              apply Ideal.sum_mem
              intro q _
              have hker := (f q).property
              have h0 : ((Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ
                  (pairRepresentatives (liftedParameterBase C Γ H)))).toLinearMap.domRestrict
                  (MvPolynomial.restrictSupport ℂ {d : Fin (e + (e + e)) →₀ ℕ |
                    (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
                    (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t})) (f q).val = 0 :=
                LinearMap.mem_ker.mp hker
              have hmk : (Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ
                  (pairRepresentatives (liftedParameterBase C Γ H)))) (((f q).val).val) = 0 := by
                simpa using h0
              have hJ : ((((f q).val).val)) ∈ MvPolynomial.vanishingIdeal ℂ
                  (pairRepresentatives (liftedParameterBase C Γ H)) := by
                have h0mk : Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ
                  (pairRepresentatives (liftedParameterBase C Γ H))) (((f q).val).val) = 0 := by
                  simpa using hmk
                exact Ideal.Quotient.eq_zero_iff_mem.mp h0mk
              have hRenMem : (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
                  (((f q).val).val) : Poly (e + (e + e) + (skewDim e + 1))) ∈
                Ideal.map (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                  (MvPolynomial.vanishingIdeal ℂ
                    (pairRepresentatives (liftedParameterBase C Γ H))) :=
                Ideal.mem_map_of_mem _ hJ
              exact Ideal.mul_mem_right _ _ hRenMem
            apply LinearMap.mem_ker.mpr
            have hmk : (Ideal.Quotient.mkₐ ℂ (Ideal.map (MvPolynomial.rename
                (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                (MvPolynomial.vanishingIdeal ℂ
                  (pairRepresentatives (liftedParameterBase C Γ H)))))
              (∑ q ∈ Finset.univ,
                (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
                  (((f q).val).val) : Poly (e + (e + e) + (skewDim e + 1))) *
                (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
                  ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))) = 0 := by
              have h0mk : Ideal.Quotient.mk (Ideal.map (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                  (MvPolynomial.vanishingIdeal ℂ
                    (pairRepresentatives (liftedParameterBase C Γ H))))
                (∑ q ∈ Finset.univ,
                  (MvPolynomial.rename
                    (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
                    (((f q).val).val) : Poly (e + (e + e) + (skewDim e + 1))) *
                  (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
                    ((q.val) k) : Poly (e + (e + e) + (skewDim e + 1)))) = 0 :=
                Ideal.Quotient.eq_zero_iff_mem.mpr hSumIdeal
              simpa using h0mk
            simpa using hmk⟩,
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        simp only [Pi.add_apply, Submodule.coe_add, map_add, add_mul, Finset.sum_add_distrib],
      map_smul' := by
        intro c x
        apply Subtype.ext
        apply Subtype.ext
        have hRenSmul : ∀ (p : Poly (e + (e + e))),
            MvPolynomial.rename
              (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
              (c • p) =
            c • MvPolynomial.rename
              (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
              p := by
          intro p
          simp [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, MvPolynomial.rename_C]
        simp only [Pi.smul_apply, Submodule.coe_smul, hRenSmul, smul_mul_assoc, Finset.smul_sum,
          RingHom.id_apply] }
    have hPsiSurj : Function.Surjective Psi := by
      classical
      intro y
      have hPmem : (y.val.val : Poly (e + (e + e) + (skewDim e + 1))) ∈
          Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))) := by
        have hker := y.property
        have h0 : ((Ideal.Quotient.mkₐ ℂ (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))).toLinearMap.domRestrict
            (MvPolynomial.restrictSupport ℂ {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
              (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
              (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
              (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u})) y.val = 0 :=
          LinearMap.mem_ker.mp hker
        have hmk : (Ideal.Quotient.mkₐ ℂ (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))) (y.val.val) = 0 := by
          simpa using h0
        have h0mk : Ideal.Quotient.mk (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H)))) (y.val.val) = 0 := by
          simpa using hmk
        exact Ideal.Quotient.eq_zero_iff_mem.mp h0mk
      have hPsupp : ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support : Set _) ⊆
          {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
            (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
            (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u} :=
        y.val.property
      have hGA0 : ∀ q : Fin (skewDim e + 1) →₀ ℕ,
          q ∉ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support.image (fun d => rspt d) →
          (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = q,
            MvPolynomial.monomial (rspair d)
              ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) = 0 := by
        intro q hq
        have hempty : (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support.filter
            (fun d => rspt d = q) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro d hd heq
          exact hq (heq ▸ Finset.mem_image_of_mem _ hd)
        rw [hempty, Finset.sum_empty]
      have hFAsub : ∀ q : Fin (skewDim e + 1) →₀ ℕ,
          q ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support.image (fun d => rspt d) →
          q.degree = u := by
        intro q hq
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
        have hd3 := (hPsupp hd).2.2
        rw [Finsupp.degree_eq_sum]
        simpa [rspt] using hd3
      have hGsupp : ∀ q0 : Fin (skewDim e + 1) →₀ ℕ,
          (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = q0,
            MvPolynomial.monomial (rspair d)
              ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) ∈
          MvPolynomial.restrictSupport ℂ {d : Fin (e + (e + e)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
            (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t} := by
        intro q0
        have hterm : ∀ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support,
            rspt d = q0 →
            (MvPolynomial.monomial (rspair d)
              ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)).IsWeightedHomogeneous
              (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e)))
              (HilbertMulti.pairDegree s t) := by
          intro d hd _
          have hsd := (hPsupp hd).1
          have hstd := (hPsupp hd).2.1
          have hrsp0 : (∑ i : Fin e, (rspair d) (Fin.castAdd (e + e) i)) = s := by
            have hcongr : ∀ i : Fin e, (rspair d) (Fin.castAdd (e + e) i) =
                d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i)) := fun i => by simp [rspair]
            rw [Finset.sum_congr rfl (fun i _ => hcongr i)]
            exact hsd
          have hrsp1 : (∑ i : Fin (e + e), (rspair d) (Fin.natAdd e i)) = t := by
            have hcongr : ∀ i : Fin (e + e), (rspair d) (Fin.natAdd e i) =
                d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i)) := fun i => by simp [rspair]
            rw [Finset.sum_congr rfl (fun i _ => hcongr i)]
            exact hstd
          exact rmono_pair_homog _ _ hrsp0 hrsp1
        have hsum := MvPolynomial.IsWeightedHomogeneous.sum _ _ _
          (fun d hd => hterm d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2)
        rw [← HilbertMulti.pairBlockPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
        exact hsum
      have hGAJ : ∀ q0 : Fin (skewDim e + 1) →₀ ℕ,
          (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = q0,
            MvPolynomial.monomial (rspair d)
              ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) ∈
          MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)) := by
        intro q0
        exact rpullback_fiber_ideal C Γ H _ hPmem q0
      refine ⟨fun q => ⟨⟨∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with
          rspt d = (q.val),
          MvPolynomial.monomial (rspair d)
            ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d), hGsupp (q.val)⟩, ?_⟩, ?_⟩
      · have hmk : (Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
            (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = (q.val),
              MvPolynomial.monomial (rspair d)
                ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) = 0 := by
          have h0mk : Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H)))
              (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = (q.val),
                MvPolynomial.monomial (rspair d)
                  ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (hGAJ _)
          simpa using h0mk
        exact LinearMap.mem_ker.mpr (by simpa using hmk)
      · have hPA := rsplit_general (y.val.val : Poly (e + (e + e) + (skewDim e + 1)))
        have hPtSum : (y.val.val : Poly (e + (e + e) + (skewDim e + 1))) =
            ∑ q' ∈ (Finset.univ : Finset ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u}),
            (MvPolynomial.rename
              (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
              (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = ((q'.val)),
                MvPolynomial.monomial (rspair d)
                  ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) : Poly (e + (e + e) + (skewDim e + 1))) *
            MvPolynomial.monomial
              (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (((q'.val)) k)) (1 : ℂ) := by
          have hinj : Set.InjOn
              (Subtype.val : ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u} → Fin (skewDim e + 1) →₀ ℕ)
              ↑(Finset.univ : Finset ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u}) :=
            fun a _ b _ h => Subtype.ext h
          calc (y.val.val : Poly (e + (e + e) + (skewDim e + 1)))
              = ∑ q ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support.image (fun d => rspt d),
                (MvPolynomial.rename
                (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
                (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = q,
                  MvPolynomial.monomial (rspair d)
                    ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) : Poly (e + (e + e) + (skewDim e + 1))) *
              MvPolynomial.monomial
                (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q k)) (1 : ℂ) := hPA
            _ = ∑ q' ∈ Finset.univ.image
                (Subtype.val : ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u} → Fin (skewDim e + 1) →₀ ℕ),
                (MvPolynomial.rename
                (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
                (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = q',
                  MvPolynomial.monomial (rspair d)
                    ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) : Poly (e + (e + e) + (skewDim e + 1))) *
              MvPolynomial.monomial
                (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (q' k)) (1 : ℂ) := by
              apply Finset.sum_subset
              · intro q hq
                apply Finset.mem_image.mpr
                refine ⟨⟨q, hFAsub q hq⟩, Finset.mem_univ _, rfl⟩
              · intro x hximg hxFA
                have hxv : (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = x,
                    MvPolynomial.monomial (rspair d)
                      ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) = 0 :=
                  hGA0 x hxFA
                rw [hxv, map_zero, zero_mul]
            _ = ∑ q' ∈ (Finset.univ : Finset ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u}),
              (MvPolynomial.rename
                (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
                (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = ((q'.val)),
                  MvPolynomial.monomial (rspair d)
                    ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) : Poly (e + (e + e) + (skewDim e + 1))) *
              MvPolynomial.monomial
                (∑ k ∈ Finset.univ, Finsupp.single (Fin.natAdd (e + (e + e)) k) (((q'.val)) k)) (1 : ℂ) :=
              Finset.sum_image hinj
        have hPolyEq : (∑ q' ∈ (Finset.univ : Finset ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u}),
            (MvPolynomial.rename
              (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
              (∑ d ∈ (y.val.val : Poly (e + (e + e) + (skewDim e + 1))).support with rspt d = ((q'.val)),
                MvPolynomial.monomial (rspair d)
                  ((y.val.val : Poly (e + (e + e) + (skewDim e + 1))).coeff d)) : Poly (e + (e + e) + (skewDim e + 1))) *
            (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^ (((q'.val)) k) :
              Poly (e + (e + e) + (skewDim e + 1)))) =
            (y.val.val : Poly (e + (e + e) + (skewDim e + 1))) :=
          (Finset.sum_congr rfl (fun q' _ => by rw [rprod_pt_eq_monomial _ Finset.univ])).trans
            hPtSum.symm
        apply Subtype.ext
        apply Subtype.ext
        exact hPolyEq
    have hPsiInj : Function.Injective Psi := by
      intro f1 f2 h12
      have h12poly : (∑ q ∈ Finset.univ, (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (((((f1) q).val).val) : Poly (e + (e + e)))) *
          (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
            (((q.val)) k) : Poly (e + (e + e) + (skewDim e + 1)))) =
          (∑ q ∈ Finset.univ, (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (((((f2) q).val).val) : Poly (e + (e + e)))) *
          (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
            (((q.val)) k) : Poly (e + (e + e) + (skewDim e + 1)))) :=
        congrArg (fun x : ↥(sectionKernel
          (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))
          {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
            (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
            (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) =>
          ((x.val).val : Poly (e + (e + e) + (skewDim e + 1)))) h12
      have hSe : (∑ q ∈ Finset.univ, (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
          (((((f1) q).val).val - (((f2) q).val).val) : Poly (e + (e + e)))) *
          (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
            (((q.val)) k) : Poly (e + (e + e) + (skewDim e + 1)))) = 0 := by
        have hdistrib : (∑ q ∈ Finset.univ, (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
            (((((f1) q).val).val - (((f2) q).val).val) : Poly (e + (e + e)))) *
            (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
              (((q.val)) k) : Poly (e + (e + e) + (skewDim e + 1)))) =
            (∑ q ∈ Finset.univ, (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
            (((((f1) q).val).val) : Poly (e + (e + e)))) *
            (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
              (((q.val)) k) : Poly (e + (e + e) + (skewDim e + 1)))) -
            (∑ q ∈ Finset.univ, (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))
            (((((f2) q).val).val) : Poly (e + (e + e)))) *
            (∏ k ∈ Finset.univ, MvPolynomial.X (Fin.natAdd (e + (e + e)) k) ^
              (((q.val)) k) : Poly (e + (e + e) + (skewDim e + 1)))) := by
          simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
        rw [hdistrib, h12poly, sub_self]
      have hall : ∀ q : ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u},
          (((((f1) q).val).val - (((f2) q).val).val) : Poly (e + (e + e))) = 0 :=
        rcore_inj (u := u) (g := fun q : ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u} =>
          (((((f1) q).val).val - (((f2) q).val).val) : Poly (e + (e + e)))) hSe
      have hconcl : f1 = f2 := by
        apply funext
        intro q0
        have hg0 : (((((f1) q0).val).val - (((f2) q0).val).val) : Poly (e + (e + e))) = 0 := hall q0
        have hpoly : ((((f1 q0).val).val) : Poly (e + (e + e))) = ((((f2 q0).val).val) : Poly (e + (e + e))) :=
          sub_eq_zero.mp hg0
        have h1 : ((f1 q0).val) = ((f2 q0).val) := Subtype.ext hpoly
        have h2 : f1 q0 = f2 q0 := Subtype.ext h1
        exact h2
      exact hconcl
    haveI := finite_pairExponents (n := e) (m := e + e) (s := s) (t := t)
    haveI := moduleFinite_restrictSupport
      {d : Fin (e + (e + e)) →₀ ℕ |
        (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
        (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}
    haveI : Module.Finite ℂ ↥(sectionKernel
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) :=
      Module.Finite.of_injective (sectionKernel
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}).subtype Subtype.val_injective
    haveI := finite_tripleExponents (n := e) (m := e + e) (o := skewDim e + 1)
      (s := s) (t := t) (u := u)
    haveI := moduleFinite_restrictSupport
      {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
        (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
        (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
        (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}
    haveI : Module.Finite ℂ ↥(sectionKernel
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) :=
      Module.Finite.of_injective (sectionKernel
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}).subtype
        Subtype.val_injective
    have hPiRank : ∀ (ι : Type) [Fintype ι] (V : Type) [AddCommGroup V] [Module ℂ V]
        (hFreePi : ∀ _ : ι, Module.Free ℂ V) (hFinPi : ∀ _ : ι, Module.Finite ℂ V)
        (c : ℕ) (hcard : Fintype.card ι = c),
        Module.finrank ℂ (∀ _ : ι, V) = Module.finrank ℂ V * c := by
      intro ι _ V _ _ hFreePi hFinPi c hcard
      rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        hcard, mul_comm]
    have hFreePiConcrete : ∀ _ : ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u}, Module.Free ℂ ↥(sectionKernel
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) :=
      fun _ => Module.Free.of_divisionRing ℂ ↥(sectionKernel
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t})
    have hFinPiConcrete : ∀ _ : ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u}, Module.Finite ℂ ↥(sectionKernel
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) :=
      fun _ => inferInstance
    have hCardConcrete : Fintype.card ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u} =
        (skewDim e + 1).multichoose u := by
      rw [← Nat.card_eq_fintype_card, hPtCardNat]
    have hDomRank : Module.finrank ℂ (∀ _ : ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u},
        ↥(sectionKernel
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))
          {d : Fin (e + (e + e)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
            (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t})) =
        Module.finrank ℂ (sectionKernel
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))
          {d : Fin (e + (e + e)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
            (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
          (skewDim e + 1).multichoose u :=
      hPiRank ↥{d : Fin (skewDim e + 1) →₀ ℕ | d.degree = u} ↥(sectionKernel
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))
        {d : Fin (e + (e + e)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
          (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) hFreePiConcrete hFinPiConcrete
        ((skewDim e + 1).multichoose u) hCardConcrete
    have hLe : Module.finrank ℂ (sectionKernel
          (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))
          {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
            (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
            (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) ≤
        Module.finrank ℂ (sectionKernel
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))
          {d : Fin (e + (e + e)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
            (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
          (skewDim e + 1).multichoose u := by
      have h1 := Psi.finrank_range_le
      have hrange : LinearMap.range Psi = ⊤ := LinearMap.range_eq_top.mpr hPsiSurj
      rw [hrange, finrank_top, hDomRank] at h1
      exact h1
    have hGe : Module.finrank ℂ (sectionKernel
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))
          {d : Fin (e + (e + e)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
            (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
          (skewDim e + 1).multichoose u ≤
        Module.finrank ℂ (sectionKernel
          (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))
          {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
            (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
            (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) := by
      have h := LinearMap.finrank_le_finrank_of_injective hPsiInj
      rw [hDomRank] at h
      exact h
    exact Nat.le_antisymm hLe hGe
  -- Arithmetic assembly from the two rank identities and the two products.
  have hArith : Module.finrank ℂ (HilbertMulti.sectionSpace
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        (HilbertMulti.tripleDegree s t u)) =
      pairHilbert (liftedParameterBase C Γ H) s t * (skewDim e + 1).multichoose u := by
    have h2 : Module.finrank ℂ (HilbertMulti.sectionSpace
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
          (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))
          (HilbertMulti.tripleDegree s t u)) +
        Module.finrank ℂ (sectionKernel
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))
          {d : Fin (e + (e + e)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
            (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
          (skewDim e + 1).multichoose u =
        pairHilbert (liftedParameterBase C Γ H) s t * (skewDim e + 1).multichoose u +
        Module.finrank ℂ (sectionKernel
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))
          {d : Fin (e + (e + e)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
            (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
          (skewDim e + 1).multichoose u := by
      calc Module.finrank ℂ (HilbertMulti.sectionSpace
              (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
              (Ideal.map (MvPolynomial.rename
                (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                (MvPolynomial.vanishingIdeal ℂ
                  (pairRepresentatives (liftedParameterBase C Γ H))))
              (HilbertMulti.tripleDegree s t u)) +
            Module.finrank ℂ (sectionKernel
              (MvPolynomial.vanishingIdeal ℂ
                (pairRepresentatives (liftedParameterBase C Γ H)))
              {d : Fin (e + (e + e)) →₀ ℕ |
                (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
                (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
              (skewDim e + 1).multichoose u
          = Module.finrank ℂ (HilbertMulti.sectionSpace
              (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
              (Ideal.map (MvPolynomial.rename
                (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                (MvPolynomial.vanishingIdeal ℂ
                  (pairRepresentatives (liftedParameterBase C Γ H))))
              (HilbertMulti.tripleDegree s t u)) +
            Module.finrank ℂ (sectionKernel
              (Ideal.map (MvPolynomial.rename
                (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                (MvPolynomial.vanishingIdeal ℂ
                  (pairRepresentatives (liftedParameterBase C Γ H))))
              {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
                (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
                (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
                (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) := by
            rw [← hKernelProduct]
        _ = Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
              {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
                (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
                (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
                (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u}) :=
            hTripleRank
        _ = Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
              {d : Fin (e + (e + e)) →₀ ℕ |
                (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
                (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
            (skewDim e + 1).multichoose u := hAmbient
        _ = (pairHilbert (liftedParameterBase C Γ H) s t +
              Module.finrank ℂ (sectionKernel
                (MvPolynomial.vanishingIdeal ℂ
                  (pairRepresentatives (liftedParameterBase C Γ H)))
                {d : Fin (e + (e + e)) →₀ ℕ |
                  (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
                  (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t})) *
            (skewDim e + 1).multichoose u := by
            rw [← hPairRank]
        _ = pairHilbert (liftedParameterBase C Γ H) s t * (skewDim e + 1).multichoose u +
            Module.finrank ℂ (sectionKernel
              (MvPolynomial.vanishingIdeal ℂ
                (pairRepresentatives (liftedParameterBase C Γ H)))
              {d : Fin (e + (e + e)) →₀ ℕ |
                (∑ i : Fin e, d (Fin.castAdd (e + e) i)) = s ∧
                (∑ i : Fin (e + e), d (Fin.natAdd e i)) = t}) *
              (skewDim e + 1).multichoose u := by
            rw [Nat.add_mul]
    exact Nat.add_right_cancel h2
  exact hArith

namespace PWorld

omit V a he hh hd R h j N in
/-- P-world (mu-deformation) weight: `none` (the deformation parameter mu)
has tridegree `(1,0,1)`; `some i` keeps the triple block weight. -/
def pWeight (e : ℕ) : Option (Fin (e + (e + e) + (skewDim e + 1))) → (Fin 3 →₀ ℕ) :=
  fun o => match o with
    | none => HilbertMulti.tripleDegree 1 0 1
    | some i => HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) i

omit V a he hh hd R h j N in
theorem pMu_weighted (e : ℕ) :
    (MvPolynomial.X none :
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).IsWeightedHomogeneous
      (pWeight e) (HilbertMulti.tripleDegree 1 0 1) := by
  have h := MvPolynomial.isWeightedHomogeneous_X ℂ (pWeight e)
    (none : Option (Fin (e + (e + e) + (skewDim e + 1))))
  simpa [pWeight] using h

omit V a he hh hd R h j N in
/-- Linear point-direction part of the mu-deformed equations:
`(D_z d)_w` as a P-world polynomial (tridegree `(1,0,1)`). -/
def pLiftLinear {e : ℕ} (C : SkewCoordinates e) (w : Fin e) :
    MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ :=
  ∑ k : Fin (skewDim e), ∑ l : Fin e,
    MvPolynomial.C ((((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single w 1))) *
      MvPolynomial.X (some (Fin.natAdd (e + (e + e)) (Fin.succ k))) *
      MvPolynomial.X (some (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l)))

omit V a he hh hd R h j N in
theorem pLiftLinear_weighted {e : ℕ} (C : SkewCoordinates e) (w : Fin e) :
    (pLiftLinear C w).IsWeightedHomogeneous
      (pWeight e) (HilbertMulti.tripleDegree 1 0 1) := by
  classical
  have wdir : ∀ l : Fin e,
      pWeight e (some (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l))) =
      HilbertMulti.tripleDegree 1 0 0 := by
    intro l
    ext j
    fin_cases j <;>
      simp [pWeight, HilbertMulti.blockWeight, HilbertMulti.tripleBlocks,
        HilbertMulti.tripleDegree]
  have wpt : ∀ k : Fin (skewDim e + 1),
      pWeight e (some (Fin.natAdd (e + (e + e)) k)) =
      HilbertMulti.tripleDegree 0 0 1 := by
    intro k
    ext j
    fin_cases j <;>
      simp [pWeight, HilbertMulti.blockWeight, HilbertMulti.tripleBlocks,
        HilbertMulti.tripleDegree]
  have hadd1 : HilbertMulti.tripleDegree 0 0 1 + HilbertMulti.tripleDegree 1 0 0 =
      HilbertMulti.tripleDegree 1 0 1 := by
    ext j
    fin_cases j <;>
      simp [HilbertMulti.tripleDegree]
  have hXdir : ∀ l : Fin e, (MvPolynomial.X
      (some (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l))) :
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).IsWeightedHomogeneous
      (pWeight e) (HilbertMulti.tripleDegree 1 0 0) := by
    intro l
    have h := MvPolynomial.isWeightedHomogeneous_X ℂ (pWeight e)
      (some (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l)))
    rwa [wdir l] at h
  have hXpt : ∀ k : Fin (skewDim e + 1), (MvPolynomial.X
      (some (Fin.natAdd (e + (e + e)) k)) :
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).IsWeightedHomogeneous
      (pWeight e) (HilbertMulti.tripleDegree 0 0 1) := by
    intro k
    have h := MvPolynomial.isWeightedHomogeneous_X ℂ (pWeight e)
      (some (Fin.natAdd (e + (e + e)) k))
    rwa [wpt k] at h
  have hterm : ∀ k : Fin (skewDim e), ∀ l : Fin e,
      (MvPolynomial.C ((((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single w 1))) *
        MvPolynomial.X (some (Fin.natAdd (e + (e + e)) (Fin.succ k))) *
        MvPolynomial.X (some (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) l))) :
        MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).IsWeightedHomogeneous
      (pWeight e) (HilbertMulti.tripleDegree 1 0 1) := by
    intro k l
    have hC := MvPolynomial.isWeightedHomogeneous_C
      (pWeight e)
      ((((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single w 1)))
    have h := ((hC.mul (hXpt (Fin.succ k))).mul (hXdir l))
    simpa [hadd1, zero_add] using h
  unfold pLiftLinear
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _
    (fun k _ => MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun l _ => hterm k l))

omit C V Γ H a he hh hd R h j N in
    theorem tripleRenameHom : ∀ (g : Poly (e + (e + e))) (d : Fin 2 →₀ ℕ),
        g.IsWeightedHomogeneous
          (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) d →
        (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) g).IsWeightedHomogeneous
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
          (HilbertMulti.tripleDegree (d 0) (d 1) 0) := by
      intro g d hg
      refine MvPolynomial.IsWeightedHomogeneous.induction_on
        (motive := fun p _ => (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))) p).IsWeightedHomogeneous
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
          (HilbertMulti.tripleDegree (d 0) (d 1) 0))
        ?_ ?_ ?_ hg
      · simpa only [map_zero] using MvPolynomial.isWeightedHomogeneous_zero ℂ
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
          (HilbertMulti.tripleDegree (d 0) (d 1) 0)
      · intro p q hp hq ihp ihq
        simpa only [map_add] using ihp.add ihq
      · intro a r ha
        rw [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_monomial]
        have hs : (∑ i ∈ a.support, a i • HilbertMulti.blockWeight
            (HilbertMulti.pairBlocks e (e + e)) i) = d := by
          simpa only [Finsupp.weight_apply, Finsupp.sum] using ha
        have hX : ∀ i : Fin (e + (e + e)),
            (MvPolynomial.X (Fin.castAdd (skewDim e + 1) i) :
              Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
              (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
              (HilbertMulti.tripleDegree
                (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 0)
                (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 1) 0) := by
          intro i
          have h := MvPolynomial.isWeightedHomogeneous_X ℂ
            (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
            (Fin.castAdd (skewDim e + 1) i)
          have hEq : HilbertMulti.blockWeight
              (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))
              (Fin.castAdd (skewDim e + 1) i) =
              HilbertMulti.tripleDegree
                (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 0)
                (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 1) 0 := by
            cases i using Fin.addCases with
            | left j =>
              ext k
              fin_cases k <;>
                simp [HilbertMulti.blockWeight, HilbertMulti.tripleBlocks,
                  HilbertMulti.tripleDegree, HilbertMulti.pairBlocks,
                  Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right]
            | right j =>
              ext k
              fin_cases k <;>
                simp [HilbertMulti.blockWeight, HilbertMulti.tripleBlocks,
                  HilbertMulti.tripleDegree, HilbertMulti.pairBlocks,
                  Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right]
          rwa [hEq] at h
        have hprod := MvPolynomial.IsWeightedHomogeneous.prod a.support
          (fun i => (MvPolynomial.X (Fin.castAdd (skewDim e + 1) i) :
            Poly (e + (e + e) + (skewDim e + 1))) ^ a i)
          (fun i => a i • HilbertMulti.tripleDegree
            (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 0)
            (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 1) 0)
          (fun i _ => (hX i).pow (a i))
        have hC := MvPolynomial.isWeightedHomogeneous_C
          (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) r
        have h := hC.mul hprod
        have hDeg : (∑ i ∈ a.support, a i • HilbertMulti.tripleDegree
            (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 0)
            (((HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) i) 1) 0) =
            HilbertMulti.tripleDegree (d 0) (d 1) 0 := by
          have h0' : ((∑ i ∈ a.support, a i • HilbertMulti.blockWeight
              (HilbertMulti.pairBlocks e (e + e)) i) 0) = d 0 :=
            congrArg (· 0) hs
          have h1' : ((∑ i ∈ a.support, a i • HilbertMulti.blockWeight
              (HilbertMulti.pairBlocks e (e + e)) i) 1) = d 1 :=
            congrArg (· 1) hs
          ext k
          fin_cases k
          · simpa [HilbertMulti.tripleDegree, HilbertMulti.blockWeight,
              HilbertMulti.pairBlocks, HilbertMulti.tripleBlocks,
              Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right] using h0'
          · simpa [HilbertMulti.tripleDegree, HilbertMulti.blockWeight,
              HilbertMulti.pairBlocks, HilbertMulti.tripleBlocks,
              Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right] using h1'
          · simp [HilbertMulti.tripleDegree, HilbertMulti.blockWeight,
              HilbertMulti.pairBlocks, HilbertMulti.tripleBlocks,
              Finsupp.single_apply, Fin.addCases_left, Fin.addCases_right]
        simpa only [Finsupp.prod, MvPolynomial.algebraMap_eq, zero_add, hDeg,
          Function.comp_apply] using h

omit V a he hh hd R h j N in
/-- Mu-deformed equations `g_w = L_w - mu * c_w` (tridegree `(1,0,1)`),
for a coefficient vector `c` to be chosen regular later. -/
def pDeformed {e : ℕ} (C : SkewCoordinates e) (c : Fin e → ℂ) (w : Fin e) :
    MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ :=
  pLiftLinear C w - MvPolynomial.X none * MvPolynomial.C (c w)

omit V a he hh hd R h j N in
theorem pDeformed_weighted {e : ℕ} (C : SkewCoordinates e) (c : Fin e → ℂ) (w : Fin e) :
    (pDeformed C c w).IsWeightedHomogeneous
      (pWeight e) (HilbertMulti.tripleDegree 1 0 1) := by
  have hC := MvPolynomial.isWeightedHomogeneous_C
    (pWeight e) (c w)
  have hprod : (MvPolynomial.X none * MvPolynomial.C (c w) :
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).IsWeightedHomogeneous
      (pWeight e) (HilbertMulti.tripleDegree 1 0 1) := by
    simpa using (pMu_weighted e).mul hC
  exact (pLiftLinear_weighted C w).sub hprod

omit C V Γ H a he hh hd R h j N in
/-- The `some`-embedding preserves triple homogeneity as P-world homogeneity
(same degree, since `pWeight` extends the triple block weight). -/
theorem pRenameHom {e : ℕ} (g : Poly (e + (e + e) + (skewDim e + 1))) (d : Fin 3 →₀ ℕ)
    (hg : g.IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) d) :
    (MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) g).IsWeightedHomogeneous
      (pWeight e) d := by
  have h : g.IsWeightedHomogeneous (fun i => pWeight e (Option.some i)) d := by
    simpa [pWeight] using hg
  exact HilbertMulti.coordinateInclude_weighted (pWeight e) h

omit V a he hh hd R h j N in
/-- P-world base ideal: pullback of the pair ideal through the triple ring. -/
def pBaseIdeal {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    Ideal (MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) :=
  Ideal.map (MvPolynomial.rename ((Option.some :
    Fin (e + (e + e) + (skewDim e + 1)) → Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
      Fin.castAdd (skewDim e + 1)))
    (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H)))

omit V a he hh hd R h j N in
theorem pBaseHom {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    (pBaseIdeal C Γ H).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (pWeight e)) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists
    (MvPolynomial.weightedHomogeneousSubmodule ℂ
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))))
    (MvPolynomial.vanishingIdeal ℂ
      (pairRepresentatives (liftedParameterBase C Γ H)))).mp
    (pairRepresentatives_blockHomogeneous _)
  rw [pBaseIdeal, hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro q ⟨p, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := z.property
  have h1 := tripleRenameHom _ d hd
  have h2 := pRenameHom _ _ h1
  rw [MvPolynomial.rename_rename] at h2
  exact ⟨_, h2⟩

omit V a he hh hd R h j N in
/-- Mu-degree of a P-world exponent. -/
def pMuPart {e : ℕ} (d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ) : ℕ :=
  d none

omit V a he hh hd R h j N in
/-- Base (triple) part of a P-world exponent. -/
def pBasePart {e : ℕ} (d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ) :
    Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => d (some i))

omit V a he hh hd R h j N in
theorem pSplit_eq {e : ℕ} (d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ) :
    d = (pBasePart d).mapDomain
        (Option.some : Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) +
      Finsupp.single (none : Option (Fin (e + (e + e) + (skewDim e + 1)))) (pMuPart d) := by
  apply Finsupp.ext
  intro o
  cases o with
  | none =>
    rw [Finsupp.add_apply]
    have h1 : ((pBasePart d).mapDomain (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))) none = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    have h2 : (Finsupp.single (none : Option (Fin (e + (e + e) + (skewDim e + 1))))
        (pMuPart d)) none = pMuPart d :=
      Finsupp.single_eq_same
    rw [h1, h2, zero_add]
    rfl
  | some i =>
    rw [Finsupp.add_apply]
    have h1 : ((pBasePart d).mapDomain (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))) (some i) = (pBasePart d) i :=
      Finsupp.mapDomain_apply_of_injective
        (Option.some_injective (Fin (e + (e + e) + (skewDim e + 1)))) _ _
    have h2 : (Finsupp.single (none : Option (Fin (e + (e + e) + (skewDim e + 1))))
        (pMuPart d)) (some i) = 0 :=
      Finsupp.single_eq_of_ne (by simp)
    rw [h1, h2, add_zero]
    simp [pBasePart]

omit V a he hh hd R h j N in
theorem pMonoFactor {e : ℕ} (d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ)
    (r : ℂ) :
    MvPolynomial.monomial d r =
      (MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.monomial (pBasePart d) r)) *
      (MvPolynomial.monomial
        (Finsupp.single (none : Option (Fin (e + (e + e) + (skewDim e + 1)))) (pMuPart d))
        (1 : ℂ)) := by
  conv_lhs => rw [pSplit_eq d, ← mul_one r, ← MvPolynomial.monomial_mul_monomial,
    ← MvPolynomial.rename_monomial]

omit V a he hh hd R h j N in
/-- General mu-monomial splitting (no degree constraints; total indexer). -/
theorem psplit_general {e : ℕ}
    (K : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) :
    K = ∑ j ∈ K.support.image (fun d => pMuPart d),
      (MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (∑ d ∈ K.support with pMuPart d = j, MvPolynomial.monomial (pBasePart d) (K.coeff d))) *
      (MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ)) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum K]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ => pMuPart d)
    (fun d hd => Finset.mem_image_of_mem _ hd)]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨_, hdpt⟩ := Finset.mem_filter.mp hd
  have hfact : MvPolynomial.monomial d (K.coeff d) =
      (MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.monomial (pBasePart d) (K.coeff d))) *
      (MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) ((pMuPart d))) (1 : ℂ)) :=
    pMonoFactor d (K.coeff d)
  rw [hfact, hdpt]

omit V a he hh hd R h j N in
/-- Mu-degree of a term supported on a renamed base times a mu-power:
the `none`-degree reads off the mu-exponent. -/
theorem pSuppMu {e : ℕ} (H : Poly (e + (e + e) + (skewDim e + 1))) (L : ℕ)
    (d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ)
    (hd : d ∈ ((MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) H) *
      (MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ))).support) :
    d none = L := by
  classical
  have hmem := MvPolynomial.support_mul _ _ hd
  rw [Finset.mem_add] at hmem
  obtain ⟨d1, hd1, d2, hd2, rfl⟩ := hmem
  have hd1mem : d1 ∈ (MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) H).support := hd1
  rw [MvPolynomial.support_rename_of_injective
    (Option.some_injective (Fin (e + (e + e) + (skewDim e + 1))))] at hd1mem
  rw [Finset.mem_image] at hd1mem
  obtain ⟨a, _, rfl⟩ := hd1mem
  have hd2mem : d2 ∈ (MvPolynomial.monomial (Finsupp.single (none :
      Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).support := hd2
  have hd2eq : d2 = Finsupp.single (none :
      Option (Fin (e + (e + e) + (skewDim e + 1)))) L :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd2mem)
  have e1 : (Finsupp.mapDomain (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) a)
      (none : Option (Fin (e + (e + e) + (skewDim e + 1)))) = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ (by simp)
  rw [Finsupp.add_apply, e1, hd2eq, Finsupp.single_eq_same, zero_add]

omit V a he hh hd R h j N in
/-- Single-sum mu-coefficient isolation (uniform; cases contained). -/
theorem psiso_mu {e : ℕ} (F : Finset ℕ)
    (G : ℕ → Poly (e + (e + e) + (skewDim e + 1)))
    (hG0 : ∀ l ∉ F, G l = 0)
    (d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ)
    (L : ℕ) (hd_mu : d none = L) :
    (∑ l ∈ F, ((MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) (G l)) *
      (MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) l) (1 : ℂ))).coeff d) =
    (((MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) (G L)) *
      (MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ))).coeff d) := by
  classical
  have hvan : ∀ l ∈ F, l ≠ L →
      (((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (G l)) *
        (MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) l) (1 : ℂ))).coeff d) = 0 := by
    intro l _ hl
    have hdis : d ∉ ((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (G l)) *
        (MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) l) (1 : ℂ))).support := by
      intro hmem
      apply hl
      have hpt : d none = l := pSuppMu _ _ _ hmem
      have h1 := hpt
      rw [hd_mu] at h1
      exact h1.symm
    exact MvPolynomial.notMem_support_iff.mp hdis
  by_cases hmem : L ∈ F
  · exact Finset.sum_eq_single L (fun l hqmem hq => hvan l hqmem hq) (fun h => absurd (hmem) h)
  · have hsum0 : (∑ l ∈ F, (((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (G l)) *
        (MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) l) (1 : ℂ))).coeff d)) = 0 := by
      apply Finset.sum_eq_zero
      intro l hq
      apply hvan l hq
      intro heq
      rw [heq] at hq
      exact hmem hq
    have hterm0 : (((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (G L)) *
        (MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ))).coeff d) = 0 := by
      have hG0 : G L = 0 := hG0 _ hmem
      rw [hG0, map_zero, zero_mul]
      simp
    rw [hsum0, hterm0]

omit V a he hh hd R h j N in
/-- Grafted mu-coefficient computation. -/
theorem pCompGen {e : ℕ} (G : Poly (e + (e + e) + (skewDim e + 1))) (L : ℕ)
    (a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ) :
    ((MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) G) *
      MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).coeff
      (Finsupp.mapDomain (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
        Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) =
      G.coeff a := by
  rw [MvPolynomial.coeff_mul_monomial,
    MvPolynomial.coeff_rename_mapDomain _
      (Option.some_injective (Fin (e + (e + e) + (skewDim e + 1)))), mul_one]

omit V a he hh hd R h j N in
theorem pMuPowMul {e : ℕ} (j : ℕ) :
    (MvPolynomial.monomial (Finsupp.single (none :
      Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ) :
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
      MvPolynomial.X none =
    MvPolynomial.monomial (Finsupp.single (none :
      Option (Fin (e + (e + e) + (skewDim e + 1)))) (j + 1)) (1 : ℂ) := by
  rw [← MvPolynomial.X_pow_eq_monomial, ← pow_succ, MvPolynomial.X_pow_eq_monomial]

omit V a he hh hd R h j N in
/-- Finite spanning expression for base-ideal elements (pullback structure). -/
theorem pMapSpan {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (P : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (hPmem : P ∈ pBaseIdeal C Γ H) :
    ∃ (T : Finset (MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ))
      (G0 : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ →
        Poly (e + (e + e)))
      (hcof : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ →
        MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ),
      (∀ t ∈ T, G0 t ∈ MvPolynomial.vanishingIdeal ℂ
        (pairRepresentatives (liftedParameterBase C Γ H))) ∧
      P = ∑ t ∈ T, MvPolynomial.rename ((Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
            Fin.castAdd (skewDim e + 1))
          (G0 t) * hcof t := by
  have hspan : P ∈ Submodule.span
      (MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
        (⇑(MvPolynomial.rename ((Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1))) ''
          ↑(MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))) := hPmem
  obtain ⟨c, hcSupp, hcSum⟩ := Submodule.mem_span_set.mp hspan
  have hpre : ∀ t : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ,
      ∃ g : Poly (e + (e + e)),
        (t ∈ c.support → g ∈ MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H))) ∧
        (t ∈ c.support → MvPolynomial.rename ((Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1)) g = t) := by
    intro t
    by_cases ht : t ∈ c.support
    · obtain ⟨g, hgJ, hgr⟩ := hcSupp ht
      exact ⟨g, fun _ => hgJ, fun _ => hgr⟩
    · exact ⟨0, fun h => absurd h ht, fun h => absurd h ht⟩
  choose G0 hG0J hG0ren using hpre
  refine ⟨c.support, G0, fun t => c t, fun t ht => hG0J t ht, ?_⟩
  have hsum : (∑ t ∈ c.support, (c t) • t) = P := hcSum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hG0ren t ht, smul_eq_mul, mul_comm]

omit V a he hh hd R h j N in
/-- Fiber-coefficient comparison for base-ideal elements: each mu-fiber piece
of `P` equals the corresponding combination of cofactor fibers. -/
theorem pFiberCompare {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (P : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (T : Finset (MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ))
    (G0 : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ →
      Poly (e + (e + e)))
    (hcof : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ →
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (hPeq : P = ∑ t ∈ T, MvPolynomial.rename ((Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1))
        (G0 t) * hcof t) :
    ∀ (L : ℕ) (a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ),
      (∑ d ∈ P.support with pMuPart d = L, MvPolynomial.monomial (pBasePart d) (P.coeff d)).coeff a =
      (∑ t ∈ T, MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
        MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d))).coeff a := by
  classical
  have hPA := psplit_general P
  have hGA0 : ∀ j : ℕ,
      j ∉ P.support.image (fun d => pMuPart d) →
      (∑ d ∈ P.support with pMuPart d = j, MvPolynomial.monomial (pBasePart d) (P.coeff d)) = 0 := by
    intro j hj
    have hempty : P.support.filter (fun d => pMuPart d = j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd heq
      exact hj (heq ▸ Finset.mem_image_of_mem _ hd)
    rw [hempty, Finset.sum_empty]
  have hGt0 : ∀ t ∈ T, ∀ j : ℕ,
      j ∉ (hcof t).support.image (fun d => pMuPart d) →
      (∑ d ∈ (hcof t).support with pMuPart d = j,
        MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)) = 0 := by
    intro t _ j hj
    have hempty : (hcof t).support.filter (fun d => pMuPart d = j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd heq
      exact hj (heq ▸ Finset.mem_image_of_mem _ hd)
    rw [hempty, Finset.sum_empty]
  have hd_none : ∀ (a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ) (L : ℕ),
      (Finsupp.mapDomain (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
        Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L)
        (none : Option (Fin (e + (e + e) + (skewDim e + 1)))) = L := by
    intro a L
    rw [Finsupp.add_apply,
      Finsupp.mapDomain_of_notMem_range _ _ (by simp),
      Finsupp.single_eq_same, zero_add]
  have hIsoP : ∀ (L : ℕ)
      (dd : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ)
      (_ : dd none = L),
      P.coeff dd =
        ((MvPolynomial.rename (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1))))
          (∑ d ∈ P.support with pMuPart d = L, MvPolynomial.monomial (pBasePart d) (P.coeff d))) *
          MvPolynomial.monomial (Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).coeff dd := by
    intro L dd hd
    have h1 : P.coeff dd =
        ∑ j ∈ P.support.image (fun d => pMuPart d),
          ((MvPolynomial.rename (Option.some :
            Fin (e + (e + e) + (skewDim e + 1)) →
              Option (Fin (e + (e + e) + (skewDim e + 1))))
            (∑ d ∈ P.support with pMuPart d = j, MvPolynomial.monomial (pBasePart d) (P.coeff d))) *
            MvPolynomial.monomial (Finsupp.single (none :
              Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ)).coeff dd := by
      conv_lhs => rw [hPA]
      rw [MvPolynomial.coeff_sum]
    rw [h1]
    exact psiso_mu _ _ hGA0 dd L hd
  have hPsum : ∀ dd : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ,
      P.coeff dd =
        ∑ t ∈ T, ((MvPolynomial.rename ((Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
            Fin.castAdd (skewDim e + 1))
          (G0 t) * hcof t)).coeff dd := by
    intro dd
    conv_lhs => rw [hPeq]
    rw [MvPolynomial.coeff_sum]
  have hIsoD : ∀ t ∈ T, ∀ (L : ℕ)
      (dd : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ)
      (_ : dd none = L),
      ((MvPolynomial.rename ((Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1))
        (G0 t) * hcof t)).coeff dd =
        ((MvPolynomial.rename (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
            MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)))) *
          MvPolynomial.monomial (Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).coeff dd := by
    intro t ht L dd hd
    have hsplit := psplit_general (hcof t)
    have hdist : MvPolynomial.rename ((Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1))
          (G0 t) * hcof t =
        ∑ j ∈ (hcof t).support.image (fun d => pMuPart d),
          MvPolynomial.rename ((Option.some :
            Fin (e + (e + e) + (skewDim e + 1)) →
              Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
              Fin.castAdd (skewDim e + 1))
            (G0 t) *
            (MvPolynomial.rename (Option.some :
              Fin (e + (e + e) + (skewDim e + 1)) →
                Option (Fin (e + (e + e) + (skewDim e + 1))))
              (∑ d ∈ (hcof t).support with pMuPart d = j,
                MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)) *
              MvPolynomial.monomial (Finsupp.single (none :
                Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ)) := by
      conv_lhs => rw [hsplit]
      rw [Finset.mul_sum]
    have hmerge : ∀ j : ℕ,
        MvPolynomial.rename ((Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
            Fin.castAdd (skewDim e + 1))
          (G0 t) *
          (MvPolynomial.rename (Option.some :
            Fin (e + (e + e) + (skewDim e + 1)) →
              Option (Fin (e + (e + e) + (skewDim e + 1))))
            (∑ d ∈ (hcof t).support with pMuPart d = j,
              MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)) *
            MvPolynomial.monomial (Finsupp.single (none :
              Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ)) =
          MvPolynomial.rename (Option.some :
            Fin (e + (e + e) + (skewDim e + 1)) →
              Option (Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = j,
              MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d))) *
            MvPolynomial.monomial (Finsupp.single (none :
              Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ) := by
      intro j
      have hrr : MvPolynomial.rename ((Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
            Fin.castAdd (skewDim e + 1)) (G0 t) =
          MvPolynomial.rename (Option.some :
            Fin (e + (e + e) + (skewDim e + 1)) →
              Option (Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t)) := by
        rw [MvPolynomial.rename_rename]
      rw [hrr, ← mul_assoc, ← map_mul]
    have hGt0' : ∀ j : ℕ,
        j ∉ (hcof t).support.image (fun d => pMuPart d) →
        MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = j,
          MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)) = 0 := by
      intro j hj
      rw [hGt0 t ht j hj, mul_zero]
    have e1 : ((MvPolynomial.rename ((Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1))
        (G0 t) * hcof t)).coeff dd =
        ∑ j ∈ (hcof t).support.image (fun d => pMuPart d),
          ((MvPolynomial.rename (Option.some :
            Fin (e + (e + e) + (skewDim e + 1)) →
              Option (Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = j,
              MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)))) *
            MvPolynomial.monomial (Finsupp.single (none :
              Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ)).coeff dd := by
      rw [hdist, MvPolynomial.coeff_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hmerge j]
    exact e1.trans (psiso_mu _ _ hGt0' dd L hd)
  have hGDsplit : ∀ L : ℕ,
      MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (∑ t ∈ T, MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d))) *
        MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ) =
        ∑ t ∈ T, MvPolynomial.rename (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
            MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d))) *
          MvPolynomial.monomial (Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ) := by
    intro L
    rw [map_sum, Finset.sum_mul]
  intro L a
  have hgraft_none : (Finsupp.mapDomain (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
      Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) L)
      (none : Option (Fin (e + (e + e) + (skewDim e + 1)))) = L :=
    hd_none a L
  have e1 : ∑ t ∈ T, ((MvPolynomial.rename ((Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
        Fin.castAdd (skewDim e + 1))
      (G0 t) * hcof t)).coeff
      (Finsupp.mapDomain (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
        Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) =
      ∑ t ∈ T, ((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)))) *
        MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).coeff
        (Finsupp.mapDomain (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
          Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) :=
    Finset.sum_congr rfl (fun t ht => hIsoD t ht L _ hgraft_none)
  have e2 : ∑ t ∈ T, ((MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1))))
      (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
        MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)))) *
      MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).coeff
      (Finsupp.mapDomain (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
        Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) =
      ((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (∑ t ∈ T, MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)))) *
        MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).coeff
        (Finsupp.mapDomain (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
          Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) := by
    rw [hGDsplit L, MvPolynomial.coeff_sum]
  calc (∑ d ∈ P.support with pMuPart d = L, MvPolynomial.monomial (pBasePart d) (P.coeff d)).coeff a
      = ((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (∑ d ∈ P.support with pMuPart d = L, MvPolynomial.monomial (pBasePart d) (P.coeff d))) *
        MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).coeff
        (Finsupp.mapDomain (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
          Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) :=
        (pCompGen _ L a).symm
    _ = P.coeff
        (Finsupp.mapDomain (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
          Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) :=
        (hIsoP L _ hgraft_none).symm
    _ = ∑ t ∈ T, ((MvPolynomial.rename ((Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1))
        (G0 t) * hcof t)).coeff
        (Finsupp.mapDomain (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
          Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) :=
        hPsum _
    _ = ∑ t ∈ T, ((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)))) *
        MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).coeff
        (Finsupp.mapDomain (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
          Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) := e1
    _ = ((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (∑ t ∈ T, MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)))) *
        MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ)).coeff
        (Finsupp.mapDomain (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
          Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) := e2
    _ = (∑ t ∈ T, MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) * (∑ d ∈ (hcof t).support with pMuPart d = L,
        MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d))).coeff a :=
        pCompGen _ L a

omit V a he hh hd R h j N in
/-- Mu-transcendence for the base ideal: `mu` is regular on the pullback quotient. -/
theorem pBaseMem_of_mul_mu {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (p : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (h : p * MvPolynomial.X (none :
      Option (Fin (e + (e + e) + (skewDim e + 1)))) ∈ pBaseIdeal C Γ H) :
    p ∈ pBaseIdeal C Γ H := by
  classical
  obtain ⟨T, G0, hcof, hG0J, hPeq⟩ := pMapSpan C Γ H _ h
  have hLpos : ∀ L ∈ (p * MvPolynomial.X (none :
      Option (Fin (e + (e + e) + (skewDim e + 1))))).support.image
      (fun d => pMuPart d), 1 ≤ L := by
    intro L hL
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hL
    have hmem := MvPolynomial.support_mul _ _ hd
    rw [Finset.mem_add] at hmem
    obtain ⟨d1, _, d2, hd2, rfl⟩ := hmem
    have hd2eq : d2 = Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) 1 := by
      have hXsup := MvPolynomial.support_X (R := ℂ) (n := (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))))
      rw [hXsup] at hd2
      exact Finset.mem_singleton.mp hd2
    show 1 ≤ pMuPart (d1 + d2)
    rw [show pMuPart (d1 + d2) = (d1 + d2) (none :
      Option (Fin (e + (e + e) + (skewDim e + 1)))) from rfl,
      Finsupp.add_apply, hd2eq, Finsupp.single_eq_same]
    omega
  have hCFib : ∀ L : ℕ, (∑ d ∈ (p * MvPolynomial.X (none :
      Option (Fin (e + (e + e) + (skewDim e + 1))))).support with pMuPart d = L,
      MvPolynomial.monomial (pBasePart d)
        ((p * MvPolynomial.X (none :
          Option (Fin (e + (e + e) + (skewDim e + 1))))).coeff d)) =
      (∑ t ∈ T, MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) *
        (∑ d ∈ (hcof t).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d))) := by
    intro L
    apply MvPolynomial.ext
    intro a
    exact pFiberCompare C Γ H _ T G0 hcof hPeq L a
  have hQmul : (∑ L ∈ (p * MvPolynomial.X (none :
      Option (Fin (e + (e + e) + (skewDim e + 1))))).support.image
      (fun d => pMuPart d),
      MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (∑ d ∈ (p * MvPolynomial.X (none :
          Option (Fin (e + (e + e) + (skewDim e + 1))))).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d)
            ((p * MvPolynomial.X (none :
              Option (Fin (e + (e + e) + (skewDim e + 1))))).coeff d)) *
        MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (L - 1)) (1 : ℂ)) *
      MvPolynomial.X (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) =
      p * MvPolynomial.X (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) := by
    rw [Finset.sum_mul]
    have hstep : ∀ L ∈ (p * MvPolynomial.X (none :
        Option (Fin (e + (e + e) + (skewDim e + 1))))).support.image
        (fun d => pMuPart d),
        MvPolynomial.rename (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1))))
          (∑ d ∈ (p * MvPolynomial.X (none :
            Option (Fin (e + (e + e) + (skewDim e + 1))))).support with pMuPart d = L,
            MvPolynomial.monomial (pBasePart d)
              ((p * MvPolynomial.X (none :
                Option (Fin (e + (e + e) + (skewDim e + 1))))).coeff d)) *
          MvPolynomial.monomial (Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) (L - 1)) (1 : ℂ) *
          MvPolynomial.X (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) =
        MvPolynomial.rename (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1))))
          (∑ d ∈ (p * MvPolynomial.X (none :
            Option (Fin (e + (e + e) + (skewDim e + 1))))).support with pMuPart d = L,
            MvPolynomial.monomial (pBasePart d)
              ((p * MvPolynomial.X (none :
                Option (Fin (e + (e + e) + (skewDim e + 1))))).coeff d)) *
          MvPolynomial.monomial (Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) L) (1 : ℂ) := by
      intro L hL
      have h1 : L - 1 + 1 = L := by have := hLpos L hL; omega
      rw [mul_assoc, pMuPowMul, h1]
    rw [Finset.sum_congr rfl (fun L hL => hstep L hL)]
    exact (psplit_general (p * MvPolynomial.X (none :
      Option (Fin (e + (e + e) + (skewDim e + 1)))))).symm
  have hQ : p = (∑ L ∈ (p * MvPolynomial.X (none :
      Option (Fin (e + (e + e) + (skewDim e + 1))))).support.image
      (fun d => pMuPart d),
      MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
        (∑ d ∈ (p * MvPolynomial.X (none :
          Option (Fin (e + (e + e) + (skewDim e + 1))))).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d)
            ((p * MvPolynomial.X (none :
              Option (Fin (e + (e + e) + (skewDim e + 1))))).coeff d)) *
        MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (L - 1)) (1 : ℂ)) := by
    apply mul_right_cancel₀ (MvPolynomial.X_ne_zero (none :
      Option (Fin (e + (e + e) + (skewDim e + 1)))))
    rw [hQmul]
  rw [hQ]
  apply Ideal.sum_mem
  intro L hL
  rw [hCFib L, map_sum, Finset.sum_mul]
  apply Ideal.sum_mem
  intro t ht
  have hmem : MvPolynomial.rename ((Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
        Fin.castAdd (skewDim e + 1)) (G0 t) ∈ pBaseIdeal C Γ H :=
    Ideal.mem_map_of_mem _ (hG0J t ht)
  have hrr : MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1))))
      (MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) *
        (∑ d ∈ (hcof t).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d))) *
      MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) (L - 1)) (1 : ℂ) =
      MvPolynomial.rename ((Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1)) (G0 t) *
        (MvPolynomial.rename (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1))))
          (∑ d ∈ (hcof t).support with pMuPart d = L,
            MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d)) *
          MvPolynomial.monomial (Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) (L - 1)) (1 : ℂ)) := by
    rw [map_mul, MvPolynomial.rename_rename, mul_assoc]
  rw [hrr]
  exact Ideal.mul_mem_right _ _ hmem

omit V a he hh hd R h j N in
/-- Forward mu-shift by a mu-free `t`: `mu ↦ mu + t`, base vars fixed. -/
def pShiftF {e : ℕ}
    (t : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) :
    Option (Fin (e + (e + e) + (skewDim e + 1))) →
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ :=
  fun o => match o with
    | none => MvPolynomial.X none + t
    | some i => MvPolynomial.X (some i)

omit V a he hh hd R h j N in
/-- Backward mu-shift by `t`. -/
def pShiftG {e : ℕ}
    (t : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) :
    Option (Fin (e + (e + e) + (skewDim e + 1))) →
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ :=
  fun o => match o with
    | none => MvPolynomial.X none - t
    | some i => MvPolynomial.X (some i)

omit V a he hh hd R h j N in
theorem pShift_vals {e : ℕ}
    (t : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) :
    pShiftF t none = MvPolynomial.X none + t ∧
    (∀ i, pShiftF t (some i) = MvPolynomial.X (some i)) ∧
    pShiftG t none = MvPolynomial.X none - t ∧
    (∀ i, pShiftG t (some i) = MvPolynomial.X (some i)) :=
  ⟨rfl, fun _ => rfl, rfl, fun _ => rfl⟩

omit V a he hh hd R h j N in
/-- Shifts fix composite-renamed base polynomials. -/
theorem pShift_fix {e : ℕ}
    (t : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (F : Option (Fin (e + (e + e) + (skewDim e + 1))) →
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (hF : ∀ i, F (some i) = MvPolynomial.X (some i))
    (q : Poly (e + (e + e))) :
    MvPolynomial.aeval F (MvPolynomial.rename ((Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
        Fin.castAdd (skewDim e + 1)) q) =
    MvPolynomial.rename ((Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
        Fin.castAdd (skewDim e + 1)) q := by
  rw [MvPolynomial.aeval_rename]
  have hcomp : F ∘ ((Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
        Fin.castAdd (skewDim e + 1)) =
      MvPolynomial.X ∘ ((Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1)) := by
    funext i
    simp only [Function.comp_apply]
    exact hF _
  rw [hcomp, ← MvPolynomial.rename_eq_aeval]

omit V a he hh hd R h j N in
/-- Shifts preserve the base ideal (generator-wise). -/
theorem pShift_preserves {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (t : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (F : Option (Fin (e + (e + e) + (skewDim e + 1))) →
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (hF : ∀ i, F (some i) = MvPolynomial.X (some i))
    (y : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (hy : y ∈ pBaseIdeal C Γ H) :
    MvPolynomial.aeval F y ∈ pBaseIdeal C Γ H := by
  have hspan : y ∈ Submodule.span
      (MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
        (⇑(MvPolynomial.rename ((Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1))) ''
          ↑(MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))) := hy
  obtain ⟨c, hcSupp, hcSum⟩ := Submodule.mem_span_set.mp hspan
  have hsum : (∑ t ∈ c.support, (c t) • t) = y := hcSum
  rw [← hsum, map_sum]
  apply Ideal.sum_mem
  intro u hu
  obtain ⟨g, hgJ, hgr⟩ := hcSupp hu
  have hfix : MvPolynomial.aeval F u =
      MvPolynomial.rename ((Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
          Fin.castAdd (skewDim e + 1)) g := by
    rw [← hgr]
    exact pShift_fix t F hF g
  have hmem : MvPolynomial.rename ((Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
        Fin.castAdd (skewDim e + 1)) g ∈ pBaseIdeal C Γ H :=
    Ideal.mem_map_of_mem _ hgJ
  rw [smul_eq_mul, map_mul, hfix]
  exact Ideal.mul_mem_left _ _ hmem

omit V a he hh hd R h j N in
/-- Shifts fix the linear part (explicit form). -/
theorem pShift_fixLinear {e : ℕ} (C : SkewCoordinates e)
    (H : Option (Fin (e + (e + e) + (skewDim e + 1))) →
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (hH : ∀ i, H (some i) = MvPolynomial.X (some i)) (w : Fin e) :
    MvPolynomial.aeval H (pLiftLinear C w) = pLiftLinear C w := by
  unfold pLiftLinear
  simp only [map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, hH]

omit V a he hh hd R h j N in
/-- Exact colon by a deformed equation with nonzero scalar part. -/
theorem pColon_g {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (c : Fin e → ℂ) (w : Fin e) (hcw : c w ≠ 0) :
    (pBaseIdeal C Γ H).colon {pDeformed C c w} = pBaseIdeal C Γ H := by
  classical
  set t : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ :=
    MvPolynomial.C ((c w)⁻¹) * pLiftLinear C w with ht_def
  obtain ⟨hFnone, hFsome, hGnone, hGsome⟩ := pShift_vals t
  have hFL : MvPolynomial.aeval (pShiftF t) (pLiftLinear C w) = pLiftLinear C w :=
    pShift_fixLinear C _ (fun i => hFsome i) w
  have hGt : MvPolynomial.aeval (pShiftG t) t = t := by
    rw [ht_def, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
      pShift_fixLinear C _ (fun i => hGsome i) w]
  have hcomp : (MvPolynomial.aeval (pShiftG t)).comp
      (MvPolynomial.aeval (pShiftF t)) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro o
    cases o with
    | none =>
      show MvPolynomial.aeval (pShiftG t)
        (MvPolynomial.aeval (pShiftF t) (MvPolynomial.X none)) =
        MvPolynomial.X none
      rw [MvPolynomial.aeval_X, hFnone, map_add, MvPolynomial.aeval_X, hGnone,
        hGt, sub_add_cancel]
    | some i =>
      show MvPolynomial.aeval (pShiftG t)
        (MvPolynomial.aeval (pShiftF t) (MvPolynomial.X (some i))) =
        MvPolynomial.X (some i)
      rw [MvPolynomial.aeval_X, hFsome, MvPolynomial.aeval_X, hGsome]
  have hinv : ∀ q, MvPolynomial.aeval (pShiftG t)
      (MvPolynomial.aeval (pShiftF t) q) = q :=
    fun q => AlgHom.congr_fun hcomp q
  have hinvC : ∀ (s : ℂ), s ≠ 0 → ∀ (A : MvPolynomial
      (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ),
      A * MvPolynomial.C s ∈ pBaseIdeal C Γ H → A ∈ pBaseIdeal C Γ H := by
    intro s hs A hmem
    have hEq : (A * MvPolynomial.C s) * MvPolynomial.C (s⁻¹) = A := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hs, map_one, mul_one]
    have h2 : (A * MvPolynomial.C s) * MvPolynomial.C (s⁻¹) ∈ pBaseIdeal C Γ H :=
      Ideal.mul_mem_right _ _ hmem
    rw [hEq] at h2
    exact h2
  have hphi_g : MvPolynomial.aeval (pShiftF t) (pDeformed C c w) =
      -(MvPolynomial.C (c w) * MvPolynomial.X none) := by
    have htC : t * MvPolynomial.C (c w) = pLiftLinear C w := by
      calc t * MvPolynomial.C (c w)
          = pLiftLinear C w * (MvPolynomial.C ((c w)⁻¹) * MvPolynomial.C (c w)) := by
            rw [ht_def]; ring
        _ = pLiftLinear C w * MvPolynomial.C ((c w)⁻¹ * c w) := by rw [← map_mul]
        _ = pLiftLinear C w := by rw [inv_mul_cancel₀ hcw, map_one, mul_one]
    unfold pDeformed
    rw [map_sub, hFL, map_mul, MvPolynomial.aeval_X, hFnone,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, add_mul, htC]
    ring
  have hfwd : ∀ q, q * pDeformed C c w ∈ pBaseIdeal C Γ H →
      MvPolynomial.aeval (pShiftF t) q ∈ pBaseIdeal C Γ H := by
    intro q hmem
    have h1 : MvPolynomial.aeval (pShiftF t) (q * pDeformed C c w) ∈
        pBaseIdeal C Γ H :=
      pShift_preserves C Γ H t _ (fun i => hFsome i) _ hmem
    rw [map_mul, hphi_g] at h1
    have e : MvPolynomial.aeval (pShiftF t) q *
        (-(MvPolynomial.C (c w) * MvPolynomial.X none)) =
        ((MvPolynomial.aeval (pShiftF t) q * MvPolynomial.X none)) *
        MvPolynomial.C (-c w) := by
      rw [← neg_mul, ← map_neg]
      ring
    rw [e] at h1
    have hPX := hinvC _ (neg_ne_zero.mpr hcw) _ h1
    exact pBaseMem_of_mul_mu C Γ H _ hPX
  apply le_antisymm
  · intro q hq
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hq
    have hphi := hfwd q hq
    have hback : q ∈ pBaseIdeal C Γ H := by
      have h2 : MvPolynomial.aeval (pShiftG t)
          (MvPolynomial.aeval (pShiftF t) q) ∈ pBaseIdeal C Γ H :=
        pShift_preserves C Γ H t _ (fun i => hGsome i) _ hphi
      rw [hinv] at h2
      exact h2
    exact hback
  · intro q hq
    apply Submodule.mem_colon_singleton.mpr
    rw [smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hq

omit V a he hh hd R h j N in
theorem pWeightNonzero {e : ℕ}
    (o : Option (Fin (e + (e + e) + (skewDim e + 1)))) :
    ∃ j, 1 ≤ (pWeight e) o j := by
  cases o with
  | none => exact ⟨0, by simp [pWeight, HilbertMulti.tripleDegree]⟩
  | some i =>
    cases i using Fin.addCases with
    | left i =>
      cases i using Fin.addCases with
      | left l => exact ⟨0, by simp [pWeight, HilbertMulti.blockWeight,
          HilbertMulti.tripleBlocks, HilbertMulti.tripleDegree]⟩
      | right i => exact ⟨1, by simp [pWeight, HilbertMulti.blockWeight,
          HilbertMulti.tripleBlocks, HilbertMulti.tripleDegree]⟩
    | right k => exact ⟨2, by simp [pWeight, HilbertMulti.blockWeight,
        HilbertMulti.tripleBlocks, HilbertMulti.tripleDegree]⟩

omit V a he hh hd R h j N in
theorem weightBoundAux {σ : Type*} (w : σ → (Fin 3 →₀ ℕ))
    (hw : ∀ o, ∃ j, 1 ≤ w o j)
    (a : σ →₀ ℕ) (d : Fin 3 →₀ ℕ)
    (ha : Finsupp.weight w a = d) (o : σ) :
    a o ≤ d 0 + d 1 + d 2 := by
  classical
  obtain ⟨j, hj⟩ := hw o
  have h1 : a o • w o ≤ Finsupp.weight w a := by
    rw [Finsupp.weight_apply]
    show (fun i c => c • w i) o (a o) ≤ _
    have hrr : (Finsupp.single o (a o)).sum (fun i c => c • w i) =
        (fun i c => c • w i) o (a o) :=
      Finsupp.sum_single_index
        (show (fun i c => c • w i) o (0 : ℕ) = 0 from zero_smul _ _)
    rw [← hrr]
    exact Finsupp.single_le_sum _ (fun _ _ => bot_le) o
  rw [ha] at h1
  have h2 : (a o • w o) j ≤ d j := h1 j
  rw [Finsupp.smul_apply, smul_eq_mul] at h2
  have h3 : a o ≤ d j := by
    calc a o = a o * 1 := (mul_one _).symm
      _ ≤ a o * w o j := Nat.mul_le_mul_left _ hj
      _ ≤ d j := h2
  calc a o ≤ d j := h3
    _ ≤ d 0 + d 1 + d 2 := by
      fin_cases j
      · show d (0 : Fin 3) ≤ d 0 + d 1 + d 2; omega
      · show d (1 : Fin 3) ≤ d 0 + d 1 + d 2; omega
      · show d (2 : Fin 3) ≤ d 0 + d 1 + d 2; omega

omit V a he hh hd R h j N in
theorem pWeightBound {e : ℕ} (d : Fin 3 →₀ ℕ)
    (a : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ)
    (ha : Finsupp.weight (pWeight e) a = d)
    (o : Option (Fin (e + (e + e) + (skewDim e + 1)))) :
    a o ≤ d 0 + d 1 + d 2 :=
  weightBoundAux (pWeight e) (fun o => pWeightNonzero o) a d ha o

omit V a he hh hd R h j N in
theorem tripleWeightNonzero {e : ℕ}
    (o : Fin (e + (e + e) + (skewDim e + 1))) :
    ∃ j, 1 ≤ (HilbertMulti.blockWeight
      (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) o j := by
  cases o using Fin.addCases with
  | left i =>
    cases i using Fin.addCases with
    | left l => exact ⟨0, by simp [HilbertMulti.blockWeight,
        HilbertMulti.tripleBlocks, HilbertMulti.tripleDegree]⟩
    | right i => exact ⟨1, by simp [HilbertMulti.blockWeight,
        HilbertMulti.tripleBlocks, HilbertMulti.tripleDegree]⟩
  | right k => exact ⟨2, by simp [HilbertMulti.blockWeight,
      HilbertMulti.tripleBlocks, HilbertMulti.tripleDegree]⟩

omit V a he hh hd R h j N in
theorem tripleWeightBound {e : ℕ} (d : Fin 3 →₀ ℕ)
    (a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ)
    (ha : Finsupp.weight (HilbertMulti.blockWeight
      (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) a = d)
    (o : Fin (e + (e + e) + (skewDim e + 1))) :
    a o ≤ d 0 + d 1 + d 2 :=
  weightBoundAux _ (fun o => tripleWeightNonzero o) a d ha o

omit V a he hh hd R h j N in
theorem pExponentsFinite {e : ℕ} (d : Fin 3 →₀ ℕ) :
    Finite ↥{a : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
      Finsupp.weight (pWeight e) a = d} := by
  classical
  let S : Set (Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ) :=
    {a | Finsupp.weight (pWeight e) a = d}
  let F : Finset (Option (Fin (e + (e + e) + (skewDim e + 1))) → ℕ) :=
    Fintype.piFinset fun _ => Finset.range (d 0 + d 1 + d 2 + 1)
  show Finite ↥S
  have hmem : ∀ a : ↥S, Finsupp.equivFunOnFinite (a : Option
      (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ) ∈ ↑F := by
    intro a
    simp only [F, Fintype.mem_piFinset, Finset.mem_range]
    intro o
    have hle : (a : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ) o ≤
        d 0 + d 1 + d 2 :=
      pWeightBound d _ a.2 o
    have heq : Finsupp.equivFunOnFinite (a : Option
        (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ) o =
        (a : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ) o := rfl
    omega
  apply Finite.of_injective (f := fun a : ↥S => (⟨Finsupp.equivFunOnFinite
    (a : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ), hmem a⟩ : ↥(↑F : Set _)))
  intro a b hab
  apply Subtype.ext
  exact Finsupp.equivFunOnFinite.injective (Subtype.mk.inj hab)

omit V a he hh hd R h j N in
theorem pPiece_eq {e : ℕ} (d : Fin 3 →₀ ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule ℂ (pWeight e) d =
      MvPolynomial.restrictSupport ℂ {a : Option
        (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
        Finsupp.weight (pWeight e) a = d} := by
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  rfl

omit V a he hh hd R h j N in
instance pPieceFinite {e : ℕ} (d : Fin 3 →₀ ℕ) :
    Module.Finite ℂ (MvPolynomial.weightedHomogeneousSubmodule ℂ (pWeight e) d) := by
  classical
  rw [pPiece_eq]
  haveI : Finite ↥{a : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
      Finsupp.weight (pWeight e) a = d} := pExponentsFinite d
  haveI := Fintype.ofFinite ↥{a : Option
    (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
    Finsupp.weight (pWeight e) a = d}
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ _)

omit V a he hh hd R h j N in
/-- Exact first Koszul rank step over a deformed equation. -/
theorem pRankStep_g {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (c : Fin e → ℂ) (w : Fin e) (hcw : c w ≠ 0) (s t u : ℕ) :
    Module.finrank ℂ (HilbertMulti.sectionSpace (pWeight e)
        (Ideal.span {pDeformed C c w} ⊔ pBaseIdeal C Γ H)
        (HilbertMulti.tripleDegree s t u + HilbertMulti.tripleDegree 1 0 1)) +
      Module.finrank ℂ (HilbertMulti.sectionSpace (pWeight e)
        (pBaseIdeal C Γ H) (HilbertMulti.tripleDegree s t u)) =
      Module.finrank ℂ (HilbertMulti.sectionSpace (pWeight e)
        (pBaseIdeal C Γ H)
        (HilbertMulti.tripleDegree s t u + HilbertMulti.tripleDegree 1 0 1)) := by
  have h := HilbertMulti.colon_rank_step (pWeight e) (pBaseIdeal C Γ H)
    (pBaseHom C Γ H) (pDeformed C c w) (pDeformed_weighted C c w)
    (HilbertMulti.tripleDegree s t u)
  rw [pColon_g C Γ H c w hcw] at h
  exact h

omit V a he hh hd R h j N in
/-- Per-term P-world homogeneity for the mu-product comparison map. -/
theorem pTermHom {e : ℕ} (g : Poly (e + (e + e) + (skewDim e + 1)))
    (s t u j : ℕ) (hs : j ≤ s) (hu : j ≤ u)
    (hg : g.IsWeightedHomogeneous
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
      (HilbertMulti.tripleDegree (s - j) t (u - j))) :
    ((MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) g) *
      MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ)).IsWeightedHomogeneous
      (pWeight e) (HilbertMulti.tripleDegree s t u) := by
  have hRen := pRenameHom g _ hg
  have hMu : (MvPolynomial.monomial (Finsupp.single (none :
      Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ) :
      MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).IsWeightedHomogeneous
      (pWeight e) (j • HilbertMulti.tripleDegree 1 0 1) := by
    rw [← MvPolynomial.X_pow_eq_monomial]
    exact (pMu_weighted e).pow j
  have hMul := hRen.mul hMu
  have hadd : HilbertMulti.tripleDegree (s - j) t (u - j) + j • HilbertMulti.tripleDegree 1 0 1 =
      HilbertMulti.tripleDegree s t u := by
    ext k
    fin_cases k <;>
      simp [HilbertMulti.tripleDegree, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] <;>
      omega
  rwa [hadd] at hMul

omit V a he hh hd R h j N in
/-- Renaming triple-pullback members into the P-world base ideal. -/
theorem pRenamePullMem {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (p : Poly (e + (e + e) + (skewDim e + 1)))
    (hp : p ∈ Ideal.map (MvPolynomial.rename
      (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
      (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H)))) :
    MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) p ∈ pBaseIdeal C Γ H := by
  have hspan : p ∈ Submodule.span (Poly (e + (e + e) + (skewDim e + 1)))
      (⇑(MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1)))) ''
        ↑(MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H)))) := hp
  obtain ⟨c, hcSupp, hcSum⟩ := Submodule.mem_span_set.mp hspan
  have hsum : (∑ t ∈ c.support, (c t) • t) = p := hcSum
  rw [← hsum, map_sum]
  apply Ideal.sum_mem
  intro u hu
  obtain ⟨g, hgJ, hgr⟩ := hcSupp hu
  have hmem : MvPolynomial.rename ((Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) ∘
        Fin.castAdd (skewDim e + 1)) g ∈ pBaseIdeal C Γ H :=
    Ideal.mem_map_of_mem _ hgJ
  set a := c u with ha
  rw [← hgr, smul_eq_mul, map_mul, MvPolynomial.rename_rename]
  exact Ideal.mul_mem_left _ _ hmem

omit V a he hh hd R h j N in
/-- Base weight equation and mu-bounds from a P-world weight equation. -/
theorem pFiberWeight {e : ℕ}
    (d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ)
    (s t u j : ℕ) (hwt : Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u)
    (hmu : pMuPart d = j) :
    Finsupp.weight (HilbertMulti.blockWeight
        (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) (pBasePart d) =
      HilbertMulti.tripleDegree (s - j) t (u - j) ∧
    j ≤ s ∧ j ≤ u := by
  classical
  have hsplit : d = (pBasePart d).mapDomain (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) +
      Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) j := by
    rw [← hmu]
    exact pSplit_eq d
  have hbase : Finsupp.weight (pWeight e)
      ((pBasePart d).mapDomain (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))) =
      Finsupp.weight (HilbertMulti.blockWeight
        (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) (pBasePart d) := by
    have hPw : ∀ i : Fin (e + (e + e) + (skewDim e + 1)),
        (pWeight e) (Option.some i) =
          HilbertMulti.blockWeight
            (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) i :=
      fun i => rfl
    have hre : (((pBasePart d).mapDomain (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))).sum
        (fun i c => c • (pWeight e) i)) =
        (pBasePart d).sum (fun a m => (fun i c => c • (pWeight e) i) (Option.some a) m) :=
      Finsupp.sum_mapDomain_index
        (fun b => show (fun i c => c • (pWeight e) i) b (0 : ℕ) = 0 from zero_smul _ _)
        (fun b m₁ m₂ => show (fun i c => c • (pWeight e) i) b (m₁ + m₂) = _ from
          add_smul _ _ _)
    rw [Finsupp.weight_apply, Finsupp.weight_apply, hre]
    simp only [hPw]
  have hmuw : Finsupp.weight (pWeight e)
      (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) j) =
      j • HilbertMulti.tripleDegree 1 0 1 := by
    rw [Finsupp.weight_single]
    rfl
  have hsum : Finsupp.weight (HilbertMulti.blockWeight
      (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) (pBasePart d) +
      j • HilbertMulti.tripleDegree 1 0 1 =
      HilbertMulti.tripleDegree s t u := by
    rw [← hbase, ← hmuw, ← map_add, ← hsplit]
    exact hwt
  have hj_s : j ≤ s := by
    have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) hsum
    rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h0
    have eD : ((HilbertMulti.tripleDegree 1 0 1 : Fin 3 →₀ ℕ)) 0 = 1 := rfl
    have eS : ((HilbertMulti.tripleDegree s t u : Fin 3 →₀ ℕ)) 0 = s := rfl
    rw [eD, eS] at h0
    omega
  have hj_u : j ≤ u := by
    have h2 := congrArg (fun f : Fin 3 →₀ ℕ => f 2) hsum
    rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h2
    have eD : ((HilbertMulti.tripleDegree 1 0 1 : Fin 3 →₀ ℕ)) 2 = 1 := rfl
    have eS : ((HilbertMulti.tripleDegree s t u : Fin 3 →₀ ℕ)) 2 = u := rfl
    rw [eD, eS] at h2
    omega
  have hwt_eq : Finsupp.weight (HilbertMulti.blockWeight
      (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) (pBasePart d) =
      HilbertMulti.tripleDegree (s - j) t (u - j) := by
    ext k
    fin_cases k
    · show (Finsupp.weight (HilbertMulti.blockWeight
          (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) (pBasePart d)) 0 =
          (HilbertMulti.tripleDegree (s - j) t (u - j)) 0
      have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) hsum
      rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h0
      have eD : ((HilbertMulti.tripleDegree 1 0 1 : Fin 3 →₀ ℕ)) 0 = 1 := rfl
      have eS : ((HilbertMulti.tripleDegree s t u : Fin 3 →₀ ℕ)) 0 = s := rfl
      have eT : ((HilbertMulti.tripleDegree (s - j) t (u - j) : Fin 3 →₀ ℕ)) 0 = s - j := rfl
      rw [eD, eS] at h0
      rw [eT]
      omega
    · show (Finsupp.weight (HilbertMulti.blockWeight
          (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) (pBasePart d)) 1 =
          (HilbertMulti.tripleDegree (s - j) t (u - j)) 1
      have h1 := congrArg (fun f : Fin 3 →₀ ℕ => f 1) hsum
      rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
      have eD : ((HilbertMulti.tripleDegree 1 0 1 : Fin 3 →₀ ℕ)) 1 = 0 := rfl
      have eS : ((HilbertMulti.tripleDegree s t u : Fin 3 →₀ ℕ)) 1 = t := rfl
      have eT : ((HilbertMulti.tripleDegree (s - j) t (u - j) : Fin 3 →₀ ℕ)) 1 = t := rfl
      rw [eD, eS] at h1
      rw [eT]
      omega
    · show (Finsupp.weight (HilbertMulti.blockWeight
          (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) (pBasePart d)) 2 =
          (HilbertMulti.tripleDegree (s - j) t (u - j)) 2
      have h2 := congrArg (fun f : Fin 3 →₀ ℕ => f 2) hsum
      rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h2
      have eD : ((HilbertMulti.tripleDegree 1 0 1 : Fin 3 →₀ ℕ)) 2 = 1 := rfl
      have eS : ((HilbertMulti.tripleDegree s t u : Fin 3 →₀ ℕ)) 2 = u := rfl
      have eT : ((HilbertMulti.tripleDegree (s - j) t (u - j) : Fin 3 →₀ ℕ)) 2 = u - j := rfl
      rw [eD, eS] at h2
      rw [eT]
      omega
  exact ⟨hwt_eq, hj_s, hj_u⟩


omit V a he hh hd R h j N in
/-- Block-sum and weight-fiber pieces coincide as submodules. -/
theorem tripleSubEq {e : ℕ} (s t u : ℕ) :
    MvPolynomial.restrictSupport ℂ {a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
      (∑ i : Fin e, a (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s ∧
      (∑ i : Fin (e + e), a (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
      (∑ i : Fin (skewDim e + 1), a (Fin.natAdd (e + (e + e)) i)) = u} =
    MvPolynomial.restrictSupport ℂ {a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
      Finsupp.weight (HilbertMulti.blockWeight
        (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) a =
        HilbertMulti.tripleDegree s t u} := by
  rw [← HilbertMulti.tripleBlockPiece,
    MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  rfl

omit V a he hh hd R h j N in
/-- Fin-indexed single-sum mu-coefficient isolation. -/
theorem psiso_mu_fin {e : ℕ} (N : ℕ)
    (G : Fin (N + 1) → Poly (e + (e + e) + (skewDim e + 1)))
    (d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ)
    (L : Fin (N + 1)) (hd_mu : d none = ↑L) :
    (∑ l ∈ Finset.univ, ((MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) (G l)) *
      (MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑l : ℕ)) (1 : ℂ))).coeff d) =
    (((MvPolynomial.rename (Option.some :
      Fin (e + (e + e) + (skewDim e + 1)) →
        Option (Fin (e + (e + e) + (skewDim e + 1)))) (G L)) *
      (MvPolynomial.monomial (Finsupp.single (none :
        Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑L : ℕ)) (1 : ℂ))).coeff d) := by
  classical
  apply Finset.sum_eq_single L
  · intro l _ hl
    have hdis : d ∉ ((MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (G l)) *
        (MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑l : ℕ)) (1 : ℂ))).support := by
      intro hmem
      apply hl
      have hpt : d none = (↑l : ℕ) := pSuppMu _ _ _ hmem
      have h1 := hpt
      rw [hd_mu] at h1
      exact Fin.ext h1.symm
    exact MvPolynomial.notMem_support_iff.mp hdis
  · intro h
    exact absurd (Finset.mem_univ L) h


omit V a he hh hd R h j N in
/-- P-world kernel ranks factor as a mu-sum of triple-pullback kernel ranks. -/
theorem pKernelProduct {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (s t u : ℕ) :
    Module.finrank ℂ (sectionKernel (pBaseIdeal C Γ H)
      {d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
        Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u}) =
    ∑ j ∈ Finset.range (Nat.min s u + 1),
      Module.finrank ℂ (sectionKernel
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - j ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - j}) := by
  classical
  haveI := pExponentsFinite (e := e) (HilbertMulti.tripleDegree s t u)
  haveI := moduleFinite_restrictSupport
    {d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
      Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u}
  haveI : Module.Finite ℂ ↥(sectionKernel (pBaseIdeal C Γ H)
      {d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
        Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u}) :=
    Module.Finite.of_injective (sectionKernel (pBaseIdeal C Γ H)
      {d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
        Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u}).subtype
      Subtype.val_injective
  have hFreeMu : ∀ j : Fin (Nat.min s u + 1), Module.Free ℂ ↥(sectionKernel
      (Ideal.map (MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H))))
      {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
        (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - ↑j ∧
        (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
        (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - ↑j}) :=
    fun j => Module.Free.of_divisionRing ℂ ↥(sectionKernel
      (Ideal.map (MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H))))
      {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
        (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - ↑j ∧
        (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
        (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - ↑j})
  have hFinSetMu : ∀ j : ℕ, Finite ↥{d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
      (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - j ∧
      (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
      (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - j} :=
    fun j => finite_tripleExponents (n := e) (m := e + e) (o := skewDim e + 1)
      (s := s - j) (t := t) (u := u - j)
  have hFinResMu : ∀ j : ℕ, Module.Finite ℂ ↥(MvPolynomial.restrictSupport ℂ
      {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
        (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - j ∧
        (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
        (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - j}) :=
    fun j => moduleFinite_restrictSupport _
  have hFinMu : ∀ j : Fin (Nat.min s u + 1), Module.Finite ℂ ↥(sectionKernel
      (Ideal.map (MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H))))
      {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
        (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - ↑j ∧
        (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
        (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - ↑j}) :=
    fun j => Module.Finite.of_injective (sectionKernel
      (Ideal.map (MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H))))
      {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
        (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - ↑j ∧
        (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
        (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - ↑j}).subtype
      Subtype.val_injective
  let Psi : (∀ j : Fin (Nat.min s u + 1),
      ↥(sectionKernel
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - ↑j ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - ↑j})) →ₗ[ℂ]
      ↥(sectionKernel (pBaseIdeal C Γ H)
        {d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
          Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u}) := {
      toFun := fun f => ⟨⟨∑ j ∈ Finset.univ,
        (MvPolynomial.rename (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1))))
          ((((f j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
          MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
        (MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
          MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ), by
            have hEach : ∀ j : Fin (Nat.min s u + 1),
                ((MvPolynomial.rename (Option.some :
                  Fin (e + (e + e) + (skewDim e + 1)) →
                    Option (Fin (e + (e + e) + (skewDim e + 1))))
                  ((((f j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
                (MvPolynomial.monomial (Finsupp.single (none :
                  Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)).IsWeightedHomogeneous
                  (pWeight e) (HilbertMulti.tripleDegree s t u) := by
              intro j
              have hj_s : (↑j : ℕ) ≤ s :=
                Nat.le_trans (Nat.le_of_lt_add_one j.2) (Nat.min_le_left s u)
              have hj_u : (↑j : ℕ) ≤ u :=
                Nat.le_trans (Nat.le_of_lt_add_one j.2) (Nat.min_le_right s u)
              have hTripleHom : ((((f j).val).val) : Poly (e + (e + e) + (skewDim e + 1))).IsWeightedHomogeneous
                  (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
                  (HilbertMulti.tripleDegree (s - ↑j) t (u - ↑j)) := by
                rw [← MvPolynomial.mem_weightedHomogeneousSubmodule, HilbertMulti.tripleBlockPiece]
                exact (f j).val.property
              exact pTermHom _ _ _ _ _ hj_s hj_u hTripleHom
            have hSumHom : (∑ j ∈ Finset.univ,
                (MvPolynomial.rename (Option.some :
                  Fin (e + (e + e) + (skewDim e + 1)) →
                    Option (Fin (e + (e + e) + (skewDim e + 1))))
                  ((((f j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
                (MvPolynomial.monomial (Finsupp.single (none :
                  Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)).IsWeightedHomogeneous
                (pWeight e) (HilbertMulti.tripleDegree s t u) :=
              MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun j _ => hEach j)
            rw [← pPiece_eq]
            exact hSumHom⟩, by
            have hSumIdeal : (∑ j ∈ Finset.univ,
                (MvPolynomial.rename (Option.some :
                  Fin (e + (e + e) + (skewDim e + 1)) →
                    Option (Fin (e + (e + e) + (skewDim e + 1))))
                  ((((f j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
                (MvPolynomial.monomial (Finsupp.single (none :
                  Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) ∈
                pBaseIdeal C Γ H := by
              apply Ideal.sum_mem
              intro j _
              have hker := (f j).property
              have h0 : ((Ideal.Quotient.mkₐ ℂ (Ideal.map (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                  (MvPolynomial.vanishingIdeal ℂ
                    (pairRepresentatives (liftedParameterBase C Γ H))))).toLinearMap.domRestrict
                  (MvPolynomial.restrictSupport ℂ {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
                    (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - ↑j ∧
                    (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
                    (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - ↑j})) (f j).val = 0 :=
                LinearMap.mem_ker.mp hker
              have hmk : (Ideal.Quotient.mkₐ ℂ (Ideal.map (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                  (MvPolynomial.vanishingIdeal ℂ
                    (pairRepresentatives (liftedParameterBase C Γ H))))) ((((f j).val).val)) = 0 := by
                simpa using h0
              have hJ : ((((f j).val).val)) ∈ Ideal.map (MvPolynomial.rename
                  (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                  (MvPolynomial.vanishingIdeal ℂ
                    (pairRepresentatives (liftedParameterBase C Γ H))) := by
                have h0mk : Ideal.Quotient.mk (Ideal.map (MvPolynomial.rename
                    (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
                    (MvPolynomial.vanishingIdeal ℂ
                      (pairRepresentatives (liftedParameterBase C Γ H)))) ((((f j).val).val)) = 0 := by
                  simpa using hmk
                exact Ideal.Quotient.eq_zero_iff_mem.mp h0mk
              have hRenMem : (MvPolynomial.rename (Option.some :
                  Fin (e + (e + e) + (skewDim e + 1)) →
                    Option (Fin (e + (e + e) + (skewDim e + 1))))
                  ((((f j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) ∈
                pBaseIdeal C Γ H :=
                pRenamePullMem C Γ H _ hJ
              exact Ideal.mul_mem_right _ _ hRenMem
            apply LinearMap.mem_ker.mpr
            have hmk : (Ideal.Quotient.mkₐ ℂ (pBaseIdeal C Γ H))
              (∑ j ∈ Finset.univ,
                (MvPolynomial.rename (Option.some :
                  Fin (e + (e + e) + (skewDim e + 1)) →
                    Option (Fin (e + (e + e) + (skewDim e + 1))))
                  ((((f j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
                (MvPolynomial.monomial (Finsupp.single (none :
                  Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) = 0 := by
              have h0mk : Ideal.Quotient.mk (pBaseIdeal C Γ H)
                (∑ j ∈ Finset.univ,
                  (MvPolynomial.rename (Option.some :
                    Fin (e + (e + e) + (skewDim e + 1)) →
                      Option (Fin (e + (e + e) + (skewDim e + 1))))
                    ((((f j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
                    MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
                  (MvPolynomial.monomial (Finsupp.single (none :
                    Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
                    MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) = 0 :=
                Ideal.Quotient.eq_zero_iff_mem.mpr hSumIdeal
              simpa using h0mk
            simpa using hmk⟩,
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        simp only [Pi.add_apply, Submodule.coe_add, map_add, add_mul, Finset.sum_add_distrib],
      map_smul' := by
        intro c x
        apply Subtype.ext
        apply Subtype.ext
        have hRenSmul : ∀ (p : Poly (e + (e + e) + (skewDim e + 1))),
            MvPolynomial.rename (Option.some :
              Fin (e + (e + e) + (skewDim e + 1)) →
                Option (Fin (e + (e + e) + (skewDim e + 1))))
              (c • p) =
            c • MvPolynomial.rename (Option.some :
              Fin (e + (e + e) + (skewDim e + 1)) →
                Option (Fin (e + (e + e) + (skewDim e + 1))))
              p := by
          intro p
          simp [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, MvPolynomial.rename_C]
        simp only [Pi.smul_apply, Submodule.coe_smul, hRenSmul, smul_mul_assoc, Finset.smul_sum,
          RingHom.id_apply] }
  have hPsiSurj : Function.Surjective Psi := by
    classical
    intro y
    have hPmem : (y.val.val : MvPolynomial (Option
        (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) ∈ pBaseIdeal C Γ H := by
      have hker := y.property
      have h0 : ((Ideal.Quotient.mkₐ ℂ (pBaseIdeal C Γ H)).toLinearMap.domRestrict
          (MvPolynomial.restrictSupport ℂ {d : Option
            (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
            Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u})) y.val = 0 :=
        LinearMap.mem_ker.mp hker
      have hmk : (Ideal.Quotient.mkₐ ℂ (pBaseIdeal C Γ H)) (y.val.val) = 0 := by
        simpa using h0
      have h0mk : Ideal.Quotient.mk (pBaseIdeal C Γ H) (y.val.val) = 0 := by
        simpa using hmk
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0mk
    have hPsupp : ((y.val.val : MvPolynomial (Option
        (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support : Set _) ⊆
        {d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
          Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u} :=
      y.val.property
    have hGA0 : ∀ j : ℕ,
        j ∉ (y.val.val : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support.image (fun d => pMuPart d) →
        (∑ d ∈ (y.val.val : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = j,
          MvPolynomial.monomial (pBasePart d)
            ((y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) = 0 := by
      intro j hj
      have hempty : (y.val.val : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support.filter
          (fun d => pMuPart d = j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro d hd heq
        exact hj (heq ▸ Finset.mem_image_of_mem _ hd)
      rw [hempty, Finset.sum_empty]
    have hFAsub : ∀ j : ℕ,
        j ∈ (y.val.val : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support.image (fun d => pMuPart d) →
        j ≤ Nat.min s u := by
      intro j hj
      obtain ⟨d, hd, hjd⟩ := Finset.mem_image.mp hj
      obtain ⟨_, hjs, hju⟩ := pFiberWeight d s t u j ((hPsupp hd)) hjd
      exact Nat.le_min.mpr ⟨hjs, hju⟩
    have hGsuppW : ∀ j : ℕ,
        (∑ d ∈ (y.val.val : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = j,
          MvPolynomial.monomial (pBasePart d)
            ((y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) ∈
        MvPolynomial.restrictSupport ℂ {a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          Finsupp.weight (HilbertMulti.blockWeight
            (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) a =
            HilbertMulti.tripleDegree (s - j) t (u - j)} := by
      intro j
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro b hb
      have hmem := MvPolynomial.support_sum hb
      rw [Finset.mem_biUnion] at hmem
      obtain ⟨d, hd, hbd⟩ := hmem
      obtain ⟨hd_mem, hdpt⟩ := Finset.mem_filter.mp hd
      have hmono : b ∈ (MvPolynomial.monomial (pBasePart d)
          ((y.val.val : MvPolynomial (Option
            (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)).support := hbd
      have hbeq : b = pBasePart d :=
        Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hmono)
      obtain ⟨hwt_eq, _, _⟩ := pFiberWeight d s t u _ ((hPsupp hd_mem)) hdpt
      rw [hbeq]
      exact hwt_eq
    have hGsupp : ∀ q : Fin (Nat.min s u + 1),
        (∑ d ∈ (y.val.val : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = ((q.val)),
          MvPolynomial.monomial (pBasePart d)
            ((y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) ∈
        MvPolynomial.restrictSupport ℂ {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - ↑q ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - ↑q} := by
      intro q
      have hW := hGsuppW (↑q : ℕ)
      rw [tripleSubEq (e := e) (s - ↑q) t (u - ↑q)]
      exact hW
    have hGAJ : ∀ L : ℕ,
        (∑ d ∈ (y.val.val : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d)
            ((y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) ∈
        Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))) := by
      intro L
      obtain ⟨T, G0, hcof, hG0J, hPeq⟩ := pMapSpan C Γ H _ hPmem
      have hEq : ∀ a : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ,
          (∑ d ∈ (y.val.val : MvPolynomial (Option
            (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = L,
            MvPolynomial.monomial (pBasePart d)
              ((y.val.val : MvPolynomial (Option
                (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)).coeff a =
          (∑ t ∈ T, MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) *
            (∑ d ∈ (hcof t).support with pMuPart d = L,
              MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d))).coeff a :=
        fun a => pFiberCompare C Γ H _ T G0 hcof hPeq L a
      have hPolyEq : (∑ d ∈ (y.val.val : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = L,
          MvPolynomial.monomial (pBasePart d)
            ((y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) =
          (∑ t ∈ T, MvPolynomial.rename (Fin.castAdd (skewDim e + 1)) (G0 t) *
            (∑ d ∈ (hcof t).support with pMuPart d = L,
              MvPolynomial.monomial (pBasePart d) ((hcof t).coeff d))) := by
        apply MvPolynomial.ext
        intro a
        exact hEq a
      rw [hPolyEq]
      apply Ideal.sum_mem
      intro t ht
      exact Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _ (hG0J t ht))
    refine ⟨fun q => ⟨⟨∑ d ∈ (y.val.val : MvPolynomial (Option
        (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = ((q.val)),
        MvPolynomial.monomial (pBasePart d)
          ((y.val.val : MvPolynomial (Option
            (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d), hGsupp q⟩, ?_⟩, ?_⟩
    · have hmk : (Ideal.Quotient.mkₐ ℂ (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H)))))
          (∑ d ∈ (y.val.val : MvPolynomial (Option
            (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = ((q.val)),
            MvPolynomial.monomial (pBasePart d)
              ((y.val.val : MvPolynomial (Option
                (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) = 0 := by
        have h0mk : Ideal.Quotient.mk (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))
            (∑ d ∈ (y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = ((q.val)),
              MvPolynomial.monomial (pBasePart d)
                ((y.val.val : MvPolynomial (Option
                  (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (hGAJ _)
        simpa using h0mk
      exact LinearMap.mem_ker.mpr (by simpa using hmk)
    · have hPA := psplit_general (y.val.val : MvPolynomial (Option
        (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
      have hPtSum : (y.val.val : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) =
          ∑ q' ∈ (Finset.univ : Finset (Fin (Nat.min s u + 1))),
          (MvPolynomial.rename (Option.some :
            Fin (e + (e + e) + (skewDim e + 1)) →
              Option (Fin (e + (e + e) + (skewDim e + 1))))
            (∑ d ∈ (y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with
              pMuPart d = ((q'.val)),
              MvPolynomial.monomial (pBasePart d)
                ((y.val.val : MvPolynomial (Option
                  (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) :
            MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
          MvPolynomial.monomial (Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) (((q'.val)))) (1 : ℂ) := by
        have hsub : (y.val.val : MvPolynomial (Option
            (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support.image (fun d => pMuPart d) ⊆
            Finset.range (Nat.min s u + 1) := by
          intro x hx
          rw [Finset.mem_range]
          have hxle := hFAsub x hx
          omega
        have hzero : ∀ x ∈ Finset.range (Nat.min s u + 1),
            x ∉ (y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support.image (fun d => pMuPart d) →
            ((MvPolynomial.rename (Option.some :
              Fin (e + (e + e) + (skewDim e + 1)) →
                Option (Fin (e + (e + e) + (skewDim e + 1))))
              (∑ d ∈ (y.val.val : MvPolynomial (Option
                (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = x,
                MvPolynomial.monomial (pBasePart d)
                  ((y.val.val : MvPolynomial (Option
                    (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) :
              MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
            MvPolynomial.monomial (Finsupp.single (none :
              Option (Fin (e + (e + e) + (skewDim e + 1)))) x) (1 : ℂ)) = 0 := by
          intro x _ hx
          have hxv : (∑ d ∈ (y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = x,
              MvPolynomial.monomial (pBasePart d)
                ((y.val.val : MvPolynomial (Option
                  (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) = 0 :=
            hGA0 x hx
          rw [hxv, map_zero, zero_mul]
        calc (y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
            = ∑ j ∈ (y.val.val : MvPolynomial (Option
              (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support.image (fun d => pMuPart d),
              (MvPolynomial.rename (Option.some :
                Fin (e + (e + e) + (skewDim e + 1)) →
                  Option (Fin (e + (e + e) + (skewDim e + 1))))
                (∑ d ∈ (y.val.val : MvPolynomial (Option
                  (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = j,
                  MvPolynomial.monomial (pBasePart d)
                    ((y.val.val : MvPolynomial (Option
                      (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) :
                MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
              MvPolynomial.monomial (Finsupp.single (none :
                Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ) := hPA
          _ = ∑ j ∈ Finset.range (Nat.min s u + 1),
              (MvPolynomial.rename (Option.some :
                Fin (e + (e + e) + (skewDim e + 1)) →
                  Option (Fin (e + (e + e) + (skewDim e + 1))))
                (∑ d ∈ (y.val.val : MvPolynomial (Option
                  (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = j,
                  MvPolynomial.monomial (pBasePart d)
                    ((y.val.val : MvPolynomial (Option
                      (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) :
                MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
              MvPolynomial.monomial (Finsupp.single (none :
                Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ) :=
              Finset.sum_subset hsub hzero
          _ = ∑ q' ∈ (Finset.univ : Finset (Fin (Nat.min s u + 1))),
              (MvPolynomial.rename (Option.some :
                Fin (e + (e + e) + (skewDim e + 1)) →
                  Option (Fin (e + (e + e) + (skewDim e + 1))))
                (∑ d ∈ (y.val.val : MvPolynomial (Option
                  (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with
                  pMuPart d = ((q'.val)),
                  MvPolynomial.monomial (pBasePart d)
                    ((y.val.val : MvPolynomial (Option
                      (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) :
                MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
              MvPolynomial.monomial (Finsupp.single (none :
                Option (Fin (e + (e + e) + (skewDim e + 1)))) (((q'.val)))) (1 : ℂ) :=
              (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
                (MvPolynomial.rename (Option.some :
                  Fin (e + (e + e) + (skewDim e + 1)) →
                    Option (Fin (e + (e + e) + (skewDim e + 1))))
                  (∑ d ∈ (y.val.val : MvPolynomial (Option
                    (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).support with pMuPart d = j,
                    MvPolynomial.monomial (pBasePart d)
                      ((y.val.val : MvPolynomial (Option
                        (Fin (e + (e + e) + (skewDim e + 1)))) ℂ).coeff d)) :
                  MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
                MvPolynomial.monomial (Finsupp.single (none :
                  Option (Fin (e + (e + e) + (skewDim e + 1)))) j) (1 : ℂ))
                (Nat.min s u + 1)).symm
      apply Subtype.ext
      apply Subtype.ext
      exact hPtSum.symm
  have hPsiInj : Function.Injective Psi := by
    intro f1 f2 h12
    have h12poly : (∑ j ∈ Finset.univ, (MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
          (((((f1) j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
          MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
        (MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
          MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) =
        (∑ j ∈ Finset.univ, (MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
          (((((f2) j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
          MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
        (MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
          MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) :=
      congrArg (fun x : ↥(sectionKernel (pBaseIdeal C Γ H)
          {d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
            Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u}) =>
          ((x.val).val : MvPolynomial (Option
            (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) h12
    have hSe : (∑ j ∈ Finset.univ, (MvPolynomial.rename (Option.some :
        Fin (e + (e + e) + (skewDim e + 1)) →
          Option (Fin (e + (e + e) + (skewDim e + 1))))
          (((((f1) j).val).val - (((f2) j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
          MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
        (MvPolynomial.monomial (Finsupp.single (none :
          Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
          MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) = 0 := by
      have hdistrib : (∑ j ∈ Finset.univ, (MvPolynomial.rename (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1))))
            (((((f1) j).val).val - (((f2) j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
            MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
          (MvPolynomial.monomial (Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
            MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) =
          (∑ j ∈ Finset.univ, (MvPolynomial.rename (Option.some :
            Fin (e + (e + e) + (skewDim e + 1)) →
              Option (Fin (e + (e + e) + (skewDim e + 1))))
              (((((f1) j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
              MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
            (MvPolynomial.monomial (Finsupp.single (none :
              Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
              MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) -
          (∑ j ∈ Finset.univ, (MvPolynomial.rename (Option.some :
            Fin (e + (e + e) + (skewDim e + 1)) →
              Option (Fin (e + (e + e) + (skewDim e + 1))))
              (((((f2) j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :
              MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ) *
            (MvPolynomial.monomial (Finsupp.single (none :
              Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j : ℕ)) (1 : ℂ) :
              MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)) := by
        simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      rw [hdistrib, h12poly, sub_self]
    have hall : ∀ j : Fin (Nat.min s u + 1),
        (((((f1) j).val).val - (((f2) j).val).val) : Poly (e + (e + e) + (skewDim e + 1))) = 0 := by
      intro j0
      apply MvPolynomial.ext
      intro a
      set gr : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ :=
        Finsupp.mapDomain (Option.some :
          Fin (e + (e + e) + (skewDim e + 1)) →
            Option (Fin (e + (e + e) + (skewDim e + 1)))) a +
          Finsupp.single (none :
            Option (Fin (e + (e + e) + (skewDim e + 1)))) (↑j0 : ℕ) with hgrdef
      have hdd : gr none = (↑j0 : ℕ) := by
        rw [hgrdef, Finsupp.add_apply,
          Finsupp.mapDomain_of_notMem_range _ _ (by simp),
          Finsupp.single_eq_same, zero_add]
      have hC := congrArg (fun P : MvPolynomial (Option
          (Fin (e + (e + e) + (skewDim e + 1)))) ℂ => P.coeff gr) h12poly
      rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum] at hC
      have hI1 := psiso_mu_fin (Nat.min s u) (fun j =>
          ((((f1) j).val).val : Poly (e + (e + e) + (skewDim e + 1)))) gr j0 hdd
      have hI2 := psiso_mu_fin (Nat.min s u) (fun j =>
          ((((f2) j).val).val : Poly (e + (e + e) + (skewDim e + 1)))) gr j0 hdd
      have hT := hI1.symm.trans (hC.trans hI2)
      have hcomp1 := pCompGen ((((f1) j0).val).val : Poly (e + (e + e) + (skewDim e + 1))) (↑j0 : ℕ) a
      have hcomp2 := pCompGen ((((f2) j0).val).val : Poly (e + (e + e) + (skewDim e + 1))) (↑j0 : ℕ) a
      have hfinal := hcomp1.symm.trans (hT.trans hcomp2)
      exact sub_eq_zero.mpr hfinal
    have hconcl : f1 = f2 := by
      apply funext
      intro q0
      have hg0 : (((((f1) q0).val).val - (((f2) q0).val).val) : Poly (e + (e + e) + (skewDim e + 1))) = 0 :=
        hall q0
      have hpoly : ((((f1 q0).val).val) : Poly (e + (e + e) + (skewDim e + 1))) =
          ((((f2 q0).val).val) : Poly (e + (e + e) + (skewDim e + 1))) :=
        sub_eq_zero.mp hg0
      have h1 : ((f1 q0).val) = ((f2 q0).val) := Subtype.ext hpoly
      have h2 : f1 q0 = f2 q0 := Subtype.ext h1
      exact h2
    exact hconcl
  have hDomRank : Module.finrank ℂ (∀ j : Fin (Nat.min s u + 1),
      ↥(sectionKernel
        (Ideal.map (MvPolynomial.rename
          (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
          (MvPolynomial.vanishingIdeal ℂ
            (pairRepresentatives (liftedParameterBase C Γ H))))
        {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
          (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - ↑j ∧
          (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
          (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - ↑j})) =
      ∑ j ∈ Finset.range (Nat.min s u + 1),
        Module.finrank ℂ (sectionKernel
          (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))
          {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - j ∧
            (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
            (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - j}) := by
    rw [Module.finrank_pi_fintype]
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => Module.finrank ℂ ↥(sectionKernel
      (Ideal.map (MvPolynomial.rename
        (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
        (MvPolynomial.vanishingIdeal ℂ
          (pairRepresentatives (liftedParameterBase C Γ H))))
      {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
        (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - j ∧
        (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
        (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - j})) (Nat.min s u + 1)
  have hLe : Module.finrank ℂ (sectionKernel (pBaseIdeal C Γ H)
      {d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
        Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u}) ≤
      ∑ j ∈ Finset.range (Nat.min s u + 1),
        Module.finrank ℂ (sectionKernel
          (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))
          {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - j ∧
            (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
            (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - j}) := by
    have h1 := Psi.finrank_range_le
    have hrange : LinearMap.range Psi = ⊤ := LinearMap.range_eq_top.mpr hPsiSurj
    rw [hrange, finrank_top, hDomRank] at h1
    exact h1
  have hGe : ∑ j ∈ Finset.range (Nat.min s u + 1),
      Module.finrank ℂ (sectionKernel
          (Ideal.map (MvPolynomial.rename
            (Fin.castAdd (skewDim e + 1) : Fin (e + (e + e)) → Fin (e + (e + e) + (skewDim e + 1))))
            (MvPolynomial.vanishingIdeal ℂ
              (pairRepresentatives (liftedParameterBase C Γ H))))
          {d : Fin (e + (e + e) + (skewDim e + 1)) →₀ ℕ |
            (∑ i : Fin e, d (Fin.castAdd (skewDim e + 1) (Fin.castAdd (e + e) i))) = s - j ∧
            (∑ i : Fin (e + e), d (Fin.castAdd (skewDim e + 1) (Fin.natAdd e i))) = t ∧
            (∑ i : Fin (skewDim e + 1), d (Fin.natAdd (e + (e + e)) i)) = u - j}) ≤
      Module.finrank ℂ (sectionKernel (pBaseIdeal C Γ H)
        {d : Option (Fin (e + (e + e) + (skewDim e + 1))) →₀ ℕ |
          Finsupp.weight (pWeight e) d = HilbertMulti.tripleDegree s t u}) := by
    have h := LinearMap.finrank_le_finrank_of_injective hPsiInj
    rw [hDomRank] at h
    exact h
  exact Nat.le_antisymm hLe hGe


end PWorld

end FiberEquations

attribute [local instance] MvPolynomial.weightedGradedAlgebra

noncomputable local instance : AddRightCancelMonoid (Fin 3 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 3 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

omit he hh hd R in
/-- The base satisfies the resolution relations `v ∥ d` and `y(d) = 0` pointwise. -/
theorem base_resolution : TripleRankRoute.ResolutionBase C Γ H := by
  classical
  intro d p hpair
  let I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives (liftedParameterBase C Γ H))
  have hev : ∀ g : Poly (e + (e + e)), Ideal.Quotient.mk I g = 0 →
      MvPolynomial.aeval (joinPoints d p) g = 0 := by
    intro g hg
    exact MvPolynomial.mem_vanishingIdeal_iff.mp (Ideal.Quotient.eq_zero_iff_mem.mp hg) _ hpair
  have hminor : ∀ i j : Fin e, d i * p (Fin.castAdd e j) = d j * p (Fin.castAdd e i) := by
    intro i j
    have h := IncidenceSections.closed_pair_parameter_minors (liftedParameterPairs C Γ H)
      (fun p q hpq => IncidenceSections.lifted_pairs_parallel C Γ H p q hpq) i j
    rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub] at h
    have := hev _ h
    simp only [map_sub, map_mul, MvPolynomial.aeval_X] at this
    simpa [joinPoints, sub_eq_zero] using this
  have horth : covectorOfPoint (secondPoint p) d = 0 := by
    have h := IncidenceSections.closed_pair_orthogonal_relation (liftedParameterPairs C Γ H)
      (fun p q hpq => IncidenceSections.lifted_pairs_orthogonal C Γ H p q hpq)
    simp only [← map_mul, ← map_sum] at h
    have := hev _ h
    simp only [map_sum, map_mul, MvPolynomial.aeval_X] at this
    have hsum : covectorOfPoint (secondPoint p) d =
        ∑ i : Fin e, d i * p (Fin.natAdd e i) := by
      simp [covectorOfPoint, secondPoint, LinearMap.sum_apply, smul_eq_mul, mul_comm]
    rw [hsum]
    simpa [joinPoints] using this
  refine ⟨?_, horth⟩
  obtain ⟨hd, _, _⟩ := TripleRankRoute.pairRep_cases hpair
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hd (funext hcon)
  refine ⟨p (Fin.castAdd e i) / d i, ?_⟩
  funext j
  have := hminor i j
  simp only [firstPoint, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination this

/-- B13.1–B13.3, conc:deg-projective-bundle in its specialized Koszul/Hilbert form.
This is the unresolved singular-base foundation, not an assumption in a data record. -/
theorem triple_rank_identity :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s → N ≤ t → N ≤ u →
      ((tripleHilbert (incidenceTriples C Γ H) s t u : ℕ) : ℚ) =
        ∑ m ∈ Finset.range e, (-1 : ℚ) ^ m *
          (∑ delta ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
            ∑ l ∈ Finset.range (m + 1), ∑ beta ∈ Finset.range (m + 1),
              if delta + k + l + beta = m then
                ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)) *
                  ((pairHilbert (liftedParameterBase C Γ H) (s - k - 2 * l - beta) (t + beta) : ℕ) : ℚ)
              else 0) *
          ((Nat.choose (u - m + e.choose 2) (e.choose 2) : ℕ) : ℚ) := by
  classical
  -- B13 redesign: Euler recursion + kernel recursion via the
  -- x0-deformation, all regularity up to direction torsion; see TripleRankRoute.lean.
  have hdeg : (parameterBaseHilbert C Γ H).totalDegree + 1 ≤ e := by
    have h1 := parameterBaseHilbert_degree C V Γ H a he hh hd R
    have h2 := R.fiber_cases
    have h3 := hh.2
    omega
  exact TripleRankRoute.triple_rank_of_parts C Γ H hdeg (base_resolution C Γ H)
    (fun s t u => FiberEquations.pairPullback_section_product C Γ H s t u)
    (fun NP hP s t u hs ht hu => KoszulEval.koszul_eval_eq_pair_ranks C Γ H s t u NP hP hs ht hu)

theorem incidence_hilbert_identity :
    compactIncidenceHilbert C Γ H = koszulIncidenceHilbert e (parameterBaseHilbert C Γ H) := by
  apply incidence_hilbert_identity_of_eventual_rank C Γ H
  obtain ⟨NP, hP⟩ := (parameterBaseHilbert_eventually_polynomial C Γ H).choose_spec
  obtain ⟨N2, hN2⟩ := triple_rank_identity C V Γ H a he hh hd R
  refine ⟨max (NP + 2 * e) (max e N2), fun s t u hs ht hu => ?_⟩
  have hs1 : NP + 2 * e ≤ s := le_trans (Nat.le_max_left _ _) hs
  have ht1 : NP ≤ t :=
    le_trans (Nat.le_add_right NP (2 * e)) (le_trans (Nat.le_max_left _ _) ht)
  have hu1 : e ≤ u := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hu)
  have hs2 : N2 ≤ s :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) hs)
  have ht2 : N2 ≤ t :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) ht)
  have hu2 : N2 ≤ u :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) hu)
  have htri := hN2 s t u hs2 ht2 hu2
  have hkos := KoszulEval.koszul_eval_eq_pair_ranks C Γ H s t u NP hP hs1 ht1 hu1
  rw [htri, hkos]

/-- B16, conc:deg-segre-coefficients, for the actual incidence coefficients. -/
theorem incidence_mixed_degree_identity :
    pointIncidenceIntegral C Γ H h j = ∑ i ∈ Finset.range (h + 1),
      (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedBaseDegree C Γ H h j i := by
  unfold pointIncidenceIntegral
  rw [incidence_hilbert_identity C V Γ H a he hh hd R]
  have hformula := koszulIncidenceHilbert_point_coefficient e h j he hh.2 R.fiber_cases
    (parameterBaseHilbert C Γ H) (parameterBaseHilbert_degree C V Γ H a he hh hd R)
  calc
    pointParameterCoefficient (koszulIncidenceHilbert e (parameterBaseHilbert C Γ H))
        (flatDim e + h) j =
        ∑ i ∈ Finset.range (h + 1), (segreCoeff (e - 1 - i) (h - i) : ℚ) *
          mixedHilbertCoefficient (parameterBaseHilbert C Γ H) (h - i) (i + j) := hformula
    _ = ∑ i ∈ Finset.range (h + 1),
        (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedBaseDegree C Γ H h j i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hih : i ≤ h := by have := Finset.mem_range.mp hi; omega
      simp [mixedBaseDegree, hih]

/-- B18, conc:deg-mixed-positivity, including birational top-degree compatibility. -/
theorem mixed_degree_nonnegative :
    (∀ i ≤ h, 0 ≤ mixedBaseDegree C Γ H h j i) ∧
      mixedBaseDegree C Γ H h j h = (parameterClosure C Γ H).degree := by
  let T := liftedParameterBase C Γ H
  let P := parameterBaseHilbert C Γ H
  have hdegree : P.totalDegree ≤ h + j := parameterBaseHilbert_degree C V Γ H a he hh hd R
  have hevent : ∃ M : ℕ, ∀ s t : ℕ, M ≤ s → M ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P =
        (pairHilbert T s t : ℚ) :=
    (parameterBaseHilbert_eventually_polynomial C Γ H).choose_spec
  constructor
  · intro i hi
    rw [mixedBaseDegree, if_pos hi]
    exact Request.pairHilbert_mixed_top_nonnegative T P hdegree hevent (h - i) (i + j) (by omega)
  · have hclosed : closedPairs T = T := closedPairs_idempotent (liftedParameterPairs C Γ H)
    have hT : (pairClosure T).IsIrreducible := by
      change (pairClosure (closedPairs (liftedParameterPairs C Γ H))).IsIrreducible
      rw [pairClosure_closedPairs]
      exact (compactIncidence_geometry C V Γ H a he hh hd R).1
    have hproj : ∀ d p, (d, p) ∈ T → p ∈ (parameterClosure C Γ H).points := by
      intro d p hdp
      have hp : p ∈ {p | ∃ d : ProjectivePoint e, (d, p) ∈ liftedParameterBase C Γ H} := ⟨d, hdp⟩
      rwa [parameter_base_projection C V Γ H a R] at hp
    obtain ⟨g, D, hhom, hg, hgen⟩ := parameter_base_birational_open C V Γ H a R
    have htop := Request.pairHilbert_birational_top_coefficient T hclosed hT
      (parameterClosure C Γ H) (parameterClosure_irreducible C V Γ H a R)
      (parameterClosure_dimension C V Γ H a he hh hd R) hproj P hdegree hevent g D hhom hg hgen
    rw [mixedBaseDegree, if_pos (Nat.le_refl h), Nat.sub_self]
    exact htop

/-- B12 support, deep leaf A (generic reducedness, characteristic zero). Over a very general
working point `z` (off countably many hypersurfaces of `V`), the scheme-theoretic fibre ideal of
the incidence is radical. -/
theorem fibreIdeal_isRadical_very_general : ∃ g : ℕ → Poly (skewDim e), (∀ i, g i ∉ V.ideal) ∧
    ∀ z ∈ workingPoints V H, (∀ i, MvPolynomial.aeval z (g i) ≠ 0) →
      (PointIntegral.tripleFibreIdeal (incidenceTriples C Γ H) z).IsRadical := by
  have hTW : ∀ w ∈ incidenceTriples C Γ H, w.2 ∈ (projectiveClosure V).points := by
    intro w hw
    have hmem : segrePoint (segrePoint w.1.1 w.1.2) w.2 ∈ (compactIncidence C Γ H).points :=
      ProjectiveVariety.subset_closure _ ⟨w.1.1, w.1.2, w.2, hw, rfl⟩
    have himage := (compactIncidence_geometry C V Γ H a he hh hd R).2.2.2.2
    rw [← himage]
    exact ⟨w.1.1, w.1.2, hmem⟩
  have hV : V.ideal ≠ ⊤ := by
    intro htop
    apply R.nonzero_section
    rw [htop]
    trivial
  obtain ⟨g, hg, hrad⟩ := PointIntegral.tripleFibreIdeal_isRadical_very_general
    (incidenceTriples C Γ H) V hV hTW
  exact ⟨g, hg, fun z _ hz => hrad z hz⟩

/-- B12 support: a radical fibre ideal has the bigraded Hilbert function of the graph of the
point-parameter fibre, `HF(s,t) = HF_Y(s+t)`. -/
theorem fibre_hilbert_eq_pointParameterFiber (z : Point (skewDim e))
    (hz : z ∈ workingPoints V H)
    (hrad : (PointIntegral.tripleFibreIdeal (incidenceTriples C Γ H) z).IsRadical)
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    PointIntegral.idealPairHilbert (PointIntegral.tripleFibreIdeal (incidenceTriples C Γ H) z)
      s t = (pointParameterFiber C Γ H z).hilbert (s + t) :=
  PointIntegral.fibre_hilbert_eq_closure C V Γ H a R z hrad s t hs ht

/-- L-fibre (B12 support). Over a very general working point z, the scheme-theoretic fibre of
the incidence has bigraded Hilbert function `HP_Y(s+t)`, `Y` the point-parameter fibre
(graph of `p = [v : D_z v]`, generic reducedness in characteristic zero). -/
theorem generic_fibre_hilbert_very_general : ∃ g : ℕ → Poly (skewDim e), (∀ i, g i ∉ V.ideal) ∧
    ∀ z ∈ workingPoints V H, (∀ i, MvPolynomial.aeval z (g i) ≠ 0) →
      ∃ M : ℕ, ∀ s t : ℕ, M ≤ s → M ≤ t →
        (PointIntegral.idealPairHilbert
          (PointIntegral.tripleFibreIdeal (incidenceTriples C Γ H) z) s t : ℚ) =
            (pointParameterFiber C Γ H z).hilbertPolynomial.eval ((s : ℚ) + t) := by
  obtain ⟨g1, hg1, hrad⟩ := fibreIdeal_isRadical_very_general C V Γ H a he hh hd R
  refine ⟨g1, hg1, ?_⟩
  intro z hz hgz
  obtain ⟨N0, hN0⟩ := (pointParameterFiber C Γ H z).hilbert_eventually
  refine ⟨N0 + 1, ?_⟩
  intro s t hs ht
  rw [fibre_hilbert_eq_pointParameterFiber C V Γ H a he hh hd R z hz (hrad z hz hgz) s t
    (by omega) (by omega)]
  rw [hN0 (s + t) (by omega)]
  push_cast
  rfl

/-- B12, conc:deg-point-integral, the numerical generic-fiber pushforward formula. -/
theorem point_integral (d : ℚ) (hdg : HasGenericPointFiberDegree C V Γ H d) :
    pointIncidenceIntegral C Γ H h j = d * V.degree := by
  classical
  let T := incidenceTriples C Γ H
  let W := projectiveClosure V
  have hVirr : V.IsIrreducible := R.variety_irreducible
  have hW : W.IsIrreducible := projectiveClosure_isIrreducible V hVirr
  have hTW : ∀ w ∈ T, w.2 ∈ W.points := by
    intro w hw
    have hmem : segrePoint (segrePoint w.1.1 w.1.2) w.2 ∈ (compactIncidence C Γ H).points :=
      ProjectiveVariety.subset_closure _ ⟨w.1.1, w.1.2, w.2, hw, rfl⟩
    have himage := (compactIncidence_geometry C V Γ H a he hh hd R).2.2.2.2
    change w.2 ∈ (projectiveClosure V).points
    rw [← himage]
    exact ⟨w.1.1, w.1.2, hmem⟩
  choose r hrg hrC using fun s t => PointIntegral.tripleHilbert_generic_rank T W hW hTW s t
  choose g Dg hgh hgW hgfib using hrg
  obtain ⟨g0, hg0, hfib⟩ := generic_fibre_hilbert_very_general C V Γ H a he hh hd R
  obtain ⟨g1, hg1, hdeg⟩ := hdg
  let fam : ℕ → Poly (skewDim e) := fun i =>
    if i = 0 then H else if i = 1 then g1 else if (i - 2) % 2 = 0 then g0 ((i - 2) / 2) else
      MvPolynomial.aeval (Fin.cons (1 : Poly (skewDim e)) MvPolynomial.X)
        (g (Nat.unpair ((i - 2) / 2)).1 (Nat.unpair ((i - 2) / 2)).2)
  have hfam : ∀ i, fam i ∉ V.ideal := by
    intro i
    by_cases h0 : i = 0
    · simpa [fam, h0] using R.nonzero_section
    by_cases h1 : i = 1
    · simpa [fam, h1] using hg1
    by_cases h2 : (i - 2) % 2 = 0
    · simpa [fam, h0, h1, h2] using hg0 ((i - 2) / 2)
    simp only [fam, if_neg h0, if_neg h1, if_neg h2]
    rw [← projectiveClosure_homogeneous_mem V _ (hgh _ _)]
    exact hgW _ _
  obtain ⟨z, hzV, hz⟩ := PointIntegral.exists_point_avoiding V hVirr fam hfam
  have hzw : z ∈ workingPoints V H := ⟨hzV, by simpa [fam] using hz 0⟩
  have hz0 : ∀ k, MvPolynomial.aeval z (g0 k) ≠ 0 := by
    intro k
    have hk := hz (2 * k + 2)
    have hne0 : 2 * k + 2 ≠ 0 := by omega
    have hne1 : 2 * k + 2 ≠ 1 := by omega
    have hev : (2 * k + 2 - 2) % 2 = 0 := by omega
    have hdiv : (2 * k + 2 - 2) / 2 = k := by omega
    simpa only [fam, if_neg hne0, if_neg hne1, if_pos hev, hdiv] using hk
  set Y := pointParameterFiber C Γ H z with hYdef
  set Q := Y.hilbertPolynomial with hQdef
  obtain ⟨MQ, hQ⟩ := hfib z hzw hz0
  have hd' : Y.degree = d := hdeg z hzw (by simpa [fam] using hz 1)
  have hzW : affineEmbedding z ∈ W.points :=
    ProjectiveVariety.subset_closure _ ⟨z, hzV, rfl⟩
  have hrQ : ∀ s t : ℕ, MQ ≤ s → MQ ≤ t → (r s t : ℚ) = Q.eval ((s : ℚ) + t) := by
    intro s t hs ht
    have hgz : MvPolynomial.eval (Fin.cons 1 z) (g s t) ≠ 0 := by
      have hzi := hz (2 * Nat.pair s t + 3)
      have hne0 : 2 * Nat.pair s t + 3 ≠ 0 := by omega
      have hne1 : 2 * Nat.pair s t + 3 ≠ 1 := by omega
      have hne2 : ¬ (2 * Nat.pair s t + 3 - 2) % 2 = 0 := by omega
      have hdiv : (2 * Nat.pair s t + 3 - 2) / 2 = Nat.pair s t := by omega
      simp only [fam, if_neg hne0, if_neg hne1, if_neg hne2, hdiv, Nat.unpair_pair] at hzi
      rw [GenericFiber.eval_aeval] at hzi
      have hfun : (fun i => MvPolynomial.aeval z
          ((Fin.cons (1 : Poly (skewDim e)) MvPolynomial.X : Fin (skewDim e + 1) → _) i)) =
          (Fin.cons 1 z : Fin (skewDim e + 1) → ℂ) := by
        funext i
        cases i using Fin.cases <;> simp
      rw [hfun] at hzi
      exact hzi
    rw [← hgfib s t z hzW hgz]
    exact hQ s t hs ht
  have hVne : V.points.Nonempty := ⟨z, hzV⟩
  have hk : W.dimension = flatDim e + h := (projectiveClosure_dimension V hVne).trans hd
  obtain ⟨NW, hNW⟩ := W.hilbert_eventually
  obtain ⟨NP, hNP⟩ := (compactIncidenceHilbert_eventually_polynomial C Γ H).choose_spec
  have hextj := fun j' : ℕ => PointIntegral.coefficient_extraction (compactIncidenceHilbert C Γ H)
    (fun s t u => (tripleHilbert T s t u : ℚ)) W.hilbertPolynomial Q (fun s t => (r s t : ℚ))
    (flatDim e + h) j' (max NP MQ) (by have := hh.1; omega)
    (fun s t u hs ht hu => hNP s t u (le_of_max_le_left hs) (le_of_max_le_left ht)
      (le_of_max_le_left hu))
    (by
      intro s t _ _
      obtain ⟨C0, M0, hM0⟩ := hrC s t
      refine ⟨C0, max M0 (NW + 1), ?_⟩
      intro u hu
      have h1 := hM0 u (le_of_max_le_left hu)
      rw [hNW u (by have := le_of_max_le_right hu; omega), hk] at h1
      exact h1)
    (fun s t hs ht => hrQ s t (le_of_max_le_right hs) (le_of_max_le_right ht))
  have hWdeg : ((flatDim e + h).factorial : ℚ) * W.hilbertPolynomial.coeff (flatDim e + h) =
      V.degree := by
    rw [← projectiveClosure_degree V]
    change _ = OAI.PiExponentJets.W22.actualMultiplicity W.ideal W.isHomogeneous W.dimension
    rw [hk]
    unfold OAI.PiExponentJets.W22.actualMultiplicity
    ring
  have hVtop : V.ideal ≠ ⊤ := by
    intro htop
    apply R.nonzero_section
    rw [htop]
    trivial
  have hVpos : (0 : ℚ) < V.degree := lt_of_lt_of_le one_pos (AffineVariety.one_le_degree V hVtop)
  -- the incidence coefficients vanish above the fibre dimension (frozen B13 identity)
  have hupper : ∀ j' : ℕ, j < j' → Q.coeff j' = 0 := by
    intro j' hj'
    have hHdeg := parameterBaseHilbert_degree C V Γ H a he hh hd R
    have hkos := IncidenceBinomial.koszul_coefficient_of_degree e h j' he hh.2
      (parameterBaseHilbert C Γ H) (le_trans hHdeg (by omega))
    have hzero : ∑ i ∈ Finset.range (h + 1), (segreCoeff (e - 1 - i) (h - i) : ℚ) *
        mixedHilbertCoefficient (parameterBaseHilbert C Γ H) (h - i) (i + j') = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hih : i ≤ h := by have := Finset.mem_range.mp hi; omega
      have hc : (parameterBaseHilbert C Γ H).coeff
          (Finsupp.single (0 : Fin 2) (h - i) + Finsupp.single (1 : Fin 2) (i + j')) = 0 := by
        apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
        have hsum : (Finsupp.single (0 : Fin 2) (h - i) +
            Finsupp.single (1 : Fin 2) (i + j')).degree = h + j' := by
          rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
          omega
        show _ < Finsupp.degree _
        rw [hsum]
        omega
      rw [mixedHilbertCoefficient, hc, mul_zero, mul_zero]
    rw [← hkos, ← incidence_hilbert_identity C V Γ H a he hh hd R] at hzero
    unfold pointParameterCoefficient at hzero
    have hP := hextj j'
    rw [hWdeg] at hP
    have hprod : ((j'.factorial : ℚ) * Q.coeff j') * V.degree = 0 := by
      rw [← hP]
      exact hzero
    rcases mul_eq_zero.mp hprod with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 (by positivity)
      · exact h1
    · exact absurd h0 hVpos.ne'
  -- the integral is at least the parameter degree (frozen B16, B18)
  have hI : pointIncidenceIntegral C Γ H h j = ((j.factorial : ℚ) * Q.coeff j) * V.degree := by
    unfold pointIncidenceIntegral pointParameterCoefficient
    rw [hextj j, hWdeg]
  have hΛ : (1 : ℚ) ≤ (parameterClosure C Γ H).degree := by
    rw [← ProjectiveVariety.degree_cone]
    apply AffineVariety.one_le_degree
    change (parameterClosure C Γ H).ideal ≠ ⊤
    intro htop
    obtain ⟨v, hv⟩ := R.dominant z hzw
    have hw : joinPoints z v ∈ rulingPoints Γ H := ⟨hv, by
      rw [RulingMaps.firstPoint_joinPoints]; exact hzw.2⟩
    have hv0 : v ≠ 0 := by
      intro hv0
      have h1 := R.normalized _ hv
      rw [RulingMaps.secondPoint_joinPoints, hv0] at h1
      simp at h1
    have hp : graphParameter C z v hv0 ∈ (parameterClosure C Γ H).points :=
      ProjectiveVariety.subset_closure _ ⟨z, v, hw, hv0, rfl⟩
    have hzl := hp _ (graphParameter C z v hv0).rep_nonzero (Projectivization.mk_rep _)
    rw [htop] at hzl
    have h1 := (MvPolynomial.mem_zeroLocus_iff.mp hzl) 1 Submodule.mem_top
    simp at h1
  have hIpos : (0 : ℚ) < pointIncidenceIntegral C Γ H h j := by
    have hmix := incidence_mixed_degree_identity C V Γ H a he hh hd R
    have hnon := mixed_degree_nonnegative C V Γ H a he hh hd R
    have hterm : ∀ i ∈ Finset.range (h + 1),
        (0 : ℚ) ≤ (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedBaseDegree C Γ H h j i := by
      intro i hi
      have hi_le : i ≤ h := by have := Finset.mem_range.mp hi; omega
      have hle : (h - i) + 1 ≤ (e - 1 - i) := by have := hh.2; omega
      exact mul_nonneg (by exact_mod_cast segreCoeff_nonnegative (e - 1 - i) (h - i) hle)
        (hnon.1 i hi_le)
    have hsingle := Finset.single_le_sum hterm (Finset.mem_range.mpr (by omega : h < h + 1))
    have htopc : (segreCoeff (e - 1 - h) (h - h) : ℚ) = 1 := by
      rw [Nat.sub_self, segreCoeff_zero]
      norm_num
    rw [htopc, one_mul, hnon.2] at hsingle
    rw [hmix]
    linarith
  have hlower : Q.coeff j ≠ 0 := by
    intro h0
    rw [hI, h0, mul_zero, zero_mul] at hIpos
    exact lt_irrefl _ hIpos
  have hnat : Q.natDegree = j :=
    le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hupper)
      (Polynomial.le_natDegree_of_ne_zero hlower)
  have hYdeg : Y.degree = (j.factorial : ℚ) * Q.coeff j := by
    change OAI.PiExponentJets.W22.actualMultiplicity Y.ideal Y.isHomogeneous Y.dimension = _
    have hdim : Y.dimension = j := hnat
    rw [hdim]
    unfold OAI.PiExponentJets.W22.actualMultiplicity
    ring
  rw [hI, ← hYdeg, hd']

/-- B19, conc:deg-bound. N is the uniform fiber cap supplied by the ruling producer. -/
theorem parameter_degree_le : (parameterClosure C Γ H).degree ≤ (N : ℚ) * V.degree := by
  obtain ⟨d, _hdpos, hdle, _hj1, hfib⟩ :=
    generic_point_fiber_degree C V Γ H a he hh hd R
  have hpoint := point_integral C V Γ H a he hh hd R d hfib
  have hmix := incidence_mixed_degree_identity C V Γ H a he hh hd R
  have hnon := mixed_degree_nonnegative C V Γ H a he hh hd R
  have hVne : V.ideal ≠ ⊤ := by
    intro htop
    apply R.nonzero_section
    rw [htop]
    trivial
  have hVnn : (0 : ℚ) ≤ V.degree :=
    le_trans (by norm_num) (AffineVariety.one_le_degree V hVne)
  have hcoeff : ∀ i ∈ Finset.range (h + 1),
      (0 : ℚ) ≤ (segreCoeff (e - 1 - i) (h - i) : ℚ) := by
    intro i hi
    have hi_le : i ≤ h := by
      have hmem := Finset.mem_range.mp hi
      omega
    have hle : (h - i) + 1 ≤ (e - 1 - i) := by
      obtain ⟨_, hh2⟩ := hh
      omega
    have hnn := segreCoeff_nonnegative (e - 1 - i) (h - i) hle
    exact_mod_cast hnn
  have hterm : ∀ i ∈ Finset.range (h + 1),
      (0 : ℚ) ≤ (segreCoeff (e - 1 - i) (h - i) : ℚ) *
        mixedBaseDegree C Γ H h j i := by
    intro i hi
    have hi_le : i ≤ h := by
      have hmem := Finset.mem_range.mp hi
      omega
    exact mul_nonneg (hcoeff i hi) (hnon.1 i hi_le)
  have hmem : h ∈ Finset.range (h + 1) := Finset.mem_range.mpr (by omega)
  have hsingle : (segreCoeff (e - 1 - h) (h - h) : ℚ) *
      mixedBaseDegree C Γ H h j h ≤
      ∑ i ∈ Finset.range (h + 1),
        (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedBaseDegree C Γ H h j i :=
    Finset.single_le_sum hterm hmem
  have htopc : (segreCoeff (e - 1 - h) (h - h) : ℚ) = 1 := by
    have h1 : h - h = 0 := by omega
    rw [h1]
    have h2 := segreCoeff_zero (e - 1 - h)
    rw [h2]
    norm_num
  have hdeg : (parameterClosure C Γ H).degree ≤
      ∑ i ∈ Finset.range (h + 1),
        (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedBaseDegree C Γ H h j i := by
    calc (parameterClosure C Γ H).degree = mixedBaseDegree C Γ H h j h := hnon.2.symm
      _ = (segreCoeff (e - 1 - h) (h - h) : ℚ) * mixedBaseDegree C Γ H h j h := by
        rw [htopc, one_mul]
      _ ≤ ∑ i ∈ Finset.range (h + 1),
          (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedBaseDegree C Γ H h j i := hsingle
  calc (parameterClosure C Γ H).degree
      ≤ ∑ i ∈ Finset.range (h + 1),
        (segreCoeff (e - 1 - i) (h - i) : ℚ) * mixedBaseDegree C Γ H h j i := hdeg
    _ = pointIncidenceIntegral C Γ H h j := hmix.symm
    _ = d * V.degree := hpoint
    _ ≤ (N : ℚ) * V.degree := mul_le_mul_of_nonneg_right hdle hVnn

/-- B20: the ruling producer's codimension-one case, with natural subtraction controlled. -/
theorem line_fiber_dimension (hj : j = 1) : h = e - 2 ∧ (parameterClosure C Γ H).dimension = e - 1 := by
  have hc : flatDim e + h + 1 = skewDim e := by
    rw [← hd]
    exact R.codimension_one hj
  have hchoose : skewDim e = flatDim e + (e - 1) := by
    simp only [skewDim, flatDim]
    rw [show e = (e - 1) + 1 by omega, Nat.choose_succ_succ']
    simp [Nat.choose_one_right, Nat.add_comm]
  have hh' : h + 1 = e - 1 := by
    rw [hchoose] at hc
    omega
  constructor
  · omega
  · calc
      (parameterClosure C Γ H).dimension = h + j :=
        parameterClosure_dimension C V Γ H a he hh hd R
      _ = e - 1 := by rw [hj]; omega

/-- B22, conc:deg-skew-pencil: the geometric differential-rank bridge. -/
theorem tangent_skew_pencil_constraint (hj : j = 1) :
    ∃ (g : Poly (e + e)) (D : ℕ), g.IsHomogeneous D ∧ g ∉ (parameterClosure C Γ H).ideal ∧
      ∀ p ∈ (parameterClosure C Γ H).points, MvPolynomial.aeval p.rep g ≠ 0 →
        p ∈ affineParameters e ∧ ∀ z0 ∈ evaluationFlat C p,
          Module.finrank ℂ (parameterTangent C (parameterClosure C Γ H) p z0) = e - 1 ∧
          ∀ B : BilinForm ℂ (TangentQuotient p), B.IsAlt →
            ¬ Function.Bijective (skewPencil (parameterTangent C (parameterClosure C Γ H) p z0) B) := by
  let F := rulingGraphPolynomials C
  let W := TrackD.rationalImage Γ F 1
  let Y := parameterClosure C Γ H
  have hnorm : ∀ w ∈ Γ.points, MvPolynomial.aeval w (F (Fin.castAdd e a)) = 1 := by
    intro w hwm
    simpa only [F, rulingGraphPolynomials, Fin.addCases_left, MvPolynomial.aeval_X, secondPoint] using
      R.normalized w hwm
  obtain ⟨_, hdimW, _⟩ := normalized_polynomial_image_geometry Γ R.incidence_irreducible
    (rulingOpenPolynomial H) (rulingOpenPolynomial_not_mem C V Γ H a R) F
    (Fin.castAdd e a) hnorm
  have hWdim : W.dimension = e - 1 := by
    dsimp only [F] at hdimW
    rw [ruling_polynomial_projective_image C V Γ H a R] at hdimW
    exact hdimW.trans (line_fiber_dimension C V Γ H a he hh hd R hj).2
  obtain ⟨gS, hgS, hgood⟩ := ruling_good_source_open C V Γ H a R hj hWdim
  let g := rulingOpenPolynomial H * gS
  have hg : g ∉ Γ.ideal := by
    intro hmem
    rcases R.incidence_irreducible.mem_or_mem hmem with hH | hS
    · exact rulingOpenPolynomial_not_mem C V Γ H a R hH
    · exact hgS hS
  have hFnz : ∀ w ∈ Γ.points, (fun i => MvPolynomial.aeval w (F i)) ≠ 0 :=
    rulingGraphPolynomials_nonzero C V Γ H a R
  have hclosure : ProjectiveVariety.closure (polynomialProjectiveImage Γ g F) = Y := by
    have h := polynomial_projective_image_closure_independent Γ R.incidence_irreducible g
      (rulingOpenPolynomial H) hg (rulingOpenPolynomial_not_mem C V Γ H a R) F hFnz
    dsimp only [F] at h
    rw [ruling_polynomial_projective_image C V Γ H a R] at h
    exact h
  obtain ⟨G, D, hhom, hG, hinside⟩ := Request.polynomial_projective_image_contains_open
    Γ R.incidence_irreducible g hg F (fun w hw _ => hFnz w hw)
  rw [hclosure] at hG hinside
  refine ⟨G, D, hhom, hG, ?_⟩
  intro p hpY hpG
  obtain ⟨w, hwΓ, hwg, hFw, hpw⟩ := hinside p hpY hpG
  let z := firstPoint w
  let v := secondPoint w
  have hwjoin : joinPoints z v = w := joinPoints_eta w
  have hva : v a = 1 := R.normalized w hwΓ
  have hv : v ≠ 0 := by
    intro hzero
    rw [hzero] at hva
    exact zero_ne_one hva
  have hpgraph : graphParameter C z v hv = p := by
    have hmk : Projectivization.mk ℂ (fun i => MvPolynomial.aeval w (F i)) hFw =
        graphParameter C z v hv := by
      apply (Projectivization.mk_eq_mk_iff' ℂ
        (fun i => MvPolynomial.aeval w (F i)) (graphVector C z v)
        hFw (graphVector_ne_zero C z v hv)).mpr
      refine ⟨1, ?_⟩
      simpa only [one_smul] using (eval_rulingGraphPolynomials C w).symm
    exact hmk.symm.trans hpw
  have hparts : MvPolynomial.aeval w (rulingOpenPolynomial H) ≠ 0 ∧
      MvPolynomial.aeval w gS ≠ 0 := by simpa only [g, map_mul, mul_ne_zero_iff] using hwg
  have hw0 : joinPoints z v ∈ rulingPoints Γ H := by
    rw [hwjoin]
    exact (hgood w hwΓ hparts.2).1
  have hpaff : p ∈ affineParameters e := hpgraph ▸ graphParameter_mem_affine C z v hv
  refine ⟨hpaff, ?_⟩
  intro z0 hz0
  let vp := firstPoint p.rep
  let K := LinearMap.ker (alternatingEvaluation vp)
  obtain ⟨ψ, φ, hφ, hdesc⟩ := alternating_kernel_quotient_coordinates vp hpaff.2
  let δ : Point (flatDim e) →ₗ[ℂ] Point (skewDim e) :=
    C.decode.symm.toLinearMap.comp (K.subtype.comp ψ.toLinearMap)
  let L : Point (flatDim e) →ₗ[ℂ] Point (skewDim e + e) :=
    { toFun := fun t => joinPoints (δ t) 0
      map_add' := by
        intro t s
        simpa only [map_add, zero_add] using joinPoints_add (δ t) (δ s) (0 : Point e) 0
      map_smul' := by
        intro c t
        simpa only [map_smul, smul_zero, RingHom.id_apply] using joinPoints_smul c (δ t) (0 : Point e) }
  let b := joinPoints z0 v
  let f := affineLinearPullback b L g
  have hsource (t : Point (flatDim e)) : b + L t = joinPoints (z0 + δ t) v := by
    change joinPoints z0 v + joinPoints (δ t) 0 = _
    rw [← joinPoints_add, add_zero]
  have hδ (t : Point (flatDim e)) : C.decode (δ t) = (ψ t).val := by
    exact C.decode.apply_symm_apply (ψ t).val
  have hδker (t : Point (flatDim e)) : (C.decode (δ t)).val vp = 0 := by
    rw [hδ]
    change alternatingEvaluation vp (ψ t).val = 0
    exact (ψ t).property
  have hzflat : z ∈ evaluationFlat C p := by
    rw [← hpgraph]
    exact (evaluationFlat_graphParameter_iff C z z v hv).mpr rfl
  have hstarK : C.decode (z - z0) ∈ K := by
    change (C.decode (z - z0)).val vp = 0
    rw [map_sub, Submodule.coe_sub, LinearMap.sub_apply]
    change (C.decode z).val (firstPoint p.rep) - (C.decode z0).val (firstPoint p.rep) = 0
    rw [hzflat, hz0, sub_self]
  let tstar := ψ.symm ⟨C.decode (z - z0), hstarK⟩
  have hδstar : δ tstar = z - z0 := by
    change C.decode.symm ((ψ tstar).val) = z - z0
    rw [ψ.apply_symm_apply, C.decode.symm_apply_apply]
  have hstarSource : b + L tstar = w := by
    rw [hsource, hδstar, add_sub_cancel, hwjoin]
  have hfstar : MvPolynomial.aeval tstar f ≠ 0 := by
    rw [eval_affineLinearPullback, hstarSource]
    exact hwg
  let Θ := parameterTangent C Y p z0
  have hlocal (t : Point (flatDim e)) (hft : MvPolynomial.aeval t f ≠ 0) :
      Module.finrank ℂ Θ = e - 1 ∧ ¬ Function.Bijective (skewPencil Θ (φ t).val) := by
    let zt := z0 + δ t
    have hgt : MvPolynomial.aeval (joinPoints zt v) g ≠ 0 := by
      rw [eval_affineLinearPullback, hsource] at hft
      exact hft
    have hgtparts : MvPolynomial.aeval (joinPoints zt v) (rulingOpenPolynomial H) ≠ 0 ∧
        MvPolynomial.aeval (joinPoints zt v) gS ≠ 0 := by
      simpa only [g, map_mul, mul_ne_zero_iff] using hgt
    have hztfirst : firstPoint (joinPoints zt v) = zt := by
      funext i
      exact Fin.addCases_left (m := skewDim e) (n := e) (motive := fun _ => ℂ)
        (left := zt) (right := v) i
    have hztsecond : secondPoint (joinPoints zt v) = v := by
      funext i
      exact Fin.addCases_right (m := skewDim e) (n := e) (motive := fun _ => ℂ)
        (left := zt) (right := v) i
    have hztH : MvPolynomial.aeval zt H ≠ 0 := by
      rw [eval_rulingOpenPolynomial, hztfirst] at hgtparts
      exact hgtparts.1
    have hztflat : zt ∈ evaluationFlat C p := by
      change (C.decode (z0 + δ t)).val vp = covectorOfPoint (secondPoint p.rep)
      rw [map_add, Submodule.coe_add, LinearMap.add_apply, hδker, add_zero]
      exact hz0
    have hwT : joinPoints zt v ∈ rulingPoints Γ H :=
      ruling_normalized_flat_fiber C V Γ H a R z v hw0 hv zt (hpgraph.symm ▸ hztflat) hztH
    have hparam : graphParameter C zt v hv = p := by
      have heval := (evaluationFlat_graphParameter_iff C z zt v hv).mp (hpgraph.symm ▸ hztflat)
      have hvec : graphVector C zt v = graphVector C z v := by
        unfold graphVector
        rw [heval]
      have hmk : graphParameter C zt v hv = graphParameter C z v hv :=
        (Projectivization.mk_eq_mk_iff' ℂ (graphVector C zt v) (graphVector C z v)
          (graphVector_ne_zero C zt v hv) (graphVector_ne_zero C z v hv)).mpr
          ⟨1, by simpa only [one_smul] using hvec.symm⟩
      exact hmk.trans hpgraph
    have hgoodT := hgood (joinPoints zt v) hwT.1 hgtparts.2
    have hdiffT := hgoodT.2.1
    have htrankT := hgoodT.2.2.1
    have hvrankT := hgoodT.2.2.2
    rw [hztfirst, hztsecond] at hdiffT htrankT
    rw [hztfirst] at hvrankT
    have hBT : ∀ x w : Point e, (C.decode (zt - z0)).val x w =
        (φ t).val ((Submodule.span ℂ {firstPoint p.rep}).mkQ x)
          ((Submodule.span ℂ {firstPoint p.rep}).mkQ w) := by
      intro x w
      have hzdiff : zt - z0 = δ t := by dsimp only [zt]; abel
      rw [hzdiff, hδ]
      exact hdesc t x w
    exact ruling_good_source_pencil_singular C V Γ H a he R zt v hwT hv p hparam
      hdiffT htrankT hvrankT z0 hz0 (φ t).val hBT
  refine ⟨(hlocal tstar hfstar).1, ?_⟩
  exact skewPencil_singular_of_polynomial_open Θ φ hφ f tstar hfstar
    (fun t ht => (hlocal t ht).2)

/-- B27, conc:degree.exception-linear. The proof uses B22/B24 and algebraic B26. -/
theorem exceptional_parameter_linear (hj : j = 1) :
    ∃ L : Submodule ℂ (Point (e + e)), IsMaximalIsotropic L ∧
      parameterClosure C Γ H = linearProjectivePlane L := by
  obtain ⟨_hh, hdim⟩ := line_fiber_dimension C V Γ H a he hh hd R hj
  obtain ⟨g, D, hhom, hg, hconstraint⟩ :=
    tangent_skew_pencil_constraint C V Γ H a he hh hd R hj
  apply null_tangent_parameter_linear C he (parameterClosure C Γ H)
    (parameterClosure_irreducible C V Γ H a R) hdim
    (parameterClosure_subset_quadric C Γ H)
  refine ⟨g, D, hhom, hg, ?_⟩
  intro p hp hgp
  obtain ⟨hpaff, hpoint⟩ := hconstraint p hp hgp
  refine ⟨hpaff, ?_⟩
  intro z0 hz0
  obtain ⟨hrank, hsingular⟩ := hpoint z0 hz0
  refine ⟨hrank, ?_⟩
  have hquot : Module.finrank ℂ (TangentQuotient p) = e - 1 := by
    change Module.finrank ℂ (Point e ⧸ Submodule.span ℂ {firstPoint p.rep}) = e - 1
    rw [Submodule.finrank_quotient, finrank_span_singleton hpaff.2]
    simp [Point, Module.finrank_fin_fun]
  apply singular_skew_pencil_isotropic _ _ hsingular
  exact hrank.trans hquot.symm

/-- B28, conc:degree. The producer supplies N=O_e(1), making this the paper's C_e bound. -/
theorem degree_comparison :
    (parameterClosure C Γ H).dimension = h + j ∧
    (parameterClosure C Γ H).degree ≤ (N : ℚ) * V.degree ∧
    (j = 1 → h = e - 2 ∧ ∃ L : Submodule ℂ (Point (e + e)),
      IsMaximalIsotropic L ∧ parameterClosure C Γ H = linearProjectivePlane L) := by
  refine ⟨parameterClosure_dimension C V Γ H a he hh hd R, ?_⟩
  refine ⟨parameter_degree_le C V Γ H a he hh hd R, ?_⟩
  intro hj
  obtain ⟨hh', _⟩ := line_fiber_dimension C V Γ H a he hh hd R hj
  obtain ⟨L, hL, hplane⟩ := exceptional_parameter_linear C V Γ H a he hh hd R hj
  exact ⟨hh', L, hL, hplane⟩

end Ruling

#print axioms mixed_degree_nonnegative
#print axioms incidence_mixed_degree_identity
#print axioms quadric_tangent_coordinates
#print axioms null_tangent_parameter_linear
#print axioms exceptional_parameter_linear
#print axioms dense_ruling_incidence
#print axioms compactIncidence_geometry
#print axioms parameterClosure_dimension
end
end DistinctDistances.TrackB

#print axioms DistinctDistances.TrackB.parameterTangent_eq_map
#print axioms DistinctDistances.TrackB.tangentCoordinateLinear_zero_iff
#print axioms DistinctDistances.TrackB.parameterTangent_normalized_chart

#print axioms DistinctDistances.TrackB.ruling_good_source_pencil_singular
#print axioms DistinctDistances.TrackB.ruling_good_source_open
#print axioms DistinctDistances.TrackB.polynomial_projective_image_closure_independent
#print axioms DistinctDistances.TrackB.tangent_skew_pencil_constraint
