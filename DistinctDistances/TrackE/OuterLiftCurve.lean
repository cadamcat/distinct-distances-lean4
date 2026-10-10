import DistinctDistances.TrackE.OuterLiftJets
import DistinctDistances.Foundations.Projection
import DistinctDistances.TrackA.ADepthAux
import DistinctDistances.Bridges.ProjectiveEnvelope
import DistinctDistances.TrackE.MOCurveAux

/-! The curve of the outer lift from point jets (sparse-cones.tex:580–594).

`outer_curve_from_jets`: under the étale hypotheses of `jet_transfer`,
for an irreducible projective curve `γ` of directions through `[q - p]` lying
in the specialized label equations, `Y ∩ (p + cone γ)` has an irreducible
component through `q` which is a curve with one-dimensional radial image in
`γ`. The jets of the cone section at `q` are those of the chart slice of `γ`
at `w₀` (`jet_transfer` with `K` its vanishing ideal): an isolated `q` would
make the local Hilbert function of the slice bounded (local dimension `0`),
and every component through `q` has local dimension `≤ 1`; a lift collapsing
to the ray of `q` would have the jets of a point (`K = m_{w₀}`). -/
namespace DistinctDistances.SparseCones
open MvPolynomial
open scoped Classical
noncomputable section
variable {n : ℕ}

/-- The slice `{z/z_{i₀} : [z] ∈ γ, z_{i₀} ≠ 0}` of the cone of `γ` by the
affine hyperplane `w_{i₀} = 1`, as an affine variety of `ℂ^n`. -/
def chartSlice (γ : ProjectiveVariety n) (i₀ : Fin n) : AffineVariety n :=
  AffineVariety.closure
    {w | ∃ z ∈ γ.points, z.rep i₀ ≠ 0 ∧ w = (z.rep i₀)⁻¹ • z.rep}

/-- The cone `p + cone(γ)` with vertex `p`: the zeros of the translated
homogeneous equations `h(y - p)`, `h ∈ I(γ)`. -/
def coneThrough (p : Point n) (γ : ProjectiveVariety n) : AffineVariety n :=
  AffineVariety.ofIdeal
    (γ.ideal.map (aeval (fun a => (X a - C (p a) : Poly n))).toRingHom)

/-- sc:outer-lift.slice . The chart slice of an
irreducible projective curve meeting the chart is an irreducible affine curve.
Irreducible: closure of the image of the irreducible chart part. Dimension:
`f ↦ f` identifies the degree-`D` part of `ℂ[z]/I(γ)` with
`ℂ[w]_{≤D}/I(slice)_{≤D}` — injective since a homogeneous `f` vanishing on the
slice vanishes on the chart part of the cone, so `z_{i₀}·f ∈ I(γ)` and
`f ∈ I(γ)` (prime, `z_{i₀} ∉ I(γ)`); surjective by homogenizing in `w_{i₀}`
(`Σ_j w_{i₀}^{D-j} g_j - g ∈ (w_{i₀} - 1)`, which vanishes on the slice).
So the affine and projective Hilbert polynomials agree
(`OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq`), and
`dimension = γ.dimension = 1`. -/
theorem chartSlice_curve (γ : ProjectiveVariety n) (hγ : γ.IsIrreducible)
    (hγd : γ.dimension = 1) (i₀ : Fin n) (hz : ∃ z ∈ γ.points, z.rep i₀ ≠ 0) :
    (chartSlice γ i₀).IsIrreducible ∧ (chartSlice γ i₀).dimension = 1 := by
  have hℓ : (MvPolynomial.X i₀ : Poly n).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℂ i₀
  have hℓV : (MvPolynomial.X i₀ : Poly n) ∉ γ.ideal := by
    intro hmem
    obtain ⟨z, hzmem, hzne⟩ := hz
    have hrep : z.rep ∈ MvPolynomial.zeroLocus ℂ γ.ideal :=
      hzmem z.rep z.rep_nonzero (Projectivization.mk_rep z)
    have h0 := MvPolynomial.mem_zeroLocus_iff.mp hrep _ hmem
    simp [MvPolynomial.aeval_X] at h0
    exact hzne h0
  have hT : {w | ∃ z ∈ γ.points, z.rep i₀ ≠ 0 ∧ w = (z.rep i₀)⁻¹ • z.rep} =
      (TrackA.projectiveLinearSlice γ (MvPolynomial.X i₀ : Poly n)).points := by
    ext w
    constructor
    · rintro ⟨z, hzmem, hzne, rfl⟩
      rw [TrackA.linearSlice_points]
      constructor
      · have hrep : z.rep ∈ MvPolynomial.zeroLocus ℂ γ.ideal :=
          hzmem z.rep z.rep_nonzero (Projectivization.mk_rep z)
        have hcone : z.rep ∈ γ.affineCone.points := hrep
        exact TrackA.cone_smul_mem γ z.rep hcone _
      · simp [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hzne]
    · intro hw
      rw [TrackA.linearSlice_points] at hw
      obtain ⟨hcone, hval⟩ := hw
      have hval' : w i₀ = 1 := by simpa using hval
      have hw0 : w ≠ 0 := by
        intro h0
        have : w i₀ = 0 := by simp [h0]
        rw [hval'] at this
        exact one_ne_zero this
      let z : ProjectivePoint n := Projectivization.mk ℂ w hw0
      have hzmem : z ∈ γ.points :=
        (ProjectiveVariety.mem_points_mk_iff γ w hw0).mpr hcone
      have hrel : Projectivization.mk ℂ w hw0
          = Projectivization.mk ℂ z.rep z.rep_nonzero := by
        simp [z, Projectivization.mk_rep]
      obtain ⟨c, hc⟩ :=
        (Projectivization.mk_eq_mk_iff' ℂ w z.rep hw0 z.rep_nonzero).mp hrel
      have hci0 : c * z.rep i₀ = 1 := by
        have h1 : w i₀ = (c • z.rep) i₀ := by rw [← hc]
        rw [hval'] at h1
        simpa [Pi.smul_apply, smul_eq_mul] using h1.symm
      have hzne : z.rep i₀ ≠ 0 := by
        intro h0
        simp [h0] at hci0
      have hc_eq : c = (z.rep i₀)⁻¹ := eq_inv_of_mul_eq_one_left hci0
      refine ⟨z, hzmem, hzne, ?_⟩
      rw [← hc, hc_eq]
  have hslice_eq : chartSlice γ i₀ =
      TrackA.projectiveLinearSlice γ (MvPolynomial.X i₀ : Poly n) := by
    unfold chartSlice
    rw [hT]
    apply AffineVariety.ext
    show MvPolynomial.vanishingIdeal ℂ _ = _
    rw [AffineVariety.vanishingIdeal_points]
  have hirr : (TrackA.projectiveLinearSlice γ
      (MvPolynomial.X i₀ : Poly n)).IsIrreducible :=
    TrackA.linearSlice_irreducible γ hγ _ hℓ hℓV
  have hdim : (TrackA.projectiveLinearSlice γ
      (MvPolynomial.X i₀ : Poly n)).dimension = 1 := by
    have h := TrackA.linearSlice_dimension γ hγ _ hℓ hℓV
    rw [hγd] at h
    exact h
  rw [hslice_eq]
  exact ⟨hirr, hdim⟩

/-- sc:outer-lift.cone-directions . Directions from `p`
of points of a subvariety of `p + cone(γ)` lie in `γ`: for `x ∈ C`, `x ≠ p`,
every `h ∈ I(γ)` vanishes at `x - p` (`points_ofIdeal`, evaluation of the
translated equation), so `[x - p] ∈ γ` (`ProjectiveVariety.mem_points_mk_iff`);
the closure `radialImage p C` stays in the closed set `γ`. -/
theorem radialImage_subset_of_cone (p : Point n) (γ : ProjectiveVariety n)
    (C : AffineVariety n) (hC : C.Subvariety (coneThrough p γ)) :
    (radialImage p C).points ⊆ γ.points := by
  have hpts : C.points ⊆ (coneThrough p γ).points :=
    (AffineVariety.subvariety_iff_points_subset C (coneThrough p γ)).mp hC
  have hS : {z | ∃ x ∈ C.points, ∃ hx : x ≠ p, radialProjection p x hx = z}
      ⊆ γ.points := by
    rintro z ⟨x, hxV, hxne, rfl⟩
    have hxCone : x ∈ (coneThrough p γ).points := hpts hxV
    have hmem : x - p ∈ MvPolynomial.zeroLocus ℂ γ.ideal := by
      rw [MvPolynomial.mem_zeroLocus_iff]
      intro h hh
      have hmap : (MvPolynomial.aeval
          (fun a => (MvPolynomial.X a -
            MvPolynomial.C (p a) : Poly n))) h ∈
          γ.ideal.map (MvPolynomial.aeval
            (fun a => (MvPolynomial.X a -
              MvPolynomial.C (p a) : Poly n))).toRingHom :=
        Ideal.mem_map_of_mem _ hh
      have hxmem : x ∈ MvPolynomial.zeroLocus ℂ
          (γ.ideal.map (MvPolynomial.aeval
            (fun a => (MvPolynomial.X a -
              MvPolynomial.C (p a) : Poly n))).toRingHom) := by
        have : (coneThrough p γ).points =
            MvPolynomial.zeroLocus ℂ
              (γ.ideal.map (MvPolynomial.aeval
                (fun a => (MvPolynomial.X a -
                  MvPolynomial.C (p a) : Poly n))).toRingHom) := by
          unfold coneThrough
          rw [AffineVariety.points_ofIdeal]
        rw [← this]
        exact hxCone
      have h0 := MvPolynomial.mem_zeroLocus_iff.mp hxmem _ hmap
      rw [MOCurveAux.mo_eval_translate_aeval] at h0
      exact h0
    have hne : x - p ≠ 0 := sub_ne_zero.mpr hxne
    have hmk : Projectivization.mk ℂ (x - p) hne ∈ γ.points :=
      (ProjectiveVariety.mem_points_mk_iff γ (x - p) hne).mpr hmem
    simpa [radialProjection] using hmk
  have heq : radialImage p C = ProjectiveVariety.closure
      {z | ∃ x ∈ C.points, ∃ hx : x ≠ p, radialProjection p x hx = z} := rfl
  rw [heq]
  exact MOCurveAux.projective_closure_points_subset_of_subset _ _ hS

/-- sc:outer-lift.image-dimension . An irreducible
variety with two points of distinct directions from `p`, whose radial image
lies in an irreducible projective curve `γ`, has one-dimensional radial image:
`≤ 1` by `TrackD.projective_dimension_mono` (or `TrackE` `MReqAux` analogues),
and not `0`, since an irreducible zero-dimensional projective variety is one
point (`Bridges.projective_zero_dim_singleton`; irreducibility by
`radialImage_irreducible`) while both directions lie in the image
(`ProjectiveVariety.subset_closure`). -/
theorem radialImage_dimension_one (p : Point n) (C : AffineVariety n)
    (hC : C.IsIrreducible) (γ : ProjectiveVariety n) (hγ : γ.IsIrreducible)
    (hγd : γ.dimension = 1) (hsub : (radialImage p C).points ⊆ γ.points)
    (x₁ x₂ : Point n) (h₁ : x₁ ∈ C.points) (h₂ : x₂ ∈ C.points)
    (hne₁ : x₁ ≠ p) (hne₂ : x₂ ≠ p)
    (hdir : radialProjection p x₁ hne₁ ≠ radialProjection p x₂ hne₂) :
    (radialImage p C).dimension = 1 := by
  have hWirr : (radialImage p C).IsIrreducible :=
    radialImage_irreducible p C hC ⟨x₁, h₁, hne₁⟩
  have hWsub : (radialImage p C).Subvariety γ :=
    MOCurveAux.projectiveSubvariety_of_points_subset _ _ hsub
  have hWne : (radialImage p C).points.Nonempty := by
    refine ⟨_, ProjectiveVariety.subset_closure _ ⟨x₁, h₁, hne₁, rfl⟩⟩
  have hγne : γ.points.Nonempty :=
    ProjectiveFamily.irreducible_points_nonempty γ hγ
  have hdim_le : (radialImage p C).dimension ≤ 1 := by
    have hmono := DistinctDistances.MReqAux.projective_cone_dimension_mono
      γ (radialImage p C) hWsub
    rw [ProjectiveVariety.dimension_cone _ hWne,
      ProjectiveVariety.dimension_cone _ hγne, hγd] at hmono
    omega
  have hdim_ne0 : (radialImage p C).dimension ≠ 0 := by
    intro h0
    obtain ⟨pt, hpt⟩ :=
      DistinctDistances.Bridges.projective_zero_dim_singleton _ hWirr h0
    have hm1 : radialProjection p x₁ hne₁ ∈ (radialImage p C).points :=
      ProjectiveVariety.subset_closure _ ⟨x₁, h₁, hne₁, rfl⟩
    have hm2 : radialProjection p x₂ hne₂ ∈ (radialImage p C).points :=
      ProjectiveVariety.subset_closure _ ⟨x₂, h₂, hne₂, rfl⟩
    rw [hpt] at hm1 hm2
    have e1 : radialProjection p x₁ hne₁ = pt := Set.mem_singleton_iff.mp hm1
    have e2 : radialProjection p x₂ hne₂ = pt := Set.mem_singleton_iff.mp hm2
    exact hdir (e1.trans e2.symm)
  omega

/-! ### Point-jet helpers for `outer_curve_from_jets` -/

/-- The jets of a variety at a point are its local Hilbert length. -/
theorem localHilbert_eq_jet (V : AffineVariety n) (x : Point n) (t : ℕ) :
    V.localHilbert x t =
      ((Module.finrank ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) : ℕ) : ℕ∞) := by
  set J := V.ideal ⊔ pointIdeal x ^ (t + 1) with hJ
  have hfin : Module.Finite ℂ (Poly n ⧸ J) := jet_quot_finite V.ideal x t
  let φ : Poly n →ₐ[ℂ] PointLocalRing x := IsScalarTower.toAlgHom ℂ (Poly n) (PointLocalRing x)
  have hφJ : ∀ a ∈ J, (Ideal.Quotient.mkₐ ℂ (localizedIdeal J x)) (φ a) = 0 := by
    intro a ha
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let g : (Poly n ⧸ J) →ₐ[ℂ] (PointLocalRing x ⧸ localizedIdeal J x) :=
    Ideal.Quotient.liftₐ J ((Ideal.Quotient.mkₐ ℂ (localizedIdeal J x)).comp φ) hφJ
  have hunit : ∀ s ∈ (pointIdeal x).primeCompl, IsUnit (Ideal.Quotient.mk J s) := by
    intro s hs
    apply jet_unit
    intro h0
    apply hs
    change s ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n))
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact h0
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h1 : (Ideal.Quotient.mk (localizedIdeal J x)) (algebraMap (Poly n) _ a) = 0 := hy
    rw [Ideal.Quotient.eq_zero_iff_mem, localizedIdeal,
      IsLocalization.mem_map_algebraMap_iff (pointIdeal x).primeCompl] at h1
    obtain ⟨⟨⟨b, hb⟩, ⟨s, hs⟩⟩, hbs⟩ := h1
    simp only at hbs
    rw [← map_mul, IsLocalization.eq_iff_exists (pointIdeal x).primeCompl] at hbs
    obtain ⟨⟨c, hc⟩, hc'⟩ := hbs
    simp only at hc'
    have hcs : c * s ∈ (pointIdeal x).primeCompl :=
      (pointIdeal x).primeCompl.mul_mem hc hs
    have hmem : (c * s) * a ∈ J := by
      have : c * (a * s) = c * b := hc'
      rw [show (c * s) * a = c * (a * s) by ring, this]
      exact J.mul_mem_left _ hb
    have hz : Ideal.Quotient.mk J ((c * s) * a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_mul] at hz
    exact (IsUnit.mul_right_eq_zero (hunit _ hcs)).mp hz
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (pointIdeal x).primeCompl z
    obtain ⟨s', hs'⟩ := (hunit s hs).exists_right_inv
    obtain ⟨s'', rfl⟩ := Ideal.Quotient.mk_surjective s'
    refine ⟨Ideal.Quotient.mk J (a * s''), ?_⟩
    show Ideal.Quotient.mk (localizedIdeal J x) (algebraMap (Poly n) _ (a * s'')) =
      Ideal.Quotient.mk (localizedIdeal J x) (IsLocalization.mk' _ a ⟨s, hs⟩)
    rw [Ideal.Quotient.eq]
    have hss : s * s'' - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hs', map_one, sub_self]
    have : algebraMap (Poly n) (PointLocalRing x) (a * s'') -
        IsLocalization.mk' (PointLocalRing x) a (⟨s, hs⟩ : (pointIdeal x).primeCompl) =
        algebraMap (Poly n) _ (a * (s * s'' - 1)) *
          IsLocalization.mk' (PointLocalRing x) (1 : Poly n)
            (⟨s, hs⟩ : (pointIdeal x).primeCompl) := by
      have hm : IsLocalization.mk' (PointLocalRing x) (1 : Poly n)
          (⟨s, hs⟩ : (pointIdeal x).primeCompl) * algebraMap (Poly n) (PointLocalRing x) s = 1 := by
        rw [IsLocalization.mk'_spec, map_one]
      rw [IsLocalization.mk'_eq_mul_mk'_one (S := PointLocalRing x) a]
      simp only [map_sub, map_mul, map_one]
      linear_combination (-(algebraMap (Poly n) (PointLocalRing x) a *
        algebraMap (Poly n) (PointLocalRing x) s'')) * hm
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (J.mul_mem_left _ hss))
  let e : (Poly n ⧸ J) ≃ₐ[ℂ] (PointLocalRing x ⧸ localizedIdeal J x) :=
    AlgEquiv.ofBijective g ⟨hinj, hsurj⟩
  unfold AffineVariety.localHilbert localLengthAt
  rw [TrackA.point_local_length_eq_complex_length x, ← e.toLinearEquiv.length_eq,
    Module.length_eq_finrank]

theorem localDimension_le_of_localHilbert_le (V W : AffineVariety n) (x y : Point n)
    (h : ∀ t, V.localHilbert x t ≤ W.localHilbert y t) :
    V.localDimension x ≤ W.localDimension y := by
  obtain ⟨_, N1, hP⟩ := (V.localHilbert_eventually_polynomial x).choose_spec
  obtain ⟨_, N2, hQ⟩ := (W.localHilbert_eventually_polynomial y).choose_spec
  have hPnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ (V.localHilbertPolynomial x).eval (T : ℚ) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N1, fun t ht => hP t ht⟩] with t ht
    obtain ⟨a, _, heval⟩ := ht
    have heval' : (V.localHilbertPolynomial x).eval (t : ℚ) = (a : ℚ) := heval
    rw [heval']
    positivity
  have hle : ∀ᶠ T : ℕ in Filter.atTop, (V.localHilbertPolynomial x).eval (T : ℚ) ≤
      (W.localHilbertPolynomial y).eval (T : ℚ) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N1, fun t ht => hP t ht⟩,
      Filter.eventually_atTop.mpr ⟨N2, fun t ht => hQ t ht⟩] with t h1 h2
    obtain ⟨a, ha, hea⟩ := h1
    obtain ⟨b, hb, heb⟩ := h2
    have hab : a ≤ b := by
      have := h t
      rw [ha, hb] at this
      exact_mod_cast this
    have hea' : (V.localHilbertPolynomial x).eval (t : ℚ) = (a : ℚ) := hea
    have heb' : (W.localHilbertPolynomial y).eval (t : ℚ) = (b : ℚ) := heb
    rw [hea', heb']
    exact_mod_cast hab
  exact OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _ hPnonneg hle

theorem localDimension_eq_zero_of_bounded (V : AffineVariety n) (x : Point n) (B : ℕ)
    (h : ∀ t, V.localHilbert x t ≤ (B : ℕ∞)) : V.localDimension x = 0 := by
  obtain ⟨_, N1, hP⟩ := (V.localHilbert_eventually_polynomial x).choose_spec
  have hPnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ (V.localHilbertPolynomial x).eval (T : ℚ) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N1, fun t ht => hP t ht⟩] with t ht
    obtain ⟨a, _, heval⟩ := ht
    have heval' : (V.localHilbertPolynomial x).eval (t : ℚ) = (a : ℚ) := heval
    rw [heval']
    positivity
  have hle : ∀ᶠ T : ℕ in Filter.atTop, (V.localHilbertPolynomial x).eval (T : ℚ) ≤
      (Polynomial.C (B : ℚ)).eval (T : ℚ) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N1, fun t ht => hP t ht⟩] with t h1
    obtain ⟨a, ha, hea⟩ := h1
    have hab : a ≤ B := by
      have := h t
      rw [ha] at this
      exact_mod_cast this
    have hea' : (V.localHilbertPolynomial x).eval (t : ℚ) = (a : ℚ) := hea
    rw [hea', Polynomial.eval_C]
    exact_mod_cast hab
  have := OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _ hPnonneg hle
  rw [Polynomial.natDegree_C] at this
  exact Nat.le_zero.mp this

/-- Jets of a subvariety of `Y` whose chart directions satisfy `K`. -/
theorem jets_bound (Y : AffineVariety n) (hY : Y.IsIrreducible)
    (q : Point n) (hqY : q ∈ Y.points)
    (hT : Module.finrank ℂ (Y.tangentSpace q) = Y.dimension)
    (p : Point n) (i₀ : Fin n) (hq : (q - p) i₀ ≠ 0) (E : Finset (Poly n))
    (h1 : ∀ y ∈ Y.points, (y - p) i₀ ≠ 0 → ∀ e ∈ E,
      eval (((y - p) i₀)⁻¹ • (y - p)) e = 0)
    (h2 : ∀ v ∈ Y.tangentSpace q,
      TrackD.dirChartDeriv (LinearMap.proj i₀) (q - p) v = 0 → v = 0)
    (h3 : Module.finrank ℂ (TrackD.jacKer E (((q - p) i₀)⁻¹ • (q - p))) ≤ Y.dimension)
    (V : AffineVariety n) (hVY : Y.ideal ≤ V.ideal)
    (K : Ideal (Poly n)) (hK : Ideal.span (E : Set (Poly n)) ≤ K)
    (hvan : ∀ x ∈ V.points, (x - p) i₀ ≠ 0 → ∀ f ∈ K,
      eval (((x - p) i₀)⁻¹ • (x - p)) f = 0) (t : ℕ) :
    V.localHilbert q t ≤ ((Module.finrank ℂ
      (Poly n ⧸ (K ⊔ pointIdeal (((q - p) i₀)⁻¹ • (q - p)) ^ (t+1))) : ℕ) : ℕ∞) := by
  rw [localHilbert_eq_jet, ← jet_transfer Y hY q hqY hT p i₀ hq E h1 h2 h3 K hK t]
  have hle : Y.ideal ⊔ Ideal.span (chartClear p i₀ '' (K : Set (Poly n))) ⊔
      pointIdeal q ^ (t+1) ≤ V.ideal ⊔ pointIdeal q ^ (t+1) := by
    refine sup_le (sup_le (hVY.trans le_sup_left) ?_) le_sup_right
    rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hδunit := jet_unit V.ideal q t (X i₀ - C (p i₀)) (by simpa using hq)
    have hprod : (X i₀ - C (p i₀)) * chartClear p i₀ f ∈ V.ideal := by
      rw [← V.vanishingIdeal_points, MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      show eval x ((X i₀ - C (p i₀)) * chartClear p i₀ f) = 0
      by_cases hδ : (x - p) i₀ = 0
      · have h0 : eval x (X i₀ - C (p i₀) : Poly n) = 0 := by simpa using hδ
        rw [map_mul, h0, zero_mul]
      · rw [map_mul, chartClear_eval p i₀ f x hδ, hvan x hx hδ f hf]
        simp
    have h0 : Ideal.Quotient.mk (V.ideal ⊔ pointIdeal q ^ (t+1))
        ((X i₀ - C (p i₀)) * chartClear p i₀ f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hprod)
    rw [map_mul] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((IsUnit.mul_right_eq_zero hδunit).mp h0)
  have hfin := jet_quot_finite (Y.ideal ⊔ Ideal.span (chartClear p i₀ '' (K : Set (Poly n)))) q t
  have hsurj : Function.Surjective (Ideal.Quotient.factorₐ ℂ hle).toLinearMap := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ z, Ideal.Quotient.factorₐ_apply_mk ℂ hle z⟩
  have hr := LinearMap.finrank_range_le (Ideal.Quotient.factorₐ ℂ hle).toLinearMap
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
  exact_mod_cast hr

theorem aeval_point (x : Point n) (f : Poly n) : aeval x f = eval x f := rfl

theorem normalized_mk (i₀ : Fin n) (v : Point n) (hv : v ≠ 0) (hvi : v i₀ ≠ 0) :
    (Projectivization.mk ℂ v hv).rep i₀ ≠ 0 ∧
      ((Projectivization.mk ℂ v hv).rep i₀)⁻¹ • (Projectivization.mk ℂ v hv).rep =
        (v i₀)⁻¹ • v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [← ha]
  have hai : (a • v) i₀ = (a : ℂ) * v i₀ := by simp [Units.smul_def]
  refine ⟨by rw [hai]; exact mul_ne_zero a.ne_zero hvi, ?_⟩
  rw [hai, Units.smul_def, smul_smul]
  congr 1
  rw [mul_inv, mul_comm (a : ℂ)⁻¹, mul_assoc, inv_mul_cancel₀ a.ne_zero, mul_one]

theorem mem_coneThrough_iff (p : Point n) (γ : ProjectiveVariety n) (x : Point n) :
    x ∈ (coneThrough p γ).points ↔ x - p ∈ MvPolynomial.zeroLocus ℂ γ.ideal := by
  unfold coneThrough
  rw [AffineVariety.points_ofIdeal, MvPolynomial.mem_zeroLocus_iff,
    MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h f hf
    have := h _ (Ideal.mem_map_of_mem _ hf)
    rw [aeval_point, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_translate] at this
    rw [aeval_point]
    exact this
  · intro h f hf
    have hle : γ.ideal.map (aeval (fun a => (X a - C (p a) : Poly n))).toRingHom ≤
        RingHom.ker (eval x) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        eval_translate]
      have := h g hg
      rw [aeval_point] at this
      exact this
    have := hle hf
    rw [RingHom.mem_ker] at this
    rw [aeval_point]
    exact this

theorem mem_zeroLocus_sup (I J : Ideal (Poly n)) (x : Point n) :
    x ∈ MvPolynomial.zeroLocus ℂ (I ⊔ J) ↔
      x ∈ MvPolynomial.zeroLocus ℂ I ∧ x ∈ MvPolynomial.zeroLocus ℂ J := by
  constructor
  · intro h
    exact ⟨MvPolynomial.zeroLocus_anti_mono le_sup_left h,
      MvPolynomial.zeroLocus_anti_mono le_sup_right h⟩
  · rintro ⟨hI, hJ⟩
    rw [MvPolynomial.mem_zeroLocus_iff] at hI hJ ⊢
    intro f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
    rw [map_add, hI a ha, hJ b hb, add_zero]

theorem chartClear_homog (p : Point n) (i₀ : Fin n) {j : ℕ} (g : Poly n)
    (hg : g.IsHomogeneous j) :
    chartClear p i₀ g = aeval (fun a => (X a - C (p a) : Poly n)) g := by
  by_cases hg0 : g = 0
  · subst hg0; simp [chartClear]
  have hdeg : g.totalDegree = j := hg.totalDegree hg0
  unfold chartClear
  rw [Finset.sum_eq_single j]
  · rw [hdeg, Nat.sub_self, pow_zero, one_mul,
      homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hg), if_pos rfl]
  · intro l _ hlj
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hg),
      if_neg hlj, map_zero, mul_zero]
  · intro hj
    exfalso; apply hj; rw [hdeg]; exact Finset.self_mem_range_succ j

/-- sc:outer-lift.curve-from-jets. The algebraic core of `outer_lift_curve`. -/
theorem outer_curve_from_jets (Y : AffineVariety n) (hY : Y.IsIrreducible)
    (q : Point n) (hqY : q ∈ Y.points)
    (hT : Module.finrank ℂ (Y.tangentSpace q) = Y.dimension)
    (p : Point n) (i₀ : Fin n) (hq : (q - p) i₀ ≠ 0) (E : Finset (Poly n))
    (h1 : ∀ y ∈ Y.points, (y - p) i₀ ≠ 0 → ∀ e ∈ E,
      eval (((y - p) i₀)⁻¹ • (y - p)) e = 0)
    (h2 : ∀ v ∈ Y.tangentSpace q,
      TrackD.dirChartDeriv (LinearMap.proj i₀) (q - p) v = 0 → v = 0)
    (h3 : Module.finrank ℂ (TrackD.jacKer E (((q - p) i₀)⁻¹ • (q - p))) ≤ Y.dimension)
    (γ : ProjectiveVariety n) (hγ : γ.IsIrreducible) (hγd : γ.dimension = 1)
    (hdir : ∃ h : q ≠ p, radialProjection p q h ∈ γ.points)
    (h4 : ∀ e ∈ E, ∀ z ∈ γ.points, z.rep i₀ ≠ 0 →
      eval ((z.rep i₀)⁻¹ • z.rep) e = 0) :
    ∃ C : AffineVariety n, C.IsIrreducible ∧ C.dimension = 1 ∧ q ∈ C.points ∧
      C.Subvariety Y ∧ (radialImage p C).points ⊆ γ.points ∧
      (radialImage p C).dimension = 1 := by
  obtain ⟨hqp, hz₀⟩ := hdir
  have hqp0 : q - p ≠ 0 := sub_ne_zero.mpr hqp
  obtain ⟨hz₀i, hz₀n⟩ := normalized_mk i₀ (q - p) hqp0 hq
  have hz₀' : Projectivization.mk ℂ (q - p) hqp0 ∈ γ.points := hz₀
  set w₀ : Point n := ((q - p) i₀)⁻¹ • (q - p) with hw₀
  obtain ⟨hΓirr, hΓdim⟩ := chartSlice_curve γ hγ hγd i₀ ⟨_, hz₀', hz₀i⟩
  have hw₀Γ : w₀ ∈ (chartSlice γ i₀).points :=
    AffineVariety.subset_closure _ ⟨_, hz₀', hz₀i, hz₀n.symm⟩
  have hlocΓ := AffineVariety.localDimension_eq_dimension _ w₀ hΓirr hw₀Γ
  set K := (chartSlice γ i₀).ideal with hKdef
  have hKmem : ∀ f : Poly n, (∀ z ∈ γ.points, z.rep i₀ ≠ 0 →
      eval ((z.rep i₀)⁻¹ • z.rep) f = 0) → f ∈ K := by
    intro f hf
    show f ∈ MvPolynomial.vanishingIdeal ℂ _
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro w ⟨z, hz, hzi, rfl⟩
    exact hf z hz hzi
  have hKvan : ∀ f ∈ K, ∀ z ∈ γ.points, z.rep i₀ ≠ 0 →
      eval ((z.rep i₀)⁻¹ • z.rep) f = 0 := by
    intro f hf z hz hzi
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hf) _ ⟨z, hz, hzi, rfl⟩
  have hEK : Ideal.span (E : Set (Poly n)) ≤ K := by
    rw [Ideal.span_le]
    intro e he
    exact hKmem e (h4 e he)
  have hconevan : ∀ x : Point n, x - p ∈ MvPolynomial.zeroLocus ℂ γ.ideal →
      (x - p) i₀ ≠ 0 → ∀ f ∈ K, eval (((x - p) i₀)⁻¹ • (x - p)) f = 0 := by
    intro x hx hδ f hf
    have hv0 : x - p ≠ 0 := fun h => hδ (by rw [h]; rfl)
    obtain ⟨hzi, hzn⟩ := normalized_mk i₀ (x - p) hv0 hδ
    have hz : Projectivization.mk ℂ (x - p) hv0 ∈ γ.points :=
      (γ.mem_points_mk_iff _ hv0).mpr hx
    rw [← hzn]
    exact hKvan f hf _ hz hzi
  -- the cone section `S = Y ∩ (p + cone γ)`
  set S : AffineVariety n := AffineVariety.ofIdeal (Y.ideal ⊔ (coneThrough p γ).ideal) with hS
  have hSpts : ∀ x ∈ S.points, x ∈ Y.points ∧ x - p ∈ MvPolynomial.zeroLocus ℂ γ.ideal := by
    intro x hx
    rw [hS, AffineVariety.points_ofIdeal, mem_zeroLocus_sup] at hx
    exact ⟨hx.1, (mem_coneThrough_iff p γ x).mp hx.2⟩
  have hqcone : q - p ∈ MvPolynomial.zeroLocus ℂ γ.ideal := (γ.mem_points_mk_iff _ hqp0).mp hz₀'
  have hqS : q ∈ S.points := by
    rw [hS, AffineVariety.points_ofIdeal, mem_zeroLocus_sup]
    exact ⟨hqY, (mem_coneThrough_iff p γ q).mpr hqcone⟩
  have hYS : Y.ideal ≤ S.ideal := le_sup_left.trans Ideal.le_radical
  -- (U): jets of `S` at `q` are bounded by those of the slice
  have hU : ∀ t, S.localHilbert q t ≤ (chartSlice γ i₀).localHilbert w₀ t := by
    intro t
    rw [localHilbert_eq_jet (chartSlice γ i₀) w₀ t]
    exact jets_bound Y hY q hqY hT p i₀ hq E h1 h2 h3 S hYS K hEK
      (fun x hx hδ f hf => hconevan x (hSpts x hx).2 hδ f hf) t
  have hSdim : S.localDimension q ≤ 1 := by
    have := localDimension_le_of_localHilbert_le S _ q w₀ hU
    omega
  -- translated equations of `γ` are cleared pullbacks of elements of `K`
  set A : Ideal (Poly n) := Y.ideal ⊔ Ideal.span (chartClear p i₀ '' (K : Set (Poly n))) with hA
  have hτ : γ.ideal.map (aeval (fun a => (X a - C (p a) : Poly n))).toRingHom ≤
      Ideal.span (chartClear p i₀ '' (K : Set (Poly n))) := by
    rw [Ideal.map_le_iff_le_comap]
    intro h hh
    rw [Ideal.mem_comap, ← sum_homogeneousComponent h, map_sum]
    refine Ideal.sum_mem _ (fun j _ => ?_)
    have hj := MvPolynomial.homogeneousComponent_mem_of_mem γ.isHomogeneous hh j
    have hjK : homogeneousComponent j h ∈ K := hKmem _ (fun z hz hzi => by
      have hzr : z.rep ∈ MvPolynomial.zeroLocus ℂ γ.ideal :=
        hz z.rep z.rep_nonzero (Projectivization.mk_rep z)
      rw [Bridges.homogeneous_eval_smul _ (homogeneousComponent_isHomogeneous j h)]
      have h0 := (MvPolynomial.mem_zeroLocus_iff.mp hzr) _ hj
      rw [aeval_point] at h0
      rw [h0, mul_zero])
    have hcl := chartClear_homog p i₀ _ (homogeneousComponent_isHomogeneous j h)
    show (aeval (fun a => (X a - C (p a) : Poly n))) (homogeneousComponent j h) ∈ _
    rw [← hcl]
    exact Ideal.subset_span ⟨_, hjK, rfl⟩
  have hSA : S.ideal ≤ A.radical := by
    show (Y.ideal ⊔ (coneThrough p γ).ideal).radical ≤ A.radical
    rw [Ideal.radical_le_radical_iff]
    refine sup_le (le_sup_left.trans Ideal.le_radical) ?_
    exact Ideal.radical_mono (hτ.trans le_sup_right)
  -- (L): some component through `q` is positive-dimensional
  have hL : ∃ P ∈ S.ideal.minimalPrimes, q ∈ MvPolynomial.zeroLocus ℂ P ∧
      1 ≤ (AffineVariety.ofIdeal P).dimension := by
    by_contra hno
    push Not at hno
    have hPm : ∀ P ∈ S.ideal.minimalPrimes, q ∈ MvPolynomial.zeroLocus ℂ P →
        P = pointIdeal q := by
      intro P hP hqP
      have hPp : P.IsPrime := hP.1.1
      have hirr : (AffineVariety.ofIdeal P).IsIrreducible := by
        show P.radical.IsPrime
        rw [hPp.radical]
        exact hPp
      have hd0 : (AffineVariety.ofIdeal P).dimension = 0 := by
        have := hno P hP hqP
        omega
      obtain ⟨x, hx, -⟩ := TrackA.zeroDim_irreducible_data _ hirr hd0
      rw [AffineVariety.points_ofIdeal] at hx
      have hxq : q = x := by
        have : q ∈ ({x} : Set (Point n)) := hx ▸ hqP
        exact this
      have h := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) P
      rw [hx, hPp.radical, ← hxq] at h
      exact h.symm
    have hfin : S.ideal.minimalPrimes.Finite :=
      Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
    have hgP : ∀ P ∈ S.ideal.minimalPrimes, P ≠ pointIdeal q →
        ∃ g ∈ P, g ∉ pointIdeal q := by
      intro P hP hne
      by_contra hall
      push Not at hall
      have hqP : q ∈ MvPolynomial.zeroLocus ℂ P := by
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro g hg
        have := hall g hg
        have h' : g ∈ MvPolynomial.vanishingIdeal ℂ ({q} : Set (Point n)) := this
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at h'
        rw [aeval_point]
        exact h'
      exact hne (hPm P hP hqP)
    choose! g hgmem hgnot using hgP
    set F := hfin.toFinset.filter (fun P => P ≠ pointIdeal q) with hF
    set h : Poly n := ∏ P ∈ F, g P with hh_def
    have hprime : (pointIdeal q).IsPrime := (pointIdeal_isMaximal q).isPrime
    have hh : h ∉ pointIdeal q := by
      intro hmem
      obtain ⟨P, hPF, hP⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hprime)).mp hmem
      rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset] at hPF
      exact hgnot P hPF.1 hPF.2 hP
    have hhm : ∀ f ∈ pointIdeal q, h * f ∈ S.ideal := by
      intro f hf
      rw [← S.isRadical.radical, ← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      by_cases hPq : P = pointIdeal q
      · rw [hPq]
        exact (pointIdeal q).mul_mem_left h hf
      · have hPF : P ∈ F := by
          rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
          exact ⟨hP, hPq⟩
        have hdvd : g P ∣ h := Finset.dvd_prod_of_mem _ hPF
        exact Ideal.mul_mem_right f P (Ideal.mem_of_dvd _ hdvd (hgmem P hP hPq))
    have hI0 : Ideal.span {h} * pointIdeal q ≤ A.radical := by
      rw [Ideal.mul_le]
      intro a ha b hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [mul_assoc]
      exact hSA (S.ideal.mul_mem_left c (hhm b hb))
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hI0
      (IsNoetherian.noetherian _)
    have hhq : eval q h ≠ 0 := by
      intro h0
      apply hh
      show h ∈ MvPolynomial.vanishingIdeal ℂ ({q} : Set (Point n))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact h0
    have hfinN := jet_quot_finite A q N
    have hbound : ∀ t, Module.finrank ℂ (Poly n ⧸ (A ⊔ pointIdeal q ^ (t+1))) ≤
        Module.finrank ℂ (Poly n ⧸ (A ⊔ pointIdeal q ^ (N+1))) := by
      intro t
      have hle : A ⊔ pointIdeal q ^ (N+1) ≤ A ⊔ pointIdeal q ^ (t+1) := by
        refine sup_le le_sup_left ?_
        intro f hf
        have hfN : f ∈ pointIdeal q ^ N := Ideal.pow_le_pow_right (by omega) hf
        have hmem : h ^ N * f ∈ A := by
          apply hN
          rw [mul_pow]
          exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self h) N) hfN
        have hu := (jet_unit A q t h hhq).pow N
        have h0 : Ideal.Quotient.mk (A ⊔ pointIdeal q ^ (t+1)) (h ^ N * f) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hmem)
        rw [map_mul, map_pow] at h0
        exact Ideal.Quotient.eq_zero_iff_mem.mp ((IsUnit.mul_right_eq_zero hu).mp h0)
      have hsurj : Function.Surjective (Ideal.Quotient.factorₐ ℂ hle).toLinearMap := by
        intro y
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨Ideal.Quotient.mk _ z, Ideal.Quotient.factorₐ_apply_mk ℂ hle z⟩
      have hr := LinearMap.finrank_range_le (Ideal.Quotient.factorₐ ℂ hle).toLinearMap
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
      exact hr
    have hΓb : ∀ t, (chartSlice γ i₀).localHilbert w₀ t ≤
        ((Module.finrank ℂ (Poly n ⧸ (A ⊔ pointIdeal q ^ (N+1))) : ℕ) : ℕ∞) := by
      intro t
      rw [localHilbert_eq_jet, ← jet_transfer Y hY q hqY hT p i₀ hq E h1 h2 h3 K hEK t]
      exact_mod_cast hbound t
    have h0 := localDimension_eq_zero_of_bounded _ w₀ _ hΓb
    rw [hlocΓ, hΓdim] at h0
    exact one_ne_zero h0
  obtain ⟨P, hPmin, hqP, hPdim⟩ := hL
  have hPp : P.IsPrime := hPmin.1.1
  set Cv : AffineVariety n := AffineVariety.ofIdeal P with hCv
  have hCideal : Cv.ideal = P := hPp.radical
  have hCirr : Cv.IsIrreducible := by
    show Cv.ideal.IsPrime
    rw [hCideal]
    exact hPp
  have hqC : q ∈ Cv.points := by
    rw [hCv, AffineVariety.points_ofIdeal]
    exact hqP
  have hSP : S.ideal ≤ P := hPmin.1.2
  have hCY : Cv.Subvariety Y := by
    show Y.ideal ≤ Cv.ideal
    rw [hCideal]
    exact hYS.trans hSP
  have hCdimle : Cv.dimension ≤ 1 := by
    rw [← AffineVariety.localDimension_eq_dimension Cv q hCirr hqC]
    refine le_trans (localDimension_le_of_localHilbert_le Cv S q q (fun t => ?_)) hSdim
    unfold AffineVariety.localHilbert
    exact TrackA.localLengthAt_antitone _ _ q
      (sup_le_sup_right (by rw [hCideal]; exact hSP) _)
  have hCdim : Cv.dimension = 1 := le_antisymm hCdimle hPdim
  have hCcone : Cv.Subvariety (coneThrough p γ) := by
    show (coneThrough p γ).ideal ≤ Cv.ideal
    rw [hCideal]
    exact (le_sup_right.trans Ideal.le_radical).trans hSP
  have hsub := radialImage_subset_of_cone p γ Cv hCcone
  refine ⟨Cv, hCirr, hCdim, hqC, hCY, hsub, ?_⟩
  by_cases hex : ∃ x ∈ Cv.points, ∃ hx : x ≠ p,
      radialProjection p x hx ≠ radialProjection p q hqp
  · obtain ⟨x, hx, hxp, hne⟩ := hex
    exact radialImage_dimension_one p Cv hCirr γ hγ hγd hsub q x hqC hx hqp hxp (Ne.symm hne)
  · push Not at hex
    exfalso
    have hEw : Ideal.span (E : Set (Poly n)) ≤ pointIdeal w₀ := by
      rw [Ideal.span_le]
      intro e he
      show e ∈ MvPolynomial.vanishingIdeal ℂ ({w₀} : Set (Point n))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact h1 q hqY hq e he
    have hvan : ∀ x ∈ Cv.points, (x - p) i₀ ≠ 0 → ∀ f ∈ pointIdeal w₀,
        eval (((x - p) i₀)⁻¹ • (x - p)) f = 0 := by
      intro x hx hδ f hf
      have hxp : x ≠ p := fun h => hδ (by rw [h, sub_self]; rfl)
      have hmk : Projectivization.mk ℂ (x - p) (sub_ne_zero.mpr hxp) =
          Projectivization.mk ℂ (q - p) hqp0 := hex x hx hxp
      have e1 := (normalized_mk i₀ (x - p) (sub_ne_zero.mpr hxp) hδ).2
      rw [hmk] at e1
      have hφ : ((x - p) i₀)⁻¹ • (x - p) = w₀ := e1.symm.trans hz₀n
      rw [hφ]
      have hf' : f ∈ MvPolynomial.vanishingIdeal ℂ ({w₀} : Set (Point n)) := hf
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).mp hf'
    have hb : ∀ t, Cv.localHilbert q t ≤ ((1 : ℕ) : ℕ∞) := by
      intro t
      refine (jets_bound Y hY q hqY hT p i₀ hq E h1 h2 h3 Cv
        (by rw [hCideal]; exact hYS.trans hSP) (pointIdeal w₀) hEw hvan t).trans ?_
      have hsup : pointIdeal w₀ ⊔ pointIdeal w₀ ^ (t+1) = pointIdeal w₀ :=
        sup_eq_left.mpr (Ideal.pow_le_self (by omega))
      rw [hsup, (TrackA.pointQuotientEquiv w₀).toLinearEquiv.finrank_eq, Module.finrank_self]
    have h0 := localDimension_eq_zero_of_bounded Cv q 1 hb
    rw [AffineVariety.localDimension_eq_dimension Cv q hCirr hqC, hCdim] at h0
    exact one_ne_zero h0


end
end DistinctDistances.SparseCones
