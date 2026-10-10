import DistinctDistances.TrackB.Requests
import DistinctDistances.TrackD.RationalImages
import DistinctDistances.TrackD.RationalContainment

namespace DistinctDistances.TrackB
noncomputable section

/-- Helper: the rational point with denominator one is the evaluation vector. -/
theorem bflat_rationalPoint_one {n m : ℕ} (F : Fin m → Poly n) (x : Point n) :
    TrackD.rationalPoint F 1 x = fun i => MvPolynomial.aeval x (F i) := by
  ext i
  simp only [TrackD.rationalPoint, map_one, div_one, MvPolynomial.aeval_eq_eval]

/-- Helper: evaluating a substituted polynomial is evaluating at the vector. -/
theorem bflat_aeval_subst {n m : ℕ} (F : Fin m → Poly n) (H : Poly m) (x : Point n) :
    MvPolynomial.aeval x (MvPolynomial.aeval F H) =
      MvPolynomial.aeval (fun i => MvPolynomial.aeval x (F i)) H := by
  induction H using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp => simp only [map_mul, MvPolynomial.aeval_X, hp]

/-- Helper: the identity coordinate map, for identity-map projective fibers. -/
def bflat_identityPolynomials (m : ℕ) : Fin m → Poly m := fun i => MvPolynomial.X i

/-- Helper: an ideal element vanishes at every representative of a variety point,
via homogeneous components. -/
theorem bflat_rep_vanish {m : ℕ} (V : ProjectiveVariety m) (G : Poly m)
    (hG : G ∈ V.ideal) (v : Point m) (hv : v ≠ 0)
    (hp : Projectivization.mk ℂ v hv ∈ V.points) :
    MvPolynomial.aeval v G = 0 := by
  have hcomp : ∀ d, MvPolynomial.aeval v
      (MvPolynomial.homogeneousComponent d G) = 0 := by
    intro d
    have hmem : MvPolynomial.homogeneousComponent d G ∈ V.ideal :=
      MvPolynomial.homogeneousComponent_mem_of_mem V.isHomogeneous hG d
    have hz := hp v hv rfl
    exact MvPolynomial.mem_zeroLocus_iff.mp hz _ hmem
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent G]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro d _
  exact hcomp d

/-- a normalized affine polynomial image is a chart of the actual
projective image. Use the existing constant-fiber dimension request with
singleton identity-map fibers on the target X_a=1. -/
theorem normalized_polynomial_image_geometry {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (g : Poly n) (hg : g ∉ X.ideal)
    (F : Fin m → Poly n) (a : Fin m)
    (hnorm : ∀ x ∈ X.points, MvPolynomial.aeval x (F a) = 1) :
    (TrackD.rationalImage X F 1).IsIrreducible ∧
      (TrackD.rationalImage X F 1).dimension =
        (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).dimension ∧
      ∀ y ∈ (TrackD.rationalImage X F 1).points, y a = 1 := by
  set W : AffineVariety m := TrackD.rationalImage X F 1 with hWdef
  obtain ⟨x₀, hx₀, hgx₀⟩ : ∃ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    rw [← X.vanishingIdeal_points]
    exact MvPolynomial.mem_vanishingIdeal_iff.mpr h
  have h1 : (1 : Poly n) ∉ X.ideal := by
    intro hmem
    rw [← X.vanishingIdeal_points] at hmem
    have hz := MvPolynomial.mem_vanishingIdeal_iff.mp hmem x₀ hx₀
    simpa using hz
  have hWirr : W.IsIrreducible :=
    TrackD.rational_image_irreducible X hX F 1 h1
  have heval1 : ∀ x : Point n, MvPolynomial.eval x (1 : Poly n) ≠ 0 := by
    intro x
    simp
  have hWideal : W.ideal =
      MvPolynomial.vanishingIdeal ℂ {y | ∃ x ∈ X, MvPolynomial.eval x (1 : Poly n) ≠ 0 ∧
        TrackD.rationalPoint F 1 x = y} := rfl
  have hnormPt : ∀ y ∈ W.points, y a = 1 := by
    have hXa : (MvPolynomial.X a - MvPolynomial.C 1 : Poly m) ∈ W.ideal := by
      rw [hWideal]
      apply MvPolynomial.mem_vanishingIdeal_iff.mpr
      rintro y ⟨x, hx, hgx, rfl⟩
      have hFa : MvPolynomial.aeval x (F a) = 1 := hnorm x hx
      rw [bflat_rationalPoint_one]
      simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Algebra.algebraMap_self, RingHom.id_apply, hFa, sub_self]
    intro y hy
    have hz := (TrackD.mem_ideal_iff_eval_zero W _).mp hXa y hy
    have hsub : y a - 1 = 0 := by simpa using hz
    exact sub_eq_zero.mp hsub
  have hW1 : (1 : Poly m) ∉ W.ideal := by
    intro hmem
    have hx₀X : x₀ ∈ X := hx₀
    have hy₀ : TrackD.rationalPoint F 1 x₀ ∈ W.points :=
      TrackD.rationalPoint_mem_image X F 1 x₀ hx₀X (heval1 x₀)
    have hz := (TrackD.mem_ideal_iff_eval_zero W _).mp hmem _ hy₀
    simpa using hz
  have hId : ∀ y ∈ W.points, MvPolynomial.aeval y (1 : Poly m) ≠ 0 →
      (fun i => MvPolynomial.aeval y (bflat_identityPolynomials m i)) ≠ 0 := by
    intro y hy _
    have hay : y a = 1 := hnormPt y hy
    intro hzero
    have hya : y a = 0 := by
      have hcon := congrFun hzero a
      simpa [bflat_identityPolynomials, MvPolynomial.aeval_X] using hcon
    rw [hay] at hya
    exact one_ne_zero hya
  have hfib0 : ∀ p ∈ polynomialProjectiveImage W 1 (bflat_identityPolynomials m),
      (AffineVariety.closure
        (polynomialProjectiveFiber W 1 (bflat_identityPolynomials m) p)).dimension = 0 := by
    intro p hp
    obtain ⟨y₀, hy₀, hg1, hF0, hmk⟩ := hp
    have hcoords0 : (fun i => MvPolynomial.aeval y₀ (bflat_identityPolynomials m i)) = y₀ := by
      ext i
      simp only [bflat_identityPolynomials, MvPolynomial.aeval_X]
    have hay₀ : y₀ a = 1 := hnormPt y₀ hy₀
    have hy0ne : y₀ ≠ 0 := by rwa [hcoords0] at hF0
    have hmk' : Projectivization.mk ℂ y₀ hy0ne = p := by
      simpa only [hcoords0] using hmk
    have hset : polynomialProjectiveFiber W 1 (bflat_identityPolynomials m) p = {y₀} := by
      ext z
      constructor
      · rintro ⟨hz, _, hFz, hmkz⟩
        have hcoordsz : (fun i => MvPolynomial.aeval z (bflat_identityPolynomials m i)) = z := by
          ext i
          simp only [bflat_identityPolynomials, MvPolynomial.aeval_X]
        have hzne0 : z ≠ 0 := by rwa [hcoordsz] at hFz
        have hmkz' : Projectivization.mk ℂ z hzne0 = p := by
          simpa only [hcoordsz] using hmkz
        have hzz : Projectivization.mk ℂ z _ = Projectivization.mk ℂ y₀ _ :=
          hmkz'.trans hmk'.symm
        obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hzz
        have hza : z a = 1 := hnormPt z hz
        have hsmul : (u : ℂ) • y₀ = z := by simpa [Units.smul_def] using hu
        have hu1 : (u : ℂ) = 1 := by
          have hcon := congrFun hsmul a
          simpa [Pi.smul_apply, smul_eq_mul, hay₀, hza] using hcon
        have hyz : y₀ = z := by
          have h1u : (1 : ℂ) • y₀ = z := by rw [← hu1]; exact hsmul
          simpa using h1u
        exact Set.mem_singleton_iff.mpr hyz.symm
      · intro hz
        rw [Set.mem_singleton_iff.mp hz]
        exact ⟨hy₀, hg1, hF0, hmk⟩
    rw [hset]
    let φ : Point 0 →ₗ[ℂ] Point m := 0
    have hφ : Function.Injective φ := fun _ _ _ => Subsingleton.elim _ _
    have hset0 : {x | ∃ t : Point 0, x = y₀ + φ t ∧
        MvPolynomial.aeval x (1 : Poly m) ≠ 0} = ({y₀} : Set (Point m)) := by
      ext x
      constructor
      · rintro ⟨t, hx, hg⟩
        apply Set.mem_singleton_iff.mpr
        simpa only [φ, LinearMap.zero_apply, add_zero] using hx
      · intro hx
        have hx' : x = y₀ := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨0, by simp [φ], by simp⟩
    have hzero := Request.affine_linear_principal_open_dimension y₀ φ hφ
      (1 : Poly m) 0 (by simp [φ])
    rw [hset0] at hzero
    exact hzero
  have hdimW := Request.polynomial_projective_image_dimension W hWirr 1 hW1
    (bflat_identityPolynomials m) hId (d := 0) hfib0
  have hPirr : (ProjectiveVariety.closure
      (polynomialProjectiveImage X g F)).IsIrreducible :=
    polynomialProjectiveImage_irreducible X hX g hg F (by
      intro x hx _
      intro hzero
      have hcon := congrFun hzero a
      rw [hnorm x hx] at hcon
      simpa using hcon)
  have hQirr : (ProjectiveVariety.closure
      (polynomialProjectiveImage W 1 (bflat_identityPolynomials m))).IsIrreducible :=
    polynomialProjectiveImage_irreducible W hWirr 1 hW1
      (bflat_identityPolynomials m) (by
        intro y hy _
        have hyc : (fun i => MvPolynomial.aeval y (bflat_identityPolynomials m i)) = y := by
          ext i
          simp only [bflat_identityPolynomials, MvPolynomial.aeval_X]
        rw [hyc]
        have hay : y a = 1 := hnormPt y hy
        intro hzero
        rw [hzero] at hay
        simp at hay)
  have hTsub : polynomialProjectiveImage X g F ⊆
      polynomialProjectiveImage W 1 (bflat_identityPolynomials m) := by
    rintro p ⟨x, hx, hxg, hF, hmk⟩
    have hxX : x ∈ X := hx
    have hmem : (fun i => MvPolynomial.aeval x (F i)) ∈ W.points := by
      have hpoint := TrackD.rationalPoint_mem_image X F 1 x hxX (heval1 x)
      rwa [bflat_rationalPoint_one] at hpoint
    have hxa : (fun i => MvPolynomial.aeval x (F i)) a = 1 := hnorm x hx
    have hne : (fun i => MvPolynomial.aeval x (F i)) ≠ 0 := by
      intro hzero
      have hcon := congrFun hzero a
      simp [hxa] at hcon
    have hcc : (fun i => MvPolynomial.aeval (fun j => MvPolynomial.aeval x (F j))
        (bflat_identityPolynomials m i)) = (fun i => MvPolynomial.aeval x (F i)) := by
      ext i
      simp only [bflat_identityPolynomials, MvPolynomial.aeval_X]
    have hne0 : (fun i => MvPolynomial.aeval (fun j => MvPolynomial.aeval x (F j))
        (bflat_identityPolynomials m i)) ≠ 0 := by
      rw [hcc]
      exact hne
    have hunit : (1 : ℂ) • (fun i => MvPolynomial.aeval x (F i)) =
        (fun i => MvPolynomial.aeval (fun j => MvPolynomial.aeval x (F j))
          (bflat_identityPolynomials m i)) := by
      rw [one_smul]
      exact hcc.symm
    refine ⟨_, hmem, by simp, hne0,
      ((Projectivization.mk_eq_mk_iff' ℂ _ _ hne0 hne).mpr ⟨1, hunit⟩).trans hmk⟩
  have hPQ : (ProjectiveVariety.closure
      (polynomialProjectiveImage X g F)).Subvariety
      (ProjectiveVariety.closure
        (polynomialProjectiveImage W 1 (bflat_identityPolynomials m))) := by
    show (ProjectiveVariety.closure
        (polynomialProjectiveImage W 1 (bflat_identityPolynomials m))).ideal ≤
      (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal
    intro G hG
    have hG' : G ∈ MvPolynomial.vanishingIdeal ℂ
        (ProjectiveVariety.nonzeroRepresentatives
          (polynomialProjectiveImage W 1 (bflat_identityPolynomials m))) := hG
    show G ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives (polynomialProjectiveImage X g F))
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro v hv
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hG' v ⟨hv.1, hTsub hv.2⟩
  have hWPts : polynomialProjectiveImage W 1 (bflat_identityPolynomials m) ⊆
      (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).points := by
    intro q hq
    obtain ⟨z, hz, hg1z, hFz, hmkz⟩ := hq
    have hcoordsz : (fun i => MvPolynomial.aeval z (bflat_identityPolynomials m i)) = z := by
      ext i
      simp only [bflat_identityPolynomials, MvPolynomial.aeval_X]
    have hzne : z ≠ 0 := by
      have haz : z a = 1 := hnormPt z hz
      intro hzero
      rw [hzero] at haz
      simp at haz
    have hmkz' : Projectivization.mk ℂ z hzne = q := by
      simpa only [hcoordsz] using hmkz
    rw [← hmkz', ProjectiveVariety.mem_points_mk_iff]
    show z ∈ MvPolynomial.zeroLocus ℂ
      (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro G hG
    have hGvan : G ∈ ProjectiveVariety.vanishingIdeal
        (polynomialProjectiveImage X g F) := hG
    have hpull : MvPolynomial.aeval F G ∈ X.ideal :=
      principal_open_vanishing X hX g _ hg (by
        intro x hx hxg
        rw [bflat_aeval_subst]
        apply MvPolynomial.mem_vanishingIdeal_iff.mp hGvan
        have hxa : (fun i => MvPolynomial.aeval x (F i)) a = 1 := hnorm x hx
        have hne : (fun i => MvPolynomial.aeval x (F i)) ≠ 0 := by
          intro hzero
          have hcon := congrFun hzero a
          simp [hxa] at hcon
        refine ⟨hne, x, hx, hxg, ?_, rfl⟩
        exact hne)
    have hpullV : MvPolynomial.aeval F G ∈
        MvPolynomial.vanishingIdeal ℂ X.points := by
      rw [X.vanishingIdeal_points]
      exact hpull
    have hSwan : ∀ y ∈ {y | ∃ x ∈ X.points,
        (fun i => MvPolynomial.aeval x (F i)) = y},
        MvPolynomial.aeval y G = 0 := by
      rintro y ⟨x, hx, rfl⟩
      rw [← bflat_aeval_subst]
      exact MvPolynomial.mem_vanishingIdeal_iff.mp hpullV x hx
    have hGS : ∀ y ∈ {y | ∃ x ∈ X, MvPolynomial.eval x (1 : Poly n) ≠ 0 ∧
        TrackD.rationalPoint F 1 x = y}, MvPolynomial.aeval y G = 0 := by
      rintro y ⟨x, hx, hgx, rfl⟩
      rw [bflat_rationalPoint_one]
      exact hSwan _ ⟨x, hx, rfl⟩
    have hGW : G ∈ W.ideal := by
      rw [hWideal]
      exact MvPolynomial.mem_vanishingIdeal_iff.mpr hGS
    exact MvPolynomial.mem_zeroLocus_iff.mp hz G hGW
  have hQP : (ProjectiveVariety.closure
      (polynomialProjectiveImage W 1 (bflat_identityPolynomials m))).Subvariety
      (ProjectiveVariety.closure (polynomialProjectiveImage X g F)) := by
    show (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal ≤
      (ProjectiveVariety.closure
        (polynomialProjectiveImage W 1 (bflat_identityPolynomials m))).ideal
    intro G hG
    show G ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives
        (polynomialProjectiveImage W 1 (bflat_identityPolynomials m)))
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro v hv
    obtain ⟨hvne, hp⟩ := hv
    exact bflat_rep_vanish _ G hG v hvne (hWPts hp)
  have hideal : (ProjectiveVariety.closure
      (polynomialProjectiveImage W 1 (bflat_identityPolynomials m))).ideal =
      (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal :=
    le_antisymm (show (ProjectiveVariety.closure
        (polynomialProjectiveImage W 1 (bflat_identityPolynomials m))).ideal ≤
        (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal from hPQ)
      (show (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal ≤
        (ProjectiveVariety.closure
          (polynomialProjectiveImage W 1 (bflat_identityPolynomials m))).ideal from hQP)
  have hQPeq : ProjectiveVariety.closure
      (polynomialProjectiveImage W 1 (bflat_identityPolynomials m)) =
      ProjectiveVariety.closure (polynomialProjectiveImage X g F) :=
    ProjectiveVariety.ext hideal
  rw [hQPeq, Nat.add_zero] at hdimW
  exact ⟨hWirr, hdimW, hnormPt⟩

namespace Request
/-- Request to track A: cone tangent versus tangent in the normalized affine
chart, supplying conc:deg-tangent-coordinates / conc:deg-skew-pencil
(concentration.tex:793–835). Both varieties are actual polynomial image
closures in the shared model; there is no pencil or isotropy conclusion. -/
theorem normalized_polynomial_image_tangent {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (g : Poly n) (hg : g ∉ X.ideal)
    (F : Fin m → Poly n) (a : Fin m)
    (hnorm : ∀ x ∈ X.points, MvPolynomial.aeval x (F a) = 1)
    (y : Point m) (hy : y ∈ (TrackD.rationalImage X F 1).points) :
    (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).affineCone.tangentSpace y =
      (TrackD.rationalImage X F 1).tangentSpace y ⊔ Submodule.span ℂ {y} := by
  classical
  let S := polynomialProjectiveImage X g F
  let W := TrackD.rationalImage X F 1
  let C := (ProjectiveVariety.closure S).affineCone
  let Fx : Point n → Point m := fun x i => MvPolynomial.aeval x (F i)
  have hFxa : ∀ x ∈ X.points, Fx x a = 1 := hnorm
  have hFx0 : ∀ x ∈ X.points, Fx x ≠ 0 := by
    intro x hx h0
    have := hFxa x hx
    rw [h0] at this
    exact zero_ne_one this
  have hFxW : ∀ x ∈ X.points, Fx x ∈ W.points := by
    intro x hx
    apply AffineVariety.subset_closure
    refine ⟨x, hx, by simp, ?_⟩
    funext i
    simp [TrackD.rationalPoint, Fx, MvPolynomial.coe_aeval_eq_eval]
  have hWideal : ∀ f ∈ W.ideal, ∀ x ∈ X.points, MvPolynomial.aeval (Fx x) f = 0 :=
    fun f hf x hx => hFxW x hx f hf
  have hSmem : ∀ x (hx : x ∈ X.points), MvPolynomial.aeval x g ≠ 0 →
      Projectivization.mk ℂ (Fx x) (hFx0 x hx) ∈ S := by
    intro x hx hxg
    exact ⟨x, hx, hxg, hFx0 x hx, rfl⟩
  -- the cone ideal is contained in the ideal of the normalized image
  have hJW : (ProjectiveVariety.closure S).ideal ≤ W.ideal := by
    intro f hf
    have hcomp : MvPolynomial.aeval F f ∈ X.ideal := by
      apply principal_open_vanishing X hX g _ hg
      intro x hx hxg
      rw [GenericFiber.eval_aeval]
      exact hf (Fx x) ⟨hFx0 x hx, hSmem x hx hxg⟩
    change f ∈ MvPolynomial.vanishingIdeal ℂ _
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨x, hx, -, rfl⟩
    have h := hx _ hcomp
    rw [GenericFiber.eval_aeval] at h
    have hrat : TrackD.rationalPoint F 1 x = Fx x := by
      funext i
      simp [TrackD.rationalPoint, Fx, MvPolynomial.coe_aeval_eq_eval]
    rw [hrat]
    exact h
  have hyC : y ∈ C.points := fun f hf => hy f (hJW hf)
  have hya : y a = 1 := by
    have hmem : (MvPolynomial.X a - 1 : Poly m) ∈ W.ideal := by
      change _ ∈ MvPolynomial.vanishingIdeal ℂ _
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      rintro _ ⟨x, hx, -, rfl⟩
      have h := hnorm x hx
      simp only [map_sub, MvPolynomial.aeval_X, map_one]
      simp [TrackD.rationalPoint, MvPolynomial.coe_aeval_eq_eval] at h ⊢
      rw [h, sub_self]
    have h := hy _ hmem
    simp only [map_sub, MvPolynomial.aeval_X, map_one] at h
    exact sub_eq_zero.mp h
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hya
    exact zero_ne_one hya
  have hSne : S.Nonempty := by
    by_contra hS
    apply hg
    rw [← X.vanishingIdeal_points, MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    by_contra hxg
    exact hS ⟨_, hSmem x hx hxg⟩
  have hscale : ∀ c : ℂ, c • y ∈ C.points := by
    intro c
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact zero_mem_projective_cone S hSne
    · have hcy : c • y ≠ 0 := smul_ne_zero hc hy0
      rw [← ProjectiveVariety.mem_points_mk_iff _ _ hcy,
        (Projectivization.mk_eq_mk_iff' ℂ (c • y) y hcy hy0).2 ⟨c, rfl⟩,
        ProjectiveVariety.mem_points_mk_iff]
      exact hyC
  have hyT : y ∈ C.tangentSpace y := by
    apply line_direction_mem_tangent C y y
    intro t
    rw [show y + t • y = (1 + t) • y by rw [add_smul, one_smul]]
    exact hscale (1 + t)
  apply le_antisymm
  · intro v hv
    let w : Point m := v - v a • y
    have hwa : w a = 0 := by
      simp [w, hya]
    have hwC : w ∈ C.tangentSpace y := sub_mem hv (Submodule.smul_mem _ _ hyT)
    have hwW : w ∈ W.tangentSpace y := by
      change w ∈ ⨅ f : W.ideal, LinearMap.ker (differential f.val y)
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro f
      let fh := BridgesB.homogenizeAt a f.val
      have hfhJ : fh ∈ C.ideal := by
        change fh ∈ MvPolynomial.vanishingIdeal ℂ _
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        rintro u ⟨hu, x, hx, hxg, hFx, hmk⟩
        obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ u (Fx x) hu hFx).mp hmk.symm
        rw [← hc, BridgesB.aeval_smul_of_isHomogeneous
          (BridgesB.homogenizeAt_isHomogeneous a f.val),
          BridgesB.aeval_homogenizeAt_of_eq_one a f.val (Fx x) (hFxa x hx),
          hWideal f.val f.property x hx, mul_zero]
      have hline : ∀ t : ℂ, MvPolynomial.aeval (y + t • w) f.val =
          MvPolynomial.aeval (y + t • w) fh := by
        intro t
        symm
        apply BridgesB.aeval_homogenizeAt_of_eq_one
        simp [hya, hwa]
      rw [BridgesB.differential_eq_of_line_eq f.val fh y w hline]
      have hwC' : w ∈ ⨅ f : C.ideal, LinearMap.ker (differential f.val y) := hwC
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hwC'
      exact hwC' ⟨fh, hfhJ⟩
    have hv : v = w + v a • y := by
      simp [w]
    rw [hv]
    exact Submodule.add_mem_sup hwW
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
  · apply sup_le
    · intro v hv
      change v ∈ ⨅ f : C.ideal, LinearMap.ker (differential f.val y)
      have hv' : v ∈ ⨅ f : W.ideal, LinearMap.ker (differential f.val y) := hv
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hv' ⊢
      intro f
      exact hv' ⟨f.val, hJW f.property⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hyT
end Request
end
end DistinctDistances.TrackB
