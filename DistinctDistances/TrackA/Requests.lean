import DistinctDistances.TrackA.Definitions
import DistinctDistances.TrackA.MAConeAux
import DistinctDistances.TrackA.ProjectiveSectionSupport
import DistinctDistances.TrackA.RegularSectionConstantSupport
import DistinctDistances.TrackA.SectionLinearDivisionSupport
import DistinctDistances.TrackA.CutSaturationSupport
import DistinctDistances.TrackA.ProjectiveCutFamilySupport
import DistinctDistances.TrackA.GenericLinearCutSupport
import DistinctDistances.TrackA.ReducedScalarExtensionSupport
import DistinctDistances.TrackA.ProjectiveReducedLinearFormSupport
import DistinctDistances.TrackA.AffineFiniteNormalizationSupport
import DistinctDistances.TrackA.NormalizationRankSupport
import DistinctDistances.TrackA.NormalizationAffineRankSupport
import DistinctDistances.TrackA.AffineFiberPointSupport
import DistinctDistances.TrackA.AffineEtaleFiberSupport
import DistinctDistances.TrackA.AffineFiberTensorSupport
import DistinctDistances.TrackA.GenericFiberFamilySupport
import DistinctDistances.TrackA.ZeroDimSectionSupport
import DistinctDistances.TrackA.LocalJacobianAssemblySupport
import DistinctDistances.TrackA.JacobianContractionSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical TensorProduct

/-- `poly:hilbert.finite-affine-etale-rank-fibers`, polynomial.tex:349–359.
The algebraic step: a nonzero principal base open on which the
literal fiber coordinate quotients are etale and their complex dimensions
equal the original affine module rank. The body uses characteristic-zero
generic etaleness, algebraic shrinking to a base open, finite-flat fiber
rank and the literal quotient/base-change equivalence. -/
theorem request_finite_affine_normalization_etale_rank_fibers {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k) (hf : (affineNormalizationMap V ψ).Finite) :
    ∃ g : Poly k, g ≠ 0 ∧ ∀ y : Point k, MvPolynomial.aeval y g ≠ 0 →
      Algebra.Etale ℂ (Poly n ⧸ affineFiberIdeal V (⟨ψ, 0⟩ : AffineProjection n k) y) ∧
      Module.finrank ℂ (Poly n ⧸ affineFiberIdeal V (⟨ψ, 0⟩ : AffineProjection n k) y) =
        affineNormalizationRank V ψ := by
  obtain ⟨g, hg, he⟩ := affineNormalization_etale_base_open V hV hd ψ hf
  refine ⟨g, hg, ?_⟩
  intro y hgy
  letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
    (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  letI : SMul (Poly k) (Poly n ⧸ V.ideal) :=
    (affineNormalizationMap V ψ).toRingHom.toAlgebra.toSMul
  letI := (MvPolynomial.aeval (R := ℂ) y).toRingHom.toAlgebra
  letI : Module (Poly k) ℂ := (MvPolynomial.aeval (R := ℂ) y).toRingHom.toAlgebra.toModule
  letI : SMul (Poly k) ℂ := (MvPolynomial.aeval (R := ℂ) y).toRingHom.toAlgebra.toSMul
  haveI : Module.Finite (Poly k) (Poly n ⧸ V.ideal) := hf
  obtain ⟨hetale, hrank⟩ := etale_base_open_field_fiber (Poly k)
    (Poly n ⧸ V.ideal) ℂ g hg he hgy
  letI := hetale
  set_option backward.isDefEq.respectTransparency false in
    let e : (ℂ ⊗[Poly k] (Poly n ⧸ V.ideal)) ≃ₐ[ℂ]
        (Poly n ⧸ affineFiberIdeal V (⟨ψ, 0⟩ : AffineProjection n k) y) :=
      affineFiberTensorEquiv V ψ y
  set_option backward.isDefEq.respectTransparency false in
    refine ⟨Algebra.Etale.of_equiv (R := ℂ)
      (A := ℂ ⊗[Poly k] (Poly n ⧸ V.ideal)) e, ?_⟩
  set_option backward.isDefEq.respectTransparency false in
    change Module.finrank ℂ _ = Module.finrank (Poly k) (Poly n ⧸ V.ideal)
  set_option backward.isDefEq.respectTransparency false in
    exact e.toLinearEquiv.finrank_eq.symm.trans hrank

/-- `poly:hilbert.finite-affine-rank-fibers`, polynomial.tex:349–359.
For the actual finite full-dimensional affine coordinate map, reduced
fibers on a principal open have complex-point count equal to module rank.
The literal quotient/point correspondence and finite etale point count
convert the constructed algebraic principal open to geometric generic degree. -/
theorem request_finite_affine_normalization_rank_fibers {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k) (hf : (affineNormalizationMap V ψ).Finite) :
    (⟨ψ, 0⟩ : AffineProjection n k).GenericallyFiniteOfDegree V
      (affineNormalizationRank V ψ) := by
  obtain ⟨g, hg, hfiber⟩ := request_finite_affine_normalization_etale_rank_fibers V hV hd ψ hf
  have hfinite := (affineNormalizationMap_finite_iff V ψ).mp hf
  refine ⟨affineNormalizationRank_pos_of_finite V hV hd ψ hf, g, ?_, ?_⟩
  · rw [finite_affine_projection_image_ideal_bot V hV hd _ hfinite]
    exact hg
  · intro y hy hgy
    obtain ⟨hetale, hrank⟩ := hfiber y hgy
    letI := hetale
    obtain ⟨hpoints, hcard⟩ := affineFiber_count_of_etale V
      (⟨ψ, 0⟩ : AffineProjection n k) y
    exact ⟨hpoints, hcard.trans hrank⟩

/-- `poly:hilbert.generic-rank-fibers`, polynomial.tex:349–359.
The remaining positive-dimensional geometric step: the original affine
projection has exactly the rank of the finite cone map on a principal open.
The body now uses the original rank comparison and the actual common-degree
rank specialization, leaving the finite affine principal-open count above.
The zero-dimensional public case is closed separately. -/
theorem request_positive_infinity_normalization_rank_fibers {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k) (hk : 0 < k)
    (ψ : LinearProjection n k)
    (hfinite : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite) :
    (⟨ψ, 0⟩ : AffineProjection n k).GenericallyFiniteOfDegree V
      (coneNormalizationRank V ψ) := by
  have hcone := coneNormalizationMap_finite V ψ hfinite
  rw [normalization_cone_rank_eq_affine_rank V ψ hcone]
  exact request_finite_affine_normalization_rank_fibers V hV hd ψ
    (affineNormalizationMap_finite_of_cone V ψ hcone)

/-- `poly:hilbert.generic-degree`, polynomial.tex:349–359.
For the original linear parameters finite on the literal infinity cut,
compare generic module rank with actual degree, then obtain the reduced
characteristic-zero fiber count on a principal open. Consumer: Hilbert.lean,
poly_hilbert_normalization. The body assembles the cone-rank comparison
and the remaining positive-dimensional rank/fiber bridge. -/
theorem request_infinity_projection_generic_degree {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k) (hψ : Function.Surjective ψ)
    (hfinite : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite) :
    ∃ r : ℕ, (r : ℚ) = V.degree ∧
      (⟨ψ, 0⟩ : AffineProjection n k).GenericallyFiniteOfDegree V r := by
  cases k with
  | zero => exact zeroDim_linear_projection_generic_degree V hV hd ψ
  | succ k =>
    exact ⟨coneNormalizationRank V ψ, infinity_normalization_rank_eq_degree V hV hd ψ hfinite,
      request_positive_infinity_normalization_rank_fibers V hV hd (Nat.succ_pos k) ψ hfinite⟩

/-- Algebraic data of the selected geometric generic fiber of a fixed
linear normalization. The ambient coordinates retain degree one. -/
structure ComponentGenericFiber {n k : ℕ} (F : AffineFamily.Family n)
    (φ : AffineProjection n k) where
  Ω : Type
  [fieldInst : Field Ω]
  [algebraInst : Algebra ℂ Ω]
  [closedInst : IsAlgClosed Ω]
  t : Fin k → Ω
  independent : AlgebraicIndependent ℂ t
  r : ℕ
  points : Fin r → FieldPoint n Ω
  points_injective : Function.Injective points
  ev : (Poly n ⧸ (AffineFamily.locus F).ideal) →ₐ[ℂ] (Fin r → Ω)
  ev_coordinates : ∀ (f : Poly n) (i : Fin r),
    ev (Ideal.Quotient.mk (AffineFamily.locus F).ideal f) i =
      MvPolynomial.eval₂ (algebraMap ℂ Ω) (points i) f
  ev_base : ∀ j : Fin k,
    ev (Ideal.Quotient.mk (AffineFamily.locus F).ideal
      (φ.pullback (MvPolynomial.X j))) = fun _ => t j
  count_degree : (r : ℚ) = AffineFamily.degree F

attribute [instance] ComponentGenericFiber.fieldInst
  ComponentGenericFiber.algebraInst ComponentGenericFiber.closedInst

def ComponentGenericFiber.equations {n k : ℕ} {F : AffineFamily.Family n}
    {φ : AffineProjection n k} (G : ComponentGenericFiber F φ) (E : Set (Poly n)) :
    Set (FieldPoly n G.Ω) :=
  (MvPolynomial.map (algebraMap ℂ G.Ω) '' E) ∪
    Set.range (fun j : Fin k =>
      MvPolynomial.map (algebraMap ℂ G.Ω) (φ.pullback (MvPolynomial.X j)) -
        MvPolynomial.C (G.t j))

/-- Construct all selected sheets in one closed generic base field,
retaining each sheet's original component for separate list isolation. -/
theorem componentGenericFiber_with_components {n k : ℕ} (F : AffineFamily.Family n)
    (hF : AffineFamily.IsPure F k) (φ : AffineProjection n k)
    (hnorm : ∀ V ∈ F, FiniteAffineProjection φ V ∧ ∃ r : ℕ,
      (r : ℚ) = V.degree ∧ φ.GenericallyFiniteOfDegree V r) :
    ∃ G : ComponentGenericFiber F φ, ∀ j : Fin G.r,
      ∃ V ∈ F, G.points j ∈ affineFiberOver V φ G.t := by
  obtain ⟨S, hS, hcard⟩ := affineFamily_genericFiber_finset F hF φ hnorm
    (GenericBaseField k) (genericBasePoint k) (genericBasePoint_independent k)
  let e : Fin S.card ≃ S := (Finset.equivFinOfCardEq rfl).symm
  let points : Fin S.card → FieldPoint n (GenericBaseField k) := fun j => (e j).val
  have hp (j : Fin S.card) : ∃ V ∈ F, points j ∈ affineFiberOver V φ (genericBasePoint k) :=
    (hS _).mp (e j).property
  let G : ComponentGenericFiber F φ :=
    { Ω := GenericBaseField k
      fieldInst := inferInstance
      algebraInst := inferInstance
      closedInst := inferInstance
      t := genericBasePoint k
      independent := genericBasePoint_independent k
      r := S.card
      points := points
      points_injective := Subtype.val_injective.comp e.injective
      ev := affineFamilyFiberEvaluation F φ _ (genericBasePoint k) points hp
      ev_coordinates := affineFamilyFiberEvaluation_coordinates F φ _ (genericBasePoint k) points hp
      ev_base := affineFamilyFiberEvaluation_base F φ _ (genericBasePoint k) points hp
      count_degree := hcard }
  exact ⟨G, hp⟩

/-- Request to track A, `poly:hilbert.generic-fiber`, polynomial.tex:349–373.
Build the selected geometric generic sheets of the supplied simultaneous
linear normalization. Their point ideals must be minimal over the *whole*
fiber system, even when omitted components have larger dimension.
The body constructs literal sheets, then contracts any prime below a sheet
to the original minimal component and uses integrality of its field fiber. -/
theorem request_component_generic_fiber {n k : ℕ} (F : AffineFamily.Family n)
    (hF : AffineFamily.IsPure F k) (φ : AffineProjection n k)
    (hnorm : Function.Surjective φ.linear ∧
      ∀ V ∈ F, FiniteAffineProjection φ V ∧ ∃ r : ℕ,
        (r : ℚ) = V.degree ∧ φ.GenericallyFiniteOfDegree V r)
    (E : Set (Poly n))
    (hcomponents : ∀ V ∈ F, V.IsComponentOf (Ideal.span E)) :
    ∃ G : ComponentGenericFiber F φ, ∀ i : Fin G.r,
      pointIdealOver (G.points i) ∈ (Ideal.span (G.equations E)).minimalPrimes := by
  obtain ⟨G, hG⟩ := componentGenericFiber_with_components F hF φ hnorm.2
  refine ⟨G, ?_⟩
  intro j
  obtain ⟨V, hV, hx⟩ := hG j
  exact affineFiberOver_minimalPrime V φ (hnorm.2 V hV).1 E
    (hcomponents V hV) G.Ω G.t G.independent ⟨G.points j, hx⟩

/-- New geometric request, `poly:polar.equation`, polynomial.tex:951–952.
A nonempty reduced pure projective plane curve has one actual nonzero
homogeneous equation. Its degree and squarefreeness are proved separately. -/
theorem request_plane_curve_equation (C : ProjectiveVariety 3)
    (hC : C.IsPure 1) (hne : C.points.Nonempty) :
    ∃ f : Poly 3, f ≠ 0 ∧ f.IsHomogeneous f.totalDegree ∧ C.ideal = Ideal.span {f} :=
  mACone_plane_curve_equation C hC hne

/-- `poly:regularity.local-jacobian-ideal`, polynomial.tex:547–555.
The remaining one-component algebraic step in the original pure-family
Jacobian germ theorem. The localized ideal is the actual polynomial point
localization. The dimension hypothesis is the original global component
dimension. -/
theorem request_irreducible_local_jacobian_ideal {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (V : AffineVariety n) (hV : V.IsIrreducible) (hdim : V.dimension = k)
    (x : Point n) (hx : x ∈ V.points)
    (f : Fin (n-k) → Poly n) (cols : Fin (n-k) ↪ Fin n)
    (hf : ∀ i, f i ∈ V.ideal)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0) :
    localizedIdeal V.ideal x = localizedIdeal (Ideal.span (Set.range f)) x := by
  classical
  have hzero : ∀ i, MvPolynomial.eval x (f i) = 0 := by
    intro i
    simpa only [MvPolynomial.aeval_eq_eval] using hx (f i) (hf i)
  let Q := jacobianContractedIdeal x f
  letI : Q.IsPrime := jacobianContractedIdeal_isPrime x f cols hzero hdet
  letI : V.ideal.IsPrime := hV
  have hspan : Ideal.span (Set.range f) ≤ V.ideal := Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hf i)
  have hle : Q ≤ V.ideal := by
    have h := Ideal.comap_mono (f := algebraMap (Poly n) (PointLocalRing x))
      (Ideal.map_mono (f := algebraMap (Poly n) (PointLocalRing x)) hspan)
    change Q ≤ (localizedIdeal V.ideal x).comap (algebraMap (Poly n) (PointLocalRing x)) at h
    rwa [localizedPrime_contraction V.ideal hV x hx] at h
  have hQdim : OAI.QuarticPowerFree.affineDimension Q = k :=
    jacobianContractedVariety_dimension hk x f cols hzero hdet
  have hQV : Q = V.ideal :=
    AffineFamily.prime_same_dimension_eq_of_le Q V.ideal hle hQdim hdim
  rw [← hQV]
  exact jacobianContractedIdeal_localized x f

/-- New geometric request, `poly:regularity.germ`, polynomial.tex:547–555.
At a point of a pure family, independent differentials of equations
vanishing on the family give the same reduced smooth germ. This needs the
algebraic/analytic local-dimension comparison beyond the implicit chart. -/
theorem request_pure_family_jacobian_germ {n : ℕ} (F : AffineFamily.Family n)
    (k : ℕ) (hk : k ≤ n) (hF : AffineFamily.IsPure F k) (E : List (Poly n))
    (hE : ∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal)
    (x : Point n) (hx : x ∈ (AffineFamily.locus F).points)
    (hm : ∃ m ∈ jacobianMinors E (n-k), MvPolynomial.eval x m ≠ 0) :
    SameGermAt (equationLocus E) (AffineFamily.locus F) x ∧
      (equationLocus E).IsSmoothAt x ∧ (equationLocus E).localDimension x = k ∧
      ∀ V ∈ F, ∀ W ∈ F, x ∈ V → x ∈ W → V = W := by
  exact pure_family_jacobian_germ_of_local_criterion
    request_irreducible_local_jacobian_ideal F k hk hF E hE x hx hm

/-- `poly:hilbert.union-generic-fiber`, polynomial.tex:349–373,407–414.
All selected sheets live in one geometric generic fiber. A sheet shared
by several component lists occurs only once, but is isolated in each
original system to whose selected list it belongs. The union of the
original systems need not isolate it. -/
theorem request_component_generic_fiber_lists {n k : ℕ}
    (F : AffineFamily.Family n) (hF : AffineFamily.IsPure F k)
    (φ : AffineProjection n k)
    (hnorm : Function.Surjective φ.linear ∧
      ∀ V ∈ F, FiniteAffineProjection φ V ∧ ∃ r : ℕ,
        (r : ℚ) = V.degree ∧ φ.GenericallyFiniteOfDegree V r)
    (s : ℕ) (lists : Fin s → AffineFamily.Family n)
    (hunion : ∀ V, V ∈ F ↔ ∃ i, V ∈ lists i)
    (E : Fin s → Set (Poly n))
    (hcomponents : ∀ i, ∀ V ∈ lists i, V.IsComponentOf (Ideal.span (E i))) :
    ∃ (G : ComponentGenericFiber F φ) (indices : Fin s → Finset (Fin G.r)),
      (∀ j : Fin G.r, ∃ i, j ∈ indices i) ∧
      ∀ i, ∀ j ∈ indices i,
        pointIdealOver (G.points j) ∈ (Ideal.span (G.equations (E i))).minimalPrimes := by
  obtain ⟨G, hG⟩ := componentGenericFiber_with_components F hF φ hnorm.2
  let indices (i : Fin s) : Finset (Fin G.r) := Finset.univ.filter
    (fun j => ∃ V ∈ lists i, G.points j ∈ affineFiberOver V φ G.t)
  refine ⟨G, indices, ?_, ?_⟩
  · intro j
    obtain ⟨V, hV, hx⟩ := hG j
    obtain ⟨i, hi⟩ := (hunion V).mp hV
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ j, V, hi, hx⟩⟩
  · intro i j hj
    obtain ⟨V, hV, hx⟩ := (Finset.mem_filter.mp hj).2
    have hVF : V ∈ F := (hunion V).mpr ⟨i, hV⟩
    exact affineFiberOver_minimalPrime V φ (hnorm.2 V hVF).1 (E i)
      (hcomponents i V hV) G.Ω G.t G.independent ⟨G.points j, hx⟩

/-- `poly:hilbert.sections-constants`, polynomial.tex:336–338.
Regular degree-zero sections on an irreducible projective component are
constant; adding components bounds the whole-family section dimension. -/
theorem request_regularSection_zero_bound {n : ℕ} (F : ProjectiveFamily.Family n)
    (k : ℕ) (hF : ProjectiveFamily.IsPure F k) :
    (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) 0) : ℚ) ≤
      ProjectiveFamily.degree F := by
  exact regularSection_family_zero_bound F (fun V hV => (hF V hV).1)

/-- `poly:hilbert.sections-points`, polynomial.tex:334–335.
All homogeneous sections of a reduced projective zero-fold are detected
by one value at each projective point, not by infinitely many cone points. -/
theorem request_regularSection_zeroDim_bound {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ProjectiveFamily.IsPure F 0) (D : ℕ) :
    (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) : ℚ) ≤
      ProjectiveFamily.degree F := by
  exact regularSection_zeroDim_bound F hF D

/-- `poly:hilbert.sections-points-finite`, polynomial.tex:334–335.
Actual finiteness of the reduced finite-point section space, needed
independently of its numerical finrank bound. -/
theorem request_regularSection_zeroDim_finite {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ProjectiveFamily.IsPure F 0) (D : ℕ) :
    Module.Finite ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) := by
  exact regularSection_zeroDim_finite F hF D

/-- `poly:hilbert.bertini-linear-form`, polynomial.tex:318–329.
The remaining reduced-Bertini input is the existence of one linear
equation whose actual cut sum ideal is radical on every coordinate chart.
The pure projective cut family and degree/clearing are proved separately. -/
theorem request_regularSection_reduced_linear_form {n : ℕ} (F : ProjectiveFamily.Family n)
    (k : ℕ) (hF : ProjectiveFamily.IsPure F (k+1)) :
    ∃ ℓ : Poly n, ℓ.IsHomogeneous 1 ∧
      (∀ V ∈ F, ℓ ∉ V.ideal) ∧ ReducedLinearCutCharts (ProjectiveFamily.locus F) ℓ := by
  exact projective_family_reduced_linear_form F (fun V hV => (hF V hV).1)

/-- `poly:hilbert.bertini-reduced-charts`, polynomial.tex:318–329.
Choose one pure reduced projective hyperplane section whose actual
sum-ideal is reduced after inverting each coordinate. Power clearing and
degree preservation are proved separately; neither is a premise here. -/
theorem request_regularSection_reduced_charts {n : ℕ} (F : ProjectiveFamily.Family n)
    (k : ℕ) (hF : ProjectiveFamily.IsPure F (k+1)) :
    ∃ (W : ProjectiveFamily.Family n) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
      (hWV : (ProjectiveFamily.locus W).Subvariety (ProjectiveFamily.locus F)),
      ProjectiveFamily.IsPure W k ∧
      (∀ V ∈ F, ℓ ∉ V.ideal) ∧
      (∀ p, p ∈ (ProjectiveFamily.locus W).points ↔
        p ∈ (ProjectiveFamily.locus F).points ∧ MvPolynomial.eval p.rep ℓ = 0) ∧
      ℓ ∈ (ProjectiveFamily.locus W).ideal ∧
      ReducedLinearCutCharts (ProjectiveFamily.locus F) ℓ := by
  obtain ⟨ℓ, hℓ, havoid, hred⟩ := request_regularSection_reduced_linear_form F k hF
  obtain ⟨W, hW, hWV, hpoints, hℓW⟩ := projective_linear_cut_family F k hF ℓ hℓ havoid
  exact ⟨W, ℓ, hℓ, hWV, hW, havoid, hpoints, hℓW, hred⟩

/-- `poly:hilbert.bertini-reduced-cut`, polynomial.tex:318–329.
The reduced generic hyperplane has the actual saturated cut ideal. The
section-map kernel identity is proved separately from this geometric
coordinate-power clearing condition. -/
theorem request_regularSection_reduced_hyperplane {n : ℕ} (F : ProjectiveFamily.Family n)
    (k : ℕ) (hF : ProjectiveFamily.IsPure F (k+1)) :
    ∃ (W : ProjectiveFamily.Family n) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
      (hWV : (ProjectiveFamily.locus W).Subvariety (ProjectiveFamily.locus F)),
      ProjectiveFamily.IsPure W k ∧ ProjectiveFamily.degree W = ProjectiveFamily.degree F ∧
      (∀ V ∈ F, ℓ ∉ V.ideal) ∧
      (∀ p, p ∈ (ProjectiveFamily.locus W).points ↔
        p ∈ (ProjectiveFamily.locus F).points ∧ MvPolynomial.eval p.rep ℓ = 0) ∧
      ℓ ∈ (ProjectiveFamily.locus W).ideal ∧
      ∀ f ∈ (ProjectiveFamily.locus W).ideal, ∀ i : Fin n, ∃ r : ℕ,
        MvPolynomial.X i ^ r * f ∈ (ProjectiveFamily.locus F).ideal ⊔ Ideal.span {ℓ} := by
  obtain ⟨W, ℓ, hℓ, hWV, hW, havoid, hpoints, hℓW, hred⟩ :=
    request_regularSection_reduced_charts F k hF
  refine ⟨W, ℓ, hℓ, hWV, hW, ?_, havoid, hpoints, hℓW, ?_⟩
  · exact projective_family_cut_degree_of_reduced_charts F W k hF hW hWV ℓ hℓ havoid hpoints hℓW hred
  · exact projective_cut_power_clear_of_reduced_charts
      (ProjectiveFamily.locus F) (ProjectiveFamily.locus W) ℓ hℓ hpoints hred

/-- `poly:hilbert.bertini-sections`, polynomial.tex:318–333.
A generic hyperplane has reduced pure section of the same degree. The
kernel of the actual section restriction is exactly the image of
multiplication by its linear equation. This is not a coordinate-quotient
Hilbert difference assertion. -/
theorem request_regularSection_hyperplane {n : ℕ} (F : ProjectiveFamily.Family n)
    (k : ℕ) (hF : ProjectiveFamily.IsPure F (k+1)) :
    ∃ (W : ProjectiveFamily.Family n) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
      (hWV : (ProjectiveFamily.locus W).Subvariety (ProjectiveFamily.locus F)),
      ProjectiveFamily.IsPure W k ∧ ProjectiveFamily.degree W = ProjectiveFamily.degree F ∧
      (∀ V ∈ F, ℓ ∉ V.ideal) ∧
      (∀ p, p ∈ (ProjectiveFamily.locus W).points ↔
        p ∈ (ProjectiveFamily.locus F).points ∧ MvPolynomial.eval p.rep ℓ = 0) ∧
      ∀ D, LinearMap.ker (sectionRestriction (ProjectiveFamily.locus F)
          (ProjectiveFamily.locus W) hWV (D+1)) =
        LinearMap.range (sectionMultiplyLinear (ProjectiveFamily.locus F) D ℓ hℓ) := by
  obtain ⟨W, ℓ, hℓ, hWV, hW, hdeg, havoid, hpoints, hℓW, hclear⟩ :=
    request_regularSection_reduced_hyperplane F k hF
  refine ⟨W, ℓ, hℓ, hWV, hW, hdeg, havoid, hpoints, ?_⟩
  intro D
  exact sectionRestriction_ker_eq_range_of_power_clear (ProjectiveFamily.locus F)
    (ProjectiveFamily.locus W) hWV D ℓ hℓ
    (projective_family_cancel_polynomial F (fun V hV => (hF V hV).1) ℓ havoid)
    hclear hℓW


end
end DistinctDistances.TrackA
