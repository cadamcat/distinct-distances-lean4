import DistinctDistances.TrackB.MixedHilbert
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
Evidence for Track B, parts (iv)–(v) of `triple_rank_identity`.

- `dehomogenize_rank_of_weight_link`: the docstring sketch for (iv) closes once
  the two missing hypotheses (`hWlink`, `hX`) are added. The frozen statement,
  which quantifies over an arbitrary weight `w` and arbitrary `μ`, is false as
  stated; see `dehomogenize_instance_hyps` /
  `dehomogenize_rank_conclusion_false` for a machine-checked counterexample
  (all hypotheses hold, the conclusion is impossible).
- `backbone_one_eq_zero` / `full_one_eq_one`: the arithmetic core showing the
  (v) backbone `k`-sum and the full `(δ,k,l,β)`-sum disagree already at `e = 1`
  with constant base rank (0 vs 1). Hence `series_bridge` cannot follow
  formally from its hypotheses.
-/

namespace DistinctDistances.TrackB
namespace MBPart2Aux

set_option autoImplicit false
open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

noncomputable local instance : AddRightCancelMonoid (Fin 2 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 2 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

noncomputable local instance : AddRightCancelMonoid (Fin 3 →₀ ℕ) :=
  { (inferInstance : AddMonoid (Fin 3 →₀ ℕ)) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

/-- Corrected dehomogenization: with the weight link, the sketch closes. -/
theorem dehomogenize_rank_of_weight_link {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (w : Option (Fin (e + (e + e) + (skewDim e + 1))) → (Fin 3 →₀ ℕ))
    (I : Ideal (MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ w))
    (g : Fin e → MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (hg : ∀ k, (g k).IsWeightedHomogeneous w (HilbertMulti.tripleDegree 1 0 1))
    (μ : MvPolynomial (Option (Fin (e + (e + e) + (skewDim e + 1)))) ℂ)
    (hμ : μ.IsWeightedHomogeneous w (HilbertMulti.tripleDegree 1 0 1))
    (hWlink : ∀ i, w (some i) =
      HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) i)
    (hX : MvPolynomial.X none ∈
      Ideal.span (Set.range g) ⊔ (Ideal.span {μ} ⊔ I))
    (hVanishG : ∀ k, OAI.PiExponentSiegel.W08.coordinateEval (g k) ∈
      MvPolynomial.vanishingIdeal ℂ
        (tripleRepresentatives (incidenceTriples C Γ H)))
    (hVanishI : OAI.PiExponentSiegel.W08.coordinateImageIdeal I ≤
      MvPolynomial.vanishingIdeal ℂ
        (tripleRepresentatives (incidenceTriples C Γ H)))
    (hReverse : ∃ N : ℕ, ∀ s t u : ℕ, e * N + 1 ≤ s →
      Module.finrank ℂ (HilbertMulti.sectionSpace
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)))
        (OAI.PiExponentSiegel.W08.coordinateImageIdeal
          (Ideal.span (Set.range g) ⊔ (Ideal.span {μ} ⊔ I)))
        (HilbertMulti.tripleDegree s t u)) =
      tripleHilbert (incidenceTriples C Γ H) s t u) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s → N ≤ t → N ≤ u →
      Module.finrank ℂ (HilbertMulti.sectionSpace w
        (Ideal.span (Set.range g) ⊔ (Ideal.span {μ} ⊔ I))
        (HilbertMulti.tripleDegree s t u)) =
      tripleHilbert (incidenceTriples C Γ H) s t u := by
  obtain ⟨N, hN⟩ := hReverse
  refine ⟨e * N + 1, fun s t u hs ht hu => ?_⟩
  have hQ := HilbertMulti.coordinateQuotient_section_finrank w _ hX
    (HilbertMulti.tripleDegree s t u)
  have hW : (fun i => w (some i)) =
      HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) :=
    funext hWlink
  rw [hW] at hQ
  rw [hQ]
  exact hN s t u hs
/-- Arithmetic core for the series_bridge refutation: at e = 1 with constant
base rank 1, the backbone sum is 0. -/
theorem backbone_one_eq_zero (s t u : ℕ) :
    ∑ k ∈ Finset.range (1 + 1), (-1 : ℚ) ^ k * ((((1 : ℕ).choose k : ℕ)) : ℚ) *
      (((1 : ℕ) : ℚ) * (((((skewDim 1 + 1).multichoose (u - k) : ℕ))) : ℚ)) = 0 := by
  have hsk : skewDim (1 : ℕ) = 0 := rfl
  simp [Finset.sum_range_succ, hsk]
/-- Arithmetic core, part 2: the full sum is 1 under the same data. -/
theorem full_one_eq_one (s t u : ℕ) :
    ∑ m ∈ Finset.range 1, (-1 : ℚ) ^ m *
      (∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (1 + 1),
        ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
          if δ + k + l + β = m then
            ((-1 : ℚ) ^ (l + β) * ((((1 : ℕ).choose k : ℕ)) : ℚ)) *
              (((1 : ℕ)) : ℚ)
          else 0) *
      (((Nat.choose (u - m + (1 : ℕ).choose 2) ((1 : ℕ).choose 2) : ℕ)) : ℚ) = 1 := by
  simp [Finset.sum_range_succ]
noncomputable example (I : Ideal (Poly 3)) : Module ℂ (Poly 3 ⧸ I) := inferInstance
#check @Module.finrank_pos_iff_of_free
/-- Alternating forms on a line vanish. -/
theorem alt_one_eq_bot : (alternatingForms (U := Point 1)) = ⊥ := by
  rw [eq_bot_iff]
  intro D hD
  rw [Submodule.mem_bot]
  have hAlt : D.IsAlt := hD
  have hDD : ∀ x y : Point 1, D x y = 0 := by
    intro x y
    have hx : x = (x 0) • Pi.single (0 : Fin 1) 1 := by
      funext i
      fin_cases i <;> simp
    have hy : y = (y 0) • Pi.single (0 : Fin 1) 1 := by
      funext i
      fin_cases i <;> simp
    rw [hx, hy, map_smul, map_smul, LinearMap.smul_apply, hAlt.self_eq_zero,
      smul_zero, smul_zero]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact hDD x y
/-- A choice of skew coordinates at e = 1 (both sides are 0-dimensional). -/
noncomputable def C1decode :
    Point (skewDim 1) ≃ₗ[ℂ] ↥(alternatingForms (U := Point 1)) := by
  have hsk : skewDim 1 = 0 := rfl
  have h0 : Module.finrank ℂ (Point (skewDim 1)) = 0 := by
    rw [hsk]
    simp
  have h1 : Module.finrank ℂ ↥(alternatingForms (U := Point 1)) = 0 := by
    rw [alt_one_eq_bot]
    exact finrank_bot ℂ _
  haveI : Module.Free ℂ ↥(alternatingForms (U := Point 1)) :=
    Module.Free.of_divisionRing ℂ ↥(alternatingForms (U := Point 1))
  exact LinearEquiv.ofFinrankEq _ _ (by rw [h0, h1])
noncomputable def C1 : SkewCoordinates 1 where
  decode := C1decode
/-- Whole-space carrier and constant-1 filter. -/
noncomputable def G1 : AffineVariety (skewDim 1 + 1) := AffineVariety.whole
noncomputable def H1 : Poly (skewDim 1) := 1
theorem G1_points : G1.points = Set.univ := by
  ext z
  simp [G1, AffineVariety.whole, AffineVariety.points_ofIdeal]
def v0 : Point 1 := fun _ => 1
theorem hv0 : v0 ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 0)
def z0 : Point (skewDim 1) := default
theorem w0mem : joinPoints z0 v0 ∈ rulingPoints G1 H1 := by
  constructor
  · have h : joinPoints z0 v0 ∈ G1.points := by
      rw [G1_points]
      exact Set.mem_univ _
    exact h
  · show MvPolynomial.aeval (firstPoint (joinPoints z0 v0)) (1 : Poly (skewDim 1)) ≠ 0
    rw [map_one]
    exact one_ne_zero
/-- The unique-pair witness (only its existence is needed). -/
noncomputable def d0 : ProjectivePoint 1 := Projectivization.mk ℂ v0 hv0
noncomputable def p0 : ProjectivePoint (1 + 1) := graphParameter C1 z0 v0 hv0
theorem pairmem : (d0, p0) ∈ liftedParameterPairs C1 G1 H1 := by
  exact ⟨z0, v0, w0mem, hv0, rfl, rfl⟩
noncomputable def x0 : ProjectivePoint (skewDim 1 + 1) :=
  Projectivization.mk ℂ (fun _ => (1 : ℂ)) (by
    intro h
    exact one_ne_zero (congrFun h 0))
theorem trimem : ((d0, p0), x0) ∈ incidenceTriples C1 G1 H1 := by
  have hbase : (d0, p0) ∈ liftedParameterBase C1 G1 H1 := by
    show (d0, p0) ∈ closedPairs (liftedParameterPairs C1 G1 H1)
    show segrePoint d0 p0 ∈ pairClosure (liftedParameterPairs C1 G1 H1)
    show segrePoint d0 p0 ∈
      (ProjectiveVariety.closure {w | ∃ p q, (p, q) ∈ liftedParameterPairs C1 G1 H1 ∧
        segrePoint p q = w}).points
    apply ProjectiveVariety.subset_closure
    exact ⟨d0, p0, pairmem, rfl⟩
  have hcond : incidenceCondition C1 d0 p0 x0 := by
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v0 hv0
    have hgv : graphVector C1 z0 v0 ≠ 0 := graphVector_ne_zero C1 z0 v0 hv0
    obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (graphVector C1 z0 v0) hgv
    have ha0 : (a : ℂ) ≠ 0 := Units.ne_zero a
    have hb0 : (b : ℂ) ≠ 0 := Units.ne_zero b
    have hfirst : firstPoint (graphVector C1 z0 v0) = v0 := by
      ext i
      simp [firstPoint, graphVector, joinPoints]
    have hfp : firstPoint p0.rep = (b : ℂ) • v0 := by
      have e1 : p0.rep = (b : ℂ) • graphVector C1 z0 v0 := by
        show (Projectivization.mk ℂ (graphVector C1 z0 v0) hgv).rep = _
        exact hb.symm
      rw [e1]
      show (b : ℂ) • firstPoint (graphVector C1 z0 v0) = (b : ℂ) • v0
      rw [hfirst]
    have hD0 : (C1.decode z0).val = 0 := by
      have hmem : (C1.decode z0).val ∈ alternatingForms (U := Point 1) :=
        (C1.decode z0).property
      simpa [alt_one_eq_bot] using hmem
    have hgv2 : secondPoint (graphVector C1 z0 v0) =
        pointOfCovector ((C1.decode z0).val v0) := by
      show secondPoint (joinPoints v0 (pointOfCovector ((C1.decode z0).val v0))) = _
      funext i
      exact Fin.addCases_right (m := 1) (n := 1) (motive := fun _ => ℂ)
        (left := v0) (right := pointOfCovector ((C1.decode z0).val v0)) i
    have hsp : secondPoint p0.rep = 0 := by
      have e2 : p0.rep = (b : ℂ) • graphVector C1 z0 v0 := by
        show (Projectivization.mk ℂ (graphVector C1 z0 v0) hgv).rep = _
        exact hb.symm
      rw [e2]
      show (b : ℂ) • secondPoint (graphVector C1 z0 v0) = 0
      rw [hgv2, hD0]
      have hpt0 : pointOfCovector ((0 : LinearMap.BilinForm ℂ (Point 1)) v0) = 0 := by
        funext i
        simp [pointOfCovector]
      rw [hpt0, smul_zero]
    have hy0 : covectorOfPoint (secondPoint p0.rep) = 0 := by
      rw [hsp]
      simp [covectorOfPoint]
    have hDt : C1.decode (Fin.tail x0.rep) = 0 := by
      have hmem : (C1.decode (Fin.tail x0.rep)).val ∈
          alternatingForms (U := Point 1) := (C1.decode _).property
      have h0 : (C1.decode (Fin.tail x0.rep)).val = 0 := by
        simpa [alt_one_eq_bot] using hmem
      exact Subtype.ext h0
    have ht0 : ((b : ℂ) / (a : ℂ)) ≠ 0 := div_ne_zero hb0 ha0
    have hfib : (x0.rep 0, C1.decode (Fin.tail x0.rep)) ∈
        incidenceFiber (d0.rep) ((b : ℂ) / (a : ℂ)) 0 := by
      rw [hDt]
      unfold incidenceFiber
      rw [Submodule.mem_comap]
      have himg : homogeneousEvaluation (d0.rep)
          ((x0.rep 0, (0 : ↥(alternatingForms (U := Point 1))))) =
          ((x0.rep 0), (0 : Module.Dual ℂ (Point 1))) := by
        show (x0.rep 0, alternatingEvaluation (d0.rep)
          (0 : ↥(alternatingForms (U := Point 1)))) = _
        rw [map_zero]
      rw [himg, Submodule.mem_span_singleton]
      refine ⟨(x0.rep 0) / ((b : ℂ) / (a : ℂ)), ?_⟩
      have hcc : ((x0.rep 0) / ((b : ℂ) / (a : ℂ))) •
          (((b : ℂ) / (a : ℂ)), (0 : Module.Dual ℂ (Point 1))) =
          ((x0.rep 0), 0) := by
        refine Prod.ext ?_ ?_
        · show ((x0.rep 0) / _) • ((b : ℂ) / (a : ℂ)) = x0.rep 0
          exact div_mul_cancel₀ _ ht0
        · show ((x0.rep 0) / _) • (0 : Module.Dual ℂ (Point 1)) = 0
          exact smul_zero _
      exact hcc
    have e0 : d0.rep = (a : ℂ) • v0 := by
      show (Projectivization.mk ℂ v0 hv0).rep = _
      exact ha.symm
    refine ⟨(b : ℂ) / (a : ℂ), ?_, ?_, ?_⟩
    · rw [hfp, e0, ← mul_smul, div_mul_cancel₀ _ ha0]
    · rw [hy0]
      rfl
    · rw [hy0]
      exact hfib
  exact ⟨hbase, hcond⟩
/-- Zero weight for the refutation instance. -/
def w0 : Option (Fin (1 + (1 + 1) + (skewDim 1 + 1))) → (Fin 3 →₀ ℕ) := fun _ => 0
theorem hweight0 (d : Option (Fin (1 + (1 + 1) + (skewDim 1 + 1))) →₀ ℕ) :
    Finsupp.weight w0 d = 0 := by
  rw [Finsupp.weight_apply]
  simp [w0]
/-- Every polynomial is homogeneous of degree 0 under the zero weight. -/
theorem hhom0 (p : MvPolynomial (Option (Fin (1 + (1 + 1) + (skewDim 1 + 1)))) ℂ) :
    p.IsWeightedHomogeneous w0 0 := by
  intro d hd
  exact hweight0 d
noncomputable def K1 : Ideal (Poly (1 + (1 + 1) + (skewDim 1 + 1))) :=
  MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives (incidenceTriples C1 G1 H1))
noncomputable def I1 : Ideal
    (MvPolynomial (Option (Fin (1 + (1 + 1) + (skewDim 1 + 1)))) ℂ) :=
  Ideal.comap
    (OAI.PiExponentSiegel.W08.coordinateEval
      (σ := Fin (1 + (1 + 1) + (skewDim 1 + 1))) (k := ℂ)).toRingHom K1
noncomputable def g1 : Fin 1 →
    MvPolynomial (Option (Fin (1 + (1 + 1) + (skewDim 1 + 1)))) ℂ :=
  fun _ => 0
noncomputable def μ1 : MvPolynomial (Option (Fin (1 + (1 + 1) + (skewDim 1 + 1)))) ℂ := 0
theorem hI1 : I1.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ w0) := by
  have hspan : Ideal.span (↑I1 : Set _) = I1 := by
    apply le_antisymm
    · exact Ideal.span_le.mpr (fun x hx => hx)
    · intro x hx
      exact Submodule.subset_span hx
  rw [← hspan]
  apply Ideal.homogeneous_span
  intro x hx
  exact ⟨0, hhom0 x⟩
theorem hevalSurj : Function.Surjective
    (OAI.PiExponentSiegel.W08.coordinateEval
      (σ := Fin (1 + (1 + 1) + (skewDim 1 + 1))) (k := ℂ)).toRingHom := by
  intro q
  exact ⟨OAI.PiExponentSiegel.W08.coordinateInclude q,
    OAI.PiExponentSiegel.W08.coordinateEval_include q⟩
theorem hImg1 : OAI.PiExponentSiegel.W08.coordinateImageIdeal
    (Ideal.span (Set.range g1) ⊔ (Ideal.span ({μ1} : Set _) ⊔ I1)) = K1 := by
  have eJ : Ideal.span (Set.range g1) ⊔ (Ideal.span ({μ1} : Set _) ⊔ I1) = I1 := by
    have e1 : Ideal.span (Set.range g1) = ⊥ := by
      have hr : Set.range g1 = {(0 : MvPolynomial (Option (Fin (1 + (1 + 1) + (skewDim 1 + 1)))) ℂ)} := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          exact Set.mem_singleton_iff.mpr rfl
        · intro hy
          refine ⟨0, ?_⟩
          show (0 : MvPolynomial (Option (Fin (1 + (1 + 1) + (skewDim 1 + 1)))) ℂ) = y
          exact (Set.mem_singleton_iff.mp hy).symm
      rw [hr]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    have e2 : Ideal.span ({μ1} : Set _) = ⊥ := by
      show Ideal.span ({(0 : MvPolynomial (Option (Fin (1 + (1 + 1) + (skewDim 1 + 1)))) ℂ)} : Set _) = ⊥
      exact Ideal.span_singleton_eq_bot.mpr rfl
    rw [e1, e2]
    simp
  rw [eJ]
  show Ideal.map
    (OAI.PiExponentSiegel.W08.coordinateEval
      (σ := Fin (1 + (1 + 1) + (skewDim 1 + 1))) (k := ℂ)).toRingHom I1 = K1
  exact Ideal.map_comap_of_surjective _ hevalSurj K1
theorem hRev1 : ∃ N : ℕ, ∀ s t u : ℕ, 1 * N + 1 ≤ s →
    Module.finrank ℂ (HilbertMulti.sectionSpace
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks 1 (1 + 1) (skewDim 1 + 1)))
      (OAI.PiExponentSiegel.W08.coordinateImageIdeal
        (Ideal.span (Set.range g1) ⊔ (Ideal.span ({μ1} : Set _) ⊔ I1)))
      (HilbertMulti.tripleDegree s t u)) =
    tripleHilbert (incidenceTriples C1 G1 H1) s t u := by
  refine ⟨0, fun s t u _ => ?_⟩
  rw [hImg1]
  have hspace : HilbertMulti.sectionSpace
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks 1 (1 + 1) (skewDim 1 + 1))) K1
      (HilbertMulti.tripleDegree s t u) =
      tripleSection (incidenceTriples C1 G1 H1) s t u := by
    rw [HilbertMulti.sectionSpace, HilbertMulti.tripleBlockPiece]
    rfl
  rw [hspace]
  rfl
/-- Block indices for the evaluating monomial. -/
def j1 : Fin (1 + (1 + 1) + (skewDim 1 + 1)) :=
  Fin.castAdd (skewDim 1 + 1) (Fin.castAdd (1 + 1) (0 : Fin 1))
def j2 : Fin (1 + (1 + 1) + (skewDim 1 + 1)) :=
  Fin.castAdd (skewDim 1 + 1) (Fin.natAdd 1 (0 : Fin (1 + 1)))
def j3 : Fin (1 + (1 + 1) + (skewDim 1 + 1)) :=
  Fin.natAdd (1 + (1 + 1)) (0 : Fin (skewDim 1 + 1))
noncomputable def avec (s t u : ℕ) : Fin (1 + (1 + 1) + (skewDim 1 + 1)) →₀ ℕ :=
  Finsupp.single j1 s + Finsupp.single j2 t + Finsupp.single j3 u
theorem hne12 : j1 ≠ j2 := by decide
theorem hne13 : j1 ≠ j3 := by decide
theorem hne23 : j2 ≠ j3 := by decide
noncomputable def w1 : Point (skewDim 1 + 1) := fun _ => 1
noncomputable def wrep : Point (1 + (1 + 1) + (skewDim 1 + 1)) :=
  joinPoints (joinPoints v0 (graphVector C1 z0 v0)) w1
theorem wrepmem : wrep ∈ tripleRepresentatives (incidenceTriples C1 G1 H1) := by
  have hgv : graphVector C1 z0 v0 ≠ 0 := graphVector_ne_zero C1 z0 v0 hv0
  have hw1 : (fun _ => (1 : ℂ)) ≠ (0 : Point (skewDim 1 + 1)) := by
    intro h
    exact one_ne_zero (congrFun h 0)
  refine ⟨v0, graphVector C1 z0 v0, (fun _ => (1 : ℂ)), hv0, hgv, hw1, trimem, rfl⟩
theorem hc1 : wrep j1 = 1 := by
  simp only [wrep, j1, joinPoints, Fin.addCases_left, v0]
theorem hc2 : wrep j2 = 1 := by
  have e1 := Fin.addCases_left (m := 1 + (1 + 1)) (n := skewDim 1 + 1)
    (motive := fun _ => ℂ) (left := Fin.addCases v0 (graphVector C1 z0 v0))
    (right := w1) (Fin.natAdd 1 (0 : Fin (1 + 1)))
  have e2 := Fin.addCases_right (m := 1) (n := 1 + 1) (motive := fun _ => ℂ)
    (left := v0) (right := graphVector C1 z0 v0) (0 : Fin (1 + 1))
  have e3 := Fin.addCases_left (m := 1) (n := 1) (motive := fun _ => ℂ)
    (left := v0) (right := pointOfCovector ((C1.decode z0).val v0)) (0 : Fin 1)
  unfold wrep j2 joinPoints
  rw [e1, e2]
  exact e3
theorem hc3 : wrep j3 = 1 := by
  simp only [wrep, j3, joinPoints, Fin.addCases_right, w1]
theorem hdir (s t u : ℕ) :
    (∑ i : Fin 1, avec s t u (Fin.castAdd (skewDim 1 + 1) (Fin.castAdd (1 + 1) i))) = s := by
  rw [Fin.sum_univ_one]
  show avec s t u j1 = s
  have h1 : Finsupp.single j2 t j1 = 0 := Finsupp.single_eq_of_ne hne12
  have h2 : Finsupp.single j3 u j1 = 0 := Finsupp.single_eq_of_ne hne13
  simp [avec, h1, h2]
theorem hpar (s t u : ℕ) :
    (∑ i : Fin (1 + 1), avec s t u (Fin.castAdd (skewDim 1 + 1) (Fin.natAdd 1 i))) = t := by
  have huniv : (Finset.univ : Finset (Fin (1 + 1))) = {0, 1} := by decide
  have h01 : (0 : Fin (1 + 1)) ∉ ({1} : Finset (Fin (1 + 1))) := by decide
  rw [huniv, Finset.sum_insert h01, Finset.sum_singleton]
  have e0 : avec s t u (Fin.castAdd (skewDim 1 + 1) (Fin.natAdd 1 (0 : Fin (1 + 1)))) = t := by
    show avec s t u j2 = t
    have h1 : Finsupp.single j1 s j2 = 0 := Finsupp.single_eq_of_ne hne12.symm
    have h3 : Finsupp.single j3 u j2 = 0 := Finsupp.single_eq_of_ne hne23
    simp [avec, h1, h3]
  have e1 : avec s t u (Fin.castAdd (skewDim 1 + 1) (Fin.natAdd 1 (1 : Fin (1 + 1)))) = 0 := by
    have d1 : Finsupp.single j1 s
        (Fin.castAdd (skewDim 1 + 1) (Fin.natAdd 1 (1 : Fin (1 + 1)))) = 0 :=
      Finsupp.single_eq_of_ne (by decide)
    have d2 : Finsupp.single j2 t
        (Fin.castAdd (skewDim 1 + 1) (Fin.natAdd 1 (1 : Fin (1 + 1)))) = 0 :=
      Finsupp.single_eq_of_ne (by decide)
    have d3 : Finsupp.single j3 u
        (Fin.castAdd (skewDim 1 + 1) (Fin.natAdd 1 (1 : Fin (1 + 1)))) = 0 :=
      Finsupp.single_eq_of_ne (by decide)
    simp only [avec, Finsupp.add_apply, d1, d2, d3, add_zero]
  rw [e0, e1, add_zero]
theorem hpt (s t u : ℕ) :
    (∑ i : Fin (skewDim 1 + 1), avec s t u (Fin.natAdd (1 + (1 + 1)) i)) = u := by
  show (∑ i : Fin 1, avec s t u (Fin.natAdd (1 + (1 + 1)) i)) = u
  rw [Fin.sum_univ_one]
  show avec s t u j3 = u
  have h1 : Finsupp.single j1 s j3 = 0 := Finsupp.single_eq_of_ne hne13.symm
  have h2 : Finsupp.single j2 t j3 = 0 := Finsupp.single_eq_of_ne (Ne.symm hne23)
  simp [avec, h1, h2]
theorem hLHS0 (s t u : ℕ) (hs : 1 ≤ s) :
    Module.finrank ℂ (HilbertMulti.sectionSpace w0
      (Ideal.span (Set.range g1) ⊔ (Ideal.span ({μ1} : Set _) ⊔ I1))
      (HilbertMulti.tripleDegree s t u)) = 0 := by
  have hs0 : (HilbertMulti.tripleDegree s t u) 0 = s := by
    simp [HilbertMulti.tripleDegree]
  have hdeg : HilbertMulti.tripleDegree s t u ≠ 0 := by
    intro hcon
    rw [hcon] at hs0
    simp at hs0
    omega
  have hpiece : MvPolynomial.weightedHomogeneousSubmodule ℂ w0
      (HilbertMulti.tripleDegree s t u) = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    rw [Submodule.mem_bot]
    by_contra hne
    obtain ⟨e, hcoeff⟩ := MvPolynomial.exists_coeff_ne_zero hne
    have hwt : Finsupp.weight w0 e = HilbertMulti.tripleDegree s t u := hp hcoeff
    rw [hweight0] at hwt
    exact hdeg hwt.symm
  rw [HilbertMulti.sectionSpace, hpiece, Submodule.map_bot]
  exact finrank_bot ℂ _
theorem hRHS1 (s t u : ℕ) :
    1 ≤ tripleHilbert (incidenceTriples C1 G1 H1) s t u := by
  have hmono_mem : (Ideal.Quotient.mkₐ ℂ K1)
      (MvPolynomial.monomial (avec s t u) 1) ∈
      tripleSection (incidenceTriples C1 G1 H1) s t u := by
    show (Ideal.Quotient.mkₐ ℂ K1) (MvPolynomial.monomial (avec s t u) (1 : ℂ)) ∈
      Submodule.map (Ideal.Quotient.mkₐ ℂ K1).toLinearMap
        (MvPolynomial.restrictSupport ℂ {d : Fin (1 + (1 + 1) + (skewDim 1 + 1)) →₀ ℕ |
          (∑ i : Fin 1, d (Fin.castAdd (skewDim 1 + 1) (Fin.castAdd (1 + 1) i))) = s ∧
          (∑ i : Fin (1 + 1), d (Fin.castAdd (skewDim 1 + 1) (Fin.natAdd 1 i))) = t ∧
          (∑ i : Fin (skewDim 1 + 1), d (Fin.natAdd (1 + (1 + 1)) i)) = u})
    apply Submodule.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro d hd
    have hda : d = avec s t u :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
    subst hda
    exact ⟨hdir s t u, hpar s t u, hpt s t u⟩
  have hne : (Ideal.Quotient.mkₐ ℂ K1)
      (MvPolynomial.monomial (avec s t u) 1) ≠ 0 := by
    intro hcon
    have hmemK : MvPolynomial.monomial (avec s t u) 1 ∈ K1 := by
      have h1 : Ideal.Quotient.mk K1
          (MvPolynomial.monomial (avec s t u) 1) = 0 := by
        have hbridge := congrFun (Ideal.Quotient.mkₐ_eq_mk (R₁ := ℂ) K1)
          (MvPolynomial.monomial (avec s t u) 1)
        rw [← hbridge]
        exact hcon
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    have hmemK' : MvPolynomial.monomial (avec s t u) 1 ∈
        MvPolynomial.vanishingIdeal ℂ
          (tripleRepresentatives (incidenceTriples C1 G1 H1)) := hmemK
    have hvan := MvPolynomial.mem_vanishingIdeal_iff.mp hmemK' wrep wrepmem
    have hne2 : MvPolynomial.aeval wrep
        (MvPolynomial.monomial (avec s t u) (1 : ℂ)) ≠ 0 := by
      rw [MvPolynomial.aeval_monomial, map_one, one_mul]
      show Finsupp.prod (avec s t u) (fun i k => wrep i ^ k) ≠ 0
      have hsup3 : ∀ i ∈ (avec s t u).support, wrep i ≠ 0 := by
        intro i hi
        have hi3 : i = j1 ∨ i = j2 ∨ i = j3 := by
          have hsub : i ∈ ({j1, j2, j3} : Finset _) := by
            have hss : (avec s t u).support ⊆ {j1, j2, j3} := by
              intro j hj
              have hi2 : (Finsupp.single j1 s + Finsupp.single j2 t +
                  Finsupp.single j3 u) j ≠ 0 := by
                have hmem := (Finsupp.mem_support_iff).mp hj
                simpa [avec] using hmem
              have hdisj : Finsupp.single j1 s j ≠ 0 ∨
                  Finsupp.single j2 t j ≠ 0 ∨ Finsupp.single j3 u j ≠ 0 := by
                by_contra hcon
                push_neg at hcon
                exact hi2 (by simp [hcon.1, hcon.2.1, hcon.2.2])
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rcases hdisj with h | h | h
              · left
                by_contra hne
                exact h (Finsupp.single_eq_of_ne hne)
              · right
                left
                by_contra hne
                exact h (Finsupp.single_eq_of_ne hne)
              · right
                right
                by_contra hne
                exact h (Finsupp.single_eq_of_ne hne)
            exact hss hi
          simpa using hsub
        rcases hi3 with rfl | rfl | rfl
        · rw [hc1]
          exact one_ne_zero
        · rw [hc2]
          exact one_ne_zero
        · rw [hc3]
          exact one_ne_zero
      have hprod : Finsupp.prod (avec s t u) (fun i k => wrep i ^ k) =
          ∏ i ∈ (avec s t u).support, wrep i ^ ((avec s t u) i) := rfl
      rw [hprod, Finset.prod_ne_zero_iff]
      intro i hi
      exact pow_ne_zero _ (hsup3 i hi)
    exact hne2 hvan
  have hNT : Nontrivial ↥(tripleSection (incidenceTriples C1 G1 H1) s t u) := by
    refine ⟨⟨_, hmono_mem⟩,
      ⟨0, (tripleSection (incidenceTriples C1 G1 H1) s t u).zero_mem⟩, ?_⟩
    intro hcon
    exact hne (congrArg Subtype.val hcon)
  haveI : Module.Free ℂ ↥(tripleSection (incidenceTriples C1 G1 H1) s t u) :=
    Module.Free.of_divisionRing ℂ ↥(tripleSection (incidenceTriples C1 G1 H1) s t u)
  have hpos := (Module.finrank_pos_iff_of_free ℂ _).mpr hNT
  show (1 : ℕ) ≤ Module.finrank ℂ ↥(tripleSection (incidenceTriples C1 G1 H1) s t u)
  omega
theorem dehomogenize_vanishG1 : ∀ k : Fin 1,
    OAI.PiExponentSiegel.W08.coordinateEval (g1 k) ∈
      MvPolynomial.vanishingIdeal ℂ
        (tripleRepresentatives (incidenceTriples C1 G1 H1)) := by
  intro k
  have hz : g1 k = 0 := rfl
  rw [hz, map_zero]
  exact Ideal.zero_mem _

theorem dehomogenize_vanishI1 :
    OAI.PiExponentSiegel.W08.coordinateImageIdeal I1 ≤
      MvPolynomial.vanishingIdeal ℂ
        (tripleRepresentatives (incidenceTriples C1 G1 H1)) := by
  have hIimg : OAI.PiExponentSiegel.W08.coordinateImageIdeal I1 = K1 := by
    show Ideal.map
      (OAI.PiExponentSiegel.W08.coordinateEval
        (σ := Fin (1 + (1 + 1) + (skewDim 1 + 1))) (k := ℂ)).toRingHom I1 = K1
    exact Ideal.map_comap_of_surjective _ hevalSurj K1
  rw [hIimg]
  exact le_rfl

/-- All hypotheses of the frozen `dehomogenize_rank` hold for the instance
(`e = 1`, zero weight, `g = μ = 0`, `I = comap eval K`). -/
theorem dehomogenize_instance_hyps :
    I1.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ w0) ∧
    (∀ k : Fin 1, (g1 k).IsWeightedHomogeneous w0
      (HilbertMulti.tripleDegree 1 0 1)) ∧
    μ1.IsWeightedHomogeneous w0 (HilbertMulti.tripleDegree 1 0 1) ∧
    (∀ k : Fin 1, OAI.PiExponentSiegel.W08.coordinateEval (g1 k) ∈
      MvPolynomial.vanishingIdeal ℂ
        (tripleRepresentatives (incidenceTriples C1 G1 H1))) ∧
    (OAI.PiExponentSiegel.W08.coordinateImageIdeal I1 ≤
      MvPolynomial.vanishingIdeal ℂ
        (tripleRepresentatives (incidenceTriples C1 G1 H1))) ∧
    (∃ N : ℕ, ∀ s t u : ℕ, 1 * N + 1 ≤ s →
      Module.finrank ℂ (HilbertMulti.sectionSpace
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks 1 (1 + 1) (skewDim 1 + 1)))
        (OAI.PiExponentSiegel.W08.coordinateImageIdeal
          (Ideal.span (Set.range g1) ⊔ (Ideal.span ({μ1} : Set _) ⊔ I1)))
        (HilbertMulti.tripleDegree s t u)) =
      tripleHilbert (incidenceTriples C1 G1 H1) s t u) :=
  ⟨hI1, fun k => MvPolynomial.isWeightedHomogeneous_zero ℂ w0 _,
    MvPolynomial.isWeightedHomogeneous_zero ℂ w0 _,
    dehomogenize_vanishG1, dehomogenize_vanishI1, hRev1⟩

/-- ...but the conclusion is impossible for the instance (LHS rank is 0,
RHS rank is ≥ 1). Together with `dehomogenize_instance_hyps` this refutes
the frozen `dehomogenize_rank` as stated. Proved from the allowed axioms only. -/
theorem dehomogenize_rank_conclusion_false :
    ¬ ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s → N ≤ t → N ≤ u →
      Module.finrank ℂ (HilbertMulti.sectionSpace w0
        (Ideal.span (Set.range g1) ⊔ (Ideal.span ({μ1} : Set _) ⊔ I1))
        (HilbertMulti.tripleDegree s t u)) =
      tripleHilbert (incidenceTriples C1 G1 H1) s t u := by
  rintro ⟨N, hN⟩
  have hconc := hN (N + 1) (N + 1) (N + 1) (by omega) (by omega) (by omega)
  rw [hLHS0 _ _ _ (by omega : 1 ≤ N + 1)] at hconc
  have hge := hRHS1 (N + 1) (N + 1) (N + 1)
  omega
end MBPart2Aux
end DistinctDistances.TrackB
