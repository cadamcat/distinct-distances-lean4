import DistinctDistances.TrackB.Compactification
import DistinctDistances.TrackB.IncidenceHilbert
import DistinctDistances.TrackB.MBHilbAux

/-!
The specialized numerical substitute for intersection classes: actual multihomogeneous
restriction ranks on the two/three projective factors in the evaluation incidence.
Varieties, vanishing ideals and degree remain those of Foundations. Compatibility with
those degrees is stated separately in Degree.lean, never a field of these definitions.
The eventual-polynomial existence theorems are new multigraded foundations, not OAI reuse.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false
noncomputable section
open scoped BigOperators

def pairRepresentatives {n m : ℕ} (T : Set (ProjectivePoint n × ProjectivePoint m)) :
    Set (Point (n + m)) :=
  {w | ∃ x : Point n, ∃ y : Point m, ∃ hx : x ≠ 0, ∃ hy : y ≠ 0,
    (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈ T ∧ w = joinPoints x y}

def pairSection {n m : ℕ} (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) :
    Submodule ℂ (Poly (n + m) ⧸ MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T)) :=
  (MvPolynomial.restrictSupport ℂ {d : Fin (n + m) →₀ ℕ |
    (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t}).map
    (Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T))).toLinearMap

theorem pairSection_finite {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) :
    Module.Finite ℂ (pairSection T s t) := by
  classical
  let S := {d : Fin (n + m) →₀ ℕ |
    (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t}
  have hS : MvPolynomial.restrictSupport ℂ S ≤
      MvPolynomial.restrictDegree (Fin (n + m)) ℂ (s + t) := by
    apply MvPolynomial.restrictSupport_mono
    intro d hd i
    have htotal : (∑ j : Fin (n + m), d j) = s + t := by
      rw [Fin.sum_univ_add, hd.1, hd.2]
    calc
      d i ≤ ∑ j : Fin (n + m), d j :=
        Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      _ = s + t := htotal
  haveI : Module.Finite ℂ (MvPolynomial.restrictSupport ℂ S) :=
    Module.Finite.of_injective (Submodule.inclusion hS) (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : MvPolynomial.restrictDegree (Fin (n + m)) ℂ (s + t) =>
        (z : MvPolynomial (Fin (n + m)) ℂ) ) hxy)
  change Module.Finite ℂ ((MvPolynomial.restrictSupport ℂ S).map
    (Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T))).toLinearMap)
  infer_instance

noncomputable instance pairSectionFinite {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) :
    Module.Finite ℂ (pairSection T s t) := pairSection_finite T s t

def pairHilbert {n m : ℕ} (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) : ℕ :=
  Module.finrank ℂ (pairSection T s t)


theorem joinPoints_smul_hilb {n m : ℕ} (c : ℂ) (x : Point n) (y : Point m) :
    joinPoints (c • x) (c • y) = c • joinPoints x y := by
  ext i
  cases i using Fin.addCases with
  | left i => simp [joinPoints, Pi.smul_apply, smul_eq_mul]
  | right i => simp [joinPoints, Pi.smul_apply, smul_eq_mul]

theorem pairRepresentatives_joint_smul {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m))
    {w : Point (n + m)} (hw : w ∈ pairRepresentatives T)
    {c : ℂ} (hc : c ≠ 0) : c • w ∈ pairRepresentatives T := by
  obtain ⟨x, y, hx, hy, hmem, rfl⟩ := hw
  refine ⟨c • x, c • y, smul_ne_zero hc hx, smul_ne_zero hc hy, ?_,
    (joinPoints_smul_hilb c x y).symm⟩
  have hxproj : Projectivization.mk ℂ (c • x) (smul_ne_zero hc hx) =
      Projectivization.mk ℂ x hx :=
    (Projectivization.mk_eq_mk_iff' ℂ (c • x) x _ _).2 ⟨c, rfl⟩
  have hyproj : Projectivization.mk ℂ (c • y) (smul_ne_zero hc hy) =
      Projectivization.mk ℂ y hy :=
    (Projectivization.mk_eq_mk_iff' ℂ (c • y) y _ _).2 ⟨c, rfl⟩
  rw [hxproj, hyproj]
  exact hmem

theorem pairRepresentatives_left_smul {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m))
    {w : Point (n + m)} (hw : w ∈ pairRepresentatives T)
    {c : ℂ} (hc : c ≠ 0) :
    joinPoints (c • (firstPoint w)) (secondPoint w) ∈ pairRepresentatives T := by
  obtain ⟨x, y, hx, hy, hmem, rfl⟩ := hw
  show joinPoints (c • firstPoint (joinPoints x y)) (secondPoint (joinPoints x y)) ∈ _
  have hfirst : firstPoint (joinPoints x y : Point (n + m)) = x := by
    ext i
    simp [firstPoint, joinPoints]
  have hsecond : secondPoint (joinPoints x y : Point (n + m)) = y := by
    ext i
    simp [secondPoint, joinPoints]
  rw [hfirst, hsecond]
  refine ⟨c • x, y, smul_ne_zero hc hx, hy, ?_, rfl⟩
  have hxproj : Projectivization.mk ℂ (c • x) (smul_ne_zero hc hx) =
      Projectivization.mk ℂ x hx :=
    (Projectivization.mk_eq_mk_iff' ℂ (c • x) x _ _).2 ⟨c, rfl⟩
  rw [hxproj]
  exact hmem

theorem pairRepresentatives_right_smul {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m))
    {w : Point (n + m)} (hw : w ∈ pairRepresentatives T)
    {c : ℂ} (hc : c ≠ 0) :
    joinPoints (firstPoint w) (c • (secondPoint w)) ∈ pairRepresentatives T := by
  obtain ⟨x, y, hx, hy, hmem, rfl⟩ := hw
  show joinPoints (firstPoint (joinPoints x y)) (c • secondPoint (joinPoints x y)) ∈ _
  have hfirst : firstPoint (joinPoints x y : Point (n + m)) = x := by
    ext i
    simp [firstPoint, joinPoints]
  have hsecond : secondPoint (joinPoints x y : Point (n + m)) = y := by
    ext i
    simp [secondPoint, joinPoints]
  rw [hfirst, hsecond]
  refine ⟨x, c • y, hx, smul_ne_zero hc hy, ?_, rfl⟩
  have hyproj : Projectivization.mk ℂ (c • y) (smul_ne_zero hc hy) =
      Projectivization.mk ℂ y hy :=
    (Projectivization.mk_eq_mk_iff' ℂ (c • y) y _ _).2 ⟨c, rfl⟩
  rw [hyproj]
  exact hmem

/-- Rank identity for the actual bigraded section: `pairHilbert` plus the
explicit kernel rank equals the ambient piece rank. -/
theorem pairSection_finrank_eq {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) :
    pairHilbert T s t +
      Module.finrank ℂ (sectionKernel
        (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T))
        {d : Fin (n + m) →₀ ℕ |
          (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
          (∑ i : Fin m, d (Fin.natAdd n i)) = t}) =
      Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
        {d : Fin (n + m) →₀ ℕ |
          (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
          (∑ i : Fin m, d (Fin.natAdd n i)) = t}) := by
  haveI := finite_pairExponents (n := n) (m := m) (s := s) (t := t)
  exact section_finrank_eq _ _

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The representative set is invariant under the two projective scaling factors. -/
theorem pairRepresentatives_blockHomogeneous {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) :
    (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ
        (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))) := by
  classical
  apply HilbertMulti.vanishingIdeal_blockHomogeneous
  intro w hw c hc
  obtain ⟨x, y, hx, hy, hmem, rfl⟩ := hw
  refine ⟨c 0 • x, c 1 • y, smul_ne_zero (hc 0) hx, smul_ne_zero (hc 1) hy, ?_, ?_⟩
  · have hxp : Projectivization.mk ℂ (c 0 • x) (smul_ne_zero (hc 0) hx) =
        Projectivization.mk ℂ x hx :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨c 0, rfl⟩
    have hyp : Projectivization.mk ℂ (c 1 • y) (smul_ne_zero (hc 1) hy) =
        Projectivization.mk ℂ y hy :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨c 1, rfl⟩
    rw [hxp, hyp]
    exact hmem
  · ext i
    cases i using Fin.addCases <;> simp [HilbertMulti.pairBlocks, joinPoints, smul_eq_mul]

/-- New B13.3 support, specialized to the actual ruling parameter base. -/
theorem parameterBaseHilbert_eventually_polynomial {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    ∃ P : BaseHilbertPolynomial, ∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P =
        (pairHilbert (liftedParameterBase C Γ H) s t : ℚ) := by
  classical
  let T := liftedParameterBase C Γ H
  let I := MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T)
  obtain ⟨P, N, hP⟩ := HilbertMulti.exists_polynomial (HilbertMulti.pairBlocks e (e + e)) I
    (pairRepresentatives_blockHomogeneous T)
  refine ⟨P, N, ?_⟩
  intro s t hs ht
  let d := HilbertMulti.pairDegree s t
  have hd : ∀ j : Fin 2, N ≤ d j := by
    intro j
    fin_cases j
    · simpa [d, HilbertMulti.pairDegree] using hs
    · simpa [d, HilbertMulti.pairDegree] using ht
  have h := hP d hd
  have hspace : HilbertMulti.sectionSpace
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks e (e + e))) I d =
      pairSection T s t := by
    rw [HilbertMulti.sectionSpace, HilbertMulti.pairBlockPiece]
    rfl
  have hev : (fun j : Fin 2 => (d j : ℚ)) =
      Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ)) := by
    ext j
    fin_cases j <;> rfl
  rw [hev, hspace] at h
  exact h

def tripleRepresentatives {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) :
    Set (Point (n + m + o)) :=
  {w | ∃ x : Point n, ∃ y : Point m, ∃ z : Point o,
    ∃ hx : x ≠ 0, ∃ hy : y ≠ 0, ∃ hz : z ≠ 0,
      ((Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy),
        Projectivization.mk ℂ z hz) ∈ T ∧ w = joinPoints (joinPoints x y) z}

def tripleSection {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) (s t u : ℕ) :
    Submodule ℂ (Poly (n + m + o) ⧸ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T)) :=
  (MvPolynomial.restrictSupport ℂ {d : Fin (n + m + o) →₀ ℕ |
    (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
    (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
    (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u}).map
    (Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))).toLinearMap

theorem tripleSection_finite {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) (s t u : ℕ) :
    Module.Finite ℂ (tripleSection T s t u) := by
  classical
  let S := {d : Fin (n + m + o) →₀ ℕ |
    (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
    (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
    (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u}
  have hS : MvPolynomial.restrictSupport ℂ S ≤
      MvPolynomial.restrictDegree (Fin (n + m + o)) ℂ (s + t + u) := by
    apply MvPolynomial.restrictSupport_mono
    intro d hd i
    have htotal : (∑ j : Fin (n + m + o), d j) = s + t + u := by
      rw [Fin.sum_univ_add, Fin.sum_univ_add, hd.1, hd.2.1, hd.2.2]
    calc
      d i ≤ ∑ j : Fin (n + m + o), d j :=
        Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      _ = s + t + u := htotal
  haveI : Module.Finite ℂ (MvPolynomial.restrictSupport ℂ S) :=
    Module.Finite.of_injective (Submodule.inclusion hS) (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : MvPolynomial.restrictDegree (Fin (n + m + o)) ℂ (s + t + u) =>
        (z : MvPolynomial (Fin (n + m + o)) ℂ)) hxy)
  change Module.Finite ℂ ((MvPolynomial.restrictSupport ℂ S).map
    (Ideal.Quotient.mkₐ ℂ
      (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))).toLinearMap)
  infer_instance

noncomputable instance tripleSectionFinite {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) (s t u : ℕ) :
    Module.Finite ℂ (tripleSection T s t u) := tripleSection_finite T s t u

def tripleHilbert {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) (s t u : ℕ) : ℕ :=
  Module.finrank ℂ (tripleSection T s t u)

theorem tripleRepresentatives_joint_smul {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    {w : Point (n + m + o)} (hw : w ∈ tripleRepresentatives T)
    {c : ℂ} (hc : c ≠ 0) : c • w ∈ tripleRepresentatives T := by
  obtain ⟨x, y, z, hx, hy, hz, hmem, rfl⟩ := hw
  refine ⟨c • x, c • y, c • z, smul_ne_zero hc hx, smul_ne_zero hc hy,
    smul_ne_zero hc hz, ?_, ?_⟩
  · have hxproj : Projectivization.mk ℂ (c • x) (smul_ne_zero hc hx) =
        Projectivization.mk ℂ x hx :=
      (Projectivization.mk_eq_mk_iff' ℂ (c • x) x _ _).2 ⟨c, rfl⟩
    have hyproj : Projectivization.mk ℂ (c • y) (smul_ne_zero hc hy) =
        Projectivization.mk ℂ y hy :=
      (Projectivization.mk_eq_mk_iff' ℂ (c • y) y _ _).2 ⟨c, rfl⟩
    have hzproj : Projectivization.mk ℂ (c • z) (smul_ne_zero hc hz) =
        Projectivization.mk ℂ z hz :=
      (Projectivization.mk_eq_mk_iff' ℂ (c • z) z _ _).2 ⟨c, rfl⟩
    rw [hxproj, hyproj, hzproj]
    exact hmem
  · rw [joinPoints_smul_hilb, joinPoints_smul_hilb]

/-- Rank identity for the actual trigraded section. -/
theorem tripleSection_finrank_eq {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    (s t u : ℕ) :
    tripleHilbert T s t u +
      Module.finrank ℂ (sectionKernel
        (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
        {d : Fin (n + m + o) →₀ ℕ |
          (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
          (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
          (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u}) =
      Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
        {d : Fin (n + m + o) →₀ ℕ |
          (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
          (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
          (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u}) := by
  haveI := finite_tripleExponents (n := n) (m := m) (o := o) (s := s) (t := t) (u := u)
  exact section_finrank_eq _ _
/-- Independent scaling in all three factors preserves the representative set. -/
theorem tripleRepresentatives_blockHomogeneous {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) :
    (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ
        (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks n m o))) := by
  classical
  apply HilbertMulti.vanishingIdeal_blockHomogeneous
  intro w hw c hc
  obtain ⟨x, y, z, hx, hy, hz, hmem, rfl⟩ := hw
  refine ⟨c 0 • x, c 1 • y, c 2 • z,
    smul_ne_zero (hc 0) hx, smul_ne_zero (hc 1) hy, smul_ne_zero (hc 2) hz, ?_, ?_⟩
  · have hxp : Projectivization.mk ℂ (c 0 • x) (smul_ne_zero (hc 0) hx) =
        Projectivization.mk ℂ x hx :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨c 0, rfl⟩
    have hyp : Projectivization.mk ℂ (c 1 • y) (smul_ne_zero (hc 1) hy) =
        Projectivization.mk ℂ y hy :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨c 1, rfl⟩
    have hzp : Projectivization.mk ℂ (c 2 • z) (smul_ne_zero (hc 2) hz) =
        Projectivization.mk ℂ z hz :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨c 2, rfl⟩
    rw [hxp, hyp, hzp]
    exact hmem
  · ext i
    cases i using Fin.addCases with
    | left i => cases i using Fin.addCases <;>
        simp [HilbertMulti.tripleBlocks, joinPoints, smul_eq_mul]
    | right i => simp [HilbertMulti.tripleBlocks, joinPoints, smul_eq_mul]

/-- New B13.3 support, specialized to this compactified incidence on its singular base. -/
theorem compactIncidenceHilbert_eventually_polynomial {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) :
    ∃ P : IncidenceHilbertPolynomial, ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s → N ≤ t → N ≤ u →
      MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ)))) P =
        (tripleHilbert (incidenceTriples C Γ H) s t u : ℚ) := by
  classical
  let T := incidenceTriples C Γ H
  let I := MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T)
  obtain ⟨P, N, hP⟩ := HilbertMulti.exists_polynomial
    (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1)) I
    (tripleRepresentatives_blockHomogeneous T)
  refine ⟨P, N, ?_⟩
  intro s t u hs ht hu
  let d := HilbertMulti.tripleDegree s t u
  have hd : ∀ j : Fin 3, N ≤ d j := by
    intro j
    fin_cases j
    · simpa [d, HilbertMulti.tripleDegree] using hs
    · simpa [d, HilbertMulti.tripleDegree] using ht
    · simpa [d, HilbertMulti.tripleDegree] using hu
  have h := hP d hd
  have hspace : HilbertMulti.sectionSpace
      (HilbertMulti.blockWeight (HilbertMulti.tripleBlocks e (e + e) (skewDim e + 1))) I d =
      tripleSection T s t u := by
    rw [HilbertMulti.sectionSpace, HilbertMulti.tripleBlockPiece]
    rfl
  have hev : (fun j : Fin 3 => (d j : ℚ)) =
      Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ))) := by
    ext j
    fin_cases j <;> rfl
  rw [hev, hspace] at h
  exact h

def parameterBaseHilbert {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) : BaseHilbertPolynomial :=
  (parameterBaseHilbert_eventually_polynomial C Γ H).choose

def compactIncidenceHilbert {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) : IncidenceHilbertPolynomial :=
  (compactIncidenceHilbert_eventually_polynomial C Γ H).choose

def mixedBaseDegree {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) (h j i : ℕ) : ℚ :=
  if i ≤ h then mixedHilbertCoefficient (parameterBaseHilbert C Γ H) (h - i) (i + j) else 0

def pointIncidenceIntegral {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e)) (h j : ℕ) : ℚ :=
  pointParameterCoefficient (compactIncidenceHilbert C Γ H) (flatDim e + h) j

end
end DistinctDistances.TrackB
