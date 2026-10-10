import DistinctDistances.Defs
import DistinctDistances.Foundations

/-!
# Track D conventions (`secants.tex`, `profiles.tex`)

Every track D statement is **finitary**. The paper's asymptotic phrases are encoded as follows:

* "`o(N^2)` along the contradiction sequence" becomes
  `∀ ε > 0, ∃ η > 0, ∃ N₀, ∀ P, N₀ ≤ |P| → M ≤ η A → … → count ≤ ε N^2`.
  The thresholds `η, N₀` are chosen before the configuration, so every constant's dependencies
  are visible in the quantifier prefix; "uniform over pieces / assignments" means that the
  conclusion is inside `∀ piece` after the thresholds.
* "`exp(±o(s))`" becomes an explicit factor `exp(±θ s)` with `θ` quantified before the
  thresholds.
* "Fixed positive fraction `α`" is quantified before the thresholds as a lower bound `α₀`; the
  conclusion then holds for every subset of relative size at least `α₀`, so later choices of the
  subset are allowed.

Real sample points live in `Pt d = EuclideanSpace ℝ (Fin d)`; the algebraic model of track A
(`DistinctDistances.Foundations`) works in `Point d = Fin d → ℂ`. `toC` is coordinatewise
complexification.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

/-- Euclidean `d`-space, the ambient space of the sample. -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- Coordinatewise complexification of a real point. -/
def toC (x : Pt d) : Point d := fun i => ((x i : ℝ) : ℂ)

/-- The paper's `N = |P|`. -/
def cfgN (P : Finset (Pt d)) : ℝ := (P.card : ℝ)

/-- The paper's `M = 1 + |Δ(P)|` (`reduction.tex`: the count of positive distances plus one). -/
def cfgM (P : Finset (Pt d)) : ℝ := (distinctDistances P : ℝ) + 1

/-- The paper's `B = N^{1/d}`. -/
def cfgB (P : Finset (Pt d)) : ℝ := (P.card : ℝ) ^ ((1 : ℝ) / (d : ℝ))

/-- The paper's `A = B^2 = N^{2/d}`. -/
def cfgA (P : Finset (Pt d)) : ℝ := (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))

/-- The proper-flat cap of `red:flat-caps` (`secants.tex:5–10`): every proper real affine
subspace contains at most `N B^{-c₀}` sample points. The complex-flat form is derived from it
(`complexFlatCap_of_real`). -/
def RealFlatCap (P : Finset (Pt d)) (c₀ : ℝ) : Prop :=
  ∀ F : AffineSubspace ℝ (Pt d), F ≠ ⊤ →
    ((P.filter (· ∈ F)).card : ℝ) ≤ cfgN P * cfgB P ^ (-c₀)

/-- Number of sample points whose complexification lies in a complex point set. -/
def massOn (P : Finset (Pt d)) (T : Set (Point d)) : ℕ := (P.filter (fun x => toC x ∈ T)).card

/-- The complex-flat cap (`secants.tex:6–10`): real points of a proper complex affine flat. -/
theorem complexFlatCap_of_real (P : Finset (Pt d)) (c₀ : ℝ) (h : RealFlatCap P c₀)
    (F : AffineSubspace ℂ (Point d)) (hF : F ≠ ⊤) :
    (massOn P (F : Set (Point d)) : ℝ) ≤ cfgN P * cfgB P ^ (-c₀) := by
  let toCfun : Pt d → Point d := toC
  let G : AffineSubspace ℝ (Pt d) :=
    { carrier := {x | toCfun x ∈ F}
      smul_vsub_vadd_mem' := by
        rintro t p₁ p₂ p₃ hp₁ hp₂ hp₃
        change toCfun p₁ ∈ F at hp₁
        change toCfun p₂ ∈ F at hp₂
        change toCfun p₃ ∈ F at hp₃
        have ht := F.smul_vsub_vadd_mem' (t : ℂ) hp₁ hp₂ hp₃
        change toCfun (t • (p₁ -ᵥ p₂) +ᵥ p₃) ∈ F
        have hmap : toCfun (t • (p₁ -ᵥ p₂) +ᵥ p₃) =
            (t : ℂ) • (toCfun p₁ -ᵥ toCfun p₂) +ᵥ toCfun p₃ := by
          ext i
          simp [toCfun, toC, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub]
        rw [hmap]
        exact ht
      }
  have hspan : vectorSpan ℂ (Set.range toCfun) = ⊤ := by
    apply top_unique
    intro z hz
    have hsingle : ∀ i : Fin d,
        (Pi.single i (1 : ℂ) : Point d) ∈ vectorSpan ℂ (Set.range toCfun) := by
      intro i
      have hp₁ : toCfun (EuclideanSpace.single i (1 : ℝ)) ∈ Set.range toCfun :=
        Set.mem_range_self _
      have hp₂ : toCfun (0 : Pt d) ∈ Set.range toCfun := Set.mem_range_self _
      have hi := vsub_mem_vectorSpan ℂ hp₁ hp₂
      have hdiff : toCfun (EuclideanSpace.single i (1 : ℝ)) -
          toCfun (0 : Pt d) = (Pi.single i (1 : ℂ) : Point d) := by
        ext j
        by_cases hji : j = i <;> simp [toCfun, toC, hji]
      simpa [vsub_eq_sub, hdiff] using hi
    have hzsum : z = ∑ i : Fin d, z i • (Pi.single i (1 : ℂ) : Point d) := by
      ext j
      simp [Pi.single_apply]
    rw [hzsum]
    exact Submodule.sum_mem _ fun i hi => (vectorSpan ℂ (Set.range toCfun)).smul_mem _ (hsingle i)
  have hspanAff : affineSpan ℂ (Set.range toCfun) = ⊤ := by
    exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
      (k := ℂ) (V := Point d) (P := Point d) (s := Set.range toCfun)
      (show (Set.range toCfun).Nonempty from ⟨toCfun 0, Set.mem_range_self 0⟩)).2 hspan
  have hG : G ≠ ⊤ := by
    intro htop
    have hall : ∀ x : Pt d, toCfun x ∈ F := by
      intro x
      have hx : x ∈ G := by rw [htop]; simp
      exact hx
    have hle : affineSpan ℂ (Set.range toCfun) ≤ F :=
      (affineSpan_le).2 fun z hz => by rcases hz with ⟨x, rfl⟩; exact hall x
    have htopF : (⊤ : AffineSubspace ℂ (Point d)) ≤ F := by
      rw [hspanAff] at hle
      exact hle
    exact hF (le_antisymm le_top htopF)
  have hGmem (x : Pt d) : x ∈ G ↔ toCfun x ∈ F := Iff.rfl
  have hmass : massOn P (F : Set (Point d)) = (P.filter (· ∈ G)).card := by
    apply congrArg Finset.card
    ext x
    simp [Finset.mem_filter, hGmem, toCfun]
  rw [hmass]
  exact h G hG

/-! ### General points and pairs

"For a general point / pair" means: off a proper Zariski-closed subset, encoded by a polynomial
that does not vanish identically on the variety (resp. on `X × Y`). For irreducible varieties the
complement of its zero set is dense. -/

/-- `Q x` holds for a general point `x` of `X`. -/
def ForGeneralPoint (X : AffineVariety d) (Q : Point d → Prop) : Prop :=
  ∃ g : Poly d, (∃ x ∈ X, MvPolynomial.eval x g ≠ 0) ∧
    ∀ x ∈ X, MvPolynomial.eval x g ≠ 0 → Q x

/-- Evaluation point of a pair in `ℂ^d × ℂ^d`, for polynomials in the variables `Fin d ⊕ Fin d`. -/
def pairPt (x y : Point d) : Fin d ⊕ Fin d → ℂ := Sum.elim x y

/-- Polynomials on pairs (source coordinates `inl`, target coordinates `inr`). -/
abbrev PairPoly (d : ℕ) := MvPolynomial (Fin d ⊕ Fin d) ℂ

/-- `Q x y` holds for a general pair `(x, y) ∈ X × Y`. -/
def ForGeneralPair (X Y : AffineVariety d) (Q : Point d → Point d → Prop) : Prop :=
  ∃ g : PairPoly d, (∃ x ∈ X, ∃ y ∈ Y, MvPolynomial.eval (pairPt x y) g ≠ 0) ∧
    ∀ x ∈ X, ∀ y ∈ Y, MvPolynomial.eval (pairPt x y) g ≠ 0 → Q x y

/-- A polynomial on pairs vanishes identically on `X × Y`. -/
def VanishesOnProduct (F : PairPoly d) (X Y : AffineVariety d) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, MvPolynomial.eval (pairPt x y) F = 0

/-! ### Flats, lines and real structure -/

/-- `Z` is a complex affine flat. -/
def IsFlat (Z : AffineVariety d) : Prop :=
  ∃ F : AffineSubspace ℂ (Point d), Z.points = (F : Set (Point d))

/-- `Z` is a complex affine line. -/
def IsLine (Z : AffineVariety d) : Prop :=
  ∃ a v : Point d, v ≠ 0 ∧ Z.points = {z | ∃ t : ℂ, z = a + t • v}

/-- `Z` is the complexification of a real affine flat (its real points span it). -/
def IsRealFlat (Z : AffineVariety d) : Prop :=
  ∃ F : AffineSubspace ℝ (Pt d), (F : Set (Pt d)).Nonempty ∧
    Z.points = (AffineVariety.closure (toC '' (F : Set (Pt d)))).points

/-- The complex affine span of a variety (as an affine subspace of `ℂ^d`). -/
def complexSpan (Z : AffineVariety d) : AffineSubspace ℂ (Point d) := affineSpan ℂ Z.points

/-! ### Directional curve families (`secants.tex:223–231`, `sparse-cones.tex:6–8`) -/

/-- A projective variety in `ℙ^{d-1} = ℙ(ℂ^d)` spans a projective subspace of dimension at most
two. -/
def SpansAtMostPlane (γ : ProjectiveVariety d) : Prop :=
  ∃ W : Submodule ℂ (Point d), Module.finrank ℂ W ≤ 3 ∧ ∀ z ∈ γ.points, z.submodule ≤ W

/-- A directional curve family: finitely many distinct irreducible projective curves in
`ℙ^{d-1}`, each spanning projective dimension at most two. Its total degree is
`ProjectiveFamily.degree`. -/
def IsDirectionalFamily (C : ProjectiveFamily.Family d) : Prop :=
  ∀ γ ∈ C, γ.IsIrreducible ∧ γ.dimension = 1 ∧ SpansAtMostPlane γ

/-- Membership in a family means membership in the union of its members. -/
def familyPoints (C : ProjectiveFamily.Family d) : Set (ProjectivePoint d) :=
  ⋃ γ ∈ C, γ.points

/-- The direction `π_p(q) = [q - p]` of a pair of distinct real points lies on the family. -/
def DirIn (C : ProjectiveFamily.Family d) (p q : Pt d) : Prop :=
  ∃ h : toC q ≠ toC p, radialProjection (toC p) (toC q) h ∈ familyPoints C

/-- The closure of the radial projection of `Y` from `p` is contained in the family:
`closure(π_p Y) ⊆ C_p` (`secants.tex:240`). -/
def ProjectsInto (C : ProjectiveFamily.Family d) (p : Pt d) (Y : AffineVariety d) : Prop :=
  (radialImage (toC p) Y).points ⊆ familyPoints C

/-! ### Assignments of sample points to carriers (`secants.tex:229–231`) -/

/-- A partial assignment of sample points to a finite family of distinct varieties: assigned sets
are contained in `P` and in their carrier, and pairwise disjoint. Repeated carriers are pooled
because the family is a `Finset`. -/
structure Assignment (P : Finset (Pt d)) (𝒴 : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) : Prop where
  subset : ∀ Y ∈ 𝒴, S Y ⊆ P
  mem : ∀ Y ∈ 𝒴, ∀ q ∈ S Y, toC q ∈ Y
  disjoint : (𝒴 : Set (AffineVariety d)).PairwiseDisjoint S

/-- Irreducible affine curve. -/
def IsCurve (Y : AffineVariety d) : Prop := Y.IsIrreducible ∧ Y.dimension = 1

end

end TrackD
end DistinctDistances
