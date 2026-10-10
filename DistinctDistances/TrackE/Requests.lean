import DistinctDistances.TrackE.GlobalConcentration
import DistinctDistances.TrackE.Directions
import DistinctDistances.Bridges.CIncidence
import DistinctDistances.Bridges.CPlanar
import DistinctDistances.Bridges.CMotions
import DistinctDistances.TrackE.RequestsFirstCut
import DistinctDistances.TrackE.RequestsWide
import DistinctDistances.TrackE.RequestsWideFlat
import DistinctDistances.TrackE.RequestsRank
import DistinctDistances.TrackE.RequestsStar
import DistinctDistances.TrackE.RequestsDirectionCuts
import DistinctDistances.Bridges.UniformConcentration
import DistinctDistances.Bridges.HypersurfaceComponents

/-!
# Inputs track E consumes from other tracks

The exact forms the track E proofs use from other tracks, stated as `Prop`s; the bridges supply
them from the owning track's theorems.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Request

open Classical in
/-- Track C, `ci:planar-occupancy` after the planar shortcut
(track C's `TrackC.ci_planar_occupancy`): in any dimension, a real affine plane
holds at most `C M^{4/3}` points. Consumer: `Reduction.card_inter_plane_le`. -/
def PlanarOccupancy : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (Q : Finset (RPoint m)) (H : AffineSubspace ℝ (RPoint m)),
    Module.finrank ℝ H.direction = 2 →
      ((Q.filter (· ∈ H)).card : ℝ) ≤ C * Mcount Q ^ ((4 : ℝ) / 3)

open Classical in
/-- Track C, `ci:st` (`classical-incidence.tex:48-61`), rich-line form in `ℝ^m`: at most
`C (n^2/t^3 + n/t)` lines hold at least `t ≥ 2` points of an `n`-point set. The same `Prop` as
track D's `TrackD.STRichLines`. Consumer: `Reduction.card_pairs_on_rich_lines`. -/
def RichLines (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset (RPoint m)) (L : Finset (AffineSubspace ℝ (RPoint m))) (t : ℝ),
    2 ≤ t → (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ t ≤ ((Q.filter (· ∈ ℓ)).card : ℝ)) →
      (L.card : ℝ) ≤ C * ((Q.card : ℝ) ^ 2 / t ^ 3 + Q.card / t)

open Classical in
/-- Track C, `mot:rich` (`motions.tex:16-31`), for a rotated copy `Q = RP`: the rigid motions
`g` with `k_g = |{p ∈ P : g p ∈ Q}| ≥ C_rich A` lie in a finite set `G` with
`∑_{g ∈ G} k_g^2 ≤ K_rich N^4/A`, both orientations included, whenever `|P| ≥ 2`, `M ≤ A`.
Consumer: `Reduction.exists_retained_graph` (`d = 3`). -/
def RichMotions : Prop :=
  ∃ Crich Krich : ℝ, 0 < Crich ∧ 0 < Krich ∧
    ∀ (P : Finset (RPoint 3)) (R : RPoint 3 ≃ₗᵢ[ℝ] RPoint 3), 2 ≤ P.card →
      Mcount P ≤ Ascale 3 P.card →
      ∃ G : Finset (RPoint 3 ≃ᵃⁱ[ℝ] RPoint 3),
        (∀ g : RPoint 3 ≃ᵃⁱ[ℝ] RPoint 3,
          Crich * Ascale 3 P.card ≤ ((P.filter fun p => g p ∈ P.image R).card : ℝ) → g ∈ G) ∧
        ∑ g ∈ G, (((P.filter fun p => g p ∈ P.image R).card : ℝ)) ^ 2 ≤
          Krich * (P.card : ℝ) ^ 4 / Ascale 3 P.card

open Classical in
/-- Track B, `conc:theorem` (`concentration.tex:44-70`), in skew-form coordinates `SkewIdx e`.
Parameters are pairs `(v, y)` with `y(v) = 0`, `v ≠ 0`, pairwise non-proportional. Hypotheses:
(i) homogeneous separators of positive degree at most `C₀ A` in the `2e` coordinates `(v,y)`;
(ii) at most `C₀ A^{r-1}` parameters in any `e`-dimensional subspace isotropic for
`(v,y),(v',y') ↦ y(v') + y'(v)`. Conclusion for irreducible `V` of dimension `s₀ + h`,
`1 ≤ h < r` (`r = e-1`, `s₀ = C(e-1,2)`): (a) if `|Λ| ≤ C₀ A^r`, (b) if `V` lies in the zero set
of a nonzero polynomial of degree at most `C₀ A`; then at most `C deg(V) A^h` flats `F_λ ⊆ V`.
Consumers: `Reduction.global_concentration` (`e = d+1`, (a)), `Reduction.local_concentration`
(`e = d`, (b)). -/
def UniformConcentration (e : ℕ) : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ), 1 ≤ A →
  ∀ Λ : Finset ((Fin e → ℂ) × (Fin e → ℂ)),
    (∀ l ∈ Λ, l.1 ≠ 0 ∧ ∑ i, l.2 i * l.1 i = 0) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ c : ℂ, l' = c • l → l' = l) →
    (∀ l ∈ Λ, ∃ (k : ℕ) (f : MvPolynomial (Fin e ⊕ Fin e) ℂ), 1 ≤ k ∧ (k : ℝ) ≤ C₀ * A ∧
      f.IsHomogeneous k ∧ MvPolynomial.eval (Sum.elim l.1 l.2) f ≠ 0 ∧
      ∀ l' ∈ Λ, l' ≠ l → MvPolynomial.eval (Sum.elim l'.1 l'.2) f = 0) →
    (∀ L : Submodule ℂ ((Fin e → ℂ) × (Fin e → ℂ)), Module.finrank ℂ L = e →
      (∀ x ∈ L, ∀ x' ∈ L, ∑ i, (x.2 i * x'.1 i + x'.2 i * x.1 i) = 0) →
      ((Λ.filter (· ∈ L)).card : ℝ) ≤ C₀ * A ^ (e - 2)) →
    ∀ V : AffineVariety (Fintype.card (SkewIdx e)), V.IsIrreducible →
    ∀ h : ℕ, 1 ≤ h → h < e - 1 → V.dimension = Nat.choose (e - 1) 2 + h →
      ((Λ.card : ℝ) ≤ C₀ * A ^ (e - 1) ∨
        ∃ g : Poly (Fintype.card (SkewIdx e)), g ≠ 0 ∧ (g.totalDegree : ℝ) ≤ C₀ * A ∧
          ∀ x ∈ V.points, MvPolynomial.eval x g = 0) →
      ((Λ.filter fun l => skewToPoint '' evalFlat l.1 l.2 ⊆ V.points).card : ℝ) ≤
        C * (V.degree : ℝ) * A ^ h

/-- Track A, hypersurface components (`reduction.tex:446-452`; `FA.model`, `FA.bezout`): for a
nonzero `g`, a finite family of irreducible varieties of dimension `n - 1` inside `Z(g)`, of total
degree at most `deg g`, such that every nonempty affine subspace on which `g` vanishes lies in one
of them. Consumer: `Reduction.local_concentration`. -/
def HypersurfaceComponents (n : ℕ) : Prop :=
  ∀ g : Poly n, g ≠ 0 → ∃ F : Finset (AffineVariety n),
    (∀ V ∈ F, V.IsIrreducible ∧ V.dimension + 1 = n ∧
      ∀ x ∈ V.points, MvPolynomial.eval x g = 0) ∧
    (∑ V ∈ F, (V.degree : ℝ)) ≤ g.totalDegree ∧
    ∀ L : AffineSubspace ℂ (Point n), (L : Set (Point n)).Nonempty →
      (∀ x ∈ L, MvPolynomial.eval x g = 0) → ∃ V ∈ F, (L : Set (Point n)) ⊆ V.points

/-- Placeholder for track A's hypersurface decomposition. -/
theorem hypersurfaceComponents (n : ℕ) : HypersurfaceComponents n :=
  Bridges.hypersurface_components n

/-- Placeholder for track C's `ci:planar-occupancy`. -/
theorem planarOccupancy : PlanarOccupancy := by
  exact Bridges.planar_occupancy_mcount

/-- Placeholder for track C's `ci:st` (rich lines in `ℝ^m`). -/
theorem richLines (m : ℕ) : RichLines m := by
  exact Bridges.ci_st_rich_real m

/-- Placeholder for track C's `mot:rich`. -/
theorem richMotions : RichMotions := by
  exact Bridges.rich_motions_rotated

/-- Placeholder for track B's `conc:theorem`. -/
theorem uniformConcentration (e : ℕ) (he : 3 ≤ e) : UniformConcentration e := by
  exact Bridges.uniform_concentration_bridge he

end Request

end

end DistinctDistances
