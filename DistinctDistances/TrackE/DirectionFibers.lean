import DistinctDistances.TrackE.Directional
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Light-line bounds for finitely many directions

`reduction.tex:145–146,197–201`: a projective point contributes at most the occupancy
of one physical line. A finite projective locus therefore contributes at most its
cardinality times the light-line bound. Track A supplies the finite-locus degree
bounds for zero-dimensional irreducible varieties and for proper curve sections.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

/-- Equal complex projective directions of real displacements put the partners on one
real physical line. Taking real parts of the complex proportionality gives its parameter. -/
theorem mem_line_of_radialProjection_eq (p q r : RPoint d)
    (hq : cplx q ≠ cplx p) (hr : cplx r ≠ cplx p)
    (h : radialProjection (cplx p) (cplx r) hr =
      radialProjection (cplx p) (cplx q) hq) :
    r ∈ affineSpan ℝ {p, q} := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ
    (cplx r - cplx p) (cplx q - cplx p) (sub_ne_zero.mpr hr) (sub_ne_zero.mpr hq)).mp h
  have hreal : a.re • (q - p) = r - p := by
    ext i
    have hi := congrArg Complex.re (congrFun ha i)
    simpa [cplx, PiLp.smul_apply, PiLp.sub_apply, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re] using hi
  have hm := smul_vsub_vadd_mem_affineSpan_pair a.re p q
  simpa only [vsub_eq_sub, vadd_eq_add, hreal, sub_add_cancel] using hm

open Classical in
/-- The partners of `p` with one specified projective direction. -/
def directionFiber (T : Finset (RPoint d)) (p : RPoint d) (z : ProjectivePoint d) :
    Finset (RPoint d) :=
  T.filter fun q => ∃ h : cplx q ≠ cplx p, radialProjection (cplx p) (cplx q) h = z

open Classical in
/-- One projective direction receives at most `H` partners if each physical line
through a partner has sample occupancy at most `H`. -/
theorem card_directionFiber_le (P T : Finset (RPoint d)) (p : RPoint d)
    (z : ProjectivePoint d) (H : ℝ) (hH : 0 ≤ H) (hT : T ⊆ P)
    (hlight : ∀ q ∈ T, ((P.filter (· ∈ affineSpan ℝ {p, q})).card : ℝ) ≤ H) :
    ((directionFiber T p z).card : ℝ) ≤ H := by
  classical
  by_cases hne : (directionFiber T p z).Nonempty
  · obtain ⟨q, hq⟩ := hne
    obtain ⟨hqT, hqc, hqz⟩ := Finset.mem_filter.mp hq
    have hsubset : directionFiber T p z ⊆ P.filter (· ∈ affineSpan ℝ {p, q}) := by
      intro r hr
      obtain ⟨hrT, hrc, hrz⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hT hrT,
        mem_line_of_radialProjection_eq p q r hqc hrc (hrz.trans hqz.symm)⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans (hlight q hqT)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa only [hempty, Finset.card_empty, Nat.cast_zero] using hH

open Classical in
/-- `red:directions.finite-locus`: the light-line bound summed over a finite projective
locus (`reduction.tex:145–146,197–201`). This applies to the base of the dimension induction
and to proper linear sections of an irreducible curve. -/
theorem card_partners_on_finite_directions_le (P T : Finset (RPoint d)) (p : RPoint d)
    (F : Finset (ProjectivePoint d)) (H : ℝ) (hH : 0 ≤ H) (hT : T ⊆ P)
    (hlight : ∀ q ∈ T, ((P.filter (· ∈ affineSpan ℝ {p, q})).card : ℝ) ≤ H)
    (hcover : ∀ q ∈ T, ∃ h : cplx q ≠ cplx p,
      radialProjection (cplx p) (cplx q) h ∈ F) :
    (T.card : ℝ) ≤ H * F.card := by
  classical
  have hsubset : T ⊆ F.biUnion (directionFiber T p) := by
    intro q hq
    obtain ⟨hc, hz⟩ := hcover q hq
    exact Finset.mem_biUnion.mpr ⟨radialProjection (cplx p) (cplx q) hc, hz,
      Finset.mem_filter.mpr ⟨hq, hc, rfl⟩⟩
  calc
    (T.card : ℝ) ≤ ((F.biUnion (directionFiber T p)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsubset)
    _ ≤ ∑ z ∈ F, ((directionFiber T p z).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := F) (t := directionFiber T p))
    _ ≤ ∑ _ ∈ F, H := Finset.sum_le_sum fun z _ =>
      card_directionFiber_le P T p z H hH hT hlight
    _ = H * F.card := by simp [mul_comm]

open Classical in
/-- Use a finite-locus degree bound without importing the unfinished definition of degree.
The consumer specializes `degree` to `Y.degree`. -/
theorem card_partners_on_finite_directions_le_degree (P T : Finset (RPoint d))
    (p : RPoint d) (F : Finset (ProjectivePoint d)) (H degree : ℝ)
    (hH : 0 ≤ H) (hT : T ⊆ P)
    (hlight : ∀ q ∈ T, ((P.filter (· ∈ affineSpan ℝ {p, q})).card : ℝ) ≤ H)
    (hcover : ∀ q ∈ T, ∃ h : cplx q ≠ cplx p,
      radialProjection (cplx p) (cplx q) h ∈ F)
    (hdegree : (F.card : ℝ) ≤ degree) :
    (T.card : ℝ) ≤ H * degree :=
  (card_partners_on_finite_directions_le P T p F H hH hT hlight hcover).trans
    (mul_le_mul_of_nonneg_left hdegree hH)

end Reduction

end

end DistinctDistances
