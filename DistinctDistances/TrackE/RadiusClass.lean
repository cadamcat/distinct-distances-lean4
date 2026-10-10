import DistinctDistances.TrackE.Directional
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The rich-radius branch of `red:directions.count`

`reduction.tex:151–178`: equal distances from two points in one radius class produce
hyperplane sections proper on the variety carrying the counted directions. Counting the
same incidences by partners and by ordered pairs gives the next dimension bound.

The collision lower bound is an explicit input here. Its distance-energy specialization
uses OAI's `PolynomialIsolation.lean`; this file does not re-prove that OAI theorem.
The proper-section degree estimate is an input from track A's projective Bézout node.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

open Classical in
/-- Count a finite incidence relation by either coordinate. -/
theorem sum_card_filter_swap {α β : Type*} (S : Finset α) (T : Finset β)
    (R : α → β → Prop) :
    ∑ x ∈ S, (T.filter (R x)).card = ∑ y ∈ T, (S.filter fun x => R x y).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

open Classical in
/-- The counting step at `reduction.tex:173–177`, with the row energy bound supplied
separately. At least `L²/(2M)` incidences in each row and at most `B` in each column
force at most `2MB` rows. Columns are ordered distinct pairs from an `L`-point set. -/
theorem card_le_two_mul_of_many_collisions {α β : Type*} (S : Finset α) (Z : Finset β)
    (R : α → β × β → Prop) (M B : ℝ) (hM : 0 < M) (hB : 0 ≤ B) (hZ : Z.Nonempty)
    (hrow : ∀ x ∈ S, (Z.card : ℝ) ^ 2 / (2 * M) ≤
      ((Z.offDiag.filter (R x)).card : ℝ))
    (hcol : ∀ e ∈ Z.offDiag, ((S.filter fun x => R x e).card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ 2 * M * B := by
  classical
  have hcount :
      (S.card : ℝ) * ((Z.card : ℝ) ^ 2 / (2 * M)) ≤
        (Z.card : ℝ) ^ 2 * B := by
    calc
      _ = ∑ x ∈ S, (Z.card : ℝ) ^ 2 / (2 * M) := by simp
      _ ≤ ∑ x ∈ S, ((Z.offDiag.filter (R x)).card : ℝ) :=
        Finset.sum_le_sum hrow
      _ = ∑ e ∈ Z.offDiag, ((S.filter fun x => R x e).card : ℝ) := by
        exact_mod_cast sum_card_filter_swap S Z.offDiag R
      _ ≤ ∑ _ ∈ Z.offDiag, B := Finset.sum_le_sum hcol
      _ = (Z.offDiag.card : ℝ) * B := by simp
      _ ≤ (Z.card : ℝ) ^ 2 * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        have h := Finset.card_le_card (show Z.offDiag ⊆ Z.product Z from by
          intro e he
          exact Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp he).1,
            (Finset.mem_offDiag.mp he).2.1⟩)
        simpa [Finset.card_product, pow_two] using (Nat.cast_le.mpr h :
          (Z.offDiag.card : ℝ) ≤ (Z.product Z).card)
  have hL : 0 < (Z.card : ℝ) ^ 2 := by
    have : (0 : ℝ) < Z.card := by exact_mod_cast hZ.card_pos
    positivity
  have hcount' : (S.card : ℝ) * (Z.card : ℝ) ^ 2 ≤
      ((Z.card : ℝ) ^ 2 * B) * (2 * M) := by
    exact (div_le_iff₀ (by positivity : 0 < 2 * M)).mp (by
      simpa [mul_div_assoc] using hcount)
  apply (mul_le_mul_iff_right₀ hL).mp
  nlinarith [hcount']

/-- Equal distances from `p` and from `q` give the orthogonality used to define
the hyperplane section (`reduction.tex:160–165`). -/
theorem inner_sub_sub_eq_zero_of_dist_eq (p q z z' : RPoint d)
    (hp : dist z p = dist z' p) (hq : dist z q = dist z' q) :
    inner ℝ (q - p) (z - z') = 0 := by
  have h := EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq hp hq
  have h' : inner ℝ (q - p) (z' - z) = 0 := by simpa only [vsub_eq_sub] using h
  rw [← neg_sub z' z, inner_neg_right, h', neg_zero]

/-- A nonzero vector in the span of a finite set has a nonzero inner product with
one of its generators. -/
theorem exists_generator_inner_ne_zero (p : RPoint d) (T : Finset (RPoint d))
    (n : RPoint d) (hn : n ≠ 0)
    (hmem : n ∈ Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))) :
    ∃ q ∈ T, inner ℝ (q - p) n ≠ 0 := by
  classical
  by_contra! hz
  have hspan : ∀ v ∈ Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d))),
      inner ℝ v n = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨q, hq, rfl⟩ := hv
      exact hz q hq
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
    | smul r x _ hx => simp [inner_smul_left, hx]
  exact hn ((inner_self_eq_zero).mp (hspan n hmem))

/-- Distinct projections give a proper hyperplane on the counted displacements.
The span is formed from the counted partners themselves, as required in the paper. -/
theorem exists_partner_inner_ne_zero_of_projection_ne (p : RPoint d)
    (T : Finset (RPoint d)) (z z' : RPoint d)
    (hproj :
      (Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))).orthogonalProjectionOnto z ≠
      (Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))).orthogonalProjectionOnto z') :
    ∃ q ∈ T, inner ℝ (q - p) (z - z') ≠ 0 := by
  let U := Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))
  let n : U := U.orthogonalProjectionOnto (z - z')
  have hn : (n : RPoint d) ≠ 0 := by
    intro hz
    apply hproj
    have hn0 : n = 0 := Subtype.ext hz
    change U.orthogonalProjectionOnto (z - z') = 0 at hn0
    rw [map_sub, sub_eq_zero] at hn0
    exact hn0
  obtain ⟨q, hq, hneq⟩ := exists_generator_inner_ne_zero p T (n : RPoint d) hn n.property
  refine ⟨q, hq, ?_⟩
  have hqU : q - p ∈ U := Submodule.subset_span ⟨q, hq, rfl⟩
  have hinner : inner ℝ (q - p) (n : RPoint d) = inner ℝ (q - p) (z - z') :=
    U.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨q - p, hqU⟩ (z - z')
  rwa [hinner] at hneq

/-- The normal supplied by distinct real projections does not vanish identically on the
complex cone over `Y` (`reduction.tex:166–171`). This uses actual representatives in the
definition of projective membership and needs no dimension or degree bridge. -/
theorem proper_section_of_projection_ne (p : RPoint d) (T : Finset (RPoint d))
    (Y : ProjectiveVariety d) (hY : ∀ q ∈ T, DirMem Y p q) (z z' : RPoint d)
    (hproj :
      (Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))).orthogonalProjectionOnto z ≠
      (Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))).orthogonalProjectionOnto z') :
    ∃ v ∈ Y.affineCone.points, ∑ i, v i * cplx (z - z') i ≠ 0 := by
  obtain ⟨q, hq, hneq⟩ := exists_partner_inner_ne_zero_of_projection_ne p T z z' hproj
  obtain ⟨hne, hdir⟩ := hY q hq
  have hsub : cplx (q - p) = cplx q - cplx p := by ext i; simp [cplx]
  refine ⟨cplx (q - p), ?_, ?_⟩
  · change cplx (q - p) ∈ MvPolynomial.zeroLocus ℂ Y.ideal
    rw [hsub]
    exact hdir (cplx q - cplx p) (sub_ne_zero.mpr hne) rfl
  · have hsum : ∑ i, cplx (q - p) i * cplx (z - z') i =
        ((inner ℝ (q - p) (z - z') : ℝ) : ℂ) := by
      simp only [cplx, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    exact_mod_cast hneq

open Classical in
/-- Sum the induction bounds over the components of a proper hyperplane section.
Components may overlap: only a covering and their total degree are used. -/
theorem direction_section_count_le (p : RPoint d) (T : Finset (RPoint d))
    (F : ProjectiveFamily.Family d) (n : RPoint d) (C A degree : ℝ) (a : ℕ)
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hcover : ∀ q ∈ T, inner ℝ (q - p) n = 0 → ∃ V ∈ F, DirMem V p q)
    (hdegree : (∑ V ∈ F, (V.degree : ℝ)) ≤ degree)
    (hcap : ∀ V ∈ F, ((T.filter fun q => DirMem V p q).card : ℝ) ≤
      C * (V.degree : ℝ) * A ^ a) :
    ((T.filter fun q => inner ℝ (q - p) n = 0).card : ℝ) ≤ C * degree * A ^ a := by
  classical
  have hsubset : (T.filter fun q => inner ℝ (q - p) n = 0) ⊆
      F.biUnion (fun V => T.filter fun q => DirMem V p q) := by
    intro q hq
    obtain ⟨hqT, hqn⟩ := Finset.mem_filter.mp hq
    obtain ⟨V, hVF, hqV⟩ := hcover q hqT hqn
    exact Finset.mem_biUnion.mpr ⟨V, hVF, Finset.mem_filter.mpr ⟨hqT, hqV⟩⟩
  calc
    _ ≤ ((F.biUnion (fun V => T.filter fun q => DirMem V p q)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsubset)
    _ ≤ ∑ V ∈ F, ((T.filter fun q => DirMem V p q).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := F)
        (t := fun V => T.filter fun q => DirMem V p q))
    _ ≤ ∑ V ∈ F, C * (V.degree : ℝ) * A ^ a := Finset.sum_le_sum hcap
    _ = C * (∑ V ∈ F, (V.degree : ℝ)) * A ^ a := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ C * degree * A ^ a := by gcongr

open Classical in
/-- `red:directions.radius` (`reduction.tex:151–178`): the rich-radius branch of the
dimension induction. The collision energy and the proper-section partner bound are
explicit inputs. The conclusion has the degree and power consumed by the next stage. -/
theorem direction_count_of_rich_radius (p : RPoint d) (T Z : Finset (RPoint d))
    (A M C degree : ℝ) (a : ℕ) (hA : 0 ≤ A) (hM : 0 < M) (hMA : M ≤ A)
    (hC : 0 ≤ C) (hdegree : 0 ≤ degree) (ha : 1 ≤ a) (hZ : Z.Nonempty)
    (hradius : ∀ z ∈ Z, ∀ z' ∈ Z, dist z p = dist z' p)
    (henergy : ∀ q ∈ T, (Z.card : ℝ) ^ 2 / (2 * M) ≤
      ((Z.offDiag.filter fun e => dist e.1 q = dist e.2 q).card : ℝ))
    (hsection : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' →
      ((T.filter fun q => inner ℝ (q - p) (z - z') = 0).card : ℝ) ≤
        C * degree * A ^ (a - 1)) :
    (T.card : ℝ) ≤ 2 * C * degree * A ^ a := by
  classical
  have hcount := card_le_two_mul_of_many_collisions T Z
    (fun q e => dist e.1 q = dist e.2 q) M (C * degree * A ^ (a - 1)) hM
    (by positivity) hZ henergy (by
      intro e he
      obtain ⟨hz, hz', hne⟩ := Finset.mem_offDiag.mp he
      apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_))
        (hsection e.1 hz e.2 hz' hne)
      intro q hq
      obtain ⟨hqT, heq⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hqT,
        inner_sub_sub_eq_zero_of_dist_eq p q e.1 e.2 (hradius e.1 hz e.2 hz') heq⟩)
  calc
    (T.card : ℝ) ≤ 2 * M * (C * degree * A ^ (a - 1)) := hcount
    _ ≤ 2 * A * (C * degree * A ^ (a - 1)) := by gcongr
    _ = 2 * C * degree * A ^ a := by
      have hpow : A ^ (a - 1) * A = A ^ a := by
        rw [← pow_succ, Nat.sub_add_cancel ha]
      calc
        _ = 2 * C * degree * (A ^ (a - 1) * A) := by ring
        _ = _ := by rw [hpow]

open Classical in
/-- The rich-radius branch with the exact projective-section interface used by
`red:directions.count`. Track A supplies the component covering and degree sum;
the dimension induction supplies `hcap`. The real properness argument is proved above. -/
theorem direction_count_of_rich_radius_sections (p : RPoint d)
    (T Z : Finset (RPoint d)) (Y : ProjectiveVariety d) (A M C : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) (hMA : M ≤ A) (hC : 0 ≤ C)
    (hdegree : 0 ≤ (Y.degree : ℝ)) (ha : 1 ≤ Y.dimension)
    (hT : ∀ q ∈ T, DirMem Y p q) (hZ : Z.Nonempty)
    (hradius : ∀ z ∈ Z, ∀ z' ∈ Z, dist z p = dist z' p)
    (hproj : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' →
      (Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))).orthogonalProjectionOnto z ≠
      (Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))).orthogonalProjectionOnto z')
    (henergy : ∀ q ∈ T, (Z.card : ℝ) ^ 2 / (2 * M) ≤
      ((Z.offDiag.filter fun e => dist e.1 q = dist e.2 q).card : ℝ))
    (hsections : ∀ n : RPoint d,
      (∃ v ∈ Y.affineCone.points, ∑ i, v i * cplx n i ≠ 0) →
      ∃ F : ProjectiveFamily.Family d,
        (∀ V ∈ F, V.IsIrreducible ∧ V.dimension + 1 = Y.dimension) ∧
        (∑ V ∈ F, (V.degree : ℝ)) ≤ (Y.degree : ℝ) ∧
        ∀ q ∈ T, inner ℝ (q - p) n = 0 → ∃ V ∈ F, DirMem V p q)
    (hcap : ∀ V : ProjectiveVariety d, V.IsIrreducible → V.dimension + 1 = Y.dimension →
      ((T.filter fun q => DirMem V p q).card : ℝ) ≤
        C * (V.degree : ℝ) * A ^ (Y.dimension - 1)) :
    (T.card : ℝ) ≤ 2 * C * (Y.degree : ℝ) * A ^ Y.dimension := by
  apply direction_count_of_rich_radius p T Z A M C (Y.degree : ℝ) Y.dimension
    hA hM hMA hC hdegree ha hZ hradius henergy
  intro z hz z' hz' hne
  obtain ⟨F, hF, hdeg, hcover⟩ := hsections (z - z')
    (proper_section_of_projection_ne p T Y hT z z' (hproj z hz z' hz' hne))
  exact direction_section_count_le p T F (z - z') C A (Y.degree : ℝ)
    (Y.dimension - 1) hC hA hcover hdeg
    (fun V hVF => hcap V (hF V hVF).1 (hF V hVF).2)

end Reduction

end

end DistinctDistances
