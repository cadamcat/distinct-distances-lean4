import DistinctDistances.TrackE.Basic
import DistinctDistances.TrackE.Requests
import Mathlib.Algebra.Module.Submodule.Union

/-!
# The equal-distance graph (`reduction.tex:251-306`)

Vertices are pairs `(p,q) ∈ P × Q` with `Q = RP`. Edges join `(p,q)` and `(p',q')` when
`(p,p')` and `(q,q')` are selected and `|p - p'| = |q - q'|`.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

/-- Equal-distance adjacency for selections `SP` on `P` and `SQ` on `Q`
(`reduction.tex:255-259`). -/
def EdAdj (SP SQ : Finset (RPoint d × RPoint d)) (x y : RPoint d × RPoint d) : Prop :=
  (x.1, y.1) ∈ SP ∧ (x.2, y.2) ∈ SQ ∧ dist x.1 y.1 = dist x.2 y.2

set_option maxHeartbeats 5000000

/-- red:u-rotation (`reduction.tex:253, 393-394`): for finitely many pairs `(x,y)` with `x ≠ 0`
there is a rotation `R` with `R x + y ≠ 0` for all of them. (False for `d = 1`.) -/
theorem exists_linearIsometryEquiv_add_ne_zero (hd : 2 ≤ d) (X : Finset (RPoint d × RPoint d))
    (hX : ∀ e ∈ X, e.1 ≠ 0) :
    ∃ R : RPoint d ≃ₗᵢ[ℝ] RPoint d, ∀ e ∈ X, R e.1 + e.2 ≠ 0 := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (RPoint d) := by infer_instance
  let ι := {e : RPoint d × RPoint d // e ∈ X}
  let bad : Option (ι × Bool) → Submodule ℝ (RPoint d) := fun i =>
    match i with
    | none => ⊥
    | some (e, true) => LinearMap.ker (innerSL ℝ (e : RPoint d × RPoint d).1).toLinearMap
    | some (e, false) => ℝ ∙ ((e : RPoint d × RPoint d).1 - (e : RPoint d × RPoint d).2)
  have hspan_ne_top (v : RPoint d) : (ℝ ∙ v) ≠ ⊤ := by
    intro htop
    have hdim : Module.finrank ℝ (ℝ ∙ v) = d := by
      calc
        Module.finrank ℝ (ℝ ∙ v) = Module.finrank ℝ (⊤ : Submodule ℝ (RPoint d)) := by rw [htop]
        _ = d := by simp [RPoint]
    by_cases hv : v = 0
    · rw [hv] at hdim
      rw [show Module.finrank ℝ (ℝ ∙ (0 : RPoint d)) = 0 by simp] at hdim
      omega
    · rw [finrank_span_singleton hv] at hdim
      omega
  have hker_ne_top (v : RPoint d) (hv : v ≠ 0) :
      LinearMap.ker (innerSL ℝ v).toLinearMap ≠ ⊤ := by
    intro htop
    have hmem : v ∈ LinearMap.ker (innerSL ℝ v).toLinearMap := by
      rw [htop]
      exact Submodule.mem_top
    have hzero := LinearMap.mem_ker.mp hmem
    have hinner : inner ℝ v v = 0 := by simpa using hzero
    exact (ne_of_gt (real_inner_self_pos.mpr hv)) hinner
  have hbad : ∀ i, bad i ≠ ⊤ := by
    intro i
    cases i with
    | none => exact bot_ne_top
    | some j =>
      rcases j with ⟨e, b⟩
      cases b with
      | false => exact hspan_ne_top (e.val.1 - e.val.2)
      | true => exact hker_ne_top e.val.1 (hX e.val e.property)
  obtain ⟨n, hn⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  let K : Submodule ℝ (RPoint d) := ℝ ∙ n
  let R : RPoint d ≃ₗᵢ[ℝ] RPoint d := K.reflection
  refine ⟨R, ?_⟩
  intro e he
  have hnker : n ∉ LinearMap.ker (innerSL ℝ e.1).toLinearMap := by
    have h := hn (some ((⟨e, he⟩ : ι), true))
    simpa [bad] using h
  have hinner : inner ℝ e.1 n ≠ 0 := by
    intro hzero
    apply hnker
    apply LinearMap.mem_ker.mpr
    simpa using hzero
  have hnspan : n ∉ ℝ ∙ (e.1 - e.2) := by
    have h := hn (some ((⟨e, he⟩ : ι), false))
    simpa [bad] using h
  intro hzero
  have hR : R e.1 = -e.2 := by
    exact (eq_neg_iff_add_eq_zero).2 hzero
  by_cases hxy : e.1 = e.2
  · have hproj : K.starProjection e.1 = 0 := by
      have hR' := hR
      change K.reflection e.1 = -e.2 at hR'
      rw [Submodule.reflection_apply] at hR'
      have hRreal : (2 : ℝ) • K.starProjection e.1 - e.1 = -e.2 := by
        have hcast : (2 : ℝ) • K.starProjection e.1 =
            (2 : ℕ) • K.starProjection e.1 := Nat.cast_smul_eq_nsmul ℝ 2 _
        rw [hcast]
        exact hR'
      have hsmul : (2 : ℝ) • K.starProjection e.1 = 0 := by
        calc
          (2 : ℝ) • K.starProjection e.1 =
              (2 : ℝ) • K.starProjection e.1 - e.1 + e.1 := by abel
          _ = -e.2 + e.1 := by rw [hRreal]
          _ = 0 := by rw [hxy]; abel
      rcases smul_eq_zero.mp hsmul with htwo | hproj
      · norm_num at htwo
      · exact hproj
    have horth : e.1 ∈ Kᗮ := (K.starProjection_apply_eq_zero_iff).mp hproj
    have hinnerzero : inner ℝ e.1 n = 0 :=
      (Submodule.mem_orthogonal_singleton_iff_inner_left).mp horth
    exact hinner hinnerzero
  · have hdiff : e.1 - e.2 ∈ K := by
      have hR' := hR
      change K.reflection e.1 = -e.2 at hR'
      rw [Submodule.reflection_apply] at hR'
      have hRreal : (2 : ℝ) • K.starProjection e.1 - e.1 = -e.2 := by
        have hcast : (2 : ℝ) • K.starProjection e.1 =
            (2 : ℕ) • K.starProjection e.1 := Nat.cast_smul_eq_nsmul ℝ 2 _
        rw [hcast]
        exact hR'
      have hEq : e.1 - e.2 = (2 : ℝ) • K.starProjection e.1 := by
        have hproj : (2 : ℝ) • K.starProjection e.1 = -e.2 + e.1 :=
          (sub_eq_iff_eq_add).mp hRreal
        rw [hproj]
        abel
      rw [hEq]
      exact Submodule.smul_mem _ _ (K.starProjection_apply_mem e.1)
    rcases Submodule.mem_span_singleton.mp hdiff with ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro ha0
      apply hxy
      have hs : e.1 - e.2 = 0 := by rw [← ha, ha0, zero_smul]
      exact sub_eq_zero.mp hs
    have hnmem : n ∈ ℝ ∙ (e.1 - e.2) := by
      rw [Submodule.mem_span_singleton]
      refine ⟨a⁻¹, ?_⟩
      calc
        a⁻¹ • (e.1 - e.2) = a⁻¹ • (a • n) := by rw [ha]
        _ = n := by simp [ha0]
    exact hnspan hnmem

open Classical in
/-- red:u-graph (`reduction.tex:261-268`): the equal-distance graph on `P × RP` has at least
`|S|^2/M` ordered edges (Cauchy–Schwarz over the lengths). -/
theorem card_edAdj_ge (P : Finset (RPoint d)) (S : Finset (RPoint d × RPoint d))
    (hS : IsSymmSelection P S) (R : RPoint d ≃ₗᵢ[ℝ] RPoint d) :
    (S.card : ℝ) ^ 2 / Mcount P ≤
      (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter fun xy =>
        EdAdj S (S.image (Prod.map R R)) xy.1 xy.2).card := by
  classical
  let D := S.image fun e : RPoint d × RPoint d => dist e.1 e.2
  let fiber := fun r : ℝ => S.filter fun e => dist e.1 e.2 = r
  let T := (S.product S).filter fun ee : (RPoint d × RPoint d) × (RPoint d × RPoint d) =>
    dist ee.1.1 ee.1.2 = dist ee.2.1 ee.2.2
  let f : ((RPoint d × RPoint d) × (RPoint d × RPoint d)) →
      ((RPoint d × RPoint d) × (RPoint d × RPoint d)) := fun ee =>
    ((ee.1.1, R ee.2.1), (ee.1.2, R ee.2.2))
  have hf : Function.Injective f := by
    intro a b hab
    have h₁ : a.1.1 = b.1.1 := congrArg (fun x => x.1.1) hab
    have h₂ : R a.2.1 = R b.2.1 := congrArg (fun x => x.1.2) hab
    have h₃ : a.1.2 = b.1.2 := congrArg (fun x => x.2.1) hab
    have h₄ : R a.2.2 = R b.2.2 := congrArg (fun x => x.2.2) hab
    have he₁ : a.1 = b.1 := Prod.ext h₁ h₃
    have he₂ : a.2 = b.2 := Prod.ext (R.injective h₂) (R.injective h₄)
    exact Prod.ext he₁ he₂
  have hsub : T.image f ⊆
      ((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter fun xy =>
        EdAdj S (S.image (Prod.map R R)) xy.1 xy.2 := by
    intro xy hxy
    rcases Finset.mem_image.mp hxy with ⟨ee, hee, rfl⟩
    rcases Finset.mem_filter.mp hee with ⟨hee, hd⟩
    rcases Finset.mem_product.mp hee with ⟨he₁, he₂⟩
    have he11 := (Finset.mem_offDiag.mp (hS.1 he₁)).1
    have he12 := (Finset.mem_offDiag.mp (hS.1 he₁)).2.1
    have he21 := (Finset.mem_offDiag.mp (hS.1 he₂)).1
    have he22 := (Finset.mem_offDiag.mp (hS.1 he₂)).2.1
    apply Finset.mem_filter.mpr
    change (f ee ∈ (P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)) ∧
      EdAdj S (S.image (Prod.map R R)) (f ee).1 (f ee).2
    simp only [Finset.mem_product, EdAdj, f]
    exact And.intro
      (And.intro (And.intro he11 (Finset.mem_image.mpr ⟨ee.2.1, he21, rfl⟩))
        (And.intro he12 (Finset.mem_image.mpr ⟨ee.2.2, he22, rfl⟩)))
      (And.intro he₁ (And.intro
        (Finset.mem_image.mpr ⟨ee.2, he₂, by ext <;> rfl⟩)
        (by simpa only [R.dist_map] using hd)))
  have hsum : ∑ r ∈ D, (fiber r).card = S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_eq_self.mpr
    intro e he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  have hT : T.card = ∑ r ∈ D, (fiber r).card ^ 2 := by
    have hfib (r : ℝ) :
        T.filter (fun ee => dist ee.1.1 ee.1.2 = r) = (fiber r).product (fiber r) := by
      ext ee
      simp only [T, fiber, Finset.mem_filter, Finset.mem_product]
      aesop
    have hcover : T.filter (fun ee => dist ee.1.1 ee.1.2 ∈ D) = T := by
      apply Finset.filter_eq_self.mpr
      intro ee hee
      apply Finset.mem_image.mpr
      exact ⟨ee.1, (Finset.mem_product.mp (Finset.mem_filter.mp hee).1).1, rfl⟩
    have hs := Finset.sum_card_fiberwise_eq_card_filter T D
      (fun ee => dist ee.1.1 ee.1.2)
    rw [hcover] at hs
    rw [← hs]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hfib r]
    simp [pow_two]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq D (fun _ => (1 : ℕ))
    (fun r => (fiber r).card)
  have hNat : S.card ^ 2 ≤ D.card * T.card := by
    simpa only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one, hsum, ← hT] using hCS
  have hDset : D ⊆ distanceSet P := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨e, he, rfl⟩
    have heP := hS.1 he
    exact Finset.mem_image.mpr ⟨e, heP, rfl⟩
  have hD : D.card ≤ distinctDistances P := by
    simpa [distinctDistances] using Finset.card_le_card hDset
  have hReal : (S.card : ℝ) ^ 2 ≤ Mcount P * (T.card : ℝ) := by
    have hn : S.card ^ 2 ≤ distinctDistances P * T.card := le_trans hNat
      (Nat.mul_le_mul_right T.card hD)
    have hn' : (S.card : ℝ) ^ 2 ≤ (distinctDistances P : ℝ) * (T.card : ℝ) := by
      exact_mod_cast hn
    dsimp [Mcount]
    nlinarith [Nat.cast_nonneg (α := ℝ) T.card]
  have hTcard : (T.card : ℝ) ≤
      (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter fun xy =>
        EdAdj S (S.image (Prod.map R R)) xy.1 xy.2).card := by
    have hn : T.card ≤
        (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter fun xy =>
          EdAdj S (S.image (Prod.map R R)) xy.1 xy.2).card := by
      rw [← Finset.card_image_of_injective T hf]
      exact Finset.card_le_card hsub
    exact_mod_cast hn
  have hM : 0 < Mcount P := by unfold Mcount; positivity
  apply (div_le_iff₀ hM).mpr
  calc
    (S.card : ℝ) ^ 2 ≤ Mcount P * (T.card : ℝ) := hReal
    _ ≤ Mcount P * (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter fun xy =>
        EdAdj S (S.image (Prod.map R R)) xy.1 xy.2).card :=
      mul_le_mul_of_nonneg_left hTcard hM.le
    _ = (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter fun xy =>
        EdAdj S (S.image (Prod.map R R)) xy.1 xy.2).card * Mcount P := by ring

open Classical in
/-- Removing one vertex deletes at most twice its current degree in a symmetric directed relation. -/
private theorem edge_card_le_erase_add_two_degree {V : Type*} (U : Finset V)
    (adj : V → V → Prop) (hsymm : ∀ v w, adj v w → adj w v) {v : V} (hv : v ∈ U) :
    (((U ×ˢ U).filter fun e => adj e.1 e.2).card : ℕ) ≤
      (((U.erase v ×ˢ U.erase v).filter fun e => adj e.1 e.2).card : ℕ) +
        2 * (U.filter fun w => adj v w).card := by
  classical
  let edges := fun T : Finset V => (T ×ˢ T).filter fun e => adj e.1 e.2
  let out := U.filter fun w => adj v w
  let left := (edges U).filter fun e => e.1 = v
  let right := (edges U).filter fun e => e.2 = v
  have hleft : left = out.image fun w => (v, w) := by
    ext e
    rcases e with ⟨x, y⟩
    simp only [left, edges, out, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, hxy⟩, hxv⟩
      subst x
      exact ⟨y, ⟨hy, hxy⟩, rfl, rfl⟩
    · rintro ⟨w, ⟨hw, hvw⟩, hvx, hwy⟩
      subst x
      subst y
      exact ⟨⟨⟨hv, hw⟩, hvw⟩, rfl⟩
  have hright : right = out.image fun w => (w, v) := by
    ext e
    rcases e with ⟨x, y⟩
    simp only [right, edges, out, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, hxv⟩, hyv⟩
      subst y
      exact ⟨x, ⟨hx, hsymm x v hxv⟩, rfl, rfl⟩
    · rintro ⟨w, ⟨hw, hvw⟩, hwx, hvy⟩
      subst x
      subst y
      exact ⟨⟨⟨hw, hv⟩, hsymm v w hvw⟩, rfl⟩
  have hleftCard : left.card = out.card := by
    rw [hleft, Finset.card_image_of_injective]
    intro a b h
    exact congrArg Prod.snd h
  have hrightCard : right.card = out.card := by
    rw [hright, Finset.card_image_of_injective]
    intro a b h
    exact congrArg Prod.fst h
  have hcover : edges U ⊆ edges (U.erase v) ∪ (left ∪ right) := by
    intro e he
    rcases e with ⟨x, y⟩
    rcases Finset.mem_filter.mp he with ⟨heprod, hxy⟩
    rcases Finset.mem_product.mp heprod with ⟨hx, hy⟩
    by_cases hxv : x = v
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, hxv⟩
    by_cases hyv : y = v
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, hyv⟩
    · apply Finset.mem_union.mpr
      apply Or.inl
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_erase.mpr ⟨hxv, hx⟩, Finset.mem_erase.mpr ⟨hyv, hy⟩⟩, hxy⟩
  calc
    (edges U).card ≤ (edges (U.erase v) ∪ (left ∪ right)).card := Finset.card_le_card hcover
    _ ≤ (edges (U.erase v)).card + (left ∪ right).card := Finset.card_union_le _ _
    _ ≤ (edges (U.erase v)).card + (left.card + right.card) := by
      exact Nat.add_le_add_left (Finset.card_union_le left right) _
    _ = (edges (U.erase v)).card + 2 * out.card := by rw [hleftCard, hrightCard]; omega

open Classical in
/-- red:u-prune (`reduction.tex:296-304`), abstract form: in a symmetric graph on `W` with
`E > 0` ordered edges, repeatedly deleting vertices of degree below `E/(2|W|)` leaves a nonempty
vertex set of minimum degree at least `E/(2|W|)`. -/
theorem exists_minDegree_core {V : Type*} (W : Finset V) (adj : V → V → Prop)
    (hsymm : ∀ v w, adj v w → adj w v)
    (hE : 0 < ((W ×ˢ W).filter fun vw => adj vw.1 vw.2).card) :
    ∃ W' ⊆ W, W'.Nonempty ∧ ∀ v ∈ W',
      (((W ×ˢ W).filter fun vw => adj vw.1 vw.2).card : ℝ) / (2 * W.card) ≤
        ((W'.filter fun w => adj v w).card : ℝ) := by
  classical
  let edgeCount := fun U : Finset V => ((U ×ˢ U).filter fun e => adj e.1 e.2).card
  let threshold : ℝ := (edgeCount W : ℝ) / (2 * (W.card : ℝ))
  let score := fun U : Finset V => (edgeCount U : ℝ) - 2 * threshold * (U.card : ℝ)
  have hWnon : W.Nonempty := by
    have hEdges : ((W ×ˢ W).filter fun e => adj e.1 e.2).Nonempty := Finset.card_pos.mp hE
    rcases hEdges with ⟨e, he⟩
    exact ⟨e.1, (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1⟩
  have hWcard : 0 < W.card := hWnon.card_pos
  have hden : (2 * (W.card : ℝ)) ≠ 0 := ne_of_gt (by positivity)
  have hscoreW : score W = 0 := by
    dsimp [score, threshold]
    field_simp
    <;> ring
  have hscoreEmpty : score (∅ : Finset V) = 0 := by simp [score, edgeCount]
  obtain ⟨U, hUmem, hUmax⟩ := Finset.exists_max_image W.powerset score
    (Finset.powerset_nonempty W)
  have hUsub : U ⊆ W := Finset.mem_powerset.mp hUmem
  have hscoreU : 0 ≤ score U := by
    have h := hUmax W (Finset.mem_powerset_self W)
    rw [hscoreW] at h
    exact h
  have hstep {T : Finset V} {x : V} (hx : x ∈ T)
      (hdeg : ((T.filter fun y => adj x y).card : ℝ) < threshold) :
      score T < score (T.erase x) := by
    have hed := edge_card_le_erase_add_two_degree T adj hsymm hx
    have hed' : (edgeCount T : ℝ) ≤
        (edgeCount (T.erase x) : ℝ) + 2 * ((T.filter fun y => adj x y).card : ℝ) := by
      exact_mod_cast hed
    have hed'' : (edgeCount T : ℝ) <
        (edgeCount (T.erase x) : ℝ) + 2 * threshold := by
      nlinarith
    have hcard : (T.card : ℝ) = ((T.erase x).card : ℝ) + 1 := by
      exact_mod_cast (Finset.card_erase_add_one hx).symm
    dsimp [score]
    rw [hcard]
    nlinarith
  by_cases hUempty : U = ∅
  · refine ⟨W, Finset.Subset.rfl, hWnon, ?_⟩
    intro v hv
    by_contra hdeg
    have hlow : ((W.filter fun w => adj v w).card : ℝ) < threshold := lt_of_not_ge hdeg
    have hstrict := hstep hv hlow
    have hdelmax := hUmax (W.erase v) (Finset.mem_powerset.mpr (Finset.erase_subset _ _))
    rw [hUempty, hscoreEmpty] at hdelmax
    rw [hscoreW] at hstrict
    linarith
  · have hUnon : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUempty
    refine ⟨U, hUsub, hUnon, ?_⟩
    intro v hv
    by_contra hdeg
    have hlow : ((U.filter fun w => adj v w).card : ℝ) < threshold := lt_of_not_ge hdeg
    have hstrict := hstep hv hlow
    have hdelmax := hUmax (U.erase v)
      (Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.erase_subset _ _) hUsub))
    linarith

private theorem edAdj_symm (P : Finset (RPoint d)) (S : Finset (RPoint d × RPoint d))
    (hS : IsSymmSelection P S) (R : RPoint d ≃ₗᵢ[ℝ] RPoint d)
    {x y : RPoint d × RPoint d}
    (hxy : EdAdj S (S.image (Prod.map R R)) x y) :
    EdAdj S (S.image (Prod.map R R)) y x := by
  rcases hxy with ⟨h₁, h₂, hdist⟩
  have hdist' : dist y.1 x.1 = dist y.2 x.2 := by
    calc
      dist y.1 x.1 = dist x.1 y.1 := dist_comm _ _
      _ = dist x.2 y.2 := hdist
      _ = dist y.2 x.2 := dist_comm _ _
  refine ⟨hS.2 _ h₁, ?_, hdist'⟩
  rcases Finset.mem_image.mp h₂ with ⟨e, he, hxy'⟩
  apply Finset.mem_image.mpr
  refine ⟨e.swap, hS.2 e he, ?_⟩
  simpa [Prod.map] using congrArg Prod.swap hxy'

open Classical in
private theorem exists_retained_core_degree (P : Finset (RPoint d))
    (R : RPoint d ≃ₗᵢ[ℝ] RPoint d) (adj : (RPoint d × RPoint d) → (RPoint d × RPoint d) → Prop)
    (hsymm : ∀ x y, adj x y → adj y x) (c : ℝ) (hc : 0 < c) (hN2 : 0 < P.card)
    (hE : (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P ≤
      (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter
        (fun xy : (RPoint d × RPoint d) × (RPoint d × RPoint d) => adj xy.1 xy.2)).card) :
    ∃ W ⊆ P ×ˢ P.image R, W.Nonempty ∧
      ∀ x ∈ W, (c ^ 2 / 4) * (P.card : ℝ) ^ 2 / Mcount P ≤
        ((W.filter fun y => adj x y).card : ℝ) := by
  classical
  let V := P ×ˢ P.image R
  let E := (V ×ˢ V).filter fun xy => adj xy.1 xy.2
  have hM : 0 < Mcount P := by
    unfold Mcount
    positivity
  have hN : 0 < (P.card : ℝ) := by exact_mod_cast hN2
  have hVcard : (V.card : ℝ) = (P.card : ℝ) ^ 2 := by
    simp [V, Finset.card_product, Finset.card_image_of_injective _ R.injective]
    <;> ring
  have hEposR : 0 < (E.card : ℝ) := by
    have hbase : 0 < (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P := by positivity
    have hle : (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P ≤ (E.card : ℝ) := by
      simpa [V, E] using hE
    exact lt_of_lt_of_le hbase hle
  have hEpos : 0 < E.card := by exact_mod_cast hEposR
  obtain ⟨W, hWsub, hWnon, hdegree⟩ :=
    exists_minDegree_core V adj hsymm hEpos
  refine ⟨W, ?_, hWnon, ?_⟩
  · simpa [V] using hWsub
  · intro x hx
    have hden : 0 < 2 * (V.card : ℝ) := by rw [hVcard]; positivity
    have hdiv := div_le_div_of_nonneg_right hE (le_of_lt hden)
    have hcalc : ((c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P) /
        (2 * (V.card : ℝ)) = (c ^ 2 / 4) * (P.card : ℝ) ^ 2 / Mcount P := by
      rw [hVcard]
      field_simp [hM.ne', hN.ne']
      <;> ring
    have hdegree' := hdegree x hx
    change ((E.card : ℝ) / (2 * (V.card : ℝ))) ≤
      ((W.filter fun y => adj x y).card : ℝ) at hdegree'
    rw [← hcalc]
    exact le_trans hdiv hdegree'

private theorem exists_good_graph_rotation (hd : 2 ≤ d)
    (P : Finset (RPoint d)) (S : Finset (RPoint d × RPoint d))
    (hS : IsSymmSelection P S) :
    ∃ R : RPoint d ≃ₗᵢ[ℝ] RPoint d, ∀ x y,
      EdAdj S (S.image (Prod.map R R)) x y →
        (y.1 - x.1) + (y.2 - x.2) ≠ 0 := by
  classical
  let X := (S ×ˢ S).image fun z : (RPoint d × RPoint d) × (RPoint d × RPoint d) =>
    (z.2.2 - z.2.1, z.1.2 - z.1.1)
  have hX : ∀ e ∈ X, e.1 ≠ 0 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨z, hz, rfl⟩
    have hz₂ : z.2 ∈ S := (Finset.mem_product.mp hz).2
    have hne := (Finset.mem_offDiag.mp (hS.1 hz₂)).2.2
    intro hzero
    apply hne
    exact (sub_eq_zero.mp hzero).symm
  obtain ⟨R, hrotate⟩ := exists_linearIsometryEquiv_add_ne_zero hd X hX
  refine ⟨R, ?_⟩
  intro x y hadj
  rcases hadj with ⟨hxy, hxyR, _⟩
  rcases Finset.mem_image.mp hxyR with ⟨q, hq, hqxy⟩
  have hXin : (q.2 - q.1, y.1 - x.1) ∈ X := by
    apply Finset.mem_image.mpr
    refine ⟨((x.1, y.1), q), Finset.mem_product.mpr ⟨hxy, hq⟩, ?_⟩
    rfl
  have hrotate' := hrotate (q.2 - q.1, y.1 - x.1) hXin
  have hx : x.2 = R q.1 := by simpa using (congrArg Prod.fst hqxy).symm
  have hy : y.2 = R q.2 := by simpa using (congrArg Prod.snd hqxy).symm
  have hdiff : y.2 - x.2 = R (q.2 - q.1) := by
    rw [hy, hx, map_sub]
  intro hzero
  apply hrotate'
  rw [← hdiff]
  simpa [add_comm] using hzero

open Classical in
private theorem good_graph_edge_count_lower (P : Finset (RPoint d))
    (S : Finset (RPoint d × RPoint d)) (c : ℝ) (hc : 0 < c)
    (hS : IsSymmSelection P S) (hSc : c * (P.card : ℝ) ^ 2 ≤ S.card)
    (R : RPoint d ≃ₗᵢ[ℝ] RPoint d) :
    c ^ 2 * (P.card : ℝ) ^ 4 / Mcount P ≤
      (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter
        (fun xy : (RPoint d × RPoint d) × (RPoint d × RPoint d) =>
          EdAdj S (S.image (Prod.map R R)) xy.1 xy.2)).card := by
  have hM : 0 < Mcount P := by
    unfold Mcount
    positivity
  have hN : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hS0 : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hlow0 : 0 ≤ c * (P.card : ℝ) ^ 2 := mul_nonneg hc.le (sq_nonneg _)
  have hSsq : (c * (P.card : ℝ) ^ 2) ^ 2 ≤ (S.card : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((S.card : ℝ) - c * (P.card : ℝ) ^ 2)]
  have hdiv : c ^ 2 * (P.card : ℝ) ^ 4 / Mcount P ≤
      (S.card : ℝ) ^ 2 / Mcount P := by
    convert div_le_div_of_nonneg_right hSsq (le_of_lt hM) using 1 <;> ring
  exact hdiv.trans (card_edAdj_ge P S hS R)

open Classical in
/-- red:u-graph + red:u-rotation + red:u-motions + red:u-prune (`reduction.tex:251-306`): from
a symmetric selection with `c N^2` pairs, a generic rotation `R` and a nonempty retained vertex
set `W ⊆ P × RP` with an adjacency inside the equal-distance graph such that
* neighbour displacements satisfy `u + w ≠ 0`;
* the minimum degree is at least `c₃ N^2/M`;
* (isotropic cap) for each vertex and each `T ∈ O(d)`, at most `C₀ A^{d-2}` neighbours
  `(p',q')` of `(p,q)` satisfy `q' - q = T(p' - p)`: for `d ≥ 4` because `N ≤ A^{d-2}`, for
  `d = 3` after deleting the edges matched by very rich motions (`mot:rich`). -/
theorem exists_retained_graph (hd : 3 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∃ c₃ C₀ ε₁ : ℝ, 0 < c₃ ∧ 0 < C₀ ∧ 0 < ε₁ ∧
      ∀ (P : Finset (RPoint d)) (S : Finset (RPoint d × RPoint d)), IsSymmSelection P S →
        2 ≤ P.card → c * (P.card : ℝ) ^ 2 ≤ S.card → Mcount P ≤ ε₁ * Ascale d P.card →
        ∃ (R : RPoint d ≃ₗᵢ[ℝ] RPoint d) (W : Finset (RPoint d × RPoint d))
          (adj : RPoint d × RPoint d → RPoint d × RPoint d → Prop),
          W ⊆ P ×ˢ P.image R ∧ W.Nonempty ∧
          (∀ x y, adj x y →
            EdAdj S (S.image (Prod.map R R)) x y ∧ (y.1 - x.1) + (y.2 - x.2) ≠ 0) ∧
          (∀ x ∈ W, c₃ * (P.card : ℝ) ^ 2 / Mcount P ≤ ((W.filter fun y => adj x y).card : ℝ)) ∧
          (∀ x ∈ W, ∀ T : RPoint d ≃ₗᵢ[ℝ] RPoint d,
            ((W.filter fun y => adj x y ∧ y.2 - x.2 = T (y.1 - x.1)).card : ℝ) ≤
              C₀ * Ascale d P.card ^ (d - 2)) := by
  classical
  by_cases hd3 : d = 3
  · subst d
    obtain ⟨Crich, Krich, hCrich, hKrich, hRich⟩ := Request.richMotions
    let ε₁ : ℝ := min 1 (c ^ 2 / (2 * Krich))
    refine ⟨c ^ 2 / 4, Crich, ε₁, by positivity, hCrich, by positivity, ?_⟩
    intro P S hS hN2 hSc hMsmall
    have hNpos : 0 < (P.card : ℝ) := by exact_mod_cast (show 0 < P.card by omega)
    have hNone : 1 ≤ (P.card : ℝ) := by exact_mod_cast (show 1 ≤ P.card by omega)
    have hAone : 1 ≤ Ascale 3 P.card := by
      unfold Ascale
      exact Real.one_le_rpow hNone (by norm_num)
    have hApos : 0 < Ascale 3 P.card := lt_of_lt_of_le zero_lt_one hAone
    have hMpos : 0 < Mcount P := by
      unfold Mcount
      positivity
    have hεone : ε₁ ≤ 1 := min_le_left _ _
    have hεK : ε₁ ≤ c ^ 2 / (2 * Krich) := min_le_right _ _
    have hMleA : Mcount P ≤ Ascale 3 P.card := by
      calc
        Mcount P ≤ ε₁ * Ascale 3 P.card := hMsmall
        _ ≤ 1 * Ascale 3 P.card :=
          mul_le_mul_of_nonneg_right hεone hApos.le
        _ = Ascale 3 P.card := one_mul _
    obtain ⟨R, hrotate⟩ := exists_good_graph_rotation (by omega) P S hS
    have hEbase := good_graph_edge_count_lower P S c hc hS hSc R
    let V := P ×ˢ P.image R
    let E₀ := (V ×ˢ V).filter fun xy => EdAdj S (S.image (Prod.map R R)) xy.1 xy.2
    have hE₀ : c ^ 2 * (P.card : ℝ) ^ 4 / Mcount P ≤ (E₀.card : ℝ) := by
      simpa [E₀, V] using hEbase
    obtain ⟨G, hRichCover, hRichSum⟩ := hRich P R (by omega) hMleA
    let matchPts := fun g : RPoint 3 ≃ᵃⁱ[ℝ] RPoint 3 =>
      P.filter fun p => g p ∈ P.image R
    let matchVerts := fun g : RPoint 3 ≃ᵃⁱ[ℝ] RPoint 3 =>
      (matchPts g).image fun p => (p, g p)
    let removed := G.biUnion fun g => matchVerts g ×ˢ matchVerts g
    let adj : (RPoint 3 × RPoint 3) → (RPoint 3 × RPoint 3) → Prop := fun x y =>
      EdAdj S (S.image (Prod.map R R)) x y ∧ (x, y) ∉ removed
    let E := E₀.filter fun e => e ∉ removed
    let adj : (RPoint 3 × RPoint 3) → (RPoint 3 × RPoint 3) → Prop := fun x y =>
      (x, y) ∈ E
    have hmatchVertsCard (g : RPoint 3 ≃ᵃⁱ[ℝ] RPoint 3) :
        (matchVerts g).card = (matchPts g).card := by
      dsimp [matchVerts]
      rw [Finset.card_image_of_injective]
      intro p q hpq
      exact congrArg Prod.fst hpq
    have hremovedNat : removed.card ≤ ∑ g ∈ G, (matchPts g).card ^ 2 := by
      calc
        removed.card ≤ ∑ g ∈ G, (matchVerts g ×ˢ matchVerts g).card :=
          Finset.card_biUnion_le
        _ = ∑ g ∈ G, (matchPts g).card ^ 2 := by
          apply Finset.sum_congr rfl
          intro g hg
          rw [Finset.card_product, hmatchVertsCard, pow_two]
    have hremoved : (removed.card : ℝ) ≤
        ∑ g ∈ G, ((matchPts g).card : ℝ) ^ 2 := by
      exact_mod_cast hremovedNat
    have hremovedBound : (removed.card : ℝ) ≤
        Krich * (P.card : ℝ) ^ 4 / Ascale 3 P.card := hremoved.trans hRichSum
    have hKm : Krich * Mcount P ≤ (c ^ 2 / 2) * Ascale 3 P.card := by
      calc
        Krich * Mcount P ≤ Krich * (ε₁ * Ascale 3 P.card) :=
          mul_le_mul_of_nonneg_left hMsmall hKrich.le
        _ = (Krich * ε₁) * Ascale 3 P.card := by ring
        _ ≤ (c ^ 2 / 2) * Ascale 3 P.card := by
          apply mul_le_mul_of_nonneg_right ?_ hApos.le
          calc
            Krich * ε₁ ≤ Krich * (c ^ 2 / (2 * Krich)) :=
              mul_le_mul_of_nonneg_left hεK hKrich.le
            _ = c ^ 2 / 2 := by field_simp [hKrich.ne']
    have hKdiv : Krich / Ascale 3 P.card ≤ (c ^ 2 / 2) / Mcount P := by
      apply (div_le_div_iff₀ hApos hMpos).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hKm
    have hremovedSmall : (removed.card : ℝ) ≤
        (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P := by
      calc
        (removed.card : ℝ) ≤ Krich * (P.card : ℝ) ^ 4 / Ascale 3 P.card := hremovedBound
        _ = (Krich / Ascale 3 P.card) * (P.card : ℝ) ^ 4 := by ring
        _ ≤ ((c ^ 2 / 2) / Mcount P) * (P.card : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right hKdiv (by positivity)
        _ = (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P := by ring
    have hcover : E₀ ⊆ E ∪ removed := by
      intro e he
      by_cases hbad : e ∈ removed
      · exact Finset.mem_union.mpr (Or.inr hbad)
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_filter.mpr
        exact ⟨he, hbad⟩
    have hE₀cover : (E₀.card : ℝ) ≤ (E.card : ℝ) + (removed.card : ℝ) := by
      have hnat : E₀.card ≤ E.card + removed.card :=
        (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
      exact_mod_cast hnat
    have hE : (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P ≤ (E.card : ℝ) := by
      have hfull : c ^ 2 * (P.card : ℝ) ^ 4 / Mcount P =
          2 * ((c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P) := by ring
      have hbaseHalf : 2 * ((c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P) ≤
          (E₀.card : ℝ) := by rw [← hfull]; exact hE₀
      linarith
    have hadjSymm : ∀ x y, adj x y → adj y x := by
      intro x y hxy
      change (x, y) ∈ E at hxy
      rcases Finset.mem_filter.mp hxy with ⟨hxy₀, hnot⟩
      rcases Finset.mem_filter.mp hxy₀ with ⟨hprod, hEdj⟩
      have hprod' : (y, x) ∈ V ×ˢ V := by
        rcases Finset.mem_product.mp hprod with ⟨hxV, hyV⟩
        exact Finset.mem_product.mpr ⟨hyV, hxV⟩
      have hEdj' := edAdj_symm P S hS R hEdj
      have hxy₀' : (y, x) ∈ E₀ := Finset.mem_filter.mpr ⟨hprod', hEdj'⟩
      have hnot' : (y, x) ∉ removed := by
        intro hrev
        rcases Finset.mem_biUnion.mp hrev with ⟨g, hg, hpair⟩
        rcases Finset.mem_product.mp hpair with ⟨hy, hx⟩
        apply hnot
        change (x, y) ∈ G.biUnion (fun g => matchVerts g ×ˢ matchVerts g)
        exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_product.mpr ⟨hx, hy⟩⟩
      exact Finset.mem_filter.mpr ⟨hxy₀', hnot'⟩
    have hEposR : 0 < (E.card : ℝ) := by
      have hbase : 0 < (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P := by positivity
      exact lt_of_lt_of_le hbase hE
    have hEpos : 0 < E.card := by exact_mod_cast hEposR
    have hEhelper : (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P ≤
        (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter fun xy =>
          adj xy.1 xy.2).card := by
      have hEq : (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter fun xy =>
          adj xy.1 xy.2) = E := by
        ext e
        constructor
        · intro he
          exact (Finset.mem_filter.mp he).2
        · intro he
          have he₀ := (Finset.mem_filter.mp he).1
          have hprodV := (Finset.mem_filter.mp he₀).1
          have hprod : e ∈ (P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R) := by
            simpa [V] using hprodV
          exact Finset.mem_filter.mpr ⟨hprod, he⟩
      rw [hEq]
      exact hE
    obtain ⟨W, hWsub, hWnon, hdegree⟩ :=
      exists_retained_core_degree P R adj hadjSymm c hc (by omega) hEhelper
    refine ⟨R, W, adj, hWsub, hWnon, ?_, ?_, ?_⟩
    · intro x y hxy
      change (x, y) ∈ E at hxy
      rcases Finset.mem_filter.mp hxy with ⟨hxy₀, _⟩
      rcases Finset.mem_filter.mp hxy₀ with ⟨_, hEdj⟩
      exact ⟨hEdj, hrotate x y hEdj⟩
    · intro x hx
      change (c ^ 2 / 4) * (P.card : ℝ) ^ 2 / Mcount P ≤
        ((W.filter fun y => adj x y).card : ℝ)
      exact hdegree x hx
    · intro x hx T
      let L := W.filter fun y => adj x y ∧ y.2 - x.2 = T (y.1 - x.1)
      let b := x.2 - T x.1
      let g : RPoint 3 ≃ᵃⁱ[ℝ] RPoint 3 :=
        AffineIsometryEquiv.mk' (fun z => T z + b) T b (by intro z; simp; abel)
      have hgx : g x.1 = x.2 := by
        dsimp [g, b]
        simp
      have hgy (y : RPoint 3 × RPoint 3) (hy : y ∈ L) : g y.1 = y.2 := by
        have hrel := (Finset.mem_filter.mp hy).2.2
        dsimp [g, b]
        calc
          T y.1 + (x.2 - T x.1) = T (y.1 - x.1) + x.2 := by rw [map_sub]; abel
          _ = (y.2 - x.2) + x.2 := by rw [hrel]
          _ = y.2 := by abel
      have hcard : L.card ≤ (matchPts g).card := by
        let f : {y : RPoint 3 × RPoint 3 // y ∈ L} → {p : RPoint 3 // p ∈ matchPts g} :=
          fun y => ⟨y.1.1, by
            have hyW := (Finset.mem_filter.mp y.2).1
            have hyV := hWsub hyW
            rcases Finset.mem_product.mp hyV with ⟨hyP, hyQ⟩
            apply Finset.mem_filter.mpr
            exact ⟨hyP, by rw [hgy y.1 y.2]; exact hyQ⟩⟩
        have hf : Function.Injective f := by
          intro y z heq
          apply Subtype.ext
          have hfst : y.1.1 = z.1.1 := congrArg Subtype.val heq
          apply Prod.ext hfst
          calc
            y.1.2 = g y.1.1 := (hgy y.1 y.2).symm
            _ = g z.1.1 := by rw [hfst]
            _ = z.1.2 := hgy z.1 z.2
        have hcard' := Fintype.card_le_of_injective f hf
        simpa [f] using hcard'
      have hcardR : (L.card : ℝ) ≤ (matchPts g).card := by exact_mod_cast hcard
      by_cases hlarge : Crich * Ascale 3 P.card ≤ (matchPts g).card
      · have hgG : g ∈ G := hRichCover g hlarge
        have hLempty : L = ∅ := by
          by_contra hne
          obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          have hyAdj := (Finset.mem_filter.mp hy).2.1
          change (x, y) ∈ E at hyAdj
          have hyNotRemoved := (Finset.mem_filter.mp hyAdj).2
          have hxV := hWsub hx
          rcases Finset.mem_product.mp hxV with ⟨hxP, hxQ⟩
          have hxMatch : x.1 ∈ matchPts g := by
            apply Finset.mem_filter.mpr
            exact ⟨hxP, by rw [hgx]; exact hxQ⟩
          have hyW := (Finset.mem_filter.mp hy).1
          have hyV := hWsub hyW
          rcases Finset.mem_product.mp hyV with ⟨hyP, hyQ⟩
          have hyMatch : y.1 ∈ matchPts g := by
            apply Finset.mem_filter.mpr
            exact ⟨hyP, by rw [hgy y hy]; exact hyQ⟩
          have hxVert : x ∈ matchVerts g := by
            apply Finset.mem_image.mpr
            refine ⟨x.1, hxMatch, ?_⟩
            exact Prod.ext rfl hgx
          have hyVert : y ∈ matchVerts g := by
            apply Finset.mem_image.mpr
            refine ⟨y.1, hyMatch, ?_⟩
            exact Prod.ext rfl (hgy y hy)
          have hremovedxy : (x, y) ∈ removed := by
            change (x, y) ∈ G.biUnion (fun g => matchVerts g ×ˢ matchVerts g)
            exact Finset.mem_biUnion.mpr ⟨g, hgG, Finset.mem_product.mpr ⟨hxVert, hyVert⟩⟩
          exact hyNotRemoved hremovedxy
        have hLcard : L.card = 0 := by rw [hLempty]; simp
        have hcap : (L.card : ℝ) ≤ Crich * Ascale 3 P.card ^ (3 - 2) := by
          simpa [hLcard] using (le_of_lt (mul_pos hCrich hApos))
        simpa [L] using hcap
      · have hsmall : (matchPts g).card < Crich * Ascale 3 P.card := lt_of_not_ge hlarge
        have hcap : (L.card : ℝ) ≤ Crich * Ascale 3 P.card :=
          hcardR.trans hsmall.le
        simpa [L] using hcap
  · have hd4 : 4 ≤ d := by omega
    refine ⟨c ^ 2 / 4, 1, 1, by positivity, by norm_num, by norm_num, ?_⟩
    intro P S hS hN2 hSc _hMsmall
    have hNpos : 0 < (P.card : ℝ) := by exact_mod_cast (show 0 < P.card by omega)
    have hNone : 1 ≤ (P.card : ℝ) := by exact_mod_cast (show 1 ≤ P.card by omega)
    obtain ⟨R, hrotate⟩ := exists_good_graph_rotation (by omega) P S hS
    let adj : (RPoint d × RPoint d) → (RPoint d × RPoint d) → Prop :=
      EdAdj S (S.image (Prod.map R R))
    have hadjSymm : ∀ x y, adj x y → adj y x := by
      intro x y hxy
      exact edAdj_symm P S hS R hxy
    have hEbase := good_graph_edge_count_lower P S c hc hS hSc R
    have hMposBase : 0 < Mcount P := by unfold Mcount; positivity
    have hEhalf : (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P ≤
        (((P ×ˢ P.image R) ×ˢ (P ×ˢ P.image R)).filter fun xy => adj xy.1 xy.2).card := by
      have hle : (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P ≤
          c ^ 2 * (P.card : ℝ) ^ 4 / Mcount P := by
        calc
          (c ^ 2 / 2) * (P.card : ℝ) ^ 4 / Mcount P =
              (c ^ 2 * (P.card : ℝ) ^ 4 / Mcount P) / 2 := by ring
          _ ≤ c ^ 2 * (P.card : ℝ) ^ 4 / Mcount P := by
            apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
            nlinarith [show 0 ≤ c ^ 2 * (P.card : ℝ) ^ 4 / Mcount P by positivity]
      exact hle.trans hEbase
    obtain ⟨W, hWsub, hWnon, hdegree⟩ :=
      exists_retained_core_degree P R adj hadjSymm c hc (by omega) hEhalf
    have hNleA : (P.card : ℝ) ≤ Ascale d P.card ^ (d - 2) := by
      have hExponent : (1 : ℝ) ≤ ((2 : ℝ) / (d : ℝ)) * ((d - 2 : ℕ) : ℝ) := by
        have hdreal : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd4
        have hdpos : 0 < (d : ℝ) := by positivity
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hdpos).2
        have hsub : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ d)]
          norm_num
        rw [hsub]
        nlinarith
      have hpow : Ascale d P.card ^ (d - 2) =
          (P.card : ℝ) ^ (((2 : ℝ) / (d : ℝ)) * ((d - 2 : ℕ) : ℝ)) := by
        unfold Ascale
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg P.card)]
      calc
        (P.card : ℝ) = (P.card : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ (P.card : ℝ) ^ (((2 : ℝ) / (d : ℝ)) * ((d - 2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hNone hExponent
        _ = Ascale d P.card ^ (d - 2) := hpow.symm
    refine ⟨R, W, adj, hWsub, hWnon, ?_, ?_, ?_⟩
    · intro x y hxy
      exact ⟨hxy, hrotate x y hxy⟩
    · intro x hx
      exact hdegree x hx
    · intro x hx T
      let L := W.filter fun y => adj x y ∧ y.2 - x.2 = T (y.1 - x.1)
      have hcard : L.card ≤ P.card := by
        let f : {y : RPoint d × RPoint d // y ∈ L} → {p : RPoint d // p ∈ P} :=
          fun y => ⟨y.1.1, by
            have hyW := (Finset.mem_filter.mp y.2).1
            exact (Finset.mem_product.mp (hWsub hyW)).1⟩
        have hf : Function.Injective f := by
          intro y z heq
          apply Subtype.ext
          have hfst : y.1.1 = z.1.1 := congrArg Subtype.val heq
          apply Prod.ext hfst
          have hyrel := (Finset.mem_filter.mp y.2).2.2
          have hzrel := (Finset.mem_filter.mp z.2).2.2
          rw [hfst] at hyrel
          calc
            y.1.2 = (y.1.2 - x.2) + x.2 := by abel
            _ = (z.1.2 - x.2) + x.2 := by rw [hyrel, hzrel]
            _ = z.1.2 := by abel
        have hcard' := Fintype.card_le_of_injective f hf
        simpa [f] using hcard'
      have hcardR : (L.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hcard
      simpa [L] using hcardR.trans hNleA

end Reduction

end

end DistinctDistances
