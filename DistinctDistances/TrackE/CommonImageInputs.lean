import DistinctDistances.TrackE.CommonImageData

/-! Page-sized coordinate and closed-image inputs, sparse-cones.tex:143–188,
239–261. Nonempty denominator domains remain explicit. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Every actual chart label lies in the complete image of its own carriers. -/
theorem common_product_label_mem (i₀ : Fin d) (X Y : AffineVariety d)
    (x y : Point d) (hx : x ∈ X) (hy : y ∈ Y) (hi : (y - x) i₀ ≠ 0) :
    TrackD.productPoint x (TrackD.dirChart (LinearMap.proj i₀) (y - x)) ∈
      commonProductImage i₀ X Y := by
  have hmem : TrackD.productPoint x y ∈ TrackD.productVariety X Y :=
    AffineVariety.subset_closure _ ⟨x, hx, y, hy, rfl⟩
  have hden : MvPolynomial.eval (TrackD.productPoint x y)
      (TrackD.secantChartDenominator i₀) ≠ 0 := by
    rw [TrackD.eval_secantChartDenominator]
    exact hi
  have h := TrackD.rationalPoint_mem_image (TrackD.productVariety X Y)
    (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀)
    (TrackD.productPoint x y) hmem hden
  rw [TrackD.rational_secant_label i₀ x y hi] at h
  exact h

/-- The first-coordinate polynomial evaluates at the original source point. -/
theorem eval_common_source_polynomial (f : Poly d) (x v : Point d) :
    MvPolynomial.eval (TrackD.productPoint x v) (commonSourcePolynomial f) =
      MvPolynomial.eval x f := by
  simpa only [commonSourcePolynomial] using TrackD.eval_product_left_rename f x v

/-- Transport of equations preserves evaluation at the literal normalized label. -/
theorem eval_common_pair_equation (i₀ : Fin d) (x y : Point d) (G : TrackD.PairPoly d) :
    MvPolynomial.eval (TrackD.productPoint x
      (TrackD.dirChart (LinearMap.proj i₀) (y - x))) (commonPairEquation G) =
        MvPolynomial.eval (TrackD.labelPt i₀ x y) G := by
  unfold commonPairEquation
  rw [MvPolynomial.eval_rename]
  have hfun : (TrackD.productPoint x
      (TrackD.dirChart (LinearMap.proj i₀) (y - x)) ∘ finSumFinEquiv) =
      TrackD.labelPt i₀ x y := by
    funext j
    cases j with
    | inl k =>
      simp only [Function.comp_apply, TrackD.productPoint, Function.comp_apply,
        Equiv.symm_apply_apply, TrackD.labelPt, TrackD.pairPt, Sum.elim_inl]
    | inr k =>
      simp only [Function.comp_apply, TrackD.productPoint, Function.comp_apply,
        Equiv.symm_apply_apply, TrackD.labelPt, TrackD.pairPt, Sum.elim_inr,
        TrackD.dirChart, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]

/-- Closed-image equations are exactly the equations vanishing on every
complete product pair in the denominator chart, including empty domains. -/
theorem common_product_image_equation_iff (i₀ : Fin d) (X Y : AffineVariety d)
    (G : TrackD.PairPoly d) :
    commonPairEquation G ∈ (commonProductImage i₀ X Y).ideal ↔
      ∀ x ∈ X, ∀ y ∈ Y, (y - x) i₀ ≠ 0 →
        MvPolynomial.eval (TrackD.labelPt i₀ x y) G = 0 := by
  constructor
  · intro h x hx y hy hi
    have hvan := (TrackD.mem_ideal_iff_eval_zero _ _).mp h
    have hlabel := common_product_label_mem i₀ X Y x y hx hy hi
    have hz := hvan _ hlabel
    rwa [eval_common_pair_equation] at hz
  · intro h
    intro z hz
    obtain ⟨p, hp, hg, rfl⟩ := hz
    have hxy : TrackD.productLeft p ∈ X ∧ TrackD.productRight p ∈ Y := by
      have hpts : p ∈ (TrackD.productVariety X Y).points := hp
      rwa [TrackD.productVariety_points] at hpts
    have hp_eq : TrackD.productPoint (TrackD.productLeft p)
        (TrackD.productRight p) = p :=
      TrackD.productPoint_left_right p
    have hi : ((TrackD.productRight p) - (TrackD.productLeft p)) i₀ ≠ 0 := by
      have he : MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 := hg
      rw [← hp_eq] at he
      simpa only [TrackD.eval_secantChartDenominator] using he
    have hG := h _ hxy.1 _ hxy.2 hi
    have hrat : TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p =
        TrackD.productPoint (TrackD.productLeft p)
          (TrackD.dirChart (LinearMap.proj i₀)
            ((TrackD.productRight p) - (TrackD.productLeft p))) := by
      conv_lhs => rw [← hp_eq]
      exact TrackD.rational_secant_label i₀ _ _ hi
    change MvPolynomial.eval (TrackD.rationalPoint
      (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀)
      p) (commonPairEquation G) = 0
    rw [hrat, eval_common_pair_equation]
    exact hG

/-- A nonempty chart domain is a nonempty principal open of the product. -/
theorem common_product_chart_general (i₀ : Fin d) (X Y : AffineVariety d)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    TrackD.ForGeneralPair X Y (fun x y => (y - x) i₀ ≠ 0) := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hi₀⟩ := hchart
  refine ⟨MvPolynomial.rename finSumFinEquiv.symm
    (TrackD.secantChartDenominator i₀), ⟨x₀, hx₀, y₀, hy₀, ?_⟩, ?_⟩
  · have he : MvPolynomial.eval (TrackD.pairPt x₀ y₀)
        (MvPolynomial.rename finSumFinEquiv.symm
          (TrackD.secantChartDenominator i₀)) = (y₀ - x₀) i₀ := by
      rw [TrackD.eval_product_rename, TrackD.eval_secantChartDenominator]
    rw [he]
    exact hi₀
  · intro x hx y hy hn
    have he : MvPolynomial.eval (TrackD.pairPt x y)
        (MvPolynomial.rename finSumFinEquiv.symm
          (TrackD.secantChartDenominator i₀)) = (y - x) i₀ := by
      rw [TrackD.eval_product_rename, TrackD.eval_secantChartDenominator]
    rw [he] at hn
    exact hn

/-- The literal secant denominator is proper on a nonempty product chart. -/
theorem common_image_domain_not_mem (i₀ : Fin d) (X Y : AffineVariety d)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    TrackD.secantChartDenominator i₀ ∉ (TrackD.productVariety X Y).ideal := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hi₀⟩ := hchart
  intro hcon
  have hmem : TrackD.productPoint x₀ y₀ ∈ TrackD.productVariety X Y :=
    AffineVariety.subset_closure _ ⟨x₀, hx₀, y₀, hy₀, rfl⟩
  have hz := (TrackD.mem_ideal_iff_eval_zero _ _).mp hcon _ hmem
  have he : MvPolynomial.eval (TrackD.productPoint x₀ y₀)
      (TrackD.secantChartDenominator i₀) = (y₀ - x₀) i₀ :=
    TrackD.eval_secantChartDenominator _ _ _
  rw [he] at hz
  exact hi₀ hz

end
end DistinctDistances.SparseCones
