import DistinctDistances.TrackE.CommonImageData
import DistinctDistances.TrackE.CommonImageInputs
import DistinctDistances.TrackE.MELabelAux

/-! The label cylinder `X × {v : v_{i₀} = 1}` of a source carrier, the complete
image of a hypersurface pair on the first plateau (sparse-cones.tex:282–295). -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- `X × {v : v_{i₀} = 1}` in the shared label coordinates `Fin (d + d)`. -/
def commonLabelCylinder (i₀ : Fin d) (X : AffineVariety d) : AffineVariety (d + d) :=
  AffineVariety.ofIdeal (Ideal.span (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
    {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1}))

/-- Points of the label cylinder. -/
theorem commonLabelCylinder_points (i₀ : Fin d) (X : AffineVariety d)
    (x v : Point d) :
    TrackD.productPoint x v ∈ commonLabelCylinder i₀ X ↔ x ∈ X ∧ v i₀ = 1 := by
  show TrackD.productPoint x v ∈ (commonLabelCylinder i₀ X).points ↔ _
  unfold commonLabelCylinder
  rw [AffineVariety.points_ofIdeal, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h
    have hsrc : ∀ f ∈ X.ideal, MvPolynomial.eval x f = 0 := by
      intro f hf
      have hmem : commonSourcePolynomial f ∈ Ideal.span
          (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
            {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1}) :=
        Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩)
      have hz := h _ hmem
      rw [MvPolynomial.aeval_eq_eval, eval_common_source_polynomial] at hz
      exact hz
    have hfix : v i₀ = 1 := by
      have hmem : MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1 ∈ Ideal.span
          (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
            {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1}) :=
        Ideal.subset_span (Or.inr rfl)
      have hz := h _ hmem
      rw [MvPolynomial.aeval_eq_eval, cyl_eval_fixed] at hz
      exact sub_eq_zero.mp hz
    have hx : x ∈ X := by
      show x ∈ MvPolynomial.zeroLocus ℂ X.ideal
      rw [MvPolynomial.mem_zeroLocus_iff]
      intro f hf
      rw [MvPolynomial.aeval_eq_eval]
      exact hsrc f hf
    exact ⟨hx, hfix⟩
  · rintro ⟨hx, hv⟩
    have hx' : ∀ f ∈ X.ideal, (MvPolynomial.aeval (TrackD.productPoint x v))
        (commonSourcePolynomial f) = 0 := by
      intro f hf
      have hfx : x ∈ MvPolynomial.zeroLocus ℂ X.ideal := hx
      have hz := (MvPolynomial.mem_zeroLocus_iff).mp hfx f hf
      rw [MvPolynomial.aeval_eq_eval, eval_common_source_polynomial]
      rw [MvPolynomial.aeval_eq_eval] at hz
      exact hz
    have hfix' : (MvPolynomial.aeval (TrackD.productPoint x v))
        ((MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1 : Poly (d + d))) = 0 := by
      rw [MvPolynomial.aeval_eq_eval, cyl_eval_fixed, hv, sub_self]
    intro g hg
    have hle : Ideal.span (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
        {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1}) ≤
        RingHom.ker (MvPolynomial.aeval (TrackD.productPoint x v)).toRingHom := by
      rw [Ideal.span_le]
      intro g hg
      show (MvPolynomial.aeval (TrackD.productPoint x v)).toRingHom g = 0
      cases hg with
      | inl h =>
        obtain ⟨f, hf, rfl⟩ := h
        exact hx' f hf
      | inr h =>
        have : g = MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1 :=
          Set.mem_singleton_iff.mp h
        rw [this]
        exact hfix'
    exact (RingHom.mem_ker).mp (hle hg)

/-- The cylinder determines its source carrier. -/
theorem commonLabelCylinder_source_ideal (i₀ : Fin d) (X : AffineVariety d)
    (f : Poly d) :
    commonSourcePolynomial f ∈ (commonLabelCylinder i₀ X).ideal ↔ f ∈ X.ideal := by
  constructor
  · intro hf
    rw [TrackD.mem_ideal_iff_eval_zero]
    intro x hx
    let v₀ : Point d := fun _ => 1
    have hv₀ : v₀ i₀ = 1 := rfl
    have hpt : TrackD.productPoint x v₀ ∈ commonLabelCylinder i₀ X :=
      (commonLabelCylinder_points i₀ X x v₀).mpr ⟨hx, hv₀⟩
    have hz := (TrackD.mem_ideal_iff_eval_zero _ _).mp hf _ hpt
    rwa [eval_common_source_polynomial] at hz
  · intro hf
    have hmem : commonSourcePolynomial f ∈ Ideal.span
        (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
          {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1}) :=
      Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩)
    have hle : Ideal.span (commonSourcePolynomial '' (X.ideal : Set (Poly d)) ∪
        {MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) - 1}) ≤
        (commonLabelCylinder i₀ X).ideal := by
      unfold commonLabelCylinder
      exact Ideal.le_radical
    exact hle hmem

/-- The cylinder determines its source carrier. -/
theorem commonLabelCylinder_injective (i₀ : Fin d) (X : AffineVariety d) :
    ∀ X' : AffineVariety d,
      commonLabelCylinder i₀ X' = commonLabelCylinder i₀ X → X' = X := by
  intro X' hEq
  apply AffineVariety.ext
  ext f
  calc f ∈ X'.ideal
      ↔ commonSourcePolynomial f ∈ (commonLabelCylinder i₀ X').ideal :=
        (commonLabelCylinder_source_ideal i₀ X' f).symm
    _ ↔ commonSourcePolynomial f ∈ (commonLabelCylinder i₀ X).ideal := by
        rw [hEq]
    _ ↔ f ∈ X.ideal := commonLabelCylinder_source_ideal i₀ X f

/-- The label cylinder is the parametrized cylinder with no fixed variables. -/
theorem commonLabelCylinder_eq_cylVar (i₀ : Fin d) (X : AffineVariety d) :
    commonLabelCylinder i₀ X = cylVar i₀ X ∅ := by
  unfold commonLabelCylinder cylVar cylIdeal
  simp only [Finset.coe_empty, Set.image_empty, Set.union_empty]

/-- The label cylinder of an irreducible `X` is irreducible of dimension
`dim X + (d - 1)`, has degree at least `deg X` (in fact equal), consists of the
points `(x, v)` with `x ∈ X` and `v_{i₀} = 1`, and determines `X`. Track A's
line-cylinder support (`TrackA/Cylinder*Support.lean`) is the model: the
coordinate ring is `ℂ[X][v_j : j ≠ i₀]`; the Hilbert function in degree `D` is
`∑_{a ≤ D} H_X(D - a) · #(monomials of degree a in d-1 variables)` after the
affine substitution `v_{i₀} ↦ 1`, which gives the same leading coefficient. -/
theorem common_label_cylinder (i₀ : Fin d) (X : AffineVariety d) (hX : X.IsIrreducible) :
    (commonLabelCylinder i₀ X).IsIrreducible ∧
    (commonLabelCylinder i₀ X).dimension = X.dimension + (d - 1) ∧
    X.degree ≤ (commonLabelCylinder i₀ X).degree ∧
    (∀ (x v : Point d), TrackD.productPoint x v ∈ commonLabelCylinder i₀ X ↔
      x ∈ X ∧ v i₀ = 1) ∧
    ∀ X' : AffineVariety d, commonLabelCylinder i₀ X' = commonLabelCylinder i₀ X → X' = X := by
  have hEq : commonLabelCylinder i₀ X = cylVar i₀ X ∅ :=
    commonLabelCylinder_eq_cylVar _ _
  have hIrr : (cylVar i₀ X ∅).IsIrreducible := by
    have h := cylIdeal_prime i₀ X hX (∅ : Finset (CylFree d i₀))
    rwa [← cylVar_ideal_eq i₀ X hX ∅] at h
  have hDim : (cylVar i₀ X ∅).dimension = X.dimension + (d - 1) := by
    rw [cylVar_dimension i₀ X hX ∅, card_CylFreeRem,
      Finset.card_empty, Nat.sub_zero]
  have hDeg : X.degree ≤ (cylVar i₀ X ∅).degree := by
    have hbase := cylBase_degree i₀ X hX
    have hchain := cylChain_degree_le i₀ X hX
    have eU : (cylVar i₀ X Finset.univ).degree = X.degree := by
      have hrad := cylVar_ideal_eq i₀ X hX Finset.univ
      rw [← hrad] at hbase
      exact hbase
    rw [← eU]
    exact hchain
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hEq]
    exact hIrr
  · rw [hEq]
    exact hDim
  · rw [hEq]
    exact hDeg
  · intro x v
    exact commonLabelCylinder_points i₀ X x v
  · intro X' hX'
    apply commonLabelCylinder_injective i₀ X
    exact hX'

end
end DistinctDistances.SparseCones
