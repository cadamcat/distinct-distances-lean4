import DistinctDistances.TrackE.CommonImageInputs
import DistinctDistances.TrackD.ProductTangents
import DistinctDistances.TrackA.Hilbert
import DistinctDistances.TrackA.Intersections
import DistinctDistances.TrackA.NormalizationRankSupport
import DistinctDistances.TrackA.AffineGenericRankSupport
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

namespace DistinctDistances.SparseCones
open scoped BigOperators Classical TensorProduct
noncomputable section
variable {d : ℕ}

-- Helper file for `mo_product_degree_upper`: product Noether normalization.

/-- Product linear projection from a common factor normalization. -/
def prodLinear {k : ℕ} (ψ : LinearProjection d k) :
    LinearProjection (d + d) (k + k) :=
  (TrackD.productLinearEquiv (d := k)).toLinearMap.comp
    ((LinearMap.prodMap ψ ψ).comp
      (TrackD.productLinearEquiv (d := d)).symm.toLinearMap)

/-- Product affine projection (zero offset). -/
def prodAffine {k : ℕ} (ψ : LinearProjection d k) :
    AffineProjection (d + d) (k + k) :=
  ⟨prodLinear ψ, 0⟩

theorem prodLinear_apply {k : ℕ} (ψ : LinearProjection d k)
    (x y : Point d) :
    prodLinear ψ (TrackD.productPoint x y) =
      TrackD.productPoint (ψ x) (ψ y) := by
  unfold prodLinear
  simp only [LinearMap.comp_apply]
  have hsymm : (TrackD.productLinearEquiv (d := d)).symm.toLinearMap
      (TrackD.productPoint x y) = (x, y) := by
    have h : (TrackD.productLinearEquiv (d := d)).symm
        (TrackD.productPoint x y) = (x, y) := by
      apply (TrackD.productLinearEquiv (d := d)).injective
      simp [TrackD.productLinearEquiv]
    simpa using h
  rw [hsymm]
  simp [TrackD.productLinearEquiv, TrackD.productPoint, LinearMap.prodMap]

theorem prodPoint_left {n : ℕ} (x y : Point n) :
    TrackD.productLeft (TrackD.productPoint x y) = x := by
  have h := TrackD.productLinearEquiv.left_inv (R := ℂ) (M := Point n × Point n)
    (x, y)
  have hfst := congrArg Prod.fst h
  simpa [TrackD.productLinearEquiv, TrackD.productPoint] using hfst

theorem prodPoint_right {n : ℕ} (x y : Point n) :
    TrackD.productRight (TrackD.productPoint x y) = y := by
  have h := TrackD.productLinearEquiv.left_inv (R := ℂ) (M := Point n × Point n)
    (x, y)
  have hsnd := congrArg Prod.snd h
  simpa [TrackD.productLinearEquiv, TrackD.productPoint] using hsnd

theorem prodLinear_surjective {k : ℕ} {ψ : LinearProjection d k}
    (hψ : Function.Surjective ψ) :
    Function.Surjective (prodLinear ψ) := by
  intro z
  obtain ⟨s, hs⟩ := hψ (TrackD.productLeft z)
  obtain ⟨t, ht⟩ := hψ (TrackD.productRight z)
  refine ⟨TrackD.productPoint s t, ?_⟩
  have hz : TrackD.productPoint (TrackD.productLeft z)
      (TrackD.productRight z) = z :=
    TrackD.productPoint_left_right z
  have himg := prodLinear_apply ψ s t
  rw [hs, ht, hz] at himg
  exact himg

theorem prodAffine_apply {k : ℕ} (ψ : LinearProjection d k)
    (x y : Point d) :
    (prodAffine ψ).apply (TrackD.productPoint x y) =
      TrackD.productPoint (ψ x) (ψ y) := by
  simp [prodAffine, AffineProjection.apply, prodLinear_apply]

theorem prodPoint_injective {n : ℕ} :
    Function.Injective (Function.uncurry (TrackD.productPoint (d := n))) := by
  intro ⟨x1, y1⟩ ⟨x2, y2⟩ h
  simp only [Function.uncurry] at h
  have hl := congrArg TrackD.productLeft h
  have hr := congrArg TrackD.productRight h
  rw [prodPoint_left, prodPoint_left] at hl
  rw [prodPoint_right, prodPoint_right] at hr
  exact Prod.ext hl hr

/-- Left factor equations pull back to the product ideal. -/
theorem prod_ideal_left {X Y : AffineVariety d} (f : Poly d) (hf : f ∈ X.ideal) :
    MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) f ∈
      (TrackD.productVariety X Y).ideal := by
  have hf' : f ∈ MvPolynomial.vanishingIdeal ℂ X.points := by
    simpa [AffineVariety.vanishingIdeal_points] using hf
  have hmem : MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) f ∈
      MvPolynomial.vanishingIdeal ℂ
        {p | ∃ x ∈ X, ∃ y ∈ Y, TrackD.productPoint x y = p} := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro p ⟨x, hx, y, hy, rfl⟩
    have hxvan : MvPolynomial.aeval x f = 0 := by
      have := (MvPolynomial.mem_vanishingIdeal_iff.mp hf') x hx
      simpa [MvPolynomial.aeval_eq_eval] using this
    have heval := TrackD.eval_product_left_rename (d := d) f x y
    simp only [MvPolynomial.aeval_eq_eval] at hxvan ⊢
    rw [heval]
    exact hxvan
  simpa [TrackD.productVariety, AffineVariety.closure] using hmem

/-- Right factor equations pull back to the product ideal. -/
theorem prod_ideal_right {X Y : AffineVariety d} (f : Poly d) (hf : f ∈ Y.ideal) :
    MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inr i)) f ∈
      (TrackD.productVariety X Y).ideal := by
  have hf' : f ∈ MvPolynomial.vanishingIdeal ℂ Y.points := by
    simpa [AffineVariety.vanishingIdeal_points] using hf
  have hmem : MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inr i)) f ∈
      MvPolynomial.vanishingIdeal ℂ
        {p | ∃ x ∈ X, ∃ y ∈ Y, TrackD.productPoint x y = p} := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro p ⟨x, hx, y, hy, rfl⟩
    have hyvan : MvPolynomial.aeval y f = 0 := by
      have := (MvPolynomial.mem_vanishingIdeal_iff.mp hf') y hy
      simpa [MvPolynomial.aeval_eq_eval] using this
    have heval := TrackD.eval_product_right_rename (d := d) f x y
    simp only [MvPolynomial.aeval_eq_eval] at hyvan ⊢
    rw [heval]
    exact hyvan
  simpa [TrackD.productVariety, AffineVariety.closure] using hmem

theorem prod_eval_left {k : ℕ} (g : Poly k) (s t : Point k) :
    MvPolynomial.eval (TrackD.productPoint s t)
      (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) g) =
      MvPolynomial.eval s g := by
  rw [MvPolynomial.eval_rename]
  have heq : TrackD.productPoint s t ∘ (fun i : Fin k => finSumFinEquiv (Sum.inl i)) = s := by
    funext i
    change TrackD.pairPt s t (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = s i
    rw [Equiv.symm_apply_apply]
    rfl
  rw [heq]

theorem prod_eval_right {k : ℕ} (g : Poly k) (s t : Point k) :
    MvPolynomial.eval (TrackD.productPoint s t)
      (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inr i)) g) =
      MvPolynomial.eval t g := by
  rw [MvPolynomial.eval_rename]
  have heq : TrackD.productPoint s t ∘ (fun i : Fin k => finSumFinEquiv (Sum.inr i)) = t := by
    funext i
    change TrackD.pairPt s t (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) = t i
    rw [Equiv.symm_apply_apply]
    rfl
  rw [heq]

/-- The product generic polynomial detects both factor generics. -/
def prodGenericPoly {k : ℕ} (gX gY : Poly k) : Poly (k + k) :=
  MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) gX *
    MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inr i)) gY

theorem prodGenericPoly_eval {k : ℕ} (gX gY : Poly k) (s t : Point k) :
    MvPolynomial.eval (TrackD.productPoint s t) (prodGenericPoly gX gY) =
      MvPolynomial.eval s gX * MvPolynomial.eval t gY := by
  unfold prodGenericPoly
  rw [map_mul, prod_eval_left, prod_eval_right]

/-- Fibers of the product projection are products of factor fibers. -/
theorem prodFiber_eq {k : ℕ} (ψ : LinearProjection d k)
    (X Y : AffineVariety d) (s t : Point k) :
    (prodAffine ψ).fiber (TrackD.productVariety X Y)
      (TrackD.productPoint s t) =
      (Function.uncurry TrackD.productPoint) ''
        ({x | x ∈ X ∧ ψ x = s} ×ˢ {y | y ∈ Y ∧ ψ y = t}) := by
  ext p
  constructor
  · rintro ⟨hpS, hpEq⟩
    have hpSpts : p ∈ (TrackD.productVariety X Y).points := hpS
    rw [TrackD.productVariety_points] at hpSpts
    have happly : (prodAffine ψ).apply p =
        TrackD.productPoint (ψ (TrackD.productLeft p)) (ψ (TrackD.productRight p)) := by
      have hpprod := TrackD.productPoint_left_right p
      conv_lhs => rw [← hpprod]
      exact prodAffine_apply ψ _ _
    rw [happly] at hpEq
    have hl : ψ (TrackD.productLeft p) = s := by
      have := congrArg TrackD.productLeft hpEq
      simpa [prodPoint_left] using this
    have hr : ψ (TrackD.productRight p) = t := by
      have := congrArg TrackD.productRight hpEq
      simpa [prodPoint_right] using this
    refine ⟨(TrackD.productLeft p, TrackD.productRight p),
      ⟨⟨hpSpts.1, hl⟩, hpSpts.2, hr⟩, ?_⟩
    show TrackD.productPoint _ _ = _
    exact TrackD.productPoint_left_right p
  · rintro ⟨⟨a, b⟩, hmem, rfl⟩
    rw [Set.mem_prod] at hmem
    obtain ⟨⟨ha, has⟩, hb, hbs⟩ := hmem
    constructor
    · show TrackD.productPoint a b ∈ _
      have hpts : TrackD.productLeft (TrackD.productPoint a b) ∈ X ∧
          TrackD.productRight (TrackD.productPoint a b) ∈ Y := by
        simpa [prodPoint_left, prodPoint_right] using ⟨ha, hb⟩
      have hSpts : TrackD.productPoint a b ∈
          (TrackD.productVariety X Y).points := by
        rw [TrackD.productVariety_points]
        exact hpts
      exact hSpts
    · show (prodAffine ψ).apply (TrackD.productPoint a b) = _
      rw [prodAffine_apply, has, hbs]


/-- Product generic degree is the product of factor generic degrees,
assuming product finiteness (for the image to be whole). -/
theorem prodGenericallyFinite {k rX rY : ℕ} {ψ : LinearProjection d k}
    {X Y : AffineVariety d}
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXd : X.dimension = k) (hYd : Y.dimension = k)
    (hfX : TrackA.FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection d k) X)
    (hfY : TrackA.FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection d k) Y)
    (hgX : (⟨ψ, 0⟩ : AffineProjection d k).GenericallyFiniteOfDegree X rX)
    (hgY : (⟨ψ, 0⟩ : AffineProjection d k).GenericallyFiniteOfDegree Y rY)
    (hfS : TrackA.FiniteAffineProjection (prodAffine ψ)
      (TrackD.productVariety X Y)) :
    (prodAffine ψ).GenericallyFiniteOfDegree
      (TrackD.productVariety X Y) (rX * rY) := by
  classical
  have hSirr := TrackD.productVariety_irreducible X Y hX hY
  have hSdim : (TrackD.productVariety X Y).dimension = k + k := by
    rw [TrackD.product_dimension X Y hX hY, hXd, hYd]
  obtain ⟨hrXpos, gX, hgXmem, hgXfib⟩ := hgX
  obtain ⟨hrYpos, gY, hgYmem, hgYfib⟩ := hgY
  have hXimg : ((⟨ψ, 0⟩ : AffineProjection d k).image X).ideal = ⊥ :=
    TrackA.finite_affine_projection_image_ideal_bot X hX hXd _ hfX
  have hYimg : ((⟨ψ, 0⟩ : AffineProjection d k).image Y).ideal = ⊥ :=
    TrackA.finite_affine_projection_image_ideal_bot Y hY hYd _ hfY
  have hSimg : ((prodAffine ψ).image (TrackD.productVariety X Y)).ideal = ⊥ :=
    TrackA.finite_affine_projection_image_ideal_bot _ hSirr hSdim _ hfS
  have hgX0 : gX ≠ 0 := by simpa [hXimg] using hgXmem
  have hgY0 : gY ≠ 0 := by simpa [hYimg] using hgYmem
  have hleft_inj : Function.Injective
      (fun i : Fin k => finSumFinEquiv (Sum.inl i) : Fin k → Fin (k + k)) := by
    intro a b hab
    have := congrArg finSumFinEquiv.symm hab
    simpa using this
  have hright_inj : Function.Injective
      (fun i : Fin k => finSumFinEquiv (Sum.inr i) : Fin k → Fin (k + k)) := by
    intro a b hab
    have := congrArg finSumFinEquiv.symm hab
    simpa using this
  have hgXr : (MvPolynomial.rename
      (fun i : Fin k => finSumFinEquiv (Sum.inl i)) gX : Poly (k + k)) ≠ 0 := by
    intro h0
    apply hgX0
    have hinj := MvPolynomial.rename_injective
      (R := ℂ) (fun i : Fin k => finSumFinEquiv (Sum.inl i) : Fin k → Fin (k + k))
      hleft_inj
    have h01 : MvPolynomial.rename
        (fun i : Fin k => finSumFinEquiv (Sum.inl i) : Fin k → Fin (k + k))
        (0 : Poly k) = 0 := by simp
    exact hinj (h0.trans h01.symm)
  have hgYr : (MvPolynomial.rename
      (fun i : Fin k => finSumFinEquiv (Sum.inr i)) gY : Poly (k + k)) ≠ 0 := by
    intro h0
    apply hgY0
    have hinj := MvPolynomial.rename_injective
      (R := ℂ) (fun i : Fin k => finSumFinEquiv (Sum.inr i) : Fin k → Fin (k + k))
      hright_inj
    have h01 : MvPolynomial.rename
        (fun i : Fin k => finSumFinEquiv (Sum.inr i) : Fin k → Fin (k + k))
        (0 : Poly k) = 0 := by simp
    exact hinj (h0.trans h01.symm)
  refine ⟨Nat.mul_pos hrXpos hrYpos, prodGenericPoly gX gY, ?_, ?_⟩
  · rw [hSimg]
    have hne : prodGenericPoly gX gY ≠ 0 := by
      unfold prodGenericPoly
      exact mul_ne_zero hgXr hgYr
    simpa [Ideal.mem_bot] using hne
  · intro y hy hyne
    -- y is a product point since image is whole; write y = productPoint s t
    have hyuniv : y ∈ ((prodAffine ψ).image (TrackD.productVariety X Y)).points := hy
    -- reduce to product form via surjectivity of productPoint decomposition
    obtain ⟨s, t, rfl⟩ : ∃ s t : Point k, TrackD.productPoint s t = y := by
      exact ⟨TrackD.productLeft y, TrackD.productRight y,
        TrackD.productPoint_left_right y⟩
    have heval := prodGenericPoly_eval gX gY s t
    have hyne' : MvPolynomial.eval s gX * MvPolynomial.eval t gY ≠ 0 := by
      simpa [heval] using hyne
    have hXs : MvPolynomial.eval s gX ≠ 0 := (mul_ne_zero_iff.mp hyne').1
    have hYt : MvPolynomial.eval t gY ≠ 0 := (mul_ne_zero_iff.mp hyne').2
    have hsimg : s ∈ ((⟨ψ, 0⟩ : AffineProjection d k).image X).points := by
      show s ∈ MvPolynomial.zeroLocus ℂ
        ((⟨ψ, 0⟩ : AffineProjection d k).image X).ideal
      rw [hXimg]
      intro f hf
      rw [Ideal.mem_bot] at hf
      simp [hf]
    have htimg : t ∈ ((⟨ψ, 0⟩ : AffineProjection d k).image Y).points := by
      show t ∈ MvPolynomial.zeroLocus ℂ
        ((⟨ψ, 0⟩ : AffineProjection d k).image Y).ideal
      rw [hYimg]
      intro f hf
      rw [Ideal.mem_bot] at hf
      simp [hf]
    obtain ⟨hXfin, hXcard⟩ := hgXfib s hsimg (by simpa using hXs)
    obtain ⟨hYfin, hYcard⟩ := hgYfib t htimg (by simpa using hYt)
    -- factor fibers as sets with ψ (offset 0 apply = ψ)
    have hXfib : {x | x ∈ X ∧ ψ x = s} =
        (⟨ψ, 0⟩ : AffineProjection d k).fiber X s := by
      ext x
      simp [AffineProjection.fiber, AffineProjection.apply]
    have hYfib : {y | y ∈ Y ∧ ψ y = t} =
        (⟨ψ, 0⟩ : AffineProjection d k).fiber Y t := by
      ext x
      simp [AffineProjection.fiber, AffineProjection.apply]
    rw [prodFiber_eq ψ X Y s t]
    have hfinprod : ({x | x ∈ X ∧ ψ x = s} ×ˢ {y | y ∈ Y ∧ ψ y = t}).Finite := by
      have h1 : {x | x ∈ X ∧ ψ x = s}.Finite := by
        rw [hXfib]; exact hXfin
      have h2 : {y | y ∈ Y ∧ ψ y = t}.Finite := by
        rw [hYfib]; exact hYfin
      exact h1.prod h2
    have hXcard' : ({x | x ∈ X ∧ ψ x = s}).ncard = rX := by
      rw [hXfib]; exact hXcard
    have hYcard' : ({y | y ∈ Y ∧ ψ y = t}).ncard = rY := by
      rw [hYfib]; exact hYcard
    have hcardprod : ({x | x ∈ X ∧ ψ x = s} ×ˢ {y | y ∈ Y ∧ ψ y = t}).ncard =
        rX * rY := by
      rw [Set.ncard_prod, hXcard', hYcard']
    constructor
    · exact hfinprod.image _
    · rw [Set.ncard_image_of_injective _ prodPoint_injective, hcardprod]

/-- Every polynomial in product variables is a sum of separable products.
This is the algebraic heart of affine finiteness (variables partition). -/
theorem separableDecompList (F : Poly (d + d)) :
    ∃ (L : List (Poly d × Poly d)),
      F = (L.map (fun p => MvPolynomial.rename
        (fun i : Fin d => finSumFinEquiv (Sum.inl i)) p.1 *
        MvPolynomial.rename
        (fun i : Fin d => finSumFinEquiv (Sum.inr i)) p.2)).sum := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨[(MvPolynomial.C a, 1)], ?_⟩
    simp [MvPolynomial.rename_C]
  | add f g hf hg =>
    obtain ⟨Lf, hLf⟩ := hf
    obtain ⟨Lg, hLg⟩ := hg
    refine ⟨Lf ++ Lg, ?_⟩
    simp [List.map_append, List.sum_append, hLf, hLg]
  | mul_X f j hf =>
    obtain ⟨Lf, hLf⟩ := hf
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    cases s with
    | inl i =>
      refine ⟨List.map (fun p : Poly d × Poly d => (p.1 * MvPolynomial.X i, p.2)) Lf, ?_⟩
      have hX : MvPolynomial.rename
          (fun i : Fin d => finSumFinEquiv (Sum.inl i))
          (MvPolynomial.X i) =
          (MvPolynomial.X (finSumFinEquiv (Sum.inl i)) : Poly (d + d)) := by
        simp [MvPolynomial.rename_X]
      have hsep : ∀ p : Poly d × Poly d,
          (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i))
            (p.1 * MvPolynomial.X i) *
          MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i)) p.2) =
          ((MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i)) p.1 *
            MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i)) p.2) *
          MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i))
            (MvPolynomial.X i)) := by
        intro p
        rw [map_mul]
        ring
      calc f * MvPolynomial.X (finSumFinEquiv (Sum.inl i))
          = ((List.map (fun p => MvPolynomial.rename
              (fun i : Fin d => finSumFinEquiv (Sum.inl i)) p.1 *
              MvPolynomial.rename
              (fun i : Fin d => finSumFinEquiv (Sum.inr i)) p.2) Lf).sum) *
            MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i))
              (MvPolynomial.X i) := by rw [← hLf, hX]
        _ = (((List.map (fun p : Poly d × Poly d => (p.1 * MvPolynomial.X i, p.2)) Lf).map
              (fun p => MvPolynomial.rename
                (fun i : Fin d => finSumFinEquiv (Sum.inl i)) p.1 *
                MvPolynomial.rename
                (fun i : Fin d => finSumFinEquiv (Sum.inr i)) p.2)).sum) := by
            simp only [List.map_map, Function.comp_def, ← List.sum_map_mul_right, hsep]
    | inr i =>
      refine ⟨List.map (fun p : Poly d × Poly d => (p.1, p.2 * MvPolynomial.X i)) Lf, ?_⟩
      have hX : MvPolynomial.rename
          (fun i : Fin d => finSumFinEquiv (Sum.inr i))
          (MvPolynomial.X i) =
          (MvPolynomial.X (finSumFinEquiv (Sum.inr i)) : Poly (d + d)) := by
        simp [MvPolynomial.rename_X]
      have hsep : ∀ p : Poly d × Poly d,
          (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i)) p.1 *
          MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i))
            (p.2 * MvPolynomial.X i)) =
          ((MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i)) p.1 *
            MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i)) p.2) *
          MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i))
            (MvPolynomial.X i)) := by
        intro p
        rw [map_mul]
        ring
      calc f * MvPolynomial.X (finSumFinEquiv (Sum.inr i))
          = ((List.map (fun p => MvPolynomial.rename
              (fun i : Fin d => finSumFinEquiv (Sum.inl i)) p.1 *
              MvPolynomial.rename
              (fun i : Fin d => finSumFinEquiv (Sum.inr i)) p.2) Lf).sum) *
            MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i))
              (MvPolynomial.X i) := by rw [← hLf, hX]
        _ = (((List.map (fun p : Poly d × Poly d => (p.1, p.2 * MvPolynomial.X i)) Lf).map
              (fun p => MvPolynomial.rename
                (fun i : Fin d => finSumFinEquiv (Sum.inl i)) p.1 *
                MvPolynomial.rename
                (fun i : Fin d => finSumFinEquiv (Sum.inr i)) p.2)).sum) := by
            simp only [List.map_map, Function.comp_def, ← List.sum_map_mul_right, hsep]

/-- Left base inclusion for product normalizations. -/
def leftBase {k : ℕ} : Poly k →ₐ[ℂ] Poly (k + k) :=
  MvPolynomial.rename (fun i : Fin k => finSumFinEquiv (Sum.inl i))

/-- Right base inclusion for product normalizations. -/
def rightBase {k : ℕ} : Poly k →ₐ[ℂ] Poly (k + k) :=
  MvPolynomial.rename (fun i : Fin k => finSumFinEquiv (Sum.inr i))

/-- Base tensor isomorphism (polynomials in split variables). -/
def baseIsoForward {k : ℕ} : Poly (k + k) →ₐ[ℂ] (Poly k ⊗[ℂ] Poly k) :=
  MvPolynomial.aeval (fun j : Fin (k + k) =>
    match finSumFinEquiv.symm j with
    | Sum.inl i => MvPolynomial.X i ⊗ₜ[ℂ] 1
    | Sum.inr i => 1 ⊗ₜ[ℂ] MvPolynomial.X i)

/-- Backward base map (tensor to split polynomials). -/
def baseIsoBackward {k : ℕ} : (Poly k ⊗[ℂ] Poly k) →ₐ[ℂ] Poly (k + k) :=
  Algebra.TensorProduct.lift leftBase rightBase (fun _ _ => Commute.all _ _)

/-- Base isomorphism (forward/backward inverse). -/
theorem baseIso_inv {k : ℕ} :
    (baseIsoBackward (k := k)).comp baseIsoForward = AlgHom.id _ _ ∧
    (baseIsoForward (k := k)).comp baseIsoBackward =
      AlgHom.id _ _ := by
  constructor
  · -- Backward ∘ Forward = id on split polynomials (check on variables)
    apply MvPolynomial.algHom_ext
    intro j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    cases s with
    | inl i =>
      show baseIsoBackward (baseIsoForward (MvPolynomial.X _)) = _
      simp only [baseIsoForward, MvPolynomial.aeval_X]
      have hsymm : (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)).symm
          ((finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k))
            (Sum.inl i : Fin k ⊕ Fin k)) = Sum.inl i :=
        Equiv.symm_apply_apply _ _
      simp only [hsymm]
      simp only [baseIsoBackward, Algebra.TensorProduct.lift_tmul,
        leftBase, rightBase, MvPolynomial.rename_X, map_one, mul_one,
        AlgHom.id_apply]
    | inr i =>
      show baseIsoBackward (baseIsoForward (MvPolynomial.X _)) = _
      simp only [baseIsoForward, MvPolynomial.aeval_X]
      have hsymm : (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)).symm
          ((finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k))
            (Sum.inr i : Fin k ⊕ Fin k)) = Sum.inr i :=
        Equiv.symm_apply_apply _ _
      simp only [hsymm]
      simp only [baseIsoBackward, Algebra.TensorProduct.lift_tmul,
        leftBase, rightBase, MvPolynomial.rename_X, map_one, one_mul,
        AlgHom.id_apply]
  · -- Forward ∘ Backward = id on tensors (check on pure tensors)
    apply Algebra.TensorProduct.ext'
    intro a b
    show baseIsoForward (baseIsoBackward (a ⊗ₜ[ℂ] b)) = _
    simp only [baseIsoBackward, Algebra.TensorProduct.lift_tmul]
    -- Forward(leftBase a * rightBase b) = (a ⊗ 1) * (1 ⊗ b) = a ⊗ b
    have hleft : baseIsoForward (leftBase a) = a ⊗ₜ[ℂ] (1 : Poly k) := by
      -- both sides AlgHoms in a; check on variables
      have h : baseIsoForward.comp leftBase =
          (Algebra.TensorProduct.includeLeft :
            Poly k →ₐ[ℂ] (Poly k ⊗[ℂ] Poly k)) := by
        apply MvPolynomial.algHom_ext
        intro i
        show baseIsoForward (leftBase (MvPolynomial.X i)) = _
        simp only [leftBase, MvPolynomial.rename_X, baseIsoForward,
          MvPolynomial.aeval_X]
        have hsymm : (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)).symm
            ((finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k))
              (Sum.inl i : Fin k ⊕ Fin k)) = Sum.inl i :=
          Equiv.symm_apply_apply _ _
        simp only [hsymm]
        simp [Algebra.TensorProduct.includeLeft]
      exact AlgHom.congr_fun h a
    have hright : baseIsoForward (rightBase b) = (1 : Poly k) ⊗ₜ[ℂ] b := by
      have h : baseIsoForward.comp rightBase =
          (Algebra.TensorProduct.includeRight :
            Poly k →ₐ[ℂ] (Poly k ⊗[ℂ] Poly k)) := by
        apply MvPolynomial.algHom_ext
        intro i
        show baseIsoForward (rightBase (MvPolynomial.X i)) = _
        simp only [rightBase, MvPolynomial.rename_X, baseIsoForward,
          MvPolynomial.aeval_X]
        have hsymm : (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)).symm
            ((finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k))
              (Sum.inr i : Fin k ⊕ Fin k)) = Sum.inr i :=
          Equiv.symm_apply_apply _ _
        simp only [hsymm]
        simp [Algebra.TensorProduct.includeRight]
      exact AlgHom.congr_fun h b
    simp only [map_mul, hleft, hright]
    simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- Left coordinate lift to the product quotient. -/
def liftLeft (X Y : AffineVariety d) :
    (Poly d ⧸ X.ideal) →ₐ[ℂ] (Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) :=
  Ideal.Quotient.liftₐ X.ideal
    ((Ideal.Quotient.mkₐ ℂ _).comp
      (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i))))
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr (prod_ideal_left f hf))

/-- Right coordinate lift to the product quotient. -/
def liftRight (X Y : AffineVariety d) :
    (Poly d ⧸ Y.ideal) →ₐ[ℂ] (Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) :=
  Ideal.Quotient.liftₐ Y.ideal
    ((Ideal.Quotient.mkₐ ℂ _).comp
      (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i))))
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr (prod_ideal_right f hf))

/-- Product pullback agrees with factor pullback on left variables
(evaluation proof, avoiding explicit linear-coordinate computation). -/
theorem prodPullback_left {k : ℕ} (ψ : LinearProjection d k) (r : Poly k) :
    (prodAffine ψ).pullback (leftBase r) =
      MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i))
        ((⟨ψ, 0⟩ : AffineProjection d k).pullback r) := by
  apply MvPolynomial.funext
  intro p
  have hpprod := TrackD.productPoint_left_right p
  have happly : (prodAffine ψ).apply p =
      TrackD.productPoint (ψ (TrackD.productLeft p)) (ψ (TrackD.productRight p)) := by
    conv_lhs => rw [← hpprod]
    exact prodAffine_apply ψ _ _
  have hLHS : MvPolynomial.eval p ((prodAffine ψ).pullback (leftBase r)) =
      MvPolynomial.eval (ψ (TrackD.productLeft p)) r := by
    have h1 : MvPolynomial.eval p ((prodAffine ψ).pullback (leftBase r)) =
        MvPolynomial.eval ((prodAffine ψ).apply p) (leftBase r) := by
      rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval]
      exact AffineProjection.eval_pullback _ _ _
    rw [h1, happly]
    unfold leftBase
    rw [prod_eval_left]
  have hRHS : MvPolynomial.eval p
        (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i))
          ((⟨ψ, 0⟩ : AffineProjection d k).pullback r)) =
      MvPolynomial.eval (ψ (TrackD.productLeft p)) r := by
    conv_lhs => rw [← hpprod]
    rw [TrackD.eval_product_left_rename]
    have h2 : MvPolynomial.eval (TrackD.productLeft p)
          ((⟨ψ, 0⟩ : AffineProjection d k).pullback r) =
        MvPolynomial.eval (ψ (TrackD.productLeft p)) r := by
      rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval]
      have he := AffineProjection.eval_pullback
        (⟨ψ, 0⟩ : AffineProjection d k) (TrackD.productLeft p) r
      simpa [AffineProjection.apply] using he
    exact h2
  rw [hLHS, hRHS]

/-- Product pullback agrees with factor pullback on right variables. -/
theorem prodPullback_right {k : ℕ} (ψ : LinearProjection d k) (r : Poly k) :
    (prodAffine ψ).pullback (rightBase r) =
      MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i))
        ((⟨ψ, 0⟩ : AffineProjection d k).pullback r) := by
  apply MvPolynomial.funext
  intro p
  have hpprod := TrackD.productPoint_left_right p
  have happly : (prodAffine ψ).apply p =
      TrackD.productPoint (ψ (TrackD.productLeft p)) (ψ (TrackD.productRight p)) := by
    conv_lhs => rw [← hpprod]
    exact prodAffine_apply ψ _ _
  have hLHS : MvPolynomial.eval p ((prodAffine ψ).pullback (rightBase r)) =
      MvPolynomial.eval (ψ (TrackD.productRight p)) r := by
    have h1 : MvPolynomial.eval p ((prodAffine ψ).pullback (rightBase r)) =
        MvPolynomial.eval ((prodAffine ψ).apply p) (rightBase r) := by
      rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval]
      exact AffineProjection.eval_pullback _ _ _
    rw [h1, happly]
    unfold rightBase
    rw [prod_eval_right]
  have hRHS : MvPolynomial.eval p
        (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i))
          ((⟨ψ, 0⟩ : AffineProjection d k).pullback r)) =
      MvPolynomial.eval (ψ (TrackD.productRight p)) r := by
    conv_lhs => rw [← hpprod]
    rw [TrackD.eval_product_right_rename]
    have h2 : MvPolynomial.eval (TrackD.productRight p)
          ((⟨ψ, 0⟩ : AffineProjection d k).pullback r) =
        MvPolynomial.eval (ψ (TrackD.productRight p)) r := by
      rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval]
      have he := AffineProjection.eval_pullback
        (⟨ψ, 0⟩ : AffineProjection d k) (TrackD.productRight p) r
      simpa [AffineProjection.apply] using he
    exact h2
  rw [hLHS, hRHS]

theorem prodLiftLeft_map {k : ℕ} {X Y : AffineVariety d} (ψ : LinearProjection d k)
    (r : Poly k) :
    liftLeft X Y (TrackA.affineProjectionMap X (⟨ψ, 0⟩ : AffineProjection d k) r) =
      TrackA.affineProjectionMap (TrackD.productVariety X Y) (prodAffine ψ)
        (leftBase r) := by
  simp only [TrackA.affineProjectionMap, AlgHom.comp_apply]
  have hpull := prodPullback_left (d := d) ψ r
  have hmk : ∀ a : Poly d, liftLeft X Y (Ideal.Quotient.mk X.ideal a) =
      Ideal.Quotient.mk (TrackD.productVariety X Y).ideal
        (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i)) a) := by
    intro a
    rfl
  rw [Ideal.Quotient.mkₐ_eq_mk, hmk, hpull]
  rfl

theorem prodLiftRight_map {k : ℕ} {X Y : AffineVariety d} (ψ : LinearProjection d k)
    (r : Poly k) :
    liftRight X Y (TrackA.affineProjectionMap Y (⟨ψ, 0⟩ : AffineProjection d k) r) =
      TrackA.affineProjectionMap (TrackD.productVariety X Y) (prodAffine ψ)
        (rightBase r) := by
  simp only [TrackA.affineProjectionMap, AlgHom.comp_apply]
  have hpull := prodPullback_right (d := d) ψ r
  have hmk : ∀ a : Poly d, liftRight X Y (Ideal.Quotient.mk Y.ideal a) =
      Ideal.Quotient.mk (TrackD.productVariety X Y).ideal
        (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i)) a) := by
    intro a
    rfl
  rw [Ideal.Quotient.mkₐ_eq_mk, hmk, hpull]
  rfl

/-- Product affine projection is finite from factor finiteness. -/
theorem prodFinite {k : ℕ} {ψ : LinearProjection d k}
    {X Y : AffineVariety d}
    (hfX : TrackA.FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection d k) X)
    (hfY : TrackA.FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection d k) Y) :
    TrackA.FiniteAffineProjection (prodAffine ψ)
      (TrackD.productVariety X Y) := by
  classical
  letI := (TrackA.affineProjectionMap X (⟨ψ, 0⟩ : AffineProjection d k)).toRingHom.toAlgebra
  letI : Module (Poly k) (Poly d ⧸ X.ideal) :=
    (TrackA.affineProjectionMap X (⟨ψ, 0⟩ : AffineProjection d k)).toRingHom.toAlgebra.toModule
  letI := (TrackA.affineProjectionMap Y (⟨ψ, 0⟩ : AffineProjection d k)).toRingHom.toAlgebra
  letI : Module (Poly k) (Poly d ⧸ Y.ideal) :=
    (TrackA.affineProjectionMap Y (⟨ψ, 0⟩ : AffineProjection d k)).toRingHom.toAlgebra.toModule
  letI := (TrackA.affineProjectionMap (TrackD.productVariety X Y)
    (prodAffine ψ)).toRingHom.toAlgebra
  letI : Module (Poly (k + k)) (Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) :=
    (TrackA.affineProjectionMap (TrackD.productVariety X Y)
      (prodAffine ψ)).toRingHom.toAlgebra.toModule
  haveI hFX : Module.Finite (Poly k) (Poly d ⧸ X.ideal) := hfX
  haveI hFY : Module.Finite (Poly k) (Poly d ⧸ Y.ideal) := hfY
  obtain ⟨nX, sX, hsX⟩ :=
    Module.Finite.exists_fin (R := Poly k) (M := Poly d ⧸ X.ideal)
  obtain ⟨nY, sY, hsY⟩ :=
    Module.Finite.exists_fin (R := Poly k) (M := Poly d ⧸ Y.ideal)
  -- product generators
  let w : Fin nX × Fin nY → Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal :=
    fun pq => liftLeft X Y (sX pq.1) * liftRight X Y (sY pq.2)
  have hspan : Submodule.span (Poly (k + k)) (Set.range w) = ⊤ := by
    apply top_unique
    intro a ha
    -- write a as quotient of F
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective (I := (TrackD.productVariety X Y).ideal) a
    obtain ⟨L, hL⟩ := separableDecompList (d := d) F
    -- each separable term lies in the span; List.sum stays in the span
    have hterm : ∀ p : Poly d × Poly d,
        liftLeft X Y (Ideal.Quotient.mk X.ideal p.1) *
          liftRight X Y (Ideal.Quotient.mk Y.ideal p.2) ∈
          Submodule.span (Poly (k + k)) (Set.range w) := by
      intro p
      -- factor expansions from finiteness
      have hmemX : Ideal.Quotient.mk X.ideal p.1 ∈
          Submodule.span (Poly k) (Set.range sX) := hsX.symm ▸ Submodule.mem_top
      have hmemY : Ideal.Quotient.mk Y.ideal p.2 ∈
          Submodule.span (Poly k) (Set.range sY) := hsY.symm ▸ Submodule.mem_top
      obtain ⟨cX, hcX⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmemX
      obtain ⟨cY, hcY⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmemY
      -- lift expansions to the product base
      have hLX : liftLeft X Y (Ideal.Quotient.mk X.ideal p.1) =
          ∑ i : Fin nX, leftBase (cX i) •
            (liftLeft X Y (sX i) :
              Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) := by
        have hmap : ∀ c : Poly k, ∀ s : Poly d ⧸ X.ideal,
            liftLeft X Y (c • s) =
              (leftBase c) •
                (liftLeft X Y s :
                  Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) := by
          intro c s
          rw [Algebra.smul_def, Algebra.smul_def]
          rw [map_mul]
          congr 1
          -- algebraMap agrees with affineProjectionMap by construction
          have hXalg : algebraMap (Poly k) (Poly d ⧸ X.ideal) c =
              TrackA.affineProjectionMap X (⟨ψ, 0⟩ : AffineProjection d k) c := rfl
          have hSalg : algebraMap (Poly (k + k))
                (Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) (leftBase c) =
              TrackA.affineProjectionMap (TrackD.productVariety X Y)
                (prodAffine ψ) (leftBase c) := rfl
          rw [hXalg, hSalg]
          exact (prodLiftLeft_map (X := X) (Y := Y) ψ c)
        conv_lhs => rw [← hcX]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact hmap _ _
      have hRY : liftRight X Y (Ideal.Quotient.mk Y.ideal p.2) =
          ∑ j : Fin nY, rightBase (cY j) •
            (liftRight X Y (sY j) :
              Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) := by
        have hmap : ∀ c : Poly k, ∀ s : Poly d ⧸ Y.ideal,
            liftRight X Y (c • s) =
              (rightBase c) •
                (liftRight X Y s :
                  Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) := by
          intro c s
          rw [Algebra.smul_def, Algebra.smul_def]
          rw [map_mul]
          congr 1
          have hYalg : algebraMap (Poly k) (Poly d ⧸ Y.ideal) c =
              TrackA.affineProjectionMap Y (⟨ψ, 0⟩ : AffineProjection d k) c := rfl
          have hSalg : algebraMap (Poly (k + k))
                (Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) (rightBase c) =
              TrackA.affineProjectionMap (TrackD.productVariety X Y)
                (prodAffine ψ) (rightBase c) := rfl
          rw [hYalg, hSalg]
          exact (prodLiftRight_map (X := X) (Y := Y) ψ c)
        conv_lhs => rw [← hcY]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact hmap _ _
      rw [hLX, hRY]
      -- product of sums is a sum of product generators
      have hprod : (∑ i : Fin nX, leftBase (cX i) •
            (liftLeft X Y (sX i) :
              Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal)) *
          (∑ j : Fin nY, rightBase (cY j) •
            (liftRight X Y (sY j) :
              Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal)) =
          ∑ pq : Fin nX × Fin nY,
            (leftBase (cX pq.1) * rightBase (cY pq.2)) • w pq := by
        have hterm_eq : ∀ i : Fin nX, ∀ j : Fin nY,
            (leftBase (cX i) •
              (liftLeft X Y (sX i) :
                Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal)) *
            (rightBase (cY j) •
              (liftRight X Y (sY j) :
                Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal)) =
            (leftBase (cX i) * rightBase (cY j)) • w (i, j) := by
          intro i j
          simp only [w, Algebra.smul_def, map_mul]
          ring
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum, hterm_eq]
        exact (Fintype.sum_prod_type
          (fun pq : Fin nX × Fin nY =>
            (leftBase (cX pq.1) * rightBase (cY pq.2)) • w pq)).symm
      rw [hprod]
      apply Submodule.sum_mem
      intro pq _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨pq, rfl⟩
    -- assemble via the separable decomposition
    have hmk : ∀ q : Poly d × Poly d,
        Ideal.Quotient.mk (TrackD.productVariety X Y).ideal
          (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i)) q.1 *
           MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i)) q.2) =
        liftLeft X Y (Ideal.Quotient.mk X.ideal q.1) *
          liftRight X Y (Ideal.Quotient.mk Y.ideal q.2) := by
      intro q
      rfl
    have hsum : Ideal.Quotient.mk (TrackD.productVariety X Y).ideal F ∈
        Submodule.span (Poly (k + k)) (Set.range w) := by
      subst hL
      clear ha
      induction L with
      | nil =>
        simp only [List.map_nil, List.sum_nil, map_zero]
        exact Submodule.zero_mem _
      | cons q qs ih =>
        simp only [List.map_cons, List.sum_cons, map_add, hmk]
        exact Submodule.add_mem _ (hterm q) ih
    exact hsum
  have hFG : (⊤ : Submodule (Poly (k + k))
      (Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal)).FG := by
    have hfin : (Set.range w).Finite := Set.finite_range w
    have hfg := Submodule.fg_span (R := Poly (k + k)) hfin
    rwa [hspan] at hfg
  have hFin : Module.Finite (Poly (k + k))
      (Poly (d + d) ⧸ (TrackD.productVariety X Y).ideal) :=
    Module.finite_def.mpr hFG
  -- convert (instances definitionally equal via mkₐ_toRingHom rfl)
  exact hFin

/-- Left embedding of factor projective variables into product projective space
(`Y0 ↦ X0`, `Y_{succ i} ↦ X_{succ (inl i)}`). -/
def embLeftProj : Fin (d + 1) → Fin ((d + d) + 1) :=
  fun j => Fin.cases 0 (fun i => Fin.succ (finSumFinEquiv (Sum.inl i))) j

/-- Right embedding (`Y0 ↦ X0`, `Y_{succ i} ↦ X_{succ (inr i)}`). -/
def embRightProj : Fin (d + 1) → Fin ((d + d) + 1) :=
  fun j => Fin.cases 0 (fun i => Fin.succ (finSumFinEquiv (Sum.inr i))) j

theorem embLeftProj_zero : embLeftProj (d := d) 0 = 0 := rfl

theorem embRightProj_zero : embRightProj (d := d) 0 = 0 := rfl

theorem embLeftProj_succ (i : Fin d) :
    embLeftProj (d := d) (Fin.succ i) = Fin.succ (finSumFinEquiv (Sum.inl i)) := rfl

theorem embRightProj_succ (i : Fin d) :
    embRightProj (d := d) (Fin.succ i) = Fin.succ (finSumFinEquiv (Sum.inr i)) := rfl

/-- Every product projective polynomial is congruent mod `X0` to a sum of
separable left/right products. `X0`-multiples vanish in the infinity quotient. -/
theorem separableDecompProjList (F : Poly ((d + d) + 1)) :
    ∃ (L : List (Poly (d + 1) × Poly (d + 1))),
      F - (L.map (fun p => MvPolynomial.rename embLeftProj p.1 *
        MvPolynomial.rename embRightProj p.2)).sum ∈
        Ideal.span ({MvPolynomial.X 0} : Set (Poly ((d + d) + 1))) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨[(MvPolynomial.C a, 1)], ?_⟩
    simp [MvPolynomial.rename_C]
  | add f g hf hg =>
    obtain ⟨Lf, hLf⟩ := hf
    obtain ⟨Lg, hLg⟩ := hg
    refine ⟨Lf ++ Lg, ?_⟩
    rw [List.map_append, List.sum_append]
    have hsub : (f + g) -
          ((Lf.map (fun p => MvPolynomial.rename embLeftProj p.1 *
            MvPolynomial.rename embRightProj p.2)).sum +
          (Lg.map (fun p => MvPolynomial.rename embLeftProj p.1 *
            MvPolynomial.rename embRightProj p.2)).sum) =
        (f - (Lf.map (fun p => MvPolynomial.rename embLeftProj p.1 *
          MvPolynomial.rename embRightProj p.2)).sum) +
        (g - (Lg.map (fun p => MvPolynomial.rename embLeftProj p.1 *
          MvPolynomial.rename embRightProj p.2)).sum) := by ring
    rw [hsub]
    exact Ideal.add_mem _ hLf hLg
  | mul_X f j hf =>
    obtain ⟨Lf, hLf⟩ := hf
    cases j using Fin.cases with
    | zero =>
      refine ⟨[], ?_⟩
      simp only [List.map_nil, List.sum_nil, sub_zero]
      have hX0 : f * MvPolynomial.X (0 : Fin ((d + d) + 1)) ∈
          Ideal.span ({MvPolynomial.X 0} : Set (Poly ((d + d) + 1))) := by
        apply Ideal.mem_span_singleton'.mpr
        exact ⟨f, rfl⟩
      -- `X 0` commutes; rewrite to the span form
      have heq : f * MvPolynomial.X (0 : Fin ((d + d) + 1)) =
          MvPolynomial.X 0 * f := by ring
      rw [heq] at hX0 ⊢
      -- goal is `f * X 0 - 0 ∈ span`; same as `X 0 * f ∈ span`
      simpa using hX0
    | succ j =>
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
      cases s with
      | inl i =>
        refine ⟨List.map (fun p : Poly (d + 1) × Poly (d + 1) =>
          (p.1 * MvPolynomial.X (Fin.succ i), p.2)) Lf, ?_⟩
        have hX : MvPolynomial.rename embLeftProj
            (MvPolynomial.X (Fin.succ i) : Poly (d + 1)) =
            (MvPolynomial.X (Fin.succ (finSumFinEquiv (Sum.inl i))) :
              Poly ((d + d) + 1)) := by
          simp [embLeftProj, MvPolynomial.rename_X]
        have hsep : ∀ p : Poly (d + 1) × Poly (d + 1),
            (MvPolynomial.rename embLeftProj (p.1 * MvPolynomial.X (Fin.succ i)) *
            MvPolynomial.rename embRightProj p.2) =
            ((MvPolynomial.rename embLeftProj p.1 *
              MvPolynomial.rename embRightProj p.2) *
            MvPolynomial.rename embLeftProj
              (MvPolynomial.X (Fin.succ i))) := by
          intro p
          rw [map_mul]
          ring
        have hmul : ((Lf.map (fun p => MvPolynomial.rename embLeftProj p.1 *
            MvPolynomial.rename embRightProj p.2)).sum) *
            MvPolynomial.rename embLeftProj
              (MvPolynomial.X (Fin.succ i)) =
            (((List.map (fun p : Poly (d + 1) × Poly (d + 1) =>
              (p.1 * MvPolynomial.X (Fin.succ i), p.2)) Lf).map
              (fun p => MvPolynomial.rename embLeftProj p.1 *
                MvPolynomial.rename embRightProj p.2)).sum) := by
          simp only [List.map_map, Function.comp_def, ← List.sum_map_mul_right, hsep]
        have heq : f * MvPolynomial.X (Fin.succ (finSumFinEquiv (Sum.inl i))) -
            (((List.map (fun p : Poly (d + 1) × Poly (d + 1) =>
              (p.1 * MvPolynomial.X (Fin.succ i), p.2)) Lf).map
              (fun p => MvPolynomial.rename embLeftProj p.1 *
                MvPolynomial.rename embRightProj p.2)).sum) =
            (f - (Lf.map (fun p => MvPolynomial.rename embLeftProj p.1 *
              MvPolynomial.rename embRightProj p.2)).sum) *
            MvPolynomial.X (Fin.succ (finSumFinEquiv (Sum.inl i))) := by
          rw [← hmul, ← hX]
          ring
        rw [heq]
        exact Ideal.mul_mem_right _ _ hLf
      | inr i =>
        refine ⟨List.map (fun p : Poly (d + 1) × Poly (d + 1) =>
          (p.1, p.2 * MvPolynomial.X (Fin.succ i))) Lf, ?_⟩
        have hX : MvPolynomial.rename embRightProj
            (MvPolynomial.X (Fin.succ i) : Poly (d + 1)) =
            (MvPolynomial.X (Fin.succ (finSumFinEquiv (Sum.inr i))) :
              Poly ((d + d) + 1)) := by
          simp [embRightProj, MvPolynomial.rename_X]
        have hsep : ∀ p : Poly (d + 1) × Poly (d + 1),
            (MvPolynomial.rename embLeftProj p.1 *
            MvPolynomial.rename embRightProj (p.2 * MvPolynomial.X (Fin.succ i))) =
            ((MvPolynomial.rename embLeftProj p.1 *
              MvPolynomial.rename embRightProj p.2) *
            MvPolynomial.rename embRightProj
              (MvPolynomial.X (Fin.succ i))) := by
          intro p
          rw [map_mul]
          ring
        have hmul : ((Lf.map (fun p => MvPolynomial.rename embLeftProj p.1 *
            MvPolynomial.rename embRightProj p.2)).sum) *
            MvPolynomial.rename embRightProj
              (MvPolynomial.X (Fin.succ i)) =
            (((List.map (fun p : Poly (d + 1) × Poly (d + 1) =>
              (p.1, p.2 * MvPolynomial.X (Fin.succ i))) Lf).map
              (fun p => MvPolynomial.rename embLeftProj p.1 *
                MvPolynomial.rename embRightProj p.2)).sum) := by
          simp only [List.map_map, Function.comp_def, ← List.sum_map_mul_right, hsep]
        have heq : f * MvPolynomial.X (Fin.succ (finSumFinEquiv (Sum.inr i))) -
            (((List.map (fun p : Poly (d + 1) × Poly (d + 1) =>
              (p.1, p.2 * MvPolynomial.X (Fin.succ i))) Lf).map
              (fun p => MvPolynomial.rename embLeftProj p.1 *
                MvPolynomial.rename embRightProj p.2)).sum) =
            (f - (Lf.map (fun p => MvPolynomial.rename embLeftProj p.1 *
              MvPolynomial.rename embRightProj p.2)).sum) *
            MvPolynomial.X (Fin.succ (finSumFinEquiv (Sum.inr i))) := by
          rw [← hmul, ← hX]
          ring
        rw [heq]
        exact Ideal.mul_mem_right _ _ hLf

theorem embLeft_comp_succ :
    embLeftProj (d := d) ∘ Fin.succ =
      Fin.succ ∘ (fun i : Fin d => finSumFinEquiv (Sum.inl i)) := rfl

theorem embRight_comp_succ :
    embRightProj (d := d) ∘ Fin.succ =
      Fin.succ ∘ (fun i : Fin d => finSumFinEquiv (Sum.inr i)) := rfl

/-- Affine product linear coordinates split (corollary of pullback compatibility
on variables). -/
theorem prodLinearCoord_left {k : ℕ} (ψ : LinearProjection d k) (i : Fin k) :
    linearCoordinate (prodLinear ψ) (finSumFinEquiv (Sum.inl i)) =
      MvPolynomial.rename (fun j : Fin d => finSumFinEquiv (Sum.inl j))
        (linearCoordinate ψ i) := by
  have h := prodPullback_left (d := d) (k := k) ψ (MvPolynomial.X i)
  have hXleft : leftBase (MvPolynomial.X i : Poly k) =
      MvPolynomial.X (finSumFinEquiv (Sum.inl i) : Fin (k + k)) := by
    simp [leftBase, MvPolynomial.rename_X]
  have hpullS : (prodAffine ψ).pullback
      (MvPolynomial.X (finSumFinEquiv (Sum.inl i) : Fin (k + k))) =
      linearCoordinate (prodLinear ψ) (finSumFinEquiv (Sum.inl i)) := by
    simp [AffineProjection.pullback, prodAffine, MvPolynomial.aeval_X]
  have hpullX : (⟨ψ, 0⟩ : AffineProjection d k).pullback
      (MvPolynomial.X i : Poly k) = linearCoordinate ψ i := by
    simp [AffineProjection.pullback, MvPolynomial.aeval_X]
  rw [hXleft, hpullS, hpullX] at h
  exact h

theorem prodLinearCoord_right {k : ℕ} (ψ : LinearProjection d k) (i : Fin k) :
    linearCoordinate (prodLinear ψ) (finSumFinEquiv (Sum.inr i)) =
      MvPolynomial.rename (fun j : Fin d => finSumFinEquiv (Sum.inr j))
        (linearCoordinate ψ i) := by
  have h := prodPullback_right (d := d) (k := k) ψ (MvPolynomial.X i)
  have hXright : rightBase (MvPolynomial.X i : Poly k) =
      MvPolynomial.X (finSumFinEquiv (Sum.inr i) : Fin (k + k)) := by
    simp [rightBase, MvPolynomial.rename_X]
  have hpullS : (prodAffine ψ).pullback
      (MvPolynomial.X (finSumFinEquiv (Sum.inr i) : Fin (k + k))) =
      linearCoordinate (prodLinear ψ) (finSumFinEquiv (Sum.inr i)) := by
    simp [AffineProjection.pullback, prodAffine, MvPolynomial.aeval_X]
  have hpullX : (⟨ψ, 0⟩ : AffineProjection d k).pullback
      (MvPolynomial.X i : Poly k) = linearCoordinate ψ i := by
    simp [AffineProjection.pullback, MvPolynomial.aeval_X]
  rw [hXright, hpullS, hpullX] at h
  exact h

/-- Infinity polynomial compatibility on the left (rename composition +
affine coordinate split). -/
theorem prodInfPoly_left {k : ℕ} (ψ : LinearProjection d k) (i : Fin k) :
    MvPolynomial.rename embLeftProj
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)) =
      MvPolynomial.rename Fin.succ
        (linearCoordinate (prodLinear ψ) (finSumFinEquiv (Sum.inl i))) := by
  rw [prodLinearCoord_left, MvPolynomial.rename_rename,
    MvPolynomial.rename_rename, embLeft_comp_succ]

theorem prodInfPoly_right {k : ℕ} (ψ : LinearProjection d k) (i : Fin k) :
    MvPolynomial.rename embRightProj
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)) =
      MvPolynomial.rename Fin.succ
        (linearCoordinate (prodLinear ψ) (finSumFinEquiv (Sum.inr i))) := by
  rw [prodLinearCoord_right, MvPolynomial.rename_rename,
    MvPolynomial.rename_rename, embRight_comp_succ]

theorem dehom_embLeft (f : Poly (d + 1)) :
    TrackA.normalizationDehomogenize
      (MvPolynomial.rename embLeftProj f) =
      MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i))
        (TrackA.normalizationDehomogenize f) := by
  have hEq : (TrackA.normalizationDehomogenize (n := d + d)).comp
        (MvPolynomial.rename embLeftProj) =
      (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inl i))).comp
        (TrackA.normalizationDehomogenize (n := d)) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j using Fin.cases with
    | zero =>
      simp [TrackA.normalizationDehomogenize, embLeftProj,
        MvPolynomial.aeval_X]
    | succ i =>
      simp [TrackA.normalizationDehomogenize, embLeftProj,
        MvPolynomial.aeval_X, MvPolynomial.rename_X]
  exact AlgHom.congr_fun hEq f

theorem dehom_embRight (f : Poly (d + 1)) :
    TrackA.normalizationDehomogenize
      (MvPolynomial.rename embRightProj f) =
      MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i))
        (TrackA.normalizationDehomogenize f) := by
  have hEq : (TrackA.normalizationDehomogenize (n := d + d)).comp
        (MvPolynomial.rename embRightProj) =
      (MvPolynomial.rename (fun i : Fin d => finSumFinEquiv (Sum.inr i))).comp
        (TrackA.normalizationDehomogenize (n := d)) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j using Fin.cases with
    | zero =>
      simp [TrackA.normalizationDehomogenize, embRightProj,
        MvPolynomial.aeval_X]
    | succ i =>
      simp [TrackA.normalizationDehomogenize, embRightProj,
        MvPolynomial.aeval_X, MvPolynomial.rename_X]
  exact AlgHom.congr_fun hEq f

theorem embLeft_closure_hom {X Y : AffineVariety d} {D : ℕ} {f : Poly (d + 1)}
    (hf : f.IsHomogeneous D) (hmem : f ∈ (projectiveClosure X).ideal) :
    MvPolynomial.rename embLeftProj f ∈
      (projectiveClosure (TrackD.productVariety X Y)).ideal := by
  -- dehomogenize lands in factor ideal, then left inclusion, then homogenize back
  have hdehomX : TrackA.normalizationDehomogenize f ∈ X.ideal :=
    projectiveClosure_aeval_mem X f hmem
  have hdehomS : TrackA.normalizationDehomogenize
      (MvPolynomial.rename embLeftProj f) ∈
      (TrackD.productVariety X Y).ideal := by
    rw [dehom_embLeft]
    exact prod_ideal_left _ hdehomX
  have hhom : (MvPolynomial.rename embLeftProj f).IsHomogeneous D :=
    hf.rename_isHomogeneous
  have hmem_iff := projectiveClosure_homogeneous_mem
    (TrackD.productVariety X Y)
    (MvPolynomial.rename embLeftProj f) hhom
  -- `projectiveClosure_homogeneous_mem` uses `aeval (Fin.cons 1 X)`, same as dehom
  have hdehom_eq : MvPolynomial.aeval (Fin.cons (1 : Poly (d + d)) MvPolynomial.X)
      (MvPolynomial.rename embLeftProj f) =
      TrackA.normalizationDehomogenize (MvPolynomial.rename embLeftProj f) := rfl
  rw [hdehom_eq] at hmem_iff
  exact hmem_iff.mpr hdehomS

theorem embRight_closure_hom {X Y : AffineVariety d} {D : ℕ} {f : Poly (d + 1)}
    (hf : f.IsHomogeneous D) (hmem : f ∈ (projectiveClosure Y).ideal) :
    MvPolynomial.rename embRightProj f ∈
      (projectiveClosure (TrackD.productVariety X Y)).ideal := by
  have hdehomY : TrackA.normalizationDehomogenize f ∈ Y.ideal :=
    projectiveClosure_aeval_mem Y f hmem
  have hdehomS : TrackA.normalizationDehomogenize
      (MvPolynomial.rename embRightProj f) ∈
      (TrackD.productVariety X Y).ideal := by
    rw [dehom_embRight]
    exact prod_ideal_right _ hdehomY
  have hhom : (MvPolynomial.rename embRightProj f).IsHomogeneous D :=
    hf.rename_isHomogeneous
  have hmem_iff := projectiveClosure_homogeneous_mem
    (TrackD.productVariety X Y)
    (MvPolynomial.rename embRightProj f) hhom
  have hdehom_eq : MvPolynomial.aeval (Fin.cons (1 : Poly (d + d)) MvPolynomial.X)
      (MvPolynomial.rename embRightProj f) =
      TrackA.normalizationDehomogenize (MvPolynomial.rename embRightProj f) := rfl
  rw [hdehom_eq] at hmem_iff
  exact hmem_iff.mpr hdehomS

/-- Left embedding sends the factor infinity ideal into the product infinity ideal.
Arbitrary elements reduce to homogeneous components (closure is homogeneous)
plus an `X0`-multiple. -/
theorem embLeft_map_mem {X Y : AffineVariety d} {f : Poly (d + 1)}
    (hf : f ∈ (projectiveClosure X).ideal ⊔ Ideal.span {MvPolynomial.X 0}) :
    MvPolynomial.rename embLeftProj f ∈
      (projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
        Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))} := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
  have hrename_add : MvPolynomial.rename embLeftProj (a + b) =
      MvPolynomial.rename embLeftProj a + MvPolynomial.rename embLeftProj b := map_add _ _ _
  rw [hrename_add]
  apply Ideal.add_mem
  · -- closure part via homogeneous decomposition
    have hhomX := (projectiveClosure X).isHomogeneous
    have hdecomp : a = ∑ i ∈ Finset.range (a.totalDegree + 1),
        MvPolynomial.homogeneousComponent i a := by
      rw [MvPolynomial.sum_homogeneousComponent]
    have hcomp_mem : ∀ i ∈ Finset.range (a.totalDegree + 1),
        MvPolynomial.homogeneousComponent i a ∈ (projectiveClosure X).ideal := by
      intro i _
      exact MvPolynomial.homogeneousComponent_mem_of_mem hhomX ha i
    have hrename_sum : MvPolynomial.rename embLeftProj a =
        ∑ i ∈ Finset.range (a.totalDegree + 1),
          MvPolynomial.rename embLeftProj
            (MvPolynomial.homogeneousComponent i a) := by
      conv_lhs => rw [hdecomp, map_sum]
    rw [hrename_sum]
    apply Ideal.sum_mem
    intro i hi
    have hhom : (MvPolynomial.homogeneousComponent i a).IsHomogeneous i :=
      MvPolynomial.homogeneousComponent_isHomogeneous i a
    have hmem : MvPolynomial.rename embLeftProj
        (MvPolynomial.homogeneousComponent i a) ∈
        (projectiveClosure (TrackD.productVariety X Y)).ideal :=
      embLeft_closure_hom hhom (hcomp_mem i hi)
    exact Ideal.mem_sup_left hmem
  · -- `X0`-span part maps into `X0`-span
    have hbX0 : b ∈ Ideal.span ({MvPolynomial.X 0} : Set (Poly (d + 1))) := hb
    rw [Ideal.mem_span_singleton'] at hbX0
    obtain ⟨h, rfl⟩ := hbX0
    have hX0 : MvPolynomial.rename (R := ℂ) (embLeftProj (d := d))
        (MvPolynomial.X (R := ℂ) (0 : Fin (d + 1))) =
        MvPolynomial.X (R := ℂ) (0 : Fin ((d + d) + 1)) := by
      rw [MvPolynomial.rename_X, embLeftProj_zero]
    have hmem : MvPolynomial.rename (embLeftProj (d := d)) (h * MvPolynomial.X 0) ∈
        Ideal.span ({MvPolynomial.X (0 : Fin ((d + d) + 1))} :
          Set (Poly ((d + d) + 1))) := by
      rw [map_mul, hX0]
      exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    exact Ideal.mem_sup_right hmem

/-- Right embedding sends the factor infinity ideal into the product infinity ideal. -/
theorem embRight_map_mem {X Y : AffineVariety d} {f : Poly (d + 1)}
    (hf : f ∈ (projectiveClosure Y).ideal ⊔ Ideal.span {MvPolynomial.X 0}) :
    MvPolynomial.rename embRightProj f ∈
      (projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
        Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))} := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
  have hrename_add : MvPolynomial.rename embRightProj (a + b) =
      MvPolynomial.rename embRightProj a + MvPolynomial.rename embRightProj b := map_add _ _ _
  rw [hrename_add]
  apply Ideal.add_mem
  · have hhomY := (projectiveClosure Y).isHomogeneous
    have hdecomp : a = ∑ i ∈ Finset.range (a.totalDegree + 1),
        MvPolynomial.homogeneousComponent i a := by
      rw [MvPolynomial.sum_homogeneousComponent]
    have hcomp_mem : ∀ i ∈ Finset.range (a.totalDegree + 1),
        MvPolynomial.homogeneousComponent i a ∈ (projectiveClosure Y).ideal := by
      intro i _
      exact MvPolynomial.homogeneousComponent_mem_of_mem hhomY ha i
    have hrename_sum : MvPolynomial.rename embRightProj a =
        ∑ i ∈ Finset.range (a.totalDegree + 1),
          MvPolynomial.rename embRightProj
            (MvPolynomial.homogeneousComponent i a) := by
      conv_lhs => rw [hdecomp, map_sum]
    rw [hrename_sum]
    apply Ideal.sum_mem
    intro i hi
    have hhom : (MvPolynomial.homogeneousComponent i a).IsHomogeneous i :=
      MvPolynomial.homogeneousComponent_isHomogeneous i a
    have hmem : MvPolynomial.rename embRightProj
        (MvPolynomial.homogeneousComponent i a) ∈
        (projectiveClosure (TrackD.productVariety X Y)).ideal :=
      embRight_closure_hom hhom (hcomp_mem i hi)
    exact Ideal.mem_sup_left hmem
  · have hbX0 : b ∈ Ideal.span ({MvPolynomial.X 0} : Set (Poly (d + 1))) := hb
    rw [Ideal.mem_span_singleton'] at hbX0
    obtain ⟨h, rfl⟩ := hbX0
    have hX0 : MvPolynomial.rename (R := ℂ) (embRightProj (d := d))
        (MvPolynomial.X (R := ℂ) (0 : Fin (d + 1))) =
        MvPolynomial.X (R := ℂ) (0 : Fin ((d + d) + 1)) := by
      rw [MvPolynomial.rename_X, embRightProj_zero]
    have hmem : MvPolynomial.rename (embRightProj (d := d)) (h * MvPolynomial.X 0) ∈
        Ideal.span ({MvPolynomial.X (0 : Fin ((d + d) + 1))} :
          Set (Poly ((d + d) + 1))) := by
      rw [map_mul, hX0]
      exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    exact Ideal.mem_sup_right hmem

/-- Left infinity lift (factor infinity quotient to product infinity quotient). -/
def liftLeftInf (X Y : AffineVariety d) :
    (Poly (d + 1) ⧸ ((projectiveClosure X).ideal ⊔ Ideal.span {MvPolynomial.X 0})) →ₐ[ℂ]
      (Poly ((d + d) + 1) ⧸ ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
        Ideal.span {MvPolynomial.X 0})) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℂ _).comp
    (MvPolynomial.rename embLeftProj)) (by
    intro f hf
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact embLeft_map_mem hf)

/-- Right infinity lift. -/
def liftRightInf (X Y : AffineVariety d) :
    (Poly (d + 1) ⧸ ((projectiveClosure Y).ideal ⊔ Ideal.span {MvPolynomial.X 0})) →ₐ[ℂ]
      (Poly ((d + d) + 1) ⧸ ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
        Ideal.span {MvPolynomial.X 0})) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℂ _).comp
    (MvPolynomial.rename embRightProj)) (by
    intro f hf
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact embRight_map_mem hf)

theorem prodInfMap_left {k : ℕ} (ψ : LinearProjection d k)
    {X Y : AffineVariety d} :
    (liftLeftInf X Y).comp
        (MvPolynomial.aeval (R := ℂ) (fun i =>
          Ideal.Quotient.mk ((projectiveClosure X).ideal ⊔
            Ideal.span {MvPolynomial.X 0})
            (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))) =
      (MvPolynomial.aeval (R := ℂ) (fun j =>
        Ideal.Quotient.mk ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
          Ideal.span {MvPolynomial.X 0})
          (MvPolynomial.rename Fin.succ
            (linearCoordinate (prodLinear ψ) j)))).comp leftBase := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, leftBase,
    MvPolynomial.rename_X]
  have hL : liftLeftInf X Y
      (Ideal.Quotient.mk ((projectiveClosure X).ideal ⊔
        Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i))) =
      Ideal.Quotient.mk ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
        Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename embLeftProj
          (MvPolynomial.rename Fin.succ (linearCoordinate ψ i))) := rfl
  rw [hL, prodInfPoly_left]

theorem prodInfMap_right {k : ℕ} (ψ : LinearProjection d k)
    {X Y : AffineVariety d} :
    (liftRightInf X Y).comp
        (MvPolynomial.aeval (R := ℂ) (fun i =>
          Ideal.Quotient.mk ((projectiveClosure Y).ideal ⊔
            Ideal.span {MvPolynomial.X 0})
            (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))) =
      (MvPolynomial.aeval (R := ℂ) (fun j =>
        Ideal.Quotient.mk ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
          Ideal.span {MvPolynomial.X 0})
          (MvPolynomial.rename Fin.succ
            (linearCoordinate (prodLinear ψ) j)))).comp rightBase := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, rightBase,
    MvPolynomial.rename_X]
  have hL : liftRightInf X Y
      (Ideal.Quotient.mk ((projectiveClosure Y).ideal ⊔
        Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i))) =
      Ideal.Quotient.mk ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
        Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename embRightProj
          (MvPolynomial.rename Fin.succ (linearCoordinate ψ i))) := rfl
  rw [hL, prodInfPoly_right]

/-- Product infinity parameters are finite from factor infinity finiteness. -/
theorem prodInfinityFinite {k : ℕ} {ψ : LinearProjection d k}
    {X Y : AffineVariety d}
    (hinfX : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure X).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite)
    (hinfY : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure Y).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite) :
    (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
        Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ
          (linearCoordinate (prodLinear ψ) i)))).Finite := by
  classical
  -- abbreviations for the three infinity maps and quotients
  let QX := Poly (d + 1) ⧸ ((projectiveClosure X).ideal ⊔
    Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})
  let QY := Poly (d + 1) ⧸ ((projectiveClosure Y).ideal ⊔
    Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})
  let QS := Poly ((d + d) + 1) ⧸ ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
    Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))})
  let aX : Poly k →ₐ[ℂ] QX := MvPolynomial.aeval (fun i =>
    Ideal.Quotient.mk ((projectiveClosure X).ideal ⊔
      Ideal.span {MvPolynomial.X 0})
      (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))
  let aY : Poly k →ₐ[ℂ] QY := MvPolynomial.aeval (fun i =>
    Ideal.Quotient.mk ((projectiveClosure Y).ideal ⊔
      Ideal.span {MvPolynomial.X 0})
      (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))
  let aS : Poly (k + k) →ₐ[ℂ] QS := MvPolynomial.aeval (fun j =>
    Ideal.Quotient.mk ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
      Ideal.span {MvPolynomial.X 0})
      (MvPolynomial.rename Fin.succ (linearCoordinate (prodLinear ψ) j)))
  letI := aX.toRingHom.toAlgebra
  letI : Module (Poly k) QX := aX.toRingHom.toAlgebra.toModule
  letI := aY.toRingHom.toAlgebra
  letI : Module (Poly k) QY := aY.toRingHom.toAlgebra.toModule
  letI := aS.toRingHom.toAlgebra
  letI : Module (Poly (k + k)) QS := aS.toRingHom.toAlgebra.toModule
  haveI hFX : Module.Finite (Poly k) QX := hinfX
  haveI hFY : Module.Finite (Poly k) QY := hinfY
  obtain ⟨nX, sX, hsX⟩ := Module.Finite.exists_fin (R := Poly k) (M := QX)
  obtain ⟨nY, sY, hsY⟩ := Module.Finite.exists_fin (R := Poly k) (M := QY)
  let w : Fin nX × Fin nY → QS :=
    fun pq => liftLeftInf X Y (sX pq.1) * liftRightInf X Y (sY pq.2)
  have hspan : Submodule.span (Poly (k + k)) (Set.range w) = ⊤ := by
    apply top_unique
    intro a ha
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective
      (I := ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
        Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))})) a
    obtain ⟨L, hL⟩ := separableDecompProjList (d := d) F
    -- each separable term lies in the span
    have hterm : ∀ p : Poly (d + 1) × Poly (d + 1),
        liftLeftInf X Y (Ideal.Quotient.mk
          ((projectiveClosure X).ideal ⊔ Ideal.span {MvPolynomial.X 0}) p.1) *
          liftRightInf X Y (Ideal.Quotient.mk
            ((projectiveClosure Y).ideal ⊔ Ideal.span {MvPolynomial.X 0}) p.2) ∈
          Submodule.span (Poly (k + k)) (Set.range w) := by
      intro p
      have hmemX : Ideal.Quotient.mk
          ((projectiveClosure X).ideal ⊔ Ideal.span {MvPolynomial.X 0}) p.1 ∈
          Submodule.span (Poly k) (Set.range sX) := hsX.symm ▸ Submodule.mem_top
      have hmemY : Ideal.Quotient.mk
          ((projectiveClosure Y).ideal ⊔ Ideal.span {MvPolynomial.X 0}) p.2 ∈
          Submodule.span (Poly k) (Set.range sY) := hsY.symm ▸ Submodule.mem_top
      obtain ⟨cX, hcX⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmemX
      obtain ⟨cY, hcY⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmemY
      have hLX : liftLeftInf X Y (Ideal.Quotient.mk
          ((projectiveClosure X).ideal ⊔ Ideal.span {MvPolynomial.X 0}) p.1) =
          ∑ i : Fin nX, leftBase (cX i) •
            (liftLeftInf X Y (sX i) : QS) := by
        have hmap : ∀ c : Poly k, ∀ s : QX,
            liftLeftInf X Y (c • s) = (leftBase c) • (liftLeftInf X Y s : QS) := by
          intro c s
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1
          have hXalg : algebraMap (Poly k) QX c = aX c := rfl
          have hSalg : algebraMap (Poly (k + k)) QS (leftBase c) =
              aS (leftBase c) := rfl
          rw [hXalg, hSalg]
          exact AlgHom.congr_fun (prodInfMap_left (d := d) ψ (X := X) (Y := Y)) c
        conv_lhs => rw [← hcX]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact hmap _ _
      have hRY : liftRightInf X Y (Ideal.Quotient.mk
          ((projectiveClosure Y).ideal ⊔ Ideal.span {MvPolynomial.X 0}) p.2) =
          ∑ j : Fin nY, rightBase (cY j) •
            (liftRightInf X Y (sY j) : QS) := by
        have hmap : ∀ c : Poly k, ∀ s : QY,
            liftRightInf X Y (c • s) = (rightBase c) •
              (liftRightInf X Y s : QS) := by
          intro c s
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1
          have hYalg : algebraMap (Poly k) QY c = aY c := rfl
          have hSalg : algebraMap (Poly (k + k)) QS (rightBase c) =
              aS (rightBase c) := rfl
          rw [hYalg, hSalg]
          exact AlgHom.congr_fun (prodInfMap_right (d := d) ψ (X := X) (Y := Y)) c
        conv_lhs => rw [← hcY]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact hmap _ _
      rw [hLX, hRY]
      have hprod : (∑ i : Fin nX, leftBase (cX i) •
            (liftLeftInf X Y (sX i) : QS)) *
          (∑ j : Fin nY, rightBase (cY j) •
            (liftRightInf X Y (sY j) : QS)) =
          ∑ pq : Fin nX × Fin nY,
            (leftBase (cX pq.1) * rightBase (cY pq.2)) • w pq := by
        have hterm_eq : ∀ i : Fin nX, ∀ j : Fin nY,
            (leftBase (cX i) • (liftLeftInf X Y (sX i) : QS)) *
            (rightBase (cY j) • (liftRightInf X Y (sY j) : QS)) =
            (leftBase (cX i) * rightBase (cY j)) • w (i, j) := by
          intro i j
          simp only [w, Algebra.smul_def, map_mul]
          ring
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum, hterm_eq]
        exact (Fintype.sum_prod_type
          (fun pq : Fin nX × Fin nY =>
            (leftBase (cX pq.1) * rightBase (cY pq.2)) • w pq)).symm
      rw [hprod]
      apply Submodule.sum_mem
      intro pq _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨pq, rfl⟩
    -- assemble: `mk F = mk Σ` since difference in `X0`-span ⊆ `J_S`, then induction
    have hJS : Ideal.span ({MvPolynomial.X (0 : Fin ((d + d) + 1))} :
        Set (Poly ((d + d) + 1))) ≤
        ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
          Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))}) :=
      le_sup_right
    have hdiff : F - (L.map (fun p => MvPolynomial.rename embLeftProj p.1 *
        MvPolynomial.rename embRightProj p.2)).sum ∈
        ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
          Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))}) :=
      hJS hL
    have hmkEq : Ideal.Quotient.mk
        ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
          Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))}) F =
        Ideal.Quotient.mk
          ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
            Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))})
          ((L.map (fun p => MvPolynomial.rename embLeftProj p.1 *
            MvPolynomial.rename embRightProj p.2)).sum) := by
      have hsub : Ideal.Quotient.mk
          ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
            Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))})
          (F - (L.map (fun p => MvPolynomial.rename embLeftProj p.1 *
            MvPolynomial.rename embRightProj p.2)).sum) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
      have hmap : Ideal.Quotient.mk
          ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
            Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))})
          (F - (L.map (fun p => MvPolynomial.rename embLeftProj p.1 *
            MvPolynomial.rename embRightProj p.2)).sum) =
          Ideal.Quotient.mk
            ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
              Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))}) F -
            Ideal.Quotient.mk
              ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
                Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))})
              ((L.map (fun p => MvPolynomial.rename embLeftProj p.1 *
                MvPolynomial.rename embRightProj p.2)).sum) :=
        map_sub _ _ _
      rw [hmap] at hsub
      exact sub_eq_zero.mp hsub
    have hmk : ∀ q : Poly (d + 1) × Poly (d + 1),
        Ideal.Quotient.mk
          ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
            Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))})
          (MvPolynomial.rename embLeftProj q.1 *
           MvPolynomial.rename embRightProj q.2) =
        liftLeftInf X Y (Ideal.Quotient.mk
          ((projectiveClosure X).ideal ⊔ Ideal.span {MvPolynomial.X 0}) q.1) *
          liftRightInf X Y (Ideal.Quotient.mk
            ((projectiveClosure Y).ideal ⊔ Ideal.span {MvPolynomial.X 0}) q.2) := by
      intro q
      rfl
    have hall : ∀ L : List (Poly (d + 1) × Poly (d + 1)),
        Ideal.Quotient.mk
          ((projectiveClosure (TrackD.productVariety X Y)).ideal ⊔
            Ideal.span {MvPolynomial.X (0 : Fin ((d + d) + 1))})
          ((L.map (fun p => MvPolynomial.rename embLeftProj p.1 *
            MvPolynomial.rename embRightProj p.2)).sum) ∈
          Submodule.span (Poly (k + k)) (Set.range w) := by
      intro L
      induction L with
      | nil =>
        simp only [List.map_nil, List.sum_nil, map_zero]
        exact Submodule.zero_mem _
      | cons q qs ih =>
        simp only [List.map_cons, List.sum_cons, map_add, hmk]
        exact Submodule.add_mem _ (hterm q) ih
    have hsum := hall L
    rw [← hmkEq] at hsum
    exact hsum
  have hFG : (⊤ : Submodule (Poly (k + k)) QS).FG := by
    have hfin : (Set.range w).Finite := Set.finite_range w
    have hfg := Submodule.fg_span (R := Poly (k + k)) hfin
    rwa [hspan] at hfg
  have hFin : Module.Finite (Poly (k + k)) QS := Module.finite_def.mpr hFG
  exact hFin

/-- Affine projection rank coincides with normalization rank at zero offset. -/
theorem projRank_eq_normRank {n k : ℕ} (V : AffineVariety n)
    (ψ : LinearProjection n k) :
    TrackA.affineProjectionRank V (⟨ψ, 0⟩ : AffineProjection n k) =
      TrackA.affineNormalizationRank V ψ := by
  unfold TrackA.affineProjectionRank TrackA.affineNormalizationRank
  have hmap : TrackA.affineProjectionMap V (⟨ψ, 0⟩ : AffineProjection n k) =
      TrackA.affineNormalizationMap V ψ := by
    simp only [TrackA.affineProjectionMap]
    exact (TrackA.affineNormalizationMap_eq_projection_pullback V ψ).symm
  rw [hmap]

/-- Ambient dimension bounds irreducible dimension (local copy to avoid
circular imports with MODegAux). -/
theorem prod_dim_le {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) : V.dimension ≤ n := by
  letI : V.ideal.IsPrime := hV
  have htrdeg : Algebra.trdeg ℂ (Poly n ⧸ V.ideal) ≤ (n : Cardinal) := by
    have hsurj := Ideal.Quotient.mk_surjective (I := V.ideal)
    have h := trdeg_le_of_surjective (Ideal.Quotient.mkₐ ℂ V.ideal) hsurj
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin,
      Cardinal.lift_natCast] using h
  have hdim := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg V.ideal
    (OAI.QuarticPowerFree.coordinateHilbert V.ideal)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal)
  have hle : (V.dimension : Cardinal) ≤ (n : Cardinal) := by
    change ((OAI.QuarticPowerFree.coordinateHilbert V.ideal).natDegree : Cardinal) ≤ _
    rw [hdim]
    exact htrdeg
  exact_mod_cast hle

/-- Product degree equals product of degrees (rational version). -/
theorem prodDegreeEq {k : ℕ} {X Y : AffineVariety d}
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXd : X.dimension = k) (hYd : Y.dimension = k) :
    ((TrackD.productVariety X Y).degree : ℚ) = X.degree * Y.degree := by
  classical
  have hk : k ≤ d := by
    rw [← hXd]
    exact prod_dim_le X hX
  -- common pure family {X, Y}
  let F : AffineFamily.Family d := {X, Y}
  have hF : AffineFamily.IsPure F k := by
    intro V hV
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hV
    rcases hV with rfl | rfl
    · exact ⟨hX, hXd⟩
    · exact ⟨hY, hYd⟩
  obtain ⟨ψ, hψsurj, hψinf⟩ :=
    TrackA.family_infinity_normalized_linear_projection F hk hF
  have hfXinf := hψinf X (by simp [F])
  have hfYinf := hψinf Y (by simp [F, Finset.mem_insert])
  have hfXfin : TrackA.FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection d k) X :=
    TrackA.finite_affine_projection_of_infinity_parameters X ψ hfXinf
  have hfYfin : TrackA.FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection d k) Y :=
    TrackA.finite_affine_projection_of_infinity_parameters Y ψ hfYinf
  obtain ⟨rX, hrXdeg, hrXgen⟩ :=
    TrackA.request_infinity_projection_generic_degree X hX hXd ψ hψsurj hfXinf
  obtain ⟨rY, hrYdeg, hrYgen⟩ :=
    TrackA.request_infinity_projection_generic_degree Y hY hYd ψ hψsurj hfYinf
  have hSirr := TrackD.productVariety_irreducible X Y hX hY
  have hSdim : (TrackD.productVariety X Y).dimension = k + k := by
    rw [TrackD.product_dimension X Y hX hY, hXd, hYd]
  have hfSfin : TrackA.FiniteAffineProjection (prodAffine ψ)
      (TrackD.productVariety X Y) := prodFinite hfXfin hfYfin
  have hSgen : (prodAffine ψ).GenericallyFiniteOfDegree
      (TrackD.productVariety X Y) (rX * rY) :=
    prodGenericallyFinite hX hY hXd hYd hfXfin hfYfin hrXgen hrYgen hfSfin
  have hrank : TrackA.affineProjectionRank (TrackD.productVariety X Y)
      (prodAffine ψ) = rX * rY :=
    TrackA.affineProjectionRank_eq_genericDegree _ hSirr hSdim _ hfSfin hSgen
  -- rank = degree via infinity finiteness for the product projection
  have hSinf := prodInfinityFinite (X := X) (Y := Y) (ψ := ψ) hfXinf hfYinf
  have hdeg : ((TrackA.affineNormalizationRank (TrackD.productVariety X Y)
      (prodLinear ψ) : ℕ) : ℚ) = (TrackD.productVariety X Y).degree :=
    TrackA.infinity_normalization_affine_rank_eq_degree _ hSirr hSdim _ hSinf
  have hrankEq : TrackA.affineProjectionRank (TrackD.productVariety X Y)
      (prodAffine ψ) =
      TrackA.affineNormalizationRank (TrackD.productVariety X Y) (prodLinear ψ) := by
    have h0 : (prodAffine ψ : AffineProjection (d + d) (k + k)) =
        (⟨prodLinear ψ, 0⟩ : AffineProjection (d + d) (k + k)) := rfl
    rw [h0]
    exact projRank_eq_normRank _ _
  rw [hrankEq] at hrank
  have hrankQ : ((rX * rY : ℕ) : ℚ) = (TrackD.productVariety X Y).degree := by
    rw [← hrank]
    exact hdeg
  rw [Nat.cast_mul] at hrankQ
  rw [hrXdeg, hrYdeg] at hrankQ
  exact hrankQ.symm


end
end DistinctDistances.SparseCones
