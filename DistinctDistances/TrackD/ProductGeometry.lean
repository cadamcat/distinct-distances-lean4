import DistinctDistances.TrackD.PairGenericity

namespace DistinctDistances.TrackD

noncomputable section
variable {d : ℕ}

/-- Product coordinates in the shared affine-variety model. -/
def productPoint (x y : Point d) : Point (d + d) :=
  pairPt x y ∘ finSumFinEquiv.symm

def productLeft (p : Point (d + d)) : Point d := fun i => p (finSumFinEquiv (Sum.inl i))
def productRight (p : Point (d + d)) : Point d := fun i => p (finSumFinEquiv (Sum.inr i))

@[simp] theorem productPoint_left_right (p : Point (d + d)) :
    productPoint (productLeft p) (productRight p) = p := by
  funext i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp only [productPoint, productLeft, productRight,
    Function.comp_apply, Equiv.symm_apply_apply, pairPt, Sum.elim_inl, Sum.elim_inr]

@[simp] theorem eval_product_rename (f : Poly (d + d)) (x y : Point d) :
    MvPolynomial.eval (pairPt x y) (MvPolynomial.rename finSumFinEquiv.symm f) =
      MvPolynomial.eval (productPoint x y) f := by
  rw [MvPolynomial.eval_rename]
  rfl

@[simp] theorem eval_product_left_rename (f : Poly d) (x y : Point d) :
    MvPolynomial.eval (productPoint x y)
      (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) f) = MvPolynomial.eval x f := by
  rw [MvPolynomial.eval_rename]
  have heq : productPoint x y ∘ (fun i : Fin d => finSumFinEquiv (Sum.inl i)) = x := by
    funext i
    change pairPt x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = x i
    rw [Equiv.symm_apply_apply]
    rfl
  rw [heq]

@[simp] theorem eval_product_right_rename (f : Poly d) (x y : Point d) :
    MvPolynomial.eval (productPoint x y)
      (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inr i)) f) = MvPolynomial.eval y f := by
  rw [MvPolynomial.eval_rename]
  have heq : productPoint x y ∘ (fun i : Fin d => finSumFinEquiv (Sum.inr i)) = y := by
    funext i
    change pairPt x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) = y i
    rw [Equiv.symm_apply_apply]
    rfl
  rw [heq]

/-- The product remains an ordinary `AffineVariety`, rather than introducing
a second variety model for secant labels. -/
def productVariety (X Y : AffineVariety d) : AffineVariety (d + d) :=
  AffineVariety.closure {p | ∃ x ∈ X, ∃ y ∈ Y, productPoint x y = p}

theorem irreducible_points_nonempty (X : AffineVariety d) (hX : X.IsIrreducible) :
    X.points.Nonempty := by
  by_contra h
  have he : X.points = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hI := X.vanishingIdeal_points
  rw [he, MvPolynomial.vanishingIdeal_empty] at hI
  exact hX.ne_top hI.symm

@[simp] theorem productVariety_points (X Y : AffineVariety d) :
    (productVariety X Y).points = {p | productLeft p ∈ X ∧ productRight p ∈ Y} := by
  ext p
  constructor
  · intro hp
    constructor
    · intro f hf
      let F : Poly (d + d) := MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) f
      have hF : F ∈ (productVariety X Y).ideal := by
        intro q hq
        obtain ⟨x, hx, y, hy, rfl⟩ := hq
        change MvPolynomial.eval (productPoint x y)
          (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) f) = 0
        rw [eval_product_left_rename]
        exact hx f hf
      have hh := hp F hF
      change MvPolynomial.eval p F = 0 at hh
      change MvPolynomial.eval (fun i => p (finSumFinEquiv (Sum.inl i))) f = 0
      simpa only [F, MvPolynomial.eval_rename, Function.comp_def] using hh
    · intro f hf
      let F : Poly (d + d) := MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inr i)) f
      have hF : F ∈ (productVariety X Y).ideal := by
        intro q hq
        obtain ⟨x, hx, y, hy, rfl⟩ := hq
        change MvPolynomial.eval (productPoint x y)
          (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inr i)) f) = 0
        rw [eval_product_right_rename]
        exact hy f hf
      have hh := hp F hF
      change MvPolynomial.eval p F = 0 at hh
      change MvPolynomial.eval (fun i => p (finSumFinEquiv (Sum.inr i))) f = 0
      simpa only [F, MvPolynomial.eval_rename, Function.comp_def] using hh
  · rintro ⟨hx, hy⟩
    apply AffineVariety.subset_closure
    exact ⟨productLeft p, hx, productRight p, hy, productPoint_left_right p⟩

theorem productVariety_irreducible (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible) :
    (productVariety X Y).IsIrreducible := by
  apply Ideal.isPrime_iff.mpr
  constructor
  · obtain ⟨x, hx⟩ := irreducible_points_nonempty X hX
    obtain ⟨y, hy⟩ := irreducible_points_nonempty Y hY
    intro htop
    have hone : (1 : Poly (d + d)) ∈ (productVariety X Y).ideal := by rw [htop]; trivial
    have h := hone (productPoint x y) ⟨x, hx, y, hy, rfl⟩
    simpa using h
  · intro f g hfg
    by_contra h
    push Not at h
    have hf : ∃ x ∈ X, ∃ y ∈ Y,
        MvPolynomial.eval (productPoint x y) f ≠ 0 := by
      by_contra hh
      push Not at hh
      apply h.1
      intro p hp
      obtain ⟨x, hx, y, hy, rfl⟩ := hp
      exact hh x hx y hy
    have hg : ∃ x ∈ X, ∃ y ∈ Y,
        MvPolynomial.eval (productPoint x y) g ≠ 0 := by
      by_contra hh
      push Not at hh
      apply h.2
      intro p hp
      obtain ⟨x, hx, y, hy, rfl⟩ := hp
      exact hh x hx y hy
    have hfgen : ForGeneralPair X Y (fun x y => MvPolynomial.eval (productPoint x y) f ≠ 0) := by
      refine ⟨MvPolynomial.rename finSumFinEquiv.symm f, ?_, ?_⟩
      · simpa using hf
      · intro x hx y hy hn
        simpa using hn
    have hggen : ForGeneralPair X Y (fun x y => MvPolynomial.eval (productPoint x y) g ≠ 0) := by
      refine ⟨MvPolynomial.rename finSumFinEquiv.symm g, ?_, ?_⟩
      · simpa using hg
      · intro x hx y hy hn
        simpa using hn
    obtain ⟨x, hx, y, hy, hfx, hgx⟩ := (hfgen.and hX hY hggen).exists
    have hz := hfg (productPoint x y) ⟨x, hx, y, hy, rfl⟩
    rw [map_mul] at hz
    exact (mul_ne_zero hfx hgx) hz

end
end DistinctDistances.TrackD
