import DistinctDistances.TrackD.PerspectiveGroup

/-! Elementary linear algebra of the projective chart in `secants.tex:351–357`.
A projectivity fixing the line at infinity pointwise acts by a scalar-affine map. -/

namespace DistinctDistances.TrackD

open scoped Classical
noncomputable section

/-- An endomorphism of the two-dimensional coordinate plane that sends every
vector to its own line is multiplication by one common scalar. -/
theorem plane_linewise_map_scalar (T : Point 2 →ₗ[ℂ] Point 2)
    (hline : ∀ x, ∃ a : ℂ, T x = a • x) :
    ∃ a : ℂ, ∀ x, T x = a • x := by
  let e₀ : Point 2 := Pi.single (0 : Fin 2) 1
  let e₁ : Point 2 := Pi.single (1 : Fin 2) 1
  obtain ⟨a₀, ha₀⟩ := hline e₀
  obtain ⟨a₁, ha₁⟩ := hline e₁
  obtain ⟨a, ha⟩ := hline (e₀ + e₁)
  have heq : a₀ • e₀ + a₁ • e₁ = a • (e₀ + e₁) := by
    rw [← ha₀, ← ha₁, ← map_add, ha]
  have h₀ : a₀ = a := by
    have h := congrFun heq (0 : Fin 2)
    simpa [e₀, e₁] using h
  have h₁ : a₁ = a := by
    have h := congrFun heq (1 : Fin 2)
    simpa [e₀, e₁] using h
  refine ⟨a, ?_⟩
  intro x
  have hx : x = x 0 • e₀ + x 1 • e₁ := by
    ext i
    fin_cases i <;> simp [e₀, e₁]
  rw [hx, map_add, map_smul, map_smul, ha₀, ha₁, h₀, h₁]
  simp [smul_add, smul_smul, mul_comm]

/-- In homogeneous coordinates `(x,t)`, a linear representative fixing the
line `t=0` pointwise has the scalar block form `(a x + t b, c t)`. -/
theorem projective_fixed_line_block_form
    (T : (Point 2 × ℂ) →ₗ[ℂ] (Point 2 × ℂ))
    (hline : ∀ x : Point 2, ∃ a : ℂ, T (x, 0) = (a • x, 0)) :
    ∃ (a c : ℂ) (b : Point 2), ∀ (x : Point 2) (t : ℂ),
      T (x, t) = (a • x + t • b, c * t) := by
  let A : Point 2 →ₗ[ℂ] Point 2 :=
    (LinearMap.fst ℂ (Point 2) ℂ).comp (T.comp (LinearMap.inl ℂ (Point 2) ℂ))
  obtain ⟨a, ha⟩ := plane_linewise_map_scalar A (by
    intro x
    obtain ⟨a, h⟩ := hline x
    exact ⟨a, congrArg Prod.fst h⟩)
  have hzero : ∀ x : Point 2, (T (x, 0)).2 = 0 := by
    intro x
    obtain ⟨a, h⟩ := hline x
    exact congrArg Prod.snd h
  refine ⟨a, (T (0, 1)).2, (T (0, 1)).1, ?_⟩
  intro x t
  have hdecomp : (x, t) = (x, 0) + t • ((0, 1) : Point 2 × ℂ) := by simp
  rw [hdecomp, map_add, map_smul]
  apply Prod.ext
  · change (T (x, 0)).1 + t • (T (0, 1)).1 = _
    rw [show (T (x, 0)).1 = a • x from ha x]
  · change (T (x, 0)).2 + t * (T (0, 1)).2 = _
    rw [hzero]
    simp [mul_comm]

/-- For an invertible representative, both diagonal scalars in the block form
are nonzero. The chart `t=1` therefore has unit scalar `a/c` and offset `b/c`. -/
theorem projective_fixed_line_diagonal_nonzero
    (T : (Point 2 × ℂ) ≃ₗ[ℂ] (Point 2 × ℂ))
    (a c : ℂ) (b : Point 2)
    (hform : ∀ (x : Point 2) (t : ℂ), T (x, t) = (a • x + t • b, c * t)) :
    a ≠ 0 ∧ c ≠ 0 := by
  constructor
  · intro ha
    let e₀ : Point 2 := Pi.single (0 : Fin 2) 1
    have hz : T (e₀, 0) = T (0, 0) := by simp [hform, ha]
    have heq := T.injective hz
    have h := congrFun (congrArg Prod.fst heq) (0 : Fin 2)
    simpa [e₀] using h
  · intro hc
    obtain ⟨⟨x, t⟩, hx⟩ := T.surjective ((0, 1) : Point 2 × ℂ)
    have h := congrArg Prod.snd hx
    simp [hform, hc] at h

/-- After normalizing the final homogeneous coordinate, a projectivity fixing
the line at infinity has precisely the concrete scalar-affine form. -/
theorem projective_fixed_line_scalar_affine
    (T : (Point 2 × ℂ) ≃ₗ[ℂ] (Point 2 × ℂ))
    (hline : ∀ x : Point 2, ∃ a : ℂ, T (x, 0) = (a • x, 0)) :
    ∃ g : ScalarAffine, ∀ x : Point 2,
      (T (x, 1)).2 ≠ 0 ∧
        ((T (x, 1)).2)⁻¹ • (T (x, 1)).1 = ScalarAffine.act g x := by
  obtain ⟨a, c, b, hform⟩ := projective_fixed_line_block_form T.toLinearMap hline
  obtain ⟨ha, hc⟩ := projective_fixed_line_diagonal_nonzero T a c b hform
  let g : ScalarAffine := ⟨Units.mk0 (a / c) (div_ne_zero ha hc), c⁻¹ • b⟩
  refine ⟨g, ?_⟩
  intro x
  have hform' : T (x, 1) = (a • x + b, c) := by simpa using hform x 1
  rw [hform']
  refine ⟨by simpa using hc, ?_⟩
  simp [g, ScalarAffine.act, smul_add, smul_smul, div_eq_mul_inv, mul_comm]

end
end DistinctDistances.TrackD
