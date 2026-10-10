import DistinctDistances.TrackD.PerspectiveGeometry

/-! The concrete group of affine plane maps fixing the line at infinity pointwise,
used in the perspective comparison in `secants.tex:351–370`. -/

namespace DistinctDistances.TrackD

open scoped Classical
noncomputable section

@[ext] structure ScalarAffine where
  scalar : ℂˣ
  offset : Point 2

namespace ScalarAffine

instance : One ScalarAffine := ⟨⟨1, 0⟩⟩
instance : Mul ScalarAffine := ⟨fun g h =>
  ⟨g.scalar * h.scalar, (g.scalar : ℂ) • h.offset + g.offset⟩⟩
instance : Inv ScalarAffine := ⟨fun g =>
  ⟨g.scalar⁻¹, (-((g.scalar⁻¹ : ℂˣ) : ℂ)) • g.offset⟩⟩

@[simp] theorem scalar_one : (1 : ScalarAffine).scalar = 1 := rfl
@[simp] theorem offset_one : (1 : ScalarAffine).offset = 0 := rfl
@[simp] theorem scalar_mul (g h : ScalarAffine) :
    (g * h).scalar = g.scalar * h.scalar := rfl
@[simp] theorem offset_mul (g h : ScalarAffine) :
    (g * h).offset = (g.scalar : ℂ) • h.offset + g.offset := rfl
@[simp] theorem scalar_inv (g : ScalarAffine) : (g⁻¹).scalar = g.scalar⁻¹ := rfl
@[simp] theorem offset_inv (g : ScalarAffine) :
    (g⁻¹).offset = -((g.scalar⁻¹ : ℂˣ) : ℂ) • g.offset := rfl

instance : Group ScalarAffine where
  mul_assoc g h k := by
    apply ScalarAffine.ext
    · simp [mul_assoc]
    · simp [smul_add, mul_smul, add_assoc]
  one_mul g := by
    apply ScalarAffine.ext <;> simp
  mul_one g := by
    apply ScalarAffine.ext <;> simp
  inv_mul_cancel g := by
    apply ScalarAffine.ext <;> simp

def act (g : ScalarAffine) (x : Point 2) : Point 2 :=
  (g.scalar : ℂ) • x + g.offset

@[simp] theorem act_one (x : Point 2) : act 1 x = x := by simp [act]

theorem act_mul (g h : ScalarAffine) (x : Point 2) :
    act (g * h) x = act g (act h x) := by
  simp [act, smul_add, mul_smul, add_assoc]

@[simp] theorem act_inv_act (g : ScalarAffine) (x : Point 2) :
    act g⁻¹ (act g x) = x := by rw [← act_mul, inv_mul_cancel, act_one]

@[simp] theorem act_act_inv (g : ScalarAffine) (x : Point 2) :
    act g (act g⁻¹ x) = x := by rw [← act_mul, mul_inv_cancel, act_one]

def scalarHom : ScalarAffine →* ℂˣ where
  toFun := scalar
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Equality of the curve's point set is used, so the inverse also preserves it. -/
def stabilizer (Y : AffineVariety 2) : Subgroup ScalarAffine where
  carrier := {g | ∀ x, act g x ∈ Y ↔ x ∈ Y}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x
    rw [act_mul, hg, hh]
  inv_mem' := by
    intro g hg x
    simpa using (hg (act g⁻¹ x)).symm

theorem stabilizer_faithful (Y : AffineVariety 2) (g : stabilizer Y)
    (hs : g.val.scalar = 1) (hb : g.val.offset = 0) : g = 1 := by
  apply Subtype.ext
  apply ScalarAffine.ext <;> assumption

/-- The full scalar-affine stabilizer has the bound supplied by the abstract
homothety argument; no finiteness hypothesis on this group is imposed. -/
theorem stabilizer_degree_bound (Y : AffineVariety 2) (hY : IsCurve Y)
    (hne : Y.points.Nonempty)
    (hproper : ∀ L : AffineSubspace ℂ (Point 2), Module.finrank ℂ L.direction = 1 →
      ¬ Y.points ⊆ L) :
    (Set.univ : Set (stabilizer Y)).Finite ∧
      ((Set.univ : Set (stabilizer Y)).ncard : ℝ) ≤ (Y.degree : ℝ) := by
  let χ : stabilizer Y →* ℂˣ := scalarHom.comp (stabilizer Y).subtype
  let b : stabilizer Y → Point 2 := fun g => g.val.offset
  apply PerspectiveCore.planar_stabilizer_bound Y hY hne hproper χ b
  · intro g h
    exact offset_mul g.val h.val
  · intro g hs hb
    exact stabilizer_faithful Y g hs hb
  · intro g x hx
    exact (g.property x).mpr hx

end ScalarAffine
end
end DistinctDistances.TrackD
