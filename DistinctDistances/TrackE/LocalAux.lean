import DistinctDistances.TrackE.Requests

/-!
# Auxiliary facts for `red:local-concentration` (`reduction.tex:402-445`)

Separators from independent stars, nonemptiness of the neighbour flats, the real Gram identity
behind the isotropic cap, and complexification identities.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

variable {d : ℕ}

theorem cplx_add (a b : RPoint d) : cplx (a + b) = cplx a + cplx b := by
  ext i; simp [cplx]

theorem cplx_sub (a b : RPoint d) : cplx (a - b) = cplx a - cplx b := by
  ext i; simp [cplx]

theorem cplx_smul (t : ℝ) (a : RPoint d) : cplx (t • a) = (t : ℂ) • cplx a := by
  ext i; simp [cplx]

theorem cplx_injective : Function.Injective (cplx (d := d)) := by
  intro a b h
  ext i
  have := congrFun h i
  simpa [cplx] using this

theorem cplx_eq_zero_iff (a : RPoint d) : cplx a = 0 ↔ a = 0 := by
  constructor
  · intro h; apply cplx_injective; rw [h]; ext i; simp [cplx]
  · rintro rfl; ext i; simp [cplx]

/-- `∑ (cplx a)_i (cplx b)_i` is the real inner product. -/
theorem sum_cplx_mul (a b : RPoint d) :
    ∑ i, cplx a i * cplx b i = ((inner ℝ a b : ℝ) : ℂ) := by
  simp only [cplx, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Separators from an independent star (`reduction.tex:242-244`): for each partner `q` a
homogeneous polynomial of degree `D` equal to `1` at `q - p` and `0` at the other partners. -/
theorem IndependentStar.exists_separator {D : ℕ} {p : RPoint d} {T : Finset (RPoint d)}
    (hT : IndependentStar D p T) {q : RPoint d} (hq : q ∈ T) :
    ∃ s : MvPolynomial (Fin d) ℂ, s.IsHomogeneous D ∧ MvPolynomial.aeval (cplx (q - p)) s = 1 ∧
      ∀ q' ∈ T, q' ≠ q → MvPolynomial.aeval (cplx (q' - p)) s = 0 := by
  classical
  let H := MvPolynomial.homogeneousSubmodule (Fin d) ℂ D
  let Φ : H →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun q' : T => homEval d D (cplx ((q' : RPoint d) - p))
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hfmap⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    apply hf0
    have hker : ∀ s : H, f (Φ s) = 0 := by
      intro s
      have : f (Φ s) ∈ (LinearMap.range Φ).map f :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self Φ s)
      rw [hfmap] at this
      simpa using this
    have hexp : ∀ x : T → ℂ, f x = ∑ i : T, x i * f (Pi.single i 1) := by
      intro x
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (Pi.single i (x i) : T → ℂ) = x i • Pi.single i 1 by
        rw [← Pi.single_smul]; simp]
      rw [map_smul, smul_eq_mul]
    have hc : ∀ i : T, f (Pi.single i 1) = 0 := by
      refine Fintype.linearIndependent_iff.mp hT (fun i => f (Pi.single i 1)) ?_
      apply LinearMap.ext
      intro s
      rw [LinearMap.sum_apply, LinearMap.zero_apply]
      have := hker s
      rw [hexp] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro i _
      simp only [LinearMap.smul_apply, smul_eq_mul, Φ, LinearMap.pi_apply]
      ring
    apply LinearMap.pi_ext
    intro i x
    rw [show (Pi.single i x : T → ℂ) = x • Pi.single i 1 by rw [← Pi.single_smul]; simp,
      map_smul, hc i]
    simp
  obtain ⟨s, hs⟩ := hsurj (Pi.single ⟨q, hq⟩ 1)
  refine ⟨s.1, s.2, ?_, ?_⟩
  · have := congrFun hs ⟨q, hq⟩
    simpa [Φ, homEval] using this
  · intro q' hq' hne
    have := congrFun hs ⟨q', hq'⟩
    have hne' : (⟨q', hq'⟩ : T) ≠ ⟨q, hq⟩ := fun h => hne (congrArg Subtype.val h)
    simpa [Φ, homEval, Pi.single_apply, hne'] using this

/-- The neighbour flat `Z(u+w) = u-w` is nonempty when `|u| = |w|` and `u + w ≠ 0`. -/
theorem evalFlat_nonempty (u w : RPoint d) (hnorm : ‖u‖ = ‖w‖) (hv : u + w ≠ 0) :
    (evalFlat (cplx (u + w)) (cplx (u - w))).Nonempty := by
  set v := cplx (u + w)
  set y := cplx (u - w)
  set s : ℂ := ∑ j, v j * v j
  have hs : s ≠ 0 := by
    have h1 : s = ((inner ℝ (u + w) (u + w) : ℝ) : ℂ) := sum_cplx_mul _ _
    rw [h1, real_inner_self_eq_norm_sq]
    have : ‖u + w‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    exact_mod_cast pow_ne_zero 2 this
  have hyv : ∑ j, y j * v j = 0 := by
    have h1 : ∑ j, y j * v j = ((inner ℝ (u - w) (u + w) : ℝ) : ℂ) := sum_cplx_mul _ _
    rw [h1]
    have : inner ℝ (u - w) (u + w) = ‖u‖ ^ 2 - ‖w‖ ^ 2 := by
      rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq, real_inner_comm u w]
      ring
    rw [this, hnorm]
    simp
  refine ⟨fun ij => (y ij.1.1 * v ij.1.2 - v ij.1.1 * y ij.1.2) / s, ?_⟩
  have hM : skewMatrix (fun ij : SkewIdx d => (y ij.1.1 * v ij.1.2 - v ij.1.1 * y ij.1.2) / s) =
      fun i j => (y i * v j - v i * y j) / s := by
    ext i j
    simp only [skewMatrix]
    split_ifs with h1 h2
    · rfl
    · ring
    · have : i = j := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      subst this
      ring
  show (skewMatrix _).mulVec v = y
  rw [hM]
  ext i
  simp only [Matrix.mulVec, dotProduct]
  have : ∑ j, (y i * v j - v i * y j) / s * v j =
      (y i * s - v i * (∑ j, y j * v j)) / s := by
    simp only [s, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [this, hyv, mul_zero, sub_zero, mul_div_assoc, div_self hs, mul_one]

/-- The real Gram identity behind isotropy (`reduction.tex:420-429`):
`(u-w)·(u'+w') + (u'-w')·(u+w) = 2(u·u' - w·w')`. -/
theorem isotropy_sum_eq (u w u' w' : RPoint d) :
    ∑ i, (cplx (u - w) i * cplx (u' + w') i + cplx (u' - w') i * cplx (u + w) i) =
      ((2 * (inner ℝ u u' - inner ℝ w w') : ℝ) : ℂ) := by
  rw [Finset.sum_add_distrib, sum_cplx_mul, sum_cplx_mul]
  push_cast
  have h1 : inner ℝ (u - w) (u' + w') = inner ℝ u u' + inner ℝ u w' - inner ℝ w u' -
      inner ℝ w w' := by
    rw [inner_sub_left, inner_add_right, inner_add_right]; ring
  have h2 : inner ℝ (u' - w') (u + w) = inner ℝ u' u + inner ℝ u' w - inner ℝ w' u -
      inner ℝ w' w := by
    rw [inner_sub_left, inner_add_right, inner_add_right]; ring
  rw [h1, h2, real_inner_comm u' u, real_inner_comm u' w, real_inner_comm w' u,
    real_inner_comm w' w]
  push_cast
  ring

theorem skewMatrix_add {e : ℕ} (z z' : SkewIdx e → ℂ) :
    skewMatrix (z + z') = skewMatrix z + skewMatrix z' := by
  ext i j; simp only [skewMatrix, Pi.add_apply, Matrix.add_apply]; split_ifs <;> ring

theorem skewMatrix_smul {e : ℕ} (c : ℂ) (z : SkewIdx e → ℂ) :
    skewMatrix (c • z) = c • skewMatrix z := by
  ext i j; simp only [skewMatrix, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem skewMatrix_sub {e : ℕ} (z z' : SkewIdx e → ℂ) :
    skewMatrix (z - z') = skewMatrix z - skewMatrix z' := by
  ext i j; simp only [skewMatrix, Pi.sub_apply, Matrix.sub_apply]; split_ifs <;> ring

/-- The evaluation flat `{z : z v = y}`, transported to track A's coordinates, as an affine
subspace. -/
def skewAffine {e : ℕ} (v y : Fin e → ℂ) : AffineSubspace ℂ (Point (Fintype.card (SkewIdx e))) where
  carrier := {x | (skewMatrix (fun ij => x (Fintype.equivFin (SkewIdx e) ij))).mulVec v = y}
  smul_vsub_vadd_mem' := by
    intro c p1 p2 p3 h1 h2 h3
    simp only [Set.mem_setOf_eq] at h1 h2 h3 ⊢
    have : (fun ij => (c • (p1 -ᵥ p2) +ᵥ p3) (Fintype.equivFin (SkewIdx e) ij)) =
        c • ((fun ij => p1 (Fintype.equivFin (SkewIdx e) ij)) -
          (fun ij => p2 (Fintype.equivFin (SkewIdx e) ij))) +
          (fun ij => p3 (Fintype.equivFin (SkewIdx e) ij)) := by
      ext ij; simp [vsub_eq_sub, vadd_eq_add]
    rw [this, skewMatrix_add, skewMatrix_smul, skewMatrix_sub, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.sub_mulVec, h1, h2, h3]
    simp

theorem coe_skewAffine {e : ℕ} (v y : Fin e → ℂ) :
    (skewAffine v y : Set (Point (Fintype.card (SkewIdx e)))) = skewToPoint '' evalFlat v y := by
  ext x
  constructor
  · intro hx
    refine ⟨fun ij => x (Fintype.equivFin (SkewIdx e) ij), hx, ?_⟩
    ext i; simp [skewToPoint]
  · rintro ⟨z, hz, rfl⟩
    show (skewMatrix _).mulVec v = y
    have hz' : (fun ij => skewToPoint z (Fintype.equivFin (SkewIdx e) ij)) = z := by
      funext ij; simp [skewToPoint]
    rw [hz']
    exact hz

theorem eval_rename_skewToPoint {e : ℕ} (g : MvPolynomial (SkewIdx e) ℂ) (z : SkewIdx e → ℂ) :
    MvPolynomial.eval (skewToPoint z) (MvPolynomial.rename (Fintype.equivFin (SkewIdx e)) g) =
      MvPolynomial.eval z g := by
  have hz : skewToPoint z ∘ (Fintype.equivFin (SkewIdx e)) = z := by
    funext ij; simp [skewToPoint]
  rw [MvPolynomial.eval_rename, hz]

/-- `Fintype.card (SkewIdx e) = C(e,2)`. -/
theorem card_skewIdx (e : ℕ) : Fintype.card (SkewIdx e) = e.choose 2 := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ b : Fin e, (∑ a : Fin e, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter]
    rw [show (Finset.univ.filter fun a : Fin e => a < b) = Finset.Iio b by ext; simp]
    simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) e, Finset.sum_range_id, Nat.choose_two_right]

end

end DistinctDistances
