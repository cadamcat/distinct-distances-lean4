import DistinctDistances.TrackC.PlaneExtension

open Filter
open scoped Topology BigOperators

namespace DistinctDistances.TrackC

abbrev OtherCoordinates (i : Fin 3) := {j : Fin 3 // j ≠ i}

/-- Single out one coordinate as the univariate variable. -/
noncomputable def coordinatePolynomialEquiv (i : Fin 3) :
    Poly 3 ≃ₐ[ℝ] Polynomial (MvPolynomial (OtherCoordinates i) ℝ) :=
  (MvPolynomial.renameEquiv ℝ (Equiv.optionSubtypeNe i).symm).trans
    (MvPolynomial.optionEquivLeft ℝ (OtherCoordinates i))

noncomputable def coordinateGraphPoint (i : Fin 3) (s : OtherCoordinates i → ℝ) (t : ℝ) : E 3 :=
  WithLp.toLp 2 (fun j => Option.elim ((Equiv.optionSubtypeNe i).symm j) t s)

/-- Evaluation commutes with the coordinate decomposition. -/
theorem eval_coordinatePolynomialEquiv (i : Fin 3) (f : Poly 3)
    (s : OtherCoordinates i → ℝ) (t : ℝ) :
    (coordinatePolynomialEquiv i f).eval₂ (MvPolynomial.eval s) t =
      evalR f (coordinateGraphPoint i s t) := by
  have h := (MvPolynomial.optionEquivLeft_elim_eval ℝ (OtherCoordinates i) s t
    (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm f)).symm
  simpa [coordinatePolynomialEquiv, MvPolynomial.renameEquiv_apply,
    MvPolynomial.eval_rename, coordinateGraphPoint, evalR,
    Polynomial.eval_map, Function.comp_def] using h

@[simp] theorem coordinatePolynomialEquiv_X_self (i : Fin 3) :
    coordinatePolynomialEquiv i (MvPolynomial.X i) = Polynomial.X := by
  simp [coordinatePolynomialEquiv, MvPolynomial.renameEquiv_apply,
    Equiv.optionSubtypeNe_symm_self]

@[simp] theorem coordinatePolynomialEquiv_X_other (i : Fin 3) (j : OtherCoordinates i) :
    coordinatePolynomialEquiv i (MvPolynomial.X j.val) = Polynomial.C (MvPolynomial.X j) := by
  simp [coordinatePolynomialEquiv, MvPolynomial.renameEquiv_apply,
    Equiv.optionSubtypeNe_symm_of_ne j.property]

@[simp] theorem coordinatePolynomialEquiv_C (i : Fin 3) (c : ℝ) :
    coordinatePolynomialEquiv i (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [coordinatePolynomialEquiv, MvPolynomial.renameEquiv_apply]

@[simp] theorem coordinatePolynomialEquiv_symm_X (i : Fin 3) :
    (coordinatePolynomialEquiv i).symm Polynomial.X = MvPolynomial.X i := by
  apply (coordinatePolynomialEquiv i).injective
  simp

@[simp] theorem coordinatePolynomialEquiv_symm_C_C (i : Fin 3) (c : ℝ) :
    (coordinatePolynomialEquiv i).symm (Polynomial.C (MvPolynomial.C c)) = MvPolynomial.C c := by
  apply (coordinatePolynomialEquiv i).injective
  simp

@[simp] theorem coordinatePolynomialEquiv_symm_C_X (i : Fin 3) (j : OtherCoordinates i) :
    (coordinatePolynomialEquiv i).symm (Polynomial.C (MvPolynomial.X j)) = MvPolynomial.X j.val := by
  apply (coordinatePolynomialEquiv i).injective
  simp

@[simp] theorem coordinateGraphPoint_self (i : Fin 3) (s : OtherCoordinates i → ℝ) (t : ℝ) :
    coordinateGraphPoint i s t i = t := by
  simp [coordinateGraphPoint, Equiv.optionSubtypeNe_symm_self]

@[simp] theorem coordinateGraphPoint_other (i : Fin 3) (s : OtherCoordinates i → ℝ) (t : ℝ)
    (j : OtherCoordinates i) : coordinateGraphPoint i s t j.val = s j := by
  simp [coordinateGraphPoint, Equiv.optionSubtypeNe_symm_of_ne j.property, j.property]

/-- Internal graph-factor lemma; the consumer uses an affine-linear graph. -/
private theorem coordinate_graph_factor (i : Fin 3)
    (q : MvPolynomial (OtherCoordinates i) ℝ) (f : Poly 3)
    (hf : ∀ s : OtherCoordinates i → ℝ,
      evalR f (coordinateGraphPoint i s (MvPolynomial.eval s q)) = 0) :
    (coordinatePolynomialEquiv i).symm (Polynomial.X - Polynomial.C q) ∣ f := by
  have hp : (coordinatePolynomialEquiv i f).eval q = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_zero, ← Polynomial.eval₂_at_apply,
      eval_coordinatePolynomialEquiv]
    exact hf s
  have hd : Polynomial.X - Polynomial.C q ∣ coordinatePolynomialEquiv i f :=
    Polynomial.dvd_iff_isRoot.mpr hp
  obtain ⟨g, hg⟩ := hd
  refine ⟨(coordinatePolynomialEquiv i).symm g, ?_⟩
  apply (coordinatePolynomialEquiv i).injective
  rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact hg

noncomputable def affineGraphPolynomial (i : Fin 3) (g : Fin 3 → ℝ) (a : ℝ) :
    MvPolynomial (OtherCoordinates i) ℝ :=
  MvPolynomial.C (a / g i) - ∑ j : OtherCoordinates i,
    MvPolynomial.C (g j.val / g i) * MvPolynomial.X j

noncomputable def affineGraphFactor (i : Fin 3) (g : Fin 3 → ℝ) (a : ℝ) : Poly 3 :=
  (coordinatePolynomialEquiv i).symm (Polynomial.X - Polynomial.C (affineGraphPolynomial i g a))

/-- Its coordinate equation has a monic distinguished variable. -/
theorem affineGraphFactor_expansion (i : Fin 3) (g : Fin 3 → ℝ) (a : ℝ) :
    affineGraphFactor i g a = MvPolynomial.X i -
      (MvPolynomial.C (a / g i) - ∑ j : OtherCoordinates i,
        MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val) := by
  simp [affineGraphFactor, affineGraphPolynomial]

/-- Every such affine graph equation is a genuine degree-one polynomial. -/
theorem affineGraphFactor_totalDegree (i : Fin 3) (g : Fin 3 → ℝ) (a : ℝ) :
    (affineGraphFactor i g a).totalDegree = 1 := by
  classical
  rw [affineGraphFactor_expansion]
  have hsum : (∑ j : OtherCoordinates i,
      MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val : Poly 3).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp only
      [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]; norm_num)
  have hle : (MvPolynomial.X i - (MvPolynomial.C (a / g i) -
      ∑ j : OtherCoordinates i, MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val) : Poly 3).totalDegree ≤ 1 := by
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) <|
      (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) hsum))
  have hderiv : MvPolynomial.pderiv i (MvPolynomial.X i - (MvPolynomial.C (a / g i) -
      ∑ j : OtherCoordinates i, MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val) : Poly 3) = 1 := by
    have hz : MvPolynomial.pderiv i (∑ j : OtherCoordinates i,
        MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val : Poly 3) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j hj
      simp [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne j.property]
    simp [hz]
  by_contra hne
  have hdegreezero : (MvPolynomial.X i - (MvPolynomial.C (a / g i) -
      ∑ j : OtherCoordinates i, MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val) : Poly 3).totalDegree = 0 := by omega
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegreezero] at hderiv
  simpa using hderiv

/-- Sum the distinguished coordinate separately from the graph coordinates. -/
theorem coordinateGraphPoint_sum (i : Fin 3) (g : Fin 3 → ℝ)
    (s : OtherCoordinates i → ℝ) (t : ℝ) :
    (∑ j : Fin 3, g j * coordinateGraphPoint i s t j) =
      g i * t + ∑ j : OtherCoordinates i, g j.val * s j := by
  classical
  calc
    _ = ∑ o : Option (OtherCoordinates i),
        g ((Equiv.optionSubtypeNe i) o) * coordinateGraphPoint i s t ((Equiv.optionSubtypeNe i) o) :=
      (Equiv.sum_comp (Equiv.optionSubtypeNe i) _).symm
    _ = _ := by simp

/-- Graph points at the affine graph value lie on the original hyperplane. -/
theorem affineGraphPolynomial_plane (i : Fin 3) (g : Fin 3 → ℝ) (a : ℝ) (hi : g i ≠ 0)
    (s : OtherCoordinates i → ℝ) :
    (∑ j : Fin 3, g j * coordinateGraphPoint i s (MvPolynomial.eval s (affineGraphPolynomial i g a)) j) = a := by
  classical
  rw [coordinateGraphPoint_sum]
  have hq : MvPolynomial.eval s (affineGraphPolynomial i g a) =
      a / g i - ∑ j : OtherCoordinates i, (g j.val / g i) * s j := by
    simp [affineGraphPolynomial]
  rw [hq, mul_sub, Finset.mul_sum]
  have hterm (j : OtherCoordinates i) : g i * ((g j.val / g i) * s j) = g j.val * s j := by
    field_simp
  have hconstant : g i * (a / g i) = a := by field_simp
  simp_rw [hterm]
  rw [hconstant]
  ring

/-- Reassemble the three coordinates from the distinguished coordinate and its complement. -/
theorem coordinateGraphPoint_reassemble (i : Fin 3) (y : E 3) :
    coordinateGraphPoint i (fun j => y j.val) (y i) = y := by
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · exact coordinateGraphPoint_other i (fun k => y k.val) (y i) ⟨j, hj⟩

/-- The graph factor vanishes at every point of the original hyperplane. -/
theorem affineGraphFactor_eval_zero (i : Fin 3) (g : Fin 3 → ℝ) (a : ℝ) (hi : g i ≠ 0)
    (y : E 3) (hy : (∑ j : Fin 3, g j * y j) = a) :
    evalR (affineGraphFactor i g a) y = 0 := by
  let s : OtherCoordinates i → ℝ := fun j => y j.val
  have hsum := coordinateGraphPoint_sum i g s (y i)
  rw [coordinateGraphPoint_reassemble] at hsum
  have hactual : g i * y i + ∑ j : OtherCoordinates i, g j.val * s j = a :=
    hsum.symm.trans hy
  have hgraph := affineGraphPolynomial_plane i g a hi s
  rw [coordinateGraphPoint_sum] at hgraph
  have hm : g i * (MvPolynomial.eval s (affineGraphPolynomial i g a) - y i) = 0 := by
    nlinarith
  have hval : MvPolynomial.eval s (affineGraphPolynomial i g a) = y i :=
    sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hi)
  have he := eval_coordinatePolynomialEquiv i (affineGraphFactor i g a) s (y i)
  rw [coordinateGraphPoint_reassemble] at he
  have hz : (coordinatePolynomialEquiv i (affineGraphFactor i g a)).eval₂ (MvPolynomial.eval s) (y i) = 0 := by
    simp [affineGraphFactor, hval]
  exact he.symm.trans hz

/-- The real hyperplane's linear equation divides a polynomial vanishing on it. -/
theorem affine_hyperplane_factor (f : Poly 3) (g : Fin 3 → ℝ) (a : ℝ) (i : Fin 3)
    (hi : g i ≠ 0) (hf : ∀ y : E 3, (∑ j : Fin 3, g j * y j) = a → evalR f y = 0) :
    ∃ l : Poly 3, l.totalDegree = 1 ∧ l ∣ f := by
  refine ⟨affineGraphFactor i g a, affineGraphFactor_totalDegree i g a, ?_⟩
  apply coordinate_graph_factor
  intro s
  exact hf _ (affineGraphPolynomial_plane i g a hi s)

/-- Local regular flatness forces a genuine linear polynomial factor. -/
theorem flat_surface_linear_factor (f : Poly 3) (x : E 3) (hx : regularPoint f x)
    (hflat : ∀ᶠ y in 𝓝 x, regularPoint f y → flatPoint f y) :
    ∃ l : Poly 3, l.totalDegree = 1 ∧ l ∣ f := by
  classical
  obtain ⟨i, hi⟩ := hx.2
  let g := gradient f x
  let a := ∑ j : Fin 3, g j * x j
  apply affine_hyperplane_factor f g a i hi
  intro y hy
  have hT : polynomialDifferential f x (y-x) = 0 := by
    simpa [polynomialDifferential_apply, gradient, mul_sub, Finset.sum_sub_distrib, g, a] using
      sub_eq_zero.mpr hy
  let v : (polynomialDifferential f x).ker := ⟨y-x, hT⟩
  have h := flat_surface_on_tangent_plane f x hx hflat v
  simpa [v] using h

/-- The linear factor passes through the regular point; needed to identify
its irreducible component rather than an unrelated factor. -/
theorem flat_surface_linear_factor_through_point (f : Poly 3) (x : E 3) (hx : regularPoint f x)
    (hflat : ∀ᶠ y in 𝓝 x, regularPoint f y → flatPoint f y) :
    ∃ l : Poly 3, l.totalDegree = 1 ∧ l ∣ f ∧ evalR l x = 0 := by
  classical
  obtain ⟨i, hi⟩ := hx.2
  let g := gradient f x
  let a := ∑ j : Fin 3, g j * x j
  have hv (y : E 3) (hy : (∑ j : Fin 3, g j * y j) = a) : evalR f y = 0 := by
    have hT : polynomialDifferential f x (y-x) = 0 := by
      simpa [polynomialDifferential_apply, gradient, mul_sub, Finset.sum_sub_distrib, g, a] using
        sub_eq_zero.mpr hy
    let v : (polynomialDifferential f x).ker := ⟨y-x, hT⟩
    have h := flat_surface_on_tangent_plane f x hx hflat v
    simpa [v] using h
  refine ⟨affineGraphFactor i g a, affineGraphFactor_totalDegree i g a, ?_, ?_⟩
  · apply coordinate_graph_factor
    intro s
    exact hv _ (affineGraphPolynomial_plane i g a hi s)
  · exact affineGraphFactor_eval_zero i g a hi x rfl

end DistinctDistances.TrackC
