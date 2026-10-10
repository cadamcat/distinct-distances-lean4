import DistinctDistances.TrackC.LineParameter

open Filter
open scoped Topology BigOperators

namespace DistinctDistances.TrackC

abbrev PlanarOtherCoordinates (i : Fin 2) := {j : Fin 2 // j ≠ i}

/-- Single out one coordinate as the univariate variable. -/
noncomputable def planarCoordinatePolynomialEquiv (i : Fin 2) :
    Poly 2 ≃ₐ[ℝ] Polynomial (MvPolynomial (PlanarOtherCoordinates i) ℝ) :=
  (MvPolynomial.renameEquiv ℝ (Equiv.optionSubtypeNe i).symm).trans
    (MvPolynomial.optionEquivLeft ℝ (PlanarOtherCoordinates i))

noncomputable def planarCoordinateGraphPoint (i : Fin 2) (s : PlanarOtherCoordinates i → ℝ) (t : ℝ) : E 2 :=
  WithLp.toLp 2 (fun j => Option.elim ((Equiv.optionSubtypeNe i).symm j) t s)

/-- Evaluation commutes with the coordinate decomposition. -/
theorem eval_planarCoordinatePolynomialEquiv (i : Fin 2) (f : Poly 2)
    (s : PlanarOtherCoordinates i → ℝ) (t : ℝ) :
    (planarCoordinatePolynomialEquiv i f).eval₂ (MvPolynomial.eval s) t =
      evalR f (planarCoordinateGraphPoint i s t) := by
  have h := (MvPolynomial.optionEquivLeft_elim_eval ℝ (PlanarOtherCoordinates i) s t
    (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm f)).symm
  simpa [planarCoordinatePolynomialEquiv, MvPolynomial.renameEquiv_apply,
    MvPolynomial.eval_rename, planarCoordinateGraphPoint, evalR,
    Polynomial.eval_map, Function.comp_def] using h

@[simp] theorem planarCoordinatePolynomialEquiv_X_self (i : Fin 2) :
    planarCoordinatePolynomialEquiv i (MvPolynomial.X i) = Polynomial.X := by
  simp [planarCoordinatePolynomialEquiv, MvPolynomial.renameEquiv_apply,
    Equiv.optionSubtypeNe_symm_self]

@[simp] theorem planarCoordinatePolynomialEquiv_X_other (i : Fin 2) (j : PlanarOtherCoordinates i) :
    planarCoordinatePolynomialEquiv i (MvPolynomial.X j.val) = Polynomial.C (MvPolynomial.X j) := by
  simp [planarCoordinatePolynomialEquiv, MvPolynomial.renameEquiv_apply,
    Equiv.optionSubtypeNe_symm_of_ne j.property]

@[simp] theorem planarCoordinatePolynomialEquiv_C (i : Fin 2) (c : ℝ) :
    planarCoordinatePolynomialEquiv i (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [planarCoordinatePolynomialEquiv, MvPolynomial.renameEquiv_apply]

@[simp] theorem planarCoordinatePolynomialEquiv_symm_X (i : Fin 2) :
    (planarCoordinatePolynomialEquiv i).symm Polynomial.X = MvPolynomial.X i := by
  apply (planarCoordinatePolynomialEquiv i).injective
  simp

@[simp] theorem planarCoordinatePolynomialEquiv_symm_C_C (i : Fin 2) (c : ℝ) :
    (planarCoordinatePolynomialEquiv i).symm (Polynomial.C (MvPolynomial.C c)) = MvPolynomial.C c := by
  apply (planarCoordinatePolynomialEquiv i).injective
  simp

@[simp] theorem planarCoordinatePolynomialEquiv_symm_C_X (i : Fin 2) (j : PlanarOtherCoordinates i) :
    (planarCoordinatePolynomialEquiv i).symm (Polynomial.C (MvPolynomial.X j)) = MvPolynomial.X j.val := by
  apply (planarCoordinatePolynomialEquiv i).injective
  simp

@[simp] theorem planarCoordinateGraphPoint_self (i : Fin 2) (s : PlanarOtherCoordinates i → ℝ) (t : ℝ) :
    planarCoordinateGraphPoint i s t i = t := by
  simp [planarCoordinateGraphPoint, Equiv.optionSubtypeNe_symm_self]

@[simp] theorem planarCoordinateGraphPoint_other (i : Fin 2) (s : PlanarOtherCoordinates i → ℝ) (t : ℝ)
    (j : PlanarOtherCoordinates i) : planarCoordinateGraphPoint i s t j.val = s j := by
  simp [planarCoordinateGraphPoint, Equiv.optionSubtypeNe_symm_of_ne j.property, j.property]

/-- Internal graph-factor lemma; the consumer uses an affine-linear graph. -/
private theorem planar_coordinate_graph_factor (i : Fin 2)
    (q : MvPolynomial (PlanarOtherCoordinates i) ℝ) (f : Poly 2)
    (hf : ∀ s : PlanarOtherCoordinates i → ℝ,
      evalR f (planarCoordinateGraphPoint i s (MvPolynomial.eval s q)) = 0) :
    (planarCoordinatePolynomialEquiv i).symm (Polynomial.X - Polynomial.C q) ∣ f := by
  have hp : (planarCoordinatePolynomialEquiv i f).eval q = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_zero, ← Polynomial.eval₂_at_apply,
      eval_planarCoordinatePolynomialEquiv]
    exact hf s
  have hd : Polynomial.X - Polynomial.C q ∣ planarCoordinatePolynomialEquiv i f :=
    Polynomial.dvd_iff_isRoot.mpr hp
  obtain ⟨g, hg⟩ := hd
  refine ⟨(planarCoordinatePolynomialEquiv i).symm g, ?_⟩
  apply (planarCoordinatePolynomialEquiv i).injective
  rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact hg

noncomputable def planarAffineGraphPolynomial (i : Fin 2) (g : Fin 2 → ℝ) (a : ℝ) :
    MvPolynomial (PlanarOtherCoordinates i) ℝ :=
  MvPolynomial.C (a / g i) - ∑ j : PlanarOtherCoordinates i,
    MvPolynomial.C (g j.val / g i) * MvPolynomial.X j

noncomputable def planarAffineGraphFactor (i : Fin 2) (g : Fin 2 → ℝ) (a : ℝ) : Poly 2 :=
  (planarCoordinatePolynomialEquiv i).symm (Polynomial.X - Polynomial.C (planarAffineGraphPolynomial i g a))

/-- Its coordinate equation has a monic distinguished variable. -/
theorem planarAffineGraphFactor_expansion (i : Fin 2) (g : Fin 2 → ℝ) (a : ℝ) :
    planarAffineGraphFactor i g a = MvPolynomial.X i -
      (MvPolynomial.C (a / g i) - ∑ j : PlanarOtherCoordinates i,
        MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val) := by
  simp [planarAffineGraphFactor, planarAffineGraphPolynomial]

/-- Every such affine graph equation is a genuine degree-one polynomial. -/
theorem planarAffineGraphFactor_totalDegree (i : Fin 2) (g : Fin 2 → ℝ) (a : ℝ) :
    (planarAffineGraphFactor i g a).totalDegree = 1 := by
  classical
  rw [planarAffineGraphFactor_expansion]
  have hsum : (∑ j : PlanarOtherCoordinates i,
      MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val : Poly 2).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp only
      [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]; norm_num)
  have hle : (MvPolynomial.X i - (MvPolynomial.C (a / g i) -
      ∑ j : PlanarOtherCoordinates i, MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val) : Poly 2).totalDegree ≤ 1 := by
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) <|
      (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) hsum))
  have hderiv : MvPolynomial.pderiv i (MvPolynomial.X i - (MvPolynomial.C (a / g i) -
      ∑ j : PlanarOtherCoordinates i, MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val) : Poly 2) = 1 := by
    have hz : MvPolynomial.pderiv i (∑ j : PlanarOtherCoordinates i,
        MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val : Poly 2) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j hj
      simp [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne j.property]
    simp [hz]
  by_contra hne
  have hdegreezero : (MvPolynomial.X i - (MvPolynomial.C (a / g i) -
      ∑ j : PlanarOtherCoordinates i, MvPolynomial.C (g j.val / g i) * MvPolynomial.X j.val) : Poly 2).totalDegree = 0 := by omega
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegreezero] at hderiv
  simpa using hderiv

/-- Sum the distinguished coordinate separately from the graph coordinates. -/
theorem planarCoordinateGraphPoint_sum (i : Fin 2) (g : Fin 2 → ℝ)
    (s : PlanarOtherCoordinates i → ℝ) (t : ℝ) :
    (∑ j : Fin 2, g j * planarCoordinateGraphPoint i s t j) =
      g i * t + ∑ j : PlanarOtherCoordinates i, g j.val * s j := by
  classical
  calc
    _ = ∑ o : Option (PlanarOtherCoordinates i),
        g ((Equiv.optionSubtypeNe i) o) * planarCoordinateGraphPoint i s t ((Equiv.optionSubtypeNe i) o) :=
      (Equiv.sum_comp (Equiv.optionSubtypeNe i) _).symm
    _ = _ := by simp

/-- Graph points at the affine graph value lie on the original hyperplane. -/
theorem planarAffineGraphPolynomial_plane (i : Fin 2) (g : Fin 2 → ℝ) (a : ℝ) (hi : g i ≠ 0)
    (s : PlanarOtherCoordinates i → ℝ) :
    (∑ j : Fin 2, g j * planarCoordinateGraphPoint i s (MvPolynomial.eval s (planarAffineGraphPolynomial i g a)) j) = a := by
  classical
  rw [planarCoordinateGraphPoint_sum]
  have hq : MvPolynomial.eval s (planarAffineGraphPolynomial i g a) =
      a / g i - ∑ j : PlanarOtherCoordinates i, (g j.val / g i) * s j := by
    simp [planarAffineGraphPolynomial]
  rw [hq, mul_sub, Finset.mul_sum]
  have hterm (j : PlanarOtherCoordinates i) : g i * ((g j.val / g i) * s j) = g j.val * s j := by
    field_simp
  have hconstant : g i * (a / g i) = a := by field_simp
  simp_rw [hterm]
  rw [hconstant]
  ring

/-- Reassemble the two coordinates from the distinguished coordinate and its complement. -/
theorem planarCoordinateGraphPoint_reassemble (i : Fin 2) (y : E 2) :
    planarCoordinateGraphPoint i (fun j => y j.val) (y i) = y := by
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · exact planarCoordinateGraphPoint_other i (fun k => y k.val) (y i) ⟨j, hj⟩

/-- The graph factor vanishes at every point of the original hyperplane. -/
theorem planarAffineGraphFactor_eval_zero (i : Fin 2) (g : Fin 2 → ℝ) (a : ℝ) (hi : g i ≠ 0)
    (y : E 2) (hy : (∑ j : Fin 2, g j * y j) = a) :
    evalR (planarAffineGraphFactor i g a) y = 0 := by
  let s : PlanarOtherCoordinates i → ℝ := fun j => y j.val
  have hsum := planarCoordinateGraphPoint_sum i g s (y i)
  rw [planarCoordinateGraphPoint_reassemble] at hsum
  have hactual : g i * y i + ∑ j : PlanarOtherCoordinates i, g j.val * s j = a :=
    hsum.symm.trans hy
  have hgraph := planarAffineGraphPolynomial_plane i g a hi s
  rw [planarCoordinateGraphPoint_sum] at hgraph
  have hm : g i * (MvPolynomial.eval s (planarAffineGraphPolynomial i g a) - y i) = 0 := by
    nlinarith
  have hval : MvPolynomial.eval s (planarAffineGraphPolynomial i g a) = y i :=
    sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hi)
  have he := eval_planarCoordinatePolynomialEquiv i (planarAffineGraphFactor i g a) s (y i)
  rw [planarCoordinateGraphPoint_reassemble] at he
  have hz : (planarCoordinatePolynomialEquiv i (planarAffineGraphFactor i g a)).eval₂ (MvPolynomial.eval s) (y i) = 0 := by
    simp [planarAffineGraphFactor, hval]
  exact he.symm.trans hz

/-- The real hyperplane's linear equation divides a polynomial vanishing on it. -/
theorem planar_affine_hyperplane_factor (f : Poly 2) (g : Fin 2 → ℝ) (a : ℝ) (i : Fin 2)
    (hi : g i ≠ 0) (hf : ∀ y : E 2, (∑ j : Fin 2, g j * y j) = a → evalR f y = 0) :
    ∃ l : Poly 2, l.totalDegree = 1 ∧ l ∣ f := by
  refine ⟨planarAffineGraphFactor i g a, planarAffineGraphFactor_totalDegree i g a, ?_⟩
  apply planar_coordinate_graph_factor
  intro s
  exact hf _ (planarAffineGraphPolynomial_plane i g a hi s)

/-- The normalized graph equation differs from the original normal equation by a nonzero scalar. -/
theorem planarAffineGraphFactor_eval_identity (i : Fin 2) (g : Fin 2 → ℝ) (a : ℝ)
    (hi : g i ≠ 0) (y : E 2) :
    g i * evalR (planarAffineGraphFactor i g a) y = (∑ j : Fin 2, g j*y j)-a := by
  let s : PlanarOtherCoordinates i → ℝ := fun j => y j.val
  have he := eval_planarCoordinatePolynomialEquiv i (planarAffineGraphFactor i g a) s (y i)
  rw [planarCoordinateGraphPoint_reassemble] at he
  have hev : evalR (planarAffineGraphFactor i g a) y = y i -
      MvPolynomial.eval s (planarAffineGraphPolynomial i g a) := by
    rw [← he]
    simp [planarAffineGraphFactor]
  have hgraph := planarAffineGraphPolynomial_plane i g a hi s
  rw [planarCoordinateGraphPoint_sum] at hgraph
  have hsum := planarCoordinateGraphPoint_sum i g s (y i)
  rw [planarCoordinateGraphPoint_reassemble] at hsum
  rw [hev]
  nlinarith

/-- A real planar line is the zero set of a nontrivial affine normal equation. -/
theorem planar_line_normal (l : Line 2) :
    ∃ (g : Fin 2 → ℝ) (a : ℝ) (i : Fin 2), g i ≠ 0 ∧
      ∀ y : E 2, y ∈ l.1 ↔ (∑ j : Fin 2, g j*y j) = a := by
  obtain ⟨x,v,hv,hrange,hinj⟩ := affine_line_parameter 2 l
  let g : Fin 2 → ℝ := ![-v 1,v 0]
  let a := ∑ j : Fin 2, g j*x j
  have hcoord : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra! h
    apply hv
    apply PiLp.ext
    intro i
    fin_cases i
    · simpa using h.1
    · simpa using h.2
  have hnormal : ∀ y : E 2, y ∈ l.1 ↔ (∑ j : Fin 2,g j*y j) = a := by
    intro y
    have hdet : (∑ j : Fin 2,g j*y j) = a ↔ v 0*(y 1-x 1)-v 1*(y 0-x 0) = 0 := by
      simp only [g,a,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      constructor <;> intro h <;> linarith
    rw [hdet]
    change y ∈ (l.1:Set (E 2)) ↔ _
    rw [← hrange]
    constructor
    · rintro ⟨t,rfl⟩
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      ring
    · intro hzero
      by_cases hv0 : v 0 = 0
      · have hv1 : v 1 ≠ 0 := hcoord.resolve_left (not_not.mpr hv0)
        let t := (y 1-x 1)/v 1
        have ht : t*v 1 = y 1-x 1 := div_mul_cancel₀ _ hv1
        have hy0 : y 0 = x 0 := by
          have hm : v 1*(y 0-x 0) = 0 := by simpa [hv0] using hzero.symm
          exact (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hv1))
        refine ⟨t,?_⟩
        apply PiLp.ext
        intro i
        fin_cases i
        · change x 0+t*v 0 = y 0
          simp [hv0,hy0]
        · change x 1+t*v 1 = y 1
          linarith
      · let t := (y 0-x 0)/v 0
        have ht : t*v 0 = y 0-x 0 := div_mul_cancel₀ _ hv0
        refine ⟨t,?_⟩
        apply PiLp.ext
        intro i
        fin_cases i
        · change x 0+t*v 0 = y 0
          linarith
        · change x 1+t*v 1 = y 1
          apply mul_left_cancel₀ hv0
          calc
            v 0*(x 1+t*v 1) = v 0*x 1+(t*v 0)*v 1 := by ring
            _ = v 0*x 1+(y 0-x 0)*v 1 := by rw [ht]
            _ = v 0*y 1 := by nlinarith
  rcases hcoord with hv0 | hv1
  · exact ⟨g,a,1,by simpa [g] using hv0,hnormal⟩
  · exact ⟨g,a,0,by simpa [g] using neg_ne_zero.mpr hv1,hnormal⟩

/-- A polynomial vanishing on a planar line has its degree-one equation as a factor. -/
theorem planar_line_factor (f : Poly 2) (l : Line 2) (hl : onPolynomial f l) :
    ∃ p : Poly 2, p.totalDegree = 1 ∧ p ∣ f ∧ zeroSet p = (l.1 : Set (E 2)) := by
  obtain ⟨g,a,i,hi,hnormal⟩ := planar_line_normal l
  let p := planarAffineGraphFactor i g a
  have hdiv : p ∣ f := by
    apply planar_coordinate_graph_factor
    intro s
    apply hl
    apply (hnormal _).mpr
    exact planarAffineGraphPolynomial_plane i g a hi s
  refine ⟨p,planarAffineGraphFactor_totalDegree i g a,hdiv,?_⟩
  ext y
  have he := planarAffineGraphFactor_eval_identity i g a hi y
  change evalR p y = 0 ↔ y ∈ l.1
  rw [hnormal]
  constructor
  · intro hz
    change g i * evalR p y = _ at he
    rw [hz,mul_zero] at he
    linarith
  · intro hy
    have hm : g i*evalR p y = 0 := by
      change g i*evalR p y = _ at he
      linarith
    exact (mul_eq_zero.mp hm).resolve_left hi

end DistinctDistances.TrackC
