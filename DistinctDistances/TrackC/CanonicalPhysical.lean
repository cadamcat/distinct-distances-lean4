import DistinctDistances.TrackC.MotionCoordinates

namespace DistinctDistances.TrackC

/-- The physical graph coordinates are an affine equivalence in the canonical
axis frame, motions.tex:310–314. -/
theorem canonical_physical_equiv (g : Motion 3)
    (haxis : axis g = Submodule.span ℝ {EuclideanSpace.single (2 : Fin 3) (1 : ℝ)}) :
    ∃ T : E 3 ≃ᵃ[ℝ] E 3, ∀ x : E 3, T x = canonicalPhysicalPoint g x := by
  let S := g.linearIsometryEquiv
  let e₂ : E 3 := EuclideanSpace.single (2 : Fin 3) 1
  let b : E 3 := g 0
  have hg (x : E 3) : g x = S x + b := by
    calc
      g x = g (x +ᵥ (0 : E 3)) := by simp
      _ = g.linearIsometryEquiv x +ᵥ g 0 := g.map_vadd 0 x
      _ = S x + b := rfl
  have he₂axis : e₂ ∈ axis g := by
    rw [haxis]
    exact Submodule.subset_span (by simp [e₂])
  have hSe₂ : S e₂ = -e₂ := by
    have h := he₂axis
    change g.toAffineEquiv.linear.toLinearMap e₂ + e₂ = 0 at h
    have h' : S e₂ + e₂ = 0 := by
      simpa [S, AffineIsometryEquiv.linear_eq_linear_isometry] using h
    exact eq_neg_of_add_eq_zero_left h'
  have hS2 (v : E 3) : (S v) 2 = -v 2 := by
    have h := S.inner_map_map v e₂
    rw [hSe₂] at h
    have h' : -((S v) 2) = v 2 := by
      simpa [e₂, PiLp.inner_apply, Fin.sum_univ_three,
        EuclideanSpace.single_apply] using h
    linarith
  let L : E 3 →ₗ[ℝ] E 3 := {
    toFun := fun x => WithLp.toLp 2 ![
      ((x + g.linearIsometryEquiv x) 0) / 2,
      ((x + g.linearIsometryEquiv x) 1) / 2,
      ((x - g.linearIsometryEquiv x) 2) / 2]
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp <;> ring
    map_smul' := by
      intro c x
      ext i
      fin_cases i <;> simp <;> ring
  }
  have hLinj : Function.Injective L := by
    intro x y hxy
    let v : E 3 := x - y
    have hv : L v = 0 := by
      dsimp [v]
      rw [map_sub, hxy, sub_self]
    have hplus : v + S v = 0 := by
      ext i
      fin_cases i
      · have h := congrArg (fun q : E 3 => q 0) hv
        change ((v + S v) 0) / 2 = 0 at h
        simp only [WithLp.ofLp_add, PiLp.add_apply] at h
        change (v + S v) 0 = 0
        change v 0 + (S v) 0 = 0
        linarith
      · have h := congrArg (fun q : E 3 => q 1) hv
        change ((v + S v) 1) / 2 = 0 at h
        simp only [WithLp.ofLp_add, PiLp.add_apply] at h
        change (v + S v) 1 = 0
        change v 1 + (S v) 1 = 0
        linarith
      · have h := hS2 v
        change (v + S v).ofLp 2 = 0
        simp only [WithLp.ofLp_add, PiLp.add_apply]
        rw [h]
        ring
    have hvaxis : v ∈ axis g := by
      change v ∈ LinearMap.ker (g.toAffineEquiv.linear.toLinearMap + LinearMap.id)
      rw [LinearMap.mem_ker]
      simpa [S, AffineIsometryEquiv.linear_eq_linear_isometry, add_comm] using hplus
    rw [haxis] at hvaxis
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hvaxis
    have hv₂ : v 2 = 0 := by
      have h := congrArg (fun q : E 3 => q 2) hv
      change ((v - S v) 2) / 2 = 0 at h
      simp only [WithLp.ofLp_sub, PiLp.sub_apply] at h
      rw [hS2 v] at h
      nlinarith
    have htzero : t = 0 := by
      have h := congrArg (fun q : E 3 => q 2) ht
      simpa [e₂, hv₂] using h
    have hvzero : v = 0 := by simpa [htzero] using ht.symm
    dsimp [v] at hvzero
    exact sub_eq_zero.mp hvzero
  let LE : E 3 ≃ₗ[ℝ] E 3 :=
    LinearEquiv.ofBijective L ⟨hLinj, LinearMap.injective_iff_surjective.mp hLinj⟩
  have hpoint (x : E 3) :
      canonicalPhysicalPoint g x = L x + canonicalPhysicalPoint g 0 := by
    ext i
    fin_cases i <;> simp [canonicalPhysicalPoint, L, S, b, hg x] <;> ring
  refine ⟨AffineEquiv.ofLinearEquiv LE 0 (canonicalPhysicalPoint g 0), ?_⟩
  intro x
  simp only [AffineEquiv.ofLinearEquiv_apply, vsub_eq_sub, sub_zero, zero_vadd,
    LE, LinearEquiv.ofBijective_apply]
  change L x + canonicalPhysicalPoint g 0 = canonicalPhysicalPoint g x
  exact (hpoint x).symm

/-- Avoidance of physical triple spans makes all transformed triples
nonvertical, motions.tex:253–277, 447–449. -/
private theorem vsub_pair_independent_iff_not_collinear_local {d : ℕ} {x y z : E d} :
    LinearIndependent ℝ ![y - x, z - x] ↔
      ¬ Collinear ℝ ({x, y, z} : Set (E d)) := by
  let p : Fin 3 → E d := ![x, y, z]
  let f : Fin 2 → {i : Fin 3 // i ≠ 0} := fun i => ⟨i.succ, Fin.succ_ne_zero _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.succ_injective 2
      exact congrArg Subtype.val hij
    · intro i
      obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero i.2
      exact ⟨j, Subtype.ext hj⟩
  let e : Fin 2 ≃ {i : Fin 3 // i ≠ 0} := Equiv.ofBijective f hf
  have hfun :
      (fun i : Fin 2 => p (e i).1 -ᵥ p 0) = ![y - x, z - x] := by
    funext i
    fin_cases i <;> simp [p, e, f]
  calc
    LinearIndependent ℝ ![y - x, z - x] ↔
        LinearIndependent ℝ (fun i : {i : Fin 3 // i ≠ 0} => p i.1 -ᵥ p 0) :=
      linearIndependent_equiv' (e := e)
        (f := fun i : {i : Fin 3 // i ≠ 0} => p i.1 -ᵥ p 0)
        (g := ![y - x, z - x]) hfun
    _ ↔ AffineIndependent ℝ p :=
      (affineIndependent_iff_linearIndependent_vsub (k := ℝ) p 0).symm
    _ ↔ ¬ Collinear ℝ ({x, y, z} : Set (E d)) := by
      simpa [p] using (affineIndependent_iff_not_collinear_set (k := ℝ)
        (p₁ := x) (p₂ := y) (p₃ := z))

theorem canonical_projection_triples (g : Motion 3) (S : Finset (E 3))
    (haxis : axis g = Submodule.span ℝ {EuclideanSpace.single (2 : Fin 3) (1 : ℝ)})
    (havoid : axisAvoidsTriples g S) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ¬ Collinear ℝ ({x,y,z} : Set (E 3)) →
      ¬ Collinear ℝ ({WithLp.toLp 2 ![(canonicalPhysicalPoint g x) 0,(canonicalPhysicalPoint g x) 1],
        WithLp.toLp 2 ![(canonicalPhysicalPoint g y) 0,(canonicalPhysicalPoint g y) 1],
        WithLp.toLp 2 ![(canonicalPhysicalPoint g z) 0,(canonicalPhysicalPoint g z) 1]} : Set (E 2)) := by
  intro x hx y hy z hz hncol hproj
  let project (x : E 3) : E 2 :=
    WithLp.toLp 2 ![(canonicalPhysicalPoint g x) 0, (canonicalPhysicalPoint g x) 1]
  have hproj' : Collinear ℝ ({project x, project y, project z} : Set (E 2)) := by
    simpa [project] using hproj
  have hsource : LinearIndependent ℝ ![y - x, z - x] :=
    (vsub_pair_independent_iff_not_collinear_local).2 hncol
  have hdep : ¬ LinearIndependent ℝ ![project y - project x, project z - project x] := by
    intro hli
    exact (vsub_pair_independent_iff_not_collinear_local.mp hli) hproj'
  let p : Fin 2 → E 2 := ![project y - project x, project z - project x]
  obtain ⟨a, hsum, i, hi⟩ :=
    Fintype.not_linearIndependent_iff.mp (by simpa [p] using hdep)
  let Rg := g.linearIsometryEquiv
  let b : E 3 := g 0
  have hg (u : E 3) : g u = Rg u + b := by
    calc
      g u = g (u +ᵥ (0 : E 3)) := by simp
      _ = g.linearIsometryEquiv u +ᵥ g 0 := g.map_vadd 0 u
      _ = Rg u + b := rfl
  let Lp : E 3 →ₗ[ℝ] E 2 := {
    toFun := fun u => WithLp.toLp 2 ![
      ((u + Rg u) 0) / 2,
      ((u + Rg u) 1) / 2]
    map_add' := by
      intro u v
      ext j
      fin_cases j <;> simp <;> ring
    map_smul' := by
      intro c u
      ext j
      fin_cases j <;> simp <;> ring
  }
  have hprojectDiff (u v : E 3) : project v - project u = Lp (v - u) := by
    ext j
    fin_cases j <;>
      simp [project, canonicalPhysicalPoint, Lp, hg, map_sub] <;> ring
  let v : E 3 := a 0 • (y - x) + a 1 • (z - x)
  have hLpv : Lp v = 0 := by
    have hrel : a 0 • (project y - project x) + a 1 • (project z - project x) = 0 := by
      simpa [p, Fin.sum_univ_two] using hsum
    calc
      Lp v = a 0 • (project y - project x) + a 1 • (project z - project x) := by
        simp [v, map_add, map_smul, hprojectDiff]
      _ = 0 := hrel
  let e₂ : E 3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have he₂axis : e₂ ∈ axis g := by
    rw [haxis]
    exact Submodule.subset_span (by simp [e₂])
  have hRge₂ : Rg e₂ = -e₂ := by
    have h := he₂axis
    change g.toAffineEquiv.linear.toLinearMap e₂ + e₂ = 0 at h
    have h' : Rg e₂ + e₂ = 0 := by
      simpa [Rg, AffineIsometryEquiv.linear_eq_linear_isometry] using h
    exact eq_neg_of_add_eq_zero_left h'
  have hRg2 (u : E 3) : (Rg u) 2 = -u 2 := by
    have h := Rg.inner_map_map u e₂
    rw [hRge₂] at h
    have h' : -((Rg u) 2) = u 2 := by
      simpa [e₂, PiLp.inner_apply, Fin.sum_univ_three,
        EuclideanSpace.single_apply] using h
    linarith
  have hLp0 : (v + Rg v) 0 = 0 := by
    have h := congrArg (fun q : E 2 => q 0) hLpv
    change ((v + Rg v) 0) / 2 = 0 at h
    nlinarith
  have hLp1 : (v + Rg v) 1 = 0 := by
    have h := congrArg (fun q : E 2 => q 1) hLpv
    change ((v + Rg v) 1) / 2 = 0 at h
    nlinarith
  have hplus : v + Rg v = 0 := by
    ext j
    fin_cases j
    · exact hLp0
    · exact hLp1
    · have h := hRg2 v
      have h' : v 2 + (Rg v) 2 = 0 := by linarith
      change v 2 + (Rg v) 2 = 0
      exact h'
  have hvaxis : v ∈ axis g := by
    change v ∈ LinearMap.ker (g.toAffineEquiv.linear.toLinearMap + LinearMap.id)
    rw [LinearMap.mem_ker]
    simpa [Rg, AffineIsometryEquiv.linear_eq_linear_isometry, add_comm] using hplus
  have hyx : y - x ∈ vectorSpan ℝ ({x, y, z} : Set (E 3)) := by
    simpa using vsub_mem_vectorSpan ℝ (by simp : y ∈ ({x, y, z} : Set (E 3)))
      (by simp : x ∈ ({x, y, z} : Set (E 3)))
  have hzx : z - x ∈ vectorSpan ℝ ({x, y, z} : Set (E 3)) := by
    simpa using vsub_mem_vectorSpan ℝ (by simp : z ∈ ({x, y, z} : Set (E 3)))
      (by simp : x ∈ ({x, y, z} : Set (E 3)))
  have hvspan : v ∈ vectorSpan ℝ ({x, y, z} : Set (E 3)) := by
    dsimp [v]
    exact (vectorSpan ℝ ({x, y, z} : Set (E 3))).add_mem
      ((vectorSpan ℝ ({x, y, z} : Set (E 3))).smul_mem (a 0) hyx)
      ((vectorSpan ℝ ({x, y, z} : Set (E 3))).smul_mem (a 1) hzx)
  have hvIntersection : v ∈ axis g ⊓ vectorSpan ℝ ({x, y, z} : Set (E 3)) :=
    ⟨hvaxis, hvspan⟩
  have hvzero : v = 0 := by
    rw [havoid x hx y hy z hz hncol] at hvIntersection
    simpa only [Submodule.mem_bot] using hvIntersection
  have hsourceRel : ∑ j : Fin 2, a j • (![y - x, z - x] j) = 0 := by
    simpa [Fin.sum_univ_two, v] using hvzero
  have hallzero : ∀ j : Fin 2, a j = 0 :=
    (Fintype.linearIndependent_iff.mp hsource) a hsourceRel
  exact hi (hallzero i)

end DistinctDistances.TrackC
