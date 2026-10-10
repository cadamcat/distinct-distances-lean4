import DistinctDistances.TrackC.MotionGeometry
import DistinctDistances.TrackC.GraphDualGeometry

open Classical

namespace DistinctDistances.TrackC

private def projectedPoint (p : E 3) : E 2 := WithLp.toLp 2 ![p 0, p 1]

private theorem vsub_pair_independent_iff_not_collinear {d : ℕ} {x y z : E d} :
    LinearIndependent ℝ ![y-x, z-x] ↔
      ¬ Collinear ℝ ({x,y,z} : Set (E d)) := by
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
      (fun i : Fin 2 => p (e i).1 -ᵥ p 0) = ![y-x, z-x] := by
    funext i
    fin_cases i <;> simp [p, e, f]
  calc
    LinearIndependent ℝ ![y-x, z-x] ↔
        LinearIndependent ℝ (fun i : {i : Fin 3 // i ≠ 0} => p i.1 -ᵥ p 0) :=
      linearIndependent_equiv' (e := e)
        (f := fun i : {i : Fin 3 // i ≠ 0} => p i.1 -ᵥ p 0)
        (g := ![y-x, z-x]) hfun
    _ ↔ AffineIndependent ℝ p :=
      (affineIndependent_iff_linearIndependent_vsub (k := ℝ) p 0).symm
    _ ↔ ¬ Collinear ℝ ({x,y,z} : Set (E d)) := by
      simpa [p] using (affineIndependent_iff_not_collinear_set (k := ℝ)
        (p₁ := x) (p₂ := y) (p₃ := z))

private def graphPrimalLinear (u : E 3) : E 2 →ₗ[ℝ] E 3 where
  toFun q := WithLp.toLp 2 ![q 0, q 1, u 0 * q 0 + u 1 * q 1]
  map_add' q r := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a q := by
    ext i
    fin_cases i <;> simp <;> ring

private theorem graphPrimalLinear_injective (u : E 3) :
    Function.Injective (graphPrimalLinear u) := by
  intro q r h
  ext i
  fin_cases i
  · have h0 := congrArg (fun p : E 3 => p 0) h
    simpa [graphPrimalLinear] using h0
  · have h1 := congrArg (fun p : E 3 => p 1) h
    simpa [graphPrimalLinear] using h1

private def graphPrimalBase (u : E 3) : E 3 := WithLp.toLp 2 ![0, 0, u 2]

private noncomputable def graphPrimalSubspace (u : E 3) : AffineSubspace ℝ (E 3) :=
  AffineSubspace.mk' (graphPrimalBase u) (LinearMap.range (graphPrimalLinear u))

private noncomputable def graphPrimalPlane (u : E 3) : Plane 3 := by
  refine ⟨graphPrimalSubspace u, ?_, ?_⟩
  · exact ⟨graphPrimalBase u, AffineSubspace.self_mem_mk' _ _⟩
  · rw [graphPrimalSubspace, AffineSubspace.direction_mk']
    change Module.finrank ℝ (LinearMap.range (graphPrimalLinear u)) = 2
    rw [LinearMap.finrank_range_of_inj (graphPrimalLinear_injective u)]
    simp [E]

private theorem graphPrimalPlane_mem (u p : E 3) (hp : u ∈ graphDualPlane p) :
    p ∈ (graphPrimalPlane u).1 := by
  let q : E 2 := WithLp.toLp 2 ![p 0, p 1]
  have hq : graphPrimalLinear u q = p - graphPrimalBase u := by
    apply (WithLp.ext_iff 2).2
    funext i
    fin_cases i
    · simp [graphPrimalLinear, graphPrimalBase, q, vsub_eq_sub]
    · simp [graphPrimalLinear, graphPrimalBase, q, vsub_eq_sub]
    · change u 0 * p 0 + u 1 * p 1 = p 2 - u 2
      change u 2 + u 0 * p 0 + u 1 * p 1 = p 2 at hp
      linarith
  have hpRange : p -ᵥ graphPrimalBase u ∈ LinearMap.range (graphPrimalLinear u) := by
    rw [vsub_eq_sub, ← hq]
    exact LinearMap.mem_range.mpr ⟨q, rfl⟩
  change p ∈ AffineSubspace.mk' (graphPrimalBase u) (LinearMap.range (graphPrimalLinear u))
  rw [AffineSubspace.mem_mk']
  exact hpRange

private theorem planes_eq_of_shared_noncollinear_triple {H K : Plane 3}
    {x y z : E 3} (hxH : x ∈ H.1) (hyH : y ∈ H.1) (hzH : z ∈ H.1)
    (hxK : x ∈ K.1) (hyK : y ∈ K.1) (hzK : z ∈ K.1)
    (hnoncol : ¬ Collinear ℝ ({x,y,z} : Set (E 3))) : H = K := by
  have hLI : LinearIndependent ℝ ![y-x, z-x] :=
    vsub_pair_independent_iff_not_collinear.mpr hnoncol
  let W : Submodule ℝ (E 3) := Submodule.span ℝ ({y-x,z-x} : Set (E 3))
  have hWrank : Module.finrank ℝ W = 2 := by
    change Module.finrank ℝ (Submodule.span ℝ ({y-x,z-x} : Set (E 3))) = 2
    rw [← Matrix.range_cons_cons_empty (y-x) (z-x) ![]]
    simp [finrank_span_eq_card hLI]
  have hWH : W ≤ H.1.direction := by
    apply Submodule.span_le.2
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hyH hxH
    · simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hzH hxH
  have hWK : W ≤ K.1.direction := by
    apply Submodule.span_le.2
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hyK hxK
    · simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hzK hxK
  have hdirH : H.1.direction = W := by
    have h := Submodule.eq_of_le_of_finrank_eq hWH
      (by rw [hWrank, H.2.2])
    exact h.symm
  have hdirK : K.1.direction = W := by
    have h := Submodule.eq_of_le_of_finrank_eq hWK
      (by rw [hWrank, K.2.2])
    exact h.symm
  apply Subtype.ext
  exact AffineSubspace.ext_of_direction_eq (hdirH.trans hdirK.symm) ⟨x, hxH, hxK⟩

private theorem exists_graph_dual_triple_point (x y z : E 3)
    (hproj : ¬ Collinear ℝ
      ({projectedPoint x, projectedPoint y, projectedPoint z} : Set (E 2))) :
    ∃ u : E 3, u ∈ graphDualPlane x ∧ u ∈ graphDualPlane y ∧ u ∈ graphDualPlane z := by
  let dy := projectedPoint y - projectedPoint x
  let dz := projectedPoint z - projectedPoint x
  let a₀ : ℝ := y 0 - x 0
  let a₁ : ℝ := y 1 - x 1
  let b₀ : ℝ := z 0 - x 0
  let b₁ : ℝ := z 1 - x 1
  let vY : E 2 := WithLp.toLp 2 ![a₀,a₁]
  let vZ : E 2 := WithLp.toLp 2 ![b₀,b₁]
  have hLI : LinearIndependent ℝ ![dy,dz] :=
    vsub_pair_independent_iff_not_collinear.mpr hproj
  have hdy : dy = vY := by
    apply (WithLp.ext_iff 2).2
    funext i
    fin_cases i <;> simp [dy, vY, projectedPoint, a₀, a₁]
  have hdz : dz = vZ := by
    apply (WithLp.ext_iff 2).2
    funext i
    fin_cases i <;> simp [dz, vZ, projectedPoint, b₀, b₁]
  have hLI2 : LinearIndependent ℝ ![vY,vZ] := by
    rw [← hdy, ← hdz]
    exact hLI
  have hvY : vY ≠ 0 := by
    intro hzero
    have h := (LinearIndependent.pair_iff.mp hLI2) 1 0 (by simp [hzero])
    norm_num at h
  have hcoord : a₀ ≠ 0 ∨ a₁ ≠ 0 := by
    by_cases ha₀ : a₀ = 0
    · right
      intro ha₁
      apply hvY
      ext i
      fin_cases i <;> simp [vY, ha₀, ha₁]
    · exact Or.inl ha₀
  let Δ : ℝ := a₀*b₁-a₁*b₀
  have hΔ : Δ ≠ 0 := by
    by_cases ha₀ : a₀ = 0
    · have ha₁ : a₁ ≠ 0 := by
        rcases hcoord with h | h
        · exact (h ha₀).elim
        · exact h
      intro hbad
      have hb₀ : b₀ = 0 := by
        have hmul : a₁*b₀ = 0 := by
          dsimp [Δ] at hbad
          rw [ha₀] at hbad
          nlinarith
        rcases mul_eq_zero.mp hmul with h | h
        · exact (ha₁ h).elim
        · exact h
      have hrel : b₁ • vY + (-a₁) • vZ = 0 := by
        ext i
        fin_cases i <;> simp [vY,vZ,ha₀,hb₀] <;> ring
      have h := (LinearIndependent.pair_iff.mp hLI2) b₁ (-a₁) hrel
      exact ha₁ (by linarith [h.2])
    · intro hbad
      have hrel : b₀ • vY + (-a₀) • vZ = 0 := by
        ext i
        fin_cases i <;> simp [vY,vZ] <;> nlinarith [hbad]
      have h := (LinearIndependent.pair_iff.mp hLI2) b₀ (-a₀) hrel
      exact ha₀ (by linarith [h.2])
  let c₀ : ℝ := ((y 2-x 2)*b₁-(z 2-x 2)*a₁)/Δ
  let c₁ : ℝ := (a₀*(z 2-x 2)-b₀*(y 2-x 2))/Δ
  have hsolveY : c₀*a₀+c₁*a₁ = y 2-x 2 := by
    dsimp [c₀,c₁]
    field_simp [hΔ]
    <;> ring
  have hsolveZ : c₀*b₀+c₁*b₁ = z 2-x 2 := by
    dsimp [c₀,c₁]
    field_simp [hΔ]
    <;> ring
  let c₂ : ℝ := x 2-c₀*x 0-c₁*x 1
  let u : E 3 := WithLp.toLp 2 ![c₀,c₁,c₂]
  have huX : u ∈ graphDualPlane x := by
    change u 2 + u 0*x 0 + u 1*x 1 = x 2
    simp [u,c₂]
    ring
  have hy0 : y 0 = x 0+a₀ := by dsimp [a₀]; ring
  have hy1 : y 1 = x 1+a₁ := by dsimp [a₁]; ring
  have hz0 : z 0 = x 0+b₀ := by dsimp [b₀]; ring
  have hz1 : z 1 = x 1+b₁ := by dsimp [b₁]; ring
  have huYscalar : c₂+c₀*y 0+c₁*y 1 = y 2 := by
    rw [hy0,hy1]
    calc
      _ = x 2+(c₀*a₀+c₁*a₁) := by dsimp [c₂]; ring
      _ = y 2 := by dsimp [a₀,a₁] at hsolveY; linarith
  have huZscalar : c₂+c₀*z 0+c₁*z 1 = z 2 := by
    rw [hz0,hz1]
    calc
      _ = x 2+(c₀*b₀+c₁*b₁) := by dsimp [c₂]; ring
      _ = z 2 := by dsimp [b₀,b₁] at hsolveZ; linarith
  have huY : u ∈ graphDualPlane y := by
    change u 2+u 0*y 0+u 1*y 1=y 2
    simpa [u] using huYscalar
  have huZ : u ∈ graphDualPlane z := by
    change u 2+u 0*z 0+u 1*z 1=z 2
    simpa [u] using huZscalar
  exact ⟨u,huX,huY,huZ⟩

/-- Spanned nonvertical physical planes are distinct triple-dual points,
motions.tex:445–451. -/
theorem graph_dual_spanned_points (S : Finset (E 3)) (x : E 3) (hx : x ∈ S)
    (hproj : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      ¬ Collinear ℝ ({a,b,c} : Set (E 3)) →
        ¬ Collinear ℝ ({WithLp.toLp 2 ![a 0,a 1], WithLp.toLp 2 ![b 0,b 1],
          WithLp.toLp 2 ![c 0,c 1]} : Set (E 2)))
    (P : Finset (Plane 3)) (hP : ∀ H ∈ P, x ∈ H.1 ∧ ∃ y ∈ S, ∃ z ∈ S,
      y ∈ H.1 ∧ z ∈ H.1 ∧ ¬ Collinear ℝ ({x,y,z} : Set (E 3))) :
    ∃ Z : Finset (E 3), Z.card = P.card ∧
      ∀ u ∈ Z, u ∈ graphDualPlane x ∧ ∃ y ∈ S, ∃ z ∈ S,
        ¬ Collinear ℝ ({x,y,z} : Set (E 3)) ∧
          u ∈ graphDualPlane y ∧ u ∈ graphDualPlane z := by
  classical
  let yOf (q : {H : Plane 3 // H ∈ P}) : E 3 := Classical.choose (hP q.1 q.2).2
  have ySpec (q : {H : Plane 3 // H ∈ P}) :
      yOf q ∈ S ∧ ∃ z ∈ S, yOf q ∈ q.1.1 ∧ z ∈ q.1.1 ∧
        ¬ Collinear ℝ ({x,yOf q,z} : Set (E 3)) :=
    Classical.choose_spec (hP q.1 q.2).2
  let zOf (q : {H : Plane 3 // H ∈ P}) : E 3 := Classical.choose (ySpec q).2
  have zSpec (q : {H : Plane 3 // H ∈ P}) :
      zOf q ∈ S ∧ yOf q ∈ q.1.1 ∧ zOf q ∈ q.1.1 ∧
        ¬ Collinear ℝ ({x,yOf q,zOf q} : Set (E 3)) :=
    Classical.choose_spec (ySpec q).2
  have tripleSpec (q : {H : Plane 3 // H ∈ P}) :
      yOf q ∈ S ∧ zOf q ∈ S ∧ yOf q ∈ q.1.1 ∧ zOf q ∈ q.1.1 ∧
        ¬ Collinear ℝ ({x,yOf q,zOf q} : Set (E 3)) :=
    ⟨(ySpec q).1, (zSpec q).1, (zSpec q).2.1, (zSpec q).2.2.1, (zSpec q).2.2.2⟩
  have hprojQ (q : {H : Plane 3 // H ∈ P}) :
      ¬ Collinear ℝ
        ({projectedPoint x,projectedPoint (yOf q),projectedPoint (zOf q)} : Set (E 2)) :=
    hproj x hx (yOf q) (tripleSpec q).1 (zOf q) (tripleSpec q).2.1
      (tripleSpec q).2.2.2.2
  let dualOf (q : {H : Plane 3 // H ∈ P}) : E 3 :=
    Classical.choose (exists_graph_dual_triple_point x (yOf q) (zOf q) (hprojQ q))
  have dualSpec (q : {H : Plane 3 // H ∈ P}) :
      dualOf q ∈ graphDualPlane x ∧ dualOf q ∈ graphDualPlane (yOf q) ∧
        dualOf q ∈ graphDualPlane (zOf q) :=
    Classical.choose_spec (exists_graph_dual_triple_point x (yOf q) (zOf q) (hprojQ q))
  have hplaneEq (q : {H : Plane 3 // H ∈ P}) : q.1 = graphPrimalPlane (dualOf q) := by
    apply planes_eq_of_shared_noncollinear_triple
      (H := q.1) (K := graphPrimalPlane (dualOf q))
    · exact (hP q.1 q.2).1
    · exact (tripleSpec q).2.2.1
    · exact (tripleSpec q).2.2.2.1
    · exact graphPrimalPlane_mem (dualOf q) x (dualSpec q).1
    · exact graphPrimalPlane_mem (dualOf q) (yOf q) (dualSpec q).2.1
    · exact graphPrimalPlane_mem (dualOf q) (zOf q) (dualSpec q).2.2
    · exact (tripleSpec q).2.2.2.2
  have hdualInj : Function.Injective dualOf := by
    intro q q' heq
    apply Subtype.ext
    calc
      q.1 = graphPrimalPlane (dualOf q) := hplaneEq q
      _ = graphPrimalPlane (dualOf q') := by rw [heq]
      _ = q'.1 := (hplaneEq q').symm
  let Z := P.attach.image dualOf
  have hZcard : Z.card = P.card := by
    dsimp [Z]
    rw [Finset.card_image_of_injective _ hdualInj, Finset.card_attach]
  refine ⟨Z, hZcard, ?_⟩
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨q, hq, rfl⟩
  exact ⟨(dualSpec q).1, yOf q, (tripleSpec q).1, zOf q, (tripleSpec q).2.1,
    (tripleSpec q).2.2.2.2, (dualSpec q).2.1, (dualSpec q).2.2⟩

private def graphDualParam (x : E 3) (s t : ℝ) : E 3 :=
  WithLp.toLp 2 ![s, t, x 2 - s * x 0 - t * x 1]

private theorem graphDualParam_mem (x : E 3) (s t : ℝ) :
    graphDualParam x s t ∈ graphDualPlane x := by
  change (graphDualParam x s t) 2 + (graphDualParam x s t) 0 * x 0 +
    (graphDualParam x s t) 1 * x 1 = x 2
  simp [graphDualParam]
  ring

private theorem graphDualParam_mem_iff (x y : E 3) (s t : ℝ) :
    graphDualParam x s t ∈ graphDualPlane y ↔
      x 2 + s * (y 0 - x 0) + t * (y 1 - x 1) = y 2 := by
  change (graphDualParam x s t) 2 + (graphDualParam x s t) 0 * y 0 +
    (graphDualParam x s t) 1 * y 1 = y 2 ↔ _
  simp [graphDualParam]
  constructor <;> intro h <;> nlinarith [h]

private noncomputable def graphDualPlaneWitness (x : E 3) : Plane 3 :=
  Classical.choose (graph_dual_plane_geometry x)

private theorem graphDualPlaneWitness_coe (x : E 3) :
    (graphDualPlaneWitness x).1 = graphDualPlane x :=
  Classical.choose_spec (graph_dual_plane_geometry x)

private theorem graphDualPlaneWitness_eq_imp_projected_eq (x y : E 3)
    (h : graphDualPlaneWitness x = graphDualPlaneWitness y) :
    projectedPoint x = projectedPoint y := by
  have hsets : graphDualPlane x = graphDualPlane y := by
    calc
      graphDualPlane x = (graphDualPlaneWitness x).1 :=
        (graphDualPlaneWitness_coe x).symm
      _ = (graphDualPlaneWitness y).1 :=
        congrArg (fun H : Plane 3 => (H.1 : Set (E 3))) h
      _ = graphDualPlane y := graphDualPlaneWitness_coe y
  have h00 : x 2 = y 2 := by
    have hh : graphDualParam x 0 0 ∈ graphDualPlane y := by
      rw [← hsets]
      exact graphDualParam_mem x 0 0
    change (graphDualParam x 0 0) 2 + (graphDualParam x 0 0) 0 * y 0 +
      (graphDualParam x 0 0) 1 * y 1 = y 2 at hh
    simp [graphDualParam] at hh
    exact hh
  have h10 : x 2 - x 0 + y 0 = y 2 := by
    have hh : graphDualParam x 1 0 ∈ graphDualPlane y := by
      rw [← hsets]
      exact graphDualParam_mem x 1 0
    change (graphDualParam x 1 0) 2 + (graphDualParam x 1 0) 0 * y 0 +
      (graphDualParam x 1 0) 1 * y 1 = y 2 at hh
    simp [graphDualParam] at hh
    nlinarith [hh]
  have h01 : x 2 - x 1 + y 1 = y 2 := by
    have hh : graphDualParam x 0 1 ∈ graphDualPlane y := by
      rw [← hsets]
      exact graphDualParam_mem x 0 1
    change (graphDualParam x 0 1) 2 + (graphDualParam x 0 1) 0 * y 0 +
      (graphDualParam x 0 1) 1 * y 1 = y 2 at hh
    simp [graphDualParam] at hh
    nlinarith [hh]
  apply (WithLp.ext_iff 2).2
  funext i
  fin_cases i
  · simp [projectedPoint, h00, h10]
    linarith
  · simp [projectedPoint, h00, h01]
    linarith

private theorem graphDualPlane_intersection_neempty (x y : E 3)
    (hxy : projectedPoint y ≠ projectedPoint x) :
    (((graphDualPlaneWitness x).1 : Set (E 3)) ∩
      ((graphDualPlaneWitness y).1 : Set (E 3))).Nonempty := by
  have hcoord : y 0 ≠ x 0 ∨ y 1 ≠ x 1 := by
    by_contra h
    push_neg at h
    apply hxy
    apply (WithLp.ext_iff 2).2
    funext i
    fin_cases i <;> simp [projectedPoint, h.1, h.2]
  let c : ℝ := y 2 - x 2
  rcases hcoord with h0 | h1
  · let p := graphDualParam x (c / (y 0 - x 0)) 0
    refine ⟨p, ?_⟩
    constructor
    · rw [graphDualPlaneWitness_coe]
      exact graphDualParam_mem x _ _
    · rw [graphDualPlaneWitness_coe]
      apply (graphDualParam_mem_iff x y _ _).2
      dsimp [c]
      field_simp [sub_ne_zero.mpr h0]
      ring
  · let p := graphDualParam x 0 (c / (y 1 - x 1))
    refine ⟨p, ?_⟩
    constructor
    · rw [graphDualPlaneWitness_coe]
      exact graphDualParam_mem x _ _
    · rw [graphDualPlaneWitness_coe]
      apply (graphDualParam_mem_iff x y _ _).2
      dsimp [c]
      field_simp [sub_ne_zero.mpr h1]
      ring

private theorem plane_intersection_is_line (H H' : Plane 3) (hne : H ≠ H')
    (hinter : ((H.1 : Set (E 3)) ∩ (H'.1 : Set (E 3))).Nonempty) :
    ∃ l : Line 3, (l.1 : Set (E 3)) = (H.1 : Set (E 3)) ∩ (H'.1 : Set (E 3)) := by
  rcases hinter with ⟨x, hx⟩
  have hxH : x ∈ H.1 := hx.1
  have hxH' : x ∈ H'.1 := hx.2
  let V : Submodule ℝ (E 3) := H.1.direction
  let W : Submodule ℝ (E 3) := H'.1.direction
  let I : AffineSubspace ℝ (E 3) := H.1 ⊓ H'.1
  have hdir : I.direction = (V ⊓ W : Submodule ℝ (E 3)) := by
    exact AffineSubspace.direction_inf_of_mem hxH hxH'
  have hHdim : Module.finrank ℝ V = 2 := H.2.2
  have hH'dim : Module.finrank ℝ W = 2 := H'.2.2
  have hsup : Module.finrank ℝ (V ⊔ W : Submodule ℝ (E 3)) ≤ 3 := by
    calc
      Module.finrank ℝ (V ⊔ W : Submodule ℝ (E 3)) ≤
          Module.finrank ℝ (⊤ : Submodule ℝ (E 3)) := Submodule.finrank_mono le_top
      _ = 3 := by simp [E]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V W
  rw [hHdim, hH'dim] at hsum
  have hIlo : 1 ≤ Module.finrank ℝ I.direction := by
    rw [hdir]
    omega
  have hIhi : Module.finrank ℝ I.direction ≤ 1 := by
    by_contra hnot
    have hIge2 : 2 ≤ Module.finrank ℝ I.direction := by omega
    have hIeq2 : Module.finrank ℝ (V ⊓ W : Submodule ℝ (E 3)) = 2 := by
      apply le_antisymm
      · exact le_trans (Submodule.finrank_mono inf_le_left) (by rw [hHdim])
      · rw [← hdir]
        exact hIge2
    have hsubeqH : (V ⊓ W : Submodule ℝ (E 3)) = V :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hIeq2, hHdim])
    have hsubeqH' : (V ⊓ W : Submodule ℝ (E 3)) = W :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hIeq2, hH'dim])
    have hdirs : H.1.direction = H'.1.direction := by
      change V = W
      exact hsubeqH.symm.trans hsubeqH'
    have hplanes : H.1 = H'.1 :=
      (AffineSubspace.eq_iff_direction_eq_of_mem hxH hxH').2 hdirs
    exact hne (Subtype.ext hplanes)
  have hIdim : Module.finrank ℝ I.direction = 1 := by omega
  refine ⟨⟨I, ⟨?_, hIdim⟩⟩, ?_⟩
  · exact ⟨x, (AffineSubspace.mem_inf_iff x H.1 H'.1).2 ⟨hxH, hxH'⟩⟩
  · change (I : Set (E 3)) = (H.1 : Set (E 3)) ∩ (H'.1 : Set (E 3))
    exact AffineSubspace.coe_inf H.1 H'.1

private noncomputable def dualArrangementLine (x y : E 3)
    (hxy : projectedPoint y ≠ projectedPoint x) : Line 3 :=
  Classical.choose (plane_intersection_is_line (graphDualPlaneWitness x)
    (graphDualPlaneWitness y)
    (by
      intro h
      exact hxy (graphDualPlaneWitness_eq_imp_projected_eq x y h).symm)
    (graphDualPlane_intersection_neempty x y hxy))

private theorem dualArrangementLine_spec (x y : E 3)
    (hxy : projectedPoint y ≠ projectedPoint x) :
    (dualArrangementLine x y hxy).1 =
      ((graphDualPlaneWitness x).1 : Set (E 3)) ∩
        ((graphDualPlaneWitness y).1 : Set (E 3)) := by
  exact Classical.choose_spec (plane_intersection_is_line (graphDualPlaneWitness x)
    (graphDualPlaneWitness y)
    (by
      intro h
      exact hxy (graphDualPlaneWitness_eq_imp_projected_eq x y h).symm)
    (graphDualPlane_intersection_neempty x y hxy))

private theorem dualArrangementLine_mem_iff (x y : E 3)
    (hxy : projectedPoint y ≠ projectedPoint x) (u : E 3) :
    u ∈ (dualArrangementLine x y hxy).1 ↔
      u ∈ graphDualPlane x ∧ u ∈ graphDualPlane y := by
  change u ∈ ((dualArrangementLine x y hxy).1 : Set (E 3)) ↔ _
  rw [dualArrangementLine_spec, graphDualPlaneWitness_coe, graphDualPlaneWitness_coe]
  exact Set.mem_inter_iff u _ _

private theorem projectedTriple_y_ne (x y z : E 3)
    (hproj : ¬ Collinear ℝ
      ({projectedPoint x, projectedPoint y, projectedPoint z} : Set (E 2))) :
    projectedPoint y ≠ projectedPoint x := by
  intro heq
  have hLI : LinearIndependent ℝ
      ![projectedPoint y - projectedPoint x, projectedPoint z - projectedPoint x] :=
    vsub_pair_independent_iff_not_collinear.mpr hproj
  have hzero : projectedPoint y - projectedPoint x = 0 := sub_eq_zero.mpr heq
  have h := (LinearIndependent.pair_iff.mp hLI) 1 0 (by simp [hzero])
  norm_num at h

private theorem projectedTriple_z_ne (x y z : E 3)
    (hproj : ¬ Collinear ℝ
      ({projectedPoint x, projectedPoint y, projectedPoint z} : Set (E 2))) :
    projectedPoint z ≠ projectedPoint x := by
  intro heq
  have hLI : LinearIndependent ℝ
      ![projectedPoint y - projectedPoint x, projectedPoint z - projectedPoint x] :=
    vsub_pair_independent_iff_not_collinear.mpr hproj
  have hzero : projectedPoint z - projectedPoint x = 0 := sub_eq_zero.mpr heq
  have h := (LinearIndependent.pair_iff.mp hLI) 0 1 (by simp [hzero])
  norm_num at h

private theorem projectedTriple_det_ne (x y z : E 3)
    (hproj : ¬ Collinear ℝ
      ({projectedPoint x, projectedPoint y, projectedPoint z} : Set (E 2))) :
    ((y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0)) ≠ 0 := by
  let a : ℝ := y 0 - x 0
  let b : ℝ := y 1 - x 1
  let c : ℝ := z 0 - x 0
  let d : ℝ := z 1 - x 1
  let vY : E 2 := WithLp.toLp 2 ![a,b]
  let vZ : E 2 := WithLp.toLp 2 ![c,d]
  have hLI : LinearIndependent ℝ ![vY,vZ] := by
    have h := vsub_pair_independent_iff_not_collinear.mpr hproj
    have hdy : projectedPoint y - projectedPoint x = vY := by
      apply (WithLp.ext_iff 2).2
      funext i
      fin_cases i <;> simp [projectedPoint, vY, a, b]
    have hdz : projectedPoint z - projectedPoint x = vZ := by
      apply (WithLp.ext_iff 2).2
      funext i
      fin_cases i <;> simp [projectedPoint, vZ, c, d]
    rw [← hdy, ← hdz]
    exact h
  have hvY : vY ≠ 0 := by
    intro hzero
    have h := (LinearIndependent.pair_iff.mp hLI) 1 0 (by simp [hzero])
    norm_num at h
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_cases ha : a = 0
    · right
      intro hb
      apply hvY
      ext i
      fin_cases i <;> simp [vY, ha, hb]
    · exact Or.inl ha
  intro hdet
  have hdet' : a * d - b * c = 0 := by simpa [a, b, c, d] using hdet
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      rcases hab with ha' | hb'
      · exact (ha' ha).elim
      · exact hb'
    have hc : c = 0 := by
      have hmul : b * c = 0 := by
        rw [ha] at hdet'
        nlinarith [hdet']
      exact (mul_eq_zero.mp hmul).resolve_left hb
    have hrel : d • vY + (-b) • vZ = 0 := by
      ext i
      fin_cases i <;> simp [vY, vZ, ha, hc] <;> ring
    have h := (LinearIndependent.pair_iff.mp hLI) d (-b) hrel
    exact hb (by linarith [h.2])
  · have hrel : c • vY + (-a) • vZ = 0 := by
      ext i
      fin_cases i
      · simp [vY, vZ] <;> ring
      · simp [vY, vZ]
        nlinarith [hdet']
    have h := (LinearIndependent.pair_iff.mp hLI) c (-a) hrel
    exact ha (by linarith [h.2])

private theorem graphDual_direction_condition (x : E 3) (H : Plane 3)
    (hH : (H.1 : Set (E 3)) = graphDualPlane x) {v : E 3}
    (hv : v ∈ H.1.direction) :
    v 2 + v 0 * x 0 + v 1 * x 1 = 0 := by
  let p := graphDualParam x 0 0
  have hp : p ∈ H.1 := by
    change p ∈ (H.1 : Set (E 3))
    rw [hH]
    exact graphDualParam_mem x 0 0
  have hvadd : v +ᵥ p ∈ H.1 := H.1.vadd_mem_of_mem_direction hv hp
  have hpGraph : p ∈ graphDualPlane x := graphDualParam_mem x 0 0
  have hvGraph : v +ᵥ p ∈ graphDualPlane x := by
    change v +ᵥ p ∈ (H.1 : Set (E 3)) at hvadd
    rw [hH] at hvadd
    exact hvadd
  change p 2 + p 0 * x 0 + p 1 * x 1 = x 2 at hpGraph
  change (v +ᵥ p) 2 + (v +ᵥ p) 0 * x 0 + (v +ᵥ p) 1 * x 1 = x 2 at hvGraph
  simp [graphDualParam, vadd_eq_add] at hpGraph hvGraph
  nlinarith [hpGraph, hvGraph]

private theorem dualArrangementLines_ne_of_projectedTriple (x y z : E 3)
    (hproj : ¬ Collinear ℝ
      ({projectedPoint x, projectedPoint y, projectedPoint z} : Set (E 2))) :
    dualArrangementLine x y (projectedTriple_y_ne x y z hproj) ≠
      dualArrangementLine x z (projectedTriple_z_ne x y z hproj) := by
  let hyx := projectedTriple_y_ne x y z hproj
  let hzx := projectedTriple_z_ne x y z hproj
  let ly := dualArrangementLine x y hyx
  let lz := dualArrangementLine x z hzx
  intro hEq
  have hflatEq : ly.1 = lz.1 := congrArg Subtype.val hEq
  have hsubX : ly.1 ≤ (graphDualPlaneWitness x).1 := by
    intro p hp
    have hpSet : p ∈ (ly.1 : Set (E 3)) := hp
    rw [dualArrangementLine_spec] at hpSet
    change p ∈ ((graphDualPlaneWitness x).1 : Set (E 3))
    exact hpSet.1
  have hsubY : ly.1 ≤ (graphDualPlaneWitness y).1 := by
    intro p hp
    have hpSet : p ∈ (ly.1 : Set (E 3)) := hp
    rw [dualArrangementLine_spec] at hpSet
    change p ∈ ((graphDualPlaneWitness y).1 : Set (E 3))
    exact hpSet.2
  have hsubZ : ly.1 ≤ (graphDualPlaneWitness z).1 := by
    intro p hp
    have hpLz : p ∈ lz.1 := by simpa [hflatEq] using hp
    have hpSet : p ∈ (lz.1 : Set (E 3)) := hpLz
    rw [dualArrangementLine_spec] at hpSet
    change p ∈ ((graphDualPlaneWitness z).1 : Set (E 3))
    exact hpSet.2
  have hdirNe : ly.1.direction ≠ ⊥ := by
    intro hbot
    have hfin : Module.finrank ℝ ly.1.direction = 0 := by simp [hbot]
    rw [ly.2.2] at hfin
    norm_num at hfin
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdirNe
  have hvx := graphDual_direction_condition x (graphDualPlaneWitness x)
    (graphDualPlaneWitness_coe x) ((AffineSubspace.direction_le hsubX) hv)
  have hvy := graphDual_direction_condition y (graphDualPlaneWitness y)
    (graphDualPlaneWitness_coe y) ((AffineSubspace.direction_le hsubY) hv)
  have hvz := graphDual_direction_condition z (graphDualPlaneWitness z)
    (graphDualPlaneWitness_coe z) ((AffineSubspace.direction_le hsubZ) hv)
  have heqY : v 0 * (y 0 - x 0) + v 1 * (y 1 - x 1) = 0 := by
    nlinarith [hvx, hvy]
  have heqZ : v 0 * (z 0 - x 0) + v 1 * (z 1 - x 1) = 0 := by
    nlinarith [hvx, hvz]
  have hdet := projectedTriple_det_ne x y z hproj
  have hprod0 :
      ((y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0)) * v 0 = 0 := by
    calc
      _ = (z 1 - x 1) *
          (v 0 * (y 0 - x 0) + v 1 * (y 1 - x 1)) -
          (y 1 - x 1) * (v 0 * (z 0 - x 0) + v 1 * (z 1 - x 1)) := by ring
      _ = 0 := by rw [heqY, heqZ]; ring
  have hprod1 :
      ((y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0)) * v 1 = 0 := by
    calc
      _ = (y 0 - x 0) *
          (v 0 * (z 0 - x 0) + v 1 * (z 1 - x 1)) -
          (z 0 - x 0) * (v 0 * (y 0 - x 0) + v 1 * (y 1 - x 1)) := by ring
      _ = 0 := by rw [heqY, heqZ]; ring
  have hv0 : v 0 = 0 := (mul_eq_zero.mp hprod0).resolve_left hdet
  have hv1 : v 1 = 0 := (mul_eq_zero.mp hprod1).resolve_left hdet
  have hv2 : v 2 = 0 := by rw [hv0, hv1] at hvx; linarith
  apply hvne
  apply (WithLp.ext_iff 2).2
  funext i
  fin_cases i
  · exact hv0
  · exact hv1
  · exact hv2

private theorem dualArrangementLine_designated_cap (S : Finset (E 3)) (x : E 3)
    (Z : Finset (E 3))
    (hZ : ∀ u ∈ Z, u ∈ graphDualPlane x ∧ ∃ y ∈ S, ∃ z ∈ S,
      ¬ Collinear ℝ ({WithLp.toLp 2 ![x 0,x 1], WithLp.toLp 2 ![y 0,y 1],
        WithLp.toLp 2 ![z 0,z 1]} : Set (E 2)) ∧
        u ∈ graphDualPlane y ∧ u ∈ graphDualPlane z)
    (w : E 3) (hw : projectedPoint w ≠ projectedPoint x) :
    (Z.filter (fun u => u ∈ (dualArrangementLine x w hw).1)).card ≤ S.card := by
  classical
  let l := dualArrangementLine x w hw
  let T := Z.filter (fun u => u ∈ l.1)
  let hmemZ (q : {u // u ∈ T}) : q.1 ∈ Z := (Finset.mem_filter.mp q.2).1
  let yOf (q : {u // u ∈ T}) : E 3 := Classical.choose (hZ q.1 (hmemZ q)).2
  have ySpec (q : {u // u ∈ T}) :
      yOf q ∈ S ∧ ∃ z ∈ S,
        ¬ Collinear ℝ ({WithLp.toLp 2 ![x 0,x 1], WithLp.toLp 2 ![yOf q 0,yOf q 1],
          WithLp.toLp 2 ![z 0,z 1]} : Set (E 2)) ∧
          q.1 ∈ graphDualPlane (yOf q) ∧ q.1 ∈ graphDualPlane z :=
    Classical.choose_spec (hZ q.1 (hmemZ q)).2
  let zOf (q : {u // u ∈ T}) : E 3 := Classical.choose (ySpec q).2
  have zSpec (q : {u // u ∈ T}) :
      zOf q ∈ S ∧
        ¬ Collinear ℝ ({WithLp.toLp 2 ![x 0,x 1], WithLp.toLp 2 ![yOf q 0,yOf q 1],
          WithLp.toLp 2 ![zOf q 0,zOf q 1]} : Set (E 2)) ∧
          q.1 ∈ graphDualPlane (yOf q) ∧ q.1 ∈ graphDualPlane (zOf q) :=
    Classical.choose_spec (ySpec q).2
  have hproj (q : {u // u ∈ T}) :
      ¬ Collinear ℝ
        ({projectedPoint x, projectedPoint (yOf q), projectedPoint (zOf q)} : Set (E 2)) := by
    simpa [projectedPoint] using (zSpec q).2.1
  let arrangementLine (q : {p : E 3 // projectedPoint p ≠ projectedPoint x}) :=
    dualArrangementLine x q.1 q.2
  let lineY (q : {u // u ∈ T}) :=
    arrangementLine ⟨yOf q, projectedTriple_y_ne x (yOf q) (zOf q) (hproj q)⟩
  let lineZ (q : {u // u ∈ T}) :=
    arrangementLine ⟨zOf q, projectedTriple_z_ne x (yOf q) (zOf q) (hproj q)⟩
  let partner (q : {u // u ∈ T}) : E 3 := if lineY q = l then zOf q else yOf q
  have partner_mem (q : {u // u ∈ T}) : partner q ∈ S := by
    by_cases hEq : lineY q = l
    · simpa [partner, hEq] using (zSpec q).1
    · simpa [partner, hEq] using (ySpec q).1
  have partner_valid (q : {u // u ∈ T}) :
      projectedPoint (partner q) ≠ projectedPoint x := by
    by_cases hEq : lineY q = l
    · simpa [partner, hEq] using
        (projectedTriple_z_ne x (yOf q) (zOf q) (hproj q))
    · simpa [partner, hEq] using
        (projectedTriple_y_ne x (yOf q) (zOf q) (hproj q))
  let partnerLine (q : {u // u ∈ T}) :=
    arrangementLine ⟨partner q, partner_valid q⟩
  have partnerLine_ne (q : {u // u ∈ T}) : partnerLine q ≠ l := by
    by_cases hEq : lineY q = l
    · have hYZ : lineY q ≠ lineZ q :=
        dualArrangementLines_ne_of_projectedTriple x (yOf q) (zOf q) (hproj q)
      have hpartnerIsZ : partnerLine q = lineZ q := by
        apply congrArg arrangementLine
        apply Subtype.ext
        simp [partner, hEq]
      intro hbad
      have hzEq : lineZ q = l := hpartnerIsZ.symm.trans hbad
      exact hYZ (hEq.trans hzEq.symm)
    · have hpartnerIsY : partnerLine q = lineY q := by
        apply congrArg arrangementLine
        apply Subtype.ext
        simp [partner, hEq]
      intro hbad
      exact hEq (hpartnerIsY.symm.trans hbad)
  have partner_inc (q : {u // u ∈ T}) : q.1 ∈ (partnerLine q).1 := by
    apply (dualArrangementLine_mem_iff x (partner q) (partner_valid q) q.1).2
    constructor
    · exact (hZ q.1 (hmemZ q)).1
    · by_cases hEq : lineY q = l
      · simpa [partner, hEq] using (zSpec q).2.2.2
      · simpa [partner, hEq] using (zSpec q).2.2.1
  have hcard : T.card ≤ S.card := by
    calc
      T.card = T.attach.card := by simp
      _ ≤ S.card := Finset.card_le_card_of_injOn partner
        (by
          intro q hq
          exact partner_mem q)
        (by
          intro q hq r hr hpr
          have hvalidEq :
              (⟨partner q, partner_valid q⟩ :
                {p : E 3 // projectedPoint p ≠ projectedPoint x}) =
              ⟨partner r, partner_valid r⟩ := Subtype.ext hpr
          have hlineEq : partnerLine q = partnerLine r := congrArg arrangementLine hvalidEq
          have hbound := affine_lines_intersection_bound 3 l (partnerLine q)
            (partnerLine_ne q).symm
          have hboundNat : ((l.1 : Set (E 3)) ∩
              ((partnerLine q).1 : Set (E 3))).ncard ≤ 1 := by
            exact_mod_cast hbound.2
          have hsub := (Set.ncard_le_one hbound.1).mp hboundNat
          apply Subtype.ext
          apply hsub
          · exact ⟨(Finset.mem_filter.mp q.2).2, partner_inc q⟩
          · have hrinc : r.1 ∈ (partnerLine q).1 := by
              rw [hlineEq]
              exact partner_inc r
            exact ⟨(Finset.mem_filter.mp r.2).2, hrinc⟩)
  exact hcard

/-- An anchor graph plane has at most n arrangement lines; designated transverse
triple points lie on two lines and any one line contains at most n of them,
motions.tex:451–458. -/
theorem graph_dual_anchor_lines (S : Finset (E 3)) (x : E 3) (Z : Finset (E 3))
    (hZ : ∀ u ∈ Z, u ∈ graphDualPlane x ∧ ∃ y ∈ S, ∃ z ∈ S,
      ¬ Collinear ℝ ({WithLp.toLp 2 ![x 0,x 1], WithLp.toLp 2 ![y 0,y 1],
        WithLp.toLp 2 ![z 0,z 1]} : Set (E 2)) ∧
        u ∈ graphDualPlane y ∧ u ∈ graphDualPlane z) :
    ∃ L : Finset (Line 3), L.card ≤ S.card ∧
      (∀ l ∈ L, (l.1 : Set (E 3)) ⊆ graphDualPlane x) ∧
      (∀ u ∈ Z, 2 ≤ (L.filter (fun l => u ∈ l.1)).card) ∧
      (∀ l ∈ L, (Z.filter (fun u => u ∈ l.1)).card ≤ S.card) := by
  classical
  let I := S.filter (fun y => projectedPoint y ≠ projectedPoint x)
  let lineFor (q : {y : E 3 // y ∈ I}) : Line 3 :=
    dualArrangementLine x q.1 (Finset.mem_filter.mp q.2).2
  let L : Finset (Line 3) := I.attach.image lineFor
  have hLcard : L.card ≤ S.card := by
    calc
      L.card ≤ I.attach.card := Finset.card_image_le
      _ = I.card := by simp
      _ ≤ S.card := Finset.card_filter_le S _
  refine ⟨L, hLcard, ?_, ?_, ?_⟩
  · intro l hl u hu
    rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
    change u ∈ (dualArrangementLine x q.1 (Finset.mem_filter.mp q.2).2).1 at hu
    exact (dualArrangementLine_mem_iff x q.1 (Finset.mem_filter.mp q.2).2 u).mp hu |>.1
  · intro u hu
    rcases hZ u hu with ⟨huX, y, hyS, z, hzS, hprojRaw, huY, huZ⟩
    have hproj : ¬ Collinear ℝ
        ({projectedPoint x, projectedPoint y, projectedPoint z} : Set (E 2)) := by
      simpa [projectedPoint] using hprojRaw
    have hyx := projectedTriple_y_ne x y z hproj
    have hzx := projectedTriple_z_ne x y z hproj
    let qy : {a : E 3 // a ∈ I} := ⟨y, Finset.mem_filter.mpr ⟨hyS, hyx⟩⟩
    let qz : {a : E 3 // a ∈ I} := ⟨z, Finset.mem_filter.mpr ⟨hzS, hzx⟩⟩
    let ly := dualArrangementLine x y hyx
    let lz := dualArrangementLine x z hzx
    have hlymem : ly ∈ L := by
      change ly ∈ I.attach.image lineFor
      apply Finset.mem_image.mpr
      refine ⟨qy, Finset.mem_attach _ _, ?_⟩
      dsimp [ly, lineFor, qy]
    have hlzmem : lz ∈ L := by
      change lz ∈ I.attach.image lineFor
      apply Finset.mem_image.mpr
      refine ⟨qz, Finset.mem_attach _ _, ?_⟩
      dsimp [lz, lineFor, qz]
    have huLy : u ∈ ly.1 :=
      (dualArrangementLine_mem_iff x y hyx u).2 ⟨huX, huY⟩
    have huLz : u ∈ lz.1 :=
      (dualArrangementLine_mem_iff x z hzx u).2 ⟨huX, huZ⟩
    have hlyz : ly ≠ lz := by
      simpa [ly, lz] using dualArrangementLines_ne_of_projectedTriple x y z hproj
    have hpairSub : ({ly, lz} : Finset (Line 3)) ⊆
        L.filter (fun l => u ∈ l.1) := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hlymem, huLy⟩
      · exact Finset.mem_filter.mpr ⟨hlzmem, huLz⟩
    calc
      2 = ({ly, lz} : Finset (Line 3)).card := by simp [hlyz]
      _ ≤ (L.filter (fun l => u ∈ l.1)).card := Finset.card_le_card hpairSub
  · intro l hl
    rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
    exact dualArrangementLine_designated_cap S x Z hZ q.1
      (Finset.mem_filter.mp q.2).2

end DistinctDistances.TrackC
