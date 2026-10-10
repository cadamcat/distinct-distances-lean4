import DistinctDistances.TrackA.ProjectiveCutProjectionSupport
import OAI.NumberTheory.PowerFree.SurfaceCounting

namespace DistinctDistances.TrackA
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators

theorem equal_dimension_separator {n l : ℕ} (X W : AffineVariety n)
    (hX : X.IsIrreducible) (hW : W.IsIrreducible) (hl : 1 ≤ l)
    (hXd : X.dimension = l) (hWd : W.dimension = l) (hne : X ≠ W) :
    ∃ f : Poly n, f ∈ W.ideal ∧ f ∉ X.ideal := by
  have hnot : ¬ W.ideal ≤ X.ideal := by
    intro hle
    letI : W.ideal.IsPrime := hW
    have he := OAI.QuarticPowerFree.prime_same_dimension_eq (h := l-1)
      W.ideal X.ideal hle (by change W.dimension = _; omega)
      (by change X.dimension = _; omega)
    exact hne (AffineVariety.ext he.symm)
  change ¬ ∀ f, f ∈ W.ideal → f ∈ X.ideal at hnot
  push Not at hnot
  exact hnot

theorem projectiveHomogenize_eval_cons {n : ℕ} (f : Poly n) (x : Point n) :
    MvPolynomial.eval (Fin.cons 1 x) (projectiveHomogenize f.totalDegree f) =
      MvPolynomial.eval x f := by
  have h := congrArg (MvPolynomial.aeval x) (projectiveHomogenize_aeval f)
  rw [MvPolynomial.comp_aeval_apply] at h
  have hcoords : (fun j : Fin (n+1) => MvPolynomial.aeval x
      ((Fin.cons (1 : Poly n) MvPolynomial.X : Fin (n+1) → Poly n) j)) =
      Fin.cons (1 : ℂ) x := by
    ext j
    cases j using Fin.cases <;> simp
  rw [hcoords] at h
  simpa only [MvPolynomial.aeval_eq_eval] using h

/-- A proper source cut has a nondominant radial image in the dimension-preserving case. -/
theorem radial_fiber_avoids_proper_cut {n l : ℕ} (X : AffineVariety n)
    (hX : X.IsIrreducible) (hXd : X.dimension = l) (p : Point n)
    (himage : (radialImage p X).dimension = l) (hactual : ∃ x ∈ X.points, x ≠ p)
    (f : Poly n) (hf : f ∉ X.ideal) :
    ∃ (H : Poly n) (e : ℕ), H.IsHomogeneous e ∧ H ∉ (radialImage p X).ideal ∧
      ∀ z : ProjectivePoint n, MvPolynomial.eval z.rep H ≠ 0 →
        ∀ x ∈ radialFiber p X z, MvPolynomial.eval x f ≠ 0 := by
  let V := projectiveClosure X
  let F := projectiveHomogenize f.totalDegree f
  let φ := radialLinearProjection p
  let Y := radialImage p X
  obtain ⟨x0, hx0, hx0ne⟩ := hactual
  have hVne : V.points.Nonempty :=
    ⟨affineEmbedding x0, (affineEmbedding_mem_closure X x0).2 hx0⟩
  have hVdim : V.affineCone.dimension = l+1 := by
    rw [V.dimension_cone hVne, projectiveClosure_dimension X ⟨x0, hx0⟩, hXd]
  have hVprime : V.IsIrreducible := projectiveClosure_isIrreducible X hX
  have hFhom : F.IsHomogeneous f.totalDegree := projectiveHomogenize_homogeneous _ _
  have hFnot : F ∉ V.ideal := by
    intro h
    apply hf
    have hh := projectiveClosure_aeval_mem X F h
    rwa [projectiveHomogenize_aeval] at hh
  have hYne : Y.points.Nonempty :=
    ⟨radialProjection p x0 hx0ne, ProjectiveVariety.subset_closure _ ⟨x0, hx0, hx0ne, rfl⟩⟩
  obtain ⟨H, e, hHhom, hHnot, hHZ⟩ := cone_cut_image_separator V hVprime hVdim F
    hFhom hFnot φ Y hYne himage
  refine ⟨H, e, hHhom, hHnot, ?_⟩
  intro z hz x hx hfx
  obtain ⟨hxX, hxne, hproj⟩ := hx
  have hcons0 : (Fin.cons (1 : ℂ) x : Point (n+1)) ≠ 0 := by
    intro h
    have hh := congrFun h (0 : Fin (n+1))
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using hh)
  have hconsV : Fin.cons (1 : ℂ) x ∈ V.affineCone.points := by
    apply (ProjectiveVariety.mem_points_mk_iff V _ hcons0).1
    exact (affineEmbedding_mem_closure X x).2 hxX
  have hconsF : MvPolynomial.eval (Fin.cons 1 x) F = 0 :=
    (projectiveHomogenize_eval_cons f x).trans hfx
  have hφ : φ (Fin.cons 1 x) ≠ 0 := by
    simpa only [φ, radialLinearProjection_cons] using sub_ne_zero.mpr hxne
  have hzZ : z ∈ (projectiveCutImage V F φ).points := by
    apply ProjectiveVariety.subset_closure
    refine ⟨Fin.cons 1 x, hconsV, hconsF, hφ, ?_⟩
    simpa only [φ, radialLinearProjection_cons, radialProjection] using hproj
  have hzcone : z.rep ∈ (projectiveCutImage V F φ).affineCone.points := by
    apply (ProjectiveVariety.mem_points_mk_iff _ _ z.rep_nonzero).1
    simpa using hzZ
  apply hz
  simpa only [MvPolynomial.aeval_eq_eval] using hzcone H hHZ

theorem radial_fibers_disjoint_open {n l : ℕ} (X W : AffineVariety n)
    (hX : X.IsIrreducible) (hW : W.IsIrreducible) (hl : 1 ≤ l)
    (hXd : X.dimension = l) (hWd : W.dimension = l) (hne : X ≠ W)
    (p : Point n) (himage : (radialImage p X).dimension = l)
    (hactual : ∃ x ∈ X.points, x ≠ p) :
    ∃ (H : Poly n) (e : ℕ), H.IsHomogeneous e ∧ H ∉ (radialImage p X).ideal ∧
      ∀ z : ProjectivePoint n, MvPolynomial.eval z.rep H ≠ 0 →
        Disjoint (radialFiber p X z) (radialFiber p W z) := by
  obtain ⟨f, hfW, hfX⟩ := equal_dimension_separator X W hX hW hl hXd hWd hne
  obtain ⟨H, e, hhom, hnot, havoid⟩ := radial_fiber_avoids_proper_cut X hX hXd p
    himage hactual f hfX
  refine ⟨H, e, hhom, hnot, ?_⟩
  intro z hz
  rw [Set.disjoint_left]
  intro x hxX hxW
  apply havoid z hz x hxX
  simpa only [MvPolynomial.aeval_eq_eval] using hxW.1 f hfW

end
end DistinctDistances.TrackA
