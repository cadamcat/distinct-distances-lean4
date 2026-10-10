import DistinctDistances.TrackD.GeoRadial
import DistinctDistances.Bridges.RealLineLift
import DistinctDistances.TrackD.Inputs

/-! Real affine lines associated to real complex source lines. -/

namespace DistinctDistances.TrackD.GeoLines
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

 theorem toC_injective : Function.Injective (toC (d := d)) := by
  intro x y h
  ext i
  exact Complex.ofReal_injective (congrFun h i)

 @[simp] theorem toC_add (x y : Pt d) : toC (x+y) = toC x + toC y := by
  ext i; simp [toC]

 @[simp] theorem toC_sub (x y : Pt d) : toC (x-y) = toC x - toC y := by
  ext i; simp [toC]

 @[simp] theorem toC_zero : toC (0 : Pt d) = 0 := by ext i; simp [toC]

 @[simp] theorem toC_smul (t : ℝ) (x : Pt d) : toC (t • x) = (t : ℂ) • toC x := by
  ext i; simp [toC]

 theorem param_set_eq_mk {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a v : V) : (AffineSubspace.mk' a (K ∙ v) : Set V) = {z | ∃ t : K, z = a+t • v} := by
  ext z
  simp only [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub,
    Submodule.mem_span_singleton, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      z = a+(z-a) := by abel
      _ = a+t • v := by rw [← ht]
  · rintro ⟨t, rfl⟩
    exact ⟨t, by abel⟩

 theorem line_curve (Y : AffineVariety d) (hY : IsLine Y) : IsCurve Y := by
  obtain ⟨a, v, hv, hpts⟩ := hY
  obtain ⟨j, hj⟩ := GeoRadial.exists_coord v hv
  have heq : Y = Bridges.complexLine a v :=
    (AffineVariety.points_eq_iff _ _).mp (hpts.trans (Bridges.complexLine_points a v j hj).symm)
  rw [heq]
  exact ⟨Bridges.complexLine_irreducible a v, Bridges.complexLine_dimension a v j hj⟩

 theorem closure_minimal (T : Set (Point d)) (Y : AffineVariety d) (hT : T ⊆ Y.points) :
    (AffineVariety.closure T).points ⊆ Y.points := by
  intro z hz f hf
  exact hz f (fun x hx => hT hx f hf)

 theorem closure_mono (T U : Set (Point d)) (h : T ⊆ U) :
    (AffineVariety.closure T).points ⊆ (AffineVariety.closure U).points := by
  intro z hz f hf
  exact hz f (fun x hx => hf x (h hx))

 theorem two_points_line (Y : AffineVariety d) (hY : IsLine Y)
    (a b : Point d) (ha : a ∈ Y.points) (hb : b ∈ Y.points) (hne : b ≠ a) :
    Y.points = {z | ∃ t : ℂ, z = a+t • (b-a)} := by
  obtain ⟨a₀, v₀, hv₀, hpts⟩ := hY
  let F := AffineSubspace.mk' a₀ (ℂ ∙ v₀)
  have hF : Y.points = (F : Set (Point d)) := hpts.trans (param_set_eq_mk a₀ v₀).symm
  have haF : a ∈ F := by change a ∈ (F : Set (Point d)); rw [← hF]; exact ha
  have hbF : b ∈ F := by change b ∈ (F : Set (Point d)); rw [← hF]; exact hb
  have hvdir : b-a ∈ F.direction := by
    simpa only [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hbF haF
  have hle : (ℂ ∙ (b-a)) ≤ F.direction :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvdir)
  have he : (ℂ ∙ (b-a)) = F.direction :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_span_singleton (sub_ne_zero.mpr hne)]
      dsimp only [F]; rw [AffineSubspace.direction_mk', finrank_span_singleton hv₀])
  have hmk : AffineSubspace.mk' a (ℂ ∙ (b-a)) = F := by
    rw [he]
    exact AffineSubspace.mk'_eq haF
  rw [hF, ← hmk]
  exact param_set_eq_mk _ _

 theorem real_parameters (Y : AffineVariety d) (hY : IsLine Y) (hreal : IsRealFlat Y) :
    ∃ a v : Pt d, v ≠ 0 ∧ Y.points = {z | ∃ t : ℂ, z = toC a+t • toC v} := by
  obtain ⟨F, hFne, hF⟩ := hreal
  have hsub : toC '' (F : Set (Pt d)) ⊆ Y.points := by
    rw [hF]
    exact AffineVariety.subset_closure _
  obtain ⟨a, ha⟩ := hFne
  have hnot : ¬ (F : Set (Pt d)).Subsingleton := by
    intro hs
    have hall : ∀ z ∈ Y.points, z = toC a := by
      intro z hz
      ext j
      let f : Poly d := MvPolynomial.X j - MvPolynomial.C (toC a j)
      have hf : f ∈ (AffineVariety.closure (toC '' (F : Set (Pt d)))).ideal := by
        rintro x ⟨q, hq, rfl⟩
        have he : q = a := hs hq ha
        simp [f, he]
      have hz' : z ∈ (AffineVariety.closure (toC '' (F : Set (Pt d)))).points := hF ▸ hz
      have he := hz' f hf
      simpa [f, sub_eq_zero] using he
    have hfinite : Y.points.Finite := (Set.finite_singleton (toC a)).subset (fun z hz => hall z hz)
    have hYC := line_curve Y hY
    exact (Bridges.curve_points_infinite Y hYC.1 hYC.2) hfinite
  obtain ⟨b, hb, hba⟩ : ∃ b ∈ F, b ≠ a := by
    by_contra! h
    apply hnot
    intro x hx y hy
    exact (h x hx).trans (h y hy).symm
  let v := b-a
  have hv : v ≠ 0 := sub_ne_zero.mpr hba
  have hCa : toC a ∈ Y.points := hsub ⟨a, ha, rfl⟩
  have hCb : toC b ∈ Y.points := hsub ⟨b, hb, rfl⟩
  have hCne : toC b ≠ toC a := fun h => hba (toC_injective h)
  refine ⟨a, v, hv, ?_⟩
  simpa only [v, toC_sub] using two_points_line Y hY (toC a) (toC b) hCa hCb hCne

 def realLine (Y : AffineVariety d) : AffineSubspace ℝ (Pt d) :=
  if h : ∃ a v : Pt d, v ≠ 0 ∧ Y.points = {z | ∃ t : ℂ, z = toC a+t • toC v}
  then AffineSubspace.mk' h.choose (ℝ ∙ h.choose_spec.choose) else ⊥

 theorem realLine_spec (Y : AffineVariety d) (hY : IsLine Y) (hreal : IsRealFlat Y) :
    IsRealLine (realLine Y) ∧ ∀ x : Pt d, toC x ∈ Y.points ↔ x ∈ realLine Y := by
  have hex := real_parameters Y hY hreal
  unfold realLine
  rw [dif_pos hex]
  let a := hex.choose
  let v := hex.choose_spec.choose
  have hv : v ≠ 0 := hex.choose_spec.choose_spec.1
  have hpts : Y.points = {z | ∃ t : ℂ, z = toC a+t • toC v} := hex.choose_spec.choose_spec.2
  refine ⟨?_, ?_⟩
  · unfold IsRealLine
    rw [AffineSubspace.direction_mk', finrank_span_singleton hv]
  · intro x
    conv_lhs => rw [hpts]
    change (∃ t : ℂ, toC x = toC a+t • toC v) ↔
      x ∈ (AffineSubspace.mk' a (ℝ ∙ v) : Set (Pt d))
    rw [param_set_eq_mk]
    obtain ⟨j, hj⟩ : ∃ j : Fin d, v j ≠ 0 := by
      by_contra! h
      apply hv
      ext j
      exact h j
    exact Bridges.cplx_line_param_iff a v j hj x

 theorem realLine_closure (Y : AffineVariety d) (hY : IsLine Y) (hreal : IsRealFlat Y) :
    (AffineVariety.closure (toC '' (realLine Y : Set (Pt d)))).points = Y.points := by
  have hmem := (realLine_spec Y hY hreal).2
  have hsub : toC '' (realLine Y : Set (Pt d)) ⊆ Y.points := by
    rintro z ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  apply Set.Subset.antisymm (closure_minimal _ Y hsub)
  obtain ⟨F, hFne, hF⟩ := hreal
  rw [hF]
  apply closure_mono
  rintro z ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  apply (hmem x).mp
  rw [hF]
  exact AffineVariety.subset_closure _ ⟨x, hx, rfl⟩

 theorem realLine_injective (Y Z : AffineVariety d) (hY : IsLine Y) (hZ : IsLine Z)
    (hrY : IsRealFlat Y) (hrZ : IsRealFlat Z) (he : realLine Y = realLine Z) : Y = Z := by
  apply (AffineVariety.points_eq_iff Y Z).mp
  rw [← realLine_closure Y hY hrY, ← realLine_closure Z hZ hrZ, he]

 theorem realLine_parameters (Y : AffineVariety d) (hY : IsLine Y) (hreal : IsRealFlat Y) :
    ∃ a v : Pt d, v ≠ 0 ∧ Y.points = {z | ∃ t : ℂ, z = toC a+t • toC v} ∧
      realLine Y = AffineSubspace.mk' a (ℝ ∙ v) := by
  have hex := real_parameters Y hY hreal
  refine ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.1,
    hex.choose_spec.choose_spec.2, ?_⟩
  unfold realLine
  rw [dif_pos hex]

end
end DistinctDistances.TrackD.GeoLines
