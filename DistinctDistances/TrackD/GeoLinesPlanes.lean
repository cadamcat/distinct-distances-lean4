import DistinctDistances.TrackD.GeoLinesRadial

/-! Real planes determined by source lines and equal radial images. -/

namespace DistinctDistances.TrackD.GeoLines
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

 def rePoint (z : Point d) : Pt d := WithLp.toLp 2 (fun i => (z i).re)
 def imPoint (z : Point d) : Pt d := WithLp.toLp 2 (fun i => (z i).im)

 @[simp] theorem rePoint_toC (x : Pt d) : rePoint (toC x) = x := by ext i; simp [rePoint, toC]
 @[simp] theorem imPoint_toC (x : Pt d) : imPoint (toC x) = 0 := by ext i; simp [imPoint, toC]
 @[simp] theorem rePoint_zero : rePoint (0 : Point d) = 0 := by ext i; simp [rePoint]
 @[simp] theorem imPoint_zero : imPoint (0 : Point d) = 0 := by ext i; simp [imPoint]
 @[simp] theorem rePoint_add (x y : Point d) : rePoint (x+y) = rePoint x + rePoint y := by
  ext i; simp [rePoint]
 @[simp] theorem imPoint_add (x y : Point d) : imPoint (x+y) = imPoint x + imPoint y := by
  ext i; simp [imPoint]

 theorem rePoint_smul (c : ℂ) (z : Point d) :
    rePoint (c • z) = c.re • rePoint z - c.im • imPoint z := by
  ext i; simp [rePoint, imPoint, Complex.mul_re, smul_eq_mul]

 theorem imPoint_smul (c : ℂ) (z : Point d) :
    imPoint (c • z) = c.re • imPoint z + c.im • rePoint z := by
  ext i; simp [rePoint, imPoint, Complex.mul_im, smul_eq_mul]

 def complexDir (V : Submodule ℝ (Pt d)) : Submodule ℂ (Point d) :=
  Submodule.span ℂ (toC '' (V : Set (Pt d)))

 theorem complexDir_parts (V : Submodule ℝ (Pt d)) (z : Point d) (hz : z ∈ complexDir V) :
    rePoint z ∈ V ∧ imPoint z ∈ V := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    simpa using And.intro hx V.zero_mem
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [rePoint_add, imPoint_add] using
      And.intro (V.add_mem hx.1 hy.1) (V.add_mem hx.2 hy.2)
  | smul c z _ hz =>
    rw [rePoint_smul, imPoint_smul]
    exact ⟨V.sub_mem (V.smul_mem c.re hz.1) (V.smul_mem c.im hz.2),
      V.add_mem (V.smul_mem c.re hz.2) (V.smul_mem c.im hz.1)⟩

 theorem toC_mem_complexDir (V : Submodule ℝ (Pt d)) (x : Pt d) :
    toC x ∈ complexDir V ↔ x ∈ V := by
  constructor
  · intro h; simpa only [rePoint_toC] using (complexDir_parts V (toC x) h).1
  · intro h; exact Submodule.subset_span ⟨x, h, rfl⟩

 def sourcePlane (p : Pt d) (Y : AffineVariety d) : AffineSubspace ℝ (Pt d) :=
  affineSpan ℝ (insert p (realLine Y : Set (Pt d)))

 theorem sourcePlane_center (p : Pt d) (Y : AffineVariety d) : p ∈ sourcePlane p Y :=
  subset_affineSpan ℝ _ (Set.mem_insert p _)

 theorem realLine_le_sourcePlane (p : Pt d) (Y : AffineVariety d) : realLine Y ≤ sourcePlane p Y :=
  fun x hx => subset_affineSpan ℝ _ (Set.mem_insert_of_mem p hx)

 theorem sourcePlane_isPlane (p : Pt d) (Y : AffineVariety d) (hY : IsLine Y)
    (hreal : IsRealFlat Y) (hp : p ∉ realLine Y) : IsRealPlane (sourcePlane p Y) := by
  obtain ⟨a, v, hv, hpts, hline⟩ := realLine_parameters Y hY hreal
  have ha : a ∈ realLine Y := by rw [hline]; exact AffineSubspace.self_mem_mk' _ _
  have hnot : p-a ∉ (realLine Y).direction := by
    intro h
    have hm := AffineSubspace.vadd_mem_of_mem_direction h ha
    apply hp
    simpa only [vadd_eq_add, sub_add_cancel] using hm
  unfold IsRealPlane sourcePlane
  rw [AffineSubspace.direction_affineSpan_insert ha, vsub_eq_sub, sup_comm,
    Submodule.finrank_sup_span_singleton hnot, (realLine_spec Y hY hreal).1]

 theorem source_in_complex_plane (p : Pt d) (Y : AffineVariety d)
    (hY : IsLine Y) (hreal : IsRealFlat Y)
    (H : AffineSubspace ℝ (Pt d)) (hp : p ∈ H) (hline : realLine Y ≤ H) :
    Y.points ⊆ (AffineSubspace.mk' (toC p) (complexDir H.direction) : Set (Point d)) := by
  obtain ⟨a, v, hv, hpts, hL⟩ := realLine_parameters Y hY hreal
  have haL : a ∈ realLine Y := by rw [hL]; exact AffineSubspace.self_mem_mk' _ _
  have haH := hline haL
  have hvL : v ∈ (realLine Y).direction := by
    rw [hL, AffineSubspace.direction_mk']
    exact Submodule.mem_span_singleton_self v
  have hvH : v ∈ H.direction := AffineSubspace.direction_le hline hvL
  have hap : a-p ∈ H.direction := by
    simpa only [vsub_eq_sub] using AffineSubspace.vsub_mem_direction haH hp
  have hCv : toC v ∈ complexDir H.direction := (toC_mem_complexDir _ _).mpr hvH
  have hCap : toC a-toC p ∈ complexDir H.direction := by
    rw [← toC_sub]; exact (toC_mem_complexDir _ _).mpr hap
  intro z hz
  rw [hpts] at hz
  obtain ⟨t, rfl⟩ := hz
  apply AffineSubspace.mem_mk'.mpr
  rw [vsub_eq_sub]
  have h := (complexDir H.direction).add_mem hCap ((complexDir H.direction).smul_mem t hCv)
  convert h using 1 <;> abel

 theorem sourcePlane_le_of_radial_eq (p : Pt d) (Y Z : AffineVariety d)
    (hY : IsLine Y) (hZ : IsLine Z) (hrY : IsRealFlat Y) (hrZ : IsRealFlat Z)
    (he : radialImage (toC p) Y = radialImage (toC p) Z) : sourcePlane p Z ≤ sourcePlane p Y := by
  let H := sourcePlane p Y
  have hpH : p ∈ H := sourcePlane_center p Y
  have hYH := source_in_complex_plane p Y hY hrY H hpH (realLine_le_sourcePlane p Y)
  have hreps := radial_reps_in_flat (toC p) Y (complexDir H.direction) hYH
  rw [he] at hreps
  have hZH := GeoRadial.radial_subset_flat (toC p) Z (complexDir H.direction) hreps
  apply affineSpan_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hpH
  · have hxZ := (realLine_spec Z hZ hrZ).2 x |>.mpr hx
    have hxC := AffineSubspace.mem_mk'.mp (hZH hxZ)
    have hxdir : x-p ∈ H.direction := by
      apply (toC_mem_complexDir _ _).mp
      simpa only [vsub_eq_sub, toC_sub] using hxC
    have hm := AffineSubspace.vadd_mem_of_mem_direction hxdir hpH
    have hxH : x ∈ H := by simpa only [vadd_eq_add, sub_add_cancel] using hm
    exact hxH

 theorem sourcePlane_eq_of_radial_eq (p : Pt d) (Y Z : AffineVariety d)
    (hY : IsLine Y) (hZ : IsLine Z) (hrY : IsRealFlat Y) (hrZ : IsRealFlat Z)
    (he : radialImage (toC p) Y = radialImage (toC p) Z) : sourcePlane p Y = sourcePlane p Z :=
  le_antisymm (sourcePlane_le_of_radial_eq p Z Y hZ hY hrZ hrY he.symm)
    (sourcePlane_le_of_radial_eq p Y Z hY hZ hrY hrZ he)

end
end DistinctDistances.TrackD.GeoLines
