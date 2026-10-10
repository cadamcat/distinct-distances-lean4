import DistinctDistances.TrackD.GeoLinesPlanes

/-! Transfer source assignments and record at most one plane per directional member. -/

namespace DistinctDistances.TrackD.GeoLines
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

 def lineCurves (𝒴 : Finset (AffineVariety d)) : Finset (AffineVariety d) := 𝒴.filter IsLine
 def realLines (𝒴 : Finset (AffineVariety d)) : Finset (AffineSubspace ℝ (Pt d)) :=
   (lineCurves 𝒴).image realLine
 def realAssignment (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d))
    (ℓ : AffineSubspace ℝ (Pt d)) : Finset (Pt d) :=
   ((lineCurves 𝒴).filter (fun Y => realLine Y = ℓ)).biUnion S

 theorem realLines_are_lines (𝒴 : Finset (AffineVariety d))
    (hreal : ∀ Y ∈ 𝒴, IsLine Y → IsRealFlat Y) : ∀ ℓ ∈ realLines 𝒴, IsRealLine ℓ := by
   intro ℓ hℓ
   obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hℓ
   obtain ⟨hYm, hYline⟩ := Finset.mem_filter.mp hY
   exact (realLine_spec Y hYline (hreal Y hYm hYline)).1

 theorem realAssignment_subset (P : Finset (Pt d)) (𝒴 : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) (hS : Assignment P 𝒴 S)
    (hreal : ∀ Y ∈ 𝒴, IsLine Y → IsRealFlat Y) :
    ∀ ℓ ∈ realLines 𝒴, realAssignment 𝒴 S ℓ ⊆ P.filter (· ∈ ℓ) := by
   intro ℓ hℓ q hq
   obtain ⟨Y, hY, hqS⟩ := Finset.mem_biUnion.mp hq
   obtain ⟨hYm, he⟩ := Finset.mem_filter.mp hY
   obtain ⟨hYm, hYline⟩ := Finset.mem_filter.mp hYm
   refine Finset.mem_filter.mpr ⟨hS.subset Y hYm hqS, ?_⟩
   rw [← he]
   exact (realLine_spec Y hYline (hreal Y hYm hYline)).2 q |>.mp (hS.mem Y hYm q hqS)

 theorem realAssignment_disjoint (P : Finset (Pt d)) (𝒴 : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) (hS : Assignment P 𝒴 S) :
    (realLines 𝒴 : Set (AffineSubspace ℝ (Pt d))).PairwiseDisjoint (realAssignment 𝒴 S) := by
   intro ℓ hℓ ℓ' hℓ' hne
   apply Finset.disjoint_left.mpr
   intro q hq hq'
   obtain ⟨Y, hY, hqS⟩ := Finset.mem_biUnion.mp hq
   obtain ⟨Z, hZ, hqS'⟩ := Finset.mem_biUnion.mp hq'
   obtain ⟨hYm, heY⟩ := Finset.mem_filter.mp hY
   obtain ⟨hZm, heZ⟩ := Finset.mem_filter.mp hZ
   have hYm := (Finset.mem_filter.mp hYm).1
   have hZm := (Finset.mem_filter.mp hZm).1
   have hYZ : Y ≠ Z := by
     intro he
     apply hne
     exact heY.symm.trans ((congrArg realLine he).trans heZ)
   exact Finset.disjoint_left.mp (hS.disjoint hYm hZm hYZ) hqS hqS'

 theorem assigned_mem_realAssignment (𝒴 : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) (Y : AffineVariety d)
    (hY : Y ∈ 𝒴) (hline : IsLine Y) (q : Pt d) (hq : q ∈ S Y) :
    q ∈ realAssignment 𝒴 S (realLine Y) :=
   Finset.mem_biUnion.mpr ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hY, hline⟩, rfl⟩, hq⟩

 def planeWitness (𝒴 : Finset (AffineVariety d)) (p : Pt d) (γ : ProjectiveVariety d) : Prop :=
   ∃ Y ∈ 𝒴, IsLine Y ∧ p ∉ realLine Y ∧ radialImage (toC p) Y = γ

 def planeOf (𝒴 : Finset (AffineVariety d)) (p : Pt d) (γ : ProjectiveVariety d) :
    AffineSubspace ℝ (Pt d) :=
   if h : planeWitness 𝒴 p γ then sourcePlane p h.choose else ⊥

 def recordedPlanes (𝒴 : Finset (AffineVariety d)) (Cf : Pt d → ProjectiveFamily.Family d)
    (p : Pt d) : Finset (AffineSubspace ℝ (Pt d)) :=
   ((Cf p).filter (planeWitness 𝒴 p)).image (planeOf 𝒴 p)

 theorem planeOf_isPlane (𝒴 : Finset (AffineVariety d))
    (hreal : ∀ Y ∈ 𝒴, IsLine Y → IsRealFlat Y) (p : Pt d) (γ : ProjectiveVariety d)
    (hγ : planeWitness 𝒴 p γ) : IsRealPlane (planeOf 𝒴 p γ) := by
   unfold planeOf
   rw [dif_pos hγ]
   exact sourcePlane_isPlane p hγ.choose hγ.choose_spec.2.1
     (hreal hγ.choose hγ.choose_spec.1 hγ.choose_spec.2.1) hγ.choose_spec.2.2.1

 theorem recordedPlanes_are_planes (𝒴 : Finset (AffineVariety d))
    (hreal : ∀ Y ∈ 𝒴, IsLine Y → IsRealFlat Y)
    (Cf : Pt d → ProjectiveFamily.Family d) (p : Pt d) :
    ∀ H ∈ recordedPlanes 𝒴 Cf p, IsRealPlane H := by
   intro H hH
   obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hH
   exact planeOf_isPlane 𝒴 hreal p γ (Finset.mem_filter.mp hγ).2

 theorem recordedPlanes_card (𝒴 : Finset (AffineVariety d))
    (Cf : Pt d → ProjectiveFamily.Family d) (p : Pt d) :
    (recordedPlanes 𝒴 Cf p).card ≤ (Cf p).card :=
   Finset.card_image_le.trans (Finset.card_filter_le _ _)

 theorem family_card_le_degree (C : ProjectiveFamily.Family d) (hC : IsDirectionalFamily C) :
    (C.card : ℝ) ≤ ProjectiveFamily.degree C := by
   calc
     _ = ∑ γ ∈ C, (1 : ℝ) := by simp
     _ ≤ ∑ γ ∈ C, (γ.degree : ℝ) := by
       apply Finset.sum_le_sum
       intro γ hγ
       have h := γ.affineCone.one_le_degree (hC γ hγ).1.ne_top
       rw [γ.degree_cone] at h
       exact_mod_cast h
     _ = _ := by simp [ProjectiveFamily.degree]

 theorem sourcePlane_recorded (𝒴 : Finset (AffineVariety d))
    (hreal : ∀ Y ∈ 𝒴, IsLine Y → IsRealFlat Y)
    (Cf : Pt d → ProjectiveFamily.Family d) (p : Pt d) (hC : IsDirectionalFamily (Cf p))
    (Y : AffineVariety d) (hYm : Y ∈ 𝒴) (hY : IsLine Y)
    (hp : p ∉ realLine Y) (hproj : ProjectsInto (Cf p) p Y) :
    sourcePlane p Y ∈ recordedPlanes 𝒴 Cf p := by
   let γ := radialImage (toC p) Y
   have hrealY := hreal Y hYm hY
   have hpY : toC p ∉ Y.points := fun h => hp ((realLine_spec Y hY hrealY).2 p |>.mp h)
   have hγmem : γ ∈ Cf p := (radial_member_off p Y (line_curve Y hY) hpY (Cf p) hC hproj).1
   have hγ : planeWitness 𝒴 p γ := ⟨Y, hYm, hY, hp, rfl⟩
   apply Finset.mem_image.mpr
   refine ⟨γ, Finset.mem_filter.mpr ⟨hγmem, hγ⟩, ?_⟩
   unfold planeOf
   rw [dif_pos hγ]
   exact sourcePlane_eq_of_radial_eq p hγ.choose Y hγ.choose_spec.2.1 hY
     (hreal hγ.choose hγ.choose_spec.1 hγ.choose_spec.2.1) hrealY hγ.choose_spec.2.2.2

 theorem selected_pair_cover (P : Finset (Pt d)) (Cf : Pt d → ProjectiveFamily.Family d)
    (hCf : ∀ p ∈ P, IsDirectionalFamily (Cf p))
    (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d))
    (hreal : ∀ Y ∈ 𝒴, IsLine Y → IsRealFlat Y) (pq : Pt d × Pt d)
    (hpq : pq ∈ (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
      ∃ Y ∈ 𝒴, IsLine Y ∧ pq.2 ∈ S Y ∧ ProjectsInto (Cf pq.1) pq.1 Y)) :
    ∃ ℓ ∈ realLines 𝒴, pq.2 ∈ realAssignment 𝒴 S ℓ ∧
      (pq.1 ∈ ℓ ∨ affineSpan ℝ (insert pq.1 (ℓ : Set (Pt d))) ∈ recordedPlanes 𝒴 Cf pq.1) := by
   obtain ⟨hpqP, _, Y, hYm, hY, hq, hproj⟩ := Finset.mem_filter.mp hpq
   have hpP := (Finset.mem_product.mp hpqP).1
   refine ⟨realLine Y, Finset.mem_image.mpr ⟨Y, Finset.mem_filter.mpr ⟨hYm, hY⟩, rfl⟩,
     assigned_mem_realAssignment 𝒴 S Y hYm hY pq.2 hq, ?_⟩
   by_cases hp : pq.1 ∈ realLine Y
   · exact Or.inl hp
   · exact Or.inr (sourcePlane_recorded 𝒴 hreal Cf pq.1 (hCf _ hpP) Y hYm hY hp hproj)

end
end DistinctDistances.TrackD.GeoLines
