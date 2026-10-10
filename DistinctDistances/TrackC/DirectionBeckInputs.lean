import DistinctDistances.TrackC.MotionGeometry

open Classical

namespace DistinctDistances.TrackC

private noncomputable def anchorLine (x y : E 3) (hxy : x ≠ y) : Line 3 := by
  refine ⟨affineSpan ℝ ({x, y} : Set (E 3)), ?_, ?_⟩
  · exact ⟨x, left_mem_affineSpan_pair ℝ x y⟩
  · rw [direction_affineSpan, vectorSpan_pair_rev]
    apply finrank_span_singleton
    intro hv
    exact hxy.symm (vsub_eq_zero_iff_eq.mp hv)

private theorem anchorLine_left (x y : E 3) (hxy : x ≠ y) :
    x ∈ (anchorLine x y hxy).1 := by
  change x ∈ affineSpan ℝ ({x, y} : Set (E 3))
  exact left_mem_affineSpan_pair ℝ x y

private theorem anchorLine_right (x y : E 3) (hxy : x ≠ y) :
    y ∈ (anchorLine x y hxy).1 := by
  change y ∈ affineSpan ℝ ({x, y} : Set (E 3))
  exact right_mem_affineSpan_pair ℝ x y

private theorem lines_eq_of_two_mem {l l' : Line 3} {x y : E 3}
    (hx : x ∈ l.1) (hx' : x ∈ l'.1) (hy : y ∈ l.1) (hy' : y ∈ l'.1)
    (hxy : x ≠ y) : l = l' := by
  have hv : y -ᵥ x ≠ 0 := by
    intro hv
    exact hxy.symm (vsub_eq_zero_iff_eq.mp hv)
  have hs : ℝ ∙ (y -ᵥ x) ≤ l.1.direction := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact AffineSubspace.vsub_mem_direction hy hx
  have hs' : ℝ ∙ (y -ᵥ x) ≤ l'.1.direction := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact AffineSubspace.vsub_mem_direction hy' hx'
  have hd : ℝ ∙ (y -ᵥ x) = l.1.direction := by
    apply Submodule.eq_of_le_of_finrank_eq hs
    rw [finrank_span_singleton hv, l.2.2]
  have hd' : ℝ ∙ (y -ᵥ x) = l'.1.direction := by
    apply Submodule.eq_of_le_of_finrank_eq hs'
    rw [finrank_span_singleton hv, l'.2.2]
  apply Subtype.ext
  exact AffineSubspace.ext_of_direction_eq (hd.symm.trans hd') ⟨x, hx, hx'⟩

private noncomputable def lineDirectionProjective (l : Line 3) : PFlat ℝ 3 1 :=
  ⟨l.1.direction.map (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap, by
    calc
      Module.finrank ℝ
          (l.1.direction.map (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap) =
        Module.finrank ℝ l.1.direction := LinearEquiv.finrank_map_eq _ _
      _ = 1 := l.2.2⟩

private theorem lineDirectionProjective_span (l : Line 3) {x y : E 3}
    (hx : x ∈ l.1) (hy : y ∈ l.1) (hyx : y ≠ x) :
    (lineDirectionProjective l).1 =
      Submodule.span ℝ {WithLp.ofLp (y-x)} := by
  have hvec : y - x ≠ 0 := sub_ne_zero.mpr hyx
  have hmem : y - x ∈ l.1.direction := by
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hy hx
  have hspan : l.1.direction = ℝ ∙ (y-x) :=
    eq_span_singleton_of_mem_of_finrank_eq_one l.2.2 hmem hvec
  change l.1.direction.map (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap = _
  rw [hspan, Submodule.map_span]
  simp

private theorem exists_other_point {X : Finset (E 3)} {x : E 3}
    (hcard : 2 ≤ X.card) : ∃ y ∈ X, y ≠ x := by
  obtain ⟨y, z, hy, hz, hyz⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < X.card)
  by_cases hyx : y = x
  · subst y
    exact ⟨z, hz, fun hzx => hyz hzx.symm⟩
  · exact ⟨y, hy, hyx⟩

/-- Outgoing projective directions are in bijection with the spanned physical
lines through an anchor, motions.tex:437–439. -/
theorem anchor_direction_cloud (S : Finset (E 3)) (x : E 3) (hx : x ∈ S) :
    ∃ D : Finset (PFlat ℝ 3 1),
      D.card = {l : Line 3 | l ∈ spannedLines S ∧ x ∈ l.1}.ncard ∧
      ∀ u ∈ D, ∃ y ∈ S, y ≠ x ∧
        u.1 = Submodule.span ℝ {WithLp.ofLp (y-x)} := by
  classical
  let A : Set (Line 3) := {l | l ∈ spannedLines S ∧ x ∈ l.1}
  let F : Finset (Line 3) := (S.erase x).attach.image fun q =>
    anchorLine x q.1 (Finset.mem_erase.mp q.2).1.symm
  have hcover : A ⊆ (F : Set (Line 3)) := by
    intro l hl
    have hreal : (2 : ℝ) ≤ ((pointsOn S l).card : ℝ) := by
      simpa [spannedLines, richLines] using hl.1
    have hcard : 2 ≤ (pointsOn S l).card := by exact_mod_cast hreal
    obtain ⟨y, hyOn, hyx⟩ := exists_other_point hcard
    rcases Finset.mem_filter.mp hyOn with ⟨hyS, hyl⟩
    let q : {q : E 3 // q ∈ S.erase x} :=
      ⟨y, Finset.mem_erase.mpr ⟨hyx, hyS⟩⟩
    have hline : anchorLine x y hyx.symm = l :=
      lines_eq_of_two_mem (anchorLine_left x y hyx.symm) hl.2
        (anchorLine_right x y hyx.symm) hyl hyx.symm
    change l ∈ (S.erase x).attach.image
      (fun q => anchorLine x q.1 (Finset.mem_erase.mp q.2).1.symm)
    exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ q, hline⟩
  have hAfinite : A.Finite := (Finset.finite_toSet F).subset hcover
  let AFin := hAfinite.toFinset
  have hdirInj : Set.InjOn lineDirectionProjective (AFin : Set (Line 3)) := by
    intro l hl l' hl' heq
    have hmaps :
        l.1.direction.map (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap =
          l'.1.direction.map (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap :=
      congrArg Subtype.val heq
    have hdir := Submodule.map_injective_of_injective
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective hmaps
    have hlA := hAfinite.mem_toFinset.mp hl
    have hl'A := hAfinite.mem_toFinset.mp hl'
    apply Subtype.ext
    exact AffineSubspace.ext_of_direction_eq hdir ⟨x, hlA.2, hl'A.2⟩
  let D := AFin.image lineDirectionProjective
  refine ⟨D, ?_, ?_⟩
  · calc
      D.card = AFin.card := Finset.card_image_of_injOn hdirInj
      _ = A.ncard := (Set.ncard_eq_toFinset_card A hAfinite).symm
  · intro u hu
    rcases Finset.mem_image.mp hu with ⟨l, hl, rfl⟩
    have hlA := hAfinite.mem_toFinset.mp hl
    have hreal : (2 : ℝ) ≤ ((pointsOn S l).card : ℝ) := by
      simpa [spannedLines, richLines] using hlA.1
    have hcard : 2 ≤ (pointsOn S l).card := by exact_mod_cast hreal
    obtain ⟨y, hyOn, hyx⟩ := exists_other_point hcard
    rcases Finset.mem_filter.mp hyOn with ⟨hyS, hyl⟩
    exact ⟨y, hyS, hyx, lineDirectionProjective_span l hlA.2 hyl hyx⟩

/-- A projective line of directions lies in one physical plane through its
anchor, motions.tex:439–441. -/
theorem anchor_direction_plane_cap (S : Finset (E 3)) (x : E 3)
    (D : Finset (PFlat ℝ 3 1))
    (hD : ∀ u ∈ D, ∃ y ∈ S, y ≠ x ∧ u.1 = Submodule.span ℝ {WithLp.ofLp (y-x)})
    (B : ℝ) (hcap : ∀ H : Plane 3, ((pointsOn S H).card : ℝ) < B) :
    ∀ V : PFlat ℝ 3 2, ((D.filter (fun u => u.1 ≤ V.1)).card : ℝ) < B := by
  classical
  intro V
  let e : E 3 ≃ₗ[ℝ] (Fin 3 → ℝ) := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  let W : Submodule ℝ (E 3) := V.1.map e.symm.toLinearMap
  have hWrank : Module.finrank ℝ W = 2 := by
    exact (LinearEquiv.finrank_map_eq e.symm V.1).trans V.2
  let H : Plane 3 := ⟨AffineSubspace.mk' x W,
    ⟨x, AffineSubspace.self_mem_mk' x W⟩, by
      rw [AffineSubspace.direction_mk']
      exact hWrank⟩
  let F := D.filter (fun u => u.1 ≤ V.1)
  let partner : {u : PFlat ℝ 3 1 // u ∈ F} → E 3 := fun u =>
    Classical.choose (hD u.1 (Finset.mem_filter.mp u.2).1)
  have hpartner (u : {u : PFlat ℝ 3 1 // u ∈ F}) :
      partner u ∈ S ∧ partner u ≠ x ∧
        u.1.1 = Submodule.span ℝ {WithLp.ofLp (partner u-x)} :=
    Classical.choose_spec (hD u.1 (Finset.mem_filter.mp u.2).1)
  have hpartner_injective : Function.Injective partner := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    calc
      u.1.1 = Submodule.span ℝ {WithLp.ofLp (partner u-x)} := (hpartner u).2.2
      _ = Submodule.span ℝ {WithLp.ofLp (partner v-x)} := by rw [huv]
      _ = v.1.1 := (hpartner v).2.2.symm
  have hpartner_mem (u : {u : PFlat ℝ 3 1 // u ∈ F}) :
      partner u ∈ pointsOn S H := by
    have huD := Finset.mem_filter.mp u.2
    rcases hpartner u with ⟨hyS, hyx, hyspan⟩
    have hvec : WithLp.ofLp (partner u-x) ∈ V.1 := by
      apply huD.2
      rw [hyspan]
      exact Submodule.subset_span (by simp)
    have hWmem : partner u-x ∈ W := by
      change partner u-x ∈ V.1.map e.symm.toLinearMap
      exact Submodule.mem_map.mpr ⟨WithLp.ofLp (partner u-x), hvec, by simp [e]⟩
    have hHmem : partner u ∈ H.1 := by
      change partner u ∈ AffineSubspace.mk' x W
      rw [AffineSubspace.mem_mk']
      simpa [vsub_eq_sub] using hWmem
    exact Finset.mem_filter.mpr ⟨hyS, hHmem⟩
  let Image := F.attach.image partner
  have hImage : Image ⊆ pointsOn S H := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
    exact hpartner_mem u
  have hcardNat : F.card ≤ (pointsOn S H).card := by
    calc
      F.card = F.attach.card := by rw [Finset.card_attach]
      _ = Image.card := (Finset.card_image_of_injective _ hpartner_injective).symm
      _ ≤ (pointsOn S H).card := Finset.card_le_card hImage
  have hcardReal : (F.card : ℝ) ≤ ((pointsOn S H).card : ℝ) := by
    exact_mod_cast hcardNat
  have hbound : (F.card : ℝ) < B := lt_of_le_of_lt hcardReal (hcap H)
  simpa [F] using hbound

private def euclideanCoordEquiv : E 3 ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)

private def projectivePlaneDirection (V : PFlat ℝ 3 2) : Submodule ℝ (E 3) :=
  V.1.map euclideanCoordEquiv.symm.toLinearMap

private noncomputable def projectivePlaneThrough (x : E 3) (V : PFlat ℝ 3 2) :
    Plane 3 := by
  let W := projectivePlaneDirection V
  have hWrank : Module.finrank ℝ W = 2 := by
    exact (LinearEquiv.finrank_map_eq euclideanCoordEquiv.symm V.1).trans V.2
  refine ⟨AffineSubspace.mk' x W, ⟨x, AffineSubspace.self_mem_mk' x W⟩, ?_⟩
  rw [AffineSubspace.direction_mk']
  exact hWrank

private theorem projectivePlaneThrough_anchor (x : E 3) (V : PFlat ℝ 3 2) :
    x ∈ (projectivePlaneThrough x V).1 := by
  change x ∈ AffineSubspace.mk' x (projectivePlaneDirection V)
  exact AffineSubspace.self_mem_mk' x _

private theorem projectivePlaneThrough_mem (x : E 3) (V : PFlat ℝ 3 2)
    {y : E 3} (hyV : WithLp.ofLp (y-x) ∈ V.1) :
    y ∈ (projectivePlaneThrough x V).1 := by
  have hW : y-x ∈ projectivePlaneDirection V := by
    exact Submodule.mem_map.mpr ⟨WithLp.ofLp (y-x), hyV, by simp [euclideanCoordEquiv]⟩
  change y ∈ AffineSubspace.mk' x (projectivePlaneDirection V)
  rw [AffineSubspace.mem_mk']
  simpa [vsub_eq_sub] using hW

private theorem projectivePlaneThrough_injective (x : E 3) :
    Function.Injective (projectivePlaneThrough x) := by
  intro V V' h
  have hdir :
      (projectivePlaneThrough x V).1.direction =
        (projectivePlaneThrough x V').1.direction := congrArg (fun H : Plane 3 => H.1.direction) h
  have hmap : projectivePlaneDirection V = projectivePlaneDirection V' := by
    simpa [projectivePlaneThrough, projectivePlaneDirection, AffineSubspace.direction_mk'] using hdir
  have hsub := Submodule.map_injective_of_injective euclideanCoordEquiv.symm.injective hmap
  exact Subtype.ext hsub

private theorem noncollinear_of_distinct_projective_directions {x y z : E 3}
    (U V : PFlat ℝ 3 1)
    (hU : U.1 = Submodule.span ℝ {WithLp.ofLp (y-x)})
    (hV : V.1 = Submodule.span ℝ {WithLp.ofLp (z-x)}) (hUV : U ≠ V) :
    ¬ Collinear ℝ ({x,y,z} : Set (E 3)) := by
  intro hcol
  let Q := vectorSpan ℝ ({x,y,z} : Set (E 3))
  have hQrank : Module.finrank ℝ Q ≤ 1 := by
    exact hcol.finrank_le_one
  have hyQ : y-x ∈ Q := by
    simpa [Q, vsub_eq_sub] using
      (vsub_mem_vectorSpan ℝ (show y ∈ ({x,y,z} : Set (E 3)) by simp)
        (show x ∈ ({x,y,z} : Set (E 3)) by simp))
  have hzQ : z-x ∈ Q := by
    simpa [Q, vsub_eq_sub] using
      (vsub_mem_vectorSpan ℝ (show z ∈ ({x,y,z} : Set (E 3)) by simp)
        (show x ∈ ({x,y,z} : Set (E 3)) by simp))
  let Qc := Q.map euclideanCoordEquiv.toLinearMap
  have hyQc : WithLp.ofLp (y-x) ∈ Qc :=
    Submodule.mem_map.mpr ⟨y-x, hyQ, rfl⟩
  have hzQc : WithLp.ofLp (z-x) ∈ Qc :=
    Submodule.mem_map.mpr ⟨z-x, hzQ, rfl⟩
  have hUle : U.1 ≤ Qc := by
    rw [hU]
    rw [Submodule.span_singleton_le_iff_mem]
    exact hyQc
  have hVle : V.1 ≤ Qc := by
    rw [hV]
    rw [Submodule.span_singleton_le_iff_mem]
    exact hzQc
  have hQcrank : Module.finrank ℝ Qc ≤ 1 := by
    calc
      Module.finrank ℝ Qc = Module.finrank ℝ Q :=
        LinearEquiv.finrank_map_eq euclideanCoordEquiv Q
      _ ≤ 1 := hQrank
  have hUeq : U.1 = Qc := by
    apply Submodule.eq_of_le_of_finrank_eq hUle
    have hmono := Submodule.finrank_mono hUle
    have hUr : Module.finrank ℝ U.1 = 1 := U.2
    omega
  have hVeq : V.1 = Qc := by
    apply Submodule.eq_of_le_of_finrank_eq hVle
    have hmono := Submodule.finrank_mono hVle
    have hVr : Module.finrank ℝ V.1 = 1 := V.2
    omega
  apply hUV
  exact Subtype.ext (hUeq.trans hVeq.symm)

/-- Distinct spanned projective lines produce distinct spanned physical planes,
motions.tex:441–443. -/
theorem projective_spanned_physical_planes (S : Finset (E 3)) (x : E 3)
    (D : Finset (PFlat ℝ 3 1))
    (hD : ∀ u ∈ D, ∃ y ∈ S, y ≠ x ∧ u.1 = Submodule.span ℝ {WithLp.ofLp (y-x)})
    (L : Finset (PFlat ℝ 3 2))
    (hL : ∀ V ∈ L, 2 ≤ (D.filter (fun u => u.1 ≤ V.1)).card) :
    ∃ P : Finset (Plane 3), P.card = L.card ∧
      ∀ H ∈ P, x ∈ H.1 ∧ ∃ y ∈ S, ∃ z ∈ S,
        y ∈ H.1 ∧ z ∈ H.1 ∧ ¬ Collinear ℝ ({x,y,z} : Set (E 3)) := by
  classical
  let planeOf := projectivePlaneThrough x
  let P := L.attach.image (fun q => planeOf q.1)
  have hplaneOfInj : Function.Injective planeOf := projectivePlaneThrough_injective x
  have himageInj : Function.Injective (fun q : {V : PFlat ℝ 3 2 // V ∈ L} => planeOf q.1) := by
    intro q q' h
    apply Subtype.ext
    exact hplaneOfInj h
  have hPcard : P.card = L.card := by
    calc
      P.card = L.attach.card := Finset.card_image_of_injective _ himageInj
      _ = L.card := by rw [Finset.card_attach]
  refine ⟨P, hPcard, ?_⟩
  intro H hH
  rcases Finset.mem_image.mp hH with ⟨V, _, hVH⟩
  have hVL : V.1 ∈ L := V.2
  subst H
  let F := D.filter (fun u => u.1 ≤ V.1.1)
  have hFcard : 2 ≤ F.card := by
    simpa [F] using hL V.1 hVL
  obtain ⟨u, v, hu, hv, huv⟩ :=
    Finset.one_lt_card_iff.mp (by omega : 1 < F.card)
  rcases hD u (Finset.mem_filter.mp hu).1 with ⟨y, hyS, hyx, hUy⟩
  rcases hD v (Finset.mem_filter.mp hv).1 with ⟨z, hzS, hzx, hVz⟩
  have hyV : WithLp.ofLp (y-x) ∈ V.1.1 := by
    apply (Finset.mem_filter.mp hu).2
    rw [hUy]
    exact Submodule.subset_span (by simp)
  have hzV : WithLp.ofLp (z-x) ∈ V.1.1 := by
    apply (Finset.mem_filter.mp hv).2
    rw [hVz]
    exact Submodule.subset_span (by simp)
  have hnoncol := noncollinear_of_distinct_projective_directions u v hUy hVz huv
  refine ⟨projectivePlaneThrough_anchor x V.1, ?_⟩
  exact ⟨y, hyS, z, hzS, projectivePlaneThrough_mem x V.1 hyV,
    projectivePlaneThrough_mem x V.1 hzV, hnoncol⟩

end DistinctDistances.TrackC
