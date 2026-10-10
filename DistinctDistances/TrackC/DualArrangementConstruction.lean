import DistinctDistances.TrackC.MappedPolynomialPropagation
import DistinctDistances.TrackC.BeckAnchorPlanes
import DistinctDistances.TrackC.GraphDualCounting
import DistinctDistances.TrackC.DualCloudTransport
import DistinctDistances.TrackC.DualGradient

open Classical

noncomputable section

namespace DistinctDistances.TrackC

private theorem collinear_affine_image (T : E 3 ≃ᵃ[ℝ] E 3)
    (a b c : E 3) (h : Collinear ℝ ({a,b,c} : Set (E 3))) :
    Collinear ℝ ({T a,T b,T c} : Set (E 3)) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨p,v,hv⟩ := h
  refine ⟨T p,T.linear v,?_⟩
  intro x hx
  have hx' : ∃ y ∈ ({a,b,c} : Set (E 3)), T y = x := by
    rcases Set.mem_insert_iff.mp hx with hxa | hx
    · exact ⟨a,by simp,hxa.symm⟩
    · rcases Set.mem_insert_iff.mp hx with hxb | hxc
      · exact ⟨b,by simp,hxb.symm⟩
      · exact ⟨c,by simp,(Set.mem_singleton_iff.mp hxc).symm⟩
  obtain ⟨y,hy,rfl⟩ := hx'
  obtain ⟨r,hr⟩ := hv y hy
  refine ⟨r,?_⟩
  rw [hr,T.map_vadd]
  simp

private theorem dual_partial_degree_le (f : Poly 6) (i : Fin 6) :
    (MvPolynomial.pderiv i f).totalDegree ≤ f.totalDegree := by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro m hm
  have hcoeff : (MvPolynomial.pderiv i f).coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hmem : m + Finsupp.single i 1 ∈ f.support := by
    rw [MvPolynomial.mem_support_iff]
    intro hzero
    simp [hzero] at hcoeff
  have hsum : m.sum (fun _ e => e) ≤ (m + Finsupp.single i 1).sum (fun _ e => e) := by
    simp [Finsupp.sum_add_index']
  exact hsum.trans (MvPolynomial.le_totalDegree hmem)

/-- For large clouds, the two-Beck certificate and graph duality propagate
all first derivatives through points, lines, anchor planes and the motion flat. -/
theorem dual_arrangement_large (η₁ η₂ ρ C : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchors : ∀ (S : Finset (E 3)) (ℓ : ℝ), C ≤ ℓ →
      ℓ/4 ≤ (S.card : ℝ) →
      (∀ l : Line 3, ((pointsOn S l).card : ℝ) < η₁*ℓ) →
      (∀ H : Plane 3, ((pointsOn S H).card : ℝ) < η₂*ℓ) →
      ∃ A : Finset (E 3), A ⊆ S ∧ ρ*ℓ ≤ (A.card : ℝ) ∧
        ∀ x ∈ A, ∃ P : Finset (Plane 3), ρ*ℓ^2 ≤ (P.card : ℝ) ∧
          ∀ H ∈ P, x ∈ H.1 ∧ ∃ y ∈ S, ∃ z ∈ S,
            y ∈ H.1 ∧ z ∈ H.1 ∧ ¬ Collinear ℝ ({x,y,z} : Set (E 3)))
    (g : Motion 3) (S : Finset (E 3)) (G : Flat 6 3) (f : Poly 6) (ℓ : ℝ)
    (hℓ : 0 < ℓ) (hlarge : C ≤ ℓ) (hSlo : ℓ/4 ≤ (S.card : ℝ))
    (hShi : (S.card : ℝ) < 2*ℓ)
    (hline : ∀ l : Line 3, ((pointsOn S l).card : ℝ) < η₁*ℓ)
    (hplane : ∀ H : Plane 3, ((pointsOn S H).card : ℝ) < η₂*ℓ)
    (hmodel : MotionFlatModel g S G) (hdeg : (f.totalDegree : ℝ) < ρ*ℓ/4)
    (hfG : onPolynomial f G)
    (hpair : ∀ x ∈ S, ∀ z ∈ pairFlatSet x (g x), evalR f z = 0) :
    ∀ i : Fin 6, onPolynomial (MvPolynomial.pderiv i f) G := by
  obtain ⟨hnull,T,φ,hφ,hrange,hinter,hnoncol⟩ := hmodel
  have hmodel' : MotionFlatModel g S G :=
    ⟨hnull,T,φ,hφ,hrange,hinter,hnoncol⟩
  let S' := S.image T
  obtain ⟨hcard,hline',hplane'⟩ := affine_cloud_caps T S (η₁*ℓ) (η₂*ℓ) hline hplane
  have hS'lo : ℓ/4 ≤ (S'.card : ℝ) := by simpa [S',hcard] using hSlo
  have hS'hi : (S'.card : ℝ) < 2*ℓ := by simpa [S',hcard] using hShi
  have hproj : ∀ a ∈ S', ∀ b ∈ S', ∀ c ∈ S',
      ¬ Collinear ℝ ({a,b,c} : Set (E 3)) →
        ¬ Collinear ℝ ({WithLp.toLp 2 ![a 0,a 1],WithLp.toLp 2 ![b 0,b 1],
          WithLp.toLp 2 ![c 0,c 1]} : Set (E 2)) := by
    intro a ha b hb c hc htri
    obtain ⟨a₀,ha₀,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b₀,hb₀,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c₀,hc₀,rfl⟩ := Finset.mem_image.mp hc
    apply hnoncol a₀ ha₀ b₀ hb₀ c₀ hc₀
    intro hcol
    exact htri (collinear_affine_image T a₀ b₀ c₀ hcol)
  obtain ⟨A,hAS,hA,hAP⟩ := hanchors S' ℓ hlarge hS'lo hline' hplane'
  have hcert : ∀ x ∈ A, ∃ (Z : Finset (E 3)) (L : Finset (Line 3)),
      ρ*ℓ^2 ≤ (Z.card : ℝ) ∧ (L.card : ℝ) ≤ 2*ℓ ∧
      (∀ l ∈ L, (l.1 : Set (E 3)) ⊆ graphDualPlane x) ∧
      (∀ u ∈ Z, 2 ≤ (L.filter (fun l => u ∈ l.1)).card) ∧
      (∀ l ∈ L, ((Z.filter (fun u => u ∈ l.1)).card : ℝ) ≤ 2*ℓ) ∧
      (∀ u ∈ Z, ∀ i : Fin 6, evalR (MvPolynomial.pderiv i f) (φ u) = 0) := by
    intro x hx
    have hxS := hAS hx
    obtain ⟨P,hPcard,hP⟩ := hAP x hx
    obtain ⟨Z,hZcard,hZ⟩ := graph_dual_spanned_points S' x hxS hproj P hP
    have hZ' : ∀ u ∈ Z, u ∈ graphDualPlane x ∧ ∃ y ∈ S', ∃ z ∈ S',
        ¬ Collinear ℝ ({WithLp.toLp 2 ![x 0,x 1],WithLp.toLp 2 ![y 0,y 1],
          WithLp.toLp 2 ![z 0,z 1]} : Set (E 2)) ∧
          u ∈ graphDualPlane y ∧ u ∈ graphDualPlane z := by
      intro u hu
      obtain ⟨hux,y,hy,z,hz,htri,huy,huz⟩ := hZ u hu
      exact ⟨hux,y,hy,z,hz,hproj x hxS y hy z hz htri,huy,huz⟩
    obtain ⟨L,hLcard,hLplane,hleft,hright⟩ := graph_dual_anchor_lines S' x Z hZ'
    refine ⟨Z,L,?_,?_,hLplane,hleft,?_,?_⟩
    · simpa [hZcard] using hPcard
    · exact (show (L.card : ℝ) ≤ S'.card by exact_mod_cast hLcard).trans hS'hi.le
    · intro l hl
      exact (show ((Z.filter (fun u => u ∈ l.1)).card : ℝ) ≤ S'.card by
        exact_mod_cast hright l hl).trans hS'hi.le
    · intro u hu
      obtain ⟨hux,y,hy,z,hz,htri,huy,huz⟩ := hZ u hu
      obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hxS
      obtain ⟨b,hb,hby⟩ := Finset.mem_image.mp hy
      obtain ⟨c,hc,hcz⟩ := Finset.mem_image.mp hz
      have habc : ¬ Collinear ℝ ({a,b,c} : Set (E 3)) := by
        intro hcol
        apply htri
        simpa [hax,hby,hcz] using collinear_affine_image T a b c hcol
      have huG : φ u ∈ G.1 := by
        change φ u ∈ (G.1 : Set (E 6))
        rw [← hrange]
        exact Set.mem_range_self u
      have hupair (a : E 3) (ha : a ∈ S) (hua : u ∈ graphDualPlane (T a)) :
          φ u ∈ pairFlatSet a (g a) := by
        have hh := Set.mem_image_of_mem φ hua
        rw [← hinter a ha] at hh
        exact hh.1
      apply partials_zero_of_raised_gradient_zero
      exact motion_triple_gradient_zero g S G hmodel' f hfG hpair (φ u) huG
        a b c ha hb hc habc (hupair a ha (by simpa [hax] using hux))
        (hupair b hb (by simpa [hby] using huy)) (hupair c hc (by simpa [hcz] using huz))
  intro i
  have hdi : ((MvPolynomial.pderiv i f).totalDegree : ℝ) < ρ*ℓ/4 :=
    (show ((MvPolynomial.pderiv i f).totalDegree : ℝ) ≤ f.totalDegree by
      exact_mod_cast dual_partial_degree_le f i).trans_lt hdeg
  apply polynomial_on_mapped_anchor_family φ hφ G hrange A (MvPolynomial.pderiv i f)
    ℓ ρ hℓ hρ hρ1 hA _ hdi
  intro x hx
  obtain ⟨Z,L,hZ,hL,hplane,hleft,hright,hzero⟩ := hcert x hx
  exact ⟨Z,L,hZ,hL,hplane,hleft,hright,fun u hu => hzero u hu i⟩

/-- Select absolute constants for the frozen dual-arrangement theorem. Small
clouds have degree zero; the other case uses the full geometric certificate. -/
theorem dual_arrangement_construct (δ γ δp γp : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hδp : 0 < δp) (hγp : 0 < γp)
    (hBeck : ∀ S : Finset (E 3), 2 ≤ S.card → cloudLineCap S (δ*S.card) →
      γ*S.card ≤ (anchors S γ).card)
    (hProj : ∀ D : Finset (PFlat ℝ 3 1), 2 ≤ D.card →
      (∀ V : PFlat ℝ 3 2, ((D.filter (fun u => u.1 ≤ V.1)).card : ℝ) ≤ δp*D.card) →
      let Q : Set (PFlat ℝ 3 2) := {V | 2 ≤ (D.filter (fun u => u.1 ≤ V.1)).card}
      Q.Finite ∧ γp*(D.card : ℝ)^2 ≤ Q.ncard) :
    ∃ η₁ η₂ ε : ℝ, 0 < η₁ ∧ 0 < η₂ ∧ 0 < ε ∧ η₁ ≤ η₂/100 ∧ η₂ < 1 ∧
      ∀ (g : Motion 3) (S : Finset (E 3)) (G : Flat 6 3) (f : Poly 6) (ℓ : ℝ),
        0 < ℓ → ℓ/4 ≤ (S.card : ℝ) → (S.card : ℝ) < 2*ℓ →
        (∀ l : Line 3, ((pointsOn S l).card : ℝ) < η₁*ℓ) →
        (∀ H : Plane 3, ((pointsOn S H).card : ℝ) < η₂*ℓ) →
        MotionFlatModel g S G → (f.totalDegree : ℝ) < ε*ℓ → onPolynomial f G →
        (∀ x ∈ S, ∀ z ∈ pairFlatSet x (g x), evalR f z = 0) →
        ∀ i : Fin 6, onPolynomial (MvPolynomial.pderiv i f) G := by
  obtain ⟨η₁,η₂,ρ,hη₁,hη₂,hρ,hη,hη₂1,hρ1,hanchors⟩ :=
    beck_anchor_planes δ γ δp γp hδ hγ hδp hγp hBeck hProj
  let C := 8+8/γ
  have hC : 0 < C := by dsimp [C]; positivity
  let ε := min (ρ/8) (1/C)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨η₁,η₂,ε,hη₁,hη₂,hε,hη,hη₂1,?_⟩
  intro g S G f ℓ hℓ hSlo hShi hline hplane hmodel hdeg hfG hpair
  by_cases hlarge : C ≤ ℓ
  · have hdegbig : (f.totalDegree : ℝ) < ρ*ℓ/4 := by
      have he : ε ≤ ρ/8 := min_le_left _ _
      have hm := mul_le_mul_of_nonneg_right he hℓ.le
      nlinarith [mul_pos hρ hℓ]
    exact dual_arrangement_large η₁ η₂ ρ C hρ hρ1 hanchors
      g S G f ℓ hℓ hlarge hSlo hShi hline hplane hmodel hdegbig hfG hpair
  · have hsmall : ℓ < C := lt_of_not_ge hlarge
    have hd1 : (f.totalDegree : ℝ) < 1 := by
      have he : ε ≤ 1/C := min_le_right _ _
      have hm := mul_le_mul_of_nonneg_right he hℓ.le
      have hq : ℓ/C < 1 := (div_lt_one hC).mpr hsmall
      have hm' : ε*ℓ ≤ ℓ/C := by simpa [div_eq_mul_inv,mul_comm] using hm
      exact hdeg.trans_le hm' |>.trans hq
    have hd0 : f.totalDegree = 0 := by
      have : f.totalDegree < 1 := by exact_mod_cast hd1
      omega
    have hfC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd0
    intro i z hz
    rw [hfC,MvPolynomial.pderiv_C]
    simp [evalR]

end DistinctDistances.TrackC
