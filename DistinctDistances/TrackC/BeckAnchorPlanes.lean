import DistinctDistances.TrackC.DirectionBeckInputs

open Classical

noncomputable section

namespace DistinctDistances.TrackC

set_option maxHeartbeats 2000000 in
/-- Two specialized Beck applications produce many planes at many anchors,
motions.tex:434–443. The frozen Beck theorems supply the two callbacks. -/
theorem beck_anchor_planes (δ γ δp γp : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hδp : 0 < δp) (hγp : 0 < γp)
    (hBeck : ∀ S : Finset (E 3), 2 ≤ S.card → cloudLineCap S (δ*S.card) →
      γ*S.card ≤ (anchors S γ).card)
    (hProj : ∀ D : Finset (PFlat ℝ 3 1), 2 ≤ D.card →
      (∀ V : PFlat ℝ 3 2, ((D.filter (fun u => u.1 ≤ V.1)).card : ℝ) ≤ δp*D.card) →
      let Q : Set (PFlat ℝ 3 2) := {V | 2 ≤ (D.filter (fun u => u.1 ≤ V.1)).card}
      Q.Finite ∧ γp*(D.card : ℝ)^2 ≤ Q.ncard) :
    ∃ η₁ η₂ ρ : ℝ, 0 < η₁ ∧ 0 < η₂ ∧ 0 < ρ ∧ η₁ ≤ η₂/100 ∧ η₂ < 1 ∧ ρ ≤ 1 ∧
      ∀ (S : Finset (E 3)) (ℓ : ℝ), 8+8/γ ≤ ℓ →
        ℓ/4 ≤ (S.card : ℝ) →
        (∀ l : Line 3, ((pointsOn S l).card : ℝ) < η₁*ℓ) →
        (∀ H : Plane 3, ((pointsOn S H).card : ℝ) < η₂*ℓ) →
        ∃ A : Finset (E 3), A ⊆ S ∧ ρ*ℓ ≤ (A.card : ℝ) ∧
          ∀ x ∈ A, ∃ P : Finset (Plane 3), ρ*ℓ^2 ≤ (P.card : ℝ) ∧
            ∀ H ∈ P, x ∈ H.1 ∧ ∃ y ∈ S, ∃ z ∈ S,
              y ∈ H.1 ∧ z ∈ H.1 ∧ ¬ Collinear ℝ ({x,y,z} : Set (E 3)) := by
  let η₂ := min (1/2 : ℝ) (δp*γ/16)
  let η₁ := min (δ/8) (η₂/100)
  let ρ := min (1 : ℝ) (min (γ/4) (γp*γ^2/16))
  have hη₂ : 0 < η₂ := by dsimp [η₂]; positivity
  have hη₁ : 0 < η₁ := by dsimp [η₁]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρa : ρ ≤ γ/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρp : ρ ≤ γp*γ^2/16 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η₁,η₂,ρ,hη₁,hη₂,hρ,min_le_right _ _,?_,hρ1,?_⟩
  · have h := min_le_left (1/2 : ℝ) (δp*γ/16)
    dsimp [η₂]
    linarith
  intro S ℓ hlarge hS hline hplane
  have hℓ8 : 8 ≤ ℓ := by
    have hq : 0 ≤ 8/γ := by positivity
    linarith
  have hℓ : 0 < ℓ := by linarith
  have hS2 : 2 ≤ S.card := by exact_mod_cast (show (2 : ℝ) ≤ S.card by linarith)
  have hcap : cloudLineCap S (δ*S.card) := by
    intro l
    apply (hline l).le.trans
    calc
      η₁*ℓ ≤ (δ/8)*ℓ := mul_le_mul_of_nonneg_right (min_le_left _ _) hℓ.le
      _ ≤ δ*(ℓ/4) := by nlinarith [mul_pos hδ hℓ]
      _ ≤ δ*(S.card : ℝ) := mul_le_mul_of_nonneg_left hS hδ.le
  let A := anchors S γ
  have hA : γ*(S.card : ℝ) ≤ A.card := hBeck S hS2 hcap
  have hAρ : ρ*ℓ ≤ (A.card : ℝ) := by
    calc
      ρ*ℓ ≤ (γ/4)*ℓ := mul_le_mul_of_nonneg_right hρa hℓ.le
      _ = γ*(ℓ/4) := by ring
      _ ≤ γ*(S.card : ℝ) := mul_le_mul_of_nonneg_left hS hγ.le
      _ ≤ A.card := hA
  refine ⟨A,Finset.filter_subset _ _,hAρ,?_⟩
  intro x hx
  obtain ⟨hxS,hxD⟩ := Finset.mem_filter.mp hx
  obtain ⟨D,hDcard,hD⟩ := anchor_direction_cloud S x hxS
  have hDγ : γ*(S.card : ℝ) ≤ D.card := by rw [hDcard];exact hxD
  have hDlower : γ*(ℓ/4) ≤ (D.card : ℝ) :=
    (mul_le_mul_of_nonneg_left hS hγ.le).trans hDγ
  have hγℓ : 8 ≤ γ*ℓ := by
    have hl : 8/γ ≤ ℓ := by linarith
    have h := (div_le_iff₀ hγ).mp hl
    simpa [mul_comm] using h
  have hD2 : 2 ≤ D.card := by exact_mod_cast (show (2 : ℝ) ≤ D.card by linarith)
  have hDcap : ∀ V : PFlat ℝ 3 2,
      ((D.filter (fun u => u.1 ≤ V.1)).card : ℝ) ≤ δp*D.card := by
    intro V
    apply (anchor_direction_plane_cap S x D hD (η₂*ℓ) hplane V).le.trans
    calc
      η₂*ℓ ≤ (δp*γ/16)*ℓ := mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ.le
      _ ≤ δp*(γ*(ℓ/4)) := by nlinarith [mul_pos hδp (mul_pos hγ hℓ)]
      _ ≤ δp*(D.card : ℝ) := mul_le_mul_of_nonneg_left hDlower hδp.le
  let Q : Set (PFlat ℝ 3 2) := {V | 2 ≤ (D.filter (fun u => u.1 ≤ V.1)).card}
  obtain ⟨hQ,hQlower⟩ := hProj D hD2 hDcap
  let L := hQ.toFinset
  have hLcard : L.card = Q.ncard := (Set.ncard_eq_toFinset_card Q hQ).symm
  obtain ⟨P,hPcard,hP⟩ := projective_spanned_physical_planes S x D hD L
    (by intro V hV;simpa [L] using hV)
  have hscale : ρ*ℓ^2 ≤ γp*(D.card : ℝ)^2 := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ γ*(ℓ/4)) hDlower 2
    calc
      ρ*ℓ^2 ≤ (γp*γ^2/16)*ℓ^2 := mul_le_mul_of_nonneg_right hρp (sq_nonneg ℓ)
      _ = γp*(γ*(ℓ/4))^2 := by ring
      _ ≤ γp*(D.card : ℝ)^2 := mul_le_mul_of_nonneg_left hpow hγp.le
  refine ⟨P,?_,hP⟩
  rw [hPcard,hLcard]
  exact hscale.trans hQlower

end DistinctDistances.TrackC
