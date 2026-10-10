import DistinctDistances.TrackE.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import DistinctDistances.TrackC.WeakPlanar

/-!
# `red:flat-caps`: occupancy of proper flats (`reduction.tex:30-65`)

Uniform single-configuration forms. "Sufficiently large terms of the sequence" becomes
"`N₀ ≤ |P|`" with `N₀` depending only on `d` and the constants of IH(d) and of the planar input.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

private theorem card_le_two_mul_image_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β)
    (hf : ∀ y ∈ S.image f, (S.filter fun x => f x = y).card ≤ 2) :
    S.card ≤ 2 * (S.image f).card := by
  classical
  let T := S.image f
  have hsum : (∑ y ∈ T, (S.filter fun x => f x = y).card) = S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  calc
    S.card = ∑ y ∈ T, (S.filter fun x => f x = y).card := hsum.symm
    _ ≤ ∑ y ∈ T, (2 : ℕ) := Finset.sum_le_sum fun y hy => hf y hy
    _ = 2 * T.card := by simp [T, mul_comm]

private theorem affineSpan_pair_eq_of_mem_of_mem_of_finrank_le_one
    (L : AffineSubspace ℝ (RPoint d))
    (hL : Module.finrank ℝ L.direction ≤ 1) {x y : RPoint d}
    (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y) :
    affineSpan ℝ ({x, y} : Set (RPoint d)) = L := by
  let K := affineSpan ℝ ({x, y} : Set (RPoint d))
  have hKL : K ≤ L := affineSpan_pair_le_of_mem_of_mem hx hy
  have hv : (x -ᵥ y : RPoint d) ≠ 0 := by
    intro h
    exact hxy (vsub_eq_zero_iff_eq.mp h)
  have hKdim : Module.finrank ℝ K.direction = 1 := by
    dsimp [K]
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton hv
  have hdir : K.direction ≤ L.direction := AffineSubspace.direction_le hKL
  have hLdim : Module.finrank ℝ L.direction = 1 := by
    apply le_antisymm hL
    calc
      1 = Module.finrank ℝ K.direction := hKdim.symm
      _ ≤ Module.finrank ℝ L.direction := Submodule.finrank_mono hdir
  have hdirEq : K.direction = L.direction :=
    Submodule.eq_of_le_of_finrank_eq hdir (hKdim.trans hLdim.symm)
  have hKeq : K = L :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirEq
      ⟨x, left_mem_affineSpan_pair ℝ x y⟩ hKL
  exact hKeq

private theorem card_line_dist_fiber_le_two (L : AffineSubspace ℝ (RPoint d))
    (hL : Module.finrank ℝ L.direction ≤ 1) (S : Finset (RPoint d))
    (hSL : ∀ x ∈ S, x ∈ L) (p : RPoint d) (ρ : ℝ) :
    (S.filter fun x => dist x p = ρ).card ≤ 2 := by
  classical
  let T := S.filter fun x => dist x p = ρ
  by_cases hT : T.card ≤ 1
  · exact hT.trans (by omega)
  · have hlarge : 1 < T.card := Nat.lt_of_not_ge hT
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlarge
    have hxS := (Finset.mem_filter.mp hx).1
    have hyS := (Finset.mem_filter.mp hy).1
    have hxs : x ∈ (⟨p, ρ⟩ : EuclideanGeometry.Sphere (RPoint d)) := by
      change dist x p = ρ
      exact (Finset.mem_filter.mp hx).2
    have hys : y ∈ (⟨p, ρ⟩ : EuclideanGeometry.Sphere (RPoint d)) := by
      change dist y p = ρ
      exact (Finset.mem_filter.mp hy).2
    have hlineeq := affineSpan_pair_eq_of_mem_of_mem_of_finrank_le_one L hL
      (hSL x hxS) (hSL y hyS) hxy
    have hsubset : T ⊆ {x, (⟨p, ρ⟩ : EuclideanGeometry.Sphere (RPoint d)).secondInter x
        (y -ᵥ x)} := by
      intro z hz
      have hzS := (Finset.mem_filter.mp hz).1
      have hzL := hSL z hzS
      have hzline : z ∈ affineSpan ℝ ({x, y} : Set (RPoint d)) := by
        exact hlineeq ▸ hzL
      have hzSphere : z ∈ (⟨p, ρ⟩ : EuclideanGeometry.Sphere (RPoint d)) := by
        change dist z p = ρ
        exact (Finset.mem_filter.mp hz).2
      rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hxs hzline).2 hzSphere with h | h
      · simp [h]
      · simp [h]
    exact (Finset.card_le_card hsubset).trans (by
      simpa using (Finset.card_le_two (a := x)
        (b := (⟨p, ρ⟩ : EuclideanGeometry.Sphere (RPoint d)).secondInter x (y -ᵥ x))))

private theorem card_circle_dist_fiber_le_two (H : AffineSubspace ℝ (RPoint d))
    (hH : Module.finrank ℝ H.direction = 2) (c : RPoint d) (r : ℝ)
    (hc : c ∈ H) (p : RPoint d) (hp : p ∈ H) (hpc : p ≠ c)
    (S : Finset (RPoint d))
    (hS : ∀ x ∈ S, x ∈ H ∧ dist x c = r) (ρ : ℝ) :
    (S.filter fun x => dist x p = ρ).card ≤ 2 := by
  classical
  let T := S.filter fun x => dist x p = ρ
  by_cases hT : T.card ≤ 1
  · exact hT.trans (by omega)
  · have hlarge : 1 < T.card := Nat.lt_of_not_ge hT
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlarge
    let s₁ : EuclideanGeometry.Sphere (RPoint d) := ⟨c, r⟩
    let s₂ : EuclideanGeometry.Sphere (RPoint d) := ⟨p, ρ⟩
    have hsne : s₁ ≠ s₂ := by
      intro h
      have hcent := congrArg EuclideanGeometry.Sphere.center h
      exact hpc hcent.symm
    have hxs₁ : x ∈ s₁ := by
      change dist x c = r
      exact (hS x ((Finset.mem_filter.mp hx).1)).2
    have hys₁ : y ∈ s₁ := by
      change dist y c = r
      exact (hS y ((Finset.mem_filter.mp hy).1)).2
    have hxs₂ : x ∈ s₂ := by
      change dist x p = ρ
      exact (Finset.mem_filter.mp hx).2
    have hys₂ : y ∈ s₂ := by
      change dist y p = ρ
      exact (Finset.mem_filter.mp hy).2
    have hsubset : T ⊆ {x, y} := by
      intro z hz
      have hzS := (Finset.mem_filter.mp hz).1
      have hzH := (hS z hzS).1
      have hzs₁ : z ∈ s₁ := by
        change dist z c = r
        exact (hS z hzS).2
      have hzs₂ : z ∈ s₂ := by
        change dist z p = ρ
        exact (Finset.mem_filter.mp hz).2
      have hresult : z = x ∨ z = y := by
        letI : FiniteDimensional ℝ H.direction := inferInstance
        exact EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two
          hH (by simpa [s₁] using hc) (by simpa [s₂] using hp)
          (hS x ((Finset.mem_filter.mp hx).1)).1
          (hS y ((Finset.mem_filter.mp hy).1)).1 hzH hsne hxy
          (by simpa [s₁] using hxs₁) (by simpa [s₁] using hys₁)
          (by simpa [s₁] using hzs₁)
          (by simpa [s₂] using hxs₂) (by simpa [s₂] using hys₂)
          (by simpa [s₂] using hzs₂)
      rcases hresult with h | h <;> simp [h]
    exact (Finset.card_le_card hsubset).trans (by
      simpa using (Finset.card_le_two (a := x) (b := y)))

open Classical in
/-- red:flat-caps.line-circle (`reduction.tex:49-54`): a real line holds at most `2M - 1`
points. Also covers flats of dimension `0`. -/
theorem card_inter_line_le (P : Finset (RPoint d)) (L : AffineSubspace ℝ (RPoint d))
    (hL : Module.finrank ℝ L.direction ≤ 1) :
    ((P.filter (· ∈ L)).card : ℝ) ≤ 2 * Mcount P - 1 := by
  classical
  let S := P.filter (· ∈ L)
  by_cases hS : S.Nonempty
  · obtain ⟨p, hp⟩ := hS
    let T := S.erase p
    let f : RPoint d → ℝ := fun x => dist x p
    have hfib : ∀ ρ ∈ T.image f, (T.filter fun x => f x = ρ).card ≤ 2 := by
      intro ρ hρ
      exact card_line_dist_fiber_le_two L hL T
        (by intro x hx; exact (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2)
        p ρ
    have himage : T.image f ⊆ distanceSet P := by
      intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨x, hx, rfl⟩
      have hxP := (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).1
      have hpP := (Finset.mem_filter.mp hp).1
      have hxp : x ≠ p := (Finset.mem_erase.mp hx).1
      exact Finset.mem_image.mpr ⟨(x, p), Finset.mem_offDiag.mpr ⟨hxP, hpP, hxp⟩,
        rfl⟩
    have hcardT : T.card ≤ 2 * distinctDistances P := by
      calc
        T.card ≤ 2 * (T.image f).card := card_le_two_mul_image_card T f hfib
        _ ≤ 2 * distinctDistances P := by
          exact Nat.mul_le_mul_left 2 (by simpa [distinctDistances] using Finset.card_le_card himage)
    have hcardS : S.card = T.card + 1 := (Finset.card_erase_add_one hp).symm
    have hrealT : (T.card : ℝ) ≤ 2 * (distinctDistances P : ℝ) := by exact_mod_cast hcardT
    rw [hcardS]
    unfold Mcount
    push_cast
    linarith
  · have hS0 : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hS)
    rw [hS0]
    norm_num only [Nat.cast_ofNat]
    unfold Mcount
    have hD : (0 : ℝ) ≤ (distinctDistances P : ℝ) := Nat.cast_nonneg _
    linarith

open Classical in
/-- red:flat-caps.line-circle (`reduction.tex:41, 50-54`): a circle (a sphere inside a real
2-plane, centred in that plane) holds at most `2M - 1` points. -/
theorem card_inter_circle_le (P : Finset (RPoint d)) (H : AffineSubspace ℝ (RPoint d))
    (hH : Module.finrank ℝ H.direction = 2) (c : RPoint d) (hc : c ∈ H) (r : ℝ) :
    ((P.filter fun x => x ∈ H ∧ dist x c = r).card : ℝ) ≤ 2 * Mcount P - 1 := by
  classical
  let S := P.filter fun x => x ∈ H ∧ dist x c = r
  by_cases hr : r = 0
  · have hsub : S ⊆ {c} := by
      intro x hx
      apply Finset.mem_singleton.mpr
      have hdist := (Finset.mem_filter.mp hx).2.2
      have hzero : dist x c = 0 := by simpa [hr] using hdist
      exact dist_eq_zero.mp hzero
    have hcard : S.card ≤ 1 := by
      calc
        S.card ≤ ({c} : Finset (RPoint d)).card := Finset.card_le_card hsub
        _ = 1 := by simp
    have hM : (1 : ℝ) ≤ Mcount P := by
      unfold Mcount
      have hD : (0 : ℝ) ≤ (distinctDistances P : ℝ) := Nat.cast_nonneg _
      linarith
    have hreal : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    change (S.card : ℝ) ≤ 2 * Mcount P - 1
    linarith
  · obtain hS | hS := S.eq_empty_or_nonempty
    · have hM : (1 : ℝ) ≤ Mcount P := by
        unfold Mcount
        have hD : (0 : ℝ) ≤ (distinctDistances P : ℝ) := Nat.cast_nonneg _
        linarith
      change (S.card : ℝ) ≤ 2 * Mcount P - 1
      have hScast : (S.card : ℝ) = 0 := by simp [hS]
      rw [hScast]
      have hM' : (1 : ℝ) ≤ (distinctDistances P : ℝ) + 1 := by
        simpa [Mcount] using hM
      unfold Mcount
      nlinarith [hM']
    obtain ⟨p, hp⟩ := hS
    have hpH : p ∈ H := (Finset.mem_filter.mp hp).2.1
    have hpc : p ≠ c := by
      intro h
      have hdist := (Finset.mem_filter.mp hp).2.2
      have : (0 : ℝ) = r := by simpa [h] using hdist
      exact hr this.symm
    let T := S.erase p
    let f : RPoint d → ℝ := fun x => dist x p
    have hfib : ∀ ρ ∈ T.image f, (T.filter fun x => f x = ρ).card ≤ 2 := by
      intro ρ hρ
      exact card_circle_dist_fiber_le_two H hH c r hc p hpH hpc T
        (by intro x hx; exact (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2) ρ
    have himage : T.image f ⊆ distanceSet P := by
      intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨x, hx, rfl⟩
      have hxP := (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).1
      have hpP := (Finset.mem_filter.mp hp).1
      have hxp : x ≠ p := (Finset.mem_erase.mp hx).1
      exact Finset.mem_image.mpr ⟨(x, p), Finset.mem_offDiag.mpr ⟨hxP, hpP, hxp⟩,
        rfl⟩
    have hcardT : T.card ≤ 2 * distinctDistances P := by
      calc
        T.card ≤ 2 * (T.image f).card := card_le_two_mul_image_card T f hfib
        _ ≤ 2 * distinctDistances P := by
          exact Nat.mul_le_mul_left 2 (by simpa [distinctDistances] using Finset.card_le_card himage)
    have hcardS : S.card = T.card + 1 := (Finset.card_erase_add_one hp).symm
    have hrealT : (T.card : ℝ) ≤ 2 * (distinctDistances P : ℝ) := by exact_mod_cast hcardT
    change (S.card : ℝ) ≤ 2 * Mcount P - 1
    rw [hcardS]
    unfold Mcount
    push_cast
    linarith

open Classical in
/-- red:flat-caps.isometry (`reduction.tex:56-58`): the points of `P` in a real affine
`u`-flat form an isometric copy of a finite subset of `ℝ^u`; its distances are distances of
`P`. -/
theorem exists_isometric_copy (P : Finset (RPoint d)) (F : AffineSubspace ℝ (RPoint d)) (u : ℕ)
    (hF : Module.finrank ℝ F.direction = u) :
    ∃ Q : Finset (RPoint u), Q.card = (P.filter (· ∈ F)).card ∧
      distanceSet Q ⊆ distanceSet P := by
  classical
  let S := P.filter (· ∈ F)
  by_cases hS : S.Nonempty
  · obtain ⟨p, hp⟩ := hS
    have hpF : p ∈ F := (Finset.mem_filter.mp hp).2
    let base : F := ⟨p, hpF⟩
    haveI : Nonempty F := ⟨base⟩
    let bF : OrthonormalBasis (Fin (Module.finrank ℝ F.direction)) ℝ F.direction :=
      stdOrthonormalBasis ℝ F.direction
    let bU : OrthonormalBasis (Fin u) ℝ (RPoint u) := EuclideanSpace.basisFun (Fin u) ℝ
    let eDir : F.direction ≃ₗᵢ[ℝ] RPoint u := bF.equiv bU (finCongr hF)
    let E : F ≃ᵃⁱ[ℝ] RPoint u :=
      AffineIsometryEquiv.mk' (fun x : F => eDir (x -ᵥ base)) eDir base (by
        intro x
        simp)
    let g : {x // x ∈ S} → RPoint u := fun x => E ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
    let Q := S.attach.image g
    have hg : Function.Injective g := by
      intro x y hxy
      have hE : (E ⟨(x : RPoint d), (Finset.mem_filter.mp x.2).2⟩ : RPoint u) =
          E ⟨(y : RPoint d), (Finset.mem_filter.mp y.2).2⟩ := hxy
      have hFxy : (⟨(x : RPoint d), (Finset.mem_filter.mp x.2).2⟩ : F) =
          ⟨(y : RPoint d), (Finset.mem_filter.mp y.2).2⟩ := E.injective hE
      apply Subtype.ext
      exact congrArg (fun z : F => (z : RPoint d)) hFxy
    have hQcard : Q.card = S.card := by
      calc
        Q.card = S.attach.card := by
          dsimp [Q]
          rw [Finset.card_image_iff]
          intro x hx y hy hxy
          exact hg hxy
        _ = S.card := Finset.card_attach
    have hdist (x y : {z // z ∈ S}) :
        dist (g x) (g y) = dist (x : RPoint d) (y : RPoint d) := by
      have hxF : (x : RPoint d) ∈ F := (Finset.mem_filter.mp x.2).2
      have hyF : (y : RPoint d) ∈ F := (Finset.mem_filter.mp y.2).2
      change dist (E (⟨x, hxF⟩ : F)) (E ⟨y, hyF⟩) =
        dist (⟨x, hxF⟩ : F) (⟨y, hyF⟩ : F)
      exact E.dist_map _ _
    refine ⟨Q, ?_, ?_⟩
    · simpa [S] using hQcard
    · intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨pair, hpair, rfl⟩
      rcases pair with ⟨q₁, q₂⟩
      rcases Finset.mem_offDiag.mp hpair with ⟨hq₁, hq₂, hqne⟩
      rcases Finset.mem_image.mp hq₁ with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hq₂ with ⟨y, hy, rfl⟩
      have hxy : (x : RPoint d) ≠ y := by
        intro h
        apply hqne
        exact congrArg g (Subtype.ext h)
      have hxP : (x : RPoint d) ∈ P := (Finset.mem_filter.mp x.2).1
      have hyP : (y : RPoint d) ∈ P := (Finset.mem_filter.mp y.2).1
      have hpairP : ((x : RPoint d), (y : RPoint d)) ∈ P.offDiag :=
        Finset.mem_offDiag.mpr ⟨hxP, hyP, hxy⟩
      change dist (g x) (g y) ∈ P.offDiag.image fun pair => dist pair.1 pair.2
      exact Finset.mem_image.mpr ⟨((x : RPoint d), (y : RPoint d)), hpairP, (hdist x y).symm⟩
  · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    refine ⟨∅, ?_, ?_⟩
    · simp [S, hS0]
    · simp [distanceSet]

open Classical in
/-- red:flat-caps, `3 ≤ u < d` (`reduction.tex:38, 56-58`): from IH(d), a real affine
`u`-flat holds at most `C_u M^{u/2}` points. -/
theorem card_inter_flat_le_of_IH (hIH : IH d) (u : ℕ) (hu3 : 3 ≤ u) (hud : u < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (RPoint d)) (F : AffineSubspace ℝ (RPoint d)),
      Module.finrank ℝ F.direction = u →
        ((P.filter (· ∈ F)).card : ℝ) ≤ C * Mcount P ^ ((u : ℝ) / 2) := by
  classical
  obtain ⟨c, hc, hLower⟩ := hIH u hu3 hud
  let α : ℝ := (u : ℝ) / 2
  let β : ℝ := 2 / (u : ℝ)
  let K : ℝ := (c ^ α)⁻¹
  let C : ℝ := max 1 K
  have hu0 : (u : ℝ) ≠ 0 := by
    exact_mod_cast (show u ≠ 0 by omega)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβα : β * α = 1 := by
    dsimp [α, β]
    field_simp
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hCpos, ?_⟩
  intro P F hF
  let S := P.filter (· ∈ F)
  obtain ⟨Q, hQcard, hQdist⟩ := exists_isometric_copy P F u hF
  have hMge : (1 : ℝ) ≤ Mcount P := by
    unfold Mcount
    have hD : (0 : ℝ) ≤ (distinctDistances P : ℝ) := Nat.cast_nonneg _
    linarith
  have hMnonneg : 0 ≤ Mcount P := le_trans (by norm_num) hMge
  have hMpow : 0 ≤ Mcount P ^ α := Real.rpow_nonneg hMnonneg α
  by_cases hQsmall : Q.card ≤ 1
  · have hQsmallReal : (Q.card : ℝ) ≤ 1 := by exact_mod_cast hQsmall
    have hMpowOne : 1 ≤ Mcount P ^ α := Real.one_le_rpow hMge hα
    have hCOne : 1 ≤ C := le_max_left _ _
    have hprod : 1 ≤ C * Mcount P ^ α := by
      calc
        1 ≤ Mcount P ^ α := hMpowOne
        _ ≤ C * Mcount P ^ α := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hCOne hMpow
    change (S.card : ℝ) ≤ C * Mcount P ^ α
    rw [← hQcard]
    exact hQsmallReal.trans hprod
  · have hQtwo : 2 ≤ Q.card := by omega
    have hLB := hLower Q hQtwo
    have hdistCard : distinctDistances Q ≤ distinctDistances P := by
      unfold distinctDistances
      exact Finset.card_le_card hQdist
    have hdistReal : (distinctDistances Q : ℝ) ≤ (distinctDistances P : ℝ) := by
      exact_mod_cast hdistCard
    have hMdist : (distinctDistances P : ℝ) ≤ Mcount P := by
      unfold Mcount
      linarith
    have hraw : c * (Q.card : ℝ) ^ β ≤ Mcount P := hLB.trans (hdistReal.trans hMdist)
    have hQpow : (Q.card : ℝ) ^ β ≤ Mcount P / c := by
      apply (le_div_iff₀ hc).2
      nlinarith [hraw]
    have hQnonneg : (0 : ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
    have hroot : (Q.card : ℝ) ≤ (Mcount P / c) ^ α := by
      calc
        (Q.card : ℝ) = ((Q.card : ℝ) ^ β) ^ α := by
          rw [← Real.rpow_mul hQnonneg β α, hβα, Real.rpow_one]
        _ ≤ (Mcount P / c) ^ α :=
          Real.rpow_le_rpow (Real.rpow_nonneg hQnonneg β) hQpow hα
    have hcoef : (Mcount P / c) ^ α = K * Mcount P ^ α := by
      rw [Real.div_rpow hMnonneg hc.le α]
      dsimp [K]
      rw [div_eq_mul_inv]
      ring
    have hKleC : K ≤ C := le_max_right _ _
    have hcoefle : K * Mcount P ^ α ≤ C * Mcount P ^ α :=
      mul_le_mul_of_nonneg_right hKleC hMpow
    change (S.card : ℝ) ≤ C * Mcount P ^ α
    rw [← hQcard]
    exact hroot.trans (hcoef ▸ hcoefle)

open Classical in
/-- red:flat-caps, `u = 2` (`reduction.tex:37, 56`, with the planar
shortcut): a real affine plane holds at most `C M^{4/3}`
points. This is track C's `ci:planar-occupancy` (`Request.PlanarOccupancy`). -/
theorem card_inter_plane_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (RPoint d)) (H : AffineSubspace ℝ (RPoint d)),
      Module.finrank ℝ H.direction = 2 →
        ((P.filter (· ∈ H)).card : ℝ) ≤ C * Mcount P ^ ((4 : ℝ) / 3) := by
  classical
  obtain ⟨C, hC, hplanar⟩ := TrackC.ci_planar_occupancy
  refine ⟨C, hC, ?_⟩
  intro P H hH
  have hM : (1 : ℝ) ≤ Mcount P := by
    unfold Mcount
    have hD : (0 : ℝ) ≤ (distinctDistances P : ℝ) := Nat.cast_nonneg _
    linarith
  have hMpos : 0 < Mcount P := lt_of_lt_of_le zero_lt_one hM
  by_cases hHne : (H : Set (RPoint d)).Nonempty
  · have hpos : TrackC.positiveDistances P = distanceSet P := by rfl
    have hdist : ((TrackC.positiveDistances P).card : ℝ) ≤ Mcount P := by
      rw [hpos]
      change (distinctDistances P : ℝ) ≤ Mcount P
      unfold Mcount
      linarith
    let plane : TrackC.Plane d := ⟨H, hHne, hH⟩
    have hcap := hplanar d P (Mcount P) hM hdist plane
    simpa [TrackC.pointsOn, plane] using hcap
  · have hfilter : P.filter (· ∈ H) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx hxH
      exact hHne ⟨x, hxH⟩
    have hcard : ((P.filter (· ∈ H)).card : ℝ) = 0 := by simp [hfilter]
    rw [hcard]
    positivity

open Classical in
/-- red:flat-caps.uniform (`reduction.tex:42-46, 59-61`, with `c₀ = 3 - 2·(4/3) = 1/3` after the
planar shortcut): every proper real affine flat holds at most `N B^{-1/3}` points once `N` is
large and `M ≤ ε₀ A`. (For `d = 3` the plane bound `C M^{4/3}` equals `C N B^{-1/3}` at
`M = A`, so a small `ε₀` is needed.) -/
theorem card_inter_proper_flat_le (hd : 3 ≤ d) (hIH : IH d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, ∀ P : Finset (RPoint d), N₀ ≤ P.card →
      Mcount P ≤ ε₀ * Ascale d P.card →
      ∀ F : AffineSubspace ℝ (RPoint d), F ≠ ⊤ →
        ((P.filter (· ∈ F)).card : ℝ) ≤ P.card * Bscale d P.card ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨Cplane, hCplane, hplane⟩ := card_inter_plane_le
  let flatConstant : ℕ → ℝ := fun v =>
    if hv : 3 ≤ v then
      if hvd : v < d then
        Classical.choose (card_inter_flat_le_of_IH hIH v hv hvd)
      else 0
    else 0
  have hflatConstantSpec : ∀ v, 3 ≤ v → v < d →
      0 < flatConstant v ∧
        ∀ P : Finset (RPoint d), ∀ F : AffineSubspace ℝ (RPoint d),
          Module.finrank ℝ F.direction = v →
            ((P.filter (· ∈ F)).card : ℝ) ≤ flatConstant v * Mcount P ^ ((v : ℝ) / 2) := by
    intro v hv hvd
    have hspec := Classical.choose_spec (card_inter_flat_le_of_IH hIH v hv hvd)
    simpa [flatConstant, hv, hvd] using hspec
  have hflatConstant_nonneg : ∀ v, 0 ≤ flatConstant v := by
    intro v
    by_cases hv : 3 ≤ v
    · by_cases hvd : v < d
      · exact (hflatConstantSpec v hv hvd).1.le
      · simp [flatConstant, hv, hvd]
    · simp [flatConstant, hv]
  let Cflat : ℝ := 1 + ∑ v ∈ Finset.range d, flatConstant v
  have hCflat : 0 < Cflat := by
    dsimp [Cflat]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun v hv => hflatConstant_nonneg v)
  have hflatConstant_le (v : ℕ) (hvd : v < d) : flatConstant v ≤ Cflat := by
    dsimp [Cflat]
    have hsum : flatConstant v ≤ ∑ w ∈ Finset.range d, flatConstant w :=
      Finset.single_le_sum (fun w hw => hflatConstant_nonneg w)
        (Finset.mem_range.mpr hvd)
    linarith
  let ε₀ : ℝ := min (1 / 2) (min (1 / (Cplane + 1)) (1 / (Cflat + 1)))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hεhalf : ε₀ ≤ 1 / 2 := min_le_left _ _
  have hεone : ε₀ ≤ 1 := le_trans hεhalf (by norm_num)
  have hεplane : ε₀ ≤ 1 / (Cplane + 1) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεflat : ε₀ ≤ 1 / (Cflat + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hεpow : ε₀ ^ ((4 : ℝ) / 3) ≤ ε₀ := by
    calc
      ε₀ ^ ((4 : ℝ) / 3) ≤ ε₀ ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hε₀ hεone (by norm_num)
      _ = ε₀ := Real.rpow_one _
  have hCεpow : Cplane * ε₀ ^ ((4 : ℝ) / 3) ≤ 1 := by
    calc
      Cplane * ε₀ ^ ((4 : ℝ) / 3) ≤ Cplane * ε₀ :=
        mul_le_mul_of_nonneg_left hεpow hCplane.le
      _ ≤ Cplane * (1 / (Cplane + 1)) :=
        mul_le_mul_of_nonneg_left hεplane hCplane.le
      _ = Cplane / (Cplane + 1) := by ring
      _ ≤ 1 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hCflatε : Cflat * ε₀ ≤ 1 := by
    calc
      Cflat * ε₀ ≤ Cflat * (1 / (Cflat + 1)) :=
        mul_le_mul_of_nonneg_left hεflat hCflat.le
      _ = Cflat / (Cflat + 1) := by ring
      _ ≤ 1 := (div_le_iff₀ (by positivity)).2 (by linarith)
  let N₀ : ℕ := 1
  refine ⟨ε₀, hε₀, N₀, ?_⟩
  intro P hPN hM F hF
  have hPone : 1 ≤ P.card := by simpa [N₀] using hPN
  have hPpos : (0 : ℝ) < (P.card : ℝ) := by
    exact_mod_cast (show 0 < P.card by omega)
  have hPge : (1 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hPone
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hdinv : 0 ≤ 1 / (d : ℝ) := by positivity
  have hAnonneg : 0 ≤ Ascale d P.card := by
    unfold Ascale
    positivity
  have hAeq : Ascale d P.card = Bscale d P.card ^ 2 := by
    unfold Ascale Bscale
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg P.card)]
    congr 1
    push_cast
    ring
  have hBpos : 0 < Bscale d P.card := by
    unfold Bscale
    exact Real.rpow_pos_of_pos hPpos _
  have hBnonneg : 0 ≤ Bscale d P.card := hBpos.le
  have hBge : 1 ≤ Bscale d P.card := by
    unfold Bscale
    exact Real.one_le_rpow hPge hdinv
  have hBpowd : Bscale d P.card ^ (d : ℝ) = (P.card : ℝ) := by
    rw [Bscale, ← Real.rpow_mul hPpos.le]
    have hmul : (1 / (d : ℝ)) * (d : ℝ) = 1 := by
      field_simp
    rw [hmul, Real.rpow_one]
  have htarget : (P.card : ℝ) * Bscale d P.card ^ (-(1 / 3 : ℝ)) =
      Bscale d P.card ^ ((d : ℝ) - 1 / 3) := by
    calc
      (P.card : ℝ) * Bscale d P.card ^ (-(1 / 3 : ℝ)) =
          Bscale d P.card ^ (d : ℝ) * Bscale d P.card ^ (-(1 / 3 : ℝ)) := by
        rw [hBpowd]
      _ = Bscale d P.card ^ ((d : ℝ) - 1 / 3) := by
        rw [← Real.rpow_add hBpos]
        rw [sub_eq_add_neg]
  have hAtoTarget : Ascale d P.card ≤
      (P.card : ℝ) * Bscale d P.card ^ (-(1 / 3 : ℝ)) := by
    rw [hAeq]
    calc
      Bscale d P.card ^ 2 = Bscale d P.card ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (Bscale d P.card) 2).symm
      _ ≤ Bscale d P.card ^ ((d : ℝ) - 1 / 3) :=
        Real.rpow_le_rpow_of_exponent_le hBge (by
          have hd' : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
          linarith)
      _ = (P.card : ℝ) * Bscale d P.card ^ (-(1 / 3 : ℝ)) := htarget.symm
  have hMnonneg : 0 ≤ Mcount P := by
    unfold Mcount
    positivity
  have h2MleA : 2 * Mcount P ≤ Ascale d P.card := by
    have hMhalf : Mcount P ≤ (1 / 2) * Ascale d P.card :=
      le_trans hM (mul_le_mul_of_nonneg_right hεhalf hAnonneg)
    nlinarith
  have hMleA : Mcount P ≤ Ascale d P.card := by
    calc
      Mcount P ≤ ε₀ * Ascale d P.card := hM
      _ ≤ 1 * Ascale d P.card := mul_le_mul_of_nonneg_right hεone hAnonneg
      _ = Ascale d P.card := one_mul _
  let u : ℕ := Module.finrank ℝ F.direction
  have hu_le : u ≤ d := by
    dsimp [u]
    calc
      Module.finrank ℝ F.direction ≤ Module.finrank ℝ (RPoint d) := Submodule.finrank_le _
      _ = d := by simp [RPoint]
  have hu_lt : u < d := by
    rcases AffineSubspace.eq_bot_or_nonempty F with hbot | hFne
    · dsimp [u]
      rw [hbot, AffineSubspace.direction_bot, finrank_bot]
      omega
    · by_contra hnot
      have hu_eq : u = d := Nat.le_antisymm hu_le (Nat.le_of_not_lt hnot)
      have hdir : F.direction = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        simpa [u, RPoint] using hu_eq
      exact hF ((AffineSubspace.direction_eq_top_iff_of_nonempty hFne).mp hdir)
  by_cases hu_line : u ≤ 1
  · have hline := card_inter_line_le P F (by simpa [u] using hu_line)
    have hcapA : ((P.filter (· ∈ F)).card : ℝ) ≤ Ascale d P.card := by
      linarith
    exact hcapA.trans hAtoTarget
  · by_cases hu_plane : u = 2
    · have hplane' := hplane P F (by simpa [u] using hu_plane)
      have hβ : 0 ≤ (4 : ℝ) / 3 := by positivity
      have hMβ : Mcount P ^ ((4 : ℝ) / 3) ≤
          (ε₀ * Ascale d P.card) ^ ((4 : ℝ) / 3) :=
        Real.rpow_le_rpow hMnonneg hM hβ
      have hplaneA : ((P.filter (· ∈ F)).card : ℝ) ≤ Ascale d P.card ^ ((4 : ℝ) / 3) := by
        calc
          ((P.filter (· ∈ F)).card : ℝ) ≤ Cplane * Mcount P ^ ((4 : ℝ) / 3) := hplane'
          _ ≤ Cplane * (ε₀ * Ascale d P.card) ^ ((4 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_left hMβ hCplane.le
          _ = (Cplane * ε₀ ^ ((4 : ℝ) / 3)) *
                Ascale d P.card ^ ((4 : ℝ) / 3) := by
            rw [Real.mul_rpow (le_of_lt hε₀) hAnonneg]
            ring
          _ ≤ Ascale d P.card ^ ((4 : ℝ) / 3) := by
            calc
              (Cplane * ε₀ ^ ((4 : ℝ) / 3)) * Ascale d P.card ^ ((4 : ℝ) / 3) ≤
                  1 * Ascale d P.card ^ ((4 : ℝ) / 3) :=
                mul_le_mul_of_nonneg_right hCεpow (Real.rpow_nonneg hAnonneg _)
              _ = Ascale d P.card ^ ((4 : ℝ) / 3) := one_mul _
      have hAplane : Ascale d P.card ^ ((4 : ℝ) / 3) =
          Bscale d P.card ^ ((8 : ℝ) / 3) := by
        rw [hAeq, ← Real.rpow_natCast, ← Real.rpow_mul hBnonneg]
        congr 1
        norm_num
      have hExponent : (8 : ℝ) / 3 ≤ (d : ℝ) - 1 / 3 := by
        have hd' : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      calc
        ((P.filter (· ∈ F)).card : ℝ) ≤ Ascale d P.card ^ ((4 : ℝ) / 3) := hplaneA
        _ = Bscale d P.card ^ ((8 : ℝ) / 3) := hAplane
        _ ≤ Bscale d P.card ^ ((d : ℝ) - 1 / 3) :=
          Real.rpow_le_rpow_of_exponent_le hBge hExponent
        _ = (P.card : ℝ) * Bscale d P.card ^ (-(1 / 3 : ℝ)) := htarget.symm
    · have hu3 : 3 ≤ u := by omega
      let α : ℝ := (u : ℝ) / 2
      have hα : 0 ≤ α := by dsimp [α]; positivity
      have hαone : 1 ≤ α := by
        dsimp [α]
        have hu3' : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
        linarith
      have hεα : ε₀ ^ α ≤ ε₀ := by
        calc
          ε₀ ^ α ≤ ε₀ ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hε₀ hεone hαone
          _ = ε₀ := Real.rpow_one _
      have hCεα : Cflat * ε₀ ^ α ≤ 1 := by
        calc
          Cflat * ε₀ ^ α ≤ Cflat * ε₀ :=
            mul_le_mul_of_nonneg_left hεα hCflat.le
          _ ≤ 1 := hCflatε
      have hMα : Mcount P ^ α ≤ (ε₀ * Ascale d P.card) ^ α :=
        Real.rpow_le_rpow hMnonneg hM hα
      have hflat := (hflatConstantSpec u hu3 hu_lt).2 P F rfl
      have hAalpha : Ascale d P.card ^ α = Bscale d P.card ^ (u : ℝ) := by
        rw [hAeq, ← Real.rpow_natCast, ← Real.rpow_mul hBnonneg]
        congr 1
        dsimp [α]
        ring
      have hcapB : ((P.filter (· ∈ F)).card : ℝ) ≤ Bscale d P.card ^ (u : ℝ) := by
        calc
          ((P.filter (· ∈ F)).card : ℝ) ≤ flatConstant u * Mcount P ^ α := by
            simpa [α] using hflat
          _ ≤ Cflat * Mcount P ^ α :=
            mul_le_mul_of_nonneg_right (hflatConstant_le u hu_lt)
              (Real.rpow_nonneg hMnonneg α)
          _ ≤ Cflat * (ε₀ * Ascale d P.card) ^ α :=
            mul_le_mul_of_nonneg_left hMα hCflat.le
          _ = (Cflat * ε₀ ^ α) * Ascale d P.card ^ α := by
            rw [Real.mul_rpow (le_of_lt hε₀) hAnonneg]
            ring
          _ ≤ Ascale d P.card ^ α := by
            calc
              (Cflat * ε₀ ^ α) * Ascale d P.card ^ α ≤
                  1 * Ascale d P.card ^ α :=
                mul_le_mul_of_nonneg_right hCεα (Real.rpow_nonneg hAnonneg α)
              _ = Ascale d P.card ^ α := one_mul _
          _ = Bscale d P.card ^ (u : ℝ) := hAalpha
      have hExponent : (u : ℝ) ≤ (d : ℝ) - 1 / 3 := by
        have huNat : u + 1 ≤ d := by omega
        have huCast : (u : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast huNat
        linarith
      calc
        ((P.filter (· ∈ F)).card : ℝ) ≤ Bscale d P.card ^ (u : ℝ) := hcapB
        _ ≤ Bscale d P.card ^ ((d : ℝ) - 1 / 3) :=
          Real.rpow_le_rpow_of_exponent_le hBge hExponent
        _ = (P.card : ℝ) * Bscale d P.card ^ (-(1 / 3 : ℝ)) := htarget.symm

open Classical in
/-- red:flat-caps.uniform, complex flats (`reduction.tex:44-45, 61-64`): a proper complex
affine flat of `ℂ^d` holds at most `N B^{-1/3}` real sample points. -/
theorem card_inter_proper_complex_flat_le (hd : 3 ≤ d) (hIH : IH d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, ∀ P : Finset (RPoint d), N₀ ≤ P.card →
      Mcount P ≤ ε₀ * Ascale d P.card →
      ∀ F : AffineSubspace ℂ (Fin d → ℂ), F ≠ ⊤ →
        ((P.filter fun p => cplx p ∈ F).card : ℝ) ≤
          P.card * Bscale d P.card ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨ε₀, hε₀, N₀, hreal⟩ := card_inter_proper_flat_le hd hIH
  refine ⟨ε₀, hε₀, N₀, ?_⟩
  intro P hN hM F hF
  let S : Finset (RPoint d) := P.filter fun p => cplx p ∈ F
  by_cases hS : S.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hS
    have hp₀F : cplx p₀ ∈ F := (Finset.mem_filter.mp hp₀).2
    let V : Submodule ℝ (RPoint d) :=
      Submodule.span ℝ (Set.range fun q : S => (q : RPoint d) -ᵥ p₀)
    let H : AffineSubspace ℝ (RPoint d) := AffineSubspace.mk' p₀ V
    have hSsub : S ⊆ P.filter (· ∈ H) := by
      intro q hq
      have hqH : (q -ᵥ p₀) ∈ V :=
        Submodule.subset_span ⟨⟨q, hq⟩, rfl⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1, by
        change (q -ᵥ p₀) ∈ V
        exact hqH⟩
    have hVtoF : ∀ v ∈ V, cplx v ∈ F.direction := by
      intro v hv
      change v ∈ Submodule.span ℝ (Set.range fun q : S => (q : RPoint d) -ᵥ p₀) at hv
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · intro x hx
        rcases Set.mem_range.mp hx with ⟨q, rfl⟩
        have hqF : cplx (q : RPoint d) ∈ F :=
          (Finset.mem_filter.mp q.property).2
        have hdiff := AffineSubspace.vsub_mem_direction hqF hp₀F
        have hmap : cplx ((q : RPoint d) -ᵥ p₀) = cplx q - cplx p₀ := by
          ext i
          simp [cplx, vsub_eq_sub]
        rw [hmap]
        exact hdiff
      · have hzero : cplx (0 : RPoint d) = 0 := by
          ext i
          simp [cplx]
        rw [hzero]
        exact F.direction.zero_mem
      · intro x y hx hy hix hiy
        have hmap : cplx (x + y) = cplx x + cplx y := by
          ext i
          simp [cplx]
        rw [hmap]
        exact F.direction.add_mem hix hiy
      · intro a x hx ih
        have hmap : cplx (a • x) = (a : ℂ) • cplx x := by
          ext i
          simp [cplx]
        rw [hmap]
        exact F.direction.smul_mem (a : ℂ) ih
    have hHproper : H ≠ ⊤ := by
      intro hHtop
      have hVtop : V = ⊤ := by
        have hdir : H.direction = ⊤ := by rw [hHtop, AffineSubspace.direction_top]
        simpa [H] using hdir
      have hbasis : ∀ i : Fin d, (Pi.basisFun ℂ (Fin d)) i ∈ F.direction := by
        intro i
        have hi : EuclideanSpace.single i (1 : ℝ) ∈ V := by
          rw [hVtop]
          exact Submodule.mem_top
        have h := hVtoF (EuclideanSpace.single i (1 : ℝ)) hi
        have hmap : cplx (EuclideanSpace.single i (1 : ℝ)) =
            (Pi.basisFun ℂ (Fin d)) i := by
          ext j
          by_cases hji : j = i <;>
            simp [cplx, EuclideanSpace.single_apply, Pi.single_apply,
              Pi.basisFun_apply, hji]
        rw [hmap] at h
        exact h
      have htop : (⊤ : Submodule ℂ (Fin d → ℂ)) ≤ F.direction := by
        rw [← (Pi.basisFun ℂ (Fin d)).span_eq]
        apply Submodule.span_le.mpr
        rintro z ⟨i, rfl⟩
        exact hbasis i
      have hFdir : F.direction = ⊤ := top_le_iff.mp htop
      have hFne : (F : Set (Fin d → ℂ)).Nonempty := ⟨cplx p₀, hp₀F⟩
      exact hF ((AffineSubspace.direction_eq_top_iff_of_nonempty hFne).mp hFdir)
    have hcap := hreal P hN hM H hHproper
    have hScard : (S.card : ℝ) ≤ ((P.filter (· ∈ H)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSsub
    change (S.card : ℝ) ≤ P.card * Bscale d P.card ^ (-(1 / 3 : ℝ))
    exact hScard.trans hcap
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ P.card * Bscale d P.card ^ (-(1 / 3 : ℝ))
    have hBnonneg : 0 ≤ Bscale d P.card := by
      unfold Bscale
      positivity
    have hright : 0 ≤ (P.card : ℝ) * Bscale d P.card ^ (-(1 / 3 : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hBnonneg _)
    simpa [hSempty] using hright

open Classical Filter in
/-- red:flat-caps, the `B^{u+o(1)}` form for `3 ≤ u < d` (consumed at
`sparse-cones.tex:383-388`, `(k+1)`-flats with `k ≥ 2`): for every `ε > 0`, a real affine
`u`-flat holds at most `B^{u+ε}` points once `N` is large and `M ≤ A`. (Planes are covered by
`card_inter_plane_le`; after the planar shortcut they hold up to `C B^{8/3}` points.) -/
theorem card_inter_flat_le_rpow (hd : 3 ≤ d) (hIH : IH d) (u : ℕ) (hu3 : 3 ≤ u)
    (hud : u < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ P : Finset (RPoint d), N₀ ≤ P.card → Mcount P ≤ Ascale d P.card →
      ∀ F : AffineSubspace ℝ (RPoint d), Module.finrank ℝ F.direction = u →
        ((P.filter (· ∈ F)).card : ℝ) ≤ Bscale d P.card ^ ((u : ℝ) + ε) := by
  classical
  obtain ⟨C, hC, hcap⟩ := card_inter_flat_le_of_IH hIH u hu3 hud
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  let γ : ℝ := (1 / (d : ℝ)) * ε
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ γ) atTop atTop := by
    exact (tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop
  have hCeventually : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ γ :=
    htend.eventually (eventually_ge_atTop C)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hCeventually
  let N₁ : ℕ := max N₀ 1
  refine ⟨N₁, ?_⟩
  intro P hPN hMP F hF
  let α : ℝ := (u : ℝ) / 2
  have hα : 0 ≤ α := by
    dsimp [α]
    positivity
  have hNcard : (N₁ : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hPN
  have hPone : 1 ≤ P.card := le_trans (le_max_right N₀ 1) hPN
  have hPpos : (0 : ℝ) < (P.card : ℝ) := by
    exact_mod_cast (show 0 < P.card by omega)
  have hCscale : C ≤ Bscale d P.card ^ ε := by
    unfold Bscale
    rw [← Real.rpow_mul (Nat.cast_nonneg P.card)]
    calc
      C ≤ (N₁ : ℝ) ^ γ := hN₀ N₁ (le_max_left N₀ 1)
      _ ≤ (P.card : ℝ) ^ γ :=
        Real.rpow_le_rpow (Nat.cast_nonneg N₁) hNcard hγ.le
  have hAeq : Ascale d P.card = Bscale d P.card ^ 2 := by
    unfold Ascale Bscale
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg P.card)]
    congr 1
    push_cast
    ring
  have hBpos : 0 < Bscale d P.card := by
    unfold Bscale
    exact Real.rpow_pos_of_pos hPpos _
  have hBnonneg : 0 ≤ Bscale d P.card := hBpos.le
  have hAalpha : Ascale d P.card ^ α = Bscale d P.card ^ (u : ℝ) := by
    rw [hAeq, ← Real.rpow_natCast, ← Real.rpow_mul hBnonneg]
    congr 1
    dsimp [α]
    ring
  have hMge : (1 : ℝ) ≤ Mcount P := by
    unfold Mcount
    have hD : (0 : ℝ) ≤ (distinctDistances P : ℝ) := Nat.cast_nonneg _
    linarith
  have hMnonneg : 0 ≤ Mcount P := le_trans (by norm_num) hMge
  have hMpow : Mcount P ^ α ≤ Ascale d P.card ^ α :=
    Real.rpow_le_rpow hMnonneg hMP hα
  have hMpowNonneg : 0 ≤ Mcount P ^ α := Real.rpow_nonneg hMnonneg α
  have hBpowNonneg : 0 ≤ Bscale d P.card ^ ε := Real.rpow_nonneg hBnonneg ε
  calc
    ((P.filter (· ∈ F)).card : ℝ) ≤ C * Mcount P ^ α := by
      simpa [α] using hcap P F hF
    _ ≤ Bscale d P.card ^ ε * Mcount P ^ α :=
      mul_le_mul_of_nonneg_right hCscale hMpowNonneg
    _ ≤ Bscale d P.card ^ ε * Ascale d P.card ^ α :=
      mul_le_mul_of_nonneg_left hMpow hBpowNonneg
    _ = Bscale d P.card ^ ε * Bscale d P.card ^ (u : ℝ) := by rw [hAalpha]
    _ = Bscale d P.card ^ ((u : ℝ) + ε) := by
      rw [← Real.rpow_add hBpos]
      ring

end Reduction

end

end DistinctDistances
