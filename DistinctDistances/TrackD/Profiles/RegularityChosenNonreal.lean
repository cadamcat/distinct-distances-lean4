import DistinctDistances.TrackD.Profiles.RegularityChosenCuts

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

variable {d : ℕ}

/-- A polynomial vanishing on a real affine subspace vanishes on its complex affine span. -/
private theorem dnonreal_vanishing_on_affineSpan (G : AffineSubspace ℝ (Pt d))
    (x₀ : Pt d) (hx₀ : x₀ ∈ G) (f : Poly d)
    (hvan : ∀ x ∈ G, MvPolynomial.eval (toC x) f = 0)
    (z : Point d) (hz : z ∈ affineSpan ℂ (toC '' (G : Set (Pt d)))) :
    MvPolynomial.eval z f = 0 := by
  classical
  let T : Set (Point d) := toC '' (G : Set (Pt d))
  let S : Set (Point d) := (fun y : Point d => y -ᵥ toC x₀) '' T
  let r : ℕ := Module.finrank ℂ (Submodule.span ℂ S)
  obtain ⟨v, hvS, hvspan, _⟩ :
      ∃ v : Fin r → Point d, (∀ i, v i ∈ S) ∧
        Submodule.span ℂ (Set.range v) = Submodule.span ℂ S ∧ LinearIndependent ℂ v := by
    simpa [r] using Submodule.exists_fun_fin_finrank_span_eq ℂ S
  have hx₀T : toC x₀ ∈ T := Set.mem_image_of_mem toC hx₀
  have hdir : (affineSpan ℂ T).direction = Submodule.span ℂ (Set.range v) := by
    rw [direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℂ hx₀T]
    exact hvspan.symm
  have hvWitness : ∀ i, ∃ x : Pt d, x ∈ G ∧ toC x -ᵥ toC x₀ = v i := by
    intro i
    rcases hvS i with ⟨y, hy, hyv⟩
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    simpa [hxy] using hyv
  choose x hxG hvx using hvWitness
  have hvxC (i : Fin r) : v i = toC (x i -ᵥ x₀) := by
    rw [← hvx i]
    ext j
    simp [toC]
  let param : Fin d → MvPolynomial (Fin r) ℂ := fun j =>
    MvPolynomial.C (toC x₀ j) +
      ∑ i, MvPolynomial.C (v i j) * MvPolynomial.X i
  let q : MvPolynomial (Fin r) ℂ := MvPolynomial.aeval param f
  have hEval (u : Fin r → ℂ) :
      MvPolynomial.eval u q =
        MvPolynomial.eval (fun j => toC x₀ j + ∑ i, u i * v i j) f := by
    have hcomp : (MvPolynomial.aeval u).comp (MvPolynomial.aeval param) =
        MvPolynomial.aeval (fun j => toC x₀ j + ∑ i, u i * v i j) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [param, mul_comm]
    simpa [q] using congrArg (fun φ : Poly d →ₐ[ℂ] ℂ => φ f) hcomp
  have hrealPoint (u : Fin r → ℝ) :
      (fun j => toC x₀ j + ∑ i, (u i : ℂ) * v i j) =
        toC ((∑ i, u i • (x i -ᵥ x₀)) +ᵥ x₀) := by
    funext j
    simp [toC, hvxC, Finset.sum_apply, Complex.ofReal_sum, Complex.ofReal_mul]
    <;> ring
  have hpointG (u : Fin r → ℝ) :
      (∑ i, u i • (x i -ᵥ x₀)) +ᵥ x₀ ∈ G := by
    apply AffineSubspace.vadd_mem_of_mem_direction
    · exact Submodule.sum_mem _ fun i hi =>
        G.direction.smul_mem _ (AffineSubspace.vsub_mem_direction (hxG i) hx₀)
    · exact hx₀
  have hqzero : q = 0 := by
    apply MvPolynomial.funext_set
      (s := fun _ : Fin r => Set.range (fun t : ℝ => (t : ℂ)))
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro u hu
    have hucoord : ∀ i, u i ∈ Set.range (fun t : ℝ => (t : ℂ)) := by
      intro i
      exact (Set.mem_pi.mp hu) i (Set.mem_univ i)
    choose t ht using hucoord
    have huEq : u = fun i => (t i : ℂ) := by
      funext i
      exact (ht i).symm
    rw [huEq, hEval, hrealPoint]
    exact hvan _ (hpointG t)
  have hzdir : z -ᵥ toC x₀ ∈ Submodule.span ℂ (Set.range v) := by
    rw [← hdir]
    exact AffineSubspace.vsub_mem_direction hz (subset_affineSpan ℂ T hx₀T)
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hzdir
  have hqu : MvPolynomial.eval u q = 0 := by rw [hqzero]; simp
  rw [hEval] at hqu
  have hzEq : z = fun j => toC x₀ j + ∑ i, u i * v i j := by
    calc
      z = (z -ᵥ toC x₀) +ᵥ toC x₀ := by simp
      _ = (∑ i, u i • v i) +ᵥ toC x₀ := by rw [hu]
      _ = _ := by
        ext j
        simp [Finset.sum_apply, smul_eq_mul]
        ring
  rw [hzEq]
  exact hqu

private def dnonrealAffineLinearPoly (L : Point d →ₗ[ℂ] ℂ) (a : Point d) : Poly d :=
  (∑ i : Fin d, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i) -
    MvPolynomial.C (L a)

private theorem dnonrealAffineLinearPoly_degree (L : Point d →ₗ[ℂ] ℂ) (a : Point d) :
    (dnonrealAffineLinearPoly L a).totalDegree ≤ 1 := by
  classical
  have hsum :
      (∑ i : Fin d, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    calc
      _ ≤ (MvPolynomial.C (L (Pi.single i 1))).totalDegree +
          (MvPolynomial.X i : Poly d).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = 1 := by simp
  unfold dnonrealAffineLinearPoly
  rw [sub_eq_add_neg]
  calc
    _ ≤ max _ _ := MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := max_le hsum (by simp)

private theorem dnonrealAffineLinearPoly_eval (L : Point d →ₗ[ℂ] ℂ) (a y : Point d) :
    MvPolynomial.eval y (dnonrealAffineLinearPoly L a) = L (y -ᵥ a) := by
  classical
  have hy : y = ∑ i : Fin d, y i • (Pi.single i (1 : ℂ) : Point d) := by
    ext j
    simp [Pi.single_apply]
  unfold dnonrealAffineLinearPoly
  rw [MvPolynomial.eval_sub]
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  have hlin :
      (∑ i : Fin d, L (Pi.single i (1 : ℂ)) * y i) = L y := by
    calc
      _ = ∑ i : Fin d, L (y i • (Pi.single i (1 : ℂ) : Point d)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [map_smul, mul_comm]
      _ = L (∑ i : Fin d, y i • (Pi.single i (1 : ℂ) : Point d)) := by rw [map_sum]
      _ = L y := congrArg L hy.symm
  rw [vsub_eq_sub, map_sub, hlin]

/-- A nonreal affine flat with a real point has a proper degree-one cut containing all its real
points. The density helper above identifies the complex affine span of the real locus with its
Zariski closure. -/
private theorem dnonreal_affine_separator (Z : AffineVariety d) (hflat : IsFlat Z)
    (hnonreal : ¬ IsRealFlat Z) (hne : ∃ x : Pt d, toC x ∈ Z) :
    ∃ f : Poly d, f.totalDegree ≤ 1 ∧
      (∀ x : Pt d, toC x ∈ Z → MvPolynomial.eval (toC x) f = 0) ∧
      ∃ z ∈ Z, MvPolynomial.eval z f ≠ 0 := by
  classical
  obtain ⟨F, hF⟩ := hflat
  rcases hne with ⟨x₀, hx₀Z⟩
  have hx₀F : toC x₀ ∈ F := by
    change toC x₀ ∈ Z.points at hx₀Z
    rw [hF] at hx₀Z
    exact hx₀Z
  let G : AffineSubspace ℝ (Pt d) :=
    { carrier := {x | toC x ∈ F}
      smul_vsub_vadd_mem' := by
        rintro t p₁ p₂ p₃ hp₁ hp₂ hp₃
        change toC p₁ ∈ F at hp₁
        change toC p₂ ∈ F at hp₂
        change toC p₃ ∈ F at hp₃
        have ht := F.smul_vsub_vadd_mem' (t : ℂ) hp₁ hp₂ hp₃
        change toC (t • (p₁ -ᵥ p₂) +ᵥ p₃) ∈ F
        have hmap : toC (t • (p₁ -ᵥ p₂) +ᵥ p₃) =
            (t : ℂ) • (toC p₁ -ᵥ toC p₂) +ᵥ toC p₃ := by
          ext i
          simp [toC, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub]
        rw [hmap]
        exact ht }
  have hGmem (x : Pt d) : x ∈ G ↔ toC x ∈ F := Iff.rfl
  have hx₀G : x₀ ∈ G := hGmem x₀ |>.2 hx₀F
  let T : Set (Point d) := toC '' (G : Set (Pt d))
  let H : AffineSubspace ℂ (Point d) := affineSpan ℂ T
  have hTsub : T ⊆ Z.points := by
    rintro y ⟨x, hxG, rfl⟩
    rw [hF]
    exact (hGmem x).mp hxG
  have hTsubF : T ⊆ (F : Set (Point d)) := by
    rintro y ⟨x, hxG, rfl⟩
    exact (hGmem x).mp hxG
  have hHle : H ≤ F := affineSpan_le_of_subset_coe hTsubF
  have hHne : H ≠ F := by
    intro hHF
    have hclosure : AffineVariety.closure T = Z := by
      apply AffineVariety.ext
      apply le_antisymm
      · intro f hf
        change f ∈ MvPolynomial.vanishingIdeal ℂ T at hf
        change f ∈ Z.ideal
        rw [← AffineVariety.vanishingIdeal_points Z]
        rw [MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
        intro z hz
        have hfvan : ∀ x ∈ G, MvPolynomial.eval (toC x) f = 0 := by
          intro x hx
          exact hf (toC x) (Set.mem_image_of_mem toC hx)
        have hzF : z ∈ F := by
          change z ∈ Z.points at hz
          rw [hF] at hz
          exact hz
        have hzH : z ∈ H := by rw [hHF]; exact hzF
        exact dnonreal_vanishing_on_affineSpan G x₀ hx₀G f hfvan z hzH
      · intro f hf
        change f ∈ Z.ideal at hf
        rw [← AffineVariety.vanishingIdeal_points Z] at hf
        change f ∈ MvPolynomial.vanishingIdeal ℂ T
        rw [MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
        intro z hz
        rcases hz with ⟨x, hxG, rfl⟩
        exact hf (toC x) (hTsub (Set.mem_image_of_mem toC hxG))
    have hreal : IsRealFlat Z := by
      refine ⟨G, ⟨x₀, hx₀G⟩, ?_⟩
      change Z.points = (AffineVariety.closure T).points
      rw [hclosure]
    exact hnonreal hreal
  have hHlt : H < F := lt_of_le_of_ne hHle hHne
  obtain ⟨z, hzF, hznotH⟩ := AffineSubspace.exists_of_lt hHlt
  have hx₀H : toC x₀ ∈ H := subset_affineSpan ℂ T
    (Set.mem_image_of_mem toC hx₀G)
  have hvnot : z -ᵥ toC x₀ ∉ H.direction := by
    intro hv
    have hzH : (z -ᵥ toC x₀) +ᵥ toC x₀ ∈ H :=
      AffineSubspace.vadd_mem_of_mem_direction hv hx₀H
    exact hznotH (by simpa using hzH)
  obtain ⟨L, hLv, hker⟩ := Submodule.exists_le_ker_of_notMem hvnot
  let f : Poly d := dnonrealAffineLinearPoly L (toC x₀)
  refine ⟨f, ?_, ?_, ?_⟩
  · exact dnonrealAffineLinearPoly_degree L (toC x₀)
  · intro x hxZ
    have hxF : toC x ∈ F := by
      change toC x ∈ Z.points at hxZ
      rw [hF] at hxZ
      exact hxZ
    have hxG : x ∈ G := (hGmem x).2 hxF
    have hxH : toC x ∈ H := subset_affineSpan ℂ T
      (Set.mem_image_of_mem toC hxG)
    rw [dnonrealAffineLinearPoly_eval]
    apply hker
    exact AffineSubspace.vsub_mem_direction hxH hx₀H
  · refine ⟨z, ?_, ?_⟩
    · change z ∈ Z.points
      rw [hF]
      exact hzF
    · rw [dnonrealAffineLinearPoly_eval]
      exact hLv

/-- Chosen-margin form of `prof:regularity.nonreal` (`profiles.tex:357–358, 431–435`):
choose and expose the cuts input margin `η ≤ ξ / 2`, then reuse the same nonreal
separator proof with `prof_regularity_cuts_with_margin`. The output plateau `ξ`
and test degree are unchanged. -/
theorem prof_regularity_nonreal_with_margin (d : ℕ) (hd : 3 ≤ d) :
    ∀ θ > 0, ∀ ξ > 0, ∃ θ₁ > 0, ∃ η > 0, η ≤ ξ / 2 ∧ ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (X : Piece d), PieceGood P θ₁ η 1 X → s₁ ≤ X.width →
        ∀ j : ℕ, j < d → (∃ b : ℝ, OnPlateau X.path.time j ξ b ∧
          1 ≤ testDeg (cfgB P) X.width b) →
          ((X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x),
              IsFlat Z ∧ ¬ IsRealFlat Z)).card : ℝ) ≤ θ * X.pts.card := by
  intro θ hθ ξ hξ
  obtain ⟨θ₁, hθ₁, η, hη, hηξ, s₁, hcuts⟩ :=
    prof_regularity_cuts_with_margin d hd θ hθ ξ hξ 1 (by norm_num)
  refine ⟨θ₁, hθ₁, η, hη, hηξ, s₁, ?_⟩
  intro P X hX hs j hj hb
  rcases hb with ⟨b, hbplateau, hT⟩
  let nonrealAt (Z : AffineVariety d) :=
    IsFlat Z ∧ ¬ IsRealFlat Z ∧ ∃ x : Pt d, toC x ∈ Z
  let g : AffineVariety d → Poly d := fun Z =>
    if h : nonrealAt Z then
      Classical.choose (dnonreal_affine_separator Z h.1 h.2.1 h.2.2)
    else 0
  have hspec (Z : AffineVariety d) (h : nonrealAt Z) :
      (g Z).totalDegree ≤ 1 ∧
        (∀ x : Pt d, toC x ∈ Z → MvPolynomial.eval (toC x) (g Z) = 0) ∧
        ∃ z ∈ Z, MvPolynomial.eval z (g Z) ≠ 0 := by
    simpa [g, nonrealAt, h] using
      (Classical.choose_spec (dnonreal_affine_separator Z h.1 h.2.1 h.2.2))
  have hgdeg (Z : AffineVariety d) :
      ((g Z).totalDegree : ℝ) ≤ 1 * testDeg (cfgB P) X.width b := by
    by_cases h : nonrealAt Z
    · have hdeg : ((g Z).totalDegree : ℝ) ≤ 1 := by
        exact_mod_cast (hspec Z h).1
      calc
        _ ≤ 1 := hdeg
        _ ≤ 1 * testDeg (cfgB P) X.width b := by nlinarith [hT]
    · have hg0 : g Z = 0 := by simp [g, h]
      rw [hg0]
      simp only [MvPolynomial.totalDegree_zero, Nat.cast_zero]
      nlinarith [hT]
  have hcut := hcuts P X hX hs j hj b hbplateau hT g hgdeg
  let bad : Finset (Pt d) := X.pts.filter (fun x =>
    ∃ Z ∈ X.path.localCarriers j (toC x), IsFlat Z ∧ ¬ IsRealFlat Z)
  let captured : Finset (Pt d) := X.pts.filter (fun x =>
    ∃ Z ∈ X.path.localCarriers j (toC x),
      g Z ∉ Z.ideal ∧ MvPolynomial.eval (toC x) (g Z) = 0)
  have hsub : bad ⊆ captured := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxin, hbad⟩
    rcases hbad with ⟨Z, hZ, hflat, hnonreal⟩
    have hlocal : X.path.IsCarrier j Z ∧ toC x ∈ Z := by
      change Z ∈ X.path.localCarriers j (toC x) at hZ
      exact hZ
    have hcondition : nonrealAt Z := ⟨hflat, hnonreal, x, hlocal.2⟩
    have hsep := hspec Z hcondition
    have hnot : g Z ∉ Z.ideal := by
      intro hf
      rw [← AffineVariety.vanishingIdeal_points Z] at hf
      rw [MvPolynomial.mem_vanishingIdeal_iff] at hf
      rcases hsep.2.2 with ⟨z, hz, hznz⟩
      exact hznz (hf z hz)
    have heval : MvPolynomial.eval (toC x) (g Z) = 0 := hsep.2.1 x hlocal.2
    exact Finset.mem_filter.mpr ⟨hxin, ⟨Z, hZ, hnot, heval⟩⟩
  have hcaptured : (captured.card : ℝ) ≤ θ * X.pts.card := by
    simpa [captured] using hcut
  have hcard : (bad.card : ℝ) ≤ (captured.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    (bad.card : ℝ) ≤ (captured.card : ℝ) := hcard
    _ ≤ θ * X.pts.card := hcaptured

end
end DistinctDistances.TrackD
