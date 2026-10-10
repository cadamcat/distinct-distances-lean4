import DistinctDistances.TrackD.Profiles.RegularityChosenJacobian

namespace DistinctDistances.TrackD
open Filter
open scoped Topology BigOperators Classical
noncomputable section

/-- An asymptotic piece sequence that supplies every fixed capture margin
can consume the chosen-margin cuts interface without changing its tests. -/
theorem regularity_cuts_sequence (d : ℕ) (hd : 3 ≤ d)
    (P : ℕ → Finset (Pt d)) (X : ℕ → Piece d)
    (hgood : ∀ θ > 0, ∀ η > 0, ∀ᶠ i in atTop, PieceGood (P i) θ η 1 (X i))
    (hgrows : Tendsto (fun i => (X i).width) atTop atTop)
    (θ ξ K : ℝ) (hθ : 0 < θ) (hξ : 0 < ξ) (hK : 1 ≤ K) :
    ∀ᶠ i in atTop, ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau (X i).path.time j ξ b →
      1 ≤ testDeg (cfgB (P i)) (X i).width b →
      ∀ f : AffineVariety d → Poly d,
        (∀ Z, ((f Z).totalDegree : ℝ) ≤ K * testDeg (cfgB (P i)) (X i).width b) →
        (((X i).pts.filter (fun x => ∃ Z ∈ (X i).path.localCarriers j (toC x),
          f Z ∉ Z.ideal ∧ MvPolynomial.eval (toC x) (f Z) = 0)).card : ℝ) ≤
            θ * (X i).pts.card := by
  obtain ⟨θ₁, hθ₁, η, hη, _, s₁, hcuts⟩ :=
    prof_regularity_cuts_with_margin d hd θ hθ ξ hξ K hK
  filter_upwards [hgood θ₁ hθ₁ η hη, hgrows.eventually_ge_atTop s₁] with i hi hs
  exact hcuts (P i) (X i) hi hs

/-- A pool sequence with every fixed capture margin and profile precision
can consume the chosen-margin Jacobian interface. -/
theorem regularity_jacobian_sequence (d : ℕ) (hd : 3 ≤ d)
    (P : ℕ → Finset (Pt d)) (pl : ℕ → Finset (Piece d)) (s : ℕ → ℝ) (t : Fin d → ℝ)
    (hgood : ∀ θ > 0, ∀ η > 0, ∀ ρ > 0,
      ∀ᶠ i in atTop, PoolGood (P i) θ η 1 ρ (pl i) (s i) t)
    (hgrows : Tendsto s atTop atTop) (θ ξ : ℝ) (hθ : 0 < θ) (hξ : 0 < ξ) :
    ∀ᶠ i in atTop, ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau t j ξ b →
      1 ≤ testDeg (cfgB (P i)) (s i) b →
      ∃ (F : Finset (Poly d)) (g : Poly d),
        (∀ f ∈ F, (f.totalDegree : ℝ) ≤ testDeg (cfgB (P i)) (s i) b) ∧
        (g.totalDegree : ℝ) ≤ testDeg (cfgB (P i)) (s i) b ∧
        (∀ Z, PoolCarrier (pl i) j Z → ∀ f ∈ F, f ∈ Z.ideal) ∧
        (∀ y : Point d, MvPolynomial.eval y g ≠ 0 → Module.finrank ℂ (jacKer F y) + j ≤ d) ∧
        ∀ X ∈ pl i, ((X.pts.filter (fun x => ¬ JacRegularAt (pl i) j F g (toC x))).card : ℝ) ≤
          θ * X.pts.card := by
  obtain ⟨θ₁, hθ₁, η, hη, ρ₀, hρ₀, _, s₁, hJac⟩ :=
    prof_regularity_jacobian_with_margin d hd θ hθ ξ hξ
  have hρ : 0 < ρ₀ / 2 := by positivity
  filter_upwards [hgood θ₁ hθ₁ η hη (ρ₀ / 2) hρ, hgrows.eventually_ge_atTop s₁] with i hi hs
  exact hJac (P i) (pl i) (s i) (ρ₀ / 2) t (by linarith) hi hs

end
end DistinctDistances.TrackD
