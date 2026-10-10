import DistinctDistances.TrackC.LineParameter
import DistinctDistances.TrackC.SignInterval
import DistinctDistances.TrackC.RootIntervals

open Classical

namespace DistinctDistances.TrackC

/-- A line not contained in the product zero set meets at most degree+1
strict sign cells, without a connected-cell topology model. -/
theorem partition_line_crossing (d : ℕ) (fs : List (Poly d)) (cells : Finset (Set (E d)))
    (hcells : ∀ R ∈ cells, ∃ σ, R = factorSignCell fs σ)
    (hdisj : ∀ R ∈ cells, ∀ R' ∈ cells, R ≠ R' → Disjoint R R')
    (l : Line d) (hn : ¬ onPolynomial fs.prod l) :
    (cells.filter (fun R => (R ∩ (l.1 : Set (E d))).Nonempty)).card ≤ fs.prod.totalDegree+1 := by
  classical
  obtain ⟨x, v, hv0, hrange, hinj⟩ := affine_line_parameter d l
  let C := cells.filter (fun R => (R ∩ (l.1 : Set (E d))).Nonempty)
  have hex (R : {R : Set (E d) // R ∈ C}) : ∃ t : ℝ, x+t • v ∈ R.val := by
    obtain ⟨y, hyR, hyl⟩ := (Finset.mem_filter.mp R.property).2
    have hy : y ∈ Set.range (fun t : ℝ => x+t • v) := hrange.symm ▸ hyl
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, hyR⟩
  choose t ht using hex
  have htinj : Function.Injective t := by
    intro R R' hteq
    apply Subtype.ext
    by_contra hRR
    have h := hdisj R.val (Finset.mem_filter.mp R.property).1
      R'.val (Finset.mem_filter.mp R'.property).1 hRR
    have hp := ht R'
    rw [← hteq] at hp
    exact Set.disjoint_left.mp h (ht R) hp
  let T : Finset ℝ := Finset.univ.image t
  let p := linePolynomial d fs.prod x v
  have hp : p ≠ 0 := linePolynomial_ne_zero_of_range d fs.prod l x v hrange hn
  have hroot : ∀ a ∈ T, ∀ b ∈ T, a < b → ∃ u : ℝ, a < u ∧ u < b ∧ p.IsRoot u := by
    intro a ha b hb hab
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp hb
    have hRR : R.val ≠ R'.val := by
      intro h
      have he : R = R' := Subtype.ext h
      rw [he] at hab
      exact lt_irrefl _ hab
    obtain ⟨σ, hσ⟩ := hcells R.val (Finset.mem_filter.mp R.property).1
    obtain ⟨τ, hτ⟩ := hcells R'.val (Finset.mem_filter.mp R'.property).1
    have hστ : σ ≠ τ := by
      intro h
      apply hRR
      rw [hσ, hτ, h]
    have haσ : x+t R • v ∈ factorSignCell fs σ := hσ ▸ ht R
    have hbτ : x+t R' • v ∈ factorSignCell fs τ := hτ ▸ ht R'
    exact factor_sign_interval_root d fs x v (t R) (t R') hab σ τ hστ haσ hbτ
  have hbound := polynomial_sign_sample_bound p hp T hroot
  have hcard : T.card = C.card := by
    rw [Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_coe]
  have hdegree := linePolynomial_natDegree_le d fs.prod x v
  rw [hcard] at hbound
  exact hbound.trans (Nat.add_le_add_right hdegree 1)

end DistinctDistances.TrackC
