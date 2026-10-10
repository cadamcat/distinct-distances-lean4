import DistinctDistances.TrackC.PartitionSigns
import DistinctDistances.TrackC.PartitionDegree
import DistinctDistances.TrackC.BisectionPolynomial

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- Iterate finite bisection on all current strict sign classes. -/
theorem iterated_sign_bisection (d : ℕ) (hd : 1 ≤ d) (S : Finset (E d)) (J : ℕ) :
    ∃ fs : List (Poly d), fs.length = J ∧ fs.prod ≠ 0 ∧
      fs.prod.totalDegree ≤ ∑ j ∈ Finset.range J, d * 2^(j/d+1) ∧
      ∀ σ : Fin fs.length → Bool,
        ((pointsIn S (factorSignCell fs σ)).card : ℝ) ≤ (S.card : ℝ) / (2 : ℝ)^J := by
  classical
  induction J with
  | zero =>
    refine ⟨[], rfl, by simp, by simp, ?_⟩
    intro σ
    simp [pointsIn]
  | succ J ih =>
    obtain ⟨fs, hlen, hprod, hdegree, hcount⟩ := ih
    let family : Finset (Finset (E d)) :=
      Finset.univ.image (fun σ : Fin fs.length → Bool => pointsIn S (factorSignCell fs σ))
    have hfamily : family.card ≤ 2^J := by
      have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin fs.length → Bool)))
        (f := fun σ => pointsIn S (factorSignCell fs σ))
      simpa [family, hlen] using h
    have hdim : family.card < Nat.choose (d * 2^(J/d+1)+d) d :=
      hfamily.trans_lt (bisection_level_dimension d J hd)
    obtain ⟨f, hf0, hfdegree, hfcount⟩ :=
      polynomial_bisection_construct d family (d * 2^(J/d+1)) hdim
    refine ⟨f::fs, by simp [hlen], by simpa using mul_ne_zero hf0 hprod, ?_, ?_⟩
    · calc
        (f::fs).prod.totalDegree ≤ f.totalDegree + fs.prod.totalDegree := MvPolynomial.totalDegree_mul _ _
        _ ≤ d * 2^(J/d+1) + ∑ j ∈ Finset.range J, d * 2^(j/d+1) := Nat.add_le_add hfdegree hdegree
        _ = ∑ j ∈ Finset.range (J+1), d * 2^(j/d+1) := by rw [Finset.sum_range_succ]; omega
    · intro σ
      let τ : Fin fs.length → Bool := fun i => σ i.succ
      let X := pointsIn S (factorSignCell fs τ)
      have hX : X ∈ family := Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, rfl⟩
      have hhalf := hfcount X hX
      have hold : (X.card : ℝ) ≤ (S.card : ℝ) / (2 : ℝ)^J := hcount τ
      have hsmall : (X.card : ℝ) / 2 ≤ (S.card : ℝ) / (2 : ℝ)^(J+1) := by
        have h := div_le_div_of_nonneg_right hold (by norm_num : (0 : ℝ) ≤ 2)
        simpa only [pow_succ, div_div] using h
      have hset : pointsIn S (factorSignCell (f::fs) σ) =
          if σ 0 then X.filter (fun x => 0 < evalR f x) else X.filter (fun x => evalR f x < 0) := by
        ext x
        cases hσ : σ 0 <;>
          simp [pointsIn, factorSignCell_cons, X, τ, hσ, and_assoc, and_comm, and_left_comm]
      rw [hset]
      cases hσ : σ 0
      · simpa [hσ] using hhalf.2.trans hsmall
      · simpa [hσ] using hhalf.1.trans hsmall

end DistinctDistances.TrackC
