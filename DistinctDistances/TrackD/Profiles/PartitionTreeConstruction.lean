import DistinctDistances.TrackD.Profiles.PartitionTreeStep

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

/-- Construct the forest by induction on the finite number of remaining
time/dimension events. Children add a cut; residuals advance time. -/
theorem partition_grid_forest_exists (grid : Fin G → ℝ) (hgrid : StrictMono grid)
    (L : Fin G → ℕ) (s u : ℝ) (hu : 0 < u) (a : Fin (G * d) → ℝ)
    (ha : ∀ i, u ≤ a i)
    (htail : ∀ i, (∑ k ∈ Finset.univ.filter (fun k : Fin (G * d) => i < k), a k) ≤ a i / 9)
    (r : Fin G) (S S₀ : Finset (Pt d)) (hsubset : S ⊆ S₀)
    (E : Set (Poly d))
    (hdegree : ∀ f ∈ E, f.totalDegree ≤ L ⟨G - 1, by have := r.isLt; omega⟩)
    (hisolate : MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (S₀ : Set (Pt d)))
    (π : CutPath d) (j : ℕ) (hj : j ≤ d)
    (hvan : ∀ x ∈ S, ∀ i : Fin d, i.val < j → MvPolynomial.eval (toC x) (π.cut i) = 0)
    (hproper : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      ∀ Z ∈ π.localCarriers i.val (toC x), π.cut i ∉ Z.ideal)
    (hmono : ∀ i k : Fin d, i.val < j → k.val < j → i ≤ k → π.time i ≤ π.time k)
    (hfinal : ∀ i : Fin d, i.val < j → π.time i ≤ grid r) :
    Nonempty (PartitionGridForest grid L s u a r π j S) := by
  classical
  have ha0 : ∀ i, 0 ≤ a i := fun i => hu.le.trans (ha i)
  have hbound (r' : Fin G) (j' : ℕ) (hj' : j' ≤ d) : r'.val * d + j' ≤ G * d := by
    calc
      r'.val * d + j' ≤ r'.val * d + d := Nat.add_le_add_left hj' _
      _ = (r'.val + 1) * d := by ring
      _ ≤ G * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt r'.isLt)
  have main : ∀ n : ℕ, ∀ (r' : Fin G) (π' : CutPath d) (j' : ℕ) (T : Finset (Pt d)),
      G * d - (r'.val * d + j') = n → j' ≤ d → T ⊆ S₀ →
      (∀ x ∈ T, ∀ i : Fin d, i.val < j' → MvPolynomial.eval (toC x) (π'.cut i) = 0) →
      (∀ x ∈ T, ∀ i : Fin d, i.val < j' →
        ∀ Z ∈ π'.localCarriers i.val (toC x), π'.cut i ∉ Z.ideal) →
      (∀ i k : Fin d, i.val < j' → k.val < j' → i ≤ k → π'.time i ≤ π'.time k) →
      (∀ i : Fin d, i.val < j' → π'.time i ≤ grid r') →
      Nonempty (PartitionGridForest grid L s u a r' π' j' T) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro r' π' j' T hmeasure hj' hsub hvan' hproper' hmono' hfinal'
        by_cases hne : T.Nonempty
        · by_cases hjdone : j' = d
          · subst j'
            exact partition_complete_prefix_forest grid hgrid.monotone L s u a ha0 r' π' T hne
              (fun i k hik => hmono' i k i.isLt k.isLt hik)
              (fun x hx i => hvan' x hx i i.isLt)
              (fun x hx i Z hZ => hproper' x hx i i.isLt Z hZ)
              (fun i => hfinal' i i.isLt)
          · have hjlt : j' < d := by omega
            by_cases hnext : r'.val + 1 < G
            · apply partition_grid_forest_step grid hgrid L s u hu a ha htail r' π' j'
                hjlt hnext T S₀ hne hsub hvan' hproper' hmono' hfinal'
              intro r'' π'' j'' U hprogress hj'' hsub'' hvan'' hproper'' hmono'' hfinal''
              have hless : G * d - (r''.val * d + j'') < n := by
                have hb := hbound r'' j'' hj''
                have hb' := hbound r' j' hj'
                omega
              exact ih _ hless r'' π'' j'' U rfl hj'' hsub'' hvan'' hproper'' hmono'' hfinal''
            · have hlast : r' = (⟨G - 1, by have := r'.isLt; omega⟩ : Fin G) := by
                apply Fin.ext
                change r'.val = G - 1
                have := r'.isLt
                omega
              have hdegree' : ∀ f ∈ E, f.totalDegree ≤ L r' := by
                intro f hf
                rw [hlast]
                exact hdegree f hf
              exact partition_finish_node_forest grid hgrid.monotone L s u a ha0 r' T S₀ hne
                hsub E hdegree' hisolate π' j' hj' hvan' hproper' hmono' hfinal'
        · have hTempty := Finset.not_nonempty_iff_eq_empty.mp hne
          subst T
          exact partition_empty_forest grid L s u a r' π' j'
  exact main _ r π j S rfl hj hsubset hvan hproper hmono hfinal

end
end DistinctDistances.TrackD
