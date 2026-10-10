import DistinctDistances.Bridges.ComponentLength
import DistinctDistances.TrackA.Intersections

/-! Refined Bézout bounds the number of degree-one curve components. -/

namespace DistinctDistances.Bridges

open scoped BigOperators
noncomputable section

theorem card_degree_one_components (f g : Poly 3)
    (hf : 1 ≤ f.totalDegree) (hg : 1 ≤ g.totalDegree)
    (F : AffineFamily.Family 3) (hF : AffineFamily.IsPure F 1)
    (hcomponents : ∀ V ∈ F, V.IsComponentOf (Ideal.span {f, g}))
    (hdegree : ∀ V ∈ F, V.degree = 1) :
    (F.card : ℚ) ≤ (f.totalDegree : ℚ) * g.totalDegree := by
  classical
  let fs : Fin 2 → Poly 3 := ![f, g]
  have hfs : ∀ i, 1 ≤ (fs i).totalDegree := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  have hspan : Ideal.span (Set.range fs) = Ideal.span ({f, g} : Set (Poly 3)) := by
    congr 1
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
  have hcomps : ∀ V ∈ F, V.IsComponentOf (Ideal.span (Set.range fs)) := by
    simpa only [hspan] using hcomponents
  calc
    (F.card : ℚ) = ∑ V ∈ F, (1 : ℚ) := by simp
    _ = ∑ V ∈ F, V.degree := by
      apply Finset.sum_congr rfl
      intro V hV
      exact (hdegree V hV).symm
    _ ≤ ∏ i, ((fs i).totalDegree : ℚ) :=
      TrackA.fa_bezout_components (n := 3) (c := 2) (by decide) fs hfs F hF hcomps
    _ = (f.totalDegree : ℚ) * g.totalDegree := by simp [fs, Fin.prod_univ_two]

end
end DistinctDistances.Bridges
