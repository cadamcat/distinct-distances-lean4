import DistinctDistances.TrackA.HomogeneousRankSupport
import DistinctDistances.OAIInterface.DeterminantHomogeneous

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

theorem jacobian_minor_homogeneous {n : ℕ} (E : List (Poly n)) (D q : ℕ)
    (hE : ∀ f ∈ E, f.IsHomogeneous D) (m : Poly n) (hm : m ∈ jacobianMinors E q) :
    m.IsHomogeneous (q*(D-1)) := by
  obtain ⟨rows, cols, rfl⟩ := hm
  have h := OAI.PermanentBorder.CI.det_homogeneous
    ((jacobian E).submatrix rows cols) (fun _ => D-1)
    (fun i j => (hE (E.get (rows i)) (List.get_mem _ _)).pderiv)
  simpa using h

theorem choose_homogeneous_jacobian_certificate {n : ℕ} (good : AffineFamily.Family n)
    (E : List (Poly n)) (k D : ℕ) (hk : k ≤ n)
    (hE : ∀ f ∈ E, f.IsHomogeneous D)
    (hwitness : ∀ V ∈ good, ∃ m ∈ jacobianMinors E (n-k), m ∉ V.ideal) :
    ∃ g : Poly n, g.totalDegree ≤ n*D ∧ g.IsHomogeneous ((n-k)*(D-1)) ∧
      g ∈ Submodule.span ℂ (jacobianMinors E (n-k)) ∧ ∀ V ∈ good, g ∉ V.ideal := by
  obtain ⟨g, hd, hsp, hg⟩ := choose_jacobian_certificate good E k D hk
    (fun f hf => (hE f hf).totalDegree_le) hwitness
  have hle : Submodule.span ℂ (jacobianMinors E (n-k)) ≤
      MvPolynomial.homogeneousSubmodule (Fin n) ℂ ((n-k)*(D-1)) := by
    apply Submodule.span_le.mpr
    intro m hm
    exact jacobian_minor_homogeneous E D (n-k) hE m hm
  exact ⟨g, hd, hle hsp, hsp, hg⟩

end
end DistinctDistances.TrackA
