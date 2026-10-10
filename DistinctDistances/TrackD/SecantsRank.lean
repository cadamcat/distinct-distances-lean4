import DistinctDistances.TrackD.Basic
import DistinctDistances.TrackD.PairGenericity
import DistinctDistances.TrackD.GenericTangent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace DistinctDistances.TrackD

noncomputable section
variable {d : ℕ}

/-- `secants.tex:75–87`: the tangent inclusion modulo a transverse connecting line
compares dimensions, and equal dimensions make the projected tangent spaces equal. -/
theorem secant_rank_conclusion (TX TY : Submodule ℂ (Point d)) (v : Point d)
    (hTX : v ∉ TX) (hTY : v ∉ TY) (hinc : TX ≤ TY ⊔ (ℂ ∙ v)) :
    Module.finrank ℂ TX ≤ Module.finrank ℂ TY ∧
      (Module.finrank ℂ TX = Module.finrank ℂ TY →
        TX ⊔ (ℂ ∙ v) = TY ⊔ (ℂ ∙ v)) := by
  have hle : TX ⊔ (ℂ ∙ v) ≤ TY ⊔ (ℂ ∙ v) := sup_le hinc le_sup_right
  have hrX : Module.finrank ℂ ↥(TX ⊔ (ℂ ∙ v)) = Module.finrank ℂ TX + 1 :=
    Submodule.finrank_sup_span_singleton hTX
  have hrY : Module.finrank ℂ ↥(TY ⊔ (ℂ ∙ v)) = Module.finrank ℂ TY + 1 :=
    Submodule.finrank_sup_span_singleton hTY
  constructor
  · have hm := Submodule.finrank_mono hle
    omega
  · intro hdim
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hrX, hrY, hdim])

/-- The final generic rank step in `secants.tex:75–87`, with the label-image
tangent inclusion kept as an explicit geometric input. All principal-open
conditions are combined before choosing a witness. -/
theorem generic_secant_rank (X Y : AffineVariety d) (k l : ℕ)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hk : X.dimension = k) (hl : Y.dimension = l)
    (htr : ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y))
    (hinc : ForGeneralPair X Y (fun x y =>
      X.tangentSpace x ≤ Y.tangentSpace y ⊔ (ℂ ∙ (y - x)))) :
    k ≤ l ∧ (k = l → ForGeneralPair X Y (fun x y =>
      X.tangentSpace x ⊔ (ℂ ∙ (y - x)) = Y.tangentSpace y ⊔ (ℂ ∙ (y - x)))) := by
  obtain ⟨x₀, hx₀, y₀, hy₀, _⟩ := htr.exists
  have hdX : ForGeneralPoint X (fun x => Module.finrank ℂ (X.tangentSpace x) = k) := by
    simpa only [hk] using general_tangent_finrank X hX
  have hdY : ForGeneralPoint Y (fun y => Module.finrank ℂ (Y.tangentSpace y) = l) := by
    simpa only [hl] using general_tangent_finrank Y hY
  have hdata := (((htr.and hX hY hinc).and hX hY (hdX.on_left ⟨y₀, hy₀⟩)).and
    hX hY (hdY.on_right ⟨x₀, hx₀⟩))
  have hle : k ≤ l := by
    obtain ⟨x, hx, y, hy, ⟨⟨⟨htrans, hi⟩, hdx⟩, hdy⟩⟩ := hdata.exists
    have h := (secant_rank_conclusion (X.tangentSpace x) (Y.tangentSpace y)
      (y - x) htrans.1 htrans.2 hi).1
    simpa only [hdx, hdy] using h
  refine ⟨hle, ?_⟩
  intro heq
  apply hdata.mono
  intro x hx y hy h
  rcases h with ⟨⟨⟨htrans, hi⟩, hdx⟩, hdy⟩
  apply (secant_rank_conclusion (X.tangentSpace x) (Y.tangentSpace y)
    (y - x) htrans.1 htrans.2 hi).2
  rw [hdx, hdy, heq]

end
end DistinctDistances.TrackD
