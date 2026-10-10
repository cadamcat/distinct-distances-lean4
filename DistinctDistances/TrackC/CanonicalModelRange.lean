import DistinctDistances.TrackC.CanonicalMotionModel

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Retain the canonical parameter range for the global distinctness proof.
The original frozen model theorem exposes only the model predicate. -/
theorem canonical_motion_flat_model_with_range (g : Motion 3) (S : Finset (E 3)) (s ω d₀ d₁ : ℝ)
    (T : E 3 ≃ᵃ[ℝ] E 3)
    (hT : ∀ x ∈ S,T x = WithLp.toLp 2 ![((x+g x) 0)/2,((x+g x) 1)/2,((x-g x) 2)/2])
    (hgraph : ∀ x ∈ S,((x+g x) 2)/2 = s ∧
      ((x-g x) 0)/2 = d₀-ω*((x+g x) 1)/2 ∧
      ((x-g x) 1)/2 = d₁+ω*((x+g x) 0)/2)
    (hproj : ∀ x ∈ S,∀ y ∈ S,∀ z ∈ S,¬Collinear ℝ ({x,y,z}:Set (E 3)) →
      ¬Collinear ℝ ({WithLp.toLp 2 ![T x 0,T x 1],WithLp.toLp 2 ![T y 0,T y 1],
        WithLp.toLp 2 ![T z 0,T z 1]}:Set (E 2))) :
    ∃ G : Flat 6 3,(G.1 : Set (E 6)) = Set.range (canonicalMotionParameter s ω d₀ d₁) ∧
      MotionFlatModel g S G := by
  obtain ⟨G,hRange,hNull⟩ := canonical_motion_null_flat s ω d₀ d₁
  let φ := canonicalMotionParameter s ω d₀ d₁
  have hφ : Function.Injective φ := canonicalMotionParameter_injective s ω d₀ d₁
  have hnull : maximalNull G := by
    intro v hv
    exact hNull v hv
  refine ⟨G,hRange,hnull,T,φ,hφ,hRange.symm,?_,hproj⟩
  intro x hx
  let v : E 3 := (1/2:ℝ) • (x+g x)
  let b : E 3 := (1/2:ℝ) • (x-g x)
  obtain ⟨hv,hb₀,hb₁⟩ := hgraph x hx
  have hv' : v 2 = s := by
    dsimp [v]
    convert hv using 1 <;> simp only [PiLp.smul_apply,PiLp.add_apply,smul_eq_mul] <;> ring
  have hb₀' : b 0 = d₀-ω*v 1 := by
    dsimp [v,b]
    convert hb₀ using 1 <;> simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul] <;> ring
  have hb₁' : b 1 = d₁+ω*v 0 := by
    dsimp [v,b]
    convert hb₁ using 1 <;> simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul] <;> ring
  have hpair : ∀ u : E 3,φ u ∈ pairFlatSet x (g x) ↔ u ∈ graphDualPlane (T x) := by
    intro u
    have heq := canonical_motion_pair_equation s ω d₀ d₁ v b u hv' hb₀' hb₁'
    have hleft : φ u ∈ pairFlatSet x (g x) ↔
        b 0 = (φ u) 1*v 2-(φ u) 2*v 1+(φ u) 3 ∧
        b 1 = (φ u) 2*v 0-(φ u) 0*v 2+(φ u) 4 ∧
        b 2 = (φ u) 0*v 1-(φ u) 1*v 0+(φ u) 5 := by
      change b = cross3 (wCoord (φ u)) v+cCoord (φ u) ↔ _
      constructor
      · intro h
        have h₀ := congrArg (fun y : E 3 => y 0) h
        have h₁ := congrArg (fun y : E 3 => y 1) h
        have h₂ := congrArg (fun y : E 3 => y 2) h
        simpa [wCoord,cCoord,cross3] using And.intro h₀ (And.intro h₁ h₂)
      · rintro ⟨h₀,h₁,h₂⟩
        ext i
        fin_cases i
        · simpa [wCoord,cCoord,cross3] using h₀
        · simpa [wCoord,cCoord,cross3] using h₁
        · simpa [wCoord,cCoord,cross3] using h₂
    have hright : u 2+u 0*v 0+u 1*v 1 = b 2 ↔ u ∈ graphDualPlane (T x) := by
      rw [hT x hx]
      change _ ↔ u 2+u 0*((x+g x) 0/2)+u 1*((x+g x) 1/2) = (x-g x) 2/2
      simp only [v,b,PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
      constructor <;> intro h <;> nlinarith
    exact hleft.trans (heq.trans hright)
  ext z
  constructor
  · intro hz
    have hzG : z ∈ Set.range φ := by rw [hRange] at hz;exact hz.2
    obtain ⟨u,rfl⟩ := hzG
    exact ⟨u,(hpair u).mp hz.1,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    refine ⟨(hpair u).mpr hu,?_⟩
    rw [hRange]
    exact Set.mem_range_self u

end DistinctDistances.TrackC
