import DistinctDistances.TrackC.MotionGeometry
import DistinctDistances.TrackC.CanonicalNullFlat

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Canonical-axis graph data give the null motion flat and graph-dual arrangement consumed by propagation. -/
theorem canonical_motion_flat_model (g : Motion 3) (S : Finset (E 3)) (s ω d₀ d₁ : ℝ)
    (T : E 3 ≃ᵃ[ℝ] E 3)
    (hT : ∀ x ∈ S,T x = WithLp.toLp 2 ![((x+g x) 0)/2,((x+g x) 1)/2,((x-g x) 2)/2])
    (hgraph : ∀ x ∈ S,((x+g x) 2)/2 = s ∧
      ((x-g x) 0)/2 = d₀-ω*((x+g x) 1)/2 ∧
      ((x-g x) 1)/2 = d₁+ω*((x+g x) 0)/2)
    (hproj : ∀ x ∈ S,∀ y ∈ S,∀ z ∈ S,¬Collinear ℝ ({x,y,z}:Set (E 3)) →
      ¬Collinear ℝ ({WithLp.toLp 2 ![T x 0,T x 1],WithLp.toLp 2 ![T y 0,T y 1],
        WithLp.toLp 2 ![T z 0,T z 1]}:Set (E 2))) :
    ∃ G : Flat 6 3,MotionFlatModel g S G := by
  obtain ⟨G,hRange,hNull⟩ := canonical_motion_null_flat s ω d₀ d₁
  let φ := canonicalMotionParameter s ω d₀ d₁
  have hφ : Function.Injective φ := canonicalMotionParameter_injective s ω d₀ d₁
  have hnull : maximalNull G := by
    intro v hv
    exact hNull v hv
  refine ⟨G,hnull,T,φ,hφ,hRange.symm,?_,hproj⟩
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

/-- Full canonical graph data uniquely recover the physical rigid motion. -/
theorem canonical_motion_graph_unique (g h : Motion 3) (s ω d₀ d₁ : ℝ)
    (hg : ∀ x : E 3,((x+g x) 2)/2 = s ∧
      ((x-g x) 0)/2 = d₀-ω*((x+g x) 1)/2 ∧
      ((x-g x) 1)/2 = d₁+ω*((x+g x) 0)/2)
    (hh : ∀ x : E 3,((x+h x) 2)/2 = s ∧
      ((x-h x) 0)/2 = d₀-ω*((x+h x) 1)/2 ∧
      ((x-h x) 1)/2 = d₁+ω*((x+h x) 0)/2) : g = h := by
  ext x : 1
  obtain ⟨hg₂,hg₀,hg₁⟩ := hg x
  obtain ⟨hh₂,hh₀,hh₁⟩ := hh x
  simp only [PiLp.add_apply,PiLp.sub_apply] at hg₂ hg₀ hg₁ hh₂ hh₀ hh₁
  have he₀ : (g x) 0-(h x) 0 = ω*((g x) 1-(h x) 1) := by linarith
  have he₁ : (g x) 1-(h x) 1 = -ω*((g x) 0-(h x) 0) := by linarith
  have hd₀ : (g x) 0 = (h x) 0 := by
    rw [he₁] at he₀
    have hp : (1+ω^2)*((g x) 0-(h x) 0) = 0 := by nlinarith only [he₀]
    have hn : (1+ω^2) ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg ω])
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hn)
  have hd₁ : (g x) 1 = (h x) 1 := by rw [hd₀,sub_self,mul_zero] at he₁;exact sub_eq_zero.mp he₁
  have hd₂ : (g x) 2 = (h x) 2 := by linarith
  apply PiLp.ext
  intro i
  fin_cases i <;> assumption

/-- Every canonical graph pair has a nonempty section in its motion-parameter flat. -/
theorem canonical_motion_pair_section_nonempty (g : Motion 3) (x : E 3)
    (s ω d₀ d₁ : ℝ)
    (hgraph : ((x+g x) 2)/2 = s ∧
      ((x-g x) 0)/2 = d₀-ω*((x+g x) 1)/2 ∧
      ((x-g x) 1)/2 = d₁+ω*((x+g x) 0)/2) :
    (pairFlatSet x (g x) ∩ Set.range (canonicalMotionParameter s ω d₀ d₁)).Nonempty := by
  let u : E 3 := WithLp.toLp 2 ![0,0,(x-g x) 2/2]
  refine ⟨canonicalMotionParameter s ω d₀ d₁ u,?_,Set.mem_range_self u⟩
  change (1/2:ℝ) • (x-g x) =
    cross3 (wCoord (canonicalMotionParameter s ω d₀ d₁ u)) ((1/2:ℝ) • (x+g x)) +
      cCoord (canonicalMotionParameter s ω d₀ d₁ u)
  obtain ⟨hs,h₀,h₁⟩ := hgraph
  simp only [PiLp.add_apply,PiLp.sub_apply] at hs h₀ h₁
  ext i
  fin_cases i <;>
    simp [u,canonicalMotionParameter,wCoord,cCoord,cross3,PiLp.smul_apply,smul_eq_mul] <;>
    nlinarith

/-- Distinct motions in a common canonical-axis chart have distinct pair-flat sections. -/
theorem canonical_motion_pair_sections_distinct (g h : Motion 3) (x : E 3)
    (s ω d₀ d₁ s' ω' d₀' d₁' : ℝ)
    (hg : ∀ a : E 3,((a+g a) 2)/2 = s ∧
      ((a-g a) 0)/2 = d₀-ω*((a+g a) 1)/2 ∧
      ((a-g a) 1)/2 = d₁+ω*((a+g a) 0)/2)
    (hh : ∀ a : E 3,((a+h a) 2)/2 = s' ∧
      ((a-h a) 0)/2 = d₀'-ω'*((a+h a) 1)/2 ∧
      ((a-h a) 1)/2 = d₁'+ω'*((a+h a) 0)/2)
    (hx : g x = h x) (hne : g ≠ h) :
    pairFlatSet x (g x) ∩ Set.range (canonicalMotionParameter s ω d₀ d₁) ≠
      pairFlatSet x (g x) ∩ Set.range (canonicalMotionParameter s' ω' d₀' d₁') := by
  intro heq
  obtain ⟨z,hzPair,⟨u,hu⟩⟩ := canonical_motion_pair_section_nonempty g x s ω d₀ d₁ (hg x)
  have hz' : z ∈ Set.range (canonicalMotionParameter s' ω' d₀' d₁') := by
    have hz : z ∈ pairFlatSet x (g x) ∩ Set.range (canonicalMotionParameter s ω d₀ d₁) :=
      ⟨hzPair,u,hu⟩
    rw [heq] at hz
    exact hz.2
  obtain ⟨v,hv⟩ := hz'
  have hω : ω = ω' := by
    have hcoord := congrArg (fun a : E 6 => a 2) (hu.trans hv.symm)
    simpa [canonicalMotionParameter] using hcoord
  obtain ⟨hgs,hg₀,hg₁⟩ := hg x
  obtain ⟨hhs,hh₀,hh₁⟩ := hh x
  rw [← hx] at hhs hh₀ hh₁
  have hs : s = s' := hgs.symm.trans hhs
  have hd₀ : d₀ = d₀' := by rw [hω] at hg₀;linarith
  have hd₁ : d₁ = d₁' := by rw [hω] at hg₁;linarith
  rw [← hs,← hω,← hd₀,← hd₁] at hh
  exact hne (canonical_motion_graph_unique g h s ω d₀ d₁ hg hh)

end DistinctDistances.TrackC
