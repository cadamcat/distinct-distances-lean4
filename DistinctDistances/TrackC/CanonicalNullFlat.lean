import DistinctDistances.TrackC.Basic

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def canonicalMotionLinear (s : ℝ) : E 3 →ₗ[ℝ] E 6 where
  toFun u := WithLp.toLp 2 ![u 1,-u 0,0,s*u 0,s*u 1,u 2]
  map_add' u v := by ext i;fin_cases i <;> simp [mul_add] <;> ring
  map_smul' a u := by ext i;fin_cases i <;> simp [mul_comm,mul_left_comm,mul_assoc]

def canonicalMotionParameter (s ω d₀ d₁ : ℝ) : E 3 →ᵃ[ℝ] E 6 where
  toFun u := WithLp.toLp 2 ![u 1,-u 0,ω,d₀+s*u 0,d₁+s*u 1,u 2]
  linear := canonicalMotionLinear s
  map_vadd' u v := by ext i;fin_cases i <;> simp [canonicalMotionLinear,mul_add] <;> ring

theorem canonicalMotionLinear_injective (s : ℝ) : Function.Injective (canonicalMotionLinear s) := by
  intro u v huv
  have h₀ := congrArg (fun z : E 6 => z 1) huv
  have h₁ := congrArg (fun z : E 6 => z 0) huv
  have h₂ := congrArg (fun z : E 6 => z 5) huv
  simp [canonicalMotionLinear] at h₀ h₁ h₂
  ext i
  fin_cases i <;> assumption

theorem canonicalMotionParameter_injective (s ω d₀ d₁ : ℝ) : Function.Injective (canonicalMotionParameter s ω d₀ d₁) := by
  exact (canonicalMotionParameter s ω d₀ d₁).linear_injective_iff.mp (canonicalMotionLinear_injective s)

/-- Canonical-axis motion parameters produce a maximal null affine three-flat. -/
theorem canonical_motion_null_flat (s ω d₀ d₁ : ℝ) :
    ∃ G : Flat 6 3,(G.1:Set (E 6)) = Set.range (canonicalMotionParameter s ω d₀ d₁) ∧
      ∀ z ∈ G.1.direction,(∑ i : Fin 3,z (i.castAdd 3)*z (i.natAdd 3)) = 0 := by
  let φ := canonicalMotionParameter s ω d₀ d₁
  let G := (⊤:AffineSubspace ℝ (E 3)).map φ
  have hGne : (G:Set (E 6)).Nonempty := ⟨φ 0,Set.mem_image_of_mem φ (by simp)⟩
  have hdim : Module.finrank ℝ G.direction = 3 := by
    rw [AffineSubspace.map_direction,AffineSubspace.direction_top,Submodule.map_top]
    exact (LinearMap.finrank_range_of_inj (canonicalMotionLinear_injective s)).trans (by simp [E])
  refine ⟨⟨G,hGne,hdim⟩,?_,?_⟩
  · change φ '' (Set.univ:Set (E 3)) = Set.range φ
    exact Set.image_univ
  · intro z hz
    change z ∈ G.direction at hz
    rw [AffineSubspace.map_direction,AffineSubspace.direction_top,Submodule.map_top] at hz
    obtain ⟨u,rfl⟩ := hz
    simp [φ,canonicalMotionParameter,canonicalMotionLinear,Fin.sum_univ_three]
    ring

/-- In the canonical axis coordinates, the pair-flat equation is exactly the graph-dual plane equation. -/
theorem canonical_motion_pair_equation (s ω d₀ d₁ : ℝ) (v b u : E 3)
    (hV : v 2 = s) (hB₀ : b 0 = d₀-ω*v 1) (hB₁ : b 1 = d₁+ω*v 0) :
    let z := canonicalMotionParameter s ω d₀ d₁ u
    (b 0 = z 1*v 2-z 2*v 1+z 3 ∧
      b 1 = z 2*v 0-z 0*v 2+z 4 ∧
      b 2 = z 0*v 1-z 1*v 0+z 5) ↔ u 2+u 0*v 0+u 1*v 1 = b 2 := by
  dsimp [canonicalMotionParameter]
  rw [hV,hB₀,hB₁]
  constructor <;> intro h
  · nlinarith [h.2.2]
  · refine ⟨by ring,by ring,?_⟩
    nlinarith

/-- Three transverse graph-dual directions kill a canonical null-flat direction. -/
theorem canonical_motion_direction_transverse (s : ℝ) (v₀ v₁ v₂ : E 3) (z : E 6)
    (hz : z ∈ LinearMap.range (canonicalMotionLinear s))
    (hdet : Matrix.det !![v₀ 0,v₀ 1,1;v₁ 0,v₁ 1,1;v₂ 0,v₂ 1,1] ≠ 0)
    (h₀ : z 5+(-z 1)*v₀ 0+z 0*v₀ 1 = 0)
    (h₁ : z 5+(-z 1)*v₁ 0+z 0*v₁ 1 = 0)
    (h₂ : z 5+(-z 1)*v₂ 0+z 0*v₂ 1 = 0) : z = 0 := by
  obtain ⟨u,rfl⟩ := hz
  simp [canonicalMotionLinear] at h₀ h₁ h₂
  have hu : u = 0 := by
    by_contra hne
    have hv : (WithLp.ofLp u : Fin 3 → ℝ) ≠ 0 := by
      intro hz
      apply hne
      ext i
      exact congrFun hz i
    have hmul : Matrix.mulVec !![v₀ 0,v₀ 1,1;v₁ 0,v₁ 1,1;v₂ 0,v₂ 1,1] (WithLp.ofLp u) = 0 := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three] <;> nlinarith
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨WithLp.ofLp u,hv,hmul⟩)
  rw [hu,map_zero]

/-- The canonical null-flat range recovers all four motion parameters. -/
theorem canonical_motion_range_parameters (s ω d₀ d₁ s' ω' d₀' d₁' : ℝ)
    (hRange : Set.range (canonicalMotionParameter s ω d₀ d₁) =
      Set.range (canonicalMotionParameter s' ω' d₀' d₁')) :
    s = s' ∧ ω = ω' ∧ d₀ = d₀' ∧ d₁ = d₁' := by
  have hzero : canonicalMotionParameter s ω d₀ d₁ 0 ∈ Set.range (canonicalMotionParameter s' ω' d₀' d₁') := by
    rw [← hRange]
    exact Set.mem_range_self 0
  obtain ⟨u,hu⟩ := hzero
  have hu₀ := congrArg (fun z : E 6 => z 1) hu
  have hu₁ := congrArg (fun z : E 6 => z 0) hu
  simp [canonicalMotionParameter] at hu₀ hu₁
  have hω := congrArg (fun z : E 6 => z 2) hu
  have hd₀ := congrArg (fun z : E 6 => z 3) hu
  have hd₁ := congrArg (fun z : E 6 => z 4) hu
  simp [canonicalMotionParameter,hu₀,hu₁] at hω hd₀ hd₁
  let e : E 3 := EuclideanSpace.single (0:Fin 3) 1
  have hone : canonicalMotionParameter s ω d₀ d₁ e ∈ Set.range (canonicalMotionParameter s' ω' d₀' d₁') := by
    rw [← hRange]
    exact Set.mem_range_self e
  obtain ⟨v,hv⟩ := hone
  have hv₀ := congrArg (fun z : E 6 => z 1) hv
  simp [canonicalMotionParameter,e] at hv₀
  have hs := congrArg (fun z : E 6 => z 3) hv
  simp [canonicalMotionParameter,e,hv₀] at hs
  exact ⟨by linarith, hω.symm,hd₀.symm,hd₁.symm⟩

end DistinctDistances.TrackC
