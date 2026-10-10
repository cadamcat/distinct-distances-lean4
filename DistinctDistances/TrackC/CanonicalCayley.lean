import DistinctDistances.TrackC.MotionCoordinates
import DistinctDistances.TrackC.RotationAxisCertificate

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

set_option maxHeartbeats 2000000 in
/-- The reversing orthogonal matrix in canonical axis coordinates has a proper
two-dimensional rotation block, motions.tex:298–302. -/
theorem canonical_reversing_block (g : Motion 3) (hrev : reverseMotion g)
    (haxis : axis g = Submodule.span ℝ {EuclideanSpace.single (2 : Fin 3) (1 : ℝ)}) :
    ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ 1 + a ≠ 0 ∧
      ∀ x : E 3, g.linearIsometryEquiv x =
        WithLp.toLp 2 ![a*x 0-b*x 1,b*x 0+a*x 1,-x 2] := by
  let S := g.linearIsometryEquiv
  let e₀ : E 3 := EuclideanSpace.single (0 : Fin 3) 1
  let e₁ : E 3 := EuclideanSpace.single (1 : Fin 3) 1
  let e₂ : E 3 := EuclideanSpace.single (2 : Fin 3) 1
  have he₂axis : e₂ ∈ axis g := by
    rw [haxis]
    exact Submodule.subset_span (Set.mem_singleton _)
  have hSe₂ : S e₂ = -e₂ := by
    have h := he₂axis
    change g.toAffineEquiv.linear.toLinearMap e₂ + e₂ = 0 at h
    have h' : S e₂ + e₂ = 0 := by
      simpa [S, AffineIsometryEquiv.linear_eq_linear_isometry] using h
    exact eq_neg_of_add_eq_zero_left h'
  have hthird₀ : (S e₀) 2 = 0 := by
    have h := S.inner_map_map e₀ e₂
    rw [hSe₂] at h
    simpa [e₀,e₂,PiLp.inner_apply,Fin.sum_univ_three,EuclideanSpace.single_apply] using h
  have hthird₁ : (S e₁) 2 = 0 := by
    have h := S.inner_map_map e₁ e₂
    rw [hSe₂] at h
    simpa [e₁,e₂,PiLp.inner_apply,Fin.sum_univ_three,EuclideanSpace.single_apply] using h
  let a : ℝ := (S e₀) 0
  let b : ℝ := (S e₀) 1
  let c : ℝ := (S e₁) 0
  let d : ℝ := (S e₁) 1
  have hnorm : a ^ 2 + b ^ 2 = 1 := by
    have h := S.inner_map_map e₀ e₀
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fin.sum_univ_three] at h
    simpa [a,b,e₀,PiLp.inner_apply,Fin.sum_univ_three,hthird₀,pow_two] using h
  have hdot : a*c+b*d = 0 := by
    have h := S.inner_map_map e₀ e₁
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fin.sum_univ_three] at h
    simpa [a,b,c,d,e₀,e₁,PiLp.inner_apply,Fin.sum_univ_three,hthird₀,hthird₁,mul_comm] using h
  have hmat : spatialIsometryMatrix S = !![a,c,0;b,d,0;0,0,-1] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [spatialIsometryMatrix,LinearMap.toMatrix_apply,homRotationStdBasis,
      EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,a,b,c,d,e₀,e₁,e₂,
      hthird₀,hthird₁,hSe₂]
  have hdetS : LinearMap.det S.toLinearMap = -1 := by
    simpa [S,reverseMotion,AffineIsometryEquiv.linear_eq_linear_isometry] using hrev
  have hdet : a*d-b*c = 1 := by
    have h := (LinearMap.det_toMatrix homRotationStdBasis S.toLinearMap).trans hdetS
    change Matrix.det (spatialIsometryMatrix S) = -1 at h
    rw [hmat] at h
    simp only [Matrix.det_fin_three] at h
    norm_num at h
    linarith
  have hc : c = -b := by
    calc
      c = c*(a^2+b^2) := by rw [hnorm,mul_one]
      _ = a*(a*c+b*d)-b*(a*d-b*c) := by ring
      _ = -b := by rw [hdot,hdet];ring
  have hd : d = a := by
    calc
      d = d*(a^2+b^2) := by rw [hnorm,mul_one]
      _ = b*(a*c+b*d)+a*(a*d-b*c) := by ring
      _ = a := by rw [hdot,hdet];ring
  have hS₀ : S e₀ = WithLp.toLp 2 ![a,b,0] := by
    ext i
    fin_cases i <;> simp [a,b,hthird₀]
  have hS₁ : S e₁ = WithLp.toLp 2 ![-b,a,0] := by
    ext i
    fin_cases i
    · simpa [c] using hc
    · simpa [d] using hd
    · simpa using hthird₁
  have hSapply (x : E 3) : S x = WithLp.toLp 2 ![a*x 0-b*x 1,b*x 0+a*x 1,-x 2] := by
    have hx : x = x 0 • e₀ + x 1 • e₁ + x 2 • e₂ := by
      ext i
      fin_cases i <;> simp [e₀,e₁,e₂,EuclideanSpace.single_apply]
    calc
      S x = S (x 0 • e₀ + x 1 • e₁ + x 2 • e₂) := congrArg S hx
      _ = _ := by
        rw [map_add,map_add,map_smul,map_smul,map_smul,hS₀,hS₁,hSe₂]
        ext i
        fin_cases i <;> simp [e₂,EuclideanSpace.single_apply] <;> ring
  have hden : 1+a ≠ 0 := by
    intro hzero
    have ha : a = -1 := by linarith
    have hb : b = 0 := by nlinarith [hnorm]
    have he₀axis : e₀ ∈ axis g := by
      change g.toAffineEquiv.linear.toLinearMap e₀ + e₀ = 0
      change S e₀+e₀ = 0
      rw [hSapply,ha,hb]
      ext i
      fin_cases i <;> simp [e₀,EuclideanSpace.single_apply]
    rw [haxis] at he₀axis
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp he₀axis
    have h := congrArg (fun v : E 3 => v 0) ht
    norm_num [e₀,EuclideanSpace.single_apply] at h
  exact ⟨a,b,hnorm,hden,hSapply⟩

set_option maxHeartbeats 1000000 in
/-- Full canonical graph data for a reversing motion with canonical axis,
motions.tex:300–314; normalization's coordinate calculation. -/
theorem canonical_reversing_graph (g : Motion 3) (hrev : reverseMotion g)
    (haxis : axis g = Submodule.span ℝ {EuclideanSpace.single (2 : Fin 3) (1 : ℝ)}) :
    ∃ s ω d₀ d₁ : ℝ, ∀ x : E 3,
      ((x+g x) 2)/2 = s ∧
      ((x-g x) 0)/2 = d₀-ω*((x+g x) 1)/2 ∧
      ((x-g x) 1)/2 = d₁+ω*((x+g x) 0)/2 := by
  obtain ⟨a,b,hnorm,hden,hS⟩ := canonical_reversing_block g hrev haxis
  let ω : ℝ := -b/(1+a)
  let h := g 0
  have hcoef₀ : 1-a = -ω*b := by
    dsimp [ω]
    field_simp [hden]
    nlinarith [hnorm]
  have hcoef₁ : b = -ω*(1+a) := by
    dsimp [ω]
    field_simp [hden]
  have hg (x : E 3) : g x = WithLp.toLp 2 ![a*x 0-b*x 1,b*x 0+a*x 1,-x 2]+h := by
    calc
      g x = g (x +ᵥ (0 : E 3)) := by simp
      _ = g.linearIsometryEquiv x +ᵥ g 0 := g.map_vadd 0 x
      _ = _ := by rw [hS];rfl
  refine ⟨h 2/2,ω,(-h 0+ω*h 1)/2,(-h 1-ω*h 0)/2,?_⟩
  intro x
  rw [hg]
  change (x 2+(-x 2+h 2))/2 = h 2/2 ∧
    (x 0-(a*x 0-b*x 1+h 0))/2 = (-h 0+ω*h 1)/2-ω*(x 1+(b*x 0+a*x 1+h 1))/2 ∧
    (x 1-(b*x 0+a*x 1+h 1))/2 = (-h 1-ω*h 0)/2+ω*(x 0+(a*x 0-b*x 1+h 0))/2
  refine ⟨by ring,?_,?_⟩
  · have h₀ := congrArg (fun q : ℝ => q*x 0) hcoef₀
    have h₁ := congrArg (fun q : ℝ => q*x 1) hcoef₁
    nlinarith only [h₀,h₁]
  · have h₀ := congrArg (fun q : ℝ => q*x 1) hcoef₀
    have h₁ := congrArg (fun q : ℝ => q*x 0) hcoef₁
    nlinarith only [h₀,h₁]

end DistinctDistances.TrackC
