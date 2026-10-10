import DistinctDistances.TrackC.PolynomialCore
import DistinctDistances.TrackC.LinearPlanes

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

theorem pointsOn_sdiff_add (S T : Finset (E 3)) (hT : T ⊆ S) (l : Line 3) :
    (pointsOn (S \ T) l).card+(pointsOn T l).card = (pointsOn S l).card := by
  have hs : pointsOn T l ⊆ pointsOn S l := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hT (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
  have heq : pointsOn (S \ T) l = pointsOn S l \ pointsOn T l := by
    ext x
    simp only [pointsOn,Finset.mem_filter,Finset.mem_sdiff]
    tauto
  rw [heq]
  exact Finset.card_sdiff_add_card_eq_card hs

/-- The geometric forcing step in the uniform rich-line argument, with line censuses explicit. -/
theorem polynomial_uniform_plane_forcing (f : Poly 3) (hf : f ≠ 0) (hsq : Squarefree f)
    (L : Finset (Line 3)) (S : Finset (E 3)) (B : ℝ) (k : ℕ)
    (hL : L.Nonempty) (hs : (0:ℝ) < S.card) (hk : 3 ≤ k) (hB : 0 ≤ B) (hcap : planeCap L B)
    (hS : ∀ x ∈ S,k ≤ lineMultiplicity L x ∧ lineMultiplicity L x ≤ 2*k)
    (hUniform : (L.card:ℝ)/100 ≤ ((L.filter (fun l => (S.card:ℝ)*k/(100*(L.card:ℝ)) ≤
      (pointsOn S l).card)).card:ℝ))
    (hoff : cloudMass S (zeroSet f)ᶜ ≤ (S.card:ℝ)/1000000)
    (hD : (f.totalDegree:ℝ) ≤ (S.card:ℝ)*k/(100000000*(L.card:ℝ)))
    (hDsq : (f.totalDegree:ℝ)^2 ≤ (L.card:ℝ)/1000000)
    (hcritical : FiniteCardBound {l : Line 3 | criticalLine f l} ((f.totalDegree:ℝ)^2))
    (hflat : FiniteCardBound {l : Line 3 | flatLine f l ∧ ¬inPlaneComponent f l} (3*(f.totalDegree:ℝ)^2)) :
    (L.card:ℝ)/400 ≤ (f.totalDegree:ℝ)*B := by
  have hLpos : (0:ℝ) < L.card := by exact_mod_cast Finset.card_pos.mpr hL
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let T := polynomialCore f L S
  let U := S \ T
  have hTsub : T ⊆ S := polynomialCore_subset f L S
  have hUsub : U ⊆ S := Finset.sdiff_subset
  have hU : (U.card:ℝ) ≤ 2*(S.card:ℝ)/1000000 := by
    have hcore := polynomialCore_discard_bound f L S k hk (fun x hx => (hS x hx).1)
    have hroot : 3*(L.card:ℝ)*f.totalDegree/k ≤ (S.card:ℝ)/1000000 := by
      calc
        _ ≤ 3*(L.card:ℝ)*((S.card:ℝ)*k/(100000000*(L.card:ℝ)))/k := by gcongr
        _ = 3*(S.card:ℝ)/100000000 := by field_simp <;> ring
        _ ≤ _ := by linarith
    linarith
  let θ := (S.card:ℝ)*k/(100*(L.card:ℝ))
  let τ := θ/2
  have hθ : 0 < θ := by dsimp [θ];positivity
  have hτ : 0 < τ := by dsimp [τ];positivity
  have hDouble : 2*τ = θ := by dsimp [τ];ring
  have h6D : 6*(f.totalDegree:ℝ) < τ := by
    calc
      _ ≤ 6*((S.card:ℝ)*k/(100000000*(L.card:ℝ))) := mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = (3/250000:ℝ)*τ := by dsimp [τ,θ];field_simp <;> ring
      _ < _ := by nlinarith
  let A := L.filter (fun l => θ ≤ (pointsOn S l).card)
  let P := A.filter (fun l => τ ≤ (pointsOn T l).card)
  let F := A.filter (fun l => ¬τ ≤ (pointsOn T l).card)
  have hAsub : A ⊆ L := Finset.filter_subset _ _
  have hPsub : P ⊆ L := (Finset.filter_subset _ _).trans hAsub
  have hFsub : F ⊆ L := (Finset.filter_subset _ _).trans hAsub
  have hfailureRow : ∀ l ∈ F,τ ≤ (pointsOn U l).card := by
    intro l hl
    obtain ⟨hlA,hlfail⟩ := Finset.mem_filter.mp hl
    have hlS := (Finset.mem_filter.mp hlA).2
    have hlT : ((pointsOn T l).card:ℝ) < τ := lt_of_not_ge hlfail
    have hsplit : ((pointsOn U l).card:ℝ)+((pointsOn T l).card:ℝ) = (pointsOn S l).card := by
      exact_mod_cast pointsOn_sdiff_add S T hTsub l
    linarith
  have hfailLower : (F.card:ℝ)*τ ≤ relationMass U F (fun x l => x ∈ l.1) := by
    rw [relationMass_swap,relationMass_sum_card]
    calc
      _ = ∑ _l ∈ F,τ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun l hl => hfailureRow l hl)
  have hfailUpper : relationMass U F (fun x l => x ∈ l.1) ≤ 4*(S.card:ℝ)*k/1000000 := by
    have hu : relationMass U F (fun x l => x ∈ l.1) ≤ 2*(k:ℝ)*U.card := by
      rw [relationMass_sum_card]
      calc
        _ ≤ ∑ _x ∈ U,2*(k:ℝ) := by
          apply Finset.sum_le_sum
          intro x hx
          have hm := (lineMultiplicity_mono F L hFsub x).trans (hS x (hUsub hx)).2
          exact_mod_cast hm
        _ = _ := by simp [mul_comm]
    apply hu.trans
    have hm := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 2*(k:ℝ))
    nlinarith
  have hFcard : (F.card:ℝ) ≤ (L.card:ℝ)/1000 := by
    have hpay : ((L.card:ℝ)/1000)*τ = 5*(S.card:ℝ)*k/1000000 := by
      dsimp [τ,θ]
      field_simp <;> ring
    apply (mul_le_mul_iff_left₀ hτ).mp
    rw [hpay]
    nlinarith [mul_pos hs hkpos]
  have hPcard : (L.card:ℝ)/200 ≤ P.card := by
    have hsplit : (P.card:ℝ)+(F.card:ℝ) = A.card := by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (fun l => τ ≤ (pointsOn T l).card)
    have hA : (L.card:ℝ)/100 ≤ A.card := hUniform
    linarith
  have hPtype : ∀ l ∈ P,criticalLine f l ∨ flatLine f l := by
    intro l hl
    have hm := (Finset.mem_filter.mp hl).2
    apply critical_or_flat_line_of_many f l (pointsOn T l)
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun x hx => polynomialCore_point_type f L S x (Finset.mem_filter.mp hx).1)
    exact h6D.trans_le hm
  let C₀ := L.filter (fun l => criticalLine f l)
  let F₀ := L.filter (fun l => flatLine f l ∧ ¬inPlaneComponent f l)
  let P₀ := L.filter (fun l => inPlaneComponent f l)
  have hsub : P ⊆ C₀ ∪ F₀ ∪ P₀ := by
    intro l hl
    rcases hPtype l hl with hc | hf
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hPsub hl,hc⟩))))
    · by_cases hp : inPlaneComponent f l
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hPsub hl,hp⟩))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hPsub hl,hf,hp⟩))))
  have hcount : (P.card:ℝ) ≤ (C₀.card:ℝ)+(F₀.card:ℝ)+(P₀.card:ℝ) := by
    have hc : P.card ≤ C₀.card+F₀.card+P₀.card :=
      (Finset.card_le_card hsub).trans ((Finset.card_union_le (C₀ ∪ F₀) P₀).trans (add_le_add (Finset.card_union_le C₀ F₀) le_rfl))
    exact_mod_cast hc
  have hCcount : (C₀.card:ℝ) ≤ (f.totalDegree:ℝ)^2 :=
    (Nat.cast_le.mpr (finset_card_le_ncard C₀ _ hcritical.1 (fun l hl => (Finset.mem_filter.mp hl).2))).trans hcritical.2
  have hFcount : (F₀.card:ℝ) ≤ 3*(f.totalDegree:ℝ)^2 :=
    (Nat.cast_le.mpr (finset_card_le_ncard F₀ _ hflat.1 (fun l hl => (Finset.mem_filter.mp hl).2))).trans hflat.2
  have hPlaneCount : (L.card:ℝ)/400 ≤ P₀.card := by nlinarith
  exact hPlaneCount.trans (plane_component_line_budget f hf hsq L B hB hcap)

end DistinctDistances.TrackC
