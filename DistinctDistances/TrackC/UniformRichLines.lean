import DistinctDistances.TrackC.RichPlaneForcing
import DistinctDistances.TrackC.PartitionRichCell
import DistinctDistances.TrackC.RichLineScale

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Assemble polynomial partitioning, critical/flat forcing and the scale choice. -/
theorem uniform_rich_lines_construct (C : ℝ) (hC : 0 < C)
    (hST : ∀ (A : Finset (Line 3)) (j : ℕ),2 ≤ j →
      FiniteCardBound (richPoints A j) (C*((A.card:ℝ)^2/(j:ℝ)^3+(A.card:ℝ)/j)))
    (hCritical : ∀ (f : Poly 3),f ≠ 0 → Squarefree f →
      FiniteCardBound {l : Line 3 | criticalLine f l} ((f.totalDegree:ℝ)^2))
    (hFlat : ∀ (f : Poly 3),f ≠ 0 → Squarefree f →
      FiniteCardBound {l : Line 3 | flatLine f l ∧ ¬inPlaneComponent f l} (3*(f.totalDegree:ℝ)^2)) :
    ∃ K : ℝ,0 < K ∧ ∀ (L : Finset (Line 3)) (S : Finset (E 3)) (B : ℝ) (k : ℕ),
      L.Nonempty → 0 ≤ B → planeCap L B → 3 ≤ k →
      (∀ x ∈ S,k ≤ lineMultiplicity L x ∧ lineMultiplicity L x ≤ 2*k) →
      (L.card:ℝ)/100 ≤ ((L.filter (fun l => (S.card:ℝ)*k/(100*(L.card:ℝ)) ≤
        (pointsOn S l).card)).card:ℝ) →
      (S.card:ℝ) ≤ K*richLineBudget L.card B k := by
  obtain ⟨p,hp,hPart⟩ := ci_partition
  obtain ⟨θ,A,hθ,hA,hθC,hθQ,hAC,hAD,hADsq,hACell⟩ := rich_partition_constants p C hp hC
  let Q := 2000000*p*(p+1)
  have hQ : 0 < Q := by dsimp [Q];positivity
  let K := A+800*p*θ+1
  have hK : 0 < K := by dsimp [K];positivity
  have hKA : A ≤ K := by dsimp [K];nlinarith
  have hKθ : 800*p*θ ≤ K := by dsimp [K];linarith
  refine ⟨K,hK,?_⟩
  intro L S B k hL hB hcap hk hS hUniform
  have hN : (0:ℝ) < L.card := by exact_mod_cast Finset.card_pos.mpr hL
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  by_cases hlarge : A*((L.card:ℝ)^((3:ℝ)/2)/(k:ℝ)^2+(L.card:ℝ)/k) < S.card
  · have hs : (0:ℝ) < S.card := lt_of_le_of_lt (by positivity) hlarge
    have hRich := hST L k (by omega)
    have hglobal : (S.card:ℝ) ≤ C*((L.card:ℝ)^2/(k:ℝ)^3+(L.card:ℝ)/k) :=
      (Nat.cast_le.mpr (finset_card_le_ncard S _ hRich.1 (fun x hx => (hS x hx).1))).trans hRich.2
    obtain ⟨r,hr,hsmall,hsmallSq,hDegreeScale,hCell⟩ :=
      rich_partition_scale_choice p C θ A Q L.card S.card k hp hC hθ hA hQ hN hs
        (by exact_mod_cast (by omega : 1 ≤ k)) hθC hθQ hAC hAD hADsq hACell hglobal hlarge
    obtain ⟨f,cells,hf,hDegree,hCard,hCells,hDisjoint,hCover,hCross⟩ := hPart S r hr
    have hCell' : C*(((2*p*(p+1)/(1/1000000:ℝ))*(L.card:ℝ)/(r:ℝ)^2)^2/(k:ℝ)^3+
        ((2*p*(p+1)/(1/1000000:ℝ))*(L.card:ℝ)/(r:ℝ)^2)/k) <
        (1/1000000:ℝ)*S.card/(2*p*(r:ℝ)^3) := by
      convert hCell using 1 <;> (try dsimp [Q]) <;> field_simp <;> ring
    have hOff := partition_rich_off_zero_bound S L k r p C (1/1000000) hp hC (by norm_num)
      hr (by omega) hs (fun x hx => (hS x hx).1) hST f cells hDegree hCard
      (fun R hR => (hCells R hR).2) hCover hCross hCell'
    obtain ⟨g,hg,hsq,hgd,hzero⟩ := squarefree_part f hf
    have hoff : cloudMass S (zeroSet g)ᶜ ≤ (S.card:ℝ)/1000000 := by
      rw [hzero]
      convert hOff using 1 <;> ring
    have hgdReal : (g.totalDegree:ℝ) ≤ p*r := (Nat.cast_le.mpr hgd).trans hDegree
    have hD : (g.totalDegree:ℝ) ≤ (S.card:ℝ)*k/(100000000*(L.card:ℝ)) := hgdReal.trans hsmall
    have hDsq : (g.totalDegree:ℝ)^2 ≤ (L.card:ℝ)/1000000 := by
      apply ((sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr hgdReal).trans hsmallSq
    have hPlane := polynomial_uniform_plane_forcing g hg hsq L S B k hL hs hk hB hcap hS
      hUniform hoff hD hDsq (hCritical g hg hsq) (hFlat g hg hsq)
    have hUpper : (g.totalDegree:ℝ) ≤ 2*p*θ*(L.card:ℝ)^2/((S.card:ℝ)*(k:ℝ)^3) :=
      hgdReal.trans hDegreeScale
    have hPlane' : (L.card:ℝ)/400 ≤
        (2*p*θ*(L.card:ℝ)^2*B)/((S.card:ℝ)*(k:ℝ)^3) := by
      have h := hPlane.trans (mul_le_mul_of_nonneg_right hUpper hB)
      convert h using 1 <;> ring
    have hmul := (le_div_iff₀ (by positivity : (0:ℝ) < (S.card:ℝ)*(k:ℝ)^3)).mp hPlane'
    have hmass : (S.card:ℝ) ≤ 800*p*θ*(L.card:ℝ)*B/(k:ℝ)^3 := by
      apply (le_div_iff₀ (by positivity : (0:ℝ) < (k:ℝ)^3)).mpr
      apply (mul_le_mul_iff_right₀ hN).mp
      calc
        _ = 400*(((L.card:ℝ)/400)*((S.card:ℝ)*(k:ℝ)^3)) := by ring
        _ ≤ 400*(2*p*θ*(L.card:ℝ)^2*B) := mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = _ := by ring
    calc
      _ ≤ 800*p*θ*(L.card:ℝ)*B/(k:ℝ)^3 := hmass
      _ = (800*p*θ)*((L.card:ℝ)*B/(k:ℝ)^3) := by ring
      _ ≤ K*((L.card:ℝ)*B/(k:ℝ)^3) := mul_le_mul_of_nonneg_right hKθ (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hK.le
        unfold richLineBudget
        have hn₁ : 0 ≤ (L.card:ℝ)^((3:ℝ)/2)/(k:ℝ)^2 := by positivity
        have hn₃ : 0 ≤ (L.card:ℝ)/k := by positivity
        linarith
  · calc
      _ ≤ A*((L.card:ℝ)^((3:ℝ)/2)/(k:ℝ)^2+(L.card:ℝ)/k) := le_of_not_gt hlarge
      _ ≤ K*((L.card:ℝ)^((3:ℝ)/2)/(k:ℝ)^2+(L.card:ℝ)/k) := mul_le_mul_of_nonneg_right hKA (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hK.le
        unfold richLineBudget
        have hn : 0 ≤ (L.card:ℝ)*B/(k:ℝ)^3 := by positivity
        linarith

end DistinctDistances.TrackC
