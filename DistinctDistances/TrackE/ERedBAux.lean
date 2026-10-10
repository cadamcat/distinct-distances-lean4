import DistinctDistances.TrackE.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Constructions.Pi
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace DistinctDistances

namespace Reduction

def ind (b : Bool) : ℝ := if b then 1 else 0

open Classical in
theorem exists_sample_finiteBernoulli {V : Type*} (W : Finset V) (adj : V → V → Prop)
    (δ θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hdeg : ∀ v ∈ W, δ ≤ ((W.filter fun w => adj v w).card : ℝ))
    (hunion : (W.card : ℝ) * Real.exp (-(θ ^ 2 * δ / 2)) < 1 / 2) :
    ∃ T ⊆ W, (T.card : ℝ) ≤ 2 * θ * W.card ∧
      ∀ v ∈ W, θ * δ / 2 ≤ ((T.filter fun w => adj v w).card : ℝ) := by
  classical
  by_cases hWempty : W = ∅
  · subst W
    refine ⟨∅, by simp, by simp, ?_⟩
    intro v hv
    simp at hv
  have hWpos : 0 < W.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hWempty)
  have hn1Nat : 1 ≤ W.card := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hWpos)
  have hn1 : 1 ≤ (W.card : ℝ) := by exact_mod_cast hn1Nat
  have hExpLt : Real.exp (-(θ ^ 2 * δ / 2)) < 1 := by
    have hExpPos := Real.exp_pos (-(θ ^ 2 * δ / 2))
    have hExpLe : Real.exp (-(θ ^ 2 * δ / 2)) ≤
        (W.card : ℝ) * Real.exp (-(θ ^ 2 * δ / 2)) := by
      calc
        _ = 1 * Real.exp (-(θ ^ 2 * δ / 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hn1 hExpPos.le
    exact lt_of_le_of_lt hExpLe (lt_trans hunion (by norm_num))
  have hδpos : 0 < δ := by
    have harg : -(θ ^ 2 * δ / 2) < 0 := (Real.exp_lt_one_iff).mp hExpLt
    nlinarith [sq_pos_of_pos hθ0]
  let α := {v // v ∈ W}
  letI : Fintype α := Fintype.ofFinite α
  have hn : Fintype.card α = W.card := by simp [α]
  let θI : unitInterval := ⟨θ, ⟨le_of_lt hθ0, hθ1⟩⟩
  let ν : Measure Bool := bernoulliMeasure true false θI
  haveI : IsProbabilityMeasure ν := inferInstance
  let Ω := α → Bool
  let μ : Measure Ω := Measure.pi fun _ : α => ν
  haveI : IsProbabilityMeasure μ := by infer_instance
  have hmean : ∫ b : Bool, ind b ∂ν = θ := by
    simp [ν, ind, ProbabilityTheory.integral_bernoulliMeasure, θI]
  have hraw : HasSubgaussianMGF (fun b : Bool => ind b - θ) (1/4 : NNReal) ν := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := ind) (a := (0:ℝ)) (b := 1)
      (by fun_prop) (by filter_upwards with b; cases b <;> simp [ind])
    rw [← hmean]
    convert h using 1 <;> norm_num
  let Z : α → Ω → ℝ := fun i ω => ind (ω i) - θ
  let Zneg : α → Ω → ℝ := fun i ω => -(Z i ω)
  have hprod : ∀ i : α, HasSubgaussianMGF (Z i) (1/4 : NNReal) μ := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) μ ν := by
      simpa [μ] using (measurePreserving_eval (fun _ : α => ν) i)
    have hrawMap : HasSubgaussianMGF (fun b : Bool => ind b - θ) (1/4:NNReal)
        (Measure.map (Function.eval i) μ) := by
      rw [hmp.map_eq]
      exact hraw
    simpa [Z, Ω, Function.comp_def] using HasSubgaussianMGF.of_map hmp.aemeasurable hrawMap
  have hbool : iIndepFun (fun i : α => fun ω : Ω => ω i) μ := by
    simpa [μ, Ω] using (iIndepFun_pi (μ := fun _ : α => ν) (X := fun _ => id)
      (by intro i; exact aemeasurable_id))
  have hindep : iIndepFun Z μ := by
    exact (hbool.comp (fun _ b => ind b) (by intro i; fun_prop)).comp
      (fun _ x => x - θ) (by intro i; fun_prop)
  have hindeNeg : iIndepFun Zneg μ := by
    exact hindep.comp (fun _ x => -x) (by intro i; fun_prop)
  let chosen (ω : Ω) : Finset V :=
    (Finset.univ.filter fun i : α => ω i = true).image Subtype.val
  have hchosenCard (ω : Ω) : ((chosen ω).card : ℝ) = ∑ i : α, ind (ω i) := by
    dsimp [chosen]
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    simp [ind]
  have hcenterSum (ω : Ω) : (∑ i : α, Z i ω) =
      (chosen ω).card - θ * (W.card : ℝ) := by
    calc
      _ = (∑ i : α, ind (ω i)) - ∑ i : α, θ := by
        simp [Z, Finset.sum_sub_distrib]
      _ = _ := by rw [hchosenCard]; simp [hn, mul_comm]
  let neigh (v : V) : Finset α := Finset.univ.filter fun i => adj v i.1
  have hneighCard (v : V) : (neigh v).card = (W.filter fun w => adj v w).card := by
    have himage : (neigh v).image Subtype.val = W.filter fun w => adj v w := by
      ext w
      simp [neigh, and_comm]
    rw [← Finset.card_image_of_injective (neigh v) Subtype.val_injective, himage]
  have hchosenNeighCard (v : V) (ω : Ω) :
      ((chosen ω).filter fun w => adj v w).card =
        ((neigh v).filter fun i => ω i = true).card := by
    dsimp [chosen]
    rw [Finset.filter_image]
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    simp [neigh, Finset.filter_filter, and_comm, and_left_comm, and_assoc]
    rfl
  have hneighLower (i : α) : δ ≤ ((neigh i.1).card : ℝ) := by
    have h := hdeg i.1 i.2
    simpa [hneighCard] using h
  have htail (s : Finset α) (ε : ℝ) (hε : 0 ≤ ε) :
      μ.real {ω | ε ≤ ∑ i ∈ s, Zneg i ω} ≤
        Real.exp (-ε ^ 2 / (2 * ((s.card : ℝ) * (4 : ℝ)⁻¹))) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := s)
      (c := fun _ : α => (1/4 : NNReal)) hindeNeg
      (fun i hi => (hprod i).neg) hε
    have hsum : ((∑ i ∈ s, (1/4 : NNReal) : NNReal) : ℝ) =
        (s.card : ℝ) * (4 : ℝ)⁻¹ := by simp [Finset.sum_const]
    simpa [Zneg, hsum] using h
  have htailPos (s : Finset α) (ε : ℝ) (hε : 0 ≤ ε) :
      μ.real {ω | ε ≤ ∑ i ∈ s, Z i ω} ≤
        Real.exp (-ε ^ 2 / (2 * ((s.card : ℝ) * (4 : ℝ)⁻¹))) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := s)
      (c := fun _ : α => (1/4 : NNReal)) hindep
      (fun i hi => hprod i) hε
    have hsum : ((∑ i ∈ s, (1/4 : NNReal) : NNReal) : ℝ) =
        (s.card : ℝ) * (4 : ℝ)⁻¹ := by simp [Finset.sum_const]
    simpa [Z, hsum] using h
  let sizeBad : Set Ω := {ω | 2 * θ * (W.card : ℝ) < (chosen ω).card}
  have hsizeSubset : sizeBad ⊆ {ω | θ * (W.card : ℝ) ≤ ∑ i : α, Z i ω} := by
    intro ω hω
    have hs := hcenterSum ω
    change 2 * θ * (W.card : ℝ) < (chosen ω).card at hω
    change θ * (W.card : ℝ) ≤ ∑ i : α, Z i ω
    rw [hs]
    linarith
  have hδle : δ ≤ (W.card : ℝ) := by
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hWempty
    have h := hdeg v hv
    have hc : (W.filter (fun w => adj v w)).card ≤ W.card :=
      Finset.card_le_card (Finset.filter_subset (p := fun w => adj v w) W)
    exact h.trans (by exact_mod_cast hc)
  have hsizeTail : μ.real sizeBad ≤ Real.exp (-(θ ^ 2 * δ / 2)) := by
    have h := htailPos Finset.univ (θ * (W.card : ℝ)) (by positivity)
    have hTailBad := measureReal_mono (μ := μ) hsizeSubset (by finiteness)
    have hcard : (Finset.univ : Finset α).card = W.card := by
      simpa using hn
    calc
      μ.real sizeBad ≤ Real.exp ((-((θ * (W.card : ℝ)) ^ 2)) /
          (2 * ((W.card : ℝ) * (4 : ℝ)⁻¹))) := by
        simpa [hcard, Finset.card_univ] using hTailBad.trans h
      _ ≤ Real.exp (-(θ ^ 2 * δ / 2)) := by
        apply Real.exp_le_exp.mpr
        have hnpos : 0 < (W.card : ℝ) := by exact_mod_cast hWpos
        field_simp
        nlinarith [sq_nonneg θ, hδle]
  let lowBad (i : α) : Set Ω :=
    {ω | ((chosen ω).filter fun w => adj i.1 w).card < θ * δ / 2}
  have hlowSubset (i : α) : lowBad i ⊆
      {ω | θ * ((neigh i.1).card : ℝ) / 2 ≤
        ∑ j ∈ neigh i.1, Zneg j ω} := by
    intro ω hω
    have hN := hneighLower i
    have hcount := hchosenNeighCard i.1 ω
    dsimp [lowBad] at hω
    have hsum : (∑ j ∈ neigh i.1, Zneg j ω) =
        θ * (neigh i.1).card - ((chosen ω).filter fun w => adj i.1 w).card := by
      calc
        _ = ∑ j ∈ neigh i.1, (θ - ind (ω j)) := by simp [Zneg, Z]
        _ = _ := by
          rw [Finset.sum_sub_distrib]
          have hcountReal :
              (∑ j ∈ neigh i.1, ind (ω j)) =
                (((chosen ω).filter fun w => adj i.1 w).card : ℝ) := by
            calc
              _ = ∑ j ∈ neigh i.1, if ω j = true then (1 : ℝ) else 0 := by
                congr 1
              _ = ((neigh i.1).filter fun j => ω j = true).card :=
                Finset.sum_boole _ _
              _ = _ := by exact_mod_cast hcount.symm
          rw [hcountReal]
          simp [Finset.sum_const, mul_comm]
    change θ * ((neigh i.1).card : ℝ) / 2 ≤
      ∑ j ∈ neigh i.1, Zneg j ω
    rw [hsum]
    nlinarith [hθ0]
  have hlowTail (i : α) : μ.real (lowBad i) ≤
      Real.exp (-(θ ^ 2 * δ / 2)) := by
    have hN := hneighLower i
    have hNpos : 0 < (neigh i.1).card := by
      exact_mod_cast (lt_of_lt_of_le hδpos hN)
    have h := htail (neigh i.1) (θ * (neigh i.1).card / 2) (by positivity)
    have hsub := measureReal_mono (μ := μ) (hlowSubset i) (by finiteness)
    have hTail : μ.real {ω | θ * ((neigh i.1).card : ℝ) / 2 ≤
        ∑ j ∈ neigh i.1, Zneg j ω} ≤
        Real.exp (-(θ ^ 2 * (neigh i.1).card / 2)) := by
      calc
        _ ≤ Real.exp (-(θ * (neigh i.1).card / 2) ^ 2 /
            (2 * (((neigh i.1).card : ℝ) * (4 : ℝ)⁻¹))) := by
          simpa only [neg_div] using h
        _ = _ := by
          congr 1
          field_simp
          ring
    exact hsub.trans (hTail.trans (by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg θ, hN]))
  have hbadUnion : μ.real (sizeBad ∪ ⋃ i : α, lowBad i) < 1 := by
    have hlow := measureReal_iUnion_fintype_le (μ := μ) lowBad
    have hsum : (∑ i : α, μ.real (lowBad i)) ≤
        (Fintype.card α : ℝ) * Real.exp (-(θ ^ 2 * δ / 2)) := by
      calc
        _ = ∑ i ∈ (Finset.univ : Finset α), μ.real (lowBad i) := rfl
        _ ≤ ∑ i ∈ Finset.univ, Real.exp (-(θ ^ 2 * δ / 2)) :=
          Finset.sum_le_sum fun i hi => hlowTail i
        _ = _ := by simp
    have hExpLe : Real.exp (-(θ ^ 2 * δ / 2)) ≤
        (W.card : ℝ) * Real.exp (-(θ ^ 2 * δ / 2)) := by
      have hp := Real.exp_pos (-(θ ^ 2 * δ / 2))
      calc
        _ = 1 * _ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hn1 hp.le
    calc
      _ ≤ μ.real sizeBad + μ.real (⋃ i : α, lowBad i) := measureReal_union_le _ _
      _ ≤ Real.exp (-(θ ^ 2 * δ / 2)) +
          (Fintype.card α : ℝ) * Real.exp (-(θ ^ 2 * δ / 2)) :=
        add_le_add hsizeTail (hlow.trans hsum)
      _ ≤ (W.card : ℝ) * Real.exp (-(θ ^ 2 * δ / 2)) +
          (W.card : ℝ) * Real.exp (-(θ ^ 2 * δ / 2)) := by rw [hn]; gcongr
      _ < 1 := by nlinarith [hunion]
  have hgood : ∃ ω : Ω, ω ∉ sizeBad ∪ ⋃ i : α, lowBad i := by
    by_contra h
    have hall : Set.univ ⊆ sizeBad ∪ ⋃ i : α, lowBad i := by
      intro ω hω
      by_contra hnω
      exact h ⟨ω, hnω⟩
    have hone : 1 ≤ μ.real (sizeBad ∪ ⋃ i : α, lowBad i) := by
      calc
        _ = μ.real Set.univ := by simp
        _ ≤ _ := measureReal_mono hall
    linarith
  obtain ⟨ω, hω⟩ := hgood
  refine ⟨chosen ω, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact i.2
  · have hnotsize : ¬ 2 * θ * (W.card : ℝ) < (chosen ω).card := by
      intro hbad
      exact hω (Or.inl hbad)
    exact le_of_not_gt hnotsize
  · intro v hv
    let i : α := ⟨v, hv⟩
    have hnotlow : ¬ ω ∈ lowBad i := by
      intro hbad
      exact hω (Or.inr (Set.mem_iUnion.mpr ⟨i, hbad⟩))
    exact le_of_not_gt hnotlow

end Reduction

end DistinctDistances
