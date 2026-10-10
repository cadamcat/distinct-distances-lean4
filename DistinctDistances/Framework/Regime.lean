import DistinctDistances.OAIInterface.Distances
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Algebra.Order.Floor.Ring

open Filter
open scoped Topology

namespace DistinctDistances

noncomputable section

/-- Real Euclidean `d`-space (`Point` is the complex affine space of `Foundations`). -/
abbrev RPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The lower clause of the target in one dimension, with the real exponent. -/
def LowerBound (d : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ P : Finset (RPoint d), 2 ≤ P.card →
    c * (P.card : ℝ) ^ (2 / (d : ℝ)) ≤ (distinctDistances P : ℝ)

/-- The induction hypothesis available in the least failing dimension. -/
def IH (d : ℕ) : Prop := ∀ u : ℕ, 3 ≤ u → u < d → LowerBound u

/-- `FW.regime`, reduction.tex:10–28. All casts precede division and powers.
Growth of cardinality is a derived fact, rather than an additional assumption. -/
structure Regime (d : ℕ) where
  dimension_ge_three : 3 ≤ d
  P : ℕ → Finset (RPoint d)
  card_ge_two : ∀ k, 2 ≤ (P k).card
  ratio_tendsto : Tendsto (fun k => (1 + (distinctDistances (P k) : ℝ)) /
    ((P k).card : ℝ) ^ (2 / (d : ℝ))) atTop (𝓝 0)
  inductionHypothesis : IH d

namespace Regime

variable {d : ℕ} (r : Regime d)

/-- Real-valued cardinality, so scale arithmetic never uses natural division. -/
def N (k : ℕ) : ℝ := (r.P k).card
def M (k : ℕ) : ℝ := 1 + (distinctDistances (r.P k) : ℝ)
def B (k : ℕ) : ℝ := r.N k ^ (1 / (d : ℝ))
/-- Defined in the form used by the target and OAI; `A_eq_B_sq` gives the paper form. -/
def A (k : ℕ) : ℝ := r.N k ^ (2 / (d : ℝ))
noncomputable def D (k : ℕ) : ℕ := ⌊r.A k⌋₊

theorem N_ge_two (k : ℕ) : 2 ≤ r.N k := by
  dsimp [N]
  exact_mod_cast r.card_ge_two k

theorem N_pos (k : ℕ) : 0 < r.N k := lt_of_lt_of_le (by norm_num) (r.N_ge_two k)

theorem M_ge_two (k : ℕ) : 2 ≤ r.M k := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (r.card_ge_two k)
  have hmem : dist p q ∈ distanceSet (r.P k) := by
    exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩
  have hcard : 1 ≤ distinctDistances (r.P k) :=
    Finset.card_pos.mpr ⟨dist p q, hmem⟩
  have : (1 : ℝ) ≤ (distinctDistances (r.P k) : ℝ) := by exact_mod_cast hcard
  dsimp [M]
  linarith

theorem A_pos (k : ℕ) : 0 < r.A k := Real.rpow_pos_of_pos (r.N_pos k) _
theorem B_pos (k : ℕ) : 0 < r.B k := Real.rpow_pos_of_pos (r.N_pos k) _

theorem A_eq_B_sq (k : ℕ) : r.A k = r.B k ^ 2 := by
  rw [A, B, ← Real.rpow_natCast, ← Real.rpow_mul (r.N_pos k).le]
  congr 1
  push_cast
  ring

theorem M_div_A_tendsto : Tendsto (fun k => r.M k / r.A k) atTop (𝓝 0) :=
  r.ratio_tendsto

/-- `FW.regime`: vanishing ratio forces unbounded sample size. -/
theorem N_tendsto : Tendsto r.N atTop atTop := by
  have hd : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by have := r.dimension_ge_three; omega)
  have hexp : 2 / (d : ℝ) ≤ 1 := by
    apply (div_le_one hd).mpr
    exact_mod_cast (show 2 ≤ d by have := r.dimension_ge_three; omega)
  have hAN (k : ℕ) : r.A k ≤ r.N k :=
    Real.rpow_le_self_of_one_le (by linarith [r.N_ge_two k]) hexp
  refine tendsto_atTop.2 fun b => ?_
  let C : ℝ := max b 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  have hsmall := r.M_div_A_tendsto.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / C by positivity))
  filter_upwards [hsmall] with k hk
  have hlt : r.M k < r.A k / C := by
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using
      (div_lt_iff₀ (r.A_pos k)).mp hk
  have hCA : C < r.A k := by
    have hCA' := (lt_div_iff₀ hC).mp (lt_of_le_of_lt
      (show (1 : ℝ) ≤ r.M k by linarith [r.M_ge_two k]) hlt)
    simpa using hCA'
  exact (le_max_left b 1).trans (hCA.le.trans (hAN k))

theorem card_tendsto : Tendsto (fun k => (r.P k).card) atTop atTop := by
  exact tendsto_natCast_atTop_iff.mp r.N_tendsto

theorem A_tendsto : Tendsto r.A atTop atTop := by
  apply (tendsto_rpow_atTop ?_).comp r.N_tendsto
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by have := r.dimension_ge_three; omega)
  positivity

theorem B_tendsto : Tendsto r.B atTop atTop := by
  apply (tendsto_rpow_atTop ?_).comp r.N_tendsto
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by have := r.dimension_ge_three; omega)
  positivity

theorem eventually_M_le_A : ∀ᶠ k in atTop, r.M k ≤ r.A k := by
  have h := r.M_div_A_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with k hk
  exact le_of_lt ((div_lt_one (r.A_pos k)).mp hk)

/-- Rounding down the testing degree loses at most a factor two eventually. -/
theorem eventually_D_bounds : ∀ᶠ k in atTop,
    r.A k / 2 ≤ (r.D k : ℝ) ∧ (r.D k : ℝ) ≤ r.A k := by
  filter_upwards [r.A_tendsto.eventually (eventually_ge_atTop (2 : ℝ))] with k hk
  constructor
  · have hfloor := Nat.lt_floor_add_one (r.A k)
    dsimp [D]
    linarith
  · exact Nat.floor_le (r.A_pos k).le

/-- `FW.regime`: subsequences retain the same dimension and induction hypothesis. -/
def comp (φ : ℕ → ℕ) (hφ : StrictMono φ) : Regime d where
  dimension_ge_three := r.dimension_ge_three
  P := fun k => r.P (φ k)
  card_ge_two := fun k => r.card_ge_two (φ k)
  ratio_tendsto := r.ratio_tendsto.comp hφ.tendsto_atTop
  inductionHypothesis := r.inductionHypothesis

@[simp] theorem comp_P (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : ℕ) :
    (r.comp φ hφ).P k = r.P (φ k) := rfl
@[simp] theorem comp_N (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : ℕ) :
    (r.comp φ hφ).N k = r.N (φ k) := rfl
@[simp] theorem comp_M (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : ℕ) :
    (r.comp φ hφ).M k = r.M (φ k) := rfl
@[simp] theorem comp_A (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : ℕ) :
    (r.comp φ hφ).A k = r.A (φ k) := rfl
@[simp] theorem comp_B (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : ℕ) :
    (r.comp φ hφ).B k = r.B (φ k) := rfl
@[simp] theorem comp_D (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : ℕ) :
    (r.comp φ hφ).D k = r.D (φ k) := rfl

/-- A window has diverging width bounded by the outer width, eventually. -/
structure Window where
  s : ℕ → ℝ
  grows : Tendsto s atTop atTop
  le_logB : ∀ᶠ k in atTop, s k ≤ Real.log (r.B k)

def Window.comp (w : r.Window) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    (r.comp φ hφ).Window where
  s := fun k => w.s (φ k)
  grows := w.grows.comp hφ.tendsto_atTop
  le_logB := hφ.tendsto_atTop.eventually w.le_logB

/-- The converse to `TOP.regime`, matching OAI's `regime_precludes_bound`. -/
theorem precludes_lowerBound (r : Regime d) : ¬ LowerBound d := by
  rintro ⟨c, hc, hb⟩
  have hcle : c ≤ 0 := ge_of_tendsto' r.M_div_A_tendsto fun k => by
    apply (le_div_iff₀ (r.A_pos k)).mpr
    have h := hb (r.P k) (r.card_ge_two k)
    dsimp [M, A, N]
    linarith
  exact (not_le_of_gt hc) hcle

end Regime

/-- `TOP.regime`: failure together with the induction hypothesis supplies a regime. -/
theorem failure_gives_regime {d : ℕ} (hd : 3 ≤ d) (hIH : IH d)
    (hfail : ¬ LowerBound d) : Nonempty (Regime d) := by
  obtain ⟨P, hP, _, hlim⟩ := OAIInterface.failure_gives_regime hd hfail
  exact ⟨⟨hd, P, hP, hlim, hIH⟩⟩

end

end DistinctDistances
