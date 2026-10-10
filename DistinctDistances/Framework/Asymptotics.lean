import DistinctDistances.Framework.Regime
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.MetricSpace.Sequences

open Filter
open scoped Topology BigOperators

namespace DistinctDistances.Framework

/-- Scalar little-o at infinity. The absolute-value definition handles zero scales;
`littleO_iff_ratio` recovers the ratio convention for eventually nonzero scales. -/
abbrev LittleO (f g : ℕ → ℝ) : Prop := Asymptotics.IsLittleO atTop f g

/-- `FW.asym`: one large-index threshold works for every member of the family.
Empty families are allowed; use an explicit nonemptiness assumption when selecting. -/
def UniformLittleO (ι : ℕ → Type*) (f g : (k : ℕ) → ι k → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i : ι k, |f k i| ≤ ε * |g k i|

/-- The implied constant and threshold are independent of the family member. -/
def UniformBigO (ι : ℕ → Type*) (f g : (k : ℕ) → ι k → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop, ∀ i : ι k, |f k i| ≤ C * |g k i|

/-- Uniform convergence to a specified, possibly varying, reference value. -/
def UniformConverges (ι : ℕ → Type*) (f a : (k : ℕ) → ι k → ℝ) : Prop :=
  UniformLittleO ι (fun k i => f k i - a k i) (fun _ _ => 1)

/-- `U ≥ V exp(-o(s))`, profiles.tex:21–29. Use with nonnegative masses;
positivity is required by any subsequent logarithmic interpretation. -/
def ExpLower (ι : ℕ → Type*) (U V : (k : ℕ) → ι k → ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i : ι k,
    V k i * Real.exp (-ε * s k) ≤ U k i

/-- `U ≤ V exp(o(s))`, with uniformity over the same index family. -/
def ExpUpper (ι : ℕ → Type*) (U V : (k : ℕ) → ι k → ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i : ι k,
    U k i ≤ V k i * Real.exp (ε * s k)

def ExpEquivalent (ι : ℕ → Type*) (U V : (k : ℕ) → ι k → ℝ) (s : ℕ → ℝ) : Prop :=
  ExpLower ι U V s ∧ ExpUpper ι U V s

/-- A fixed density is chosen before the asymptotic limit. Assumptions about
nonzero total mass belong to the consumer. -/
def PositiveDensity (mass total : ℕ → ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ k in atTop, ρ * total k ≤ mass k

/-- Every subcollection of any later fixed positive density obeys `Q`.
The family `ι k` includes all choices made after deletions, such as centers,
envelopes and subcollections. The threshold may depend on `ρ`.
depth.tex:78–83; sparse-cones.tex:668–678. -/
def ForFixedDensity (ι : ℕ → Type*) (mass total : (k : ℕ) → ι k → ℝ)
    (Q : (k : ℕ) → ι k → Prop) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ᶠ k in atTop, ∀ i : ι k,
    ρ * total k i ≤ mass k i → Q k i

/-- Honest limits of a finite list of recorded normalized cut times. -/
def ProfileConverges {m : ℕ} (times : ℕ → Fin m → ℝ) (b : Fin m → ℝ) : Prop :=
  ∀ j, Tendsto (fun k => times k j) atTop (𝓝 (b j))

/-- The recorded time of a positive testing degree; use when `B,s > 0`. -/
noncomputable def normalizedTime (B s degree : ℝ) : ℝ := Real.log (degree / B) / s

/-- A result after passage to a subsequence; no uniform choice of subsequence
across independent input regimes is implied. -/
def OnSubsequence {d : ℕ} (r : Regime d) (Q : Regime d → Prop) : Prop :=
  ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ, Q (r.comp φ hφ)

theorem littleO_iff_ratio {f g : ℕ → ℝ} (hg : ∀ᶠ k in atTop, g k ≠ 0) :
    LittleO f g ↔ Tendsto (fun k => f k / g k) atTop (𝓝 0) := by
  apply Asymptotics.isLittleO_iff_tendsto'
  filter_upwards [hg] with k hk
  exact fun h => (hk h).elim

theorem uniformLittleO_unit {f g : ℕ → ℝ} :
    UniformLittleO (fun _ => Unit) (fun k _ => f k) (fun k _ => g k) ↔ LittleO f g := by
  simp only [UniformLittleO, Asymptotics.isLittleO_iff, Real.norm_eq_abs,
    forall_const]

theorem UniformBigO.comp {ι : ℕ → Type*} {f g : (k : ℕ) → ι k → ℝ}
    (hf : UniformBigO ι f g) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    UniformBigO (fun k => ι (φ k)) (fun k => f (φ k)) (fun k => g (φ k)) := by
  obtain ⟨C, hC, hbound⟩ := hf
  exact ⟨C, hC, hφ.tendsto_atTop.eventually hbound⟩

theorem ForFixedDensity.comp {ι : ℕ → Type*} {mass total : (k : ℕ) → ι k → ℝ}
    {Q : (k : ℕ) → ι k → Prop} (h : ForFixedDensity ι mass total Q)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ForFixedDensity (fun k => ι (φ k)) (fun k => mass (φ k)) (fun k => total (φ k))
      (fun k => Q (φ k)) := by
  intro ρ hρ
  exact hφ.tendsto_atTop.eventually (h ρ hρ)

theorem ProfileConverges.comp {m : ℕ} {times : ℕ → Fin m → ℝ} {b : Fin m → ℝ}
    (h : ProfileConverges times b) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ProfileConverges (fun k => times (φ k)) b := by
  exact fun j => (h j).comp hφ.tendsto_atTop

namespace UniformLittleO

variable {ι : ℕ → Type*} {f g h : (k : ℕ) → ι k → ℝ}

theorem zero (g : (k : ℕ) → ι k → ℝ) : UniformLittleO ι (fun _ _ => 0) g := by
  intro ε hε
  exact Eventually.of_forall fun k i => by simpa using mul_nonneg hε.le (abs_nonneg (g k i))

theorem mono (hf : UniformLittleO ι f g)
    (hbound : ∀ᶠ k in atTop, ∀ i, |h k i| ≤ |f k i|) : UniformLittleO ι h g := by
  intro ε hε
  filter_upwards [hf ε hε, hbound] with k hk hbk
  exact fun i => (hbk i).trans (hk i)

theorem comp (hf : UniformLittleO ι f g) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    UniformLittleO (fun k => ι (φ k)) (fun k => f (φ k)) (fun k => g (φ k)) := by
  intro ε hε
  exact hφ.tendsto_atTop.eventually (hf ε hε)

theorem select (hf : UniformLittleO ι f g) (i : (k : ℕ) → ι k) :
    LittleO (fun k => f k (i k)) (fun k => g k (i k)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hf ε hε] with k hk
  simpa only [Real.norm_eq_abs] using hk (i k)

theorem add (hf : UniformLittleO ι f h) (hg : UniformLittleO ι g h) :
    UniformLittleO ι (fun k i => f k i + g k i) h := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by linarith), hg (ε / 2) (by linarith)] with k hfk hgk
  intro i
  calc
    |f k i + g k i| ≤ |f k i| + |g k i| := abs_add_le _ _
    _ ≤ ε / 2 * |h k i| + ε / 2 * |h k i| := add_le_add (hfk i) (hgk i)
    _ = ε * |h k i| := by ring

theorem const_mul (hf : UniformLittleO ι f g) (c : ℝ) :
    UniformLittleO ι (fun k i => c * f k i) g := by
  by_cases hc : c = 0
  · simpa [hc] using zero g
  have hcabs : 0 < |c| := abs_pos.mpr hc
  intro ε hε
  filter_upwards [hf (ε / |c|) (div_pos hε hcabs)] with k hk
  intro i
  rw [abs_mul]
  calc
    |c| * |f k i| ≤ |c| * (ε / |c| * |g k i|) :=
      mul_le_mul_of_nonneg_left (hk i) (abs_nonneg c)
    _ = ε * |g k i| := by field_simp

theorem mul_bigO {f' g' : (k : ℕ) → ι k → ℝ}
    (hf : UniformLittleO ι f g) (hf' : UniformBigO ι f' g') :
    UniformLittleO ι (fun k i => f k i * f' k i) (fun k i => g k i * g' k i) := by
  obtain ⟨C, hC, hbound⟩ := hf'
  intro ε hε
  filter_upwards [hf (ε / C) (div_pos hε hC), hbound] with k hk hk'
  intro i
  rw [abs_mul, abs_mul]
  calc
    |f k i| * |f' k i| ≤ (ε / C * |g k i|) * (C * |g' k i|) :=
      mul_le_mul (hk i) (hk' i) (abs_nonneg _) (by positivity)
    _ = ε * (|g k i| * |g' k i|) := by field_simp

/-- The number of summands is fixed independently of `k`. -/
theorem finite_sum {α : Type*} (S : Finset α) (F : α → (k : ℕ) → ι k → ℝ)
    (hF : ∀ a ∈ S, UniformLittleO ι (F a) g) :
    UniformLittleO ι (fun k i => ∑ a ∈ S, F a k i) g := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using zero g
  | @insert a S ha ih =>
      have h₁ := hF a (Finset.mem_insert_self a S)
      have h₂ := ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))
      simpa [Finset.sum_insert ha] using h₁.add h₂

end UniformLittleO

/-- "Along every sequence of pieces" is uniform, assuming pieces exist.
For possibly empty families use `UniformLittleO` directly. -/
theorem uniformLittleO_iff_selections {ι : ℕ → Type*}
    (hne : ∀ k, Nonempty (ι k)) (f g : (k : ℕ) → ι k → ℝ) :
    UniformLittleO ι f g ↔
      ∀ i : (k : ℕ) → ι k, LittleO (fun k => f k (i k)) (fun k => g k (i k)) := by
  classical
  constructor
  · exact fun h i => h.select i
  intro h ε hε
  let pick : (k : ℕ) → ι k := fun k =>
    if hbad : ∃ i : ι k, ¬ |f k i| ≤ ε * |g k i|
    then Classical.choose hbad else Classical.choice (hne k)
  filter_upwards [(h pick).def hε] with k hk
  intro i
  by_contra hi
  have hbad : ∃ i : ι k, ¬ |f k i| ≤ ε * |g k i| := ⟨i, hi⟩
  have hpick : ¬ |f k (pick k)| ≤ ε * |g k (pick k)| := by
    simpa only [pick, dif_pos hbad] using Classical.choose_spec hbad
  exact hpick (by simpa only [Real.norm_eq_abs] using hk)

namespace ExpLower

variable {ι : ℕ → Type*} {U V W : (k : ℕ) → ι k → ℝ} {s : ℕ → ℝ}

theorem comp (h : ExpLower ι U V s) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ExpLower (fun k => ι (φ k)) (fun k => U (φ k)) (fun k => V (φ k))
      (fun k => s (φ k)) := by
  intro ε hε
  exact hφ.tendsto_atTop.eventually (h ε hε)

theorem trans (hUV : ExpLower ι U V s) (hVW : ExpLower ι V W s) :
    ExpLower ι U W s := by
  intro ε hε
  filter_upwards [hUV (ε / 2) (by linarith), hVW (ε / 2) (by linarith)] with k hk hk'
  intro i
  have he : Real.exp (-ε * s k) =
      Real.exp (-(ε / 2) * s k) * Real.exp (-(ε / 2) * s k) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    W k i * Real.exp (-ε * s k) =
        (W k i * Real.exp (-(ε / 2) * s k)) * Real.exp (-(ε / 2) * s k) := by
      rw [he, mul_assoc]
    _ ≤ V k i * Real.exp (-(ε / 2) * s k) :=
      mul_le_mul_of_nonneg_right (hk' i) (Real.exp_pos _).le
    _ ≤ U k i := hk i

theorem mul {U' V' : (k : ℕ) → ι k → ℝ}
    (hUV : ExpLower ι U V s) (hUV' : ExpLower ι U' V' s)
    (hV : ∀ᶠ k in atTop, ∀ i, 0 ≤ V k i)
    (hU' : ∀ᶠ k in atTop, ∀ i, 0 ≤ U' k i) :
    ExpLower ι (fun k i => U k i * U' k i) (fun k i => V k i * V' k i) s := by
  intro ε hε
  filter_upwards [hUV (ε / 2) (by linarith), hUV' (ε / 2) (by linarith), hV, hU']
    with k hk hk' hv hu'
  intro i
  have he : Real.exp (-ε * s k) =
      Real.exp (-(ε / 2) * s k) * Real.exp (-(ε / 2) * s k) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (V k i * V' k i) * Real.exp (-ε * s k) =
        (V k i * Real.exp (-(ε / 2) * s k)) *
          (V' k i * Real.exp (-(ε / 2) * s k)) := by rw [he]; ring
    _ ≤ (V k i * Real.exp (-(ε / 2) * s k)) * U' k i :=
      mul_le_mul_of_nonneg_left (hk' i) (mul_nonneg (hv i) (Real.exp_pos _).le)
    _ ≤ U k i * U' k i := mul_le_mul_of_nonneg_right (hk i) (hu' i)

end ExpLower

namespace ExpUpper

variable {ι : ℕ → Type*} {U V W : (k : ℕ) → ι k → ℝ} {s : ℕ → ℝ}

theorem comp (h : ExpUpper ι U V s) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ExpUpper (fun k => ι (φ k)) (fun k => U (φ k)) (fun k => V (φ k))
      (fun k => s (φ k)) := by
  intro ε hε
  exact hφ.tendsto_atTop.eventually (h ε hε)

theorem trans (hUV : ExpUpper ι U V s) (hVW : ExpUpper ι V W s) :
    ExpUpper ι U W s := by
  intro ε hε
  filter_upwards [hUV (ε / 2) (by linarith), hVW (ε / 2) (by linarith)] with k hk hk'
  intro i
  calc
    U k i ≤ V k i * Real.exp ((ε / 2) * s k) := hk i
    _ ≤ (W k i * Real.exp ((ε / 2) * s k)) * Real.exp ((ε / 2) * s k) :=
      mul_le_mul_of_nonneg_right (hk' i) (Real.exp_pos _).le
    _ = W k i * Real.exp (ε * s k) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end ExpUpper

/-- Moving the positive exponential factor across an inequality exchanges
the lower and upper conventions; it does not require logarithms or division by mass. -/
theorem expLower_iff_expUpper_reverse {ι : ℕ → Type*}
    (U V : (k : ℕ) → ι k → ℝ) (s : ℕ → ℝ) :
    ExpLower ι U V s ↔ ExpUpper ι V U s := by
  have hcancel (ε : ℝ) (k : ℕ) :
      Real.exp (-ε * s k) * Real.exp (ε * s k) = 1 := by
    rw [← Real.exp_add, show -ε * s k + ε * s k = 0 by ring, Real.exp_zero]
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with k hk
    intro i
    have hm := mul_le_mul_of_nonneg_right (hk i) (Real.exp_pos (ε * s k)).le
    simpa only [mul_assoc, hcancel, mul_one] using hm
  · intro h ε hε
    filter_upwards [h ε hε] with k hk
    intro i
    have hc : Real.exp (ε * s k) * Real.exp (-ε * s k) = 1 := by
      simpa only [mul_comm] using hcancel ε k
    have hm := mul_le_mul_of_nonneg_right (hk i) (Real.exp_pos (-ε * s k)).le
    simpa only [mul_assoc, hc, mul_one] using hm

/-- A fixed finite sum preserves exponential lower accuracy with the same width. -/
theorem expLower_finite_sum {ι : ℕ → Type*} {α : Type*} (S : Finset α)
    (U V : α → (k : ℕ) → ι k → ℝ) (s : ℕ → ℝ)
    (h : ∀ a ∈ S, ExpLower ι (U a) (V a) s) :
    ExpLower ι (fun k i => ∑ a ∈ S, U a k i) (fun k i => ∑ a ∈ S, V a k i) s := by
  intro ε hε
  have hh : ∀ᶠ k in atTop, ∀ a ∈ S, ∀ i : ι k,
      V a k i * Real.exp (-ε * s k) ≤ U a k i :=
    (eventually_all_finset S).mpr (fun a ha => h a ha ε hε)
  filter_upwards [hh] with k hk
  intro i
  simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun a ha => hk a ha i)

/-- The strict margin used at sparse-cones.tex:886–906. It makes the degree
comparison valid for arbitrarily slow vanishing `δ`. -/
theorem strict_margin {δ s : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hs : Tendsto s atTop atTop) {η ε : ℝ} (hgap : ε < η) :
    Tendsto (fun k => δ k * Real.exp (-(η - ε) * s k)) atTop (𝓝 0) := by
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop (sub_pos.mpr hgap) hs)
  simpa only [Function.comp_def, neg_mul, mul_zero] using hδ.mul hexp

/-- A fixed finite list of conditions can be imposed at one threshold. -/
theorem eventually_finite {α : Type*} (S : Finset α) (Q : α → ℕ → Prop)
    (hQ : ∀ a ∈ S, ∀ᶠ k in atTop, Q a k) :
    ∀ᶠ k in atTop, ∀ a ∈ S, Q a k := by
  exact (eventually_all_finset S).mpr hQ

end DistinctDistances.Framework
