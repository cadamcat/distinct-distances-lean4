import DistinctDistances.TrackE.SkewPoint
import DistinctDistances.TrackE.GlobalParameters
import DistinctDistances.Bridges.UniformConcentration

/-!
# `red:global-concentration` (`reduction.tex:348-384`)

Skew forms on `ℂ^{d+1}` enter track A's model through a fixed enumeration of `SkewIdx (d+1)`.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

open Classical in
/-- red:global-concentration (`reduction.tex:348-356`, from `conc:theorem` (a) with `e = d+1`):
for `P, Q` with `|Q| = |P|` and both `M ≤ A`, every set `W ⊆ P × Q` of vertices, and every
irreducible variety `V` of dimension `s₀ + h` (`s₀ = C(d,2)`, `0 ≤ h ≤ d`) in skew-form space,
at most `C deg(V) A^h` pair flats of `W` lie in `V`. -/
theorem global_concentration (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ P Q : Finset (RPoint d), 2 ≤ P.card → Q.card = P.card →
      Mcount P ≤ Ascale d P.card → Mcount Q ≤ Ascale d P.card →
      ∀ W ⊆ P ×ˢ Q, ∀ h : ℕ, h ≤ d →
      ∀ V : AffineVariety (Fintype.card (SkewIdx (d + 1))), V.IsIrreducible →
        V.dimension = Nat.choose d 2 + h →
        ((W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points).card : ℝ) ≤
          C * (V.degree : ℝ) * Ascale d P.card ^ h := by
  classical
  obtain ⟨C, hC, hconc⟩ := Bridges.uniform_concentration_all_dimensions_bridge
    (e := d + 1) (by omega) 5 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro P Q hPcard hQcard hMP hMQ W hW h hh V hV hdim
  let A := Ascale d P.card
  obtain ⟨hA, hNcap, hNtotal⟩ := global_parameter_scale hd P.card hPcard
  let Λ := W.image globalParameter
  have hparams : ∀ l ∈ Λ, l.1 ≠ 0 ∧ ∑ i, l.2 i * l.1 i = 0 := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
    exact global_parameter_quadric x
  have hprop : ∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ c : ℂ, l' = c • l → l' = l := by
    intro l hl l' hl' c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hl'
    exact global_parameter_nonproportional x x' c hc
  have hsep : ∀ l ∈ Λ, ∃ (k : ℕ)
      (f : MvPolynomial (Fin (d + 1) ⊕ Fin (d + 1)) ℂ),
      1 ≤ k ∧ (k : ℝ) ≤ 5 * A ∧ f.IsHomogeneous k ∧
      MvPolynomial.eval (Sum.elim l.1 l.2) f ≠ 0 ∧
      ∀ l' ∈ Λ, l' ≠ l → MvPolynomial.eval (Sum.elim l'.1 l'.2) f = 0 := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨k, f, hk, hkA, hf, hfval, hfzero⟩ :=
      global_parameter_separators P Q A hA hMP hMQ x (hW hx)
    refine ⟨k, f, hk, hkA, hf, hfval, ?_⟩
    intro l' hl' hlne
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hl'
    exact hfzero x' (hW hx') (fun heq => hlne (congrArg globalParameter heq))
  have hcap : ∀ L : Submodule ℂ
      ((Fin (d + 1) → ℂ) × (Fin (d + 1) → ℂ)), Module.finrank ℂ L = d + 1 →
      (∀ x ∈ L, ∀ x' ∈ L, ∑ i, (x.2 i * x'.1 i + x'.2 i * x.1 i) = 0) →
      ((Λ.filter (· ∈ L)).card : ℝ) ≤ 5 * A ^ (d + 1 - 2) := by
    intro L _ hL
    have hcount := global_parameter_isotropic_count P Q W hW L hL
    have hexp : d + 1 - 2 = d - 1 := by omega
    rw [hexp]
    exact hcount.trans (hNcap.trans (by
      have hp : 0 ≤ A ^ (d - 1) := pow_nonneg (le_trans (by norm_num) hA) _
      nlinarith))
  have htotal : (Λ.card : ℝ) ≤ 5 * A ^ (d + 1 - 1) := by
    have hcount : (Λ.card : ℝ) ≤ (P.card : ℝ) ^ 2 := by
      calc (Λ.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast Finset.card_image_le
        _ ≤ ((P ×ˢ Q).card : ℝ) := by exact_mod_cast Finset.card_le_card hW
        _ = (P.card : ℝ) ^ 2 := by rw [Finset.card_product, hQcard]; push_cast; ring
    rw [Nat.add_sub_cancel]
    exact hcount.trans (by
      rw [hNtotal]
      have hp : 0 ≤ A ^ d := pow_nonneg (le_trans (by norm_num) hA) _
      nlinarith)
  have hcount := hconc A hA Λ hparams hprop hsep hcap V hV h
    (by omega) (by simpa only [Nat.add_sub_cancel] using hdim) htotal
  refine le_trans ?_ hcount
  have hmaps : Set.MapsTo (globalParameter (d := d))
      (W.filter fun x => skewToPoint '' pairFlat x.1 x.2 ⊆ V.points)
      (Λ.filter fun l => skewToPoint '' evalFlat l.1 l.2 ⊆ V.points) := by
    intro x hx
    obtain ⟨hxW, hxV⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem globalParameter hxW, hxV⟩
  exact_mod_cast Finset.card_le_card_of_injOn (globalParameter (d := d)) hmaps
    (global_parameter_injective (d := d)).injOn

end Reduction

end

end DistinctDistances
