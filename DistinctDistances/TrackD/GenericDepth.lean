import DistinctDistances.TrackD.Secants
import DistinctDistances.TrackD.GeoTangent
import DistinctDistances.TrackD.GeoCommon
import DistinctDistances.TrackD.MDGeoAux

/-!
# `geo:generic-depth` (`secants.tex:110–219`)

Generic projection depth for weighted families of carriers. Consumers:
`sparse-cones.tex:139–145` (`w = s`, `e = e_j`) and `depth.tex:261` (`w = log B`,
`e = B^{d-l}`).
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

variable {d : ℕ}

/-- Total assigned mass of a family. -/
def famMass (𝒳 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d)) : ℝ :=
  ∑ X ∈ 𝒳, ((S X).card : ℝ)

/-- The moving roots over `π_x y` on the union of a target list: points `z ≠ x` of the listed
varieties on the line through `x` and `y` (`secants.tex:139–142`). -/
def movingRoots (𝒵 : Finset (AffineVariety d)) (x y : Point d) : Set (Point d) :=
  {z | (∃ Z ∈ 𝒵, z ∈ Z) ∧ z ≠ x ∧ ∃ c : ℂ, z - x = c • (y - x)}

/-- `geo:generic-depth.tangent` (`secants.tex:150–158`). For a fixed irreducible target `Y`
of dimension `l < d`, one proper complex flat (`y + T_yY` at a general smooth `y`) contains every
member of a finite source family that is not generically transverse at the target endpoint. -/
theorem generic_depth_tangent_target (Y : AffineVariety d) (l : ℕ) (hY : Y.IsIrreducible)
    (hl : Y.dimension = l) (hld : l < d) (hYne : Y.points.Nonempty)
    (𝒳 : Finset (AffineVariety d)) (h𝒳 : ∀ X ∈ 𝒳, X.IsIrreducible ∧ X.points.Nonempty) :
    ∃ F : AffineSubspace ℂ (Point d), F ≠ ⊤ ∧ ∀ X ∈ 𝒳,
      ForGeneralPair X Y (fun x y => y - x ∉ Y.tangentSpace y) ∨ X.points ⊆ F := by
  obtain ⟨x0, hx0, f0, hf0, hdf0⟩ :=
    GeoTangent.exists_diffNonzero Y l hY hl hld hYne
  refine ⟨AffineSubspace.mk' x0 (Y.tangentSpace x0), ?_, ?_⟩
  · intro htop
    have hdir : Y.tangentSpace x0 = ⊤ := by
      have h := congrArg AffineSubspace.direction htop
      simpa [AffineSubspace.direction_mk', AffineSubspace.direction_top] using h
    have hle : Y.tangentSpace x0 ≤ LinearMap.ker (differential f0 x0) := by
      have hle2 := iInf_le
        (fun f : ↥Y.ideal => LinearMap.ker (differential ↑f x0)) ⟨f0, hf0⟩
      show (⨅ f : ↥Y.ideal, LinearMap.ker (differential ↑f x0)) ≤ _
      exact hle2
    rw [hdir] at hle
    have hker : LinearMap.ker (differential f0 x0) = ⊤ := top_unique hle
    have h0 : differential f0 x0 = 0 := by
      apply LinearMap.ext
      intro v
      have hmem : v ∈ LinearMap.ker (differential f0 x0) := by
        rw [hker]
        trivial
      exact LinearMap.mem_ker.mp hmem
    exact hdf0 h0
  · intro X hX
    exact GeoTangent.perW Y x0 hx0 X

/-- `geo:generic-depth.tangent`, source endpoint (`secants.tex:156–157`). -/
theorem generic_depth_tangent_source (X : AffineVariety d) (k : ℕ) (hX : X.IsIrreducible)
    (hk : X.dimension = k) (hkd : k < d) (hXne : X.points.Nonempty)
    (𝒴 : Finset (AffineVariety d)) (h𝒴 : ∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.points.Nonempty) :
    ∃ F : AffineSubspace ℂ (Point d), F ≠ ⊤ ∧ ∀ Y ∈ 𝒴,
      ForGeneralPair X Y (fun x y => y - x ∉ X.tangentSpace x) ∨ Y.points ⊆ F := by
  obtain ⟨x0, hx0, f0, hf0, hdf0⟩ :=
    GeoTangent.exists_diffNonzero X k hX hk hkd hXne
  refine ⟨AffineSubspace.mk' x0 (X.tangentSpace x0), ?_, ?_⟩
  · intro htop
    have hdir : X.tangentSpace x0 = ⊤ := by
      have h := congrArg AffineSubspace.direction htop
      simpa [AffineSubspace.direction_mk', AffineSubspace.direction_top] using h
    have hle : X.tangentSpace x0 ≤ LinearMap.ker (differential f0 x0) := by
      have hle2 := iInf_le
        (fun f : ↥X.ideal => LinearMap.ker (differential ↑f x0)) ⟨f0, hf0⟩
      show (⨅ f : ↥X.ideal, LinearMap.ker (differential ↑f x0)) ≤ _
      exact hle2
    rw [hdir] at hle
    have hker : LinearMap.ker (differential f0 x0) = ⊤ := top_unique hle
    have h0 : differential f0 x0 = 0 := by
      apply LinearMap.ext
      intro v
      have hmem : v ∈ LinearMap.ker (differential f0 x0) := by
        rw [hker]
        trivial
      exact LinearMap.mem_ker.mp hmem
    exact hdf0 h0
  · intro Y hY
    exact GeoTangent.perW_source X x0 hx0 Y

/-- `geo:generic-depth.commonflat` (`secants.tex:160–165`). A nonlinear irreducible
`k`-dimensional variety contained in an affine flat of dimension at most `k + 1` spans that flat;
in particular all such flats coincide with its span, which is proper when `k + 1 < d`. -/
theorem generic_depth_commonflat (X : AffineVariety d) (k : ℕ) (hX : X.IsIrreducible)
    (hk : X.dimension = k) (hXne : X.points.Nonempty) (hnl : ¬ IsFlat X) (hkd : k + 1 < d) :
    ∀ G : AffineSubspace ℂ (Point d),
      Module.finrank ℂ G.direction ≤ k + 1 → X.points ⊆ G →
        complexSpan X ≠ ⊤ ∧ G = complexSpan X := by
  intro G hG hXG
  exact GeoCommon.commonflat_aux X k hX hk hXne hnl hkd G hG hXG

private lemma sum_odd_range_real (n : ℕ) :
    (∑ r ∈ Finset.range n, ((2 * r + 1 : ℕ) : ℝ)) = (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private lemma sum_inv_shift_sq_Ico_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico a b, 1 / ((r + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (a : ℝ) := by
  have htel (a b : ℕ) (hab : a ≤ b) :
      (∑ r ∈ Finset.Ico a b, (1 / (r : ℝ) - 1 / ((r + 1 : ℕ) : ℝ))) =
        1 / (a : ℝ) - 1 / (b : ℝ) := by
    induction b generalizing a with
    | zero =>
        have : a = 0 := by omega
        subst a
        simp
    | succ b ih =>
        by_cases h : a ≤ b
        · rw [Finset.sum_Ico_succ_top h, ih a h]
          push_cast
          ring
        · have ha' : a = b + 1 := by omega
          subst a
          simp
  have hterm : ∀ r ∈ Finset.Ico a b,
      1 / ((r + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (r : ℝ) - 1 / ((r + 1 : ℕ) : ℝ) := by
    intro r hr
    have hrpos : 0 < (r : ℝ) := by
      have : 0 < r := by
        have := (Finset.mem_Ico.mp hr).1
        omega
      exact_mod_cast this
    have hr1pos : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
    have hcalc : (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) := by norm_num
    rw [← hcalc]
    have hfrac : 1 / (r : ℝ) - 1 / ((r : ℝ) + 1) =
        1 / ((r : ℝ) * ((r : ℝ) + 1)) := by
      field_simp
      ring
    have hprod : (r : ℝ) * ((r : ℝ) + 1) ≤ ((r : ℝ) + 1) ^ 2 := by
      nlinarith [hrpos]
    rw [hfrac]
    exact one_div_le_one_div_of_le (by positivity) hprod
  calc
    _ ≤ ∑ r ∈ Finset.Ico a b, (1 / (r : ℝ) - 1 / ((r + 1 : ℕ) : ℝ)) :=
      Finset.sum_le_sum fun r hr => hterm r hr
    _ = 1 / (a : ℝ) - 1 / (b : ℝ) := htel a b hab
    _ ≤ 1 / (a : ℝ) := by
      have hbpos : 0 < (b : ℝ) := by
        have : 0 < b := by omega
        exact_mod_cast this
      have : 0 ≤ 1 / (b : ℝ) := by positivity
      linarith

private lemma sum_nat_sq_by_layers {α : Type*} [DecidableEq α] (A : Finset α)
    (occ : α → ℕ) (T : ℕ) (hocc : ∀ a ∈ A, occ a ≤ T) :
    (∑ a ∈ A, (occ a : ℝ) ^ 2) =
      ∑ r ∈ Finset.range T,
        ((2 * r + 1 : ℕ) : ℝ) * ((A.filter (fun a => r < occ a)).card : ℝ) := by
  calc
    (∑ a ∈ A, (occ a : ℝ) ^ 2) =
        ∑ a ∈ A, ∑ r ∈ Finset.range T,
          if r < occ a then ((2 * r + 1 : ℕ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have hfilter : (Finset.range T).filter (fun r => r < occ a) = Finset.range (occ a) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range]
        have hle := hocc a ha
        omega
      rw [← sum_odd_range_real (occ a), ← hfilter, Finset.sum_filter]
    _ = ∑ r ∈ Finset.range T, ∑ a ∈ A,
          if r < occ a then ((2 * r + 1 : ℕ) : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.range T,
          ((2 * r + 1 : ℕ) : ℝ) * ((A.filter (fun a => r < occ a)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      ring

private lemma occ_second_moment_le_of_tail {α : Type*} [DecidableEq α]
    (A : Finset α) (occ : α → ℕ) (n τ tmax C : ℝ)
    (hτ : 2 ≤ τ) (ht : τ ≤ tmax) (hn : 0 ≤ n) (hC : 0 < C)
    (hheavy : ∀ a ∈ A, τ ≤ (occ a : ℝ))
    (hocc : ∀ a ∈ A, (occ a : ℝ) ≤ tmax)
    (hTail : ∀ t : ℝ, 2 ≤ t →
      ((A.filter (fun a => t ≤ (occ a : ℝ))).card : ℝ) ≤
        C * (n ^ 2 / t ^ 3 + n / t)) :
    (∑ a ∈ A, (occ a : ℝ) ^ 2) ≤ 8 * C * (n ^ 2 / τ + n * tmax) := by
  classical
  let U := Nat.ceil τ
  let T := Nat.ceil tmax
  let low := (Finset.range T).filter (fun r => r + 1 < U)
  let high := (Finset.range T).filter (fun r => U ≤ r + 1)
  have hτ0 : 0 ≤ τ := by linarith
  have ht0 : 0 ≤ tmax := by linarith
  have hUcast : τ ≤ (U : ℝ) := by
    exact Nat.le_ceil τ
  have hTcast : tmax ≤ (T : ℝ) := by
    exact Nat.le_ceil tmax
  have hUge : 2 ≤ U := by
    have : (2 : ℝ) ≤ (U : ℝ) := le_trans hτ hUcast
    exact_mod_cast this
  have hTge : 2 ≤ T := by
    have : (2 : ℝ) ≤ (T : ℝ) := le_trans hτ (le_trans ht hTcast)
    exact_mod_cast this
  have hUT : U ≤ T := (Nat.ceil_le).2 (le_trans ht hTcast)
  have hUle : (U : ℝ) ≤ 2 * τ := by
    have hceil : (U : ℝ) < τ + 1 := by
      simpa [U] using (Nat.ceil_lt_add_one hτ0)
    nlinarith [hτ]
  have hTle : (T : ℝ) ≤ 2 * tmax := by
    have hceil : (T : ℝ) < tmax + 1 := by
      simpa [T] using (Nat.ceil_lt_add_one ht0)
    nlinarith [hτ, ht]
  have hoccNat : ∀ a ∈ A, occ a ≤ T := by
    intro a ha
    have hcast : (occ a : ℝ) ≤ (T : ℝ) := le_trans (hocc a ha) hTcast
    exact_mod_cast hcast
  have hTailτ : (A.card : ℝ) ≤ C * (n ^ 2 / τ ^ 3 + n / τ) := by
    have hfilter : A.filter (fun a => τ ≤ (occ a : ℝ)) = A := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro ha
        exact ⟨ha, hheavy a ha⟩
    simpa [hfilter] using hTail τ hτ
  have hlowCard : ∀ r ∈ low,
      ((A.filter (fun a => r < occ a)).card : ℝ) ≤
        C * (n ^ 2 / τ ^ 3 + n / τ) := by
    intro r hr
    have hrU : r + 1 < U := (Finset.mem_filter.mp hr).2
    have hrτ : ((r + 1 : ℕ) : ℝ) < τ := by
      have hnot : ¬ τ ≤ ((r + 1 : ℕ) : ℝ) := by
        intro h
        have hc : U ≤ r + 1 := (Nat.ceil_le).2 h
        omega
      exact lt_of_not_ge hnot
    have hEq : A.filter (fun a => r < occ a) = A := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro ha
        have hrle : ((r + 1 : ℕ) : ℝ) ≤ (occ a : ℝ) :=
          le_trans (le_of_lt hrτ) (hheavy a ha)
        have hrleNat : r + 1 ≤ occ a := by exact_mod_cast hrle
        exact ⟨ha, by omega⟩
    simpa [hEq] using hTailτ
  have hhighCard : ∀ r ∈ high,
      ((A.filter (fun a => r < occ a)).card : ℝ) ≤
        C * (n ^ 2 / ((r + 1 : ℕ) : ℝ) ^ 3 + n / ((r + 1 : ℕ) : ℝ)) := by
    intro r hr
    have hrU : U ≤ r + 1 := (Finset.mem_filter.mp hr).2
    let t : ℝ := ((r + 1 : ℕ) : ℝ)
    have hrUcast : (U : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast hrU
    have hτt : τ ≤ t := by dsimp [t]; exact le_trans hUcast hrUcast
    have ht2 : 2 ≤ t := le_trans hτ hτt
    have hEq : A.filter (fun a => r < occ a) =
        A.filter (fun a => t ≤ (occ a : ℝ)) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha, hlt⟩
        refine ⟨ha, ?_⟩
        have hnat : r + 1 ≤ occ a := by omega
        dsimp [t]
        exact_mod_cast hnat
      · rintro ⟨ha, hle⟩
        refine ⟨ha, ?_⟩
        have hle' : ((r + 1 : ℕ) : ℝ) ≤ (occ a : ℝ) := by simpa [t] using hle
        have hnat : r + 1 ≤ occ a := by exact_mod_cast hle'
        omega
    simpa [t, hEq] using hTail t ht2
  have hlayer := sum_nat_sq_by_layers A occ T hoccNat
  rw [hlayer]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range T)
    (fun r => U ≤ r + 1)
    (fun r => ((2 * r + 1 : ℕ) : ℝ) *
      ((A.filter (fun a => r < occ a)).card : ℝ))
  rw [← hsplit]
  have hLowBound :
      (∑ r ∈ low, ((2 * r + 1 : ℕ) : ℝ) *
        ((A.filter (fun a => r < occ a)).card : ℝ)) ≤
        4 * C * (n ^ 2 / τ + n * tmax) := by
    have hterm : ∀ r ∈ low,
        ((2 * r + 1 : ℕ) : ℝ) *
          ((A.filter (fun a => r < occ a)).card : ℝ) ≤
        ((2 * r + 1 : ℕ) : ℝ) * (C * (n ^ 2 / τ ^ 3 + n / τ)) := by
      intro r hr
      have hcard := hlowCard r hr
      have hodd : 0 ≤ ((2 * r + 1 : ℕ) : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hcard hodd
    have hsumTerm := Finset.sum_le_sum hterm
    have hlowOdds : (∑ r ∈ low, ((2 * r + 1 : ℕ) : ℝ)) ≤ (U : ℝ) ^ 2 := by
      have hsubset : low ⊆ Finset.range U := by
        intro r hr
        have hh := (Finset.mem_filter.mp hr).2
        simp only [Finset.mem_range]
        omega
      calc
        _ ≤ ∑ r ∈ Finset.range U, ((2 * r + 1 : ℕ) : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro r hr hrnot
          positivity
        _ = (U : ℝ) ^ 2 := sum_odd_range_real U
    have hTlow : (U : ℝ) ^ 2 ≤ 4 * τ ^ 2 := by
      have hU0 : 0 ≤ (U : ℝ) := by positivity
      have hτ0' : 0 ≤ τ := by linarith
      nlinarith [sq_nonneg ((2 * τ) - (U : ℝ))]
    have hval : C * (n ^ 2 / τ ^ 3 + n / τ) ≥ 0 := by positivity
    calc
      _ ≤ ∑ r ∈ low, ((2 * r + 1 : ℕ) : ℝ) *
          (C * (n ^ 2 / τ ^ 3 + n / τ)) := hsumTerm
      _ = (∑ r ∈ low, ((2 * r + 1 : ℕ) : ℝ)) *
          (C * (n ^ 2 / τ ^ 3 + n / τ)) := by rw [Finset.sum_mul]
      _ ≤ (U : ℝ) ^ 2 * (C * (n ^ 2 / τ ^ 3 + n / τ)) :=
        mul_le_mul_of_nonneg_right hlowOdds hval
      _ ≤ 4 * C * (n ^ 2 / τ + n * tmax) := by
        have hτpos : 0 < τ := by linarith
        calc
          _ ≤ (4 * τ ^ 2) * (C * (n ^ 2 / τ ^ 3 + n / τ)) :=
            mul_le_mul_of_nonneg_right hTlow hval
          _ = 4 * C * (n ^ 2 / τ + n * τ) := by
            field_simp
          _ ≤ 4 * C * (n ^ 2 / τ + n * tmax) := by
            gcongr
  have hHighBound :
      (∑ r ∈ high, ((2 * r + 1 : ℕ) : ℝ) *
        ((A.filter (fun a => r < occ a)).card : ℝ)) ≤
        4 * C * (n ^ 2 / τ + n * tmax) := by
    have hterm : ∀ r ∈ high,
        ((2 * r + 1 : ℕ) : ℝ) *
          ((A.filter (fun a => r < occ a)).card : ℝ) ≤
        2 * C * (n ^ 2 / ((r + 1 : ℕ) : ℝ) ^ 2 + n) := by
      intro r hr
      have hcard := hhighCard r hr
      let t : ℝ := ((r + 1 : ℕ) : ℝ)
      have htpos : 0 < t := by
        have hnat : 0 < r + 1 := by omega
        dsimp [t]
        exact_mod_cast hnat
      have ht0 : 0 ≤ t := le_of_lt htpos
      have hodd : ((2 * r + 1 : ℕ) : ℝ) ≤ 2 * t := by
        dsimp [t]
        push_cast
        nlinarith
      have htail0 : 0 ≤ n ^ 2 / t ^ 3 + n / t := by positivity
      have htail0' : 0 ≤ C * (n ^ 2 / t ^ 3 + n / t) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hcard (by positivity : 0 ≤ ((2 * r + 1 : ℕ) : ℝ))
      have hmul' := mul_le_mul_of_nonneg_right hodd htail0'
      have hcalc :
          (2 * t) * (C * (n ^ 2 / t ^ 3 + n / t)) =
            2 * C * (n ^ 2 / t ^ 2 + n) := by
        field_simp <;> ring
      calc
        _ ≤ ((2 * r + 1 : ℕ) : ℝ) * (C * (n ^ 2 / t ^ 3 + n / t)) := hmul
        _ ≤ (2 * t) * (C * (n ^ 2 / t ^ 3 + n / t)) := by
          exact mul_le_mul_of_nonneg_right hodd htail0'
        _ = 2 * C * (n ^ 2 / t ^ 2 + n) := hcalc
    have hsumTerm := Finset.sum_le_sum hterm
    have hhighEq : high = Finset.Ico (U - 1) T := by
      ext r
      simp only [high, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      have hsub : U - 1 + 1 = U := Nat.sub_add_cancel (by omega : 1 ≤ U)
      omega
    have hrecip :
        (∑ r ∈ high, 1 / ((r + 1 : ℕ) : ℝ) ^ 2) ≤ 2 / τ := by
      rw [hhighEq]
      have hUminus : 1 ≤ U - 1 := by omega
      have hUminusT : U - 1 ≤ T := by omega
      have hsum := sum_inv_shift_sq_Ico_le (U - 1) T hUminus hUminusT
      have hden : τ / 2 ≤ ((U - 1 : ℕ) : ℝ) := by
        have hUcast' : ((U - 1 : ℕ) : ℝ) + 1 = (U : ℝ) := by
          exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ U))
        have hUminus : ((U - 1 : ℕ) : ℝ) = (U : ℝ) - 1 := by linarith
        rw [hUminus]
        linarith [hτ]
      have hrecip' : 1 / ((U - 1 : ℕ) : ℝ) ≤ 2 / τ := by
        have hτp : 0 < τ := by linarith
        have hle : 1 / ((U - 1 : ℕ) : ℝ) ≤ 1 / (τ / 2) :=
          one_div_le_one_div_of_le (by positivity) hden
        have hform : 1 / (τ / 2) = 2 / τ := by field_simp
        rw [hform] at hle
        exact hle
      exact le_trans hsum hrecip'
    have hhighCardBound : (high.card : ℝ) ≤ 2 * tmax := by
      rw [hhighEq]
      have hsubset : Finset.Ico (U - 1) T ⊆ Finset.range T := by
        intro r hr
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2
      have hcard := Finset.card_le_card hsubset
      have hcard' : ((Finset.range T).card : ℝ) ≤ 2 * tmax := by
        simpa using hTle
      exact le_trans (by exact_mod_cast hcard) hcard'
    have hn : 0 ≤ n := by positivity
    have hsumrewrite :
        (∑ r ∈ high, 2 * C * (n ^ 2 / ((r + 1 : ℕ) : ℝ) ^ 2 + n)) =
          2 * C * (n ^ 2 * (∑ r ∈ high, 1 / ((r + 1 : ℕ) : ℝ) ^ 2) +
            n * (high.card : ℝ)) := by
      calc
        _ = ∑ r ∈ high,
            ((2 * C * n ^ 2) * (1 / ((r + 1 : ℕ) : ℝ) ^ 2) + 2 * C * n) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          ring
        _ = (2 * C * n ^ 2) *
            (∑ r ∈ high, 1 / ((r + 1 : ℕ) : ℝ) ^ 2) +
            (2 * C * n) * (high.card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
        _ = 2 * C * (n ^ 2 *
            (∑ r ∈ high, 1 / ((r + 1 : ℕ) : ℝ) ^ 2) +
            n * (high.card : ℝ)) := by ring
    calc
      _ ≤ ∑ r ∈ high, 2 * C *
          (n ^ 2 / ((r + 1 : ℕ) : ℝ) ^ 2 + n) := hsumTerm
      _ = 2 * C * (n ^ 2 *
          (∑ r ∈ high, 1 / ((r + 1 : ℕ) : ℝ) ^ 2) +
          n * (high.card : ℝ)) := hsumrewrite
      _ ≤ 4 * C * (n ^ 2 / τ + n * tmax) := by
        have hinner : n ^ 2 * (∑ r ∈ high, 1 / ((r + 1 : ℕ) : ℝ) ^ 2) +
            n * (high.card : ℝ) ≤ n ^ 2 * (2 / τ) + n * (2 * tmax) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hrecip (sq_nonneg n))
            (mul_le_mul_of_nonneg_left hhighCardBound hn)
        calc
          _ ≤ 2 * C * (n ^ 2 * (2 / τ) + n * (2 * tmax)) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
          _ = 4 * C * (n ^ 2 / τ + n * tmax) := by ring
  have hresult := add_le_add hLowBound hHighBound
  simp only [low, high, not_le]
  nlinarith [hresult]

/-- `geo:generic-depth.flatslice-core` (`secants.tex:188–209`), abstract form: weighted points
and rich lines in `ℝ^m`. If at most `C(n^2/t^3 + n/t)` lines contain `t ≥ 2` points, then the
squared weight carried by lines with at least `τ ≥ 2` points is at most
`C' ω_max^2 (n^2/τ + n t_max)`, `t_max` the largest occupancy. -/
theorem flatslice_core (m : ℕ) (hST : STRichLines m) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (Q : Finset (Pt m)) (ω : Pt m → ℝ) (ωmax τ tmax : ℝ)
      (𝓛 : Finset (AffineSubspace ℝ (Pt m))),
      (∀ q ∈ Q, 0 ≤ ω q ∧ ω q ≤ ωmax) → 2 ≤ τ → 0 ≤ tmax →
      (∀ ℓ ∈ 𝓛, IsRealLine ℓ ∧ (occ Q ℓ : ℝ) ≤ tmax) →
      ∑ ℓ ∈ 𝓛.filter (fun ℓ => τ ≤ (occ Q ℓ : ℝ)), (∑ q ∈ Q.filter (· ∈ ℓ), ω q) ^ 2 ≤
        C' * ωmax ^ 2 * ((Q.card : ℝ) ^ 2 / τ + Q.card * tmax) := by
  rcases hST with ⟨C, hC, hRich⟩
  refine ⟨8 * C, by positivity, ?_⟩
  intro Q ω ωmax τ tmax 𝓛 hω hτ htmax hlines
  let H := 𝓛.filter (fun ℓ => τ ≤ (occ Q ℓ : ℝ))
  let lineWeight : AffineSubspace ℝ (Pt m) → ℝ := fun ℓ =>
    ∑ q ∈ Q.filter (· ∈ ℓ), ω q
  by_cases hH : H.Nonempty
  · obtain ⟨ℓ₀, hℓ₀⟩ := hH
    have hℓ₀L : ℓ₀ ∈ 𝓛 := (Finset.mem_filter.mp hℓ₀).1
    have hτocc₀ : τ ≤ (occ Q ℓ₀ : ℝ) := (Finset.mem_filter.mp hℓ₀).2
    have htmax₀ : (occ Q ℓ₀ : ℝ) ≤ tmax := (hlines ℓ₀ hℓ₀L).2
    have hτtmax : τ ≤ tmax := le_trans hτocc₀ htmax₀
    have hoccpos₀ : 0 < occ Q ℓ₀ := by
      have hpos : (1 : ℝ) ≤ (occ Q ℓ₀ : ℝ) := by linarith
      exact_mod_cast hpos
    have hfilterNe : (Q.filter (· ∈ ℓ₀)).Nonempty := by
      exact Finset.card_pos.mp (by simpa [occ] using hoccpos₀)
    obtain ⟨q₀, hq₀⟩ := hfilterNe
    have hq₀Q : q₀ ∈ Q := (Finset.mem_filter.mp hq₀).1
    have hωmax : 0 ≤ ωmax := le_trans (hω q₀ hq₀Q).1 (hω q₀ hq₀Q).2
    have hTail : ∀ t : ℝ, 2 ≤ t →
        ((H.filter (fun ℓ => t ≤ (occ Q ℓ : ℝ))).card : ℝ) ≤
          C * ((Q.card : ℝ) ^ 2 / t ^ 3 + Q.card / t) := by
      intro t ht
      have hrichLines : ∀ ℓ ∈ H.filter (fun ℓ => t ≤ (occ Q ℓ : ℝ)),
          IsRealLine ℓ ∧ t ≤ (occ Q ℓ : ℝ) := by
        intro ℓ hℓ
        have hℓH : ℓ ∈ H := (Finset.mem_filter.mp hℓ).1
        have hℓL : ℓ ∈ 𝓛 := (Finset.mem_filter.mp hℓH).1
        exact ⟨(hlines ℓ hℓL).1, (Finset.mem_filter.mp hℓ).2⟩
      exact hRich Q (H.filter (fun ℓ => t ≤ (occ Q ℓ : ℝ))) t ht hrichLines
    have hsecond :
        (∑ ℓ ∈ H, (occ Q ℓ : ℝ) ^ 2) ≤
          8 * C * ((Q.card : ℝ) ^ 2 / τ + Q.card * tmax) := by
      apply occ_second_moment_le_of_tail H (occ Q) (Q.card : ℝ) τ tmax C
        hτ hτtmax (by positivity) hC
      · intro ℓ hℓ
        exact (Finset.mem_filter.mp hℓ).2
      · intro ℓ hℓ
        exact (hlines ℓ ((Finset.mem_filter.mp hℓ).1)).2
      · exact hTail
    have hlineWeightNonneg (ℓ : AffineSubspace ℝ (Pt m)) : 0 ≤ lineWeight ℓ := by
      apply Finset.sum_nonneg
      intro q hq
      exact (hω q ((Finset.mem_filter.mp hq).1)).1
    have hlineWeightLe (ℓ : AffineSubspace ℝ (Pt m)) :
        lineWeight ℓ ≤ ωmax * (occ Q ℓ : ℝ) := by
      dsimp [lineWeight]
      calc
        _ ≤ ∑ q ∈ Q.filter (· ∈ ℓ), ωmax := by
          apply Finset.sum_le_sum
          intro q hq
          exact (hω q ((Finset.mem_filter.mp hq).1)).2
        _ = ((Q.filter (· ∈ ℓ)).card : ℝ) * ωmax := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ = ωmax * (occ Q ℓ : ℝ) := by
          simp [occ, mul_comm]
    have hlineSq (ℓ : AffineSubspace ℝ (Pt m)) :
        lineWeight ℓ ^ 2 ≤ ωmax ^ 2 * (occ Q ℓ : ℝ) ^ 2 := by
      have hocc0 : 0 ≤ (occ Q ℓ : ℝ) := by positivity
      have htop0 : 0 ≤ ωmax * (occ Q ℓ : ℝ) := mul_nonneg hωmax hocc0
      have hw0 : 0 ≤ lineWeight ℓ := hlineWeightNonneg ℓ
      have hprod : 0 ≤
          (ωmax * (occ Q ℓ : ℝ) - lineWeight ℓ) *
          (ωmax * (occ Q ℓ : ℝ) + lineWeight ℓ) :=
        mul_nonneg (sub_nonneg.mpr (hlineWeightLe ℓ)) (add_nonneg htop0 hw0)
      calc
        _ ≤ (ωmax * (occ Q ℓ : ℝ)) ^ 2 := by nlinarith [hprod]
        _ = ωmax ^ 2 * (occ Q ℓ : ℝ) ^ 2 := by ring
    have hweighted :
        (∑ ℓ ∈ H, lineWeight ℓ ^ 2) ≤
          ωmax ^ 2 * (∑ ℓ ∈ H, (occ Q ℓ : ℝ) ^ 2) := by
      calc
        _ ≤ ∑ ℓ ∈ H, ωmax ^ 2 * (occ Q ℓ : ℝ) ^ 2 :=
          Finset.sum_le_sum fun ℓ hℓ => hlineSq ℓ
        _ = ωmax ^ 2 * (∑ ℓ ∈ H, (occ Q ℓ : ℝ) ^ 2) := by
          rw [← Finset.mul_sum]
    change (∑ ℓ ∈ H, lineWeight ℓ ^ 2) ≤
      8 * C * ωmax ^ 2 * ((Q.card : ℝ) ^ 2 / τ + Q.card * tmax)
    calc
      _ ≤ ωmax ^ 2 * (∑ ℓ ∈ H, (occ Q ℓ : ℝ) ^ 2) := hweighted
      _ ≤ ωmax ^ 2 * (8 * C * ((Q.card : ℝ) ^ 2 / τ + Q.card * tmax)) :=
        mul_le_mul_of_nonneg_left hsecond (sq_nonneg ωmax)
      _ = 8 * C * ωmax ^ 2 * ((Q.card : ℝ) ^ 2 / τ + Q.card * tmax) := by ring
  · have hEmpty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    simp [H, hEmpty]
    positivity

theorem famMass_nonneg (𝒳 : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) : 0 ≤ famMass 𝒳 S := by
  exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- Disjoint assignments in a subfamily share the physical mass bound of
any set containing their carriers. -/
theorem assignment_subfamily_mass_on (P : Finset (Pt d))
    (𝒳 I : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d))
    (hS : Assignment P 𝒳 S) (hI : I ⊆ 𝒳) (A : Set (Point d))
    (hA : ∀ X ∈ I, X.points ⊆ A) : famMass I S ≤ (massOn P A : ℝ) := by
  have hd : (I : Set (AffineVariety d)).PairwiseDisjoint S := by
    intro X hX Y hY hne
    exact hS.disjoint (hI hX) (hI hY) hne
  have hsub : I.biUnion S ⊆ P.filter (fun q => toC q ∈ A) := by
    intro q hq
    obtain ⟨X, hX, hq⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_filter.mpr
      ⟨hS.subset X (hI hX) hq, hA X hX (hS.mem X (hI hX) q hq)⟩
  have hcard : (∑ X ∈ I, (S X).card) ≤ massOn P A := by
    rw [← Finset.card_biUnion hd]
    exact Finset.card_le_card hsub
  unfold famMass
  exact_mod_cast hcard

theorem assignment_subfamily_flat_cap (P : Finset (Pt d)) (c₀ : ℝ)
    (hcap : RealFlatCap P c₀) (𝒳 I : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) (hS : Assignment P 𝒳 S)
    (hI : I ⊆ 𝒳) (F : AffineSubspace ℂ (Point d)) (hF : F ≠ ⊤)
    (hsub : ∀ X ∈ I, X.points ⊆ F) :
    famMass I S ≤ cfgN P * cfgB P ^ (-c₀) := by
  exact (assignment_subfamily_mass_on P 𝒳 I S hS hI F hsub).trans
    (complexFlatCap_of_real P c₀ hcap F hF)

/-- Weighted union bound for deleting either of two pair predicates. -/
theorem discarded_product_weight_le {α β : Type*}
    (I : Finset α) (J : Finset β) (a : α → ℝ) (b : β → ℝ)
    (Q R : α → β → Prop) (A B : ℝ)
    (ha : ∀ x ∈ I, 0 ≤ a x) (hb : ∀ y ∈ J, 0 ≤ b y)
    (hQ : ∀ x ∈ I, (∑ y ∈ J.filter (fun y => ¬ Q x y), b y) ≤ A)
    (hR : ∀ y ∈ J, (∑ x ∈ I.filter (fun x => ¬ R x y), a x) ≤ B) :
    (∑ x ∈ I, ∑ y ∈ J \ J.filter (fun y => Q x y ∧ R x y), a x * b y) ≤
      A * (∑ x ∈ I, a x) + B * (∑ y ∈ J, b y) := by
  classical
  have hdiff (x : α) : J \ J.filter (fun y => Q x y ∧ R x y) =
      J.filter (fun y => ¬ (Q x y ∧ R x y)) := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  simp_rw [hdiff, Finset.sum_filter]
  calc
    _ ≤ ∑ x ∈ I, ∑ y ∈ J,
        ((if ¬ Q x y then a x * b y else 0) +
          (if ¬ R x y then a x * b y else 0)) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have hprod := mul_nonneg (ha x hx) (hb y hy)
      by_cases hq : Q x y <;> by_cases hr : R x y <;> simp [hq, hr] <;> linarith
    _ = (∑ x ∈ I, a x * (∑ y ∈ J.filter (fun y => ¬ Q x y), b y)) +
        (∑ y ∈ J, b y * (∑ x ∈ I.filter (fun x => ¬ R x y), a x)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_filter]
      congr 1
      · simp_rw [Finset.mul_sum, mul_ite, mul_zero]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        simp only [Finset.mul_sum, mul_ite, mul_zero, mul_comm]
    _ ≤ (∑ x ∈ I, a x * A) + (∑ y ∈ J, b y * B) := by
      exact add_le_add
        (Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hQ x hx) (ha x hx))
        (Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (hR y hy) (hb y hy))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

/-- The two tangent endpoint deletions cost at most one flat cap per
opposite-family mass (`secants.tex:150–158`). -/
theorem generic_depth_transverse_pruning (P : Finset (Pt d)) (c₀ : ℝ)
    (hcap : RealFlatCap P c₀) (k l : ℕ) (hkd : k < d) (hld : l < d)
    (𝒳 𝒴 : Finset (AffineVariety d)) (S T : AffineVariety d → Finset (Pt d))
    (h𝒳 : ∀ X ∈ 𝒳, X.IsIrreducible ∧ X.dimension = k)
    (h𝒴 : ∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = l)
    (hS : Assignment P 𝒳 S) (hT : Assignment P 𝒴 T) :
    ∃ L : AffineVariety d → Finset (AffineVariety d),
      (∀ X ∈ 𝒳, L X ⊆ 𝒴) ∧
      (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, ((S X).card : ℝ) * (T Y).card) ≤
        cfgN P * cfgB P ^ (-c₀) * (famMass 𝒳 S + famMass 𝒴 T) ∧
      ∀ X ∈ 𝒳, ∀ Y ∈ L X, GenericallyTransverse X Y := by
  classical
  let Q := fun X Y : AffineVariety d =>
    ForGeneralPair X Y (fun x y => y - x ∉ X.tangentSpace x)
  let R := fun X Y : AffineVariety d =>
    ForGeneralPair X Y (fun x y => y - x ∉ Y.tangentSpace y)
  let L := fun X => 𝒴.filter (fun Y => Q X Y ∧ R X Y)
  have h𝒳ne : ∀ X ∈ 𝒳, X.IsIrreducible ∧ X.points.Nonempty := by
    intro X hX
    exact ⟨(h𝒳 X hX).1, X.points_nonempty_of_isIrreducible (h𝒳 X hX).1⟩
  have h𝒴ne : ∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.points.Nonempty := by
    intro Y hY
    exact ⟨(h𝒴 Y hY).1, Y.points_nonempty_of_isIrreducible (h𝒴 Y hY).1⟩
  have hQ : ∀ X ∈ 𝒳, famMass (𝒴.filter (fun Y => ¬ Q X Y)) T ≤
      cfgN P * cfgB P ^ (-c₀) := by
    intro X hX
    obtain ⟨F, hF, hbad⟩ := generic_depth_tangent_source X k (h𝒳 X hX).1
      (h𝒳 X hX).2 hkd (h𝒳ne X hX).2 𝒴 h𝒴ne
    apply assignment_subfamily_flat_cap P c₀ hcap 𝒴 _ T hT (Finset.filter_subset _ _) F hF
    intro Y hY
    obtain ⟨hY, hn⟩ := Finset.mem_filter.mp hY
    exact (hbad Y hY).resolve_left hn
  have hR : ∀ Y ∈ 𝒴, famMass (𝒳.filter (fun X => ¬ R X Y)) S ≤
      cfgN P * cfgB P ^ (-c₀) := by
    intro Y hY
    obtain ⟨F, hF, hbad⟩ := generic_depth_tangent_target Y l (h𝒴 Y hY).1
      (h𝒴 Y hY).2 hld (h𝒴ne Y hY).2 𝒳 h𝒳ne
    apply assignment_subfamily_flat_cap P c₀ hcap 𝒳 _ S hS (Finset.filter_subset _ _) F hF
    intro X hX
    obtain ⟨hX, hn⟩ := Finset.mem_filter.mp hX
    exact (hbad X hX).resolve_left hn
  refine ⟨L, fun X _ => Finset.filter_subset _ _, ?_, ?_⟩
  · have h := discarded_product_weight_le 𝒳 𝒴 (fun X => ((S X).card : ℝ))
      (fun Y => ((T Y).card : ℝ)) Q R
      (cfgN P * cfgB P ^ (-c₀)) (cfgN P * cfgB P ^ (-c₀))
      (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _) hQ hR
    change _ ≤ _ at h
    change _ ≤ _
    simpa only [famMass, mul_add] using h
  · intro X hX Y hY
    obtain ⟨hY, hq, hr⟩ := Finset.mem_filter.mp hY
    exact hq.and (h𝒳 X hX).1 (h𝒴 Y hY).1 hr

/-- A nonlinear source pins every containing small common flat to its span.
All targets sharing such a flat therefore have only one physical cap in total. -/
theorem generic_depth_nonlinear_commonflat_mass (P : Finset (Pt d)) (c₀ : ℝ)
    (hcap : RealFlatCap P c₀) (X : AffineVariety d) (k : ℕ)
    (hX : X.IsIrreducible) (hk : X.dimension = k) (hnl : ¬ IsFlat X)
    (hkd : k + 1 < d) (𝒴 : Finset (AffineVariety d))
    (T : AffineVariety d → Finset (Pt d)) (hT : Assignment P 𝒴 T) :
    famMass (𝒴.filter (fun Y => ∃ F : AffineSubspace ℂ (Point d),
      Module.finrank ℂ F.direction ≤ k + 1 ∧ X.points ⊆ F ∧ Y.points ⊆ F)) T ≤
      cfgN P * cfgB P ^ (-c₀) := by
  classical
  let I := 𝒴.filter (fun Y => ∃ F : AffineSubspace ℂ (Point d),
    Module.finrank ℂ F.direction ≤ k + 1 ∧
      X.points ⊆ (F : Set (Point d)) ∧ Y.points ⊆ (F : Set (Point d)))
  have hne := X.points_nonempty_of_isIrreducible hX
  by_cases hI : I.Nonempty
  · obtain ⟨Y₀, hY₀⟩ := hI
    obtain ⟨_, F₀, hF₀, hXF₀, _⟩ := Finset.mem_filter.mp hY₀
    have hproper := (generic_depth_commonflat X k hX hk hne hnl hkd F₀ hF₀ hXF₀).1
    apply assignment_subfamily_flat_cap P c₀ hcap 𝒴 I T hT
      (Finset.filter_subset _ _) (complexSpan X) hproper
    intro Y hY
    obtain ⟨_, F, hF, hXF, hYF⟩ := Finset.mem_filter.mp hY
    have hEq := (generic_depth_commonflat X k hX hk hne hnl hkd F hF hXF).2
    rwa [← hEq]
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hI
    change famMass I T ≤ _
    rw [hEmpty]
    simp only [famMass, Finset.sum_empty]
    unfold cfgN cfgB
    positivity

/-- Removing common-flat pairs with a nonlinear endpoint has the same
weighted cap cost as removing tangencies (`secants.tex:160–165`). -/
theorem generic_depth_commonflat_pruning (P : Finset (Pt d)) (c₀ : ℝ)
    (hcap : RealFlatCap P c₀) (k : ℕ) (hkd : k + 1 < d)
    (𝒳 𝒴 : Finset (AffineVariety d)) (S T : AffineVariety d → Finset (Pt d))
    (h𝒳 : ∀ X ∈ 𝒳, X.IsIrreducible ∧ X.dimension = k)
    (h𝒴 : ∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = k)
    (hS : Assignment P 𝒳 S) (hT : Assignment P 𝒴 T) :
    ∃ L : AffineVariety d → Finset (AffineVariety d),
      (∀ X ∈ 𝒳, L X ⊆ 𝒴) ∧
      (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, ((S X).card : ℝ) * (T Y).card) ≤
        cfgN P * cfgB P ^ (-c₀) * (famMass 𝒳 S + famMass 𝒴 T) ∧
      ∀ X ∈ 𝒳, ∀ Y ∈ L X, ∀ F : AffineSubspace ℂ (Point d),
        Module.finrank ℂ F.direction ≤ k + 1 → X.points ⊆ F → Y.points ⊆ F →
          IsFlat X ∧ IsFlat Y := by
  classical
  let common := fun X Y : AffineVariety d => ∃ F : AffineSubspace ℂ (Point d),
    Module.finrank ℂ F.direction ≤ k + 1 ∧ X.points ⊆ F ∧ Y.points ⊆ F
  let Q := fun X Y => IsFlat X ∨ ¬ common X Y
  let R := fun X Y => IsFlat Y ∨ ¬ common X Y
  let L := fun X => 𝒴.filter (fun Y => Q X Y ∧ R X Y)
  have hQ : ∀ X ∈ 𝒳, famMass (𝒴.filter (fun Y => ¬ Q X Y)) T ≤
      cfgN P * cfgB P ^ (-c₀) := by
    intro X hX
    by_cases hnl : IsFlat X
    · simp [famMass, Q, hnl]
      unfold cfgN cfgB
      positivity
    · have heq : 𝒴.filter (fun Y => ¬ Q X Y) = 𝒴.filter (common X) := by
        ext Y
        simp [Q, hnl]
      rw [heq]
      exact generic_depth_nonlinear_commonflat_mass P c₀ hcap X k
        (h𝒳 X hX).1 (h𝒳 X hX).2 hnl hkd 𝒴 T hT
  have hR : ∀ Y ∈ 𝒴, famMass (𝒳.filter (fun X => ¬ R X Y)) S ≤
      cfgN P * cfgB P ^ (-c₀) := by
    intro Y hY
    by_cases hnl : IsFlat Y
    · simp [famMass, R, hnl]
      unfold cfgN cfgB
      positivity
    · have heq : 𝒳.filter (fun X => ¬ R X Y) = 𝒳.filter (common Y) := by
        ext X
        have hs : common X Y ↔ common Y X := by
          constructor <;> rintro ⟨F, hF, h₁, h₂⟩ <;> exact ⟨F, hF, h₂, h₁⟩
        simp [R, hnl, hs]
      rw [heq]
      exact generic_depth_nonlinear_commonflat_mass P c₀ hcap Y k
        (h𝒴 Y hY).1 (h𝒴 Y hY).2 hnl hkd 𝒳 S hS
  refine ⟨L, fun _ _ => Finset.filter_subset _ _, ?_, ?_⟩
  · have h := discarded_product_weight_le 𝒳 𝒴 (fun X => ((S X).card : ℝ))
      (fun Y => ((T Y).card : ℝ)) Q R
      (cfgN P * cfgB P ^ (-c₀)) (cfgN P * cfgB P ^ (-c₀))
      (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
      (by
        intro X hX
        convert hQ X hX using 1
        unfold famMass
        apply Finset.sum_congr
        · ext Y
          simp only [Finset.mem_filter]
        · intro Y hY
          rfl)
      (by
        intro Y hY
        convert hR Y hY using 1
        unfold famMass
        apply Finset.sum_congr
        · ext X
          simp only [Finset.mem_filter]
        · intro X hX
          rfl)
    convert h using 1
    · apply Finset.sum_congr rfl
      intro X hX
      apply Finset.sum_congr
      · ext Y
        simp only [L, Finset.mem_sdiff, Finset.mem_filter]
      · intro Y hY
        rfl
    · simp only [famMass, mul_add]
  · intro X hX Y hY F hF hXF hYF
    obtain ⟨_, hq, hr⟩ := Finset.mem_filter.mp hY
    have hc : common X Y := ⟨F, hF, hXF, hYF⟩
    exact ⟨hq.resolve_right (not_not.mpr hc), hr.resolve_right (not_not.mpr hc)⟩

theorem discarded_product_weight_inter_le {α β : Type*}
    (I : Finset α) (J : Finset β) (a : α → ℝ) (b : β → ℝ)
    (L M : α → Finset β) (ha : ∀ x ∈ I, 0 ≤ a x) (hb : ∀ y ∈ J, 0 ≤ b y) :
    (∑ x ∈ I, ∑ y ∈ J \ (L x ∩ M x), a x * b y) ≤
      (∑ x ∈ I, ∑ y ∈ J \ L x, a x * b y) +
        (∑ x ∈ I, ∑ y ∈ J \ M x, a x * b y) := by
  classical
  have hdiff (A : Finset β) : J \ A = J.filter (fun y => y ∉ A) := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_filter]
  simp_rw [hdiff, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y hy
  have hprod := mul_nonneg (ha x hx) (hb y hy)
  by_cases hl : y ∈ L x <;> by_cases hm : y ∈ M x <;> simp [hl, hm] <;> linarith

/-- Both geometric deletions, before the flat occupancy deletion, with
one uniform loss bound. No degree or number-of-flats hypotheses are used. -/
theorem generic_depth_geometric_pruning (P : Finset (Pt d)) (c₀ : ℝ)
    (hcap : RealFlatCap P c₀) (k l : ℕ) (hkd : k < d) (hld : l + 1 < d)
    (𝒳 𝒴 : Finset (AffineVariety d)) (S T : AffineVariety d → Finset (Pt d))
    (h𝒳 : ∀ X ∈ 𝒳, X.IsIrreducible ∧ X.dimension = k)
    (h𝒴 : ∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = l)
    (hS : Assignment P 𝒳 S) (hT : Assignment P 𝒴 T) :
    ∃ L : AffineVariety d → Finset (AffineVariety d),
      (∀ X ∈ 𝒳, L X ⊆ 𝒴) ∧
      (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, ((S X).card : ℝ) * (T Y).card) ≤
        2 * cfgN P * cfgB P ^ (-c₀) * (famMass 𝒳 S + famMass 𝒴 T) ∧
      ∀ X ∈ 𝒳, ∀ Y ∈ L X,
        GenericallyTransverse X Y ∧
        (k = l → ∀ F : AffineSubspace ℂ (Point d),
          Module.finrank ℂ F.direction ≤ k + 1 → X.points ⊆ F → Y.points ⊆ F →
            IsFlat X ∧ IsFlat Y) := by
  obtain ⟨L, hL, hcost, htrans⟩ := generic_depth_transverse_pruning P c₀ hcap k l hkd
    (by omega) 𝒳 𝒴 S T h𝒳 h𝒴 hS hT
  by_cases heq : k = l
  · have h𝒴' : ∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = k := by
      simpa only [heq] using h𝒴
    obtain ⟨M, hM, hMcost, hflat⟩ := generic_depth_commonflat_pruning P c₀ hcap k
      (by omega) 𝒳 𝒴 S T h𝒳 h𝒴' hS hT
    refine ⟨fun X => L X ∩ M X, ?_, ?_, ?_⟩
    · intro X hX
      exact Finset.Subset.trans Finset.inter_subset_left (hL X hX)
    · have h := discarded_product_weight_inter_le 𝒳 𝒴 (fun X => ((S X).card : ℝ))
        (fun Y => ((T Y).card : ℝ)) L M
        (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
      calc
        _ ≤ _ := h
        _ ≤ 2 * cfgN P * cfgB P ^ (-c₀) * (famMass 𝒳 S + famMass 𝒴 T) := by
          linarith
    · intro X hX Y hY
      obtain ⟨hYL, hYM⟩ := Finset.mem_inter.mp hY
      exact ⟨htrans X hX Y hYL, fun _ => hflat X hX Y hYM⟩
  · refine ⟨L, hL, hcost.trans ?_, ?_⟩
    · have hnonneg : 0 ≤ cfgN P * cfgB P ^ (-c₀) * (famMass 𝒳 S + famMass 𝒴 T) :=
        mul_nonneg (by unfold cfgN cfgB; positivity)
          (add_nonneg (famMass_nonneg _ _) (famMass_nonneg _ _))
      nlinarith
    · intro X hX Y hY
      exact ⟨htrans X hX Y hY, fun hk => (heq hk).elim⟩

theorem generic_depth_cap_normalized_loss (N nx ny B c₀ θ w : ℝ)
    (hB : 0 < B) (hc₀ : 0 < c₀) (hθ : θ ≤ c₀ / 2) (hw : 0 ≤ w)
    (hwB : w ≤ Real.log B) (hnx0 : 0 ≤ nx) (hny0 : 0 ≤ ny)
    (hnx : N * Real.exp (-θ * w) ≤ nx) (hny : N * Real.exp (-θ * w) ≤ ny) :
    2 * N * B ^ (-c₀) * (nx + ny) ≤ 4 * Real.exp (-(c₀ / 2) * w) * nx * ny := by
  have hexp : Real.exp (θ*w) * Real.exp (-θ*w) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hcancel : Real.exp (θ*w) * (N * Real.exp (-θ*w)) = N := by
    calc
      _ = N * (Real.exp (θ*w) * Real.exp (-θ*w)) := by ring
      _ = N := by rw [hexp, mul_one]
  have hxN : N ≤ Real.exp (θ*w) * nx := by
    have h := mul_le_mul_of_nonneg_left hnx (Real.exp_pos (θ*w)).le
    rwa [hcancel] at h
  have hyN : N ≤ Real.exp (θ*w) * ny := by
    have h := mul_le_mul_of_nonneg_left hny (Real.exp_pos (θ*w)).le
    rwa [hcancel] at h
  have hdecay : Real.exp (θ*w) * B ^ (-c₀) ≤ Real.exp (-(c₀ / 2)*w) := by
    rw [Real.rpow_def_of_pos hB, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h₁ := mul_le_mul_of_nonneg_right hθ hw
    have h₂ := mul_le_mul_of_nonpos_left hwB (neg_nonpos.mpr hc₀.le)
    nlinarith only [h₁, h₂]
  have hcapx : N * B ^ (-c₀) ≤ Real.exp (-(c₀ / 2)*w) * nx := by
    calc
      _ ≤ (Real.exp (θ*w) * nx) * B ^ (-c₀) :=
        mul_le_mul_of_nonneg_right hxN (Real.rpow_nonneg hB.le _)
      _ = (Real.exp (θ*w) * B ^ (-c₀)) * nx := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdecay hnx0
  have hcapy : N * B ^ (-c₀) ≤ Real.exp (-(c₀ / 2)*w) * ny := by
    calc
      _ ≤ (Real.exp (θ*w) * ny) * B ^ (-c₀) :=
        mul_le_mul_of_nonneg_right hyN (Real.rpow_nonneg hB.le _)
      _ = (Real.exp (θ*w) * B ^ (-c₀)) * ny := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdecay hny0
  have h₁ := mul_le_mul_of_nonneg_right hcapx hny0
  have h₂ := mul_le_mul_of_nonneg_right hcapy hnx0
  nlinarith only [h₁, h₂]

theorem generic_depth_decay_threshold (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) :
    ∃ w₀ : ℝ, 1 ≤ w₀ ∧ ∀ w : ℝ, w₀ ≤ w → 4 * Real.exp (-(c₀ / 2)*w) ≤ δ := by
  let w₀ := max 1 (-Real.log (δ/4) / (c₀/2))
  refine ⟨w₀, le_max_left _ _, ?_⟩
  intro w hw
  have hbound : -Real.log (δ/4) / (c₀/2) ≤ w := (le_max_right _ _).trans hw
  have hmul := (div_le_iff₀ (by positivity : 0 < c₀/2)).mp hbound
  have hexp : Real.exp (-(c₀/2)*w) ≤ δ/4 := by
    rw [← Real.exp_log (by positivity : 0 < δ/4)]
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Uniform quantitative form of the tangent and nonlinear-common-flat
deletions, with the thresholds chosen before the configuration and families. -/
theorem generic_depth_geometric_pruning_small (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ δ > 0, ∃ θ > 0, ∃ w₀ : ℝ, ∀ (P : Finset (Pt d)) (w : ℝ),
      w₀ ≤ w → w ≤ Real.log (cfgB P) → RealFlatCap P c₀ →
      ∀ (k l : ℕ), k < d → l + 1 < d →
      ∀ (𝒳 𝒴 : Finset (AffineVariety d)) (S T : AffineVariety d → Finset (Pt d)),
        (∀ X ∈ 𝒳, X.IsIrreducible ∧ X.dimension = k) →
        (∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = l) →
        Assignment P 𝒳 S → Assignment P 𝒴 T →
        cfgN P * Real.exp (-θ*w) ≤ famMass 𝒳 S →
        cfgN P * Real.exp (-θ*w) ≤ famMass 𝒴 T →
        ∃ L : AffineVariety d → Finset (AffineVariety d),
          (∀ X ∈ 𝒳, L X ⊆ 𝒴) ∧
          (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, ((S X).card : ℝ) * (T Y).card) ≤
            δ * famMass 𝒳 S * famMass 𝒴 T ∧
          ∀ X ∈ 𝒳, ∀ Y ∈ L X, GenericallyTransverse X Y ∧
            (k = l → ∀ F : AffineSubspace ℂ (Point d),
              Module.finrank ℂ F.direction ≤ k + 1 → X.points ⊆ F → Y.points ⊆ F →
                IsFlat X ∧ IsFlat Y) := by
  intro δ hδ
  obtain ⟨w₀, hw₀, htail⟩ := generic_depth_decay_threshold c₀ δ hc₀ hδ
  refine ⟨c₀/4, by positivity, w₀, ?_⟩
  intro P w hw hwB hcap k l hkd hld 𝒳 𝒴 S T h𝒳 h𝒴 hS hT hnx hny
  have hw1 : 1 ≤ w := hw₀.trans hw
  have hB : 0 < cfgB P := by
    have hB0 : 0 ≤ cfgB P := by unfold cfgB; positivity
    by_contra hn
    have hz : cfgB P = 0 := le_antisymm (le_of_not_gt hn) hB0
    rw [hz, Real.log_zero] at hwB
    linarith
  obtain ⟨L, hL, hcost, hgood⟩ :=
    generic_depth_geometric_pruning P c₀ hcap k l hkd hld 𝒳 𝒴 S T h𝒳 h𝒴 hS hT
  refine ⟨L, hL, hcost.trans ?_, hgood⟩
  have hnorm := generic_depth_cap_normalized_loss (cfgN P) (famMass 𝒳 S) (famMass 𝒴 T)
    (cfgB P) c₀ (c₀/4) w hB hc₀ (by linarith) (by linarith) hwB
    (famMass_nonneg _ _) (famMass_nonneg _ _) hnx hny
  exact hnorm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (htail w hw) (famMass_nonneg _ _)) (famMass_nonneg _ _))

/-- The weighted rich-line estimate applies to containments between any
finite families of real `k`-flats and `(k+1)`-flats after a common slice. -/
theorem flatslice_weighted_flat_containments (d : ℕ) (hd : 0 < d)
    (hST : STRichLines d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 0 < k →
      ∀ (L H : Finset (AffineSubspace ℝ (Pt d)))
        (ω : AffineSubspace ℝ (Pt d) → ℝ) (ωmax τ tmax : ℝ),
      (∀ F ∈ L, Module.finrank ℝ F.direction = k) →
      (∀ G ∈ H, Module.finrank ℝ G.direction = k + 1) →
      (∀ F ∈ L, 0 ≤ ω F ∧ ω F ≤ ωmax) → 2 ≤ τ → 0 ≤ tmax →
      (∀ G ∈ H, ((L.filter (fun F => F ≤ G)).card : ℝ) ≤ tmax) →
      ∑ G ∈ H.filter (fun G => τ ≤ ((L.filter (fun F => F ≤ G)).card : ℝ)),
        (∑ F ∈ L.filter (fun F => F ≤ G), ω F) ^ 2 ≤
          C * ωmax ^ 2 * ((L.card : ℝ) ^ 2 / τ + L.card * tmax) := by
  obtain ⟨C, hC, hcore⟩ := flatslice_core d hST
  refine ⟨C, hC, ?_⟩
  intro k hk L H ω ωmax τ tmax hL hH hω hτ htmax hocc
  obtain ⟨a, b, ha, hb, hline, hinc⟩ :=
    FiniteFlatSlice.exists_point_line_representation hd k hk L H hL hH
  let Q := L.image a
  let lines := H.image b
  let W := FiniteFlatSlice.imageWeight L a ω
  have hQcard : Q.card = L.card := Finset.card_image_of_injOn ha
  have hW : ∀ q ∈ Q, 0 ≤ W q ∧ W q ≤ ωmax := by
    intro q hq
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
    simpa only [W, FiniteFlatSlice.imageWeight_apply L a ω ha F hF] using hω F hF
  have hbocc : ∀ G ∈ H, occ Q (b G) = (L.filter (fun F => F ≤ G)).card := by
    intro G hG
    exact FiniteFlatSlice.occ_image L a ha G (b G) (fun F hF => hinc F hF G hG)
  have hbweight : ∀ G ∈ H,
      (∑ q ∈ Q.filter (fun q => q ∈ b G), W q) =
        ∑ F ∈ L.filter (fun F => F ≤ G), ω F := by
    intro G hG
    exact FiniteFlatSlice.sum_imageWeight_incidence L a ω ha G (b G)
      (fun F hF => hinc F hF G hG)
  have hlines : ∀ B ∈ lines, IsRealLine B ∧ (occ Q B : ℝ) ≤ tmax := by
    intro B hB
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨hline G hG, by rw [hbocc G hG]; exact hocc G hG⟩
  have hrich : lines.filter (fun B => τ ≤ (occ Q B : ℝ)) =
      (H.filter (fun G => τ ≤ ((L.filter (fun F => F ≤ G)).card : ℝ))).image b := by
    dsimp only [lines]
    ext B
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨G, hG, rfl⟩, hr⟩
      exact ⟨G, ⟨hG, by rwa [hbocc G hG] at hr⟩, rfl⟩
    · rintro ⟨G, ⟨hG, hr⟩, rfl⟩
      exact ⟨⟨G, hG, rfl⟩, by rwa [hbocc G hG]⟩
  have hsum :
      (∑ B ∈ lines.filter (fun B => τ ≤ (occ Q B : ℝ)),
        (∑ q ∈ Q.filter (fun q => q ∈ B), W q) ^ 2) =
      ∑ G ∈ H.filter (fun G => τ ≤ ((L.filter (fun F => F ≤ G)).card : ℝ)),
        (∑ F ∈ L.filter (fun F => F ≤ G), ω F) ^ 2 := by
    rw [hrich, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro G hG
      rw [hbweight G (Finset.mem_filter.mp hG).1]
    · intro F hF G hG he
      exact hb (Finset.mem_filter.mp hF).1 (Finset.mem_filter.mp hG).1 he
  have hbound := hcore Q W ωmax τ tmax lines hW hτ htmax hlines
  rwa [hsum, hQcard] at hbound

/-- Cancellation of the flat-count parameter in the normalized
rich-flat bound; both families may contribute to each flat's weight. -/
theorem flatslice_normalized_expression_le (C n e B c₀ θ η ε w : ℝ)
    (hC : 0 ≤ C) (hn : 0 ≤ n) (he : 0 < e) (hB : 0 < B)
    (hnmax : n ≤ 2 * e * Real.exp (θ*w)) :
    C * (2 * e⁻¹ * Real.exp (θ*w)) ^ 2 *
      (n ^ 2 / Real.exp (ε*w) +
        n * (2 * e * Real.exp ((η+θ)*w) * B ^ (-c₀))) ≤
      16 * C * (Real.exp ((4*θ-ε)*w) +
        Real.exp ((η+4*θ)*w) * B ^ (-c₀)) := by
  have hsquare : n ^ 2 ≤ (2 * e * Real.exp (θ*w)) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hnmax)
      (add_nonneg (by positivity : 0 ≤ 2 * e * Real.exp (θ*w)) hn)
    nlinarith only [hprod]
  have hfirst : Real.exp ((4*θ-ε)*w) = Real.exp (θ*w) ^ 4 / Real.exp (ε*w) := by
    rw [show (4*θ-ε)*w = 4*(θ*w) - ε*w by ring, Real.exp_sub]
    congr 1
    exact Real.exp_nat_mul (θ*w) 4
  have hsecond : Real.exp ((η+4*θ)*w) =
      Real.exp ((η+θ)*w) * Real.exp (θ*w) ^ 3 := by
    rw [show (η+4*θ)*w = (η+θ)*w + 3*(θ*w) by ring, Real.exp_add]
    congr 1
    exact Real.exp_nat_mul (θ*w) 3
  calc
    _ ≤ C * (2 * e⁻¹ * Real.exp (θ*w)) ^ 2 *
        ((2 * e * Real.exp (θ*w)) ^ 2 / Real.exp (ε*w) +
          (2 * e * Real.exp (θ*w)) *
            (2 * e * Real.exp ((η+θ)*w) * B ^ (-c₀))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (sq_nonneg _))
      apply add_le_add
      · exact div_le_div_of_nonneg_right hsquare (Real.exp_pos _).le
      · exact mul_le_mul_of_nonneg_right hnmax (by positivity)
    _ = _ := by
      rw [hfirst, hsecond]
      field_simp
      ring

/-- Uniform thresholds for the light-flat and rich-flat normalized
losses. All choices precede the configuration and the flat-count parameter. -/
theorem generic_depth_flatslice_tail_small (c₀ ε δ C : ℝ)
    (hc₀ : 0 < c₀) (hε : 0 < ε) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ θ > 0, ∃ η > θ, ∃ w₀ : ℝ, 1 ≤ w₀ ∧ θ ≤ c₀/32 ∧ θ ≤ ε/8 ∧ ∀ B w : ℝ,
      0 < B → w₀ ≤ w → w ≤ Real.log B →
      2 ≤ Real.exp (ε*w) ∧
      2 * Real.exp ((θ-η)*w) +
        16 * C * (Real.exp ((4*θ-ε)*w) +
          Real.exp ((η+4*θ)*w) * B ^ (-c₀)) ≤ δ := by
  let θ := min (ε/8) (c₀/32)
  let η := c₀/8
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθε : θ ≤ ε/8 := min_le_left _ _
  have hθc : θ ≤ c₀/32 := min_le_right _ _
  have hη : θ < η := by dsimp [η]; linarith
  obtain ⟨wa, hwa, hlight⟩ := generic_depth_decay_threshold (c₀/8) (δ/3)
    (by positivity) (by positivity)
  obtain ⟨wb, hwb, hfirst⟩ := generic_depth_decay_threshold ε (δ/(12*C))
    hε (by positivity)
  obtain ⟨wc, hwc, hsecond⟩ := generic_depth_decay_threshold c₀ (δ/(12*C))
    hc₀ (by positivity)
  let w₀ := max wa (max wb (max wc (Real.log 2 / ε)))
  refine ⟨θ, hθ, η, hη, w₀, hwa.trans (le_max_left _ _), hθc, hθε, ?_⟩
  intro B w hB hw hwB
  have haw : wa ≤ w := (le_max_left _ _).trans hw
  have hbw : wb ≤ w := (le_max_left _ _).trans ((le_max_right _ _).trans hw)
  have hcw : wc ≤ w := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hw))
  have hlogw : Real.log 2 / ε ≤ w := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hw))
  have hw0 : 0 ≤ w := le_trans (by norm_num) (hwa.trans haw)
  have hτ : 2 ≤ Real.exp (ε*w) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have h := (div_le_iff₀ hε).mp hlogw
    linarith
  have hlightDecay : Real.exp ((θ-η)*w) ≤ Real.exp (-(c₀/16)*w) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hw0
    dsimp [η]
    linarith
  have hfirstDecay : Real.exp ((4*θ-ε)*w) ≤ Real.exp (-(ε/2)*w) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hw0
    linarith
  have hsecondDecay : Real.exp ((η+4*θ)*w) * B ^ (-c₀) ≤
      Real.exp (-(c₀/2)*w) := by
    rw [Real.rpow_def_of_pos hB, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc := mul_le_mul_of_nonpos_left hwB (neg_nonpos.mpr hc₀.le)
    have hθw := mul_le_mul_of_nonneg_right hθc hw0
    dsimp [η]
    nlinarith only [hc, hθw, mul_nonneg hc₀.le hw0]
  have ha := hlight w haw
  have hb := hfirst w hbw
  have hc := hsecond w hcw
  have ha' : 2 * Real.exp ((θ-η)*w) ≤ δ/3 := by
    have he0 := Real.exp_pos (-(c₀/16)*w)
    have heq : -((c₀/8)/2)*w = -(c₀/16)*w := by ring
    rw [heq] at ha
    linarith
  have hb' : 16*C*Real.exp ((4*θ-ε)*w) ≤ δ/3 := by
    have h := (le_div_iff₀ (by positivity : 0 < 12*C)).mp hb
    have hh := mul_le_mul_of_nonneg_left hfirstDecay hC.le
    nlinarith only [h, hh]
  have hc' : 16*C*(Real.exp ((η+4*θ)*w) * B ^ (-c₀)) ≤ δ/3 := by
    have h := (le_div_iff₀ (by positivity : 0 < 12*C)).mp hc
    have hh := mul_le_mul_of_nonneg_left hsecondDecay hC.le
    nlinarith only [h, hh]
  exact ⟨hτ, by nlinarith only [ha', hb', hc']⟩

/-- Uniform pruning estimate for a real flat arrangement with the
normalized upper weights, light cutoff and physical flat-mass bound
used in generic depth. -/
theorem generic_depth_real_flat_pruning_small (d : ℕ) (hd : 0 < d)
    (c₀ ε δ : ℝ) (hc₀ : 0 < c₀) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ θ > 0, ∃ η > θ, ∃ w₀ : ℝ, 1 ≤ w₀ ∧ θ ≤ c₀/32 ∧ θ ≤ ε/8 ∧
      ∀ (B w e : ℝ), 0 < B → w₀ ≤ w → w ≤ Real.log B → 0 < e →
      ∀ (k : ℕ), 0 < k →
      ∀ (L H : Finset (AffineSubspace ℝ (Pt d)))
        (ω : AffineSubspace ℝ (Pt d) → ℝ),
      (∀ F ∈ L, Module.finrank ℝ F.direction = k) →
      (∀ G ∈ H, Module.finrank ℝ G.direction = k + 1) →
      (L.card : ℝ) ≤ 2 * e * Real.exp (θ*w) →
      (∀ F ∈ L, e⁻¹ * Real.exp (-η*w) ≤ ω F ∧
        ω F ≤ 2 * e⁻¹ * Real.exp (θ*w)) →
      (∀ G ∈ H, (∑ F ∈ L.filter (fun F => F ≤ G), ω F) ≤
        2 * Real.exp (θ*w) * B ^ (-c₀)) →
      2 ≤ Real.exp (ε*w) ∧
      (∑ G ∈ H.filter (fun G => Real.exp (ε*w) ≤
          ((L.filter (fun F => F ≤ G)).card : ℝ)),
        (∑ F ∈ L.filter (fun F => F ≤ G), ω F) ^ 2) +
          2 * Real.exp ((θ-η)*w) ≤ δ := by
  obtain ⟨C, hC, hcore⟩ := flatslice_weighted_flat_containments d hd (ci_st_rich d)
  obtain ⟨θ, hθ, η, hη, w₀, hw₀, hθc, hθε, htail⟩ :=
    generic_depth_flatslice_tail_small c₀ ε δ C hc₀ hε hδ hC
  refine ⟨θ, hθ, η, hη, w₀, hw₀, hθc, hθε, ?_⟩
  intro B w e hB hw hwB he k hk L H ω hL hH hcard hω hmass
  let a := e⁻¹ * Real.exp (-η*w)
  let M := 2 * Real.exp (θ*w) * B ^ (-c₀)
  let tmax := 2 * e * Real.exp ((η+θ)*w) * B ^ (-c₀)
  have ha : 0 < a := by dsimp [a]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have heq : M / a = tmax := by
    apply (div_eq_iff ha.ne').mpr
    dsimp only [M, tmax, a]
    symm
    calc
      _ = 2 * (e * e⁻¹) *
          (Real.exp ((η+θ)*w) * Real.exp (-η*w)) * B ^ (-c₀) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ he.ne', ← Real.exp_add,
          show (η+θ)*w + -η*w = θ*w by ring]
        ring
  have hocc : ∀ G ∈ H, ((L.filter (fun F => F ≤ G)).card : ℝ) ≤ tmax := by
    intro G hG
    rw [← heq]
    exact FiniteFlatSlice.occupancy_le_mass_div L ω a M ha
      (fun F hF => (hω F hF).1) G (hmass G hG)
  have hweights : ∀ F ∈ L, 0 ≤ ω F ∧ ω F ≤ 2 * e⁻¹ * Real.exp (θ*w) := by
    intro F hF
    exact ⟨ha.le.trans (hω F hF).1, (hω F hF).2⟩
  have hsmall := htail B w hB hw hwB
  have hraw := hcore k hk L H ω (2 * e⁻¹ * Real.exp (θ*w))
    (Real.exp (ε*w)) tmax hL hH hweights hsmall.1 htmax hocc
  have hnorm := flatslice_normalized_expression_le C L.card e B c₀ θ η ε w
    hC.le (by positivity) he hB hcard
  have hcost := hraw.trans hnorm
  exact ⟨hsmall.1, by linarith [hsmall.2]⟩

theorem normalized_assigned_weight_sum (I : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) (h : 0 < famMass I S) :
    (∑ X ∈ I, ((S X).card : ℝ) / famMass I S) = 1 := by
  rw [← Finset.sum_div]
  exact div_self h.ne'

/-- The physical flat cap for a subfamily, after normalization by its
original family's assigned mass. -/
theorem normalized_assigned_flat_cap (P : Finset (Pt d)) (c₀ θ w : ℝ)
    (hcap : RealFlatCap P c₀) (𝒳 I : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) (hS : Assignment P 𝒳 S)
    (hI : I ⊆ 𝒳) (hnx : 0 < famMass 𝒳 S)
    (hmass : cfgN P * Real.exp (-θ*w) ≤ famMass 𝒳 S)
    (F : AffineSubspace ℂ (Point d)) (hF : F ≠ ⊤) (hsub : ∀ X ∈ I, X.points ⊆ F) :
    (∑ X ∈ I, ((S X).card : ℝ) / famMass 𝒳 S) ≤ Real.exp (θ*w) * cfgB P ^ (-c₀) := by
  have hcancel : Real.exp (θ*w) * Real.exp (-θ*w) = 1 := by
    rw [← Real.exp_add, show θ*w + -θ*w = 0 by ring, Real.exp_zero]
  have hN : cfgN P ≤ Real.exp (θ*w) * famMass 𝒳 S := by
    calc
      _ = Real.exp (θ*w) * (cfgN P * Real.exp (-θ*w)) := by
        rw [← mul_assoc, mul_comm (Real.exp (θ*w)) (cfgN P), mul_assoc, hcancel, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
  rw [← Finset.sum_div]
  apply (div_le_iff₀ hnx).mpr
  change famMass I S ≤ _
  calc
    _ ≤ cfgN P * cfgB P ^ (-c₀) := assignment_subfamily_flat_cap P c₀ hcap 𝒳 I S hS hI F hF hsub
    _ ≤ (Real.exp (θ*w) * famMass 𝒳 S) * cfgB P ^ (-c₀) :=
      mul_le_mul_of_nonneg_right hN (by unfold cfgB; positivity)
    _ = _ := by ring

/-- Exact cost of deleting a specified finite carrier-pair set. -/
theorem discarded_pair_set_weight {α β : Type*} (I : Finset α) (J : Finset β)
    (a : α → ℝ) (b : β → ℝ) (R : Finset (α × β)) (hR : R ⊆ I ×ˢ J) :
    (∑ x ∈ I, ∑ y ∈ J \ J.filter (fun y => (x,y) ∉ R), a x * b y) =
      ∑ xy ∈ R, a xy.1 * b xy.2 := by
  have hdiff : ∀ x : α, J \ J.filter (fun y => (x,y) ∉ R) =
      J.filter (fun y => (x,y) ∈ R) := by
    intro x
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  simp_rw [hdiff, Finset.sum_filter]
  rw [← Finset.sum_product I J (fun xy => if xy ∈ R then a xy.1 * b xy.2 else 0),
    ← Finset.sum_filter]
  have hf : (I ×ˢ J).filter (fun xy => xy ∈ R) = R := by
    ext xy
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hR h, h⟩⟩
  rw [hf]

/-- With total normalized masses one, source and target light deletions
cost their two light masses; all other discarded pairs cost their product sum. -/
theorem discarded_weight_light_and_pairs_le {α β : Type*}
    (I : Finset α) (J : Finset β) (a : α → ℝ) (b : β → ℝ)
    (p : α → Prop) (q : β → Prop) (R : Finset (α × β))
    (ha : ∀ x ∈ I, 0 ≤ a x) (hb : ∀ y ∈ J, 0 ≤ b y)
    (ha1 : (∑ x ∈ I, a x) = 1) (hb1 : (∑ y ∈ J, b y) = 1) (hR : R ⊆ I ×ˢ J) :
    (∑ x ∈ I, ∑ y ∈ J \ (J.filter (fun y => ¬ q y ∧ ¬ p x) ∩
        J.filter (fun y => (x,y) ∉ R)), a x * b y) ≤
      (∑ x ∈ I.filter p, a x) + (∑ y ∈ J.filter q, b y) +
        ∑ xy ∈ R, a xy.1 * b xy.2 := by
  have hlight := discarded_product_weight_le I J a b
    (fun _ y => ¬ q y) (fun x _ => ¬ p x)
    (∑ y ∈ J.filter q, b y) (∑ x ∈ I.filter p, a x) ha hb
    (by intro x hx; simp only [not_not]; exact le_refl _)
    (by intro y hy; simp only [not_not]; exact le_refl _)
  rw [ha1, hb1, mul_one, mul_one] at hlight
  have hlight' :
      (∑ x ∈ I, ∑ y ∈ J \ J.filter (fun y => ¬ q y ∧ ¬ p x), a x * b y) ≤
        (∑ x ∈ I.filter p, a x) + (∑ y ∈ J.filter q, b y) := by
    convert hlight using 1
    · apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_sdiff, Finset.mem_filter]
      · intro y hy
        rfl
    · ring
  have hinter := discarded_product_weight_inter_le I J a b
    (fun x => J.filter (fun y => ¬ q y ∧ ¬ p x))
    (fun x => J.filter (fun y => (x,y) ∉ R)) ha hb
  rw [discarded_pair_set_weight I J a b R hR] at hinter
  calc
    _ ≤ _ := hinter
    _ ≤ _ := add_le_add hlight' (le_refl _)

set_option maxHeartbeats 2000000 in
/-- Actual assigned-family version of the real-flat pruning estimate.
After a uniformly small product-weight deletion, each admitted pair of
distinct flat carriers has few listed flat targets in its common flat. -/
theorem generic_depth_flat_pruning_small (d : ℕ) (hd : 0 < d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∀ δ > 0, ∃ θ > 0, ∃ w₀ : ℝ, 1 ≤ w₀ ∧ θ ≤ c₀/32 ∧ θ ≤ ε/8 ∧
      ∀ (P : Finset (Pt d)) (w e : ℝ), w₀ ≤ w → w ≤ Real.log (cfgB P) → 0 < e →
      RealFlatCap P c₀ → ∀ k : ℕ, 0 < k → k+1 < d →
      ∀ (𝒳 𝒴 : Finset (AffineVariety d)) (S T : AffineVariety d → Finset (Pt d)),
        (∀ X ∈ 𝒳, X.IsIrreducible ∧ X.dimension = k) →
        (∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = k) →
        Assignment P 𝒳 S → Assignment P 𝒴 T →
        (∀ Z ∈ 𝒳 ∪ 𝒴, IsFlat Z → IsRealFlat Z) →
        0 < famMass 𝒳 S → 0 < famMass 𝒴 T →
        cfgN P * Real.exp (-θ*w) ≤ famMass 𝒳 S →
        cfgN P * Real.exp (-θ*w) ≤ famMass 𝒴 T →
        ((𝒳.filter IsFlat).card : ℝ) ≤ e * Real.exp (θ*w) →
        ((𝒴.filter IsFlat).card : ℝ) ≤ e * Real.exp (θ*w) →
        (∀ X ∈ 𝒳, IsFlat X → ((S X).card : ℝ) ≤ famMass 𝒳 S * e⁻¹ * Real.exp (θ*w)) →
        (∀ Y ∈ 𝒴, IsFlat Y → ((T Y).card : ℝ) ≤ famMass 𝒴 T * e⁻¹ * Real.exp (θ*w)) →
        ∃ L : AffineVariety d → Finset (AffineVariety d),
          (∀ X ∈ 𝒳, L X ⊆ 𝒴) ∧
          (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, ((S X).card : ℝ) * (T Y).card) ≤
            δ * famMass 𝒳 S * famMass 𝒴 T ∧
          ∀ X ∈ 𝒳, ∀ Y ∈ L X, IsFlat X → IsFlat Y → X ≠ Y →
            ∀ F : AffineSubspace ℂ (Point d), Module.finrank ℂ F.direction ≤ k+1 →
              X.points ⊆ F → Y.points ⊆ F →
              (((L X).filter (fun Z => IsFlat Z ∧ Z.points ⊆ F)).card : ℝ) ≤
                Real.exp (ε*w) := by
  intro ε hε δ hδ
  obtain ⟨θ, hθ, η, hη, w₀, hw₀, hθc, hθε, hprune⟩ :=
    generic_depth_real_flat_pruning_small d hd c₀ ε δ hc₀ hε hδ
  refine ⟨θ, hθ, w₀, hw₀, hθc, hθε, ?_⟩
  intro P w e hw hwB he hcap k hk hkd 𝒳 𝒴 S T h𝒳 h𝒴 hS hT hreal hnx hny hmassX hmassY
    hcardX hcardY hupperX hupperY
  have hB : 0 < cfgB P := by
    have hB0 : 0 ≤ cfgB P := by unfold cfgB; positivity
    by_contra hn
    have hz : cfgB P = 0 := le_antisymm (le_of_not_gt hn) hB0
    rw [hz, Real.log_zero] at hwB
    linarith only [hw₀, hw, hwB]
  let a : AffineVariety d → ℝ := fun X => ((S X).card : ℝ) / famMass 𝒳 S
  let b : AffineVariety d → ℝ := fun Y => ((T Y).card : ℝ) / famMass 𝒴 T
  let cutoff := e⁻¹ * Real.exp (-η*w)
  let upper := e⁻¹ * Real.exp (θ*w)
  have hcut : 0 < cutoff := by dsimp [cutoff]; positivity
  have hupp0 : 0 ≤ upper := by dsimp [upper]; positivity
  have ha0 : ∀ X : AffineVariety d, 0 ≤ a X := by intro X; dsimp [a]; positivity
  have hb0 : ∀ Y : AffineVariety d, 0 ≤ b Y := by intro Y; dsimp [b]; positivity
  have haUpper : ∀ X ∈ 𝒳, IsFlat X → a X ≤ upper := by
    intro X hX hflat
    apply (div_le_iff₀ hnx).mpr
    simpa only [upper, mul_assoc, mul_comm, mul_left_comm] using hupperX X hX hflat
  have hbUpper : ∀ Y ∈ 𝒴, IsFlat Y → b Y ≤ upper := by
    intro Y hY hflat
    apply (div_le_iff₀ hny).mpr
    simpa only [upper, mul_assoc, mul_comm, mul_left_comm] using hupperY Y hY hflat
  let I := 𝒳.filter (fun X => IsFlat X ∧ cutoff ≤ a X)
  let J := 𝒴.filter (fun Y => IsFlat Y ∧ cutoff ≤ b Y)
  let U := I ∪ J
  have hIX : I ⊆ 𝒳 := Finset.filter_subset _ _
  have hJY : J ⊆ 𝒴 := Finset.filter_subset _ _
  have hUreal : ∀ Z ∈ U, IsRealFlat Z := by
    intro Z hZ
    rcases Finset.mem_union.mp hZ with hZI | hZJ
    · exact hreal Z (Finset.mem_union_left _ (hIX hZI)) (Finset.mem_filter.mp hZI).2.1
    · exact hreal Z (Finset.mem_union_right _ (hJY hZJ)) (Finset.mem_filter.mp hZJ).2.1
  have hUdim : ∀ Z ∈ U, Z.IsIrreducible ∧ Z.dimension = k := by
    intro Z hZ
    rcases Finset.mem_union.mp hZ with hZI | hZJ
    · exact h𝒳 Z (hIX hZI)
    · exact h𝒴 Z (hJY hZJ)
  let carrier := RealFlatGeometry.realCarrier (d := d)
  have hi : Set.InjOn carrier (U : Set (AffineVariety d)) := by
    intro X hX Y hY heq
    exact RealFlatGeometry.realCarrier_injective X Y (hUreal X hX) (hUreal Y hY) heq
  let A := U.image carrier
  let C := CarrierWeights.combined I J a b
  let ω := FiniteFlatSlice.imageWeight U carrier C
  have hωeq : ∀ Z ∈ U, ω (carrier Z) = C Z := by
    intro Z hZ
    exact FiniteFlatSlice.imageWeight_apply U carrier C hi Z hZ
  have hArank : ∀ F ∈ A, Module.finrank ℝ F.direction = k := by
    intro F hF
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hF
    exact (RealFlatGeometry.realCarrier_finrank Z (hUdim Z hZ).1 (hUreal Z hZ)).trans
      (hUdim Z hZ).2
  have hAcard : (A.card : ℝ) ≤ 2 * e * Real.exp (θ*w) := by
    have hcardA : A.card = U.card := Finset.card_image_of_injOn hi
    have hIcard : I.card ≤ (𝒳.filter IsFlat).card := by
      apply Finset.card_le_card
      intro Z hZ
      exact Finset.mem_filter.mpr ⟨hIX hZ, (Finset.mem_filter.mp hZ).2.1⟩
    have hJcard : J.card ≤ (𝒴.filter IsFlat).card := by
      apply Finset.card_le_card
      intro Z hZ
      exact Finset.mem_filter.mpr ⟨hJY hZ, (Finset.mem_filter.mp hZ).2.1⟩
    have hunion : U.card ≤ I.card + J.card := Finset.card_union_le _ _
    rw [hcardA]
    have hIc : (I.card : ℝ) ≤ ((𝒳.filter IsFlat).card : ℝ) := by exact_mod_cast hIcard
    have hJc : (J.card : ℝ) ≤ ((𝒴.filter IsFlat).card : ℝ) := by exact_mod_cast hJcard
    have hUc : (U.card : ℝ) ≤ (I.card : ℝ) + J.card := by exact_mod_cast hunion
    linarith
  have hωbounds : ∀ F ∈ A, cutoff ≤ ω F ∧ ω F ≤ 2 * upper := by
    intro F hF
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hF
    rw [hωeq Z hZ]
    constructor
    · rcases Finset.mem_union.mp hZ with hZI | hZJ
      · exact (Finset.mem_filter.mp hZI).2.2 |>.trans
          (CarrierWeights.le_combined_left I J a b (fun Y _ => hb0 Y) Z hZI)
      · exact (Finset.mem_filter.mp hZJ).2.2 |>.trans
          (CarrierWeights.le_combined_right I J a b (fun X _ => ha0 X) Z hZJ)
    · have hbound := CarrierWeights.combined_le I J a b upper upper hupp0 hupp0
        (fun X hX => haUpper X (hIX hX) (Finset.mem_filter.mp hX).2.1)
        (fun Y hY => hbUpper Y (hJY hY) (Finset.mem_filter.mp hY).2.1) Z
      linarith
  let H := ((A ×ˢ A).image (fun FG => FG.1 ⊔ FG.2)).filter
    (fun G => Module.finrank ℝ G.direction = k+1)
  have hHrank : ∀ G ∈ H, Module.finrank ℝ G.direction = k+1 :=
    fun G hG => (Finset.mem_filter.mp hG).2
  have hmass : ∀ G ∈ H, (∑ F ∈ A.filter (fun F => F ≤ G), ω F) ≤
      2 * Real.exp (θ*w) * cfgB P ^ (-c₀) := by
    intro G hG
    have hGne := GeoSlice.affine_nonempty G
      (GeoSlice.direction_ne_bot_of_rank G (k+1) (by omega) (hHrank G hG))
    have hproper := RealFlatGeometry.complexify_ne_top_of_finrank_lt G hGne
      (by rw [hHrank G hG]; exact hkd)
    have hsub : ∀ Z ∈ U, carrier Z ≤ G → Z.points ⊆ RealFlatGeometry.complexify G := by
      intro Z hZ hZG
      rw [RealFlatGeometry.realCarrier_complexify Z (hUreal Z hZ)]
      exact RealFlatGeometry.complexify_mono _ _ hZG
    have hsrc := normalized_assigned_flat_cap P c₀ θ w hcap 𝒳
      (I.filter (fun Z => carrier Z ≤ G)) S hS
      (fun Z hZ => hIX (Finset.mem_filter.mp hZ).1) hnx hmassX
      (RealFlatGeometry.complexify G) hproper
      (fun Z hZ => hsub Z (Finset.mem_union_left _ (Finset.mem_filter.mp hZ).1)
        (Finset.mem_filter.mp hZ).2)
    have htgt := normalized_assigned_flat_cap P c₀ θ w hcap 𝒴
      (J.filter (fun Z => carrier Z ≤ G)) T hT
      (fun Z hZ => hJY (Finset.mem_filter.mp hZ).1) hny hmassY
      (RealFlatGeometry.complexify G) hproper
      (fun Z hZ => hsub Z (Finset.mem_union_right _ (Finset.mem_filter.mp hZ).1)
        (Finset.mem_filter.mp hZ).2)
    rw [CarrierWeights.sum_imageWeight_filter U carrier C hi (fun F => F ≤ G)]
    change (∑ Z ∈ (I ∪ J).filter (fun Z => carrier Z ≤ G),
      CarrierWeights.combined I J a b Z) ≤ _
    rw [CarrierWeights.sum_combined_filter]
    change (∑ Z ∈ I.filter (fun Z => carrier Z ≤ G), ((S Z).card : ℝ) / famMass 𝒳 S) +
      (∑ Z ∈ J.filter (fun Z => carrier Z ≤ G), ((T Z).card : ℝ) / famMass 𝒴 T) ≤ _
    linarith
  have hsmall := hprune (cfgB P) w e hB hw hwB he k hk A H ω hArank hHrank hAcard
    (by intro F hF; simpa only [cutoff, upper, mul_assoc] using hωbounds F hF) hmass
  let τ := Real.exp (ε*w)
  let join : AffineVariety d × AffineVariety d → AffineSubspace ℝ (Pt d) :=
    fun XY => carrier XY.1 ⊔ carrier XY.2
  let R := (I ×ˢ J).filter (fun XY =>
    Module.finrank ℝ (join XY).direction = k+1 ∧
      τ < ((A.filter (fun F => F ≤ join XY)).card : ℝ))
  let rich := H.filter (fun G => τ ≤ ((A.filter (fun F => F ≤ G)).card : ℝ))
  let f : AffineVariety d × AffineVariety d →
      AffineSubspace ℝ (Pt d) × AffineSubspace ℝ (Pt d) :=
    fun XY => (carrier XY.1, carrier XY.2)
  have hRmem : ∀ XY ∈ R, XY.1 ∈ I ∧ XY.2 ∈ J :=
    fun XY hXY => Finset.mem_product.mp (Finset.mem_filter.mp hXY).1
  have hRU : ∀ XY ∈ R, XY.1 ∈ U ∧ XY.2 ∈ U := by
    intro XY hXY
    exact ⟨Finset.mem_union_left _ (hRmem XY hXY).1,
      Finset.mem_union_right _ (hRmem XY hXY).2⟩
  have hf : Set.InjOn f (R : Set (AffineVariety d × AffineVariety d)) := by
    intro XY hXY ZW hZW heq
    exact Prod.ext (hi (hRU XY hXY).1 (hRU ZW hZW).1 (congrArg Prod.fst heq))
      (hi (hRU XY hXY).2 (hRU ZW hZW).2 (congrArg Prod.snd heq))
  have hRimage : R.image f ⊆ A ×ˢ A := by
    intro FG hFG
    obtain ⟨XY, hXY, rfl⟩ := Finset.mem_image.mp hFG
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ (hRU XY hXY).1,
      Finset.mem_image_of_mem _ (hRU XY hXY).2⟩
  have hjoins : ∀ FG ∈ R.image f, FG.1 ⊔ FG.2 ∈ rich ∧
      FG.1 ≤ FG.1 ⊔ FG.2 ∧ FG.2 ≤ FG.1 ⊔ FG.2 := by
    intro FG hFG
    obtain ⟨XY, hXY, rfl⟩ := Finset.mem_image.mp hFG
    have hm := Finset.mem_filter.mp hXY
    have hprod : f XY ∈ A ×ˢ A := hRimage (Finset.mem_image_of_mem _ hXY)
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem (fun FG => FG.1 ⊔ FG.2) hprod, hm.2.1⟩, hm.2.2.le⟩,
      le_sup_left, le_sup_right⟩
  have hrichCost : (∑ XY ∈ R, a XY.1 * b XY.2) ≤
      ∑ G ∈ rich, (∑ F ∈ A.filter (fun F => F ≤ G), ω F) ^ 2 := by
    calc
      _ ≤ ∑ XY ∈ R, C XY.1 * C XY.2 := by
        apply Finset.sum_le_sum
        intro XY hXY
        apply mul_le_mul
        · exact CarrierWeights.le_combined_left I J a b (fun Y _ => hb0 Y) _ (hRmem XY hXY).1
        · exact CarrierWeights.le_combined_right I J a b (fun X _ => ha0 X) _ (hRmem XY hXY).2
        · exact hb0 _
        · exact CarrierWeights.combined_nonneg I J a b (fun X _ => ha0 X) (fun Y _ => hb0 Y) _
      _ = ∑ FG ∈ R.image f, ω FG.1 * ω FG.2 := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro XY hXY
          rw [hωeq XY.1 (hRU XY hXY).1, hωeq XY.2 (hRU XY hXY).2]
        · exact hf
      _ ≤ _ := FiniteFlatSlice.weighted_pairs_le_squared_flat_mass A rich ω (R.image f)
        (fun FG => FG.1 ⊔ FG.2)
        (fun F hF => hcut.le.trans (hωbounds F hF).1) hRimage hjoins
  let lightX := fun X => IsFlat X ∧ a X < cutoff
  let lightY := fun Y => IsFlat Y ∧ b Y < cutoff
  letI : DecidablePred lightX := fun X => Classical.propDecidable (lightX X)
  letI : DecidablePred lightY := fun Y => Classical.propDecidable (lightY Y)
  have hcutCancel : (e * Real.exp (θ*w)) * cutoff = Real.exp ((θ-η)*w) := by
    dsimp only [cutoff]
    calc
      _ = (e * e⁻¹) * (Real.exp (θ*w) * Real.exp (-η*w)) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ he.ne', one_mul, ← Real.exp_add]
        congr 1
        ring
  have hlightX : (∑ X ∈ 𝒳.filter lightX, a X) ≤ Real.exp ((θ-η)*w) := by
    have hfilter : 𝒳.filter lightX = (𝒳.filter IsFlat).filter (fun X => a X < cutoff) := by
      ext X
      simp only [lightX, Finset.mem_filter]
      tauto
    rw [hfilter, ← hcutCancel]
    exact (FiniteFlatSlice.sum_light_weights_le_card_mul (𝒳.filter IsFlat) a cutoff hcut.le).trans
      (mul_le_mul_of_nonneg_right hcardX hcut.le)
  have hlightY : (∑ Y ∈ 𝒴.filter lightY, b Y) ≤ Real.exp ((θ-η)*w) := by
    have hfilter : 𝒴.filter lightY = (𝒴.filter IsFlat).filter (fun Y => b Y < cutoff) := by
      ext Y
      simp only [lightY, Finset.mem_filter]
      tauto
    rw [hfilter, ← hcutCancel]
    exact (FiniteFlatSlice.sum_light_weights_le_card_mul (𝒴.filter IsFlat) b cutoff hcut.le).trans
      (mul_le_mul_of_nonneg_right hcardY hcut.le)
  let L : AffineVariety d → Finset (AffineVariety d) := fun X =>
    𝒴.filter (fun Y => ¬ lightY Y ∧ ¬ lightX X) ∩ 𝒴.filter (fun Y => (X,Y) ∉ R)
  have hRfull : R ⊆ 𝒳 ×ˢ 𝒴 := by
    intro XY hXY
    exact Finset.mem_product.mpr ⟨hIX (hRmem XY hXY).1, hJY (hRmem XY hXY).2⟩
  have hnormalized : (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, a X * b Y) ≤ δ := by
    have hdel := discarded_weight_light_and_pairs_le 𝒳 𝒴 a b lightX lightY R
      (fun X _ => ha0 X) (fun Y _ => hb0 Y)
      (normalized_assigned_weight_sum 𝒳 S hnx) (normalized_assigned_weight_sum 𝒴 T hny) hRfull
    have htotal := hsmall.2
    change (∑ G ∈ rich, (∑ F ∈ A.filter (fun F => F ≤ G), ω F) ^ 2) +
      2 * Real.exp ((θ-η)*w) ≤ δ at htotal
    change (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ (𝒴.filter (fun Y => ¬ lightY Y ∧ ¬ lightX X) ∩
      𝒴.filter (fun Y => (X,Y) ∉ R)), a X * b Y) ≤ δ
    calc
      _ ≤ _ := hdel
      _ ≤ Real.exp ((θ-η)*w) + Real.exp ((θ-η)*w) +
          (∑ G ∈ rich, (∑ F ∈ A.filter (fun F => F ≤ G), ω F) ^ 2) :=
        add_le_add (add_le_add hlightX hlightY) hrichCost
      _ ≤ δ := by linarith only [htotal]
  refine ⟨L, ?_, ?_, ?_⟩
  · intro X hX
    exact Finset.Subset.trans Finset.inter_subset_left (Finset.filter_subset _ _)
  · have hprod : ∀ X Y : AffineVariety d, ((S X).card : ℝ) * (T Y).card =
        (a X * b Y) * famMass 𝒳 S * famMass 𝒴 T := by
      intro X Y
      dsimp [a, b]
      field_simp
    calc
      _ = (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, a X * b Y) * famMass 𝒳 S * famMass 𝒴 T := by
        simp_rw [hprod]
        simp only [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnormalized hnx.le) hny.le
  · intro X hX Y hY hXflat hYflat hXY F hF hXF hYF
    have hYparts := Finset.mem_inter.mp hY
    have hYlight := (Finset.mem_filter.mp hYparts.1).2
    have hYfull := (Finset.mem_filter.mp hYparts.1).1
    have hXYnotR := (Finset.mem_filter.mp hYparts.2).2
    have hXI : X ∈ I := Finset.mem_filter.mpr ⟨hX, hXflat, by
      apply le_of_not_gt
      intro hn
      exact hYlight.2 ⟨hXflat, hn⟩⟩
    have hYJ : Y ∈ J := Finset.mem_filter.mpr ⟨hYfull, hYflat, by
      apply le_of_not_gt
      intro hn
      exact hYlight.1 ⟨hYflat, hn⟩⟩
    have hXU : X ∈ U := Finset.mem_union_left _ hXI
    have hYU : Y ∈ U := Finset.mem_union_right _ hYJ
    let G := carrier X ⊔ carrier Y
    have hGne : (G : Set (Pt d)).Nonempty := by
      obtain ⟨x, hx⟩ := (RealFlatGeometry.realCarrier_spec X (hUreal X hXU)).1
      exact ⟨x, (show carrier X ≤ G from le_sup_left) hx⟩
    have hGk : Module.finrank ℝ G.direction = k+1 :=
      RealFlatGeometry.realCarrier_join_finrank X Y k (h𝒳 X hX).1 (h𝒴 Y hYfull).1
        (hUreal X hXU) (hUreal Y hYU) (h𝒳 X hX).2 (h𝒴 Y hYfull).2 hXY F hF hXF hYF
    have hGF : RealFlatGeometry.complexify G = F :=
      RealFlatGeometry.complexify_realCarrier_join_eq X Y k (h𝒳 X hX).1 (h𝒴 Y hYfull).1
        (hUreal X hXU) (hUreal Y hYU) (h𝒳 X hX).2 (h𝒴 Y hYfull).2 hXY F hF hXF hYF
    have hocc : ((A.filter (fun H => H ≤ G)).card : ℝ) ≤ τ := by
      apply le_of_not_gt
      intro hr
      apply hXYnotR
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hXI, hYJ⟩, hGk, hr⟩
    have hsub : (L X).filter (fun Z => IsFlat Z ∧ Z.points ⊆ F) ⊆
        U.filter (fun Z => carrier Z ≤ G) := by
      intro Z hZ
      obtain ⟨hZL, hZflat, hZF⟩ := Finset.mem_filter.mp hZ
      have hZparts := Finset.mem_inter.mp hZL
      have hZfull := (Finset.mem_filter.mp hZparts.1).1
      have hZheavy : cutoff ≤ b Z := by
        apply le_of_not_gt
        intro hn
        exact (Finset.mem_filter.mp hZparts.1).2.1 ⟨hZflat, hn⟩
      have hZJ : Z ∈ J := Finset.mem_filter.mpr ⟨hZfull, hZflat, hZheavy⟩
      have hZU : Z ∈ U := Finset.mem_union_right _ hZJ
      refine Finset.mem_filter.mpr ⟨hZU, ?_⟩
      intro q hq
      have hqZ := (RealFlatGeometry.realCarrier_mem Z (hUreal Z hZU) q).mpr hq
      have hqF := hZF hqZ
      rw [← hGF] at hqF
      exact (RealFlatGeometry.real_locus_complexify G hGne q).mp hqF
    have hcount := Finset.card_le_card hsub
    have hcard := CarrierWeights.card_image_filter U carrier hi (fun H => H ≤ G)
    rw [← hcard] at hcount
    have hcountR : (((L X).filter (fun Z => IsFlat Z ∧ Z.points ⊆ F)).card : ℝ) ≤
        ((A.filter (fun H => H ≤ G)).card : ℝ) := by exact_mod_cast hcount
    exact hcountR.trans hocc

theorem assigned_product_weight_sum (𝒳 𝒴 : Finset (AffineVariety d))
    (S T : AffineVariety d → Finset (Pt d)) :
    (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴, ((S X).card : ℝ) * (T Y).card) =
      famMass 𝒳 S * famMass 𝒴 T := by
  simp only [famMass, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

set_option maxHeartbeats 1000000 in
/-- All carrier-pair deletions for generic depth, with the frozen root's
uniform parameter order. Only the moving-root geometry remains to be supplied. -/
theorem generic_depth_full_pruning (d : ℕ) (hd : 0 < d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∀ δ > 0, ∃ θ > 0, ∃ w₀ : ℝ, 1 ≤ w₀ ∧
      ∀ (P : Finset (Pt d)) (w e : ℝ), w₀ ≤ w → w ≤ Real.log (cfgB P) → 0 < e →
      RealFlatCap P c₀ → ∀ (k l : ℕ), l ≤ k → 1 ≤ l → k < d → l+1 < d →
      ∀ (𝒳 𝒴 : Finset (AffineVariety d)) (S T : AffineVariety d → Finset (Pt d)),
        (∀ X ∈ 𝒳, X.IsIrreducible ∧ X.dimension = k) →
        (∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = l) →
        Assignment P 𝒳 S → Assignment P 𝒴 T →
        (∀ Z ∈ 𝒳 ∪ 𝒴, IsFlat Z → IsRealFlat Z) →
        cfgN P * Real.exp (-θ*w) ≤ famMass 𝒳 S →
        cfgN P * Real.exp (-θ*w) ≤ famMass 𝒴 T →
        (k = l →
          ((𝒳.filter IsFlat).card : ℝ) ≤ e * Real.exp (θ*w) ∧
          ((𝒴.filter IsFlat).card : ℝ) ≤ e * Real.exp (θ*w) ∧
          (∀ X ∈ 𝒳, IsFlat X → ((S X).card : ℝ) ≤ famMass 𝒳 S * e⁻¹ * Real.exp (θ*w)) ∧
          (∀ Y ∈ 𝒴, IsFlat Y → ((T Y).card : ℝ) ≤ famMass 𝒴 T * e⁻¹ * Real.exp (θ*w))) →
        ∃ L : AffineVariety d → Finset (AffineVariety d),
          (∀ X ∈ 𝒳, L X ⊆ 𝒴) ∧
          (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, ((S X).card : ℝ) * (T Y).card) ≤
            δ * famMass 𝒳 S * famMass 𝒴 T ∧
          ∀ X ∈ 𝒳, ∀ Y ∈ L X, GenericallyTransverse X Y ∧
            (k = l → ∀ F : AffineSubspace ℂ (Point d),
              Module.finrank ℂ F.direction ≤ k+1 → X.points ⊆ F → Y.points ⊆ F →
              IsFlat X ∧ IsFlat Y ∧
                (((L X).filter (fun Z => IsFlat Z ∧ Z.points ⊆ F)).card : ℝ) ≤
                  Real.exp (ε*w)) := by
  intro ε hε δ hδ
  obtain ⟨θ, hθ, wf, hwf, hθc, hθε, hflat⟩ :=
    generic_depth_flat_pruning_small d hd c₀ hc₀ ε hε (δ/2) (by positivity)
  obtain ⟨wg, hwg, htail⟩ := generic_depth_decay_threshold c₀ (δ/2) hc₀ (by positivity)
  refine ⟨θ, hθ, max wf wg, hwf.trans (le_max_left _ _), ?_⟩
  intro P w e hw hwB he hcap k l hlk hl hkd hld 𝒳 𝒴 S T h𝒳 h𝒴 hS hT hreal hmassX hmassY hbudget
  have hwf' : wf ≤ w := (le_max_left _ _).trans hw
  have hwg' : wg ≤ w := (le_max_right _ _).trans hw
  have hw0 : 0 ≤ w := le_trans (by norm_num) (hwf.trans hwf')
  by_cases hnx0 : famMass 𝒳 S = 0
  · refine ⟨fun _ => ∅, by simp, ?_, by simp⟩
    simp only [Finset.sdiff_empty]
    rw [assigned_product_weight_sum, hnx0]
    simp
  by_cases hny0 : famMass 𝒴 T = 0
  · refine ⟨fun _ => ∅, by simp, ?_, by simp⟩
    simp only [Finset.sdiff_empty]
    rw [assigned_product_weight_sum, hny0]
    simp
  have hnx : 0 < famMass 𝒳 S := lt_of_le_of_ne (famMass_nonneg _ _) (Ne.symm hnx0)
  have hny : 0 < famMass 𝒴 T := lt_of_le_of_ne (famMass_nonneg _ _) (Ne.symm hny0)
  have hB : 0 < cfgB P := by
    have hB0 : 0 ≤ cfgB P := by unfold cfgB; positivity
    by_contra hn
    have hz : cfgB P = 0 := le_antisymm (le_of_not_gt hn) hB0
    rw [hz, Real.log_zero] at hwB
    linarith only [hwf, hwf', hwB]
  obtain ⟨G, hG, hGcost, hGgood⟩ :=
    generic_depth_geometric_pruning P c₀ hcap k l hkd hld 𝒳 𝒴 S T h𝒳 h𝒴 hS hT
  have hnorm := generic_depth_cap_normalized_loss (cfgN P) (famMass 𝒳 S) (famMass 𝒴 T)
    (cfgB P) c₀ θ w hB hc₀ (by linarith only [hθc, hc₀]) hw0 hwB hnx.le hny.le hmassX hmassY
  have hGeoCost : (∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ G X, ((S X).card : ℝ) * (T Y).card) ≤
      (δ/2) * famMass 𝒳 S * famMass 𝒴 T := by
    exact hGcost.trans (hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (htail w hwg') hnx.le) hny.le))
  by_cases hkl : k = l
  · have h𝒴k : ∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = k := by
      simpa only [hkl] using h𝒴
    obtain ⟨hcX, hcY, huX, huY⟩ := hbudget hkl
    obtain ⟨M, hM, hMcost, hMgood⟩ := hflat P w e hwf' hwB he hcap k
      (by omega) (by omega) 𝒳 𝒴 S T h𝒳 h𝒴k hS hT hreal hnx hny hmassX hmassY hcX hcY huX huY
    refine ⟨fun X => G X ∩ M X, ?_, ?_, ?_⟩
    · intro X hX
      exact Finset.Subset.trans Finset.inter_subset_left (hG X hX)
    · have hinter := discarded_product_weight_inter_le 𝒳 𝒴
        (fun X => ((S X).card : ℝ)) (fun Y => ((T Y).card : ℝ)) G M
        (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
      calc
        _ ≤ _ := hinter
        _ ≤ (δ/2) * famMass 𝒳 S * famMass 𝒴 T + (δ/2) * famMass 𝒳 S * famMass 𝒴 T :=
          add_le_add hGeoCost hMcost
        _ = _ := by ring
    · intro X hX Y hY
      obtain ⟨hYG, hYM⟩ := Finset.mem_inter.mp hY
      have htrans := (hGgood X hX Y hYG).1
      refine ⟨htrans, ?_⟩
      intro heq F hF hXF hYF
      obtain ⟨hXflat, hYflat⟩ := (hGgood X hX Y hYG).2 hkl F hF hXF hYF
      have hXY := RealFlatGeometry.genericallyTransverse_flat_ne X Y hXflat htrans
      have hcount := hMgood X hX Y hYM hXflat hYflat hXY F hF hXF hYF
      refine ⟨hXflat, hYflat, ?_⟩
      apply le_trans _ hcount
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ Finset.inter_subset_right)
  · refine ⟨G, hG, hGeoCost.trans ?_, ?_⟩
    · apply mul_le_mul_of_nonneg_right _ hny.le
      apply mul_le_mul_of_nonneg_right _ hnx.le
      linarith only [hδ]
    · intro X hX Y hY
      exact ⟨(hGgood X hX Y hY).1, fun heq => (hkl heq).elim⟩

/-- Finite simultaneous pair conditions, with nonemptiness supplied by
the two irreducible carriers. -/
theorem ForGeneralPair.finset_all {ι : Type*} {X Y : AffineVariety d}
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible) (I : Finset ι)
    (Q : ι → Point d → Point d → Prop) (hI : ∀ i ∈ I, ForGeneralPair X Y (Q i)) :
    ForGeneralPair X Y (fun x y => ∀ i ∈ I, Q i x y) := by
  classical
  revert hI
  induction I using Finset.induction_on with
  | empty =>
      intro hI
      obtain ⟨x, hx⟩ := X.points_nonempty_of_isIrreducible hX
      obtain ⟨y, hy⟩ := Y.points_nonempty_of_isIrreducible hY
      exact ⟨1, ⟨x, hx, y, hy, by simp⟩, by simp⟩
  | @insert i I hi ih =>
      intro hI
      have hhead := hI i (Finset.mem_insert_self i I)
      have htail := ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))
      apply (hhead.and hX hY htail).mono
      intro x hx y hy h j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact h.1
      · exact h.2 j hj

theorem movingRoots_mono (K L : Finset (AffineVariety d)) (hKL : K ⊆ L) (x y : Point d) :
    movingRoots K x y ⊆ movingRoots L x y := by
  rintro z ⟨⟨Z, hZ, hz⟩, hzx, c, hc⟩
  exact ⟨⟨Z, hKL hZ, hz⟩, hzx, c, hc⟩

theorem movingRoots_insert (K : Finset (AffineVariety d)) (Z : AffineVariety d)
    (x y : Point d) :
    movingRoots (insert Z K) x y =
      movingRoots {Z} x y ∪ movingRoots K x y := by
  ext z
  simp only [movingRoots, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton,
    exists_eq_left, Set.mem_union]
  aesop

/-- A finite list of flat targets, each avoiding the centre, contributes at
most one literal moving root per member. -/
theorem movingRoots_flat_finite_ncard_le (K : Finset (AffineVariety d)) (x y : Point d)
    (hflat : ∀ Z ∈ K, IsFlat Z) (havoid : ∀ Z ∈ K, x ∉ Z.points) :
    (movingRoots K x y).Finite ∧ (movingRoots K x y).ncard ≤ K.card := by
  classical
  revert hflat havoid
  induction K using Finset.induction_on with
  | empty =>
      intro hflat havoid
      have he : movingRoots ∅ x y = ∅ := by ext z; simp [movingRoots]
      simp [he]
  | @insert Z K hZ ih =>
      intro hflat havoid
      have hsingle : (movingRoots {Z} x y).Subsingleton := by
        simpa only [movingRoots, Finset.mem_singleton, exists_eq_left] using
          flat_secant_roots_subsingleton Z (hflat Z (Finset.mem_insert_self _ _))
            x y (havoid Z (Finset.mem_insert_self _ _))
      obtain ⟨hfin, hcard⟩ := ih (fun W hW => hflat W (Finset.mem_insert_of_mem hW))
        (fun W hW => havoid W (Finset.mem_insert_of_mem hW))
      rw [movingRoots_insert]
      refine ⟨hsingle.finite.union hfin, ?_⟩
      have hsinglecard : (movingRoots {Z} x y).ncard ≤ 1 :=
        (Set.ncard_le_one hsingle.finite).mpr hsingle
      have hsum := (Set.ncard_union_le (movingRoots {Z} x y) (movingRoots K x y)).trans
        (add_le_add hsinglecard hcard)
      simpa only [Finset.card_insert_of_notMem hZ, Nat.add_comm] using hsum

/-- The remaining moving-root argument, conditional only on the
constructible further-root dichotomy for the finite target list. -/
theorem generic_depth_moving_roots_of_dichotomy
    (X Y : AffineVariety d) (k l : ℕ) (hlk : l ≤ k) (hl : 1 ≤ l)
    (hX : X.IsIrreducible) (hk : X.dimension = k)
    (K : Finset (AffineVariety d)) (hYmem : Y ∈ K)
    (hK : ∀ Z ∈ K, Z.IsIrreducible ∧ Z.dimension = l)
    (htr : ∀ Z ∈ K, GenericallyTransverse X Z)
    (hgood : k = l → ∀ Z ∈ K, ∀ F : AffineSubspace ℂ (Point d),
      Module.finrank ℂ F.direction ≤ k+1 → X.points ⊆ F → Z.points ⊆ F → IsFlat X ∧ IsFlat Z)
    (R : ℝ) (hR : 1 ≤ R)
    (hcount : k = l → ∀ F : AffineSubspace ℂ (Point d),
      Module.finrank ℂ F.direction ≤ k+1 → X.points ⊆ F → Y.points ⊆ F →
      (((K.filter (fun Z => IsFlat Z ∧ Z.points ⊆ F)).card : ℝ)) ≤ R)
    (hdich : ∀ Z ∈ K,
      ForGeneralPair X Y (fun x y => ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x)) ∨
      ForGeneralPair X Y (fun x y => ¬ ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x))) :
    ForGeneralPair X Y (fun x y =>
      y-x ∉ X.tangentSpace x ∧ y-x ∉ Y.tangentSpace y ∧
      (movingRoots K x y).Finite ∧ ((movingRoots K x y).ncard : ℝ) ≤ R) := by
  classical
  have hY := (hK Y hYmem).1
  have hYdim := (hK Y hYmem).2
  let E : AffineVariety d → Prop := fun Z =>
    ForGeneralPair X Y (fun x y => ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x))
  have habsent : ForGeneralPair X Y (fun x y => ∀ Z ∈ K, ¬ E Z →
      ¬ ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x)) := by
    apply ForGeneralPair.finset_all hX hY K
    intro Z hZ
    by_cases he : E Z
    · exact (htr Y hYmem).mono (fun _ _ _ _ _ hne => (hne he).elim)
    · exact ((hdich Z hZ).resolve_left he).mono (fun _ _ _ _ h _ => h)
  by_cases hex : ∃ Z ∈ K, E Z
  · obtain ⟨Z₀, hZ₀, he₀⟩ := hex
    obtain ⟨hkl, hcommon⟩ := geo_secants_further_root X Y Z₀ k l hX hY (hK Z₀ hZ₀).1
      hk hYdim (hK Z₀ hZ₀).2 (by omega) hl (htr Y hYmem) he₀
    have hEq : k = l := Nat.le_antisymm hkl hlk
    obtain ⟨F, hFdim, hXF, hYF⟩ := hcommon hEq
    have hYflat := (hgood hEq Y hYmem F hFdim hXF hYF).2
    have htarget : ∀ Z ∈ K, E Z → IsFlat Z ∧ Z.points ⊆ F := by
      intro Z hZ he
      have hZF := generic_further_root_target_in_flat X Y Z hX hY (hK Z hZ).1
        ((hK Z hZ).2.trans hYdim.symm) (by omega) (htr Y hYmem) he F hXF hYF
      exact ⟨(hgood hEq Z hZ F hFdim hXF hZF).2, hZF⟩
    have havoid : ForGeneralPoint X (fun x => ∀ Z ∈ K, IsFlat Z → x ∉ Z.points) := by
      apply ForGeneralPoint.finset_all hX (X.points_nonempty_of_isIrreducible hX) K
      intro Z hZ
      by_cases hflat : IsFlat Z
      · exact (genericallyTransverse_avoid_flat X Z hflat (htr Z hZ)).mono (fun _ _ h _ => h)
      · obtain ⟨x, hx⟩ := X.points_nonempty_of_isIrreducible hX
        exact ⟨1, ⟨x, hx, by simp⟩, by simp [hflat]⟩
    apply (((htr Y hYmem).and hX hY habsent).and hX hY
      (havoid.on_left (Y.points_nonempty_of_isIrreducible hY))).mono
    intro x hx y hy hh
    obtain ⟨⟨htrans, habs⟩, hav⟩ := hh
    let A := K.filter (fun Z => IsFlat Z ∧ Z.points ⊆ F)
    have hsub : movingRoots K x y ⊆ movingRoots A x y := by
      rintro z ⟨⟨Z, hZ, hz⟩, hzx, c, hc⟩
      by_cases hzy : z = y
      · subst z
        exact ⟨⟨Y, Finset.mem_filter.mpr ⟨hYmem, hYflat, hYF⟩, hy⟩, hzx, c, hc⟩
      · have he : E Z := by
          by_contra he
          exact habs Z hZ he ⟨z, hz, hzx, hzy, c, hc⟩
        exact ⟨⟨Z, Finset.mem_filter.mpr ⟨hZ, htarget Z hZ he⟩, hz⟩, hzx, c, hc⟩
    obtain ⟨hfin, hcard⟩ := movingRoots_flat_finite_ncard_le A x y
      (fun Z hZ => (Finset.mem_filter.mp hZ).2.1)
      (fun Z hZ => hav Z (Finset.mem_filter.mp hZ).1 (Finset.mem_filter.mp hZ).2.1)
    refine ⟨htrans.1, htrans.2, hfin.subset hsub, ?_⟩
    have hn : (movingRoots K x y).ncard ≤ A.card := (Set.ncard_le_ncard hsub hfin).trans hcard
    exact (by exact_mod_cast hn : ((movingRoots K x y).ncard : ℝ) ≤ A.card).trans
      (hcount hEq F hFdim hXF hYF)
  · apply ((htr Y hYmem).and hX hY habsent).mono
    intro x hx y hy hh
    have hsub : movingRoots K x y ⊆ {y} := by
      rintro z ⟨⟨Z, hZ, hz⟩, hzx, c, hc⟩
      by_contra hzy
      have hzy' : z ≠ y := by simpa only [Set.mem_singleton_iff] using hzy
      exact hh.2 Z hZ (fun he => hex ⟨Z, hZ, he⟩) ⟨z, hz, hzx, hzy', c, hc⟩
    have hfin := (Set.finite_singleton y).subset hsub
    have hcard : (movingRoots K x y).ncard ≤ 1 := by
      simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub (Set.finite_singleton y)
    exact ⟨hh.1.1, hh.1.2, hfin, (by exact_mod_cast hcard :
      ((movingRoots K x y).ncard : ℝ) ≤ 1).trans hR⟩

/-- The constructibility frontier in the point model. The alternative is
generic literal existence or generic literal absence, for each fixed target. -/
def FurtherRootDichotomy (d : ℕ) : Prop :=
  ∀ X Y Z : AffineVariety d, X.IsIrreducible → Y.IsIrreducible →
    ForGeneralPair X Y (fun x y => ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x)) ∨
    ForGeneralPair X Y (fun x y => ¬ ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x))

/-- Uniform generic depth from the proved pruning and moving-root
assembly, with the constructible dichotomy as its only extra input. -/
theorem generic_depth_of_further_root_dichotomy (d : ℕ) (hd : 3 ≤ d) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hdich : FurtherRootDichotomy d) :
    ∀ ε > 0, ∀ ε' > 0, ∃ θ > 0, ∃ w₀ : ℝ, ∀ (P : Finset (Pt d)) (w e : ℝ),
      w₀ ≤ w → w ≤ Real.log (cfgB P) → 0 < e → RealFlatCap P c₀ →
      ∀ (k l : ℕ), l ≤ k → 1 ≤ l → k < d → l + 1 < d →
      ∀ (𝒳 𝒴 : Finset (AffineVariety d)) (S T : AffineVariety d → Finset (Pt d)),
        (∀ X ∈ 𝒳, X.IsIrreducible ∧ X.dimension = k) →
        (∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = l) →
        Assignment P 𝒳 S → Assignment P 𝒴 T →
        (∀ Z ∈ 𝒳 ∪ 𝒴, IsFlat Z → IsRealFlat Z) →
        cfgN P * Real.exp (-θ * w) ≤ famMass 𝒳 S →
        cfgN P * Real.exp (-θ * w) ≤ famMass 𝒴 T →
        (k = l →
          ((𝒳.filter IsFlat).card : ℝ) ≤ e * Real.exp (θ * w) ∧
          ((𝒴.filter IsFlat).card : ℝ) ≤ e * Real.exp (θ * w) ∧
          (∀ X ∈ 𝒳, IsFlat X → ((S X).card : ℝ) ≤ famMass 𝒳 S * e⁻¹ * Real.exp (θ * w)) ∧
          (∀ Y ∈ 𝒴, IsFlat Y → ((T Y).card : ℝ) ≤ famMass 𝒴 T * e⁻¹ * Real.exp (θ * w))) →
        ∃ L : AffineVariety d → Finset (AffineVariety d),
          (∀ X ∈ 𝒳, L X ⊆ 𝒴) ∧
          ∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, ((S X).card : ℝ) * (T Y).card ≤
            ε' * famMass 𝒳 S * famMass 𝒴 T ∧
          ∀ X ∈ 𝒳, ∀ Y ∈ L X, ForGeneralPair X Y (fun x y =>
            y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
            (movingRoots (L X) x y).Finite ∧
            ((movingRoots (L X) x y).ncard : ℝ) ≤ Real.exp (ε * w)) := by
  intro ε hε δ hδ
  obtain ⟨θ, hθ, w₀, hw₀, hprune⟩ := generic_depth_full_pruning d (by omega) c₀ hc₀ ε hε δ hδ
  refine ⟨θ, hθ, w₀, ?_⟩
  intro P w e hw hwB he hcap k l hlk hl hkd hld 𝒳 𝒴 S T h𝒳 h𝒴 hS hT hreal hmassX hmassY hbudget
  obtain ⟨L, hL, hcost, hgood⟩ := hprune P w e hw hwB he hcap k l hlk hl hkd hld
    𝒳 𝒴 S T h𝒳 h𝒴 hS hT hreal hmassX hmassY hbudget
  refine ⟨L, hL, hcost, ?_⟩
  intro X hX Y hY
  have hK : ∀ Z ∈ L X, Z.IsIrreducible ∧ Z.dimension = l :=
    fun Z hZ => h𝒴 Z (hL X hX hZ)
  have hR : 1 ≤ Real.exp (ε*w) := by
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg hε.le (le_trans (by norm_num) (hw₀.trans hw))
  apply generic_depth_moving_roots_of_dichotomy X Y k l hlk hl (h𝒳 X hX).1 (h𝒳 X hX).2
    (L X) hY hK (fun Z hZ => (hgood X hX Z hZ).1)
    (fun heq Z hZ F hF hXF hZF =>
      let h := (hgood X hX Z hZ).2 heq F hF hXF hZF
      ⟨h.1, h.2.1⟩)
    (Real.exp (ε*w)) hR
    (fun heq F hF hXF hYF => ((hgood X hX Y hY).2 heq F hF hXF hYF).2.2)
    (fun Z hZ => hdich X Y Z (h𝒳 X hX).1 (hK Y hY).1)

/-- `geo:generic-depth` (`secants.tex:110–147`), finitary form. Families `𝒳, 𝒴` of distinct
irreducible carriers of dimensions `k ≥ l ≥ 1`, `k < d`, `l < d - 1`, with disjoint assigned
real sample sets (source and target assignments may overlap), masses
`n_x, n_y ≥ N exp(-θ w)`, `w₀ ≤ w ≤ log B`, flat members real, and for `k = l` at most
`e exp(θ w)` flat members per family, each of normalized weight at most `e⁻¹ exp(θ w)`.
Then one can discard carrier pairs of normalized product weight at most `ε'` so that, for every
remaining pair `(X, Y)` (that is, `Y` in the list `L X`), at a general pair both projected
tangents are injective and there are at most `exp(ε w)` moving roots on the list over `π_x y`.
The thresholds `θ, w₀` depend only on `d, c₀, ε, ε'`. -/
theorem geo_generic_depth (d : ℕ) (hd : 3 ≤ d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∀ ε' > 0, ∃ θ > 0, ∃ w₀ : ℝ, ∀ (P : Finset (Pt d)) (w e : ℝ),
      w₀ ≤ w → w ≤ Real.log (cfgB P) → 0 < e → RealFlatCap P c₀ →
      ∀ (k l : ℕ), l ≤ k → 1 ≤ l → k < d → l + 1 < d →
      ∀ (𝒳 𝒴 : Finset (AffineVariety d)) (S T : AffineVariety d → Finset (Pt d)),
        (∀ X ∈ 𝒳, X.IsIrreducible ∧ X.dimension = k) →
        (∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = l) →
        Assignment P 𝒳 S → Assignment P 𝒴 T →
        (∀ Z ∈ 𝒳 ∪ 𝒴, IsFlat Z → IsRealFlat Z) →
        cfgN P * Real.exp (-θ * w) ≤ famMass 𝒳 S →
        cfgN P * Real.exp (-θ * w) ≤ famMass 𝒴 T →
        (k = l →
          ((𝒳.filter IsFlat).card : ℝ) ≤ e * Real.exp (θ * w) ∧
          ((𝒴.filter IsFlat).card : ℝ) ≤ e * Real.exp (θ * w) ∧
          (∀ X ∈ 𝒳, IsFlat X → ((S X).card : ℝ) ≤ famMass 𝒳 S * e⁻¹ * Real.exp (θ * w)) ∧
          (∀ Y ∈ 𝒴, IsFlat Y → ((T Y).card : ℝ) ≤ famMass 𝒴 T * e⁻¹ * Real.exp (θ * w))) →
        ∃ L : AffineVariety d → Finset (AffineVariety d),
          (∀ X ∈ 𝒳, L X ⊆ 𝒴) ∧
          ∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, ((S X).card : ℝ) * (T Y).card ≤
            ε' * famMass 𝒳 S * famMass 𝒴 T ∧
          ∀ X ∈ 𝒳, ∀ Y ∈ L X, ForGeneralPair X Y (fun x y =>
            y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
            (movingRoots (L X) x y).Finite ∧
            ((movingRoots (L X) x y).ncard : ℝ) ≤ Real.exp (ε * w)) := by
  exact generic_depth_of_further_root_dichotomy d hd c₀ hc₀
    (fun X Y Z hX hY => ConstructibleSecants.generic_further_root_dichotomy X Y Z hX hY)

end

end TrackD
end DistinctDistances
