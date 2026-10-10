import DistinctDistances.Bridges.AmbientHilbert
import DistinctDistances.Bridges.ProjectiveCurves
import DistinctDistances.TrackA.Projection

/-! A uniform high-multiplicity point bound from finite plane projection and the polar estimate. -/

namespace DistinctDistances.Bridges
open scoped BigOperators Classical
noncomputable section

 theorem nonlinear_curve_degree_ge_two {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) (hline : ¬ TrackD.IsLine Y) :
    2 ≤ Y.degree := by
  obtain ⟨a,ha⟩ := curve_degree_nat Y hY hdim
  have hone := Y.one_le_degree hY.ne_top
  have hne : a ≠ 1 := by
    intro he
    apply hline
    apply degree_one_curve_line Y hY hdim
    simpa [he] using ha
  have hapos : 1 ≤ a := by exact_mod_cast (ha ▸ hone)
  rw [ha]
  exact_mod_cast (by omega : 2 ≤ a)

 theorem highmult_mem_curve {n : ℕ} (Y : AffineVariety n) (hY : Y.IsIrreducible)
    (p : Point n) (hp : Y.degree / 2 < Y.multiplicity p) : p ∈ Y.points := by
  by_contra h
  have hz := Y.multiplicity_eq_zero_off p h
  have ha := Y.one_le_degree hY.ne_top
  linarith

 theorem highmult_ge_two {n : ℕ} (Y : AffineVariety n) (hY : Y.IsIrreducible)
    (hdim : Y.dimension = 1) (ha : 2 ≤ Y.degree)
    (p : Point n) (hp : Y.degree / 2 < Y.multiplicity p) : 2 ≤ Y.multiplicity p := by
  obtain ⟨m,hm⟩ := curve_multiplicity_nat Y hY hdim p
  have hmpos : (1 : ℚ) < m := by rw [hm] at hp; linarith
  have hm2 : 2 ≤ m := by
    have h : 1 < m := by exact_mod_cast hmpos
    omega
  rw [hm]
  exact_mod_cast hm2

 theorem curve_exists_point_off {n : ℕ} (Y : AffineVariety n)
    (hdim : Y.dimension = 1) (hn : 2 ≤ n) : ∃ x : Point n, x ∉ Y.points := by
  by_contra! h
  apply curve_ideal_ne_bot Y hdim hn
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply MvPolynomial.funext
  intro x
  simpa using (h x) f hf

 theorem curve_highmult_finset_bound {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) (hline : ¬ TrackD.IsLine Y)
    (S : Finset (Point n)) (hS : ∀ p ∈ S, Y.degree / 2 < Y.multiplicity p) :
    S.card ≤ 8 := by
  classical
  have hcard : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hpq
    rcases TrackA.exists_linear_through_two_or_line Y hY hdim p q hpq with
      ⟨f, hfdeg, hfY, hfp, hfq⟩ | hline'
    · have hsum := TrackA.curve_two_point_cut Y hY hdim f hfY hfdeg p q hpq
        (highmult_mem_curve Y hY p (hS p hp)) (highmult_mem_curve Y hY q (hS q hq)) hfp hfq
      have h1 := hS p hp
      have h2 := hS q hq
      linarith
    · exact hline hline'
  omega

 theorem curve_highmult_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : AffineVariety n,
      TrackD.IsCurve Y → ¬ TrackD.IsLine Y →
      {p : Point n | Y.degree / 2 < Y.multiplicity p}.Finite ∧
        ({p : Point n | Y.degree / 2 < Y.multiplicity p}.ncard : ℝ) ≤ C := by
  refine ⟨8,by norm_num,?_⟩
  intro Y hY hline
  let S := {p : Point n | Y.degree / 2 < Y.multiplicity p}
  have hfin : S.Finite := by
    by_contra h
    obtain ⟨T,hTS,hcard⟩ := Set.Infinite.exists_subset_card_eq h 9
    have hc := curve_highmult_finset_bound Y hY.1 hY.2 hline T (fun p hp => hTS hp)
    omega
  refine ⟨hfin,?_⟩
  have hc := curve_highmult_finset_bound Y hY.1 hY.2 hline hfin.toFinset
    (fun p hp => hfin.mem_toFinset.mp hp)
  change (S.ncard : ℝ) ≤ 8
  rw [Set.ncard_eq_toFinset_card S hfin]
  exact_mod_cast hc

end
end DistinctDistances.Bridges
