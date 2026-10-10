import DistinctDistances.TrackD.Profiles.RankCore

namespace DistinctDistances.TrackD.RankCore

noncomputable section

def timeAt {d : ℕ} (t : Fin d → ℝ) (hd : 0 < d) (i : ℕ) : ℝ :=
  t ⟨min i (d-1), by omega⟩

theorem timeAt_eq {d : ℕ} (t : Fin d → ℝ) (hd : 0 < d) (i : Fin d) :
    timeAt t hd i.val = t i := by
  have hi : i.val ≤ d - 1 := by omega
  simp only [timeAt, min_eq_left hi]

theorem timeAt_mono {d : ℕ} (t : Fin d → ℝ) (hd : 0 < d) (ht : Monotone t) :
    Monotone (timeAt t hd) := by
  intro i j hij
  apply ht
  exact Fin.le_iff_val_le_val.mpr (min_le_min_right _ hij)

theorem adjacent_gap_bound (u : ℕ → ℝ) (r m : ℕ) (hrm : r ≤ m) (δ : ℝ)
    (hgap : ∀ i, r ≤ i → i < m → u (i+1) - u i ≤ δ) :
    u m - u r ≤ ((m-r : ℕ) : ℝ) * δ := by
  induction m, hrm using Nat.le_induction with
  | base => simp
  | succ m hrm ih =>
    have hprev := ih (fun i hri him => hgap i hri (by omega))
    have hstep := hgap m hrm (by omega)
    have hnat : m + 1 - r = (m-r) + 1 := by omega
    rw [hnat, Nat.cast_add, Nat.cast_one]
    linarith

/-- A preceding cluster starts just before its first cut. Its entire width
is at most 2dξ, with no dependence on any subsequently chosen dense subset. -/
theorem preceding_cluster {d : ℕ} (hd : 0 < d) (t : Fin d → ℝ) (ht : Monotone t)
    (ξ : ℝ) (hξ : 0 < ξ) (j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ d)
    (b : ℝ) (hb : OnPlateau t j ξ b) :
    ∃ (r : ℕ) (a c : ℝ), r < j ∧ OnPlateau t r ξ a ∧ OnPlateau t j 0 c ∧
      a ≤ c ∧ c ≤ b ∧ c-a ≤ 2*(d : ℝ)*ξ := by
  let u := timeAt t hd
  have hu : Monotone u := timeAt_mono t hd ht
  let C := (Finset.range j).filter (fun r =>
    ∀ i, r ≤ i → i < j-1 → u (i+1) - u i ≤ 2*ξ)
  have hCne : C.Nonempty := by
    refine ⟨j-1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    intro i hri hij
    omega
  let r := C.min' hCne
  have hrmem : r ∈ C := Finset.min'_mem C hCne
  obtain ⟨hrj, hrinside⟩ := Finset.mem_filter.mp hrmem
  have hrlt : r < j := Finset.mem_range.mp hrj
  have hbefore : 0 < r → 2*ξ < u r - u (r-1) := by
    intro hrpos
    by_contra h
    have hgap : u r - u (r-1) ≤ 2*ξ := le_of_not_gt h
    have hmem : r-1 ∈ C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      intro i hri hij
      by_cases hi : i = r-1
      · subst i
        have heq : r-1+1 = r := by omega
        simpa only [heq] using hgap
      · exact hrinside i (by omega) hij
    have hle : r ≤ r-1 := Finset.min'_le C (r-1) hmem
    omega
  let a := u r - ξ
  let c := u (j-1) + ξ
  have hlast : c ≤ b := by
    let i : Fin d := ⟨j-1, by omega⟩
    have h := (hb i).1 (by dsimp [i]; omega)
    have heq := timeAt_eq t hd i
    simpa only [c, u, i, heq] using h
  have hac : a ≤ c := by
    have hm := hu (show r ≤ j-1 by omega)
    dsimp only [a, c]
    linarith
  have ha : OnPlateau t r ξ a := by
    intro i
    have heq := timeAt_eq t hd i
    constructor
    · intro hir
      have hrpos : 0 < r := by omega
      have hm : t i ≤ u (r-1) := by
        rw [← heq]
        exact hu (by omega)
      have hwide := hbefore hrpos
      dsimp only [a]
      linarith
    · intro hri
      have hm : u r ≤ t i := by
        rw [← heq]
        exact hu hri
      dsimp only [a]
      linarith
  have hc : OnPlateau t j 0 c := by
    intro i
    have heq := timeAt_eq t hd i
    constructor
    · intro hij
      have hm : t i ≤ u (j-1) := by
        rw [← heq]
        exact hu (by omega)
      dsimp only [c]
      linarith
    · intro hji
      have hh := (hb i).2 hji
      linarith
  have hbound := adjacent_gap_bound u r (j-1) (by omega) (2*ξ) hrinside
  have hnat : (j-1-r)+1 = j-r := by omega
  have hcast : ((j-1-r : ℕ) : ℝ) + 1 = ((j-r : ℕ) : ℝ) := by exact_mod_cast hnat
  have hcount : ((j-r : ℕ) : ℝ) ≤ d := by exact_mod_cast (show j-r ≤ d by omega)
  have hwidth : c-a ≤ 2*(d : ℝ)*ξ := by
    dsimp only [a, c]
    nlinarith [mul_le_mul_of_nonneg_right hcount (by positivity : 0 ≤ 2*ξ)]
  exact ⟨r, a, c, hrlt, ha, hc, hac, hlast, hwidth⟩

end
end DistinctDistances.TrackD.RankCore
