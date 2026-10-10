import DistinctDistances.TrackD.PerspectiveCore

namespace DistinctDistances.TrackD.PerspectiveCore

open scoped Classical
noncomputable section

variable {G : Type*} [Group G]

theorem offset_one (χ : G →* ℂˣ) (b : G → Point 2)
    (hcomp : ∀ g h, b (g * h) = (χ g : ℂ) • b h + b g) : b 1 = 0 := by
  have h := hcomp 1 1
  simp only [one_mul, map_one, Units.val_one, one_smul] at h
  exact add_left_cancel (show b 1 + b 1 = b 1 + 0 by simpa only [add_zero] using h.symm)

/-- Iterating a translation gives its characteristic-zero arithmetic progression. -/
theorem translation_orbit_form (χ : G →* ℂˣ) (b : G → Point 2)
    (hcomp : ∀ g h, b (g * h) = (χ g : ℂ) • b h + b g)
    (g : G) (hscalar : χ g = 1) (p : Point 2) (n : ℕ) :
    orbit χ b p (g ^ n) = p + n • b g := by
  have hpow : ∀ n : ℕ, b (g ^ n) = n • b g := by
    intro n
    induction n with
    | zero => simp [offset_one χ b hcomp]
    | succ n ih =>
      rw [pow_succ', hcomp, hscalar]
      simp only [Units.val_one, one_smul, ih, Nat.succ_eq_add_one, add_nsmul, one_nsmul]
  simp [orbit, map_pow, hscalar, hpow]

theorem translation_orbit_injective (χ : G →* ℂˣ) (b : G → Point 2)
    (hcomp : ∀ g h, b (g * h) = (χ g : ℂ) • b h + b g)
    (g : G) (hscalar : χ g = 1) (p : Point 2) (hb : b g ≠ 0) :
    Function.Injective (fun n : ℕ => orbit χ b p (g ^ n)) := by
  intro n m he
  change orbit χ b p (g ^ n) = orbit χ b p (g ^ m) at he
  rw [translation_orbit_form χ b hcomp g hscalar p,
    translation_orbit_form χ b hcomp g hscalar p] at he
  have hnsmul := add_left_cancel he
  have hs : ((n : ℂ) - (m : ℂ)) • b g = 0 := by
    rw [sub_smul, sub_eq_zero]
    simpa only [Nat.cast_smul_eq_nsmul] using hnsmul
  have hnm : (n : ℂ) = (m : ℂ) :=
    sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hb)
  exact_mod_cast hnm

/-- A finite curve–line intersection cannot contain the orbit of a nonzero translation.
The geometric proof supplies that intersection and its degree bound. -/
theorem translation_zero_of_finite_orbit (χ : G →* ℂˣ) (b : G → Point 2)
    (hcomp : ∀ g h, b (g * h) = (χ g : ℂ) • b h + b g)
    (g : G) (hscalar : χ g = 1) (p : Point 2) (T : Set (Point 2))
    (hT : T.Finite) (hmem : ∀ n : ℕ, orbit χ b p (g ^ n) ∈ T) : b g = 0 := by
  by_contra hb
  have hinj := translation_orbit_injective χ b hcomp g hscalar p hb
  have hpre : (fun n : ℕ => orbit χ b p (g ^ n)) ⁻¹' T = Set.univ :=
    Set.eq_univ_of_forall hmem
  have hf := hT.preimage hinj.injOn
  rw [hpre] at hf
  exact Set.infinite_univ hf

end
end DistinctDistances.TrackD.PerspectiveCore
