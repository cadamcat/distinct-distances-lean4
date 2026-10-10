import DistinctDistances.TrackD.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Set.Card

/-! The stabilizer calculation of `secants.tex:351–367`, in the affine chart where the
fixed projective line is at infinity. The geometric reduction supplies a faithful group of
maps `u ↦ χ(g) u + b(g)`, excludes translations, and bounds intersection with a line. -/

namespace DistinctDistances.TrackD.PerspectiveCore

open scoped Classical
noncomputable section

variable {G : Type*} [Group G]

theorem scalar_injective (χ : G →* ℂˣ) (b : G → Point 2)
    (hfaithful : ∀ g, χ g = 1 → b g = 0 → g = 1)
    (htranslation : ∀ g, χ g = 1 → b g = 0) : Function.Injective χ := by
  apply (injective_iff_map_eq_one χ).mpr
  intro g hg
  exact hfaithful g hg (htranslation g hg)

/-- Trivial translation kernel makes the group abelian; a nonidentity scalar then
determines a common fixed center. -/
theorem center_exists (χ : G →* ℂˣ) (b : G → Point 2)
    (hinj : Function.Injective χ)
    (hcomp : ∀ g h, b (g * h) = (χ g : ℂ) • b h + b g) :
    ∃ c : Point 2, ∀ g, b g = (1 - (χ g : ℂ)) • c := by
  have hcomm : ∀ g h : G, g * h = h * g := by
    intro g h
    apply hinj
    simp only [map_mul, mul_comm]
  by_cases hn : ∃ g : G, χ g ≠ 1
  · obtain ⟨g₀, hg₀⟩ := hn
    have hscalar : (χ g₀ : ℂ) ≠ 1 := by
      intro h
      exact hg₀ (Units.ext h)
    have hden : (1 : ℂ) - (χ g₀ : ℂ) ≠ 0 := sub_ne_zero.mpr hscalar.symm
    refine ⟨((1 : ℂ) - (χ g₀ : ℂ))⁻¹ • b g₀, ?_⟩
    intro g
    have he : (χ g₀ : ℂ) • b g + b g₀ = (χ g : ℂ) • b g₀ + b g := by
      rw [← hcomp, ← hcomp, hcomm g₀ g]
    ext i
    have hi := congrFun he i
    change (χ g₀ : ℂ) * b g i + b g₀ i = (χ g : ℂ) * b g₀ i + b g i at hi
    change b g i = (1 - (χ g : ℂ)) * (((1 : ℂ) - (χ g₀ : ℂ))⁻¹ * b g₀ i)
    field_simp [hden]
    linear_combination -hi
  · push Not at hn
    have hg : ∀ g : G, g = 1 := fun g => hinj ((hn g).trans χ.map_one.symm)
    have hb0 : b 1 = 0 := by
      have h := hcomp 1 1
      simp only [one_mul, map_one, Units.val_one, one_smul] at h
      exact add_left_cancel (show b 1 + b 1 = b 1 + 0 by simpa only [add_zero] using h.symm)
    refine ⟨0, ?_⟩
    intro g
    rw [hg g, hb0]
    simp

def orbit (χ : G →* ℂˣ) (b : G → Point 2) (p : Point 2) (g : G) : Point 2 :=
  (χ g : ℂ) • p + b g

theorem orbit_form (χ : G →* ℂˣ) (b : G → Point 2) (c p : Point 2)
    (hcenter : ∀ g, b g = (1 - (χ g : ℂ)) • c) (g : G) :
    orbit χ b p g = (χ g : ℂ) • (p - c) + c := by
  ext i
  simp only [orbit, hcenter, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The orbit of any point other than the common center is free. -/
theorem orbit_injective (χ : G →* ℂˣ) (b : G → Point 2) (c p : Point 2)
    (hinj : Function.Injective χ) (hcenter : ∀ g, b g = (1 - (χ g : ℂ)) • c)
    (hp : p ≠ c) : Function.Injective (orbit χ b p) := by
  intro g h he
  rw [orbit_form χ b c p hcenter, orbit_form χ b c p hcenter] at he
  have hs : ((χ g : ℂ) - (χ h : ℂ)) • (p - c) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact add_right_cancel he
  have hsc : (χ g : ℂ) = (χ h : ℂ) :=
    sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr hp))
  exact hinj (Units.ext hsc)

theorem orbit_on_line (χ : G →* ℂˣ) (b : G → Point 2) (c p : Point 2)
    (hcenter : ∀ g, b g = (1 - (χ g : ℂ)) • c) (g : G) :
    orbit χ b p g ∈ AffineSubspace.mk' c (ℂ ∙ (p - c)) := by
  rw [orbit_form χ b c p hcenter, AffineSubspace.mem_mk']
  change (χ g : ℂ) • (p - c) + c - c ∈ (ℂ ∙ (p - c) : Submodule ℂ (Point 2))
  rw [add_sub_cancel_right]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (p - c))

theorem orbit_line_dimension (c p : Point 2) (hp : p ≠ c) :
    Module.finrank ℂ (AffineSubspace.mk' c (ℂ ∙ (p - c))).direction = 1 := by
  rw [AffineSubspace.direction_mk']
  exact finrank_span_singleton (sub_ne_zero.mpr hp)

/-- A finite line intersection containing a free orbit bounds the entire stabilizer,
including groups not known to be finite beforehand. -/
theorem stabilizer_bound (χ : G →* ℂˣ) (b : G → Point 2) (c p : Point 2)
    (hinj : Function.Injective χ) (hcenter : ∀ g, b g = (1 - (χ g : ℂ)) • c)
    (hp : p ≠ c) (T : Set (Point 2)) (hT : T.Finite)
    (hmem : ∀ g, orbit χ b p g ∈ T) :
    (Set.univ : Set G).Finite ∧ (Set.univ : Set G).ncard ≤ T.ncard := by
  have horbit := orbit_injective χ b c p hinj hcenter hp
  have hpre : orbit χ b p ⁻¹' T = Set.univ := Set.eq_univ_of_forall hmem
  refine ⟨?_, ?_⟩
  · have hf := hT.preimage horbit.injOn
    rwa [hpre] at hf
  · exact Set.ncard_le_ncard_of_injOn (orbit χ b p)
      (fun g hg => hmem g) horbit.injOn hT

end
end DistinctDistances.TrackD.PerspectiveCore
