import DistinctDistances.TrackA.HypersurfaceJetsSupport
import DistinctDistances.TrackA.CurveLengthSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical

theorem length_cut_domain_exact (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    (I J : Ideal R) (f : R) (hdetect : ∀ a, f*a ∈ I ↔ a ∈ J) :
    Module.length K (R ⧸ I) =
      Module.length K (R ⧸ J) + Module.length K (R ⧸ I ⊔ Ideal.span {f}) := by
  let mulf : R →ₗ[R] R ⧸ I := I.mkQ.comp (LinearMap.mulLeft R f)
  let L : (R ⧸ J) →ₗ[R] R ⧸ I := J.liftQ mulf (by
    intro a ha
    change Ideal.Quotient.mk I (f*a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hdetect a).mpr ha))
  let hI : I ≤ I ⊔ Ideal.span {f} := le_sup_left
  let π : (R ⧸ I) →ₗ[R] (R ⧸ I ⊔ Ideal.span {f}) := Submodule.factor hI
  have hL (a : R) : L (J.mkQ a) = I.mkQ (f*a) := rfl
  have hπ (a : R) : π (I.mkQ a) = (I ⊔ Ideal.span {f}).mkQ a := rfl
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨a, rfl⟩ := J.mkQ_surjective x
    rw [LinearMap.mem_ker, hL] at hx
    change Ideal.Quotient.mk I (f*a) = 0 at hx
    have ha := (hdetect a).mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    change J.mkQ a ∈ (⊥ : Submodule R (R ⧸ J))
    simpa only [Submodule.mem_bot, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  have hex : Function.Exact L π := by
    intro x
    obtain ⟨a, rfl⟩ := I.mkQ_surjective x
    rw [hπ]
    change Ideal.Quotient.mk (I ⊔ Ideal.span {f}) a = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro ha
      obtain ⟨b, hb, v, hv, heq⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hv
      refine ⟨J.mkQ c, ?_⟩
      rw [hL]
      apply (Submodule.Quotient.eq _).mpr
      rw [← heq, hc]
      convert I.neg_mem hb using 1 <;> ring
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := J.mkQ_surjective y
      rw [hL] at hy
      have hmem : f*b-a ∈ I := (Submodule.Quotient.eq _).mp hy
      have hfb : f*b ∈ I ⊔ Ideal.span {f} :=
        (show Ideal.span {f} ≤ I ⊔ Ideal.span {f} from le_sup_right)
          (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
      have hdiff : f*b-a ∈ I ⊔ Ideal.span {f} :=
        (show I ≤ I ⊔ Ideal.span {f} from le_sup_left) hmem
      simpa only [sub_sub_cancel] using (I ⊔ Ideal.span {f}).sub_mem hfb hdiff
  exact Module.length_eq_add_of_exact (L.restrictScalars K) (π.restrictScalars K)
    hinj (Submodule.factor_surjective hI) hex

theorem hypersurface_origin_jet_length {n : ℕ} (f : Poly n) (s : ℕ)
    (hs : (f : MvPowerSeries (Fin n) ℂ).order = (s : ℕ∞)) (t : ℕ) (hst : s ≤ t) :
    Module.finrank ℂ
      (Poly n ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1) ⊔ Ideal.span {f}) =
      (t+n).choose n - (t-s+n).choose n := by
  let I := MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1)
  let J := MvPolynomial.idealOfVars (Fin n) ℂ ^ (t-s+1)
  have hsub : I ≤ I ⊔ Ideal.span {f} := le_sup_left
  letI : Module.Finite ℂ (Poly n ⧸ I ⊔ Ideal.span {f}) :=
    Module.Finite.of_surjective ((Submodule.factor hsub).restrictScalars ℂ)
      (Submodule.factor_surjective hsub)
  have he := length_cut_domain_exact ℂ (Poly n) I J f (by
    intro a
    have h := vars_power_mul_detect f s hs (t+1) (by omega) a
    simpa only [show t+1-s = t-s+1 by omega] using h)
  rw [Module.length_eq_finrank, Module.length_eq_finrank, Module.length_eq_finrank] at he
  have hn : Module.finrank ℂ (Poly n ⧸ I) = Module.finrank ℂ (Poly n ⧸ J) +
      Module.finrank ℂ (Poly n ⧸ I ⊔ Ideal.span {f}) := by exact_mod_cast he
  dsimp [I, J] at hn
  rw [point_jet_quotient_finrank, point_jet_quotient_finrank] at hn
  omega

set_option maxHeartbeats 800000 in
instance point_jet_cut_quotient_finite {n : ℕ} (t : ℕ) (f : Poly n) :
    Module.Finite ℂ (Poly n ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ t ⊔ Ideal.span {f}) := by
  let h : MvPolynomial.idealOfVars (Fin n) ℂ ^ t ≤
      MvPolynomial.idealOfVars (Fin n) ℂ ^ t ⊔ Ideal.span {f} := le_sup_left
  exact Module.Finite.of_surjective ((Submodule.factor h).restrictScalars ℂ)
    (Submodule.factor_surjective h)

end
end DistinctDistances.TrackA
