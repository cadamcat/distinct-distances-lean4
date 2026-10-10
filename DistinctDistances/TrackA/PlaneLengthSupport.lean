import DistinctDistances.TrackA.CurveLengthSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- A cut loses at most the length of any quotient through which its
multiplication map factors. The bound includes infinite lengths. -/
theorem length_cut_domain_bound (R : Type*) [CommRing R] (I J : Ideal R) (f : R)
    (hkill : ∀ a ∈ J, f*a ∈ I) :
    Module.length R (R ⧸ I) ≤
      Module.length R (R ⧸ J) + Module.length R (R ⧸ I ⊔ Ideal.span {f}) := by
  let mulf : R →ₗ[R] R ⧸ I := I.mkQ.comp (LinearMap.mulLeft R f)
  let L : (R ⧸ J) →ₗ[R] R ⧸ I := J.liftQ mulf (by
    intro a ha
    change I.mkQ (f*a) = 0
    change Ideal.Quotient.mk I (f*a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hkill a ha))
  let hI : I ≤ I ⊔ Ideal.span {f} := le_sup_left
  let π : (R ⧸ I) →ₗ[R] (R ⧸ I ⊔ Ideal.span {f}) := Submodule.factor hI
  have hL (a : R) : L (J.mkQ a) = I.mkQ (f*a) := rfl
  have hπ (a : R) : π (I.mkQ a) = (I ⊔ Ideal.span {f}).mkQ a := rfl
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
  exact curve_length_le_add_of_exact L π (Submodule.factor_surjective hI) hex

/-- Two equations of orders r and s leave at least the corresponding
truncated length after subtracting the two multiplication domains. -/
theorem length_two_order_cut_bound (R : Type*) [CommRing R] (m : Ideal R)
    (f g : R) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hf : f ∈ m^r) (hg : g ∈ m^s) :
    Module.length R (R ⧸ m^(r+s-1)) ≤
      Module.length R (R ⧸ m^(s-1)) + Module.length R (R ⧸ m^(r-1)) +
        Module.length R (R ⧸ Ideal.span {f,g}) := by
  let t := r+s-1
  have hfkill : ∀ a ∈ m^(s-1), f*a ∈ m^t := by
    intro a ha
    have hh := Ideal.mul_mem_mul hf ha
    rwa [← pow_add, show r+(s-1) = t by dsimp [t]; omega] at hh
  have hgkill : ∀ a ∈ m^(r-1), g*a ∈ m^t ⊔ Ideal.span {f} := by
    intro a ha
    apply (show m^t ≤ m^t ⊔ Ideal.span {f} from le_sup_left)
    have hh := Ideal.mul_mem_mul hg ha
    rwa [← pow_add, show s+(r-1) = t by dsimp [t]; omega] at hh
  have h₁ := length_cut_domain_bound R (m^t) (m^(s-1)) f hfkill
  have h₂ := length_cut_domain_bound R (m^t ⊔ Ideal.span {f}) (m^(r-1)) g hgkill
  have hlast : Module.length R (R ⧸ (m^t ⊔ Ideal.span {f}) ⊔ Ideal.span {g}) ≤
      Module.length R (R ⧸ Ideal.span {f,g}) := by
    apply Module.length_le_of_surjective
      (Submodule.factor (show Ideal.span {f,g} ≤ (m^t ⊔ Ideal.span {f}) ⊔ Ideal.span {g} from
        Ideal.span_le.mpr (by
          intro a ha
          rcases Set.mem_insert_iff.mp ha with h | h
          · subst a
            apply (show m^t ⊔ Ideal.span {f} ≤ (m^t ⊔ Ideal.span {f}) ⊔ Ideal.span {g} from le_sup_left)
            exact (show Ideal.span {f} ≤ m^t ⊔ Ideal.span {f} from le_sup_right) (Ideal.subset_span rfl)
          · rw [Set.mem_singleton_iff] at h
            subst a
            exact (show Ideal.span {g} ≤ (m^t ⊔ Ideal.span {f}) ⊔ Ideal.span {g} from le_sup_right)
              (Ideal.subset_span rfl))))
    exact Submodule.factor_surjective _
  calc
    _ ≤ Module.length R (R ⧸ m^(s-1)) +
        (Module.length R (R ⧸ m^(r-1)) +
          Module.length R (R ⧸ (m^t ⊔ Ideal.span {f}) ⊔ Ideal.span {g})) :=
      h₁.trans (add_le_add le_rfl h₂)
    _ ≤ _ := by simpa only [add_assoc] using add_le_add le_rfl (add_le_add le_rfl hlast)

end
end DistinctDistances.TrackA
