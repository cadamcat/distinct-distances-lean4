import DistinctDistances.TrackA.GenericLinearCutSupport

namespace DistinctDistances.TrackA
noncomputable section

/-- The actual quotient map between the two standard localized charts. -/
def localizedQuotientMap {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    Localization.Away x →+* Localization.Away (Ideal.Quotient.mk I x) :=
  IsLocalization.Away.map _ _ (Ideal.Quotient.mk I) x

/-- Localizing a quotient introduces exactly the localized original
ideal as kernel, including when the localization is the zero ring. -/
theorem localizedQuotientMap_ker {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    RingHom.ker (localizedQuotientMap I x) =
      I.map (algebraMap R (Localization.Away x)) := by
  let S := Localization.Away x
  let B := Localization.Away (Ideal.Quotient.mk I x)
  ext z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers x) z
  change localizedQuotientMap I x (IsLocalization.mk' S a s) = 0 ↔ _
  rw [localizedQuotientMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff (Submonoid.powers x)]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨n, hn⟩ := t.property
    change Ideal.Quotient.mk I x ^ n = (t : R ⧸ I) at hn
    refine ⟨x ^ n, ⟨n, rfl⟩, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, hn]
    exact ht
  · rintro ⟨m, ⟨n, rfl⟩, hm⟩
    refine ⟨⟨Ideal.Quotient.mk I x ^ n, ⟨n, rfl⟩⟩, ?_⟩
    simpa only [map_mul, map_pow] using (Ideal.Quotient.eq_zero_iff_mem.mpr hm)

/-- The chart quotient map is surjective, with denominators lifted by
their actual coordinate powers. -/
theorem localizedQuotientMap_surjective {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    Function.Surjective (localizedQuotientMap I x) := by
  let S := Localization.Away x
  let B := Localization.Away (Ideal.Quotient.mk I x)
  intro z
  obtain ⟨a, s, rfl⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers (Ideal.Quotient.mk I x)) z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨n, hn⟩ := s.property
  refine ⟨IsLocalization.mk' (M := Submonoid.powers x) S r ⟨x ^ n, ⟨n, rfl⟩⟩, ?_⟩
  rw [localizedQuotientMap, IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simpa only [map_pow] using hn

/-- A reduced principal cut in the localized coordinate quotient is
precisely a reduced literal sum ideal in the localized ambient ring. -/
theorem localized_sum_ideal_radical_of_quotient_cut {R : Type*} [CommRing R]
    (I : Ideal R) (x ℓ : R)
    (h : (Ideal.span {algebraMap (R ⧸ I)
      (Localization.Away (Ideal.Quotient.mk I x)) (Ideal.Quotient.mk I ℓ)}).IsRadical) :
    ((I ⊔ Ideal.span {ℓ}).map (algebraMap R (Localization.Away x))).IsRadical := by
  let S := Localization.Away x
  let B := Localization.Away (Ideal.Quotient.mk I x)
  let g := localizedQuotientMap I x
  let J : Ideal S := Ideal.span {algebraMap R S ℓ}
  have hmap : J.map g =
      Ideal.span {algebraMap (R ⧸ I) B (Ideal.Quotient.mk I ℓ)} := by
    simp only [J, Ideal.map_span, Set.image_singleton, g, localizedQuotientMap,
      IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have hc := h.comap g
  rw [← hmap, Ideal.comap_map_of_surjective g (localizedQuotientMap_surjective I x),
    ← RingHom.ker_eq_comap_bot, localizedQuotientMap_ker, sup_comm] at hc
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact hc

end
end DistinctDistances.TrackA
