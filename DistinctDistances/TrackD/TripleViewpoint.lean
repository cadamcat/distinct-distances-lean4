import DistinctDistances.TrackD.SecantsSpan
import DistinctDistances.TrackD.PerspectiveCentersGeometry

/-! Generic-viewpoint direction separation, `secants.tex:433–437`.
The point set is assumed contained in no affine line; no degree or
multiplicity input is used by these genericity/incidence arguments. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

variable {d : ℕ}

theorem ForGeneralPoint.avoid_flat {X : AffineVariety d}
    (F : AffineSubspace ℂ (Point d)) (hproper : ¬ X.points ⊆ F) :
    ForGeneralPoint X (fun v => v ∉ F) := by
  obtain ⟨a, ha, haF⟩ := Set.not_subset.mp hproper
  by_cases hF : (F : Set (Point d)).Nonempty
  · obtain ⟨b, hb⟩ := hF
    have hab : a - b ∉ F.direction := by
      intro h
      exact haF ((AffineSubspace.vsub_right_mem_direction_iff_mem hb a).mp h)
    obtain ⟨lam, hlam, hmap⟩ := F.direction.exists_dual_map_eq_bot_of_notMem hab inferInstance
    refine ⟨covectorPoly lam b, ⟨a, ha, ?_⟩, ?_⟩
    · rw [eval_covectorPoly]
      exact hlam
    · intro v hv hpoly hvF
      have hvmem : lam (v - b) ∈ F.direction.map lam :=
        Submodule.mem_map.mpr ⟨v - b, AffineSubspace.vsub_mem_direction hvF hb, rfl⟩
      have hzero : lam (v - b) = 0 := by simpa [hmap] using hvmem
      exact hpoly (by rw [eval_covectorPoly]; exact hzero)
  · have hempty : (F : Set (Point d)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    refine ⟨1, ⟨a, ha, by simp⟩, ?_⟩
    intro v hv hpoly hvF
    change v ∈ (F : Set (Point d)) at hvF
    rw [hempty] at hvF
    simpa using hvF

theorem ForGeneralPoint.finset_all {ι : Type*} {X : AffineVariety d}
    (hX : X.IsIrreducible) (hne : X.points.Nonempty) (I : Finset ι)
    (Q : ι → Point d → Prop) (hI : ∀ i ∈ I, ForGeneralPoint X (Q i)) :
    ForGeneralPoint X (fun v => ∀ i ∈ I, Q i v) := by
  classical
  revert hI
  induction I using Finset.induction_on with
  | empty =>
      intro hI
      obtain ⟨v, hv⟩ := hne
      exact ⟨1, ⟨v, hv, by simp⟩, by simp⟩
  | @insert i I hi ih =>
      intro hI
      have hhead := hI i (Finset.mem_insert_self i I)
      have htail := ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))
      apply (hhead.and hX htail).mono
      intro v hv h j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact h.1
      · exact h.2 j hj

/-- Equal directions from an exterior point force that point onto the joining
line of the two distinct endpoints. -/
theorem equal_radial_directions_center_on_line
    (v p q : Point d) (hp : p ≠ v) (hq : q ≠ v) (hpq : p ≠ q)
    (heq : radialProjection v p hp = radialProjection v q hq) :
    v ∈ affineSpan ℂ {p, q} := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ (p - v) (q - v)
    (sub_ne_zero.mpr hp) (sub_ne_zero.mpr hq)).mp heq
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, one_smul] at ha
    have hqp : q = p := by
      have h := congrArg (fun w : Point d => w + v) ha
      simpa using h
    exact hpq hqp.symm
  have hden : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hform : (-((a - 1)⁻¹)) • (p - q) + q = v := by
    ext i
    have h := congrFun ha i
    change a * (q i - v i) = p i - v i at h
    change -((a - 1)⁻¹) * (p i - q i) + q i = v i
    field_simp [hden]
    linear_combination h
  have hmem := (affineSpan ℂ {p, q}).smul_vsub_vadd_mem' (-((a - 1)⁻¹))
    (left_mem_affineSpan_pair ℂ p q) (right_mem_affineSpan_pair ℂ p q)
    (right_mem_affineSpan_pair ℂ p q)
  have hmem' : (-((a - 1)⁻¹)) • (p - q) + q ∈ affineSpan ℂ {p, q} := hmem
  rw [hform] at hmem'
  exact hmem'

/-- One general source point separates all directions of an arbitrary finite
centre list simultaneously. Its principal open may depend on the list, while
the final triple-centre constant is independent of that choice. -/
theorem general_viewpoint_centers_separated (X : AffineVariety 3)
    (hX : X.IsIrreducible) (hne : X.points.Nonempty)
    (hproper : ∀ L : AffineSubspace ℂ (Point 3), Module.finrank ℂ L.direction = 1 →
      ¬ X.points ⊆ L) (Pc : Finset (Point 3)) :
    ForGeneralPoint X (fun v =>
      (∀ p ∈ Pc, v ≠ p) ∧ ∀ p ∈ Pc, ∀ q ∈ Pc, p ≠ q →
        ∀ (hp : p ≠ v) (hq : q ≠ v), radialProjection v p hp ≠ radialProjection v q hq) := by
  let u : Point 3 := Pi.single (0 : Fin 3) 1
  have hu : u ≠ 0 := by
    intro h
    have hi := congrFun h (0 : Fin 3)
    simpa [u] using hi
  let axis (p : Point 3) : AffineSubspace ℂ (Point 3) := AffineSubspace.mk' p (ℂ ∙ u)
  have haxis : ∀ p, Module.finrank ℂ (axis p).direction = 1 := by
    intro p
    rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton hu
  have hpoints := ForGeneralPoint.finset_all hX hne Pc
    (fun p v => v ∉ axis p) (fun p hp => ForGeneralPoint.avoid_flat (axis p) (hproper _ (haxis p)))
  let pairs := (Pc ×ˢ Pc).filter (fun pq => pq.1 ≠ pq.2)
  have hpair := ForGeneralPoint.finset_all hX hne pairs
    (fun pq v => v ∉ affineSpan ℂ {pq.1, pq.2}) (by
      intro pq hpq
      apply ForGeneralPoint.avoid_flat
      exact hproper _ (complex_pair_line_dimension pq.1 pq.2 (Finset.mem_filter.mp hpq).2))
  apply (hpoints.and hX hpair).mono
  intro v hv h
  constructor
  · intro p hp hEq
    subst v
    exact h.1 p hp (AffineSubspace.self_mem_mk' _ _)
  · intro p hp q hq hpq hpv hqv heq
    have hmem : (p, q) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq⟩
    exact h.2 (p, q) hmem (equal_radial_directions_center_on_line v p q hpv hqv hpq heq)

end
end DistinctDistances.TrackD
