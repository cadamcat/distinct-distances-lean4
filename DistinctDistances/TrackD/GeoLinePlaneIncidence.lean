import DistinctDistances.TrackD.GeoLinePlaneGeometry

/-! Transfer of the ambient paraboloid lift to the planar incidence bound. -/

namespace DistinctDistances.TrackD.GeoLinePlane
open scoped BigOperators Classical
open Finset
noncomputable section
variable {d : ℕ}

theorem lifted_incidence_bound (C : ℝ) (hC : 0 < C)
    (hST : ∀ (Q : Finset (Pt 2)) (L : Finset (AffineSubspace ℝ (Pt 2))),
      (∀ ℓ ∈ L, IsRealLine ℓ) →
      (((Q ×ˢ L).filter (fun x => x.1 ∈ x.2)).card : ℝ) ≤
        C * (((Q.card : ℝ) * L.card) ^ ((2 : ℝ)/3) + Q.card + L.card))
    (P Q : Finset (Pt d)) (H : AffineSubspace ℝ (Pt d)) (hH : IsRealPlane H)
    (hQP : Q ⊆ P) (hQH : ∀ x ∈ Q, x ∈ H)
    (a v : Pt d) (hv : v ≠ 0) (ha : a ∈ H) (hb : a+v ∈ H)
    (T : Finset ℝ) (hT : ∀ t ∈ T, a+t • v ∈ P) :
    (T.card : ℝ) * Q.card ≤
      2*C * ((((T.card : ℝ)*Q.card)*cfgM P)^((2 : ℝ)/3) + Q.card + T.card*cfgM P) := by
  let U := Q.image (lift a v)
  let L := (T ×ˢ distances P).image (fun tr => liftedLine tr.1 (tr.2^2-tr.1^2*‖v‖^2))
  let I := (U ×ˢ L).filter (fun zl => zl.1 ∈ zl.2)
  let f : ℝ × Pt d → Pt 2 × AffineSubspace ℝ (Pt 2) :=
    fun tq => (lift a v tq.2, liftedLine tq.1 (dist tq.2 (a+tq.1 • v)^2-tq.1^2*‖v‖^2))
  have hf : ∀ tq ∈ T ×ˢ Q, f tq ∈ I := by
    intro tq htq
    obtain ⟨ht, hq⟩ := mem_product.mp htq
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_image_of_mem _ hq, ?_⟩, lift_incidence a v tq.2 tq.1⟩
    exact mem_image.mpr ⟨(tq.1, dist tq.2 (a+tq.1 • v)),
      mem_product.mpr ⟨ht, mem_distances P (hQP hq) (hT tq.1 ht)⟩, rfl⟩
  have hcount : (T ×ˢ Q).card ≤ 2 * I.card := by
    apply card_le_mul_card_image_of_maps_to hf 2
    intro zl _
    let F := (T ×ˢ Q).filter (fun tq => f tq = zl)
    have hmap : Set.MapsTo Prod.snd (F : Set (ℝ × Pt d))
        (Q.filter (fun x => lift a v x = zl.1)) := by
      intro tq htq
      obtain ⟨htq, he⟩ := mem_filter.mp htq
      exact mem_filter.mpr ⟨(mem_product.mp htq).2, congrArg Prod.fst he⟩
    have hinj : (F : Set (ℝ × Pt d)).InjOn Prod.snd := by
      intro tq htq sq hsq he
      have htf := (mem_filter.mp htq).2
      have hsf := (mem_filter.mp hsq).2
      have hl := congrArg Prod.snd (htf.trans hsf.symm)
      have ht := (liftedLine_injective hl).1
      exact Prod.ext ht he
    exact (card_le_card_of_injOn Prod.snd hmap hinj).trans
      (lift_fiber Q H hH hQH a v ha hb hv zl.1)
  have hI := hST U L (by
    intro ℓ hℓ
    obtain ⟨tr, -, rfl⟩ := mem_image.mp hℓ
    exact liftedLine_line _ _)
  have hU : (U.card : ℝ) ≤ Q.card := by exact_mod_cast card_image_le
  have hL : (L.card : ℝ) ≤ T.card * cfgM P := by
    have hn : L.card ≤ T.card * (distances P).card := (card_image_le).trans_eq (card_product _ _)
    have hr : (L.card : ℝ) ≤ (T.card : ℝ) * (distances P).card := by exact_mod_cast hn
    simpa only [distances_card_real] using hr
  have hM : 0 ≤ cfgM P := by unfold cfgM; positivity
  have hI' : (I.card : ℝ) ≤
      C * ((((T.card : ℝ)*Q.card)*cfgM P)^((2 : ℝ)/3) + Q.card + T.card*cfgM P) := by
    calc
      (I.card : ℝ) ≤ C * (((U.card : ℝ)*L.card)^((2 : ℝ)/3)+U.card+L.card) := hI
      _ ≤ C * ((((T.card : ℝ)*Q.card)*cfgM P)^((2 : ℝ)/3)+Q.card+T.card*cfgM P) := by
        have hmul : (U.card : ℝ)*L.card ≤ ((T.card : ℝ)*Q.card)*cfgM P := by
          calc
            (U.card : ℝ)*L.card ≤ (Q.card : ℝ)*(T.card*cfgM P) := by gcongr
            _ = _ := by ring
        gcongr
  have hcount' : (T.card : ℝ)*Q.card ≤ 2*(I.card : ℝ) := by
    exact_mod_cast (by simpa only [card_product] using hcount)
  linarith

theorem occupancy_incidence (C : ℝ) (hC : 0 < C)
    (hST : ∀ (Q : Finset (Pt 2)) (L : Finset (AffineSubspace ℝ (Pt 2))),
      (∀ ℓ ∈ L, IsRealLine ℓ) →
      (((Q ×ˢ L).filter (fun x => x.1 ∈ x.2)).card : ℝ) ≤
        C * (((Q.card : ℝ) * L.card) ^ ((2 : ℝ)/3) + Q.card + L.card))
    (P : Finset (Pt d)) (ℓ H : AffineSubspace ℝ (Pt d))
    (hℓ : IsRealLine ℓ) (hH : IsRealPlane H) (hℓH : ℓ ≤ H) :
    (occ P ℓ : ℝ)*occ P H ≤
      2*C * ((((occ P ℓ : ℝ)*occ P H)*cfgM P)^((2 : ℝ)/3) + occ P H + occ P ℓ*cfgM P) := by
  obtain ⟨a, ha⟩ := line_nonempty ℓ hℓ
  obtain ⟨v, hv, hp⟩ := line_params ℓ hℓ a ha
  let A := P.filter (· ∈ ℓ)
  let Q := P.filter (· ∈ H)
  let tau : Pt d → ℝ := fun x => if hx : x ∈ ℓ then ((hp x).mp hx).choose else 0
  have htau : ∀ x ∈ A, x = a+tau x • v := by
    intro x hx
    have hxℓ := (mem_filter.mp hx).2
    simp only [tau, dif_pos hxℓ]
    exact ((hp x).mp hxℓ).choose_spec
  let T := A.image tau
  have hcard : T.card = A.card := card_image_of_injOn (by
    intro x hx y hy he
    rw [htau x hx, htau y hy, he])
  have hT : ∀ t ∈ T, a+t • v ∈ P := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
    rw [← htau x hx]
    exact (mem_filter.mp hx).1
  have hb : a+v ∈ H := hℓH ((hp _).mpr ⟨1, by simp⟩)
  have hi := lifted_incidence_bound C hC hST P Q H hH
    (filter_subset _ _) (fun x hx => (mem_filter.mp hx).2) a v hv (hℓH ha) hb T hT
  rw [hcard] at hi
  exact hi

end
end DistinctDistances.TrackD.GeoLinePlane
