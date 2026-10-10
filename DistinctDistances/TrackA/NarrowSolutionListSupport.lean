import DistinctDistances.TrackA.NarrowActualRootSupport
import DistinctDistances.TrackA.CylinderDegreeSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- The finite original center/root pairs give an equally large list of
literal cylinder points. Each point retains its original isolated center
and its unique carrier in the entire original family. -/
theorem narrow_parameter_solution_list {n l : ℕ} (J : AffineFamily.Family n)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l) (Y : AffineVariety n) (hY : Y ∈ J)
    (S : Finset (Point n)) (himage : ∀ p ∈ S, (radialImage p Y).dimension = l) :
    ∃ y ∈ Y.points, ∃ Q : Finset (Point (n+1)),
      Q.card = ∑ p ∈ S, (groupDepth p J Y - 1) ∧
      ∀ q ∈ Q, ∃ p ∈ S, ∃ V ∈ J, ∃ hpy : y ≠ p,
        Fin.tail q ∈ V.points ∧
        (radialFiber p V (radialProjection p y hpy)).Finite ∧
        (∀ W ∈ J, Fin.tail q ∈ W.points → W = V) ∧
        p = lineParameterPoint y q := by
  obtain ⟨y, hy, hgood⟩ := common_actual_radial_root_counts J hl hJ Y hY S himage
  let hpy (p : S) : y ≠ p.val := (hgood p.val p.property).choose
  let T (p : S) : Set (Point n) :=
    groupMovingFiber J p.val Y (radialProjection p.val y (hpy p)) y
  have hfinite (p : S) : (T p).Finite := (hgood p.val p.property).choose_spec.1
  letI (p : S) : Fintype (T p) := (hfinite p).fintype
  let U := (p : S) × T p
  have hparam : ∀ u : U, ∃ t : ℂ, u.1.val = y + t • (u.2.val-y) := by
    intro u
    obtain ⟨V, hV, hx, hf, hu, t, ht, htu⟩ :=
      (hgood u.1.val u.1.property).choose_spec.2.2 u.2.val u.2.property
    exact ⟨t, ht⟩
  choose τ hτ using hparam
  let q (u : U) : Point (n+1) := Fin.cons (τ u) u.2.val
  have htail (u : U) : Fin.tail (q u) = u.2.val := Fin.tail_cons _ _
  have hmap (u : U) : lineParameterPoint y (q u) = u.1.val := by
    simpa only [lineParameterPoint, q, Fin.cons_zero, Fin.tail_cons] using (hτ u).symm
  have hinj : Function.Injective q := by
    intro a b he
    have hp : a.1 = b.1 := Subtype.ext
      ((hmap a).symm.trans ((congrArg (lineParameterPoint y) he).trans (hmap b)))
    have hx : a.2.val = b.2.val :=
      (htail a).symm.trans ((congrArg Fin.tail he).trans (htail b))
    cases a with
    | mk p x =>
      cases b with
      | mk r z =>
        cases hp
        exact congrArg (Sigma.mk p) (Subtype.ext hx)
  let Q := Finset.univ.image q
  refine ⟨y, hy, Q, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_sigma]
    calc
      (∑ p : S, Fintype.card (T p)) = ∑ p : S, (groupDepth p.val J Y - 1) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Set.fintypeCard_eq_ncard]
        exact (hgood p.val p.property).choose_spec.2.1
      _ = ∑ p ∈ S, (groupDepth p J Y - 1) :=
        Finset.sum_coe_sort S (fun p => groupDepth p J Y - 1)
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨V, hV, hx, hf, huniq, hparameter⟩ :=
      (hgood u.1.val u.1.property).choose_spec.2.2 u.2.val u.2.property
    refine ⟨u.1.val, u.1.property, V, hV, hpy u.1, ?_, hf, ?_, (hmap u).symm⟩
    · rw [htail]
      exact hx.1
    · simpa only [htail] using huniq

end
end DistinctDistances.TrackA
