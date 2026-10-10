import DistinctDistances.TrackA.NarrowSolutionListSupport
import DistinctDistances.TrackA.Intersections

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- Count the original literal parameter solutions on each original carrier
with the frozen relative isolated-point Bezout bound, then sum. -/
theorem narrow_root_count_dimensional {n l : ℕ} (J : AffineFamily.Family n)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l) (Y : AffineVariety n) (hY : Y ∈ J)
    (S : Finset (Point n)) (E : Set (Poly n)) (L : ℕ) (hL : 1 ≤ L)
    (hE : ∀ f ∈ E, f.totalDegree ≤ L) (hS : IsolatedPoints E S)
    (himage : ∀ p ∈ S, (radialImage p Y).dimension = l) :
    (∑ p ∈ S, ((groupDepth p J Y - 1 : ℕ) : ℚ)) ≤
      (l+1 : ℕ) * AffineFamily.degree J * (2*L : ℕ)^(l+1) := by
  obtain ⟨y, hy, Q, hcard, hgood⟩ := narrow_parameter_solution_list J hl hJ Y hY S himage
  let R (V : AffineVariety n) :=
    Q.filter (fun (q : Point (n+1)) => Fin.tail q ∈ V.points)
  let φ := polynomialPointPullback (lineParameterCoordinate y)
  let E' : Set (Poly (n+1)) := φ.toRingHom '' E
  have hE' : ∀ f ∈ E', f.totalDegree ≤ 2*L := by
    rintro f ⟨g, hg, rfl⟩
    exact (lineParameter_pullback_degree y g).trans (Nat.mul_le_mul_left 2 (hE g hg))
  have hbound : ∀ V ∈ J,
      ((R V).card : ℚ) ≤ (l+1 : ℕ) * V.degree * (2*L : ℕ)^(l+1) := by
    intro V hV
    have hpure : (lineCylinder V).IsPure (l+1) := by
      rw [← (hJ V hV).2]
      exact lineCylinder_pure V (hJ V hV).1
    have hisolated : ∀ q ∈ R V,
        pointIdeal q ∈ ((lineCylinder V).ideal ⊔ Ideal.span E').minimalPrimes := by
      intro q hq
      obtain ⟨hqQ, hqV⟩ := Finset.mem_filter.mp hq
      obtain ⟨p, hp, W, hW, hpy, hxW, hfinite, huniq, hmap⟩ := hgood q hqQ
      have hVW : V = W := huniq V hV hqV
      have hfV : (radialFiber p V (radialProjection p y hpy)).Finite := by
        rwa [hVW]
      have ht : p = y + q 0 • (Fin.tail q-y) := hmap
      have h := lineCylinder_isolated_parameter V (Ideal.span E) p y (Fin.tail q)
        hpy hqV (q 0) ht (hS p hp) hfV
      simpa only [Fin.cons_self_tail, Ideal.map_span, φ, E'] using h
    have hbez := fa_bezout_relative_points (lineCylinder V) (l+1) hpure E'
      (2*L) (by omega) hE' (R V) hisolated
    have hdegree := lineCylinder_degree_le V (hJ V hV).1
    rw [(hJ V hV).2] at hdegree
    exact hbez.trans (mul_le_mul_of_nonneg_right hdegree (pow_nonneg (Nat.cast_nonneg _) _))
  have hcover : Q ⊆ J.biUnion R := by
    intro q hq
    obtain ⟨p, hp, V, hV, hpy, hxV, hf, hu, hm⟩ := hgood q hq
    exact Finset.mem_biUnion.mpr ⟨V, hV, Finset.mem_filter.mpr ⟨hq, hxV⟩⟩
  have hcount : Q.card ≤ ∑ V ∈ J, (R V).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  calc
    (∑ p ∈ S, ((groupDepth p J Y - 1 : ℕ) : ℚ)) = (Q.card : ℚ) := by
      exact_mod_cast hcard.symm
    _ ≤ ∑ V ∈ J, ((R V).card : ℚ) := by exact_mod_cast hcount
    _ ≤ ∑ V ∈ J, (l+1 : ℕ) * V.degree * (2*L : ℕ)^(l+1) :=
      Finset.sum_le_sum hbound
    _ = (l+1 : ℕ) * AffineFamily.degree J * (2*L : ℕ)^(l+1) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rfl

end
end DistinctDistances.TrackA
