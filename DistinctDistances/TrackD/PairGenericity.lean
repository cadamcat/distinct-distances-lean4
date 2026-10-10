import DistinctDistances.TrackD.Genericity

namespace DistinctDistances.TrackD

noncomputable section
variable {d : ℕ}

theorem ForGeneralPair.exists {X Y : AffineVariety d}
    {Q : Point d → Point d → Prop} (h : ForGeneralPair X Y Q) :
    ∃ x ∈ X, ∃ y ∈ Y, Q x y := by
  obtain ⟨g, ⟨x, hx, y, hy, hg⟩, hQ⟩ := h
  exact ⟨x, hx, y, hy, hQ x hx y hy hg⟩

theorem ForGeneralPair.mono {X Y : AffineVariety d}
    {Q R : Point d → Point d → Prop} (h : ForGeneralPair X Y Q)
    (hQR : ∀ x ∈ X, ∀ y ∈ Y, Q x y → R x y) : ForGeneralPair X Y R := by
  obtain ⟨g, hg, hQ⟩ := h
  exact ⟨g, hg, fun x hx y hy hn => hQR x hx y hy (hQ x hx y hy hn)⟩

/-- Combine generic pair conditions by intersecting generic fibers, so no
separate product-variety irreducibility interface is needed. -/
theorem ForGeneralPair.and {X Y : AffineVariety d}
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    {Q R : Point d → Point d → Prop}
    (hQ : ForGeneralPair X Y Q) (hR : ForGeneralPair X Y R) :
    ForGeneralPair X Y (fun x y => Q x y ∧ R x y) := by
  obtain ⟨f, hf, hQ⟩ := hQ
  obtain ⟨g, hg, hR⟩ := hR
  have hfgen : ForGeneralPair X Y (fun x y => MvPolynomial.eval (pairPt x y) f ≠ 0) :=
    ⟨f, hf, fun _ _ _ _ hn => hn⟩
  have hggen : ForGeneralPair X Y (fun x y => MvPolynomial.eval (pairPt x y) g ≠ 0) :=
    ⟨g, hg, fun _ _ _ _ hn => hn⟩
  obtain ⟨y, hy, hfy, hgy⟩ :=
    (hfgen.fiber_right.and hY hggen.fiber_right).exists
  obtain ⟨x, hx, hfx, hgx⟩ := (hfy.and hX hgy).exists
  refine ⟨f * g, ⟨x, hx, y, hy, ?_⟩, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hfx hgx
  · intro x hx y hy hn
    rw [map_mul, mul_ne_zero_iff] at hn
    exact ⟨hQ x hx y hy hn.1, hR x hx y hy hn.2⟩

theorem ForGeneralPoint.on_left {X Y : AffineVariety d}
    {Q : Point d → Prop} (h : ForGeneralPoint X Q) (hY : Y.points.Nonempty) :
    ForGeneralPair X Y (fun x _ => Q x) := by
  obtain ⟨f, ⟨x, hx, hfx⟩, hQ⟩ := h
  obtain ⟨y, hy⟩ := hY
  refine ⟨MvPolynomial.rename Sum.inl f, ⟨x, hx, y, hy, ?_⟩, ?_⟩
  · simpa [MvPolynomial.eval_rename, pairPt, Function.comp_def] using hfx
  · intro x hx y hy hn
    apply hQ x hx
    simpa [MvPolynomial.eval_rename, pairPt, Function.comp_def] using hn

theorem ForGeneralPoint.on_right {X Y : AffineVariety d}
    {Q : Point d → Prop} (h : ForGeneralPoint Y Q) (hX : X.points.Nonempty) :
    ForGeneralPair X Y (fun _ y => Q y) := by
  exact (h.on_left hX).swap

end
end DistinctDistances.TrackD
