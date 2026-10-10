import DistinctDistances.TrackD.Basic

namespace DistinctDistances.TrackD

open scoped Classical
noncomputable section

variable {d : ℕ}

theorem mem_ideal_iff_eval_zero (X : AffineVariety d) (f : Poly d) :
    f ∈ X.ideal ↔ ∀ x ∈ X, MvPolynomial.eval x f = 0 := by
  rw [← X.vanishingIdeal_points]
  rfl

theorem exists_eval_mul_ne_zero (X : AffineVariety d) (hX : X.IsIrreducible)
    (f g : Poly d) (hf : ∃ x ∈ X, MvPolynomial.eval x f ≠ 0)
    (hg : ∃ x ∈ X, MvPolynomial.eval x g ≠ 0) :
    ∃ x ∈ X, MvPolynomial.eval x (f * g) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hfg := (mem_ideal_iff_eval_zero X (f * g)).mpr hn
  rcases hX.mem_or_mem hfg with hf' | hg'
  · obtain ⟨x, hx, hfx⟩ := hf
    exact hfx ((mem_ideal_iff_eval_zero X f).mp hf' x hx)
  · obtain ⟨x, hx, hgx⟩ := hg
    exact hgx ((mem_ideal_iff_eval_zero X g).mp hg' x hx)

theorem ForGeneralPoint.exists {X : AffineVariety d} {Q : Point d → Prop}
    (h : ForGeneralPoint X Q) : ∃ x ∈ X, Q x := by
  obtain ⟨g, ⟨x, hx, hg⟩, hQ⟩ := h
  exact ⟨x, hx, hQ x hx hg⟩

theorem ForGeneralPoint.mono {X : AffineVariety d} {Q R : Point d → Prop}
    (h : ForGeneralPoint X Q) (hQR : ∀ x ∈ X, Q x → R x) : ForGeneralPoint X R := by
  obtain ⟨g, hg, hQ⟩ := h
  exact ⟨g, hg, fun x hx hn => hQR x hx (hQ x hx hn)⟩

theorem ForGeneralPoint.and {X : AffineVariety d} (hX : X.IsIrreducible)
    {Q R : Point d → Prop} (hQ : ForGeneralPoint X Q) (hR : ForGeneralPoint X R) :
    ForGeneralPoint X (fun x => Q x ∧ R x) := by
  obtain ⟨f, hf, hQ⟩ := hQ
  obtain ⟨g, hg, hR⟩ := hR
  refine ⟨f * g, exists_eval_mul_ne_zero X hX f g hf hg, ?_⟩
  intro x hx hn
  rw [map_mul, mul_ne_zero_iff] at hn
  exact ⟨hQ x hx hn.1, hR x hx hn.2⟩

/-- A polynomial identity on a nonempty principal open extends across an irreducible carrier. -/
theorem ForGeneralPoint.eval_zero {X : AffineVariety d} (hX : X.IsIrreducible)
    (f : Poly d) (h : ForGeneralPoint X (fun x => MvPolynomial.eval x f = 0)) :
    ∀ x ∈ X, MvPolynomial.eval x f = 0 := by
  obtain ⟨g, hg, h⟩ := h
  have hgf : g * f ∈ X.ideal := (mem_ideal_iff_eval_zero X _).mpr (by
    intro x hx
    rw [map_mul]
    by_cases hn : MvPolynomial.eval x g = 0
    · rw [hn, zero_mul]
    · rw [h x hx hn, mul_zero])
  rcases hX.mem_or_mem hgf with hg' | hf
  · obtain ⟨x, hx, hn⟩ := hg
    exact False.elim (hn ((mem_ideal_iff_eval_zero X g).mp hg' x hx))
  · exact (mem_ideal_iff_eval_zero X f).mp hf

def pairFixRight (g : PairPoly d) (y : Point d) : Poly d :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (y i))) g

def pairFixLeft (g : PairPoly d) (x : Point d) : Poly d :=
  MvPolynomial.aeval (Sum.elim (fun i => MvPolynomial.C (x i)) MvPolynomial.X) g

@[simp] theorem eval_pairFixRight (g : PairPoly d) (x y : Point d) :
    MvPolynomial.eval x (pairFixRight g y) = MvPolynomial.eval (pairPt x y) g := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [pairFixRight]
  | add f g hf hg => simp_all [pairFixRight]
  | mul_X f i hf => cases i <;> simp_all [pairFixRight, pairPt]

@[simp] theorem eval_pairFixLeft (g : PairPoly d) (x y : Point d) :
    MvPolynomial.eval y (pairFixLeft g x) = MvPolynomial.eval (pairPt x y) g := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [pairFixLeft]
  | add f g hf hg => simp_all [pairFixLeft]
  | mul_X f i hf => cases i <;> simp_all [pairFixLeft, pairPt]

/-- The target points with a nonempty generic source fiber themselves form a principal open. -/
theorem ForGeneralPair.fiber_right {X Y : AffineVariety d}
    {Q : Point d → Point d → Prop} (h : ForGeneralPair X Y Q) :
    ForGeneralPoint Y (fun y => ForGeneralPoint X (fun x => Q x y)) := by
  obtain ⟨g, ⟨x₀, hx₀, y₀, hy₀, hg₀⟩, hQ⟩ := h
  refine ⟨pairFixLeft g x₀, ⟨y₀, hy₀, by simpa using hg₀⟩, ?_⟩
  intro y hy hn
  refine ⟨pairFixRight g y, ⟨x₀, hx₀, ?_⟩, ?_⟩
  · simpa using hn
  · intro x hx hn'
    exact hQ x hx y hy (by simpa using hn')

theorem ForGeneralPair.swap {X Y : AffineVariety d}
    {Q : Point d → Point d → Prop} (h : ForGeneralPair X Y Q) :
    ForGeneralPair Y X (fun y x => Q x y) := by
  obtain ⟨g, ⟨x₀, hx₀, y₀, hy₀, hg₀⟩, hQ⟩ := h
  have heval : ∀ x y : Point d,
      MvPolynomial.eval (pairPt y x) (MvPolynomial.rename Sum.swap g) =
        MvPolynomial.eval (pairPt x y) g := by
    intro x y
    rw [MvPolynomial.eval_rename]
    have hp : pairPt y x ∘ Sum.swap = pairPt x y := by
      funext i
      cases i <;> rfl
    rw [hp]
  refine ⟨MvPolynomial.rename Sum.swap g, ⟨y₀, hy₀, x₀, hx₀, ?_⟩, ?_⟩
  · simpa only [heval] using hg₀
  · intro y hy x hx hn
    exact hQ x hx y hy (by simpa only [heval] using hn)

end
end DistinctDistances.TrackD
