import DistinctDistances.TrackD.RationalImages
import OAI.NumberTheory.PiExponent.Polynomials.Homogenization

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

theorem homogeneous_eval_scaled {σ : Type*} (q : MvPolynomial σ ℂ) (D : ℕ)
    (hq : q.IsHomogeneous D) (c : ℂ) (y : σ → ℂ) :
    MvPolynomial.eval (fun i => c * y i) q = c^D * MvPolynomial.eval y q := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdeg : D = ∑ i ∈ e.support, e i := hq.degree_eq_sum_deg_support he
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hdeg]
  ring

def rationalNumerator {n m : ℕ} (f : Fin m → Poly n) (g : Poly n) (q : Poly m) : Poly n :=
  MvPolynomial.aeval (fun o : Option (Fin m) => o.elim g f) (OAI.PiExponentJets.W22.homogenize q)

theorem eval_polynomial_substitution {n : ℕ} {σ : Type*}
    (f : σ → Poly n) (x : Point n) (q : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval f q) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (f i)) q := by
  change (MvPolynomial.aeval x) (MvPolynomial.aeval f q) = _
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem homogenize_eval_one {m : ℕ} (q : Poly m) (y : Point m) :
    MvPolynomial.eval (fun o : Option (Fin m) => o.elim 1 y)
      (OAI.PiExponentJets.W22.homogenize q) = MvPolynomial.eval y q := by
  have h := congrArg (MvPolynomial.eval y) (OAI.PiExponentJets.W22.dehomogenize_homogenize q)
  have heval : ∀ Q : MvPolynomial (Option (Fin m)) ℂ,
      MvPolynomial.eval y (OAI.PiExponentJets.W22.dehomogenize Q) =
        MvPolynomial.eval (fun o : Option (Fin m) => o.elim 1 y) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => simp [OAI.PiExponentJets.W22.dehomogenize]
    | add p q hp hq => simp_all [OAI.PiExponentJets.W22.dehomogenize]
    | mul_X p i hp =>
      cases i <;> simp_all [OAI.PiExponentJets.W22.dehomogenize]
  rwa [heval] at h

theorem rationalNumerator_eval {n m : ℕ} (f : Fin m → Poly n) (g : Poly n)
    (q : Poly m) (x : Point n) (hg : MvPolynomial.eval x g ≠ 0) :
    MvPolynomial.eval x (rationalNumerator f g q) =
      (MvPolynomial.eval x g)^q.totalDegree * MvPolynomial.eval (rationalPoint f g x) q := by
  rw [rationalNumerator, eval_polynomial_substitution]
  have hcoords : (fun o : Option (Fin m) => MvPolynomial.eval x (o.elim g f)) =
      (fun o : Option (Fin m) => MvPolynomial.eval x g * o.elim 1 (rationalPoint f g x)) := by
    funext o
    cases o with
    | none => simp
    | some i =>
      change MvPolynomial.eval x (f i) = MvPolynomial.eval x g *
        (MvPolynomial.eval x (f i) / MvPolynomial.eval x g)
      field_simp [hg]
  rw [hcoords, homogeneous_eval_scaled _ _ (OAI.PiExponentJets.W22.homogenize_isHomogeneous q),
    homogenize_eval_one]

/-- Generic closed containment extends to the actual rational-image closure,
using OAI homogenization to clear the denominator before generic extension. -/
theorem rational_image_generic_subset {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (f : Fin m → Poly n) (g : Poly n) (W : AffineVariety m)
    (h : ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0 ∧ rationalPoint f g x ∈ W)) :
    (rationalImage X f g).Subvariety W := by
  intro q hq
  have hgeneric : ForGeneralPoint X (fun x => MvPolynomial.eval x (rationalNumerator f g q) = 0) := by
    apply h.mono
    intro x hx hh
    rw [rationalNumerator_eval f g q x hh.1]
    have hz : MvPolynomial.eval (rationalPoint f g x) q = 0 := hh.2 q hq
    rw [hz, mul_zero]
  have hall := ForGeneralPoint.eval_zero hX (rationalNumerator f g q) hgeneric
  intro y hy
  obtain ⟨x, hx, hg, rfl⟩ := hy
  have hz := hall x hx
  rw [rationalNumerator_eval f g q x hg] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hg)

theorem rational_image_nonzero_open {n m : ℕ}
    (X : AffineVariety n) (f : Fin m → Poly n) (g : Poly n) (q : Poly m)
    (hq : q ∉ (rationalImage X f g).ideal) :
    ForGeneralPoint X (fun x => MvPolynomial.eval x g ≠ 0 ∧
      MvPolynomial.eval (rationalPoint f g x) q ≠ 0) := by
  have hex : ∃ x ∈ X, MvPolynomial.eval x g ≠ 0 ∧
      MvPolynomial.eval (rationalPoint f g x) q ≠ 0 := by
    by_contra h
    apply hq
    intro y hy
    obtain ⟨x, hx, hg, rfl⟩ := hy
    by_contra hqx
    exact h ⟨x, hx, hg, hqx⟩
  obtain ⟨x, hx, hg, hqx⟩ := hex
  refine ⟨g * rationalNumerator f g q, ⟨x, hx, ?_⟩, ?_⟩
  · rw [map_mul, rationalNumerator_eval f g q x hg]
    exact mul_ne_zero hg (mul_ne_zero (pow_ne_zero _ hg) hqx)
  · intro z hz hprod
    rw [map_mul, mul_ne_zero_iff] at hprod
    have hnum := hprod.2
    rw [rationalNumerator_eval f g q z hprod.1, mul_ne_zero_iff] at hnum
    exact ⟨hprod.1, hnum.2⟩

/-- A nonempty rational image of an irreducible carrier is irreducible.
Principal opens are pulled back by cleared numerators before intersecting. -/
theorem rational_image_irreducible {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (f : Fin m → Poly n) (g : Poly n) (hg : g ∉ X.ideal) :
    (rationalImage X f g).IsIrreducible := by
  apply Ideal.isPrime_iff.mpr
  constructor
  · have hex : ∃ x ∈ X, MvPolynomial.eval x g ≠ 0 := by
      by_contra h
      push Not at h
      exact hg ((mem_ideal_iff_eval_zero X g).mpr h)
    obtain ⟨x, hx, hgx⟩ := hex
    intro htop
    have hone : (1 : Poly m) ∈ (rationalImage X f g).ideal := by rw [htop]; trivial
    have hz := hone (rationalPoint f g x) ⟨x, hx, hgx, rfl⟩
    simpa using hz
  · intro p q hpq
    by_contra h
    push Not at h
    have hp := rational_image_nonzero_open X f g p h.1
    have hq := rational_image_nonzero_open X f g q h.2
    obtain ⟨x, hx, ⟨hgx, hpx⟩, ⟨_, hqx⟩⟩ := (hp.and hX hq).exists
    have hz := hpq (rationalPoint f g x) ⟨x, hx, hgx, rfl⟩
    rw [map_mul] at hz
    exact (mul_ne_zero hpx hqx) hz

end
end DistinctDistances.TrackD
