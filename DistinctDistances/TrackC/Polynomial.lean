import DistinctDistances.TrackC.Basic
import DistinctDistances.TrackC.ZeroVolume
import DistinctDistances.TrackC.FlatFactorObstruction
import DistinctDistances.TrackC.FlatLineCount
import DistinctDistances.TrackC.BisectionPolynomial
import DistinctDistances.TrackC.PartitionTheorem
import DistinctDistances.OAIInterface.Borsuk
import DistinctDistances.TrackC.CPolynomialAux
import DistinctDistances.Bridges.RealCommonLines

open scoped BigOperators
open Classical

namespace DistinctDistances.TrackC

/-- CI:10–12, 115–116; a wrapper, not a reproof of the OAI sphere theorem. -/
theorem borsuk_ulam_zero (q : ℕ) (f : E (q + 1) → E q)
    (hc : ContinuousOn f {x | ‖x‖ = 1})
    (ho : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    ∃ x, ‖x‖ = 1 ∧ f x = 0 := by
  classical
  by_cases hq0 : q = 0
  · subst q
    let x : E 1 := EuclideanSpace.single ⟨0, by omega⟩ 1
    have hx : ‖x‖ = 1 := by simp [x]
    exact ⟨x, hx, Subsingleton.elim _ _⟩
  · have hqpos : 0 < q := by omega
    by_contra h
    have hnonzero : ∀ x, ‖x‖ = 1 → f x ≠ 0 := by
      intro x hx hfx
      apply h
      exact ⟨x, hx, hfx⟩
    let sphere : Set (E (q + 1)) := {x | ‖x‖ = 1}
    let radial : E (q + 1) → E q := fun x =>
      OAI.BorsukNine.SimplicialChains.unitRadial (f x)
    have himage_nonzero : ∀ y ∈ f '' sphere, y ≠ 0 := by
      rintro y ⟨x, hx, rfl⟩
      exact hnonzero x hx
    have hmaps : Set.MapsTo f sphere (f '' sphere) := by
      intro x hx
      exact ⟨x, hx, rfl⟩
    have hradial_cont : ContinuousOn
        OAI.BorsukNine.SimplicialChains.unitRadial (f '' sphere) :=
      OAI.BorsukNine.SimplicialChains.unitRadial_continuousOn himage_nonzero
    have hcont : ContinuousOn radial sphere := by
      change ContinuousOn
        (OAI.BorsukNine.SimplicialChains.unitRadial ∘ f) sphere
      exact hradial_cont.comp hc hmaps
    have hnorm : ∀ x, ‖x‖ = 1 → ‖radial x‖ = 1 := by
      intro x hx
      exact OAI.BorsukNine.SimplicialChains.unitRadial_norm (hnonzero x hx)
    have hodd : ∀ x, ‖x‖ = 1 → radial (-x) = -radial x := by
      intro x hx
      change OAI.BorsukNine.SimplicialChains.unitRadial (f (-x)) =
        -OAI.BorsukNine.SimplicialChains.unitRadial (f x)
      rw [ho x hx, OAI.BorsukNine.SimplicialChains.unitRadial_neg]
    have hdim := OAI.BorsukNine.SimplicialChains.odd_sphere_dimension_bound
      (q + 1) q (by omega) radial hcont hnorm hodd
    omega

/-- CI:113–115, Fubini induction. -/
theorem polynomial_zero_volume (d : ℕ) (f : Poly d) (hf : f ≠ 0) :
    MeasureTheory.volume (zeroSet f) = 0 := by
  exact polynomial_euclidean_zero_volume d f hf

/-- Simultaneous finite bisection, CI:109–127. -/
theorem finite_polynomial_bisection (d : ℕ) (S : Finset (Finset (E d))) (D : ℕ)
    (hD : S.card < Nat.choose (D + d) d) :
    ∃ f : Poly d, f ≠ 0 ∧ f.totalDegree ≤ D ∧
      ∀ X ∈ S,
        ((X.filter (fun x => 0 < evalR f x)).card : ℝ) ≤ (X.card : ℝ) / 2 ∧
        ((X.filter (fun x => evalR f x < 0)).card : ℝ) ≤ (X.card : ℝ) / 2 := by
  exact polynomial_bisection_construct d S D hD

/-- A strict sign class of the factors used in iterated bisection. -/
def signCell {d : ℕ} (fs : List (Poly d)) (σ : Fin fs.length → Bool) : Set (E d) :=
  {x | ∀ i : Fin fs.length,
    if σ i then 0 < evalR (fs.get i) x else evalR (fs.get i) x < 0}

/-- Dimension-parametric sign partition; CI:109–139, also consumed in dimension 2
by the replacement point-circle and Szemerédi--Trotter proofs. -/
theorem ci_partition_dim (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset (E d)) (r : ℕ), 1 ≤ r →
      ∃ (fs : List (Poly d)) (cells : Finset (Set (E d))),
        fs.prod ≠ 0 ∧ (fs.prod.totalDegree : ℝ) ≤ C * r ∧
        (cells.card : ℝ) ≤ C * (r : ℝ) ^ d ∧
        (∀ R ∈ cells, (∃ σ, R = signCell fs σ) ∧ IsOpen R ∧
          ((pointsIn S R).card : ℝ) ≤ C * S.card / (r : ℝ) ^ d) ∧
        (∀ R ∈ cells, ∀ R' ∈ cells, R ≠ R' → Disjoint R R') ∧
        (⋃ R ∈ cells, R) = (zeroSet fs.prod)ᶜ ∧
        (∀ l : Line d, ¬ onPolynomial fs.prod l →
          (cells.filter (fun R => (R ∩ (l.1 : Set (E d))).Nonempty)).card ≤
            fs.prod.totalDegree + 1) := by
  simpa only [signCell, factorSignCell] using partition_dimension_construct d hd

/-- ci:partition, CI:102–139. Open sign cells may be disconnected. -/
theorem ci_partition : ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset (E 3)) (r : ℕ), 1 ≤ r →
      ∃ (f : Poly 3) (cells : Finset (Set (E 3))),
        f ≠ 0 ∧ (f.totalDegree : ℝ) ≤ C * r ∧
        (cells.card : ℝ) ≤ C * (r : ℝ) ^ 3 ∧
        (∀ R ∈ cells, IsOpen R ∧ ((pointsIn S R).card : ℝ) ≤
          C * S.card / (r : ℝ) ^ 3) ∧
        (∀ R ∈ cells, ∀ R' ∈ cells, R ≠ R' → Disjoint R R') ∧
        (⋃ R ∈ cells, R) = (zeroSet f)ᶜ ∧
        (∀ l : Line 3, ¬ onPolynomial f l →
          (cells.filter (fun R => (R ∩ (l.1 : Set (E 3))).Nonempty)).card ≤
            f.totalDegree + 1) := by
  obtain ⟨C, hC, hdim⟩ := ci_partition_dim 3 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro S r hr
  obtain ⟨fs, cells, hfs, hdeg, hcard, hocc, hdisj, hcover, hcross⟩ := hdim S r hr
  refine ⟨fs.prod, cells, hfs, hdeg, hcard, ?_, hdisj, hcover, hcross⟩
  intro R hR
  rcases hocc R hR with ⟨_, hopen, hpoints⟩
  exact ⟨hopen, hpoints⟩

/-- Line-restriction zero count, CI:8–9, 172–173, motions.tex:466–469. -/
private noncomputable def polynomialLineRestriction {d : ℕ} (f : Poly d)
    (p v : E d) : Polynomial ℝ :=
  MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i)) f

private theorem polynomialLineRestriction_degree {d : ℕ} (f : Poly d) (p v : E d) :
    (polynomialLineRestriction f p v).natDegree ≤ f.totalDegree := by
  have hcoord : ∀ i : Fin d,
      (Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i)).natDegree ≤ 1 := by
    intro i
    calc
      (Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i)).natDegree ≤
          max (Polynomial.C (p i)).natDegree (Polynomial.X * Polynomial.C (v i)).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 1 := max_le (by simp) (by
        calc
          (Polynomial.X * Polynomial.C (v i)).natDegree ≤
              Polynomial.X.natDegree + (Polynomial.C (v i)).natDegree :=
            Polynomial.natDegree_mul_le
          _ = 1 := by simp)
  simpa [polynomialLineRestriction] using
    (MvPolynomial.aeval_natDegree_le f (le_rfl : f.totalDegree ≤ f.totalDegree)
      (fun i => Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i)) hcoord)

private theorem polynomialLineRestriction_eval {d : ℕ} (f : Poly d) (p v : E d)
    (t : ℝ) :
    (polynomialLineRestriction f p v).eval t = evalR f (p + t • v) := by
  rw [polynomialLineRestriction, MvPolynomial.aeval_def,
    MvPolynomial.polynomial_eval_eval₂]
  have hcoeff :
      (Polynomial.evalRingHom t).comp (algebraMap ℝ (Polynomial ℝ)) = RingHom.id ℝ := by
    ext a
    simp
  rw [hcoeff, MvPolynomial.eval₂_id]
  change MvPolynomial.eval
      (fun i => Polynomial.eval t (Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i))) f =
    MvPolynomial.eval (fun i => (p + t • v) i) f
  have hvars :
      (fun i => Polynomial.eval t (Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i))) =
        (fun i => (p + t • v) i) := by
    funext i
    simp [PiLp.add_apply, PiLp.smul_apply]
    ring
  rw [hvars]

theorem polynomial_line_zeros (d : ℕ) (f : Poly d) (l : Line d) (S : Finset (E d))
    (hS : ∀ x ∈ S, x ∈ l.1 ∧ evalR f x = 0) (hcard : f.totalDegree < S.card) :
    onPolynomial f l := by
  classical
  have hne : (l.1 : Set (E d)).Nonempty := l.2.1
  have hdim : Module.finrank ℝ l.1.direction = 1 := l.2.2
  letI : Nonempty l.1 := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let p₀ : l.1 := ⟨hne.choose, hne.choose_spec⟩
  let e : ℝ ≃ₗ[ℝ] l.1.direction :=
    Classical.choice (Module.nonempty_linearEquiv_of_finrank_eq_one hdim)
  let τ : l.1 → ℝ := fun x => e.symm (x -ᵥ p₀)
  let p : E d := p₀
  let v : E d := e 1
  let P : Polynomial ℝ := polynomialLineRestriction f p v
  have hτ : Function.Injective τ := by
    intro x y hxy
    have hv : x -ᵥ p₀ = y -ᵥ p₀ := e.symm.injective (by simpa [τ] using hxy)
    exact (vsub_left_injective p₀) hv
  have hparam (x : l.1) : (x : E d) = p + τ x • v := by
    have hlin : e (τ x) = τ x • e 1 := by
      simpa using e.map_smul (τ x) (1 : ℝ)
    have hvsub : e (τ x) = x -ᵥ p₀ := by simp [τ]
    have hpoint : x = (τ x • e 1) +ᵥ p₀ := by
      calc
        x = (x -ᵥ p₀) +ᵥ p₀ := by rw [vsub_vadd]
        _ = e (τ x) +ᵥ p₀ := by rw [hvsub]
        _ = (τ x • e 1) +ᵥ p₀ := by rw [hlin]
    simpa [p, v, AffineSubspace.coe_vadd, add_comm] using
      congrArg (fun y : l.1 => (y : E d)) hpoint
  let ψ : S → ℝ := fun x => τ ⟨x.1, (hS x.1 x.2).1⟩
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have hline : (⟨x.1, (hS x.1 x.2).1⟩ : l.1) = ⟨y.1, (hS y.1 y.2).1⟩ :=
      hτ (by simpa [ψ] using hxy)
    apply Subtype.ext
    exact congrArg (fun z : l.1 => (z : E d)) hline
  let T : Finset ℝ := S.attach.image ψ
  have hTcard : T.card = S.card := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ hψ]
    simp
  have hroots : ∀ t ∈ T, P.eval t = 0 := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨x, hx, rfl⟩
    calc
      P.eval (ψ x) = evalR f (p + ψ x • v) := by
        exact polynomialLineRestriction_eval f p v (ψ x)
      _ = evalR f x.1 := by
        rw [← hparam ⟨x.1, (hS x.1 x.2).1⟩]
      _ = 0 := (hS x.1 x.2).2
  have hdeg : P.natDegree ≤ f.totalDegree := by
    exact polynomialLineRestriction_degree f p v
  have hlt : P.natDegree < T.card := by
    rw [hTcard]
    exact lt_of_le_of_lt hdeg hcard
  have hP : P = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P T hroots hlt
  intro x hx
  let x₀ : l.1 := ⟨x, hx⟩
  have hzero : P.eval (τ x₀) = 0 := by rw [hP]; simp
  calc
    evalR f x = evalR f (p + τ x₀ • v) := by rw [← hparam x₀]
    _ = P.eval (τ x₀) := (polynomialLineRestriction_eval f p v (τ x₀)).symm
    _ = 0 := hzero

/-- Flat interpolation in six-space, motions.tex:393–399. -/
theorem flat_interpolation (n k D : ℕ) (H : Finset (Flat n k))
    (hsize : H.card * Nat.choose (D + k) k < Nat.choose (D + n) n) :
    ∃ f : Poly n, f ≠ 0 ∧ f.totalDegree ≤ D ∧ ∀ h ∈ H, onPolynomial f h := by
  exact flatInterpolationAux H hsize

/-- Removing repeated factors, CI:267–268, 723. -/
theorem squarefree_part (f : Poly 3) (hf : f ≠ 0) :
    ∃ g : Poly 3, g ≠ 0 ∧ Squarefree g ∧ g.totalDegree ≤ f.totalDegree ∧
      zeroSet g = zeroSet f := by
  classical
  obtain ⟨g, n, hsq, hgf, hfgn⟩ := exists_squarefree_dvd_pow_of_ne_zero hf
  obtain ⟨a, ha⟩ := hgf
  obtain ⟨b, hb⟩ := hfgn
  have hg : g ≠ 0 := by
    intro hzero
    subst g
    simp at ha
    exact hf ha
  have hdeg : g.totalDegree ≤ f.totalDegree :=
    MvPolynomial.totalDegree_le_of_dvd_of_isDomain ⟨a, ha⟩ hf
  have hfa (x : E 3) : evalR f x = evalR g x * evalR a x := by
    rw [ha]
    simp [evalR]
  have hpow (x : E 3) : evalR g x ^ n = evalR f x * evalR b x := by
    have he := congrArg (fun q : Poly 3 => evalR q x) hb
    simpa [evalR] using he
  have hrootfree (x : E 3) (hfx : evalR f x = 0) (hn : n = 0) : False := by
    have he := hpow x
    simp [hn, hfx] at he
  have hzeroSet : zeroSet g = zeroSet f := by
    ext x
    by_cases hn : n = 0
    · constructor
      · intro hx
        change evalR g x = 0 at hx
        have hfx : evalR f x = 0 := by rw [hfa x, hx]; simp
        exact (hrootfree x hfx hn).elim
      · intro hx
        exact (hrootfree x hx hn).elim
    · constructor
      · intro hx
        change evalR g x = 0 at hx
        change evalR f x = 0
        rw [hfa x, hx]
        simp
      · intro hx
        change evalR f x = 0 at hx
        have hp : evalR g x ^ n = 0 := by
          rw [hpow x, hx]
          simp
        exact (pow_eq_zero_iff hn).mp hp
  exact ⟨g, hg, hsq, hdeg, hzeroSet⟩

/-- Shared-model adapter required from track A; CI:6–8. -/
theorem coprime_common_lines_real (f g : Poly 3) (hf : f ≠ 0) (hg : g ≠ 0)
    (hcop : IsRelPrime f g) :
    FiniteCardBound {l : Line 3 | onPolynomial f l ∧ onPolynomial g l}
      ((f.totalDegree : ℝ) * g.totalDegree) := by
  exact DistinctDistances.Bridges.coprime_common_lines_real f g hf hg hcop

private theorem polynomialLineRestriction_derivative (f : Poly 3) (p v : E 3) :
    Polynomial.derivative (polynomialLineRestriction f p v) =
      ∑ i : Fin 3, Polynomial.C (v i) *
        polynomialLineRestriction (MvPolynomial.pderiv i f) p v := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [polynomialLineRestriction]
  | add f g hf hg =>
      have hsum : polynomialLineRestriction (f + g) p v =
          polynomialLineRestriction f p v + polynomialLineRestriction g p v := by
        simp [polynomialLineRestriction]
      rw [hsum]
      rw [Polynomial.derivative_add, hf, hg]
      simp only [polynomialLineRestriction, map_add, Finset.sum_add_distrib]
      rw [← Finset.sum_add_distrib]
      simp only [mul_add]
  | mul_X f i hf =>
      have hcoord : polynomialLineRestriction (MvPolynomial.X i) p v =
          Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i) := by
        simp [polynomialLineRestriction]
      have hcoord' : Polynomial.derivative
          (Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i)) =
            Polynomial.C (v i) := by simp
      have hmul : polynomialLineRestriction (f * MvPolynomial.X i) p v =
          polynomialLineRestriction f p v * polynomialLineRestriction (MvPolynomial.X i) p v := by
        simp [polynomialLineRestriction]
      rw [hmul, Polynomial.derivative_mul, hf, hcoord, hcoord']
      have hdelta : ∑ j : Fin 3,
          Polynomial.C (v j) * Polynomial.C (if i = j then (1 : ℝ) else 0) =
            Polynomial.C (v i) := by
        simp
      have htail : ∑ j : Fin 3, Polynomial.C (v j) *
          (polynomialLineRestriction f p v *
            Polynomial.C (if i = j then (1 : ℝ) else 0)) =
            polynomialLineRestriction f p v * Polynomial.C (v i) := by
        calc
          _ = ∑ j : Fin 3, polynomialLineRestriction f p v *
              (Polynomial.C (v j) *
                Polynomial.C (if i = j then (1 : ℝ) else 0)) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = polynomialLineRestriction f p v *
              (∑ j : Fin 3, Polynomial.C (v j) *
                Polynomial.C (if i = j then (1 : ℝ) else 0)) := by
                rw [Finset.mul_sum]
          _ = _ := by rw [hdelta]
      have hmain :
          (∑ j : Fin 3, Polynomial.C (v j) * polynomialLineRestriction
            (MvPolynomial.pderiv j f) p v) *
              (Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i)) +
            polynomialLineRestriction f p v * Polynomial.C (v i) =
          ∑ j : Fin 3, Polynomial.C (v j) *
            (polynomialLineRestriction (MvPolynomial.pderiv j f) p v *
                (Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i)) +
              polynomialLineRestriction f p v *
                Polynomial.C (if i = j then (1 : ℝ) else 0)) := by
        calc
          _ = ∑ j : Fin 3,
                (Polynomial.C (v j) * polynomialLineRestriction
                    (MvPolynomial.pderiv j f) p v * Polynomial.C (p i) +
                  Polynomial.C (v j) * polynomialLineRestriction
                    (MvPolynomial.pderiv j f) p v *
                    (Polynomial.X * Polynomial.C (v i)) +
                  Polynomial.C (v j) *
                    (polynomialLineRestriction f p v *
                      Polynomial.C (if i = j then (1 : ℝ) else 0))) := by
                  rw [mul_add, Finset.sum_mul, Finset.sum_mul, ← htail,
                    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          _ = _ := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
      have hrhs (j : Fin 3) :
          polynomialLineRestriction (MvPolynomial.pderiv j (f * MvPolynomial.X i)) p v =
            polynomialLineRestriction (MvPolynomial.pderiv j f) p v *
                (Polynomial.C (p i) + Polynomial.X * Polynomial.C (v i)) +
              polynomialLineRestriction f p v *
                Polynomial.C (if i = j then (1 : ℝ) else 0) := by
        rw [MvPolynomial.pderiv_mul]
        by_cases hji : j = i
        · subst j
          simp [polynomialLineRestriction, hcoord]
        · have hij : i ≠ j := Ne.symm hji
          simp [polynomialLineRestriction, hcoord, hij]
      rw [hmain]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hrhs]

private theorem polynomialLineRestriction_firstDerivative_eval (f : Poly 3) (p v : E 3) :
    (Polynomial.derivative (polynomialLineRestriction f p v)).eval 0 =
      ∑ i : Fin 3, v i * evalR (MvPolynomial.pderiv i f) p := by
  rw [polynomialLineRestriction_derivative]
  simp [Polynomial.eval_finsetSum, polynomialLineRestriction_eval, evalR]

private theorem polynomialLineRestriction_secondDerivative_eval (f : Poly 3) (p v : E 3) :
    (Polynomial.derivative (Polynomial.derivative (polynomialLineRestriction f p v))).eval 0 =
      hessian f p v v := by
  have hpoly :
      Polynomial.derivative (Polynomial.derivative (polynomialLineRestriction f p v)) =
        ∑ i : Fin 3, Polynomial.C (v i) *
          (∑ j : Fin 3, Polynomial.C (v j) *
            polynomialLineRestriction (MvPolynomial.pderiv j (MvPolynomial.pderiv i f)) p v) := by
    calc
      _ = Polynomial.derivative
          (∑ i : Fin 3, Polynomial.C (v i) *
            polynomialLineRestriction (MvPolynomial.pderiv i f) p v) := by
              rw [polynomialLineRestriction_derivative]
      _ = ∑ i : Fin 3, Polynomial.derivative
          (Polynomial.C (v i) * polynomialLineRestriction (MvPolynomial.pderiv i f) p v) := by
              rw [Polynomial.derivative_sum]
      _ = ∑ i : Fin 3, Polynomial.C (v i) *
          Polynomial.derivative (polynomialLineRestriction (MvPolynomial.pderiv i f) p v) := by
              simp [Polynomial.derivative_mul, Polynomial.derivative_C]
      _ = _ := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [polynomialLineRestriction_derivative]
  rw [hpoly]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    polynomialLineRestriction_eval]
  simp only [hessian]
  simp only [zero_smul, add_zero]
  have hdist (i : Fin 3) :
      v i * (∑ j : Fin 3, v j *
        evalR (MvPolynomial.pderiv j (MvPolynomial.pderiv i f)) p) =
        ∑ j : Fin 3, v i * (v j *
          evalR (MvPolynomial.pderiv j (MvPolynomial.pderiv i f)) p) := by
    simpa using (Finset.mul_sum Finset.univ
      (fun j : Fin 3 => v j * evalR (MvPolynomial.pderiv j (MvPolynomial.pderiv i f)) p)
      (v i))
  simp_rw [hdist]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem onPolynomial_direction_jet_zero (f : Poly 3) (l : Line 3) (x : E 3)
    (hx : x ∈ l.1) (hf : onPolynomial f l) (v : E 3) (hv : v ∈ l.1.direction) :
    (∑ i : Fin 3, gradient f x i * v i) = 0 ∧ hessian f x v v = 0 := by
  have hpath (t : ℝ) : x + t • v ∈ l.1 := by
    have hmem := AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.smul_mem l.1.direction t hv) hx
    simpa [AffineSubspace.coe_vadd, add_comm] using hmem
  have heval (t : ℝ) : (polynomialLineRestriction f x v).eval t = 0 := by
    rw [polynomialLineRestriction_eval]
    exact hf (x + t • v) (hpath t)
  have hrootset :
      {t : ℝ | Polynomial.IsRoot (polynomialLineRestriction f x v) t} = Set.univ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact Polynomial.IsRoot.def.mpr (heval t)
  have hzero : polynomialLineRestriction f x v = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    rw [hrootset]
    exact Set.infinite_univ
  have hfirst :
      (Polynomial.derivative (polynomialLineRestriction f x v)).eval 0 = 0 := by
    rw [hzero]
    simp
  rw [polynomialLineRestriction_firstDerivative_eval] at hfirst
  have hgrad : (∑ i : Fin 3, gradient f x i * v i) = 0 := by
    simpa [gradient, evalR, mul_comm] using hfirst
  have hsecond :
      (Polynomial.derivative (Polynomial.derivative (polynomialLineRestriction f x v))).eval 0 = 0 := by
    rw [hzero]
    simp
  rw [polynomialLineRestriction_secondDerivative_eval] at hsecond
  exact ⟨hgrad, hsecond⟩

private theorem exists_nonzero_line_direction (l : Line 3) :
    ∃ v : E 3, v ∈ l.1.direction ∧ v ≠ 0 := by
  let e : ℝ ≃ₗ[ℝ] l.1.direction :=
    Classical.choice (Module.nonempty_linearEquiv_of_finrank_eq_one l.2.2)
  let v : E 3 := e 1
  have hv : v ∈ l.1.direction := (e 1).property
  have hvne : v ≠ 0 := by
    intro h
    have he : e (1 : ℝ) = e 0 := by
      rw [map_zero]
      exact Subtype.ext h
    exact one_ne_zero (e.injective he)
  exact ⟨v, hv, hvne⟩

private theorem line_generators_not_smul (l₁ l₂ : Line 3) (x : E 3)
    (hx₁ : x ∈ l₁.1) (hx₂ : x ∈ l₂.1) (hneq : l₁ ≠ l₂)
    (v₁ v₂ : E 3) (hv₁ : v₁ ∈ l₁.1.direction) (hv₂ : v₂ ∈ l₂.1.direction)
    (hv₁ne : v₁ ≠ 0) (hv₂ne : v₂ ≠ 0) :
    ∀ a : ℝ, a • v₁ ≠ v₂ := by
  have hspan₁ : Submodule.span ℝ ({v₁} : Set (E 3)) = l₁.1.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.2
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact hv₁
    · rw [finrank_span_singleton hv₁ne, l₁.2.2]
  have hspan₂ : Submodule.span ℝ ({v₂} : Set (E 3)) = l₂.1.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.2
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact hv₂
    · rw [finrank_span_singleton hv₂ne, l₂.2.2]
  intro a ha
  have hv₂span : v₂ ∈ Submodule.span ℝ ({v₁} : Set (E 3)) := by
    rw [Submodule.mem_span_singleton]
    exact ⟨a, ha⟩
  have hle : l₂.1.direction ≤ l₁.1.direction := by
    rw [← hspan₂, ← hspan₁]
    exact Submodule.span_le.2 (by
      intro z hz
      have hzv : z = v₂ := Set.mem_singleton_iff.mp hz
      subst z
      exact hv₂span)
  have hdir : l₁.1.direction = l₂.1.direction := by
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [l₂.2.2, l₁.2.2])
    exact heq.symm
  have hflat : l₁.1 = l₂.1 :=
    (AffineSubspace.eq_iff_direction_eq_of_mem hx₁ hx₂).2 hdir
  exact hneq (Subtype.ext hflat)

private noncomputable def hessianBilinear (f : Poly 3) (x : E 3) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => hessian f x u v
      map_add' := by
        intro v w
        simp only [hessian, Pi.add_apply]
        calc
          (∑ i, ∑ j, u i * (v j + w j) *
              evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x) =
              ∑ i, ∑ j, (u i * v j * evalR (MvPolynomial.pderiv i
                (MvPolynomial.pderiv j f)) x +
                u i * w j * evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = _ := by simp only [Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        simp only [hessian, Pi.smul_apply, smul_eq_mul]
        calc
          (∑ i, ∑ j, u i * (a * v j) *
              evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x) =
              ∑ i, ∑ j, a * (u i * v j *
                evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = a * ∑ i, ∑ j, u i * v j *
                evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x := by
            simp only [Finset.mul_sum] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change hessian f x (u + v) w = hessian f x u w + hessian f x v w
    simp only [hessian, Pi.add_apply]
    calc
      (∑ i, ∑ j, (u i + v i) * w j *
          evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x) =
          ∑ i, ∑ j, (u i * w j * evalR (MvPolynomial.pderiv i
            (MvPolynomial.pderiv j f)) x +
            v i * w j * evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp only [Finset.sum_add_distrib]
  map_smul' := by
    intro a u
    apply LinearMap.ext
    intro v
    change hessian f x (a • u) v = a * hessian f x u v
    simp only [hessian, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, ∑ j, (a * u i) * v j *
          evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x) =
          ∑ i, ∑ j, a * (u i * v j *
            evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = a * ∑ i, ∑ j, u i * v j *
            evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x := by
        simp only [Finset.mul_sum]

private theorem hessian_sum_bilinear (f : Poly 3) (x : E 3)
    (c d : Fin 3 → ℝ) (u v : Fin 3 → (Fin 3 → ℝ)) :
    hessian f x (∑ j, c j • u j) (∑ k, d k • v k) =
      ∑ j, ∑ k, c j * d k * hessian f x (u j) (v k) := by
  change hessianBilinear f x (∑ j, c j • u j) (∑ k, d k • v k) = _
  simp [hessianBilinear, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum,
    Finset.smul_sum, Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]

private theorem hessian_zero_left (f : Poly 3) (x : E 3) (v : Fin 3 → ℝ) :
    hessian f x 0 v = 0 := by simp [hessian]

private theorem hessian_zero_right (f : Poly 3) (x : E 3) (u : Fin 3 → ℝ) :
    hessian f x u 0 = 0 := by simp [hessian]

private theorem pderiv_commute (i j : Fin 3) (f : Poly 3) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f k hf =>
      by_cases hij : i = j
      · subst j
        simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, hf,
          Pi.single_apply, add_comm, add_left_comm, add_assoc]
      · simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
        have hji : j ≠ i := fun h => hij h.symm
        by_cases hkj : k = j
        · by_cases hki : k = i
          · exact (hij (hki.symm.trans hkj)).elim
          · simp [hij, hji, hkj, hki, hf, Pi.single_apply, add_comm, add_left_comm, add_assoc]
        · by_cases hki : k = i
          · simp [hij, hji, hkj, hki, hf, Pi.single_apply, add_comm, add_left_comm, add_assoc]
          · simp [hij, hji, hkj, hki, hf, Pi.single_apply, add_comm, add_left_comm, add_assoc]

private theorem hessian_symm (f : Poly 3) (x : E 3) (u v : Fin 3 → ℝ) :
    hessian f x u v = hessian f x v u := by
  unfold hessian
  calc
    (∑ i : Fin 3, ∑ j : Fin 3,
        u i * v j * evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x) =
      ∑ j : Fin 3, ∑ i : Fin 3,
        v j * u i * evalR (MvPolynomial.pderiv j (MvPolynomial.pderiv i f)) x := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          rw [pderiv_commute]
          ring
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        v i * u j * evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x := rfl

private def tangentPairingLinear (g : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun u := ∑ i : Fin 3, g i * u i
  map_add' u v := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' a u := by
    calc
      (∑ i : Fin 3, g i * (a * u i)) =
          ∑ i : Fin 3, a * (g i * u i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = a * ∑ i : Fin 3, g i * u i := by rw [Finset.mul_sum]

/-- ci:flat(1), CI:152–165. -/
theorem three_lines_critical_or_flat (f : Poly 3) (x : E 3)
    (l₁ l₂ l₃ : Line 3) (h12 : l₁ ≠ l₂) (h13 : l₁ ≠ l₃) (h23 : l₂ ≠ l₃)
    (h₁ : onPolynomial f l₁) (h₂ : onPolynomial f l₂) (h₃ : onPolynomial f l₃)
    (hx₁ : x ∈ l₁.1) (hx₂ : x ∈ l₂.1) (hx₃ : x ∈ l₃.1) :
    criticalPoint f x ∨ flatPoint f x := by
  classical
  have hzero : evalR f x = 0 := h₁ x hx₁
  by_cases hcrit : ∀ i : Fin 3, gradient f x i = 0
  · exact Or.inl ⟨hzero, hcrit⟩
  · push_neg at hcrit
    obtain ⟨i, hi⟩ := hcrit
    right
    have hreg : regularPoint f x := ⟨hzero, i, hi⟩
    obtain ⟨v₁, hv₁dir, hv₁ne⟩ := exists_nonzero_line_direction l₁
    obtain ⟨v₂, hv₂dir, hv₂ne⟩ := exists_nonzero_line_direction l₂
    obtain ⟨v₃, hv₃dir, hv₃ne⟩ := exists_nonzero_line_direction l₃
    have hj₁ := onPolynomial_direction_jet_zero f l₁ x hx₁ h₁ v₁ hv₁dir
    have hj₂ := onPolynomial_direction_jet_zero f l₂ x hx₂ h₂ v₂ hv₂dir
    have hj₃ := onPolynomial_direction_jet_zero f l₃ x hx₃ h₃ v₃ hv₃dir
    let w₁ : Fin 3 → ℝ := v₁.ofLp
    let w₂ : Fin 3 → ℝ := v₂.ofLp
    let w₃ : Fin 3 → ℝ := v₃.ofLp
    have hj₁' :
        (∑ i : Fin 3, gradient f x i * w₁ i) = 0 ∧ hessian f x w₁ w₁ = 0 := by
      simpa [w₁] using hj₁
    have hj₂' :
        (∑ i : Fin 3, gradient f x i * w₂ i) = 0 ∧ hessian f x w₂ w₂ = 0 := by
      simpa [w₂] using hj₂
    have hj₃' :
        (∑ i : Fin 3, gradient f x i * w₃ i) = 0 ∧ hessian f x w₃ w₃ = 0 := by
      simpa [w₃] using hj₃
    have hn₁₂ := line_generators_not_smul l₁ l₂ x hx₁ hx₂ h12
      v₁ v₂ hv₁dir hv₂dir hv₁ne hv₂ne
    have hn₁₃ := line_generators_not_smul l₁ l₃ x hx₁ hx₃ h13
      v₁ v₃ hv₁dir hv₃dir hv₁ne hv₃ne
    have hn₂₃ := line_generators_not_smul l₂ l₃ x hx₂ hx₃ h23
      v₂ v₃ hv₂dir hv₃dir hv₂ne hv₃ne
    have hn₁₂' : ∀ a : ℝ, a • w₁ ≠ w₂ := by
      intro a ha
      apply hn₁₂ a
      apply PiLp.ext
      intro i
      simpa [w₁, w₂, PiLp.smul_apply] using congrFun ha i
    have hn₁₃' : ∀ a : ℝ, a • w₁ ≠ w₃ := by
      intro a ha
      apply hn₁₃ a
      apply PiLp.ext
      intro i
      simpa [w₁, w₃, PiLp.smul_apply] using congrFun ha i
    have hn₂₃' : ∀ a : ℝ, a • w₂ ≠ w₃ := by
      intro a ha
      apply hn₂₃ a
      apply PiLp.ext
      intro i
      simpa [w₂, w₃, PiLp.smul_apply] using congrFun ha i
    let L := tangentPairingLinear (gradient f x)
    have hw₁ker : w₁ ∈ L.ker := by
      change L w₁ = 0
      simpa [L, tangentPairingLinear] using hj₁'.1
    have hw₂ker : w₂ ∈ L.ker := by
      change L w₂ = 0
      simpa [L, tangentPairingLinear] using hj₂'.1
    have hw₃ker : w₃ ∈ L.ker := by
      change L w₃ = 0
      simpa [L, tangentPairingLinear] using hj₃'.1
    have hvalue : L (Pi.single i (1 : ℝ)) = gradient f x i := by
      simp [L, tangentPairingLinear, Pi.single_apply]
    have hrange_ne : L.range ≠ (⊥ : Submodule ℝ ℝ) := by
      intro hbot
      have hmem : L (Pi.single i (1 : ℝ)) ∈ L.range := ⟨_, rfl⟩
      rw [hbot] at hmem
      have hz : L (Pi.single i (1 : ℝ)) = 0 := by simpa using hmem
      rw [hvalue] at hz
      exact hi hz
    have hrange_pos : 1 ≤ Module.finrank ℝ L.range :=
      Submodule.one_le_finrank_iff.mpr hrange_ne
    have hrange_le : Module.finrank ℝ L.range ≤ 1 := by
      calc
        Module.finrank ℝ L.range ≤ Module.finrank ℝ ℝ := L.range.finrank_le
        _ = 1 := by simp
    have hrange_dim : Module.finrank ℝ L.range = 1 := le_antisymm hrange_le hrange_pos
    have hker_dim : Module.finrank ℝ L.ker = 2 := by
      have h := L.finrank_range_add_finrank_ker
      rw [hrange_dim] at h
      have hV : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
      rw [hV] at h
      omega
    let p₁₂ : Fin 2 → (Fin 3 → ℝ) := ![w₁, w₂]
    have hpair : LinearIndependent ℝ p₁₂ := by
      exact (LinearIndependent.pair_iff' (by simpa [w₁] using hv₁ne)).2 hn₁₂'
    have hrange₁₂ : Set.range p₁₂ = ({w₁, w₂} : Set (Fin 3 → ℝ)) := by
      ext z
      constructor
      · rintro ⟨j, rfl⟩
        fin_cases j <;> simp [p₁₂]
      · intro hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact ⟨0, by simp [p₁₂]⟩
        · rcases Set.mem_singleton_iff.mp hz with rfl
          exact ⟨1, by simp [p₁₂]⟩
    have hspan_dim : Module.finrank ℝ (Submodule.span ℝ (Set.range p₁₂)) = 2 := by
      rw [finrank_span_eq_card hpair]
      simp [p₁₂]
    have hspan_le : Submodule.span ℝ (Set.range p₁₂) ≤ L.ker := by
      rw [hrange₁₂]
      apply Submodule.span_le.2
      intro z hz
      rcases Set.mem_insert_iff.mp hz with hz | hz
      · rw [hz]
        exact hw₁ker
      · rcases Set.mem_singleton_iff.mp hz with rfl
        exact hw₂ker
    have hspan_eq : Submodule.span ℝ (Set.range p₁₂) = L.ker := by
      apply Submodule.eq_of_le_of_finrank_eq hspan_le
      rw [hspan_dim, hker_dim]
    have htangent_span (u : Fin 3 → ℝ)
        (hu : (∑ i : Fin 3, gradient f x i * u i) = 0) :
        u ∈ Submodule.span ℝ ({w₁, w₂} : Set (Fin 3 → ℝ)) := by
      have huKer : u ∈ L.ker := by
        change L u = 0
        simpa [L, tangentPairingLinear] using hu
      have huSpan : u ∈ Submodule.span ℝ (Set.range p₁₂) := by
        rw [hspan_eq]
        exact huKer
      simpa only [hrange₁₂] using huSpan
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp
      (show w₃ ∈ Submodule.span ℝ ({w₁, w₂} : Set (Fin 3 → ℝ)) from htangent_span
        w₃ (by simpa [L, tangentPairingLinear] using hj₃'.1))
    have ha : a ≠ 0 := by
      intro ha
      have hmul : b • w₂ = w₃ := by simpa [ha] using hab
      exact hn₂₃' b hmul
    have hb : b ≠ 0 := by
      intro hb
      have hmul : a • w₁ = w₃ := by simpa [hb] using hab
      exact hn₁₃' a hmul
    let basis₃ : Fin 3 → (Fin 3 → ℝ) := ![w₁, w₂, 0]
    let coeff₃ : Fin 3 → ℝ := ![a, b, 0]
    have hw₃repr : w₃ = ∑ j : Fin 3, coeff₃ j • basis₃ j := by
      simpa [coeff₃, basis₃, Fin.sum_univ_succ] using hab.symm
    have hquad0 : hessian f x
        (∑ j : Fin 3, coeff₃ j • basis₃ j)
        (∑ j : Fin 3, coeff₃ j • basis₃ j) = 0 := by
      simpa only [hw₃repr] using hj₃'.2
    rw [hessian_sum_bilinear] at hquad0
    have hcross : a * b *
        (hessian f x w₁ w₂ + hessian f x w₂ w₁) = 0 := by
      simp [coeff₃, basis₃, Fin.sum_univ_succ, hessian_zero_left, hessian_zero_right] at hquad0
      rw [hj₁'.2, hj₂'.2] at hquad0
      nlinarith [hquad0]
    have hcross_ne : a * b ≠ 0 := mul_ne_zero ha hb
    have hsum : hessian f x w₁ w₂ + hessian f x w₂ w₁ = 0 :=
      (mul_eq_zero.mp hcross).resolve_left hcross_ne
    have h₁₂ : hessian f x w₁ w₂ = 0 := by
      nlinarith [hsum, hessian_symm f x w₁ w₂]
    have h₂₁ : hessian f x w₂ w₁ = 0 := by
      rw [hessian_symm f x w₂ w₁]
      exact h₁₂
    have h₁₁ : hessian f x w₁ w₁ = 0 := hj₁'.2
    have h₂₂ : hessian f x w₂ w₂ = 0 := hj₂'.2
    refine ⟨hreg, ?_⟩
    intro u v hu hv
    obtain ⟨au, bu, huPair⟩ := Submodule.mem_span_pair.mp (htangent_span u hu)
    obtain ⟨av, bv, hvPair⟩ := Submodule.mem_span_pair.mp (htangent_span v hv)
    let coeffᵤ : Fin 3 → ℝ := ![au, bu, 0]
    let coeffᵥ : Fin 3 → ℝ := ![av, bv, 0]
    have huRepr : u = ∑ j : Fin 3, coeffᵤ j • basis₃ j := by
      simpa [coeffᵤ, basis₃, Fin.sum_univ_succ] using huPair.symm
    have hvRepr : v = ∑ j : Fin 3, coeffᵥ j • basis₃ j := by
      simpa [coeffᵥ, basis₃, Fin.sum_univ_succ] using hvPair.symm
    rw [huRepr, hvRepr, hessian_sum_bilinear]
    simp [coeffᵤ, coeffᵥ, basis₃, Fin.sum_univ_succ, h₁₁, h₁₂, h₂₁, h₂₂,
      hessian_zero_left, hessian_zero_right]

private theorem pderiv_totalDegree_lt (f : Poly 3) (i : Fin 3)
    (hD : 0 < f.totalDegree) :
    (MvPolynomial.pderiv i f).totalDegree < f.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff (Nat.zero_lt_of_lt hD)]
  intro m hm
  have hcoeff : (MvPolynomial.pderiv i f).coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hsource : m + Finsupp.single i 1 ∈ f.support := by
    rw [MvPolynomial.mem_support_iff]
    intro hz
    simp [hz] at hcoeff
  have hsum : (m.sum fun _ e => e) + 1 ≤
      (m + Finsupp.single i 1).sum fun _ e => e := by
    simp [Finsupp.sum_add_index']
  calc
    (m.sum fun _ e => e) < (m.sum fun _ e => e) + 1 := Nat.lt_succ_self _
    _ ≤ (m + Finsupp.single i 1).sum fun _ e => e := hsum
    _ ≤ f.totalDegree := MvPolynomial.le_totalDegree hsource

private theorem irreducible_pderiv_not_dvd (p : Poly 3) (hp : Irreducible p) :
    ∃ i : Fin 3, ¬ p ∣ MvPolynomial.pderiv i p := by
  classical
  have hD : 0 < p.totalDegree := by
    by_contra hnot
    have hzero : p.totalDegree = 0 := by omega
    have hconst := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hzero
    have hcoeff : p.coeff 0 ≠ 0 := by
      intro h
      apply hp.ne_zero
      rw [hconst, h]
      simp
    have hunit : IsUnit p := by
      rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced]
      exact ⟨isUnit_iff_ne_zero.mpr hcoeff, hzero⟩
    exact hp.not_isUnit hunit
  have hvars : p.vars.Nonempty := by
    by_contra h
    have hconst := MvPolynomial.vars_eq_empty_iff_eq_C.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    have hcoeff : p.coeff 0 ≠ 0 := by
      intro hz
      apply hp.ne_zero
      rw [hconst, hz]
      simp
    have hunit : IsUnit p := by
      rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced]
      refine ⟨isUnit_iff_ne_zero.mpr hcoeff, ?_⟩
      rw [hconst]
      simp
    exact hp.not_isUnit hunit
  obtain ⟨i, hi⟩ := hvars
  obtain ⟨m, hm, hmi⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hmcoeff : p.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hmexp : m i ≠ 0 := Finsupp.mem_support_iff.mp hmi
  let m' : Fin 3 →₀ ℕ := m - Finsupp.single i (1 : ℕ)
  have hderivCoeff :
      (MvPolynomial.pderiv i p).coeff m' ≠ 0 := by
    rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hmexp]
    have he : m' i + 1 = m i := by
      simpa [m', Finsupp.single_apply] using
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hmexp)
    have heR : (m' i : ℝ) + 1 = (m i : ℝ) := by exact_mod_cast he
    rw [heR]
    exact mul_ne_zero hmcoeff (Nat.cast_ne_zero.mpr hmexp)
  have hderiv : MvPolynomial.pderiv i p ≠ 0 := by
    intro hz
    have := congrArg (fun q : Poly 3 => q.coeff m') hz
    exact hderivCoeff (by simpa using this)
  refine ⟨i, ?_⟩
  intro hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hle : p.totalDegree ≤ (MvPolynomial.pderiv i p).totalDegree :=
    MvPolynomial.totalDegree_le_of_dvd_of_isDomain ⟨q, hq⟩ hderiv
  exact (not_lt_of_ge hle) (pderiv_totalDegree_lt p i hD)

private theorem exists_pderiv_not_dvd_of_squarefree (f : Poly 3) (hsq : Squarefree f)
    {p : Poly 3} (hp : Prime p) (hpf : p ∣ f) :
    ∃ i : Fin 3, ¬ p ∣ MvPolynomial.pderiv i f := by
  classical
  obtain ⟨b, hfb⟩ := hpf
  have hpnotb : ¬ p ∣ b := by
    intro hpb
    obtain ⟨c, hc⟩ := hpb
    apply hp.not_isUnit
    apply hsq p
    refine ⟨c, ?_⟩
    calc
      f = p * b := hfb
      _ = p * (p * c) := by rw [hc]
      _ = p * p * c := by ring
  obtain ⟨i, hi⟩ := irreducible_pderiv_not_dvd p hp.irreducible
  refine ⟨i, ?_⟩
  intro hpfderiv
  have hproduct : MvPolynomial.pderiv i f =
      MvPolynomial.pderiv i p * b + p * MvPolynomial.pderiv i b := by
    rw [hfb, MvPolynomial.pderiv_mul]
  have hterm : p ∣ p * MvPolynomial.pderiv i b := ⟨MvPolynomial.pderiv i b, rfl⟩
  have hsub := dvd_sub hpfderiv hterm
  rw [hproduct] at hsub
  have hdiv : p ∣ MvPolynomial.pderiv i p * b := by
    convert hsub using 1 <;> ring
  rcases hp.dvd_mul.mp hdiv with h | h
  · exact hi h
  · exact hpnotb h

private noncomputable def criticalDerivativeCombinationMap (f : Poly 3) :
    (Fin 3 → ℝ) →ₗ[ℝ] Poly 3 where
  toFun c := ∑ i : Fin 3, c i • MvPolynomial.pderiv i f
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [smul_smul, Finset.smul_sum]

private noncomputable def criticalDerivativeBadCoeffs (f p : Poly 3) : Submodule ℝ (Fin 3 → ℝ) :=
  Submodule.comap (criticalDerivativeCombinationMap f)
    ((Ideal.span ({p} : Set (Poly 3))).restrictScalars ℝ)

private theorem mem_criticalDerivativeBadCoeffs_iff (f p : Poly 3) (c : Fin 3 → ℝ) :
    c ∈ criticalDerivativeBadCoeffs f p ↔
      p ∣ criticalDerivativeCombinationMap f c := by
  change criticalDerivativeCombinationMap f c ∈ Ideal.span ({p} : Set (Poly 3)) ↔ _
  rw [Ideal.mem_span_singleton]

private theorem exists_coprime_derivative_combination (f : Poly 3) (hf : f ≠ 0)
    (hsq : Squarefree f) (hD : 0 < f.totalDegree) :
    ∃ c : Fin 3 → ℝ, IsRelPrime f (criticalDerivativeCombinationMap f c) := by
  classical
  let factors := (UniqueFactorizationMonoid.factors f).toFinset
  letI : Fintype {p // p ∈ factors} := Fintype.ofFinset factors fun _ => Iff.rfl
  have hproper : ∀ p : {p // p ∈ factors}, criticalDerivativeBadCoeffs f p.val ≠ ⊤ := by
    intro p htop
    have hfactor : p.val ∈ UniqueFactorizationMonoid.factors f :=
      Multiset.mem_toFinset.mp p.property
    have hp : Prime p.val := UniqueFactorizationMonoid.prime_of_factor _ hfactor
    have hpf : p.val ∣ f := UniqueFactorizationMonoid.dvd_of_mem_factors hfactor
    obtain ⟨i, hi⟩ := exists_pderiv_not_dvd_of_squarefree f hsq hp hpf
    have hmem : (Pi.single i (1 : ℝ) : Fin 3 → ℝ) ∈
        criticalDerivativeBadCoeffs f p.val := by
      rw [htop]
      exact Submodule.mem_top
    have hdiv := (mem_criticalDerivativeBadCoeffs_iff f p.val _).mp hmem
    have hsingle : criticalDerivativeCombinationMap f (Pi.single i (1 : ℝ)) =
        MvPolynomial.pderiv i f := by
      simp [criticalDerivativeCombinationMap]
    exact hi (hsingle ▸ hdiv)
  obtain ⟨c, hc⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top
      (fun p : {p // p ∈ factors} => criticalDerivativeBadCoeffs f p.val) hproper
  refine ⟨c, ?_⟩
  rw [UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hf]
  intro d hdf hdg hdPrime
  obtain ⟨q, hq, hqd⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hf hdPrime.irreducible hdf
  have hqfactor : q ∈ factors := Multiset.mem_toFinset.mpr hq
  have hqnot : c ∉ criticalDerivativeBadCoeffs f q := hc ⟨q, hqfactor⟩
  apply hqnot
  apply (mem_criticalDerivativeBadCoeffs_iff f q c).2
  exact hqd.dvd'.trans hdg

private theorem criticalDerivativeCombination_degree_le (f : Poly 3) (c : Fin 3 → ℝ)
    (hD : 0 < f.totalDegree) :
    (criticalDerivativeCombinationMap f c).totalDegree ≤ f.totalDegree - 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  rw [MvPolynomial.smul_eq_C_mul]
  calc
    (MvPolynomial.C (c i) * MvPolynomial.pderiv i f).totalDegree ≤
        (MvPolynomial.C (c i)).totalDegree + (MvPolynomial.pderiv i f).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (MvPolynomial.pderiv i f).totalDegree := by simp
    _ ≤ f.totalDegree - 1 := Nat.le_sub_one_of_lt (pderiv_totalDegree_lt f i hD)

/-- ci:flat(2), CI:155–156, 167–171. -/
theorem critical_line_bound (f : Poly 3) (hf : f ≠ 0) (hsq : Squarefree f) :
    FiniteCardBound {l : Line 3 | criticalLine f l}
      ((f.totalDegree : ℝ) * (f.totalDegree - 1 : ℕ)) := by
  classical
  by_cases hD : f.totalDegree = 0
  · have hconst := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hD
    have hcoeff : f.coeff 0 ≠ 0 := by
      intro hz
      apply hf
      rw [hconst, hz]
      simp
    have hempty : {l : Line 3 | criticalLine f l} = ∅ := by
      ext l
      constructor
      · intro hl
        obtain ⟨x, hx⟩ := l.2.1
        have hpoint : evalR f x = 0 := (hl x hx).1
        have heval : evalR f x = f.coeff 0 := by
          rw [hconst]
          simp [evalR]
        exact (hcoeff (heval.symm.trans hpoint)).elim
      · simp
    rw [hempty]
    exact ⟨Set.finite_empty, by simp [hD]⟩
  · have hDpos : 0 < f.totalDegree := by omega
    obtain ⟨c, hcop⟩ := exists_coprime_derivative_combination f hf hsq hDpos
    let g := criticalDerivativeCombinationMap f c
    have hdegree : g.totalDegree ≤ f.totalDegree - 1 :=
      criticalDerivativeCombination_degree_le f c hDpos
    have hnotunit : ¬ IsUnit f := by
      intro hu
      have hz : f.totalDegree = 0 :=
        (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
      exact (Nat.ne_of_gt hDpos) hz
    have hg : g ≠ 0 := by
      intro hzero
      apply hnotunit
      have hzero' : criticalDerivativeCombinationMap f c = 0 := by
        simpa [g] using hzero
      exact hcop.isUnit_of_dvd (hzero'.symm ▸ dvd_zero f)
    have hcritSubset : {l : Line 3 | criticalLine f l} ⊆
        {l : Line 3 | onPolynomial f l ∧ onPolynomial g l} := by
      intro l hl
      constructor
      · intro x hx
        exact (hl x hx).1
      · intro x hx
        have hgrad : ∀ i, gradient f x i = 0 := (hl x hx).2
        have hgradEval : ∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i f) = 0 := by
          intro i
          simpa [gradient, evalR] using hgrad i
        simp [g, criticalDerivativeCombinationMap, evalR, hgradEval]
    have hcommon := coprime_common_lines_real f g hf hg hcop
    refine ⟨hcommon.1.subset hcritSubset, ?_⟩
    have hcard := Set.ncard_le_ncard hcritSubset hcommon.1
    have hdegreeReal : (g.totalDegree : ℝ) ≤ ((f.totalDegree - 1 : ℕ) : ℝ) := by
      exact_mod_cast hdegree
    calc
      ({l : Line 3 | criticalLine f l}.ncard : ℝ) ≤
          ({l : Line 3 | onPolynomial f l ∧ onPolynomial g l}.ncard : ℝ) := by
        exact_mod_cast hcard
      _ ≤ (f.totalDegree : ℝ) * g.totalDegree := hcommon.2
      _ ≤ (f.totalDegree : ℝ) * (f.totalDegree - 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hdegreeReal (Nat.cast_nonneg _)

/-- ci:flat(3), CI:157–158, 172–186. -/
private theorem pderiv_totalDegree_le (i : Fin 3) (f : Poly 3) :
    (MvPolynomial.pderiv i f).totalDegree ≤ f.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro m hm
  have hcoeff : (MvPolynomial.pderiv i f).coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hmem : m + Finsupp.single i 1 ∈ f.support := by
    rw [MvPolynomial.mem_support_iff]
    intro hzero
    simp [hzero] at hcoeff
  have hsum : m.sum (fun _ e => e) ≤ (m + Finsupp.single i 1).sum (fun _ e => e) := by
    simp [Finsupp.sum_add_index']
  exact hsum.trans (MvPolynomial.le_totalDegree hmem)

private noncomputable def flatTangentPoly (f : Poly 3) (j : Fin 3) : Fin 3 → Poly 3 :=
  crossProduct (Pi.single j 1) (fun i => MvPolynomial.pderiv i f)

private noncomputable def flatTestPoly (f : Poly 3) (j k : Fin 3) : Poly 3 :=
  ∑ i : Fin 3, ∑ r : Fin 3,
    flatTangentPoly f j i * flatTangentPoly f k r *
      MvPolynomial.pderiv i (MvPolynomial.pderiv r f)

private def flatTestIndexI (q : Fin 9) : Fin 3 := ⟨q.val / 3, by omega⟩

private def flatTestIndexJ (q : Fin 9) : Fin 3 := ⟨q.val % 3, Nat.mod_lt _ (by norm_num)⟩

private noncomputable def flatnessTestsEarly (f : Poly 3) : Fin 9 → Poly 3 := fun q =>
  flatTestPoly f (flatTestIndexI q) (flatTestIndexJ q)

private theorem flatTestPair_surjective (j k : Fin 3) :
    ∃ q : Fin 9, flatTestIndexI q = j ∧ flatTestIndexJ q = k := by
  refine ⟨⟨3 * j.val + k.val, by omega⟩, ?_, ?_⟩
  · apply Fin.ext
    dsimp [flatTestIndexI]
    omega
  · apply Fin.ext
    dsimp [flatTestIndexJ]
    omega

private theorem flatTangentPoly_degree (f : Poly 3) (j i : Fin 3) :
    (flatTangentPoly f j i).totalDegree ≤ f.totalDegree := by
  classical
  fin_cases j <;> fin_cases i <;>
    simp [flatTangentPoly, cross_apply, pderiv_totalDegree_le]

set_option maxHeartbeats 500000 in
private theorem flatTestPoly_degree (f : Poly 3) (j k : Fin 3) :
    (flatTestPoly f j k).totalDegree ≤ 3 * f.totalDegree := by
  classical
  unfold flatTestPoly
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r hr
  have h₁ := flatTangentPoly_degree f j i
  have h₂ := flatTangentPoly_degree f k r
  have h₃ := (pderiv_totalDegree_le i (MvPolynomial.pderiv r f)).trans
    (pderiv_totalDegree_le r f)
  have hmul :
      (flatTangentPoly f j i * flatTangentPoly f k r).totalDegree ≤
        (flatTangentPoly f j i).totalDegree + (flatTangentPoly f k r).totalDegree :=
    MvPolynomial.totalDegree_mul (flatTangentPoly f j i) (flatTangentPoly f k r)
  calc
    (flatTangentPoly f j i * flatTangentPoly f k r *
        MvPolynomial.pderiv i (MvPolynomial.pderiv r f)).totalDegree ≤
        (flatTangentPoly f j i * flatTangentPoly f k r).totalDegree +
          (MvPolynomial.pderiv i (MvPolynomial.pderiv r f)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ (flatTangentPoly f j i).totalDegree + (flatTangentPoly f k r).totalDegree +
          (MvPolynomial.pderiv i (MvPolynomial.pderiv r f)).totalDegree := by
      calc
        _ = (MvPolynomial.pderiv i (MvPolynomial.pderiv r f)).totalDegree +
              (flatTangentPoly f j i * flatTangentPoly f k r).totalDegree := by omega
        _ ≤ (MvPolynomial.pderiv i (MvPolynomial.pderiv r f)).totalDegree +
              ((flatTangentPoly f j i).totalDegree + (flatTangentPoly f k r).totalDegree) :=
          Nat.add_le_add_left hmul _
        _ = _ := by omega
    _ ≤ f.totalDegree + f.totalDegree + f.totalDegree := by omega
    _ = 3 * f.totalDegree := by omega

private theorem eval_flatTangentPoly (f : Poly 3) (x : E 3) (j : Fin 3) :
    (fun i => evalR (flatTangentPoly f j i) x) =
      crossProduct (Pi.single j 1) (gradient f x) := by
  funext i
  fin_cases i <;>
    simp [flatTangentPoly, gradient, evalR, cross_apply, Pi.single_apply,
      MvPolynomial.eval_sub] <;> split_ifs <;> simp [evalR]

private theorem eval_flatTestPoly (f : Poly 3) (x : E 3) (j k : Fin 3) :
    evalR (flatTestPoly f j k) x =
      hessian f x (fun i => evalR (flatTangentPoly f j i) x)
        (fun i => evalR (flatTangentPoly f k i) x) := by
  simp [flatTestPoly, hessian, evalR]

private theorem flatCrossExpand (v w : Fin 3 → ℝ) :
    crossProduct v w = ∑ j : Fin 3, v j • crossProduct (Pi.single j 1) w := by
  ext i
  fin_cases i <;>
    simp [cross_apply, Fin.sum_univ_succ, Pi.single_apply] <;> ring

private theorem flatCrossTriple (g u : Fin 3 → ℝ) :
    crossProduct (crossProduct g u) g =
      (dotProduct g g) • u - (dotProduct u g) • g := by
  ext i
  fin_cases i <;>
    simp [cross_apply, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem flatTangentSpan (g u : Fin 3 → ℝ) (hg : g ≠ 0)
    (hu : dotProduct g u = 0) :
    ∃ c : Fin 3 → ℝ, u = ∑ j : Fin 3, c j • crossProduct (Pi.single j 1) g := by
  classical
  have hgg : dotProduct g g ≠ 0 := by
    intro h
    exact hg (dotProduct_self_eq_zero.mp h)
  have hug : dotProduct u g = 0 := by
    simpa [dotProduct, Finset.sum_comm, mul_comm] using hu
  have htriple := flatCrossTriple g u
  rw [hug, zero_smul, sub_zero] at htriple
  have hexpand := flatCrossExpand (crossProduct g u) g
  refine ⟨fun j => (dotProduct g g)⁻¹ * (crossProduct g u) j, ?_⟩
  calc
    u = (dotProduct g g)⁻¹ • ((dotProduct g g) • u) := by
      rw [smul_smul, inv_mul_cancel₀ hgg, one_smul]
    _ = (dotProduct g g)⁻¹ • crossProduct (crossProduct g u) g := by rw [← htriple]
    _ = (dotProduct g g)⁻¹ •
          ∑ j : Fin 3, (crossProduct g u) j • crossProduct (Pi.single j 1) g := by
      rw [hexpand]
    _ = ∑ j : Fin 3,
          ((dotProduct g g)⁻¹ * (crossProduct g u) j) • crossProduct (Pi.single j 1) g := by
      simp [Finset.smul_sum, smul_smul, mul_assoc, mul_comm]

private theorem flatnessPolynomialTestsEarly (f : Poly 3) :
    ∃ T : Fin 9 → Poly 3,
      (∀ j, (T j).totalDegree ≤ 3 * f.totalDegree) ∧
      ∀ x, regularPoint f x → (flatPoint f x ↔ ∀ j, evalR (T j) x = 0) := by
  refine ⟨flatnessTestsEarly f, ?_, ?_⟩
  · intro q
    exact flatTestPoly_degree f (flatTestIndexI q) (flatTestIndexJ q)
  · intro x hxreg
    let g : Fin 3 → ℝ := gradient f x
    let w : Fin 3 → (Fin 3 → ℝ) := fun j => crossProduct (Pi.single j 1) g
    have hg : g ≠ 0 := by
      obtain ⟨i, hi⟩ := hxreg.2
      intro hz
      exact hi (congrFun hz i)
    have hw (j : Fin 3) : dotProduct g (w j) = 0 := by
      exact dot_cross_self (Pi.single j 1) g
    have htest (q : Fin 9) : evalR (flatnessTestsEarly f q) x =
        hessian f x (w (flatTestIndexI q)) (w (flatTestIndexJ q)) := by
      change evalR (flatTestPoly f (flatTestIndexI q) (flatTestIndexJ q)) x = _
      rw [eval_flatTestPoly, eval_flatTangentPoly, eval_flatTangentPoly]
    constructor
    · intro hflat q
      rw [htest q]
      exact hflat.2 _ _ (hw _) (hw _)
    · intro htests
      have hpair : ∀ j k : Fin 3, hessian f x (w j) (w k) = 0 := by
        intro j k
        obtain ⟨q, hqj, hqk⟩ := flatTestPair_surjective j k
        have hq := htests q
        rw [htest q, hqj, hqk] at hq
        exact hq
      refine ⟨hxreg, ?_⟩
      intro u v hu hv
      change dotProduct g u = 0 at hu
      change dotProduct g v = 0 at hv
      obtain ⟨cu, hcu⟩ := flatTangentSpan g u hg hu
      obtain ⟨cv, hcv⟩ := flatTangentSpan g v hg hv
      rw [hcu, hcv]
      calc
        hessian f x (∑ j, cu j • w j) (∑ k, cv k • w k) =
            ∑ j, ∑ k, cu j * cv k * hessian f x (w j) (w k) :=
          hessian_sum_bilinear f x cu cv w w
        _ = 0 := by simp [hpair]

theorem many_critical_flat_points (f : Poly 3) (l : Line 3) (S : Finset (E 3))
    (hS : ∀ x ∈ S, x ∈ l.1) :
    (f.totalDegree < S.card → (∀ x ∈ S, criticalPoint f x) → criticalLine f l) ∧
    (3 * f.totalDegree < S.card → (∀ x ∈ S, flatPoint f x) → flatLine f l) := by
  constructor
  · intro hcard hcrit
    have hf : onPolynomial f l := by
      apply polynomial_line_zeros 3 f l S
      · intro x hx
        exact ⟨hS x hx, (hcrit x hx).1⟩
      · exact hcard
    have hderiv (i : Fin 3) : onPolynomial (MvPolynomial.pderiv i f) l := by
      apply polynomial_line_zeros 3 (MvPolynomial.pderiv i f) l S
      · intro x hx
        refine ⟨hS x hx, ?_⟩
        simpa [gradient] using (hcrit x hx).2 i
      · exact lt_of_le_of_lt (pderiv_totalDegree_le i f) hcard
    intro x hx
    refine ⟨hf x hx, ?_⟩
    intro i
    simpa [gradient] using hderiv i x hx
  · intro hcard hflat
    obtain ⟨T, hTdeg, hTchar⟩ := flatnessPolynomialTestsEarly f
    have hf : onPolynomial f l := by
      apply polynomial_line_zeros 3 f l S
      · intro x hx
        exact ⟨hS x hx, (hflat x hx).1.1⟩
      · omega
    have htestsLine (q : Fin 9) : onPolynomial (T q) l := by
      apply polynomial_line_zeros 3 (T q) l S
      · intro x hx
        refine ⟨hS x hx, ?_⟩
        exact ((hTchar x (hflat x hx).1).mp (hflat x hx)) q
      · exact lt_of_le_of_lt (hTdeg q) hcard
    have hSpos : 0 < S.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hSpos
    have hregx := (hflat x hx).1
    have hnot : ¬ criticalLine f l := by
      intro hc
      obtain ⟨i, hi⟩ := hregx.2
      exact hi ((hc x (hS x hx)).2 i)
    refine ⟨hf, hnot, ?_⟩
    intro y hy hregy
    apply (hTchar y hregy).mpr
    intro q
    exact htestsLine q y hy

/-- The nine polynomial flatness tests, CI:175–186. -/
theorem flatness_polynomial_tests (f : Poly 3) :
    ∃ T : Fin 9 → Poly 3,
      (∀ j, (T j).totalDegree ≤ 3 * f.totalDegree) ∧
      ∀ x, regularPoint f x → (flatPoint f x ↔ ∀ j, evalR (T j) x = 0) := by
  exact flatnessPolynomialTestsEarly f

/-- ci:flat(4), CI:159–160, 188–210. -/
theorem flat_line_bound (f : Poly 3) (hf : f ≠ 0) (hsq : Squarefree f) :
    FiniteCardBound {l : Line 3 | flatLine f l ∧ ¬ inPlaneComponent f l}
      (3 * (f.totalDegree : ℝ) ^ 2) := by
  letI : StrongNormalizationMonoid (Poly 3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  obtain ⟨T,hdegree,hT⟩ := flatness_polynomial_tests f
  exact flat_line_bound_of_bezout f hf hsq T hdegree hT coprime_common_lines_real

end DistinctDistances.TrackC
