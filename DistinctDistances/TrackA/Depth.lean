import DistinctDistances.TrackA.DepthAlgebra

namespace DistinctDistances.TrackA
noncomputable section
open Filter
open scoped BigOperators Classical Topology

/-- Row-sum form of an incidence mass over a subset of the center–carrier product. -/
theorem wide_mass_rows {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (T : Finset β) (B : Finset (α × β)) (hB : B ⊆ P.product T)
    (w : β → ℝ) :
    (∑ a ∈ B, w a.2) = ∑ Y ∈ T, w Y * ((P.filter (fun p => (p, Y) ∈ B)).card : ℝ) := by
  have hfilter : (P.product T).filter (fun a => a ∈ B) = B := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hB h, h⟩⟩
  calc
    (∑ a ∈ B, w a.2) = ∑ a ∈ (P.product T).filter (fun a => a ∈ B), w a.2 := by rw [hfilter]
    _ = ∑ a ∈ P.product T, if a ∈ B then w a.2 else 0 := by rw [Finset.sum_filter]
    _ = ∑ p ∈ P, ∑ Y ∈ T, if (p, Y) ∈ B then w Y else 0 :=
      Finset.sum_product P T (fun a => if a ∈ B then w a.2 else 0)
    _ = ∑ Y ∈ T, ∑ p ∈ P, if (p, Y) ∈ B then w Y else 0 := Finset.sum_comm
    _ = ∑ Y ∈ T, w Y * ((P.filter (fun p => (p, Y) ∈ B)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem wide_incidenceMass_nonneg {d j : ℕ} {regime : Regime d}
    (D : SeparatedDepthData regime j) (i : ℕ) (A : Finset (Point d × AffineVariety d)) :
    0 ≤ D.incidenceMass i A := by
  unfold SeparatedDepthData.incidenceMass
  apply div_nonneg
  · exact Finset.sum_nonneg fun a _ => Nat.cast_nonneg _
  · positivity

theorem wide_incidenceMass_union_le {d j : ℕ} {regime : Regime d}
    (D : SeparatedDepthData regime j) (i : ℕ) (A B : Finset (Point d × AffineVariety d)) :
    D.incidenceMass i (A ∪ B) ≤ D.incidenceMass i A + D.incidenceMass i B := by
  unfold SeparatedDepthData.incidenceMass
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := fun a => (D.mass i a.2 : ℝ))
  have hnn : 0 ≤ ∑ a ∈ A ∩ B, (D.mass i a.2 : ℝ) :=
    Finset.sum_nonneg fun a _ => Nat.cast_nonneg _
  linarith

set_option backward.isDefEq.respectTransparency true in
theorem first_radialCone_homogeneous {n j : ℕ} (V : AffineVariety n) (p : Point n)
    (h : Poly n) (hh : h.IsHomogeneous j) :
    radialConePullback V p h = Polynomial.X ^ j *
      Polynomial.C (Ideal.Quotient.mk V.ideal (MvPolynomial.aeval (radialCoordinate p) h)) := by
  change MvPolynomial.aeval (fun i => Polynomial.X *
    Polynomial.C (Ideal.Quotient.mk V.ideal (radialCoordinate p i))) h = _
  rw [homogeneous_aeval_scale (R := Polynomial (Poly n ⧸ V.ideal)) h hh Polynomial.X
    (fun i => Polynomial.C (Ideal.Quotient.mk V.ideal (radialCoordinate p i)))]
  congr 1
  clear hh
  induction h using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_apply]; rfl
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, hf, MvPolynomial.aeval_X]

theorem first_aeval_radialCoordinate_translation {n : ℕ} (p : Point n) (f : Poly n) :
    MvPolynomial.aeval (radialCoordinate p)
      (OAI.PiExponent.WeightedBezout.translationEquiv p f) = f := by
  change MvPolynomial.aeval (radialCoordinate p)
    (OAI.PiExponent.WeightedBezout.translation p f) = f
  unfold OAI.PiExponent.WeightedBezout.translation
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have : (fun i => MvPolynomial.aeval (radialCoordinate p)
      (MvPolynomial.C (p i) + MvPolynomial.X i)) = MvPolynomial.X := by
    funext i
    simp [radialCoordinate]
  rw [this, MvPolynomial.aeval_X_left_apply]

theorem first_eval_aeval_radialCoordinate {n : ℕ} (p y : Point n) (g : Poly n) :
    MvPolynomial.eval y (MvPolynomial.aeval (radialCoordinate p) g) =
      MvPolynomial.eval (y - p) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
      rw [map_mul, map_mul, hf, MvPolynomial.aeval_X, map_mul, MvPolynomial.eval_X]
      simp [radialCoordinate]

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1000000 in
/-- A first-system equation that vanishes on `V` but not on some joining ray from `p`
certifies that `p` is not a vertex of `V`; radial projection then keeps the dimension. -/
theorem first_radial_dimension_of_ray {n l : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (hl : 1 ≤ l) (hd : V.dimension = l) (p : Point n) (f : Poly n) (hf : f ∈ V.ideal)
    (hproper : ∃ y ∈ V.points, ∃ t : ℂ, MvPolynomial.eval (p + t • (y-p)) f ≠ 0) :
    (radialImage p V).dimension = l := by
  letI : V.ideal.IsPrime := hV
  let R := RadialConeBase V p
  let B := Polynomial (Poly n ⧸ V.ideal)
  letI : (RingHom.ker (radialConePullback V p)).IsPrime := RingHom.ker_isPrime _
  letI := radialConeAlgebra V p
  letI : SMul ℂ R := (inferInstance : Algebra ℂ R).toSMul
  haveI : IsScalarTower ℂ R B := by
    refine IsScalarTower.of_algebraMap_eq (R := ℂ) (S := R) (A := B) ?_
    intro c
    change algebraMap ℂ B c = radialConeInclusion V p (algebraMap ℂ R c)
    exact (radialConeInclusion V p).commutes c |>.symm
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr
    (radialConeInclusion_injective V p)
  haveI : FaithfulSMul ℂ R := (faithfulSMul_iff_algebraMap_injective ℂ R).mpr
    (algebraMap ℂ R).injective
  obtain ⟨x0, hx0, hx0ne⟩ := radial_actual_of_positive_dimension V hV hl hd p
  have hpoints : (radialImage p V).points.Nonempty :=
    ⟨radialProjection p x0 hx0ne, ProjectiveVariety.subset_closure _ ⟨x0, hx0, hx0ne, rfl⟩⟩
  have hincl (g : Poly n) : algebraMap R B (Ideal.Quotient.mk _ g) = radialConePullback V p g := by
    change radialConeInclusion V p (Ideal.Quotient.mk _ g) = _
    exact Ideal.kerLiftAlg_mk _ g
  -- the cone variable is algebraic over the image ring
  let T := OAI.PiExponent.WeightedBezout.translationEquiv p f
  let D := T.totalDegree
  let h : ℕ → Poly n := fun j => MvPolynomial.homogeneousComponent j T
  let P : Polynomial R := ∑ j ∈ Finset.range (D+1),
    Polynomial.monomial (D - j) (Ideal.Quotient.mk (RingHom.ker (radialConePullback V p)) (h j))
  have hPeval : Polynomial.aeval (Polynomial.X : B) P = 0 := by
    simp only [P, map_sum, Polynomial.aeval_monomial, hincl]
    have hterm : ∀ j ∈ Finset.range (D+1),
        radialConePullback V p (h j) * (Polynomial.X : B) ^ (D - j) =
          Polynomial.X ^ D * Polynomial.C (Ideal.Quotient.mk V.ideal
            (MvPolynomial.aeval (radialCoordinate p) (h j))) := by
      intro j hj
      rw [first_radialCone_homogeneous V p (h j)
        (MvPolynomial.homogeneousComponent_isHomogeneous j T)]
      have hjD : j + (D - j) = D := by
        have := Finset.mem_range.mp hj
        omega
      calc _ = (Polynomial.X : B) ^ (j + (D - j)) * Polynomial.C (Ideal.Quotient.mk V.ideal
            (MvPolynomial.aeval (radialCoordinate p) (h j))) := by ring
        _ = _ := by rw [hjD]
    have hsum1 : ∀ j ∈ Finset.range (D+1),
        algebraMap R B (Ideal.Quotient.mk (RingHom.ker (radialConePullback V p)) (h j)) *
          (Polynomial.X : B) ^ (D - j) = Polynomial.X ^ D * Polynomial.C (Ideal.Quotient.mk V.ideal
            (MvPolynomial.aeval (radialCoordinate p) (h j))) := fun j hj => by
      rw [hincl]; exact hterm j hj
    erw [Finset.sum_congr rfl hsum1]
    rw [← Finset.mul_sum, ← map_sum, ← map_sum, ← map_sum]
    have hsum : (∑ j ∈ Finset.range (D+1), h j) = T :=
      MvPolynomial.sum_homogeneousComponent T
    rw [hsum, first_aeval_radialCoordinate_translation,
      Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero, mul_zero]
  have hPne : P ≠ 0 := by
    obtain ⟨y, hy, t, hne⟩ := hproper
    have hQne : rayPolynomial p (y-p) f ≠ 0 := by
      intro h0
      apply hne
      rw [← rayPolynomial_eval, h0]
      simp
    obtain ⟨j, hj⟩ : ∃ j, (rayPolynomial p (y-p) f).coeff j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hQne (Polynomial.ext (fun j => by simpa using hn j))
    have hjD : j ≤ D :=
      (Polynomial.le_natDegree_of_ne_zero hj).trans (rayPolynomial_degree_translated p (y-p) f)
    have hyh : MvPolynomial.eval (y-p) (h j) ≠ 0 := by
      simpa only [rayPolynomial_coeff p (y-p) f j hjD] using hj
    have hmk : Ideal.Quotient.mk (RingHom.ker (radialConePullback V p)) (h j) ≠ 0 := by
      intro h0
      rw [Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker,
        first_radialCone_homogeneous V p (h j)
          (MvPolynomial.homogeneousComponent_isHomogeneous j T)] at h0
      have hC : Polynomial.C (Ideal.Quotient.mk V.ideal
          (MvPolynomial.aeval (radialCoordinate p) (h j))) = 0 := by
        rcases mul_eq_zero.mp h0 with h1 | h1
        · exact absurd h1 (pow_ne_zero _ Polynomial.X_ne_zero)
        · exact h1
      rw [Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at hC
      apply hyh
      rw [← first_eval_aeval_radialCoordinate]
      simpa [MvPolynomial.aeval_eq_eval] using hy _ hC
    intro h0
    apply hmk
    have hcoeff := congrArg (fun Q : Polynomial R => Q.coeff (D - j)) h0
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_eq_single j] at hcoeff
    · simpa using hcoeff
    · intro b hb hbj
      have hbD := Finset.mem_range.mp hb
      have : D - b ≠ D - j := by omega
      simp [this]
    · intro hjn
      exact absurd (Finset.mem_range.mpr (by omega)) hjn
  have hXalg : IsAlgebraic R (Polynomial.X : B) := ⟨P, hPne, hPeval⟩
  -- every element of the cone source is algebraic
  let S := Subalgebra.algebraicClosure R B
  have hconst (c : ℂ) : (algebraMap ℂ B c) ∈ S := by
    rw [IsScalarTower.algebraMap_apply ℂ R B]
    exact S.algebraMap_mem _
  have hCC (c : ℂ) : (Polynomial.C (Ideal.Quotient.mk V.ideal (MvPolynomial.C c)) : B) =
      algebraMap ℂ B c := by
    rw [Polynomial.algebraMap_apply, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
  have hCi (i : Fin n) : (Polynomial.C (Ideal.Quotient.mk V.ideal (MvPolynomial.X i)) : B) ∈ S := by
    have hrad : (Polynomial.C (Ideal.Quotient.mk V.ideal (radialCoordinate p i)) : B) ∈ S := by
      have hmem : (Polynomial.X : B) ∈ nonZeroDivisors B :=
        mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero
      have hprod : IsAlgebraic R ((Polynomial.X : B) *
          Polynomial.C (Ideal.Quotient.mk V.ideal (radialCoordinate p i))) := by
        rw [← radialConePullback_X, ← hincl]
        exact isAlgebraic_algebraMap _
      have h' : IsAlgebraic R (Polynomial.C (Ideal.Quotient.mk V.ideal (radialCoordinate p i)) : B) :=
        IsAlgebraic.of_mul (R := R) (S := B) hmem hXalg hprod
      exact h'
    have hsplit : (Polynomial.C (Ideal.Quotient.mk V.ideal (MvPolynomial.X i)) : B) =
        Polynomial.C (Ideal.Quotient.mk V.ideal (radialCoordinate p i)) + algebraMap ℂ B (p i) := by
      rw [← hCC]
      simp only [radialCoordinate, map_sub]
      ring
    rw [hsplit]
    exact S.add_mem hrad (hconst _)
  have hCall (a : Poly n ⧸ V.ideal) : (Polynomial.C a : B) ∈ S := by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction g using MvPolynomial.induction_on with
    | C c =>
        have : (Polynomial.C (Ideal.Quotient.mk V.ideal (MvPolynomial.C c)) : B) =
            algebraMap ℂ B c := hCC c
        rw [this]
        exact hconst c
    | add f g hf hg => simpa only [map_add] using S.add_mem hf hg
    | mul_X f i hf => simpa only [map_mul] using S.mul_mem hf (hCi i)
  have hXS : (Polynomial.X : B) ∈ S := hXalg
  have hall : Algebra.IsAlgebraic R B := by
    constructor
    intro b
    change b ∈ S
    induction b using Polynomial.induction_on with
    | C a => exact hCall a
    | add f g hf hg => exact S.add_mem hf hg
    | monomial k a hk =>
        rw [pow_succ, ← mul_assoc]
        exact S.mul_mem hk hXS
  have hB : Algebra.trdeg ℂ B = ((l+1 : ℕ) : Cardinal) := by
    rw [GenericFiber.trdeg_polynomial_quotient]
    change (V.dimension : Cardinal) + 1 = _
    rw [hd, Nat.cast_add, Nat.cast_one]
  have hR : Algebra.trdeg ℂ R = ((l+1 : ℕ) : Cardinal) := by
    have hadd := trdeg_add_eq ℂ R (A := B)
    have h0 : Algebra.trdeg R B = 0 := (trdeg_eq_zero_iff (R := R) (A := B)).mpr hall
    rw [h0, add_zero, hB] at hadd
    exact hadd
  rw [← GenericFiber.affineDimension_eq_trdeg, ← radialImage_ideal_eq_cone_ker V hV p
    ⟨x0, hx0, hx0ne⟩] at hR
  change ((radialImage p V).affineCone.dimension : Cardinal) = _ at hR
  rw [ProjectiveVariety.dimension_cone _ hpoints] at hR
  have hnat : (radialImage p V).dimension + 1 = l + 1 := by exact_mod_cast hR
  omega

def firstLineRestriction {n : ℕ} (p v : Point n) : Poly n →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X)

theorem first_eval_lineRestriction {n : ℕ} (p v : Point n) (t : ℂ) (f : Poly n) :
    Polynomial.eval t (firstLineRestriction p v f) = MvPolynomial.aeval (p + t • v) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [firstLineRestriction]
  | add f g hf hg => simp only [map_add, Polynomial.eval_add, hf, hg]
  | mul_X f i hf =>
      rw [map_mul, Polynomial.eval_mul, hf]
      simp only [firstLineRestriction, MvPolynomial.aeval_X, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        map_mul, MvPolynomial.aeval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

theorem first_coeff_zero_lineRestriction {n : ℕ} (p v : Point n) (f : Poly n) :
    (firstLineRestriction p v f).coeff 0 = MvPolynomial.aeval p f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa using first_eval_lineRestriction p v 0 f

theorem first_differential_add {n : ℕ} (f g : Poly n) (p v : Point n) :
    differential (f + g) p v = differential f p v + differential g p v := by
  simp [differential, LinearMap.sum_apply, LinearMap.smul_apply, add_mul,
    Finset.sum_add_distrib]

theorem first_differential_mul_X {n : ℕ} (f : Poly n) (i : Fin n) (p v : Point n) :
    differential (f * MvPolynomial.X i) p v =
      p i * differential f p v + MvPolynomial.aeval p f * v i := by
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, MvPolynomial.pderiv_mul, map_add, map_mul,
    MvPolynomial.aeval_X, MvPolynomial.pderiv_X]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp [Pi.single_apply]

theorem first_coeff_one_lineRestriction {n : ℕ} (p v : Point n) (f : Poly n) :
    (firstLineRestriction p v f).coeff 1 = differential f p v := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [firstLineRestriction, differential, LinearMap.sum_apply]
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg, first_differential_add]
  | mul_X f i hf =>
      rw [map_mul, Polynomial.mul_coeff_one, first_coeff_zero_lineRestriction, hf]
      simp [firstLineRestriction, first_differential_mul_X] <;> ring

/-- A line contained in the point locus is a Zariski tangent direction. -/
theorem first_line_direction_mem_tangent {n : ℕ} (V : AffineVariety n) (p v : Point n)
    (hline : ∀ t : ℂ, p + t • v ∈ V.points) : v ∈ V.tangentSpace p := by
  change v ∈ ⨅ f : V.ideal, LinearMap.ker (differential f.val p)
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro f
  have hz : firstLineRestriction p v f.val = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hall : {t : ℂ | Polynomial.IsRoot (firstLineRestriction p v f.val) t} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro t
      change Polynomial.eval t (firstLineRestriction p v f.val) = 0
      rw [first_eval_lineRestriction]
      exact hline t f.val f.property
    rw [hall]
    exact Set.infinite_univ
  rw [← first_coeff_one_lineRestriction, hz, Polynomial.coeff_zero]

theorem first_ideal_ne_bot {n l : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (hd : V.dimension = l) (hl : l < n) : V.ideal ≠ ⊥ := by
  intro hbot
  letI : V.ideal.IsPrime := hV
  have h1 : (V.dimension : Cardinal) = Algebra.trdeg ℂ (Poly n ⧸ V.ideal) :=
    GenericFiber.affineDimension_eq_trdeg V.ideal
  let e : (Poly n ⧸ V.ideal) ≃ₐ[ℂ] Poly n :=
    (Ideal.quotientEquivAlgOfEq ℂ hbot).trans (AlgEquiv.quotientBot ℂ (Poly n))
  rw [e.trdeg_eq, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast,
    hd] at h1
  have : l = n := by exact_mod_cast h1
  omega

theorem first_exists_outside {n : ℕ} (V : AffineVariety n) (hV : V.ideal ≠ ⊥) :
    ∃ x : Point n, x ∉ V.points := by
  by_contra h
  push Not at h
  apply hV
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  apply MvPolynomial.funext
  intro x
  simpa [MvPolynomial.aeval_eq_eval] using h x f hf

theorem first_mem_points_span {n : ℕ} (E : Set (Poly n)) (z : Point n)
    (hz : ∀ f ∈ E, MvPolynomial.eval z f = 0) :
    z ∈ (AffineVariety.ofIdeal (Ideal.span E)).points := by
  rw [AffineVariety.points_ofIdeal, MvPolynomial.mem_zeroLocus_iff]
  intro f hf
  have hle : Ideal.span E ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
    rw [Ideal.span_le]
    intro g hg
    simpa [MvPolynomial.aeval_eq_eval] using hz g hg
  simpa using hle hf

theorem first_mass_total {d j : ℕ} {regime : Regime d} (D : SeparatedDepthData regime j)
    (i : ℕ) : (∑ Y ∈ D.carriers i, (D.mass i Y : ℝ)) = (D.targets i).card := by
  have hmaps : ∀ q ∈ D.targets i, D.owner i q ∈ D.carriers i :=
    fun q hq => D.owner_member i q hq
  have := (Finset.card_eq_sum_card_fiberwise (s := D.targets i) (t := D.carriers i)
    (f := D.owner i) hmaps).symm
  exact_mod_cast (by simpa [SeparatedDepthData.mass] using this)

/-- Double counting of ray-contained incidences through their owned targets. -/
theorem first_mass_by_targets {d j : ℕ} {regime : Regime d} (D : SeparatedDepthData regime j)
    (i : ℕ) (A : Finset (Point d × AffineVariety d))
    (hA : A ⊆ (D.centers i).product (D.carriers i)) :
    (∑ a ∈ A, D.mass i a.2) ≤
      ∑ q ∈ D.targets i, ((D.centers i).filter (fun p => (p, D.owner i q) ∈ A)).card := by
  have hswap : (∑ a ∈ A, D.mass i a.2) =
      ∑ q ∈ D.targets i, (A.filter (fun a => D.owner i q = a.2)).card := by
    simp only [SeparatedDepthData.mass, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap]
  apply Finset.sum_le_sum
  intro q _
  apply Finset.card_le_card_of_injOn (fun a => a.1)
  · intro a ha
    obtain ⟨haA, hq⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (hA haA)).1, ?_⟩
    have : a = (a.1, D.owner i q) := Prod.ext rfl hq.symm
    rw [← this]
    exact haA
  · intro a ha b hb hab
    obtain ⟨_, hqa⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hqb⟩ := Finset.mem_filter.mp hb
    exact Prod.ext hab (hqa.symm.trans hqb)

set_option maxHeartbeats 2000000 in
/-- `dep:first-R`, depth.tex:90–168. Weighted dimension/multiplicity deletion
and the first-cut degree bound are independent of later density thresholds. -/
theorem dep_first_depth {d j : ℕ} {regime : Regime d}
    (D : SeparatedDepthData regime j) (hD : D.Hypotheses) :
    D.NegligibleSafeDepth D.firstRate := by
  classical
  intro η hη
  rcases hD with ⟨_, hflat, hinit, hfirst, _, _⟩
  obtain ⟨E, badT, _, hbadTsmall, hEdeg, hsub, hsmooth⟩ := hfirst
  let l : ℕ := d - j
  have hl : 1 ≤ l := by have := D.j_lt; omega
  have hld : l < d := by have := D.j_pos; have := D.j_lt; omega
  let VE (i : ℕ) : AffineVariety d := AffineVariety.ofIdeal (Ideal.span (E i : Set (Poly d)))
  have hEmem (i : ℕ) (Y : AffineVariety d) (hY : Y ∈ D.carriers i) (f : Poly d)
      (hf : f ∈ E i) : f ∈ Y.ideal :=
    hsub i Y hY (Ideal.le_radical (Ideal.subset_span hf))
  let rayBad (i : ℕ) : Finset (Point d × AffineVariety d) :=
    ((D.centers i).product (D.carriers i)).filter (fun a =>
      ∀ f ∈ E i, ∀ y ∈ a.2.points, ∀ t : ℂ, MvPolynomial.eval (a.1 + t • (y - a.1)) f = 0)
  let multBad (i : ℕ) : Finset (Point d × AffineVariety d) :=
    ((D.centers i).product (D.carriers i)).filter (fun a =>
      a.2.degree / 2 < a.2.multiplicity a.1)
  let bad (i : ℕ) : Finset (Point d × AffineVariety d) := rayBad i ∪ multBad i
  -- high-multiplicity tests
  let highGood (i : ℕ) (Y : AffineVariety d) (g : Poly d) : Prop :=
    g ≠ 0 ∧ g.totalDegree ≤ 2*(d+1) ∧
      ∀ p ∈ D.centers i, Y.degree / 2 < Y.multiplicity p → MvPolynomial.eval p g = 0
  have highExists : ∀ i, ∀ Y ∈ D.carriers i, ∃ g, highGood i Y g := by
    intro i Y hY
    obtain ⟨hYirr, hYdim⟩ := D.carrier_pure i Y hY
    have hbot := first_ideal_ne_bot Y hYirr hYdim hld
    obtain ⟨x, hx⟩ := first_exists_outside Y hbot
    let S := (D.centers i).filter (fun p => Y.degree / 2 < Y.multiplicity p)
    have hS : ∀ p ∈ S, p ∈ Y.points ∧ Y.degree / 2 < Y.multiplicity p := by
      intro p hp
      have hlt := (Finset.mem_filter.mp hp).2
      refine ⟨?_, hlt⟩
      by_contra hpY
      have h0 := Y.multiplicity_eq_zero_off p hpY
      have hdeg := Y.one_le_degree (Ideal.IsPrime.ne_top hYirr)
      rw [h0] at hlt
      linarith
    obtain ⟨g, hgdeg, hgS, hgx⟩ := poly_high_multiplicity Y hYirr hbot S hS x hx
    refine ⟨g, ?_, hgdeg, ?_⟩
    · intro h0
      apply hgx
      simp [h0]
    · intro p hp hlt
      exact hgS p (Finset.mem_filter.mpr ⟨hp, hlt⟩)
  let highTest (i : ℕ) (Y : AffineVariety d) :
      {f : Poly d // f ≠ 0 ∧ f.totalDegree ≤ 2*(d+1)} :=
    if h : ∃ g, highGood i Y g then ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩
    else ⟨1, one_ne_zero, by simp⟩
  have hmultSmall : Framework.LittleO
      (fun i => D.incidenceMass i (multBad i)) (fun _ => 1) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    filter_upwards [hinit (2*(d+1)) ε hε] with i hcap
    rw [Real.norm_eq_abs, abs_of_nonneg (wide_incidenceMass_nonneg D i _), norm_one, mul_one]
    unfold SeparatedDepthData.incidenceMass
    apply div_le_of_le_mul₀ (by positivity) hε.le
    rw [wide_mass_rows (D.centers i) (D.carriers i) (multBad i) (Finset.filter_subset _ _)
      (fun Y => (D.mass i Y : ℝ))]
    calc
      (∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) *
          (((D.centers i).filter (fun p => (p, Y) ∈ multBad i)).card : ℝ)) ≤
          ∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) * (ε * (D.centers i).card) := by
        apply Finset.sum_le_sum
        intro Y hY
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have h1 := hcap (highTest i Y)
        rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)] at h1
        refine le_trans ?_ h1
        have hex := highExists i Y hY
        exact_mod_cast Finset.card_le_card (by
          intro p hp
          obtain ⟨hpc, hpbad⟩ := Finset.mem_filter.mp hp
          refine Finset.mem_filter.mpr ⟨hpc, ?_⟩
          have hlt := (Finset.mem_filter.mp hpbad).2
          change MvPolynomial.eval p (highTest i Y).val = 0
          simp only [highTest, dif_pos hex]
          exact hex.choose_spec.2.2 p hpc hlt)
      _ = ε * ((D.centers i).card * (D.targets i).card) := by
        rw [← Finset.sum_mul, first_mass_total]
        ring
  -- ray-contained incidences
  have hdpos : 0 < d := by omega
  let flatOf (i : ℕ) (q : Point d) : ProperFlat d :=
    if h : Module.finrank ℂ ((VE i).tangentSpace q) < d then ⟨(q, (VE i).tangentSpace q), h⟩
    else ⟨(0, ⊥), by simpa using hdpos⟩
  have hraySmall : Framework.LittleO
      (fun i => D.incidenceMass i (rayBad i)) (fun _ => 1) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have hε2 : 0 < ε/2 := by positivity
    filter_upwards [hflat (ε/2) hε2, hbadTsmall.def hε2, hsmooth] with i hcap hbadi hsm
    rw [Real.norm_eq_abs, abs_of_nonneg (wide_incidenceMass_nonneg D i _), norm_one, mul_one]
    unfold SeparatedDepthData.incidenceMass
    apply div_le_of_le_mul₀ (by positivity) hε.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _)] at hbadi
    have hdouble := first_mass_by_targets D i (rayBad i) (Finset.filter_subset _ _)
    have hdoubleR : (∑ a ∈ rayBad i, (D.mass i a.2 : ℝ)) ≤
        ∑ q ∈ D.targets i,
          (((D.centers i).filter (fun p => (p, D.owner i q) ∈ rayBad i)).card : ℝ) := by
      exact_mod_cast hdouble
    have hrow : ∀ q ∈ D.targets i,
        (((D.centers i).filter (fun p => (p, D.owner i q) ∈ rayBad i)).card : ℝ) ≤
          (if q ∈ badT i then ((D.centers i).card : ℝ) else 0) +
            ε/2 * (D.centers i).card := by
      intro q hq
      by_cases hqb : q ∈ badT i
      · rw [if_pos hqb]
        have : (((D.centers i).filter (fun p => (p, D.owner i q) ∈ rayBad i)).card : ℝ) ≤
            (D.centers i).card := by exact_mod_cast Finset.card_filter_le _ _
        have : (0 : ℝ) ≤ ε/2 * (D.centers i).card := by positivity
        linarith
      · rw [if_neg hqb, zero_add]
        obtain ⟨hsmq, hlocq⟩ := hsm q hq hqb
        have hfin : Module.finrank ℂ ((VE i).tangentSpace q) < d := by
          rw [hsmq.2]
          exact hlocq
        have h1 := hcap (flatOf i q)
        rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)] at h1
        refine le_trans ?_ h1
        exact_mod_cast Finset.card_le_card (by
          intro p hp
          obtain ⟨hpc, hpbad⟩ := Finset.mem_filter.mp hp
          refine Finset.mem_filter.mpr ⟨hpc, ?_⟩
          have hray := (Finset.mem_filter.mp hpbad).2
          have hline : ∀ s : ℂ, q + s • (p - q) ∈ (VE i).points := by
            intro s
            apply first_mem_points_span
            intro f hf
            have h := hray f hf q (D.owner_contains i q hq) (1 - s)
            have heq : p + (1 - s) • (q - p) = q + s • (p - q) := by module
            rw [heq] at h
            exact h
          have htan := first_line_direction_mem_tangent (VE i) q (p - q) hline
          simp only [flatOf, dif_pos hfin]
          exact htan)
    have hbadCard : (((D.targets i).filter (fun q => q ∈ badT i)).card : ℝ) ≤
        ε/2 * (D.targets i).card := by
      refine le_trans ?_ hbadi
      exact_mod_cast Finset.card_le_card (fun q hq => (Finset.mem_filter.mp hq).2)
    calc
      (∑ a ∈ rayBad i, (D.mass i a.2 : ℝ)) ≤ ∑ q ∈ D.targets i,
          ((if q ∈ badT i then ((D.centers i).card : ℝ) else 0) +
            ε/2 * (D.centers i).card) := hdoubleR.trans (Finset.sum_le_sum hrow)
      _ = (((D.targets i).filter (fun q => q ∈ badT i)).card : ℝ) * (D.centers i).card +
            (D.targets i).card * (ε/2 * (D.centers i).card) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul]
      _ ≤ ε/2 * (D.targets i).card * (D.centers i).card +
            (D.targets i).card * (ε/2 * (D.centers i).card) := by
        gcongr
      _ = ε * ((D.centers i).card * (D.targets i).card) := by ring
  have hbadSmall : Framework.LittleO (fun i => D.incidenceMass i (bad i)) (fun _ => 1) := by
    have hsum := hraySmall.add hmultSmall
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hsum
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with i
    have h1 := wide_incidenceMass_union_le D i (rayBad i) (multBad i)
    have n1 := wide_incidenceMass_nonneg D i (rayBad i)
    have n2 := wide_incidenceMass_nonneg D i (multBad i)
    have n0 := wide_incidenceMass_nonneg D i (bad i)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg n0, abs_of_nonneg (by positivity)]
    change D.incidenceMass i (rayBad i ∪ multBad i) ≤ 1 * _
    linarith
  have hbadSubset (i : ℕ) : bad i ⊆ (D.centers i).product (D.carriers i) := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (Finset.mem_filter.mp ha).1
    · exact (Finset.mem_filter.mp ha).1
  refine ⟨bad, hbadSubset, hbadSmall, ?_⟩
  filter_upwards [hEdeg η hη] with i hdeg
  intro p hp Y hY
  change Y ∈ (D.carriers i).filter (fun Y => (p,Y) ∉ bad i) at hY
  rcases Finset.mem_filter.mp hY with ⟨hYc, hnot⟩
  have hpY : (p, Y) ∈ (D.centers i).product (D.carriers i) :=
    Finset.mem_product.mpr ⟨hp, hYc⟩
  have hnray : ¬ (∀ f ∈ E i, ∀ y ∈ Y.points, ∀ t : ℂ,
      MvPolynomial.eval (p + t • (y - p)) f = 0) := fun h =>
    hnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpY, h⟩))
  push Not at hnray
  obtain ⟨f, hfE, y, hy, t, hft⟩ := hnray
  have hnmult : ¬ (Y.degree / 2 < Y.multiplicity p) := fun h =>
    hnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpY, h⟩))
  obtain ⟨hYirr, hYdim⟩ := D.carrier_pure i Y hYc
  have hdim := first_radial_dimension_of_ray Y hYirr hl hYdim p f (hEmem i Y hYc f hfE)
    ⟨y, hy, t, hft⟩
  refine ⟨hdim, not_lt.mp hnmult, ?_⟩
  have hJ : AffineFamily.IsPure (D.retained i (bad i) p) l :=
    fun Z hZ => D.carrier_pure i Z (Finset.mem_filter.mp hZ).1
  have hdepth := dep_first_cut_depth (D.retained i (bad i) p) l hl hJ Y hY p hdim f
    f.totalDegree le_rfl (fun Z hZ => hEmem i Z (Finset.mem_filter.mp hZ).1 f hfE)
    ⟨y, hy, t, hft⟩
  calc
    (groupDepth p (D.retained i (bad i) p) Y : ℝ) ≤ f.totalDegree := by exact_mod_cast hdepth
    _ ≤ D.firstRate i * Real.exp (η * D.s i) := hdeg ⟨f, hfE⟩

set_option maxHeartbeats 500000 in
/-- `dep:narrow-R`, depth.tex:170–218. Weighted Markov on the isolated-root count. -/
theorem dep_narrow_depth {d j : ℕ} {regime : Regime d}
    (D : SeparatedDepthData regime j) (hD : D.Hypotheses)
    (hseparated : Tendsto (fun i => D.v i / D.s i) atTop (𝓝 0)) :
    D.NegligibleSafeDepth D.narrowRate := by
  classical
  intro η hη
  let l : ℕ := d-j
  let η₀ : ℝ := η/2
  let δ : ℝ := η / (8 * ((l : ℝ) + 2))
  have hl : 1 ≤ l := by dsimp [l]; have := D.j_lt; omega
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδbudget : δ * ((l : ℝ) + 2) = η/8 := by
    dsimp [δ]
    field_simp
  have hδle : δ ≤ η/8 := by
    have hl' : 1 ≤ (l : ℝ) + 2 := by exact_mod_cast (by omega : 1 ≤ l+2)
    dsimp [δ]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hfirst := dep_first_depth D hD
  rcases hD with ⟨hbudget, _, _, _, hNarrowInput, _⟩
  obtain ⟨L, E, hNarrowData, hLupper⟩ := hNarrowInput hseparated
  obtain ⟨C, hC, hrootCount⟩ := dep_narrow_root_count d
  obtain ⟨bad₁, hbad₁Subset, hbad₁Small, hsafe₁⟩ := hfirst η₀ hη₀
  let tail : Finset (Fin d) := Finset.univ.filter (fun t => j ≤ t.val)
  let tailSum : ℝ := ∑ t ∈ tail, D.b t
  let thresh : ℕ → ℝ := fun i => D.narrowRate i * Real.exp (η₀ * D.s i)
  let cutoff : ℕ → ℕ := fun i => Nat.floor (thresh i)
  let goodCenters (i : ℕ) (Y : AffineVariety d) : Finset (Point d) :=
    (D.centers i).filter (fun p => (p,Y) ∉ bad₁ i)
  let highCenters (i : ℕ) (Y : AffineVariety d) : Finset (Point d) :=
    (goodCenters i Y).filter (fun p => cutoff i < groupDepth p (D.carriers i) Y)
  let bad₂ (i : ℕ) : Finset (Point d × AffineVariety d) :=
    ((D.centers i).product (D.carriers i)).filter (fun a =>
      a ∉ bad₁ i ∧ cutoff i < groupDepth a.1 (D.carriers i) a.2)
  let bad (i : ℕ) : Finset (Point d × AffineVariety d) := bad₁ i ∪ bad₂ i
  have hmassTotalNat (i : ℕ) :
      (∑ Y ∈ D.carriers i, D.mass i Y) = (D.targets i).card := by
    have hmaps : ∀ q ∈ D.targets i, D.owner i q ∈ D.carriers i :=
      fun q hq => D.owner_member i q hq
    simpa [SeparatedDepthData.mass] using
      (Finset.card_eq_sum_card_fiberwise (s := D.targets i) (t := D.carriers i)
        (f := D.owner i) hmaps).symm
  have hmassTotalReal (i : ℕ) :
      (∑ Y ∈ D.carriers i, (D.mass i Y : ℝ)) = (D.targets i).card := by
    exact_mod_cast hmassTotalNat i
  have hcentersPos : ∀ᶠ i in atTop, 1 ≤ (D.centers i).card := by
    filter_upwards [D.source_size.1 1 (by norm_num)] with i hi
    have hpos : (0 : ℝ) < regime.N i * Real.exp (-1 * D.v i) :=
      mul_pos (regime.N_pos i) (Real.exp_pos _)
    have hcard : (0 : ℝ) < (D.centers i).card := lt_of_lt_of_le hpos (hi ())
    exact_mod_cast hcard
  have htargetsPos : ∀ᶠ i in atTop, 1 ≤ (D.targets i).card := by
    filter_upwards [D.target_size.1 1 (by norm_num)] with i hi
    have hpos : (0 : ℝ) < regime.N i * Real.exp (-1 * D.s i) :=
      mul_pos (regime.N_pos i) (Real.exp_pos _)
    have hcard : (0 : ℝ) < (D.targets i).card := lt_of_lt_of_le hpos (hi ())
    exact_mod_cast hcard
  have hgoodEventually : ∀ᶠ i in atTop,
      ∀ p ∈ D.centers i, ∀ Y ∈ D.carriers i, (p,Y) ∉ bad₁ i →
        (radialImage p Y).dimension = l ∧ Y.multiplicity p ≤ Y.degree / 2 := by
    filter_upwards [hsafe₁] with i hi
    intro p hp Y hY hpnot
    exact ⟨(hi p hp Y (Finset.mem_filter.mpr ⟨hY, hpnot⟩)).1,
      (hi p hp Y (Finset.mem_filter.mpr ⟨hY, hpnot⟩)).2.1⟩
  have hdegreeBase (i : ℕ) : regime.B i ^ d = regime.N i := by
    rw [Regime.B, ← Real.rpow_natCast, ← Real.rpow_mul (regime.N_pos i).le]
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast (show 0 < d by have hd := regime.dimension_ge_three; omega)
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
    have hexp : (1 / (d : ℝ)) * (d : ℝ) = 1 := by field_simp [hdne]
    rw [hexp]
    exact Real.rpow_one _
  have hcutProducts (i : ℕ) :
      ∏ t ∈ Finset.univ, D.cutDegree i t = regime.B i ^ d := by
    have hprodB :
        (∏ t ∈ (Finset.univ : Finset (Fin d)), regime.B i) = regime.B i ^ d := by simp
    have hsumExp :
        (∏ t ∈ (Finset.univ : Finset (Fin d)), Real.exp (D.b t * D.s i)) = 1 := by
      rw [← Real.exp_sum]
      have hsum : (∑ t : Fin d, D.b t * D.s i) = 0 := by
        rw [← Finset.sum_mul, D.b_sum]
        simp
      rw [hsum, Real.exp_zero]
    calc
      ∏ t ∈ Finset.univ, D.cutDegree i t =
          (∏ t ∈ Finset.univ, regime.B i) *
            ∏ t ∈ Finset.univ, Real.exp (D.b t * D.s i) := by
        simp only [SeparatedDepthData.cutDegree, Finset.prod_mul_distrib]
        rfl
      _ = regime.B i ^ d * 1 := by rw [hprodB, hsumExp]
      _ = regime.B i ^ d := by ring
  have hbudgetTail (i : ℕ) : D.degreeBudget i * D.tailBudget i = regime.N i := by
    have hsplit :
        (∏ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), D.cutDegree i t) *
          ∏ t ∈ Finset.univ.filter (fun t : Fin d => j ≤ t.val), D.cutDegree i t =
        ∏ t ∈ Finset.univ, D.cutDegree i t := by
      simpa only [not_lt] using
        (Finset.prod_filter_mul_prod_filter_not (Finset.univ)
          (fun t : Fin d => t.val < j) (fun t => D.cutDegree i t))
    calc
      D.degreeBudget i * D.tailBudget i =
          (∏ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), D.cutDegree i t) *
            ∏ t ∈ Finset.univ.filter (fun t : Fin d => j ≤ t.val), D.cutDegree i t := by
        rfl
      _ = ∏ t ∈ Finset.univ, D.cutDegree i t := hsplit
      _ = regime.B i ^ d := hcutProducts i
      _ = regime.N i := hdegreeBase i
  have htailFilter : tail = Finset.Ici (⟨j, D.j_lt⟩ : Fin d) := by
    ext t
    simp [tail, Finset.mem_Ici, Fin.le_iff_val_le_val]
  have htailCard : tail.card = d-j := by
    rw [htailFilter, Fin.card_Ici]
  have htailFormula (i : ℕ) :
      D.tailBudget i = regime.B i ^ (d-j) * Real.exp (tailSum * D.s i) := by
    have hprodB : (∏ t ∈ tail, regime.B i) = regime.B i ^ (d-j) := by
      simp [htailCard]
    have hprodExp :
        (∏ t ∈ tail, Real.exp (D.b t * D.s i)) = Real.exp (tailSum * D.s i) := by
      rw [← Real.exp_sum]
      rw [← Finset.sum_mul]
    calc
      D.tailBudget i =
          (∏ t ∈ tail, regime.B i) * ∏ t ∈ tail, Real.exp (D.b t * D.s i) := by
        simp [SeparatedDepthData.tailBudget, SeparatedDepthData.cutDegree, tail,
          Finset.prod_mul_distrib]
      _ = regime.B i ^ (d-j) * Real.exp (tailSum * D.s i) := by rw [hprodB, hprodExp]
  have htailNarrow (i : ℕ) :
      D.tailBudget i * D.narrowRate i = regime.B i ^ (l+1) := by
    calc
      D.tailBudget i * D.narrowRate i =
          regime.B i ^ (d-j) * Real.exp (tailSum * D.s i) *
            (regime.B i * Real.exp (-D.s i * tailSum)) := by
        rw [htailFormula i]
        simp [SeparatedDepthData.narrowRate, tail, tailSum]
      _ = regime.B i ^ (d-j) * regime.B i *
          (Real.exp (tailSum * D.s i) * Real.exp (-D.s i * tailSum)) := by ring
          _ = regime.B i ^ (d-j) * regime.B i := by
        have he : Real.exp (tailSum * D.s i) * Real.exp (-D.s i * tailSum) = 1 := by
          rw [← Real.exp_add]
          have hsum : tailSum * D.s i + -D.s i * tailSum = 0 := by ring
          rw [hsum, Real.exp_zero]
        rw [he, mul_one]
      _ = regime.B i ^ (l+1) := by
        have hlEq : d-j = l := rfl
        rw [hlEq, pow_succ]
  have hdegreeLBase (i : ℕ) :
      D.degreeBudget i * regime.B i ^ (l+1) = regime.N i * D.narrowRate i := by
    calc
      D.degreeBudget i * regime.B i ^ (l+1) =
          D.degreeBudget i * (D.tailBudget i * D.narrowRate i) := by rw [htailNarrow]
      _ = regime.N i * D.narrowRate i := by rw [← mul_assoc, hbudgetTail]
  have hthreshFormula (i : ℕ) :
      thresh i = regime.B i * Real.exp ((η₀-tailSum) * D.s i) := by
    calc
      thresh i = regime.B i *
          (Real.exp (-D.s i * tailSum) * Real.exp (η₀ * D.s i)) := by
        change regime.B i * Real.exp (-D.s i * tailSum) * Real.exp (η₀ * D.s i) =
          regime.B i * (Real.exp (-D.s i * tailSum) * Real.exp (η₀ * D.s i))
        ring
      _ = regime.B i * Real.exp (-D.s i * tailSum + η₀ * D.s i) := by
        rw [← Real.exp_add]
      _ = regime.B i * Real.exp ((η₀-tailSum) * D.s i) := by
        congr 2
        ring
  have hRateFormula (i : ℕ) :
      D.narrowRate i = regime.B i * Real.exp (-D.s i * tailSum) := by
    unfold SeparatedDepthData.narrowRate
    simp [tail, tailSum]
  let c : ℝ := η₀ - tailSum
  have hlogB : Tendsto (fun i => Real.log (regime.B i)) atTop atTop :=
    Real.tendsto_log_atTop.comp regime.B_tendsto
  have hlogLarge : ∀ᶠ i in atTop, Real.log (regime.B i) ≥ Real.log 4 :=
    hlogB.eventually (Ici_mem_atTop (Real.log 4))
  let κ : ℝ := 1 / (2 * (|c| + 1))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hcκ : |c| * κ < 1/2 := by
    dsimp [κ]
    field_simp
    nlinarith [abs_nonneg c]
  have hsSmall : ∀ᶠ i in atTop, ‖D.s i‖ ≤ κ * ‖Real.log (regime.B i)‖ :=
    D.s_small.def hκ
  have hTtwo : ∀ᶠ i in atTop, 2 ≤ thresh i := by
    filter_upwards [hlogLarge, hsSmall] with i hlog hsmall
    have hlogPos : 0 < Real.log (regime.B i) := by
      exact lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 4)) hlog
    have hsAbs : |D.s i| ≤ κ * Real.log (regime.B i) := by
      simpa [Real.norm_eq_abs, abs_of_pos hlogPos] using hsmall
    have hcoeff : |c| * κ * Real.log (regime.B i) <
        (1/2 : ℝ) * Real.log (regime.B i) :=
      mul_lt_mul_of_pos_right hcκ hlogPos
    have hcs : -(|c| * |D.s i|) ≤ c * D.s i := by
      simpa [abs_mul] using (neg_abs_le (c * D.s i))
    have hlower : -(1/2 : ℝ) * Real.log (regime.B i) ≤ c * D.s i := by
      have hprod : |c| * |D.s i| ≤ |c| * κ * Real.log (regime.B i) := by
        calc
          |c| * |D.s i| ≤ |c| * (κ * Real.log (regime.B i)) :=
            mul_le_mul_of_nonneg_left hsAbs (abs_nonneg c)
          _ = |c| * κ * Real.log (regime.B i) := by ring
      linarith
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have hhalfLog : Real.log 2 ≤ (1/2 : ℝ) * Real.log (regime.B i) := by
      calc
        Real.log 2 = (1/2 : ℝ) * Real.log 4 := by rw [hlog4]; ring
        _ ≤ (1/2 : ℝ) * Real.log (regime.B i) :=
          mul_le_mul_of_nonneg_left hlog (by norm_num)
    have hExpHalf : 2 ≤ Real.exp ((1/2 : ℝ) * Real.log (regime.B i)) := by
      have h := Real.exp_le_exp.mpr hhalfLog
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
      exact h
    rw [hthreshFormula i]
    have hbase : regime.B i * Real.exp (-(1/2 : ℝ) * Real.log (regime.B i)) =
        Real.exp ((1/2 : ℝ) * Real.log (regime.B i)) := by
      calc
        regime.B i * Real.exp (-(1/2 : ℝ) * Real.log (regime.B i)) =
            Real.exp (Real.log (regime.B i)) *
              Real.exp (-(1/2 : ℝ) * Real.log (regime.B i)) := by
                exact congrArg (fun x : ℝ => x * Real.exp (-(1/2 : ℝ) * Real.log (regime.B i)))
                  (Real.exp_log (regime.B_pos i)).symm
        _ = Real.exp (Real.log (regime.B i) + -(1/2 : ℝ) * Real.log (regime.B i)) := by
          rw [← Real.exp_add]
        _ = Real.exp ((1/2 : ℝ) * Real.log (regime.B i)) := by congr 1 <;> ring
    calc
      2 ≤ Real.exp ((1/2 : ℝ) * Real.log (regime.B i)) := hExpHalf
      _ = regime.B i * Real.exp (-(1/2 : ℝ) * Real.log (regime.B i)) := hbase.symm
      _ ≤ regime.B i * Real.exp (c * D.s i) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlower) (regime.B_pos i).le
  have hcutoffLower : ∀ᶠ i in atTop, thresh i / 2 ≤ (cutoff i : ℝ) := by
    filter_upwards [hTtwo] with i hi
    have hfloor : thresh i < (cutoff i : ℝ) + 1 := by
      exact_mod_cast (Nat.lt_floor_add_one (thresh i))
    dsimp [cutoff]
    linarith
  have hcutoffPos : ∀ᶠ i in atTop, 0 < (cutoff i : ℝ) := by
    filter_upwards [hcutoffLower] with i hi
    have ht : 0 < thresh i := by
      have hrate : 0 < D.narrowRate i := by
        dsimp [SeparatedDepthData.narrowRate]
        exact mul_pos (regime.B_pos i) (Real.exp_pos _)
      dsimp [thresh]
      exact mul_pos hrate (Real.exp_pos _)
    have : 0 < thresh i / 2 := by positivity
    linarith
  have hdegreeBudgetPos (i : ℕ) : 0 < D.degreeBudget i := by
    unfold SeparatedDepthData.degreeBudget SeparatedDepthData.cutDegree
    apply Finset.prod_pos
    intro t ht
    exact mul_pos (regime.B_pos i) (Real.exp_pos _)
  have hcarrierDegreeNonneg (i : ℕ) :
      0 ≤ (AffineFamily.degree (D.carriers i) : ℝ) := by
    have hq : (0 : ℚ) ≤ AffineFamily.degree (D.carriers i) := by
      unfold AffineFamily.degree
      apply Finset.sum_nonneg
      intro Y hY
      have hYprime := (D.carrier_pure i Y hY).1
      have hdegree : (1 : ℚ) ≤ Y.degree := by
        simpa [AffineVariety.degree] using
          OAI.QuarticPowerFree.one_le_affineDegree Y.ideal hYprime.ne_top
      linarith
    exact_mod_cast hq
  have hcountBound (i : ℕ) (Y : AffineVariety d) (hY : Y ∈ D.carriers i)
      (hsafeI : ∀ p ∈ D.centers i, ∀ Z ∈ D.carriers i, (p,Z) ∉ bad₁ i →
        (radialImage p Z).dimension = l ∧ Z.multiplicity p ≤ Z.degree/2) :
      ((highCenters i Y).card : ℝ) * (cutoff i : ℝ) ≤
        (C : ℝ) * (AffineFamily.degree (D.carriers i) : ℝ) * (L i : ℝ)^(l+1) := by
    have hSsubset : goodCenters i Y ⊆ D.centers i := Finset.filter_subset _ _
    have hSisolated : IsolatedPoints (E i : Set (Poly d)) (goodCenters i Y) := by
      intro p hp
      exact (hNarrowData i).2.2 p (hSsubset hp)
    have hSimages : ∀ p ∈ goodCenters i Y, (radialImage p Y).dimension = l := by
      intro p hp
      have hpcenter := hSsubset hp
      have hpair := (Finset.mem_filter.mp hp).2
      exact (hsafeI p hpcenter Y hY hpair).1
    have hroots := hrootCount (D.carriers i) l hl (D.carrier_pure i) Y hY
      (goodCenters i Y) (E i : Set (Poly d)) (L i) (hNarrowData i).1
      (hNarrowData i).2.1 hSisolated hSimages
    have hsumLower :
        ((highCenters i Y).card : ℚ) * (cutoff i : ℚ) ≤
          ∑ p ∈ highCenters i Y, ((groupDepth p (D.carriers i) Y - 1 : ℕ) : ℚ) := by
      calc
        _ = ∑ _p ∈ highCenters i Y, (cutoff i : ℚ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun p hp => by
          have hlt := (Finset.mem_filter.mp hp).2
          have hnat : cutoff i ≤ groupDepth p (D.carriers i) Y - 1 := by omega
          exact_mod_cast hnat
    have hsumUpper :
        (∑ p ∈ highCenters i Y, ((groupDepth p (D.carriers i) Y - 1 : ℕ) : ℚ)) ≤
          ∑ p ∈ goodCenters i Y, ((groupDepth p (D.carriers i) Y - 1 : ℕ) : ℚ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp hpn
      positivity
    have hcountQ :
        ((highCenters i Y).card : ℚ) * (cutoff i : ℚ) ≤
          C * AffineFamily.degree (D.carriers i) * (L i : ℚ)^(l+1) := hsumLower.trans (hsumUpper.trans hroots)
    exact_mod_cast hcountQ
  have hbad₂Mass (i : ℕ) :
      (∑ a ∈ bad₂ i, (D.mass i a.2 : ℝ)) =
        ∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) * (highCenters i Y).card := by
    have hbad₂Sub : bad₂ i ⊆ (D.centers i).product (D.carriers i) := Finset.filter_subset _ _
    have hfilter : ((D.centers i).product (D.carriers i)).filter (fun a => a ∈ bad₂ i) = bad₂ i := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro ha
        exact ⟨hbad₂Sub ha, ha⟩
    calc
      (∑ a ∈ bad₂ i, (D.mass i a.2 : ℝ)) =
          ∑ a ∈ ((D.centers i).product (D.carriers i)).filter (fun a => a ∈ bad₂ i),
            (D.mass i a.2 : ℝ) := by rw [hfilter]
      _ = ∑ a ∈ (D.centers i).product (D.carriers i),
          if a ∈ bad₂ i then (D.mass i a.2 : ℝ) else 0 := by rw [Finset.sum_filter]
      _ = ∑ p ∈ D.centers i, ∑ Y ∈ D.carriers i,
          if (p,Y) ∈ bad₂ i then (D.mass i Y : ℝ) else 0 :=
        Finset.sum_product (D.centers i) (D.carriers i)
          (fun a => if a ∈ bad₂ i then (D.mass i a.2 : ℝ) else 0)
      _ = ∑ Y ∈ D.carriers i, ∑ p ∈ D.centers i,
          if (p,Y) ∈ bad₂ i then (D.mass i Y : ℝ) else 0 := by rw [Finset.sum_comm]
      _ = ∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) * (highCenters i Y).card := by
        apply Finset.sum_congr rfl
        intro Y hY
        have hinner :
            (∑ p ∈ D.centers i, if (p,Y) ∈ bad₂ i then (D.mass i Y : ℝ) else 0) =
              ∑ p ∈ highCenters i Y, (D.mass i Y : ℝ) := by
          rw [← Finset.sum_filter]
          have hbadFilter : (D.centers i).filter
              (fun p => (p,Y) ∈ bad₂ i) =
                (D.centers i).filter (fun p => (p,Y) ∉ bad₁ i ∧
                  cutoff i < groupDepth p (D.carriers i) Y) := by
            apply Finset.filter_congr
            intro p hp
            change ((p,Y) ∈ ((D.centers i).product (D.carriers i)).filter
              (fun a => a ∉ bad₁ i ∧ cutoff i < groupDepth a.1 (D.carriers i) a.2)) ↔ _
            simp [Finset.mem_filter, Finset.mem_product, hp, hY]
          have hfilterHigh : (D.centers i).filter
              (fun p => (p,Y) ∉ bad₁ i ∧ cutoff i < groupDepth p (D.carriers i) Y) =
                highCenters i Y := by
            simp [highCenters, goodCenters, Finset.filter_filter, and_assoc]
          rw [hbadFilter, hfilterHigh]
        rw [hinner, Finset.sum_const, nsmul_eq_mul]
        ring
  have hdisjoint (i : ℕ) : Disjoint (bad₁ i) (bad₂ i) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_filter.mp hb).2.1 ha
  have hbadSubset (i : ℕ) : bad i ⊆ (D.centers i).product (D.carriers i) := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hbad₁Subset i ha
    · exact (Finset.mem_filter.mp ha).1
  have hincEq (i : ℕ) : D.incidenceMass i (bad i) =
      D.incidenceMass i (bad₁ i) + D.incidenceMass i (bad₂ i) := by
    unfold SeparatedDepthData.incidenceMass
    dsimp [bad]
    rw [Finset.sum_union (hdisjoint i), add_div]
  have hbudgetUpper : ∀ᶠ i in atTop,
      (AffineFamily.degree (D.carriers i) : ℝ) ≤
        D.degreeBudget i * Real.exp (δ * D.s i) := by
    filter_upwards [hbudget.1 δ hδ] with i hi
    exact hi ()
  have hLBound : ∀ᶠ i in atTop,
      (L i : ℝ) ≤ regime.B i * Real.exp (δ * D.s i) := by
    filter_upwards [hLupper δ hδ] with i hi
    exact hi ()
  have hcenterLower : ∀ᶠ i in atTop,
      regime.N i * Real.exp (-δ * D.v i) ≤ (D.centers i).card := by
    filter_upwards [D.source_size.1 δ hδ] with i hi
    exact hi ()
  have hsepSmall : ∀ᶠ i in atTop, D.v i ≤ D.s i := by
    have hsPos : ∀ᶠ i in atTop, 0 < D.s i := D.s_grows.eventually_gt_atTop 0
    have hratio : ∀ᶠ i in atTop, D.v i / D.s i < 1 :=
      hseparated.eventually (Iio_mem_nhds (by norm_num))
    filter_upwards [hsPos, hratio] with i hs hv
    have hv' : D.v i < 1 * D.s i := (div_lt_iff₀ hs).mp hv
    simpa only [one_mul] using hv'.le
  let K (i : ℕ) : ℝ :=
    (C : ℝ) * (AffineFamily.degree (D.carriers i) : ℝ) * (L i : ℝ)^(l+1) /
      (cutoff i : ℝ)
  have hKNonneg (i : ℕ) (hq : 0 < (cutoff i : ℝ)) : 0 ≤ K i := by
    dsimp [K]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (hcarrierDegreeNonneg i)) (by positivity)) hq.le
  have hhighCard (i : ℕ) (Y : AffineVariety d) (hY : Y ∈ D.carriers i)
      (hsafeI : ∀ p ∈ D.centers i, ∀ Z ∈ D.carriers i, (p,Z) ∉ bad₁ i →
        (radialImage p Z).dimension = l ∧ Z.multiplicity p ≤ Z.degree/2)
      (hq : 0 < (cutoff i : ℝ)) : (highCenters i Y).card ≤ K i := by
    apply (le_div_iff₀ hq).2
    simpa [K, mul_comm, mul_left_comm, mul_assoc] using hcountBound i Y hY hsafeI
  have hbad₂MassBound (i : ℕ)
      (hsafeI : ∀ p ∈ D.centers i, ∀ Y ∈ D.carriers i, (p,Y) ∉ bad₁ i →
        (radialImage p Y).dimension = l ∧ Y.multiplicity p ≤ Y.degree/2)
      (hq : 0 < (cutoff i : ℝ)) :
      (∑ a ∈ bad₂ i, (D.mass i a.2 : ℝ)) ≤ (D.targets i).card * K i := by
    rw [hbad₂Mass i]
    calc
      (∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) * (highCenters i Y).card) ≤
          ∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) * K i := by
        apply Finset.sum_le_sum
        intro Y hY
        exact mul_le_mul_of_nonneg_left (hhighCard i Y hY hsafeI hq) (Nat.cast_nonneg _)
      _ = (D.targets i).card * K i := by
        rw [← Finset.sum_mul, hmassTotalReal]
  have hbad₂IncidenceBound : ∀ᶠ i in atTop,
      D.incidenceMass i (bad₂ i) ≤
        (C : ℝ) * 4 * Real.exp (-(η/4) * D.s i) := by
    filter_upwards [hsafe₁, hcentersPos, htargetsPos, hbudgetUpper, hLBound,
      hcenterLower, hsepSmall, hcutoffLower, hcutoffPos,
      D.s_grows.eventually_gt_atTop 0] with
      i hsafeI hc ht hdeg hLi hcenter hsep hqLower hqPos hs
    have hbadMass := hbad₂MassBound i (by
      intro p hp Y hY hpY
      have hret : Y ∈ D.retained i (bad₁ i) p := Finset.mem_filter.mpr ⟨hY, hpY⟩
      have hs := hsafeI p hp Y hret
      exact ⟨hs.1, hs.2.1⟩) hqPos
    have hinc : D.incidenceMass i (bad₂ i) ≤ K i / (D.centers i).card := by
      unfold SeparatedDepthData.incidenceMass
      have hdenPosReal : 0 < ((D.centers i).card : ℝ) * (D.targets i).card := by positivity
      have htargetsReal : (0 : ℝ) < (D.targets i).card := by exact_mod_cast (show 0 < (D.targets i).card by omega)
      have hcentersReal : (0 : ℝ) < (D.centers i).card := by exact_mod_cast (show 0 < (D.centers i).card by omega)
      calc
        (∑ a ∈ bad₂ i, (D.mass i a.2 : ℝ)) /
            ((D.centers i).card * (D.targets i).card : ℝ) ≤
          ((D.targets i).card : ℝ) * K i /
            ((D.centers i).card * (D.targets i).card : ℝ) := by
              exact div_le_div_of_nonneg_right hbadMass hdenPosReal.le
        _ = K i / (D.centers i).card := by
          field_simp [ne_of_gt htargetsReal, ne_of_gt hcentersReal] <;> ring
    have hBpow : (regime.B i * Real.exp (δ * D.s i))^(l+1) =
        regime.B i^(l+1) * Real.exp (δ * D.s i * (l+1 : ℝ)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hnum : (C : ℝ) * (AffineFamily.degree (D.carriers i) : ℝ) *
          (L i : ℝ)^(l+1) ≤
        (C : ℝ) * D.degreeBudget i * Real.exp (δ * D.s i) *
          (regime.B i * Real.exp (δ * D.s i))^(l+1) := by
      have hpow : (L i : ℝ)^(l+1) ≤
          (regime.B i * Real.exp (δ * D.s i))^(l+1) := by
        gcongr
      calc
        _ ≤ (C : ℝ) * (D.degreeBudget i * Real.exp (δ * D.s i)) * (L i : ℝ)^(l+1) := by
          gcongr
        _ ≤ (C : ℝ) * (D.degreeBudget i * Real.exp (δ * D.s i)) *
            (regime.B i * Real.exp (δ * D.s i))^(l+1) := by
          exact mul_le_mul_of_nonneg_left hpow (by positivity [hdegreeBudgetPos i])
        _ = _ := by ring
    have hdenLower : (thresh i / 2) * (regime.N i * Real.exp (-δ * D.v i)) ≤
        (cutoff i : ℝ) * (D.centers i).card := by
      calc
        (thresh i / 2) * (regime.N i * Real.exp (-δ * D.v i)) ≤
            (cutoff i : ℝ) * (regime.N i * Real.exp (-δ * D.v i)) :=
          mul_le_mul_of_nonneg_right hqLower
            (mul_nonneg (regime.N_pos i).le (Real.exp_pos _).le)
        _ ≤ (cutoff i : ℝ) * (D.centers i).card :=
          mul_le_mul_of_nonneg_left hcenter hqPos.le
    have hNpos : 0 < regime.N i := regime.N_pos i
    have hthreshPos : 0 < thresh i := by
      have hrate : 0 < D.narrowRate i := by
        unfold SeparatedDepthData.narrowRate
        exact mul_pos (regime.B_pos i) (Real.exp_pos _)
      dsimp [thresh]
      exact mul_pos hrate (Real.exp_pos _)
    have hlowPos : 0 < (thresh i / 2) * (regime.N i * Real.exp (-δ * D.v i)) :=
      mul_pos (half_pos hthreshPos) (mul_pos hNpos (Real.exp_pos _))
    have hcenterPosReal : (0 : ℝ) < (D.centers i).card := by
      exact_mod_cast (show 0 < (D.centers i).card by omega)
    have hCnonneg : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC.le
    have hcutNonneg : 0 ≤ (C : ℝ) * D.degreeBudget i * Real.exp (δ * D.s i) *
        (regime.B i * Real.exp (δ * D.s i))^(l+1) := by
      have hBexp : 0 < regime.B i * Real.exp (δ * D.s i) := mul_pos (regime.B_pos i) (Real.exp_pos _)
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hCnonneg (hdegreeBudgetPos i).le) (Real.exp_pos _).le)
        (pow_nonneg hBexp.le _)
    have hKratio : K i / (D.centers i).card ≤
      ((C : ℝ) * D.degreeBudget i * Real.exp (δ * D.s i) *
        (regime.B i * Real.exp (δ * D.s i))^(l+1)) /
        ((thresh i / 2) * (regime.N i * Real.exp (-δ * D.v i))) := by
      apply (div_le_div_iff₀ hcenterPosReal hlowPos).2
      dsimp [K]
      have hLpowNonneg : 0 ≤ (L i : ℝ)^(l+1) := by positivity
      have hratioNonneg : 0 ≤
          ((C : ℝ) * (AffineFamily.degree (D.carriers i) : ℝ) * (L i : ℝ)^(l+1)) /
            (cutoff i : ℝ) := div_nonneg
              (mul_nonneg (mul_nonneg hCnonneg (hcarrierDegreeNonneg i)) hLpowNonneg)
              hqPos.le
      calc
        ((C : ℝ) * (AffineFamily.degree (D.carriers i) : ℝ) * (L i : ℝ)^(l+1) /
            (cutoff i : ℝ)) * ((thresh i / 2) * (regime.N i * Real.exp (-δ * D.v i))) ≤
          ((C : ℝ) * (AffineFamily.degree (D.carriers i) : ℝ) * (L i : ℝ)^(l+1)) *
            ((D.centers i).card : ℝ) := by
              calc
                _ ≤ (((C : ℝ) * (AffineFamily.degree (D.carriers i) : ℝ) * (L i : ℝ)^(l+1)) /
                    (cutoff i : ℝ)) * (((cutoff i : ℝ) * (D.centers i).card)) :=
                  mul_le_mul_of_nonneg_left hdenLower hratioNonneg
                _ = _ := by
                  rw [div_eq_mul_inv]
                  calc
                    _ = ((C : ℝ) * (AffineFamily.degree (D.carriers i) : ℝ) *
                        (L i : ℝ)^(l+1)) *
                        (((cutoff i : ℝ)⁻¹ * (cutoff i : ℝ)) * (D.centers i).card) := by ring
                    _ = _ := by rw [inv_mul_cancel₀ (ne_of_gt hqPos), one_mul]
        _ ≤ ((C : ℝ) * D.degreeBudget i * Real.exp (δ * D.s i) *
            (regime.B i * Real.exp (δ * D.s i))^(l+1)) *
            ((D.centers i).card : ℝ) :=
              mul_le_mul_of_nonneg_right hnum (by positivity)
    have hExpRatio :
        (Real.exp (-D.s i * tailSum) * Real.exp (δ * D.s i) *
            Real.exp (δ * D.s i * (l+1 : ℝ))) /
          (Real.exp ((η₀-tailSum) * D.s i) * Real.exp (-δ * D.v i)) =
          Real.exp ((δ * ((l : ℝ)+2) - η₀) * D.s i + δ * D.v i) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
      congr 1
      dsimp [η₀]
      push_cast
      ring
    have hscaleExact :
        ((C : ℝ) * D.degreeBudget i * Real.exp (δ * D.s i) *
          (regime.B i * Real.exp (δ * D.s i))^(l+1)) /
          ((thresh i / 2) * (regime.N i * Real.exp (-δ * D.v i))) =
        (C : ℝ) * 2 * Real.exp ((δ * ((l : ℝ)+2) - η₀) * D.s i + δ * D.v i) := by
      rw [hBpow]
      have hBne : regime.B i ≠ 0 := ne_of_gt (regime.B_pos i)
      have hNne : regime.N i ≠ 0 := ne_of_gt hNpos
      let a : ℝ := (C : ℝ) * D.narrowRate i *
        (Real.exp (δ * D.s i) * Real.exp (δ * D.s i * (l+1 : ℝ)))
      let b : ℝ := (thresh i / 2) * Real.exp (-δ * D.v i)
      have hcancelN :
          (regime.N i * a) / (regime.N i * b) = a / b :=
        mul_div_mul_left a b hNne
      have hcancelB :
          ((C : ℝ) * (regime.B i * Real.exp (-D.s i * tailSum)) *
            (Real.exp (δ * D.s i) * Real.exp (δ * D.s i * (l+1 : ℝ)))) /
              ((regime.B i * Real.exp ((η₀-tailSum) * D.s i) / 2) *
                Real.exp (-δ * D.v i)) =
          (C : ℝ) * 2 *
            ((Real.exp (-D.s i * tailSum) * Real.exp (δ * D.s i) *
              Real.exp (δ * D.s i * (l+1 : ℝ))) /
              (Real.exp ((η₀-tailSum) * D.s i) * Real.exp (-δ * D.v i))) := by
        calc
          _ = (regime.B i * ((C : ℝ) * 2 *
              (Real.exp (-D.s i * tailSum) * Real.exp (δ * D.s i) *
                Real.exp (δ * D.s i * (l+1 : ℝ))))) /
              (regime.B i * (Real.exp ((η₀-tailSum) * D.s i) * Real.exp (-δ * D.v i))) := by
            field_simp [hBne]
          _ = ((C : ℝ) * 2 *
              (Real.exp (-D.s i * tailSum) * Real.exp (δ * D.s i) *
                Real.exp (δ * D.s i * (l+1 : ℝ)))) /
              (Real.exp ((η₀-tailSum) * D.s i) * Real.exp (-δ * D.v i)) :=
            mul_div_mul_left _ _ hBne
          _ = (C : ℝ) * 2 *
              ((Real.exp (-D.s i * tailSum) * Real.exp (δ * D.s i) *
                Real.exp (δ * D.s i * (l+1 : ℝ))) /
                (Real.exp ((η₀-tailSum) * D.s i) * Real.exp (-δ * D.v i))) := by
            rw [mul_div_assoc]
      calc
        _ = ((C : ℝ) * (D.degreeBudget i * regime.B i^(l+1)) *
            (Real.exp (δ * D.s i) * Real.exp (δ * D.s i * (l+1 : ℝ)))) /
              ((thresh i / 2) * (regime.N i * Real.exp (-δ * D.v i))) := by
          congr 1
          ring
        _ = ((C : ℝ) * (regime.N i * D.narrowRate i) *
            (Real.exp (δ * D.s i) * Real.exp (δ * D.s i * (l+1 : ℝ)))) /
              ((thresh i / 2) * (regime.N i * Real.exp (-δ * D.v i))) := by
          rw [hdegreeLBase i]
        _ = (C : ℝ) * 2 *
            ((Real.exp (-D.s i * tailSum) * Real.exp (δ * D.s i) *
              Real.exp (δ * D.s i * (l+1 : ℝ))) /
              (Real.exp ((η₀-tailSum) * D.s i) * Real.exp (-δ * D.v i))) := by
          calc
            _ = (regime.N i * a) / (regime.N i * b) := by dsimp [a, b]; ring
            _ = a / b := hcancelN
            _ = _ := by
              change ((C : ℝ) * D.narrowRate i *
                  (Real.exp (δ * D.s i) * Real.exp (δ * D.s i * (l+1 : ℝ)))) /
                  ((thresh i / 2) * Real.exp (-δ * D.v i)) = _
              rw [hRateFormula i, hthreshFormula i]
              exact hcancelB
        _ = (C : ℝ) * 2 *
            Real.exp ((δ * ((l : ℝ)+2) - η₀) * D.s i + δ * D.v i) := by rw [hExpRatio]
    have hExponentBound :
        (δ * ((l : ℝ)+2) - η₀) * D.s i + δ * D.v i ≤ -(η/4) * D.s i := by
      have hsTail : δ * ((l : ℝ)+2) * D.s i = (η/8) * D.s i :=
        congrArg (fun x : ℝ => x * D.s i) hδbudget
      have hvScale : δ * D.v i ≤ δ * D.s i := mul_le_mul_of_nonneg_left hsep hδ.le
      have hsScale : δ * D.s i ≤ (η/8) * D.s i := mul_le_mul_of_nonneg_right hδle hs.le
      have hvScale' : δ * D.v i ≤ (η/8) * D.s i := hvScale.trans hsScale
      calc
        (δ * ((l : ℝ)+2) - η₀) * D.s i + δ * D.v i =
            δ * ((l : ℝ)+2) * D.s i - η₀ * D.s i + δ * D.v i := by ring
        _ = (η/8) * D.s i - η₀ * D.s i + δ * D.v i := by rw [hsTail]
        _ ≤ (η/8) * D.s i - η₀ * D.s i + (η/8) * D.s i :=
          add_le_add_right hvScale' ((η/8) * D.s i - η₀ * D.s i)
        _ = -(η/4) * D.s i := by dsimp [η₀]; ring
    have hscale :
        ((C : ℝ) * D.degreeBudget i * Real.exp (δ * D.s i) *
          (regime.B i * Real.exp (δ * D.s i))^(l+1)) /
          ((thresh i / 2) * (regime.N i * Real.exp (-δ * D.v i))) ≤
        (C : ℝ) * 4 * Real.exp (-(η/4) * D.s i) := by
      calc
        _ = (C : ℝ) * 2 *
            Real.exp ((δ * ((l : ℝ)+2) - η₀) * D.s i + δ * D.v i) := hscaleExact
        _ ≤ (C : ℝ) * 2 * Real.exp (-(η/4) * D.s i) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExponentBound) (by positivity)
        _ ≤ (C : ℝ) * 4 * Real.exp (-(η/4) * D.s i) := by
          have hCpos : (0:ℝ) < (C:ℝ) := by exact_mod_cast hC
          have hexp : 0 < Real.exp (-(η/4) * D.s i) := Real.exp_pos _
          nlinarith
    exact le_trans hinc (le_trans hKratio hscale)
  have hbad₂Small : Framework.LittleO
      (fun i => D.incidenceMass i (bad₂ i)) (fun _ => 1) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ζ hζ
    have hdecay : Tendsto (fun i => (C : ℝ) * 4 * Real.exp (-(η/4) * D.s i))
        atTop (𝓝 0) := by
      have hExp := Real.tendsto_exp_atBot.comp
        (D.s_grows.const_mul_atTop_of_neg (by
          have hη4 : 0 < η / 4 := div_pos hη (by norm_num)
          exact neg_lt_zero.mpr hη4))
      simpa [mul_comm] using hExp.const_mul ((C : ℝ) * 4)
    filter_upwards [hbad₂IncidenceBound, hdecay.eventually (gt_mem_nhds hζ)] with i hbound hsmall
    have hincNonneg : 0 ≤ D.incidenceMass i (bad₂ i) := by
      unfold SeparatedDepthData.incidenceMass
      apply div_nonneg
      · exact Finset.sum_nonneg fun a ha => Nat.cast_nonneg _
      · positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hincNonneg]
    simpa [Real.norm_eq_abs] using le_trans hbound hsmall.le
  have hdisjoint (i : ℕ) : Disjoint (bad₁ i) (bad₂ i) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_filter.mp hb).2.1 ha
  have hbadSubset (i : ℕ) : bad i ⊆ (D.centers i).product (D.carriers i) := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hbad₁Subset i ha
    · exact (Finset.mem_filter.mp ha).1
  have hincEq (i : ℕ) : D.incidenceMass i (bad i) =
      D.incidenceMass i (bad₁ i) + D.incidenceMass i (bad₂ i) := by
    unfold SeparatedDepthData.incidenceMass
    dsimp [bad]
    rw [Finset.sum_union (hdisjoint i), add_div]
  have hbadSmall : Framework.LittleO
      (fun i => D.incidenceMass i (bad i)) (fun _ => 1) := by
    simpa [hincEq] using hbad₁Small.add hbad₂Small
  refine ⟨bad, hbadSubset, hbadSmall, ?_⟩
  filter_upwards [hgoodEventually, D.s_grows.eventually_gt_atTop 0] with i hgood hsPos
  intro p hp Y hY
  change Y ∈ (D.carriers i).filter (fun Y => (p,Y) ∉ bad i) at hY
  rcases Finset.mem_filter.mp hY with ⟨hYcarrier, hpairnot⟩
  have hpair₁ : (p,Y) ∉ bad₁ i := by
    intro hpbad
    exact hpairnot (Finset.mem_union.mpr (Or.inl hpbad))
  have hgoodPair := hgood p hp Y hYcarrier hpair₁
  refine ⟨hgoodPair.1, hgoodPair.2, ?_⟩
  have hdepthMono : groupDepth p (D.retained i (bad i) p) Y ≤
      groupDepth p (D.carriers i) Y := by
    unfold groupDepth
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro Z hZ
      obtain ⟨hZret, hZequal⟩ := Finset.mem_filter.mp hZ
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hZret).1, hZequal⟩
    · intro Z hZ hZnot
      exact Nat.zero_le _
  have hcutoffBound : groupDepth p (D.carriers i) Y ≤ cutoff i := by
    by_contra hnot
    have hlarge : cutoff i < groupDepth p (D.carriers i) Y := Nat.lt_of_not_ge hnot
    have hpYmem : (p,Y) ∈ (D.centers i).product (D.carriers i) := Finset.mem_product.mpr ⟨hp, hYcarrier⟩
    have hbad₂mem : (p,Y) ∈ bad₂ i := Finset.mem_filter.mpr ⟨hpYmem, ⟨hpair₁, hlarge⟩⟩
    exact hpairnot (Finset.mem_union.mpr (Or.inr hbad₂mem))
  have hNatBound : (groupDepth p (D.retained i (bad i) p) Y : ℝ) ≤ thresh i := by
    have hratePos : 0 < D.narrowRate i := by
      dsimp [SeparatedDepthData.narrowRate]
      exact mul_pos (regime.B_pos i) (Real.exp_pos _)
    have hthreshPos : 0 < thresh i := by
      dsimp [thresh]
      exact mul_pos hratePos (Real.exp_pos _)
    calc
      (groupDepth p (D.retained i (bad i) p) Y : ℝ) ≤ groupDepth p (D.carriers i) Y := by exact_mod_cast hdepthMono
      _ ≤ cutoff i := by exact_mod_cast hcutoffBound
      _ ≤ thresh i := Nat.floor_le hthreshPos.le
  have hrateBound : thresh i ≤ D.narrowRate i * Real.exp (η * D.s i) := by
    dsimp [thresh, η₀]
    apply mul_le_mul_of_nonneg_left ?_ (mul_pos (regime.B_pos i) (Real.exp_pos _)).le
    apply Real.exp_le_exp.mpr
    nlinarith [hsPos]
  exact hNatBound.trans hrateBound

set_option maxHeartbeats 1000000 in
/-- Explicit eventual guards for the wide rank-loss parameters. -/
theorem wide_guards (d : ℕ) (B s : ℕ → ℝ) (hBpos : ∀ i, 0 < B i) (hB : Tendsto B atTop atTop)
    (hs : Tendsto s atTop atTop) (hsmall : Framework.LittleO s (fun i => Real.log (B i)))
    (C₀ η : ℝ) (hC₀ : 0 < C₀) (hη : 0 < η) :
    ∀ᶠ i in atTop, 1 ≤ ⌈B i * Real.exp (C₀ * s i)⌉₊ ∧
      ⌈B i * Real.exp (-2 * s i)⌉₊ ≤ ⌈B i * Real.exp (C₀ * s i)⌉₊ ∧
      2 * ⌊B i ^ (1/2 : ℝ)⌋₊ + 8 ≤ ⌈B i * Real.exp (-2 * s i)⌉₊ ∧
      (∀ G : ℕ, (⌈B i * Real.exp (-2 * s i)⌉₊ / 2) * G ≤
          (d+1) * (2 * ⌈B i * Real.exp (C₀ * s i)⌉₊ ^ 2) →
        (G : ℝ) ≤ B i * Real.exp ((2*C₀+3) * s i)) ∧
      (⌈B i * Real.exp (-2 * s i)⌉₊ : ℝ) ≤ B i * Real.exp (-2 * s i) * Real.exp (η * s i) := by
  have hκ : (0 : ℝ) < 1/8 := by norm_num
  let σ₀ : ℝ := max (Real.log (32 * ((d : ℝ) + 1))) (Real.log 2 / η)
  filter_upwards [hB.eventually_ge_atTop 256, hs.eventually_ge_atTop (max σ₀ 0),
    hsmall.def hκ] with i hBi hsi hsmalli
  set x := B i with hx
  set σ := s i with hσ
  have hxpos : 0 < x := hBpos i
  have hσ0 : 0 ≤ σ := le_trans (le_max_right _ _) hsi
  have hσ₀ : σ₀ ≤ σ := le_trans (le_max_left _ _) hsi
  set Λ := Real.log x with hLam
  have hL256 : Real.log 256 ≤ Λ := Real.log_le_log (by norm_num) hBi
  have hlog256 : Real.log 256 = 4 * Real.log 4 := by
    rw [show (256 : ℝ) = 4^4 by norm_num, Real.log_pow]
    norm_num
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hLpos : 0 < Λ := by linarith
  have hsL : σ ≤ Λ / 8 := by
    have h := hsmalli
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hσ0, abs_of_pos hLpos] at h
    linarith
  have hxexp : x = Real.exp Λ := (Real.exp_log hxpos).symm
  set u := Real.exp (Λ / 4) with hu
  have hu4 : 4 ≤ u := by
    have h : Real.log 4 ≤ Λ / 4 := by linarith
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ u := Real.exp_le_exp.mpr h
  have hu2 : Real.exp (Λ / 2) = u ^ 2 := by
    rw [hu, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu3 : Real.exp (3 * Λ / 4) = u ^ 3 := by
    rw [hu, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hlow : u ^ 3 ≤ x * Real.exp (-2 * σ) := by
    rw [← hu3, hxexp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hsqrt : x ^ (1/2 : ℝ) = u ^ 2 := by
    rw [Real.rpow_def_of_pos hxpos, ← hu2]
    congr 1
    ring
  have hrrReal : x * Real.exp (-2 * σ) ≤ (⌈x * Real.exp (-2 * σ)⌉₊ : ℝ) := Nat.le_ceil _
  have hrrUpper : (⌈x * Real.exp (-2 * σ)⌉₊ : ℝ) < x * Real.exp (-2 * σ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hLLUpper : (⌈x * Real.exp (C₀ * σ)⌉₊ : ℝ) < x * Real.exp (C₀ * σ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hexpC₀ : 1 ≤ Real.exp (C₀ * σ) := Real.one_le_exp (by positivity)
  have hx1 : 1 ≤ x := le_trans (by norm_num) hBi
  have hu64 : 64 ≤ u ^ 3 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  · apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_left _ hxpos.le
    exact Real.exp_le_exp.mpr (by nlinarith)
  · have hfloor : (⌊x ^ (1/2 : ℝ)⌋₊ : ℝ) ≤ u ^ 2 := by
      rw [← hsqrt]
      exact Nat.floor_le (by positivity)
    have hpoly : 2 * u ^ 2 + 8 ≤ u ^ 3 := by nlinarith
    have hreal : ((2 * ⌊x ^ (1/2 : ℝ)⌋₊ + 8 : ℕ) : ℝ) ≤ (⌈x * Real.exp (-2 * σ)⌉₊ : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hreal
  · intro G hG
    set rr := ⌈x * Real.exp (-2 * σ)⌉₊ with hrr
    set LL := ⌈x * Real.exp (C₀ * σ)⌉₊ with hLL
    have hrr64 : (64 : ℝ) ≤ rr := by linarith
    have hhalf : (rr : ℝ) / 4 ≤ ((rr / 2 : ℕ) : ℝ) := by
      have hmod := Nat.div_add_mod rr 2
      have hmodlt : rr % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have h1 : (rr : ℝ) ≤ 2 * ((rr / 2 : ℕ) : ℝ) + 1 := by
        have : rr ≤ 2 * (rr / 2) + 1 := by omega
        exact_mod_cast this
      linarith
    have hhalfpos : 0 < ((rr / 2 : ℕ) : ℝ) := by linarith
    have hGreal : ((rr / 2 : ℕ) : ℝ) * G ≤ ((d : ℝ) + 1) * (2 * (LL : ℝ) ^ 2) := by
      exact_mod_cast hG
    have hLL2 : (LL : ℝ) ≤ 2 * (x * Real.exp (C₀ * σ)) := by
      have : 1 ≤ x * Real.exp (C₀ * σ) := by nlinarith
      linarith
    have hLLnn : 0 ≤ (LL : ℝ) := Nat.cast_nonneg _
    have hLLsq : (LL : ℝ) ^ 2 ≤ 4 * (x * Real.exp (C₀ * σ)) ^ 2 := by nlinarith
    have hG1 : (rr : ℝ) / 4 * G ≤ ((d : ℝ) + 1) * (2 * (4 * (x * Real.exp (C₀ * σ)) ^ 2)) := by
      have hGnn : (0 : ℝ) ≤ G := Nat.cast_nonneg _
      calc (rr : ℝ) / 4 * G ≤ ((rr / 2 : ℕ) : ℝ) * G := mul_le_mul_of_nonneg_right hhalf hGnn
        _ ≤ ((d : ℝ) + 1) * (2 * (LL : ℝ) ^ 2) := hGreal
        _ ≤ ((d : ℝ) + 1) * (2 * (4 * (x * Real.exp (C₀ * σ)) ^ 2)) := by gcongr
    have hG2 : x * Real.exp (-2 * σ) / 4 * G ≤
        ((d : ℝ) + 1) * (2 * (4 * (x * Real.exp (C₀ * σ)) ^ 2)) := by
      have hGnn : (0 : ℝ) ≤ G := Nat.cast_nonneg _
      calc x * Real.exp (-2 * σ) / 4 * G ≤ (rr : ℝ) / 4 * G := by gcongr
        _ ≤ _ := hG1
    have he2 : Real.exp (-2 * σ) * Real.exp (2 * σ) = 1 := by
      rw [← Real.exp_add]; simp
    have hσbig : 32 * ((d : ℝ) + 1) ≤ Real.exp σ := by
      have h : Real.log (32 * ((d : ℝ) + 1)) ≤ σ := le_trans (le_max_left _ _) hσ₀
      calc 32 * ((d : ℝ) + 1) = Real.exp (Real.log (32 * ((d : ℝ) + 1))) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp σ := Real.exp_le_exp.mpr h
    have hexpsplit : Real.exp ((2*C₀+3) * σ) =
        Real.exp (C₀ * σ) ^ 2 * Real.exp (2 * σ) * Real.exp σ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have hpos1 : 0 < x * Real.exp (-2 * σ) := by positivity
    -- G ≤ 32 (d+1) x e^{2C₀σ} e^{2σ}
    have hG3 : (G : ℝ) ≤ 32 * ((d : ℝ) + 1) * x * Real.exp (C₀ * σ) ^ 2 * Real.exp (2 * σ) := by
      have hmul : (G : ℝ) * (x * Real.exp (-2 * σ)) ≤
          (32 * ((d : ℝ) + 1) * x * Real.exp (C₀ * σ) ^ 2 * Real.exp (2 * σ)) *
            (x * Real.exp (-2 * σ)) := by
        have hrhs : (32 * ((d : ℝ) + 1) * x * Real.exp (C₀ * σ) ^ 2 * Real.exp (2 * σ)) *
            (x * Real.exp (-2 * σ)) = 4 * (((d : ℝ) + 1) * (2 * (4 * (x * Real.exp (C₀ * σ)) ^ 2))) := by
          have : Real.exp (2 * σ) * Real.exp (-2 * σ) = 1 := by rw [mul_comm]; exact he2
          calc _ = 32 * ((d : ℝ) + 1) * x * Real.exp (C₀ * σ) ^ 2 * x *
                (Real.exp (2 * σ) * Real.exp (-2 * σ)) := by ring
            _ = _ := by rw [this]; ring
        rw [hrhs]
        linarith
      exact le_of_mul_le_mul_right hmul hpos1
    calc (G : ℝ) ≤ 32 * ((d : ℝ) + 1) * x * Real.exp (C₀ * σ) ^ 2 * Real.exp (2 * σ) := hG3
      _ ≤ Real.exp σ * x * Real.exp (C₀ * σ) ^ 2 * Real.exp (2 * σ) := by gcongr
      _ = x * Real.exp ((2*C₀+3) * σ) := by rw [hexpsplit]; ring
  · have hησ : 2 ≤ Real.exp (η * σ) := by
      have h : Real.log 2 / η ≤ σ := le_trans (le_max_right _ _) hσ₀
      have h' : Real.log 2 ≤ η * σ := by
        rw [div_le_iff₀ hη] at h
        linarith
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (η * σ) := Real.exp_le_exp.mpr h'
    have h1 : 1 ≤ x * Real.exp (-2 * σ) := by linarith
    nlinarith

set_option maxHeartbeats 1000000 in
/-- `dep:wide-R`, depth.tex:220–474. Generic lists, specialization, compression,
and componentwise no-capture turn generic depth into actual-center depth. -/
theorem dep_wide_depth {d j : ℕ} {regime : Regime d}
    (D : SeparatedDepthData regime j) (hD : D.Hypotheses)
    (hseparated : Tendsto (fun i => D.s i / D.v i) atTop (𝓝 0))
    (hnext : 0 < D.b ⟨j, D.j_lt⟩) (hlow : d-j < d-1) :
    D.NegligibleSafeDepth D.wideRate := by
  classical
  intro η hη
  obtain ⟨bad₁, hbad₁Subset, hbad₁Small, hsafe₁⟩ := dep_first_depth D hD 1 one_pos
  rcases hD with ⟨_, _, _, _, _, hWideInput⟩
  obtain ⟨k, sources, sourceOwner, lists, ignored, _, _, hsourcesPure, _, _,
    hsourceOwner, hlistsSub, hgenericEv, hexclSmall, hcomponentTests⟩ :=
    hWideInput hseparated hnext hlow
  obtain ⟨C₀, hC₀, hpathDeg⟩ := D.path_degree
  let l : ℕ := d - j
  have hl : 1 ≤ l := by have := D.j_lt; omega
  let C : ℝ := 2*C₀+3
  have hC : 0 < C := by positivity
  let r : ℕ → ℕ := fun i => ⌈regime.B i * Real.exp (-2 * D.s i)⌉₊
  let L : ℕ → ℕ := fun i => ⌈regime.B i * Real.exp (C₀ * D.s i)⌉₊
  let S (i : ℕ) (X Y : AffineVariety d) : Finset (Point d) :=
    (D.centers i).filter (fun p => p ∉ ignored i ∧ sourceOwner i p = X ∧
      (radialImage p Y).dimension = l)
  let Good (i : ℕ) (X Y : AffineVariety d) (g : Poly d) : Prop :=
    g ∉ X.ideal ∧ (g.totalDegree : ℝ) ≤ regime.B i * Real.exp (C * D.s i) ∧
      ∀ p ∈ S i X Y, r i < groupDepth p (lists i X) Y → MvPolynomial.eval p g = 0
  let test (i : ℕ) (Y X : AffineVariety d) : Poly d :=
    if h : ∃ g, Good i X Y g then h.choose else 1
  have htestMem (i : ℕ) (Y : AffineVariety d) : ∀ X ∈ sources i,
      test i Y X ∉ X.ideal ∧
        ((test i Y X).totalDegree : ℝ) ≤ regime.B i * Real.exp (C * D.s i) := by
    intro X hX
    by_cases h : ∃ g, Good i X Y g
    · have hspec := h.choose_spec
      simp only [test, dif_pos h]
      exact ⟨hspec.1, hspec.2.1⟩
    · simp only [test, dif_neg h]
      refine ⟨?_, ?_⟩
      · have hprime : X.ideal.IsPrime := (hsourcesPure i X hX).1
        exact fun h1 => hprime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
      · simp only [MvPolynomial.totalDegree_one, Nat.cast_zero]
        exact (mul_pos (regime.B_pos i) (Real.exp_pos _)).le
  let testOf (i : ℕ) (Y : AffineVariety d) : D.ComponentTests sources C i :=
    ⟨test i Y, htestMem i Y⟩
  let bad₂ (i : ℕ) : Finset (Point d × AffineVariety d) :=
    ((D.centers i).product (D.carriers i)).filter
      (fun a => a.1 ∈ ignored i ∨ a.2 ∉ lists i (sourceOwner i a.1))
  let bad₃ (i : ℕ) : Finset (Point d × AffineVariety d) :=
    ((D.centers i).product (D.carriers i)).filter
      (fun a => a.1 ∉ ignored i ∧ a.2 ∈ lists i (sourceOwner i a.1) ∧
        (radialImage a.1 a.2).dimension = l ∧
        r i < groupDepth a.1 (lists i (sourceOwner i a.1)) a.2)
  let bad (i : ℕ) : Finset (Point d × AffineVariety d) := bad₁ i ∪ bad₂ i ∪ bad₃ i
  have hguards := wide_guards d regime.B D.s regime.B_pos regime.B_tendsto D.s_grows
    D.s_small C₀ η hC₀ hη
  -- the proper tests exist eventually
  have hGoodEv : ∀ᶠ i in atTop, ∀ X ∈ sources i, ∀ Y ∈ lists i X, ∃ g, Good i X Y g := by
    filter_upwards [hguards, hpathDeg, hgenericEv] with i hg hdeg hgen
    obtain ⟨hL1, hrL, hgap, hGbound, _⟩ := hg
    intro X hX Y hY
    have hXirr : X.IsIrreducible := (hsourcesPure i X hX).1
    have hJ : AffineFamily.IsPure (lists i X) l := fun V hV =>
      D.carrier_pure i V (hlistsSub i X hX hV)
    have hE : ∀ f ∈ (D.pathEquations i : Set (Poly d)), f.totalDegree ≤ L i := by
      intro f hf
      have h1 := hdeg f (Finset.mem_coe.mp hf)
      exact_mod_cast le_trans h1 (Nat.le_ceil _)
    have hcomp : ∀ Z ∈ lists i X,
        Z.IsComponentOf (Ideal.span (D.pathEquations i : Set (Poly d))) :=
      fun Z hZ => D.path_component i Z (hlistsSub i X hX hZ)
    have hSX : ∀ p ∈ S i X Y, p ∈ X.points := by
      intro p hp
      obtain ⟨hpc, hpi, hpX, _⟩ := Finset.mem_filter.mp hp
      rw [← hpX]
      exact (hsourceOwner i p hpc hpi).2
    have hSim : ∀ p ∈ S i X Y, (radialImage p Y).dimension = l :=
      fun p hp => (Finset.mem_filter.mp hp).2.2.2
    obtain ⟨g, hgX, hgdeg, hgvan⟩ := dep_wide_proper_test X hXirr (lists i X) l hl hJ Y hY
      (D.pathEquations i : Set (Poly d)) (L i) ⌊regime.B i ^ (1/2 : ℝ)⌋₊ (r i) hL1 hrL hgap
      hE hcomp (hgen X hX Y hY) (S i X Y) hSX hSim
    exact ⟨g, hgX, hGbound _ hgdeg, hgvan⟩
  -- bad₃ rows are captured by one component test per target
  have hrow : ∀ᶠ i in atTop, ∀ Y ∈ D.carriers i,
      ((D.centers i).filter (fun p => (p, Y) ∈ bad₃ i)).card ≤
        ((D.centers i).filter (fun p => p ∉ ignored i ∧
          MvPolynomial.eval p ((testOf i Y).val (sourceOwner i p)) = 0)).card := by
    filter_upwards [hGoodEv] with i hgood
    intro Y _
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hpc, hpbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hpi, hYl, hdim, hdepth⟩ := Finset.mem_filter.mp hpbad
    refine Finset.mem_filter.mpr ⟨hpc, hpi, ?_⟩
    set X := sourceOwner i p with hXdef
    have hX : X ∈ sources i := (hsourceOwner i p hpc hpi).1
    have hex := hgood X hX Y hYl
    change MvPolynomial.eval p (test i Y X) = 0
    simp only [test, dif_pos hex]
    exact hex.choose_spec.2.2 p (Finset.mem_filter.mpr ⟨hpc, hpi, hXdef.symm, hdim⟩) hdepth
  have hbad₃Small : Framework.LittleO (fun i => D.incidenceMass i (bad₃ i)) (fun _ => 1) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    filter_upwards [hrow, hcomponentTests C hC ε hε] with i hrowi hcap
    rw [Real.norm_eq_abs, abs_of_nonneg (wide_incidenceMass_nonneg D i _), norm_one, mul_one]
    unfold SeparatedDepthData.incidenceMass
    apply div_le_of_le_mul₀ (by positivity) hε.le
    have hsub : bad₃ i ⊆ (D.centers i).product (D.carriers i) := Finset.filter_subset _ _
    rw [wide_mass_rows (D.centers i) (D.carriers i) (bad₃ i) hsub (fun Y => (D.mass i Y : ℝ))]
    have hmassTotal : (∑ Y ∈ D.carriers i, (D.mass i Y : ℝ)) = (D.targets i).card := by
      have hmaps : ∀ q ∈ D.targets i, D.owner i q ∈ D.carriers i :=
        fun q hq => D.owner_member i q hq
      have := (Finset.card_eq_sum_card_fiberwise (s := D.targets i) (t := D.carriers i)
        (f := D.owner i) hmaps).symm
      exact_mod_cast (by simpa [SeparatedDepthData.mass] using this)
    calc
      (∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) *
          (((D.centers i).filter (fun p => (p, Y) ∈ bad₃ i)).card : ℝ)) ≤
          ∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) * (ε * (D.centers i).card) := by
        apply Finset.sum_le_sum
        intro Y hY
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have h1 := hcap (testOf i Y)
        rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)] at h1
        exact le_trans (by exact_mod_cast hrowi Y hY) h1
      _ = ε * ((D.centers i).card * (D.targets i).card) := by
        rw [← Finset.sum_mul, hmassTotal]
        ring
  have hbadSmall : Framework.LittleO (fun i => D.incidenceMass i (bad i)) (fun _ => 1) := by
    have hsum := (hbad₁Small.add hexclSmall).add hbad₃Small
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hsum
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with i
    have h1 := wide_incidenceMass_union_le D i (bad₁ i ∪ bad₂ i) (bad₃ i)
    have h2 := wide_incidenceMass_union_le D i (bad₁ i) (bad₂ i)
    have n1 := wide_incidenceMass_nonneg D i (bad₁ i)
    have n2 := wide_incidenceMass_nonneg D i (bad₂ i)
    have n3 := wide_incidenceMass_nonneg D i (bad₃ i)
    have n0 := wide_incidenceMass_nonneg D i (bad i)
    simp only [Real.norm_eq_abs, ]
    rw [abs_of_nonneg n0, abs_of_nonneg (by positivity)]
    change D.incidenceMass i (bad₁ i ∪ bad₂ i ∪ bad₃ i) ≤ 1 * _
    linarith
  have hbadSubset (i : ℕ) : bad i ⊆ (D.centers i).product (D.carriers i) := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · exact hbad₁Subset i ha
      · exact (Finset.mem_filter.mp ha).1
    · exact (Finset.mem_filter.mp ha).1
  refine ⟨bad, hbadSubset, hbadSmall, ?_⟩
  filter_upwards [hsafe₁, hguards] with i hsafeI hg
  obtain ⟨_, _, _, _, hrRate⟩ := hg
  intro p hp Y hY
  change Y ∈ (D.carriers i).filter (fun Y => (p,Y) ∉ bad i) at hY
  rcases Finset.mem_filter.mp hY with ⟨hYcarrier, hpairnot⟩
  have hn₁ : (p,Y) ∉ bad₁ i := fun h => hpairnot (by simp [bad, h])
  have hn₂ : (p,Y) ∉ bad₂ i := fun h => hpairnot (by simp [bad, h])
  have hn₃ : (p,Y) ∉ bad₃ i := fun h => hpairnot (by simp [bad, h])
  have hsafe := hsafeI p hp Y (Finset.mem_filter.mpr ⟨hYcarrier, hn₁⟩)
  refine ⟨hsafe.1, hsafe.2.1, ?_⟩
  have hpY : (p, Y) ∈ (D.centers i).product (D.carriers i) :=
    Finset.mem_product.mpr ⟨hp, hYcarrier⟩
  have hpi : p ∉ ignored i := fun h => hn₂ (Finset.mem_filter.mpr ⟨hpY, Or.inl h⟩)
  have hYl : Y ∈ lists i (sourceOwner i p) := by
    by_contra h
    exact hn₂ (Finset.mem_filter.mpr ⟨hpY, Or.inr h⟩)
  have hmono : groupDepth p (D.retained i (bad i) p) Y ≤
      groupDepth p (lists i (sourceOwner i p)) Y := by
    unfold groupDepth
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro Z hZ
      obtain ⟨hZret, hZeq⟩ := Finset.mem_filter.mp hZ
      obtain ⟨hZc, hZnot⟩ := Finset.mem_filter.mp hZret
      refine Finset.mem_filter.mpr ⟨?_, hZeq⟩
      by_contra h
      exact hZnot (by
        have : (p, Z) ∈ bad₂ i :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hZc⟩, Or.inr h⟩
        simp [bad, this])
    · intro _ _ _
      exact Nat.zero_le _
  have hdepthR : groupDepth p (lists i (sourceOwner i p)) Y ≤ r i := by
    by_contra h
    exact hn₃ (Finset.mem_filter.mpr ⟨hpY, hpi, hYl, hsafe.1, Nat.lt_of_not_ge h⟩)
  calc
    (groupDepth p (D.retained i (bad i) p) Y : ℝ) ≤ r i := by exact_mod_cast hmono.trans hdepthR
    _ ≤ D.wideRate i * Real.exp (η * D.s i) := hrRate

/-- `dep:degree-assembly`, depth.tex:90–144,468–474.
The density quantifier follows the deletions and precedes its eventual threshold. -/
theorem dep_degree_assembly {d j : ℕ} {regime : Regime d}
    (D : SeparatedDepthData regime j) (hbudget : D.DegreeBudgets) (R : ℕ → ℝ)
    (hR : ∀ᶠ i in atTop, 0 < R i) (hdepth : D.NegligibleSafeDepth R)
    (ε : ℝ) (hε : 0 < ε) : D.ProjectedDegreeConclusion R ε := by
  classical
  let η : ℝ := ε / 4
  let δ : ℝ := ε / 8
  let θ : ℝ := ε - η - 2 * δ
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hθ : 0 < θ := by dsimp [θ, η, δ]; linarith
  obtain ⟨bad, hbadSubset, hbadSmall, hsafe⟩ := hdepth η hη
  let α : ℕ → ℝ := fun i => D.incidenceMass i (bad i)
  let root : ℕ → ℝ := fun i => Real.sqrt (α i)
  have hrootSmall : Framework.LittleO root (fun _ => 1) := by
    simpa [root, α] using hbadSmall.sqrt (by
      filter_upwards [] with i
      norm_num)
  have hmassTotalNat (i : ℕ) :
      (∑ Y ∈ D.carriers i, D.mass i Y) = (D.targets i).card := by
    have hmaps : ∀ q ∈ D.targets i, D.owner i q ∈ D.carriers i :=
      fun q hq => D.owner_member i q hq
    simpa [SeparatedDepthData.mass] using
      (Finset.card_eq_sum_card_fiberwise (s := D.targets i) (t := D.carriers i)
        (f := D.owner i) hmaps).symm
  have hmassTotalReal (i : ℕ) :
      (∑ Y ∈ D.carriers i, (D.mass i Y : ℝ)) = (D.targets i).card := by
    exact_mod_cast hmassTotalNat i
  have hcentersPos : ∀ᶠ i in atTop, 1 ≤ (D.centers i).card := by
    filter_upwards [D.source_size.1 1 (by norm_num)] with i hi
    have hpos : (0 : ℝ) < regime.N i * Real.exp (-1 * D.v i) :=
      mul_pos (regime.N_pos i) (Real.exp_pos _)
    have hcard : (0 : ℝ) < (D.centers i).card := lt_of_lt_of_le hpos (hi ())
    exact_mod_cast hcard
  have htargetsPos : ∀ᶠ i in atTop, 1 ≤ (D.targets i).card := by
    filter_upwards [D.target_size.1 1 (by norm_num)] with i hi
    have hpos : (0 : ℝ) < regime.N i * Real.exp (-1 * D.s i) :=
      mul_pos (regime.N_pos i) (Real.exp_pos _)
    have hcard : (0 : ℝ) < (D.targets i).card := lt_of_lt_of_le hpos (hi ())
    exact_mod_cast hcard
  have hmassPos : ∀ᶠ i in atTop,
      1 ≤ ∑ Y ∈ D.carriers i, D.mass i Y := by
    filter_upwards [htargetsPos] with i hi
    rw [hmassTotalNat]
    exact hi
  let valid (i : ℕ) : Prop :=
    1 ≤ (D.centers i).card ∧ 1 ≤ ∑ Y ∈ D.carriers i, D.mass i Y
  have hvalid : ∀ᶠ i in atTop, valid i := by
    filter_upwards [hcentersPos, hmassPos] with i hi hj
    exact ⟨hi, hj⟩
  have hdegreeBase (i : ℕ) : regime.B i ^ d = regime.N i := by
    rw [Regime.B, ← Real.rpow_natCast, ← Real.rpow_mul (regime.N_pos i).le]
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast (show 0 < d by have hd := regime.dimension_ge_three; omega)
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
    have hexp : (1 / (d : ℝ)) * (d : ℝ) = 1 := by field_simp [hdne]
    rw [hexp]
    exact Real.rpow_one _
  have hcutProducts (i : ℕ) :
      ∏ t ∈ Finset.univ, D.cutDegree i t = regime.B i ^ d := by
    have hprodB :
        (∏ t ∈ (Finset.univ : Finset (Fin d)), regime.B i) = regime.B i ^ d := by simp
    have hsumExp :
        (∏ t ∈ (Finset.univ : Finset (Fin d)), Real.exp (D.b t * D.s i)) = 1 := by
      rw [← Real.exp_sum]
      have hsum : (∑ t : Fin d, D.b t * D.s i) = 0 := by
        rw [← Finset.sum_mul, D.b_sum]
        simp
      rw [hsum, Real.exp_zero]
    calc
      ∏ t ∈ Finset.univ, D.cutDegree i t =
          (∏ t ∈ Finset.univ, regime.B i) *
            ∏ t ∈ Finset.univ, Real.exp (D.b t * D.s i) := by
        simp only [SeparatedDepthData.cutDegree, Finset.prod_mul_distrib]
        rfl
      _ = regime.B i ^ d * 1 := by rw [hprodB, hsumExp]
      _ = regime.B i ^ d := by ring
  have hbudgetTail (i : ℕ) : D.degreeBudget i * D.tailBudget i = regime.N i := by
    have hsplit :
        (∏ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), D.cutDegree i t) *
          ∏ t ∈ Finset.univ.filter (fun t : Fin d => j ≤ t.val), D.cutDegree i t =
        ∏ t ∈ Finset.univ, D.cutDegree i t := by
      simpa only [not_lt] using
        (Finset.prod_filter_mul_prod_filter_not (Finset.univ)
          (fun t : Fin d => t.val < j) (fun t => D.cutDegree i t))
    calc
      D.degreeBudget i * D.tailBudget i =
          (∏ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), D.cutDegree i t) *
            ∏ t ∈ Finset.univ.filter (fun t : Fin d => j ≤ t.val), D.cutDegree i t := by
        rfl
      _ = ∏ t ∈ Finset.univ, D.cutDegree i t := hsplit
      _ = regime.B i ^ d := hcutProducts i
      _ = regime.N i := hdegreeBase i
  let rowProperty (i : ℕ) (B : Finset (Point d)) : Prop :=
    B ⊆ D.centers i ∧
      (valid i → (B.card : ℝ) ≤ (D.centers i).card * root i) ∧
      (valid i → ∀ p ∈ D.centers i, p ∉ B →
        D.deletedRowMass i (bad i) p ≤ (D.targets i).card * root i)
  have hrowExists (i : ℕ) : ∃ B, rowProperty i B := by
    by_cases hv : valid i
    · obtain ⟨B, hB, hBcard, hBmass⟩ :=
        dep_row_deletion (D.centers i) (D.carriers i) (D.mass i)
          hv.1 hv.2 (bad i) (hbadSubset i)
      refine ⟨B, hB, ?_, ?_⟩
      · intro _
        simpa [SeparatedDepthData.incidenceMass, hmassTotalReal i,
          Nat.cast_mul, root, α] using hBcard
      · intro _ p hp hpn
        simpa [SeparatedDepthData.deletedRowMass, SeparatedDepthData.incidenceMass,
          hmassTotalReal i, Nat.cast_mul, root, α] using hBmass p hp hpn
    · refine ⟨∅, ?_⟩
      simp [rowProperty, hv]
  let badCenters : ℕ → Finset (Point d) := fun i => Classical.choose (hrowExists i)
  have hrowSpec (i : ℕ) : rowProperty i (badCenters i) :=
    Classical.choose_spec (hrowExists i)
  have hbadCentersSmall :
      Framework.LittleO (fun i => (badCenters i).card) (fun i => (D.centers i).card) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ζ hζ
    filter_upwards [hvalid, hrootSmall.def hζ] with i hiv hroot
    have hrootNonneg : 0 ≤ root i := by positivity [root]
    have hroot' : root i ≤ ζ := by
      have hroot'' : ‖root i‖ ≤ ζ * ‖(1 : ℝ)‖ := hroot
      simpa [Real.norm_eq_abs, abs_of_nonneg hrootNonneg] using hroot''
    have hcard := (hrowSpec i).2.1 hiv
    rw [Real.norm_eq_abs]
    calc
      |((badCenters i).card : ℝ)| = (badCenters i).card := abs_of_nonneg (by positivity)
      _ ≤ (D.centers i).card * root i := hcard
      _ ≤ ζ * (D.centers i).card := by
        calc
          _ ≤ (D.centers i).card * ζ := mul_le_mul_of_nonneg_left hroot'
            (show (0 : ℝ) ≤ (D.centers i).card by positivity)
          _ = ζ * (D.centers i).card := by ring
      _ = ζ * |((D.centers i).card : ℝ)| := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ (D.centers i).card by positivity)]
  have hdeletedSmall :
      Framework.UniformLittleO
        (fun i => {p : Point d // p ∈ D.centers i ∧ p ∉ badCenters i})
        (fun i p => D.deletedRowMass i (bad i) p.val)
        (fun i _ => (D.targets i).card) := by
    intro ζ hζ
    have hrootHalf : ∀ᶠ i in atTop, ‖root i‖ ≤ (ζ / 2) * ‖(1 : ℝ)‖ :=
      hrootSmall.def (show 0 < ζ / 2 by linarith)
    filter_upwards [hvalid, hrootHalf] with i hiv hroot p
    have hrootNonneg : 0 ≤ root i := by positivity [root]
    have hroot' : root i ≤ ζ / 2 := by
      have hroot'' : ‖root i‖ ≤ (ζ / 2) * ‖(1 : ℝ)‖ := hroot
      simpa [Real.norm_eq_abs, abs_of_nonneg hrootNonneg] using hroot''
    have hmass := (hrowSpec i).2.2 hiv p.1 p.2.1 p.2.2
    calc
      |D.deletedRowMass i (bad i) p.val| = D.deletedRowMass i (bad i) p.val := by
        apply abs_of_nonneg
        unfold SeparatedDepthData.deletedRowMass
        positivity
      _ ≤ (D.targets i).card * root i := hmass
      _ ≤ ζ * (D.targets i).card := by
        have htargetNonneg : (0 : ℝ) ≤ (D.targets i).card := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hroot' htargetNonneg]
      _ = ζ * |((D.targets i).card : ℝ)| := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ (D.targets i).card by positivity)]
  have hRsafe : ∀ᶠ i in atTop, 1 ≤ R i * Real.exp (η * D.s i) := by
    have hrootHalf : ∀ᶠ i in atTop, ‖root i‖ ≤ (1 / 2 : ℝ) * ‖(1 : ℝ)‖ :=
      hrootSmall.def (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [hsafe, hvalid, hcentersPos, htargetsPos, hrootHalf] with
      i hsi hvi hci hti hri
    have hrootNonneg : 0 ≤ root i := by positivity [root]
    have hrootle : root i ≤ (1 / 2 : ℝ) := by
      have hr : ‖root i‖ ≤ (1 / 2 : ℝ) * ‖(1 : ℝ)‖ := hri
      simpa [Real.norm_eq_abs, abs_of_nonneg hrootNonneg] using hr
    have hcenterNonneg : (0 : ℝ) ≤ (D.centers i).card := Nat.cast_nonneg _
    have hcenterPos : (0 : ℝ) < (D.centers i).card := by
      exact_mod_cast (Nat.pos_of_ne_zero (by omega : (D.centers i).card ≠ 0))
    have hbadLtReal : ((badCenters i).card : ℝ) < (D.centers i).card := by
      have hbadCard := (hrowSpec i).2.1 hvi
      calc
        (badCenters i).card ≤ (D.centers i).card * root i := hbadCard
        _ ≤ (D.centers i).card * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hrootle hcenterNonneg
        _ < (D.centers i).card := by nlinarith
    have hbadLt : (badCenters i).card < (D.centers i).card := by exact_mod_cast hbadLtReal
    obtain ⟨p, hp, hpb⟩ := Finset.exists_mem_notMem_of_card_lt_card hbadLt
    have htargetPosReal : (0 : ℝ) < (D.targets i).card := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hti)
    have hdeleted := (hrowSpec i).2.2 hvi p hp hpb
    have hsplit : D.submass i (D.retained i (bad i) p) +
        D.deletedRowMass i (bad i) p = (D.targets i).card := by
      calc
        _ = (∑ Y ∈ (D.carriers i).filter (fun Y => (p,Y) ∉ bad i),
              (D.mass i Y : ℝ)) +
            ∑ Y ∈ (D.carriers i).filter (fun Y => (p,Y) ∈ bad i),
              (D.mass i Y : ℝ) := by
          simp [SeparatedDepthData.submass, SeparatedDepthData.retained,
            SeparatedDepthData.deletedRowMass]
        _ = ∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) := by
          rw [add_comm, Finset.sum_filter_add_sum_filter_not (D.carriers i)
            (fun Y => (p,Y) ∈ bad i) (fun Y => (D.mass i Y : ℝ))]
        _ = (D.targets i).card := hmassTotalReal i
    have hdeletedLt : D.deletedRowMass i (bad i) p < (D.targets i).card := by
      calc
        D.deletedRowMass i (bad i) p ≤ (D.targets i).card * root i := hdeleted
        _ ≤ (D.targets i).card * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hrootle (Nat.cast_nonneg _)
        _ < (D.targets i).card := by nlinarith
    have hretainedPos : 0 < D.submass i (D.retained i (bad i) p) := by
      linarith [hsplit, hdeletedLt]
    have hpositiveCarrier : ∃ Y ∈ D.retained i (bad i) p, 0 < (D.mass i Y : ℝ) := by
      by_contra hnone
      have hzero : ∀ Y ∈ D.retained i (bad i) p, (D.mass i Y : ℝ) = 0 := by
        intro Y hY
        have hn : ¬ 0 < (D.mass i Y : ℝ) := by
          intro hpos
          exact hnone ⟨Y, hY, hpos⟩
        exact le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
      have hsumzero : D.submass i (D.retained i (bad i) p) = 0 := by
        unfold SeparatedDepthData.submass
        apply Finset.sum_eq_zero
        intro Y hY
        exact hzero Y hY
      linarith
    obtain ⟨Y, hY, _hYmass⟩ := hpositiveCarrier
    have hYcar : Y ∈ D.carriers i := Finset.mem_filter.mp hY |>.1
    have hYpure := D.carrier_pure i Y hYcar
    have hl : 1 ≤ d-j := by have hj := D.j_lt; omega
    have hsafeY := hsi p hp Y hY
    have hgeneric := dep_radial_degree_exists Y hYpure.1 (d-j) hl hYpure.2 p hsafeY.1
    have hdepthLower : 1 ≤ groupDepth p (D.retained i (bad i) p) Y := by
      have hYfilter : Y ∈ (D.retained i (bad i) p).filter
          (fun Z => radialImage p Z = radialImage p Y) := by
        simp [hY]
      have hsum : radialMapDegree p Y ≤ groupDepth p (D.retained i (bad i) p) Y := by
        unfold groupDepth
        exact Finset.single_le_sum (fun Z hZ => Nat.zero_le _) hYfilter
      exact (Nat.succ_le_of_lt hgeneric.1).trans hsum
    have hdepthReal : (1 : ℝ) ≤ (groupDepth p (D.retained i (bad i) p) Y : ℝ) := by
      exact_mod_cast hdepthLower
    exact le_trans hdepthReal hsafeY.2.2
  have hdegreeMargin (ρ : ℝ) (hρ : 0 < ρ) :
      ∀ᶠ i in atTop, 4 * Real.exp (-θ * D.s i) ≤ ρ := by
    let T : ℝ := Real.log (4 / ρ) / θ
    filter_upwards [D.s_grows.eventually (eventually_ge_atTop T)] with i hi
    have hlog : Real.log (4 / ρ) ≤ θ * D.s i := by
      calc
        Real.log (4 / ρ) = θ * (Real.log (4 / ρ) / θ) := by
          field_simp [ne_of_gt hθ]
        _ ≤ θ * D.s i := mul_le_mul_of_nonneg_left hi hθ.le
    have hexp : 4 / ρ ≤ Real.exp (θ * D.s i) := by
      calc
        4 / ρ = Real.exp (Real.log (4 / ρ)) := by rw [Real.exp_log (by positivity)]
        _ ≤ Real.exp (θ * D.s i) := Real.exp_le_exp.mpr hlog
    have hmul : 4 ≤ Real.exp (θ * D.s i) * ρ := (div_le_iff₀ hρ).mp hexp
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (θ * D.s i))).mp
    calc
      Real.exp (θ * D.s i) * (4 * Real.exp (-θ * D.s i)) = 4 := by
        calc
          Real.exp (θ * D.s i) * (4 * Real.exp (-θ * D.s i)) =
              4 * (Real.exp (θ * D.s i) * Real.exp (-θ * D.s i)) := by ring
          _ = 4 := by
            have hcancel : Real.exp (θ * D.s i) * Real.exp (-θ * D.s i) = 1 := by
              rw [← Real.exp_add]
              rw [show θ * D.s i + (-θ * D.s i) = 0 by ring, Real.exp_zero]
            rw [hcancel]
            ring
      _ ≤ Real.exp (θ * D.s i) * ρ := hmul
  refine ⟨bad, badCenters, ?_, hbadSmall, hbadCentersSmall, hdeletedSmall, ?_, ?_⟩
  · intro i
    exact ⟨hbadSubset i, (hrowSpec i).1⟩
  · filter_upwards [hsafe] with i hi
    intro p hp hpb Y hY
    exact (hi p hp Y hY).1
  · intro ρ hρ
    let γ : ℕ → ℝ := fun i => R i * Real.exp (η * D.s i)
    filter_upwards [hvalid, htargetsPos, hRsafe, hsafe, hR,
      D.target_size.1 δ hδ, hbudget.2 δ hδ, hdegreeMargin ρ hρ] with
      i hvi hti hγ hsi hRi htargetLower hsubUpper hmargin
    intro p hp hpb J hJ hJmass
    have hJcar : J ⊆ D.carriers i := by
      intro Y hY
      exact Finset.mem_filter.mp (hJ hY) |>.1
    have hl : 1 ≤ d-j := by have hj := D.j_lt; omega
    have hmassBase :
        D.degreeBudget i * D.tailBudget i * Real.exp (-δ * D.s i) ≤
          (D.targets i).card := by
      have := htargetLower ()
      simpa [hbudgetTail i] using this
    have hexpCut : Real.exp (-2*δ * D.s i) * Real.exp (δ * D.s i) =
        Real.exp (-δ * D.s i) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hraw :
        (ρ * D.degreeBudget i * Real.exp (-2*δ * D.s i)) *
            (D.tailBudget i * Real.exp (δ * D.s i)) ≤
          (AffineFamily.degree J : ℝ) * (D.tailBudget i * Real.exp (δ * D.s i)) := by
      calc
        _ = ρ * (D.degreeBudget i * D.tailBudget i * Real.exp (-δ * D.s i)) := by
          calc
            _ = ρ * (D.degreeBudget i * D.tailBudget i) *
                (Real.exp (-2*δ * D.s i) * Real.exp (δ * D.s i)) := by ring
            _ = ρ * (D.degreeBudget i * D.tailBudget i) * Real.exp (-δ * D.s i) := by
              rw [hexpCut]
            _ = ρ * (D.degreeBudget i * D.tailBudget i * Real.exp (-δ * D.s i)) := by ring
        _ ≤ ρ * (D.targets i).card :=
          mul_le_mul_of_nonneg_left hmassBase hρ.le
        _ ≤ D.submass i J := hJmass
        _ ≤ (AffineFamily.degree J : ℝ) * D.tailBudget i * Real.exp (δ * D.s i) :=
          hsubUpper ⟨J, hJcar⟩
        _ = (AffineFamily.degree J : ℝ) * (D.tailBudget i * Real.exp (δ * D.s i)) := by ring
    have htailPos : 0 < D.tailBudget i := by
      unfold SeparatedDepthData.tailBudget SeparatedDepthData.cutDegree
      apply Finset.prod_pos
      intro t ht
      exact mul_pos (regime.B_pos i) (Real.exp_pos _)
    have hdegreeBudgetPos : 0 < D.degreeBudget i := by
      unfold SeparatedDepthData.degreeBudget SeparatedDepthData.cutDegree
      apply Finset.prod_pos
      intro t ht
      exact mul_pos (regime.B_pos i) (Real.exp_pos _)
    have htailExpPos : 0 < D.tailBudget i * Real.exp (δ * D.s i) :=
      mul_pos htailPos (Real.exp_pos _)
    have hdegreeLower :
        ρ * D.degreeBudget i * Real.exp (-2*δ * D.s i) ≤
          (AffineFamily.degree J : ℝ) := by
      exact le_of_mul_le_mul_right hraw htailExpPos
    have htargetPosReal : (0 : ℝ) < (D.targets i).card := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hti)
    have hmassPosHere : 0 < D.submass i J :=
      lt_of_lt_of_le (mul_pos hρ htargetPosReal) hJmass
    have hdegreeJPos : 0 < (AffineFamily.degree J : ℝ) := by
      by_contra hnot
      have hnonpos : (AffineFamily.degree J : ℝ) ≤ 0 := le_of_not_gt hnot
      have hprodNonpos : (AffineFamily.degree J : ℝ) *
          (D.tailBudget i * Real.exp (δ * D.s i)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hnonpos htailExpPos.le
      linarith [hsubUpper ⟨J, hJcar⟩, hmassPosHere]
    have hJpure : AffineFamily.IsPure J (d-j) := by
      intro Y hY
      exact D.carrier_pure i Y (hJcar hY)
    have himages : ∀ Y ∈ J, (radialImage p Y).dimension = d-j := by
      intro Y hY
      exact (hsi p hp Y (hJ hY)).1
    have hmult : ∀ Y ∈ J, Y.multiplicity p ≤ Y.degree / 2 := by
      intro Y hY
      exact (hsi p hp Y (hJ hY)).2.1
    have hdepthMono (Y : AffineVariety d) :
        groupDepth p J Y ≤ groupDepth p (D.retained i (bad i) p) Y := by
      unfold groupDepth
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro Z hZ
        rcases Finset.mem_filter.mp hZ with ⟨hZJ, hZequal⟩
        exact Finset.mem_filter.mpr ⟨hJ hZJ, hZequal⟩
      · intro Z hZ hZ'
        exact Nat.zero_le _
    let Q : ℕ := Nat.ceil (γ i)
    have hQlower : γ i ≤ (Q : ℝ) := Nat.le_ceil _
    have hQupper : (Q : ℝ) ≤ 2 * γ i := by
      have hceil : Q ≤ Nat.floor (γ i) + 1 := by
        dsimp [Q]
        exact Nat.ceil_le_floor_add_one _
      have hceilReal : (Q : ℝ) ≤ (Nat.floor (γ i) : ℝ) + 1 := by exact_mod_cast hceil
      have hfloor : (Nat.floor (γ i) : ℝ) ≤ γ i := Nat.floor_le (le_trans (by norm_num) hγ)
      nlinarith
    have hdepthQ : ∀ Y ∈ J, (groupDepth p J Y : ℚ) ≤ (Q : ℚ) := by
      intro Y hY
      have hdepthRealRet :
          (groupDepth p (D.retained i (bad i) p) Y : ℝ) ≤ R i * Real.exp (η * D.s i) :=
        (hsi p hp Y (hJ hY)).2.2
      have hdepthReal : (groupDepth p J Y : ℝ) ≤ γ i := by
        calc
          (groupDepth p J Y : ℝ) ≤
              (groupDepth p (D.retained i (bad i) p) Y : ℝ) := by
            exact_mod_cast hdepthMono Y
          _ ≤ γ i := by simpa [γ] using hdepthRealRet
      have hdepthNat : groupDepth p J Y ≤ Q := by
        exact_mod_cast hdepthReal.trans hQlower
      exact_mod_cast hdepthNat
    have hdepthDegree := dep_depth_to_degree J (d-j) hl hJpure p (Q : ℚ)
      himages hmult hdepthQ
    have hdepthDegreeReal : (AffineFamily.degree J : ℝ) ≤
        2 * (Q : ℝ) * (ProjectiveFamily.degree (projectedFamily p J) : ℝ) := by
      exact_mod_cast hdepthDegree
    have hprojectedNonneg :
        (0 : ℝ) ≤ (ProjectiveFamily.degree (projectedFamily p J) : ℝ) := by
      by_contra hneg
      have hprojneg : (ProjectiveFamily.degree (projectedFamily p J) : ℝ) < 0 := lt_of_not_ge hneg
      have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith [hγ, hQlower]
      have hprodneg : 2 * (Q : ℝ) *
          (ProjectiveFamily.degree (projectedFamily p J) : ℝ) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) hprojneg
      linarith [hdepthDegreeReal, hdegreeJPos]
    have hdepthDegreeUpper : (AffineFamily.degree J : ℝ) ≤
        4 * γ i * (ProjectiveFamily.degree (projectedFamily p J) : ℝ) := by
      calc
        (AffineFamily.degree J : ℝ) ≤
            2 * (Q : ℝ) * (ProjectiveFamily.degree (projectedFamily p J) : ℝ) :=
          hdepthDegreeReal
        _ ≤ 4 * γ i * (ProjectiveFamily.degree (projectedFamily p J) : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by nlinarith [hQupper]) hprojectedNonneg
    have hscaleExp : Real.exp (η * D.s i) * Real.exp (-ε * D.s i) =
        Real.exp (-2 * δ * D.s i) * Real.exp (-θ * D.s i) := by
      calc
        _ = Real.exp ((η - ε) * D.s i) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        _ = Real.exp ((-2 * δ - θ) * D.s i) := by
          congr 1
          dsimp [θ]
          <;> ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 1 <;> ring
    have hscaled : 4 * γ i *
        (D.degreeBudget i / R i * Real.exp (-ε * D.s i)) ≤
        ρ * D.degreeBudget i * Real.exp (-2*δ * D.s i) := by
      calc
        _ = D.degreeBudget i * Real.exp (-2*δ * D.s i) *
            (4 * Real.exp (-θ * D.s i)) := by
          have hcancel : (R i * Real.exp (η * D.s i)) *
              (D.degreeBudget i / R i) = D.degreeBudget i * Real.exp (η * D.s i) := by
            field_simp [ne_of_gt hRi]
          calc
            _ = 4 * (R i * Real.exp (η * D.s i)) *
                (D.degreeBudget i / R i) * Real.exp (-ε * D.s i) := by
              dsimp [γ]
              ring
            _ = 4 * ((R i * Real.exp (η * D.s i)) *
                (D.degreeBudget i / R i)) * Real.exp (-ε * D.s i) := by ring
            _ = 4 * (D.degreeBudget i * Real.exp (η * D.s i)) *
                Real.exp (-ε * D.s i) := by rw [hcancel]
            _ = 4 * D.degreeBudget i *
                (Real.exp (η * D.s i) * Real.exp (-ε * D.s i)) := by ring
            _ = 4 * D.degreeBudget i *
                (Real.exp (-2*δ * D.s i) * Real.exp (-θ * D.s i)) := by rw [hscaleExp]
            _ = D.degreeBudget i * Real.exp (-2*δ * D.s i) *
                (4 * Real.exp (-θ * D.s i)) := by ring
        _ ≤ D.degreeBudget i * Real.exp (-2*δ * D.s i) * ρ := by
          exact mul_le_mul_of_nonneg_left hmargin
            (mul_nonneg hdegreeBudgetPos.le (Real.exp_pos _).le)
        _ = ρ * D.degreeBudget i * Real.exp (-2*δ * D.s i) := by ring
    have hmulFinal : 4 * γ i *
        (D.degreeBudget i / R i * Real.exp (-ε * D.s i)) ≤
        4 * γ i * (ProjectiveFamily.degree (projectedFamily p J) : ℝ) :=
      hscaled.trans (hdegreeLower.trans hdepthDegreeUpper)
    have hγpos : 0 < 4 * γ i := by positivity [hγ]
    exact (mul_le_mul_iff_right₀ hγpos).mp hmulFinal

/-- `dep:projected-degree`, depth.tex:51–84,86–474; sparse-cones.tex:658–695,795–928.
The inputs are the primitive profile/generic-list interfaces in DepthHypotheses,
not an assumed projected-degree or actual-center depth bound. -/
theorem dep_projected_degree {d j : ℕ} {regime : Regime d}
    (D : SeparatedDepthData regime j) (hD : D.Hypotheses) (ε : ℝ) (hε : 0 < ε) :
    D.ProjectedDegreeConclusion D.firstRate ε ∧
      (Tendsto (fun i => D.v i / D.s i) atTop (𝓝 0) →
        D.ProjectedDegreeConclusion D.narrowRate ε) ∧
      (Tendsto (fun i => D.s i / D.v i) atTop (𝓝 0) →
        0 < D.b ⟨j, D.j_lt⟩ → d-j < d-1 → D.ProjectedDegreeConclusion D.wideRate ε) := by
  have hfirstPos : ∀ᶠ i in atTop, 0 < D.firstRate i := by
    filter_upwards [] with i
    unfold SeparatedDepthData.firstRate SeparatedDepthData.cutDegree
    exact mul_pos (regime.B_pos i) (Real.exp_pos _)
  have hnarrowPos : ∀ᶠ i in atTop, 0 < D.narrowRate i := by
    filter_upwards [] with i
    unfold SeparatedDepthData.narrowRate
    exact mul_pos (regime.B_pos i) (Real.exp_pos _)
  have hwidePos : ∀ᶠ i in atTop, 0 < D.wideRate i := by
    filter_upwards [] with i
    unfold SeparatedDepthData.wideRate
    exact mul_pos (regime.B_pos i) (Real.exp_pos _)
  refine ⟨dep_degree_assembly D hD.1 D.firstRate hfirstPos
      (dep_first_depth D hD) ε hε, ?_, ?_⟩
  · intro hseparated
    exact dep_degree_assembly D hD.1 D.narrowRate hnarrowPos
      (dep_narrow_depth D hD hseparated) ε hε
  · intro hseparated hnext hlow
    exact dep_degree_assembly D hD.1 D.wideRate hwidePos
      (dep_wide_depth D hD hseparated hnext hlow) ε hε

end
end DistinctDistances.TrackA
