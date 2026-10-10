import DistinctDistances.TrackA.Definitions
import DistinctDistances.TrackA.CompressionDescent
import DistinctDistances.TrackA.CompressionFrobenius
import DistinctDistances.TrackA.GAProjAux

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- `poly:compression.failed-separation`, polynomial.tex:661–670.
Finite-dimensional duality; needed to preserve failure under specialization. -/
theorem poly_compression_failed_separation {n : ℕ} {F : Type*} [Field F]
    (S : Finset (FieldPoint n F)) (x : FieldPoint n F) (q : ℕ)
    (hfailure : ∀ g : FieldPoly n F, g.totalDegree ≤ q →
      (∀ z ∈ S, MvPolynomial.eval z g = 0) → MvPolynomial.eval x g = 0) :
    ∃ weights : S → F, ∀ g : FieldPoly n F, g.totalDegree ≤ q →
      MvPolynomial.eval x g = ∑ z : S, weights z * MvPolynomial.eval z.val g :=
  poly_compression_failed_separation_proof S x q hfailure

/-- `poly:compression.positive-characteristic`, polynomial.tex:630–659.
Grade lead: Frobenius digit decomposition and the translated p-power quotient basis. -/
theorem poly_compression_positive_characteristic {F : Type*} [Field F] [IsAlgClosed F]
    (n p : ℕ) (hp : Nat.Prime p) [CharP F p]
    (S : Finset (FieldPoint n F)) (x : FieldPoint n F) (f : FieldPoly n F)
    (E r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ p) (hf : f.totalDegree ≤ E)
    (horder : ∀ z ∈ S, OrderAtLeast f z r) (hx : MvPolynomial.eval x f ≠ 0) :
    ∃ g : FieldPoly n F, r * g.totalDegree ≤ (n+1)*E ∧
      (∀ z ∈ S, MvPolynomial.eval z g = 0) ∧ MvPolynomial.eval x g ≠ 0 := by
  exact compression_positive_characteristic_core n p hp S x f E r hr hrp hf horder hx

/-- The only nonmaximal prime of ℤ is zero, whose Jacobson radical
vanishes since an integer x with 3x+1 a unit must be zero. -/
private theorem compression_integers_jacobson : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  letI : P.IsPrime := hP
  by_cases hbot : P = ⊥
  · subst P
    apply le_antisymm ?_ Ideal.le_jacobson
    intro x hx
    have hu := (Ideal.mem_jacobson_bot.mp hx) (3 : ℤ)
    have hunit := Int.isUnit_iff.mp hu
    have hz : x = 0 := by rcases hunit with h | h <;> omega
    simpa using hz
  · letI : P.IsMaximal := IsPrime.to_maximal_ideal hbot
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- `poly:compression.specialization`, polynomial.tex:672–691.
Invert the bound factorial and use finite-type Jacobson residue fields. -/
theorem poly_compression_specialization (R : Subalgebra ℤ ℂ) (hfg : R.FG) (bound : ℕ) :
    ∃ (p : ℕ) (hp : Nat.Prime p), bound ≤ p ∧
      (letI : Fact (Nat.Prime p) := ⟨hp⟩;
        Nonempty (R →+* AlgebraicClosure (ZMod p))) := by
  letI : IsJacobsonRing ℤ := compression_integers_jacobson
  let d : ℂ := (bound.factorial : ℂ)
  let S : Subalgebra ℤ ℂ := R ⊔ Algebra.adjoin ℤ {d⁻¹}
  have hSfg : S.FG := hfg.sup (by
    simpa using Subalgebra.fg_adjoin_finset (R := ℤ) ({d⁻¹} : Finset ℂ))
  letI : Algebra.FiniteType ℤ S := S.fg_iff_finiteType.mp hSfg
  obtain ⟨M, hM⟩ := Ideal.exists_maximal S
  letI : M.IsMaximal := hM
  let K := S ⧸ M
  letI : Field K := Ideal.Quotient.field M
  letI : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ K
  rcases CharP.exists' K with hzero | ⟨p, hp, hchar⟩
  · letI : CharZero K := hzero
    exact (Int.not_isField (isField_of_isIntegral_of_isField
      (FaithfulSMul.algebraMap_injective ℤ K) (Field.toIsField K))).elim
  · letI : Fact p.Prime := hp
    letI : CharP K p := hchar
    have hinv : d⁻¹ ∈ S :=
      (show Algebra.adjoin ℤ {d⁻¹} ≤ S from le_sup_right)
        (Algebra.subset_adjoin (by simp))
    let invd : S := ⟨d⁻¹, hinv⟩
    have hid : (bound.factorial : S) * invd = 1 := by
      apply Subtype.ext
      change d * d⁻¹ = 1
      exact mul_inv_cancel₀ (by
        change (bound.factorial : ℂ) ≠ 0
        exact_mod_cast Nat.factorial_ne_zero bound)
    have hnz : (bound.factorial : K) ≠ 0 := by
      intro hz
      have h := congrArg (Ideal.Quotient.mk M) hid
      exact zero_ne_one (by
        simpa only [map_mul, map_natCast, map_one, hz, zero_mul] using h)
    have hbound : bound ≤ p := by
      by_contra! hlt
      exact hnz ((CharP.cast_eq_zero_iff K p _).mpr
        (Nat.dvd_factorial hp.out.pos (Nat.le_of_lt hlt)))
    letI : Algebra (ZMod p) K := (ZMod.castHom (m := p) dvd_rfl K).toAlgebra
    letI : Module.IsTorsionFree (ZMod p) K :=
      (Module.isTorsionFree_iff_algebraMap_injective).mpr (RingHom.injective _)
    letI : Algebra.FiniteType (ZMod p) K :=
      Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) K
    letI : Module.Finite (ZMod p) K :=
      finite_of_finite_type_of_isJacobsonRing (ZMod p) K
    let embedding : K →+* AlgebraicClosure (ZMod p) :=
      (IsAlgClosed.lift : K →ₐ[ZMod p] AlgebraicClosure (ZMod p)).toRingHom
    refine ⟨p, hp.out, hbound, ⟨embedding.comp
      ((Ideal.Quotient.mk M).comp (Subalgebra.inclusion (show R ≤ S from le_sup_left)).toRingHom)⟩⟩

/-- `poly:compression`, polynomial.tex:616–701; depth.tex:451–462.
The multiplicative natural bound is exactly deg(g) ≤ (n+1)E/r with r positive. -/
theorem poly_compression {n : ℕ} (S : Finset (Point n)) (x : Point n) (f : Poly n)
    (E r : ℕ) (hr : 1 ≤ r) (hf : f.totalDegree ≤ E)
    (horder : ∀ z ∈ S, OrderAtLeast f z r) (hx : MvPolynomial.eval x f ≠ 0) :
    ∃ g : Poly n, r * g.totalDegree ≤ (n+1)*E ∧
      (∀ z ∈ S, MvPolynomial.eval z g = 0) ∧ MvPolynomial.eval x g ≠ 0 := by
  by_contra h
  let q := (n+1)*E/r
  have hfailure : ∀ g : Poly n, g.totalDegree ≤ q →
      (∀ z ∈ S, MvPolynomial.eval z g = 0) → MvPolynomial.eval x g = 0 := by
    intro g hg hzero
    by_contra hstar
    apply h
    refine ⟨g, ?_, hzero, hstar⟩
    calc
      r*g.totalDegree ≤ r*q := Nat.mul_le_mul_left r hg
      _ ≤ (n+1)*E := by
        simpa [q, Nat.mul_comm] using Nat.div_mul_le_self ((n+1)*E) r
  obtain ⟨weights, hweights⟩ := poly_compression_failed_separation S x q hfailure
  have hmoments (a : Fin n →₀ ℕ) (ha : a.degree ≤ q) :
      MvPolynomial.eval x (MvPolynomial.monomial a 1) =
        ∑ z : S, weights z * MvPolynomial.eval z.val (MvPolynomial.monomial a 1) := by
    apply hweights
    simpa [MvPolynomial.totalDegree_monomial a one_ne_zero,
      Finsupp.degree_apply, Finsupp.sum] using ha
  obtain ⟨R, hR, fR, xR, zR, weightsR, inv, hfR, hxR, hzR, hunit, horders, hmomentsR⟩ :=
    compression_finite_data S x f r q weights horder hx hmoments
  obtain ⟨p, hp, hpr, hφ⟩ := poly_compression_specialization R hR r
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ⟩ := hφ
  let K := AlgebraicClosure (ZMod p)
  let f' : FieldPoly n K := MvPolynomial.map φ fR
  let x' : FieldPoint n K := φ ∘ xR
  let S' : Finset (FieldPoint n K) := Finset.univ.image (fun z : S => φ ∘ zR z)
  have hdegree : f'.totalDegree ≤ E :=
    (compression_map_degree_le φ fR).trans ((compression_lift_degree R fR f hfR).le.trans hf)
  have hunit' : MvPolynomial.eval x' f' * φ inv = 1 := by
    have he := congrArg φ hunit
    simpa only [map_mul, map_one, MvPolynomial.map_eval] using he
  have hx' : MvPolynomial.eval x' f' ≠ 0 := by
    intro hz
    exact zero_ne_one (by simpa only [hz, zero_mul] using hunit')
  have horder' : ∀ z ∈ S', OrderAtLeast f' z r := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    exact compression_order_specialize φ fR (zR a) r (horders a)
  obtain ⟨g, hg, hgzero, hgstar⟩ :=
    poly_compression_positive_characteristic n p hp S' x' f' E r hr hpr hdegree horder' hx'
  have hqg : g.totalDegree ≤ q := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < r)).mpr
    simpa only [Nat.mul_comm] using hg
  have heval := compression_eval_from_moments q xR zR weightsR hmomentsR φ g hqg
  have hgx : MvPolynomial.eval x' g = 0 := by
    change MvPolynomial.eval (φ ∘ xR) g = 0
    rw [heval]
    apply Finset.sum_eq_zero
    intro z _
    rw [hgzero (φ ∘ zR z) (Finset.mem_image_of_mem _ (Finset.mem_univ z)), mul_zero]
  exact hgstar hgx

/-- `poly:matrix-multiplicity.minor`, polynomial.tex:703–721; depth.tex:440–449.
The guard h ≤ q prevents natural subtraction from changing the rank condition. -/
theorem poly_matrix_multiplicity {n a b q h : ℕ}
    (A : Matrix (Fin a) (Fin b) (Poly n)) (p : Point n)
    (rows : Fin q ↪ Fin a) (cols : Fin q ↪ Fin b) (hhq : h ≤ q)
    (hrank : Matrix.rank (fun i j => MvPolynomial.eval p (A i j)) ≤ q-h) :
    OrderAtLeast (Matrix.det (A.submatrix rows cols)) p h :=
  poly_matrix_multiplicity_proof A p rows cols hhq hrank

/-- `poly:matrix-multiplicity.compression`, polynomial.tex:707–710; depth.tex:435–458. -/
theorem poly_matrix_multiplicity_compression {n a b q h : ℕ}
    (A : Matrix (Fin a) (Fin b) (Poly n)) (S : Finset (Point n)) (x : Point n)
    (rows : Fin q ↪ Fin a) (cols : Fin q ↪ Fin b) (hh : 1 ≤ h) (hhq : h ≤ q)
    (E : ℕ) (hdegree : (Matrix.det (A.submatrix rows cols)).totalDegree ≤ E)
    (hrank : ∀ p ∈ S, Matrix.rank (fun i j => MvPolynomial.eval p (A i j)) ≤ q-h)
    (hx : MvPolynomial.eval x (Matrix.det (A.submatrix rows cols)) ≠ 0) :
    ∃ g : Poly n, h * g.totalDegree ≤ (n+1)*E ∧
      (∀ z ∈ S, MvPolynomial.eval z g = 0) ∧ MvPolynomial.eval x g ≠ 0 :=
  poly_compression S x (Matrix.det (A.submatrix rows cols)) E h hh hdegree
    (fun z hz => poly_matrix_multiplicity A z rows cols hhq (hrank z hz)) hx

end
end DistinctDistances.TrackA
