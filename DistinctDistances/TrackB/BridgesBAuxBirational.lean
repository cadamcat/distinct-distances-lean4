import DistinctDistances.TrackB.BridgesBMixedHilbert
import DistinctDistances.TrackB.BridgesBAux

/-!
Support for `Request.pairHilbert_birational_top_coefficient` (lane bridges-b).

For a fixed large first degree `s` the pair Hilbert function is squeezed between
`H_Y(t)` and `H_Y(t + s E)`:
* lower bound: multiplication by `x_a^s` embeds the restriction space of `Y`;
* upper bound: the second projection is birational, so every ratio `x_i / x_a` is a
  quotient `b_i / h_i` of homogeneous forms on `Y`, and substituting these ratios
  embeds the pair restriction space into a restriction space of `Y`.
Birationality is proved by lying over: if a ratio had degree `r ≥ 2` over the
function field of `Y`, the `r` distinct roots of its specialized minimal polynomial
at a generic point of `Y` would give `r` distinct lifts, contradicting `hgen`.
Algebraicity of the ratios comes from the total-degree bound on the Hilbert polynomial.
-/

namespace DistinctDistances.TrackB.BridgesBBir

open scoped BigOperators

set_option autoImplicit false
noncomputable section

variable {n m : ℕ}

/-! ### Bigraded monomial spaces -/

/-- Monomials of bidegree `(s,t)`. -/
def bideg (n m s t : ℕ) : Set (Fin (n + m) →₀ ℕ) :=
  {d | (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧ (∑ i : Fin m, d (Fin.natAdd n i)) = t}

/-- Bihomogeneous polynomials of bidegree `(s,t)`. -/
abbrev BiSpace (n m s t : ℕ) : Submodule ℂ (Poly (n + m)) :=
  MvPolynomial.restrictSupport ℂ (bideg n m s t)

/-- The actual bigraded vanishing ideal of a pair set. -/
abbrev pairIdeal (T : Set (ProjectivePoint n × ProjectivePoint m)) : Ideal (Poly (n + m)) :=
  MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T)

/-- Second-factor polynomials, viewed on the pair space. -/
abbrev yRen : Poly m →ₐ[ℂ] Poly (n + m) := MvPolynomial.rename (Fin.natAdd n)

theorem pairSection_eq (T : Set (ProjectivePoint n × ProjectivePoint m)) (s t : ℕ) :
    pairSection T s t =
      (BiSpace n m s t).map (Ideal.Quotient.mkₐ ℂ (pairIdeal T)).toLinearMap := rfl

theorem castAdd_ne_natAdd (i : Fin n) (k : Fin m) : Fin.castAdd m i ≠ Fin.natAdd n k := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
  have := i.2
  omega

theorem natAdd_ne_castAdd (k : Fin m) (i : Fin n) : Fin.natAdd n k ≠ Fin.castAdd m i :=
  fun h => castAdd_ne_natAdd i k h.symm

theorem biSpace_finite (s t : ℕ) : Module.Finite ℂ (BiSpace n m s t) := by
  have hS : BiSpace n m s t ≤ MvPolynomial.restrictDegree (Fin (n + m)) ℂ (s + t) := by
    apply MvPolynomial.restrictSupport_mono
    intro d hd i
    have htotal : (∑ j : Fin (n + m), d j) = s + t := by
      rw [Fin.sum_univ_add, hd.1, hd.2]
    calc
      d i ≤ ∑ j : Fin (n + m), d j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = s + t := htotal
  exact Module.Finite.of_injective (Submodule.inclusion hS) (Submodule.inclusion_injective hS)

theorem mul_mem_biSpace {s t s' t' : ℕ} {f g : Poly (n + m)}
    (hf : f ∈ BiSpace n m s t) (hg : g ∈ BiSpace n m s' t') :
    f * g ∈ BiSpace n m (s + s') (t + t') := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff] at hf hg ⊢
  intro d hd
  obtain ⟨d1, hd1, d2, hd2, rfl⟩ :=
    Finset.mem_add.mp (MvPolynomial.support_mul f g (Finset.mem_coe.mp hd))
  obtain ⟨h1, h1'⟩ := hf (Finset.mem_coe.mpr hd1)
  obtain ⟨h2, h2'⟩ := hg (Finset.mem_coe.mpr hd2)
  refine ⟨?_, ?_⟩
  · simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    omega
  · simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    omega

theorem one_mem_biSpace : (1 : Poly (n + m)) ∈ BiSpace n m 0 0 := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro d hd
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply] at hd
  have hd0 : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst hd0
  simp [bideg]

theorem X_castAdd_mem_biSpace (i : Fin n) :
    (MvPolynomial.X (Fin.castAdd m i) : Poly (n + m)) ∈ BiSpace n m 1 0 := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff, MvPolynomial.support_X]
  intro d hd
  rw [Finset.coe_singleton, Set.mem_singleton_iff] at hd
  subst hd
  refine ⟨?_, ?_⟩
  · simp [Finsupp.single_apply, Fin.castAdd_inj]
  · simp only [Finsupp.single_apply, if_neg (castAdd_ne_natAdd i _), Finset.sum_const_zero]

theorem X_natAdd_mem_biSpace (k : Fin m) :
    (MvPolynomial.X (Fin.natAdd n k) : Poly (n + m)) ∈ BiSpace n m 0 1 := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff, MvPolynomial.support_X]
  intro d hd
  rw [Finset.coe_singleton, Set.mem_singleton_iff] at hd
  subst hd
  refine ⟨?_, ?_⟩
  · simp [Finsupp.single_apply, natAdd_ne_castAdd]
  · simp [Finsupp.single_apply, Fin.natAdd_inj]

theorem pow_mem_biSpace {s t : ℕ} {f : Poly (n + m)} (hf : f ∈ BiSpace n m s t) (e : ℕ) :
    f ^ e ∈ BiSpace n m (e * s) (e * t) := by
  induction e with
  | zero => simpa using (one_mem_biSpace (n := n) (m := m))
  | succ e ih =>
    rw [pow_succ]
    have h := mul_mem_biSpace ih hf
    convert h using 2 <;> ring

theorem biSpace_congr {s t s' t' : ℕ} (hs : s = s') (ht : t = t') {f : Poly (n + m)}
    (hf : f ∈ BiSpace n m s t) : f ∈ BiSpace n m s' t' := by
  subst hs ht
  exact hf

theorem yRen_mem_biSpace {t : ℕ} {b : Poly m} (hb : b.IsHomogeneous t) :
    (yRen b : Poly (n + m)) ∈ BiSpace n m 0 t := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro d hd
  rw [Finset.mem_coe, MvPolynomial.support_rename_of_injective (Fin.natAdd_injective m n)]
    at hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
  have hdeg : (∑ k : Fin m, e k) = t := by
    have h := hb (MvPolynomial.mem_support_iff.mp he)
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
    simp
  refine ⟨?_, ?_⟩
  · apply Finset.sum_eq_zero
    intro i _
    apply Finsupp.mapDomain_notin_range
    rintro ⟨k, hk⟩
    exact castAdd_ne_natAdd i k hk.symm
  · rw [← hdeg]
    apply Finset.sum_congr rfl
    intro k _
    exact Finsupp.mapDomain_apply_of_injective (Fin.natAdd_injective m n) e k

/-- Scaling the first block of variables by `c` multiplies a bidegree-`(s,t)`
polynomial by `c^s`. -/
theorem aeval_xscale {R : Type*} [CommRing R] [Algebra ℂ R] {s t : ℕ} {f : Poly (n + m)}
    (hf : f ∈ BiSpace n m s t) (c : R) (x : Fin n → R) (y : Fin m → R) :
    MvPolynomial.aeval (Fin.addCases (fun i => c * x i) y : Fin (n + m) → R) f =
      c ^ s * MvPolynomial.aeval (Fin.addCases x y : Fin (n + m) → R) f := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff] at hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hs, -⟩ := hf (Finset.mem_coe.mpr hd)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_add, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hs]
  ring

/-! ### Dimension comparisons -/

theorem finrank_range_le_of_ker_le {V W₁ W₂ : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    (f : V →ₗ[ℂ] W₁) (g : V →ₗ[ℂ] W₂) (h : LinearMap.ker g ≤ LinearMap.ker f) :
    Module.finrank ℂ (LinearMap.range f) ≤ Module.finrank ℂ (LinearMap.range g) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  have h3 := Submodule.finrank_mono h
  omega

/-- Upper bound: an algebra map to the second factor which is injective modulo the
two ideals on bidegree `(s,t)` and lands in degree `D`. -/
theorem pairHilbert_le_hilbert (T : Set (ProjectivePoint n × ProjectivePoint m))
    (Y : ProjectiveVariety m) (Φ : Poly (n + m) →ₐ[ℂ] Poly m) (s t D : ℕ)
    (hdeg : ∀ f ∈ BiSpace n m s t, (Φ f).IsHomogeneous D)
    (hker : ∀ f ∈ BiSpace n m s t, Φ f ∈ Y.ideal → f ∈ pairIdeal T) :
    pairHilbert T s t ≤ Y.hilbert D := by
  classical
  haveI := biSpace_finite (n := n) (m := m) s t
  let V := BiSpace n m s t
  let f₁ : V →ₗ[ℂ] Poly (n + m) ⧸ pairIdeal T :=
    (Ideal.Quotient.mkₐ ℂ (pairIdeal T)).toLinearMap ∘ₗ V.subtype
  let g₁ : V →ₗ[ℂ] Poly m ⧸ Y.ideal :=
    (Ideal.Quotient.mkₐ ℂ Y.ideal).toLinearMap ∘ₗ Φ.toLinearMap ∘ₗ V.subtype
  have hf₁ : LinearMap.range f₁ = pairSection T s t := by
    rw [pairSection_eq, LinearMap.range_comp, Submodule.range_subtype]
  have hg₁ : LinearMap.range g₁ ≤ Y.restrictionSpace D := by
    rintro _ ⟨v, rfl⟩
    exact ⟨Φ v, (MvPolynomial.mem_homogeneousSubmodule D _).mpr (hdeg v v.2), rfl⟩
  have hker' : LinearMap.ker g₁ ≤ LinearMap.ker f₁ := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 : Φ v ∈ Y.ideal := Ideal.Quotient.eq_zero_iff_mem.mp hv
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker v v.2 h1)
  have hle := finrank_range_le_of_ker_le f₁ g₁ hker'
  rw [hf₁] at hle
  calc pairHilbert T s t = Module.finrank ℂ (pairSection T s t) := rfl
    _ ≤ Module.finrank ℂ (LinearMap.range g₁) := hle
    _ ≤ Module.finrank ℂ (Y.restrictionSpace D) := Submodule.finrank_mono hg₁
    _ = Y.hilbert D := rfl

/-- Lower bound: `r` first-factor forms of degree `s`, independent over the second
factor modulo the ideals, embed `r` copies of the restriction space of `Y`. -/
theorem mul_hilbert_le_pairHilbert (T : Set (ProjectivePoint n × ProjectivePoint m))
    (Y : ProjectiveVariety m) (hYJ : ∀ b ∈ Y.ideal, yRen b ∈ pairIdeal T)
    {r s : ℕ} (w : Fin r → Poly (n + m)) (hw : ∀ k, w k ∈ BiSpace n m s 0)
    (hind : ∀ b : Fin r → Poly m, (∑ k, w k * yRen (b k)) ∈ pairIdeal T →
      ∀ k, b k ∈ Y.ideal) (t : ℕ) :
    r * Y.hilbert t ≤ pairHilbert T s t := by
  classical
  haveI := biSpace_finite (n := n) (m := m) s t
  let Q := Y.restrictionSpace t
  let J := pairIdeal T
  let ι : (Poly m ⧸ Y.ideal) →ₐ[ℂ] (Poly (n + m) ⧸ J) :=
    Ideal.quotientMapₐ J (yRen (n := n)) (fun b hb => hYJ b hb)
  let Λ : (Fin r → Q) →ₗ[ℂ] (Poly (n + m) ⧸ J) :=
    ∑ k, (LinearMap.mulLeft ℂ (Ideal.Quotient.mk J (w k))) ∘ₗ ι.toLinearMap ∘ₗ Q.subtype ∘ₗ
      LinearMap.proj k
  have hΛ : ∀ β : Fin r → Q, Λ β = ∑ k, Ideal.Quotient.mk J (w k) * ι (β k) := by
    intro β
    simp [Λ, LinearMap.sum_apply]
  have hmkι : ∀ b : Poly m, ι (Ideal.Quotient.mk Y.ideal b) = Ideal.Quotient.mk J (yRen b) := by
    intro b
    rfl
  have hrange : ∀ β, Λ β ∈ pairSection T s t := by
    intro β
    have hrep : ∀ k, ∃ b : Poly m, b.IsHomogeneous t ∧
        Ideal.Quotient.mk Y.ideal b = (β k : Poly m ⧸ Y.ideal) := by
      intro k
      obtain ⟨b, hb, hbeq⟩ := Submodule.mem_map.mp (β k).2
      exact ⟨b, (MvPolynomial.mem_homogeneousSubmodule t b).mp hb, hbeq⟩
    choose b hb hbeq using hrep
    rw [hΛ]
    have hsum : (∑ k, Ideal.Quotient.mk J (w k) * ι (β k)) =
        Ideal.Quotient.mkₐ ℂ J (∑ k, w k * yRen (b k)) := by
      simp only [map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [← hbeq k, hmkι]
      rfl
    rw [hsum]
    refine Submodule.mem_map.mpr ⟨_, ?_, rfl⟩
    apply Submodule.sum_mem
    intro k _
    exact biSpace_congr (by simp) (by simp)
      (mul_mem_biSpace (hw k) (yRen_mem_biSpace (n := n) (hb k)))
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro β hβ
    rw [LinearMap.mem_ker] at hβ
    have hrep : ∀ k, ∃ b : Poly m, Ideal.Quotient.mk Y.ideal b = (β k : Poly m ⧸ Y.ideal) :=
      fun k => Ideal.Quotient.mk_surjective _
    choose b hbeq using hrep
    have hmem : (∑ k, w k * yRen (b k)) ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hβ, hΛ]
      simp only [map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [← hbeq k, hmkι]
    have hall := hind b hmem
    funext k
    apply Subtype.ext
    rw [← hbeq k]
    simp only [Pi.zero_apply, ZeroMemClass.coe_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall k)
  let Λ' : (Fin r → Q) →ₗ[ℂ] pairSection T s t := Λ.codRestrict _ hrange
  have hinj' : Function.Injective Λ' := by
    intro a b h
    apply hinj
    exact congrArg Subtype.val h
  have hle := LinearMap.finrank_le_finrank_of_injective hinj'
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hle
  exact hle

/-! ### Coefficient comparisons -/

theorem coeff_le_of_eventually_le (p q : Polynomial ℚ) (d N : ℕ) (hp : p.natDegree ≤ d)
    (hq : q.natDegree ≤ d) (h : ∀ t : ℕ, N ≤ t → p.eval (t : ℚ) ≤ q.eval (t : ℚ)) :
    p.coeff d ≤ q.coeff d := by
  set r := q - p with hr_def
  have hr : r.natDegree ≤ d := (Polynomial.natDegree_sub_le q p).trans (max_le hq hp)
  have hcoeff : r.coeff d = q.coeff d - p.coeff d := Polynomial.coeff_sub q p d
  have hnn : 0 ≤ r.coeff d := by
    by_cases hrd : r.natDegree = d
    · have hlead := OAI.PiExponentJets.W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg
        r N (fun t ht => by
          rw [hr_def, Polynomial.eval_sub]
          linarith [h t ht])
      rw [Polynomial.leadingCoeff, hrd] at hlead
      exact hlead
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne hr hrd)]
  linarith

theorem comp_shift_natDegree (p : Polynomial ℚ) (c : ℚ) :
    (p.comp (Polynomial.X + Polynomial.C c)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]

theorem comp_shift_coeff (p : Polynomial ℚ) (c : ℚ) :
    (p.comp (Polynomial.X + Polynomial.C c)).coeff p.natDegree = p.coeff p.natDegree := by
  have h := Polynomial.leadingCoeff_comp (p := p)
    (q := Polynomial.X + Polynomial.C c) (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero)
  rw [Polynomial.leadingCoeff_X_add_C, one_pow, mul_one] at h
  rw [Polynomial.leadingCoeff, comp_shift_natDegree] at h
  exact h

/-- Lower comparison of the pure top coefficient with a multiple of the Hilbert
polynomial of the second factor. -/
theorem mul_coeff_le_top (P : BaseHilbertPolynomial) {d : ℕ} (hdeg : P.totalDegree ≤ d)
    (H : ℕ → ℕ → ℕ) (N : ℕ)
    (hP : ∀ s t : ℕ, N ≤ s → N ≤ t → BridgesBMixed.evalPair P s t = (H s t : ℚ))
    (hY : ℕ → ℕ) (HP : Polynomial ℚ) (hHP : HP.natDegree = d) (NY : ℕ)
    (hHPev : ∀ t : ℕ, NY < t → (hY t : ℚ) = HP.eval (t : ℚ))
    (s r : ℕ) (hs : N ≤ s) (hlow : ∀ t, r * hY t ≤ H s t) :
    (r : ℚ) * HP.coeff d ≤
      P.coeff (Finsupp.single 0 0 + Finsupp.single 1 d) := by
  rw [← BridgesBMixed.sliceT_coeff_top P s d hdeg, ← Polynomial.coeff_C_mul]
  apply coeff_le_of_eventually_le _ _ d (N + NY + 1)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hHP.le
  · exact (BridgesBMixed.sliceT_natDegree_le P s).trans hdeg
  · intro t ht
    rw [Polynomial.eval_C_mul, BridgesBMixed.sliceT_eval, hP s t hs (by omega),
      ← hHPev t (by omega)]
    exact_mod_cast hlow t

/-- Upper comparison of the pure top coefficient with a shifted Hilbert polynomial. -/
theorem top_le_coeff (P : BaseHilbertPolynomial) {d : ℕ} (hdeg : P.totalDegree ≤ d)
    (H : ℕ → ℕ → ℕ) (N : ℕ)
    (hP : ∀ s t : ℕ, N ≤ s → N ≤ t → BridgesBMixed.evalPair P s t = (H s t : ℚ))
    (hY : ℕ → ℕ) (HP : Polynomial ℚ) (hHP : HP.natDegree = d) (NY : ℕ)
    (hHPev : ∀ t : ℕ, NY < t → (hY t : ℚ) = HP.eval (t : ℚ))
    (s e : ℕ) (hs : N ≤ s) (hup : ∀ t, H s t ≤ hY (t + e)) :
    P.coeff (Finsupp.single 0 0 + Finsupp.single 1 d) ≤ HP.coeff d := by
  rw [← BridgesBMixed.sliceT_coeff_top P s d hdeg]
  have hc := comp_shift_coeff HP (e : ℚ)
  rw [hHP] at hc
  rw [← hc]
  apply coeff_le_of_eventually_le _ _ d (N + NY + 1)
  · exact (BridgesBMixed.sliceT_natDegree_le P s).trans hdeg
  · rw [comp_shift_natDegree, hHP]
  · intro t ht
    rw [BridgesBMixed.sliceT_eval, hP s t hs (by omega), Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have h := hHPev (t + e) (by omega)
    push_cast at h
    rw [← h]
    exact_mod_cast hup t

/-! ### Points of the pair set and of the second factor -/

section Points

variable (T : Set (ProjectivePoint n × ProjectivePoint m)) (Y : ProjectiveVariety m)

theorem joinPoints_comp_natAdd (x : Point n) (y : Point m) :
    (joinPoints x y ∘ Fin.natAdd n : Fin m → ℂ) = y := by
  funext k
  simp [joinPoints]

theorem eval_join_yRen (x : Point n) (y : Point m) (b : Poly m) :
    MvPolynomial.aeval (joinPoints x y) (yRen b : Poly (n + m)) = MvPolynomial.aeval y b := by
  rw [MvPolynomial.aeval_rename, joinPoints_comp_natAdd]

theorem join_mem (x : Point n) (y : Point m) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈ T) :
    joinPoints x y ∈ pairRepresentatives T := ⟨x, y, hx, hy, h, rfl⟩

theorem yRen_mem_of_mem (hproj : ∀ p q, (p, q) ∈ T → q ∈ Y.points) {b : Poly m}
    (hb : b ∈ Y.ideal) : (yRen b : Poly (n + m)) ∈ pairIdeal T := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro w ⟨x, y, hx, hy, hmem, rfl⟩
  rw [eval_join_yRen]
  exact (MvPolynomial.mem_zeroLocus_iff.mp (hproj _ _ hmem y hy rfl)) b hb

/-- A nonzero representative of a point of `Y` where `g` does not vanish has a lift. -/
theorem exists_lift {g : Poly m} {D : ℕ} (hhom : g.IsHomogeneous D)
    (hgen : ∀ q ∈ Y.points, MvPolynomial.aeval q.rep g ≠ 0 →
      ∃! p : ProjectivePoint n, (p, q) ∈ T)
    (v : Point m) (hv : v ≠ 0) (hvY : Projectivization.mk ℂ v hv ∈ Y.points)
    (hgv : MvPolynomial.aeval v g ≠ 0) :
    ∃ x : Point n, ∃ hx : x ≠ 0, (Projectivization.mk ℂ x hx, Projectivization.mk ℂ v hv) ∈ T := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  have hrep : MvPolynomial.aeval (Projectivization.mk ℂ v hv).rep g ≠ 0 := by
    rw [← ha, Units.smul_def, BridgesB.aeval_smul_of_isHomogeneous hhom]
    exact mul_ne_zero (pow_ne_zero _ a.ne_zero) hgv
  obtain ⟨p, hp, -⟩ := hgen _ hvY hrep
  refine ⟨p.rep, p.rep_nonzero, ?_⟩
  rw [Projectivization.mk_rep]
  exact hp

/-- Second-factor polynomials vanishing on the pair set vanish on `Y`. -/
theorem mem_of_yRen_mem (hY : Y.IsIrreducible) {g : Poly m} {D : ℕ}
    (hhom : g.IsHomogeneous D) (hg : g ∉ Y.ideal)
    (hgen : ∀ q ∈ Y.points, MvPolynomial.aeval q.rep g ≠ 0 →
      ∃! p : ProjectivePoint n, (p, q) ∈ T)
    {b : Poly m} (hb : (yRen b : Poly (n + m)) ∈ pairIdeal T) : b ∈ Y.ideal := by
  have hbg : b * g ∈ Y.ideal := by
    rw [← ProjectiveVariety.vanishingIdeal_points Y]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro v ⟨hv, hvY⟩
    rw [map_mul]
    by_cases hgv : MvPolynomial.aeval v g = 0
    · rw [hgv, mul_zero]
    · obtain ⟨x, hx, hT⟩ := exists_lift T Y hhom hgen v hv hvY hgv
      have h0 := (MvPolynomial.mem_vanishingIdeal_iff.mp hb) _ (join_mem T x v hx hv hT)
      rw [eval_join_yRen] at h0
      rw [h0, zero_mul]
  exact ((Ideal.IsPrime.mem_or_mem hY) hbg).resolve_right hg

/-- A polynomial outside the ideal of `Y` is nonzero at a nonzero point of `Y`. -/
theorem exists_point_ne {f : Poly m} (hf : f ∉ Y.ideal) :
    ∃ v : Point m, ∃ hv : v ≠ 0, Projectivization.mk ℂ v hv ∈ Y.points ∧
      MvPolynomial.aeval v f ≠ 0 := by
  rw [← ProjectiveVariety.vanishingIdeal_points Y] at hf
  by_contra hcon
  push_neg at hcon
  apply hf
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro v ⟨hv, hvY⟩
  exact hcon v hv hvY

end Points

/-! ### Segre coordinates on the pair space -/

/-- Pullback of the Segre coordinates `z_{ij} = x_i y_j`. -/
def segrePull (n m : ℕ) : Poly (n * m) →ₐ[ℂ] Poly (n + m) :=
  MvPolynomial.aeval (fun z : Fin (n * m) =>
    (MvPolynomial.X (Fin.castAdd m (finProdFinEquiv.symm z).1) *
      MvPolynomial.X (Fin.natAdd n (finProdFinEquiv.symm z).2) : Poly (n + m)))

theorem eval_segrePull (x : Point n) (y : Point m) (F : Poly (n * m)) :
    MvPolynomial.aeval (joinPoints x y) (segrePull n m F) =
      MvPolynomial.aeval (segreVector x y) F := by
  have h := congrArg (fun φ : Poly (n * m) →ₐ[ℂ] ℂ => φ F)
    (MvPolynomial.comp_aeval (R := ℂ) (fun z : Fin (n * m) =>
      (MvPolynomial.X (Fin.castAdd m (finProdFinEquiv.symm z).1) *
        MvPolynomial.X (Fin.natAdd n (finProdFinEquiv.symm z).2) : Poly (n + m)))
      (MvPolynomial.aeval (joinPoints x y)))
  simp only [AlgHom.comp_apply] at h
  have hfun : (fun z : Fin (n * m) => MvPolynomial.aeval (joinPoints x y)
      (MvPolynomial.X (Fin.castAdd m (finProdFinEquiv.symm z).1) *
        MvPolynomial.X (Fin.natAdd n (finProdFinEquiv.symm z).2) : Poly (n + m))) =
      segreVector x y := by
    funext z
    simp [segreVector, joinPoints]
  rw [segrePull, h, hfun]

theorem segreVector_smul_left (c : ℂ) (x : Point n) (y : Point m) :
    segreVector (c • x) y = c • segreVector x y := by
  funext z
  simp [segreVector, mul_assoc]

theorem C_mem_biSpace (c : ℂ) : (MvPolynomial.C c : Poly (n + m)) ∈ BiSpace n m 0 0 := by
  have h := Submodule.smul_mem (BiSpace n m 0 0) c (one_mem_biSpace (n := n) (m := m))
  simpa [MvPolynomial.smul_eq_C_mul] using h

theorem prod_mem_biSpace {ι : Type*} (S : Finset ι) (f : ι → Poly (n + m)) (a b : ι → ℕ)
    (h : ∀ i ∈ S, f i ∈ BiSpace n m (a i) (b i)) :
    (∏ i ∈ S, f i) ∈ BiSpace n m (∑ i ∈ S, a i) (∑ i ∈ S, b i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (one_mem_biSpace (n := n) (m := m))
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    exact mul_mem_biSpace (h j (Finset.mem_insert_self j S))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem segrePull_X_mem (z : Fin (n * m)) :
    segrePull n m (MvPolynomial.X z) ∈ BiSpace n m 1 1 := by
  rw [segrePull, MvPolynomial.aeval_X]
  exact biSpace_congr (by rfl) (by rfl)
    (mul_mem_biSpace (X_castAdd_mem_biSpace (m := m) _) (X_natAdd_mem_biSpace (n := n) _))

/-- Homogeneous Segre polynomials pull back to balanced bihomogeneous polynomials. -/
theorem segrePull_mem_of_isHomogeneous {F : Poly (n * m)} {N : ℕ}
    (hF : F.IsHomogeneous N) : segrePull n m F ∈ BiSpace n m N N := by
  classical
  rw [F.as_sum, map_sum]
  apply Submodule.sum_mem
  intro e he
  have hdeg : (∑ z ∈ e.support, e z) = N := by
    have h := hF (MvPolynomial.mem_support_iff.mp he)
    rw [Finsupp.weight_apply] at h
    simpa [Finsupp.sum] using h
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.algHom_C, Finsupp.prod, map_prod]
  have hprod := prod_mem_biSpace e.support
    (fun z => segrePull n m (MvPolynomial.X z ^ e z)) (fun z => e z) (fun z => e z)
    (fun z _ => by
      rw [map_pow]
      have h := pow_mem_biSpace (segrePull_X_mem (n := n) (m := m) z) (e z)
      simpa using h)
  rw [hdeg] at hprod
  have h := mul_mem_biSpace (C_mem_biSpace (n := n) (m := m) (F.coeff e)) hprod
  simpa using h

/-- Balanced bihomogeneous polynomials are Segre pullbacks. -/
theorem monomial_mem_range_segrePull :
    ∀ (N : ℕ) (d : Fin (n + m) →₀ ℕ), d ∈ bideg n m N N →
      (MvPolynomial.monomial d (1 : ℂ) : Poly (n + m)) ∈ (segrePull n m).range := by
  classical
  intro N
  induction N with
  | zero =>
    intro d hd
    have hd0 : d = 0 := by
      ext v
      refine Fin.addCases (fun i => ?_) (fun k => ?_) v
      · have h := hd.1
        have h3 : d (Fin.castAdd m i) ≤ ∑ j, d (Fin.castAdd m j) :=
          Finset.single_le_sum (f := fun j => d (Fin.castAdd m j)) (fun j _ => Nat.zero_le _)
            (Finset.mem_univ i)
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        omega
      · have h := hd.2
        have h3 : d (Fin.natAdd n k) ≤ ∑ j, d (Fin.natAdd n j) :=
          Finset.single_le_sum (f := fun j => d (Fin.natAdd n j)) (fun j _ => Nat.zero_le _)
            (Finset.mem_univ k)
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        omega
    subst hd0
    rw [← MvPolynomial.C_apply, map_one]
    exact Subalgebra.one_mem _
  | succ N ih =>
    intro d hd
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun i : Fin n => d (Fin.castAdd m i)) (by rw [hd.1]; omega)
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun k : Fin m => d (Fin.natAdd n k)) (by rw [hd.2]; omega)
    set e : Fin (n + m) →₀ ℕ :=
      Finsupp.single (Fin.castAdd m i) 1 + Finsupp.single (Fin.natAdd n k) 1 with he
    have hle : e ≤ d := by
      intro v
      simp only [he, Finsupp.add_apply, Finsupp.single_apply]
      by_cases h1 : Fin.castAdd m i = v
      · subst h1
        rw [if_pos rfl, if_neg (castAdd_ne_natAdd i k).symm]
        omega
      · by_cases h2 : Fin.natAdd n k = v
        · subst h2
          rw [if_neg h1, if_pos rfl]
          omega
        · rw [if_neg h1, if_neg h2]
          omega
    set d' := d - e with hd'
    have hdd : d = d' + e := (tsub_add_cancel_of_le hle).symm
    have hesum1 : (∑ j : Fin n, e (Fin.castAdd m j)) = 1 := by
      simp [he, Finsupp.single_apply, Fin.castAdd_inj, castAdd_ne_natAdd]
    have hesum2 : (∑ j : Fin m, e (Fin.natAdd n j)) = 1 := by
      simp [he, Finsupp.single_apply, Fin.natAdd_inj,
        fun j => (castAdd_ne_natAdd (m := m) i j).symm]
    have hd'mem : d' ∈ bideg n m N N := by
      have h1 := hd.1
      have h2 := hd.2
      rw [hdd] at h1 h2
      simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h1 h2
      exact ⟨by omega, by omega⟩
    have hmon : (MvPolynomial.monomial d (1 : ℂ) : Poly (n + m)) =
        MvPolynomial.monomial d' 1 * segrePull n m (MvPolynomial.X (finProdFinEquiv (i, k))) := by
      rw [segrePull, MvPolynomial.aeval_X, Equiv.symm_apply_apply, MvPolynomial.X,
        MvPolynomial.X, MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, hdd, he]
      simp only [mul_one, add_assoc]
    rw [hmon]
    exact Subalgebra.mul_mem _ (ih d' hd'mem) ⟨_, rfl⟩

theorem mem_range_segrePull {N : ℕ} {f : Poly (n + m)} (hf : f ∈ BiSpace n m N N) :
    f ∈ (segrePull n m).range := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff] at hf
  rw [f.as_sum]
  apply Subalgebra.sum_mem
  intro d hd
  rw [← mul_one (f.coeff d), ← MvPolynomial.C_mul_monomial]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (monomial_mem_range_segrePull N d (hf (Finset.mem_coe.mpr hd)))

section Segre

variable (T : Set (ProjectivePoint n × ProjectivePoint m))

/-- The Segre image set whose closure is `pairClosure T`. -/
abbrev segreSet : Set (ProjectivePoint (n * m)) :=
  {w | ∃ p q, (p, q) ∈ T ∧ segrePoint p q = w}

theorem segreVector_mem_reps (x : Point n) (y : Point m) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈ T) :
    segreVector x y ∈ ProjectiveVariety.nonzeroRepresentatives (segreSet T) :=
  ⟨segreVector_ne_zero x y hx hy, _, _, h, segrePoint_mk x y hx hy⟩

theorem reps_cases {v : Point (n * m)}
    (hv : v ∈ ProjectiveVariety.nonzeroRepresentatives (segreSet T)) :
    ∃ x : Point n, ∃ y : Point m, ∃ hx : x ≠ 0, ∃ hy : y ≠ 0,
      (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈ T ∧ v = segreVector x y := by
  obtain ⟨hv0, p, q, hpq, hseg⟩ := hv
  have hseg' : segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero)
      (Projectivization.mk ℂ q.rep q.rep_nonzero) = Projectivization.mk ℂ v hv0 := by
    rw [Projectivization.mk_rep, Projectivization.mk_rep]
    exact hseg
  rw [segrePoint_mk] at hseg'
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hseg'.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv0
    rw [← hc, zero_smul]
  refine ⟨c • p.rep, q.rep, smul_ne_zero hc0 p.rep_nonzero, q.rep_nonzero, ?_, ?_⟩
  · have hmk : Projectivization.mk ℂ (c • p.rep) (smul_ne_zero hc0 p.rep_nonzero) = p :=
      ((Projectivization.mk_eq_mk_iff' ℂ _ _ _ p.rep_nonzero).mpr ⟨c, rfl⟩).trans
        (Projectivization.mk_rep p)
    rw [hmk, Projectivization.mk_rep]
    exact hpq
  · rw [segreVector_smul_left, hc]

theorem segrePull_mem_pairIdeal_iff (F : Poly (n * m)) :
    segrePull n m F ∈ pairIdeal T ↔ F ∈ (pairClosure T).ideal := by
  constructor
  · intro hF
    change F ∈ MvPolynomial.vanishingIdeal ℂ
      (ProjectiveVariety.nonzeroRepresentatives (segreSet T))
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro v hv
    obtain ⟨x, y, hx, hy, hT, rfl⟩ := reps_cases T hv
    rw [← eval_segrePull]
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hF) _ (join_mem T x y hx hy hT)
  · intro hF
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro w ⟨x, y, hx, hy, hT, rfl⟩
    rw [eval_segrePull]
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hF) _ (segreVector_mem_reps T x y hx hy hT)

/-- Bihomogeneous primality test from the irreducible Segre closure. -/
theorem bihom_mem_or_mem (hT : (pairClosure T).IsIrreducible) {a b a' b' : ℕ}
    {f g : Poly (n + m)} (hf : f ∈ BiSpace n m a b) (hg : g ∈ BiSpace n m a' b')
    (hfg : f * g ∈ pairIdeal T) : f ∈ pairIdeal T ∨ g ∈ pairIdeal T := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hf0, hg0⟩ := hcon
  -- balance a bihomogeneous polynomial outside the ideal
  have hbal : ∀ {a b : ℕ} {f : Poly (n + m)}, f ∈ BiSpace n m a b → f ∉ pairIdeal T →
      ∃ f' : Poly (n + m), ∃ F : Poly (n * m), segrePull n m F = f' ∧ f' ∉ pairIdeal T ∧
        ∃ u : Poly (n + m), f' = f * u := by
    intro a b f hf hf0
    have hex : ∃ w ∈ pairRepresentatives T, MvPolynomial.aeval w f ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf0 (MvPolynomial.mem_vanishingIdeal_iff.mpr h)
    obtain ⟨w, ⟨x, y, hx, hy, hT, rfl⟩, hw⟩ := hex
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hy
    let u : Poly (n + m) := MvPolynomial.X (Fin.castAdd m i) ^ b *
      MvPolynomial.X (Fin.natAdd n k) ^ a
    have hu : f * u ∈ BiSpace n m (a + b) (a + b) := by
      have h := mul_mem_biSpace hf (mul_mem_biSpace
        (pow_mem_biSpace (X_castAdd_mem_biSpace (m := m) i) b)
        (pow_mem_biSpace (X_natAdd_mem_biSpace (n := n) k) a))
      exact biSpace_congr (by ring) (by ring) h
    obtain ⟨F, hF⟩ := mem_range_segrePull hu
    refine ⟨f * u, F, hF, ?_, u, rfl⟩
    intro hmem
    have h0 := (MvPolynomial.mem_vanishingIdeal_iff.mp hmem) _ (join_mem T x y hx hy hT)
    simp only [u, map_mul, map_pow, MvPolynomial.aeval_X] at h0
    simp only [joinPoints, Fin.addCases_left, Fin.addCases_right] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hw h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hi (pow_eq_zero_iff'.mp h2).1
      · exact hk (pow_eq_zero_iff'.mp h2).1
  obtain ⟨f', F, hF, hf', u, rfl⟩ := hbal hf hf0
  obtain ⟨g', G, hG, hg', u', rfl⟩ := hbal hg hg0
  have hFG : F * G ∈ (pairClosure T).ideal := by
    rw [← segrePull_mem_pairIdeal_iff, map_mul, hF, hG]
    have h := Ideal.mul_mem_right (u * u') _ hfg
    convert h using 1
    ring
  rcases (Ideal.IsPrime.mem_or_mem hT) hFG with h | h
  · exact hf' (hF ▸ (segrePull_mem_pairIdeal_iff T F).mpr h)
  · exact hg' (hG ▸ (segrePull_mem_pairIdeal_iff T G).mpr h)

/-- Points of the closed pair set: bihomogeneous balanced vanishing suffices. -/
theorem mem_of_balanced_vanish (hclosed : closedPairs T = T) (x : Point n) (y : Point m)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hvan : ∀ N : ℕ, ∀ f ∈ BiSpace n m N N, f ∈ pairIdeal T →
      MvPolynomial.aeval (joinPoints x y) f = 0) :
    (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈ T := by
  rw [← hclosed]
  show segrePoint (Projectivization.mk ℂ x hx) (Projectivization.mk ℂ y hy) ∈ pairClosure T
  rw [segrePoint_mk]
  change _ ∈ (pairClosure T).points
  rw [ProjectiveVariety.mem_points_mk_iff]
  intro F hF
  rw [← MvPolynomial.sum_homogeneousComponent F]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro N _
  have hN : MvPolynomial.homogeneousComponent N F ∈ (pairClosure T).ideal :=
    MvPolynomial.homogeneousComponent_mem_of_mem (pairClosure T).isHomogeneous hF N
  rw [← eval_segrePull]
  exact hvan N _ (segrePull_mem_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous N F))
    ((segrePull_mem_pairIdeal_iff T _).mpr hN)

end Segre

/-! ### Primality of the pair ideal -/

section Prime

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- Bidegrees, ordered lexicographically. -/
def lexOf : (Fin 2 →₀ ℕ) →+ Lex (ℕ × ℕ) where
  toFun D := toLex (D 0, D 1)
  map_zero' := rfl
  map_add' D E := rfl

theorem lexOf_injective : Function.Injective lexOf := by
  intro D E h
  have h' : (D 0, D 1) = (E 0, E 1) := toLex.injective h
  ext j
  fin_cases j
  · exact congrArg Prod.fst h'
  · exact congrArg Prod.snd h'

theorem lexOf_pairDegree (s t : ℕ) : lexOf (HilbertMulti.pairDegree s t) = toLex (s, t) := by
  change toLex (HilbertMulti.pairDegree s t 0, HilbertMulti.pairDegree s t 1) = toLex (s, t)
  simp [HilbertMulti.pairDegree]

/-- Lexicographic bidegree weight on the pair variables. -/
def lexWeight (n m : ℕ) : Fin (n + m) → Lex (ℕ × ℕ) :=
  fun i => lexOf (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m) i)

theorem weight_lexWeight (d : Fin (n + m) →₀ ℕ) :
    Finsupp.weight (lexWeight n m) d =
      lexOf (Finsupp.weight (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) d) := by
  simp only [Finsupp.weight_apply, lexWeight, map_finsuppSum, map_nsmul]

theorem weight_block_eq_iff (d : Fin (n + m) →₀ ℕ) (s t : ℕ) :
    Finsupp.weight (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) d =
        HilbertMulti.pairDegree s t ↔ d ∈ bideg n m s t := by
  classical
  have hEq : MvPolynomial.weightedHomogeneousSubmodule ℂ
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) (HilbertMulti.pairDegree s t) =
      BiSpace n m s t := HilbertMulti.pairBlockPiece n m s t
  have h2 : (MvPolynomial.monomial d (1 : ℂ) ∈ BiSpace n m s t) ↔ d ∈ bideg n m s t := by
    rw [MvPolynomial.mem_restrictSupport_iff, MvPolynomial.support_monomial,
      if_neg one_ne_zero, Finset.coe_singleton, Set.singleton_subset_iff]
  rw [← h2, ← hEq, MvPolynomial.mem_weightedHomogeneousSubmodule]
  constructor
  · intro hw
    exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ hw
  · intro hw
    exact hw (by rw [MvPolynomial.coeff_monomial, if_pos rfl]; exact one_ne_zero)

theorem lexComponent_eq (μ : Lex (ℕ × ℕ)) (f : Poly (n + m)) :
    MvPolynomial.weightedHomogeneousComponent (lexWeight n m) μ f =
      MvPolynomial.weightedHomogeneousComponent
        (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))
        (HilbertMulti.pairDegree (ofLex μ).1 (ofLex μ).2) f := by
  classical
  rw [MvPolynomial.weightedHomogeneousComponent_apply,
    MvPolynomial.weightedHomogeneousComponent_apply]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro d _
  rw [weight_lexWeight]
  constructor
  · intro h
    apply lexOf_injective
    rw [h, lexOf_pairDegree]
    rfl
  · intro h
    rw [h, lexOf_pairDegree]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem pairIdeal_lexHomogeneous (T : Set (ProjectivePoint n × ProjectivePoint m)) :
    (pairIdeal T).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (lexWeight n m)) := by
  classical
  intro μ f hf
  change ((MvPolynomial.weightedDecomposition ℂ (lexWeight n m)).decompose' f μ :
    Poly (n + m)) ∈ pairIdeal T
  rw [MvPolynomial.weightedDecomposition.decompose'_apply, lexComponent_eq]
  have h := pairRepresentatives_blockHomogeneous T
    (HilbertMulti.pairDegree (ofLex μ).1 (ofLex μ).2) hf
  change ((MvPolynomial.weightedDecomposition ℂ
    (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))).decompose' f _ :
      Poly (n + m)) ∈ _ at h
  rwa [MvPolynomial.weightedDecomposition.decompose'_apply] at h

theorem lexHom_mem_biSpace {μ : Lex (ℕ × ℕ)} {f : Poly (n + m)}
    (hf : f ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ (lexWeight n m) μ) :
    f ∈ BiSpace n m (ofLex μ).1 (ofLex μ).2 := by
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hf
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro d hd
  have hw := hf (MvPolynomial.mem_support_iff.mp hd)
  rw [weight_lexWeight] at hw
  rw [← weight_block_eq_iff]
  apply lexOf_injective
  rw [hw, lexOf_pairDegree]
  rfl

/-- The pair ideal of a set with irreducible Segre closure is prime. -/
theorem pairIdeal_isPrime (T : Set (ProjectivePoint n × ProjectivePoint m))
    (hT : (pairClosure T).IsIrreducible) (hne : (pairRepresentatives T).Nonempty) :
    (pairIdeal T).IsPrime := by
  classical
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (pairIdeal_lexHomogeneous T) ?_ ?_
  · intro htop
    obtain ⟨w, hw⟩ := hne
    have h1 : (1 : Poly (n + m)) ∈ pairIdeal T := by
      rw [htop]
      exact Submodule.mem_top
    have h0 := (MvPolynomial.mem_vanishingIdeal_iff.mp h1) w hw
    simp at h0
  · rintro f g ⟨μ, hf⟩ ⟨ν, hg⟩ hfg
    exact bihom_mem_or_mem T hT (lexHom_mem_biSpace hf) (lexHom_mem_biSpace hg) hfg

end Prime

/-! ### Lying over -/

section LyingOver

/-- Polynomial evaluation as a `ℂ`-algebra map. -/
def evalAlg {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (x : B) : Polynomial A →ₐ[ℂ] B :=
  { Polynomial.eval₂RingHom (f : A →+* B) x with
    commutes' := fun c => by
      simp [Polynomial.algebraMap_apply] }

theorem evalAlg_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (x : B) (G : Polynomial A) :
    evalAlg f x G = Polynomial.eval₂ (f : A →+* B) x G := rfl

/-- Characters extend along integral extensions (port of OAI `extend_algHom_of_integral`,
whose module `OAI.Analysis.SymmetricDomains.FiniteAlgebraGenericSheets` is not prebuilt). -/
theorem extend_algHom_of_integral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [FaithfulSMul A B] [Algebra.IsIntegral A B] [Algebra.FiniteType ℂ B]
    (e : A →ₐ[ℂ] ℂ) :
    ∃ f : B →ₐ[ℂ] ℂ, ∀ a : A, f (algebraMap A B a) = e a := by
  let m := RingHom.ker e
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective e
    (fun x => ⟨algebraMap ℂ A x, e.commutes x⟩)
  let := hm
  have hker : RingHom.ker (algebraMap A B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := B) m (by rw [hker]; exact bot_le)
  let := hQmax
  let : Field (B ⧸ Q) := Ideal.Quotient.field Q
  let : Module.Finite ℂ (B ⧸ Q) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ Q)
  let f : B →ₐ[ℂ] ℂ := IsAlgClosed.lift.comp (Ideal.Quotient.mkₐ ℂ Q)
  refine ⟨f, fun a => ?_⟩
  have ham : a - algebraMap ℂ A (e a) ∈ m := by
    change e (a - algebraMap ℂ A (e a)) = 0
    rw [map_sub, e.commutes]
    simp
  have haQ : algebraMap A B (a - algebraMap ℂ A (e a)) ∈ Q := by
    change a - algebraMap ℂ A (e a) ∈ Q.under A
    rw [hQ]
    exact ham
  have hz : f (algebraMap A B (a - algebraMap ℂ A (e a))) = 0 := by
    change IsAlgClosed.lift (Ideal.Quotient.mk Q _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr haQ, map_zero]
  rw [map_sub, map_sub, ← IsScalarTower.algebraMap_apply ℂ A B, f.commutes] at hz
  exact sub_eq_zero.mp hz

/-- A monic lift of a minimal polynomial kills the element. -/
theorem eval₂_eq_zero_of_map_minpoly {L : Type*} [Field L] [Algebra ℂ L]
    (yA : Poly m →ₐ[ℂ] L) (K : IntermediateField ℂ L) (yK : Poly m →ₐ[ℂ] K)
    (hyK : ∀ b : Poly m, (yK b : L) = yA b) (F : Polynomial (Poly m)) (x : L)
    (hFmin : F.map (yK : Poly m →+* K) = minpoly K x) :
    Polynomial.eval₂ (yA : Poly m →+* L) x F = 0 := by
  have h1 : (yA : Poly m →+* L) = (algebraMap K L).comp (yK : Poly m →+* K) :=
    RingHom.ext fun b => by simp [hyK]
  rw [h1, ← Polynomial.eval₂_map, hFmin, ← Polynomial.aeval_def]
  exact minpoly.aeval K x

/-- Lying over: a root of the specialized minimal polynomial is the value of a point of
the integral extension generated by `V` over the base point `q`. -/
theorem realize_root {L : Type*} [Field L] [Algebra ℂ L] {N : ℕ}
    (yA : Poly m →ₐ[ℂ] L) (K : IntermediateField ℂ L) (yK : Poly m →ₐ[ℂ] K)
    (hyK : ∀ b : Poly m, (yK b : L) = yA b)
    (V : Fin N → L) (iθ : Fin N)
    (hyV : ∀ b : Poly m, yA b ∈ (MvPolynomial.aeval (R := ℂ) V).range)
    (hint : ∀ v, ∃ G : Polynomial (Poly m), G.Monic ∧
      Polynomial.eval₂ (yA : Poly m →+* L) (V v) G = 0)
    (F : Polynomial (Poly m)) (hF : F.Monic)
    (hFmin : F.map (yK : Poly m →+* K) = minpoly K (V iθ))
    (q : Point m) (hq : ∀ b, yA b = 0 → MvPolynomial.aeval q b = 0)
    (w : ℂ) (hw : Polynomial.eval₂ ((MvPolynomial.aeval q : Poly m →ₐ[ℂ] ℂ) : Poly m →+* ℂ) w F = 0) :
    ∃ z : Fin N → ℂ,
      (∀ f : MvPolynomial (Fin N) ℂ, MvPolynomial.aeval V f = 0 →
        MvPolynomial.aeval z f = 0) ∧
      (∀ v (b : Poly m), V v = yA b → z v = MvPolynomial.aeval q b) ∧ z iθ = w := by
  classical
  set θ := V iθ with hθ
  let S : Subalgebra ℂ L := (MvPolynomial.aeval (R := ℂ) V).range
  let Ψ : Polynomial (Poly m) →ₐ[ℂ] L := evalAlg yA θ
  let A : Subalgebra ℂ L := Ψ.range
  have h1 : (yA : Poly m →+* L) = (algebraMap K L).comp (yK : Poly m →+* K) :=
    RingHom.ext fun b => by simp [hyK]
  have hΨF : Ψ F = 0 := eval₂_eq_zero_of_map_minpoly yA K yK hyK F θ hFmin
  have hker : ∀ G : Polynomial (Poly m), Ψ G = 0 →
      Polynomial.eval₂ ((MvPolynomial.aeval q : Poly m →ₐ[ℂ] ℂ) : Poly m →+* ℂ) w G = 0 := by
    intro G hG
    have hdecomp := Polynomial.modByMonic_add_div G F
    set R := G %ₘ F with hR
    have hΨR : Ψ R = 0 := by
      have h2 := congrArg Ψ hdecomp
      rw [map_add, map_mul, hΨF, zero_mul, add_zero, hG] at h2
      exact h2
    have hRmap : R.map (yK : Poly m →+* K) = 0 := by
      by_contra hne
      have haev : Polynomial.aeval θ (R.map (yK : Poly m →+* K)) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← h1]
        exact hΨR
      have hle := minpoly.degree_le_of_ne_zero K θ hne haev
      have hlt : (R.map (yK : Poly m →+* K)).degree < (minpoly K θ).degree := by
        calc (R.map (yK : Poly m →+* K)).degree ≤ R.degree := Polynomial.degree_map_le
          _ < F.degree := Polynomial.degree_modByMonic_lt G hF
          _ = (minpoly K θ).degree := by rw [← hFmin, hF.degree_map]
      exact absurd hle (not_le.mpr hlt)
    have hRq : R.map ((MvPolynomial.aeval q : Poly m →ₐ[ℂ] ℂ) : Poly m →+* ℂ) = 0 := by
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      apply hq
      rw [← hyK]
      have h3 := congrArg (fun P => P.coeff k) hRmap
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h3
      rw [show (yK (R.coeff k) : L) = ((0 : K) : L) from congrArg Subtype.val h3]
      rfl
    rw [← hdecomp, Polynomial.eval₂_add, Polynomial.eval₂_mul, hw, zero_mul, add_zero,
      Polynomial.eval₂_eq_eval_map, hRq, Polynomial.eval_zero]
  let ev : Polynomial (Poly m) →ₐ[ℂ] ℂ := evalAlg (MvPolynomial.aeval q) w
  have hkerA : ∀ G ∈ RingHom.ker Ψ.rangeRestrict, ev G = 0 := by
    intro G hG
    apply hker
    have h2 := congrArg Subtype.val (RingHom.mem_ker.mp hG)
    exact h2
  let eqv := Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective Ψ)
  let eA : A →ₐ[ℂ] ℂ :=
    (Ideal.Quotient.liftₐ (RingHom.ker Ψ.rangeRestrict) ev hkerA).comp eqv.symm.toAlgHom
  have heA : ∀ G, eA (Ψ.rangeRestrict G) = ev G := by
    intro G
    have h2 : eqv (Ideal.Quotient.mk _ G) = Ψ.rangeRestrict G := rfl
    change Ideal.Quotient.liftₐ (RingHom.ker Ψ.rangeRestrict) ev hkerA
      (eqv.symm (Ψ.rangeRestrict G)) = ev G
    rw [← h2, AlgEquiv.symm_apply_apply]
    rfl
  have hθS : θ ∈ S := ⟨MvPolynomial.X iθ, MvPolynomial.aeval_X V iθ⟩
  have hAS : A ≤ S := by
    rintro _ ⟨G, rfl⟩
    change Polynomial.eval₂ (yA : Poly m →+* L) θ G ∈ S
    rw [Polynomial.eval₂_eq_sum_range]
    exact Subalgebra.sum_mem _ fun k _ =>
      Subalgebra.mul_mem _ (hyV _) (Subalgebra.pow_mem _ hθS _)
  letI : Algebra A S := (Subalgebra.inclusion hAS).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A S := IsScalarTower.of_algebraMap_eq (fun c => rfl)
  haveI : FaithfulSMul A S :=
    (faithfulSMul_iff_algebraMap_injective A S).mpr (Subalgebra.inclusion_injective hAS)
  haveI : Algebra.FiniteType ℂ S :=
    Algebra.FiniteType.of_surjective (MvPolynomial.aeval (R := ℂ) V).rangeRestrict
      (AlgHom.rangeRestrict_surjective _)
  let Vs : Fin N → S := fun v => ⟨V v, ⟨MvPolynomial.X v, MvPolynomial.aeval_X V v⟩⟩
  have hvalaeval : ∀ f : MvPolynomial (Fin N) ℂ,
      ((MvPolynomial.aeval Vs f : S) : L) = MvPolynomial.aeval V f := by
    intro f
    exact MvPolynomial.comp_aeval_apply (f := Vs) S.val f
  have hgenInt : ∀ v, IsIntegral A (Vs v) := by
    intro v
    obtain ⟨G, hGm, hG0⟩ := hint v
    let ι : Poly m →+* A := (Ψ.rangeRestrict : Polynomial (Poly m) →+* A).comp Polynomial.C
    refine ⟨G.map ι, hGm.map ι, ?_⟩
    apply Subtype.val_injective
    rw [Polynomial.eval₂_map]
    have h2 := Polynomial.hom_eval₂ G ((algebraMap A S).comp ι) (S.val : S →+* L) (Vs v)
    change (S.val : S →+* L) _ = 0
    rw [h2]
    have h3 : (S.val : S →+* L).comp ((algebraMap A S).comp ι) = (yA : Poly m →+* L) := by
      apply RingHom.ext
      intro b
      change Polynomial.eval₂ (yA : Poly m →+* L) θ (Polynomial.C b) = yA b
      rw [Polynomial.eval₂_C]
      rfl
    rw [h3]
    exact hG0
  haveI : Algebra.IsIntegral A S := by
    have hall : ∀ f : MvPolynomial (Fin N) ℂ, IsIntegral A (MvPolynomial.aeval Vs f) := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C c =>
        rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply ℂ A S]
        exact isIntegral_algebraMap
      | add p r hp hr =>
        rw [map_add]
        exact hp.add hr
      | mul_X p v hp =>
        rw [map_mul, MvPolynomial.aeval_X]
        exact hp.mul (hgenInt v)
    constructor
    intro s
    obtain ⟨f, hf⟩ := s.2
    have hs : s = MvPolynomial.aeval Vs f := by
      apply Subtype.ext
      rw [hvalaeval]
      exact hf.symm
    rw [hs]
    exact hall f
  obtain ⟨φ, hφ⟩ := extend_algHom_of_integral (A := A) (B := S) eA
  refine ⟨fun v => φ (Vs v), ?_, ?_, ?_⟩
  · intro f hf
    have h2 : MvPolynomial.aeval (fun v => φ (Vs v)) f = φ (MvPolynomial.aeval Vs f) :=
      (MvPolynomial.comp_aeval_apply (f := Vs) φ f).symm
    rw [h2]
    have h3 : MvPolynomial.aeval Vs f = 0 := Subtype.ext (by rw [hvalaeval]; exact hf)
    rw [h3, map_zero]
  · intro v b hvb
    have hmem : Vs v = algebraMap A S (Ψ.rangeRestrict (Polynomial.C b)) := by
      apply Subtype.ext
      change V v = Polynomial.eval₂ (yA : Poly m →+* L) θ (Polynomial.C b)
      rw [Polynomial.eval₂_C, hvb]
      rfl
    change φ (Vs v) = _
    rw [hmem, hφ, heA]
    change Polynomial.eval₂ _ w (Polynomial.C b) = _
    rw [Polynomial.eval₂_C]
    rfl
  · have hmem : Vs iθ = algebraMap A S (Ψ.rangeRestrict Polynomial.X) := by
      apply Subtype.ext
      change V iθ = Polynomial.eval₂ (yA : Poly m →+* L) θ Polynomial.X
      rw [Polynomial.eval₂_X]
    change φ (Vs iθ) = _
    rw [hmem, hφ, heA]
    change Polynomial.eval₂ _ w Polynomial.X = _
    rw [Polynomial.eval₂_X]

/-- Specialization of a monic polynomial with nonzero discriminant is separable
(port of OAI `separable_map_of_resultant_ne_zero`). -/
theorem separable_map_of_resultant_ne_zero {R K : Type*} [CommRing R] [Field K]
    (p : Polynomial R) (hp : p.Monic) (e : R →+* K)
    (hd : e (p.resultant (Polynomial.derivative p)) ≠ 0) :
    (p.map e).Separable := by
  by_cases hdeg : p.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hp hdeg, Polynomial.map_one]
    exact Polynomial.separable_one
  obtain ⟨a, b, _, _, hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    p (Polynomial.derivative p) le_rfl le_rfl (Or.inl hdeg)
  have hh := congrArg (Polynomial.map e) hab
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C] at hh
  rw [Polynomial.Separable, Polynomial.derivative_map]
  refine ⟨Polynomial.C (e (p.resultant (Polynomial.derivative p)))⁻¹ * a.map e,
    Polynomial.C (e (p.resultant (Polynomial.derivative p)))⁻¹ * b.map e, ?_⟩
  calc Polynomial.C (e (p.resultant (Polynomial.derivative p)))⁻¹ * a.map e * p.map e +
        Polynomial.C (e (p.resultant (Polynomial.derivative p)))⁻¹ * b.map e *
          (Polynomial.derivative p).map e
      = Polynomial.C (e (p.resultant (Polynomial.derivative p)))⁻¹ *
          (p.map e * a.map e + (Polynomial.derivative p).map e * b.map e) := by ring
    _ = 1 := by
      rw [hh, ← Polynomial.C_mul, inv_mul_cancel₀ hd, Polynomial.C_1]

end LyingOver

/-! ### Minimal polynomials of rescaled elements -/

theorem minpoly_mul_eq_scaleRoots {K L : Type*} [Field K] [Field L] [Algebra K L] (u : L)
    (hu : IsIntegral K u) (δ : K) (hδ : δ ≠ 0) :
    minpoly K (algebraMap K L δ * u) = (minpoly K u).scaleRoots δ := by
  set p := minpoly K u with hp
  have hpm : p.Monic := minpoly.monic hu
  have hqm : (p.scaleRoots δ).Monic := (Polynomial.monic_scaleRoots_iff δ).mpr hpm
  have hq0 : Polynomial.aeval (algebraMap K L δ * u) (p.scaleRoots δ) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero (minpoly.aeval K u)
  have hint' : IsIntegral K (algebraMap K L δ * u) := isIntegral_algebraMap.mul hu
  have hdvd := minpoly.dvd K _ hq0
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint') hqm hdvd ?_).symm
  rw [Polynomial.natDegree_scaleRoots]
  set μ := minpoly K (algebraMap K L δ * u) with hμ
  have hμm : μ.Monic := minpoly.monic hint'
  have h2 : Polynomial.aeval u (μ.scaleRoots δ⁻¹) = 0 := by
    have h3 := Polynomial.scaleRoots_aeval_eq_zero (r := δ⁻¹)
      (minpoly.aeval K (algebraMap K L δ * u))
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hδ, map_one, one_mul] at h3
  have hsm : (μ.scaleRoots δ⁻¹).Monic := (Polynomial.monic_scaleRoots_iff _).mpr hμm
  have h4 := minpoly.min K u hsm h2
  rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hu),
    Polynomial.degree_eq_natDegree hsm.ne_zero, Polynomial.natDegree_scaleRoots] at h4
  exact_mod_cast h4

/-! ### The function field of the pair set -/

section Birational

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable (T : Set (ProjectivePoint n × ProjectivePoint m)) [hJ : (pairIdeal T).IsPrime]

/-- The function field of the (irreducible) pair cone. -/
abbrev LF := FractionRing (Poly (n + m) ⧸ pairIdeal T)

/-- Polynomials as functions on the pair set. -/
def toL : Poly (n + m) →ₐ[ℂ] LF T :=
  (IsScalarTower.toAlgHom ℂ (Poly (n + m) ⧸ pairIdeal T) (LF T)).comp
    (Ideal.Quotient.mkₐ ℂ (pairIdeal T))

theorem toL_eq_zero_iff (f : Poly (n + m)) : toL T f = 0 ↔ f ∈ pairIdeal T := by
  change algebraMap (Poly (n + m) ⧸ pairIdeal T) (LF T) (Ideal.Quotient.mk _ f) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

/-- First-factor coordinates. -/
def xL (i : Fin n) : LF T := toL T (MvPolynomial.X (Fin.castAdd m i))

/-- Second-factor polynomials as functions on the pair set. -/
def yAlg : Poly m →ₐ[ℂ] LF T := (toL T).comp (yRen (n := n))

theorem yAlg_eq_aeval (b : Poly m) :
    yAlg T b = MvPolynomial.aeval (fun k => yAlg T (MvPolynomial.X k)) b :=
  AlgHom.congr_fun (MvPolynomial.aeval_unique (yAlg T)) b

theorem toL_eq_aeval (f : Poly (n + m)) :
    toL T f = MvPolynomial.aeval
      (Fin.addCases (xL T) (fun k => yAlg T (MvPolynomial.X k)) : Fin (n + m) → LF T) f := by
  have hfun : (⇑(toL T) ∘ MvPolynomial.X : Fin (n + m) → LF T) =
      Fin.addCases (xL T) (fun k => yAlg T (MvPolynomial.X k)) := by
    funext v
    refine Fin.addCases (fun i => ?_) (fun k => ?_) v
    · simp [xL]
    · simp [yAlg]
  rw [← hfun]
  exact AlgHom.congr_fun (MvPolynomial.aeval_unique (toL T)) f

/-- The function field of the second factor inside that of the pair set. -/
abbrev KF : IntermediateField ℂ (LF T) :=
  IntermediateField.adjoin ℂ (Set.range fun k : Fin m => yAlg T (MvPolynomial.X k))

def yK : Poly m →ₐ[ℂ] KF T :=
  MvPolynomial.aeval fun k => (⟨yAlg T (MvPolynomial.X k),
    IntermediateField.subset_adjoin ℂ _ ⟨k, rfl⟩⟩ : KF T)

theorem yK_val (b : Poly m) : (yK T b : LF T) = yAlg T b := by
  have h : (KF T).val.comp (yK T) = yAlg T := MvPolynomial.algHom_ext fun k => by simp [yK]
  exact AlgHom.congr_fun h b

theorem coeff_monicSum {R : Type*} [CommRing R] (r : ℕ) (f : Fin r → R) (i : ℕ) :
    (Polynomial.X ^ r + ∑ k : Fin r, Polynomial.C (f k) * Polynomial.X ^ (k : ℕ)).coeff i =
      if h : i < r then f ⟨i, h⟩ else if i = r then 1 else 0 := by
  classical
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases h : i < r
  · rw [dif_pos h, if_neg (by omega), zero_add, Finset.sum_eq_single (⟨i, h⟩ : Fin r)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg]
      intro h'
      exact hk (Fin.ext h'.symm)
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [dif_neg h]
    have hz : (∑ k : Fin r, if i = (k : ℕ) then f k else 0) = 0 :=
      Finset.sum_eq_zero fun k _ => if_neg (by have := k.2; omega)
    rw [hz, add_zero]

/-- Clearing denominators of a minimal polynomial over the second factor. -/
theorem exists_clearing (u : LF T) (hu : IsAlgebraic (KF T) u) :
    ∃ c : Poly m, yAlg T c ≠ 0 ∧ ∀ e : Poly m, yAlg T e ≠ 0 →
      ∃ F : Polynomial (Poly m), F.Monic ∧
        F.map (yK T : Poly m →+* KF T) = minpoly (KF T) (yAlg T (c * e) * u) := by
  classical
  have hint := hu.isIntegral
  obtain ⟨p, hp⟩ : ∃ p, p = minpoly (KF T) u := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = p.natDegree := ⟨_, rfl⟩
  have hpm : p.Monic := hp ▸ minpoly.monic hint
  have hcoef : ∀ k : Fin r, ∃ nu de : Poly m, yAlg T de ≠ 0 ∧
      ((p.coeff k : KF T) : LF T) * yAlg T de = yAlg T nu := by
    intro k
    have hmem : ((p.coeff k : KF T) : LF T) ∈ KF T := (p.coeff k).2
    rw [IntermediateField.mem_adjoin_range_iff] at hmem
    obtain ⟨r1, s1, hrs⟩ := hmem
    rw [← yAlg_eq_aeval, ← yAlg_eq_aeval] at hrs
    by_cases hs : yAlg T s1 = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [hrs, hs, div_zero, zero_mul, map_zero]
    · exact ⟨r1, s1, hs, by rw [hrs, div_mul_cancel₀ _ hs]⟩
  choose nu de hde hnd using hcoef
  have hc : yAlg T (∏ k, de k) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hde k
  refine ⟨∏ k, de k, hc, ?_⟩
  intro e he
  set c := ∏ k, de k with hcdef
  set δ : KF T := yK T (c * e) with hδdef
  have hδL : (δ : LF T) = yAlg T c * yAlg T e := by rw [hδdef, yK_val, map_mul]
  have hδ : δ ≠ 0 := by
    intro h
    apply mul_ne_zero hc he
    rw [← hδL, h]
    rfl
  have hθ : yAlg T (c * e) * u = algebraMap (KF T) (LF T) δ * u := by
    rw [hδdef, IntermediateField.algebraMap_apply, yK_val]
  rw [hθ, minpoly_mul_eq_scaleRoots u hint δ hδ, ← hp]
  let lift : Fin r → Poly m := fun k =>
    nu k * (∏ l ∈ Finset.univ.erase k, de l) * c ^ (r - k - 1) * e ^ (r - k)
  refine ⟨Polynomial.X ^ r + ∑ k : Fin r, Polynomial.C (lift k) * Polynomial.X ^ (k : ℕ),
    ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    exact Polynomial.degree_sum_fin_lt _
  · refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_map, coeff_monicSum, Polynomial.coeff_scaleRoots]
    by_cases hi : i < r
    · rw [dif_pos hi]
      apply Subtype.ext
      simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
      rw [yK_val, IntermediateField.coe_mul, IntermediateField.coe_pow, hδL, ← hr]
      simp only [lift, map_mul, map_pow, map_prod]
      rw [← hnd ⟨i, hi⟩]
      have hci : yAlg T c = yAlg T (de ⟨i, hi⟩) *
          ∏ l ∈ Finset.univ.erase (⟨i, hi⟩ : Fin r), yAlg T (de l) := by
        rw [hcdef, map_prod,
          Finset.mul_prod_erase Finset.univ (fun l => yAlg T (de l)) (Finset.mem_univ _)]
      rw [hci]
      simp only [Fin.val_mk]
      have hk : r - i = (r - i - 1) + 1 := by omega
      set k := r - i - 1 with hkdef
      rw [hk]
      ring
    · rw [dif_neg hi]
      by_cases hir : i = r
      · rw [if_pos hir, map_one, hir, ← hr, Nat.sub_self, pow_zero, mul_one, hr]
        exact hpm.leadingCoeff.symm
      · rw [if_neg hir, map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [← hr]; omega),
          zero_mul]

end Birational

/-! ### Homogeneous components of first-degree relations -/

section Component

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The bigraded decomposition of the pair polynomial ring. -/
abbrev blockGr (n m : ℕ) : (Fin 2 →₀ ℕ) → Submodule ℂ (Poly (n + m)) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ
    (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))

theorem mem_blockGr_iff {f : Poly (n + m)} {s t : ℕ} :
    f ∈ blockGr n m (HilbertMulti.pairDegree s t) ↔ f ∈ BiSpace n m s t := by
  rw [blockGr, HilbertMulti.pairBlockPiece]
  exact Iff.rfl

theorem pairDegree_add (s t s' t' : ℕ) :
    HilbertMulti.pairDegree s t + HilbertMulti.pairDegree s' t' =
      HilbertMulti.pairDegree (s + s') (t + t') := by
  ext j
  fin_cases j <;> simp [HilbertMulti.pairDegree]

theorem pairDegree_inj {s t s' t' : ℕ}
    (h : HilbertMulti.pairDegree s t = HilbertMulti.pairDegree s' t') : s = s' ∧ t = t' := by
  have h0 := congrArg (fun D : Fin 2 →₀ ℕ => D 0) h
  have h1 := congrArg (fun D : Fin 2 →₀ ℕ => D 1) h
  simp [HilbertMulti.pairDegree] at h0 h1
  exact ⟨h0, h1⟩

theorem decompose_X_yRen (j : Fin n) (b : Poly m) (e : ℕ) :
    (DirectSum.decompose (blockGr n m)
      (MvPolynomial.X (Fin.castAdd m j) * yRen b : Poly (n + m))
      (HilbertMulti.pairDegree 1 e) : Poly (n + m)) =
      MvPolynomial.X (Fin.castAdd m j) * yRen (MvPolynomial.homogeneousComponent e b) := by
  classical
  have hmem : ∀ k, (MvPolynomial.X (Fin.castAdd m j) *
      yRen (MvPolynomial.homogeneousComponent k b) : Poly (n + m)) ∈
      blockGr n m (HilbertMulti.pairDegree 1 k) := fun k =>
    mem_blockGr_iff.mpr (biSpace_congr (by simp) (by simp) (mul_mem_biSpace
      (X_castAdd_mem_biSpace j)
      (yRen_mem_biSpace (n := n) (MvPolynomial.homogeneousComponent_isHomogeneous k b))))
  rw [← GradedRing.proj_apply]
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent b]
  rw [map_sum, Finset.mul_sum, map_sum]
  by_cases he : e < b.totalDegree + 1
  · rw [Finset.sum_eq_single e]
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_same _ (hmem e)
    · intro k _ hk
      rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne _ (hmem k) (fun h => hk (pairDegree_inj h).2)
    · intro h
      exact absurd (Finset.mem_range.mpr he) h
  · rw [Finset.sum_eq_zero, MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega), map_zero,
      mul_zero]
    intro k hk
    rw [GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_ne _ (hmem k) (fun h => by
      have h2 := (pairDegree_inj h).2
      rw [Finset.mem_range] at hk
      omega)

theorem relation_component_mem (T : Set (ProjectivePoint n × ProjectivePoint m))
    {i a : Fin n} {s r : Poly m}
    (hmem : (MvPolynomial.X (Fin.castAdd m i) * yRen s -
      MvPolynomial.X (Fin.castAdd m a) * yRen r : Poly (n + m)) ∈ pairIdeal T) (e : ℕ) :
    (MvPolynomial.X (Fin.castAdd m i) * yRen (MvPolynomial.homogeneousComponent e s) -
      MvPolynomial.X (Fin.castAdd m a) * yRen (MvPolynomial.homogeneousComponent e r) :
        Poly (n + m)) ∈ pairIdeal T := by
  have h := pairRepresentatives_blockHomogeneous T (HilbertMulti.pairDegree 1 e) hmem
  change (DirectSum.decompose (blockGr n m) _ (HilbertMulti.pairDegree 1 e) :
    Poly (n + m)) ∈ _ at h
  rw [← GradedRing.proj_apply, map_sub, GradedRing.proj_apply, GradedRing.proj_apply,
    decompose_X_yRen, decompose_X_yRen] at h
  exact h

end Component

/-! ### Birationality and the top coefficient -/

section Ratio

variable (T : Set (ProjectivePoint n × ProjectivePoint m)) [hJ : (pairIdeal T).IsPrime]

theorem exists_homog_relation (a i : Fin n) (ha : xL T a ≠ 0)
    (hu : xL T i / xL T a ∈ KF T) :
    ∃ e : ℕ, ∃ h b : Poly m, h.IsHomogeneous e ∧ b.IsHomogeneous e ∧ yAlg T h ≠ 0 ∧
      yAlg T h * xL T i = yAlg T b * xL T a := by
  classical
  rw [IntermediateField.mem_adjoin_range_iff] at hu
  obtain ⟨r1, s1, hrs⟩ := hu
  rw [← yAlg_eq_aeval, ← yAlg_eq_aeval] at hrs
  by_cases hs : yAlg T s1 = 0
  · refine ⟨0, 1, 0, MvPolynomial.isHomogeneous_one _ _, MvPolynomial.isHomogeneous_zero _ _ _,
      by simp, ?_⟩
    rw [hs, div_zero, div_eq_zero_iff] at hrs
    rcases hrs with h | h
    · rw [h, mul_zero, map_zero, zero_mul]
    · exact absurd h ha
  have hrel : yAlg T s1 * xL T i = yAlg T r1 * xL T a := by
    rw [div_eq_div_iff ha hs] at hrs
    linear_combination hrs
  have hmem : (MvPolynomial.X (Fin.castAdd m i) * yRen s1 -
      MvPolynomial.X (Fin.castAdd m a) * yRen r1 : Poly (n + m)) ∈ pairIdeal T := by
    rw [← toL_eq_zero_iff, map_sub, map_mul, map_mul]
    change xL T i * yAlg T s1 - xL T a * yAlg T r1 = 0
    linear_combination hrel
  obtain ⟨e, he⟩ : ∃ e, yAlg T (MvPolynomial.homogeneousComponent e s1) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hs
    rw [← MvPolynomial.sum_homogeneousComponent s1, map_sum]
    exact Finset.sum_eq_zero fun e _ => hall e
  refine ⟨e, _, _, MvPolynomial.homogeneousComponent_isHomogeneous e s1,
    MvPolynomial.homogeneousComponent_isHomogeneous e r1, he, ?_⟩
  have h0 := (toL_eq_zero_iff T _).mpr (relation_component_mem T hmem e)
  rw [map_sub, map_mul, map_mul] at h0
  change xL T i * yAlg T _ - xL T a * yAlg T _ = 0 at h0
  linear_combination h0

theorem ratio_mem (Y : ProjectiveVariety m) (hY : Y.IsIrreducible)
    (hclosed : closedPairs T = T)
    (hproj : ∀ p q, (p, q) ∈ T → q ∈ Y.points)
    {g : Poly m} {D : ℕ} (hhom : g.IsHomogeneous D) (hg : g ∉ Y.ideal)
    (hgen : ∀ q ∈ Y.points, MvPolynomial.aeval q.rep g ≠ 0 →
      ∃! p : ProjectivePoint n, (p, q) ∈ T)
    (a : Fin n) (ha : xL T a ≠ 0)
    (halg : ∀ j, IsAlgebraic (KF T) (xL T j / xL T a)) (i : Fin n) :
    xL T i / xL T a ∈ KF T := by
  classical
  set u : Fin n → LF T := fun j => xL T j / xL T a with hu
  have hyz : ∀ b, yAlg T b = 0 → b ∈ Y.ideal := fun b hb =>
    mem_of_yRen_mem T Y hY hhom hg hgen ((toL_eq_zero_iff T _).mp hb)
  have hzy : ∀ b, b ∈ Y.ideal → yAlg T b = 0 := fun b hb =>
    (toL_eq_zero_iff T _).mpr (yRen_mem_of_mem T Y hproj hb)
  choose c hc hcF using fun j => exists_clearing T (u j) (halg j)
  set δ := ∏ j, c j with hδdef
  have hδ : yAlg T δ ≠ 0 := by
    rw [hδdef, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hc j
  have hsplit : ∀ j, c j * ∏ l ∈ Finset.univ.erase j, c l = δ := fun j =>
    Finset.mul_prod_erase _ _ (Finset.mem_univ j)
  have hrest : ∀ j, yAlg T (∏ l ∈ Finset.univ.erase j, c l) ≠ 0 := by
    intro j h
    apply hδ
    rw [← hsplit j, map_mul, h, mul_zero]
  let V : Fin (n + m) → LF T :=
    Fin.addCases (fun j => yAlg T δ * u j) (fun k => yAlg T (MvPolynomial.X k))
  have hVx : ∀ j, V (Fin.castAdd m j) = yAlg T δ * u j := fun j => by simp [V]
  have hVy : ∀ k, V (Fin.natAdd n k) = yAlg T (MvPolynomial.X k) := fun k => by simp [V]
  have hFj : ∀ j, ∃ F : Polynomial (Poly m), F.Monic ∧
      F.map (yK T : Poly m →+* KF T) = minpoly (KF T) (V (Fin.castAdd m j)) := by
    intro j
    obtain ⟨F, hFm, hFmin⟩ := hcF j _ (hrest j)
    refine ⟨F, hFm, ?_⟩
    rw [hFmin, hVx, hsplit j]
  have hint : ∀ v, ∃ G : Polynomial (Poly m), G.Monic ∧
      Polynomial.eval₂ (yAlg T : Poly m →+* LF T) (V v) G = 0 := by
    intro v
    refine Fin.addCases (fun j => ?_) (fun k => ?_) v
    · obtain ⟨F, hFm, hFmin⟩ := hFj j
      exact ⟨F, hFm,
        eval₂_eq_zero_of_map_minpoly (yAlg T) (KF T) (yK T) (yK_val T) F _ hFmin⟩
    · refine ⟨Polynomial.X - Polynomial.C (MvPolynomial.X k), Polynomial.monic_X_sub_C _, ?_⟩
      rw [hVy]
      simp
  have hyV : ∀ b : Poly m, yAlg T b ∈ (MvPolynomial.aeval (R := ℂ) V).range := by
    intro b
    refine ⟨yRen b, ?_⟩
    change MvPolynomial.aeval V (yRen b) = yAlg T b
    rw [MvPolynomial.aeval_rename]
    have hfun : (V ∘ Fin.natAdd n) = fun k => yAlg T (MvPolynomial.X k) := funext hVy
    rw [hfun, ← yAlg_eq_aeval]
  obtain ⟨F, hFm, hFmin⟩ := hFj i
  have hθint : IsIntegral (KF T) (V (Fin.castAdd m i)) := by
    rw [hVx, ← yK_val, ← IntermediateField.algebraMap_apply]
    exact isIntegral_algebraMap.mul (halg i).isIntegral
  have hr1 : F.natDegree = 1 := by
    by_contra hne
    have hpos : 0 < F.natDegree := by
      rw [← hFm.natDegree_map (yK T : Poly m →+* KF T), hFmin]
      exact minpoly.natDegree_pos hθint
    haveI : CharZero (KF T) :=
      charZero_of_injective_algebraMap (algebraMap ℂ (KF T)).injective
    have hsep : (minpoly (KF T) (V (Fin.castAdd m i))).Separable :=
      (minpoly.irreducible hθint).separable
    set φ : Poly m →+* KF T := (yK T : Poly m →+* KF T) with hφ
    set ρ := F.resultant (Polynomial.derivative F) with hρdef
    have hdeg1 : (F.map φ).natDegree = F.natDegree := hFm.natDegree_map φ
    have hdeg2 : (Polynomial.derivative (F.map φ)).natDegree =
        (Polynomial.derivative F).natDegree := by
      rw [Polynomial.natDegree_derivative, Polynomial.natDegree_derivative, hdeg1]
    have hkey : (F.map φ).resultant (Polynomial.derivative (F.map φ)) = φ ρ := by
      have h := Polynomial.resultant_map_map F (Polynomial.derivative F) F.natDegree
        (Polynomial.derivative F).natDegree φ
      rw [← Polynomial.derivative_map] at h
      rw [← h, hdeg1, hdeg2]
    have hρ : yAlg T ρ ≠ 0 := by
      rw [← yK_val]
      intro h0
      have h1 : φ ρ = 0 := Subtype.ext h0
      rw [← hkey, hFmin] at h1
      exact Polynomial.resultant_ne_zero _ _ hsep h1
    have hδY : δ ∉ Y.ideal := fun h => hδ (hzy δ h)
    have hρY : ρ ∉ Y.ideal := fun h => hρ (hzy ρ h)
    have hPi : g * δ * ρ ∉ Y.ideal := by
      intro h
      rcases (Ideal.IsPrime.mem_or_mem hY) h with h | h
      · rcases (Ideal.IsPrime.mem_or_mem hY) h with h | h
        · exact hg h
        · exact hδY h
      · exact hρY h
    obtain ⟨v, hv, hvY, hPiv⟩ := exists_point_ne Y hPi
    rw [map_mul, map_mul] at hPiv
    have hgv : MvPolynomial.aeval v g ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hPiv)
    have hδv : MvPolynomial.aeval v δ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hPiv)
    have hρv : MvPolynomial.aeval v ρ ≠ 0 := right_ne_zero_of_mul hPiv
    have hq : ∀ b, yAlg T b = 0 → MvPolynomial.aeval v b = 0 := fun b hb =>
      (MvPolynomial.mem_zeroLocus_iff.mp (hvY v hv rfl)) b (hyz b hb)
    set ev : Poly m →+* ℂ := ((MvPolynomial.aeval v : Poly m →ₐ[ℂ] ℂ) : Poly m →+* ℂ)
      with hev
    have hsepq : (F.map ev).Separable := separable_map_of_resultant_ne_zero F hFm ev hρv
    have hFq0 : F.map ev ≠ 0 := (hFm.map ev).ne_zero
    have hcard : (F.map ev).roots.toFinset.card = F.natDegree := by
      rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsepq),
        IsAlgClosed.card_roots_eq_natDegree, hFm.natDegree_map]
    obtain ⟨w1, hw1, w2, hw2, hw12⟩ :=
      Finset.one_lt_card.mp (show 1 < (F.map ev).roots.toFinset.card by omega)
    have hroot : ∀ w ∈ (F.map ev).roots.toFinset, Polynomial.eval₂ ev w F = 0 := by
      intro w hw
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hFq0, Polynomial.IsRoot.def,
        Polynomial.eval_map] at hw
      exact hw
    have hpt : ∀ w ∈ (F.map ev).roots.toFinset, ∃ x : Point n, ∃ hx : x ≠ 0,
        (Projectivization.mk ℂ x hx, Projectivization.mk ℂ v hv) ∈ T ∧
          x a = MvPolynomial.aeval v δ ∧ x i = w := by
      intro w hw
      obtain ⟨z, hz0, hzy', hzθ⟩ := realize_root (yAlg T) (KF T) (yK T) (yK_val T) V
        (Fin.castAdd m i) hyV hint F hFm hFmin v hq w (hroot w hw)
      let x : Point n := fun j => z (Fin.castAdd m j)
      have hxa : x a = MvPolynomial.aeval v δ := by
        apply hzy'
        rw [hVx]
        simp only [u]
        rw [div_self ha, mul_one]
      have hx0 : x ≠ 0 := by
        intro h
        apply hδv
        rw [← hxa, h]
        rfl
      have hzv : ∀ k, z (Fin.natAdd n k) = v k := by
        intro k
        rw [hzy' _ (MvPolynomial.X k) (hVy k), MvPolynomial.aeval_X]
      have hjoin : joinPoints x v = z := by
        funext w'
        refine Fin.addCases (fun j => ?_) (fun k => ?_) w'
        · simp [joinPoints, x]
        · simp [joinPoints, hzv]
      refine ⟨x, hx0, ?_, hxa, hzθ⟩
      apply mem_of_balanced_vanish T hclosed x v hx0 hv
      intro N f hf hfJ
      rw [hjoin]
      apply hz0
      have hV' : V = (Fin.addCases (fun j => (yAlg T δ / xL T a) * xL T j)
          (fun k => yAlg T (MvPolynomial.X k)) : Fin (n + m) → LF T) := by
        funext w'
        refine Fin.addCases (fun j => ?_) (fun k => ?_) w'
        · rw [hVx]
          simp only [Fin.addCases_left, u]
          ring
        · rw [hVy]
          simp
      rw [hV', aeval_xscale hf, ← toL_eq_aeval, (toL_eq_zero_iff T f).mpr hfJ, mul_zero]
    obtain ⟨x1, hx1, hT1, hx1a, hx1i⟩ := hpt w1 hw1
    obtain ⟨x2, hx2, hT2, hx2a, hx2i⟩ := hpt w2 hw2
    obtain ⟨b0, hb0⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
    have hrep : MvPolynomial.aeval (Projectivization.mk ℂ v hv).rep g ≠ 0 := by
      rw [← hb0, Units.smul_def, BridgesB.aeval_smul_of_isHomogeneous hhom]
      exact mul_ne_zero (pow_ne_zero _ b0.ne_zero) hgv
    obtain ⟨p, _, huniq⟩ := hgen _ hvY hrep
    have hmk : Projectivization.mk ℂ x1 hx1 = Projectivization.mk ℂ x2 hx2 :=
      (huniq _ hT1).trans (huniq _ hT2).symm
    obtain ⟨c', hc'⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ hx1 hx2).mp hmk
    have hc1 : c' = 1 := by
      have h := congrFun hc' a
      simp only [Pi.smul_apply, smul_eq_mul, hx1a, hx2a] at h
      have h2 : (c' - 1) * MvPolynomial.aeval v δ = 0 := by
        rw [sub_mul, h, one_mul, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hδv)
    apply hw12
    rw [← hx1i, ← hx2i, ← hc', hc1, one_smul]
  have hθK : V (Fin.castAdd m i) ∈ KF T := by
    have h := (minpoly.natDegree_eq_one_iff (A := KF T) (x := V (Fin.castAdd m i))).mp
      (by rw [← hFmin, hFm.natDegree_map, hr1])
    obtain ⟨k, hk⟩ := h
    rw [← hk]
    exact k.2
  have hδK : yAlg T δ ∈ KF T := by
    rw [← yK_val]
    exact (yK T δ).2
  have hui : xL T i / xL T a = V (Fin.castAdd m i) / yAlg T δ := by
    rw [hVx]
    simp only [u]
    field_simp
  rw [hui]
  exact div_mem hθK hδK

end Ratio

/-- The top second-factor coefficient of the pair Hilbert polynomial under a birational
projection is the degree of the image. -/
theorem birational_top_coefficient {d : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (hclosed : closedPairs T = T)
    (hT : (pairClosure T).IsIrreducible)
    (Y : ProjectiveVariety m) (hY : Y.IsIrreducible) (hdim : Y.dimension = d)
    (hproj : ∀ p q, (p, q) ∈ T → q ∈ Y.points)
    (P : BaseHilbertPolynomial) (hdeg : P.totalDegree ≤ d)
    (hevent : ∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P =
        (pairHilbert T s t : ℚ))
    (g : Poly m) (D : ℕ) (hhom : g.IsHomogeneous D) (hg : g ∉ Y.ideal)
    (hgen : ∀ q ∈ Y.points, MvPolynomial.aeval q.rep g ≠ 0 →
      ∃! p : ProjectivePoint n, (p, q) ∈ T) :
    mixedHilbertCoefficient P 0 d = Y.degree := by
  classical
  obtain ⟨v0, hv0, hv0Y, hgv0⟩ := exists_point_ne Y hg
  obtain ⟨x0, hx0, hT0⟩ := exists_lift T Y hhom hgen v0 hv0 hv0Y hgv0
  have hne : (pairRepresentatives T).Nonempty := ⟨_, join_mem T x0 v0 hx0 hv0 hT0⟩
  haveI hJ : (pairIdeal T).IsPrime := pairIdeal_isPrime T hT hne
  obtain ⟨a, ha0⟩ : ∃ a, x0 a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)
  have ha : xL T a ≠ 0 := by
    intro h
    have hJa := (toL_eq_zero_iff T _).mp h
    have h1 := (MvPolynomial.mem_vanishingIdeal_iff.mp hJa) _ (join_mem T x0 v0 hx0 hv0 hT0)
    simp [joinPoints] at h1
    exact ha0 h1
  obtain ⟨N, hN⟩ := hevent
  obtain ⟨NY, hNY⟩ := ProjectiveVariety.hilbert_eventually Y
  have hHP : Y.hilbertPolynomial.natDegree = d := hdim
  set c0 := P.coeff (Finsupp.single 0 0 + Finsupp.single 1 d) with hc0
  have hYJ : ∀ b ∈ Y.ideal, (yRen b : Poly (n + m)) ∈ pairIdeal T := fun b hb =>
    yRen_mem_of_mem T Y hproj hb
  have hyz : ∀ b, yAlg T b = 0 → b ∈ Y.ideal := fun b hb =>
    mem_of_yRen_mem T Y hY hhom hg hgen ((toL_eq_zero_iff T _).mp hb)
  -- the leading coefficient of the Hilbert polynomial of `Y` is positive
  have hκ : 0 < Y.hilbertPolynomial.coeff d := by
    have hnn : 0 ≤ Y.hilbertPolynomial.leadingCoeff :=
      OAI.PiExponentJets.W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg _ (NY + 1)
        (fun t ht => by rw [← hNY t (by omega)]; positivity)
    rw [Polynomial.leadingCoeff, hHP] at hnn
    refine lt_of_le_of_ne hnn (fun h0 => ?_)
    have hHP0 : Y.hilbertPolynomial = 0 := by
      rw [← Polynomial.leadingCoeff_eq_zero, Polynomial.leadingCoeff, hHP]
      exact h0.symm
    obtain ⟨cY, hcY⟩ : ∃ cY : Fin m, (MvPolynomial.X cY : Poly m) ∉ Y.ideal := by
      by_contra hall
      push_neg at hall
      apply (Ideal.IsPrime.ne_top hY)
      rw [Ideal.eq_top_iff_one]
      exact Y.isSaturated 1 (fun k => ⟨1, by simpa using hall k⟩)
    have hzero : Y.hilbert (NY + 1) = 0 := by
      have h1 := hNY (NY + 1) (by omega)
      rw [hHP0, Polynomial.eval_zero] at h1
      exact_mod_cast h1
    have hbot : Y.restrictionSpace (NY + 1) = ⊥ := Submodule.finrank_eq_zero.mp hzero
    have hmem : Ideal.Quotient.mk Y.ideal (MvPolynomial.X cY ^ (NY + 1)) ∈
        Y.restrictionSpace (NY + 1) :=
      ⟨_, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X_pow _ _), rfl⟩
    rw [hbot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
    exact hcY (Ideal.IsPrime.mem_of_pow_mem hY _ hmem)
  -- the first-factor ratios are algebraic over the function field of `Y`
  have halg : ∀ j, IsAlgebraic (KF T) (xL T j / xL T a) := by
    intro j
    by_contra htr
    have hbound : ∀ s, N ≤ s → ((s + 1 : ℕ) : ℚ) * Y.hilbertPolynomial.coeff d ≤ c0 := by
      intro s hs
      apply mul_coeff_le_top P hdeg (pairHilbert T) N hN Y.hilbert Y.hilbertPolynomial hHP NY
        hNY s (s + 1) hs
      intro t
      refine mul_hilbert_le_pairHilbert T Y hYJ
        (fun k : Fin (s + 1) => MvPolynomial.X (Fin.castAdd m a) ^ (s - (k : ℕ)) *
          MvPolynomial.X (Fin.castAdd m j) ^ (k : ℕ)) ?_ ?_ t
      · intro k
        have h := mul_mem_biSpace (pow_mem_biSpace (X_castAdd_mem_biSpace (m := m) a) (s - k))
          (pow_mem_biSpace (X_castAdd_mem_biSpace (m := m) j) k)
        exact biSpace_congr (by have := k.2; omega) (by simp) h
      · intro b hb k
        apply hyz
        have h0 := (toL_eq_zero_iff T _).mpr hb
        rw [map_sum] at h0
        have hterm : ∀ l : Fin (s + 1), toL T (MvPolynomial.X (Fin.castAdd m a) ^ (s - (l : ℕ)) *
            MvPolynomial.X (Fin.castAdd m j) ^ (l : ℕ) * yRen (b l)) =
            xL T a ^ s * ((xL T j / xL T a) ^ (l : ℕ) * yAlg T (b l)) := by
          intro l
          rw [map_mul, map_mul, map_pow, map_pow]
          change xL T a ^ (s - (l : ℕ)) * xL T j ^ (l : ℕ) * yAlg T (b l) = _
          have hl : (l : ℕ) ≤ s := by have := l.2; omega
          have hpow : xL T a ^ s = xL T a ^ (s - (l : ℕ)) * xL T a ^ (l : ℕ) := by
            rw [← pow_add, Nat.sub_add_cancel hl]
          rw [hpow, div_pow]
          field_simp
        simp_rw [hterm] at h0
        rw [← Finset.mul_sum] at h0
        have hsum : ∑ l : Fin (s + 1), (xL T j / xL T a) ^ (l : ℕ) * yAlg T (b l) = 0 :=
          (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ ha)
        let pK : Polynomial (KF T) :=
          ∑ l : Fin (s + 1), Polynomial.C (yK T (b l)) * Polynomial.X ^ (l : ℕ)
        have hpK : Polynomial.aeval (xL T j / xL T a) pK = 0 := by
          simp only [pK, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
            IntermediateField.algebraMap_apply, yK_val]
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro l _
          ring
        have hpK0 : pK = 0 := by
          by_contra hne
          exact htr ⟨pK, hne, hpK⟩
        have hcoeff := congrArg (fun Q : Polynomial (KF T) => Q.coeff k) hpK0
        simp only [pK, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
          Polynomial.coeff_zero] at hcoeff
        rw [Finset.sum_eq_single k] at hcoeff
        · rw [if_pos rfl] at hcoeff
          rw [← yK_val, hcoeff]
          rfl
        · intro l _ hl
          rw [if_neg]
          intro h
          exact hl (Fin.ext h.symm)
        · intro h
          exact absurd (Finset.mem_univ _) h
    obtain ⟨s0, hs0⟩ := exists_nat_gt (c0 / Y.hilbertPolynomial.coeff d)
    have h1 := hbound (max N s0) (le_max_left _ _)
    have h2 : (s0 : ℚ) ≤ ((max N s0 + 1 : ℕ) : ℚ) := by
      exact_mod_cast (by omega : s0 ≤ max N s0 + 1)
    rw [div_lt_iff₀ hκ] at hs0
    nlinarith
  -- birationality: the ratios are quotients of homogeneous forms on `Y`
  have hratio : ∀ i, xL T i / xL T a ∈ KF T := fun i =>
    ratio_mem T Y hY hclosed hproj hhom hg hgen a ha halg i
  choose e hh hb hhH hbH hh0 hrel using fun i => exists_homog_relation T a i ha (hratio i)
  set H : Poly m := ∏ i, hh i with hHdef
  set E : ℕ := ∑ i, e i with hEdef
  let b' : Fin n → Poly m := fun i => hb i * ∏ j ∈ Finset.univ.erase i, hh j
  have hb'H : ∀ i, (b' i).IsHomogeneous E := by
    intro i
    have h1 := (hbH i).mul
      (MvPolynomial.IsHomogeneous.prod (Finset.univ.erase i) hh e (fun j _ => hhH j))
    rwa [Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1
  have hH0 : yAlg T H ≠ 0 := by
    rw [hHdef, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hh0 i
  have hrel' : ∀ i, yAlg T (b' i) = (yAlg T H / xL T a) * xL T i := by
    intro i
    have hsplit : yAlg T H = yAlg T (hh i) * ∏ j ∈ Finset.univ.erase i, yAlg T (hh j) := by
      rw [hHdef, map_prod,
        Finset.mul_prod_erase Finset.univ (fun j => yAlg T (hh j)) (Finset.mem_univ i)]
    simp only [b', map_mul, map_prod]
    rw [hsplit, div_mul_eq_mul_div, eq_div_iff ha]
    linear_combination (-(∏ j ∈ Finset.univ.erase i, yAlg T (hh j))) * (hrel i)
  let Φ : Poly (n + m) →ₐ[ℂ] Poly m :=
    MvPolynomial.aeval (Fin.addCases b' (fun k => MvPolynomial.X k))
  have hdegΦ : ∀ s t, ∀ f ∈ BiSpace n m s t, (Φ f).IsHomogeneous (t + s * E) := by
    intro s t f hf
    rw [MvPolynomial.mem_restrictSupport_iff] at hf
    rw [f.as_sum, map_sum]
    apply MvPolynomial.IsHomogeneous.sum
    intro d' hd
    obtain ⟨hs, ht⟩ := hf (Finset.mem_coe.mpr hd)
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    have h1 := MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i => b' i ^ d' (Fin.castAdd m i)) (fun i => E * d' (Fin.castAdd m i))
      (fun i _ => (hb'H i).pow _)
    have h2 := MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun k => (MvPolynomial.X k : Poly m) ^ d' (Fin.natAdd n k))
      (fun k => d' (Fin.natAdd n k)) (fun k _ => MvPolynomial.isHomogeneous_X_pow _ _)
    have h3 := (MvPolynomial.isHomogeneous_C (Fin m) (f.coeff d')).mul (h1.mul h2)
    rw [← Finset.mul_sum, hs, ht] at h3
    rw [MvPolynomial.algebraMap_eq]
    convert h3 using 1
    ring
  have hΦL : ∀ f, yAlg T (Φ f) = MvPolynomial.aeval
      (Fin.addCases (fun i => (yAlg T H / xL T a) * xL T i)
        (fun k => yAlg T (MvPolynomial.X k)) : Fin (n + m) → LF T) f := by
    intro f
    rw [MvPolynomial.comp_aeval_apply]
    have hfun : (fun v => yAlg T (Fin.addCases b' (fun k => MvPolynomial.X k) v)) =
        (Fin.addCases (fun i => (yAlg T H / xL T a) * xL T i)
          (fun k => yAlg T (MvPolynomial.X k)) : Fin (n + m) → LF T) := by
      funext v
      refine Fin.addCases (fun i => ?_) (fun k => ?_) v
      · simp only [Fin.addCases_left]
        exact hrel' i
      · simp
    rw [hfun]
  have hkerΦ : ∀ s t, ∀ f ∈ BiSpace n m s t, Φ f ∈ Y.ideal → f ∈ pairIdeal T := by
    intro s t f hf hΦf
    have h1 : yAlg T (Φ f) = 0 := (toL_eq_zero_iff T _).mpr (hYJ _ hΦf)
    rw [hΦL, aeval_xscale hf, ← toL_eq_aeval] at h1
    have hc : yAlg T H / xL T a ≠ 0 := div_ne_zero hH0 ha
    exact (toL_eq_zero_iff T f).mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc))
  have hupper : ∀ t, pairHilbert T N t ≤ Y.hilbert (t + N * E) := fun t =>
    pairHilbert_le_hilbert T Y Φ N t (t + N * E) (hdegΦ N t) (hkerΦ N t)
  have hlower : ∀ t, 1 * Y.hilbert t ≤ pairHilbert T N t := by
    intro t
    refine mul_hilbert_le_pairHilbert T Y hYJ
      (fun _ : Fin 1 => MvPolynomial.X (Fin.castAdd m a) ^ N) ?_ ?_ t
    · intro _
      exact biSpace_congr (by ring) (by ring)
        (pow_mem_biSpace (X_castAdd_mem_biSpace (m := m) a) N)
    · intro b hb k
      apply hyz
      have h0 := (toL_eq_zero_iff T _).mpr hb
      rw [Fin.sum_univ_one, map_mul, map_pow] at h0
      change xL T a ^ N * yAlg T (b 0) = 0 at h0
      have hk : k = 0 := Subsingleton.elim _ _
      rw [hk]
      exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ ha)
  have hle1 := top_le_coeff P hdeg (pairHilbert T) N hN Y.hilbert Y.hilbertPolynomial hHP NY
    hNY N (N * E) le_rfl hupper
  have hle2 := mul_coeff_le_top P hdeg (pairHilbert T) N hN Y.hilbert Y.hilbertPolynomial hHP
    NY hNY N 1 le_rfl hlower
  have hceq : c0 = Y.hilbertPolynomial.coeff d := by
    refine le_antisymm hle1 ?_
    rw [Nat.cast_one, one_mul] at hle2
    exact hle2
  unfold mixedHilbertCoefficient
  change _ = OAI.PiExponentJets.W22.actualMultiplicity Y.ideal Y.isHomogeneous Y.dimension
  unfold OAI.PiExponentJets.W22.actualMultiplicity
  rw [hdim]
  change (Nat.factorial 0 : ℚ) * d.factorial * c0 = Y.hilbertPolynomial.coeff d * d.factorial
  rw [hceq, Nat.factorial_zero, Nat.cast_one, one_mul, mul_comm]

end
end DistinctDistances.TrackB.BridgesBBir
