import DistinctDistances.Foundations.Affine
import DistinctDistances.Foundations.Local
import DistinctDistances.Foundations.PointLocal
import DistinctDistances.Foundations.LocalHilbert
import DistinctDistances.TrackD.Profiles.Defs
import DistinctDistances.TrackD.SecantsChart
import DistinctDistances.TrackA.LocalHilbertFiniteSupport
import DistinctDistances.TrackA.TangentHyperplaneSupport
import DistinctDistances.TrackA.PrincipalPointIsolationSupport
import DistinctDistances.Bridges.ProjectiveEnvelope
import OAI.RingTheory.Multiplicity.IdealGradedRing

/-! Point jets for the outer lift (sparse-cones.tex:580–594).

The lift `outer_lift_curve` (193) needs that the chart label map
`φ(y) = (y - p)/(y - p)_{i₀}` is étale at a smooth point `q` of the target
carrier `Y` onto the specialized label equations. We use the purely algebraic
form: the jets `ℂ[w]/(E + m_{w₀}^{t+1})` of the equations at `w₀ = φ(q)` and
the jets `ℂ[y]/(I(Y) + m_q^{t+1})` of `Y` at `q` are isomorphic through `φ`
(`jet_transfer`). Surjectivity comes from injectivity of `dφ` on `T_qY`; the
dimension count compares the Jacobian bound on the source (`jet_source_upper`)
with the smooth-point lower bound on the target (`jet_smooth_lower`). -/
namespace DistinctDistances.SparseCones
open MvPolynomial
open scoped Classical
noncomputable section
variable {n : ℕ}

/-- Clearing the chart denominator of `f(φ(y))`, `φ(y) = (y - p)/(y - p)_{i₀}`:
`chartClear p i₀ f (y) = (y - p)_{i₀}^{deg f} · f(φ(y))` off the chart hyperplane. -/
def chartClear (p : Point n) (i₀ : Fin n) (f : Poly n) : Poly n :=
  ∑ j ∈ Finset.range (f.totalDegree + 1),
    (X i₀ - C (p i₀)) ^ (f.totalDegree - j) *
      aeval (fun a => X a - C (p a)) (homogeneousComponent j f)

theorem eval_translate (p x : Point n) (g : Poly n) :
    eval x (aeval (fun a => (X a - C (p a) : Poly n)) g) = eval (x - p) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | mul_X f i hf =>
    rw [map_mul, map_mul, hf, map_mul]
    simp

theorem chartClear_eval (p : Point n) (i₀ : Fin n) (f : Poly n) (x : Point n)
    (hx : (x - p) i₀ ≠ 0) :
    eval x (chartClear p i₀ f) =
      ((x - p) i₀) ^ f.totalDegree * eval (((x - p) i₀)⁻¹ • (x - p)) f := by
  set δ := (x - p) i₀ with hδ
  set v : Point n := δ⁻¹ • (x - p) with hv
  have hxv : x - p = δ • v := by
    rw [hv, smul_smul, mul_inv_cancel₀ hx, one_smul]
  have hf : eval v f = ∑ j ∈ Finset.range (f.totalDegree + 1),
      eval v (homogeneousComponent j f) := by
    conv_lhs => rw [← sum_homogeneousComponent f]
    rw [map_sum]
  unfold chartClear
  rw [map_sum, hf, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjD : j ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [map_mul, map_pow, eval_translate, hxv,
    Bridges.homogeneous_eval_smul _ (homogeneousComponent_isHomogeneous j f)]
  have hδx : eval x (X i₀ - C (p i₀) : Poly n) = δ := by simp [hδ]
  rw [hδx, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hjD]

/-- A polynomial nonzero at `x` is a unit in the jets at `x`. -/
theorem jet_unit (I : Ideal (Poly n)) (x : Point n) (t : ℕ) (g : Poly n)
    (hg : eval x g ≠ 0) :
    IsUnit (Ideal.Quotient.mk (I ⊔ pointIdeal x ^ (t+1)) g) := by
  set J := I ⊔ pointIdeal x ^ (t+1)
  have hsplit : Ideal.Quotient.mk J g =
      Ideal.Quotient.mk J (C (eval x g)) + Ideal.Quotient.mk J (g - C (eval x g)) := by
    rw [← map_add]; congr 1; ring
  have hmem : g - C (eval x g) ∈ pointIdeal x := by
    change g - C (eval x g) ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n))
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  have hnil : IsNilpotent (Ideal.Quotient.mk J (g - C (eval x g))) := by
    refine ⟨t+1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.pow_mem_pow hmem (t+1))
  have hunit : IsUnit (Ideal.Quotient.mk J (C (eval x g))) := by
    have : Ideal.Quotient.mk J (C (eval x g)) =
        algebraMap ℂ (Poly n ⧸ J) (eval x g) := rfl
    rw [this]
    exact (IsUnit.mk0 _ hg).map _
  rw [hsplit]
  exact hnil.isUnit_add_left_of_commute hunit (Commute.all _ _)

/-- The chart label map on jets: `w_b ↦ (y_b - p_b)/(y_b - p_b)_{i₀}` in
`ℂ[y]/(I + m_q^{t+1})`, where the denominator is a unit (`jet_unit`). -/
def chartJetMap (I : Ideal (Poly n)) (q p : Point n) (i₀ : Fin n)
    (hq : (q - p) i₀ ≠ 0) (t : ℕ) :
    Poly n →ₐ[ℂ] Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1)) :=
  aeval fun b => Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X b - C (p b)) *
    ((jet_unit I q t (X i₀ - C (p i₀)) (by simpa using hq)).unit⁻¹ :
      (Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1)))ˣ)

/-- The linear polynomial `∑ ℓ(e_i) (X_i - x_i)` of a functional. -/
def linPoly (x : Point n) : (Point n →ₗ[ℂ] ℂ) →ₗ[ℂ] Poly n where
  toFun ℓ := ∑ i : Fin n, ℓ (Pi.single i 1) • (X i - C (x i))
  map_add' ℓ ℓ' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c ℓ := by simp [smul_smul, Finset.smul_sum]

theorem linPoly_proj (x : Point n) (i : Fin n) :
    linPoly x (LinearMap.proj i) = X i - C (x i) := by
  simp [linPoly, Pi.single_apply]

theorem linPoly_differential (x : Point n) (f : Poly n) :
    linPoly x (differential f x) = TrackA.tangentLinearPart f x := by
  simp only [linPoly, LinearMap.coe_mk, AddHom.coe_mk, TrackA.tangentLinearPart, differential]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [MvPolynomial.C_mul']
  congr 1
  simp [Pi.single_apply]

/-- sc:outer-lift.cotangent . If `S ⊆ I ≤ m_x` and the
common kernel `T` of the differentials of `S` at `x` has rank `k`, then `k`
coordinate functions span the cotangent space `m_x/(I + m_x²)`: every
`X_i - x_i` lies in their span plus `I + m_x²`. Proof: the coordinate
functionals restricted to `T` span `T*`; extract a basis `e_{j_a}*|_T`
(`exists_linearIndependent`); for each `i`, `e_i* - ∑ c_a e_{j_a}*` vanishes on
`T = ⨅ ker df(x)`, hence is a finite combination of differentials `df(x)`,
`f ∈ S` (`Submodule.mem_span_of_iInf_ker_le_ker` after reducing to a finite
spanning subfamily of `span {df(x)}`); first-order Taylor expansion
`f - ∑ ∂_i f(x) (X_i - x_i) ∈ m_x²` (as `f(x) = 0`) finishes. -/
theorem jet_cotangent_coordinates (I : Ideal (Poly n)) (x : Point n)
    (hI : I ≤ pointIdeal x) (S : Set (Poly n)) (hS : S ⊆ I) (k : ℕ)
    (hk : Module.finrank ℂ
      ((⨅ f ∈ S, LinearMap.ker (differential f x) : Submodule ℂ (Point n))) = k) :
    ∃ j : Fin k → Fin n, ∀ i : Fin n, X i - C (x i) ∈
      Submodule.span ℂ (Set.range fun a => (X (j a) - C (x (j a)) : Poly n)) ⊔
        (I ⊔ pointIdeal x ^ 2).restrictScalars ℂ := by
  set T : Submodule ℂ (Point n) := ⨅ f ∈ S, LinearMap.ker (differential f x) with hT
  let L : Fin n → Module.Dual ℂ T := fun i => (LinearMap.proj i).comp T.subtype
  -- the coordinate functionals span the dual of `T`
  have hspan : Submodule.span ℂ (Set.range L) = ⊤ := by
    rw [eq_top_iff]
    intro K _
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    rw [Submodule.mem_iInf] at hv
    have hv0 : (v : Point n) = 0 := funext fun i => hv i
    have : v = 0 := Subtype.ext hv0
    rw [LinearMap.mem_ker, this, map_zero]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' ℂ L
  have hfin : Finite κ := hli.finite_of_isNoetherian
  have hκft : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli, hsp, hspan, finrank_top, Subspace.dual_finrank_eq, hk]
  let eκ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun b => a (eκ b), fun i => ?_⟩
  -- `L i` is a combination of the chosen `L (a b)`
  have hLi : L i ∈ Submodule.span ℂ (Set.range (L ∘ a)) := by
    rw [hsp, hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hLi
  -- the defect functional vanishes on `T`
  set ℓ : Point n →ₗ[ℂ] ℂ :=
    LinearMap.proj i - ∑ b : κ, c b • LinearMap.proj (a b) with hℓ
  have hℓT : (⨅ f : S, LinearMap.ker (differential (f : Poly n) x)) ≤ LinearMap.ker ℓ := by
    intro v hv
    have hvT : v ∈ T := by
      rw [hT, Submodule.mem_iInf]
      intro f
      rw [Submodule.mem_iInf]
      intro hf
      exact (Submodule.mem_iInf _).mp hv ⟨f, hf⟩
    have := congrArg (fun K : Module.Dual ℂ T => K ⟨v, hvT⟩) hc
    have hthis : ((∑ b, c b • LinearMap.proj (a b) : Point n →ₗ[ℂ] ℂ)) v = v i := by
      simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        Function.comp_apply, L, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.proj_apply] using this
    rw [LinearMap.mem_ker, hℓ]
    simp only [LinearMap.sub_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply]
    have hthis2 : (∑ c_1, c c_1 • v (a c_1)) = v i := by
      simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply] using hthis
    rw [hthis2, sub_self]
  have hℓspan := FiniteDimensional.mem_span_of_iInf_ker_le_ker hℓT
  obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hℓspan
  -- translate into polynomials
  have hpoly : X i - C (x i) =
      ∑ b : κ, c b • (X (a b) - C (x (a b))) + linPoly x ℓ := by
    rw [hℓ, map_sub, map_sum, linPoly_proj]
    simp only [map_smul, linPoly_proj]
    ring
  have hlin : linPoly x ℓ ∈ (I ⊔ pointIdeal x ^ 2).restrictScalars ℂ := by
    rw [← hcf, map_finsuppSum]
    refine Submodule.finsuppSum_mem _ _ _ _ (fun f _ => ?_)
    rw [map_smul, linPoly_differential]
    refine Submodule.smul_mem _ _ ?_
    have hrem := TrackA.tangent_first_order_remainder (f : Poly n) x
    have hfx : aeval x (f : Poly n) = 0 := by
      have : (f : Poly n) ∈ pointIdeal x := hI (hS f.2)
      have h' : (f : Poly n) ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Point n)) := this
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at h'
      exact h'
    rw [hfx, map_zero, sub_zero] at hrem
    show TrackA.tangentLinearPart (f : Poly n) x ∈ I ⊔ pointIdeal x ^ 2
    rw [show TrackA.tangentLinearPart (f : Poly n) x =
      (f : Poly n) - ((f : Poly n) - TrackA.tangentLinearPart (f : Poly n) x) by ring]
    exact (I ⊔ pointIdeal x ^ 2).sub_mem (Ideal.mem_sup_left (hS f.2))
      (Ideal.mem_sup_right hrem)
  rw [hpoly]
  refine Submodule.add_mem_sup ?_ hlin
  refine Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact ⟨eκ.symm b, by simp⟩

/-! ### Helpers for the smooth-point jet count -/

theorem jet_quot_finite (I : Ideal (Poly n)) (x : Point n) (t : ℕ) :
    Module.Finite ℂ (Poly n ⧸ (I ⊔ pointIdeal x ^ (t + 1))) := by
  have hTSfin : Module.Finite ℂ
      ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t) :=
    OAI.QuarticPowerFree.totalSpace_finite t
  have hKsup : pointIdeal x ^ (t + 1) ≤ I ⊔ pointIdeal x ^ (t + 1) := le_sup_right
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mkₐ ℂ (I ⊔ pointIdeal x ^ (t + 1))).toLinearMap.domRestrict
        (OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t)) := by
    intro y
    obtain ⟨gg, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨low, high, hgh, hlow_deg, hhigh_mem⟩ := AffineVariety.transDecomp x t gg
    have hlow_mem : low ∈ OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t := by
      rwa [OAI.QuarticPowerFree.mem_totalSpace]
    refine ⟨⟨low, hlow_mem⟩, ?_⟩
    show (Ideal.Quotient.mkₐ ℂ (I ⊔ pointIdeal x ^ (t + 1))) low =
      Ideal.Quotient.mk (I ⊔ pointIdeal x ^ (t + 1)) gg
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have h_eq : low - gg = -high := by rw [hgh]; ring
    rw [h_eq]
    exact neg_mem (hKsup hhigh_mem)
  exact Module.Finite.of_surjective _ hsurj

theorem finrank_homogeneousSubmodule (k s : ℕ) :
    Module.finrank ℂ (homogeneousSubmodule (Fin k) ℂ s) = k.multichoose s := by
  rw [(OAI.Lech.Grading.homogeneousEquiv ℂ k s).finrank_eq, Module.finrank_pi,
    OAI.Lech.Grading.index_card]

instance homogeneousSubmodule_finite (k s : ℕ) :
    Module.Finite ℂ (homogeneousSubmodule (Fin k) ℂ s) :=
  Module.Finite.equiv (OAI.Lech.Grading.homogeneousEquiv ℂ k s).symm

theorem aeval_homog_mem_pow {k : ℕ} (u : Fin k → Poly n) (m : Ideal (Poly n))
    (hu : ∀ a, u a ∈ m) {s : ℕ} {F : MvPolynomial (Fin k) ℂ} (hF : F.IsHomogeneous s) :
    aeval u F ∈ m ^ s := by
  rw [F.as_sum, map_sum]
  refine Ideal.sum_mem _ (fun d hd => ?_)
  rw [aeval_monomial]
  have hdeg : ∑ i ∈ d.support, d i = s := by
    rw [← Finsupp.degree_apply, Finsupp.degree_eq_weight_one]
    exact hF (mem_support_iff.mp hd)
  refine Ideal.mul_mem_left _ _ ?_
  rw [Finsupp.prod, ← hdeg, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (hu i) _)

theorem mul_mem_sup_pow (I m : Ideal (Poly n)) {r r' : ℕ} {a b : Poly n}
    (ha : a ∈ I ⊔ m ^ r) (hb : b ∈ I ⊔ m ^ r') : a * b ∈ I ⊔ m ^ (r + r') := by
  obtain ⟨i, hi, μ, hμ, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨i', hi', μ', hμ', rfl⟩ := Submodule.mem_sup.mp hb
  have h1 : i * (i' + μ') + μ * i' ∈ I :=
    I.add_mem (I.mul_mem_right _ hi) (I.mul_mem_left _ hi')
  have h2 : μ * μ' ∈ m ^ (r + r') := by
    rw [pow_add]; exact Ideal.mul_mem_mul hμ hμ'
  have : (i + μ) * (i' + μ') = (i * (i' + μ') + μ * i') + μ * μ' := by ring
  rw [this]
  exact Submodule.add_mem_sup h1 h2

/-- The image of homogeneous polynomials of degree `s` in `u`. -/
def homogImage {k : ℕ} (u : Fin k → Poly n) (s : ℕ) : Submodule ℂ (Poly n) :=
  (homogeneousSubmodule (Fin k) ℂ s).map (aeval u).toLinearMap

theorem pow_le_homogImage_sup (I m : Ideal (Poly n)) {k : ℕ} (u : Fin k → Poly n)
    (hu : ∀ a, u a ∈ m)
    (hm0 : ∀ x : Poly n, x ∈ homogImage u 0 ⊔ m.restrictScalars ℂ)
    (hm1 : ∀ x ∈ m, x ∈ homogImage u 1 ⊔ (I ⊔ m ^ 2).restrictScalars ℂ) :
    ∀ s : ℕ, ∀ x ∈ m ^ s, x ∈ homogImage u s ⊔ (I ⊔ m ^ (s+1)).restrictScalars ℂ := by
  intro s
  induction s with
  | zero =>
    intro x _
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp (hm0 x)
    refine Submodule.add_mem_sup hw ?_
    show c ∈ I ⊔ m ^ (0+1)
    rw [zero_add, pow_one]
    exact Ideal.mem_sup_right hc
  | succ s ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => add_mem hx hy)
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp (ih a ha)
    obtain ⟨w', hw', c', hc', rfl⟩ := Submodule.mem_sup.mp (hm1 b hb)
    obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hw'
    have hFG : (aeval u).toLinearMap F * (aeval u).toLinearMap G ∈ homogImage u (s+1) := by
      refine Submodule.mem_map.mpr ⟨F * G, ?_, ?_⟩
      · exact (mem_homogeneousSubmodule _ _).mpr
          (((mem_homogeneousSubmodule _ _).mp hF).mul ((mem_homogeneousSubmodule _ _).mp hG))
      · simp
    have hwm : (aeval u).toLinearMap F ∈ m ^ s :=
      aeval_homog_mem_pow u m hu ((mem_homogeneousSubmodule _ _).mp hF)
    have hw'm : (aeval u).toLinearMap G ∈ m ^ 1 :=
      aeval_homog_mem_pow u m hu ((mem_homogeneousSubmodule _ _).mp hG)
    have hc' : c' ∈ I ⊔ m ^ 2 := hc'
    have hc : c ∈ I ⊔ m ^ (s+1) := hc
    have hrest : (aeval u).toLinearMap F * c' + c * (aeval u).toLinearMap G + c * c' ∈
        I ⊔ m ^ (s + 1 + 1) := by
      refine add_mem (add_mem ?_ ?_) ?_
      · have := mul_mem_sup_pow I m (Ideal.mem_sup_right hwm) hc'
        exact (sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) I) this
      · have := mul_mem_sup_pow I m hc (Ideal.mem_sup_right hw'm)
        exact (sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) I) this
      · have := mul_mem_sup_pow I m hc hc'
        exact (sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) I) this
    have heq : ((aeval u).toLinearMap F + c) * ((aeval u).toLinearMap G + c') =
        (aeval u).toLinearMap F * (aeval u).toLinearMap G +
          ((aeval u).toLinearMap F * c' + c * (aeval u).toLinearMap G + c * c') := by ring
    rw [heq]
    exact Submodule.add_mem_sup hFG hrest


theorem finrank_quot_le_of_sup (A B : Ideal (Poly n)) (hAB : A ≤ B)
    [Module.Finite ℂ (Poly n ⧸ A)] (W : Submodule ℂ (Poly n))
    (hBW : ∀ z ∈ B, ∃ w ∈ W, z - w ∈ A) :
    Module.finrank ℂ (Poly n ⧸ A) ≤ Module.finrank ℂ (Poly n ⧸ B) +
      Module.finrank ℂ (W.map (Ideal.Quotient.mkₐ ℂ A).toLinearMap) := by
  have hρ : Function.Surjective (Ideal.Quotient.factorₐ ℂ hAB).toLinearMap := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk A z, Ideal.Quotient.factorₐ_apply_mk ℂ hAB z⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (Ideal.Quotient.factorₐ ℂ hAB).toLinearMap
  rw [LinearMap.range_eq_top.mpr hρ, finrank_top] at h1
  have hker : LinearMap.ker (Ideal.Quotient.factorₐ ℂ hAB).toLinearMap ≤
      W.map (Ideal.Quotient.mkₐ ℂ A).toLinearMap := by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply_mk,
      Ideal.Quotient.eq_zero_iff_mem] at hy
    obtain ⟨w, hw, hzw⟩ := hBW z hy
    refine Submodule.mem_map.mpr ⟨w, hw, ?_⟩
    rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    rw [show w - z = -(z - w) by ring]
    exact neg_mem hzw
  have h3 := Submodule.finrank_mono hker
  omega

/-- One graded step of the jet count. -/
theorem jet_step (I m : Ideal (Poly n)) {k : ℕ} (u : Fin k → Poly n) (hu : ∀ a, u a ∈ m)
    (hspan : ∀ s : ℕ, ∀ x ∈ m ^ s, x ∈ homogImage u s ⊔ (I ⊔ m ^ (s+1)).restrictScalars ℂ)
    {e : ℕ} {Fe : MvPolynomial (Fin k) ℂ} (hFe : Fe.IsHomogeneous e) (hFe0 : Fe ≠ 0)
    (hrel : aeval u Fe ∈ I ⊔ m ^ (e+1)) (s : ℕ)
    [Module.Finite ℂ (Poly n ⧸ (I ⊔ m ^ (s+1)))] :
    Module.finrank ℂ (Poly n ⧸ (I ⊔ m ^ (s+1))) +
        (if e ≤ s then k.multichoose (s - e) else 0) ≤
      Module.finrank ℂ (Poly n ⧸ (I ⊔ m ^ s)) + k.multichoose s := by
  have hAB : I ⊔ m ^ (s+1) ≤ I ⊔ m ^ s :=
    sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) I
  have hstep := finrank_quot_le_of_sup (I ⊔ m ^ (s+1)) (I ⊔ m ^ s) hAB (homogImage u s)
    (by
      intro z hz
      obtain ⟨i, hi, μ, hμ, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨w, hw, c, hc, hwc⟩ := Submodule.mem_sup.mp (hspan s μ hμ)
      refine ⟨w, hw, ?_⟩
      have hc' : c ∈ I ⊔ m ^ (s+1) := hc
      rw [show i + μ - w = i + c by rw [← hwc]; ring]
      exact (I ⊔ m ^ (s+1)).add_mem (Ideal.mem_sup_left hi) hc')
  -- the image of degree-`s` forms modulo `I + m^{s+1}`
  set g : MvPolynomial (Fin k) ℂ →ₗ[ℂ] Poly n ⧸ (I ⊔ m ^ (s+1)) :=
    (Ideal.Quotient.mkₐ ℂ (I ⊔ m ^ (s+1))).toLinearMap ∘ₗ (aeval u).toLinearMap with hg
  have hmapeq : (homogImage u s).map (Ideal.Quotient.mkₐ ℂ (I ⊔ m ^ (s+1))).toLinearMap =
      LinearMap.range (g.domRestrict (homogeneousSubmodule (Fin k) ℂ s)) := by
    rw [LinearMap.range_domRestrict, hg, Submodule.map_comp]
    rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker
    (g.domRestrict (homogeneousSubmodule (Fin k) ℂ s))
  rw [finrank_homogeneousSubmodule] at h2
  have h4 : (if e ≤ s then k.multichoose (s - e) else 0) ≤
      Module.finrank ℂ (LinearMap.ker (g.domRestrict (homogeneousSubmodule (Fin k) ℂ s))) := by
    split_ifs with hes
    · have hmap : ∀ G ∈ homogeneousSubmodule (Fin k) ℂ (s - e),
          LinearMap.mulLeft ℂ Fe G ∈ homogeneousSubmodule (Fin k) ℂ s := by
        intro G hG
        have := hFe.mul ((mem_homogeneousSubmodule _ _).mp hG)
        rw [show e + (s - e) = s by omega] at this
        exact (mem_homogeneousSubmodule _ _).mpr this
      have hinj : Function.Injective ((LinearMap.mulLeft ℂ Fe).restrict hmap) := by
        intro G G' hGG
        apply Subtype.ext
        have := congrArg Subtype.val hGG
        exact mul_left_cancel₀ hFe0 this
      have hgk : LinearMap.range ((LinearMap.mulLeft ℂ Fe).restrict hmap) ≤
          LinearMap.ker (g.domRestrict (homogeneousSubmodule (Fin k) ℂ s)) := by
        rintro _ ⟨G, rfl⟩
        rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.restrict_coe_apply,
          LinearMap.mulLeft_apply, hg, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
          AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
          map_mul]
        have hG : aeval u (G : MvPolynomial (Fin k) ℂ) ∈ m ^ (s - e) :=
          aeval_homog_mem_pow u m hu ((mem_homogeneousSubmodule _ _).mp G.2)
        have := mul_mem_sup_pow I m hrel (Ideal.mem_sup_right hG)
        rwa [show e + 1 + (s - e) = s + 1 by omega] at this
      calc k.multichoose (s - e)
          = Module.finrank ℂ (homogeneousSubmodule (Fin k) ℂ (s - e)) :=
            (finrank_homogeneousSubmodule _ _).symm
        _ = Module.finrank ℂ (LinearMap.range ((LinearMap.mulLeft ℂ Fe).restrict hmap)) :=
            (LinearMap.finrank_range_of_inj hinj).symm
        _ ≤ _ := Submodule.finrank_mono hgk
    · exact Nat.zero_le _
  rw [hmapeq] at hstep
  omega

/-- Summed jet count. -/
theorem jet_sum (I m : Ideal (Poly n)) {k : ℕ} (u : Fin k → Poly n) (hu : ∀ a, u a ∈ m)
    (hspan : ∀ s : ℕ, ∀ x ∈ m ^ s, x ∈ homogImage u s ⊔ (I ⊔ m ^ (s+1)).restrictScalars ℂ)
    {e : ℕ} {Fe : MvPolynomial (Fin k) ℂ} (hFe : Fe.IsHomogeneous e) (hFe0 : Fe ≠ 0)
    (hrel : aeval u Fe ∈ I ⊔ m ^ (e+1))
    (hfin : ∀ s, Module.Finite ℂ (Poly n ⧸ (I ⊔ m ^ (s+1)))) (N : ℕ) :
    Module.finrank ℂ (Poly n ⧸ (I ⊔ m ^ N)) +
        ∑ s ∈ Finset.range N, (if e ≤ s then k.multichoose (s - e) else 0) ≤
      ∑ s ∈ Finset.range N, k.multichoose s := by
  induction N with
  | zero =>
    have : I ⊔ m ^ 0 = ⊤ := by rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
    rw [this]
    have : Subsingleton (Poly n ⧸ (⊤ : Ideal (Poly n))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    simp [Module.finrank_zero_of_subsingleton]
  | succ N ih =>
    have := hfin N
    have := jet_step I m u hu hspan hFe hFe0 hrel N
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    omega

theorem multichoose_mono {k : ℕ} (hk : 1 ≤ k) {s N : ℕ} (h : s ≤ N) :
    k.multichoose s ≤ k.multichoose N := by
  rw [Nat.multichoose_eq, Nat.multichoose_eq]
  rw [Nat.choose_symm_of_eq_add (show k + s - 1 = s + (k - 1) by omega),
    Nat.choose_symm_of_eq_add (show k + N - 1 = N + (k - 1) by omega)]
  exact Nat.choose_le_choose _ (by omega)

/-- The tail bound: all but `e` consecutive multichoose terms cancel. -/
theorem jet_tail_bound {k : ℕ} (hk : 1 ≤ k) (e N : ℕ) :
    ∑ s ∈ Finset.range N, k.multichoose s ≤
      ∑ s ∈ Finset.range N, (if e ≤ s then k.multichoose (s - e) else 0) +
        e * k.multichoose N := by
  by_cases hNe : e ≤ N
  · have hsplit := Finset.sum_range_add_sum_Ico (fun s => k.multichoose s) (show N - e ≤ N by omega)
    have hshift : ∑ s ∈ Finset.range N, (if e ≤ s then k.multichoose (s - e) else 0) =
        ∑ s ∈ Finset.range (N - e), k.multichoose s := by
      rw [← Finset.sum_range_add_sum_Ico _ hNe]
      rw [Finset.sum_eq_zero (fun s hs => by
        rw [if_neg]; exact Nat.not_le.mpr (Finset.mem_range.mp hs)), zero_add]
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [if_pos (by omega), show e + j - e = j by omega]
    have htail : ∑ s ∈ Finset.Ico (N - e) N, k.multichoose s ≤ e * k.multichoose N := by
      have := Finset.sum_le_card_nsmul (Finset.Ico (N - e) N) (fun s => k.multichoose s)
        (k.multichoose N) (fun s hs => multichoose_mono hk (Finset.mem_Ico.mp hs).2.le)
      simpa [Nat.card_Ico, show N - (N - e) = e by omega] using this
    rw [hshift]
    omega
  · have : ∑ s ∈ Finset.range N, k.multichoose s ≤ N * k.multichoose N := by
      have := Finset.sum_le_card_nsmul (Finset.range N) (fun s => k.multichoose s)
        (k.multichoose N) (fun s hs => multichoose_mono hk (Finset.mem_range.mp hs).le)
      simpa using this
    have h2 : N * k.multichoose N ≤ e * k.multichoose N :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem localHilbert_le_jet (V : AffineVariety n) (x : Point n) (hx : x ∈ V)
    (t : ℕ) :
    V.localHilbert x t ≤
      ((Module.finrank ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) : ℕ) : ℕ∞) := by
  classical
  have hle : V.ideal ≤ pointIdeal x := AffineVariety.ideal_le_pointIdeal_of_mem hx
  have hKsup : pointIdeal x ^ (t + 1) ≤ V.ideal ⊔ pointIdeal x ^ (t + 1) :=
    le_sup_right
  haveI hTSfin : Module.Finite ℂ
      ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t) :=
    OAI.QuarticPowerFree.totalSpace_finite t
  have hfinR : Module.Finite ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) := by
    have hsurj : Function.Surjective
        ((Ideal.Quotient.mkₐ ℂ (V.ideal ⊔ pointIdeal x ^ (t + 1))).toLinearMap.domRestrict
          (OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t)) := by
      intro y
      obtain ⟨gg, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨low, high, hgh, hlow_deg, hhigh_mem⟩ := AffineVariety.transDecomp x t gg
      have hlow_mem : low ∈ OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) t := by
        rwa [OAI.QuarticPowerFree.mem_totalSpace]
      have hsub : gg - low ∈ V.ideal ⊔ pointIdeal x ^ (t + 1) := by
        have h_eq : gg - low = high := by linear_combination hgh
        rw [h_eq]
        exact hKsup hhigh_mem
      refine ⟨⟨low, hlow_mem⟩, ?_⟩
      show (Ideal.Quotient.mkₐ ℂ (V.ideal ⊔ pointIdeal x ^ (t + 1))) low =
        Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) gg
      have : Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) low =
          Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) gg := by
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
        have h_neg : low - gg = -(gg - low) := by abel
        rw [h_neg]
        exact neg_mem hsub
      simpa using this
    exact Module.Finite.of_surjective _ hsurj
  let φ : Poly n →ₐ[ℂ] PointLocalRing x :=
    IsScalarTower.toAlgHom ℂ (Poly n) (PointLocalRing x)
  have hφK : ∀ a : Poly n, a ∈ V.ideal ⊔ pointIdeal x ^ (t + 1) →
      (Ideal.Quotient.mkₐ ℂ
        (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)) (φ a) = 0 := by
    intro a ha
    show Ideal.Quotient.mk (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
      (φ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let g : Poly n →ₐ[ℂ]
      (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    (Ideal.Quotient.mkₐ ℂ
      (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)).comp φ
  let F : (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) →ₐ[ℂ]
      (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    Ideal.Quotient.liftₐ (V.ideal ⊔ pointIdeal x ^ (t + 1)) g hφK
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (M := (pointIdeal x).primeCompl)
      (S := PointLocalRing x) s
    have hb_notmem : (b : Poly n) ∉ pointIdeal x := b.property
    have hunit : IsUnit
        (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) (b : Poly n)) :=
      AffineVariety.isUnit_quotient_of_not_mem_pointIdeal x
        (V.ideal ⊔ pointIdeal x ^ (t + 1)) t hKsup _ hb_notmem
    obtain ⟨u, hu⟩ := isUnit_iff_exists.mp hunit
    refine ⟨Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) a * u, ?_⟩
    have hFb : F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) (b : Poly n)) =
        g (b : Poly n) := rfl
    have hFa : F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) a) = g a :=
      rfl
    have hsu : Ideal.Quotient.mk
          (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) s *
        Ideal.Quotient.mk
          (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) (φ (b : Poly n)) =
        Ideal.Quotient.mk
          (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) (φ a) := by
      have hhab : s * φ (b : Poly n) = φ a := hab
      have := congrArg
        (Ideal.Quotient.mk
          (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)) hhab
      rwa [map_mul] at this
    have hFu : g (b : Poly n) * F u = 1 := by
      have h1 : F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1))
          (b : Poly n) * u) = 1 := by
        rw [hu.1]; simp
      rw [map_mul, hFb] at h1
      exact h1
    calc F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) a * u)
        = F (Ideal.Quotient.mk (V.ideal ⊔ pointIdeal x ^ (t + 1)) a) * F u :=
          map_mul _ _ _
      _ = g a * F u := by rw [hFa]
      _ = (Ideal.Quotient.mk _ s * g (b : Poly n)) * F u := by
            have : g a = Ideal.Quotient.mk _ s * g (b : Poly n) := by
              have h2 : g a = Ideal.Quotient.mk
                  (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) (φ a) :=
                rfl
              have h3 : g (b : Poly n) =
                  Ideal.Quotient.mk
                    (localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
                    (φ (b : Poly n)) := rfl
              rw [h2, h3, ← hsu]
            rw [this]
      _ = Ideal.Quotient.mk _ s * (g (b : Poly n) * F u) := by ring
      _ = Ideal.Quotient.mk _ s := by
            rw [hFu, mul_one]
  haveI := hfinR
  have hfinS : Module.Finite ℂ
      (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    Module.Finite.of_surjective F.toLinearMap hFsurj
  haveI := hfinS
  have h_unfold : V.localHilbert x t =
      Module.length (PointLocalRing x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    rfl
  have h_alg_surj : Function.Surjective
      (algebraMap (PointLocalRing x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)) := by
    simpa only [Ideal.Quotient.algebraMap_eq] using
      (Ideal.Quotient.mk_surjective
        (I := localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x))
  have h_len_eq : Module.length (PointLocalRing x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) =
      Module.length
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
    Module.length_eq_of_surjective h_alg_surj
  have h_le : Module.length
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) ≤
      Module.length ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) := by
    have h0 := Submodule.length_le_length_restrictScalars (ℂ)
      (⊤ : Submodule
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x))
    rwa [Module.length_top, Submodule.restrictScalars_top, Module.length_top] at h0
  have h_fin_eq : Module.length ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) =
      ((Module.finrank ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :
        ℕ) : ℕ∞) :=
    Module.length_eq_finrank ℂ _
  have h_loc_le_fin : V.localHilbert x t ≤
      ((Module.finrank ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :
        ℕ) : ℕ∞) := by
    calc V.localHilbert x t
        = Module.length (PointLocalRing x)
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
            h_unfold
      _ = Module.length
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x)
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
            h_len_eq
      _ ≤ Module.length ℂ
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :=
            h_le
      _ = ((Module.finrank ℂ
          (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :
          ℕ) : ℕ∞) := h_fin_eq
  have h_fin_le : Module.finrank ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) ≤
      Module.finrank ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) :=
    AffineVariety.locQuotient_finrank_le V x hle t
  calc V.localHilbert x t
      ≤ ((Module.finrank ℂ
        (PointLocalRing x ⧸ localizedIdeal (V.ideal ⊔ pointIdeal x ^ (t + 1)) x) :
        ℕ) : ℕ∞) := h_loc_le_fin
    _ ≤ ((Module.finrank ℂ (Poly n ⧸ (V.ideal ⊔ pointIdeal x ^ (t + 1))) : ℕ) :
        ℕ∞) := by exact_mod_cast h_fin_le

/-- sc:outer-lift.source-jets . If the Jacobian kernel of
`E` at a common zero `w₀` has rank `≤ k`, then the jets of `E` at `w₀` have
dimension `≤ C(t+k, k)`. Proof: `jet_cotangent_coordinates` (with
`S = E`, `I = span E`, `k' = finrank jacKer ≤ k`) gives `k'` coordinates
`u_a = X_{j a} - w₀_{j a}` with `m ≤ span u + span E + m²`; by induction
`m^s ≤ (monomials of degree s in u) + span E + m^{s+1}`, so the quotient by
`span E + m^{t+1}` is spanned by the monomials in `u` of degree `≤ t`, of
number `C(t+k', k') ≤ C(t+k, k)`. -/
theorem jet_source_upper (E : Finset (Poly n)) (w₀ : Point n)
    (hE : ∀ e ∈ E, eval w₀ e = 0) (k : ℕ)
    (hk : Module.finrank ℂ (TrackD.jacKer E w₀) ≤ k) (t : ℕ) :
    Module.finrank ℂ (Poly n ⧸ (Ideal.span (E : Set (Poly n)) ⊔ pointIdeal w₀ ^ (t+1))) ≤
      (t + k).choose k := by
  set I : Ideal (Poly n) := Ideal.span (↑E : Set (Poly n)) with hIdef
  set m : Ideal (Poly n) := pointIdeal w₀ with hmdef
  set k' : ℕ := Module.finrank ℂ (TrackD.jacKer E w₀) with hk'def
  have hkle : k' ≤ k := hk
  have hTS : (⨅ f ∈ (↑E : Set (Poly n)), LinearMap.ker (differential f w₀)) =
      TrackD.jacKer E w₀ := by
    unfold TrackD.jacKer
    rfl
  have hI : I ≤ m := by
    rw [hIdef, Ideal.span_le]
    intro e he
    have heE : e ∈ E := Finset.mem_coe.mp he
    have he0 : eval w₀ e = 0 := hE e heE
    change e ∈ MvPolynomial.vanishingIdeal ℂ ({w₀} : Set (Point n))
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact he0
  obtain ⟨j, hj⟩ := jet_cotangent_coordinates I w₀ hI (↑E : Set (Poly n))
    Ideal.subset_span k' (by rw [hTS])
  set u : Fin k' → Poly n := fun a => X (j a) - C (w₀ (j a)) with hu_def
  have hmem_m : ∀ f : Poly n, eval w₀ f = 0 → f ∈ m := by
    intro f hf
    change f ∈ MvPolynomial.vanishingIdeal ℂ ({w₀} : Set (Point n))
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hf
  have hu : ∀ a, u a ∈ m := fun a => hmem_m _ (by simp [u])
  have hm0 : ∀ x : Poly n, x ∈ homogImage u 0 ⊔ m.restrictScalars ℂ := by
    intro x
    have h1 : C (eval w₀ x) ∈ homogImage u 0 :=
      Submodule.mem_map.mpr ⟨C (eval w₀ x), (mem_homogeneousSubmodule _ _).mpr
        (isHomogeneous_C _ _), by simp⟩
    have h2 : x - C (eval w₀ x) ∈ m := hmem_m _ (by simp)
    rw [show x = C (eval w₀ x) + (x - C (eval w₀ x)) by ring]
    exact Submodule.add_mem_sup h1 h2
  have hspanu : Submodule.span ℂ (Set.range u) ≤ homogImage u 1 := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.mem_map.mpr ⟨X a, (mem_homogeneousSubmodule _ _).mpr
      (isHomogeneous_X _ _), by simp⟩
  have hlin : ∀ i : Fin n, X i - C (w₀ i) ∈
      homogImage u 1 ⊔ (I ⊔ m ^ 2).restrictScalars ℂ := fun i =>
    (sup_le_sup_right hspanu _) (hj i)
  have hm1 : ∀ x ∈ m, x ∈ homogImage u 1 ⊔ (I ⊔ m ^ 2).restrictScalars ℂ := by
    intro x hx
    have hx0 : aeval w₀ x = 0 := by
      have : eval w₀ x = 0 := by
        have := (MvPolynomial.mem_vanishingIdeal_singleton_iff w₀ x).mp hx
        exact this
      simpa [MvPolynomial.aeval_eq_eval] using this
    have hrem := TrackA.tangent_first_order_remainder x w₀
    rw [hx0, map_zero, sub_zero] at hrem
    have hTLP : TrackA.tangentLinearPart x w₀ ∈
        homogImage u 1 ⊔ (I ⊔ m ^ 2).restrictScalars ℂ := by
      unfold TrackA.tangentLinearPart
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rw [MvPolynomial.C_mul']
      exact Submodule.smul_mem _ _ (hlin i)
    rw [show x = TrackA.tangentLinearPart x w₀ + (x - TrackA.tangentLinearPart x w₀) by ring]
    refine add_mem hTLP (Submodule.mem_sup_right ?_)
    exact Ideal.mem_sup_right hrem
  have hspan := pow_le_homogImage_sup I m u hu hm0 hm1
  -- graded upper count by induction on the power of `m`
  have hfinAll : ∀ N, Module.Finite ℂ (Poly n ⧸ (I ⊔ m ^ (N + 1))) :=
    fun N => jet_quot_finite I w₀ N
  have hcount : ∀ N, Module.finrank ℂ (Poly n ⧸ (I ⊔ m ^ N)) ≤
      ∑ s ∈ Finset.range N, k'.multichoose s := by
    intro N
    induction N with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
      have : Subsingleton (Poly n ⧸ (⊤ : Ideal (Poly n))) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
      simp [Module.finrank_zero_of_subsingleton]
    | succ N ih =>
      haveI := hfinAll (N + 1)
      have hAB : I ⊔ m ^ (N + 1) ≤ I ⊔ m ^ N :=
        sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) I
      have hBW : ∀ z ∈ I ⊔ m ^ N, ∃ w ∈ homogImage u N, z - w ∈ I ⊔ m ^ (N + 1) := by
        intro z hz
        obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
        obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp (hspan N y hy)
        refine ⟨w, hw, ?_⟩
        have heq : i + (w + c) - w = i + c := by ring
        rw [heq]
        exact (I ⊔ m ^ (N + 1)).add_mem (Ideal.mem_sup_left hi) hc
      have hstep := finrank_quot_le_of_sup (I ⊔ m ^ (N + 1)) (I ⊔ m ^ N) hAB
        (homogImage u N) hBW
      have hW : Module.finrank ℂ ((homogImage u N).map
          (Ideal.Quotient.mkₐ ℂ (I ⊔ m ^ (N + 1))).toLinearMap) ≤ k'.multichoose N := by
        set g : MvPolynomial (Fin k') ℂ →ₗ[ℂ] Poly n ⧸ (I ⊔ m ^ (N + 1)) :=
          (Ideal.Quotient.mkₐ ℂ (I ⊔ m ^ (N + 1))).toLinearMap ∘ₗ
            (aeval u).toLinearMap with hg
        have hmapeq : (homogImage u N).map
            (Ideal.Quotient.mkₐ ℂ (I ⊔ m ^ (N + 1))).toLinearMap =
            LinearMap.range (g.domRestrict (homogeneousSubmodule (Fin k') ℂ N)) := by
          rw [LinearMap.range_domRestrict, hg, Submodule.map_comp]
          rfl
        haveI : Module.Finite ℂ (homogeneousSubmodule (Fin k') ℂ N) :=
          Module.Finite.equiv (OAI.Lech.Grading.homogeneousEquiv ℂ k' N).symm
        calc Module.finrank ℂ ((homogImage u N).map
                (Ideal.Quotient.mkₐ ℂ (I ⊔ m ^ (N + 1))).toLinearMap)
            = Module.finrank ℂ (LinearMap.range (g.domRestrict
              (homogeneousSubmodule (Fin k') ℂ N))) := by rw [hmapeq]
          _ ≤ Module.finrank ℂ (homogeneousSubmodule (Fin k') ℂ N) :=
            LinearMap.finrank_range_le _
          _ = k'.multichoose N := finrank_homogeneousSubmodule _ _
      rw [Finset.sum_range_succ]
      omega
  -- the multichoose sum is `(t + k').choose k'`
  have hsum : ∑ s ∈ Finset.range (t + 1), k'.multichoose s = (t + k').choose k' := by
    rcases Nat.eq_zero_or_pos k' with hk'0 | hk'pos
    · rw [hk'0]
      have h0 : ∀ s ∈ Finset.range (t + 1),
          Nat.multichoose 0 s = (if s = 0 then 1 else 0) := by
        intro s _
        by_cases hs : s = 0
        · subst hs
          simp [Nat.multichoose_eq]
        · rw [if_neg hs]
          obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
          exact Nat.multichoose_zero_succ s
      rw [Finset.sum_congr rfl h0, Finset.sum_ite_eq']
      simp
    · calc ∑ s ∈ Finset.range (t + 1), Nat.multichoose k' s
          = ∑ i ∈ Finset.range (t + 1), (i + (k' - 1)).choose (k' - 1) := by
            apply Finset.sum_congr rfl
            intro s _
            rw [Nat.multichoose_eq, show k' + s - 1 = s + (k' - 1) by omega]
            exact Nat.choose_symm_of_eq_add rfl
        _ = (t + (k' - 1) + 1).choose ((k' - 1) + 1) :=
          Nat.sum_range_add_choose t (k' - 1)
        _ = (t + k').choose k' := by congr 1 <;> omega
  refine (hsum ▸ hcount (t + 1)).trans ?_
  have e1 : (t + k').choose k' = (t + k').choose t :=
    Nat.choose_symm_of_eq_add (by omega)
  have e2 : (t + k).choose k = (t + k).choose t :=
    Nat.choose_symm_of_eq_add (by omega)
  rw [e1, e2]
  exact Nat.choose_le_choose t (by omega)

/-- sc:outer-lift.smooth-jets .
At a point of an irreducible variety whose Zariski tangent space has the
dimension of the variety, the jets have at least the dimension of the jets of
affine `k`-space. Proof: choose `k` cotangent coordinates `u`
(`jet_cotangent_coordinates`); the map `ℂ[u]/(u)^{t+1} → ℂ[y]/(I + m^{t+1})`
is injective, since the lowest form `F_e` of a kernel element satisfies
`F_e(u) ∈ I + m^{e+1}`, whence the graded pieces `(I + m^s)/(I + m^{s+1})` have
dimension `≤ #mon_s - #mon_{s-e}` and the local Hilbert function would be
`O(t^{k-1})`, contradicting `localDimension_eq_dimension`. -/
theorem jet_smooth_lower (Y : AffineVariety n) (hY : Y.IsIrreducible)
    (q : Point n) (hq : q ∈ Y.points)
    (hT : Module.finrank ℂ (Y.tangentSpace q) = Y.dimension) (t : ℕ) :
    (t + Y.dimension).choose Y.dimension ≤
      Module.finrank ℂ (Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) := by
  set k := Y.dimension with hk
  set m := pointIdeal q with hm
  have hI : Y.ideal ≤ m := AffineVariety.ideal_le_pointIdeal_of_mem hq
  have hfinAll : ∀ s, Module.Finite ℂ (Poly n ⧸ (Y.ideal ⊔ m ^ (s+1))) :=
    fun s => jet_quot_finite Y.ideal q s
  have hfin := hfinAll t
  -- `k = 0`: the jets are a nonzero algebra
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, Nat.choose_zero_right]
    have hne : Y.ideal ⊔ m ^ (t+1) ≠ ⊤ := by
      intro htop
      have : Y.ideal ⊔ m ^ (t+1) ≤ m := sup_le hI (Ideal.pow_le_self (by omega))
      exact (pointIdeal_isMaximal q).ne_top (top_unique (htop ▸ this))
    have : Nontrivial (Poly n ⧸ (Y.ideal ⊔ m ^ (t+1))) := Ideal.Quotient.nontrivial_iff.mpr hne
    exact Module.finrank_pos
  -- cotangent coordinates
  have hTS : Module.finrank ℂ ((⨅ f ∈ (Y.ideal : Set (Poly n)),
      LinearMap.ker (differential f q) : Submodule ℂ (Point n))) = k := by
    rw [← hT]
    unfold AffineVariety.tangentSpace
    rw [iInf_subtype']
    rfl
  obtain ⟨j, hj⟩ := jet_cotangent_coordinates Y.ideal q hI (Y.ideal : Set (Poly n))
    subset_rfl k hTS
  set u : Fin k → Poly n := fun a => X (j a) - C (q (j a)) with hu_def
  have hmem_m : ∀ f : Poly n, eval q f = 0 → f ∈ m := by
    intro f hf
    change f ∈ MvPolynomial.vanishingIdeal ℂ ({q} : Set (Point n))
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hf
  have hu : ∀ a, u a ∈ m := fun a => hmem_m _ (by simp [u])
  have hm0 : ∀ x : Poly n, x ∈ homogImage u 0 ⊔ m.restrictScalars ℂ := by
    intro x
    have h1 : C (eval q x) ∈ homogImage u 0 :=
      Submodule.mem_map.mpr ⟨C (eval q x), (mem_homogeneousSubmodule _ _).mpr
        (isHomogeneous_C _ _), by simp⟩
    have h2 : x - C (eval q x) ∈ m := hmem_m _ (by simp)
    rw [show x = C (eval q x) + (x - C (eval q x)) by ring]
    exact Submodule.add_mem_sup h1 h2
  have hspanu : Submodule.span ℂ (Set.range u) ≤ homogImage u 1 := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.mem_map.mpr ⟨X a, (mem_homogeneousSubmodule _ _).mpr
      (isHomogeneous_X _ _), by simp⟩
  have hlin : ∀ i : Fin n, X i - C (q i) ∈
      homogImage u 1 ⊔ (Y.ideal ⊔ m ^ 2).restrictScalars ℂ := fun i =>
    (sup_le_sup_right hspanu _) (hj i)
  have hm1 : ∀ x ∈ m, x ∈ homogImage u 1 ⊔ (Y.ideal ⊔ m ^ 2).restrictScalars ℂ := by
    intro x hx
    have hx0 : aeval q x = 0 := by
      have : eval q x = 0 := by
        have := (MvPolynomial.mem_vanishingIdeal_singleton_iff q x).mp hx
        exact this
      simpa [MvPolynomial.aeval_eq_eval] using this
    have hrem := TrackA.tangent_first_order_remainder x q
    rw [hx0, map_zero, sub_zero] at hrem
    have hTLP : TrackA.tangentLinearPart x q ∈
        homogImage u 1 ⊔ (Y.ideal ⊔ m ^ 2).restrictScalars ℂ := by
      unfold TrackA.tangentLinearPart
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rw [MvPolynomial.C_mul']
      exact Submodule.smul_mem _ _ (hlin i)
    rw [show x = TrackA.tangentLinearPart x q + (x - TrackA.tangentLinearPart x q) by ring]
    refine add_mem hTLP (Submodule.mem_sup_right ?_)
    exact Ideal.mem_sup_right hrem
  have hspan := pow_le_homogImage_sup Y.ideal m u hu hm0 hm1
  -- the jet map from affine `k`-space
  set θ : MvPolynomial (Fin k) ℂ →ₐ[ℂ] Poly n := aeval u with hθ
  have hθvars : ∀ r : ℕ, ∀ F ∈ MvPolynomial.idealOfVars (Fin k) ℂ ^ r, θ F ∈ m ^ r := by
    intro r F hF
    have hmap : (MvPolynomial.idealOfVars (Fin k) ℂ).map θ ≤ m := by
      rw [MvPolynomial.idealOfVars, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      simpa [θ] using hu a
    have := Ideal.mem_map_of_mem θ hF
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hmap r this
  set ψ : MvPolynomial (Fin k) ℂ →ₐ[ℂ] Poly n ⧸ (Y.ideal ⊔ m ^ (t+1)) :=
    (Ideal.Quotient.mkₐ ℂ (Y.ideal ⊔ m ^ (t+1))).comp θ with hψ
  have hkerle : RingHom.ker ψ ≤ MvPolynomial.idealOfVars (Fin k) ℂ ^ (t+1) := by
    intro F hF
    by_contra hFnot
    rw [MvPolynomial.mem_pow_idealOfVars_iff'] at hFnot
    push Not at hFnot
    obtain ⟨d0, hd0, hcd0⟩ := hFnot
    have hex : ∃ e, homogeneousComponent e F ≠ 0 :=
      ⟨d0.degree, fun h => hcd0 (by
        have := congrArg (fun G : MvPolynomial (Fin k) ℂ => G.coeff d0) h
        simpa [coeff_homogeneousComponent] using this)⟩
    set e := Nat.find hex with he
    have hFe0 : homogeneousComponent e F ≠ 0 := Nat.find_spec hex
    have hemin : ∀ e' < e, homogeneousComponent e' F = 0 := fun e' he' => by
      by_contra h; exact Nat.find_min hex he' h
    have het : e ≤ t := by
      have : e ≤ d0.degree := Nat.find_min' hex (fun h => hcd0 (by
        have := congrArg (fun G : MvPolynomial (Fin k) ℂ => G.coeff d0) h
        simpa [coeff_homogeneousComponent] using this))
      omega
    have hhigh : F - homogeneousComponent e F ∈ MvPolynomial.idealOfVars (Fin k) ℂ ^ (e+1) := by
      rw [MvPolynomial.mem_pow_idealOfVars_iff']
      intro d hd
      rw [coeff_sub, coeff_homogeneousComponent]
      by_cases hde : d.degree = e
      · rw [if_pos hde, sub_self]
      · rw [if_neg hde, sub_zero]
        have hlt : d.degree < e := by omega
        have := congrArg (fun G : MvPolynomial (Fin k) ℂ => G.coeff d) (hemin _ hlt)
        simpa [coeff_homogeneousComponent] using this
    have hψF : θ F ∈ Y.ideal ⊔ m ^ (t+1) := by
      have : ψ F = 0 := hF
      rw [hψ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at this
      exact this
    have hrel : aeval u (homogeneousComponent e F) ∈ Y.ideal ⊔ m ^ (e+1) := by
      have h1 : θ F ∈ Y.ideal ⊔ m ^ (e+1) :=
        (sup_le_sup_left (Ideal.pow_le_pow_right (show e + 1 ≤ t + 1 by omega)) Y.ideal) hψF
      have h2 : θ (F - homogeneousComponent e F) ∈ Y.ideal ⊔ m ^ (e+1) :=
        Ideal.mem_sup_right (hθvars _ _ hhigh)
      have := (Y.ideal ⊔ m ^ (e+1)).sub_mem h1 h2
      rwa [map_sub, sub_sub_cancel] at this
    -- the jet count is `O(N^{k-1})`
    have hbound : ∀ N : ℕ, Module.finrank ℂ (Poly n ⧸ (Y.ideal ⊔ m ^ N)) ≤
        e * k.multichoose N := by
      intro N
      have h1 := jet_sum Y.ideal m u hu hspan (homogeneousComponent_isHomogeneous e F) hFe0
        hrel hfinAll N
      have h2 := jet_tail_bound hkpos e N
      omega
    have hlocal : ∀ t' : ℕ, (Y.localHilbert q t') ≤
        ((e * (t' + k) ^ (k - 1) : ℕ) : ℕ∞) := by
      intro t'
      refine (localHilbert_le_jet Y q hq t').trans ?_
      have h1 := hbound (t' + 1)
      have h2 : k.multichoose (t' + 1) ≤ (t' + k) ^ (k - 1) := by
        rw [Nat.multichoose_eq, Nat.choose_symm_of_eq_add
          (show k + (t' + 1) - 1 = (t' + 1) + (k - 1) by omega)]
        refine (Nat.choose_le_pow _ _).trans ?_
        exact Nat.pow_le_pow_left (by omega) _
      exact_mod_cast h1.trans (Nat.mul_le_mul_left _ h2)
    -- compare with the local Hilbert polynomial
    obtain ⟨_, N1, hP⟩ := (Y.localHilbert_eventually_polynomial q).choose_spec
    set P := Y.localHilbertPolynomial q with hPdef
    let Q : Polynomial ℚ := Polynomial.C (e : ℚ) * (Polynomial.X + Polynomial.C (k : ℚ)) ^ (k - 1)
    have hPnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ P.eval (T : ℚ) := by
      filter_upwards [Filter.eventually_atTop.mpr ⟨N1, fun t ht => hP t ht⟩] with t ht
      obtain ⟨a, _, heval⟩ := ht
      have heval' : P.eval (t : ℚ) = (a : ℚ) := heval
      rw [heval']
      positivity
    have hPle : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ) := by
      filter_upwards [Filter.eventually_atTop.mpr ⟨N1, fun t ht => hP t ht⟩] with t ht
      obtain ⟨a, ha, heval⟩ := ht
      have heval' : P.eval (t : ℚ) = (a : ℚ) := heval
      have h1 := hlocal t
      rw [ha] at h1
      have h2 : a ≤ e * (t + k) ^ (k - 1) := by exact_mod_cast h1
      rw [heval']
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X]
      exact_mod_cast h2
    have hdeg := OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds P Q hPnonneg hPle
    have hQdeg : Q.natDegree ≤ k - 1 := by
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      refine (Polynomial.natDegree_pow_le).trans ?_
      rw [Polynomial.natDegree_X_add_C, mul_one]
    have hloc : Y.localDimension q = k := AffineVariety.localDimension_eq_dimension Y q hY hq
    have : Y.localDimension q = P.natDegree := rfl
    omega
  have hker : RingHom.ker ψ = MvPolynomial.idealOfVars (Fin k) ℂ ^ (t+1) := by
    refine le_antisymm hkerle ?_
    intro F hF
    show ψ F = 0
    rw [hψ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (hθvars _ _ hF)
  have hinj := Ideal.kerLiftAlg_injective ψ
  have hle := LinearMap.finrank_le_finrank_of_injective (f := (Ideal.kerLiftAlg ψ).toLinearMap) hinj
  have heq : Module.finrank ℂ (MvPolynomial (Fin k) ℂ ⧸ RingHom.ker ψ) = (t + k).choose k := by
    rw [hker]
    exact TrackA.point_jet_quotient_finrank k t
  rw [heq] at hle
  exact hle


/-- A subalgebra of a `ℂ`-algebra with a nilpotent ideal `M` of codimension one
(every element is a constant modulo `M`) is everything once each generator of
`M` lies in it modulo `M²`. -/
theorem subalgebra_eq_top_of_cotangent {R : Type*} [CommRing R] [Algebra ℂ R]
    (S : Subalgebra ℂ R) (M : Ideal R) {ι : Type*} (g : ι → R)
    (hMg : M = Ideal.span (Set.range g))
    (hdec : ∀ r : R, ∃ c : ℂ, r - algebraMap ℂ R c ∈ M)
    (hg : ∀ i, ∃ s ∈ S, g i - s ∈ M ^ 2)
    (N : ℕ) (hN : M ^ N = ⊥) : S = ⊤ := by
  -- every element of `M` lies in `S` modulo `M²`
  have hM : ∀ m ∈ M, ∃ s ∈ S, m - s ∈ M ^ 2 := by
    intro m hm
    rw [hMg] at hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hg i
    | zero => exact ⟨0, S.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s₁, hs₁, h₁⟩ := hx
      obtain ⟨s₂, hs₂, h₂⟩ := hy
      refine ⟨s₁ + s₂, S.add_mem hs₁ hs₂, ?_⟩
      rw [show x + y - (s₁ + s₂) = (x - s₁) + (y - s₂) by ring]
      exact Ideal.add_mem _ h₁ h₂
    | smul a x hxM hx =>
      obtain ⟨s, hs, h⟩ := hx
      obtain ⟨c, hc⟩ := hdec a
      refine ⟨algebraMap ℂ R c * s, S.mul_mem (S.algebraMap_mem c) hs, ?_⟩
      have hxM' : x ∈ M := hMg ▸ hxM
      rw [show a • x - algebraMap ℂ R c * s =
          (a - algebraMap ℂ R c) * x + algebraMap ℂ R c * (x - s) by
        rw [smul_eq_mul]; ring]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ h)
      rw [pow_two]
      exact Ideal.mul_mem_mul hc hxM'
  -- `M^s ⊆ S + M^{s+1}`
  have hstep : ∀ s : ℕ, ∀ x ∈ M ^ s, ∃ y ∈ S, x - y ∈ M ^ (s + 1) := by
    intro s
    induction s with
    | zero =>
      intro x _
      obtain ⟨c, hc⟩ := hdec x
      exact ⟨algebraMap ℂ R c, S.algebraMap_mem c, by rwa [zero_add, pow_one]⟩
    | succ s ih =>
      intro x hx
      rw [pow_succ'] at hx
      refine Submodule.mul_induction_on
        (C := fun x => ∃ y ∈ S, x - y ∈ M ^ (s + 1 + 1)) hx ?_ ?_
      · intro m hm m' hm'
        obtain ⟨s₁, hs₁, h₁⟩ := hM m hm
        obtain ⟨s₂, hs₂, h₂⟩ := ih m' hm'
        refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, ?_⟩
        have hs₁M : s₁ ∈ M := by
          have h₁' : m - s₁ ∈ M := Ideal.pow_le_self two_ne_zero h₁
          rw [show s₁ = m - (m - s₁) by ring]
          exact Ideal.sub_mem _ hm h₁'
        rw [show m * m' - s₁ * s₂ = (m - s₁) * m' + s₁ * (m' - s₂) by ring]
        refine Ideal.add_mem _ ?_ ?_
        · rw [show s + 1 + 1 = 2 + s by ring, pow_add]
          exact Ideal.mul_mem_mul h₁ hm'
        · rw [show s + 1 + 1 = (s + 1) + 1 by rfl, pow_succ']
          exact Ideal.mul_mem_mul hs₁M h₂
      · intro x y hx hy
        obtain ⟨y₁, hy₁, h₁⟩ := hx
        obtain ⟨y₂, hy₂, h₂⟩ := hy
        refine ⟨y₁ + y₂, S.add_mem hy₁ hy₂, ?_⟩
        rw [show x + y - (y₁ + y₂) = (x - y₁) + (y - y₂) by ring]
        exact Ideal.add_mem _ h₁ h₂
  -- descending induction from `M^N = 0`
  have hdesc : ∀ d k : ℕ, k + d = N → ∀ x ∈ M ^ k, x ∈ S := by
    intro d
    induction d with
    | zero =>
      intro k hk x hx
      rw [add_zero] at hk
      rw [hk, hN, Ideal.mem_bot] at hx
      rw [hx]
      exact S.zero_mem
    | succ d ih =>
      intro k hk x hx
      obtain ⟨y, hy, hxy⟩ := hstep k x hx
      have := ih (k + 1) (by omega) (x - y) hxy
      rw [show x = (x - y) + y by ring]
      exact S.add_mem this hy
  rw [eq_top_iff]
  intro x _
  exact hdesc N 0 (zero_add N) x (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)

/-- sc:outer-lift.chart-jets-surjective . If `dφ_q` is
injective on `T_qY`, the chart label map is surjective on the jets of `Y` at
`q`. Proof: `jet_cotangent_coordinates` for `S = I(Y)` gives coordinates
spanning `m_q/(I + m_q²)`; each `e_j*|_T` is a combination of the
`(dφ_q)_b|_T` (these span `T*` by injectivity), and
`chartJetMap (w_b - w₀_b) ≡ (dφ_q)_b (y - q)` modulo `m_q²` (numerator
`(y_b - p_b) - w₀_b (y - p)_{i₀}` is linear and vanishes at `q`; the inverse
denominator is `δ(q)⁻¹` modulo `m_q`). Hence `m_q ≤ range + m_q²` in the jets,
`m_q^s ≤ range + m_q^{s+1}` by induction, and `m_q^{t+1} = 0` there. -/
theorem chartJetMap_surjective (Y : AffineVariety n) (q p : Point n) (i₀ : Fin n)
    (hq : (q - p) i₀ ≠ 0) (hqY : q ∈ Y.points)
    (h2 : ∀ v ∈ Y.tangentSpace q,
      TrackD.dirChartDeriv (LinearMap.proj i₀) (q - p) v = 0 → v = 0)
    (t : ℕ) :
    Function.Surjective (chartJetMap Y.ideal q p i₀ hq t) := by
  classical
  have hδ : eval q (X i₀ - C (p i₀)) ≠ 0 := by simpa using hq
  have hI : Y.ideal ≤ pointIdeal q := AffineVariety.ideal_le_pointIdeal_of_mem hqY
  set J : Ideal (Poly n) := Y.ideal ⊔ pointIdeal q ^ (t + 1) with hJ
  set φ := chartJetMap Y.ideal q p i₀ hq t with hφ
  set A := algebraMap ℂ (Poly n ⧸ J) with hA
  set M : Ideal (Poly n ⧸ J) := Ideal.map (Ideal.Quotient.mk J) (pointIdeal q) with hM
  set g : Fin n → Poly n ⧸ J := fun i => Ideal.Quotient.mk J (X i - C (q i)) with hg
  have hmkC : ∀ c : ℂ, Ideal.Quotient.mk J (C c) = A c := fun c => rfl
  have hmk_smul : ∀ (c : ℂ) (f : Poly n),
      Ideal.Quotient.mk J (c • f) = A c * Ideal.Quotient.mk J f := by
    intro c f
    rw [← MvPolynomial.C_mul', map_mul, hmkC]
  have hgM : ∀ i, g i ∈ M := by
    intro i
    refine Ideal.mem_map_of_mem _ ?_
    rw [TrackA.pointIdeal_span_coordinates]
    exact Ideal.subset_span ⟨i, rfl⟩
  -- the ideal generated by the coordinates, and its powers
  have hMg : M = Ideal.span (Set.range g) := by
    rw [hM, TrackA.pointIdeal_span_coordinates, Ideal.map_span, ← Set.range_comp]
    rfl
  have hdec : ∀ r : Poly n ⧸ J, ∃ c : ℂ, r - A c ∈ M := by
    intro r
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨eval q f, ?_⟩
    have hmem : f - C (eval q f) ∈ pointIdeal q := by
      change _ ∈ MvPolynomial.vanishingIdeal ℂ ({q} : Set (Point n))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    rw [← hmkC, ← map_sub]
    exact Ideal.mem_map_of_mem _ hmem
  have hN : M ^ (t + 1) = ⊥ := by
    rw [hM, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right
  have hsq : ∀ f ∈ Y.ideal ⊔ pointIdeal q ^ 2, Ideal.Quotient.mk J f ∈ M ^ 2 := by
    intro f hf
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hf
    rwa [Ideal.map_sup, Ideal.map_pow, ← hM,
      (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact le_sup_left),
      bot_sup_eq] at h
  -- the chart denominator
  set δ0 : ℂ := (q - p) i₀ with hδ0
  set u : Point n := q - p with hu
  set V := Ideal.Quotient.mk J (X i₀ - C (p i₀)) with hV
  set U := (jet_unit Y.ideal q t (X i₀ - C (p i₀)) hδ).unit with hU
  set W : Poly n ⧸ J := ((U⁻¹ : (Poly n ⧸ J)ˣ) : Poly n ⧸ J) with hW
  have hUV : (U : Poly n ⧸ J) = V := IsUnit.unit_spec _
  have hXb : ∀ b, Ideal.Quotient.mk J (X b - C (p b)) = g b + A (u b) := by
    intro b
    rw [hg, ← hmkC, ← map_add]
    congr 1
    simp only [hu, Pi.sub_apply, map_sub]
    ring
  have hWV : W * (A δ0 + g i₀) = 1 := by
    rw [add_comm, ← hXb i₀, ← hV, ← hUV, hW]
    exact Units.inv_mul U
  have hai : A δ0⁻¹ * A δ0 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have hφX : ∀ b, φ (X b) = (g b + A (u b)) * W := by
    intro b
    rw [hφ, chartJetMap, aeval_X, hXb]
  have hφC : ∀ c : ℂ, φ (C c) = A c := by
    intro c
    rw [hφ, chartJetMap, aeval_C]
  -- each coordinate lies in the image modulo `M²`
  have hgen : ∀ i, ∃ s ∈ φ.range, g i - s ∈ M ^ 2 := by
    intro i
    set T : Submodule ℂ (Point n) := Y.tangentSpace q with hT
    set D : Point n →ₗ[ℂ] Point n := TrackD.dirChartDeriv (LinearMap.proj i₀) u with hD
    let L : Fin n → Module.Dual ℂ T := fun b => (LinearMap.proj b ∘ₗ D).comp T.subtype
    have hker : (⨅ b, LinearMap.ker (L b)) ≤
        LinearMap.ker ((LinearMap.proj i : Point n →ₗ[ℂ] ℂ).comp T.subtype) := by
      intro v hv
      rw [Submodule.mem_iInf] at hv
      have hDv : D v = 0 := funext fun b => hv b
      have hv0 : (v : Point n) = 0 := h2 v v.2 hDv
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, hv0, map_zero]
    have hspan := FiniteDimensional.mem_span_of_iInf_ker_le_ker hker
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan
    -- the defect functional vanishes on the tangent space
    set ℓ : Point n →ₗ[ℂ] ℂ :=
      LinearMap.proj i - ∑ b, c b • (LinearMap.proj b ∘ₗ D) with hℓ
    have hℓT : (⨅ f : Y.ideal, LinearMap.ker (differential (f : Poly n) q)) ≤
        LinearMap.ker ℓ := by
      intro v hv
      have hvT : v ∈ T := hv
      have := congrArg (fun K : Module.Dual ℂ T => K ⟨v, hvT⟩) hc
      have hthis : (∑ b, c b * D v b) = v i := by
        simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, L,
          LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply,
          smul_eq_mul] using this
      rw [LinearMap.mem_ker, hℓ]
      simp only [LinearMap.sub_apply, LinearMap.coe_sum, Finset.sum_apply,
        LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]
      rw [hthis, sub_self]
    have hℓspan := FiniteDimensional.mem_span_of_iInf_ker_le_ker hℓT
    obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hℓspan
    have hlin : linPoly q ℓ ∈ Y.ideal ⊔ pointIdeal q ^ 2 := by
      have hlin' : linPoly q ℓ ∈ (Y.ideal ⊔ pointIdeal q ^ 2).restrictScalars ℂ := by
        rw [← hcf, map_finsuppSum]
        refine Submodule.finsuppSum_mem _ _ _ _ (fun f _ => ?_)
        rw [map_smul, linPoly_differential]
        refine Submodule.smul_mem _ _ ?_
        have hrem := TrackA.tangent_first_order_remainder (f : Poly n) q
        have hfx : aeval q (f : Poly n) = 0 := by
          have : (f : Poly n) ∈ pointIdeal q := hI f.2
          have h' : (f : Poly n) ∈ MvPolynomial.vanishingIdeal ℂ ({q} : Set (Point n)) := this
          rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at h'
          exact h'
        rw [hfx, map_zero, sub_zero] at hrem
        show TrackA.tangentLinearPart (f : Poly n) q ∈ Y.ideal ⊔ pointIdeal q ^ 2
        rw [show TrackA.tangentLinearPart (f : Poly n) q =
          (f : Poly n) - ((f : Poly n) - TrackA.tangentLinearPart (f : Poly n) q) by ring]
        exact (Y.ideal ⊔ pointIdeal q ^ 2).sub_mem (Ideal.mem_sup_left f.2)
          (Ideal.mem_sup_right hrem)
      exact hlin'
    -- the chart derivative in coordinates
    have hcomp : ∀ b, LinearMap.proj b ∘ₗ D =
        (δ0⁻¹ • LinearMap.proj b - ((δ0 ^ 2)⁻¹ * u b) • LinearMap.proj i₀ :
          Point n →ₗ[ℂ] ℂ) := by
      intro b
      ext v
      simp only [hD, TrackD.dirChartDeriv, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.smulRight_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hδ0, hu]
      ring
    have hlinimg : Ideal.Quotient.mk J (linPoly q ℓ) =
        g i - ∑ b, A (c b) * (A δ0⁻¹ * g b - A ((δ0 ^ 2)⁻¹ * u b) * g i₀) := by
      simp only [hℓ, map_sub, map_sum, map_smul, hcomp, linPoly_proj, hmk_smul, hg]
    -- the image element
    set G : Poly n := ∑ b, c b • (X b - C (u b * δ0⁻¹)) with hG
    have hφG : φ G = ∑ b, A (c b) * ((g b + A (u b)) * W - A (u b * δ0⁻¹)) := by
      rw [hG, map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [map_smul, map_sub, hφX, hφC, Algebra.smul_def]
    refine ⟨φ G, ⟨G, rfl⟩, ?_⟩
    -- each defect term lies in `M²`
    have hterm : ∀ b, (A δ0⁻¹ * g b - A ((δ0 ^ 2)⁻¹ * u b) * g i₀) -
        ((g b + A (u b)) * W - A (u b * δ0⁻¹)) ∈ M ^ 2 := by
      intro b
      have e1 : A ((δ0 ^ 2)⁻¹ * u b) = A δ0⁻¹ * A δ0⁻¹ * A (u b) := by
        rw [show (δ0 ^ 2)⁻¹ * u b = δ0⁻¹ * δ0⁻¹ * u b by ring, map_mul, map_mul]
      have e2 : A (u b * δ0⁻¹) = A (u b) * A δ0⁻¹ := map_mul _ _ _
      rw [e1, e2]
      have hdiff : A δ0⁻¹ - W = (A δ0⁻¹ * W) * g i₀ := by
        linear_combination (-(A δ0⁻¹)) * hWV + W * hai
      have hfac : (A δ0⁻¹ * g b - A δ0⁻¹ * A δ0⁻¹ * A (u b) * g i₀) -
          ((g b + A (u b)) * W - A (u b) * A δ0⁻¹) =
          (A δ0⁻¹ - W) * (g b - A (u b) * A δ0⁻¹ * g i₀) := by
        linear_combination (-(A (u b) * A δ0⁻¹)) * hWV + (A (u b) * W) * hai
      rw [hfac, pow_two]
      refine Ideal.mul_mem_mul ?_ ?_
      · rw [hdiff]
        exact Ideal.mul_mem_left _ _ (hgM i₀)
      · exact Ideal.sub_mem _ (hgM b) (Ideal.mul_mem_left _ _ (hgM i₀))
    have hsplit : g i - φ G = Ideal.Quotient.mk J (linPoly q ℓ) +
        ∑ b, A (c b) * ((A δ0⁻¹ * g b - A ((δ0 ^ 2)⁻¹ * u b) * g i₀) -
          ((g b + A (u b)) * W - A (u b * δ0⁻¹))) := by
      rw [hlinimg, hφG]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    refine Ideal.add_mem _ (hsq _ hlin) ?_
    exact Ideal.sum_mem _ (fun b _ => Ideal.mul_mem_left _ _ (hterm b))
  have htop := subalgebra_eq_top_of_cotangent φ.range M g hMg hdec hgen (t + 1) hN
  exact (AlgHom.range_eq_top φ).mp htop

/-- sc:outer-lift.chart-jets-clear . The jet image of `f`
times the `deg f`-th power of the denominator is the cleared pullback. Proof:
`f = ∑_j f_j` (homogeneous components), `chartJetMap f_j = u^{-j}·[f_j(y - p)]`
for `u = [(y - p)_{i₀}]` by homogeneity; multiply by `u^{deg f}`. -/
theorem chartJetMap_mul_clear (I : Ideal (Poly n)) (q p : Point n) (i₀ : Fin n)
    (hq : (q - p) i₀ ≠ 0) (t : ℕ) (f : Poly n) :
    chartJetMap I q p i₀ hq t f *
        Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) ^ f.totalDegree =
      Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (chartClear p i₀ f) := by
  have hδ : eval q (X i₀ - C (p i₀)) ≠ 0 := by simpa using hq
  set U := (jet_unit I q t (X i₀ - C (p i₀)) hδ).unit with hUdef
  have hφ : ∀ g : Poly n, chartJetMap I q p i₀ hq t g =
      aeval (fun b => Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X b - C (p b)) *
        (↑U⁻¹ : Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1)))) g := by
    intro g
    unfold chartJetMap
    rw [← hUdef]
  have hC : ∀ c : ℂ, algebraMap ℂ (Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1))) c =
      Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (algebraMap ℂ (Poly n) c) := by
    intro c
    rfl
  have hprod : ∀ d : Fin n →₀ ℕ, ∀ jj : ℕ, d.degree = jj →
      d.prod (fun b e => (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X b - C (p b)) *
        (↑U⁻¹ : Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1)))) ^ e) =
        (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1))
          (d.prod (fun b e => (X b - C (p b)) ^ e))) *
          (↑U⁻¹ : Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1))) ^ jj := by
    intro d jj hdeg
    rw [Finsupp.prod_fintype _ _ fun b => pow_zero _,
      Finsupp.prod_fintype _ _ fun b => pow_zero _]
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hsum : (∑ b, d b) = jj := by
      rw [← Finsupp.degree_eq_sum]; exact hdeg
    rw [hsum]
    congr 1
    · rw [map_prod]
      apply Finset.prod_congr rfl
      intro b _
      exact (map_pow _ _ _).symm
  have hcomp : ∀ (g : Poly n) (jj : ℕ), g.IsHomogeneous jj →
      aeval (fun b => Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X b - C (p b)) *
        (↑U⁻¹ : Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1)))) g =
        Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (aeval (fun b => X b - C (p b)) g) *
          (↑U⁻¹ : Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1))) ^ jj := by
    intro g jj hg
    conv_lhs => rw [MvPolynomial.as_sum g]
    conv_rhs => rw [MvPolynomial.as_sum g]
    simp only [map_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have hdeg : d.degree = jj := by
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hd) (hg.coeff_eq_zero hne)
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, map_mul, ← hC,
      hprod d jj hdeg, mul_assoc]
  have huv : ∀ jj : ℕ, jj ≤ f.totalDegree →
      (↑U⁻¹ : Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1))) ^ jj *
        (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀))) ^ f.totalDegree =
        (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀))) ^ (f.totalDegree - jj) := by
    intro jj hle
    have h1 : (↑U⁻¹ : Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1))) *
        Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) = 1 :=
      Units.mul_inv _
    have h2 : (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀))) ^ f.totalDegree =
        (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀))) ^ (f.totalDegree - jj) *
          (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀))) ^ jj := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    calc (↑U⁻¹ : Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1))) ^ jj *
          (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀))) ^ f.totalDegree
        = (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀))) ^ (f.totalDegree - jj) *
          ((↑U⁻¹ : Poly n ⧸ (I ⊔ pointIdeal q ^ (t+1))) ^ jj *
            (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀))) ^ jj) := by
          rw [h2]; ring
      _ = (Ideal.Quotient.mk (I ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀))) ^ (f.totalDegree - jj) := by
          rw [← mul_pow, h1, one_pow, mul_one]
  rw [hφ]
  conv_lhs =>
    lhs
    rw [← MvPolynomial.sum_homogeneousComponent f, map_sum]
  rw [Finset.sum_mul]
  conv_rhs => rw [chartClear, map_sum]
  apply Finset.sum_congr rfl
  intro jj hjj
  have hle : jj ≤ f.totalDegree := by
    have := Finset.mem_range.mp hjj
    omega
  rw [hcomp _ jj (MvPolynomial.homogeneousComponent_isHomogeneous jj f), mul_assoc,
    huv jj hle, map_mul, map_pow, mul_comm]

/-- sc:outer-lift.chart-jets-kernel . The chart label map
kills the label equations vanishing on `φ(Y)` and the `(t+1)`-st power of the
point ideal of `w₀ = φ(q)`. Proof: for `e ∈ E`, `chartClear p i₀ e` vanishes on
`Y` off the chart hyperplane, so `(X_{i₀} - p_{i₀}) · chartClear e ∈ I(Y)`
(vanishing ideal), and `chartJetMap_mul_clear` with the unit denominator gives
`chartJetMap e = 0`; each `w_b - w₀_b` maps into `m_q` (numerator linear,
vanishing at `q`), so `(m_{w₀})^{t+1}` maps into `m_q^{t+1} = 0`. -/
theorem chartJetMap_kernel (Y : AffineVariety n) (q p : Point n) (i₀ : Fin n)
    (hq : (q - p) i₀ ≠ 0) (E : Finset (Poly n))
    (h1 : ∀ y ∈ Y.points, (y - p) i₀ ≠ 0 → ∀ e ∈ E,
      eval (((y - p) i₀)⁻¹ • (y - p)) e = 0)
    (t : ℕ) :
    Ideal.span (E : Set (Poly n)) ⊔ pointIdeal (((q - p) i₀)⁻¹ • (q - p)) ^ (t+1) ≤
      RingHom.ker (chartJetMap Y.ideal q p i₀ hq t) := by
  set w₀ : Point n := ((q - p) i₀)⁻¹ • (q - p) with hw₀
  have hδ : eval q (X i₀ - C (p i₀)) ≠ 0 := by simpa using hq
  set U := (jet_unit Y.ideal q t (X i₀ - C (p i₀)) hδ).unit with hUdef
  have hφ : ∀ g : Poly n, chartJetMap Y.ideal q p i₀ hq t g =
      aeval (fun b => Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X b - C (p b)) *
        (↑U⁻¹ : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1)))) g := by
    intro g
    unfold chartJetMap
    rw [← hUdef]
  rw [sup_le_iff]
  constructor
  · -- The equation part: each `e ∈ E` maps to zero.
    rw [Ideal.span_le]
    intro e he
    have heE : e ∈ E := Finset.mem_coe.mp he
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have hvan : (X i₀ - C (p i₀)) * chartClear p i₀ e ∈ Y.ideal := by
      rw [← AffineVariety.vanishingIdeal_points, MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      have hδy : eval y (X i₀ - C (p i₀)) = (y - p) i₀ := by simp [Pi.sub_apply]
      rw [map_mul]
      simp only [MvPolynomial.aeval_eq_eval]
      rw [hδy]
      by_cases h0 : (y - p) i₀ = 0
      · rw [h0, zero_mul]
      · rw [chartClear_eval p i₀ e y h0, h1 y hy h0 e heE, mul_zero, mul_zero]
    have hQ0 : Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) *
        Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (chartClear p i₀ e) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_left hvan
    have hUval : ((U : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1)))) =
        Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) := by
      rw [hUdef]
      exact IsUnit.unit_spec _
    have hchart0 : Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))
        (chartClear p i₀ e) = 0 := by
      have h2 : (↑U : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) *
          Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (chartClear p i₀ e) = 0 := by
        rw [hUval]; exact hQ0
      have hfin := congrArg (· * (↑U⁻¹ : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1)))) h2
      simpa using hfin
    have h206 := chartJetMap_mul_clear Y.ideal q p i₀ hq t e
    rw [hchart0, ← hUval, ← Units.val_pow_eq_pow_val] at h206
    have h1U : ((↑(U ^ e.totalDegree) : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1)))) *
        ((↑((U ^ e.totalDegree)⁻¹) : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1)))) = 1 :=
      Units.mul_inv _
    calc chartJetMap Y.ideal q p i₀ hq t e
        = chartJetMap Y.ideal q p i₀ hq t e *
          ((↑(U ^ e.totalDegree) : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) *
            (↑((U ^ e.totalDegree)⁻¹) : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1)))) := by
          rw [h1U, mul_one]
      _ = (chartJetMap Y.ideal q p i₀ hq t e * (↑(U ^ e.totalDegree) : Poly n ⧸ _)) *
          (↑((U ^ e.totalDegree)⁻¹) : Poly n ⧸ _) := by
          rw [mul_assoc]
      _ = 0 := by rw [h206, zero_mul]
  · -- The point-power part.
    -- Abbreviations used only inside proofs below (goal stays explicit).
    have hCQ : ∀ c : ℂ, Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (C c) =
        algebraMap ℂ (Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) c := fun c => rfl
    have hUval : ((U : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1)))) =
        Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) := by
      rw [hUdef]
      exact IsUnit.unit_spec _
    -- The denominator error and the chart error both land in the maximal ideal image.
    have hm1' : Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) -
        algebraMap ℂ (Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) ((q - p) i₀) ∈
        Ideal.map (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))) (pointIdeal q) := by
      have hmem : (X i₀ - C (p i₀)) - C ((q - p) i₀) ∈ pointIdeal q := by
        change _ ∈ MvPolynomial.vanishingIdeal ℂ ({q} : Set (Point n))
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simp [Pi.sub_apply]
      have h2 := Ideal.mem_map_of_mem
        (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))) hmem
      rwa [map_sub, hCQ] at h2
    have he : (↑U⁻¹ : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) -
        algebraMap ℂ (Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) (((q - p) i₀)⁻¹) ∈
        Ideal.map (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))) (pointIdeal q) := by
      have heU : ((↑U⁻¹ : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) -
          algebraMap ℂ _ (((q - p) i₀)⁻¹)) * (↑U : Poly n ⧸ _) ∈
          Ideal.map (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))) (pointIdeal q) := by
        have hexpand : ((↑U⁻¹ : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) -
            algebraMap ℂ _ (((q - p) i₀)⁻¹)) * (↑U : Poly n ⧸ _) =
            1 - algebraMap ℂ _ (((q - p) i₀)⁻¹) *
              Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) := by
          rw [sub_mul, Units.inv_mul, hUval]
        rw [hexpand]
        have h3 : algebraMap ℂ (Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) (((q - p) i₀)⁻¹) *
            (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) -
              algebraMap ℂ _ ((q - p) i₀)) ∈
            Ideal.map (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))) (pointIdeal q) :=
          Ideal.mul_mem_left _ _ hm1'
        have hdda : algebraMap ℂ (Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) (((q - p) i₀)⁻¹) *
            algebraMap ℂ _ ((q - p) i₀) = 1 := by
          rw [← map_mul, inv_mul_cancel₀ hq, map_one]
        have h4 : (1 : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) -
            algebraMap ℂ _ (((q - p) i₀)⁻¹) *
              Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) =
            -(algebraMap ℂ _ (((q - p) i₀)⁻¹) *
              (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) -
                algebraMap ℂ _ ((q - p) i₀))) := by
          rw [mul_sub, hdda]
          ring
        rw [h4]
        exact neg_mem h3
      -- cancel the unit on the right: e = (e * U) * U⁻¹ ∈ M
      have hUinv : (↑U⁻¹ : Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) -
          algebraMap ℂ _ (((q - p) i₀)⁻¹) =
          ((↑U⁻¹ : Poly n ⧸ _) - algebraMap ℂ _ (((q - p) i₀)⁻¹)) *
            (↑U : Poly n ⧸ _) * (↑U⁻¹ : Poly n ⧸ _) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      rw [hUinv]
      exact Ideal.mul_mem_right _ _ heU
    -- generator images lie in the maximal ideal image
    have hgen : ∀ b : Fin n, chartJetMap Y.ideal q p i₀ hq t (X b - C (w₀ b)) ∈
        Ideal.map (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))) (pointIdeal q) := by
      intro b
      have hφb : chartJetMap Y.ideal q p i₀ hq t (X b - C (w₀ b)) =
          Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X b - C (p b)) * ↑U⁻¹ -
            algebraMap ℂ (Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) (w₀ b) := by
        rw [hφ, map_sub]
        simp only [MvPolynomial.aeval_X, MvPolynomial.aeval_C]
      have hw : w₀ b * (q - p) i₀ = q b - p b := by
        rw [hw₀, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
        calc ((q - p) i₀)⁻¹ * (q b - p b) * (q - p) i₀
            = (q b - p b) * (((q - p) i₀)⁻¹ * (q - p) i₀) := by ring
          _ = q b - p b := by rw [inv_mul_cancel₀ hq, mul_one]
      have hnum_mem : (X b - C (p b)) - C (w₀ b) * (X i₀ - C (p i₀)) ∈ pointIdeal q := by
        change _ ∈ MvPolynomial.vanishingIdeal ℂ ({q} : Set (Point n))
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
        have hw' : w₀ b * (q i₀ - p i₀) = q b - p b := by
          rwa [Pi.sub_apply] at hw
        simp [map_sub, map_mul, hw']
      have hWdQ : algebraMap ℂ (Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) (((q - p) i₀)⁻¹) *
          algebraMap ℂ _ (w₀ b) * algebraMap ℂ _ ((q - p) i₀) =
          algebraMap ℂ _ (w₀ b) := by
        rw [← map_mul, ← map_mul]
        congr 1
        calc ((q - p) i₀)⁻¹ * w₀ b * (q - p) i₀
            = w₀ b * (((q - p) i₀)⁻¹ * (q - p) i₀) := by ring
          _ = w₀ b := by rw [inv_mul_cancel₀ hq, mul_one]
      have hnum : Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))
          ((X b - C (p b)) - C (w₀ b) * (X i₀ - C (p i₀))) =
          Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X b - C (p b)) -
            algebraMap ℂ _ (w₀ b) *
              Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) := by
        rw [map_sub, map_mul, hCQ]
      have hdecomp : chartJetMap Y.ideal q p i₀ hq t (X b - C (w₀ b)) =
          algebraMap ℂ (Poly n ⧸ (Y.ideal ⊔ pointIdeal q ^ (t+1))) (((q - p) i₀)⁻¹) *
            Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))
              ((X b - C (p b)) - C (w₀ b) * (X i₀ - C (p i₀))) +
            Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X b - C (p b)) *
              (↑U⁻¹ - algebraMap ℂ _ (((q - p) i₀)⁻¹)) +
            algebraMap ℂ _ (((q - p) i₀)⁻¹) * algebraMap ℂ _ (w₀ b) *
              (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)) (X i₀ - C (p i₀)) -
                algebraMap ℂ _ ((q - p) i₀)) := by
        rw [hφb, hnum]
        linear_combination hWdQ
      rw [hdecomp]
      refine add_mem (add_mem ?_ ?_) ?_
      · exact Ideal.mul_mem_left _ _
          (Ideal.mem_map_of_mem
            (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))) hnum_mem)
      · exact Ideal.mul_mem_left _ _ he
      · exact Ideal.mul_mem_left _ _ hm1'
    -- the map comparison, then powers
    have hmap1 : Ideal.map (chartJetMap Y.ideal q p i₀ hq t) (pointIdeal w₀) ≤
        Ideal.map (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1))) (pointIdeal q) := by
      rw [Ideal.map_le_iff_le_comap, TrackA.pointIdeal_span_coordinates w₀, Ideal.span_le]
      intro x hx
      obtain ⟨b, rfl⟩ := hx
      rw [SetLike.mem_coe, Ideal.mem_comap]
      exact hgen b
    have hfin : Ideal.map (chartJetMap Y.ideal q p i₀ hq t) (pointIdeal w₀ ^ (t+1)) = ⊥ := by
      rw [Ideal.map_pow, eq_bot_iff]
      calc (Ideal.map (chartJetMap Y.ideal q p i₀ hq t) (pointIdeal w₀)) ^ (t + 1)
          ≤ (Ideal.map (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)))
              (pointIdeal q)) ^ (t + 1) :=
            pow_le_pow_left₀ bot_le hmap1 _
        _ = Ideal.map (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)))
              (pointIdeal q ^ (t + 1)) := by
            rw [← Ideal.map_pow]
        _ ≤ Ideal.map (Ideal.Quotient.mk (Y.ideal ⊔ pointIdeal q ^ (t+1)))
              (Y.ideal ⊔ pointIdeal q ^ (t + 1)) :=
            Ideal.map_mono le_sup_right
        _ = ⊥ := by
            rw [Ideal.map_eq_bot_iff_le_ker]
            intro z hz
            rw [RingHom.mem_ker]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
    intro y hy
    rw [RingHom.mem_ker]
    have hmem : (chartJetMap Y.ideal q p i₀ hq t) y ∈
        Ideal.map (chartJetMap Y.ideal q p i₀ hq t) (pointIdeal w₀ ^ (t+1)) :=
      Ideal.mem_map_of_mem _ hy
    rw [hfin] at hmem
    exact Ideal.mem_bot.mp hmem

/-- sc:outer-lift.jet-transfer .
Under the étale hypotheses (equations vanishing on `φ(Y)`, `dφ_q` injective on
`T_qY`, Jacobian kernel of the equations of rank `≤ dim Y`, `q` smooth on `Y`),
the jets of `Y` cut by the cleared pullback of any ideal `K ⊇ (E)` agree in
dimension with the jets of `K` at `w₀`. -/
theorem jet_transfer (Y : AffineVariety n) (hY : Y.IsIrreducible)
    (q : Point n) (hqY : q ∈ Y.points)
    (hT : Module.finrank ℂ (Y.tangentSpace q) = Y.dimension)
    (p : Point n) (i₀ : Fin n) (hq : (q - p) i₀ ≠ 0) (E : Finset (Poly n))
    (h1 : ∀ y ∈ Y.points, (y - p) i₀ ≠ 0 → ∀ e ∈ E,
      eval (((y - p) i₀)⁻¹ • (y - p)) e = 0)
    (h2 : ∀ v ∈ Y.tangentSpace q,
      TrackD.dirChartDeriv (LinearMap.proj i₀) (q - p) v = 0 → v = 0)
    (h3 : Module.finrank ℂ (TrackD.jacKer E (((q - p) i₀)⁻¹ • (q - p))) ≤ Y.dimension)
    (K : Ideal (Poly n)) (hK : Ideal.span (E : Set (Poly n)) ≤ K) (t : ℕ) :
    Module.finrank ℂ (Poly n ⧸ (Y.ideal ⊔ Ideal.span (chartClear p i₀ '' (K : Set (Poly n))) ⊔
        pointIdeal q ^ (t+1))) =
      Module.finrank ℂ (Poly n ⧸ (K ⊔ pointIdeal (((q - p) i₀)⁻¹ • (q - p)) ^ (t+1))) := by
  set w₀ : Point n := ((q - p) i₀)⁻¹ • (q - p) with hw₀
  set J : Ideal (Poly n) := Y.ideal ⊔ pointIdeal q ^ (t+1) with hJ
  set L : Ideal (Poly n) := Ideal.span (E : Set (Poly n)) ⊔ pointIdeal w₀ ^ (t+1) with hL
  have hsurj := chartJetMap_surjective Y q p i₀ hq hqY h2 t
  have hkerL : L ≤ RingHom.ker (chartJetMap Y.ideal q p i₀ hq t) :=
    chartJetMap_kernel Y q p i₀ hq E h1 t
  have hE0 : ∀ e ∈ E, eval w₀ e = 0 := fun e he => h1 q hqY hq e he
  have hsrc : Module.finrank ℂ (Poly n ⧸ L) ≤ (t + Y.dimension).choose Y.dimension :=
    jet_source_upper E w₀ hE0 Y.dimension h3 t
  have htgt : (t + Y.dimension).choose Y.dimension ≤ Module.finrank ℂ (Poly n ⧸ J) :=
    jet_smooth_lower Y hY q hqY hT t
  have hfinL : Module.Finite ℂ (Poly n ⧸ L) := jet_quot_finite _ w₀ t
  -- the kernel of the jet map is exactly `L`
  have hker : RingHom.ker (chartJetMap Y.ideal q p i₀ hq t) = L := by
    refine le_antisymm ?_ hkerL
    let φbar : (Poly n ⧸ L) →ₐ[ℂ] (Poly n ⧸ J) :=
      Ideal.Quotient.liftₐ L (chartJetMap Y.ideal q p i₀ hq t) (fun a ha => hkerL ha)
    have hbsurj : Function.Surjective φbar.toLinearMap := by
      intro y
      obtain ⟨a, rfl⟩ := hsurj y
      exact ⟨Ideal.Quotient.mk L a, rfl⟩
    have hrk := LinearMap.finrank_range_add_finrank_ker φbar.toLinearMap
    rw [LinearMap.range_eq_top.mpr hbsurj, finrank_top] at hrk
    have hk0 : Module.finrank ℂ (LinearMap.ker φbar.toLinearMap) = 0 := by omega
    have hkb : LinearMap.ker φbar.toLinearMap = ⊥ := Submodule.finrank_eq_zero.mp hk0
    intro a ha
    have h0 : φbar.toLinearMap (Ideal.Quotient.mk L a) = 0 := ha
    have hmem : Ideal.Quotient.mk L a ∈ LinearMap.ker φbar.toLinearMap := h0
    rw [hkb, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
    exact hmem
  -- the image of `K` is generated by the cleared pullbacks
  set C' : Set (Poly n) := chartClear p i₀ '' (K : Set (Poly n)) with hC'
  have hu : IsUnit (Ideal.Quotient.mk J (X i₀ - C (p i₀))) :=
    jet_unit Y.ideal q t (X i₀ - C (p i₀)) (by simpa using hq)
  have hmapK : K.map (chartJetMap Y.ideal q p i₀ hq t) = (Ideal.span C').map (Ideal.Quotient.mk J) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap]
      have hcl := chartJetMap_mul_clear Y.ideal q p i₀ hq t f
      have hmem : Ideal.Quotient.mk J (chartClear p i₀ f) ∈ (Ideal.span C').map (Ideal.Quotient.mk J) :=
        Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨f, hf, rfl⟩)
      rw [← hcl] at hmem
      exact (Ideal.mul_unit_mem_iff_mem _ (hu.pow _)).mp hmem
    · rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨g, ⟨f, hf, rfl⟩, rfl⟩
      rw [← chartJetMap_mul_clear Y.ideal q p i₀ hq t f]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hf)
  -- the composite onto the cut jets
  let π : Poly n →ₐ[ℂ] (Poly n ⧸ J) ⧸ K.map (chartJetMap Y.ideal q p i₀ hq t) :=
    (Ideal.Quotient.mkₐ ℂ _).comp (chartJetMap Y.ideal q p i₀ hq t)
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := hsurj z
    exact ⟨a, rfl⟩
  have hπker : RingHom.ker π = K ⊔ pointIdeal w₀ ^ (t+1) := by
    have h0 : RingHom.ker π =
        (K.map (chartJetMap Y.ideal q p i₀ hq t)).comap (chartJetMap Y.ideal q p i₀ hq t) := by
      ext a
      simp [π, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [h0, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, hker, hL]
    apply le_antisymm
    · exact sup_le le_sup_left (sup_le (hK.trans le_sup_left) le_sup_right)
    · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have e1 : (Poly n ⧸ (K ⊔ pointIdeal w₀ ^ (t+1))) ≃ₐ[ℂ]
      (Poly n ⧸ J) ⧸ K.map (chartJetMap Y.ideal q p i₀ hq t) :=
    (Ideal.quotientEquivAlgOfEq ℂ hπker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hπsurj)
  have e2 : ((Poly n ⧸ J) ⧸ K.map (chartJetMap Y.ideal q p i₀ hq t)) ≃ₐ[ℂ]
      Poly n ⧸ (Y.ideal ⊔ Ideal.span C' ⊔ pointIdeal q ^ (t+1)) := by
    refine (Ideal.quotientEquivAlgOfEq ℂ hmapK).trans
      ((DoubleQuot.quotQuotEquivQuotSupₐ ℂ J (Ideal.span C')).trans
        (Ideal.quotientEquivAlgOfEq ℂ ?_))
    rw [hJ, sup_assoc, sup_comm (pointIdeal q ^ (t+1)), ← sup_assoc]
  rw [← (e1.trans e2).toLinearEquiv.finrank_eq]

end
end DistinctDistances.SparseCones
