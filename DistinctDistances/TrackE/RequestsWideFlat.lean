import DistinctDistances.TrackD.Basic

/-! Track A input for the equal-dimensional flat weight budget.
Consumer: depth.tex:254–260; supplier: polynomial.tex degree conventions. -/
namespace DistinctDistances.Request
noncomputable section

open scoped BigOperators

private def affineForms {n m : ℕ} (a : Point n)
    (L : Point m →ₗ[ℂ] Point n) : Fin n → Poly m :=
  fun i => MvPolynomial.C (a i) +
    ∑ j : Fin m, MvPolynomial.C (L (Pi.single j (1 : ℂ)) i) * MvPolynomial.X j

private theorem affineForms_degree {n m : ℕ} (a : Point n)
    (L : Point m →ₗ[ℂ] Point n) (i : Fin n) :
    (affineForms a L i).totalDegree ≤ 1 := by
  unfold affineForms
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le_iff.mpr ⟨?_, ?_⟩)
  · simp
  · refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
    apply Finset.sup_le
    intro j _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    simp

private theorem totalDegree_aeval_linear_le {n m : ℕ} (L : Fin n → Poly m)
    (hL : ∀ i, (L i).totalDegree ≤ 1) (p : Poly n) :
    (MvPolynomial.aeval L p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p, map_sum]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  apply Finset.sup_le
  intro s hs
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  rw [MvPolynomial.aeval_monomial]
  calc (algebraMap ℂ (Poly m) (p.coeff s) * s.prod _).totalDegree
        ≤ (algebraMap ℂ (Poly m) (p.coeff s)).totalDegree +
          (s.prod fun i k => L i ^ k).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + s.sum (fun _ e => e) := by
          apply add_le_add _ _
          · have hC : algebraMap ℂ (Poly m) (p.coeff s) = MvPolynomial.C (p.coeff s) := by
              rw [MvPolynomial.algebraMap_eq]
            rw [hC, MvPolynomial.totalDegree_C]
          · calc (s.prod fun i k => L i ^ k).totalDegree
                  ≤ ∑ i ∈ s.support, ((L i ^ s i)).totalDegree :=
                    MvPolynomial.totalDegree_finsetProd _ _
                _ ≤ ∑ i ∈ s.support, s i := by
                    apply Finset.sum_le_sum
                    intro i _
                    calc ((L i ^ s i)).totalDegree ≤ s i * (L i).totalDegree :=
                              MvPolynomial.totalDegree_pow _ _
                        _ ≤ s i * 1 := mul_le_mul_of_nonneg_left (hL i) (Nat.zero_le _)
                        _ = s i := Nat.mul_one _
                _ = s.sum (fun _ e => e) := rfl
      _ = s.sum (fun _ e => e) := zero_add _

private theorem affineForms_eval {n m : ℕ} (a : Point n)
    (L : Point m →ₗ[ℂ] Point n) (t : Point m) (i : Fin n) :
    MvPolynomial.aeval t (affineForms a L i) = (a + L t) i := by
  have ht : t = ∑ j : Fin m, t j • (Pi.single j (1 : ℂ) : Point m) := by
    funext j
    simp [Pi.single_apply]
  have hLt : L t = ∑ j : Fin m, t j • L (Pi.single j (1 : ℂ)) := by
    calc
      L t = L (∑ j : Fin m, t j • (Pi.single j (1 : ℂ) : Point m)) := congrArg L ht
      _ = ∑ j : Fin m, L (t j • (Pi.single j (1 : ℂ) : Point m)) := map_sum _ _ _
      _ = ∑ j : Fin m, t j • L (Pi.single j (1 : ℂ)) := by simp
  have hLi : (L t) i = ∑ j : Fin m, t j * L (Pi.single j (1 : ℂ)) i := by
    rw [hLt]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [affineForms, map_add, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X]
  simp only [Pi.add_apply]
  rw [hLi]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [mul_comm]

/-- A nonempty irreducible affine flat has degree one in the shared model. -/
theorem affine_flat_degree_one {d : ℕ} (Z : AffineVariety d)
    (hZ : Z.IsIrreducible) (hflat : TrackD.IsFlat Z) : Z.degree = 1 := by
  classical
  rcases hflat with ⟨F, hZF⟩
  obtain ⟨x₀, hx₀⟩ := Z.points_nonempty_of_isIrreducible hZ
  have hFne : (F : Set (Point d)).Nonempty := ⟨x₀, by simpa [hZF] using hx₀⟩
  rcases hFne with ⟨a, ha⟩
  let V := F.direction
  let k := Module.finrank ℂ V
  let b := Module.finBasis ℂ V
  let e : Point k ≃ₗ[ℂ] V := b.equivFun.symm
  let φ : Point k →ₗ[ℂ] Point d := V.subtype.comp e.toLinearMap
  have hφinj : Function.Injective φ := V.subtype_injective.comp e.injective
  have hparam (x : Point d) : x ∈ F ↔ ∃ t : Point k, x = a + φ t := by
    constructor
    · intro hx
      have hxV : x - a ∈ V := by
        have h := (AffineSubspace.vsub_right_mem_direction_iff_mem ha x).2 hx
        simpa [vsub_eq_sub] using h
      let y : V := ⟨x - a, hxV⟩
      refine ⟨b.equivFun y, ?_⟩
      have hy : e (b.equivFun y) = y := by simp [e]
      change x = a + (e (b.equivFun y) : Point d)
      rw [hy]
      change x = a + (x - a)
      abel
    · rintro ⟨t, rfl⟩
      have hv : φ t ∈ V := (e t).property
      have hmem := AffineSubspace.vadd_mem_of_mem_direction hv ha
      simpa [vadd_eq_add, add_comm] using hmem
  let pull : Poly d →ₐ[ℂ] Poly k := MvPolynomial.aeval (affineForms a φ)
  have hpull_eval (t : Point k) (p : Poly d) :
      MvPolynomial.aeval t (pull p) = MvPolynomial.aeval (a + φ t) p := by
    change MvPolynomial.aeval t (MvPolynomial.aeval (affineForms a φ) p) = _
    rw [MvPolynomial.comp_aeval_apply]
    apply congrArg (fun z : Point d => MvPolynomial.aeval z p)
    funext i
    exact affineForms_eval a φ t i
  have hIdeal : Z.ideal = MvPolynomial.vanishingIdeal ℂ (F : Set (Point d)) := by
    calc
      Z.ideal = MvPolynomial.vanishingIdeal ℂ Z.points := Z.vanishingIdeal_points.symm
      _ = MvPolynomial.vanishingIdeal ℂ (F : Set (Point d)) := by rw [hZF]
  have hker : RingHom.ker pull.toRingHom = Z.ideal := by
    ext p
    rw [RingHom.mem_ker]
    change pull p = 0 ↔ p ∈ Z.ideal
    constructor
    · intro hp
      rw [hIdeal, MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      obtain ⟨t, rfl⟩ := (hparam x).mp hx
      have he := congrArg (MvPolynomial.aeval t) hp
      simpa only [hpull_eval, map_zero] using he
    · intro hp
      rw [hIdeal] at hp
      apply MvPolynomial.funext
      intro t
      change MvPolynomial.aeval t (pull p) = 0
      rw [hpull_eval]
      exact (MvPolynomial.mem_vanishingIdeal_iff.mp hp) (a + φ t) ((hparam _).2 ⟨t, rfl⟩)
  have hIle (p : Poly d) (hp : p ∈ Z.ideal) : pull p = 0 := by
    have hp' : p ∈ RingHom.ker pull.toRingHom := by rw [hker]; exact hp
    exact RingHom.mem_ker.mp hp'
  let q : (Poly d ⧸ Z.ideal) →ₐ[ℂ] Poly k := Ideal.Quotient.liftₐ Z.ideal pull hIle
  have hq_mk (p : Poly d) : q (Ideal.Quotient.mk Z.ideal p) = pull p := by
    change (q.comp (Ideal.Quotient.mkₐ ℂ Z.ideal)) p = pull p
    rw [Ideal.Quotient.liftₐ_comp]
  have hqinj : Function.Injective q := by
    intro x y hxy
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.mpr
    have hpr : pull p = pull r := by
      calc
        pull p = q (Ideal.Quotient.mk Z.ideal p) := (hq_mk p).symm
        _ = q (Ideal.Quotient.mk Z.ideal r) := hxy
        _ = pull r := hq_mk r
    have hpull : pull (p - r) = 0 := by rw [map_sub, sub_eq_zero.mpr hpr]
    have hmem : p - r ∈ RingHom.ker pull.toRingHom := RingHom.mem_ker.mpr hpull
    rw [hker] at hmem
    exact hmem
  let ρ : Point d →ₗ[ℂ] Point k := φ.leftInverse
  have hρφ (t : Point k) : ρ (φ t) = t := by
    exact DFunLike.congr_fun (LinearMap.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr hφinj)) t
  let expand : Poly k →ₐ[ℂ] Poly d := MvPolynomial.aeval (affineForms (-ρ a) ρ)
  have hexpand_eval (x : Point d) (p : Poly k) :
      MvPolynomial.aeval x (expand p) = MvPolynomial.aeval ((-ρ a) + ρ x) p := by
    change MvPolynomial.aeval x (MvPolynomial.aeval (affineForms (-ρ a) ρ) p) = _
    rw [MvPolynomial.comp_aeval_apply]
    apply congrArg (fun z : Point k => MvPolynomial.aeval z p)
    funext i
    exact affineForms_eval (-ρ a) ρ x i
  have hpull_expand (p : Poly k) : pull (expand p) = p := by
    apply MvPolynomial.funext
    intro t
    have hcoord : (-ρ a) + ρ (a + φ t) = t := by
      calc
        (-ρ a) + ρ (a + φ t) = (-ρ a) + (ρ a + ρ (φ t)) := by rw [map_add]
        _ = t := by rw [hρφ]; abel
    calc
      MvPolynomial.aeval t (pull (expand p)) =
          MvPolynomial.aeval (a + φ t) (expand p) := hpull_eval t (expand p)
      _ = MvPolynomial.aeval ((-ρ a) + ρ (a + φ t)) p := hexpand_eval (a + φ t) p
      _ = MvPolynomial.aeval t p := by rw [hcoord]
  have hHilbert (D : ℕ) : Z.hilbert D = (D + k).choose k := by
    let H : Submodule ℂ (Poly k) := OAI.QuarticPowerFree.totalSpace D
    let S : Submodule ℂ (Poly d ⧸ Z.ideal) := Z.restrictionSpace D
    letI := OAI.QuarticPowerFree.totalSpace_finite (n := k) (K := ℂ) D
    let upper : S →ₗ[ℂ] H :=
      { toFun := fun x => ⟨q.toLinearMap x.1, by
          rcases x.2 with ⟨p, hp, hpx⟩
          change q x.1 ∈ OAI.QuarticPowerFree.totalSpace D
          have hqrep : q x.1 = pull p := by
            calc
              q x.1 = q ((Ideal.Quotient.mkₐ ℂ Z.ideal).toLinearMap p) :=
                congrArg q hpx.symm
              _ = q (Ideal.Quotient.mk Z.ideal p) := rfl
              _ = pull p := hq_mk p
          rw [hqrep]
          exact OAI.QuarticPowerFree.mem_totalSpace.mpr
            ((totalDegree_aeval_linear_le (affineForms a φ)
              (fun i => affineForms_degree a φ i) p).trans
                (OAI.QuarticPowerFree.mem_totalSpace.mp hp))
        ⟩
        map_add' := by intro x y; apply Subtype.ext; simp
        map_smul' := by intro c x; apply Subtype.ext; simp }
    have hupper : Function.Injective upper := by
      intro x y hxy
      apply Subtype.ext
      apply hqinj
      exact congrArg Subtype.val hxy
    let lower : H →ₗ[ℂ] S :=
      { toFun := fun p => ⟨(Ideal.Quotient.mkₐ ℂ Z.ideal).toLinearMap (expand p.1), by
          refine Submodule.mem_map.mpr ⟨expand p.1, ?_, rfl⟩
          exact OAI.QuarticPowerFree.mem_totalSpace.mpr
            ((totalDegree_aeval_linear_le (affineForms (-ρ a) ρ)
              (fun i => affineForms_degree (-ρ a) ρ i) p.1).trans
                (OAI.QuarticPowerFree.mem_totalSpace.mp p.2))
        ⟩
        map_add' := by intro x y; apply Subtype.ext; simp [expand]
        map_smul' := by intro c x; apply Subtype.ext; simp [expand] }
    have hlower : Function.Injective lower := by
      intro x y hxy
      apply Subtype.ext
      have hclass : Ideal.Quotient.mk Z.ideal (expand x.1) =
          Ideal.Quotient.mk Z.ideal (expand y.1) := congrArg Subtype.val hxy
      have hpoly := congrArg q hclass
      rw [hq_mk, hq_mk, hpull_expand, hpull_expand] at hpoly
      exact hpoly
    have hrank : Module.finrank ℂ S = Module.finrank ℂ H :=
      Nat.le_antisymm
        (LinearMap.finrank_le_finrank_of_injective hupper)
        (LinearMap.finrank_le_finrank_of_injective hlower)
    rw [OAI.QuarticPowerFree.totalSpace_finrank] at hrank
    simpa [S, AffineVariety.hilbert] using hrank
  have hpoly : Z.hilbertPolynomial = Polynomial.preHilbertPoly ℚ k 0 := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [Z.hilbert_eventually] with D hD
    rw [← hD, hHilbert D]
    rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ k (Nat.zero_le (D + k))]
    simp only [Nat.sub_zero]
  change ((Z.hilbertPolynomial.natDegree).factorial : ℚ) *
    Z.hilbertPolynomial.coeff Z.hilbertPolynomial.natDegree = 1
  rw [hpoly, Polynomial.natDegree_preHilbertPoly, Polynomial.coeff_preHilbertPoly_self]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k)

end
end DistinctDistances.Request
