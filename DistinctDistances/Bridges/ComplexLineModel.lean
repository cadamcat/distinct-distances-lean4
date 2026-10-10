import DistinctDistances.Bridges.AffineLines

/-! The shared affine-variety model for a parametrized complex line. -/

namespace DistinctDistances.Bridges

noncomputable section

def complexLine {n : ℕ} (a v : Point n) : AffineVariety n where
  ideal := RingHom.ker (linePullback a v).toRingHom
  isRadical := (RingHom.ker_isPrime (linePullback a v).toRingHom).isRadical

theorem complexLine_irreducible {n : ℕ} (a v : Point n) :
    (complexLine a v).IsIrreducible :=
  RingHom.ker_isPrime (linePullback a v).toRingHom

theorem linePullback_section {n : ℕ} (a v : Point n) (j : Fin n) (hj : v j ≠ 0)
    (f : Poly 1) : linePullback a v (lineSection a v j f) = f :=
  DFunLike.congr_fun (linePullback_comp_section a v j hj) f

theorem complexLine_hilbert {n : ℕ} (a v : Point n) (j : Fin n) (hj : v j ≠ 0)
    (D : ℕ) : (complexLine a v).hilbert D = D + 1 := by
  let V := complexLine a v
  let H := MvPolynomial.restrictTotalDegree (Fin n) ℂ D
  let ev : H →ₗ[ℂ] Poly 1 := (linePullback a v).toLinearMap.comp H.subtype
  let q : H →ₗ[ℂ] (Poly n ⧸ V.ideal) :=
    (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap.comp H.subtype
  have hqrange : LinearMap.range q = V.restrictionSpace D := by
    ext z
    change (∃ f : H, q f = z) ↔ ∃ f,
      f ∈ OAI.QuarticPowerFree.totalSpace D ∧
        (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap f = z
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨f.val, OAI.QuarticPowerFree.mem_totalSpace.mpr ?_, rfl⟩
      exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mp f.property
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        (OAI.QuarticPowerFree.mem_totalSpace.mp hf)⟩, rfl⟩
  have herange : LinearMap.range ev = OAI.QuarticPowerFree.totalSpace D := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      apply OAI.QuarticPowerFree.mem_totalSpace.mpr
      exact (linePullback_degree_le a v g.val).trans
        ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp g.property)
    · intro hf
      let g : H := ⟨lineSection a v j f,
        (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
          ((lineSection_degree_le a v j f).trans
            (OAI.QuarticPowerFree.mem_totalSpace.mp hf))⟩
      exact ⟨g, linePullback_section a v j hj f⟩
  have hker : LinearMap.ker q = LinearMap.ker ev := by
    ext f
    change (Ideal.Quotient.mk V.ideal f.val = 0) ↔ linePullback a v f.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rfl
  have hq := q.finrank_range_add_finrank_ker
  have he := ev.finrank_range_add_finrank_ker
  rw [hker] at hq
  have hrank : Module.finrank ℂ (LinearMap.range q) =
      Module.finrank ℂ (LinearMap.range ev) := Nat.add_right_cancel (hq.trans he.symm)
  change Module.finrank ℂ (V.restrictionSpace D) = D + 1
  rw [← hqrange, hrank, herange]
  simpa only [Nat.choose_one_right] using
    OAI.QuarticPowerFree.totalSpace_finrank (n := 1) (K := ℂ) D

theorem complexLine_hilbertPolynomial {n : ℕ} (a v : Point n) (j : Fin n) (hj : v j ≠ 0) :
    (complexLine a v).hilbertPolynomial = Polynomial.X + 1 := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  filter_upwards [(complexLine a v).hilbert_eventually] with D hD
  rw [← hD, complexLine_hilbert a v j hj D]
  simp

theorem complexLine_dimension {n : ℕ} (a v : Point n) (j : Fin n) (hj : v j ≠ 0) :
    (complexLine a v).dimension = 1 := by
  change (complexLine a v).hilbertPolynomial.natDegree = 1
  rw [complexLine_hilbertPolynomial a v j hj]
  simp

theorem complexLine_degree {n : ℕ} (a v : Point n) (j : Fin n) (hj : v j ≠ 0) :
    (complexLine a v).degree = 1 := by
  change ((complexLine a v).dimension.factorial : ℚ) *
    (complexLine a v).hilbertPolynomial.coeff (complexLine a v).dimension = 1
  rw [complexLine_dimension a v j hj, complexLine_hilbertPolynomial a v j hj]
  simp [Polynomial.coeff_one]

theorem eval_linePullback {n : ℕ} (a v : Point n) (t : ℂ) (f : Poly n) :
    MvPolynomial.aeval (fun _ : Fin 1 => t) (linePullback a v f) =
      MvPolynomial.aeval (a + t • v) f := by
  rw [linePullback, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : Point n => MvPolynomial.aeval g f)
  funext i
  simp [Pi.smul_apply, smul_eq_mul, mul_comm]

theorem complexLine_points {n : ℕ} (a v : Point n) (j : Fin n) (hj : v j ≠ 0) :
    (complexLine a v).points = {z | ∃ t : ℂ, z = a + t • v} := by
  classical
  apply le_antisymm
  · intro z hz
    let t := (v j)⁻¹ * (z j - a j)
    refine ⟨t, ?_⟩
    funext i
    let f : Poly n := MvPolynomial.X i - MvPolynomial.C (a i) -
      MvPolynomial.C (v i) * lineSection a v j (MvPolynomial.X 0)
    have hf : f ∈ (complexLine a v).ideal := by
      change linePullback a v f = 0
      dsimp only [f]
      rw [map_sub, map_sub, map_mul, linePullback_section a v j hj]
      simp only [linePullback, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq]
      ring
    have hi : z i - a i - v i * t = 0 := by
      simpa [f, lineSection, t] using hz f hf
    calc
      z i = a i + v i * t := by linear_combination hi
      _ = (a + t • v) i := by simp [Pi.smul_apply, smul_eq_mul, mul_comm]
  · rintro z ⟨t, rfl⟩ f hf
    change linePullback a v f = 0 at hf
    have hzero := congrArg (MvPolynomial.aeval (fun _ : Fin 1 => t)) hf
    simpa only [eval_linePullback, map_zero] using hzero

theorem complexLine_points_infinite {n : ℕ} (a v : Point n) (j : Fin n) (hj : v j ≠ 0) :
    (complexLine a v).points.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℂ => a + t • v)
  · intro t s he
    have hcoord := congrArg (fun z : Point n => z j) he
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    exact mul_right_cancel₀ hj (add_left_cancel hcoord)
  · intro t
    rw [complexLine_points a v j hj]
    exact ⟨t, rfl⟩

end
end DistinctDistances.Bridges
