import DistinctDistances.TrackE.CommonLiftingData

/-! Page-sized graph and label-coordinate inputs,
sparse-cones.tex:158–178. The kernel and physical source remain literal. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

/-- Evaluation on the graph preserves every original source polynomial. -/
theorem common_reciprocal_tail {n : ℕ} (K : Type*) [Field K] [Algebra ℂ K]
    (φ : Poly n →ₐ[ℂ] K) (g q : Poly n) :
    commonReciprocalEvaluation K φ g (commonTailRename q) = φ q := by
  have hcomp : (commonReciprocalEvaluation K φ g).comp commonTailRename = φ := by
    apply MvPolynomial.algHom_ext
    intro i
    show MvPolynomial.aeval (Fin.cons (φ g)⁻¹ (fun j => φ (MvPolynomial.X j)))
      (MvPolynomial.rename Fin.succ (MvPolynomial.X i)) = φ (MvPolynomial.X i)
    rw [MvPolynomial.rename_X, MvPolynomial.aeval_X, Fin.cons_succ]
  exact AlgHom.congr_fun hcomp q

/-- The polynomial graph map is exactly the original rational field map. -/
theorem common_reciprocal_composition {n m : ℕ} (K : Type*) [Field K] [Algebra ℂ K]
    (φ : Poly n →ₐ[ℂ] K) (f : Fin m → Poly n) (g : Poly n) :
    (commonReciprocalEvaluation K φ g).comp (commonReciprocalLabelMap f) =
      TrackD.rationalFieldPullback K φ f g := by
  apply MvPolynomial.algHom_ext
  intro i
  have hlabel : commonReciprocalLabelMap f (MvPolynomial.X i) =
      MvPolynomial.X 0 * commonTailRename (f i) := by
    show MvPolynomial.aeval
      (fun j : Fin m => MvPolynomial.X (0 : Fin (n + 1)) * commonTailRename (f j))
      (MvPolynomial.X i) = _
    simp only [MvPolynomial.aeval_X]
  have hX0 : commonReciprocalEvaluation K φ g (MvPolynomial.X (0 : Fin (n + 1))) =
      (φ g)⁻¹ := by
    show MvPolynomial.aeval (Fin.cons (φ g)⁻¹ (fun j => φ (MvPolynomial.X j)))
      (MvPolynomial.X (0 : Fin (n + 1))) = _
    simp only [MvPolynomial.aeval_X, Fin.cons_zero]
  have htail := common_reciprocal_tail K φ g (f i)
  have hLHS : ((commonReciprocalEvaluation K φ g).comp
      (commonReciprocalLabelMap f)) (MvPolynomial.X i) =
      (φ g)⁻¹ * φ (f i) := by
    rw [AlgHom.comp_apply, hlabel, map_mul, hX0, htail]
  have hRHS : TrackD.rationalFieldPullback K φ f g (MvPolynomial.X i) =
      (φ g)⁻¹ * φ (f i) := by
    show MvPolynomial.aeval (fun j : Fin m => φ (f j) / φ g)
      (MvPolynomial.X i) = _
    rw [MvPolynomial.aeval_X, div_eq_mul_inv, mul_comm]
  rw [hLHS, hRHS]

/-- Every graph point retains the original source equations. -/
theorem common_reciprocal_point_source {n : ℕ} (V : AffineVariety n)
    (K : Type*) [Field K] [Algebra ℂ K] (φ : Poly n →ₐ[ℂ] K)
    (hker : RingHom.ker φ = V.ideal) (g : Poly n) (q : Point (n + 1))
    (hq : ∀ a ∈ RingHom.ker (commonReciprocalEvaluation K φ g),
      MvPolynomial.aeval q a = 0) : Fin.tail q ∈ V := by
  show Fin.tail q ∈ MvPolynomial.zeroLocus ℂ V.ideal
  rw [MvPolynomial.mem_zeroLocus_iff]
  intro f hf
  have hfker : f ∈ RingHom.ker φ := by
    rw [hker]
    exact hf
  have htailker : commonTailRename f ∈
      RingHom.ker (commonReciprocalEvaluation K φ g) := by
    rw [RingHom.mem_ker, common_reciprocal_tail]
    exact RingHom.mem_ker.mp hfker
  have hq0 : MvPolynomial.aeval q (commonTailRename f) = 0 := hq _ htailker
  have heval : MvPolynomial.aeval q (commonTailRename f) =
      MvPolynomial.aeval (Fin.tail q) f := by
    show MvPolynomial.aeval q (MvPolynomial.rename Fin.succ f) = _
    rw [MvPolynomial.aeval_rename]
    rfl
  rw [heval, MvPolynomial.aeval_eq_eval] at hq0
  simpa only [MvPolynomial.aeval_eq_eval] using hq0

/-- A graph point lies on the actual denominator domain and uses its inverse. -/
theorem common_reciprocal_point_denominator {n : ℕ} (K : Type*) [Field K] [Algebra ℂ K]
    (φ : Poly n →ₐ[ℂ] K) (g : Poly n) (hg : φ g ≠ 0) (q : Point (n + 1))
    (hq : ∀ a ∈ RingHom.ker (commonReciprocalEvaluation K φ g),
      MvPolynomial.aeval q a = 0) :
    MvPolynomial.eval (Fin.tail q) g ≠ 0 ∧
      q 0 = (MvPolynomial.eval (Fin.tail q) g)⁻¹ := by
  have hX0 : commonReciprocalEvaluation K φ g (MvPolynomial.X (0 : Fin (n + 1))) =
      (φ g)⁻¹ := by
    show MvPolynomial.aeval (Fin.cons (φ g)⁻¹ (fun j => φ (MvPolynomial.X j)))
      (MvPolynomial.X (0 : Fin (n + 1))) = _
    simp only [MvPolynomial.aeval_X, Fin.cons_zero]
  have htail : commonReciprocalEvaluation K φ g (commonTailRename g) = φ g :=
    common_reciprocal_tail K φ g g
  have heker : MvPolynomial.X (0 : Fin (n + 1)) * commonTailRename g - 1 ∈
      RingHom.ker (commonReciprocalEvaluation K φ g) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hX0, htail, map_one,
      inv_mul_cancel₀ hg, sub_self]
  have hq0 := hq _ heker
  have heval_tail : MvPolynomial.aeval q (commonTailRename g) =
      MvPolynomial.eval (Fin.tail q) g := by
    have h : MvPolynomial.aeval q (commonTailRename g) =
        MvPolynomial.aeval (Fin.tail q) g := by
      show MvPolynomial.aeval q (MvPolynomial.rename Fin.succ g) = _
      rw [MvPolynomial.aeval_rename]
      rfl
    rw [h, MvPolynomial.aeval_eq_eval]
  have hX0q : MvPolynomial.aeval q (MvPolynomial.X (0 : Fin (n + 1)) : Poly (n + 1)) =
      q 0 := by
    simp only [MvPolynomial.aeval_X]
  have hmul : q 0 * MvPolynomial.eval (Fin.tail q) g = 1 := by
    have h := hq0
    simp only [map_sub, map_mul, map_one] at h
    rw [hX0q, heval_tail] at h
    exact sub_eq_zero.mp h
  have hne : MvPolynomial.eval (Fin.tail q) g ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact zero_ne_one hmul
  have hinv : q 0 = (MvPolynomial.eval (Fin.tail q) g)⁻¹ := by
    calc q 0 = q 0 * 1 := by rw [mul_one]
      _ = q 0 * (MvPolynomial.eval (Fin.tail q) g *
          (MvPolynomial.eval (Fin.tail q) g)⁻¹) := by
        rw [mul_inv_cancel₀ hne]
      _ = (q 0 * MvPolynomial.eval (Fin.tail q) g) *
          (MvPolynomial.eval (Fin.tail q) g)⁻¹ := by ring
      _ = 1 * (MvPolynomial.eval (Fin.tail q) g)⁻¹ := by rw [hmul]
      _ = (MvPolynomial.eval (Fin.tail q) g)⁻¹ := by rw [one_mul]
  exact ⟨hne, hinv⟩

/-- Coordinates of the graph's polynomial map give the actual rational point. -/
theorem common_reciprocal_point_label {n m : ℕ} (f : Fin m → Poly n) (g : Poly n)
    (q : Point (n + 1)) (hrecip : q 0 = (MvPolynomial.eval (Fin.tail q) g)⁻¹) :
    ∀ i, MvPolynomial.aeval q (commonReciprocalLabelMap f (MvPolynomial.X i)) =
      TrackD.rationalPoint f g (Fin.tail q) i := by
  intro i
  have hlabel : commonReciprocalLabelMap f (MvPolynomial.X i) =
      MvPolynomial.X (0 : Fin (n + 1)) * commonTailRename (f i) := by
    show MvPolynomial.aeval
      (fun j : Fin m => MvPolynomial.X (0 : Fin (n + 1)) * commonTailRename (f j))
      (MvPolynomial.X i) = _
    simp only [MvPolynomial.aeval_X]
  have h1 : MvPolynomial.aeval q (commonReciprocalLabelMap f (MvPolynomial.X i)) =
      q 0 * MvPolynomial.eval (Fin.tail q) (f i) := by
    rw [hlabel, map_mul, MvPolynomial.aeval_X]
    congr 1
    have h : MvPolynomial.aeval q (commonTailRename (f i)) =
        MvPolynomial.aeval (Fin.tail q) (f i) := by
      show MvPolynomial.aeval q (MvPolynomial.rename Fin.succ (f i)) = _
      rw [MvPolynomial.aeval_rename]
      rfl
    rw [h, MvPolynomial.aeval_eq_eval]
  rw [h1, hrecip]
  show (MvPolynomial.eval (Fin.tail q) g)⁻¹ * MvPolynomial.eval (Fin.tail q) (f i) =
    TrackD.rationalPoint f g (Fin.tail q) i
  show (MvPolynomial.eval (Fin.tail q) g)⁻¹ * MvPolynomial.eval (Fin.tail q) (f i) =
    MvPolynomial.eval (Fin.tail q) (f i) / MvPolynomial.eval (Fin.tail q) g
  rw [div_eq_mul_inv, mul_comm]

/-- Equal actual chart labels preserve the source and the projective direction. -/
theorem common_equal_labels_direction {d : ℕ} (i₀ : Fin d) (x y x' y' : Point d)
    (hi : (y - x) i₀ ≠ 0) (hi' : (y' - x') i₀ ≠ 0)
    (heq : TrackD.productPoint x (TrackD.dirChart (LinearMap.proj i₀) (y - x)) =
      TrackD.productPoint x' (TrackD.dirChart (LinearMap.proj i₀) (y' - x'))) :
    x' = x ∧ ∃ hy : y ≠ x, ∃ hy' : y' ≠ x,
      radialProjection x y hy = radialProjection x y' hy' := by
  have hxeq : x' = x := by
    funext k
    have h := congrFun heq (finSumFinEquiv (Sum.inl k))
    simpa only [TrackD.productPoint_inl] using h.symm
  have hdir : TrackD.dirChart (LinearMap.proj i₀) (y - x) =
      TrackD.dirChart (LinearMap.proj i₀) (y' - x') := by
    funext k
    have h := congrFun heq (finSumFinEquiv (Sum.inr k))
    simpa only [TrackD.productPoint_inr] using h
  have hy : y ≠ x := by
    intro h
    apply hi
    simp [h]
  have hi'' : (y' - x) i₀ ≠ 0 := hxeq ▸ hi'
  have hy' : y' ≠ x := by
    intro h
    apply hi''
    simp [h]
  have hu : y - x ≠ 0 := by
    intro h
    apply hi
    have hcoord := congrFun h i₀
    simpa using hcoord
  have hu' : y' - x ≠ 0 := by
    intro h
    apply hi''
    have hcoord := congrFun h i₀
    simpa using hcoord
  rw [hxeq] at hdir
  have hc : ((y - x) i₀ * ((y' - x) i₀)⁻¹) • (y' - x) = (y - x) := by
    have hcoord : ∀ i, ((y - x) i₀)⁻¹ * (y - x) i =
        ((y' - x) i₀)⁻¹ * (y' - x) i := by
      intro i
      have h := congrFun hdir i
      simpa only [TrackD.dirChart, Pi.smul_apply, smul_eq_mul,
        LinearMap.proj_apply] using h
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have hci : (y - x) i =
        (y - x) i₀ * (((y' - x) i₀)⁻¹ * (y' - x) i) := by
      calc (y - x) i
          = (y - x) i₀ * (((y - x) i₀)⁻¹ * (y - x) i) := by
            rw [← mul_assoc, mul_inv_cancel₀ hi, one_mul]
        _ = (y - x) i₀ * (((y' - x) i₀)⁻¹ * (y' - x) i) := by
            rw [hcoord i]
    calc (y - x) i₀ * ((y' - x) i₀)⁻¹ * (y' - x) i
        = (y - x) i₀ * (((y' - x) i₀)⁻¹ * (y' - x) i) := by
          ring
      _ = (y - x) i := hci.symm
  have hproj : radialProjection x y hy = radialProjection x y' hy' := by
    show Projectivization.mk ℂ (y - x) _ = Projectivization.mk ℂ (y' - x) _
    exact (Projectivization.mk_eq_mk_iff' ℂ (y - x) (y' - x) hu hu').mpr
      ⟨_, hc⟩
  exact ⟨hxeq, hy, hy', hproj⟩

end
end DistinctDistances.SparseCones
