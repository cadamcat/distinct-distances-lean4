import DistinctDistances.TrackE.CommonBlockTangents
import DistinctDistances.TrackA.Hilbert
import DistinctDistances.TrackA.RelativePointBezoutSupport

/-! Whole source fibers and literal linear equations for the actual mixed
section, `sc:retained-products.family`, sparse-cones.tex:194–207. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

/-- Conditions at an ORIGINAL source point, before counting its radial slice. -/
def commonSectionSourceCondition {d k : ℕ} (i₀ : Fin d)
    (X Y : AffineVariety d) (φ : AffineProjection d k) (s : Point k)
    (p : Point d) : Prop :=
  p ∈ X ∧ φ.apply p = s ∧ Function.Injective (φ.linear.domRestrict (X.tangentSpace p)) ∧
  (∃ y ∈ Y, (y - p) i₀ ≠ 0) ∧ (radialImage p Y).dimension = k ∧
  TrackD.ForGeneralPoint Y (fun y => commonTangentPair i₀ X Y p y)

/-- The 2k equations are the SAME affine source/direction equations at every
counted label. Actual offsets and the finite-index equivalence are retained. -/
theorem common_block_affine_equations {d k : ℕ} (φ ψ : AffineProjection d k)
    (s t : Point k) :
    ∃ E : Fin (2 * k) → Poly (d + d),
      (∀ i, (E i).totalDegree ≤ 1) ∧
      (∀ p v : Point d, (∀ i, MvPolynomial.eval (TrackD.productPoint p v) (E i) = 0) ↔
        φ.apply p = s ∧ ψ.apply v = t) ∧
      ∀ z : Point (d + d), LinearMap.ker (LinearMap.pi (fun i => differential (E i) z)) =
        LinearMap.ker (commonBlockLinearMap φ.linear ψ.linear) := by
  classical
  have hkk : k + k = 2 * k := by omega
  let e : Fin k ⊕ Fin k ≃ Fin (2 * k) :=
    finSumFinEquiv.trans (finCongr hkk)
  let inlMap : Fin d → Fin (d + d) := fun i => finSumFinEquiv (Sum.inl i)
  let inrMap : Fin d → Fin (d + d) := fun i => finSumFinEquiv (Sum.inr i)
  let leftPoly : Fin k → Poly (d + d) := fun j =>
    MvPolynomial.rename inlMap (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j))
  let rightPoly : Fin k → Poly (d + d) := fun j =>
    MvPolynomial.rename inrMap (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))
  let E : Fin (2 * k) → Poly (d + d) :=
    fun i => Sum.elim leftPoly rightPoly (e.symm i)
  have hEleft : ∀ j, E (e (Sum.inl j)) = leftPoly j := by
    intro j
    show Sum.elim leftPoly rightPoly (e.symm (e (Sum.inl j))) = leftPoly j
    rw [Equiv.symm_apply_apply]
    rfl
  have hEright : ∀ j, E (e (Sum.inr j)) = rightPoly j := by
    intro j
    show Sum.elim leftPoly rightPoly (e.symm (e (Sum.inr j))) = rightPoly j
    rw [Equiv.symm_apply_apply]
    rfl
  have hdeg_left : ∀ j, (leftPoly j).totalDegree ≤ 1 := by
    intro j
    show (MvPolynomial.rename inlMap _).totalDegree ≤ 1
    refine (MvPolynomial.totalDegree_rename_le _ _).trans ?_
    refine (MvPolynomial.totalDegree_sub_C_le _ _).trans ?_
    exact TrackA.projection_base_degree φ j
  have hdeg_right : ∀ j, (rightPoly j).totalDegree ≤ 1 := by
    intro j
    show (MvPolynomial.rename inrMap _).totalDegree ≤ 1
    refine (MvPolynomial.totalDegree_rename_le _ _).trans ?_
    refine (MvPolynomial.totalDegree_sub_C_le _ _).trans ?_
    exact TrackA.projection_base_degree ψ j
  have hdeg : ∀ i, (E i).totalDegree ≤ 1 := by
    intro i
    have hq := e.symm i
    cases hqq : e.symm i with
    | inl j =>
      have hEi : E i = leftPoly j := by
        show Sum.elim leftPoly rightPoly (e.symm i) = leftPoly j
        rw [hqq]
        rfl
      rw [hEi]
      exact hdeg_left j
    | inr j =>
      have hEi : E i = rightPoly j := by
        show Sum.elim leftPoly rightPoly (e.symm i) = rightPoly j
        rw [hqq]
        rfl
      rw [hEi]
      exact hdeg_right j
  have heval_left : ∀ (p v : Point d) (j : Fin k),
      MvPolynomial.eval (TrackD.productPoint p v) (leftPoly j) =
        (φ.apply p) j - s j := by
    intro p v j
    show MvPolynomial.eval (TrackD.productPoint p v)
      (MvPolynomial.rename inlMap _) = _
    rw [TrackD.eval_product_left_rename]
    have hpb := φ.eval_pullback p (MvPolynomial.X j)
    have heq : MvPolynomial.eval p (φ.pullback (MvPolynomial.X j)) =
        (φ.apply p) j := by
      have h1 : MvPolynomial.aeval p (φ.pullback (MvPolynomial.X j)) =
          MvPolynomial.aeval (φ.apply p) (MvPolynomial.X j) := hpb
      simpa [MvPolynomial.aeval_eq_eval] using h1
    simp [heq]
  have heval_right : ∀ (p v : Point d) (j : Fin k),
      MvPolynomial.eval (TrackD.productPoint p v) (rightPoly j) =
        (ψ.apply v) j - t j := by
    intro p v j
    show MvPolynomial.eval (TrackD.productPoint p v)
      (MvPolynomial.rename inrMap _) = _
    rw [TrackD.eval_product_right_rename]
    have hpb := ψ.eval_pullback v (MvPolynomial.X j)
    have heq : MvPolynomial.eval v (ψ.pullback (MvPolynomial.X j)) =
        (ψ.apply v) j := by
      have h1 : MvPolynomial.aeval v (ψ.pullback (MvPolynomial.X j)) =
          MvPolynomial.aeval (ψ.apply v) (MvPolynomial.X j) := hpb
      simpa [MvPolynomial.aeval_eq_eval] using h1
    simp [heq]
  have hforall : ∀ (p v : Point d),
      (∀ i, MvPolynomial.eval (TrackD.productPoint p v) (E i) = 0) ↔
        (∀ j, MvPolynomial.eval (TrackD.productPoint p v) (leftPoly j) = 0) ∧
        (∀ j, MvPolynomial.eval (TrackD.productPoint p v) (rightPoly j) = 0) := by
    intro p v
    constructor
    · intro h
      constructor
      · intro j
        have hj := h (e (Sum.inl j))
        rwa [hEleft] at hj
      · intro j
        have hj := h (e (Sum.inr j))
        rwa [hEright] at hj
    · rintro ⟨hl, hr⟩ i
      cases hqq : e.symm i with
      | inl j =>
        have hEi : E i = leftPoly j := by
          show Sum.elim leftPoly rightPoly (e.symm i) = leftPoly j
          rw [hqq]
          rfl
        rw [hEi]
        exact hl j
      | inr j =>
        have hEi : E i = rightPoly j := by
          show Sum.elim leftPoly rightPoly (e.symm i) = rightPoly j
          rw [hqq]
          rfl
        rw [hEi]
        exact hr j
  have heval_iff : ∀ (p v : Point d),
      (∀ i, MvPolynomial.eval (TrackD.productPoint p v) (E i) = 0) ↔
        φ.apply p = s ∧ ψ.apply v = t := by
    intro p v
    rw [hforall p v]
    constructor
    · rintro ⟨hl, hr⟩
      constructor
      · funext j
        have hj := hl j
        rw [heval_left p v j] at hj
        exact sub_eq_zero.mp hj
      · funext j
        have hj := hr j
        rw [heval_right p v j] at hj
        exact sub_eq_zero.mp hj
    · rintro ⟨hps, hvt⟩
      constructor
      · intro j
        rw [heval_left p v j]
        have hj : (φ.apply p) j = s j := congrFun hps j
        exact sub_eq_zero.mpr hj
      · intro j
        rw [heval_right p v j]
        have hj : (ψ.apply v) j = t j := congrFun hvt j
        exact sub_eq_zero.mpr hj
  have hpullφ : ∀ (x : Point d) (j : Fin k) (v : Point d),
      differential (φ.pullback (MvPolynomial.X j)) x v = (φ.linear v) j := by
    intro x j v
    have hrat := common_affine_projection_rational_differential φ x
    have hratPi : TrackD.rationalDifferential
        (fun i => φ.pullback (MvPolynomial.X i)) 1 x =
        LinearMap.pi (fun i => differential (φ.pullback (MvPolynomial.X i)) x) := by
      unfold TrackD.rationalDifferential
      have heval1 : MvPolynomial.eval x (1 : Poly d) = 1 := by simp
      have hdiff1 : differential (1 : Poly d) x = 0 := by
        have h1 : (1 : Poly d) = MvPolynomial.C (1 : ℂ) := (map_one _).symm
        rw [h1]
        exact TrackD.differential_C 1 x
      simp [heval1, hdiff1]
    have hpiEq : LinearMap.pi (fun i => differential (φ.pullback (MvPolynomial.X i)) x) =
        φ.linear := by
      rw [← hratPi]
      exact hrat
    have h := LinearMap.congr_fun hpiEq v
    have hj := congrFun h j
    simpa [LinearMap.pi_apply] using hj
  have hpullψ : ∀ (x : Point d) (j : Fin k) (v : Point d),
      differential (ψ.pullback (MvPolynomial.X j)) x v = (ψ.linear v) j := by
    intro x j v
    have hrat := common_affine_projection_rational_differential ψ x
    have hratPi : TrackD.rationalDifferential
        (fun i => ψ.pullback (MvPolynomial.X i)) 1 x =
        LinearMap.pi (fun i => differential (ψ.pullback (MvPolynomial.X i)) x) := by
      unfold TrackD.rationalDifferential
      have heval1 : MvPolynomial.eval x (1 : Poly d) = 1 := by simp
      have hdiff1 : differential (1 : Poly d) x = 0 := by
        have h1 : (1 : Poly d) = MvPolynomial.C (1 : ℂ) := (map_one _).symm
        rw [h1]
        exact TrackD.differential_C 1 x
      simp [heval1, hdiff1]
    have hpiEq : LinearMap.pi (fun i => differential (ψ.pullback (MvPolynomial.X i)) x) =
        ψ.linear := by
      rw [← hratPi]
      exact hrat
    have h := LinearMap.congr_fun hpiEq v
    have hj := congrFun h j
    simpa [LinearMap.pi_apply] using hj
  have hleftDiff : ∀ (z w : Point (d + d)) (j : Fin k),
      differential (leftPoly j) z w =
        (φ.linear (TrackD.productLeft w)) j := by
    intro z w j
    have hz : z = TrackD.productPoint (TrackD.productLeft z) (TrackD.productRight z) := by
      rw [TrackD.productPoint_left_right]
    have hw : w = TrackD.productPoint (TrackD.productLeft w) (TrackD.productRight w) := by
      rw [TrackD.productPoint_left_right]
    conv_lhs => rw [hz, hw]
    show differential (MvPolynomial.rename inlMap _) _ _ = _
    have hF : MvPolynomial.rename (⇑finSumFinEquiv.symm)
        (MvPolynomial.rename inlMap
          (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j))) =
        MvPolynomial.rename Sum.inl
          (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j)) := by
      have hcomp : (finSumFinEquiv.symm ∘ inlMap) = Sum.inl := by
        funext i
        show finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)) = Sum.inl i
        exact Equiv.symm_apply_apply _ _
      calc MvPolynomial.rename (⇑finSumFinEquiv.symm)
            (MvPolynomial.rename inlMap _) =
          MvPolynomial.rename (finSumFinEquiv.symm ∘ inlMap) _ := by
            rw [MvPolynomial.rename_rename]
        _ = MvPolynomial.rename Sum.inl _ := by rw [hcomp]
    have hprod := TrackD.differential_product
      (MvPolynomial.rename inlMap
        (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j)))
      (TrackD.productLeft z) (TrackD.productRight z)
      (TrackD.productLeft w) (TrackD.productRight w)
    rw [hF] at hprod
    have hR : TrackD.pairFixRight
        (MvPolynomial.rename Sum.inl
          (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j)))
        (TrackD.productRight z) =
        φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j) :=
      TrackD.pairFixRight_rename_inl _ _
    have hL : TrackD.pairFixLeft
        (MvPolynomial.rename Sum.inl
          (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j)))
        (TrackD.productLeft z) =
        MvPolynomial.C (MvPolynomial.eval (TrackD.productLeft z)
          (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j))) :=
      TrackD.pairFixLeft_rename_inl _ _
    rw [hR, hL] at hprod
    have hC : differential
        (MvPolynomial.C (MvPolynomial.eval (TrackD.productLeft z)
          (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j))))
        (TrackD.productRight z) = 0 :=
      TrackD.differential_C _ _
    have hsub : differential
        (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (s j))
        (TrackD.productLeft z) (TrackD.productLeft w) =
        differential (φ.pullback (MvPolynomial.X j))
          (TrackD.productLeft z) (TrackD.productLeft w) := by
      have h := TrackD.differential_sub
        (φ.pullback (MvPolynomial.X j)) (MvPolynomial.C (s j))
        (TrackD.productLeft z)
      have h0 : differential (MvPolynomial.C (s j))
          (TrackD.productLeft z) = 0 :=
        TrackD.differential_C _ _
      simp [h, h0]
    rw [hC, LinearMap.zero_apply, add_zero, hsub] at hprod
    rw [hprod]
    exact hpullφ (TrackD.productLeft z) j (TrackD.productLeft w)
  have hrightDiff : ∀ (z w : Point (d + d)) (j : Fin k),
      differential (rightPoly j) z w =
        (ψ.linear (TrackD.productRight w)) j := by
    intro z w j
    have hz : z = TrackD.productPoint (TrackD.productLeft z) (TrackD.productRight z) := by
      rw [TrackD.productPoint_left_right]
    have hw : w = TrackD.productPoint (TrackD.productLeft w) (TrackD.productRight w) := by
      rw [TrackD.productPoint_left_right]
    conv_lhs => rw [hz, hw]
    show differential (MvPolynomial.rename inrMap _) _ _ = _
    have hF : MvPolynomial.rename (⇑finSumFinEquiv.symm)
        (MvPolynomial.rename inrMap
          (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))) =
        MvPolynomial.rename Sum.inr
          (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) := by
      have hcomp : (finSumFinEquiv.symm ∘ inrMap) = Sum.inr := by
        funext i
        show finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)) = Sum.inr i
        exact Equiv.symm_apply_apply _ _
      calc MvPolynomial.rename (⇑finSumFinEquiv.symm)
            (MvPolynomial.rename inrMap _) =
          MvPolynomial.rename (finSumFinEquiv.symm ∘ inrMap) _ := by
            rw [MvPolynomial.rename_rename]
        _ = MvPolynomial.rename Sum.inr _ := by rw [hcomp]
    have hprod := TrackD.differential_product
      (MvPolynomial.rename inrMap
        (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)))
      (TrackD.productLeft z) (TrackD.productRight z)
      (TrackD.productLeft w) (TrackD.productRight w)
    rw [hF] at hprod
    have hR : TrackD.pairFixRight
        (MvPolynomial.rename Sum.inr
          (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)))
        (TrackD.productRight z) =
        MvPolynomial.C (MvPolynomial.eval (TrackD.productRight z)
          (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))) :=
      TrackD.pairFixRight_rename_inr _ _
    have hL : TrackD.pairFixLeft
        (MvPolynomial.rename Sum.inr
          (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)))
        (TrackD.productLeft z) =
        ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j) :=
      TrackD.pairFixLeft_rename_inr _ _
    rw [hR, hL] at hprod
    have hC : differential
        (MvPolynomial.C (MvPolynomial.eval (TrackD.productRight z)
          (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))))
        (TrackD.productLeft z) = 0 :=
      TrackD.differential_C _ _
    have hsub : differential
        (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))
        (TrackD.productRight z) (TrackD.productRight w) =
        differential (ψ.pullback (MvPolynomial.X j))
          (TrackD.productRight z) (TrackD.productRight w) := by
      have h := TrackD.differential_sub
        (ψ.pullback (MvPolynomial.X j)) (MvPolynomial.C (t j))
        (TrackD.productRight z)
      have h0 : differential (MvPolynomial.C (t j))
          (TrackD.productRight z) = 0 :=
        TrackD.differential_C _ _
      simp [h, h0]
    have hCw : differential
        (MvPolynomial.C (MvPolynomial.eval (TrackD.productRight z)
          (ψ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))))
        (TrackD.productLeft z) (TrackD.productLeft w) = 0 := by
      rw [hC]
      rfl
    rw [hCw, zero_add, hsub] at hprod
    rw [hprod]
    exact hpullψ (TrackD.productRight z) j (TrackD.productRight w)
  have hblockEq : ∀ w : Point (d + d),
      commonBlockLinearMap φ.linear ψ.linear w =
        TrackD.productPoint (φ.linear (TrackD.productLeft w))
          (ψ.linear (TrackD.productRight w)) := by
    intro w
    rfl
  have hprodZero : ∀ (a b : Point k),
      TrackD.productPoint a b = 0 ↔ a = 0 ∧ b = 0 := by
    intro a b
    have hleftAB : ∀ x y : Point k,
        TrackD.productLeft (TrackD.productPoint x y) = x := by
      intro x y
      have h := TrackD.productLinearEquiv.left_inv (x, y)
      exact congrArg Prod.fst h
    have hrightAB : ∀ x y : Point k,
        TrackD.productRight (TrackD.productPoint x y) = y := by
      intro x y
      have h := TrackD.productLinearEquiv.left_inv (x, y)
      exact congrArg Prod.snd h
    have hleft0 : TrackD.productLeft (0 : Point (k + k)) = 0 := by
      funext j
      rfl
    have hright0 : TrackD.productRight (0 : Point (k + k)) = 0 := by
      funext j
      rfl
    have hprod00 : TrackD.productPoint (0 : Point k) 0 = 0 := by
      funext i
      cases hsym : finSumFinEquiv.symm i with
      | inl j =>
        have h1 : i = finSumFinEquiv (Sum.inl j) := by
          rw [← hsym]
          exact (Equiv.apply_symm_apply _ _).symm
        rw [h1, TrackD.productPoint_inl]
        rfl
      | inr j =>
        have h1 : i = finSumFinEquiv (Sum.inr j) := by
          rw [← hsym]
          exact (Equiv.apply_symm_apply _ _).symm
        rw [h1, TrackD.productPoint_inr]
        rfl
    constructor
    · intro h
      constructor
      · have h1 := congrArg TrackD.productLeft h
        rwa [hleftAB, hleft0] at h1
      · have h1 := congrArg TrackD.productRight h
        rwa [hrightAB, hright0] at h1
    · rintro ⟨ha, hb⟩
      rw [ha, hb]
      exact hprod00
  have hpiKer : ∀ (z w : Point (d + d)),
      w ∈ LinearMap.ker (LinearMap.pi (fun i => differential (E i) z)) ↔
        (∀ j, differential (leftPoly j) z w = 0) ∧
        (∀ j, differential (rightPoly j) z w = 0) := by
    intro z w
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      constructor
      · intro j
        have hj := congrFun h (e (Sum.inl j))
        simpa [LinearMap.pi_apply, hEleft] using hj
      · intro j
        have hj := congrFun h (e (Sum.inr j))
        simpa [LinearMap.pi_apply, hEright] using hj
    · rintro ⟨hl, hr⟩
      funext i
      show (LinearMap.pi (fun i => differential (E i) z)) w i = 0
      rw [LinearMap.pi_apply]
      cases hqq : e.symm i with
      | inl j =>
        have hEi : E i = leftPoly j := by
          show Sum.elim leftPoly rightPoly (e.symm i) = leftPoly j
          rw [hqq]
          rfl
        rw [hEi]
        exact hl j
      | inr j =>
        have hEi : E i = rightPoly j := by
          show Sum.elim leftPoly rightPoly (e.symm i) = rightPoly j
          rw [hqq]
          rfl
        rw [hEi]
        exact hr j
  refine ⟨E, hdeg, heval_iff, ?_⟩
  intro z
  ext w
  rw [hpiKer z w, LinearMap.mem_ker, hblockEq]
  rw [hprodZero]
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · funext j
      have hj := hl j
      rw [hleftDiff z w j] at hj
      exact hj
    · funext j
      have hj := hr j
      rw [hrightDiff z w j] at hj
      exact hj
  · rintro ⟨ha, hb⟩
    constructor
    · intro j
      rw [hleftDiff z w j]
      exact congrFun ha j
    · intro j
      rw [hrightDiff z w j]
      exact congrFun hb j

/-- Disjoint original source coordinates count every distinct direction label once. -/
theorem common_label_union_card {d : ℕ} (S : Finset (Point d))
    (T : Point d → Finset (Point d)) :
    (S.biUnion (fun p => (T p).image (TrackD.productPoint p))).card =
      ∑ p ∈ S, (T p).card := by
  classical
  have hleft : ∀ x y : Point d,
      TrackD.productLeft (TrackD.productPoint x y) = x := by
    intro x y
    have h := TrackD.productLinearEquiv.left_inv (x, y)
    exact congrArg Prod.fst h
  have hright : ∀ x y : Point d,
      TrackD.productRight (TrackD.productPoint x y) = y := by
    intro x y
    have h := TrackD.productLinearEquiv.left_inv (x, y)
    exact congrArg Prod.snd h
  have hinj : ∀ p : Point d, Function.Injective (TrackD.productPoint p) := by
    intro p v v' h
    have h2 := congrArg TrackD.productRight h
    rwa [hright, hright] at h2
  have hdisj : (↑S : Set (Point d)).PairwiseDisjoint
      (fun p => (T p).image (TrackD.productPoint p)) := by
    intro p hp p' hp' hne
    show Disjoint _ _
    rw [Finset.disjoint_left]
    rintro z hz hz'
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v', _, heq⟩ := Finset.mem_image.mp hz'
    have hpeq : p' = p := by
      have h1 := congrArg TrackD.productLeft heq
      rwa [hleft, hleft] at h1
    exact hne hpeq.symm
  rw [Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.card_image_of_injective _ (hinj p)

/-- The original nonempty chart retains the complete radial degree and dimension. -/
theorem common_radial_slice_geometry {d k : ℕ} (i₀ : Fin d)
    (Y : AffineVariety d) (hY : Y.IsIrreducible) (p : Point d)
    (hchart : ∃ y ∈ Y, (y - p) i₀ ≠ 0) (himage : (radialImage p Y).dimension = k) :
    (TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀)).IsIrreducible ∧
    (TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀)).dimension = k ∧
    (TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀)).degree =
      (radialImage p Y).degree := by
  have hne : ∃ x ∈ Y.points, x ≠ p := by
    obtain ⟨y, hy, hi⟩ := hchart
    refine ⟨y, hy, ?_⟩
    intro heq
    subst heq
    simp at hi
  have hZ : (radialImage p Y).IsIrreducible :=
    radialImage_irreducible p Y hY hne
  have hℓnot : MvPolynomial.X i₀ ∉ (radialImage p Y).ideal :=
    common_radial_chart_coordinate_not_mem Y i₀ p hchart
  have hℓ : (MvPolynomial.X i₀ : Poly d).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℂ i₀
  refine ⟨TrackA.linearSlice_irreducible _ hZ _ hℓ hℓnot,
    (TrackA.linearSlice_dimension _ hZ _ hℓ hℓnot).trans himage,
    TrackA.linearSlice_degree _ hZ _ hℓ hℓnot⟩

/-- Keep the literal proper polynomial from a nonempty original generic open. -/
theorem common_principal_open_of_general {d : ℕ} (V : AffineVariety d)
    (Q : Point d → Prop) (hQ : TrackD.ForGeneralPoint V Q) :
    ∃ g : Poly d, g ∉ V.ideal ∧
      ∀ p ∈ V, MvPolynomial.eval p g ≠ 0 → Q p := by
  obtain ⟨g, ⟨x, hx, hne⟩, hQ⟩ := hQ
  refine ⟨g, ?_, hQ⟩
  intro hmem
  exact hne ((TrackD.mem_ideal_iff_eval_zero V g).mp hmem x hx)

/-- An actual WHOLE source normalization fiber lies inside the arbitrary
original source property Q and every mixed-section source condition. -/
theorem common_good_source_section {d k : ℕ} (i₀ : Fin d)
    (X Y : AffineVariety d) (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hk : 1 ≤ k) (hXd : X.dimension = k) (hYd : Y.dimension = k)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (htrans : TrackD.ForGeneralPair X Y (fun p y => y - p ∉ Y.tangentSpace y))
    (Q : Point d → Prop) (hQ : TrackD.ForGeneralPoint X Q) :
    ∃ (φ : AffineProjection d k) (s : Point k) (S : Finset (Point d)),
      Function.Surjective φ.linear ∧ TrackA.FiniteAffineProjection φ X ∧
      (S.card : ℚ) = X.degree ∧
      (∀ p, p ∈ S ↔ p ∈ X ∧ φ.apply p = s) ∧
      ∀ p ∈ S, Q p ∧ commonSectionSourceCondition i₀ X Y φ s p := by
  classical
  have hkd : k ≤ d := by
    have hle := TrackA.pooling_dimension_le_ambient X hX
    omega
  have hPure : AffineFamily.IsPure ({X} : AffineFamily.Family d) k := by
    intro V hV
    have hVX : V = X := Finset.mem_singleton.mp hV
    subst hVX
    exact ⟨hX, hXd⟩
  obtain ⟨φ, hsurj, hnorm⟩ := TrackA.poly_hilbert_normalization ({X} : AffineFamily.Family d) k hkd hPure
  have hmem : X ∈ ({X} : AffineFamily.Family d) := Finset.mem_singleton_self X
  obtain ⟨hfinite, r, hrdeg, hr⟩ := hnorm X hmem
  have hInjGen : TrackD.ForGeneralPoint X
      (fun x => Function.Injective (φ.linear.domRestrict (X.tangentSpace x))) :=
    common_normalization_general_tangent_injective X hX hXd φ hfinite
  have hTanGen : TrackD.ForGeneralPoint X
      (fun p => TrackD.ForGeneralPoint Y (fun y => commonTangentPair i₀ X Y p y)) :=
    common_product_general_tangent_opens i₀ X Y hX hY hchart
  have hRad0 : TrackD.ForGeneralPoint X
      (fun x => (radialImage x Y).dimension = Y.dimension) :=
    common_product_general_radial_dimension i₀ X Y hX hY hchart htrans
  have hRad : TrackD.ForGeneralPoint X
      (fun x => (radialImage x Y).dimension = k) :=
    hRad0.mono (fun x _ hx => hx.trans hYd)
  have h12 : TrackD.ForGeneralPoint X (fun x => Q x ∧
      Function.Injective (φ.linear.domRestrict (X.tangentSpace x))) :=
    TrackD.ForGeneralPoint.and hX hQ hInjGen
  have h123 : TrackD.ForGeneralPoint X (fun x => (Q x ∧
      Function.Injective (φ.linear.domRestrict (X.tangentSpace x))) ∧
      (radialImage x Y).dimension = k) :=
    TrackD.ForGeneralPoint.and hX h12 hRad
  have hAll : TrackD.ForGeneralPoint X (fun x => ((Q x ∧
      Function.Injective (φ.linear.domRestrict (X.tangentSpace x))) ∧
      (radialImage x Y).dimension = k) ∧
      TrackD.ForGeneralPoint Y (fun y => commonTangentPair i₀ X Y x y)) :=
    TrackD.ForGeneralPoint.and hX h123 hTanGen
  obtain ⟨g, hgNotMem, hgImp⟩ := common_principal_open_of_general X _ hAll
  obtain ⟨t, _, S, hcard, hfib, hgOpen⟩ :=
    common_normalization_section_in_open X hX hXd φ hsurj hfinite r hr hrdeg g hgNotMem
  refine ⟨φ, t, S, hsurj, hfinite, hcard, hfib, ?_⟩
  intro p hpS
  have hfibP : p ∈ X ∧ φ.apply p = t := (hfib p).mp hpS
  have hne : MvPolynomial.eval p g ≠ 0 := hgOpen p hpS
  have hcomb := hgImp p hfibP.1 hne
  obtain ⟨⟨⟨hQp, hInjp⟩, hDimp⟩, hTanp⟩ := hcomb
  have hchartp : ∃ y ∈ Y, (y - p) i₀ ≠ 0 := by
    obtain ⟨y, hy, hpair⟩ := hTanp.exists
    exact ⟨y, hy, hpair.1⟩
  refine ⟨hQp, hfibP.1, hfibP.2, hInjp, hchartp, hDimp, hTanp⟩

end
end DistinctDistances.SparseCones
