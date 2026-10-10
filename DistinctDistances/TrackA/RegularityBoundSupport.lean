import DistinctDistances.TrackA.Hilbert
import DistinctDistances.TrackA.RegularitySheetSupport
import DistinctDistances.TrackA.GAProjAux

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- `poly:augmented-lower`, polynomial.tex:477–530. Every failing
component contributes its degree in nonzero vertical derivative columns. -/
theorem regularity_augmented_lower (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : AffineFamily.Family n) (k L D : ℕ),
      k ≤ n → AffineFamily.IsPure F k → 1 ≤ L → FromAffineLists F L → C*L ≤ D →
      ∃ bad : AffineFamily.Family n, bad ⊆ F ∧
        (∀ V ∈ F, V ∉ bad → GenericJacobianRank F V D k) ∧
        (AffineFamily.degree F + AffineFamily.degree bad) *
          ((D-C*L+k).choose k : ℚ) ≤ (AffineFamily.hilbert F D : ℚ) := by
  obtain ⟨C, hC, hinterpolate⟩ := poly_union_interpolation n
  refine ⟨C, hC, ?_⟩
  intro F k L D hk hF hL hlists hD
  let bad : AffineFamily.Family n := F.filter (fun V => ¬ GenericJacobianRank F V D k)
  have hbadsub : bad ⊆ F := Finset.filter_subset _ _
  obtain ⟨φ, _, hnorm⟩ := poly_hilbert_normalization F k hk hF
  obtain ⟨s, lists, bounds, hdefined, hunion, hsum⟩ := hlists
  choose E hdegree hcomponents using fun i => (hdefined i).2
  obtain ⟨G, indices, hG, hcover, hiso⟩ := regularity_component_generic_fiber_lists
    F hF φ hnorm lists hunion E hcomponents
  obtain ⟨b, selected, hb, hselected⟩ := regularity_subfamily_sheet_indices
    F bad hF hbadsub φ hnorm G hG
  have hdirections : ∀ i : Fin b, ∃ v : FieldPoint n G.Ω, v ≠ 0 ∧
      (∀ j, fieldDirectionalDerivative (G.points (selected i)) v
        (MvPolynomial.map (algebraMap ℂ G.Ω) (φ.pullback (MvPolynomial.X j))) = 0) ∧
      ∀ f : Poly n, f ∈ (AffineFamily.locus F).ideal → f.totalDegree ≤ D →
        fieldDirectionalDerivative (G.points (selected i)) v
          (MvPolynomial.map (algebraMap ℂ G.Ω) f) = 0 := by
    intro i
    obtain ⟨V, hV, hx⟩ := hselected i
    have hVF := (Finset.mem_filter.mp hV).1
    have hVbad := (Finset.mem_filter.mp hV).2
    exact regularity_bad_generic_sheet_vector F hF hk D V hVF hVbad φ G.Ω G.t
      ⟨G.points (selected i), hx⟩
  choose directions hdir using hdirections
  let S := Finset.univ.image G.points
  have hfiberHyp (i : Fin s) : 1 ≤ bounds i ∧
      (∀ f ∈ G.equations (E i), f.totalDegree ≤ bounds i) ∧
      IsolatedPoints (G.equations (E i)) ((indices i).image G.points) :=
    ⟨(hdefined i).1,
      generic_fiber_equations_degree G (E i) (bounds i) (hdefined i).1 (hdegree i),
      generic_fiber_isolated_sublist G (E i) (indices i) (hiso i)⟩
  have hjets : ∀ (values : FieldPoint n G.Ω → G.Ω)
      (derivatives : FieldPoint n G.Ω → Fin n → G.Ω),
      ∃ p : FieldPoly n G.Ω, p.totalDegree ≤ C*L ∧
        ∀ z ∈ S, MvPolynomial.eval z p = values z ∧
          ∀ j, MvPolynomial.eval z (MvPolynomial.pderiv j p) = derivatives z j := by
    intro values derivatives
    obtain ⟨p, hp, hjet⟩ := hinterpolate G.Ω s
      (fun i => (indices i).image G.points) (fun i => G.equations (E i))
      bounds hfiberHyp S (generic_fiber_lists_cover G indices hcover) values derivatives
    exact ⟨p, by rwa [← hsum] at hp, hjet⟩
  have hsurj := augmentedFieldEvaluation_surjective G.points G.points_injective selected
    selected.injective directions (fun i => (hdir i).1) (C*L) hjets
  obtain ⟨transverse, htransverse, hLI⟩ := augmentedComplexEvaluation_monomial_columns
    G.points selected directions (C*L) hsurj
  let psi := augmentedComplexEvaluation G.points selected directions
  have hkernel : ∀ f : Poly n, f ∈ (AffineFamily.locus F).ideal →
      f.totalDegree ≤ D → psi f = 0 := by
    intro f hf hd
    have heval : G.ev (Ideal.Quotient.mk (AffineFamily.locus F).ideal f) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [psi, augmentedComplexEvaluation_apply, augmentedFieldEvaluation,
        LinearMap.coe_mk, AddHom.coe_mk, Fin.append_left, Pi.zero_apply]
      rw [← MvPolynomial.eval₂_eq_eval_map, ← G.ev_coordinates]
      exact congrFun heval i
    · simp only [psi, augmentedComplexEvaluation_apply, augmentedFieldEvaluation,
        LinearMap.coe_mk, AddHom.coe_mk, Fin.append_right, Pi.zero_apply]
      exact (hdir i).2.2 f hf hd
  have hbase : ∀ i j, MvPolynomial.aeval (G.points i)
      (φ.pullback (MvPolynomial.X j)) = G.t j := by
    intro i j
    exact (G.ev_coordinates (φ.pullback (MvPolynomial.X j)) i).symm.trans
      (congrFun (G.ev_base j) i)
  have hlift := regularity_linear_monomial_lifting (AffineFamily.locus F) k (G.r+b)
    (C*L) D hD G.t G.independent (fun j => φ.pullback (MvPolynomial.X j))
    (projection_base_degree φ) transverse htransverse psi hkernel
    (augmentedComplexEvaluation_base_mul G.points selected directions
      (fun j => φ.pullback (MvPolynomial.X j)) G.t hbase (fun i => (hdir i).2.1)) hLI
  rw [Nat.cast_add, G.count_degree, hb] at hlift
  refine ⟨bad, hbadsub, ?_, hlift⟩
  intro V hV hnot
  by_contra h
  exact hnot (Finset.mem_filter.mpr ⟨hV, h⟩)

/-- The actual sheet estimate and the established Hilbert upper bound
supply the original exceptional-degree loss, uniformly in k ≤ n. -/
theorem regularity_exceptional_degree_proof (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : AffineFamily.Family n) (k L D : ℕ),
      k ≤ n → AffineFamily.IsPure F k → 1 ≤ L → FromAffineLists F L → C*L ≤ D →
      ∃ bad : AffineFamily.Family n, bad ⊆ F ∧
        AffineFamily.degree bad ≤ (C : ℚ) * AffineFamily.degree F * (L : ℚ) / (D : ℚ) ∧
        ∀ V ∈ F, V ∉ bad → GenericJacobianRank F V D k := by
  obtain ⟨J, hJ, hjets⟩ := regularity_augmented_lower n
  obtain ⟨B, hB, hbinomial⟩ := poly_regularity_binomial_loss_proof n
  let C := (B+2)*J
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro F k L D hk hF hL hlists hD
  have h2JL : 2*(J*L) ≤ D := by
    have hC2 : 2*J ≤ C := Nat.mul_le_mul_right J (by omega)
    have h := (Nat.mul_le_mul_right L hC2).trans hD
    simpa only [Nat.mul_assoc] using h
  have hJL : J*L ≤ D := by omega
  have hDpos : 1 ≤ D := by nlinarith
  obtain ⟨bad, hbad, hgood, hlower⟩ := hjets F k L D hk hF hL hlists hJL
  have hnonneg (G : AffineFamily.Family n) (hG : G ⊆ F) : 0 ≤ AffineFamily.degree G := by
    dsimp only [AffineFamily.degree]
    apply Finset.sum_nonneg
    intro V hV
    have hp := (hF V (hG hV)).1
    exact le_trans (by decide : (0 : ℚ) ≤ 1) (AffineVariety.one_le_degree V hp.ne_top)
  have hloss := hbinomial k (J*L) D (AffineFamily.degree F) (AffineFamily.degree bad)
    hk hDpos h2JL (hnonneg F (by rfl)) (hnonneg bad hbad)
    (hlower.trans (poly_hilbert_upper F k hF D))
  refine ⟨bad, hbad, hloss.trans ?_, hgood⟩
  have hBC : (B : ℚ)*(J : ℚ) ≤ (C : ℚ) := by
    exact_mod_cast (Nat.mul_le_mul_right J (show B ≤ B+2 by omega))
  calc
    (B : ℚ) * AffineFamily.degree F * ((J*L : ℕ) : ℚ) / (D : ℚ) =
        ((B : ℚ)*(J : ℚ)) * AffineFamily.degree F * (L : ℚ) / (D : ℚ) := by
      rw [Nat.cast_mul]
      ring
    _ ≤ (C : ℚ) * AffineFamily.degree F * (L : ℚ) / (D : ℚ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hBC (hnonneg F (by rfl))

end
end DistinctDistances.TrackA
