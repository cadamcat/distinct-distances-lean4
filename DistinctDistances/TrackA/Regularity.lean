import DistinctDistances.TrackA.Hilbert
import DistinctDistances.TrackA.Intersections
import DistinctDistances.TrackA.GAProjAux
import DistinctDistances.TrackA.PoolingSupport
import DistinctDistances.TrackA.RegularityAlgebraSupport
import DistinctDistances.TrackA.Requests
import DistinctDistances.TrackA.HomogeneousMinorSupport
import DistinctDistances.TrackA.RegularityBoundSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical Topology

/-- `poly:regularity.binomial-loss`, polynomial.tex:532–539. The constant is
uniform over all dimensions k ≤ n; D positive keeps the rational division explicit. -/
theorem poly_regularity_binomial_loss (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (k q D : ℕ) (a b : ℚ), k ≤ n → 1 ≤ D → 2*q ≤ D →
      0 ≤ a → 0 ≤ b →
      (a+b) * ((D-q+k).choose k : ℚ) ≤ a * ((D+k).choose k : ℚ) →
      b ≤ (C : ℚ) * a * (q : ℚ) / (D : ℚ) :=
  poly_regularity_binomial_loss_proof n

/-- `poly:regularity.exceptional-degree`, polynomial.tex:477–540.
Grade lead: augmented value/vertical-jet rank on a geometric generic fiber. -/
theorem poly_regularity_exceptional_degree (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : AffineFamily.Family n) (k L D : ℕ),
      k ≤ n → AffineFamily.IsPure F k → 1 ≤ L → FromAffineLists F L → C*L ≤ D →
      ∃ bad : AffineFamily.Family n, bad ⊆ F ∧
        AffineFamily.degree bad ≤ (C : ℚ) * AffineFamily.degree F * (L : ℚ) / (D : ℚ) ∧
        ∀ V ∈ F, V ∉ bad → GenericJacobianRank F V D k := by
  exact regularity_exceptional_degree_proof n

/-- `poly:regularity.minor-certificate`, polynomial.tex:542–555.
Grade impl once the family Jacobian ranks are available. -/
theorem poly_regularity_minor_certificate {n : ℕ} (F good : AffineFamily.Family n)
    (k D : ℕ) (hk : k ≤ n) (hgood : good ⊆ F) (hF : AffineFamily.IsPure F k)
    (hrank : ∀ V ∈ good, GenericJacobianRank F V D k) :
    ∃ (E : List (Poly n)) (g : Poly n),
      (∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal ∧ f.totalDegree ≤ D) ∧
      g.totalDegree ≤ n*D ∧ g ∈ Submodule.span ℂ (jacobianMinors E (n-k)) ∧
      (∀ V ∈ good, g ∉ V.ideal) ∧
      ∀ x ∈ (AffineFamily.locus F).points, MvPolynomial.eval x g ≠ 0 →
        SameGermAt (equationLocus E) (AffineFamily.locus F) x ∧
        (equationLocus E).IsSmoothAt x ∧ (equationLocus E).localDimension x = k ∧
        ∀ V ∈ F, ∀ W ∈ F, x ∈ V → x ∈ W → V = W := by
  obtain ⟨E, hE, hspan⟩ := bounded_equation_list F D
  have hwitness : ∀ V ∈ good, ∃ m ∈ jacobianMinors E (n-k), m ∉ V.ideal := by
    intro V hV
    exact generic_rank_detected_by_minor F V k D hk E hE hspan (hrank V hV)
  obtain ⟨g, hgdeg, hgspan, hgoodg⟩ := choose_jacobian_certificate good E k D hk
    (fun f hf => (hE f hf).2) hwitness
  refine ⟨E, g, hE, hgdeg, hgspan, hgoodg, ?_⟩
  intro x hx hxg
  exact request_pure_family_jacobian_germ F k hk hF E (fun f hf => (hE f hf).1) x hx
    (nonzero_certificate_detects_minor E (n-k) g hgspan x hxg)

/-- `poly:regularity`, polynomial.tex:457–556; profiles.tex:381–407;
sparse-cones.tex:497–523,873–906. Whole-family equations, union of systems allowed. -/
theorem poly_regularity (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : AffineFamily.Family n) (k L D : ℕ),
      k ≤ n → AffineFamily.IsPure F k → 1 ≤ L → FromAffineLists F L → C*L ≤ D →
      ∃ (bad : AffineFamily.Family n) (E : List (Poly n)) (g : Poly n),
        bad ⊆ F ∧
        AffineFamily.degree bad ≤ (C : ℚ) * AffineFamily.degree F * (L : ℚ) / (D : ℚ) ∧
        (∀ f ∈ E, f ∈ (AffineFamily.locus F).ideal ∧ f.totalDegree ≤ D) ∧
        g.totalDegree ≤ C*D ∧ g ∈ Submodule.span ℂ (jacobianMinors E (n-k)) ∧
        (∀ V ∈ F, V ∉ bad → g ∉ V.ideal) ∧
        ∀ x ∈ (AffineFamily.locus F).points, MvPolynomial.eval x g ≠ 0 →
          SameGermAt (equationLocus E) (AffineFamily.locus F) x ∧
          (equationLocus E).IsSmoothAt x ∧ (equationLocus E).localDimension x = k ∧
          ∀ V ∈ F, ∀ W ∈ F, x ∈ V → x ∈ W → V = W := by
  obtain ⟨C1, hC1pos, h1⟩ := poly_regularity_exceptional_degree n
  refine ⟨max C1 n, by omega, ?_⟩
  intro F k L D hk hpure hL hlists hCLD
  have hC1LD : C1 * L ≤ D := by
    have : C1 * L ≤ (max C1 n) * L := Nat.mul_le_mul_right L (le_max_left C1 n)
    omega
  obtain ⟨bad, hbad_sub, hbad_deg, hbad_rank⟩ := h1 F k L D hk hpure hL hlists hC1LD
  let good : AffineFamily.Family n := F \ bad
  have hgood_sub : good ⊆ F := Finset.sdiff_subset
  have hrank : ∀ V ∈ good, GenericJacobianRank F V D k := by
    intro V hV
    rw [Finset.mem_sdiff] at hV
    exact hbad_rank V hV.1 hV.2
  obtain ⟨E, g, hE, hgdeg, hgspan, hgideal, hgerm⟩ :=
    poly_regularity_minor_certificate F good k D hk hgood_sub hpure hrank
  refine ⟨bad, E, g, hbad_sub, ?_, hE, ?_, hgspan, ?_, hgerm⟩
  · have hdeg_nonneg : 0 ≤ AffineFamily.degree F := by
      dsimp [AffineFamily.degree]
      apply Finset.sum_nonneg
      intro V hV
      have hprime : V.ideal.IsPrime := (hpure V hV).1
      have htop : V.ideal ≠ ⊤ := hprime.ne_top
      exact le_trans (by decide : (0 : ℚ) ≤ 1) (AffineVariety.one_le_degree V htop)
    have hdeg_le : (C1 : ℚ) * AffineFamily.degree F * (L : ℚ) / (D : ℚ) ≤
        ((max C1 n : ℕ) : ℚ) * AffineFamily.degree F * (L : ℚ) / (D : ℚ) := by
      have hC1le : (C1 : ℚ) ≤ ((max C1 n : ℕ) : ℚ) := by exact_mod_cast (le_max_left C1 n)
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hC1le hdeg_nonneg
    exact hbad_deg.trans hdeg_le
  · have : n * D ≤ (max C1 n) * D := Nat.mul_le_mul_right D (le_max_right C1 n)
    omega
  · intro V hV hnotbad
    have hVgood : V ∈ good := by
      rw [Finset.mem_sdiff]
      exact ⟨hV, hnotbad⟩
    exact hgideal V hVgood

/-- `poly:pooling`, polynomial.tex:562–603; profiles.tex:368–379,405–407. -/
theorem poly_pooling (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : AffineFamily.Family n) (k L L' D : ℕ),
      AffineFamily.IsPure F k → 1 ≤ L → FromAffineLists F L → 1 ≤ L' →
      C * max L L' ≤ D → ∀ h : AffineVariety n → Poly n,
      (∀ V ∈ F, (h V).totalDegree ≤ L' ∧ h V ∉ V.ideal) →
      ∃ (bad : AffineFamily.Family n) (g : Poly n), bad ⊆ F ∧
        AffineFamily.degree bad ≤ (C : ℚ) * AffineFamily.degree F * (L' : ℚ) / (D : ℚ) ∧
        g.totalDegree ≤ D ∧ g ≠ 0 ∧
        (∀ V ∈ F, ∀ x ∈ V.points, MvPolynomial.eval x (h V) = 0 → MvPolynomial.eval x g = 0) ∧
        ∀ V ∈ F, V ∉ bad → g ∉ V.ideal := by
  exact pooling_core n

/-- `poly:regularity.projective`, polynomial.tex:457–556 in generic affine charts;
sparse-cones.tex:497–523,873–906. Homogeneous equations certify the cone away from zero. -/
theorem poly_regularity_projective (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : ProjectiveFamily.Family (n+1)) (k L D : ℕ),
      k ≤ n → ProjectiveFamily.IsPure F k → 1 ≤ L → FromProjectiveLists F L → C*L ≤ D →
      ∃ (bad : ProjectiveFamily.Family (n+1)) (E : List (Poly (n+1))) (g : Poly (n+1)),
        bad ⊆ F ∧
        ProjectiveFamily.degree bad ≤ (C : ℚ) * ProjectiveFamily.degree F * (L : ℚ) / (D : ℚ) ∧
        (∀ f ∈ E, f ∈ (ProjectiveFamily.locus F).ideal ∧ f.IsHomogeneous D) ∧
        g.totalDegree ≤ C*D ∧ g.IsHomogeneous ((n-k)*(D-1)) ∧
        g ∈ Submodule.span ℂ (jacobianMinors E (n-k)) ∧
        (∀ V ∈ F, V ∉ bad → g ∉ V.ideal) ∧
        ∀ p ∈ (ProjectiveFamily.locus F).points, MvPolynomial.eval p.rep g ≠ 0 →
          SameGermAt (equationLocus E) (ProjectiveFamily.locus F).affineCone p.rep ∧
          (equationLocus E).IsSmoothAt p.rep ∧ (equationLocus E).localDimension p.rep = k+1 ∧
          ∀ V ∈ F, ∀ W ∈ F, p ∈ V → p ∈ W → V = W := by
  obtain ⟨C1, hC1, h1⟩ := poly_regularity_exceptional_degree (n+1)
  refine ⟨max C1 (n+1), by omega, ?_⟩
  intro F k L D hk hF hL hlists hCLD
  let G := coneFamily F
  have hk1 : k+1 ≤ n+1 := by omega
  have hG : AffineFamily.IsPure G (k+1) := coneFamily_pure F k hF
  have hC1LD : C1*L ≤ D :=
    (Nat.mul_le_mul_right L (le_max_left C1 (n+1))).trans hCLD
  obtain ⟨badA, hbadA, hdegA, hrank⟩ := h1 G (k+1) L D hk1 hG hL
    (coneFamily_lists F L hlists) hC1LD
  let bad := projectiveBadFamily F badA
  have hbad : bad ⊆ F := Finset.filter_subset _ _
  have hbad_degree : ProjectiveFamily.degree bad = AffineFamily.degree badA := by
    rw [← coneFamily_degree bad, coneFamily_bad F badA hbadA]
  have hdegree : 0 ≤ ProjectiveFamily.degree F := by
    rw [← coneFamily_degree F]
    apply Finset.sum_nonneg
    intro V hV
    exact (by decide : (0 : ℚ) ≤ 1).trans
      (AffineVariety.one_le_degree V (hG V hV).1.ne_top)
  have hbad_bound : ProjectiveFamily.degree bad ≤
      ((max C1 (n+1) : ℕ) : ℚ) * ProjectiveFamily.degree F * (L : ℚ) / (D : ℚ) := by
    rw [hbad_degree]
    have hdegA' : AffineFamily.degree badA ≤
        (C1 : ℚ) * ProjectiveFamily.degree F * (L : ℚ) / (D : ℚ) := by
      simpa only [G, coneFamily_degree] using hdegA
    apply hdegA'.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hdegree
    exact_mod_cast le_max_left C1 (n+1)
  obtain ⟨E, hE, hspan⟩ := homogeneous_equation_list F D
  obtain ⟨ℓ, hℓ, hℓF⟩ := exists_common_linear_chart F (fun V hV => (hF V hV).1)
  let goodA := G \ badA
  have hq : (n+1)-(k+1) = n-k := by omega
  have hwitness : ∀ A ∈ goodA,
      ∃ m ∈ jacobianMinors E ((n+1)-(k+1)), m ∉ A.ideal := by
    intro A hA
    obtain ⟨hAG, hnotbad⟩ := Finset.mem_sdiff.mp hA
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hAG
    exact homogeneous_generic_rank_detected_by_minor F V hV (hF V hV).1
      (k+1) D hk1 E hE hspan ℓ hℓ (hℓF V hV)
      (hrank V.affineCone (Finset.mem_image.mpr ⟨V, hV, rfl⟩) hnotbad)
  obtain ⟨g, hgdeg, hghom, hgspan, hgideal⟩ := choose_homogeneous_jacobian_certificate
    goodA E (k+1) D hk1 (fun f hf => (hE f hf).2) hwitness
  rw [hq] at hghom hgspan
  refine ⟨bad, E, g, hbad, hbad_bound, hE, ?_, hghom, hgspan, ?_, ?_⟩
  · exact hgdeg.trans (Nat.mul_le_mul_right D (le_max_right C1 (n+1)))
  · intro V hV hnotbad
    apply hgideal V.affineCone
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr ⟨V, hV, rfl⟩, ?_⟩
    intro h
    exact hnotbad (Finset.mem_filter.mpr ⟨hV, h⟩)
  · intro p hp hpg
    have hrep : p.rep ∈ (ProjectiveFamily.locus F).affineCone.points := by
      apply (ProjectiveVariety.mem_points_mk_iff _ _ p.rep_nonzero).1
      simpa using hp
    have hrepG : p.rep ∈ (AffineFamily.locus G).points := by
      simpa only [G, coneFamily_locus] using hrep
    have hEcone : ∀ f ∈ E, f ∈ (AffineFamily.locus G).ideal := by
      intro f hf
      simpa only [G, coneFamily_locus, ProjectiveVariety.affineCone] using (hE f hf).1
    have hminor : ∃ m ∈ jacobianMinors E ((n+1)-(k+1)),
        MvPolynomial.eval p.rep m ≠ 0 := by
      rw [hq]
      exact nonzero_certificate_detects_minor E (n-k) g hgspan p.rep hpg
    obtain ⟨hgerm, hsmooth, hdim, hunique⟩ := request_pure_family_jacobian_germ
      G (k+1) hk1 hG E hEcone p.rep hrepG hminor
    refine ⟨?_, hsmooth, hdim, ?_⟩
    · simpa only [G, coneFamily_locus] using hgerm
    · intro V hV W hW hpV hpW
      apply affineCone_injective
      apply hunique V.affineCone (Finset.mem_image.mpr ⟨V, hV, rfl⟩)
        W.affineCone (Finset.mem_image.mpr ⟨W, hW, rfl⟩)
      · apply (ProjectiveVariety.mem_points_mk_iff V p.rep p.rep_nonzero).1
        simpa using (show p ∈ V.points from hpV)
      · apply (ProjectiveVariety.mem_points_mk_iff W p.rep p.rep_nonzero).1
        simpa using (show p ∈ W.points from hpW)

end
end DistinctDistances.TrackA
