import DistinctDistances.TrackA.SectionLinearDivisionSupport
import Mathlib.RingTheory.Localization.Ideal
import OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual linear-cut scheme is reduced on every standard cone chart. -/
def ReducedLinearCutCharts {n : ℕ} (V : ProjectiveVariety n) (ℓ : Poly n) : Prop :=
  ∀ i : Fin n, ((V.ideal ⊔ Ideal.span {ℓ}).map
    (algebraMap (Poly n) (Localization.Away (MvPolynomial.X i : Poly n)))).IsRadical

/-- An equation vanishing on the projective cut vanishes on the scheme's
affine zero locus after multiplication by any coordinate, including at zero. -/
theorem projective_cut_coordinate_mul_radical {n : ℕ} (V W : ProjectiveVariety n)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hpoints : ∀ p, p ∈ W.points ↔
      p ∈ V.points ∧ MvPolynomial.eval p.rep ℓ = 0)
    (f : Poly n) (hf : f ∈ W.ideal) (i : Fin n) :
    MvPolynomial.X i * f ∈ (V.ideal ⊔ Ideal.span {ℓ}).radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  intro x hx
  simp only [map_mul, MvPolynomial.aeval_eq_eval, MvPolynomial.eval_X]
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxV : x ∈ V.affineCone.points := fun g hg => hx g (Ideal.mem_sup_left hg)
  have hxℓ : MvPolynomial.eval x ℓ = 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using
      hx ℓ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton ℓ)))
  let p := Projectivization.mk ℂ x hx0
  have hpV : p ∈ V.points := (ProjectiveVariety.mem_points_mk_iff V x hx0).2 hxV
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx0
  have hpℓ : MvPolynomial.eval p.rep ℓ = 0 := by
    rw [← hc]
    change MvPolynomial.eval ((c : ℂ) • x) ℓ = 0
    rw [Bridges.homogeneous_eval_smul ℓ hℓ, hxℓ, mul_zero]
  have hxW : x ∈ W.affineCone.points :=
    (ProjectiveVariety.mem_points_mk_iff W x hx0).1 ((hpoints p).2 ⟨hpV, hpℓ⟩)
  rw [show MvPolynomial.eval x f = 0 by
    simpa only [MvPolynomial.aeval_eq_eval] using hxW f hf, mul_zero]

/-- Reduced coordinate charts turn set-theoretic cut equations into actual
sum-ideal membership after clearing a power of each chart coordinate. -/
theorem projective_cut_power_clear_of_reduced_charts {n : ℕ}
    (V W : ProjectiveVariety n) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hpoints : ∀ p, p ∈ W.points ↔
      p ∈ V.points ∧ MvPolynomial.eval p.rep ℓ = 0)
    (hred : ReducedLinearCutCharts V ℓ) :
    ∀ f ∈ W.ideal, ∀ i : Fin n, ∃ r : ℕ,
      MvPolynomial.X i ^ r * f ∈ V.ideal ⊔ Ideal.span {ℓ} := by
  intro f hf i
  let J := V.ideal ⊔ Ideal.span {ℓ}
  let S := Localization.Away (MvPolynomial.X i : Poly n)
  let g := algebraMap (Poly n) S
  have hmap : g (MvPolynomial.X i * f) ∈ J.map g := by
    have hmem := Ideal.mem_map_of_mem g (projective_cut_coordinate_mul_radical V W ℓ hℓ hpoints f hf i)
    rw [IsLocalization.map_radical (Submonoid.powers (MvPolynomial.X i)) S J,
      (hred i).radical] at hmem
    exact hmem
  have hunit : IsUnit (g (MvPolynomial.X i)) := IsLocalization.Away.algebraMap_isUnit _
  have hfmap : g f ∈ J.map g := by
    rw [map_mul] at hmap
    exact (Ideal.unit_mul_mem_iff_mem _ hunit).1 hmap
  obtain ⟨z, hz, hzf⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers (MvPolynomial.X i)) S J f).1 hfmap
  obtain ⟨r, rfl⟩ := hz
  exact ⟨r, hzf⟩

/-- Pointwise coordinate-power clearing has one uniform irrelevant-ideal
power annihilating the finite generated difference of the two ideals. -/
theorem ideal_irrelevant_power_colon_of_coordinate_clear {n : ℕ}
    (I J : Ideal (Poly n))
    (hclear : ∀ f ∈ J, ∀ i : Fin n, ∃ r : ℕ, MvPolynomial.X i ^ r * f ∈ I) :
    ∃ N : ℕ, MvPolynomial.idealOfVars (Fin n) ℂ ^ N ≤ I.colon (J : Set (Poly n)) := by
  have hvars : MvPolynomial.idealOfVars (Fin n) ℂ ≤ (I.colon (J : Set (Poly n))).radical := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian J)
    choose r hr using fun f : s => hclear f.val (by
      rw [← hs]; exact Ideal.subset_span f.property) i
    let R := ∑ f : s, r f
    refine ⟨R, Submodule.mem_colon.mpr ?_⟩
    intro f hf
    rw [← hs] at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      have hle : r ⟨f, hf⟩ ≤ R := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      have hm := I.mul_mem_left (MvPolynomial.X i ^ (R-r ⟨f, hf⟩)) (hr ⟨f, hf⟩)
      simpa only [smul_eq_mul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle] using hm
    | zero => simp
    | add f g hf hg ihf ihg => simpa only [smul_eq_mul, mul_add] using I.add_mem ihf ihg
    | smul a f hf ih =>
      simpa only [smul_eq_mul, mul_left_comm (MvPolynomial.X i ^ R) a f] using I.mul_mem_left a ih
  exact Ideal.exists_pow_le_of_le_radical_of_fg hvars (MvPolynomial.idealOfVars_fg (Fin n) ℂ)

/-- Uniform coordinate clearing makes the two homogeneous ideals agree in
all sufficiently high degrees. The generators need not be homogeneous. -/
theorem homogeneous_ideal_eventual_agreement_of_coordinate_clear {n : ℕ}
    (I J : Ideal (Poly n))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ)) (hIJ : I ≤ J)
    (hclear : ∀ f ∈ J, ∀ i : Fin n, ∃ r : ℕ, MvPolynomial.X i ^ r * f ∈ I) :
    ∃ T : ℕ, ∀ D ≥ T, ∀ f : Poly n, f.IsHomogeneous D → (f ∈ J ↔ f ∈ I) := by
  obtain ⟨N, hN⟩ := ideal_irrelevant_power_colon_of_coordinate_clear I J hclear
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian J
  let B := ∑ g ∈ s, g.totalDegree
  have hgen (g : Poly n) (hg : g ∈ s) : g ∈ J := by
    rw [← hs]
    exact Ideal.subset_span hg
  have hproduct (g : Poly n) (hg : g ∈ s) (a : Poly n) (D : ℕ) (hD : N+B ≤ D) :
      MvPolynomial.homogeneousComponent D (a*g) ∈ I := by
    have hgB : g.totalDegree ≤ B := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg
    have hexpand : MvPolynomial.homogeneousComponent D (a*g) =
        ∑ e ∈ Finset.range (g.totalDegree+1),
          MvPolynomial.homogeneousComponent D (a * MvPolynomial.homogeneousComponent e g) := by
      conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent g]
      rw [Finset.mul_sum, map_sum]
    rw [hexpand]
    apply I.sum_mem
    intro e he
    have heB : e ≤ B := (Nat.le_of_lt_succ (Finset.mem_range.mp he)).trans hgB
    have heD : e ≤ D := by omega
    have hne : N ≤ D-e := by omega
    have hcomp : MvPolynomial.homogeneousComponent (D-e) a ∈
        MvPolynomial.idealOfVars (Fin n) ℂ ^ N := by
      apply (MvPolynomial.mem_pow_idealOfVars_iff N _).mpr
      intro m hm
      have hd := (MvPolynomial.homogeneousComponent_isHomogeneous (D-e) a)
        (Finsupp.mem_support_iff.mp hm)
      have hd' : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) m = D-e := by
        simpa only [Pi.one_def] using hd
      rw [← Finsupp.degree_eq_weight_one] at hd'
      exact hd' ▸ hne
    have hmem := Submodule.mem_colon.mp (hN hcomp)
      (MvPolynomial.homogeneousComponent e g)
      (MvPolynomial.homogeneousComponent_mem_of_mem hJ (hgen g hg) e)
    rw [mul_comm a _, show D = (D-e)+e by omega,
      homogeneousComponent_mul_homogeneous _ a
        (MvPolynomial.homogeneousComponent_isHomogeneous e g)]
    simpa only [smul_eq_mul, mul_comm] using hmem
  refine ⟨N+B, ?_⟩
  intro D hD f hf
  refine ⟨?_, fun hfI => hIJ hfI⟩
  intro hfJ
  rw [← hs] at hfJ
  obtain ⟨a, ha⟩ := Submodule.mem_span_finset'.mp hfJ
  rw [← MvPolynomial.homogeneousComponent_eq_self hf, ← ha, map_sum]
  exact I.sum_mem (fun g _ => by
    simpa only [smul_eq_mul] using hproduct g.val g.property (a g) D hD)

/-- The quotient factor is an isomorphism at any degree where the actual
homogeneous ideal memberships agree. -/
theorem quotientSection_finrank_eq_of_homogeneous_agreement {n : ℕ}
    (I J : Ideal (Poly n)) (hIJ : I ≤ J) (D : ℕ)
    (hmem : ∀ f : Poly n, f.IsHomogeneous D → (f ∈ J ↔ f ∈ I)) :
    Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection I D) =
      Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection J D) := by
  let q := OAI.PiExponentJets.W64.quotientSectionFactor I J hIJ D
  have hinj : Function.Injective q := by
    apply (LinearMap.ker_eq_bot).1
    apply LinearMap.ker_eq_bot'.2
    intro x hx
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
    change Ideal.Quotient.mk I f = x.val at hfx
    have hfJ : f ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have heq := congrArg Subtype.val hx
      change (Ideal.Quotient.factorₐ ℂ hIJ) x.val = 0 at heq
      rw [← hfx] at heq
      simpa only [Ideal.Quotient.factorₐ_apply_mk] using heq
    apply Subtype.ext
    rw [← hfx]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem f hf).1 hfJ)
  have hsurj := OAI.PiExponentJets.W64.quotientSectionFactor_surjective I J hIJ D
  exact (LinearEquiv.ofBijective q ⟨hinj, hsurj⟩).finrank_eq

/-- Saturation changes no Hilbert polynomial: high-degree restrictions
are compared by the actual quotient map, rather than a numerical premise. -/
theorem homogeneous_hilbertPolynomial_eq_of_coordinate_clear {n : ℕ}
    (I J : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ)) (hIJ : I ≤ J)
    (hclear : ∀ f ∈ J, ∀ i : Fin n, ∃ r : ℕ, MvPolynomial.X i ^ r * f ∈ I) :
    OAI.PiExponentJets.W22.actualHP I hI = OAI.PiExponentJets.W22.actualHP J hJ := by
  obtain ⟨T, hT⟩ := homogeneous_ideal_eventual_agreement_of_coordinate_clear I J hJ hIJ hclear
  obtain ⟨N, hN⟩ := OAI.PiExponentJets.W22.actualHP_eventually J hJ
  apply OAI.PiExponentJets.W22.actualHP_unique I hI _ (T+N)
  intro D hD
  rw [quotientSection_finrank_eq_of_homogeneous_agreement I J hIJ D (hT D (by omega))]
  exact hN D (by omega)

/-- A reduced saturated linear cut has the actual scheme Hilbert
polynomial difference once the linear equation is a nonzero divisor. -/
theorem projective_cut_hilbertPolynomial_of_power_clear {n : ℕ}
    (V W : ProjectiveVariety n) (hWV : W.Subvariety V)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (hℓW : ℓ ∈ W.ideal)
    (hcancel : ∀ f : Poly n, ℓ*f ∈ V.ideal → f ∈ V.ideal)
    (hclear : ∀ f ∈ W.ideal, ∀ i : Fin n, ∃ r : ℕ,
      MvPolynomial.X i ^ r * f ∈ V.ideal ⊔ Ideal.span {ℓ}) :
    W.hilbertPolynomial = V.hilbertPolynomial - Polynomial.taylor (-1) V.hilbertPolynomial := by
  let J := Ideal.span {ℓ} ⊔ V.ideal
  have hspan : (Ideal.span {ℓ}).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
    apply Ideal.homogeneous_span
    rintro f (rfl : f = ℓ)
    exact ⟨1, hℓ⟩
  have hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := hspan.sup V.isHomogeneous
  have hJW : J ≤ W.ideal := sup_le (Ideal.span_le.mpr (by
    rintro f (rfl : f = ℓ); exact hℓW)) hWV
  have hcol : V.ideal.colon {ℓ} = V.ideal := by
    apply le_antisymm
    · intro f hf
      exact hcancel f (by simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hf)
    · exact Ideal.le_colon
  have hcolH : (V.ideal.colon {ℓ}).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := hcol.symm ▸ V.isHomogeneous
  have hcolP := OAI.PiExponentJets.W22.actualHP_congr hcolH V.isHomogeneous hcol
  have hWP := homogeneous_hilbertPolynomial_eq_of_coordinate_clear J W.ideal hJ W.isHomogeneous hJW
    (by simpa only [J, sup_comm] using hclear)
  have hstep := OAI.PiExponentJets.W22.actualHP_colon_step V.ideal V.isHomogeneous ℓ hℓ hJ hcolH
  rw [hWP, hcolP] at hstep
  have hshift : OAI.PiExponentJets.W64.shiftHilbertPolynomial V.hilbertPolynomial 1 =
      Polynomial.taylor (-1) V.hilbertPolynomial := by
    simp only [OAI.PiExponentJets.W64.shiftHilbertPolynomial,
      Polynomial.taylor_apply, Nat.cast_one, Polynomial.C_neg, sub_eq_add_neg]
  calc
    W.hilbertPolynomial = V.hilbertPolynomial -
        OAI.PiExponentJets.W64.shiftHilbertPolynomial V.hilbertPolynomial 1 :=
      (eq_sub_iff_add_eq).2 hstep.symm
    _ = _ := by rw [hshift]

/-- Saturation and actual linear-cut exactness preserve the leading degree
and lower the dimension by one; no degree equality is assumed. -/
theorem projective_cut_dimension_degree_of_power_clear {n : ℕ}
    (V W : ProjectiveVariety n) (hWV : W.Subvariety V)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (hℓW : ℓ ∈ W.ideal)
    (hcancel : ∀ f : Poly n, ℓ*f ∈ V.ideal → f ∈ V.ideal)
    (hclear : ∀ f ∈ W.ideal, ∀ i : Fin n, ∃ r : ℕ,
      MvPolynomial.X i ^ r * f ∈ V.ideal ⊔ Ideal.span {ℓ})
    (k : ℕ) (hdim : V.dimension = k+1) : W.dimension = k ∧ W.degree = V.degree := by
  have hP := projective_cut_hilbertPolynomial_of_power_clear V W hWV ℓ hℓ hℓW hcancel hclear
  have hdimW : W.dimension = k := by
    change W.hilbertPolynomial.natDegree = k
    rw [hP]
    exact (OAI.PiExponentJets.W27.backward_difference_degree_and_leading
      V.hilbertPolynomial k hdim 1 one_ne_zero).1
  refine ⟨hdimW, ?_⟩
  have hmult := OAI.PiExponentJets.W27.backward_difference_multiplicity
    V.hilbertPolynomial k hdim 1 one_ne_zero
  change W.hilbertPolynomial.leadingCoeff * (W.hilbertPolynomial.natDegree.factorial : ℚ) =
    V.hilbertPolynomial.leadingCoeff * (V.hilbertPolynomial.natDegree.factorial : ℚ)
  rw [hP]
  simpa only [ProjectiveVariety.dimension, one_mul] using hmult

/-- The dimension of a nonempty pure family's actual union is its common
component dimension, detected by high-degree restriction ranks. -/
theorem projective_family_locus_dimension {n : ℕ} (F : ProjectiveFamily.Family n)
    (k : ℕ) (hF : ProjectiveFamily.IsPure F k) (hne : F.Nonempty) :
    (ProjectiveFamily.locus F).dimension = k := by
  let V := ProjectiveFamily.locus F
  let P := ∑ W ∈ F, W.hilbertPolynomial
  have hP : P.natDegree ≤ k :=
    Polynomial.natDegree_sum_le_of_forall_le F _ (fun W hW => (hF W hW).2.le)
  have hupper : V.dimension ≤ k := by
    by_cases hz : V.hilbertPolynomial = 0
    · simp only [ProjectiveVariety.dimension, hz, Polynomial.natDegree_zero, Nat.zero_le]
    have hpos : 0 < V.hilbertPolynomial.leadingCoeff :=
      lt_of_le_of_ne (OAI.PiExponentJets.W22.actualHP_leadingCoeff_nonneg V.ideal V.isHomogeneous)
        (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hz))
    choose N hN using fun W : ProjectiveVariety n => W.hilbert_eventually
    obtain ⟨NV, hNV⟩ := V.hilbert_eventually
    let T := ∑ W ∈ F, (N W+1)
    have hle : V.hilbertPolynomial.natDegree ≤ P.natDegree :=
      OAI.PiExponentJets.W24.natDegree_le_of_eventual_polynomial_le _ _ hpos (NV+T+1) (by
        intro D hD
        rw [← hNV D (by omega)]
        have hcomp (W : ProjectiveVariety n) (hW : W ∈ F) :
            (W.hilbert D : ℚ) = W.hilbertPolynomial.eval (D : ℚ) := by
          have hWT : N W+1 ≤ T := by
            change N W+1 ≤ ∑ U ∈ F, (N U+1)
            exact Finset.single_le_sum (fun U _ => Nat.zero_le (N U+1)) hW
          exact hN W D (by omega)
        have hbound := projective_family_hilbert_le_sum F (fun W hW => (hF W hW).1) D
        have hsum : ((∑ W ∈ F, W.hilbert D : ℕ) : ℚ) = P.eval (D : ℚ) := by
          simp only [Nat.cast_sum, P, Polynomial.eval_finsetSum]
          exact Finset.sum_congr rfl hcomp
        exact (by exact_mod_cast hbound : (V.hilbert D : ℚ) ≤
          ((∑ W ∈ F, W.hilbert D : ℕ) : ℚ)).trans_eq hsum)
    exact hle.trans hP
  obtain ⟨W, hW⟩ := hne
  have hlow := OAI.PiExponentJets.W22.actualHP_natDegree_antitone V.isHomogeneous W.isHomogeneous
    (projective_family_member_subvariety F W hW)
  change W.dimension ≤ V.dimension at hlow
  rw [(hF W hW).2] at hlow
  exact le_antisymm hupper hlow

/-- For pure families, reduced standard charts imply the exact total
degree equality needed by the section recursion. -/
theorem projective_family_cut_degree_of_reduced_charts {n : ℕ}
    (F W : ProjectiveFamily.Family n) (k : ℕ)
    (hF : ProjectiveFamily.IsPure F (k+1)) (hW : ProjectiveFamily.IsPure W k)
    (hWV : (ProjectiveFamily.locus W).Subvariety (ProjectiveFamily.locus F))
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (havoid : ∀ V ∈ F, ℓ ∉ V.ideal)
    (hpoints : ∀ p, p ∈ (ProjectiveFamily.locus W).points ↔
      p ∈ (ProjectiveFamily.locus F).points ∧ MvPolynomial.eval p.rep ℓ = 0)
    (hℓW : ℓ ∈ (ProjectiveFamily.locus W).ideal)
    (hred : ReducedLinearCutCharts (ProjectiveFamily.locus F) ℓ) :
    ProjectiveFamily.degree W = ProjectiveFamily.degree F := by
  rcases F.eq_empty_or_nonempty with hF0 | hne
  · subst F
    have hW0 : W = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro V hV
      obtain ⟨p, hp⟩ := ProjectiveFamily.irreducible_points_nonempty V (hW V hV).1
      have hpW : p ∈ (ProjectiveFamily.locus W).points := by
        rw [ProjectiveFamily.points_locus]
        exact Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨hV, hp⟩⟩
      have hpF := (hpoints p).1 hpW
      simpa only [ProjectiveFamily.points_locus, Finset.notMem_empty,
        Set.iUnion_of_empty, Set.iUnion_empty, Set.mem_empty_iff_false] using hpF.1
    simp [hW0, ProjectiveFamily.degree]
  · have hclear := projective_cut_power_clear_of_reduced_charts
      (ProjectiveFamily.locus F) (ProjectiveFamily.locus W) ℓ hℓ hpoints hred
    have hdeg := (projective_cut_dimension_degree_of_power_clear
      (ProjectiveFamily.locus F) (ProjectiveFamily.locus W) hWV ℓ hℓ hℓW
      (projective_family_cancel_polynomial F (fun V hV => (hF V hV).1) ℓ havoid)
      hclear k (projective_family_locus_dimension F (k+1) hF hne)).2
    rwa [ProjectiveFamily.degree_locus W k hW, ProjectiveFamily.degree_locus F (k+1) hF] at hdeg

end
end DistinctDistances.TrackA
