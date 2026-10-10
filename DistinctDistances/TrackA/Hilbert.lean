import DistinctDistances.TrackA.Interpolation
import DistinctDistances.TrackA.GenericFiberSupport
import DistinctDistances.TrackA.ProjectiveChartFamily
import DistinctDistances.TrackA.HilbertUpperBaseSupport
import DistinctDistances.TrackA.HilbertSectionRecursionSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- `poly:hilbert.projective-upper`, polynomial.tex:306–307,315–347. -/
theorem poly_hilbert_projective_upper {n : ℕ} (F : ProjectiveFamily.Family n) (k : ℕ)
    (hF : ProjectiveFamily.IsPure F k) (D : ℕ) :
    (ProjectiveFamily.hilbert F D : ℚ) ≤ ProjectiveFamily.degree F * ((D+k).choose k : ℚ) := by
  haveI := regularSection_pure_family_finite F k hF D
  have hsections := regularSection_pure_family_upper_of_hyperplane
    (fun G j hG d => regularSection_pure_family_finite G j hG d)
    (fun G j hG => request_regularSection_zero_bound G j hG)
    (fun G hG d => request_regularSection_zeroDim_bound G hG d)
    (fun G j hG => by
      obtain ⟨W, ℓ, hℓ, hWV, hW, hdeg, _, _, hexact⟩ :=
        request_regularSection_hyperplane G j hG
      exact ⟨W, ℓ, hℓ, hWV, hW, hdeg, hexact⟩) F k hF D
  have hinject : (ProjectiveFamily.hilbert F D : ℚ) ≤
      (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) : ℚ) := by
    exact_mod_cast hilbert_le_regularSection_finrank (ProjectiveFamily.locus F) D
  exact hinject.trans hsections

/-- `poly:hilbert.upper`, polynomial.tex:289–294,315–347. Unconditional. -/
theorem poly_hilbert_upper {n : ℕ} (F : AffineFamily.Family n) (k : ℕ)
    (hF : AffineFamily.IsPure F k) (D : ℕ) :
    (AffineFamily.hilbert F D : ℚ) ≤ AffineFamily.degree F * ((D+k).choose k : ℚ) := by
  classical
  have hbound (V : AffineVariety n) (hV : V ∈ F) :
      (V.hilbert D : ℚ) ≤ V.degree * ((D+k).choose k : ℚ) := by
    have hdim : (projectiveClosure V).dimension = k :=
      (projectiveClosure_dimension V
        (V.points_nonempty_of_isIrreducible (hF V hV).1)).trans (hF V hV).2
    have hpure : ProjectiveFamily.IsPure {projectiveClosure V} k := by
      intro W hW
      have hWV : W = projectiveClosure V := Finset.mem_singleton.mp hW
      subst W
      exact ⟨projectiveClosure_isIrreducible V (hF V hV).1, hdim⟩
    have hb := poly_hilbert_projective_upper {projectiveClosure V} k hpure D
    simpa only [ProjectiveFamily.hilbert, ProjectiveFamily.locus_singleton,
      ProjectiveFamily.degree, Finset.sum_singleton, projectiveClosure_hilbert,
      projectiveClosure_degree] using hb
  calc
    (AffineFamily.hilbert F D : ℚ) ≤ ((∑ V ∈ F, V.hilbert D : ℕ) : ℚ) := by
      exact_mod_cast AffineFamily.hilbert_le_sum F D
    _ = ∑ V ∈ F, (V.hilbert D : ℚ) := by simp
    _ ≤ ∑ V ∈ F, V.degree * ((D+k).choose k : ℚ) :=
      Finset.sum_le_sum hbound
    _ = AffineFamily.degree F * ((D+k).choose k : ℚ) := by
      simp only [AffineFamily.degree, Finset.sum_mul]

/-- `poly:hilbert.normalization`, polynomial.tex:349–369.
Grade lead: generic *linear*, degree-preserving finite normalization. -/
theorem poly_hilbert_normalization {n : ℕ} (F : AffineFamily.Family n) (k : ℕ)
    (hk : k ≤ n) (hF : AffineFamily.IsPure F k) :
    ∃ φ : AffineProjection n k, Function.Surjective φ.linear ∧
      ∀ V ∈ F, FiniteAffineProjection φ V ∧ ∃ r : ℕ,
        (r : ℚ) = V.degree ∧ φ.GenericallyFiniteOfDegree V r := by
  obtain ⟨ψ, hψ, hfinite⟩ := family_infinity_normalized_linear_projection F hk hF
  refine ⟨⟨ψ, 0⟩, hψ, ?_⟩
  intro V hV
  exact ⟨finite_affine_projection_of_infinity_parameters V ψ (hfinite V hV),
    request_infinity_projection_generic_degree V (hF V hV).1 (hF V hV).2 ψ hψ (hfinite V hV)⟩

/-- `poly:hilbert.monomial-lifting`, polynomial.tex:374–386.
Specialized algebraic form of multiplying transverse columns by base monomials. -/
theorem poly_hilbert_monomial_lifting {n : ℕ} {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (V : AffineVariety n) (k r q D : ℕ) (hqD : q ≤ D)
    (t : Fin k → Ω) (ht : AlgebraicIndependent ℂ t)
    (base : Fin k → Poly n) (hbase : ∀ j, (base j).totalDegree ≤ 1)
    (transverse : Fin r → Poly n) (htransverse : ∀ i, (transverse i).totalDegree ≤ q)
    (ev : (Poly n ⧸ V.ideal) →ₐ[ℂ] (Fin r → Ω))
    (hbase_eval : ∀ j, ev (Ideal.Quotient.mk V.ideal (base j)) = fun _ => t j)
    (hindependent : LinearIndependent Ω
      (fun i => ev (Ideal.Quotient.mk V.ideal (transverse i)))) :
    (r : ℚ) * ((D-q+k).choose k : ℚ) ≤ (V.hilbert D : ℚ) := by
  classical
  let A := OAI.QuarticPowerFree.simplexExponents k (D-q)
  let Alpha := {a : Fin k →₀ ℕ // a ∈ A}
  let Idx := Fin r × Alpha
  let baseEval : MvPolynomial (Fin k) ℂ →ₐ[ℂ] Poly n := MvPolynomial.aeval base
  let psi : Poly n →ₐ[ℂ] (Fin r → Ω) :=
    ev.comp (Ideal.Quotient.mkₐ ℂ V.ideal)
  let baseMono (a : Alpha) : Poly n :=
    baseEval (MvPolynomial.monomial a.val 1)
  let p (z : Idx) : Poly n := transverse z.1 * baseMono z.2
  have hbaseDegree (a : Alpha) : (baseMono a).totalDegree ≤ a.val.degree := by
    change (MvPolynomial.aeval base (MvPolynomial.monomial a.val 1)).totalDegree ≤ _
    rw [MvPolynomial.aeval_monomial]
    simp only [map_one, one_mul]
    calc
      (a.val.prod fun j e => base j ^ e).totalDegree ≤
          ∑ j : Fin k, (base j ^ a.val j).totalDegree := by
        rw [Finsupp.prod_fintype _ _ (by intro j; simp)]
        simpa using
          (MvPolynomial.totalDegree_finsetProd Finset.univ fun j => base j ^ a.val j)
      _ ≤ ∑ j : Fin k, a.val j := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (base j ^ a.val j).totalDegree ≤ a.val j * (base j).totalDegree :=
            MvPolynomial.totalDegree_pow _ _
          _ ≤ a.val j := by
            simpa using Nat.mul_le_mul_left (a.val j) (hbase j)
      _ = a.val.degree := (Finsupp.degree_eq_sum _).symm
  have hpDegree (z : Idx) : (p z).totalDegree ≤ D := by
    have ha := (OAI.QuarticPowerFree.mem_simplexExponents z.2.val).mp z.2.property
    calc
      (p z).totalDegree ≤ (transverse z.1).totalDegree + (baseMono z.2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ q + (D-q) := Nat.add_le_add (htransverse z.1) (hbaseDegree z.2 |>.trans ha)
      _ ≤ D := by omega
  have hbaseComp : psi.comp (MvPolynomial.aeval base) =
      MvPolynomial.aeval (fun j : Fin k => fun _ : Fin r => t j) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [psi, hbase_eval]
  let monEval (a : Alpha) : Ω :=
    MvPolynomial.aeval t (MvPolynomial.monomial a.val (1 : ℂ))
  have hbaseMonoEval (a : Alpha) : psi (baseMono a) = fun _ => monEval a := by
    ext j
    have h := congrArg
      (fun f : MvPolynomial (Fin k) ℂ →ₐ[ℂ] (Fin r → Ω) =>
        f (MvPolynomial.monomial a.val 1)) hbaseComp
    simpa [baseMono, baseEval, monEval, AlgHom.comp_apply,
      MvPolynomial.aeval_monomial] using congrFun h j
  let w (i : Fin r) : Fin r → Ω := ev (Ideal.Quotient.mk V.ideal (transverse i))
  have hfacet (z : Idx) :
      ev (Ideal.Quotient.mk V.ideal (p z)) = monEval z.2 • w z.1 := by
    change psi (p z) = _
    change psi (transverse z.1 * baseMono z.2) = _
    rw [map_mul, hbaseMonoEval]
    ext j
    change ev (Ideal.Quotient.mk V.ideal (transverse z.1)) j * monEval z.2 =
      monEval z.2 * ev (Ideal.Quotient.mk V.ideal (transverse z.1)) j
    exact mul_comm _ _
  let v (z : Idx) : V.restrictionSpace D :=
    ⟨Ideal.Quotient.mk V.ideal (p z), by
      change Ideal.Quotient.mk V.ideal (p z) ∈
        (OAI.QuarticPowerFree.totalSpace D).map
          (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap
      apply Submodule.mem_map.mpr
      exact ⟨p z, OAI.QuarticPowerFree.mem_totalSpace.mpr (hpDegree z), rfl⟩⟩
  have hquotientLI : LinearIndependent ℂ
      (fun z : Idx => Ideal.Quotient.mk V.ideal (p z)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let P (i : Fin r) : MvPolynomial (Fin k) ℂ :=
      ∑ a : Alpha, MvPolynomial.C (c (i, a)) * MvPolynomial.monomial a.val 1
    have hPEval (i : Fin r) :
        MvPolynomial.aeval t (P i) =
          ∑ a : Alpha, algebraMap ℂ Ω (c (i, a)) * monEval a := by
      simp [P, monEval]
    have hsumEval : ∑ z : Idx, c z • ev (Ideal.Quotient.mk V.ideal (p z)) = 0 := by
      have h := congrArg ev.toLinearMap hc
      rw [map_sum] at h
      have hmap (z : Idx) : ev.toLinearMap (c z • Ideal.Quotient.mk V.ideal (p z)) =
          c z • ev.toLinearMap (Ideal.Quotient.mk V.ideal (p z)) :=
        ev.toLinearMap.map_smul (c z) _
      simp_rw [hmap, map_zero, AlgHom.toLinearMap_apply] at h
      exact h
    rw [Fintype.sum_prod_type] at hsumEval
    simp_rw [hfacet] at hsumEval
    simp_rw [Algebra.smul_def] at hsumEval
    have hvector : ∑ i : Fin r, (MvPolynomial.aeval t (P i)) • w i = 0 := by
      ext j
      have hj := congrArg (fun f : Fin r → Ω => f j) hsumEval
      have hcoord :
          ∑ i : Fin r, ∑ a : Alpha,
            algebraMap ℂ Ω (c (i, a)) * (monEval a * w i j) = 0 := by
        simpa using hj
      have hcoord' :
          ∑ i : Fin r, MvPolynomial.aeval t (P i) * w i j = 0 := by
        calc
          _ = ∑ i : Fin r, (∑ a : Alpha,
              algebraMap ℂ Ω (c (i, a)) * monEval a) * w i j := by
            simp_rw [hPEval]
          _ = ∑ i : Fin r, ∑ a : Alpha,
              (algebraMap ℂ Ω (c (i, a)) * monEval a) * w i j := by
            simp_rw [Finset.sum_mul]
          _ = ∑ i : Fin r, ∑ a : Alpha,
              algebraMap ℂ Ω (c (i, a)) * (monEval a * w i j) := by
            simp_rw [mul_assoc]
          _ = 0 := hcoord
      simpa [Pi.smul_apply] using hcoord'
    have hcoeff : ∀ i : Fin r, MvPolynomial.aeval t (P i) = 0 :=
      (Fintype.linearIndependent_iff.mp hindependent) _ hvector
    have htinj : Function.Injective (MvPolynomial.aeval t) :=
      (algebraicIndependent_iff_injective_aeval.mp ht)
    have hPzero (i : Fin r) : P i = 0 := by
      apply htinj
      simpa using hcoeff i
    intro z
    have hc0 := congrArg (fun f : MvPolynomial (Fin k) ℂ => f.coeff z.2.val)
      (hPzero z.1)
    have hc0sum :
        (∑ a : Alpha, c (z.1, a) * if a.val = z.2.val then (1 : ℂ) else 0) = 0 := by
      simpa only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_monomial, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply] using hc0
    have hsumid :
        (∑ a : Alpha, c (z.1, a) * if a.val = z.2.val then (1 : ℂ) else 0) =
          c (z.1, z.2) := by
      rw [Finset.sum_eq_single z.2]
      · simp
      · intro a ha hne
        have hval : a.val ≠ z.2.val := by
          intro he
          exact hne (Subtype.ext he)
        simp [hval]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    exact hsumid.symm.trans hc0sum
  have hli : LinearIndependent ℂ v := by
    apply LinearIndependent.of_comp (V.restrictionSpace D).subtype
    change LinearIndependent ℂ (fun z : Idx => (v z : Poly n ⧸ V.ideal))
    exact hquotientLI
  have hcard : Fintype.card Idx = r * (D-q+k).choose k := by
    simp [Idx, Alpha, A, OAI.QuarticPowerFree.card_simplexExponents]
  have hdim := hli.fintype_card_le_finrank
  rw [hcard] at hdim
  exact_mod_cast hdim

/-- `poly:hilbert.lower`, polynomial.tex:295–301,349–388.
Other components of the common locus may have arbitrary dimension. -/
theorem poly_hilbert_lower (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : AffineFamily.Family n) (k L : ℕ),
      AffineFamily.IsPure F k → 1 ≤ L → AffineFamily.ComponentsDefinedInDegree F L →
      ∃ q : ℕ, q ≤ C * L ∧ ∀ D : ℕ, q ≤ D →
        AffineFamily.degree F * ((D-q+k).choose k : ℚ) ≤ (AffineFamily.hilbert F D : ℚ) := by
  obtain ⟨C, hC, hjets⟩ := poly_interpolation_jets n
  refine ⟨C, hC, ?_⟩
  intro F k L hF hL hdefined
  by_cases hne : F.Nonempty
  · obtain ⟨V, hV⟩ := hne
    have hk : k ≤ n := by
      rw [← (hF V hV).2]
      exact (OAI.QuarticPowerFree.coordinate_hilbert_eventually_polynomial V.ideal).choose_spec.1
    obtain ⟨φ, hsurj, hfinite⟩ := poly_hilbert_normalization F k hk hF
    obtain ⟨E, hE, hcomponents⟩ := hdefined
    obtain ⟨G, hiso⟩ := request_component_generic_fiber F hF φ ⟨hsurj, hfinite⟩ E hcomponents
    let S := Finset.univ.image G.points
    have hS : IsolatedPoints (G.equations E) S := generic_fiber_isolated_list G E hiso
    have hfiberDegree : ∀ f ∈ G.equations E, f.totalDegree ≤ L :=
      generic_fiber_equations_degree G E L hL hE
    have hbounded : ∀ w : Fin G.r → G.Ω,
        ∃ p : FieldPoly n G.Ω, p.totalDegree ≤ C*L ∧
          (fun i => MvPolynomial.eval (G.points i) p) = w := by
      intro w
      let values := Function.extend G.points w (fun _ => 0)
      obtain ⟨p, hp, heval⟩ := hjets G.Ω L hL (G.equations E) hfiberDegree S hS
        values (fun _ _ => 0)
      refine ⟨p, hp, ?_⟩
      funext i
      exact (heval (G.points i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))).1.trans
        (G.points_injective.extend_apply w (fun _ => 0) i)
    obtain ⟨transverse, hdegree, hindependent⟩ := generic_fiber_source_columns G (C*L) hbounded
    refine ⟨C*L, le_rfl, ?_⟩
    intro D hD
    have hlift := poly_hilbert_monomial_lifting (AffineFamily.locus F) k G.r (C*L) D hD
      G.t G.independent (fun j => φ.pullback (MvPolynomial.X j))
      (projection_base_degree φ) transverse hdegree G.ev G.ev_base hindependent
    rw [G.count_degree] at hlift
    exact hlift
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hdeg : AffineFamily.degree F = 0 := by simp [AffineFamily.degree, hFempty]
    refine ⟨0, Nat.zero_le _, ?_⟩
    intro D hD
    simp [hdeg]

/-- `poly:rank-rescaling`, polynomial.tex:390–403. No defining-degree hypothesis. -/
theorem poly_rank_rescaling {n : ℕ} (V : AffineVariety n) (b L : ℕ) (hb : 1 ≤ b) :
    V.hilbert (b*L) ≤ b^n * V.hilbert L := by
  classical
  obtain ⟨s, _, hs⟩ := OAI.QuarticPowerFree.ideal_normal_finite_obstructions
    MonomialOrder.degLex V.ideal
  let q (d : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => d i / b)
  let rem (d : Fin n →₀ ℕ) : Fin n → Fin b :=
    fun i => ⟨d i % b, Nat.mod_lt _ (by omega)⟩
  let src := OAI.QuarticPowerFree.normalExponents s (b*L)
  let dst := OAI.QuarticPowerFree.normalExponents s L
  have hq_le (d : Fin n →₀ ℕ) : q d ≤ d := by
    intro i
    change d i / b ≤ d i
    exact Nat.div_le_self _ _
  have hq_degree {d : Fin n →₀ ℕ} (hd : d ∈ src) : (q d).degree ≤ L := by
    have hsrc := ((OAI.QuarticPowerFree.mem_normalExponents s (b*L) d).mp hd).1
    have hsum : ∑ i : Fin n, d i ≤ b*L := by
      simpa only [Finsupp.degree_eq_sum] using hsrc
    have hdiv : b * (∑ i : Fin n, d i / b) ≤ ∑ i : Fin n, d i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      calc
        b * (d i / b) = (d i / b) * b := Nat.mul_comm _ _
        _ ≤ d i := Nat.div_mul_le_self _ _
    have hquot : (∑ i : Fin n, d i / b) ≤ L :=
      Nat.le_of_mul_le_mul_left (hdiv.trans hsum) (by omega)
    simpa [q, Finsupp.degree_eq_sum] using hquot
  let split (d : {e : Fin n →₀ ℕ // e ∈ src}) :
      {e : Fin n →₀ ℕ // e ∈ dst} × (Fin n → Fin b) :=
    (⟨q d.val, by
      rw [OAI.QuarticPowerFree.mem_normalExponents]
      refine ⟨hq_degree d.property, ?_⟩
      intro a ha had
      have hnormal :=
        ((OAI.QuarticPowerFree.mem_normalExponents s (b*L) d.val).mp d.property).2
      exact hnormal a ha (had.trans (hq_le d.val))⟩, rem d.val)
  have hinj : Function.Injective split := by
    intro d e h
    apply Subtype.ext
    have hq : q d.val = q e.val := congrArg Subtype.val (congrArg Prod.fst h)
    have hr : rem d.val = rem e.val := congrArg Prod.snd h
    apply Finsupp.ext
    intro i
    have hquot : d.val i / b = e.val i / b := by
      exact congrArg (fun x : Fin n →₀ ℕ => x i) hq
    have hrem : d.val i % b = e.val i % b := by
      exact congrArg Fin.val (congrFun hr i)
    have hmul : b * (d.val i / b) = b * (e.val i / b) :=
      congrArg (Nat.mul b) hquot
    have hd := Nat.mod_add_div (d.val i) b
    have he := Nat.mod_add_div (e.val i) b
    omega
  have hcard := Fintype.card_le_of_injective split hinj
  have hcard' : src.card ≤ Fintype.card
      ({e : Fin n →₀ ℕ // e ∈ dst} × (Fin n → Fin b)) := by
    simpa only [Fintype.card_coe] using hcard
  have hnormalCount (T : ℕ) : V.hilbert T =
      (OAI.QuarticPowerFree.normalExponents s T).card := by
    change Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace T).map
      (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap) = _
    rw [OAI.QuarticPowerFree.coordinate_hilbert_count]
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [OAI.QuarticPowerFree.mem_normalExponents, hs, and_comm]
  rw [hnormalCount (b*L), hnormalCount L]
  calc
    src.card ≤ Fintype.card
        ({e : Fin n →₀ ℕ // e ∈ dst} × (Fin n → Fin b)) := hcard'
    _ = dst.card * b^n := by simp
    _ = b^n * dst.card := Nat.mul_comm _ _

private lemma affine_hilbert_at_L_of_shifted
    {n : ℕ} (C : ℕ) (hC : 0 < C) (H : AffineFamily.Family n → ℕ → Prop)
    (hlower : ∀ (F : AffineFamily.Family n) (k L : ℕ),
      AffineFamily.IsPure F k → 1 ≤ L → H F L →
      ∃ q : ℕ, q ≤ C * L ∧ ∀ D : ℕ, q ≤ D →
        AffineFamily.degree F * ((D-q+k).choose k : ℚ) ≤
          (AffineFamily.hilbert F D : ℚ)) :
    ∃ c : ℚ, 0 < c ∧ ∀ (F : AffineFamily.Family n) (k L : ℕ),
      AffineFamily.IsPure F k → 1 ≤ L → H F L →
      c * AffineFamily.degree F * (L : ℚ)^k ≤ (AffineFamily.hilbert F L : ℚ) := by
  let b := C + 1
  let c : ℚ := 1 / ((b : ℚ)^n * ((Nat.factorial n : ℕ) : ℚ))
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  intro F k L hF hL hsys
  by_cases hne : F.Nonempty
  · obtain ⟨V, hV⟩ := hne
    have hk : k ≤ n := by
      letI : V.ideal.IsPrime := (hF V hV).1
      have htrdeg : Algebra.trdeg ℂ (Poly n ⧸ V.ideal) ≤ (n : Cardinal) := by
        have hsurj := Ideal.Quotient.mk_surjective (I := V.ideal)
        have h := trdeg_le_of_surjective
          (Ideal.Quotient.mkₐ ℂ V.ideal) hsurj
        simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin,
          Cardinal.lift_natCast] using h
      have hdim := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg V.ideal
        (OAI.QuarticPowerFree.coordinateHilbert V.ideal)
        (OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal)
      have hle : (V.dimension : Cardinal) ≤ (n : Cardinal) := by
        change ((OAI.QuarticPowerFree.coordinateHilbert V.ideal).natDegree : Cardinal) ≤ _
        rw [hdim]
        exact htrdeg
      have hdimNat : V.dimension ≤ n := by exact_mod_cast hle
      exact (hF V hV).2 ▸ hdimNat
    obtain ⟨q, hq, hshifted⟩ := hlower F k L hF hL hsys
    have hCL : C * L ≤ b * L := Nat.mul_le_mul_right L (by dsimp [b]; omega)
    have hqL : q ≤ b * L := hq.trans hCL
    have hbL : b * L = C * L + L := by
      dsimp [b]
      simp [Nat.succ_mul]
    have harg : L ≤ b * L - q + 1 := by omega
    have hchoose :
        (L : ℚ)^k ≤ ((Nat.factorial k : ℕ) : ℚ) *
          ((b * L - q + k).choose k : ℚ) := by
      have hbin := Nat.pow_le_choose (α := ℚ) k (b * L - q + k)
      have hbin' :
          ((b * L - q + 1 : ℕ) : ℚ)^k / ((Nat.factorial k : ℕ) : ℚ) ≤
            ((b * L - q + k).choose k : ℚ) := by
        simpa only [show b * L - q + k + 1 - k = b * L - q + 1 by omega] using hbin
      have hpow : (L : ℚ)^k ≤ ((b * L - q + 1 : ℕ) : ℚ)^k := by
        exact_mod_cast Nat.pow_le_pow_left harg k
      have hfact : (0 : ℚ) < ((Nat.factorial k : ℕ) : ℚ) := by positivity
      calc
        (L : ℚ)^k ≤ ((b * L - q + 1 : ℕ) : ℚ)^k := hpow
        _ ≤ ((b * L - q + k).choose k : ℚ) * ((Nat.factorial k : ℕ) : ℚ) :=
          (div_le_iff₀ hfact).mp hbin'
        _ = ((Nat.factorial k : ℕ) : ℚ) * ((b * L - q + k).choose k : ℚ) := by ring
    have hfact : ((Nat.factorial k : ℕ) : ℚ) ≤ ((Nat.factorial n : ℕ) : ℚ) := by
      exact_mod_cast Nat.factorial_le hk
    have hchoose' :
        (L : ℚ)^k ≤ ((Nat.factorial n : ℕ) : ℚ) *
          ((b * L - q + k).choose k : ℚ) := by
      calc
        (L : ℚ)^k ≤ ((Nat.factorial k : ℕ) : ℚ) *
          ((b * L - q + k).choose k : ℚ) := hchoose
        _ ≤ ((Nat.factorial n : ℕ) : ℚ) * ((b * L - q + k).choose k : ℚ) :=
          mul_le_mul_of_nonneg_right hfact (by positivity)
    have hdegree_nonneg : 0 ≤ AffineFamily.degree F := by
      unfold AffineFamily.degree
      apply Finset.sum_nonneg
      intro W hW
      exact le_trans (by norm_num : (0 : ℚ) ≤ 1)
        (AffineVariety.one_le_degree W (hF W hW).1.ne_top)
    have hlowerAtB :
        AffineFamily.degree F * ((b * L - q + k).choose k : ℚ) ≤
          (AffineFamily.hilbert F (b * L) : ℚ) := hshifted (b * L) hqL
    have hrescaleNat := poly_rank_rescaling (AffineFamily.locus F) b L hb
    have hrescale :
        (AffineFamily.hilbert F (b * L) : ℚ) ≤
          (b : ℚ)^n * (AffineFamily.hilbert F L : ℚ) := by
      change ((AffineFamily.locus F).hilbert (b * L) : ℚ) ≤
        (b : ℚ)^n * ((AffineFamily.locus F).hilbert L : ℚ)
      exact_mod_cast hrescaleNat
    have hscaled := hlowerAtB.trans hrescale
    have hnum :
        AffineFamily.degree F * (L : ℚ)^k ≤
          ((b : ℚ)^n * ((Nat.factorial n : ℕ) : ℚ)) *
            (AffineFamily.hilbert F L : ℚ) := by
      calc
        AffineFamily.degree F * (L : ℚ)^k ≤
            AffineFamily.degree F *
              (((Nat.factorial n : ℕ) : ℚ) *
                ((b * L - q + k).choose k : ℚ)) :=
          mul_le_mul_of_nonneg_left hchoose' hdegree_nonneg
        _ = ((Nat.factorial n : ℕ) : ℚ) * (AffineFamily.degree F *
              ((b * L - q + k).choose k : ℚ)) := by ring
        _ ≤ ((Nat.factorial n : ℕ) : ℚ) *
          ((b : ℚ)^n * (AffineFamily.hilbert F L : ℚ)) :=
          mul_le_mul_of_nonneg_left hscaled (by positivity)
        _ = ((b : ℚ)^n * ((Nat.factorial n : ℕ) : ℚ)) *
            (AffineFamily.hilbert F L : ℚ) := by ring
    calc
      c * AffineFamily.degree F * (L : ℚ)^k =
          c * (AffineFamily.degree F * (L : ℚ)^k) := by ring
      _ ≤ c * (((b : ℚ)^n * ((Nat.factorial n : ℕ) : ℚ)) *
            (AffineFamily.hilbert F L : ℚ)) :=
        mul_le_mul_of_nonneg_left hnum (le_of_lt hc)
      _ = (AffineFamily.hilbert F L : ℚ) := by
        dsimp [c]
        have hden : (b : ℚ)^n * ((Nat.factorial n : ℕ) : ℚ) ≠ 0 := by positivity
        calc
          (1 / ((b : ℚ)^n * ((Nat.factorial n : ℕ) : ℚ))) *
              (((b : ℚ)^n * ((Nat.factorial n : ℕ) : ℚ)) *
                (AffineFamily.hilbert F L : ℚ)) =
              ((1 / ((b : ℚ)^n * ((Nat.factorial n : ℕ) : ℚ))) *
                ((b : ℚ)^n * ((Nat.factorial n : ℕ) : ℚ))) *
                (AffineFamily.hilbert F L : ℚ) := by ring
          _ = 1 * (AffineFamily.hilbert F L : ℚ) := by
            rw [one_div, inv_mul_cancel₀ hden]
          _ = _ := by ring
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hdeg : AffineFamily.degree F = 0 := by simp [AffineFamily.degree, hFempty]
    simp [hdeg]

/-- `poly:hilbert.at-L`, polynomial.tex:302–305,390–405; reduction.tex:215–230. -/
theorem poly_hilbert_at_L (n : ℕ) :
    ∃ c : ℚ, 0 < c ∧ ∀ (F : AffineFamily.Family n) (k L : ℕ),
      AffineFamily.IsPure F k → 1 ≤ L → AffineFamily.ComponentsDefinedInDegree F L →
      c * AffineFamily.degree F * (L : ℚ)^k ≤ (AffineFamily.hilbert F L : ℚ) := by
  obtain ⟨C, hC, hlower⟩ := poly_hilbert_lower n
  exact affine_hilbert_at_L_of_shifted (n := n) C hC
    (fun F L => AffineFamily.ComponentsDefinedInDegree F L)
    (by
      intro F k L hF hL hdefined
      exact hlower F k L hF hL hdefined)

/-- `poly:hilbert.union-lower`, polynomial.tex:309–312,407–414. -/
theorem poly_hilbert_union_lower (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : AffineFamily.Family n) (k L : ℕ),
      AffineFamily.IsPure F k → 1 ≤ L → FromAffineLists F L →
      ∃ q : ℕ, q ≤ C * L ∧ ∀ D : ℕ, q ≤ D →
        AffineFamily.degree F * ((D-q+k).choose k : ℚ) ≤ (AffineFamily.hilbert F D : ℚ) := by
  obtain ⟨C, hC, hinterpolate⟩ := poly_union_interpolation n
  refine ⟨C, hC, ?_⟩
  intro F k L hF hL hlists
  by_cases hne : F.Nonempty
  · obtain ⟨V, hV⟩ := hne
    have hk : k ≤ n := by
      rw [← (hF V hV).2]
      exact (OAI.QuarticPowerFree.coordinate_hilbert_eventually_polynomial V.ideal).choose_spec.1
    obtain ⟨φ, hsurj, hfinite⟩ := poly_hilbert_normalization F k hk hF
    obtain ⟨s, lists, bounds, hdefined, hunion, hsum⟩ := hlists
    choose E hdegree hcomponents using fun i => (hdefined i).2
    obtain ⟨G, indices, hcover, hiso⟩ := request_component_generic_fiber_lists
      F hF φ ⟨hsurj, hfinite⟩ s lists hunion E hcomponents
    let S := Finset.univ.image G.points
    have hfiberHyp (i : Fin s) : 1 ≤ bounds i ∧
        (∀ f ∈ G.equations (E i), f.totalDegree ≤ bounds i) ∧
        IsolatedPoints (G.equations (E i)) ((indices i).image G.points) :=
      ⟨(hdefined i).1,
        generic_fiber_equations_degree G (E i) (bounds i) (hdefined i).1 (hdegree i),
        generic_fiber_isolated_sublist G (E i) (indices i) (hiso i)⟩
    have hbounded : ∀ w : Fin G.r → G.Ω,
        ∃ p : FieldPoly n G.Ω, p.totalDegree ≤ C*L ∧
          (fun i => MvPolynomial.eval (G.points i) p) = w := by
      intro w
      let values := Function.extend G.points w (fun _ => 0)
      obtain ⟨p, hp, heval⟩ := hinterpolate G.Ω s
        (fun i => (indices i).image G.points) (fun i => G.equations (E i))
        bounds hfiberHyp S (generic_fiber_lists_cover G indices hcover)
        values (fun _ _ => 0)
      refine ⟨p, by rwa [← hsum] at hp, ?_⟩
      funext i
      exact (heval (G.points i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))).1.trans
        (G.points_injective.extend_apply w (fun _ => 0) i)
    obtain ⟨transverse, hdegree, hindependent⟩ := generic_fiber_source_columns G (C*L) hbounded
    refine ⟨C*L, le_rfl, ?_⟩
    intro D hD
    have hlift := poly_hilbert_monomial_lifting (AffineFamily.locus F) k G.r (C*L) D hD
      G.t G.independent (fun j => φ.pullback (MvPolynomial.X j))
      (projection_base_degree φ) transverse hdegree G.ev G.ev_base hindependent
    rw [G.count_degree] at hlift
    exact hlift
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hdeg : AffineFamily.degree F = 0 := by simp [AffineFamily.degree, hFempty]
    refine ⟨0, Nat.zero_le _, ?_⟩
    intro D hD
    simp [hdeg]

/-- `poly:hilbert.union-at-L`, polynomial.tex:309–312,407–414. -/
theorem poly_hilbert_union_at_L (n : ℕ) :
    ∃ c : ℚ, 0 < c ∧ ∀ (F : AffineFamily.Family n) (k L : ℕ),
      AffineFamily.IsPure F k → 1 ≤ L → FromAffineLists F L →
      c * AffineFamily.degree F * (L : ℚ)^k ≤ (AffineFamily.hilbert F L : ℚ) := by
  obtain ⟨C, hC, hlower⟩ := poly_hilbert_union_lower n
  exact affine_hilbert_at_L_of_shifted (n := n) C hC
    (fun F L => FromAffineLists F L)
    (by
      intro F k L hF hL hlists
      exact hlower F k L hF hL hlists)

/-- `poly:hilbert.projective-lower`, polynomial.tex:306–312,407–414. -/
theorem poly_hilbert_projective_lower (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : ProjectiveFamily.Family n) (k L : ℕ),
      ProjectiveFamily.IsPure F k → 1 ≤ L → FromProjectiveLists F L →
      ∃ q : ℕ, q ≤ C * L ∧ ∀ D : ℕ, q ≤ D →
        ProjectiveFamily.degree F * ((D-q+k).choose k : ℚ) ≤ (ProjectiveFamily.hilbert F D : ℚ) := by
  obtain ⟨C, hC, hlower⟩ := poly_hilbert_union_lower n
  refine ⟨C, hC, ?_⟩
  intro F k L hF hL hlists
  have hirr : ∀ V ∈ F, V.IsIrreducible := fun V hV => (hF V hV).1
  obtain ⟨ℓ, hℓ, hℓF⟩ := exists_common_linear_chart F hirr
  have hpure := linearSliceFamily_pure F k hF ℓ hℓ hℓF
  have hdefined := linearSliceFamily_lists F L hlists ℓ hℓ hℓF
  obtain ⟨q, hq, hD⟩ := hlower (linearSliceFamily F ℓ) k L hpure hL hdefined
  refine ⟨q, hq, ?_⟩
  intro D hqD
  have hb := hD D hqD
  rw [linearSliceFamily_degree F hirr ℓ hℓ hℓF,
    linearSliceFamily_hilbert F hirr ℓ hℓ hℓF D] at hb
  exact hb

/-- `poly:hilbert.projective-at-L`, polynomial.tex:306–312. -/
theorem poly_hilbert_projective_at_L (n : ℕ) :
    ∃ c : ℚ, 0 < c ∧ ∀ (F : ProjectiveFamily.Family n) (k L : ℕ),
      ProjectiveFamily.IsPure F k → 1 ≤ L → FromProjectiveLists F L →
      c * ProjectiveFamily.degree F * (L : ℚ)^k ≤ (ProjectiveFamily.hilbert F L : ℚ) := by
  obtain ⟨c, hc, hat⟩ := poly_hilbert_union_at_L n
  refine ⟨c, hc, ?_⟩
  intro F k L hF hL hlists
  have hirr : ∀ V ∈ F, V.IsIrreducible := fun V hV => (hF V hV).1
  obtain ⟨ℓ, hℓ, hℓF⟩ := exists_common_linear_chart F hirr
  have hpure := linearSliceFamily_pure F k hF ℓ hℓ hℓF
  have hdefined := linearSliceFamily_lists F L hlists ℓ hℓ hℓF
  have hb := hat (linearSliceFamily F ℓ) k L hpure hL hdefined
  rw [linearSliceFamily_degree F hirr ℓ hℓ hℓF,
    linearSliceFamily_hilbert F hirr ℓ hℓ hℓF L] at hb
  exact hb

private lemma affine_dimension_le_ambient {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) : V.dimension ≤ n := by
  letI : V.ideal.IsPrime := hV
  have htrdeg : Algebra.trdeg ℂ (Poly n ⧸ V.ideal) ≤ (n : Cardinal) := by
    have hsurj := Ideal.Quotient.mk_surjective (I := V.ideal)
    have h := trdeg_le_of_surjective (Ideal.Quotient.mkₐ ℂ V.ideal) hsurj
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin,
      Cardinal.lift_natCast] using h
  have hdim := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg V.ideal
    (OAI.QuarticPowerFree.coordinateHilbert V.ideal)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal)
  have hle : (V.dimension : Cardinal) ≤ (n : Cardinal) := by
    change ((OAI.QuarticPowerFree.coordinateHilbert V.ideal).natDegree : Cardinal) ≤ _
    rw [hdim]
    exact htrdeg
  exact_mod_cast hle

/-- `poly:envelope.lower`, polynomial.tex:417–423,433–436. -/
theorem poly_envelope_lower (n : ℕ) :
    ∃ c : ℚ, 0 < c ∧ ∀ (F : AffineFamily.Family n) (L : ℕ),
      1 ≤ L → AffineFamily.ComponentsDefinedInDegree F L →
      c * affineWeightedDegree F L ≤ (AffineFamily.hilbert F L : ℚ) := by
  obtain ⟨c₀, hc₀, hatL⟩ := poly_hilbert_at_L n
  let c : ℚ := c₀ / (n + 1 : ℚ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  intro F L hL hdefined
  obtain ⟨E, hE, hcomponents⟩ := hdefined
  let part (k : ℕ) : AffineFamily.Family n := F.filter fun V => V.dimension = k
  have hdim_le (V : AffineVariety n) (hV : V ∈ F) : V.dimension ≤ n := by
    exact affine_dimension_le_ambient V (hcomponents V hV).isPrime
  have hmaps (V : AffineVariety n) (hV : V ∈ F) :
      V.dimension ∈ Finset.range (n + 1) := by
    simp only [Finset.mem_range]
    have hdim := hdim_le V hV
    omega
  have hweight : affineWeightedDegree F L =
      ∑ k ∈ Finset.range (n + 1), AffineFamily.degree (part k) * (L : ℚ)^k := by
    unfold affineWeightedDegree
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [part, AffineFamily.degree]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro V hV'
    have hdim : V.dimension = k := (Finset.mem_filter.mp hV').2
    rw [hdim]
  have hbound (k : ℕ) :
      c₀ * (AffineFamily.degree (part k) * (L : ℚ)^k) ≤
        (AffineFamily.hilbert F L : ℚ) := by
    have hpure : AffineFamily.IsPure (part k) k := by
      intro V hV
      obtain ⟨hVF, hdim⟩ := Finset.mem_filter.mp hV
      exact ⟨(hcomponents V hVF).isPrime, hdim⟩
    have hdefinedPart : AffineFamily.ComponentsDefinedInDegree (part k) L := by
      refine ⟨E, hE, ?_⟩
      intro V hV
      exact hcomponents V (Finset.mem_filter.mp hV).1
    have hat := hatL (part k) k L hpure hL hdefinedPart
    have hsub : (AffineFamily.locus (part k)).Subvariety (AffineFamily.locus F) := by
      change (⨅ V ∈ F, V.ideal).radical ≤ (⨅ V ∈ part k, V.ideal).radical
      apply Ideal.radical_mono
      intro f hf
      simp only [Ideal.mem_iInf] at hf ⊢
      intro V hV
      exact hf V (Finset.mem_filter.mp hV).1
    have hmono := AffineVariety.hilbert_mono (AffineFamily.locus (part k))
      (AffineFamily.locus F) hsub L
    calc
      c₀ * (AffineFamily.degree (part k) * (L : ℚ)^k) =
          c₀ * AffineFamily.degree (part k) * (L : ℚ)^k := by ring
      _ ≤ (AffineFamily.hilbert (part k) L : ℚ) := hat
      _ ≤ (AffineFamily.hilbert F L : ℚ) := by exact_mod_cast hmono
  have hsum :
      ∑ k ∈ Finset.range (n + 1),
          c₀ * (AffineFamily.degree (part k) * (L : ℚ)^k) ≤
        ∑ _k ∈ Finset.range (n + 1), (AffineFamily.hilbert F L : ℚ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hbound k
  have htotal : c₀ * affineWeightedDegree F L ≤
      (n + 1 : ℚ) * (AffineFamily.hilbert F L : ℚ) := by
    calc
      c₀ * affineWeightedDegree F L =
          ∑ k ∈ Finset.range (n + 1),
            c₀ * (AffineFamily.degree (part k) * (L : ℚ)^k) := by
              rw [hweight, Finset.mul_sum]
      _ ≤ ∑ _k ∈ Finset.range (n + 1), (AffineFamily.hilbert F L : ℚ) := hsum
      _ = (n + 1 : ℚ) * (AffineFamily.hilbert F L : ℚ) := by simp
  calc
    c * affineWeightedDegree F L =
        (c₀ * affineWeightedDegree F L) / (n + 1 : ℚ) := by
          dsimp [c]
          ring
    _ ≤ (AffineFamily.hilbert F L : ℚ) :=
      (div_le_iff₀ (by positivity)).2 (by simpa [mul_comm] using htotal)

/-- `poly:envelope.upper`, polynomial.tex:424–428,437–439. -/
theorem poly_envelope_upper {n : ℕ} (F : AffineFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) (D : ℕ) :
    (AffineFamily.hilbert F D : ℚ) ≤
      ∑ V ∈ F, V.degree * ((D + V.dimension).choose V.dimension : ℚ) := by
  classical
  let H := AffineFamily.locus F
  letI : Fintype {V // V ∈ F} := Finset.Subtype.fintype F
  have hpoints (V : AffineVariety n) (hV : V ∈ F) : V.points ⊆ H.points := by
    intro x hx
    rw [AffineFamily.points_locus]
    exact Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨hV, hx⟩⟩
  have hIdeal (V : AffineVariety n) (hV : V ∈ F) : H.ideal ≤ V.ideal := by
    rw [← AffineVariety.vanishingIdeal_points H,
      ← AffineVariety.vanishingIdeal_points V]
    exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) (hpoints V hV)
  let mapV (W : {V // V ∈ F}) : H.restrictionSpace D →ₗ[ℂ]
      (W.val).restrictionSpace D :=
    { toFun := fun x => ⟨Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property) x.val, by
        obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.property
        apply Submodule.mem_map.mpr
        refine ⟨p, hp, ?_⟩
        change Ideal.Quotient.mkₐ ℂ W.val.ideal p =
          Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property) x.val
        rw [← hpx]
        simp⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property)).map_add x.val y.val
      map_smul' := by
        intro c x
        apply Subtype.ext
        change Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property) (c • x.val) =
          c • Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property) x.val
        exact (Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property)).toLinearMap.map_smul c x.val }
  let Φ : H.restrictionSpace D →ₗ[ℂ]
      (∀ V : {V // V ∈ F}, V.val.restrictionSpace D) := LinearMap.pi mapV
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective x.val
    obtain ⟨q, hqRep⟩ := Ideal.Quotient.mk_surjective y.val
    rw [← hp, ← hqRep]
    apply Ideal.Quotient.eq.mpr
    have hdiff (V : AffineVariety n) (hV : V ∈ F) : p - q ∈ V.ideal := by
      let W : {W // W ∈ F} := ⟨V, hV⟩
      have hcomponentEq := congrArg Subtype.val (congrFun hxy W)
      have hq' : Ideal.Quotient.mk V.ideal p = Ideal.Quotient.mk V.ideal q := by
        change (mapV W x : Poly n ⧸ V.ideal) = mapV W y at hcomponentEq
        change Ideal.Quotient.factorₐ ℂ (hIdeal V hV) x.val =
          Ideal.Quotient.factorₐ ℂ (hIdeal V hV) y.val at hcomponentEq
        rw [← hp, ← hqRep] at hcomponentEq
        simpa using hcomponentEq
      have hzero : Ideal.Quotient.mk V.ideal (p - q) = 0 := by
        rw [map_sub, hq', sub_self]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hInf' : p - q ∈ ⨅ V ∈ F, V.ideal := by
      simp only [Ideal.mem_iInf]
      intro V hV
      exact hdiff V hV
    change p - q ∈ (⨅ V ∈ F, V.ideal).radical
    exact Ideal.le_radical hInf'
  letI : ∀ V : {V // V ∈ F}, Module.Free ℂ (V.val.restrictionSpace D) :=
    fun V => Module.Free.of_divisionRing ℂ (V.val.restrictionSpace D)
  have hdim := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_pi_fintype] at hdim
  have hsubtypeSum :
      (∑ V : {V // V ∈ F}, V.val.hilbert D) = ∑ V ∈ F, V.hilbert D := by
    calc
      (∑ V : {V // V ∈ F}, V.val.hilbert D) =
          ∑ V ∈ F.attach, V.val.hilbert D := by rw [Finset.univ_eq_attach]
      _ = ∑ V ∈ F, V.hilbert D := Finset.sum_attach F (fun V => V.hilbert D)
  have hNat : H.hilbert D ≤ ∑ V ∈ F, V.hilbert D := by
    have hNat' : H.hilbert D ≤ ∑ V : {V // V ∈ F}, V.val.hilbert D := by
      simpa [H, AffineFamily.hilbert, AffineVariety.hilbert,
        Finset.univ_eq_attach] using hdim
    exact hNat'.trans (le_of_eq hsubtypeSum)
  have hUpperOne (V : AffineVariety n) (hV : V ∈ F) :
      (V.hilbert D : ℚ) ≤
        V.degree * ((D + V.dimension).choose V.dimension : ℚ) := by
    have hPure : AffineFamily.IsPure ({V} : AffineFamily.Family n) V.dimension := by
      intro W hW
      simp only [Finset.mem_singleton] at hW
      subst W
      exact ⟨hF V hV, rfl⟩
    have hLocus : AffineFamily.locus ({V} : AffineFamily.Family n) = V := by
      apply AffineVariety.ext
      change Ideal.radical (⨅ W ∈ ({V} : AffineFamily.Family n), W.ideal) = V.ideal
      rw [show (⨅ W ∈ ({V} : AffineFamily.Family n), W.ideal) = V.ideal by simp]
      exact Ideal.radical_eq_iff.mpr V.isRadical
    have hUpper := poly_hilbert_upper ({V} : AffineFamily.Family n)
      V.dimension hPure D
    simpa [AffineFamily.hilbert, AffineFamily.degree, hLocus] using hUpper
  calc
    (AffineFamily.hilbert F D : ℚ) ≤
        ∑ V ∈ F, (V.hilbert D : ℚ) := by
          exact_mod_cast hNat
    _ ≤ ∑ V ∈ F, V.degree * ((D + V.dimension).choose V.dimension : ℚ) := by
      apply Finset.sum_le_sum
      intro V hV
      exact hUpperOne V hV

private lemma projective_dimension_le_ambient {n : ℕ} (hn : 0 < n)
    (V : ProjectiveVariety n) : V.dimension ≤ n := by
  have hσ : 0 < Fintype.card (Fin n) := by simpa using hn
  obtain ⟨p, htail, hdeg⟩ :=
    OAI.PiExponentJets.W64.exists_homogeneous_hilbert_polynomial_degree_le
      (Fin n) hσ V.ideal V.isHomogeneous
  obtain ⟨N, hN⟩ := htail
  obtain ⟨NV, hNV⟩ := V.hilbert_eventually
  have heq : p = V.hilbertPolynomial := by
    apply OAI.PiExponentJets.W22.polynomial_eq_of_nat_tail p V.hilbertPolynomial
      (max N NV)
    intro D hD
    calc
      p.eval (D : ℚ) = (V.hilbert D : ℚ) := by
        exact (hN D (by omega)).symm
      _ = V.hilbertPolynomial.eval (D : ℚ) := hNV D (by omega)
  have hdim : V.dimension ≤ Fintype.card (Fin n) - 1 := by
    change V.hilbertPolynomial.natDegree ≤ _
    rw [← heq]
    exact hdeg
  have hn' : Fintype.card (Fin n) - 1 ≤ n := by simp
  exact hdim.trans hn'

/-- `poly:envelope.projective-lower`, homogeneous version used by reduction.tex:215–230. -/
theorem poly_envelope_projective_lower (n : ℕ) :
    ∃ c : ℚ, 0 < c ∧ ∀ (F : ProjectiveFamily.Family n) (L : ℕ),
      1 ≤ L → ProjectiveFamily.ComponentsDefinedInDegree F L →
      c * projectiveWeightedDegree F L ≤ (ProjectiveFamily.hilbert F L : ℚ) := by
  obtain ⟨c₀, hc₀, hatL⟩ := poly_hilbert_projective_at_L n
  let c : ℚ := c₀ / (n + 1 : ℚ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  intro F L hL hdefined
  obtain ⟨E, hE, hcomponents⟩ := hdefined
  by_cases hn : 0 < n
  · let part (k : ℕ) : ProjectiveFamily.Family n := F.filter fun V => V.dimension = k
    have hdim_le (V : ProjectiveVariety n) (hV : V ∈ F) : V.dimension ≤ n :=
      projective_dimension_le_ambient hn V
    have hmaps (V : ProjectiveVariety n) (hV : V ∈ F) :
        V.dimension ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_range]
      have hdim := hdim_le V hV
      omega
    have hweight : projectiveWeightedDegree F L =
        ∑ k ∈ Finset.range (n + 1),
          ProjectiveFamily.degree (part k) * (L : ℚ)^k := by
      unfold projectiveWeightedDegree
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [part, ProjectiveFamily.degree]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro V hV'
      have hdim : V.dimension = k := (Finset.mem_filter.mp hV').2
      rw [hdim]
    have hbound (k : ℕ) :
        c₀ * (ProjectiveFamily.degree (part k) * (L : ℚ)^k) ≤
          (ProjectiveFamily.hilbert F L : ℚ) := by
      have hpure : ProjectiveFamily.IsPure (part k) k := by
        intro V hV
        obtain ⟨hVF, hdim⟩ := Finset.mem_filter.mp hV
        exact ⟨(hcomponents V hVF).isPrime, hdim⟩
      have hdefinedPart : ProjectiveFamily.ComponentsDefinedInDegree (part k) L := by
        refine ⟨E, hE, ?_⟩
        intro V hV
        exact hcomponents V (Finset.mem_filter.mp hV).1
      have hlists : FromProjectiveLists (part k) L := by
        refine ⟨1, fun _ => part k, fun _ => L, ?_⟩
        constructor
        · intro i
          exact ⟨hL, hdefinedPart⟩
        constructor
        · intro V
          simp
        · simp
      have hat := hatL (part k) k L hpure hL hlists
      let H := ProjectiveFamily.locus F
      let Hk := ProjectiveFamily.locus (part k)
      have hpointsSubset : Hk.points ⊆ H.points := by
        intro p hp
        rw [ProjectiveFamily.points_locus] at hp
        rcases Set.mem_iUnion.mp hp with ⟨V, hVk⟩
        rcases Set.mem_iUnion.mp hVk with ⟨hVk, hpV⟩
        rw [ProjectiveFamily.points_locus]
        exact Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr
          ⟨(Finset.mem_filter.mp hVk).1, hpV⟩⟩
      have hI : H.ideal ≤ Hk.ideal := by
        rw [← ProjectiveVariety.vanishingIdeal_points H,
          ← ProjectiveVariety.vanishingIdeal_points Hk]
        have hrep : ProjectiveVariety.nonzeroRepresentatives Hk.points ⊆
            ProjectiveVariety.nonzeroRepresentatives H.points := by
          rintro v ⟨hv, hp⟩
          exact ⟨hv, hpointsSubset hp⟩
        exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) hrep
      let hfactor := OAI.PiExponentJets.W64.quotientSectionFactor
        H.ideal Hk.ideal hI L
      have hsurj := OAI.PiExponentJets.W64.quotientSectionFactor_surjective
        H.ideal Hk.ideal hI L
      have hmonoNat :
          Module.finrank ℂ (Hk.restrictionSpace L) ≤
            Module.finrank ℂ (H.restrictionSpace L) := by
        have h := hfactor.finrank_range_le
        have hsurj' : Function.Surjective hfactor := by simpa [hfactor] using hsurj
        have hrange : LinearMap.range hfactor = ⊤ := LinearMap.range_eq_top.mpr hsurj'
        rw [hrange, finrank_top] at h
        exact h
      have hmono :
          (ProjectiveFamily.hilbert (part k) L : ℚ) ≤
            (ProjectiveFamily.hilbert F L : ℚ) := by
        exact_mod_cast hmonoNat
      calc
        c₀ * (ProjectiveFamily.degree (part k) * (L : ℚ)^k) =
            c₀ * ProjectiveFamily.degree (part k) * (L : ℚ)^k := by ring
        _ ≤ (ProjectiveFamily.hilbert (part k) L : ℚ) := hat
        _ ≤ (ProjectiveFamily.hilbert F L : ℚ) := hmono
    have hsum :
        ∑ k ∈ Finset.range (n + 1),
            c₀ * (ProjectiveFamily.degree (part k) * (L : ℚ)^k) ≤
          ∑ _k ∈ Finset.range (n + 1),
            (ProjectiveFamily.hilbert F L : ℚ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hbound k
    have htotal : c₀ * projectiveWeightedDegree F L ≤
        (n + 1 : ℚ) * (ProjectiveFamily.hilbert F L : ℚ) := by
      calc
        c₀ * projectiveWeightedDegree F L =
            ∑ k ∈ Finset.range (n + 1),
              c₀ * (ProjectiveFamily.degree (part k) * (L : ℚ)^k) := by
                rw [hweight, Finset.mul_sum]
        _ ≤ ∑ _k ∈ Finset.range (n + 1),
              (ProjectiveFamily.hilbert F L : ℚ) := hsum
        _ = (n + 1 : ℚ) * (ProjectiveFamily.hilbert F L : ℚ) := by simp
    calc
      c * projectiveWeightedDegree F L =
          (c₀ * projectiveWeightedDegree F L) / (n + 1 : ℚ) := by
            dsimp [c]
            ring
      _ ≤ (ProjectiveFamily.hilbert F L : ℚ) :=
        (div_le_iff₀ (by positivity)).2 (by simpa [mul_comm] using htotal)
  · have hn0 : n = 0 := by omega
    subst n
    have hEmpty : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro V hV
      have hprime : V.ideal.IsPrime := (hcomponents V hV).isPrime
      have hsat : (1 : Poly 0) ∈ V.ideal := by
        apply V.isSaturated
        intro i
        exact Fin.elim0 i
      exact hprime.ne_top ((Ideal.eq_top_iff_one V.ideal).mpr hsat)
    simp [projectiveWeightedDegree, hEmpty]

/-- `poly:envelope.projective-upper`, polynomial.tex:417–440, homogeneous version. -/
theorem poly_envelope_projective_upper {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) (D : ℕ) :
    (ProjectiveFamily.hilbert F D : ℚ) ≤
      ∑ V ∈ F, V.degree * ((D + V.dimension).choose V.dimension : ℚ) := by
  classical
  let H := ProjectiveFamily.locus F
  letI : Fintype {V // V ∈ F} := Finset.Subtype.fintype F
  have hpoints (V : ProjectiveVariety n) (hV : V ∈ F) : V.points ⊆ H.points := by
    intro p hp
    rw [ProjectiveFamily.points_locus]
    exact Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨hV, hp⟩⟩
  have hIdeal (V : ProjectiveVariety n) (hV : V ∈ F) : H.ideal ≤ V.ideal := by
    rw [← ProjectiveVariety.vanishingIdeal_points H,
      ← ProjectiveVariety.vanishingIdeal_points V]
    have hrep : ProjectiveVariety.nonzeroRepresentatives V.points ⊆
        ProjectiveVariety.nonzeroRepresentatives H.points := by
      rintro v ⟨hv, hp⟩
      exact ⟨hv, hpoints V hV hp⟩
    exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) hrep
  let mapV (W : {V // V ∈ F}) : H.restrictionSpace D →ₗ[ℂ]
      (W.val).restrictionSpace D :=
    { toFun := fun x => ⟨Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property) x.val, by
        obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.property
        apply Submodule.mem_map.mpr
        refine ⟨p, hp, ?_⟩
        change Ideal.Quotient.mkₐ ℂ W.val.ideal p =
          Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property) x.val
        rw [← hpx]
        simp⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property)).map_add x.val y.val
      map_smul' := by
        intro c x
        apply Subtype.ext
        change Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property) (c • x.val) =
          c • Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property) x.val
        exact (Ideal.Quotient.factorₐ ℂ (hIdeal W.val W.property)).toLinearMap.map_smul c x.val }
  let Φ : H.restrictionSpace D →ₗ[ℂ]
      (∀ V : {V // V ∈ F}, V.val.restrictionSpace D) := LinearMap.pi mapV
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective x.val
    obtain ⟨q, hqRep⟩ := Ideal.Quotient.mk_surjective y.val
    rw [← hp, ← hqRep]
    apply Ideal.Quotient.eq.mpr
    have hdiff (V : ProjectiveVariety n) (hV : V ∈ F) : p - q ∈ V.ideal := by
      let W : {W // W ∈ F} := ⟨V, hV⟩
      have hcomponentEq := congrArg Subtype.val (congrFun hxy W)
      have hq' : Ideal.Quotient.mk V.ideal p = Ideal.Quotient.mk V.ideal q := by
        change (mapV W x : Poly n ⧸ V.ideal) = mapV W y at hcomponentEq
        change Ideal.Quotient.factorₐ ℂ (hIdeal V hV) x.val =
          Ideal.Quotient.factorₐ ℂ (hIdeal V hV) y.val at hcomponentEq
        rw [← hp, ← hqRep] at hcomponentEq
        simpa using hcomponentEq
      have hzero : Ideal.Quotient.mk V.ideal (p - q) = 0 := by
        rw [map_sub, hq', sub_self]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hH : p - q ∈ H.ideal := by
      rw [← ProjectiveVariety.vanishingIdeal_points H]
      change p - q ∈ ProjectiveVariety.vanishingIdeal H.points
      rw [ProjectiveVariety.vanishingIdeal]
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro v hv
      obtain ⟨hvne, hp⟩ := hv
      rw [ProjectiveFamily.points_locus] at hp
      rcases Set.mem_iUnion.mp hp with ⟨V, hVF⟩
      rcases Set.mem_iUnion.mp hVF with ⟨hV, hpV⟩
      have hVmem := hdiff V hV
      rw [← ProjectiveVariety.vanishingIdeal_points V] at hVmem
      change p - q ∈ MvPolynomial.vanishingIdeal ℂ
        (ProjectiveVariety.nonzeroRepresentatives V.points) at hVmem
      rw [MvPolynomial.mem_vanishingIdeal_iff] at hVmem
      exact hVmem v ⟨hvne, hpV⟩
    exact hH
  letI : ∀ V : {V // V ∈ F}, Module.Free ℂ (V.val.restrictionSpace D) :=
    fun V => Module.Free.of_divisionRing ℂ (V.val.restrictionSpace D)
  have hdim := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_pi_fintype] at hdim
  have hsubtypeSum :
      (∑ V : {V // V ∈ F}, V.val.hilbert D) = ∑ V ∈ F, V.hilbert D := by
    calc
      (∑ V : {V // V ∈ F}, V.val.hilbert D) =
          ∑ V ∈ F.attach, V.val.hilbert D := by rw [Finset.univ_eq_attach]
      _ = ∑ V ∈ F, V.hilbert D := Finset.sum_attach F (fun V => V.hilbert D)
  have hNat : H.hilbert D ≤ ∑ V ∈ F, V.hilbert D := by
    have hNat' : H.hilbert D ≤ ∑ V : {V // V ∈ F}, V.val.hilbert D := by
      simpa [H, ProjectiveFamily.hilbert, ProjectiveVariety.hilbert,
        Finset.univ_eq_attach] using hdim
    exact hNat'.trans (le_of_eq hsubtypeSum)
  have hUpperOne (V : ProjectiveVariety n) (hV : V ∈ F) :
      (V.hilbert D : ℚ) ≤
        V.degree * ((D + V.dimension).choose V.dimension : ℚ) := by
    have hPure : ProjectiveFamily.IsPure ({V} : ProjectiveFamily.Family n) V.dimension := by
      intro W hW
      simp only [Finset.mem_singleton] at hW
      subst W
      exact ⟨hF V hV, rfl⟩
    have hLocus : ProjectiveFamily.locus ({V} : ProjectiveFamily.Family n) = V := by
      apply ProjectiveVariety.ext
      change ProjectiveVariety.vanishingIdeal (⋃ W ∈ ({V} : ProjectiveFamily.Family n), W.points) =
        V.ideal
      rw [← ProjectiveVariety.vanishingIdeal_points V]
      congr 1
      ext p
      simp
    have hUpper := poly_hilbert_projective_upper ({V} : ProjectiveFamily.Family n)
      V.dimension hPure D
    simpa [ProjectiveFamily.hilbert, ProjectiveFamily.degree, hLocus] using hUpper
  calc
    (ProjectiveFamily.hilbert F D : ℚ) ≤
        ∑ V ∈ F, (V.hilbert D : ℚ) := by exact_mod_cast hNat
    _ ≤ ∑ V ∈ F, V.degree * ((D + V.dimension).choose V.dimension : ℚ) := by
      apply Finset.sum_le_sum
      intro V hV
      exact hUpperOne V hV

/-- Exact conjunction of the affine/projective upper and union/common-system
lower interfaces. It is the output specification of `poly_hilbert`. -/
def HilbertBounds (n C : ℕ) (c : ℚ) : Prop :=
  (∀ (F : AffineFamily.Family n) (k D : ℕ), AffineFamily.IsPure F k →
    (AffineFamily.hilbert F D : ℚ) ≤ AffineFamily.degree F * ((D+k).choose k : ℚ)) ∧
  (∀ (F : ProjectiveFamily.Family (n+1)) (k D : ℕ), ProjectiveFamily.IsPure F k →
    (ProjectiveFamily.hilbert F D : ℚ) ≤ ProjectiveFamily.degree F * ((D+k).choose k : ℚ)) ∧
  (∀ (F : AffineFamily.Family n) (k L : ℕ), AffineFamily.IsPure F k → 1 ≤ L →
    (AffineFamily.ComponentsDefinedInDegree F L ∨ FromAffineLists F L) →
    (∃ q : ℕ, q ≤ C*L ∧ ∀ D : ℕ, q ≤ D →
      AffineFamily.degree F * ((D-q+k).choose k : ℚ) ≤ (AffineFamily.hilbert F D : ℚ)) ∧
    c * AffineFamily.degree F * (L : ℚ)^k ≤ (AffineFamily.hilbert F L : ℚ)) ∧
  (∀ (F : ProjectiveFamily.Family (n+1)) (k L : ℕ), ProjectiveFamily.IsPure F k → 1 ≤ L →
    (ProjectiveFamily.ComponentsDefinedInDegree F L ∨ FromProjectiveLists F L) →
    (∃ q : ℕ, q ≤ C*L ∧ ∀ D : ℕ, q ≤ D →
      ProjectiveFamily.degree F * ((D-q+k).choose k : ℚ) ≤ (ProjectiveFamily.hilbert F D : ℚ)) ∧
    c * ProjectiveFamily.degree F * (L : ℚ)^k ≤ (ProjectiveFamily.hilbert F L : ℚ))

/-- `poly:hilbert`, polynomial.tex:289–415. The first unconditional milestone.
Constants are chosen before the family, its equations, and all degree cutoffs. -/
theorem poly_hilbert (n : ℕ) :
    ∃ (C : ℕ) (c : ℚ), 0 < C ∧ 0 < c ∧ HilbertBounds n C c := by
  obtain ⟨CA, hCA, hlowA⟩ := poly_hilbert_lower n
  obtain ⟨CU, hCU, hlowU⟩ := poly_hilbert_union_lower n
  obtain ⟨CP, hCP, hlowP⟩ := poly_hilbert_projective_lower (n+1)
  obtain ⟨cA, hcA, hatA⟩ := poly_hilbert_at_L n
  obtain ⟨cU, hcU, hatU⟩ := poly_hilbert_union_at_L n
  obtain ⟨cP, hcP, hatP⟩ := poly_hilbert_projective_at_L (n+1)
  have commonProjectiveToLists {F : ProjectiveFamily.Family (n+1)} {L : ℕ}
      (hL : 1 ≤ L) (hdefined : ProjectiveFamily.ComponentsDefinedInDegree F L) :
      FromProjectiveLists F L := by
    refine ⟨1, fun _ => F, fun _ => L, ?_⟩
    constructor
    · intro i
      exact ⟨hL, hdefined⟩
    constructor
    · intro V
      simp
    · simp
  let C := max (max CA CU) CP
  let c := min (min cA cU) cP
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le hCA (le_trans (le_max_left _ _) (le_max_left _ _))
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (lt_min hcA hcU) hcP
  have hCAle : CA ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCUle : CU ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCPle : CP ≤ C := by
    dsimp [C]
    exact le_max_right _ _
  have hcleA : c ≤ cA := by
    dsimp [c]
    exact (min_le_left (min cA cU) cP).trans (min_le_left cA cU)
  have hcleU : c ≤ cU := by
    dsimp [c]
    exact (min_le_left (min cA cU) cP).trans (min_le_right cA cU)
  have hcleP : c ≤ cP := by
    dsimp [c]
    exact min_le_right (min cA cU) cP
  refine ⟨C, c, hC, hc, ?_⟩
  unfold HilbertBounds
  refine ⟨?_, ?_⟩
  · intro F k D hF
    exact poly_hilbert_upper F k hF D
  refine ⟨?_, ?_⟩
  · intro F k D hF
    exact poly_hilbert_projective_upper F k hF D
  refine ⟨?_, ?_⟩
  · intro F k L hF hL hsystems
    constructor
    · rcases hsystems with hdefined | hlists
      · obtain ⟨q, hq, hD⟩ := hlowA F k L hF hL hdefined
        exact ⟨q, hq.trans (Nat.mul_le_mul_right L hCAle), hD⟩
      · obtain ⟨q, hq, hD⟩ := hlowU F k L hF hL hlists
        exact ⟨q, hq.trans (Nat.mul_le_mul_right L hCUle), hD⟩
    · have hdegree : 0 ≤ AffineFamily.degree F := by
        unfold AffineFamily.degree
        apply Finset.sum_nonneg
        intro V hV
        exact le_trans (by norm_num : (0 : ℚ) ≤ 1)
          (AffineVariety.one_le_degree V (hF V hV).1.ne_top)
      have hpow : 0 ≤ (L : ℚ)^k := pow_nonneg (Nat.cast_nonneg _) _
      rcases hsystems with hdefined | hlists
      · calc
          c * AffineFamily.degree F * (L : ℚ)^k =
              c * (AffineFamily.degree F * (L : ℚ)^k) := by ring
          _ ≤ cA * (AffineFamily.degree F * (L : ℚ)^k) :=
              mul_le_mul_of_nonneg_right hcleA (mul_nonneg hdegree hpow)
          _ = cA * AffineFamily.degree F * (L : ℚ)^k := by ring
          _ ≤ (AffineFamily.hilbert F L : ℚ) := hatA F k L hF hL hdefined
      · calc
          c * AffineFamily.degree F * (L : ℚ)^k =
              c * (AffineFamily.degree F * (L : ℚ)^k) := by ring
          _ ≤ cU * (AffineFamily.degree F * (L : ℚ)^k) :=
              mul_le_mul_of_nonneg_right hcleU (mul_nonneg hdegree hpow)
          _ = cU * AffineFamily.degree F * (L : ℚ)^k := by ring
          _ ≤ (AffineFamily.hilbert F L : ℚ) := hatU F k L hF hL hlists
  · intro F k L hF hL hsystems
    constructor
    · rcases hsystems with hdefined | hlists
      · have hlists := commonProjectiveToLists hL hdefined
        obtain ⟨q, hq, hD⟩ := hlowP F k L hF hL hlists
        exact ⟨q, hq.trans (Nat.mul_le_mul_right L hCPle), hD⟩
      · obtain ⟨q, hq, hD⟩ := hlowP F k L hF hL hlists
        exact ⟨q, hq.trans (Nat.mul_le_mul_right L hCPle), hD⟩
    · have hdegree : 0 ≤ ProjectiveFamily.degree F := by
        unfold ProjectiveFamily.degree
        apply Finset.sum_nonneg
        intro V hV
        have hirr : V.IsIrreducible := (hF V hV).1
        have hcone : 1 ≤ V.affineCone.degree :=
          AffineVariety.one_le_degree V.affineCone (by
            change V.ideal ≠ ⊤
            exact hirr.ne_top)
        rw [← ProjectiveVariety.degree_cone]
        exact le_trans (by norm_num : (0 : ℚ) ≤ 1) hcone
      have hpow : 0 ≤ (L : ℚ)^k := pow_nonneg (Nat.cast_nonneg _) _
      rcases hsystems with hdefined | hlists
      · have hlists := commonProjectiveToLists hL hdefined
        calc
          c * ProjectiveFamily.degree F * (L : ℚ)^k =
              c * (ProjectiveFamily.degree F * (L : ℚ)^k) := by ring
          _ ≤ cP * (ProjectiveFamily.degree F * (L : ℚ)^k) :=
              mul_le_mul_of_nonneg_right hcleP (mul_nonneg hdegree hpow)
          _ = cP * ProjectiveFamily.degree F * (L : ℚ)^k := by ring
          _ ≤ (ProjectiveFamily.hilbert F L : ℚ) := hatP F k L hF hL hlists
      · calc
          c * ProjectiveFamily.degree F * (L : ℚ)^k =
              c * (ProjectiveFamily.degree F * (L : ℚ)^k) := by ring
          _ ≤ cP * (ProjectiveFamily.degree F * (L : ℚ)^k) :=
              mul_le_mul_of_nonneg_right hcleP (mul_nonneg hdegree hpow)
          _ = cP * ProjectiveFamily.degree F * (L : ℚ)^k := by ring
          _ ≤ (ProjectiveFamily.hilbert F L : ℚ) := hatP F k L hF hL hlists

end
end DistinctDistances.TrackA
