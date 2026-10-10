import DistinctDistances.TrackB.RulingTangentSupport

namespace DistinctDistances.TrackB
noncomputable section

/-- Choosing another nonempty principal source open preserves the actual
projective image closure. This is the density input for the good B22 source. -/
theorem polynomial_projective_image_closure_independent {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible) (g h : Poly n)
    (hg : g ∉ X.ideal) (hh : h ∉ X.ideal) (F : Fin m → Poly n)
    (hF : ∀ x ∈ X.points, (fun i => MvPolynomial.aeval x (F i)) ≠ 0) :
    ProjectiveVariety.closure (polynomialProjectiveImage X g F) =
      ProjectiveVariety.closure (polynomialProjectiveImage X h F) := by
  have transfer (g h : Poly n) (hg : g ∉ X.ideal) :
      (ProjectiveVariety.closure (polynomialProjectiveImage X g F)).ideal ≤
        (ProjectiveVariety.closure (polynomialProjectiveImage X h F)).ideal := by
    intro f hf
    rintro w ⟨hw, hp⟩
    obtain ⟨x, hx, _, hFx, he⟩ := hp
    let v : Point m := fun i => MvPolynomial.aeval x (F i)
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ w v hw hFx).mp he.symm
    have ht0 : t ≠ 0 := by
      intro htzero
      rw [htzero, zero_smul] at ht
      exact hw ht.symm
    let Q : Poly n := MvPolynomial.aeval (fun i => MvPolynomial.C t * F i) f
    have heval (z : Point n) : MvPolynomial.aeval z Q =
        MvPolynomial.aeval (t • (fun i => MvPolynomial.aeval z (F i))) f := by
      dsimp only [Q]
      rw [MvPolynomial.comp_aeval_apply]
      apply congrArg (fun w : Point m => MvPolynomial.aeval w f)
      funext i
      simp
    have hQ : Q ∈ X.ideal := by
      apply principal_open_vanishing X hX g Q hg
      intro z hz hzg
      rw [heval]
      let v' : Point m := fun i => MvPolynomial.aeval z (F i)
      have hv' : v' ≠ 0 := hF z hz
      have htv' : t • v' ≠ 0 := smul_ne_zero ht0 hv'
      have hproj : Projectivization.mk ℂ (t • v') htv' = Projectivization.mk ℂ v' hv' :=
        (Projectivization.mk_eq_mk_iff' ℂ (t • v') v' htv' hv').mpr ⟨t, rfl⟩
      have hp' : Projectivization.mk ℂ v' hv' ∈ polynomialProjectiveImage X g F :=
        ⟨z, hz, hzg, hv', rfl⟩
      exact hf (t • v') ⟨htv', hproj.symm ▸ hp'⟩
    have hz := hx Q hQ
    rw [heval] at hz
    simpa only [← ht] using hz
  apply ProjectiveVariety.ext
  exact le_antisymm (transfer g h hg) (transfer h g hh)

/-- A nonempty polynomial source open where the actual graph differential
covers the target tangent and the carrier tangent has codimension one. -/
theorem ruling_good_source_open {e j N : ℕ} (C : SkewCoordinates e)
    (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (a : Fin e) (R : IsRulingIncidence C V Γ H a j N)
    (hj : j = 1)
    (hWdim : (TrackD.rationalImage Γ (rulingGraphPolynomials C) 1).dimension = e - 1) :
    ∃ g : Poly (skewDim e + e), g ∉ Γ.ideal ∧
      ∀ w ∈ Γ.points, MvPolynomial.aeval w g ≠ 0 →
        w ∈ rulingPoints Γ H ∧
        (Γ.tangentSpace w).map (rulingGraphDifferential C w) =
          (TrackD.rationalImage Γ (rulingGraphPolynomials C) 1).tangentSpace
            (graphVector C (firstPoint w) (secondPoint w)) ∧
        Module.finrank ℂ
          ((TrackD.rationalImage Γ (rulingGraphPolynomials C) 1).tangentSpace
            (graphVector C (firstPoint w) (secondPoint w))) = e - 1 ∧
        Module.finrank ℂ (V.tangentSpace (firstPoint w)) + 1 = skewDim e := by
  have h1 : (1 : Poly (skewDim e + e)) ∉ Γ.ideal :=
    Γ.ideal.ne_top_iff_one.mp R.incidence_irreducible.ne_top
  obtain ⟨_, gF, ⟨wF, hwF, hgF⟩, hF⟩ := TrackD.request_rational_image_generic_tangent
    Γ R.incidence_irreducible (rulingGraphPolynomials C) 1 h1
  obtain ⟨gV, ⟨zV, hzV, hgV⟩, hV⟩ := TrackD.general_tangent_finrank V R.variety_irreducible
  have hgFi : gF ∉ Γ.ideal := by intro hf; exact hgF (hwF _ hf)
  have hgVi : gV ∉ V.ideal := by intro hf; exact hgV (hzV _ hf)
  let g := (rulingOpenPolynomial H * gF) * rulingOpenPolynomial gV
  have hg : g ∉ Γ.ideal := by
    intro hmem
    rcases R.incidence_irreducible.mem_or_mem hmem with hmem | hmem
    · rcases R.incidence_irreducible.mem_or_mem hmem with hH | hF
      · exact rulingOpenPolynomial_not_mem C V Γ H a R hH
      · exact hgFi hF
    · exact ruling_base_polynomial_not_mem C V Γ H a R gV hgVi hmem
  refine ⟨g, hg, ?_⟩
  intro w hw hgw
  have hparts : (MvPolynomial.aeval w (rulingOpenPolynomial H) ≠ 0 ∧
      MvPolynomial.aeval w gF ≠ 0) ∧ MvPolynomial.aeval w (rulingOpenPolynomial gV) ≠ 0 := by
    simpa only [g, map_mul, mul_ne_zero_iff] using hgw
  have hwH : MvPolynomial.aeval (firstPoint w) H ≠ 0 := by
    simpa only [eval_rulingOpenPolynomial] using hparts.1.1
  have hwpV : MvPolynomial.aeval (firstPoint w) gV ≠ 0 := by
    simpa only [eval_rulingOpenPolynomial] using hparts.2
  have hgeneric := hF w hw hparts.1.2
  dsimp only at hgeneric
  have hrational : TrackD.rationalPoint (rulingGraphPolynomials C) 1 w =
      graphVector C (firstPoint w) (secondPoint w) := by
    funext i
    simp only [TrackD.rationalPoint, map_one, div_one]
    exact congrFun (eval_rulingGraphPolynomials C w) i
  rw [hrational, rationalDifferential_one] at hgeneric
  have hbase := hV (firstPoint w) (R.point_containment w hw) hwpV
  refine ⟨⟨hw, hwH⟩, hgeneric.2.1, hgeneric.2.2.trans hWdim, ?_⟩
  rw [hbase]
  exact R.codimension_one hj

end
end DistinctDistances.TrackB
