import DistinctDistances.TrackA.RegularSectionDenominatorSupport
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- Homogeneous polynomial functions on the actual nonzero cone. This
space is finite because its source polynomial restriction space is finite. -/
def conePolynomialSpace {n : ℕ} (V : ProjectiveVariety n) (M : ℕ) :
    Submodule ℂ (NonzeroConePoint V → ℂ) :=
  (V.restrictionSpace M).map (coneEvaluation V)

instance conePolynomialSpace_finite {n : ℕ} (V : ProjectiveVariety n) (M : ℕ) :
    Module.Finite ℂ (conePolynomialSpace V M) := by
  unfold conePolynomialSpace
  infer_instance

theorem conePolynomialSpace_representation {n : ℕ} (V : ProjectiveVariety n) (M : ℕ)
    (u : conePolynomialSpace V M) :
    ∃ f : Poly n, f.IsHomogeneous M ∧ ∀ x, u.val x = MvPolynomial.eval x.val f := by
  obtain ⟨v, hv, hvu⟩ := Submodule.mem_map.mp u.property
  obtain ⟨f, hf, hfv⟩ := hv
  refine ⟨f, hf, ?_⟩
  intro x
  rw [← hvu, ← hfv]
  exact coneEvaluation_mk V f x

/-- Polynomial multiplication by a regular degree-zero section is an
endomorphism once the actual homogeneous polynomial space is stable. -/
def sectionPolynomialEnd {n : ℕ} (V : ProjectiveVariety n)
    (s : regularSectionSpace V 0) (M : ℕ)
    (hstable : ∀ f : Poly n, f.IsHomogeneous M → ∃ g : Poly n,
      g.IsHomogeneous M ∧ ∀ x, s.val x * MvPolynomial.eval x.val f = MvPolynomial.eval x.val g) :
    Module.End ℂ (conePolynomialSpace V M) where
  toFun u := ⟨fun x => s.val x * u.val x, by
    obtain ⟨f, hf, hu⟩ := conePolynomialSpace_representation V M u
    obtain ⟨g, hg, he⟩ := hstable f hf
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk V.ideal g, ⟨g, hg, rfl⟩, ?_⟩
    funext x
    rw [coneEvaluation_mk, hu x, he x]⟩
  map_add' := by
    intro u v
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' := by
    intro c u
    apply Subtype.ext
    funext x
    change s.val x * (c*u.val x) = c*(s.val x*u.val x)
    ring

theorem conePolynomialSpace_nontrivial {n : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (M : ℕ) : Nontrivial (conePolynomialSpace V M) := by
  obtain ⟨p, hp⟩ := ProjectiveFamily.irreducible_points_nonempty V hV
  let x : NonzeroConePoint V := ⟨p.rep, p.rep_nonzero,
    (ProjectiveVariety.mem_points_mk_iff V p.rep p.rep_nonzero).mp (by simpa using hp)⟩
  have hi : ∃ i, x.val i ≠ 0 := by
    by_contra h
    push Not at h
    exact x.property.1 (funext h)
  obtain ⟨i, hi⟩ := hi
  let f : Poly n := MvPolynomial.X i ^ M
  have hf : f.IsHomogeneous M := by simpa [f] using (MvPolynomial.isHomogeneous_X ℂ i).pow M
  let u : conePolynomialSpace V M := ⟨coneEvaluation V (Ideal.Quotient.mk V.ideal f),
    Submodule.mem_map.mpr ⟨Ideal.Quotient.mk V.ideal f, ⟨f, hf, rfl⟩, rfl⟩⟩
  have hu : u ≠ 0 := by
    intro h
    have hx := congrFun (congrArg Subtype.val h) x
    change coneEvaluation V (Ideal.Quotient.mk V.ideal f) x = 0 at hx
    rw [coneEvaluation_mk] at hx
    have hfne : MvPolynomial.eval x.val f ≠ 0 := by
      simpa [f] using pow_ne_zero M hi
    exact hfne hx
  exact ⟨⟨u, 0, hu⟩⟩

/-- A degree-zero regular section on an irreducible projective variety
is constant. An eigenvector in a sufficiently high polynomial degree
and primality turn the eigenvalue into the section's value everywhere. -/
theorem regularSection_zero_constant {n : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (s : regularSectionSpace V 0) :
    ∃ c : ℂ, ∀ x, s.val x = c := by
  obtain ⟨M, hM⟩ := regularSection_eventually_polynomial_multiplication V hV s
  have hstable : ∀ f : Poly n, f.IsHomogeneous M → ∃ g : Poly n,
      g.IsHomogeneous M ∧ ∀ x, s.val x * MvPolynomial.eval x.val f = MvPolynomial.eval x.val g := by
    intro f hf
    simpa only [Nat.add_zero] using hM M le_rfl f hf
  let T := sectionPolynomialEnd V s M hstable
  haveI := conePolynomialSpace_nontrivial V hV M
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨u, hu⟩ := hc.exists_hasEigenvector
  obtain ⟨f, hf, huf⟩ := conePolynomialSpace_representation V M u
  have hfI : f ∉ V.ideal := by
    intro hfI
    apply hu.2
    apply Subtype.ext
    funext x
    rw [huf x]
    change MvPolynomial.eval x.val f = 0
    simpa only [MvPolynomial.aeval_eq_eval] using x.property.2 f hfI
  have heigen : ∀ x, s.val x * MvPolynomial.eval x.val f = c * MvPolynomial.eval x.val f := by
    intro x
    have he := congrFun (congrArg Subtype.val hu.apply_eq_smul) x
    change s.val x * u.val x = c * u.val x at he
    rwa [huf x] at he
  refine ⟨c, ?_⟩
  intro x
  have hs : IsRegularHomogeneousSection V 0 s.val := s.property
  obtain ⟨q, a, b, _, _, hb, ha⟩ := hs x
  have hbI : b ∉ V.ideal := by
    intro hbI
    exact hb (by simpa only [MvPolynomial.aeval_eq_eval] using x.property.2 b hbI)
  have hcf : ∀ y, MvPolynomial.eval y.val f ≠ 0 →
      s.val y * MvPolynomial.eval y.val f = MvPolynomial.eval y.val (MvPolynomial.C c * f) := by
    intro y hy
    simpa only [map_mul, MvPolynomial.eval_C] using heigen y
  have hcross := cone_fraction_cross_mem V hV s.val a b (MvPolynomial.C c * f) f hbI hfI ha hcf
  have hprod : (a-MvPolynomial.C c*b)*f ∈ V.ideal := by
    convert hcross using 1 <;> ring
  have hscalar : a-MvPolynomial.C c*b ∈ V.ideal := (hV.mem_or_mem hprod).resolve_right hfI
  have heval : MvPolynomial.eval x.val a = c * MvPolynomial.eval x.val b := by
    have hz := x.property.2 (a-MvPolynomial.C c*b) hscalar
    simpa only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.aeval_eq_eval, sub_eq_zero] using hz
  apply mul_right_cancel₀ hb
  exact (ha x hb).trans heval

theorem projective_family_member_subvariety {n : ℕ} (F : ProjectiveFamily.Family n)
    (V : ProjectiveVariety n) (hV : V ∈ F) : V.Subvariety (ProjectiveFamily.locus F) := by
  change ProjectiveVariety.vanishingIdeal (⋃ W ∈ F, W.points) ≤ V.ideal
  rw [← V.vanishingIdeal_points]
  apply MvPolynomial.vanishingIdeal_anti_mono
  rintro x ⟨hx0, hxV⟩
  exact ⟨hx0, Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨hV, hxV⟩⟩⟩

/-- One evaluation per irreducible component detects every actual
degree-zero section on a finite projective union. -/
theorem regularSection_family_zero_evaluation {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) :
    ∃ ev : regularSectionSpace (ProjectiveFamily.locus F) 0 →ₗ[ℂ] (F → ℂ),
      Function.Injective ev := by
  let p : (V : F) → NonzeroConePoint V.val := fun V => by
    let q := Classical.choose (ProjectiveFamily.irreducible_points_nonempty V.val (hF V.val V.property))
    have hq := Classical.choose_spec (ProjectiveFamily.irreducible_points_nonempty V.val (hF V.val V.property))
    exact ⟨q.rep, q.rep_nonzero,
      (ProjectiveVariety.mem_points_mk_iff V.val q.rep q.rep_nonzero).mp (by simpa using hq)⟩
  let hsub := fun V : F => projective_family_member_subvariety F V.val V.property
  let pF : F → NonzeroConePoint (ProjectiveFamily.locus F) := fun V =>
    nonzeroConeInclusion (ProjectiveFamily.locus F) V.val (hsub V) (p V)
  let ev : regularSectionSpace (ProjectiveFamily.locus F) 0 →ₗ[ℂ] (F → ℂ) :=
    LinearMap.pi (fun V => (LinearMap.proj (pF V)).comp
      (regularSectionSpace (ProjectiveFamily.locus F) 0).subtype)
  refine ⟨ev, ?_⟩
  intro s t he
  apply Subtype.ext
  funext x
  have hxF : Projectivization.mk ℂ x.val x.property.1 ∈ (ProjectiveFamily.locus F).points :=
    (ProjectiveVariety.mem_points_mk_iff _ x.val x.property.1).mpr x.property.2
  rw [ProjectiveFamily.points_locus] at hxF
  simp only [Set.mem_iUnion] at hxF
  obtain ⟨V, hV, hxV⟩ := hxF
  let v : F := ⟨V, hV⟩
  let y : NonzeroConePoint V := ⟨x.val, x.property.1,
    (ProjectiveVariety.mem_points_mk_iff V x.val x.property.1).mp hxV⟩
  let sV := sectionRestriction (ProjectiveFamily.locus F) V (hsub v) 0 s
  let tV := sectionRestriction (ProjectiveFamily.locus F) V (hsub v) 0 t
  obtain ⟨cs, hcs⟩ := regularSection_zero_constant V (hF V hV) sV
  obtain ⟨ct, hct⟩ := regularSection_zero_constant V (hF V hV) tV
  have hsame := congrFun he v
  change s.val (pF v) = t.val (pF v) at hsame
  have hcc : cs = ct := by
    calc
      cs = s.val (pF v) := (hcs (p v)).symm
      _ = t.val (pF v) := hsame
      _ = ct := hct (p v)
  calc
    s.val x = cs := hcs y
    _ = ct := hcc
    _ = t.val x := (hct y).symm

/-- Finiteness at degree zero follows from the actual component evaluation
injection, independently of the open general section-finiteness request. -/
theorem regularSection_family_zero_finite {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) :
    Module.Finite ℂ (regularSectionSpace (ProjectiveFamily.locus F) 0) := by
  obtain ⟨ev, he⟩ := regularSection_family_zero_evaluation F hF
  exact Module.Finite.of_injective ev he

theorem regularSection_family_zero_le_card {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) :
    Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) 0) ≤ F.card := by
  obtain ⟨ev, he⟩ := regularSection_family_zero_evaluation F hF
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
    LinearMap.finrank_le_finrank_of_injective he

/-- Constant regular sections on each component bound the entire
degree-zero section space by the exact total component degree. -/
theorem regularSection_family_zero_bound {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) :
    (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) 0) : ℚ) ≤
      ProjectiveFamily.degree F := by
  calc
    (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) 0) : ℚ) ≤
        (F.card : ℚ) := by exact_mod_cast regularSection_family_zero_le_card F hF
    _ = ∑ V ∈ F, (1 : ℚ) := by simp
    _ ≤ ∑ V ∈ F, V.degree := by
      apply Finset.sum_le_sum
      intro V hV
      rw [← V.degree_cone]
      exact V.affineCone.one_le_degree (hF V hV).ne_top
    _ = ProjectiveFamily.degree F := rfl

end
end DistinctDistances.TrackA
