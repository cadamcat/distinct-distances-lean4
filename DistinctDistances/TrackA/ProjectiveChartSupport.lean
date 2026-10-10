import DistinctDistances.Foundations.LocalHilbert
import DistinctDistances.Bridges.ProjectiveEnvelope
import Mathlib.Algebra.Module.Submodule.Union

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveLinearSlice {n : ℕ} (V : ProjectiveVariety n) (ℓ : Poly n) :
    AffineVariety n := AffineVariety.ofIdeal (V.ideal ⊔ Ideal.span {ℓ - 1})

theorem linearSlice_points {n : ℕ} (V : ProjectiveVariety n) (ℓ : Poly n)
    (x : Point n) :
    x ∈ (projectiveLinearSlice V ℓ).points ↔
      x ∈ V.affineCone.points ∧ MvPolynomial.eval x ℓ = 1 := by
  rw [projectiveLinearSlice, AffineVariety.points_ofIdeal]
  constructor
  · intro hx
    refine ⟨fun f hf => hx f (Ideal.mem_sup_left hf), ?_⟩
    have h := hx (ℓ - 1) (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
    simpa only [map_sub, map_one, sub_eq_zero, MvPolynomial.aeval_eq_eval] using h
  · rintro ⟨hx, hℓ⟩
    have hI : V.ideal ≤ MvPolynomial.vanishingIdeal ℂ {x} := by
      intro f hf
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).2 (hx f hf)
    have hℓI : Ideal.span {ℓ - 1} ≤ MvPolynomial.vanishingIdeal ℂ {x} := by
      apply Ideal.span_le.mpr
      rintro f rfl
      apply (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).2
      simpa only [MvPolynomial.aeval_eq_eval, map_sub, map_one, hℓ, sub_self]
    intro f hf
    exact (sup_le hI hℓI hf) x rfl

theorem cone_smul_mem {n : ℕ} (V : ProjectiveVariety n) (x : Point n)
    (hx : x ∈ V.affineCone.points) (c : ℂ) : c • x ∈ V.affineCone.points := by
  intro f hf
  rw [← MvPolynomial.sum_homogeneousComponent f]
  simp only [map_sum, MvPolynomial.aeval_eq_eval]
  apply Finset.sum_eq_zero
  intro d hd
  rw [Bridges.homogeneous_eval_smul _ (MvPolynomial.homogeneousComponent_isHomogeneous d f)]
  have hfI := MvPolynomial.homogeneousComponent_mem_of_mem V.isHomogeneous hf d
  have hz := hx (MvPolynomial.homogeneousComponent d f) hfI
  have hz' : MvPolynomial.eval x (MvPolynomial.homogeneousComponent d f) = 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using hz
  rw [hz', mul_zero]

def chartHomogenize {n : ℕ} (ℓ : Poly n) (D : ℕ) (f : Poly n) : Poly n :=
  ∑ i ∈ Finset.range (D + 1), ℓ ^ (D-i) * MvPolynomial.homogeneousComponent i f

theorem chartHomogenize_homogeneous {n D : ℕ} (ℓ f : Poly n)
    (hℓ : ℓ.IsHomogeneous 1) : (chartHomogenize ℓ D f).IsHomogeneous D := by
  unfold chartHomogenize
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have hiD : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hp := hℓ.pow (D-i)
  have hf := MvPolynomial.homogeneousComponent_isHomogeneous i f
  convert hp.mul hf using 1 <;> omega

theorem chart_components_sum {n D : ℕ} (f : Poly n) (hf : f.totalDegree ≤ D) :
    ∑ i ∈ Finset.range (D+1), MvPolynomial.homogeneousComponent i f = f := by
  calc
    _ = ∑ i ∈ Finset.range (f.totalDegree+1), MvPolynomial.homogeneousComponent i f := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hf))
      intro i hi hnot
      have hnot' := (Finset.mem_range.not).mp hnot
      exact MvPolynomial.homogeneousComponent_eq_zero i f (by omega)
    _ = f := MvPolynomial.sum_homogeneousComponent f

theorem chartHomogenize_mod {n D : ℕ} (ℓ f : Poly n) (hf : f.totalDegree ≤ D)
    (I : Ideal (Poly n)) (hℓ : ℓ - 1 ∈ I) :
    Ideal.Quotient.mk I (chartHomogenize ℓ D f) = Ideal.Quotient.mk I f := by
  have hℓq : Ideal.Quotient.mk I ℓ = 1 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hℓ
    simpa only [map_sub, map_one, sub_eq_zero] using h
  simp only [chartHomogenize, map_sum, map_mul, map_pow, hℓq, one_pow, one_mul]
  rw [← map_sum, chart_components_sum f hf]

theorem chartHomogenize_eval {n D : ℕ} (ℓ f : Poly n) (hf : f.totalDegree ≤ D)
    (x : Point n) (hℓ : MvPolynomial.eval x ℓ = 1) :
    MvPolynomial.eval x (chartHomogenize ℓ D f) = MvPolynomial.eval x f := by
  simp only [chartHomogenize, map_sum, map_mul, map_pow, hℓ, one_pow, one_mul]
  rw [← map_sum, chart_components_sum f hf]

theorem homogeneous_mem_linearSlice_iff {n d : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (ℓ f : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓV : ℓ ∉ V.ideal) (hf : f.IsHomogeneous d) :
    f ∈ (projectiveLinearSlice V ℓ).ideal ↔ f ∈ V.ideal := by
  constructor
  · intro hfs
    by_contra hfV
    have hprod : ℓ * f ∉ V.ideal := by
      intro h
      exact (hV.mem_or_mem h).elim hℓV hfV
    change ℓ * f ∉ V.affineCone.ideal at hprod
    rw [← AffineVariety.vanishingIdeal_points V.affineCone] at hprod
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hprod
    push Not at hprod
    obtain ⟨x, hx, hxf⟩ := hprod
    have hne : MvPolynomial.eval x ℓ * MvPolynomial.eval x f ≠ 0 := by
      simpa only [map_mul, MvPolynomial.aeval_eq_eval] using hxf
    have hxℓ : MvPolynomial.eval x ℓ ≠ 0 := (mul_ne_zero_iff.mp hne).1
    have hxf' : MvPolynomial.eval x f ≠ 0 := (mul_ne_zero_iff.mp hne).2
    let c : ℂ := (MvPolynomial.eval x ℓ)⁻¹
    have hc : c ≠ 0 := inv_ne_zero hxℓ
    have hy : c • x ∈ (projectiveLinearSlice V ℓ).points := by
      apply (linearSlice_points V ℓ _).2
      refine ⟨cone_smul_mem V x hx c, ?_⟩
      rw [Bridges.homogeneous_eval_smul ℓ hℓ]
      simpa only [pow_one, c] using inv_mul_cancel₀ hxℓ
    have hz := hy f hfs
    have hz' : c ^ d * MvPolynomial.eval x f = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval,
        Bridges.homogeneous_eval_smul f hf] using hz
    exact (mul_ne_zero (pow_ne_zero d hc) hxf') hz'
  · intro hfV
    exact Ideal.le_radical (Ideal.mem_sup_left hfV)

theorem chartHomogenize_mem_iff {n D : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (ℓ f : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓV : ℓ ∉ V.ideal) (hf : f.totalDegree ≤ D) :
    f ∈ (projectiveLinearSlice V ℓ).ideal ↔ chartHomogenize ℓ D f ∈ V.ideal := by
  rw [← homogeneous_mem_linearSlice_iff V hV ℓ _ hℓ hℓV
    (chartHomogenize_homogeneous ℓ f hℓ)]
  have hmod := chartHomogenize_mod ℓ f hf (projectiveLinearSlice V ℓ).ideal
    (Ideal.le_radical (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))))
  simp only [← Ideal.Quotient.eq_zero_iff_mem, hmod]

theorem linearSlice_ideal {n : ℕ} (V : ProjectiveVariety n) (hV : V.IsIrreducible)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (hℓV : ℓ ∉ V.ideal) :
    (projectiveLinearSlice V ℓ).ideal = V.ideal ⊔ Ideal.span {ℓ - 1} := by
  apply le_antisymm
  · intro f hf
    have hpad := (chartHomogenize_mem_iff V hV ℓ f hℓ hℓV le_rfl).1 hf
    let I := V.ideal ⊔ Ideal.span {ℓ - 1}
    have hmod := chartHomogenize_mod ℓ f le_rfl I
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hmod]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hpad)
  · exact Ideal.le_radical

theorem linearSlice_irreducible {n : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓV : ℓ ∉ V.ideal) : (projectiveLinearSlice V ℓ).IsIrreducible := by
  refine ⟨?_, ?_⟩
  · intro htop
    have hone : (1 : Poly n) ∈ (projectiveLinearSlice V ℓ).ideal := by
      rw [htop]
      trivial
    exact hV.one_notMem ((homogeneous_mem_linearSlice_iff V hV ℓ 1 hℓ hℓV
      (MvPolynomial.isHomogeneous_one _ _)).1 hone)
  · intro f g hfg
    let f' := chartHomogenize ℓ f.totalDegree f
    let g' := chartHomogenize ℓ g.totalDegree g
    have hf' : f'.IsHomogeneous f.totalDegree := chartHomogenize_homogeneous ℓ f hℓ
    have hg' : g'.IsHomogeneous g.totalDegree := chartHomogenize_homogeneous ℓ g hℓ
    have hfg' : f' * g' ∈ (projectiveLinearSlice V ℓ).ideal := by
      rw [← AffineVariety.vanishingIdeal_points]
      intro x hx
      have hxℓ := ((linearSlice_points V ℓ x).1 hx).2
      have hz := hx (f*g) hfg
      change MvPolynomial.eval x (f'*g') = 0
      dsimp [f', g']
      rw [map_mul, chartHomogenize_eval ℓ f le_rfl x hxℓ,
        chartHomogenize_eval ℓ g le_rfl x hxℓ]
      simpa only [map_mul, MvPolynomial.aeval_eq_eval] using hz
    have hfgI := (homogeneous_mem_linearSlice_iff V hV ℓ _ hℓ hℓV (hf'.mul hg')).1 hfg'
    rcases hV.mem_or_mem hfgI with hf | hg
    · exact Or.inl ((chartHomogenize_mem_iff V hV ℓ f hℓ hℓV le_rfl).2 hf)
    · exact Or.inr ((chartHomogenize_mem_iff V hV ℓ g hℓ hℓV le_rfl).2 hg)

end
end DistinctDistances.TrackA
