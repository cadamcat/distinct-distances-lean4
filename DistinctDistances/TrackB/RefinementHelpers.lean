import DistinctDistances.Foundations
import Mathlib.Algebra.Module.Submodule.Union

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

/-- B30, concentration.tex:1047–1049. Choose an actual least-degree nonzero equation. -/
theorem least_degree_equation {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (seed : Poly n) (hseed : seed ≠ 0) (hseedV : seed ∈ V.ideal) :
    ∃ q : Poly n, q ≠ 0 ∧ q ∈ V.ideal ∧ 0 < q.totalDegree ∧
      ∀ f : Poly n, f ≠ 0 → f ∈ V.ideal → q.totalDegree ≤ f.totalDegree := by
  classical
  let P : ℕ → Prop := fun d => ∃ q : Poly n, q ≠ 0 ∧ q ∈ V.ideal ∧ q.totalDegree = d
  have hP : ∃ d, P d := ⟨seed.totalDegree, seed, hseed, hseedV, rfl⟩
  let d := Nat.find hP
  have hd : P d := by
    exact Nat.find_spec hP
  obtain ⟨q, hq, hqV, hqd⟩ := hd
  have hmin : ∀ f : Poly n, f ≠ 0 → f ∈ V.ideal → d ≤ f.totalDegree := by
    intro f hf hVf
    apply Nat.find_min' hP
    exact ⟨f, hf, hVf, rfl⟩
  have hpos : 0 < q.totalDegree := by
    by_contra hnot
    have hzero : q.totalDegree = 0 := by omega
    have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
    have ha : q.coeff 0 ≠ 0 := by
      intro hz
      apply hq
      rw [heq, hz, MvPolynomial.C_0]
    have hunit : IsUnit (MvPolynomial.C (q.coeff 0) : Poly n) :=
      (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
    exact hV.ne_top (V.ideal.eq_top_of_isUnit_mem (heq ▸ hqV) hunit)
  refine ⟨q, hq, hqV, hpos, ?_⟩
  intro f hf hfV
  rw [hqd]
  exact hmin f hf hfV

def constantPrefixCombination {n c : ℕ} (f : Fin c → Poly n) (i : Fin c)
    (a : Fin c → ℂ) : Poly n :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin c => j.val ≤ i.val), MvPolynomial.C (a j) * f j

/-- B30, concentration.tex:1055–1056. Constant coefficients preserve the prefix's
degree bound and vanishing on V, even when the resulting polynomial is zero. -/
theorem constantPrefixCombination_bounds {n c : ℕ} (V : AffineVariety n)
    (f : Fin c → Poly n) (d : Fin c → ℕ) (hd : Monotone d)
    (hdegree : ∀ j, (f j).totalDegree ≤ d j) (hvanish : ∀ j, f j ∈ V.ideal)
    (i : Fin c) (a : Fin c → ℂ) :
    (constantPrefixCombination f i a).totalDegree ≤ d i ∧
      constantPrefixCombination f i a ∈ V.ideal := by
  constructor
  · unfold constantPrefixCombination
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    have hj' : j.val ≤ i.val := (Finset.mem_filter.mp hj).2
    have hdeg : (f j).totalDegree ≤ d i := (hdegree j).trans (hd hj')
    calc
      (MvPolynomial.C (a j) * f j).totalDegree ≤
          (MvPolynomial.C (a j)).totalDegree + (f j).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = (f j).totalDegree := by simp
      _ ≤ d i := hdeg
  · unfold constantPrefixCombination
    apply Ideal.sum_mem
    intro j hj
    exact Ideal.mul_mem_left _ _ (hvanish j)

/-- B30, concentration.tex:1051–1056. A generic constant combination avoids each
of finitely many ideals, provided the prefix is not contained in any of them. -/
theorem constantPrefixCombination_avoid {n c : ℕ} (f : Fin c → Poly n) (i : Fin c)
    (S : Finset (Ideal (Poly n)))
    (hproper : ∀ Q ∈ S, ∃ j : Fin c, j.val ≤ i.val ∧ f j ∉ Q) :
    ∃ a : Fin c → ℂ, ∀ Q ∈ S, constantPrefixCombination f i a ∉ Q := by
  classical
  let L : (Fin c → ℂ) →ₗ[ℂ] Poly n :=
    { toFun := fun a =>
        ∑ j ∈ Finset.univ.filter (fun j : Fin c => j.val ≤ i.val), a j • f j
      map_add' := by
        intro a b
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
          RingHom.id_apply] }
  have hL (a : Fin c → ℂ) : L a = constantPrefixCombination f i a := by
    simp [L, constantPrefixCombination, MvPolynomial.C_mul']
  let bad : {Q : Ideal (Poly n) // Q ∈ S} → Submodule ℂ (Fin c → ℂ) :=
    fun Q => Submodule.comap L (Q.1.restrictScalars ℂ)
  have hbad : ∀ Q, bad Q ≠ ⊤ := by
    intro Q htop
    obtain ⟨j, hj, hjnot⟩ := hproper Q.1 Q.2
    let e : Fin c → ℂ := fun k => if k = j then 1 else 0
    have hjmem : j ∈ Finset.univ.filter (fun k : Fin c => k.val ≤ i.val) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hLe : L e = f j := by
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, e]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k hk hkj
        simp [hkj]
      · intro hnot
        exact (hnot (by simpa using hjmem)).elim
    have he : e ∈ bad Q := by
      rw [htop]
      exact Submodule.mem_top
    have hmem : f j ∈ Q.1 := by
      have he' : L e ∈ Q.1 := by simpa [bad] using he
      exact hLe ▸ he'
    exact hjnot hmem
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨a, ?_⟩
  intro Q hQ hmem
  have haQ : a ∉ bad ⟨Q, hQ⟩ := ha ⟨Q, hQ⟩
  apply haQ
  simpa only [bad, Submodule.mem_comap, Submodule.restrictScalars_mem, hL] using hmem

end
end DistinctDistances.TrackB
