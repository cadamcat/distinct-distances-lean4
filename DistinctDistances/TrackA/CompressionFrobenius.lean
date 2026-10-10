import DistinctDistances.TrackA.CompressionDescent
import DistinctDistances.OAIInterface.PowerCover

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open OAI.PiExponent.PowerCover

def compressionPowerIdeal {n : ℕ} {F : Type*} [Field F] (z : FieldPoint n F) (p : ℕ) :
    Ideal (FieldPoly n F) :=
  Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i - MvPolynomial.C (z i))^p))

/-- In positive ambient dimension, np coordinate differences force one
coordinate to occur p times. The zero-dimensional case is handled separately. -/
theorem compression_point_pow_le {n : ℕ} {F : Type*} [Field F]
    (z : FieldPoint n F) (p : ℕ) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    pointIdealOver z ^ (n*p) ≤ compressionPowerIdeal z p := by
  rw [compression_pointIdeal_eq, OAI.PiExponent.WeightedBezout.pointIdeal_eq_span,
    compression_span_range_pow]
  apply Ideal.span_le.mpr
  rintro a ⟨e, rfl⟩
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, hi⟩ := Fintype.exists_le_card_fiber_of_mul_le_card e
    (show Fintype.card (Fin n) * p ≤ Fintype.card (Fin (n*p)) by simp)
  let t : Finset (Fin (n*p)) := Finset.univ.filter (fun j => e j = i)
  have ht : p ≤ t.card := hi
  let gen : Fin n → FieldPoly n F := fun j => MvPolynomial.X j - MvPolynomial.C (z j)
  have hprod : (∏ j ∈ t, gen (e j)) = (gen i)^t.card := by
    calc
      (∏ j ∈ t, gen (e j)) = ∏ _j ∈ t, gen i := by
        apply Finset.prod_congr rfl
        intro j hj
        exact congrArg gen (Finset.mem_filter.mp hj).2
      _ = (gen i)^t.card := by simp
  have hd : (gen i)^p ∣ ∏ j : Fin (n*p), gen (e j) := by
    apply (pow_dvd_pow (gen i) ht).trans
    rw [← hprod]
    exact Finset.prod_dvd_prod_of_subset t Finset.univ (fun j => gen (e j))
      (Finset.filter_subset _ _)
  obtain ⟨b, hb⟩ := hd
  change (∏ j : Fin (n*p), gen (e j)) ∈ compressionPowerIdeal z p
  rw [hb]
  exact (compressionPowerIdeal z p).mul_mem_right b (Ideal.subset_span ⟨i, rfl⟩)

theorem compression_quotient_degree {n : ℕ} (p : ℕ) (a : Fin n →₀ ℕ) :
    p * (quotient (fun _ => p) a).degree ≤ a.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa [quotient, Nat.mul_comm] using Nat.div_mul_le_self (a i) p

/-- Bounding a digit column uses only ordinary monomials, never a
denominator clearing argument. -/
theorem compression_digit_degree {n : ℕ} {F : Type*} [Field F]
    (p : ℕ) (hp : 0 < p) (P : FieldPoly n F) (r : Fin n → Fin p) :
    (decompositionAddEquiv (fun _ => p) (fun _ => hp) P r).totalDegree ≤ P.totalDegree/p := by
  have he : decompositionAddEquiv (fun _ => p) (fun _ => hp) P r =
      ∑ a ∈ P.support, if residue (fun _ => p) (fun _ => hp) a = r then
        MvPolynomial.monomial (quotient (fun _ => p) a) (P.coeff a) else 0 := by
    conv_lhs => rw [← P.support_sum_monomial_coeff]
    simp only [map_sum, decompositionAddEquiv_monomial, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
  apply OAI.QuarticPowerFree.mem_totalSpace.mp
  rw [he]
  apply Submodule.sum_mem
  intro a ha
  split_ifs
  · apply OAI.QuarticPowerFree.mem_totalSpace.mpr
    have hq : (quotient (fun _ => p) a).degree ≤ P.totalDegree/p := by
      apply (Nat.le_div_iff_mul_le hp).mpr
      have ha' : a.degree ≤ P.totalDegree := by
        simpa [Finsupp.degree_apply, Finsupp.sum] using MvPolynomial.le_totalDegree ha
      simpa only [Nat.mul_comm] using (compression_quotient_degree p a).trans ha'
    apply le_trans ?_ hq
    simpa [Finsupp.degree_apply, Finsupp.sum] using
      MvPolynomial.totalDegree_monomial_le (quotient (fun _ => p) a) (P.coeff a)
  · exact Submodule.zero_mem _

/-- OAI's power-cover basis reconstructs the polynomial from the actual
ordinary digit coefficient columns. -/
theorem compression_digit_reconstruction {n : ℕ} {F : Type*} [Field F]
    (p : ℕ) (hp : 0 < p) (P : FieldPoly n F) :
    P = ∑ r : Fin n → Fin p,
      MvPolynomial.monomial (combine (fun _ => p) (0, r)) 1 *
        powerSubstitution (fun _ => p)
          (decompositionAddEquiv (fun _ => p) (fun _ => hp) P r) := by
  let w : Fin n → ℕ := fun _ => p
  let hw : ∀ i, 0 < w i := fun _ => hp
  let v : PowerModule w F := (toPolynomial w).symm P
  have h := congrArg (toPolynomial w) ((basis (k := F) w hw).sum_repr v)
  simp only [map_sum, toPolynomial_smul, basis_toPolynomial] at h
  change (∑ r, powerSubstitution w (decompositionAddEquiv w hw P r) *
    MvPolynomial.monomial (combine w (0, r)) 1) = P at h
  simpa only [mul_comm] using h.symm

theorem compression_power_generator {n : ℕ} {F : Type*} [Field F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (z : FieldPoint n F) (i : Fin n) :
    (MvPolynomial.X i - MvPolynomial.C (z i))^p =
      powerSubstitution (fun _ => p) (MvPolynomial.X i - MvPolynomial.C ((z i)^p)) := by
  simp only [powerSubstitution, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have h := map_sub (frobenius (FieldPoly n F) p) (MvPolynomial.X i) (MvPolynomial.C (z i))
  change (MvPolynomial.X i - MvPolynomial.C (z i))^p =
    (MvPolynomial.X i)^p - (MvPolynomial.C (z i))^p at h
  have hc : (MvPolynomial.C (z i))^p = MvPolynomial.C ((z i)^p) :=
    (map_pow (MvPolynomial.C : F →+* FieldPoly n F) (z i) p).symm
  rw [hc] at h
  exact h

/-- A coordinate p-power ideal is the image of the base point ideal under
the power-cover algebra. Its coefficient columns therefore vanish on the base. -/
theorem compression_digit_vanish {n : ℕ} {F : Type*} [Field F]
    (p : ℕ) (hp : Nat.Prime p) [CharP F p] (P : FieldPoly n F) (z : FieldPoint n F)
    (hP : P ∈ compressionPowerIdeal z p) (r : Fin n → Fin p) :
    MvPolynomial.eval (fun i => (z i)^p)
      (decompositionAddEquiv (fun _ => p) (fun _ => hp.pos) P r) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hP
  have heP : P = ∑ i : Fin n,
      powerSubstitution (fun _ => p) (MvPolynomial.X i - MvPolynomial.C ((z i)^p)) * a i := by
    calc
      P = ∑ i, a i * (MvPolynomial.X i - MvPolynomial.C (z i))^p := ha.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [compression_power_generator p z i]
        exact mul_comm _ _
  have he : decompositionAddEquiv (fun _ => p) (fun _ => hp.pos) P r =
      ∑ i : Fin n, (MvPolynomial.X i - MvPolynomial.C ((z i)^p)) *
        decompositionAddEquiv (fun _ => p) (fun _ => hp.pos) (a i) r := by
    rw [heP]
    simp only [map_sum, decompositionAddEquiv_power_mul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  simp

/-- Inverse Frobenius turns the actual digit columns into pth-power
columns, preserving their degree bounds and their common zero set. -/
theorem compression_frobenius_columns {n : ℕ} {F : Type*} [Field F] [IsAlgClosed F]
    (p : ℕ) (hp : Nat.Prime p) [CharP F p] (P : FieldPoly n F) :
    ∃ h : (Fin n → Fin p) → FieldPoly n F,
      (∀ r, p*(h r).totalDegree ≤ P.totalDegree) ∧
      P = ∑ r : Fin n → Fin p, MvPolynomial.monomial (combine (fun _ => p) (0, r)) 1 * (h r)^p ∧
      ∀ z : FieldPoint n F, P ∈ compressionPowerIdeal z p →
        ∀ r, MvPolynomial.eval z (h r) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let invFrob : F →+* F := (frobeniusEquiv F p).symm.toRingHom
  let columns := decompositionAddEquiv (fun _ : Fin n => p) (fun _ => hp.pos) P
  let h : (Fin n → Fin p) → FieldPoly n F := fun r => MvPolynomial.map invFrob (columns r)
  have hmap (r) : MvPolynomial.map (frobenius F p) (h r) = columns r := by
    ext a
    simp only [h, MvPolynomial.coeff_map]
    change frobeniusEquiv F p ((frobeniusEquiv F p).symm ((columns r).coeff a)) = _
    exact (frobeniusEquiv F p).apply_symm_apply _
  have hfrob : (powerSubstitution (fun _ : Fin n => p)).toRingHom.comp
      (MvPolynomial.map (frobenius F p)) = frobenius (FieldPoly n F) p := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [powerSubstitution, frobenius_def]
    · intro i
      simp [powerSubstitution, frobenius_def]
  have hpow (r) : powerSubstitution (fun _ : Fin n => p) (columns r) = (h r)^p := by
    have he := congrArg (fun e : FieldPoly n F →+* FieldPoly n F => e (h r)) hfrob
    change powerSubstitution (fun _ => p) (MvPolynomial.map (frobenius F p) (h r)) = (h r)^p at he
    rwa [hmap] at he
  refine ⟨h, ?_, ?_, ?_⟩
  · intro r
    have hdeg : (h r).totalDegree ≤ P.totalDegree/p :=
      (compression_map_degree_le invFrob (columns r)).trans (compression_digit_degree p hp.pos P r)
    exact (Nat.mul_le_mul_left p hdeg).trans (by
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self P.totalDegree p)
  · rw [compression_digit_reconstruction p hp.pos P]
    apply Finset.sum_congr rfl
    intro r _
    rw [hpow]
  · intro z hz r
    have he := MvPolynomial.map_eval (frobenius F p) z (h r)
    change (MvPolynomial.eval z (h r))^p =
      MvPolynomial.eval (fun i => (z i)^p) (MvPolynomial.map (frobenius F p) (h r)) at he
    rw [hmap] at he
    exact eq_zero_of_pow_eq_zero (he.trans (compression_digit_vanish p hp P z hz r))

theorem compression_positive_characteristic_core {F : Type*} [Field F] [IsAlgClosed F]
    (n p : ℕ) (hp : Nat.Prime p) [CharP F p]
    (S : Finset (FieldPoint n F)) (x : FieldPoint n F) (f : FieldPoly n F)
    (E r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ p) (hf : f.totalDegree ≤ E)
    (horder : ∀ z ∈ S, OrderAtLeast f z r) (hx : MvPolynomial.eval x f ≠ 0) :
    ∃ g : FieldPoly n F, r*g.totalDegree ≤ (n+1)*E ∧
      (∀ z ∈ S, MvPolynomial.eval z g = 0) ∧ MvPolynomial.eval x g ≠ 0 := by
  by_cases hS : S.Nonempty
  · by_cases hn0 : n = 0
    · subst n
      obtain ⟨z, hz⟩ := hS
      have hi : pointIdealOver z = ⊥ := by
        rw [compression_pointIdeal_eq, OAI.PiExponent.WeightedBezout.pointIdeal_eq_span]
        simp
      have ho : f ∈ pointIdealOver z ^ r := horder z hz
      rw [hi] at ho
      have hle := (⊥ : Ideal (FieldPoly 0 F)).pow_le_pow_right hr
      have hf0 : f = 0 := by simpa only [pow_one, Submodule.mem_bot] using hle ho
      exact (hx (by simp [hf0])).elim
    · have hn : 1 ≤ n := by omega
      let m : ℕ := n*p/r+1
      let P : FieldPoly n F := f^m
      have hr0 : 0 < r := by omega
      have hnp : n*p ≤ r*m := by
        have hdiv := Nat.div_add_mod (n*p) r
        have hmod := Nat.mod_lt (n*p) hr0
        dsimp [m]
        nlinarith
      have hrm : r*m ≤ (n+1)*p := by
        have hd : r*(n*p/r) ≤ n*p := by
          simpa only [Nat.mul_comm] using Nat.div_mul_le_self (n*p) r
        calc
          r*m = r*(n*p/r)+r := by dsimp [m]; ring
          _ ≤ n*p+p := Nat.add_le_add hd hrp
          _ = (n+1)*p := by ring
      have hPdegree : P.totalDegree ≤ m*E :=
        (MvPolynomial.totalDegree_pow f m).trans (Nat.mul_le_mul_left m hf)
      have hPorder : ∀ z ∈ S, P ∈ compressionPowerIdeal z p := by
        intro z hz
        have ho : f ∈ pointIdealOver z ^ r := horder z hz
        have hom := Ideal.pow_mem_pow ho m
        rw [← pow_mul] at hom
        exact compression_point_pow_le z p hn hp.one_le
          ((pointIdealOver z).pow_le_pow_right hnp hom)
      obtain ⟨columns, hdegree, hrep, hzero⟩ := compression_frobenius_columns p hp P
      have hex : ∃ a, MvPolynomial.eval x (columns a) ≠ 0 := by
        by_contra! hvanish
        have hPx : MvPolynomial.eval x P = 0 := by
          rw [hrep]
          simp only [map_sum, map_mul, map_pow, hvanish, zero_pow hp.ne_zero, mul_zero,
            Finset.sum_const_zero]
        exact pow_ne_zero m hx (by simpa only [P, map_pow] using hPx)
      obtain ⟨a, ha⟩ := hex
      refine ⟨columns a, ?_, (fun z hz => hzero z (hPorder z hz) a), ha⟩
      have hd := (hdegree a).trans hPdegree
      have hbound : p*(r*(columns a).totalDegree) ≤ p*((n+1)*E) := by
        calc
          p*(r*(columns a).totalDegree) = r*(p*(columns a).totalDegree) := by ring
          _ ≤ r*(m*E) := Nat.mul_le_mul_left r hd
          _ = (r*m)*E := by ring
          _ ≤ ((n+1)*p)*E := Nat.mul_le_mul_right E hrm
          _ = p*((n+1)*E) := by ring
      exact le_of_mul_le_mul_left hbound hp.pos
  · refine ⟨1, by simp, ?_, by simp⟩
    intro z hz
    exact False.elim (hS ⟨z, hz⟩)

end
end DistinctDistances.TrackA
