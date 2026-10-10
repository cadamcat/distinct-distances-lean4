import DistinctDistances.TrackC.Basic
import OAI.Geometry.Borsuk.Simplicial.UnitRadial
import OAI.NumberTheory.PowerFree.HilbertGrowth

open scoped BigOperators
open Classical

namespace DistinctDistances.TrackC

private noncomputable def affineFlatBase {n k : ℕ} (h : Flat n k) : E n :=
  h.2.1.choose

private theorem affineFlatBase_mem {n k : ℕ} (h : Flat n k) : affineFlatBase h ∈ h.1 :=
  h.2.1.choose_spec

private noncomputable def affineFlatCoordinates {n k : ℕ} (h : Flat n k) :
    (Fin k → ℝ) ≃ₗ[ℝ] h.1.direction :=
  Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by simpa [h.2.2]))

private noncomputable def affineFlatLinearPart {n k : ℕ} (h : Flat n k) :
    (Fin k → ℝ) →ₗ[ℝ] E n :=
  h.1.direction.subtype.comp (affineFlatCoordinates h).toLinearMap

private theorem affineFlatLinearPart_sum {n k : ℕ} (h : Flat n k) (y : Fin k → ℝ) :
    affineFlatLinearPart h y =
      ∑ j : Fin k, y j • affineFlatLinearPart h (Pi.single j 1) := by
  have hy : y = ∑ j : Fin k, y j • (Pi.single j (1 : ℝ)) := pi_eq_sum_univ' y
  calc
    affineFlatLinearPart h y =
        affineFlatLinearPart h (∑ j : Fin k, y j • Pi.single j 1) := congrArg _ hy
    _ = ∑ j : Fin k, y j • affineFlatLinearPart h (Pi.single j 1) := by
      rw [map_sum]
      simp only [map_smul]

private noncomputable def affineFlatSubstitution {n k : ℕ} (h : Flat n k) :
    Fin n → Poly k := fun i =>
      MvPolynomial.C (affineFlatBase h i) +
        ∑ j : Fin k,
          MvPolynomial.X j * MvPolynomial.C (affineFlatLinearPart h (Pi.single j 1) i)

private theorem affineFlatSubstitution_degree {n k : ℕ} (h : Flat n k) (i : Fin n) :
    (affineFlatSubstitution h i).totalDegree ≤ 1 := by
  unfold affineFlatSubstitution
  have hsum :
      (∑ j : Fin k,
        MvPolynomial.X j * MvPolynomial.C (affineFlatLinearPart h (Pi.single j 1) i)).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    calc
      (MvPolynomial.X j * MvPolynomial.C (affineFlatLinearPart h (Pi.single j 1) i)).totalDegree ≤
          (MvPolynomial.X j).totalDegree +
            (MvPolynomial.C (affineFlatLinearPart h (Pi.single j 1) i)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = 1 := by simp
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) hsum)

private theorem affineSubstitution_monomial_degree_le {n k : ℕ}
    (g : Fin n → Poly k) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (s : Fin n →₀ ℕ) (a : ℝ) :
    (MvPolynomial.aeval g (MvPolynomial.monomial s a)).totalDegree ≤ s.sum (fun _ e => e) := by
  rw [MvPolynomial.aeval_monomial]
  have hconst : (algebraMap ℝ (Poly k) a).totalDegree = 0 := by simp
  calc
    (algebraMap ℝ (Poly k) a * s.prod (fun i e => g i ^ e)).totalDegree ≤
        (algebraMap ℝ (Poly k) a).totalDegree +
          (s.prod (fun i e => g i ^ e)).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ ∑ i ∈ s.support, s i := by
      rw [hconst, zero_add]
      calc
        (s.prod (fun i e => g i ^ e)).totalDegree ≤
            ∑ i ∈ s.support, (g i ^ s i).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ i ∈ s.support, s i := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            (g i ^ s i).totalDegree ≤ s i * (g i).totalDegree :=
              MvPolynomial.totalDegree_pow (g i) (s i)
            _ ≤ s i := by simpa using Nat.mul_le_mul_left (s i) (hg i)
    _ = s.sum (fun _ e => e) := rfl

set_option maxHeartbeats 500000 in
private theorem affineSubstitution_totalDegree_le {n k : ℕ} (g : Fin n → Poly k)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (f : Poly n) :
    (MvPolynomial.aeval g f).totalDegree ≤ f.totalDegree := by
  classical
  have hsum : MvPolynomial.aeval g f =
      ∑ s ∈ f.support, MvPolynomial.aeval g (MvPolynomial.monomial s (f.coeff s)) := by
    calc
      MvPolynomial.aeval g f =
          MvPolynomial.aeval g (∑ s ∈ f.support, MvPolynomial.monomial s (f.coeff s)) :=
        congrArg (MvPolynomial.aeval g) (MvPolynomial.as_sum f)
      _ = ∑ s ∈ f.support, MvPolynomial.aeval g (MvPolynomial.monomial s (f.coeff s)) :=
        map_sum (MvPolynomial.aeval g) (fun s => MvPolynomial.monomial s (f.coeff s)) f.support
  rw [hsum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  exact (affineSubstitution_monomial_degree_le g hg s (f.coeff s)).trans
    (MvPolynomial.le_totalDegree hs)

private theorem affineFlatSubstitution_eval {n k : ℕ} (h : Flat n k) (f : Poly n)
    (y : Fin k → ℝ) :
    MvPolynomial.eval y (MvPolynomial.aeval (affineFlatSubstitution h) f) =
      evalR f (affineFlatBase h + affineFlatLinearPart h y) := by
  classical
  rw [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_comp_left]
  have hcoeff :
      (MvPolynomial.eval y).comp (algebraMap ℝ (Poly k)) = RingHom.id ℝ := by
    ext a
    simp
  rw [hcoeff]
  change MvPolynomial.eval₂ (RingHom.id ℝ)
      (fun i => MvPolynomial.eval y (affineFlatSubstitution h i)) f = _
  have hvars :
      (fun i => MvPolynomial.eval y (affineFlatSubstitution h i)) =
        (fun i => (affineFlatBase h + affineFlatLinearPart h y) i) := by
    funext i
    rw [affineFlatSubstitution]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [affineFlatLinearPart_sum]
    simp [PiLp.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hvars]
  rfl

private noncomputable def affineFlatRestriction {n k : ℕ} (h : Flat n k) :
    Poly n →ₗ[ℝ] Poly k :=
  (MvPolynomial.aeval (affineFlatSubstitution h)).toLinearMap

private noncomputable def affineFlatRestrictionBounded {n k D : ℕ} (h : Flat n k) :
    OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℝ) D →ₗ[ℝ]
      OAI.QuarticPowerFree.totalSpace (σ := Fin k) (K := ℝ) D := by
  let L := affineFlatRestriction h
  exact (L.domRestrict (OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℝ) D)).codRestrict
    (OAI.QuarticPowerFree.totalSpace (σ := Fin k) (K := ℝ) D)
    (fun p => OAI.QuarticPowerFree.mem_totalSpace.mpr <|
      (affineSubstitution_totalDegree_le (affineFlatSubstitution h)
        (affineFlatSubstitution_degree h) p.1).trans
          (OAI.QuarticPowerFree.mem_totalSpace.mp p.2))

private noncomputable def affineFlatRestrictionFamily {n k D : ℕ}
    (H : Finset (Flat n k)) :
    OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℝ) D →ₗ[ℝ]
      (∀ h : {h // h ∈ H}, OAI.QuarticPowerFree.totalSpace (σ := Fin k) (K := ℝ) D) :=
    LinearMap.pi (fun h => affineFlatRestrictionBounded h.1)

theorem flatInterpolationAux {n k D : ℕ} (H : Finset (Flat n k))
    (hsize : H.card * Nat.choose (D + k) k < Nat.choose (D + n) n) :
    ∃ f : Poly n, f ≠ 0 ∧ f.totalDegree ≤ D ∧ ∀ h ∈ H, onPolynomial f h := by
  classical
  let V := OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℝ) D
  let W := OAI.QuarticPowerFree.totalSpace (σ := Fin k) (K := ℝ) D
  letI : Module.Finite ℝ V := OAI.QuarticPowerFree.totalSpace_finite D
  letI : Module.Finite ℝ W := OAI.QuarticPowerFree.totalSpace_finite D
  letI : Fintype {h // h ∈ H} := Finset.Subtype.fintype H
  letI : ∀ h : {h // h ∈ H}, Module.Free ℝ W := fun _ => Module.Free.of_divisionRing ℝ W
  letI : ∀ h : {h // h ∈ H}, Module.Finite ℝ W := fun _ => OAI.QuarticPowerFree.totalSpace_finite D
  letI : Module.Finite ℝ (∀ h : {h // h ∈ H}, W) := by infer_instance
  let F := affineFlatRestrictionFamily H (D := D)
  have hdimV : Module.finrank ℝ V = Nat.choose (D + n) n := by
    exact OAI.QuarticPowerFree.totalSpace_finrank D
  have hdimW : Module.finrank ℝ (∀ h : {h // h ∈ H}, W) =
      H.card * Nat.choose (D + k) k := by
    rw [Module.finrank_pi_fintype]
    simp [W, OAI.QuarticPowerFree.totalSpace_finrank, Fintype.card_coe]
  have hdim : Module.finrank ℝ (∀ h : {h // h ∈ H}, W) < Module.finrank ℝ V := by
    rw [hdimW, hdimV]
    exact hsize
  have hker : LinearMap.ker F ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨q, hqmem, hqne⟩ := (LinearMap.ker F).ne_bot_iff.mp hker
  have hzero : F q = 0 := LinearMap.mem_ker.mp hqmem
  have hpoly : (q : Poly n) ≠ 0 := by
    intro hq0
    apply hqne
    apply Subtype.ext
    exact hq0
  have hdeg : (q : Poly n).totalDegree ≤ D :=
    OAI.QuarticPowerFree.mem_totalSpace.mp q.property
  refine ⟨q, hpoly, hdeg, ?_⟩
  intro h hh x hx
  let hv : h.1.direction :=
    ⟨x -ᵥ affineFlatBase h, AffineSubspace.vsub_mem_direction hx (affineFlatBase_mem h)⟩
  let y : Fin k → ℝ := affineFlatCoordinates h |>.symm hv
  have hlinear : affineFlatLinearPart h y = x -ᵥ affineFlatBase h := by
    simp [affineFlatLinearPart, y, hv]
  have hpoint : x = affineFlatBase h + affineFlatLinearPart h y := by
    have hxv : (x -ᵥ affineFlatBase h) +ᵥ affineFlatBase h = x := vsub_vadd x _
    rw [← hlinear] at hxv
    calc
      x = affineFlatLinearPart h y +ᵥ affineFlatBase h := hxv.symm
      _ = affineFlatBase h + affineFlatLinearPart h y := by
        simp [PiLp.add_apply, add_comm]
  have hcoord : affineFlatRestrictionBounded h q = 0 := congrFun hzero ⟨h, hh⟩
  have hrestrict : affineFlatRestriction h (q : Poly n) = 0 := by
    have hv := congrArg Subtype.val hcoord
    simpa [affineFlatRestrictionBounded, affineFlatRestriction] using hv
  have hvalue : evalR (q : Poly n) (affineFlatBase h + affineFlatLinearPart h y) = 0 := by
    have hrestrict' : MvPolynomial.aeval (affineFlatSubstitution h) (q : Poly n) = 0 := by
      exact hrestrict
    have heval : MvPolynomial.eval y (MvPolynomial.aeval (affineFlatSubstitution h) (q : Poly n)) = 0 := by
      rw [hrestrict']
      simp
    rw [← affineFlatSubstitution_eval h (q : Poly n) y]
    exact heval
  simpa [hpoint] using hvalue

end DistinctDistances.TrackC
