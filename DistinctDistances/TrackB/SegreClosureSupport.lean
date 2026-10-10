import DistinctDistances.TrackB.Compactification
import DistinctDistances.TrackA.Definitions

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

def segreRow {n m : ℕ} (i : Fin n) : Point (n * m) →ₗ[ℂ] Point m :=
  LinearMap.pi (fun j => LinearMap.proj (finProdFinEquiv (i, j)))

def segreColumn {n m : ℕ} (j : Fin m) : Point (n * m) →ₗ[ℂ] Point n :=
  LinearMap.pi (fun i => LinearMap.proj (finProdFinEquiv (i, j)))

def fixedSegreLinear {n m o : ℕ} (p : ProjectivePoint n) (q : ProjectivePoint m) :
    Point o →ₗ[ℂ] Point ((n * m) * o) where
  toFun x := segreVector (segreVector p.rep q.rep) x
  map_add' x y := by
    funext k
    simp [segreVector, Pi.add_apply, mul_add]
  map_smul' c x := by
    funext k
    simp [segreVector, Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- Polynomial pullback of three linear maps followed by the Segre embedding. -/
def threeLinearSegrePullback {b n m o : ℕ}
    (A : Point b →ₗ[ℂ] Point n) (B : Point b →ₗ[ℂ] Point m)
    (C : Point b →ₗ[ℂ] Point o) : Poly ((n * m) * o) →ₐ[ℂ] Poly b :=
  MvPolynomial.aeval (fun k =>
    let ij := finProdFinEquiv.symm (finProdFinEquiv.symm k).1
    linearCoordinate A ij.1 * linearCoordinate B ij.2 *
      linearCoordinate C (finProdFinEquiv.symm k).2)

/-- the representative choice in segrePoint does not change the point. -/
theorem segrePoint_mk {n m : ℕ} (v : Point n) (w : Point m)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    segrePoint (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ w hw) =
      Projectivization.mk ℂ (segreVector v w) (segreVector_ne_zero v w hv hw) := by
  unfold segrePoint
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ w hw
  have hrepA : ∀ i, (Projectivization.mk ℂ v hv).rep i = (a : ℂ) * v i := by
    intro i
    have hi := congrFun ha i
    change (a : ℂ) * v i = _ at hi
    exact hi.symm
  have hrepB : ∀ i, (Projectivization.mk ℂ w hw).rep i = (b : ℂ) * w i := by
    intro i
    have hi := congrFun hb i
    change (b : ℂ) * w i = _ at hi
    exact hi.symm
  have htensor :
      segreVector (Projectivization.mk ℂ v hv).rep (Projectivization.mk ℂ w hw).rep =
        ((a : ℂ) * (b : ℂ)) • segreVector v w := by
    funext k
    simp only [segreVector, Pi.smul_apply, smul_eq_mul]
    rw [hrepA, hrepB]
    ring
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  exact ⟨(a : ℂ) * (b : ℂ), htensor.symm⟩

/-- the Segre map is injective on its two projective factors. -/
theorem segrePoint_injective {n m : ℕ} :
    Function.Injective (fun pq : ProjectivePoint n × ProjectivePoint m =>
      segrePoint pq.1 pq.2) := by
  intro pq pq' h
  obtain ⟨p, q⟩ := pq
  obtain ⟨p', q'⟩ := pq'
  change segrePoint p q = segrePoint p' q' at h
  change Projectivization.mk ℂ (segreVector p.rep q.rep) _ = _ at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ
    (segreVector p.rep q.rep) (segreVector p'.rep q'.rep)
    (segreVector_ne_zero _ _ p.rep_nonzero q.rep_nonzero)
    (segreVector_ne_zero _ _ p'.rep_nonzero q'.rep_nonzero)).mp h
  have hp : ∃ i, p.rep i ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply p.rep_nonzero
    funext i
    exact hn i
  have hq : ∃ j, q.rep j ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply q.rep_nonzero
    funext j
    exact hn j
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  have hcoord (k : Fin n) (l : Fin m) :
      a * (p'.rep k * q'.rep l) = p.rep k * q.rep l := by
    have h := congrFun ha (finProdFinEquiv (k, l))
    simpa [Pi.smul_apply, smul_eq_mul, segreVector] using h
  have hnonzero : a * (p'.rep i * q'.rep j) ≠ 0 := by
    rw [hcoord i j]
    exact mul_ne_zero hi hj
  have ha0 : a ≠ 0 := by
    intro hz
    apply hnonzero
    simp [hz]
  have hpi' : p'.rep i ≠ 0 := by
    intro hz
    apply hnonzero
    simp [hz]
  have hqj' : q'.rep j ≠ 0 := by
    intro hz
    apply hnonzero
    simp [hz]
  have hden : a * q'.rep j ≠ 0 := mul_ne_zero ha0 hqj'
  let c : ℂ := q.rep j / (a * q'.rep j)
  have hc : ∀ k, p'.rep k = c * p.rep k := by
    intro k
    dsimp [c]
    field_simp [hden]
    linear_combination hcoord k j
  have hcne : c ≠ 0 := by
    dsimp [c]
    exact div_ne_zero hj hden
  have hden' : a * p'.rep i ≠ 0 := mul_ne_zero ha0 hpi'
  let d : ℂ := p.rep i / (a * p'.rep i)
  have hd : ∀ l, q'.rep l = d * q.rep l := by
    intro l
    dsimp [d]
    field_simp [hden']
    linear_combination hcoord i l
  have hdne : d ≠ 0 := by
    dsimp [d]
    exact div_ne_zero hi hden'
  have hpEq : p = p' := by
    have hscalar : (c⁻¹ : ℂ) • p'.rep = p.rep := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hc k]
      simp [smul_eq_mul, mul_assoc, hcne]
    have hmk : Projectivization.mk ℂ p.rep p.rep_nonzero =
        Projectivization.mk ℂ p'.rep p'.rep_nonzero :=
      (Projectivization.mk_eq_mk_iff' ℂ p.rep p'.rep
        p.rep_nonzero p'.rep_nonzero).2 ⟨c⁻¹, hscalar⟩
    calc
      p = Projectivization.mk ℂ p.rep p.rep_nonzero := p.mk_rep.symm
      _ = Projectivization.mk ℂ p'.rep p'.rep_nonzero := hmk
      _ = p' := p'.mk_rep
  have hqEq : q = q' := by
    have hscalar : (d⁻¹ : ℂ) • q'.rep = q.rep := by
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hd l]
      simp [smul_eq_mul, mul_assoc, hdne]
    have hmk : Projectivization.mk ℂ q.rep q.rep_nonzero =
        Projectivization.mk ℂ q'.rep q'.rep_nonzero :=
      (Projectivization.mk_eq_mk_iff' ℂ q.rep q'.rep
        q.rep_nonzero q'.rep_nonzero).2 ⟨d⁻¹, hscalar⟩
    calc
      q = Projectivization.mk ℂ q.rep q.rep_nonzero := q.mk_rep.symm
      _ = Projectivization.mk ℂ q'.rep q'.rep_nonzero := hmk
      _ = q' := q'.mk_rep
  exact Prod.ext hpEq hqEq

/-- the fixed first two factors give an injective linear point map. -/
theorem fixedSegreLinear_injective {n m o : ℕ}
    (p : ProjectivePoint n) (q : ProjectivePoint m) :
    Function.Injective (fixedSegreLinear (o := o) p q) := by
  have hp : ∃ i, p.rep i ≠ 0 := by
    by_contra h
    push_neg at h
    apply p.rep_nonzero
    funext i
    exact h i
  have hq : ∃ j, q.rep j ≠ 0 := by
    by_contra h
    push_neg at h
    apply q.rep_nonzero
    funext j
    exact h j
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  intro x y hxy
  funext k
  have hcoord := congrFun hxy (finProdFinEquiv (finProdFinEquiv (i, j), k))
  apply mul_left_cancel₀ (mul_ne_zero hi hj)
  simpa [fixedSegreLinear, segreVector] using hcoord

/-- identify that point map with the actual triple Segre point. -/
theorem fixedSegreLinear_projective {n m o : ℕ}
    (p : ProjectivePoint n) (q : ProjectivePoint m) (x : ProjectivePoint o)
    (hx : fixedSegreLinear p q x.rep ≠ 0) :
    TrackA.projectiveMap (fixedSegreLinear p q) x hx = segrePoint (segrePoint p q) x := by
  have hinner : segrePoint p q =
      Projectivization.mk ℂ (segreVector p.rep q.rep)
        (segreVector_ne_zero p.rep q.rep p.rep_nonzero q.rep_nonzero) := by
    calc
      segrePoint p q = segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero)
          (Projectivization.mk ℂ q.rep q.rep_nonzero) := by
            calc
              segrePoint p q =
                  segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) q :=
                    congrArg (fun r => segrePoint r q) p.mk_rep.symm
              _ = _ := congrArg
                (fun r => segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) r)
                q.mk_rep.symm
      _ = _ := segrePoint_mk p.rep q.rep p.rep_nonzero q.rep_nonzero
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (segreVector p.rep q.rep) (segreVector_ne_zero p.rep q.rep p.rep_nonzero q.rep_nonzero)
  have hrep : (segrePoint p q).rep = (a : ℂ) • segreVector p.rep q.rep := by
    have h := congrArg Projectivization.rep hinner
    calc
      (segrePoint p q).rep =
          (Projectivization.mk ℂ (segreVector p.rep q.rep)
            (segreVector_ne_zero p.rep q.rep p.rep_nonzero q.rep_nonzero)).rep := h
      _ = (a : ℂ) • segreVector p.rep q.rep := ha.symm
  have hvec : segreVector (segrePoint p q).rep x.rep =
      (a : ℂ) • fixedSegreLinear p q x.rep := by
    funext k
    simp [segreVector, fixedSegreLinear, hrep, smul_eq_mul, mul_assoc]
  change Projectivization.mk ℂ (fixedSegreLinear p q x.rep) hx =
    Projectivization.mk ℂ (segreVector (segrePoint p q).rep x.rep)
      (segreVector_ne_zero _ _ (segrePoint p q).rep_nonzero x.rep_nonzero)
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hx _).2
  refine ⟨a⁻¹, ?_⟩
  rw [hvec]
  simp [smul_smul]

/-- use a specified point representative in the same fixed-factor map. -/
theorem fixedSegreLinear_mk_mem {n m o : ℕ} (p : ProjectivePoint n) (q : ProjectivePoint m)
    (x : Point o) (hx : x ≠ 0) (W : ProjectiveVariety ((n * m) * o)) :
    segrePoint (segrePoint p q) (Projectivization.mk ℂ x hx) ∈ W.points ↔
      fixedSegreLinear p q x ∈ W.affineCone.points := by
  have hLx : fixedSegreLinear p q x ≠ 0 := by
    intro hzero
    apply hx
    exact (fixedSegreLinear_injective p q) (by simpa using hzero)
  have hLrep : fixedSegreLinear p q (Projectivization.mk ℂ x hx).rep ≠ 0 := by
    intro hzero
    exact (Projectivization.mk ℂ x hx).rep_nonzero
      ((fixedSegreLinear_injective p q) (by simpa using hzero))
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  have hlin : fixedSegreLinear p q ((Projectivization.mk ℂ x hx).rep) =
      (a : ℂ) • fixedSegreLinear p q x := by
    rw [← ha]
    exact (fixedSegreLinear p q).map_smul a x
  have hmap : TrackA.projectiveMap (fixedSegreLinear p q)
      (Projectivization.mk ℂ x hx) hLrep =
      Projectivization.mk ℂ (fixedSegreLinear p q x) hLx := by
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hLrep hLx).2
    exact ⟨a, hlin.symm⟩
  rw [← fixedSegreLinear_projective p q (Projectivization.mk ℂ x hx) hLrep]
  rw [hmap]
  exact ProjectiveVariety.mem_points_mk_iff W (fixedSegreLinear p q x) hLx

/-- every point in the closure of Segre pairs has rank-one coordinates.
An arbitrary nonzero pivot recovers both projective factors. -/
private theorem pairClosure_minor {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (v : Point (n * m))
    (hv : v ≠ 0) (hb : Projectivization.mk ℂ v hv ∈ pairClosure T)
    (i k : Fin n) (j l : Fin m) :
    v (finProdFinEquiv (i, j)) * v (finProdFinEquiv (k, l)) =
      v (finProdFinEquiv (i, l)) * v (finProdFinEquiv (k, j)) := by
  let S : Set (ProjectivePoint (n * m)) :=
    {w | ∃ p q, (p, q) ∈ T ∧ segrePoint p q = w}
  let f : Poly (n * m) :=
    MvPolynomial.X (finProdFinEquiv (i, j)) * MvPolynomial.X (finProdFinEquiv (k, l)) -
      MvPolynomial.X (finProdFinEquiv (i, l)) * MvPolynomial.X (finProdFinEquiv (k, j))
  have hf : f ∈ (pairClosure T).ideal := by
    change f ∈ ProjectiveVariety.vanishingIdeal S
    rw [ProjectiveVariety.vanishingIdeal]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro z hz
    obtain ⟨hz0, hzS⟩ := hz
    change ∃ p q, (p, q) ∈ T ∧ segrePoint p q = Projectivization.mk ℂ z hz0 at hzS
    obtain ⟨p, q, hT, hseg⟩ := hzS
    have hsp : segrePoint p q =
        Projectivization.mk ℂ (segreVector p.rep q.rep)
          (segreVector_ne_zero p.rep q.rep p.rep_nonzero q.rep_nonzero) := by
      calc
        segrePoint p q = segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero)
            (Projectivization.mk ℂ q.rep q.rep_nonzero) := by
              calc
                segrePoint p q =
                    segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) q :=
                      congrArg (fun r => segrePoint r q) p.mk_rep.symm
                _ = _ := congrArg
                  (fun r => segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) r)
                  q.mk_rep.symm
        _ = _ := segrePoint_mk p.rep q.rep p.rep_nonzero q.rep_nonzero
    have hproj : Projectivization.mk ℂ z hz0 =
        Projectivization.mk ℂ (segreVector p.rep q.rep)
          (segreVector_ne_zero p.rep q.rep p.rep_nonzero q.rep_nonzero) :=
      hseg.symm.trans hsp
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ z (segreVector p.rep q.rep)
      hz0 (segreVector_ne_zero p.rep q.rep p.rep_nonzero q.rep_nonzero)).mp hproj
    have hEval : MvPolynomial.aeval z f = 0 := by
      rw [MvPolynomial.aeval_eq_eval, ← ha]
      simp [f, Pi.smul_apply, smul_eq_mul, segreVector]
      ring
    simpa [f, MvPolynomial.aeval_eq_eval] using hEval
  have hval := hb v hv rfl f hf
  have hsub : v (finProdFinEquiv (i, j)) * v (finProdFinEquiv (k, l)) -
      v (finProdFinEquiv (i, l)) * v (finProdFinEquiv (k, j)) = 0 := by
    simpa [f, MvPolynomial.aeval_eq_eval] using hval
  exact sub_eq_zero.mp hsub

theorem pairClosure_pivot_reconstruction {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (v : Point (n * m))
    (hv : v ≠ 0) (hb : Projectivization.mk ℂ v hv ∈ pairClosure T) (i : Fin n) (j : Fin m)
    (hij : v (finProdFinEquiv (i, j)) ≠ 0) :
    ∃ (hd : segreColumn j v ≠ 0) (hp : segreRow i v ≠ 0),
      segrePoint (Projectivization.mk ℂ (segreColumn j v) hd)
        (Projectivization.mk ℂ (segreRow i v) hp) = Projectivization.mk ℂ v hv := by
  have hd : segreColumn j v ≠ 0 := by
    intro hzero
    apply hij
    have h := congrFun hzero i
    simpa [segreColumn] using h
  have hp : segreRow i v ≠ 0 := by
    intro hzero
    apply hij
    have h := congrFun hzero j
    simpa [segreRow] using h
  have hvec : segreVector (segreColumn j v) (segreRow i v) =
      v (finProdFinEquiv (i, j)) • v := by
    funext r
    let kl := finProdFinEquiv.symm r
    have hidx : finProdFinEquiv (kl.1, kl.2) = r := by
      simpa [kl] using finProdFinEquiv.apply_symm_apply r
    have h := pairClosure_minor T v hv hb i kl.1 j kl.2
    rw [← hidx]
    simpa [segreVector, segreColumn, segreRow, kl, Pi.smul_apply,
      smul_eq_mul, mul_comm] using h.symm
  have hmk : Projectivization.mk ℂ (segreVector (segreColumn j v) (segreRow i v))
      (segreVector_ne_zero _ _ hd hp) = Projectivization.mk ℂ v hv := by
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
    exact ⟨v (finProdFinEquiv (i, j)), hvec.symm⟩
  refine ⟨hd, hp, ?_⟩
  exact (segrePoint_mk _ _ hd hp).trans hmk

/-- at a zero pivot of a rank-one matrix its pivot row or column is zero. -/
theorem pairClosure_zero_pivot {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (v : Point (n * m))
    (hv : v ≠ 0) (hb : Projectivization.mk ℂ v hv ∈ pairClosure T)
    (i : Fin n) (j : Fin m) (hij : v (finProdFinEquiv (i, j)) = 0) :
    segreColumn j v = 0 ∨ segreRow i v = 0 := by
  by_cases hcol : segreColumn j v = 0
  · exact Or.inl hcol
  · right
    have hk : ∃ k, segreColumn j v k ≠ 0 := by
      by_contra h
      push_neg at h
      apply hcol
      funext k
      exact h k
    obtain ⟨k, hk⟩ := hk
    have hk' : v (finProdFinEquiv (k, j)) ≠ 0 := by
      simpa [segreColumn] using hk
    funext l
    have hminor := pairClosure_minor T v hv hb i k j l
    have hzero : v (finProdFinEquiv (i, l)) * v (finProdFinEquiv (k, j)) = 0 := by
      rw [← hminor, hij]
      simp
    exact (mul_eq_zero.mp hzero).resolve_right hk'

/-- the resolution equations are linear equations in Segre coordinates.
Consequently taking the pair closure preserves the actual resolution relation. -/
theorem closedPairs_resolution {e : ℕ}
    (T : Set (ProjectivePoint e × ProjectivePoint (e + e)))
    (hT : T ⊆ resolutionPairs e) : closedPairs T ⊆ resolutionPairs e := by
  intro w hw
  rcases w with ⟨d, q⟩
  change segrePoint d q ∈ pairClosure T at hw
  let v := segreVector d.rep q.rep
  have hv : v ≠ 0 := segreVector_ne_zero _ _ d.rep_nonzero q.rep_nonzero
  have hmk : segrePoint d q = Projectivization.mk ℂ v hv := by
    calc
      segrePoint d q = segrePoint (Projectivization.mk ℂ d.rep d.rep_nonzero) q :=
        congrArg (fun x => segrePoint x q) d.mk_rep.symm
      _ = segrePoint (Projectivization.mk ℂ d.rep d.rep_nonzero)
          (Projectivization.mk ℂ q.rep q.rep_nonzero) :=
        congrArg (fun x => segrePoint (Projectivization.mk ℂ d.rep d.rep_nonzero) x)
          q.mk_rep.symm
      _ = Projectivization.mk ℂ v hv := segrePoint_mk d.rep q.rep d.rep_nonzero q.rep_nonzero
  have hvpoint : Projectivization.mk ℂ v hv ∈ pairClosure T := by
    rw [← hmk]
    exact hw
  have hcone : v ∈ (pairClosure T).affineCone.points :=
    (ProjectiveVariety.mem_points_mk_iff (pairClosure T) v hv).mp hvpoint
  have hminor (i k : Fin e) :
      d.rep i * firstPoint q.rep k = d.rep k * firstPoint q.rep i := by
    let f : Poly (e * (e + e)) :=
      MvPolynomial.X (finProdFinEquiv (i, Fin.castAdd e k)) -
        MvPolynomial.X (finProdFinEquiv (k, Fin.castAdd e i))
    have hf : f ∈ (pairClosure T).ideal := by
      let S : Set (ProjectivePoint (e * (e + e))) :=
        {z | ∃ p r, (p, r) ∈ T ∧ segrePoint p r = z}
      change f ∈ ProjectiveVariety.vanishingIdeal S
      rw [ProjectiveVariety.vanishingIdeal]
      apply MvPolynomial.mem_vanishingIdeal_iff.mpr
      rintro z ⟨hz0, hzS⟩
      obtain ⟨p, r, hpr, hseg⟩ := hzS
      obtain ⟨t, hfirst, _⟩ := hT hpr
      have hfirst_coord (j : Fin e) :
          r.rep (Fin.castAdd e j) = t * p.rep j := by
        have h := congrFun hfirst j
        simpa [firstPoint, Pi.smul_apply, smul_eq_mul] using h
      have hsp : segrePoint p r =
          Projectivization.mk ℂ (segreVector p.rep r.rep)
            (segreVector_ne_zero _ _ p.rep_nonzero r.rep_nonzero) :=
        by
          calc
            segrePoint p r = segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) r :=
              congrArg (fun x => segrePoint x r) p.mk_rep.symm
            _ = segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero)
                (Projectivization.mk ℂ r.rep r.rep_nonzero) :=
              congrArg (fun x => segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) x)
                r.mk_rep.symm
            _ = _ := segrePoint_mk p.rep r.rep p.rep_nonzero r.rep_nonzero
      have hproj : Projectivization.mk ℂ z hz0 =
          Projectivization.mk ℂ (segreVector p.rep r.rep)
            (segreVector_ne_zero _ _ p.rep_nonzero r.rep_nonzero) :=
        hseg.symm.trans hsp
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ z
        (segreVector p.rep r.rep) hz0
        (segreVector_ne_zero _ _ p.rep_nonzero r.rep_nonzero)).mp hproj
      have hEval : MvPolynomial.aeval z f = 0 := by
        rw [MvPolynomial.aeval_eq_eval, ← ha]
        simp [f, segreVector, hfirst_coord, Pi.smul_apply, smul_eq_mul]
        ring
      simpa [MvPolynomial.aeval_eq_eval] using hEval
    have hzero := (MvPolynomial.mem_zeroLocus_iff.mp hcone) f hf
    have hsub : d.rep i * firstPoint q.rep k - d.rep k * firstPoint q.rep i = 0 := by
      simpa [f, MvPolynomial.aeval_eq_eval, v, segreVector, firstPoint] using hzero
    exact sub_eq_zero.mp hsub
  have hcontract : covectorOfPoint (secondPoint q.rep) d.rep = 0 := by
    let f : Poly (e * (e + e)) :=
      Finset.univ.sum fun i : Fin e =>
        MvPolynomial.X (finProdFinEquiv (i, Fin.natAdd e i))
    have hf : f ∈ (pairClosure T).ideal := by
      let S : Set (ProjectivePoint (e * (e + e))) :=
        {z | ∃ p r, (p, r) ∈ T ∧ segrePoint p r = z}
      change f ∈ ProjectiveVariety.vanishingIdeal S
      rw [ProjectiveVariety.vanishingIdeal]
      apply MvPolynomial.mem_vanishingIdeal_iff.mpr
      rintro z ⟨hz0, hzS⟩
      obtain ⟨p, r, hpr, hseg⟩ := hzS
      obtain ⟨_, _, hcov⟩ := hT hpr
      have hcov_eval : covectorOfPoint (secondPoint r.rep) p.rep =
          Finset.univ.sum fun i : Fin e => secondPoint r.rep i * p.rep i := by
        simp only [covectorOfPoint, LinearMap.sum_apply, LinearMap.smul_apply,
          LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
      have hsp : segrePoint p r =
          Projectivization.mk ℂ (segreVector p.rep r.rep)
            (segreVector_ne_zero _ _ p.rep_nonzero r.rep_nonzero) :=
        by
          calc
            segrePoint p r = segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) r :=
              congrArg (fun x => segrePoint x r) p.mk_rep.symm
            _ = segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero)
                (Projectivization.mk ℂ r.rep r.rep_nonzero) :=
              congrArg (fun x => segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) x)
                r.mk_rep.symm
            _ = _ := segrePoint_mk p.rep r.rep p.rep_nonzero r.rep_nonzero
      have hproj : Projectivization.mk ℂ z hz0 =
          Projectivization.mk ℂ (segreVector p.rep r.rep)
            (segreVector_ne_zero _ _ p.rep_nonzero r.rep_nonzero) :=
        hseg.symm.trans hsp
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ z
        (segreVector p.rep r.rep) hz0
        (segreVector_ne_zero _ _ p.rep_nonzero r.rep_nonzero)).mp hproj
      have hEval : MvPolynomial.aeval z f = 0 := by
        rw [MvPolynomial.aeval_eq_eval, ← ha]
        calc
          MvPolynomial.eval ((a : ℂ) • segreVector p.rep r.rep) f =
              (a : ℂ) * covectorOfPoint (secondPoint r.rep) p.rep := by
            rw [hcov_eval]
            simp [f, segreVector, secondPoint, Pi.smul_apply, smul_eq_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = 0 := by rw [hcov]; simp
      simpa [MvPolynomial.aeval_eq_eval] using hEval
    have hzero := (MvPolynomial.mem_zeroLocus_iff.mp hcone) f hf
    have hsum :
        (Finset.univ.sum fun i : Fin e =>
          d.rep i * secondPoint q.rep i) = 0 := by
      simpa [f, MvPolynomial.aeval_eq_eval, v, segreVector, secondPoint] using hzero
    have heval : covectorOfPoint (secondPoint q.rep) d.rep =
        Finset.univ.sum fun i : Fin e => secondPoint q.rep i * d.rep i := by
      simp only [covectorOfPoint, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
    rw [heval]
    calc
      (Finset.univ.sum fun i : Fin e => secondPoint q.rep i * d.rep i) =
          Finset.univ.sum fun i : Fin e => d.rep i * secondPoint q.rep i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := hsum
  have hdi : ∃ i : Fin e, d.rep i ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply d.rep_nonzero
    funext i
    exact hn i
  obtain ⟨i, hi⟩ := hdi
  let t : ℂ := firstPoint q.rep i / d.rep i
  have hfirst : firstPoint q.rep = t • d.rep := by
    funext k
    have hcoord := hminor i k
    dsimp [t]
    change firstPoint q.rep k =
      (firstPoint q.rep i / d.rep i) * d.rep k
    field_simp [hi]
    linear_combination hcoord
  exact ⟨t, hfirst, hcontract⟩

/-- an injective projective linear map takes the closure of a point set
into any projective variety containing its image. Use polynomial pullback. -/
theorem projective_linear_closure {n m : ℕ} (φ : Point n →ₗ[ℂ] Point m)
    (hφ : Function.Injective φ) (T : Set (ProjectivePoint n)) (W : ProjectiveVariety m)
    (hT : ∀ p ∈ T, ∀ hp : φ p.rep ≠ 0, TrackA.projectiveMap φ p hp ∈ W.points) :
    ∀ p ∈ (ProjectiveVariety.closure T).points, ∀ hp : φ p.rep ≠ 0,
      TrackA.projectiveMap φ p hp ∈ W.points := by
  intro p hp hpφ
  apply (ProjectiveVariety.mem_points_mk_iff W (φ p.rep) hpφ).2
  intro f hf
  have hpull : linearPullback φ f ∈ (ProjectiveVariety.closure T).ideal := by
    change linearPullback φ f ∈ ProjectiveVariety.vanishingIdeal T
    rw [ProjectiveVariety.vanishingIdeal]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro z ⟨hz0, hzT⟩
    have hφz : φ z ≠ 0 := by
      intro hzero
      apply hz0
      exact hφ (by simpa using hzero)
    let q : ProjectivePoint n := Projectivization.mk ℂ z hz0
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ z hz0
    have hφq : φ q.rep ≠ 0 := by
      intro hzero
      apply q.rep_nonzero
      exact hφ (by simpa using hzero)
    have hWq : TrackA.projectiveMap φ q hφq ∈ W.points := hT q hzT hφq
    have hrep : q.rep = (a : ℂ) • z := by
      simpa only [Units.smul_def] using ha.symm
    have hφrep : φ q.rep = (a : ℂ) • φ z := by
      calc
        φ q.rep = φ ((a : ℂ) • z) := by rw [hrep]
        _ = (a : ℂ) • φ z := φ.map_smul (a : ℂ) z
    have hmap : TrackA.projectiveMap φ q hφq =
        Projectivization.mk ℂ (φ z) hφz := by
      change Projectivization.mk ℂ (φ q.rep) hφq = _
      apply (Projectivization.mk_eq_mk_iff' ℂ (φ q.rep) (φ z) hφq hφz).2
      exact ⟨a, hφrep.symm⟩
    have hWz : Projectivization.mk ℂ (φ z) hφz ∈ W.points := by
      rw [← hmap]
      exact hWq
    have hcone : φ z ∈ W.affineCone.points :=
      (ProjectiveVariety.mem_points_mk_iff W (φ z) hφz).mp hWz
    have hevalPullback : MvPolynomial.aeval z (linearPullback φ f) =
        MvPolynomial.aeval (φ z) f := by
      have hcoord (j : Fin m) :
          MvPolynomial.aeval z (linearCoordinate φ j) = φ z j := by
        have h := AffineProjection.eval_pullback
          (⟨φ, (0 : Point m)⟩ : AffineProjection n m) z (MvPolynomial.X j)
        simpa [AffineProjection.pullback, AffineProjection.apply,
          MvPolynomial.aeval_eq_eval] using h
      change MvPolynomial.aeval z (MvPolynomial.aeval (linearCoordinate φ) f) = _
      rw [MvPolynomial.comp_aeval_apply]
      apply congrArg (fun u : Point m => MvPolynomial.aeval u f)
      funext j
      exact hcoord j
    rw [hevalPullback]
    exact (MvPolynomial.mem_zeroLocus_iff.mp hcone) f hf
  have hvanish := MvPolynomial.mem_zeroLocus_iff.mp
    (hp p.rep p.rep_nonzero p.mk_rep) (linearPullback φ f) hpull
  have heval : MvPolynomial.aeval p.rep (linearPullback φ f) =
      MvPolynomial.aeval (φ p.rep) f := by
    have hcoord (j : Fin m) :
        MvPolynomial.aeval p.rep (linearCoordinate φ j) = φ p.rep j := by
      have h := AffineProjection.eval_pullback
        (⟨φ, (0 : Point m)⟩ : AffineProjection n m) p.rep (MvPolynomial.X j)
      simpa [AffineProjection.pullback, AffineProjection.apply,
        MvPolynomial.aeval_eq_eval] using h
    change MvPolynomial.aeval p.rep (MvPolynomial.aeval (linearCoordinate φ) f) = _
    rw [MvPolynomial.comp_aeval_apply]
    apply congrArg (fun u : Point m => MvPolynomial.aeval u f)
    funext j
    exact hcoord j
  rw [← heval]
  exact hvanish

/-- evaluate the explicit three-linear-factor polynomial pullback. -/
theorem eval_threeLinearSegrePullback {b n m o : ℕ}
    (A : Point b →ₗ[ℂ] Point n) (B : Point b →ₗ[ℂ] Point m)
    (C : Point b →ₗ[ℂ] Point o) (v : Point b) (f : Poly ((n * m) * o)) :
    MvPolynomial.aeval v (threeLinearSegrePullback A B C f) =
      MvPolynomial.aeval (segreVector (segreVector (A v) (B v)) (C v)) f := by
  have hA (j : Fin n) : MvPolynomial.eval v (linearCoordinate A j) = A v j := by
    have h := AffineProjection.eval_pullback
      (⟨A, 0⟩ : AffineProjection b n) v (MvPolynomial.X j)
    simpa [AffineProjection.pullback, AffineProjection.apply,
      MvPolynomial.aeval_eq_eval] using h
  have hB (j : Fin m) : MvPolynomial.eval v (linearCoordinate B j) = B v j := by
    have h := AffineProjection.eval_pullback
      (⟨B, 0⟩ : AffineProjection b m) v (MvPolynomial.X j)
    simpa [AffineProjection.pullback, AffineProjection.apply,
      MvPolynomial.aeval_eq_eval] using h
  have hC (j : Fin o) : MvPolynomial.eval v (linearCoordinate C j) = C v j := by
    have h := AffineProjection.eval_pullback
      (⟨C, 0⟩ : AffineProjection b o) v (MvPolynomial.X j)
    simpa [AffineProjection.pullback, AffineProjection.apply,
      MvPolynomial.aeval_eq_eval] using h
  change MvPolynomial.aeval v (MvPolynomial.aeval (fun k =>
    let ij := finProdFinEquiv.symm (finProdFinEquiv.symm k).1
    linearCoordinate A ij.1 * linearCoordinate B ij.2 *
      linearCoordinate C (finProdFinEquiv.symm k).2) f) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun u : Point ((n * m) * o) => MvPolynomial.aeval u f)
  funext k
  simp [segreVector, hA, hB, hC]

end
end DistinctDistances.TrackB
