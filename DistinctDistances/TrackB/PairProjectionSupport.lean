import DistinctDistances.TrackB.IncidenceDensity

namespace DistinctDistances.TrackB
noncomputable section

/-- the rank-one pivot reconstruction recovers the two factors of
every point in the actual pair closure. -/
theorem pairClosure_factorization {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (b : ProjectivePoint (n * m))
    (hb : b ∈ (pairClosure T).points) :
    ∃ p : ProjectivePoint n, ∃ q : ProjectivePoint m, segrePoint p q = b := by
  classical
  have hpivot : ∃ i : Fin n, ∃ j : Fin m,
      b.rep (finProdFinEquiv (i, j)) ≠ 0 := by
    by_contra h
    push_neg at h
    apply b.rep_nonzero
    funext k
    let ij := finProdFinEquiv.symm k
    have hcoord := h ij.1 ij.2
    have hidx : finProdFinEquiv (ij.1, ij.2) = k := by
      simpa [ij] using finProdFinEquiv.apply_symm_apply k
    rw [hidx] at hcoord
    exact hcoord
  obtain ⟨i, j, hij⟩ := hpivot
  have hb' : Projectivization.mk ℂ b.rep b.rep_nonzero ∈ (pairClosure T).points := by
    rw [b.mk_rep]
    exact hb
  obtain ⟨hd, hr, hfactor⟩ :=
    pairClosure_pivot_reconstruction T b.rep b.rep_nonzero hb' i j hij
  refine ⟨Projectivization.mk ℂ (segreColumn j b.rep) hd,
    Projectivization.mk ℂ (segreRow i b.rep) hr, ?_⟩
  calc
    segrePoint (Projectivization.mk ℂ (segreColumn j b.rep) hd)
        (Projectivization.mk ℂ (segreRow i b.rep) hr) =
        Projectivization.mk ℂ b.rep b.rep_nonzero := hfactor
    _ = b := b.mk_rep

/-- a homogeneous equation of the second factor pulls back to a
nonzero row slice of the tensor, and hence holds on every closed pair. -/
theorem pairClosure_projection_contained {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (W : ProjectiveVariety m)
    (hT : ∀ p q, (p, q) ∈ T → q ∈ W.points)
    (p : ProjectivePoint n) (q : ProjectivePoint m) (hpair : (p, q) ∈ closedPairs T) :
    q ∈ W.points := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin n, p.rep i ≠ 0 := by
    by_contra h
    push_neg at h
    exact p.rep_nonzero (funext h)
  have hWclosure : ProjectiveVariety.closure W.points = W := by
    apply ProjectiveVariety.ext
    exact W.vanishingIdeal_points
  let φ : Point (n * m) →ₗ[ℂ] Point m := segreRow i
  have eval_pull (y : Point (n * m)) (g : Poly m) :
      MvPolynomial.aeval y (linearPullback φ g) = MvPolynomial.aeval (φ y) g := by
    have hcoord (k : Fin m) :
        MvPolynomial.aeval y (linearCoordinate φ k) = φ y k := by
      have he := AffineProjection.eval_pullback
        (⟨φ, (0 : Point m)⟩ : AffineProjection (n * m) m) y (MvPolynomial.X k)
      simpa [AffineProjection.pullback, AffineProjection.apply,
        MvPolynomial.aeval_eq_eval] using he
    change MvPolynomial.aeval y (MvPolynomial.aeval (linearCoordinate φ) g) = _
    rw [MvPolynomial.comp_aeval_apply]
    apply congrArg (fun u : Point m => MvPolynomial.aeval u g)
    funext k
    exact hcoord k
  have closureRow (y : Point (n * m)) (hy : y ∈ (pairClosure T).affineCone.points) :
      φ y ∈ W.affineCone.points := by
    intro f hf
    have hcomponent (d : ℕ) :
        MvPolynomial.homogeneousComponent d f ∈ W.ideal :=
      MvPolynomial.homogeneousComponent_mem_of_mem W.isHomogeneous hf d
    have hpull (d : ℕ) : linearPullback φ (MvPolynomial.homogeneousComponent d f) ∈
        (pairClosure T).ideal := by
      change linearPullback φ (MvPolynomial.homogeneousComponent d f) ∈
        ProjectiveVariety.vanishingIdeal
          {w : ProjectivePoint (n * m) | ∃ r s, (r, s) ∈ T ∧ segrePoint r s = w}
      rw [ProjectiveVariety.vanishingIdeal]
      apply MvPolynomial.mem_vanishingIdeal_iff.mpr
      rintro z ⟨hz0, hzT⟩
      obtain ⟨r, s, hrs, hseg⟩ := hzT
      let t := segreVector r.rep s.rep
      have ht : t ≠ 0 := segreVector_ne_zero _ _ r.rep_nonzero s.rep_nonzero
      have hsp : segrePoint r s = Projectivization.mk ℂ t ht := by
        calc
          segrePoint r s = segrePoint (Projectivization.mk ℂ r.rep r.rep_nonzero) s :=
            congrArg (fun y => segrePoint y s) r.mk_rep.symm
          _ = segrePoint (Projectivization.mk ℂ r.rep r.rep_nonzero)
              (Projectivization.mk ℂ s.rep s.rep_nonzero) :=
            congrArg (fun y => segrePoint (Projectivization.mk ℂ r.rep r.rep_nonzero) y)
              s.mk_rep.symm
          _ = Projectivization.mk ℂ t ht := segrePoint_mk r.rep s.rep
            r.rep_nonzero s.rep_nonzero
      have hmkz : Projectivization.mk ℂ z hz0 = Projectivization.mk ℂ t ht :=
        hseg.symm.trans hsp
      obtain ⟨a, ha⟩ :=
        (Projectivization.mk_eq_mk_iff' ℂ z t hz0 ht).mp hmkz
      have hroweq : φ t = r.rep i • s.rep := by
        funext k
        simp [φ, segreRow, t, segreVector, Pi.smul_apply, smul_eq_mul]
      have hrowz : φ z = ((a : ℂ) * r.rep i) • s.rep := by
        calc
          φ z = φ ((a : ℂ) • t) := by rw [ha]
          _ = (a : ℂ) • φ t := φ.map_smul _ _
          _ = _ := by rw [hroweq]; simp [smul_smul, mul_assoc]
      have hs : s ∈ W.points := hT r s hrs
      have hzero : (0 : Point m) ∈ W.affineCone.points := by
        rw [← hWclosure]
        exact zero_mem_projective_cone W.points ⟨s, hs⟩
      have hscaled (c : ℂ) : c • s.rep ∈ W.affineCone.points := by
        by_cases hc : c = 0
        · rw [hc, zero_smul]
          exact hzero
        · have hmkc : Projectivization.mk ℂ (c • s.rep)
              (smul_ne_zero hc s.rep_nonzero) = s := by
            calc
              Projectivization.mk ℂ (c • s.rep) (smul_ne_zero hc s.rep_nonzero) =
                  Projectivization.mk ℂ s.rep s.rep_nonzero := by
                    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
                    exact ⟨c, rfl⟩
              _ = s := s.mk_rep
          have hs' : Projectivization.mk ℂ (c • s.rep)
              (smul_ne_zero hc s.rep_nonzero) ∈ W.points := by
            rw [hmkc]
            exact hs
          exact (ProjectiveVariety.mem_points_mk_iff W (c • s.rep)
            (smul_ne_zero hc s.rep_nonzero)).mp hs'
      have hrow : φ z ∈ W.affineCone.points := by
        rw [hrowz]
        exact hscaled _
      rw [eval_pull]
      exact (MvPolynomial.mem_zeroLocus_iff.mp hrow)
        (MvPolynomial.homogeneousComponent d f) (hcomponent d)
    have hzero (d : ℕ) : MvPolynomial.aeval y
        (linearPullback φ (MvPolynomial.homogeneousComponent d f)) = 0 :=
      MvPolynomial.mem_zeroLocus_iff.mp hy _ (hpull d)
    have hcomponentZero (d : ℕ) : MvPolynomial.aeval (φ y)
        (MvPolynomial.homogeneousComponent d f) = 0 := by
      rw [← eval_pull]
      exact hzero d
    rw [← MvPolynomial.sum_homogeneousComponent f]
    simp only [map_sum]
    exact Finset.sum_eq_zero fun d hd => hcomponentZero d
  change segrePoint p q ∈ pairClosure T at hpair
  let v := segreVector p.rep q.rep
  have hv : v ≠ 0 := segreVector_ne_zero _ _ p.rep_nonzero q.rep_nonzero
  have hmk : segrePoint p q = Projectivization.mk ℂ v hv := by
    calc
      segrePoint p q = segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero)
          (Projectivization.mk ℂ q.rep q.rep_nonzero) := by
            calc
              segrePoint p q = segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) q :=
                congrArg (fun x => segrePoint x q) p.mk_rep.symm
              _ = _ := congrArg
                (fun x => segrePoint (Projectivization.mk ℂ p.rep p.rep_nonzero) x)
                q.mk_rep.symm
      _ = Projectivization.mk ℂ v hv := segrePoint_mk p.rep q.rep p.rep_nonzero q.rep_nonzero
  have hvpoint : Projectivization.mk ℂ v hv ∈ (pairClosure T).points := by
    rw [← hmk]
    exact hpair
  have hcone : v ∈ (pairClosure T).affineCone.points :=
    (ProjectiveVariety.mem_points_mk_iff (pairClosure T) v hv).mp hvpoint
  have hrow := closureRow v hcone
  have hrowv : φ v = p.rep i • q.rep := by
    funext k
    simp [φ, segreRow, v, segreVector, Pi.smul_apply, smul_eq_mul]
  have hrow_ne : φ v ≠ 0 := by
    rw [hrowv]
    exact smul_ne_zero hi q.rep_nonzero
  have hmkq : Projectivization.mk ℂ (φ v) hrow_ne = q := by
    calc
      Projectivization.mk ℂ (φ v) hrow_ne =
          Projectivization.mk ℂ q.rep q.rep_nonzero := by
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
        exact ⟨p.rep i, hrowv.symm⟩
      _ = q := q.mk_rep
  have hqmk : Projectivization.mk ℂ (φ v) hrow_ne ∈ W.points :=
    (ProjectiveVariety.mem_points_mk_iff W (φ v) hrow_ne).2 hrow
  rw [hmkq] at hqmk
  exact hqmk

/-- closing pairs and then taking their Segre closure does not change
the original projective variety. Both inclusions are closure monotonicity. -/
theorem pairClosure_closedPairs {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) :
    pairClosure (closedPairs T) = pairClosure T := by
  classical
  let S : Set (ProjectivePoint (n * m)) :=
    {b | ∃ p q, (p, q) ∈ T ∧ segrePoint p q = b}
  let U : Set (ProjectivePoint (n * m)) :=
    {b | ∃ p q, (p, q) ∈ closedPairs T ∧ segrePoint p q = b}
  have hS : S ⊆ U := by
    rintro b ⟨p, q, hpq, rfl⟩
    have hclosed : (p, q) ∈ closedPairs T := by
      change segrePoint p q ∈ pairClosure T
      exact ProjectiveVariety.subset_closure S ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hclosed, rfl⟩
  have hU : U ⊆ (pairClosure T).points := by
    rintro b ⟨p, q, hpq, rfl⟩
    exact hpq
  have hforward : (pairClosure T).points ⊆ (pairClosure (closedPairs T)).points := by
    apply projective_closure_subset S (pairClosure (closedPairs T))
    intro b hb
    exact ProjectiveVariety.subset_closure U (hS hb)
  have hback : (pairClosure (closedPairs T)).points ⊆ (pairClosure T).points := by
    apply projective_closure_subset U (pairClosure T) hU
  apply ProjectiveVariety.ext
  rw [← (pairClosure (closedPairs T)).vanishingIdeal_points,
    ← (pairClosure T).vanishingIdeal_points]
  exact congrArg ProjectiveVariety.vanishingIdeal
    (Set.Subset.antisymm hback hforward)

theorem closedPairs_idempotent {n m : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) :
    closedPairs (closedPairs T) = closedPairs T := by
  change {w : ProjectivePoint n × ProjectivePoint m |
    segrePoint w.1 w.2 ∈ pairClosure (closedPairs T)} = closedPairs T
  rw [pairClosure_closedPairs]
  rfl

end
end DistinctDistances.TrackB
