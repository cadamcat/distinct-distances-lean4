import DistinctDistances.TrackC.MotionGeometry

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Physical pair flats are maximal null three-flats, motions.tex:279–296. -/
theorem pair_flat_geometry (x y : E 3) :
    ∃ F : Flat 6 3, (F.1 : Set (E 6)) = pairFlatSet x y ∧ maximalNull F := by
  classical
  let a : E 3 := (1 / 2 : ℝ) • (x - y)
  let b : E 3 := (1 / 2 : ℝ) • (x + y)
  let z0 : E 6 := WithLp.toLp 2 (Fin.addCases (motive := fun _ : Fin 6 => ℝ)
    (fun _ => 0) (fun i : Fin 3 => a i))
  let L : E 3 →ₗ[ℝ] E 6 :=
    { toFun := fun w => WithLp.toLp 2 (Fin.addCases (motive := fun _ : Fin 6 => ℝ)
        (fun i : Fin 3 => w i) (fun i : Fin 3 => -cross3 w b i))
      map_add' := by
        intro u v
        apply (WithLp.ext_iff 2).2
        funext i
        cases i using (Fin.addCases (m := 3) (n := 3)) with
        | left i => simp [Fin.addCases_left, cross3] <;> ring_nf
        | right i =>
            simp only [WithLp.ofLp_toLp, WithLp.ofLp_add]
            simp only [Pi.add_apply, Fin.addCases_right]
            fin_cases i <;> simp [cross3] <;> ring_nf
      map_smul' := by
        intro t u
        apply (WithLp.ext_iff 2).2
        funext i
        cases i using (Fin.addCases (m := 3) (n := 3)) with
        | left i => simp [Fin.addCases_left, cross3] <;> ring_nf
        | right i =>
            simp only [WithLp.ofLp_toLp, WithLp.ofLp_smul]
            simp only [Pi.smul_apply, Fin.addCases_right, RingHom.id_apply]
            fin_cases i <;> simp [cross3] <;> ring_nf }
  have hw0 : wCoord z0 = 0 := by
    ext i
    change Fin.addCases (motive := fun _ : Fin 6 => ℝ)
      (fun _ : Fin 3 => 0) (fun j : Fin 3 => a j) (Fin.castAdd 3 i) = 0
    exact Fin.addCases_left i
  have hc0 : cCoord z0 = a := by
    ext i
    change Fin.addCases (motive := fun _ : Fin 6 => ℝ)
      (fun _ : Fin 3 => 0) (fun j : Fin 3 => a j) (Fin.natAdd 3 i) = a i
    exact Fin.addCases_right i
  have hwL (w : E 3) : wCoord (L w) = w := by
    ext i
    change Fin.addCases (motive := fun _ : Fin 6 => ℝ)
      (fun j : Fin 3 => w j) (fun j : Fin 3 => -cross3 w b j) (Fin.castAdd 3 i) = w i
    exact Fin.addCases_left i
  have hcL (w : E 3) : cCoord (L w) = -cross3 w b := by
    ext i
    change Fin.addCases (motive := fun _ : Fin 6 => ℝ)
      (fun j : Fin 3 => w j) (fun j : Fin 3 => -cross3 w b j) (Fin.natAdd 3 i) =
        -cross3 w b i
    exact Fin.addCases_right i
  have hwAdd (u v : E 6) : wCoord (u + v) = wCoord u + wCoord v := by
    ext i
    simp [wCoord]
  have hcAdd (u v : E 6) : cCoord (u + v) = cCoord u + cCoord v := by
    ext i
    simp [cCoord]
  have hwSub (u v : E 6) : wCoord (u - v) = wCoord u - wCoord v := by
    ext i
    simp [wCoord]
  have hcSub (u v : E 6) : cCoord (u - v) = cCoord u - cCoord v := by
    ext i
    simp [cCoord]
  have hsplitExt {u v : E 6} (hw : wCoord u = wCoord v) (hc : cCoord u = cCoord v) :
      u = v := by
    apply (WithLp.ext_iff 2).2
    funext i
    cases i using (Fin.addCases (m := 3) (n := 3)) with
    | left i => simpa [wCoord] using congrArg (fun q : E 3 => q i) hw
    | right i => simpa [cCoord] using congrArg (fun q : E 3 => q i) hc
  have hLinj : Function.Injective L := by
    intro u v huv
    have h := congrArg wCoord huv
    rw [hwL, hwL] at h
    exact h
  let D : Submodule ℝ (E 6) := LinearMap.range L
  let Aflat : AffineSubspace ℝ (E 6) := AffineSubspace.mk' z0 D
  have hDfin : Module.finrank ℝ D = 3 := by
    dsimp [D]
    rw [LinearMap.finrank_range_of_inj hLinj]
    simp [E]
  have hAflatfin : Module.finrank ℝ Aflat.direction = 3 := by
    rw [AffineSubspace.direction_mk']
    exact hDfin
  let F : Flat 6 3 := ⟨Aflat, AffineSubspace.mk'_nonempty z0 D, hAflatfin⟩
  have hset : (F.1 : Set (E 6)) = pairFlatSet x y := by
    ext z
    constructor
    · intro hz
      have hzD : z -ᵥ z0 ∈ D := by
        change z ∈ Aflat at hz
        simpa [Aflat] using hz
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hzD
      have hzEq : z = L w +ᵥ z0 := by
        calc
          z = (z -ᵥ z0) +ᵥ z0 := by rw [vsub_vadd]
          _ = L w +ᵥ z0 := by rw [hw]
      have hwz : wCoord z = w := by
        rw [hzEq, vadd_eq_add, hwAdd, hwL, hw0]
        simp
      have hcz : cCoord z = a - cross3 w b := by
        rw [hzEq, vadd_eq_add, hcAdd, hcL, hc0]
        abel
      change a = cross3 (wCoord z) b + cCoord z
      rw [hwz, hcz]
      abel
    · intro hz
      change a = cross3 (wCoord z) b + cCoord z at hz
      let w := wCoord z
      have hwz : wCoord (z -ᵥ z0) = w := by
        rw [vsub_eq_sub, hwSub, hw0]
        simp [w]
      have hcz : cCoord (z -ᵥ z0) = -cross3 w b := by
        rw [vsub_eq_sub, hcSub, hc0]
        have haux : cCoord z = a - cross3 w b := by
          calc
            cCoord z = (cross3 w b + cCoord z) - cross3 w b := by abel
            _ = a - cross3 w b := by rw [← hz]
        rw [haux]
        abel
      have hL : L w = z -ᵥ z0 := by
        apply hsplitExt
        · rw [hwL, hwz]
        · rw [hcL, hcz]
      change z ∈ Aflat
      rw [AffineSubspace.mem_mk']
      exact LinearMap.mem_range.mpr ⟨w, hL⟩
  have hcrossDot (w : E 3) :
      ∑ i : Fin 3, w i * cross3 w b i = 0 := by
    simp [cross3, Fin.sum_univ_succ]
    ring_nf
  have hnull : maximalNull F := by
    intro z hz
    rw [AffineSubspace.direction_mk'] at hz
    change z ∈ LinearMap.range L at hz
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hz
    simp [splitQuadratic, hwL, hcL, hcrossDot]
  exact ⟨F, hset, hnull⟩

/-- Distinct hyperplane factors force vanishing on the containing flat,
motions.tex:409–413, 470–472. -/
private def affineLinePolynomial {n : ℕ} (x v : E n) (f : Poly n) : Polynomial ℝ :=
  MvPolynomial.eval₂Hom (algebraMap ℝ (Polynomial ℝ))
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) f

private theorem affineLinePolynomial_eval {n : ℕ} (x v : E n) (f : Poly n) (t : ℝ) :
    (affineLinePolynomial x v f).eval t = evalR f (x + t • v) := by
  let q : Polynomial ℝ →+* ℝ := Polynomial.evalRingHom t
  let vars : Fin n → Polynomial ℝ := fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)
  change q (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℝ)) vars f) = _
  rw [MvPolynomial.eval₂_comp_right q (algebraMap ℝ (Polynomial ℝ)) vars f]
  rw [MvPolynomial.eval₂_eq_eval_map]
  rw [MvPolynomial.map_map]
  have hcoeff : q.comp (algebraMap ℝ (Polynomial ℝ)) = RingHom.id ℝ := by
    ext a
    simp [q]
  rw [hcoeff, MvPolynomial.map_id]
  have hvars : q ∘ vars = fun i => (x + t • v) i := by
    funext i
    simp [vars, q, E, Pi.add_apply, Pi.smul_apply]
    ring
  rw [hvars]
  rfl

private theorem affineLinePolynomial_monomial_degree {n : ℕ} (x v : E n)
    (s : Fin n →₀ ℕ) (a : ℝ) :
    (MvPolynomial.eval₂Hom (algebraMap ℝ (Polynomial ℝ))
      (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))
      (MvPolynomial.monomial s a)).natDegree ≤ s.sum fun _ e => e := by
  rw [MvPolynomial.eval₂Hom_monomial]
  let vars : Fin n → Polynomial ℝ := fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)
  have hvars (i : Fin n) : (vars i).natDegree ≤ 1 := by
    dsimp [vars]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    apply max_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  have hprod : (s.prod fun i e => vars i ^ e).natDegree ≤ s.sum fun _ e => e := by
    rw [Finsupp.prod]
    calc
      (∏ i ∈ s.support, vars i ^ s i).natDegree ≤
          ∑ i ∈ s.support, (vars i ^ s i).natDegree :=
            Polynomial.natDegree_prod_le s.support (fun i => vars i ^ s i)
      _ ≤ ∑ i ∈ s.support, s i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Polynomial.natDegree_pow_le_of_le _ (hvars i)).trans_eq (Nat.mul_one _)
      _ = s.sum fun _ e => e := by simp [Finsupp.sum]
  have hconst : (algebraMap ℝ (Polynomial ℝ) a).natDegree ≤ 0 := by
    simp
  calc
    (algebraMap ℝ (Polynomial ℝ) a * s.prod fun i e => vars i ^ e).natDegree ≤
        (algebraMap ℝ (Polynomial ℝ) a).natDegree + (s.prod fun i e => vars i ^ e).natDegree :=
          Polynomial.natDegree_mul_le
    _ ≤ 0 + (s.sum fun _ e => e) := Nat.add_le_add hconst hprod
    _ = s.sum fun _ e => e := by simp

private theorem affineLinePolynomial_natDegree_le {n : ℕ} (x v : E n) (f : Poly n) :
    (affineLinePolynomial x v f).natDegree ≤ f.totalDegree := by
  have hrepr : affineLinePolynomial x v f =
      ∑ s ∈ f.support, MvPolynomial.eval₂Hom (algebraMap ℝ (Polynomial ℝ))
        (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))
        (MvPolynomial.monomial s (f.coeff s)) := by
    change MvPolynomial.eval₂Hom (algebraMap ℝ (Polynomial ℝ))
        (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) f = _
    conv_lhs => rw [f.as_sum]
    simp only [map_sum]
  rw [hrepr]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs =>
    (affineLinePolynomial_monomial_degree x v s (f.coeff s)).trans
      (MvPolynomial.le_totalDegree hs)

private theorem exists_generic_flat_direction {n k : ℕ} (H : Flat n (k + 1))
    (P : Finset (Flat n k)) (hsub : ∀ h ∈ P, h.1 ≤ H.1) (x : E n) (hx : x ∈ H.1)
    (hxnone : ∀ h ∈ P, x ∉ h.1) :
    ∃ v ∈ H.1.direction,
  (∀ h ∈ P, v ∉ h.1.direction) ∧
      (∀ h₁ ∈ P, ∀ h₂ ∈ P, h₁ ≠ h₂ → ∀ t : ℝ,
        ¬ (x + t • v ∈ h₁.1 ∧ x + t • v ∈ h₂.1)) := by
  classical
  let I := Sum (↥P) (↥P.offDiag)
  let bad : I → Submodule ℝ H.1.direction := fun i =>
    match i with
    | .inl h => Submodule.comap H.1.direction.subtype h.1.1.direction
    | .inr q => Submodule.comap H.1.direction.subtype
        (vectorSpan ℝ
          (insert x ((q.1.1.1 ⊓ q.1.2.1 : AffineSubspace ℝ (E n)) : Set (E n))))
  have hbad : ∀ i, bad i ≠ ⊤ := by
    intro i
    cases i with
    | inl h =>
        intro htop
        have hle : H.1.direction ≤ h.1.1.direction :=
          (Submodule.comap_subtype_eq_top.mp htop)
        have hdirle : h.1.1.direction ≤ H.1.direction :=
          AffineSubspace.direction_le (hsub h.1 h.2)
        have heq : h.1.1.direction = H.1.direction := le_antisymm hdirle hle
        have hrank := congrArg (fun V : Submodule ℝ (E n) => Module.finrank ℝ V) heq
        rw [h.1.2.2, H.2.2] at hrank
        omega
    | inr q =>
        let a : Flat n k := q.1.1
        let b : Flat n k := q.1.2
        let J : AffineSubspace ℝ (E n) := a.1 ⊓ b.1
        let W : Submodule ℝ (E n) :=
          vectorSpan ℝ (insert x (J : Set (E n)))
        have hq := Finset.mem_offDiag.mp q.2
        rcases hq with ⟨ha, hb, hab⟩
        have haH : a.1 ≤ H.1 := hsub a ha
        have hbH : b.1 ≤ H.1 := hsub b hb
        have hJH : J ≤ H.1 := le_trans inf_le_left haH
        have hsubW : insert x (J : Set (E n)) ⊆ (H.1 : Set (E n)) := by
          intro y hy
          rcases Set.mem_insert_iff.mp hy with rfl | hy
          · exact hx
          · exact hJH hy
        have hWle : W ≤ H.1.direction := by
          change vectorSpan ℝ (insert x (J : Set (E n))) ≤ H.1.direction
          rw [← direction_affineSpan]
          exact AffineSubspace.direction_le (affineSpan_le_of_subset_coe hsubW)
        have hWrank : Module.finrank ℝ W ≤ k := by
          by_cases hJ : (J : Set (E n)).Nonempty
          · have hJlt : J < a.1 := by
              refine lt_of_le_of_ne inf_le_left ?_
              intro hEq
              have hable : a.1 ≤ b.1 := by
                intro y hy
                have hyJ : y ∈ J := by simpa [hEq] using hy
                exact (AffineSubspace.mem_inf_iff y a.1 b.1).mp hyJ |>.2
              have hdirle : a.1.direction ≤ b.1.direction :=
                AffineSubspace.direction_le hable
              have hdireq : a.1.direction = b.1.direction :=
                Submodule.eq_of_le_of_finrank_eq hdirle (by rw [a.2.2, b.2.2])
              obtain ⟨y, hy⟩ := a.2.1
              have hab' : a.1 = b.1 :=
                AffineSubspace.ext_of_direction_eq hdireq ⟨y, hy, hable hy⟩
              have hab'' : a = b := Subtype.ext hab'
              exact hab hab''
            have hJdir : J.direction < a.1.direction :=
              AffineSubspace.direction_lt_of_nonempty hJlt hJ
            have hJrank : Module.finrank ℝ J.direction < k := by
              calc
                Module.finrank ℝ J.direction < Module.finrank ℝ a.1.direction :=
                  Submodule.finrank_lt_finrank_of_lt hJdir
                _ = k := a.2.2
            calc
              Module.finrank ℝ W ≤ Module.finrank ℝ J.direction + 1 :=
                finrank_vectorSpan_insert_le J x
              _ ≤ k := by omega
          · have hJempty : (J : Set (E n)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hJ
            have hWbot : W = ⊥ := by
              simp [W, hJempty, vectorSpan_def]
            rw [hWbot, finrank_bot]
            exact Nat.zero_le _
        intro htop
        have hVleW : H.1.direction ≤ W := Submodule.comap_subtype_eq_top.mp htop
        have hVW : W = H.1.direction := le_antisymm hWle hVleW
        have hrank := congrArg (fun V : Submodule ℝ (E n) => Module.finrank ℝ V) hVW
        rw [H.2.2] at hrank
        omega
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨v, v.property, ?_, ?_⟩
  · intro h hh
    have := hv (Sum.inl ⟨h, hh⟩)
    simpa [bad] using this
  · intro h₁ hh₁ h₂ hh₂ hne t hboth
    let q : ↥P.offDiag :=
      ⟨(h₁, h₂), Finset.mem_offDiag.mpr ⟨hh₁, hh₂, hne⟩⟩
    let J : AffineSubspace ℝ (E n) := h₁.1 ⊓ h₂.1
    let W : Submodule ℝ (E n) :=
      vectorSpan ℝ (insert x (J : Set (E n)))
    have hnotW : (v : E n) ∉ W := by
      have h := hv (Sum.inr q)
      simpa [bad, q, J, W] using h
    have hJ : x + t • (v : E n) ∈ J :=
      (AffineSubspace.mem_inf_iff _ _ _).2 hboth
    by_cases ht : t = 0
    · subst t
      exact hxnone h₁ hh₁ (by simpa using hboth.1)
    · have hdiff : (x + t • (v : E n)) -ᵥ x ∈ W :=
        vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem x hJ)
          (Set.mem_insert x (J : Set (E n)))
      have hmul : t • (v : E n) ∈ W := by
        simpa [W, vectorSpan_def, vsub_eq_sub] using hdiff
      have hvW : (v : E n) ∈ W := (W.smul_mem_iff ht).mp hmul
      exact hnotW hvW

theorem polynomial_many_hyperplanes (n k : ℕ) (H : Flat n (k + 1))
    (P : Finset (Flat n k)) (f : Poly n)
    (hP : ∀ h ∈ P, h.1 ≤ H.1 ∧ onPolynomial f h) (hdeg : f.totalDegree < P.card) :
    onPolynomial f H := by
  classical
  intro x hx
  by_cases hxP : ∃ h ∈ P, x ∈ h.1
  · rcases hxP with ⟨h, hh, hx⟩
    exact (hP h hh).2 x hx
  · have hxnone : ∀ h ∈ P, x ∉ h.1 := by
      intro h hh hx
      exact hxP ⟨h, hh, hx⟩
    have hsub : ∀ h ∈ P, h.1 ≤ H.1 := fun h hh => (hP h hh).1
    obtain ⟨v, hvH, hvflat, hvpair⟩ :=
      exists_generic_flat_direction H P hsub x hx hxnone
    let L : AffineSubspace ℝ (E n) :=
      AffineSubspace.mk' x (Submodule.span ℝ {(v : E n)})
    have hspanH : Submodule.span ℝ {(v : E n)} ≤ H.1.direction := by
      refine Submodule.span_le.2 ?_
      intro w hw
      have hw' : w = (v : E n) := by simpa using hw
      rw [hw']
      exact hvH
    have hLle : L ≤ H.1 := by
      change AffineSubspace.mk' x (Submodule.span ℝ {(v : E n)}) ≤ H.1
      rw [← AffineSubspace.mk'_eq hx]
      exact (AffineSubspace.mk'_le_mk'_iff x).2 hspanH
    have hlineInter (h : Flat n k) (hh : h ∈ P) :
        ((h.1 : Set (E n)) ∩ (L : Set (E n))).Nonempty := by
      have hdirle : h.1.direction ≤ H.1.direction :=
        AffineSubspace.direction_le (hsub h hh)
      have hnot : (v : E n) ∉ h.1.direction := hvflat h hh
      have hsupdim := Submodule.finrank_sup_span_singleton hnot
      rw [h.2.2] at hsupdim
      have hsup_le : h.1.direction ⊔ Submodule.span ℝ {(v : E n)} ≤ H.1.direction :=
        sup_le hdirle hspanH
      have hsup_eq : h.1.direction ⊔ Submodule.span ℝ {(v : E n)} = H.1.direction := by
        apply Submodule.eq_of_le_of_finrank_eq hsup_le
        rw [hsupdim, H.2.2]
      have hjoin_le : h.1 ⊔ L ≤ H.1 := sup_le (hsub h hh) hLle
      have hdir_join : (h.1 ⊔ L).direction = H.1.direction := by
        apply le_antisymm (AffineSubspace.direction_le hjoin_le)
        calc
          H.1.direction = h.1.direction ⊔ L.direction := by
            simpa [L, AffineSubspace.direction_mk'] using hsup_eq.symm
          _ ≤ (h.1 ⊔ L).direction := AffineSubspace.sup_direction_le _ _
      have hjoin_nonempty : ((h.1 ⊔ L : AffineSubspace ℝ (E n)) : Set (E n)).Nonempty := by
        obtain ⟨y, hy⟩ := h.2.1
        exact ⟨y, (le_sup_left : h.1 ≤ h.1 ⊔ L) hy⟩
      have hjoin_eq : h.1 ⊔ L = H.1 :=
        AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir_join hjoin_nonempty hjoin_le
      by_contra hdis
      have hempty : ((h.1 : Set (E n)) ∩ (L : Set (E n))) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hdis
      have hlt := AffineSubspace.sup_direction_lt_of_nonempty_of_inter_empty
        h.2.1 (AffineSubspace.mk'_nonempty x _) hempty
      rw [hjoin_eq] at hlt
      have hlt' : h.1.direction ⊔ Submodule.span ℝ {(v : E n)} < H.1.direction := by
        simpa [L, AffineSubspace.direction_mk'] using hlt
      rw [hsup_eq] at hlt'
      exact (lt_irrefl _) hlt'
    let linePoint : ℝ → E n := fun t => x + t • (v : E n)
    have hparameter (h : ↥P) : ∃ t : ℝ, linePoint t ∈ h.1.1 := by
      obtain ⟨y, hy⟩ := hlineInter h.1 h.2
      have hyline : y -ᵥ x ∈ Submodule.span ℝ {(v : E n)} := by
        simpa [L, AffineSubspace.mem_mk'] using hy.2
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hyline
      refine ⟨t, ?_⟩
      have hyEq : y = x + t • (v : E n) := by
        calc
          y = (y -ᵥ x) +ᵥ x := (vsub_vadd y x).symm
          _ = t • (v : E n) +ᵥ x := by rw [ht]
          _ = x + t • (v : E n) := by simp [vadd_eq_add, add_comm]
      simpa [linePoint, hyEq] using hy.1
    let τ : ↥P → ℝ := fun h => Classical.choose (hparameter h)
    have hτmem (h : ↥P) : linePoint (τ h) ∈ h.1.1 :=
      Classical.choose_spec (hparameter h)
    have hτinj : Function.Injective τ := by
      intro h₁ h₂ heq
      by_contra hne
      have hflatne : h₁.1 ≠ h₂.1 := by
        intro hflat
        exact hne (Subtype.ext hflat)
      have havoid := hvpair h₁.1 h₁.2 h₂.1 h₂.2 hflatne (τ h₁)
      apply havoid
      refine ⟨hτmem h₁, ?_⟩
      simpa [linePoint, heq] using hτmem h₂
    let roots : Finset ℝ := Finset.univ.image τ
    have hroot : ∀ r ∈ roots, (affineLinePolynomial x v f).eval r = 0 := by
      intro r hr
      rcases Finset.mem_image.mp hr with ⟨h, -, rfl⟩
      rw [affineLinePolynomial_eval]
      exact (hP h.1 h.2).2 (linePoint (τ h)) (hτmem h)
    have hrootsCard : roots.card = P.card := by
      dsimp [roots]
      rw [Finset.card_image_of_injective _ hτinj]
      simp
    have hdegree : (affineLinePolynomial x v f).natDegree < roots.card := by
      rw [hrootsCard]
      exact (affineLinePolynomial_natDegree_le x v f).trans_lt hdeg
    have hpzero : affineLinePolynomial x v f = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        (affineLinePolynomial x v f) roots hroot hdegree
    have hzeroEval : (affineLinePolynomial x v f).eval 0 = 0 := by
      simpa using congrArg (fun p : Polynomial ℝ => p.eval 0) hpzero
    rw [affineLinePolynomial_eval] at hzeroEval
    simpa using hzeroEval

/-- Raised gradient belongs to a self-orthogonal null direction,
motions.tex:416–424. -/
theorem raised_gradient_null_flat (H : Flat 6 3) (hnull : maximalNull H)
    (f : Poly 6) (hf : onPolynomial f H) (z : E 6) (hz : z ∈ H.1) :
    raisedGradient f z ∈ H.1.direction := by
  classical
  let D : Submodule ℝ (E 6) := H.1.direction
  have hDfin : Module.finrank ℝ D = 3 := H.2.2
  let gradVec : E 6 := WithLp.toLp 2 (fun i => evalR (MvPolynomial.pderiv i f) z)
  let σ : Fin 6 → Fin 6 := Fin.addCases (motive := fun _ : Fin 6 => Fin 6)
    (fun i : Fin 3 => i.natAdd 3) (fun i : Fin 3 => i.castAdd 3)
  have hσleft (i : Fin 3) : σ (i.castAdd 3) = i.natAdd 3 := by
    change Fin.addCases (motive := fun _ : Fin 6 => Fin 6)
      (fun j : Fin 3 => j.natAdd 3) (fun j : Fin 3 => j.castAdd 3) (i.castAdd 3) = _
    exact Fin.addCases_left i
  have hσright (i : Fin 3) : σ (i.natAdd 3) = i.castAdd 3 := by
    change Fin.addCases (motive := fun _ : Fin 6 => Fin 6)
      (fun j : Fin 3 => j.natAdd 3) (fun j : Fin 3 => j.castAdd 3) (i.natAdd 3) = _
    exact Fin.addCases_right i
  have hAddNat (i : Fin 3) : i.addNat 3 = i.natAdd 3 := by
    apply Fin.ext
    simp
  have hcasesRightNat (i : Fin 3) :
      Fin.addCases (motive := fun _ : Fin 6 => Fin 6)
        (fun j : Fin 3 => j.addNat 3) (fun j : Fin 3 => j.castAdd 3) (i.natAdd 3) =
        i.castAdd 3 := Fin.addCases_right i
  have hcasesRightAdd (i : Fin 3) :
      Fin.addCases (motive := fun _ : Fin 6 => Fin 6)
        (fun j : Fin 3 => j.addNat 3) (fun j : Fin 3 => j.castAdd 3) (i.addNat 3) =
        i.castAdd 3 := by
    have h := hcasesRightNat i
    rw [← hAddNat i] at h
    exact h
  let J : E 6 →ₗ[ℝ] E 6 :=
    { toFun := fun x => WithLp.toLp 2 (fun i => x (σ i))
      map_add' := by
        intro x y
        apply (WithLp.ext_iff 2).2
        funext i
        simp [σ]
      map_smul' := by
        intro r x
        apply (WithLp.ext_iff 2).2
        funext i
        simp [σ] }
  have hJw (x : E 6) : wCoord (J x) = cCoord x := by
    ext i
    change x (σ (i.castAdd 3)) = x (i.natAdd 3)
    rw [hσleft]
  have hJc (x : E 6) : cCoord (J x) = wCoord x := by
    ext i
    change x (σ (i.natAdd 3)) = x (i.castAdd 3)
    rw [hσright]
  have hsplitExt {a b : E 6} (hw : wCoord a = wCoord b) (hc : cCoord a = cCoord b) : a = b := by
    apply (WithLp.ext_iff 2).2
    funext i
    cases i using (Fin.addCases (m := 3) (n := 3)) with
    | left i => simpa [wCoord] using congrArg (fun q : E 3 => q i) hw
    | right i => simpa [cCoord] using congrArg (fun q : E 3 => q i) hc
  have hJinvol (x : E 6) : J (J x) = x := by
    apply hsplitExt
    · rw [hJw, hJc]
    · rw [hJc, hJw]
  have hRaised : raisedGradient f z = J gradVec := by
    apply hsplitExt
    · ext i
      simp [wCoord, cCoord, raisedGradient, gradVec, J, σ, Fin.addCases_left,
        Fin.addCases_right, WithLp.ofLp_toLp]
    · ext i
      simp [cCoord, wCoord, raisedGradient, gradVec, J, σ, Fin.addCases_left,
        Fin.addCases_right, WithLp.ofLp_toLp]
      rw [hAddNat i, Fin.addCases_right]
      rw [hcasesRightNat i]
  have hwAdd (a b : E 6) : wCoord (a + b) = wCoord a + wCoord b := by
    ext i
    simp [wCoord]
  have hcAdd (a b : E 6) : cCoord (a + b) = cCoord a + cCoord b := by
    ext i
    simp [cCoord]
  have hquad (a b : E 6) : splitQuadratic (a + b) = splitQuadratic a + splitQuadratic b +
      ∑ i : Fin 3, (wCoord a i * cCoord b i + cCoord a i * wCoord b i) := by
    simp only [splitQuadratic, hwAdd, hcAdd]
    calc
      (∑ i : Fin 3, (wCoord a i + wCoord b i) * (cCoord a i + cCoord b i)) =
          ∑ i : Fin 3, (wCoord a i * cCoord a i + wCoord b i * cCoord b i +
            (wCoord a i * cCoord b i + cCoord a i * wCoord b i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by simp [Finset.sum_add_distrib, add_assoc]
  have hinnerJ (a b : E 6) :
      inner ℝ (J a) b = ∑ i : Fin 3, (wCoord a i * cCoord b i + cCoord a i * wCoord b i) := by
    rw [PiLp.inner_apply]
    change (∑ i : Fin (3 + 3), inner ℝ ((J a) i) (b i)) = _
    simp only [Fin.sum_univ_add]
    rw [← Finset.sum_add_distrib]
    simp [J, σ, hσleft, hσright, wCoord, cCoord, Fin.addCases_left, Fin.addCases_right,
      WithLp.ofLp_toLp, mul_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcasesRightAdd]
    ring
  have horth (a b : E 6) (ha : a ∈ D) (hb : b ∈ D) : inner ℝ (J a) b = 0 := by
    rw [hinnerJ]
    have ha0 : splitQuadratic a = 0 := hnull a ha
    have hb0 : splitQuadratic b = 0 := hnull b hb
    have hab0 : splitQuadratic (a + b) = 0 := hnull (a + b) (D.add_mem ha hb)
    rw [hquad a b] at hab0
    linarith
  have hMapLe : D.map J ≤ Dᗮ := by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨a, ha, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro b hb
    exact horth a b ha hb
  let JEquiv : E 6 ≃ₗ[ℝ] E 6 := LinearEquiv.ofInvolutive J hJinvol
  have hJLin : (JEquiv : E 6 →ₗ[ℝ] E 6) = J := rfl
  have hMapFin : Module.finrank ℝ (D.map J) = 3 := by
    calc
      Module.finrank ℝ (D.map J) = Module.finrank ℝ D := by
        rw [← hJLin, LinearEquiv.finrank_map_eq JEquiv D]
      _ = 3 := hDfin
  have hOrthFin : Module.finrank ℝ Dᗮ = 3 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal D
    have hE : Module.finrank ℝ (E 6) = 6 := by simp [E]
    rw [hDfin, hE] at hsum
    omega
  have hMapEq : D.map J = Dᗮ :=
    Submodule.eq_of_le_of_finrank_eq hMapLe (by rw [hMapFin, hOrthFin])
  have hDirectionDerivative (u : E 6) (hu : u ∈ D) :
      ∑ i : Fin 6, u i * evalR (MvPolynomial.pderiv i f) z = 0 := by
    let subst : Fin 6 → Polynomial ℝ := fun i =>
      Polynomial.C (z i) + Polynomial.C (u i) * Polynomial.X
    let φ : Poly 6 →ₐ[ℝ] Polynomial ℝ := MvPolynomial.aeval subst
    letI : Algebra (Poly 6) (Polynomial ℝ) := φ.toRingHom.toAlgebra
    let Ddir : Derivation ℝ (Poly 6) (Poly 6) :=
      MvPolynomial.mkDerivation ℝ (fun i => MvPolynomial.C (u i))
    let φlin : Poly 6 →ₗ[Poly 6] Polynomial ℝ :=
      { toFun := φ
        map_add' := map_add φ
        map_smul' := by
          intro a p
          change φ (a * p) = φ a * φ p
          exact map_mul φ a p }
    let Dpush : Derivation ℝ (Poly 6) (Polynomial ℝ) := φlin.compDer Ddir
    let Dsub : Derivation ℝ (Poly 6) (Polynomial ℝ) :=
      { toLinearMap :=
          { toFun := fun p => Polynomial.derivative (φ p)
            map_add' := by intro p q; simp
            map_smul' := by intro r p; simp }
        map_one_eq_zero' := by simp
        leibniz' := by
          intro p q
          change Polynomial.derivative (φ (p * q)) =
            φ p * Polynomial.derivative (φ q) + φ q * Polynomial.derivative (φ p)
          rw [map_mul φ, Polynomial.derivative_mul]
          ring }
    have hDsubX (i : Fin 6) : Dsub (MvPolynomial.X i) = Polynomial.C (u i) := by
      simp [Dsub, φ, subst, Polynomial.derivative_add]
    have hDpushX (i : Fin 6) : Dpush (MvPolynomial.X i) = Polynomial.C (u i) := by
      simp [Dpush, φlin, Ddir]
    have hDsub : Dsub = Dpush := by
      apply MvPolynomial.derivation_ext
      intro i
      exact (hDsubX i).trans (hDpushX i).symm
    have hchain : Polynomial.derivative (φ f) = φ (Ddir f) := by
      have h := congrArg (fun d : Derivation ℝ (Poly 6) (Polynomial ℝ) => d f) hDsub
      simpa [Dsub, Dpush, φlin] using h
    have hDdir : Ddir f = ∑ i : Fin 6, u i • MvPolynomial.pderiv i f := by
      have hder : Ddir = ∑ i : Fin 6, u i • MvPolynomial.pderiv i := by
        apply MvPolynomial.derivation_ext
        intro j
        simp [Ddir, Pi.single_apply, Finset.sum_ite_eq', MvPolynomial.C_eq_smul_one]
      exact congrArg (fun d : Derivation ℝ (Poly 6) (Poly 6) => d f) hder
    have hEvalSubst (t : ℝ) (p : Poly 6) :
        Polynomial.eval t (φ p) = evalR p (z + t • u) := by
      change Polynomial.eval t (MvPolynomial.aeval subst p) =
        MvPolynomial.eval (fun i => (z + t • u) i) p
      rw [MvPolynomial.aeval_def]
      change (Polynomial.evalRingHom t) (MvPolynomial.eval₂
        (algebraMap ℝ (Polynomial ℝ)) subst p) = _
      rw [MvPolynomial.eval₂_comp_right, MvPolynomial.eval₂_map]
      have hk : (Polynomial.evalRingHom t).comp (algebraMap ℝ (Polynomial ℝ)) =
          RingHom.id ℝ := by
        ext r
        simp
      rw [hk]
      have hvars : (Polynomial.evalRingHom t ∘ subst) = fun i => (z + t • u) i := by
        funext i
        change Polynomial.eval t
          (Polynomial.C (z i) + Polynomial.C (u i) * Polynomial.X) = (z + t • u) i
        have hcoord : (z + t • u) i = z i + t * u i := by simp
        rw [hcoord]
        simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
          Polynomial.eval_X]
        ring
      rw [hvars, MvPolynomial.eval₂_eq_eval_map]
      rw [MvPolynomial.map_id]
    have hpath (t : ℝ) : Polynomial.eval t (φ f) = 0 := by
      have hpoint : z + t • u ∈ H.1 := by
        have hu' : t • u ∈ H.1.direction := Submodule.smul_mem _ _ hu
        have h := AffineSubspace.vadd_mem_of_mem_direction hu' hz
        simpa [vadd_eq_add, add_comm] using h
      have hvan := hf (z + t • u) hpoint
      rw [hEvalSubst t f]
      exact hvan
    have hderivConst : deriv (fun t : ℝ => Polynomial.eval t (φ f)) 0 = 0 := by
      rw [show (fun t : ℝ => Polynomial.eval t (φ f)) = fun _ => (0 : ℝ) from funext hpath]
      simp
    have hderivEval : Polynomial.eval 0 (Polynomial.derivative (φ f)) = 0 := by
      have h := (φ f).hasDerivAt (0 : ℝ)
      calc
        Polynomial.eval 0 (Polynomial.derivative (φ f)) = deriv (fun t : ℝ => Polynomial.eval t (φ f)) 0 :=
          h.deriv.symm
        _ = 0 := hderivConst
    have hEvalD : Polynomial.eval 0 (φ (Ddir f)) =
        ∑ i : Fin 6, u i * evalR (MvPolynomial.pderiv i f) z := by
      rw [hDdir, hEvalSubst]
      simp [evalR]
    rw [hchain, hEvalD] at hderivEval
    exact hderivEval
  have hgradOrth : gradVec ∈ Dᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    have h := hDirectionDerivative u hu
    simpa [gradVec, PiLp.inner_apply, mul_comm] using h
  have hgradMap : gradVec ∈ D.map J := by rw [hMapEq]; exact hgradOrth
  obtain ⟨v, hvD, hvEq⟩ := Submodule.mem_map.mp hgradMap
  have hJraised : J (raisedGradient f z) = gradVec := by
    rw [hRaised]
    exact hJinvol gradVec
  have hEq : raisedGradient f z = v := by
    apply JEquiv.injective
    calc
      J (raisedGradient f z) = gradVec := hJraised
      _ = J v := hvEq.symm
  rw [hEq]
  exact hvD

end DistinctDistances.TrackC
