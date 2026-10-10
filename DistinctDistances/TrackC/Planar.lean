import DistinctDistances.TrackC.Incidence

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def planarJ (x : E 2) : E 2 := WithLp.toLp 2 ![-x 1, x 0]
def cayleySet (x y : E 2) : Set (E 3) :=
  {z | WithLp.toLp 2 ![z 1, z 2] =
    (1 / 2 : ℝ) • (x - y) - z 0 • planarJ ((1 / 2 : ℝ) • (x + y))}

def planarDirect (g : Motion 2) : Prop := LinearMap.det g.toAffineEquiv.linear.toLinearMap = 1
def inPlanarChart (g : Motion 2) : Prop :=
  LinearMap.ker (g.toAffineEquiv.linear.toLinearMap + LinearMap.id) = ⊥

def cayleyLines (U V : Finset (E 2)) : Set (Line 3) :=
  {l | ∃ x ∈ U, ∃ y ∈ V, (l.1 : Set (E 3)) = cayleySet x y}

private lemma planarJ_injective_early : Function.Injective (planarJ) := by
  intro u v huv
  apply PiLp.ext
  intro i
  fin_cases i
  · have h := congrArg (fun w : E 2 => w 1) huv
    simpa [planarJ] using h
  · have h := congrArg (fun w : E 2 => w 0) huv
    simpa [planarJ] using h

private lemma planarJ_norm (x : E 2) : ‖planarJ x‖ = ‖x‖ := by
  have h₁ := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (planarJ x)
  have h₂ := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) x
  have hsq : ‖planarJ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [h₁, h₂]
    simp [planarJ, Fin.sum_univ_succ]
    ring
  nlinarith [norm_nonneg (planarJ x), norm_nonneg x]

private lemma planarJ_inner (x : E 2) : inner ℝ x (planarJ x) = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, planarJ]
  ring

private lemma planarJ_not_mem_span (x : E 2) (hx : x ≠ 0) :
    planarJ x ∉ ℝ ∙ x := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have horth := planarJ_inner x
  rw [← ha, inner_smul_right] at horth
  have hxx : inner ℝ x x ≠ 0 := inner_self_ne_zero.mpr hx
  have ha0 : a = 0 := (mul_eq_zero.mp horth).resolve_right hxx
  have hJ0 : planarJ x = 0 := by simpa [ha0] using ha.symm
  exact hx (planarJ_injective_early (by simpa [planarJ] using hJ0))

private lemma planarJ_span_top (x : E 2) (hx : x ≠ 0) :
    (ℝ ∙ x) ⊔ (ℝ ∙ planarJ x) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [Submodule.finrank_sup_span_singleton (planarJ_not_mem_span x hx),
    finrank_span_singleton hx]
  simp [E]

private lemma planar_same_norm_line {D : Submodule ℝ (E 2)}
    (hD : Module.finrank ℝ D = 1) {v w : E 2}
    (hv : v ∈ D) (hw : w ∈ D) (hn : ‖v‖ = ‖w‖) : v = w ∨ v = -w := by
  by_cases hv0 : v = 0
  · left
    have hw0 : w = 0 := by
      apply norm_eq_zero.mp
      rw [← hn, hv0]
      simp
    simp [hv0, hw0]
  · have hspan : D = ℝ ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hD hv hv0
    have hw' : w ∈ ℝ ∙ v := by rw [← hspan]; exact hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw'
    have habs : |a| = 1 := by
      have hn' := hn
      rw [← ha, norm_smul, Real.norm_eq_abs] at hn'
      have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      nlinarith
    by_cases ha0 : 0 ≤ a
    · have haeq : a = 1 := by
        rw [abs_of_nonneg ha0] at habs
        linarith
      left
      simpa [haeq] using ha
    · have haeq : a = -1 := by
        rw [abs_of_nonpos (le_of_not_ge ha0)] at habs
        linarith
      right
      have hneg : w = -v := by simpa [haeq] using ha.symm
      rw [hneg]
      simp

private lemma planar_linear_iso_J_options (f : E 2 ≃ₗᵢ[ℝ] E 2) (u v : E 2)
    (hu : u ≠ 0) (hfu : f u = v) :
    f (planarJ u) = planarJ v ∨ f (planarJ u) = -planarJ v := by
  have hv : v ≠ 0 := by
    intro hv
    apply hu
    apply f.injective
    rw [hfu, hv]
    simp
  let D : Submodule ℝ (E 2) := (ℝ ∙ v)ᗮ
  have hD : Module.finrank ℝ D = 1 := by
    change Module.finrank ℝ ↥((ℝ ∙ v)ᗮ) = 1
    have hsum := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ v)
    rw [finrank_span_singleton hv, finrank_euclideanSpace] at hsum
    simp only [Fintype.card_fin] at hsum
    omega
  have hperp : inner ℝ v (f (planarJ u)) = 0 := by
    calc
      inner ℝ v (f (planarJ u)) = inner ℝ (f u) (f (planarJ u)) := by rw [hfu]
      _ = inner ℝ u (planarJ u) := f.inner_map_map u (planarJ u)
      _ = 0 := planarJ_inner u
  have hmem : f (planarJ u) ∈ D := by
    change f (planarJ u) ∈ (ℝ ∙ v)ᗮ
    rw [Submodule.mem_orthogonal]
    intro z hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz
    calc
      inner ℝ z (f (planarJ u)) = inner ℝ (a • v) (f (planarJ u)) := by rw [ha]
      _ = (starRingEnd ℝ) a * inner ℝ v (f (planarJ u)) := inner_smul_left _ _ _
      _ = 0 := by simp [hperp]
  have hmemJ : planarJ v ∈ D := by
    change planarJ v ∈ (ℝ ∙ v)ᗮ
    rw [Submodule.mem_orthogonal]
    intro z hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz
    calc
      inner ℝ z (planarJ v) = inner ℝ (a • v) (planarJ v) := by rw [ha]
      _ = (starRingEnd ℝ) a * inner ℝ v (planarJ v) := inner_smul_left _ _ _
      _ = 0 := by simp [planarJ_inner]
  have hJv : planarJ v ≠ 0 := by
    intro h
    exact hv (planarJ_injective_early (by simpa [planarJ] using h))
  have hnorm : ‖f (planarJ u)‖ = ‖planarJ v‖ := by
    calc
      ‖f (planarJ u)‖ = ‖planarJ u‖ := f.norm_map _
      _ = ‖u‖ := planarJ_norm u
      _ = ‖v‖ := by rw [← hfu, f.norm_map]
      _ = ‖planarJ v‖ := (planarJ_norm v).symm
  exact planar_same_norm_line hD hmem hmemJ hnorm

private lemma planar_matches_pair_exists (U V : Finset (E 2)) (g : Motion 2)
    (hg : g ∈ richMotions U V 2) :
    ∃ p : E 2 × E 2, p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2 ∧
      g p.1 ∈ V ∧ g p.2 ∈ V := by
  have hcardReal : (2 : ℝ) ≤ (matchCount U V g : ℝ) := by
    change (2 : ℝ) ≤ (matchCount U V g : ℝ) at hg
    exact hg
  have hcard : 2 ≤ (matchPoints U V g).card := by
    exact_mod_cast (by simpa [matchCount] using hcardReal)
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    Finset.one_lt_card_iff.mp (show 1 < (matchPoints U V g).card by omega)
  have hx' : x ∈ U ∧ g x ∈ V := by simpa [matchPoints] using hx
  have hy' : y ∈ U ∧ g y ∈ V := by simpa [matchPoints] using hy
  exact ⟨(x, y), hx'.1, hy'.1, hxy, hx'.2, hy'.2⟩

private noncomputable def planarMotionPair (U V : Finset (E 2)) (g : Motion 2) : E 2 × E 2 :=
  if hg : g ∈ richMotions U V 2 then Classical.choose (planar_matches_pair_exists U V g hg)
  else (0, 0)

private lemma planarMotionPair_spec (U V : Finset (E 2)) (g : Motion 2)
    (hg : g ∈ richMotions U V 2) :
    (planarMotionPair U V g).1 ∈ U ∧ (planarMotionPair U V g).2 ∈ U ∧
      (planarMotionPair U V g).1 ≠ (planarMotionPair U V g).2 ∧
      g (planarMotionPair U V g).1 ∈ V ∧ g (planarMotionPair U V g).2 ∈ V := by
  simp only [planarMotionPair, dif_pos hg]
  exact Classical.choose_spec (planar_matches_pair_exists U V g hg)

private noncomputable def planarMotionCode (U V : Finset (E 2)) (g : Motion 2) :
    ((E 2 × E 2) × (E 2 × E 2)) × Bool :=
  let p := planarMotionPair U V g
  let q := (g p.1, g p.2)
  ((p, q), decide (g.linearIsometryEquiv (planarJ (p.2 -ᵥ p.1)) =
    planarJ (q.2 -ᵥ q.1)))

private noncomputable def planarMotionCodes (U V : Finset (E 2)) :
    Finset (((E 2 × E 2) × (E 2 × E 2)) × Bool) :=
  ((U.product U).product (V.product V)).product Finset.univ

/-- Two ordered matches determine at most two planar isometries, CI:345–346. -/
theorem planar_motions_finite (U V : Finset (E 2)) : (richMotions U V 2).Finite := by
  classical
  let code := planarMotionCode U V
  let codes := planarMotionCodes U V
  have hsubset : code '' richMotions U V 2 ⊆ (codes : Set _) := by
    rintro c ⟨g, hg, rfl⟩
    let p := planarMotionPair U V g
    let q := (g p.1, g p.2)
    obtain ⟨hp1, hp2, hpne, hq1, hq2⟩ := planarMotionPair_spec U V g hg
    change ((p, q), decide (g.linearIsometryEquiv (planarJ (p.2 -ᵥ p.1)) =
      planarJ (q.2 -ᵥ q.1))) ∈ codes
    exact Finset.mem_product.mpr ⟨
      Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩,
        Finset.mem_product.mpr ⟨hq1, hq2⟩⟩,
      Finset.mem_univ _⟩
  have himage : (code '' richMotions U V 2).Finite :=
    (codes.finite_toSet).subset hsubset
  have hinj : Set.InjOn code (richMotions U V 2) := by
    intro g hg h hh hcode
    let p := planarMotionPair U V g
    let p' := planarMotionPair U V h
    let q := (g p.1, g p.2)
    let q' := (h p'.1, h p'.2)
    change ((p, q), decide (g.linearIsometryEquiv (planarJ (p.2 -ᵥ p.1)) =
      planarJ (q.2 -ᵥ q.1))) =
      ((p', q'), decide (h.linearIsometryEquiv (planarJ (p'.2 -ᵥ p'.1)) =
      planarJ (q'.2 -ᵥ q'.1))) at hcode
    have hpq := congrArg Prod.fst hcode
    have hp : p = p' := congrArg Prod.fst hpq
    have hq : q = q' := congrArg Prod.snd hpq
    have hs : decide (g.linearIsometryEquiv (planarJ (p.2 -ᵥ p.1)) =
        planarJ (q.2 -ᵥ q.1)) =
      decide (h.linearIsometryEquiv (planarJ (p'.2 -ᵥ p'.1)) =
        planarJ (q'.2 -ᵥ q'.1)) := congrArg Prod.snd hcode
    have hp1 : p.1 = p'.1 := congrArg Prod.fst hp
    have hp2 : p.2 = p'.2 := congrArg Prod.snd hp
    have hq1 : q.1 = q'.1 := congrArg Prod.fst hq
    have hq2 : q.2 = q'.2 := congrArg Prod.snd hq
    have hval1 : g p.1 = h p.1 := by
      calc
        g p.1 = q.1 := rfl
        _ = q'.1 := hq1
        _ = h p.1 := by dsimp [q']; rw [← hp1]
    have hval2 : g p.2 = h p.2 := by
      calc
        g p.2 = q.2 := rfl
        _ = q'.2 := hq2
        _ = h p.2 := by dsimp [q']; rw [← hp2]
    have hspecG := planarMotionPair_spec U V g hg
    have hspecH := planarMotionPair_spec U V h hh
    have hpne : p.1 ≠ p.2 := by simpa [p] using hspecG.2.2.1
    let u : E 2 := p.2 -ᵥ p.1
    let v : E 2 := q.2 -ᵥ q.1
    have hu : u ≠ 0 := by
      intro hu0
      apply hpne
      exact (vsub_eq_zero_iff_eq.mp (by simpa [u] using hu0)).symm
    have hgu : g.linearIsometryEquiv u = v := by
      simpa [u, v, q] using g.map_vsub p.2 p.1
    have hhu : h.linearIsometryEquiv u = v := by
      calc
        h.linearIsometryEquiv u = h p.2 -ᵥ h p.1 := by simpa [u] using h.map_vsub p.2 p.1
        _ = g p.2 -ᵥ g p.1 := by rw [hval2, hval1]
        _ = v := by simp [v, q]
    have hsign : decide (g.linearIsometryEquiv (planarJ u) = planarJ v) =
        decide (h.linearIsometryEquiv (planarJ u) = planarJ v) := by
      have hs' := hs
      rw [← hp, ← hq] at hs'
      change decide (g.linearIsometryEquiv (planarJ u) = planarJ v) =
        decide (h.linearIsometryEquiv (planarJ u) = planarJ v) at hs'
      exact hs'
    have hJg := planar_linear_iso_J_options g.linearIsometryEquiv u v hu hgu
    have hJh := planar_linear_iso_J_options h.linearIsometryEquiv u v hu hhu
    have hneg_ne : -planarJ v ≠ planarJ v := by
      intro hneg
      have hsum : planarJ v + planarJ v = 0 := by
        calc
          planarJ v + planarJ v = planarJ v + -planarJ v := by
            exact congrArg (fun z : E 2 => planarJ v + z) hneg.symm
          _ = 0 := add_neg_cancel _
      have hJzero : planarJ v = 0 := by
        have htwo : (2 : ℝ) • planarJ v = 0 := by
          simpa only [two_smul] using hsum
        exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      have hv : v ≠ 0 := by
        intro hv
        apply hu
        have hgu0 : g.linearIsometryEquiv u = g.linearIsometryEquiv 0 := by
          rw [hgu, hv]
          simp
        exact g.linearIsometryEquiv.injective hgu0
      exact hv (planarJ_injective_early (by simpa [planarJ] using hJzero))
    have hJlin : g.linearIsometryEquiv (planarJ u) = h.linearIsometryEquiv (planarJ u) := by
      rcases hJg with hgplus | hgminus <;> rcases hJh with hhplus | hhminus
      · exact hgplus.trans hhplus.symm
      · have hhnot : h.linearIsometryEquiv (planarJ u) ≠ planarJ v := by
          intro heq
          exact hneg_ne (hhminus.symm.trans heq)
        simp [hgplus, hhnot] at hsign
      · have hgnot : g.linearIsometryEquiv (planarJ u) ≠ planarJ v := by
          intro heq
          exact hneg_ne (hgminus.symm.trans heq)
        simp [hgnot, hhplus] at hsign
      · calc
          g.linearIsometryEquiv (planarJ u) = -planarJ v := hgminus
          _ = h.linearIsometryEquiv (planarJ u) := hhminus.symm
    have hlin : g.linearIsometryEquiv.toLinearMap = h.linearIsometryEquiv.toLinearMap := by
      apply LinearMap.ext
      intro z
      have hz : z ∈ (ℝ ∙ u) ⊔ (ℝ ∙ planarJ u) := by
        rw [planarJ_span_top u hu]
        exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hz with ⟨z₁, hz₁, z₂, hz₂, hzsum⟩
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz₁
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hz₂
      rw [← hzsum, ← ha, ← hb]
      simp only [map_add, map_smul]
      change a • g.linearIsometryEquiv u + b • g.linearIsometryEquiv (planarJ u) =
        a • h.linearIsometryEquiv u + b • h.linearIsometryEquiv (planarJ u)
      rw [hgu, hhu, hJlin]
    have hlinAt (w : E 2) : g.linearIsometryEquiv w = h.linearIsometryEquiv w :=
      congrArg (fun f : E 2 →ₗ[ℝ] E 2 => f w) hlin
    apply AffineIsometryEquiv.ext
    intro z
    calc
      g z = g ((z -ᵥ p.1) +ᵥ p.1) := by rw [vsub_vadd]
      _ = g.linearIsometryEquiv (z -ᵥ p.1) +ᵥ g p.1 := g.map_vadd p.1 (z -ᵥ p.1)
      _ = h.linearIsometryEquiv (z -ᵥ p.1) +ᵥ h p.1 := by
        rw [hval1]
        exact congrArg (fun w : E 2 => w +ᵥ h p.1) (hlinAt (z -ᵥ p.1))
      _ = h ((z -ᵥ p.1) +ᵥ p.1) := (h.map_vadd p.1 (z -ᵥ p.1)).symm
      _ = h z := by rw [vsub_vadd]
  exact Set.Finite.of_finite_image himage hinj

/-- CI:350–366. Intercept and slope recover both endpoints. -/
private def cayleyBase (x y : E 2) : E 3 :=
  WithLp.toLp 2 ![0, ((1 / 2 : ℝ) • (x - y)) 0, ((1 / 2 : ℝ) • (x - y)) 1]

private def cayleyDirection (x y : E 2) : E 3 :=
  WithLp.toLp 2 ![1,
    -(planarJ ((1 / 2 : ℝ) • (x + y))) 0,
    -(planarJ ((1 / 2 : ℝ) • (x + y))) 1]

private def cayleyAffineLine (x y : E 2) : AffineSubspace ℝ (E 3) :=
  AffineSubspace.mk' (cayleyBase x y) (ℝ ∙ cayleyDirection x y)

private lemma cayleySet_coord0 (x y : E 2) (z : E 3)
    (hz : z ∈ cayleySet x y) :
    z 1 = ((1 / 2 : ℝ) • (x - y)) 0 - z 0 *
      (planarJ ((1 / 2 : ℝ) • (x + y))) 0 := by
  change WithLp.toLp 2 ![z 1, z 2] = _ at hz
  have h := congrArg (fun w : E 2 => w 0) hz
  change z 1 = _ at h
  exact h

private lemma cayleySet_coord1 (x y : E 2) (z : E 3)
    (hz : z ∈ cayleySet x y) :
    z 2 = ((1 / 2 : ℝ) • (x - y)) 1 - z 0 *
      (planarJ ((1 / 2 : ℝ) • (x + y))) 1 := by
  change WithLp.toLp 2 ![z 1, z 2] = _ at hz
  have h := congrArg (fun w : E 2 => w 1) hz
  change z 2 = _ at h
  exact h

private def cayleyLine (x y : E 2) : Line 3 := by
  refine ⟨cayleyAffineLine x y, ?_, ?_⟩
  · refine ⟨cayleyBase x y, ?_⟩
    change cayleyBase x y -ᵥ cayleyBase x y ∈ ℝ ∙ cayleyDirection x y
    simp
  · rw [cayleyAffineLine, AffineSubspace.direction_mk']
    apply finrank_span_singleton
    intro h
    have h0 := congrArg (fun z : E 3 => z 0) h
    simp [cayleyDirection] at h0

private lemma cayleySet_mem_iff_line (x y : E 2) (z : E 3) :
    z ∈ cayleySet x y ↔ z ∈ cayleyAffineLine x y := by
  change (WithLp.toLp 2 ![z 1, z 2] =
      (1 / 2 : ℝ) • (x - y) - z 0 • planarJ ((1 / 2 : ℝ) • (x + y))) ↔
    z -ᵥ cayleyBase x y ∈ ℝ ∙ cayleyDirection x y
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hz
    refine ⟨z 0, ?_⟩
    ext i
    fin_cases i
    · change (z 0 • cayleyDirection x y) 0 = (z - cayleyBase x y) 0
      simp [cayleyDirection, cayleyBase]
    · have hcoord := cayleySet_coord0 x y z hz
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hcoord
      change (z 0 • cayleyDirection x y) 1 = (z - cayleyBase x y) 1
      change z 0 * -(planarJ ((1 / 2 : ℝ) • (x + y))) 0 =
        z 1 - ((1 / 2 : ℝ) • (x - y)) 0
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      linarith
    · have hcoord := cayleySet_coord1 x y z hz
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hcoord
      change (z 0 • cayleyDirection x y) 2 = (z - cayleyBase x y) 2
      change z 0 * -(planarJ ((1 / 2 : ℝ) • (x + y))) 1 =
        z 2 - ((1 / 2 : ℝ) • (x - y)) 1
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      linarith
  · rintro ⟨t, ht⟩
    have ht0 := congrArg (fun w : E 3 => w 0) ht
    have ht1 := congrArg (fun w : E 3 => w 1) ht
    have ht2 := congrArg (fun w : E 3 => w 2) ht
    simp only [PiLp.smul_apply, PiLp.sub_apply, vsub_eq_sub, smul_eq_mul] at ht0 ht1 ht2
    norm_num [cayleyDirection, cayleyBase] at ht0 ht1 ht2
    have htval : t = z 0 := by linarith
    subst t
    apply PiLp.ext
    intro i
    fin_cases i
    · change z 1 = (1 / 2 : ℝ) • (x - y) 0 - z 0 •
        planarJ ((1 / 2 : ℝ) • (x + y)) 0
      simp only [smul_add]
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      linarith
    · change z 2 = (1 / 2 : ℝ) • (x - y) 1 - z 0 •
        planarJ ((1 / 2 : ℝ) • (x + y)) 1
      simp only [smul_add]
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      linarith

private lemma cayleySet_eq_line (x y : E 2) :
    (cayleyLine x y).1 = cayleySet x y := by
  ext z
  change z ∈ cayleyAffineLine x y ↔ z ∈ cayleySet x y
  exact (cayleySet_mem_iff_line x y z).symm

private lemma planarJ_injective : Function.Injective (planarJ) := by
  intro u v huv
  apply PiLp.ext
  intro i
  fin_cases i
  · have h := congrArg (fun w : E 2 => w 1) huv
    simpa [planarJ] using h
  · have h := congrArg (fun w : E 2 => w 0) huv
    simpa [planarJ] using h

theorem cayley_line_encoding :
    (∀ x y : E 2, ∃! l : Line 3, (l.1 : Set (E 3)) = cayleySet x y) ∧
    (∀ x y x' y' : E 2, cayleySet x y = cayleySet x' y' → x = x' ∧ y = y') := by
  constructor
  · intro x y
    refine ⟨cayleyLine x y, cayleySet_eq_line x y, ?_⟩
    intro l hl
    apply Subtype.ext
    apply (AffineSubspace.ext_iff _ _).2
    calc
      (l.1 : Set (E 3)) = cayleySet x y := hl
      _ = (cayleyLine x y).1 := (cayleySet_eq_line x y).symm
      _ = cayleyAffineLine x y := rfl
  · intro x y x' y' hsets
    let a : E 2 := (1 / 2 : ℝ) • (x - y)
    let b : E 2 := (1 / 2 : ℝ) • (x + y)
    let a' : E 2 := (1 / 2 : ℝ) • (x' - y')
    let b' : E 2 := (1 / 2 : ℝ) • (x' + y')
    have hzero :
        WithLp.toLp 2 ![0, a 0, a 1] ∈ cayleySet x y := by
      simp only [cayleySet, Set.mem_setOf_eq]
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [a] <;> ring
    have hzero' :
        WithLp.toLp 2 ![0, a 0, a 1] ∈ cayleySet x' y' := hsets ▸ hzero
    have ha : a = a' := by
      have h := hzero'
      simp only [cayleySet, Set.mem_setOf_eq] at h
      apply PiLp.ext
      intro i
      fin_cases i
      · have hcoord := congrArg (fun w : E 2 => w 0) h
        simpa [a, a'] using hcoord
      · have hcoord := congrArg (fun w : E 2 => w 1) h
        simpa [a, a'] using hcoord
    have hone :
        WithLp.toLp 2 ![1, (a - planarJ b) 0, (a - planarJ b) 1] ∈ cayleySet x y := by
      simp only [cayleySet, Set.mem_setOf_eq]
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [a, b] <;> ring
    have hone' :
        WithLp.toLp 2 ![1, (a - planarJ b) 0, (a - planarJ b) 1] ∈ cayleySet x' y' :=
      hsets ▸ hone
    have hslope : a - planarJ b = a' - planarJ b' := by
      have h := hone'
      simp only [cayleySet, Set.mem_setOf_eq] at h
      apply PiLp.ext
      intro i
      fin_cases i
      · have hcoord := congrArg (fun w : E 2 => w 0) h
        simpa [a', b', PiLp.sub_apply, PiLp.smul_apply] using hcoord
      · have hcoord := congrArg (fun w : E 2 => w 1) h
        simpa [a', b', PiLp.sub_apply, PiLp.smul_apply] using hcoord
    have hb : b = b' := by
      apply planarJ_injective
      have hslope' := hslope
      rw [ha] at hslope'
      exact sub_right_inj.mp hslope'
    have hxsum (u v : E 2) :
        ((1 / 2 : ℝ) • (u - v)) + ((1 / 2 : ℝ) • (u + v)) = u := by
      ext i
      fin_cases i <;> simp <;> ring
    have hysub (u v : E 2) :
        ((1 / 2 : ℝ) • (u + v)) - ((1 / 2 : ℝ) • (u - v)) = v := by
      ext i
      fin_cases i <;> simp <;> ring
    constructor
    · calc
        x = a + b := (hxsum x y).symm
        _ = a' + b' := by rw [ha, hb]
        _ = x' := hxsum x' y'
    · calc
        y = b - a := (hysub x y).symm
        _ = b' - a' := by rw [ha, hb]
        _ = y' := hysub x' y'

/-- Bijective direct-isometry chart, CI:350–362. -/
private instance planar_finrank_fact : Fact (Module.finrank ℝ (E 2) = 2) :=
  ⟨by simp [E]⟩

private noncomputable def planarStdBasis : OrthonormalBasis (Fin 2) ℝ (E 2) :=
  EuclideanSpace.basisFun (Fin 2) ℝ

private noncomputable def planarOrientation : Orientation ℝ (E 2) (Fin 2) :=
  planarStdBasis.toBasis.orientation

private lemma planarStdDet0 (y : E 2) :
    planarStdBasis.toBasis.det ![planarStdBasis 0, y] = inner ℝ (planarStdBasis 1) y := by
  rw [Module.Basis.det_apply]
  simp [Module.Basis.toMatrix_apply, planarStdBasis, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, Matrix.det_fin_two, PiLp.inner_apply]

private lemma planarStdDet1 (y : E 2) :
    planarStdBasis.toBasis.det ![planarStdBasis 1, y] = -inner ℝ (planarStdBasis 0) y := by
  rw [Module.Basis.det_apply]
  simp [Module.Basis.toMatrix_apply, planarStdBasis, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, Matrix.det_fin_two, PiLp.inner_apply]

private lemma planarOrientation_basis0 :
    planarOrientation.rightAngleRotation (planarStdBasis 0) = planarStdBasis 1 := by
  apply ext_inner_right ℝ
  intro y
  rw [planarOrientation.inner_rightAngleRotation_left, planarOrientation.areaForm_to_volumeForm,
    planarOrientation.volumeForm_robust planarStdBasis rfl, planarStdDet0]

private lemma planarOrientation_basis1 :
    planarOrientation.rightAngleRotation (planarStdBasis 1) = -planarStdBasis 0 := by
  apply ext_inner_right ℝ
  intro y
  rw [planarOrientation.inner_rightAngleRotation_left, planarOrientation.areaForm_to_volumeForm,
    planarOrientation.volumeForm_robust planarStdBasis rfl, planarStdDet1]
  simp

private lemma planarJ_add (x y : E 2) : planarJ (x + y) = planarJ x + planarJ y := by
  ext i
  fin_cases i <;> simp [planarJ] <;> ring

private lemma planarJ_smul (a : ℝ) (x : E 2) : planarJ (a • x) = a • planarJ x := by
  ext i
  fin_cases i <;> simp [planarJ]

private lemma planarJ_sq (x : E 2) : planarJ (planarJ x) = -x := by
  ext i
  fin_cases i <;> simp [planarJ]

private lemma planarJ_stdBasis0 : planarJ (planarStdBasis 0) = planarStdBasis 1 := by
  ext i
  fin_cases i <;> simp [planarJ, planarStdBasis, EuclideanSpace.basisFun_apply]

private lemma planarJ_stdBasis1 : planarJ (planarStdBasis 1) = -planarStdBasis 0 := by
  ext i
  fin_cases i <;> simp [planarJ, planarStdBasis, EuclideanSpace.basisFun_apply]

private lemma planarOrientation_rightAngleRotation (x : E 2) :
    planarOrientation.rightAngleRotation x = planarJ x := by
  have hrepr : (planarStdBasis.toBasis.repr x 0) • planarStdBasis 0 +
      (planarStdBasis.toBasis.repr x 1) • planarStdBasis 1 = x := by
    simpa [Fin.sum_univ_succ] using planarStdBasis.toBasis.sum_repr x
  calc
    planarOrientation.rightAngleRotation x = planarOrientation.rightAngleRotation
        ((planarStdBasis.toBasis.repr x 0) • planarStdBasis 0 +
          (planarStdBasis.toBasis.repr x 1) • planarStdBasis 1) :=
            congrArg planarOrientation.rightAngleRotation hrepr.symm
    _ = (planarStdBasis.toBasis.repr x 0) •
          planarOrientation.rightAngleRotation (planarStdBasis 0) +
        (planarStdBasis.toBasis.repr x 1) •
          planarOrientation.rightAngleRotation (planarStdBasis 1) := by
            simp only [map_add, map_smul]
    _ = (planarStdBasis.toBasis.repr x 0) • planarStdBasis 1 +
        (planarStdBasis.toBasis.repr x 1) • (-planarStdBasis 0) := by
          rw [planarOrientation_basis0, planarOrientation_basis1]
    _ = planarJ ((planarStdBasis.toBasis.repr x 0) • planarStdBasis 0 +
        (planarStdBasis.toBasis.repr x 1) • planarStdBasis 1) := by
          rw [planarJ_add, planarJ_smul, planarJ_smul, planarJ_stdBasis0, planarJ_stdBasis1]
    _ = planarJ x := congrArg planarJ hrepr

private def planarCayleyCos (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
private def planarCayleySin (t : ℝ) : ℝ := -(2 * t) / (1 + t ^ 2)

private lemma planarCayleyCos_sq_add_Sin_sq (t : ℝ) :
    planarCayleyCos t ^ 2 + planarCayleySin t ^ 2 = 1 := by
  dsimp [planarCayleyCos, planarCayleySin]
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hd]
  ring

private def planarCayleyComplex (t : ℝ) : ℂ :=
  ⟨planarCayleyCos t, planarCayleySin t⟩

private lemma planarCayleyComplex_norm (t : ℝ) : ‖planarCayleyComplex t‖ = 1 := by
  have hsq : planarCayleyCos t * planarCayleyCos t +
      planarCayleySin t * planarCayleySin t = 1 := by
    nlinarith [planarCayleyCos_sq_add_Sin_sq t]
  rw [Complex.norm_def, Complex.normSq_apply]
  change Real.sqrt (planarCayleyCos t * planarCayleyCos t +
    planarCayleySin t * planarCayleySin t) = 1
  rw [hsq]
  norm_num

private lemma planarCayleyComplex_ne_zero (t : ℝ) : planarCayleyComplex t ≠ 0 := by
  intro h
  have hn := congrArg (fun z : ℂ => ‖z‖) h
  simpa [planarCayleyComplex_norm] using hn

private noncomputable def planarCayleyAngle (t : ℝ) : Real.Angle :=
  (Complex.arg (planarCayleyComplex t) : Real.Angle)

private lemma planarCayleyAngle_cos (t : ℝ) :
    Real.Angle.cos (planarCayleyAngle t) = planarCayleyCos t := by
  rw [planarCayleyAngle, Real.Angle.cos_coe, Complex.cos_arg (planarCayleyComplex_ne_zero t),
    planarCayleyComplex_norm]
  simp [planarCayleyComplex]

private lemma planarCayleyAngle_sin (t : ℝ) :
    Real.Angle.sin (planarCayleyAngle t) = planarCayleySin t := by
  rw [planarCayleyAngle, Real.Angle.sin_coe, Complex.sin_arg, planarCayleyComplex_norm]
  simp [planarCayleyComplex]

private noncomputable def planarCayleyRotation (t : ℝ) : E 2 ≃ₗᵢ[ℝ] E 2 :=
  planarOrientation.rotation (planarCayleyAngle t)

private lemma planarCayleyRotation_apply (t : ℝ) (x : E 2) :
    planarCayleyRotation t x = planarCayleyCos t • x + planarCayleySin t • planarJ x := by
  rw [planarCayleyRotation, planarOrientation.rotation_apply,
    planarCayleyAngle_cos, planarCayleyAngle_sin, planarOrientation_rightAngleRotation]

private def planarCayleyTranslation (t : ℝ) (c : E 2) : E 2 :=
  -(2 / (1 + t ^ 2)) • (c - t • planarJ c)

private def planarCayleyMap (t : ℝ) (c x : E 2) : E 2 :=
  (1 / (1 + t ^ 2)) •
    ((1 - t ^ 2) • x - (2 * t) • planarJ x - 2 • c + (2 * t) • planarJ c)

private def planarCayleyPoint (t : ℝ) (c : E 2) : E 3 :=
  WithLp.toLp 2 ![t, c 0, c 1]

private noncomputable def planarCayleyMotion (t : ℝ) (c : E 2) : Motion 2 :=
  AffineIsometryEquiv.mk'
    (fun x : E 2 => planarCayleyRotation t x +ᵥ planarCayleyTranslation t c)
    (planarCayleyRotation t) 0 (by intro x; simp)

private lemma planarCayleyMotion_apply (t : ℝ) (c x : E 2) :
    planarCayleyMotion t c x = planarCayleyMap t c x := by
  change planarCayleyRotation t x + planarCayleyTranslation t c = _
  rw [planarCayleyRotation_apply]
  dsimp [planarCayleyTranslation, planarCayleyMap, planarCayleyCos, planarCayleySin]
  module

private lemma planarCayleyPoint_mem_iff (t : ℝ) (c x y : E 2) :
    planarCayleyPoint t c ∈ cayleySet x y ↔
      c = (1 / 2 : ℝ) • (x - y) - t • planarJ ((1 / 2 : ℝ) • (x + y)) := by
  change WithLp.toLp 2 ![(planarCayleyPoint t c) 1, (planarCayleyPoint t c) 2] = _ ↔ _
  have hcoord : WithLp.toLp 2 ![(planarCayleyPoint t c) 1,
      (planarCayleyPoint t c) 2] = c := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  rw [hcoord]
  change (c = (1 / 2 : ℝ) • (x - y) -
      t • planarJ ((1 / 2 : ℝ) • (x + y))) ↔ _
  rfl

private lemma planarCayleyRelation_iff (t : ℝ) (c x y : E 2) :
    c = (1 / 2 : ℝ) • (x - y) - t • planarJ ((1 / 2 : ℝ) • (x + y)) ↔
      y + t • planarJ y = x - t • planarJ x - 2 • c := by
  constructor
  · intro h
    ext i
    fin_cases i
    · have h0 := congrArg (fun z : E 2 => z 0) h
      simp [planarJ, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h0 ⊢
      nlinarith [h0]
    · have h1 := congrArg (fun z : E 2 => z 1) h
      simp [planarJ, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h1 ⊢
      nlinarith [h1]
  · intro h
    ext i
    fin_cases i
    · have h0 := congrArg (fun z : E 2 => z 0) h
      simp [planarJ, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h0 ⊢
      nlinarith [h0]
    · have h1 := congrArg (fun z : E 2 => z 1) h
      simp [planarJ, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h1 ⊢
      nlinarith [h1]

private lemma planarI_add_tJ_injective (t : ℝ) :
    Function.Injective (fun x : E 2 => x + t • planarJ x) := by
  intro x y h
  have h0 := congrArg (fun z : E 2 => z 0) h
  have h1 := congrArg (fun z : E 2 => z 1) h
  simp [planarJ, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at h0 h1
  have hdiff0 : x 0 - y 0 = t * (x 1 - y 1) := by linarith
  have hdiff1 : x 1 - y 1 = -t * (x 0 - y 0) := by linarith
  have hdiff1' : t * (x 1 - y 1) = -t ^ 2 * (x 0 - y 0) := by
    calc
      t * (x 1 - y 1) = t * (-t * (x 0 - y 0)) := congrArg (fun q : ℝ => t * q) hdiff1
      _ = -t ^ 2 * (x 0 - y 0) := by ring
  have hsum : (1 + t ^ 2) * (x 0 - y 0) = 0 := by nlinarith [hdiff0, hdiff1']
  have h0eq : x 0 = y 0 := by
    have hp : 0 < 1 + t ^ 2 := by positivity
    nlinarith
  have h1eq : x 1 = y 1 := by nlinarith [hdiff1, h0eq]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [h0eq, h1eq]

private lemma planarCayleyMap_solve (t : ℝ) (c x : E 2) :
    planarCayleyMap t c x + t • planarJ (planarCayleyMap t c x) =
      x - t • planarJ x - 2 • c := by
  ext i
  fin_cases i
  · simp [planarCayleyMap, planarJ, PiLp.smul_apply, PiLp.add_apply,
      PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring
  · simp [planarCayleyMap, planarJ, PiLp.smul_apply, PiLp.add_apply,
      PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring

private lemma planarCayleyMap_eq_iff (t : ℝ) (c x y : E 2) :
    planarCayleyMap t c x = y ↔
      c = (1 / 2 : ℝ) • (x - y) - t • planarJ ((1 / 2 : ℝ) • (x + y)) := by
  have hsolve : planarCayleyMap t c x + t • planarJ (planarCayleyMap t c x) =
      x - t • planarJ x - 2 • c := planarCayleyMap_solve t c x
  have hiff : planarCayleyMap t c x = y ↔
      y + t • planarJ y = x - t • planarJ x - 2 • c := by
    constructor
    · intro h
      simpa [h] using hsolve
    · intro h
      have heq : y + t • planarJ y =
          planarCayleyMap t c x + t • planarJ (planarCayleyMap t c x) := by
        calc
          y + t • planarJ y = x - t • planarJ x - 2 • c := h
          _ = planarCayleyMap t c x + t • planarJ (planarCayleyMap t c x) := hsolve.symm
      exact (planarI_add_tJ_injective t heq).symm
  exact hiff.trans (planarCayleyRelation_iff t c x y).symm

private lemma planarCayleyMotion_match_iff (t : ℝ) (c x y : E 2) :
    planarCayleyMotion t c x = y ↔ planarCayleyPoint t c ∈ cayleySet x y := by
  rw [planarCayleyMotion_apply, planarCayleyMap_eq_iff, planarCayleyPoint_mem_iff]

private lemma planarCayleyMotion_direct (t : ℝ) (c : E 2) :
    planarDirect (planarCayleyMotion t c) := by
  change LinearMap.det (planarCayleyRotation t).toLinearEquiv.toLinearMap = 1
  rw [planarCayleyRotation]
  exact planarOrientation.det_rotation _

private lemma planarCayleyMotion_inChart (t : ℝ) (c : E 2) :
    inPlanarChart (planarCayleyMotion t c) := by
  change LinearMap.ker
    ((planarCayleyRotation t).toLinearEquiv.toLinearMap + LinearMap.id) = ⊥
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change planarCayleyRotation t x + x = 0 at hx
  rw [planarCayleyRotation_apply] at hx
  have h0 := congrArg (fun z : E 2 => z 0) hx
  have h1 := congrArg (fun z : E 2 => z 1) hx
  simp [planarJ, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    planarCayleyCos, planarCayleySin] at h0 h1
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hd] at h0 h1
  have hcoord0 : x 0 + t * x 1 = 0 := by nlinarith [h0]
  have hcoord1 : x 1 - t * x 0 = 0 := by nlinarith [h1]
  have hcoord1mul := congrArg (fun q : ℝ => t * q) hcoord1
  have hsum : (1 + t ^ 2) * x 0 = 0 := by nlinarith [hcoord0, hcoord1mul]
  have hx0 : x 0 = 0 := by
    have hp : 0 < 1 + t ^ 2 := by positivity
    nlinarith
  have hx1 : x 1 = 0 := by nlinarith [hcoord1, hx0]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [hx0, hx1]

private lemma planarCayleyTranslation_recover (t : ℝ) (v : E 2) :
    planarCayleyTranslation t ((-1 / 2 : ℝ) • (v + t • planarJ v)) = v := by
  have hJc : planarJ ((-1 / 2 : ℝ) • (v + t • planarJ v)) =
      (-1 / 2 : ℝ) • (planarJ v - t • v) := by
    rw [planarJ_smul, planarJ_add, planarJ_smul, planarJ_sq]
    module
  have hinside :
      (-1 / 2 : ℝ) • (v + t • planarJ v) -
        t • planarJ ((-1 / 2 : ℝ) • (v + t • planarJ v)) =
      (-(1 + t ^ 2) / 2) • v := by
    rw [hJc]
    module
  change -(2 / (1 + t ^ 2)) •
      (((-1 / 2 : ℝ) • (v + t • planarJ v)) -
        t • planarJ ((-1 / 2 : ℝ) • (v + t • planarJ v))) = v
  rw [hinside, smul_smul]
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  have hscale : (-(2 / (1 + t ^ 2))) * (-(1 + t ^ 2) / 2) = 1 := by
    field_simp [hd] <;> ring
  rw [hscale]
  simp

private lemma planarCayley_param_recover (t : ℝ) :
    -planarCayleySin t / (1 + planarCayleyCos t) = t := by
  dsimp [planarCayleySin, planarCayleyCos]
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hd]
  ring

theorem planar_cayley_chart :
    (∀ z : E 3, ∃! g : Motion 2, planarDirect g ∧ inPlanarChart g ∧
      ∀ x y : E 2, g x = y ↔ z ∈ cayleySet x y) ∧
    (∀ g : Motion 2, planarDirect g → inPlanarChart g →
      ∃! z : E 3, ∀ x y : E 2, g x = y ↔ z ∈ cayleySet x y) := by
  constructor
  · intro z
    let t : ℝ := z 0
    let c : E 2 := WithLp.toLp 2 ![z 1, z 2]
    let p : E 3 := planarCayleyPoint t c
    have hp : p = z := by
      ext i
      fin_cases i <;> simp [p, t, c, planarCayleyPoint]
    refine ⟨planarCayleyMotion t c, ?_, ?_⟩
    · refine ⟨planarCayleyMotion_direct t c, planarCayleyMotion_inChart t c, ?_⟩
      intro x y
      rw [← hp]
      exact planarCayleyMotion_match_iff t c x y
    · intro g' hg'
      apply AffineIsometryEquiv.ext
      intro x
      have hmem : p ∈ cayleySet x (planarCayleyMotion t c x) :=
        (planarCayleyMotion_match_iff t c x (planarCayleyMotion t c x)).mp rfl
      rw [hp] at hmem
      exact (hg'.2.2 x (planarCayleyMotion t c x)).mpr hmem
  · intro g hdirect hchart
    have hdet : LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap = 1 := by
      simpa [planarDirect, AffineIsometryEquiv.linear_eq_linear_isometry] using hdirect
    have hdetpos : 0 < LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
      rw [hdet]
      norm_num
    obtain ⟨θ, hθ⟩ :=
      planarOrientation.exists_linearIsometryEquiv_eq_of_det_pos
        (f := g.linearIsometryEquiv) hdetpos
    have hker : LinearMap.ker
        (g.linearIsometryEquiv.toLinearEquiv.toLinearMap + LinearMap.id) = ⊥ := by
      simpa [inPlanarChart, AffineIsometryEquiv.linear_eq_linear_isometry] using hchart
    let a : ℝ := Real.Angle.cos θ
    let b : ℝ := Real.Angle.sin θ
    have htrig : a ^ 2 + b ^ 2 = 1 := by
      simpa [a, b] using θ.cos_sq_add_sin_sq
    have hden : 1 + a ≠ 0 := by
      intro hz
      have ha : a = -1 := by linarith
      have hb : b = 0 := by nlinarith [htrig]
      have hneg (x : E 2) : g.linearIsometryEquiv x = -x := by
        rw [hθ, planarOrientation.rotation_apply]
        change a • x + b • planarOrientation.rightAngleRotation x = -x
        rw [ha, hb]
        simp
      have he0ker : planarStdBasis 0 ∈ LinearMap.ker
          (g.linearIsometryEquiv.toLinearEquiv.toLinearMap + LinearMap.id) := by
        change g.linearIsometryEquiv (planarStdBasis 0) + planarStdBasis 0 = 0
        rw [hneg]
        simp
      have he0bot : planarStdBasis 0 ∈ (⊥ : Submodule ℝ (E 2)) := by
        rw [← hker]
        exact he0ker
      have he0zero : planarStdBasis 0 = 0 := by simpa using he0bot
      have he0ne : planarStdBasis 0 ≠ 0 := by
        intro h
        have hc := congrArg (fun v : E 2 => v 0) h
        have hc' : (1 : ℝ) = 0 := by
          simpa [planarStdBasis, EuclideanSpace.basisFun_apply] using hc
        norm_num at hc'
      exact he0ne he0zero
    let t : ℝ := -b / (1 + a)
    have hcoeffCos : planarCayleyCos t = a := by
      dsimp [t, planarCayleyCos]
      have htrig1 : (1 + a) * (a ^ 2 + b ^ 2) = 1 + a :=
        by simpa using congrArg (fun q : ℝ => (1 + a) * q) htrig
      field_simp [hden] <;> nlinarith [htrig1]
    have hcoeffSin : planarCayleySin t = b := by
      dsimp [t, planarCayleySin]
      have htrigb : b * (a ^ 2 + b ^ 2) = b := by
        simpa using congrArg (fun q : ℝ => b * q) htrig
      field_simp [hden] <;> nlinarith [htrigb]
    let v : E 2 := g 0
    let c : E 2 := (-1 / 2 : ℝ) • (v + t • planarJ v)
    have htrans : planarCayleyTranslation t c = g 0 := by
      simpa [c, v] using planarCayleyTranslation_recover t (g 0)
    have hrotation : g.linearIsometryEquiv = planarCayleyRotation t := by
      apply LinearIsometryEquiv.ext
      intro x
      calc
        g.linearIsometryEquiv x = planarOrientation.rotation θ x := congrArg (fun f => f x) hθ
        _ = a • x + b • planarJ x := by
          rw [planarOrientation.rotation_apply, planarOrientation_rightAngleRotation]
        _ = planarCayleyRotation t x := by
          rw [planarCayleyRotation_apply, hcoeffCos, hcoeffSin]
    have hmotion : g = planarCayleyMotion t c := by
      apply AffineIsometryEquiv.ext
      intro x
      calc
        g x = g (x +ᵥ (0 : E 2)) := by simp
        _ = g.linearIsometryEquiv x +ᵥ g 0 := g.map_vadd 0 x
        _ = planarCayleyRotation t x +ᵥ planarCayleyTranslation t c := by
          rw [hrotation, htrans]
        _ = planarCayleyMotion t c x := by simp [planarCayleyMotion]
    have hgraph (x y : E 2) :
        g x = y ↔ planarCayleyPoint t c ∈ cayleySet x y := by
      rw [hmotion]
      exact planarCayleyMotion_match_iff t c x y
    refine ⟨planarCayleyPoint t c, hgraph, ?_⟩
    intro z' hz'
    let t' : ℝ := z' 0
    let c' : E 2 := WithLp.toLp 2 ![z' 1, z' 2]
    have hzpoint : planarCayleyPoint t' c' = z' := by
      ext i
      fin_cases i <;> simp [t', c', planarCayleyPoint]
    let x₀ : E 2 := 0
    let x₁ : E 2 := planarStdBasis 0
    let y₀ : E 2 := g x₀
    let y₁ : E 2 := g x₁
    let d₀ : E 2 := (1 / 2 : ℝ) • (x₀ - y₀)
    let m₀ : E 2 := (1 / 2 : ℝ) • (x₀ + y₀)
    let d₁ : E 2 := (1 / 2 : ℝ) • (x₁ - y₁)
    let m₁ : E 2 := (1 / 2 : ℝ) • (x₁ + y₁)
    have hmem₀ : planarCayleyPoint t c ∈ cayleySet x₀ y₀ := (hgraph x₀ y₀).mp rfl
    have hmem₀' : planarCayleyPoint t' c' ∈ cayleySet x₀ y₀ := by
      have h := (hz' x₀ y₀).mp rfl
      rw [← hzpoint] at h
      exact h
    have hmem₁ : planarCayleyPoint t c ∈ cayleySet x₁ y₁ := (hgraph x₁ y₁).mp rfl
    have hmem₁' : planarCayleyPoint t' c' ∈ cayleySet x₁ y₁ := by
      have h := (hz' x₁ y₁).mp rfl
      rw [← hzpoint] at h
      exact h
    have h₀ : c = d₀ - t • planarJ m₀ := by
      simpa [d₀, m₀, x₀, y₀] using
        (planarCayleyPoint_mem_iff t c x₀ y₀).mp hmem₀
    have h₀' : c' = d₀ - t' • planarJ m₀ := by
      simpa [d₀, m₀, x₀, y₀] using
        (planarCayleyPoint_mem_iff t' c' x₀ y₀).mp hmem₀'
    have h₁ : c = d₁ - t • planarJ m₁ := by
      simpa [d₁, m₁, x₁, y₁] using
        (planarCayleyPoint_mem_iff t c x₁ y₁).mp hmem₁
    have h₁' : c' = d₁ - t' • planarJ m₁ := by
      simpa [d₁, m₁, x₁, y₁] using
        (planarCayleyPoint_mem_iff t' c' x₁ y₁).mp hmem₁'
    have hdelta₀ : c - c' = -(t - t') • planarJ m₀ := by
      rw [h₀, h₀']
      module
    have hdelta₁ : c - c' = -(t - t') • planarJ m₁ := by
      rw [h₁, h₁']
      module
    have h₀s : (t - t') • planarJ m₀ = -(c - c') := by
      calc
        (t - t') • planarJ m₀ = -((t' - t) • planarJ m₀) := by
          have htcoeff : t - t' = -(t' - t) := by ring
          rw [htcoeff, neg_smul]
        _ = -(c - c') := by
          rw [hdelta₀]
          have htcoeff : t' - t = -(t - t') := by ring
          rw [htcoeff]
    have h₁s : (t - t') • planarJ m₁ = -(c - c') := by
      calc
        (t - t') • planarJ m₁ = -((t' - t) • planarJ m₁) := by
          have htcoeff : t - t' = -(t' - t) := by ring
          rw [htcoeff, neg_smul]
        _ = -(c - c') := by
          rw [hdelta₁]
          have htcoeff : t' - t = -(t - t') := by ring
          rw [htcoeff]
    have hsmul : (t - t') • (planarJ m₁ - planarJ m₀) = 0 := by
      rw [smul_sub, h₁s, h₀s]
      simp
    have hgu : y₁ = g.linearIsometryEquiv x₁ +ᵥ y₀ := by
      dsimp [y₁, y₀]
      simpa using g.map_vadd 0 x₁
    have hmdelta : m₁ - m₀ = (1 / 2 : ℝ) • (x₁ + g.linearIsometryEquiv x₁) := by
      dsimp [m₁, m₀, x₀]
      rw [hgu]
      simp only [zero_add, smul_add, vadd_eq_add]
      abel
    have hx₁ne : x₁ ≠ 0 := by
      intro h
      have hc := congrArg (fun w : E 2 => w 0) h
      have hc' : (1 : ℝ) = 0 := by
        simpa [x₁, planarStdBasis, EuclideanSpace.basisFun_apply] using hc
      norm_num at hc'
    have hlinne : x₁ + g.linearIsometryEquiv x₁ ≠ 0 := by
      intro h
      have hmem : x₁ ∈ LinearMap.ker
          (g.linearIsometryEquiv.toLinearEquiv.toLinearMap + LinearMap.id) := by
        change g.linearIsometryEquiv x₁ + x₁ = 0
        simpa [add_comm] using h
      have hmem' : x₁ ∈ (⊥ : Submodule ℝ (E 2)) := by
        rw [← hker]
        exact hmem
      exact hx₁ne (by simpa using hmem')
    have hmdelta_ne : m₁ - m₀ ≠ 0 := by
      intro h
      rw [hmdelta] at h
      rcases smul_eq_zero.mp h with hzero | hzero
      · norm_num at hzero
      · exact hlinne hzero
    have hjne : planarJ m₁ - planarJ m₀ ≠ 0 := by
      intro h
      apply hmdelta_ne
      apply sub_eq_zero.mpr
      apply planarJ_injective
      exact sub_eq_zero.mp h
    have ht : t = t' := by
      rcases smul_eq_zero.mp hsmul with hzero | hzero
      · exact sub_eq_zero.mp hzero
      · exact False.elim (hjne hzero)
    have hc : c = c' := by
      calc
        c = d₀ - t • planarJ m₀ := h₀
        _ = d₀ - t' • planarJ m₀ := by rw [ht]
        _ = c' := h₀'.symm
    calc
      z' = planarCayleyPoint t' c' := hzpoint.symm
      _ = planarCayleyPoint t c := by rw [ht, hc]

/-- Finite generic rotation avoids every half-turn, CI:347–349, 818–824. -/
private lemma planarCayleyRotation_injective : Function.Injective planarCayleyRotation := by
  intro s t h
  have h0 := congrArg (fun f : E 2 ≃ₗᵢ[ℝ] E 2 => f (planarStdBasis 0)) h
  rw [planarCayleyRotation_apply, planarCayleyRotation_apply, planarJ_stdBasis0] at h0
  have hcos : planarCayleyCos s = planarCayleyCos t := by
    have hc := congrArg (fun x : E 2 => x 0) h0
    simpa [planarStdBasis, EuclideanSpace.basisFun_apply] using hc
  have hsin : planarCayleySin s = planarCayleySin t := by
    have hs := congrArg (fun x : E 2 => x 1) h0
    simpa [planarStdBasis, EuclideanSpace.basisFun_apply] using hs
  calc
    s = -planarCayleySin s / (1 + planarCayleyCos s) :=
      (planarCayley_param_recover s).symm
    _ = -planarCayleySin t / (1 + planarCayleyCos t) := by rw [hsin, hcos]
    _ = t := planarCayley_param_recover t

private lemma planarDirect_ker_ne_bot_eq_neg (g : Motion 2) (hdirect : planarDirect g)
    (hker : LinearMap.ker
      (g.linearIsometryEquiv.toLinearEquiv.toLinearMap + LinearMap.id) ≠ ⊥) :
    ∀ x : E 2, g.linearIsometryEquiv x = -x := by
  have hdet : LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap = 1 := by
    simpa [planarDirect, AffineIsometryEquiv.linear_eq_linear_isometry] using hdirect
  have hdetpos : 0 < LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
    rw [hdet]
    norm_num
  obtain ⟨θ, hθ⟩ :=
    planarOrientation.exists_linearIsometryEquiv_eq_of_det_pos
      (f := g.linearIsometryEquiv) hdetpos
  obtain ⟨v, hvker, hv0⟩ :=
    (Submodule.ne_bot_iff
      (LinearMap.ker
        (g.linearIsometryEquiv.toLinearEquiv.toLinearMap + LinearMap.id))).mp hker
  change g.linearIsometryEquiv v + v = 0 at hvker
  have hv : g.linearIsometryEquiv v = -v := by
    calc
      g.linearIsometryEquiv v = g.linearIsometryEquiv v + v - v := by abel
      _ = -v := by rw [hvker]; simp
  let a : ℝ := Real.Angle.cos θ
  let b : ℝ := Real.Angle.sin θ
  have htrig : a ^ 2 + b ^ 2 = 1 := by
    simpa [a, b] using θ.cos_sq_add_sin_sq
  have hvrot : a • v + b • planarJ v = -v := by
    calc
      a • v + b • planarJ v = planarOrientation.rotation θ v := by
        rw [planarOrientation.rotation_apply, planarOrientation_rightAngleRotation]
      _ = g.linearIsometryEquiv v := by rw [hθ]
      _ = -v := hv
  have hv0coord := congrArg (fun x : E 2 => x 0) hvrot
  have hv1coord := congrArg (fun x : E 2 => x 1) hvrot
  simp [a, b, planarJ, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at hv0coord hv1coord
  have hcoord0 : (1 + a) * v 0 - b * v 1 = 0 := by linarith
  have hcoord1 : b * v 0 + (1 + a) * v 1 = 0 := by linarith
  have hnormsq : (v 0) ^ 2 + (v 1) ^ 2 ≠ 0 := by
    intro hz
    have hz0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hz1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    apply hv0
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hz0, hz1]
  have ha : a = -1 := by
    have hz : (1 + a) * ((v 0) ^ 2 + (v 1) ^ 2) = 0 := by
      linear_combination (v 0) * hcoord0 + (v 1) * hcoord1
    rcases mul_eq_zero.mp hz with ha | hvnorm
    · linarith
    · exact (hnormsq hvnorm).elim
  have hb : b = 0 := by
    have hz : b * ((v 0) ^ 2 + (v 1) ^ 2) = 0 := by
      linear_combination -(v 1) * hcoord0 + (v 0) * hcoord1
    rcases mul_eq_zero.mp hz with hb | hvnorm
    · exact hb
    · exact (hnormsq hvnorm).elim
  intro x
  calc
    g.linearIsometryEquiv x = planarOrientation.rotation θ x := by rw [hθ]
    _ = a • x + b • planarJ x := by
      rw [planarOrientation.rotation_apply, planarOrientation_rightAngleRotation]
    _ = -x := by simp [ha, hb]

private noncomputable def planarPostcompose (R : E 2 ≃ₗᵢ[ℝ] E 2) (g : Motion 2) : Motion 2 :=
  AffineIsometryEquiv.mk'
    (fun x : E 2 => R (g x)) (g.linearIsometryEquiv.trans R) 0
    (by
      intro x
      have h := congrArg R (g.map_vadd (0 : E 2) x)
      simpa using h)

@[simp] private lemma planarPostcompose_apply (R : E 2 ≃ₗᵢ[ℝ] E 2) (g : Motion 2)
    (x : E 2) : planarPostcompose R g x = R (g x) := rfl

@[simp] private lemma planarPostcompose_linear (R : E 2 ≃ₗᵢ[ℝ] E 2) (g : Motion 2) :
    (planarPostcompose R g).linearIsometryEquiv = g.linearIsometryEquiv.trans R := by
  simp [planarPostcompose]

private noncomputable def planarForbiddenParam (g : Motion 2) : ℝ :=
  if h : ∃ t : ℝ, ∀ x : E 2, planarCayleyRotation t (g.linearIsometryEquiv x) = -x then
    Classical.choose h
  else 0

private lemma planarForbiddenParam_eq_of (g : Motion 2) (t : ℝ)
    (ht : ∀ x : E 2, planarCayleyRotation t (g.linearIsometryEquiv x) = -x) :
    planarForbiddenParam g = t := by
  let hp : ∃ s : ℝ, ∀ x : E 2, planarCayleyRotation s (g.linearIsometryEquiv x) = -x :=
    ⟨t, ht⟩
  unfold planarForbiddenParam
  rw [dif_pos hp]
  apply planarCayleyRotation_injective
  apply LinearIsometryEquiv.ext
  intro z
  obtain ⟨x, hx⟩ := g.linearIsometryEquiv.surjective z
  have hs := (Classical.choose_spec hp) x
  have ht' := ht x
  calc
    planarCayleyRotation (Classical.choose hp) z =
        planarCayleyRotation (Classical.choose hp) (g.linearIsometryEquiv x) := by rw [← hx]
    _ = -x := hs
    _ = planarCayleyRotation t (g.linearIsometryEquiv x) := ht'.symm
    _ = planarCayleyRotation t z := by rw [← hx]

theorem planar_generic_rotation (U V : Finset (E 2)) :
    ∃ R : E 2 ≃ₗᵢ[ℝ] E 2,
      LinearMap.det R.toLinearEquiv.toLinearMap = 1 ∧
      ∀ g : Motion 2, planarDirect g →
        2 ≤ matchCount U (V.image R) g → inPlanarChart g := by
  classical
  let M : Finset (Motion 2) := (planar_motions_finite U V).toFinset
  let B : Finset ℝ := M.image planarForbiddenParam
  obtain ⟨t, -, htB⟩ := (Set.infinite_univ : (Set.univ : Set ℝ).Infinite).exists_notMem_finset B
  let R : E 2 ≃ₗᵢ[ℝ] E 2 := planarCayleyRotation t
  have hRdet : LinearMap.det R.toLinearEquiv.toLinearMap = 1 := by
    change LinearMap.det (planarCayleyRotation t).toLinearEquiv.toLinearMap = 1
    rw [planarCayleyRotation]
    exact planarOrientation.det_rotation _
  refine ⟨R, hRdet, ?_⟩
  intro g hdirect hmatches
  by_contra hchart
  have hker : LinearMap.ker
      (g.linearIsometryEquiv.toLinearEquiv.toLinearMap + LinearMap.id) ≠ ⊥ := by
    intro hk
    apply hchart
    change LinearMap.ker
      (g.toAffineEquiv.linear.toLinearMap + LinearMap.id) = ⊥
    simpa [AffineIsometryEquiv.linear_eq_linear_isometry] using hk
  have hneg := planarDirect_ker_ne_bot_eq_neg g hdirect hker
  let h : Motion 2 := planarPostcompose R.symm g
  have hmatches' : matchPoints U V h = matchPoints U (V.image R) g := by
    ext x
    simp only [matchPoints, Finset.mem_filter]
    constructor
    · rintro ⟨hxU, hxV⟩
      refine ⟨hxU, ?_⟩
      change g x ∈ V.image R
      apply Finset.mem_image.mpr
      exact ⟨R.symm (g x), hxV, R.apply_symm_apply _⟩
    · rintro ⟨hxU, hxy⟩
      refine ⟨hxU, ?_⟩
      rcases Finset.mem_image.mp hxy with ⟨y, hyV, hgy⟩
      have hsymm : R.symm (g x) = y := by rw [← hgy]; simp
      change R.symm (g x) ∈ V
      rw [hsymm]
      exact hyV
  have hcount : matchCount U V h = matchCount U (V.image R) g := by
    simp [matchCount, hmatches']
  have hrich : h ∈ richMotions U V 2 := by
    change (2 : ℝ) ≤ (matchCount U V h : ℝ)
    rw [hcount]
    exact_mod_cast hmatches
  have hM : h ∈ M := by
    simpa [M] using (planar_motions_finite U V).mem_toFinset.mpr hrich
  have hforbidden : ∀ x : E 2, planarCayleyRotation t (h.linearIsometryEquiv x) = -x := by
    intro x
    rw [planarPostcompose_linear]
    change R (R.symm (g.linearIsometryEquiv x)) = -x
    simpa using hneg x
  have hparam : planarForbiddenParam h = t := planarForbiddenParam_eq_of h t hforbidden
  have htmem : t ∈ B := by
    rw [← hparam]
    exact Finset.mem_image.mpr ⟨h, hM, rfl⟩
  exact htB htmem

/-- Plane cap, CI:367–373. -/
private lemma cayleyLine_eq_of_set_eq (l : Line 3) (x y : E 2)
    (h : (l.1 : Set (E 3)) = cayleySet x y) : l = cayleyLine x y := by
  obtain ⟨l₀, hl₀, huniq⟩ := (cayley_line_encoding).1 x y
  exact (huniq l h).trans (huniq (cayleyLine x y) (cayleySet_eq_line x y)).symm

private lemma cayleyAffineLine_eq_of_set_eq (l : Line 3) (x y : E 2)
    (h : (l.1 : Set (E 3)) = cayleySet x y) : l.1 = cayleyAffineLine x y := by
  apply AffineSubspace.ext
  intro z
  change z ∈ (l.1 : Set (E 3)) ↔ z ∈ cayleyAffineLine x y
  rw [h]
  exact cayleySet_mem_iff_line x y z

private lemma cayleyLine_plane_data (x y : E 2) (H : Plane 3)
    (hL : cayleyAffineLine x y ≤ H.1) :
    cayleyBase x y ∈ H.1 ∧ cayleyDirection x y ∈ H.1.direction := by
  constructor
  · apply hL
    exact AffineSubspace.self_mem_mk' _ _
  · apply AffineSubspace.direction_le hL
    rw [cayleyAffineLine, AffineSubspace.direction_mk']
    exact Submodule.mem_span_singleton_self _

private lemma cayley_inner3_coords (u v : E 3) :
    inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ]
  ring

private lemma cayley_plane_fixed_left (H : Plane 3) (x y y' : E 2)
    (hL : cayleyAffineLine x y ≤ H.1) (hL' : cayleyAffineLine x y' ≤ H.1) : y = y' := by
  have horth_finrank : Module.finrank ℝ ↥(H.1.directionᗮ) = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal H.1.direction
    rw [H.2.2, finrank_euclideanSpace] at hsum
    simp only [Fintype.card_fin] at hsum
    omega
  have horth_ne : (H.1.directionᗮ : Submodule ℝ (E 3)) ≠ ⊥ := by
    intro h
    rw [h] at horth_finrank
    simp at horth_finrank
  obtain ⟨n, hn, hn0⟩ := (Submodule.ne_bot_iff (H.1.directionᗮ)).mp horth_ne
  have hn_orth (v : E 3) (hv : v ∈ H.1.direction) : inner ℝ n v = 0 := by
    calc
      inner ℝ n v = inner ℝ v n := (real_inner_comm n v).symm
      _ = 0 := (Submodule.mem_orthogonal H.1.direction n).mp hn v hv
  have hdata := cayleyLine_plane_data x y H hL
  have hdata' := cayleyLine_plane_data x y' H hL'
  have hbaseDiff : cayleyBase x y -ᵥ cayleyBase x y' ∈ H.1.direction :=
    AffineSubspace.vsub_mem_direction hdata.1 hdata'.1
  have hdirDiff : cayleyDirection x y - cayleyDirection x y' ∈ H.1.direction :=
    Submodule.sub_mem _ hdata.2 hdata'.2
  have hBaseOrth := hn_orth _ hbaseDiff
  have hDirOrth := hn_orth _ hdirDiff
  have hDirOneOrth := hn_orth _ hdata.2
  have hbaseEq : n 1 * (y 0 - y' 0) + n 2 * (y 1 - y' 1) = 0 := by
    have h := hBaseOrth
    simp [cayley_inner3_coords, vsub_eq_sub, cayleyBase, PiLp.sub_apply,
      PiLp.smul_apply] at h
    linear_combination -2 * h
  have hdirEq : -(n 2) * (y 0 - y' 0) + n 1 * (y 1 - y' 1) = 0 := by
    have h := hDirOrth
    simp [cayley_inner3_coords, cayleyDirection, planarJ, PiLp.sub_apply,
      PiLp.smul_apply] at h
    linear_combination 2 * h
  have hhor : n 1 ≠ 0 ∨ n 2 ≠ 0 := by
    by_contra h
    push_neg at h
    have hn1zero : n 0 = 0 := by
      have h' := hDirOneOrth
      simp [cayley_inner3_coords, cayleyDirection, planarJ, h.1, h.2] at h'
      exact h'
    have hn_eq : n = 0 := by
      apply PiLp.ext
      intro i
      fin_cases i
      · exact hn1zero
      · exact h.1
      · exact h.2
    exact hn0 hn_eq
  have hcoeff : 0 < (n 1) ^ 2 + (n 2) ^ 2 := by
    rcases hhor with h | h
    · have : 0 < (n 1) ^ 2 := sq_pos_of_ne_zero h
      nlinarith
    · have : 0 < (n 2) ^ 2 := sq_pos_of_ne_zero h
      nlinarith
  have hdet0 : ((n 1) ^ 2 + (n 2) ^ 2) * (y 0 - y' 0) = 0 := by
    linear_combination (n 1) * hbaseEq - (n 2) * hdirEq
  have hdet1 : ((n 1) ^ 2 + (n 2) ^ 2) * (y 1 - y' 1) = 0 := by
    linear_combination (n 2) * hbaseEq + (n 1) * hdirEq
  have hxy0 : y 0 = y' 0 := by
    rcases mul_eq_zero.mp hdet0 with hc | hy
    · linarith
    · linarith
  have hxy1 : y 1 = y' 1 := by
    rcases mul_eq_zero.mp hdet1 with hc | hy
    · linarith
    · linarith
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hxy0
  · exact hxy1

private lemma cayley_plane_fixed_right (H : Plane 3) (y x x' : E 2)
    (hL : cayleyAffineLine x y ≤ H.1) (hL' : cayleyAffineLine x' y ≤ H.1) : x = x' := by
  have horth_finrank : Module.finrank ℝ ↥(H.1.directionᗮ) = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal H.1.direction
    rw [H.2.2, finrank_euclideanSpace] at hsum
    simp only [Fintype.card_fin] at hsum
    omega
  have horth_ne : (H.1.directionᗮ : Submodule ℝ (E 3)) ≠ ⊥ := by
    intro h
    rw [h] at horth_finrank
    simp at horth_finrank
  obtain ⟨n, hn, hn0⟩ := (Submodule.ne_bot_iff (H.1.directionᗮ)).mp horth_ne
  have hn_orth (v : E 3) (hv : v ∈ H.1.direction) : inner ℝ n v = 0 := by
    calc
      inner ℝ n v = inner ℝ v n := (real_inner_comm n v).symm
      _ = 0 := (Submodule.mem_orthogonal H.1.direction n).mp hn v hv
  have hdata := cayleyLine_plane_data x y H hL
  have hdata' := cayleyLine_plane_data x' y H hL'
  have hbaseDiff : cayleyBase x y -ᵥ cayleyBase x' y ∈ H.1.direction :=
    AffineSubspace.vsub_mem_direction hdata.1 hdata'.1
  have hdirDiff : cayleyDirection x y - cayleyDirection x' y ∈ H.1.direction :=
    Submodule.sub_mem _ hdata.2 hdata'.2
  have hBaseOrth := hn_orth _ hbaseDiff
  have hDirOrth := hn_orth _ hdirDiff
  have hDirOneOrth := hn_orth _ hdata.2
  have hbaseEq : n 1 * (x 0 - x' 0) + n 2 * (x 1 - x' 1) = 0 := by
    have h := hBaseOrth
    simp [cayley_inner3_coords, vsub_eq_sub, cayleyBase, PiLp.sub_apply,
      PiLp.smul_apply] at h
    linear_combination 2 * h
  have hdirEq : -(n 2) * (x 0 - x' 0) + n 1 * (x 1 - x' 1) = 0 := by
    have h := hDirOrth
    simp [cayley_inner3_coords, cayleyDirection, planarJ, PiLp.sub_apply,
      PiLp.smul_apply] at h
    linear_combination 2 * h
  have hhor : n 1 ≠ 0 ∨ n 2 ≠ 0 := by
    by_contra h
    push_neg at h
    have hn1zero : n 0 = 0 := by
      have h' := hDirOneOrth
      simp [cayley_inner3_coords, cayleyDirection, planarJ, h.1, h.2] at h'
      exact h'
    have hn_eq : n = 0 := by
      apply PiLp.ext
      intro i
      fin_cases i
      · exact hn1zero
      · exact h.1
      · exact h.2
    exact hn0 hn_eq
  have hcoeff : 0 < (n 1) ^ 2 + (n 2) ^ 2 := by
    rcases hhor with h | h
    · have : 0 < (n 1) ^ 2 := sq_pos_of_ne_zero h
      nlinarith
    · have : 0 < (n 2) ^ 2 := sq_pos_of_ne_zero h
      nlinarith
  have hdet0 : ((n 1) ^ 2 + (n 2) ^ 2) * (x 0 - x' 0) = 0 := by
    linear_combination (n 1) * hbaseEq - (n 2) * hdirEq
  have hdet1 : ((n 1) ^ 2 + (n 2) ^ 2) * (x 1 - x' 1) = 0 := by
    linear_combination (n 2) * hbaseEq + (n 1) * hdirEq
  have hxy0 : x 0 = x' 0 := by
    rcases mul_eq_zero.mp hdet0 with hc | hx
    · linarith
    · linarith
  have hxy1 : x 1 = x' 1 := by
    rcases mul_eq_zero.mp hdet1 with hc | hx
    · linarith
    · linarith
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hxy0
  · exact hxy1

private lemma cayleyLines_endpoint_exists (U V : Finset (E 2)) (l : Line 3)
    (hl : l ∈ cayleyLines U V) :
    ∃ p : E 2 × E 2, p.1 ∈ U ∧ p.2 ∈ V ∧ (l.1 : Set (E 3)) = cayleySet p.1 p.2 := by
  simp only [cayleyLines, Set.mem_setOf_eq] at hl
  rcases hl with ⟨x, hx, y, hy, hset⟩
  exact ⟨(x, y), hx, hy, hset⟩

private noncomputable def cayleyEndpoints (U V : Finset (E 2)) (l : Line 3) : E 2 × E 2 :=
  if h : l ∈ cayleyLines U V then Classical.choose (cayleyLines_endpoint_exists U V l h)
  else (0, 0)

private lemma cayleyEndpoints_spec (U V : Finset (E 2)) (l : Line 3)
    (hl : l ∈ cayleyLines U V) :
    (cayleyEndpoints U V l).1 ∈ U ∧ (cayleyEndpoints U V l).2 ∈ V ∧
      (l.1 : Set (E 3)) = cayleySet (cayleyEndpoints U V l).1 (cayleyEndpoints U V l).2 := by
  simp only [cayleyEndpoints, dif_pos hl]
  exact Classical.choose_spec (cayleyLines_endpoint_exists U V l hl)

theorem cayley_plane_cap (U V : Finset (E 2)) (H : Plane 3) :
    FiniteCardBound {l : Line 3 | l ∈ cayleyLines U V ∧ l.1 ≤ H.1}
      (min (U.card : ℝ) V.card) := by
  classical
  let S : Set (Line 3) := {l | l ∈ cayleyLines U V ∧ l.1 ≤ H.1}
  let L : Finset (Line 3) := (U.product V).image (fun p => cayleyLine p.1 p.2)
  have hSsub : S ⊆ (L : Set (Line 3)) := by
    intro l hl
    rcases hl with ⟨hlines, hplane⟩
    simp only [cayleyLines, Set.mem_setOf_eq] at hlines
    rcases hlines with ⟨x, hx, y, hy, hset⟩
    have hline : l = cayleyLine x y := cayleyLine_eq_of_set_eq l x y hset
    have hLmem : cayleyLine x y ∈ L := by
      exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
    change l ∈ L
    rw [hline]
    exact hLmem
  have hSfinite : S.Finite := (L.finite_toSet).subset hSsub
  let fLeft : Line 3 → E 2 := fun l => (cayleyEndpoints U V l).1
  let fRight : Line 3 → E 2 := fun l => (cayleyEndpoints U V l).2
  have hleft : S.ncard ≤ (U : Set (E 2)).ncard := by
    apply Set.ncard_le_ncard_of_injOn fLeft
    · intro l hl
      exact (cayleyEndpoints_spec U V l hl.1).1
    · intro l hl l' hl' hxy
      rcases hl with ⟨hlines, hplane⟩
      rcases hl' with ⟨hlines', hplane'⟩
      have hdata := cayleyEndpoints_spec U V l hlines
      have hdata' := cayleyEndpoints_spec U V l' hlines'
      have hleftEq : (cayleyEndpoints U V l).1 = (cayleyEndpoints U V l').1 := hxy
      have hcan : cayleyAffineLine (cayleyEndpoints U V l).1 (cayleyEndpoints U V l).2 ≤ H.1 := by
        have hAffine := cayleyAffineLine_eq_of_set_eq l _ _ hdata.2.2
        rw [← hAffine]
        exact hplane
      have hcan' : cayleyAffineLine (cayleyEndpoints U V l').1 (cayleyEndpoints U V l').2 ≤ H.1 := by
        have hAffine := cayleyAffineLine_eq_of_set_eq l' _ _ hdata'.2.2
        rw [← hAffine]
        exact hplane'
      have hcan'left := hcan'
      rw [← hleftEq] at hcan'left
      have hleftRight : (cayleyEndpoints U V l).2 = (cayleyEndpoints U V l').2 :=
        cayley_plane_fixed_left H (cayleyEndpoints U V l).1 (cayleyEndpoints U V l).2
          (cayleyEndpoints U V l').2 hcan hcan'left
      have hpairs : cayleyEndpoints U V l = cayleyEndpoints U V l' :=
        Prod.ext hleftEq hleftRight
      have hset : (l.1 : Set (E 3)) = (l'.1 : Set (E 3)) := by
        calc
          (l.1 : Set (E 3)) = cayleySet (cayleyEndpoints U V l).1 (cayleyEndpoints U V l).2 :=
            hdata.2.2
          _ = cayleySet (cayleyEndpoints U V l').1 (cayleyEndpoints U V l').2 := by rw [hpairs]
          _ = (l'.1 : Set (E 3)) := hdata'.2.2.symm
      apply Subtype.ext
      exact (AffineSubspace.ext_iff _ _).2 hset
  have hright : S.ncard ≤ (V : Set (E 2)).ncard := by
    apply Set.ncard_le_ncard_of_injOn fRight
    · intro l hl
      exact (cayleyEndpoints_spec U V l hl.1).2.1
    · intro l hl l' hl' hxy
      rcases hl with ⟨hlines, hplane⟩
      rcases hl' with ⟨hlines', hplane'⟩
      have hdata := cayleyEndpoints_spec U V l hlines
      have hdata' := cayleyEndpoints_spec U V l' hlines'
      have hrightEq : (cayleyEndpoints U V l).2 = (cayleyEndpoints U V l').2 := hxy
      have hcan : cayleyAffineLine (cayleyEndpoints U V l).1 (cayleyEndpoints U V l).2 ≤ H.1 := by
        have hAffine := cayleyAffineLine_eq_of_set_eq l _ _ hdata.2.2
        rw [← hAffine]
        exact hplane
      have hcan' : cayleyAffineLine (cayleyEndpoints U V l').1 (cayleyEndpoints U V l').2 ≤ H.1 := by
        have hAffine := cayleyAffineLine_eq_of_set_eq l' _ _ hdata'.2.2
        rw [← hAffine]
        exact hplane'
      have hcan'right := hcan'
      rw [← hrightEq] at hcan'right
      have hleftRight : (cayleyEndpoints U V l).1 = (cayleyEndpoints U V l').1 :=
        cayley_plane_fixed_right H (cayleyEndpoints U V l).2 (cayleyEndpoints U V l).1
          (cayleyEndpoints U V l').1 hcan hcan'right
      have hpairs : cayleyEndpoints U V l = cayleyEndpoints U V l' :=
        Prod.ext hleftRight hrightEq
      have hset : (l.1 : Set (E 3)) = (l'.1 : Set (E 3)) := by
        calc
          (l.1 : Set (E 3)) = cayleySet (cayleyEndpoints U V l).1 (cayleyEndpoints U V l).2 :=
            hdata.2.2
          _ = cayleySet (cayleyEndpoints U V l').1 (cayleyEndpoints U V l').2 := by rw [hpairs]
          _ = (l'.1 : Set (E 3)) := hdata'.2.2.symm
      apply Subtype.ext
      exact (AffineSubspace.ext_iff _ _).2 hset
  change S.Finite ∧ (S.ncard : ℝ) ≤ min (U.card : ℝ) V.card
  refine ⟨hSfinite, ?_⟩
  have hnat : S.ncard ≤ min U.card V.card := by
    exact Nat.le_min.mpr ⟨by simpa using hleft, by simpa using hright⟩
  exact_mod_cast hnat

/-- ci:planar-motions, CI:338–376; both orientation classes. -/
private def planarCayleyLinesFinset (U V : Finset (E 2)) : Finset (Line 3) :=
  (U.product V).image (fun p => cayleyLine p.1 p.2)

private lemma planarCayleyLinesFinset_card (U V : Finset (E 2)) :
    (planarCayleyLinesFinset U V).card = U.card * V.card := by
  classical
  have hinj : Set.InjOn (fun p : E 2 × E 2 => cayleyLine p.1 p.2)
      (U.product V : Set (E 2 × E 2)) := by
    intro p hp q hq hline
    have hsets : cayleySet p.1 p.2 = cayleySet q.1 q.2 := by
      calc
        cayleySet p.1 p.2 = (cayleyLine p.1 p.2).1 := (cayleySet_eq_line _ _).symm
        _ = (cayleyLine q.1 q.2).1 :=
          congrArg (fun l : Line 3 => (l.1 : Set (E 3))) hline
        _ = cayleySet q.1 q.2 := cayleySet_eq_line _ _
    rcases (cayley_line_encoding).2 p.1 p.2 q.1 q.2 hsets with ⟨h₁, h₂⟩
    exact Prod.ext h₁ h₂
  calc
    (planarCayleyLinesFinset U V).card = (U.product V).card :=
      Finset.card_image_iff.mpr hinj
    _ = U.card * V.card := Finset.card_product _ _

private noncomputable def planarGraphCode (g : Motion 2) : E 3 :=
  if h : ∃ z : E 3, ∀ x y : E 2, g x = y ↔ z ∈ cayleySet x y then
    Classical.choose h
  else 0

private lemma planarGraphCode_spec (g : Motion 2)
    (h : ∃ z : E 3, ∀ x y : E 2, g x = y ↔ z ∈ cayleySet x y) :
    ∀ x y : E 2, g x = y ↔ planarGraphCode g ∈ cayleySet x y := by
  unfold planarGraphCode
  rw [dif_pos h]
  exact Classical.choose_spec h

private lemma planarPostcompose_matchPoints (R : E 2 ≃ₗᵢ[ℝ] E 2)
    (U V : Finset (E 2)) (g : Motion 2) :
    matchPoints U (V.image R) (planarPostcompose R g) = matchPoints U V g := by
  classical
  ext x
  simp only [matchPoints, Finset.mem_filter]
  constructor
  · rintro ⟨hxU, hximg⟩
    rcases Finset.mem_image.mp hximg with ⟨y, hy, hEq⟩
    refine ⟨hxU, ?_⟩
    have hyx : y = g x := R.injective (by simpa [planarPostcompose] using hEq)
    exact hyx ▸ hy
  · rintro ⟨hxU, hxV⟩
    refine ⟨hxU, Finset.mem_image.mpr ?_⟩
    exact ⟨g x, hxV, by simp [planarPostcompose]⟩

private lemma planarPostcompose_det (R : E 2 ≃ₗᵢ[ℝ] E 2) (g : Motion 2) :
    LinearMap.det ((planarPostcompose R g).linearIsometryEquiv.toLinearEquiv.toLinearMap) =
      LinearMap.det R.toLinearEquiv.toLinearMap *
        LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  have hcomp :
      (planarPostcompose R g).linearIsometryEquiv.toLinearEquiv.toLinearMap =
        R.toLinearEquiv.toLinearMap.comp g.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
    ext x
    rfl
  rw [hcomp, LinearMap.det_comp]

private lemma planar_isometry_det_cases (g : Motion 2) :
    LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap = 1 ∨
      LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap = -1 := by
  let f : E 2 →ₗ[ℝ] E 2 := g.linearIsometryEquiv.toLinearEquiv.toLinearMap
  have hnorm : f.normDet = 1 := by
    change (g.linearIsometryEquiv.toLinearIsometry.toLinearMap).normDet = 1
    exact g.linearIsometryEquiv.toLinearIsometry.normDet_eq_one
  have habs : |LinearMap.det f| = 1 := by
    rw [← LinearMap.normDet_eq_abs_det]
    exact hnorm
  by_cases hdet : 0 ≤ LinearMap.det f
  · left
    rw [abs_of_nonneg hdet] at habs
    simpa [f] using habs
  · right
    have hdet' : LinearMap.det f < 0 := lt_of_not_ge hdet
    rw [abs_of_neg hdet'] at habs
    have hneg : LinearMap.det f = -1 := by linarith
    simpa [f] using hneg

private lemma planar_rich_line_expression_bound (u v k : ℕ)
    (hk₃ : 3 ≤ k) (hkuv : k ≤ min u v) :
    ((u * v : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2 +
      ((u * v : ℕ) : ℝ) * min (u : ℝ) (v : ℝ) / (k : ℝ) ^ 3 +
      ((u * v : ℕ) : ℝ) / (k : ℝ) ≤
      3 * (((u * v : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by
  let m : ℝ := u
  let n : ℝ := v
  let q : ℝ := k
  let l : ℝ := m * n
  let b : ℝ := min m n
  have h3q : (3 : ℝ) ≤ q := by
    dsimp [q]
    exact_mod_cast hk₃
  have hqpos : 0 < q := by linarith
  have hqone : 1 ≤ q := by linarith
  have hmpos : 0 < m := by
    have hu : 3 ≤ u := hk₃.trans (hkuv.trans (Nat.min_le_left _ _))
    dsimp [m]
    exact_mod_cast (by omega : 0 < u)
  have hnpos : 0 < n := by
    have hv : 3 ≤ v := hk₃.trans (hkuv.trans (Nat.min_le_right _ _))
    dsimp [n]
    exact_mod_cast (by omega : 0 < v)
  have hqleM : q ≤ m := by
    have hu : k ≤ u := hkuv.trans (Nat.min_le_left _ _)
    dsimp [q, m]
    exact_mod_cast hu
  have hqleN : q ≤ n := by
    have hv : k ≤ v := hkuv.trans (Nat.min_le_right _ _)
    dsimp [q, n]
    exact_mod_cast hv
  have hLpos : 0 < l := by dsimp [l]; positivity
  have hLnonneg : 0 ≤ l := le_of_lt hLpos
  have hbnonneg : 0 ≤ b := by dsimp [b]; positivity
  have hqSq : q ^ 2 ≤ l := by
    have hprod : 0 ≤ (m - q) * (n - q) :=
      mul_nonneg (sub_nonneg.mpr hqleM) (sub_nonneg.mpr hqleN)
    dsimp [l]
    nlinarith
  have hbSq : b ^ 2 ≤ l := by
    change (min m n) ^ 2 ≤ l
    rcases le_total m n with hmn | hnm
    · rw [min_eq_left hmn]
      dsimp [l]
      nlinarith [mul_nonneg (le_of_lt hmpos) (sub_nonneg.mpr hmn)]
    · rw [min_eq_right hnm]
      dsimp [l]
      nlinarith [mul_nonneg (le_of_lt hnpos) (sub_nonneg.mpr hnm)]
  have hqsqrt : q ≤ Real.sqrt l := Real.le_sqrt_of_sq_le hqSq
  have hbsqrt : b ≤ Real.sqrt l := Real.le_sqrt_of_sq_le hbSq
  have hbq : b / q ≤ Real.sqrt l := by
    have hbq' : b ≤ q * Real.sqrt l := by
      calc
      b ≤ Real.sqrt l := hbsqrt
      _ ≤ q * Real.sqrt l := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hqone) (Real.sqrt_nonneg l)]
    apply (div_le_iff₀ hqpos).2
    simpa [mul_comm] using hbq'
  have hpow : l ^ ((3 : ℝ) / 2) = l * Real.sqrt l := by
    have he : (3 : ℝ) / 2 = 1 + (1 : ℝ) / 2 := by ring
    rw [he, Real.rpow_add hLpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hscale : 0 ≤ l / q ^ 2 := by positivity
  have hmid : l * b / q ^ 3 ≤ l * Real.sqrt l / q ^ 2 := by
    calc
      l * b / q ^ 3 = (l / q ^ 2) * (b / q) := by
        field_simp [ne_of_gt hqpos] <;> ring
      _ ≤ (l / q ^ 2) * Real.sqrt l := mul_le_mul_of_nonneg_left hbq hscale
      _ = l * Real.sqrt l / q ^ 2 := by ring
  have hlast : l / q ≤ l * Real.sqrt l / q ^ 2 := by
    calc
      l / q = (l / q ^ 2) * q := by field_simp [ne_of_gt hqpos] <;> ring
      _ ≤ (l / q ^ 2) * Real.sqrt l := mul_le_mul_of_nonneg_left hqsqrt hscale
      _ = l * Real.sqrt l / q ^ 2 := by ring
  have hLcast : ((u * v : ℕ) : ℝ) = l := by simp [l, m, n, Nat.cast_mul]
  have hBcast : min (u : ℝ) (v : ℝ) = b := rfl
  rw [hLcast, hBcast]
  rw [hpow]
  linarith [hmid, hlast]

private theorem planar_direct_rich_bound (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hci : ∀ (L : Finset (Line 3)) (B : ℝ) (k : ℕ), 0 ≤ B → planeCap L B → 3 ≤ k →
      FiniteCardBound (richPoints L k) (C₀ *
        ((L.card : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2 +
          (L.card : ℝ) * B / (k : ℝ) ^ 3 + (L.card : ℝ) / k)))
    (U V : Finset (E 2)) (k : ℕ) (hk₃ : 3 ≤ k) (hkuv : k ≤ min U.card V.card) :
    FiniteCardBound
      {g : Motion 2 | g ∈ richMotions U V k ∧ planarDirect g}
      (3 * C₀ * (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2)) := by
  classical
  obtain ⟨R, hRdet, hgeneric⟩ := planar_generic_rotation U V
  let V' : Finset (E 2) := V.image R
  let L : Finset (Line 3) := planarCayleyLinesFinset U V'
  let B : ℝ := min (U.card : ℝ) (V'.card : ℝ)
  let D : Set (Motion 2) := {g | g ∈ richMotions U V k ∧ planarDirect g}
  let code : Motion 2 → E 3 := fun g => planarGraphCode (planarPostcompose R g)
  have hVcard : V'.card = V.card := by
    dsimp [V']
    exact Finset.card_image_iff.mpr R.injective.injOn
  have hkuv' : k ≤ min U.card V'.card := by rw [hVcard]; exact hkuv
  have hLcard : L.card = U.card * V'.card := planarCayleyLinesFinset_card U V'
  have hcap : planeCap L B := by
    intro H
    let T : Set (Line 3) := {l | l ∈ cayleyLines U V' ∧ l.1 ≤ H.1}
    obtain ⟨hTfin, hTbound⟩ := cayley_plane_cap U V' H
    let F := L.filter (fun l => l.1 ≤ H.1)
    have hFsub : (F : Set (Line 3)) ⊆ T := by
      intro l hl
      rcases Finset.mem_filter.mp hl with ⟨hlL, hlplane⟩
      rcases Finset.mem_image.mp hlL with ⟨p, hp, rfl⟩
      rcases Finset.mem_product.mp hp with ⟨hpU, hpV⟩
      exact ⟨by
        simp only [cayleyLines, Set.mem_setOf_eq]
        exact ⟨p.1, hpU, p.2, hpV, cayleySet_eq_line p.1 p.2⟩,
        hlplane⟩
    have hFcard : F.card ≤ T.ncard := by
      have h := Set.ncard_le_ncard hFsub hTfin
      simpa using h
    change (F.card : ℝ) ≤ B
    calc
      (F.card : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast hFcard
      _ ≤ B := by simpa [T, B] using hTbound
  have hBnonneg : 0 ≤ B := by positivity
  obtain ⟨hRichFin, hRichBound⟩ := hci L B k hBnonneg hcap hk₃
  have hDsub : D ⊆ richMotions U V 2 := by
    intro g hg
    change (2 : ℝ) ≤ (matchCount U V g : ℝ)
    rcases hg with ⟨hg, -⟩
    change (k : ℝ) ≤ (matchCount U V g : ℝ) at hg
    have h2k : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
    exact h2k.trans hg
  have hDfin : D.Finite := (planar_motions_finite U V).subset hDsub
  have hspec : ∀ g ∈ D, ∀ x y : E 2,
      (planarPostcompose R g) x = y ↔ code g ∈ cayleySet x y := by
    intro g hg x y
    rcases hg with ⟨hgRich, hgDirect⟩
    have hgdet : LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap = 1 := by
      simpa [planarDirect, AffineIsometryEquiv.linear_eq_linear_isometry] using hgDirect
    have hdirect' : planarDirect (planarPostcompose R g) := by
      change LinearMap.det
        ((planarPostcompose R g).linearIsometryEquiv.toLinearEquiv.toLinearMap) = 1
      rw [planarPostcompose_det, hRdet, hgdet]
      norm_num
    have hkg : k ≤ matchCount U V g := by
      change (k : ℝ) ≤ (matchCount U V g : ℝ) at hgRich
      exact_mod_cast hgRich
    have h2 : 2 ≤ matchCount U V' (planarPostcompose R g) := by
      have hcount := congrArg Finset.card (planarPostcompose_matchPoints R U V g)
      have hcount' : matchCount U V' (planarPostcompose R g) = matchCount U V g := by
        simpa [matchCount, V'] using hcount
      rw [hcount']
      omega
    have hchart := hgeneric (planarPostcompose R g) hdirect' h2
    obtain ⟨z, hz, -⟩ := (planar_cayley_chart).2 (planarPostcompose R g) hdirect' hchart
    exact planarGraphCode_spec (planarPostcompose R g) ⟨z, hz⟩ x y
  have hmaps : ∀ g ∈ D, code g ∈ richPoints L k := by
    intro g hg
    let h := planarPostcompose R g
    let P := matchPoints U V' h
    let F := L.filter (fun l => code g ∈ l.1)
    have hmatch : matchCount U V' h = matchCount U V g := by
      have hcount := congrArg Finset.card (planarPostcompose_matchPoints R U V g)
      simpa [matchCount, V', h, P] using hcount
    have hmatchcard : matchCount U V' h = P.card := by rfl
    have hlineMaps : Set.MapsTo (fun x : E 2 => cayleyLine x (h x))
        (P : Set (E 2)) (F : Set (Line 3)) := by
      intro x hx
      have hx' : x ∈ U ∧ h x ∈ V' := by simpa [P, matchPoints] using hx
      have hz : code g ∈ (cayleyLine x (h x)).1 := by
        have hz' := (hspec g hg x (h x)).mp rfl
        change code g ∈ ((cayleyLine x (h x)).1 : Set (E 3))
        rw [cayleySet_eq_line]
        exact hz'
      apply Finset.mem_filter.mpr
      refine ⟨?_, hz⟩
      apply Finset.mem_image.mpr
      exact ⟨(x, h x), Finset.mem_product.mpr hx', rfl⟩
    have hlineInj : Set.InjOn (fun x : E 2 => cayleyLine x (h x)) (P : Set (E 2)) := by
      intro x hx y hy hxy
      have hsets : cayleySet x (h x) = cayleySet y (h y) := by
        calc
          cayleySet x (h x) = (cayleyLine x (h x)).1 := (cayleySet_eq_line _ _).symm
          _ = (cayleyLine y (h y)).1 :=
            congrArg (fun l : Line 3 => (l.1 : Set (E 3))) hxy
          _ = cayleySet y (h y) := cayleySet_eq_line _ _
      exact ((cayley_line_encoding).2 x (h x) y (h y) hsets).1
    have hcard : P.card ≤ F.card := Finset.card_le_card_of_injOn _ hlineMaps hlineInj
    have hkg : k ≤ matchCount U V g := by
      rcases hg with ⟨hgRich, -⟩
      change (k : ℝ) ≤ (matchCount U V g : ℝ) at hgRich
      exact_mod_cast hgRich
    change k ≤ lineMultiplicity L (code g)
    calc
      k ≤ matchCount U V g := hkg
      _ = P.card := hmatch.symm.trans hmatchcard
      _ ≤ F.card := hcard
      _ = lineMultiplicity L (code g) := by simp [F, lineMultiplicity]
  have hcodeInj : Set.InjOn code D := by
    intro g hg g' hg' hcode
    apply AffineIsometryEquiv.ext
    intro x
    apply R.injective
    have hval : (planarPostcompose R g') x = (planarPostcompose R g) x := by
      apply (hspec g' hg' x ((planarPostcompose R g) x)).mpr
      rw [← hcode]
      exact (hspec g hg x ((planarPostcompose R g) x)).mp rfl
    simpa [planarPostcompose] using hval.symm
  have hDcard : D.ncard ≤ (richPoints L k).ncard :=
    Set.ncard_le_ncard_of_injOn code hmaps hcodeInj hRichFin
  have hexpr :
      (L.card : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2 +
        (L.card : ℝ) * B / (k : ℝ) ^ 3 + (L.card : ℝ) / k ≤
        3 * (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by
    have h := planar_rich_line_expression_bound U.card V'.card k hk₃ hkuv'
    simpa [B, hLcard, hVcard, Nat.cast_mul, Nat.cast_min] using h
  have hDbound :
      (D.ncard : ℝ) ≤
        3 * C₀ * (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by
    calc
      (D.ncard : ℝ) ≤ (richPoints L k).ncard := by exact_mod_cast hDcard
      _ ≤ C₀ * ((L.card : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2 +
          (L.card : ℝ) * B / (k : ℝ) ^ 3 + (L.card : ℝ) / k) := hRichBound
      _ ≤ 3 * C₀ * (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by
        nlinarith [hC₀, hexpr]
  exact ⟨hDfin, hDbound⟩

theorem ci_planar_motions : ∃ C : ℝ, 0 < C ∧
    ∀ (U V : Finset (E 2)) (k : ℕ), 3 ≤ k → k ≤ min U.card V.card →
      FiniteCardBound (richMotions U V k)
        (C * ((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2) := by
  classical
  obtain ⟨C₀, hC₀, hci⟩ := ci_rich_lines
  refine ⟨6 * C₀, by positivity, ?_⟩
  intro U V k hk₃ hkuv
  let S : Set (Motion 2) := richMotions U V k
  let D : Set (Motion 2) := {g | g ∈ S ∧
    LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap = 1}
  let N : Set (Motion 2) := {g | g ∈ S ∧
    LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap = -1}
  let Q : ℝ := ((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2
  have hSsub : S ⊆ richMotions U V 2 := by
    intro g hg
    change (2 : ℝ) ≤ (matchCount U V g : ℝ)
    change (k : ℝ) ≤ (matchCount U V g : ℝ) at hg
    have h2k : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
    exact h2k.trans hg
  have hSfin : S.Finite := (planar_motions_finite U V).subset hSsub
  have hDfin : D.Finite := hSfin.subset (by
    intro g hg
    exact hg.1)
  have hNfin : N.Finite := hSfin.subset (by
    intro g hg
    exact hg.1)
  have hDbound : FiniteCardBound D (3 * C₀ * Q) := by
    simpa [D, S, planarDirect, AffineIsometryEquiv.linear_eq_linear_isometry, Q] using
      (planar_direct_rich_bound C₀ hC₀ hci U V k hk₃ hkuv)
  have he₀ : planarStdBasis 0 ≠ 0 := by
    intro h
    have hc := congrArg (fun x : E 2 => x 0) h
    have hc' : (1 : ℝ) = 0 := by
      simpa [planarStdBasis, EuclideanSpace.basisFun_apply] using hc
    norm_num at hc'
  have horthDim : Module.finrank ℝ ↥((ℝ ∙ planarStdBasis 0)ᗮ) = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ planarStdBasis 0)
    rw [finrank_span_singleton he₀, finrank_euclideanSpace] at hsum
    simp only [Fintype.card_fin] at hsum
    omega
  let F : E 2 ≃ₗᵢ[ℝ] E 2 := Submodule.reflection (ℝ ∙ planarStdBasis 0)
  have hFdet : LinearMap.det F.toLinearEquiv.toLinearMap = -1 := by
    have h := Submodule.det_reflection (ℝ ∙ planarStdBasis 0)
    simpa [F, horthDim] using h
  let V' : Finset (E 2) := V.image F
  let D' : Set (Motion 2) := {g | g ∈ richMotions U V' k ∧ planarDirect g}
  have hV'card : V'.card = V.card := by
    dsimp [V']
    exact Finset.card_image_iff.mpr F.injective.injOn
  have hkuv' : k ≤ min U.card V'.card := by rw [hV'card]; exact hkuv
  have hD'bound : FiniteCardBound D'
      (3 * C₀ * (((U.card : ℝ) * V'.card) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ 2)) :=
    planar_direct_rich_bound C₀ hC₀ hci U V' k hk₃ hkuv'
  have hNmaps : ∀ g ∈ N, planarPostcompose F g ∈ D' := by
    intro g hg
    rcases hg with ⟨hgrich, hgdet⟩
    have hcount : matchCount U V' (planarPostcompose F g) = matchCount U V g := by
      have h := congrArg Finset.card (planarPostcompose_matchPoints F U V g)
      simpa [matchCount, V'] using h
    have hrich : planarPostcompose F g ∈ richMotions U V' k := by
      change (k : ℝ) ≤ (matchCount U V' (planarPostcompose F g) : ℝ)
      change (k : ℝ) ≤ (matchCount U V g : ℝ) at hgrich
      rw [hcount]
      exact hgrich
    have hdirect : planarDirect (planarPostcompose F g) := by
      change LinearMap.det
        ((planarPostcompose F g).linearIsometryEquiv.toLinearEquiv.toLinearMap) = 1
      rw [planarPostcompose_det, hFdet, hgdet]
      norm_num
    exact ⟨hrich, hdirect⟩
  have hNinj : Set.InjOn (fun g : Motion 2 => planarPostcompose F g) N := by
    intro g hg g' hg' heq
    apply AffineIsometryEquiv.ext
    intro x
    have hval := congrArg (fun h : Motion 2 => h x) heq
    apply F.injective
    simpa [planarPostcompose] using hval
  have hNcard : N.ncard ≤ D'.ncard :=
    Set.ncard_le_ncard_of_injOn _ hNmaps hNinj hD'bound.1
  have hNbound : (N.ncard : ℝ) ≤ 3 * C₀ * Q := by
    calc
      (N.ncard : ℝ) ≤ (D'.ncard : ℝ) := by exact_mod_cast hNcard
      _ ≤ 3 * C₀ * (((U.card : ℝ) * V'.card) ^ ((3 : ℝ) / 2) /
          (k : ℝ) ^ 2) := hD'bound.2
      _ = 3 * C₀ * Q := by simp [Q, hV'card]
  have hSN : S = D ∪ N := by
    ext g
    constructor
    · intro hg
      rcases planar_isometry_det_cases g with hdet | hdet
      · exact Or.inl ⟨hg, hdet⟩
      · exact Or.inr ⟨hg, hdet⟩
    · intro hg
      rcases hg with hg | hg
      · exact hg.1
      · exact hg.1
  have hdisj : Disjoint D N := by
    rw [Set.disjoint_left]
    intro g hg hn
    have hfalse : (1 : ℝ) = -1 := hg.2.symm.trans hn.2
    norm_num at hfalse
  have hScard : S.ncard = D.ncard + N.ncard := by
    rw [hSN, Set.ncard_union_eq hdisj hDfin hNfin]
  have hsumBound : (S.ncard : ℝ) ≤ 6 * C₀ * Q := by
    rw [hScard, Nat.cast_add]
    linarith [hDbound.2, hNbound]
  refine ⟨hSfin, ?_⟩
  change (S.ncard : ℝ) ≤ 6 * C₀ *
    (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2)) / (k : ℝ) ^ 2
  calc
    (S.ncard : ℝ) ≤ 6 * C₀ * Q := hsumBound
    _ = 6 * C₀ * (((U.card : ℝ) * V.card) ^ ((3 : ℝ) / 2)) / (k : ℝ) ^ 2 := by
      simp [Q]
      ring

end DistinctDistances.TrackC
