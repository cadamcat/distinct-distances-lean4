import OAI.AlgebraicGeometry.PlaneCurves.Factorization
import DistinctDistances.TrackA.GcdSpecializationSupport
import DistinctDistances.TrackA.SylvesterMatrixSupport
import DistinctDistances.TrackA.RegularityGenericVectorSupport
import DistinctDistances.TrackA.CommonRadialSourceOpenSupport
import DistinctDistances.TrackA.NarrowRadialCountSupport
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
open UniqueFactorizationMonoid

/-- Minimality in the full path system, rather than an equal-dimension
assumption, separates a retained component from every other component. -/
theorem a2_minimal_component_separator {d : ℕ} (I : Ideal (Poly d))
    (V W : AffineVariety d) (hV : V.IsComponentOf I) (hW : W.IsComponentOf I)
    (hne : V ≠ W) : ∃ f : Poly d, f ∈ W.ideal ∧ f ∉ V.ideal := by
  have hnot : ¬ W.ideal ≤ V.ideal := by
    intro hle
    have he : W.ideal = V.ideal := le_antisymm hle (hV.2 ⟨hW.isPrime, hW.le⟩ hle)
    exact hne (AffineVariety.ext he.symm)
  change ¬ ∀ f, f ∈ W.ideal → f ∈ V.ideal at hnot
  push Not at hnot
  exact hnot

/-- Actual finite radial fibers of a retained component avoid every other
full-path component on a principal target open, whatever its dimension. -/
theorem a2_radial_fiber_avoids_other_component {d l : ℕ} (I : Ideal (Poly d))
    (V W : AffineVariety d) (hV : V.IsComponentOf I) (hW : W.IsComponentOf I)
    (hne : V ≠ W) (hVl : V.dimension = l) (p : Point d)
    (himage : (radialImage p V).dimension = l) (hactual : ∃ x ∈ V.points, x ≠ p) :
    ∃ (H : Poly d) (e : ℕ), H.IsHomogeneous e ∧ H ∉ (radialImage p V).ideal ∧
      ∀ z : ProjectivePoint d, MvPolynomial.eval z.rep H ≠ 0 →
        ∀ x ∈ radialFiber p V z, x ∉ W.points := by
  obtain ⟨f, hfW, hfV⟩ := a2_minimal_component_separator I V W hV hW hne
  obtain ⟨H, e, hhom, hnot, havoid⟩ := radial_fiber_avoids_proper_cut V hV.isPrime
    hVl p himage hactual f hfV
  refine ⟨H, e, hhom, hnot, ?_⟩
  intro z hz x hx hxW
  exact havoid z hz x hx (by simpa only [MvPolynomial.aeval_eq_eval] using hxW f hfW)

/-- One target open makes actual retained fibers avoid all other minimal
components of the full system, including omitted components. -/
theorem a2_radial_group_open_full_components {d l : ℕ} (I : Ideal (Poly d))
    (J : AffineFamily.Family d) (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l)
    (Y : AffineVariety d) (hY : Y ∈ J) (hcomponents : ∀ V ∈ J, V.IsComponentOf I)
    (p : Point d) (himage : (radialImage p Y).dimension = l)
    (r : AffineVariety d → ℕ)
    (hgen : ∀ V ∈ J, radialImage p V = radialImage p Y →
      GenericallyFiniteRadialDegree p V (r V)) :
    ∃ (Q : Poly d) (e : ℕ), Q.IsHomogeneous e ∧ Q ∉ (radialImage p Y).ideal ∧
      ∀ z : ProjectivePoint d, MvPolynomial.eval z.rep Q ≠ 0 →
        (∀ V ∈ J, radialImage p V = radialImage p Y → z ∈ (radialImage p Y).points →
          (radialFiber p V z).Finite ∧ (radialFiber p V z).ncard = r V) ∧
        ∀ V ∈ J, radialImage p V = radialImage p Y → ∀ x ∈ radialFiber p V z,
          ∀ W : AffineVariety d, W.IsComponentOf I → x ∈ W.points → W = V := by
  let Z := radialImage p Y
  letI : Z.ideal.IsPrime := radialImage_irreducible p Y (hJ Y hY).1
    (radial_actual_of_generic Y p (hgen Y hY rfl))
  letI : Fintype I.minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly d) I).fintype
  let Pairs := {a : J × I.minimalPrimes //
    radialImage p a.1.val = Z ∧ a.1.val.ideal ≠ a.2.val}
  have hpw (a : Pairs) : ∃ (H : Poly d) (e : ℕ), H.IsHomogeneous e ∧ H ∉ Z.ideal ∧
      ∀ z : ProjectivePoint d, MvPolynomial.eval z.rep H ≠ 0 →
        ∀ x ∈ radialFiber p a.val.1.val z,
          x ∉ (⟨a.val.2.val, a.val.2.property.isPrime.isRadical⟩ : AffineVariety d).points := by
    let W : AffineVariety d := ⟨a.val.2.val, a.val.2.property.isPrime.isRadical⟩
    have hne : a.val.1.val ≠ W := fun he => a.property.2 (congrArg AffineVariety.ideal he)
    have hd : (radialImage p a.val.1.val).dimension = l := by
      rw [a.property.1]
      exact himage
    obtain ⟨H, e, hh, hn, hc⟩ := a2_radial_fiber_avoids_other_component I
      a.val.1.val W (hcomponents _ a.val.1.property) a.val.2.property hne
      (hJ _ a.val.1.property).2 p hd
      (radial_actual_of_generic _ p (hgen _ a.val.1.property a.property.1))
    rw [a.property.1] at hn
    exact ⟨H, e, hh, hn, hc⟩
  choose H e hhom hnot havoid using hpw
  obtain ⟨Q₀, e₀, hh₀, hn₀, hc₀⟩ := radial_group_fiber_open J hl hJ Y hY p
    himage r hgen
  have hprod : (∏ a : Pairs, H a) ∉ Z.ideal := by
    intro h
    obtain ⟨a, _, ha⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hnot a ha
  refine ⟨Q₀ * ∏ a : Pairs, H a, e₀ + ∑ a : Pairs, e a,
    hh₀.mul (MvPolynomial.IsHomogeneous.prod Finset.univ H e (fun a _ => hhom a)),
    (fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hn₀ hprod), ?_⟩
  intro z hz
  have hzparts : MvPolynomial.eval z.rep Q₀ ≠ 0 ∧
      (∏ a : Pairs, MvPolynomial.eval z.rep (H a)) ≠ 0 := by
    simpa only [map_mul, map_prod, mul_ne_zero_iff] using hz
  refine ⟨(hc₀ z hzparts.1).1, ?_⟩
  intro V hV hVz x hx W hW hxW
  by_contra hne
  have hi : V.ideal ≠ W.ideal := fun he => hne (AffineVariety.ext he.symm)
  let a : Pairs := ⟨(⟨V, hV⟩, ⟨W.ideal, hW⟩), hVz, hi⟩
  have hzH := Finset.prod_ne_zero_iff.mp hzparts.2 a (Finset.mem_univ _)
  exact havoid a z hzH x hx hxW

/-- Fix the first coordinate tuple of the original product polynomial. -/
def a2_productLeft {d : ℕ} (x : Point d) (H : Poly (d+d)) : Poly d :=
  MvPolynomial.aeval (Fin.append (fun i => MvPolynomial.C (x i)) MvPolynomial.X) H

theorem a2_productLeft_eval {d : ℕ} (x y : Point d) (H : Poly (d+d)) :
    MvPolynomial.eval y (a2_productLeft x H) =
      MvPolynomial.eval (Fin.append x y) H := by
  change (MvPolynomial.aeval y).comp
    (MvPolynomial.aeval (Fin.append (fun i => MvPolynomial.C (x i)) MvPolynomial.X)) H =
      MvPolynomial.aeval (Fin.append x y) H
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append, Fin.addCases, j.isLt]
  · simp [Fin.append, Fin.addCases, show ¬ d + j.val < d by omega]

/-- A single target point preserves the generic list open and realizes
all actual-center fibers outside every other full-system component. -/
theorem a2_common_target_full_components {d l : ℕ} (I : Ideal (Poly d))
    (X : AffineVariety d) (J : AffineFamily.Family d) (hl : 1 ≤ l)
    (hJ : AffineFamily.IsPure J l) (Y : AffineVariety d) (hY : Y ∈ J)
    (hcomponents : ∀ V ∈ J, V.IsComponentOf I)
    (q : ℕ) (hgeneric : GenericMovingRootBound X Y J q)
    (S : Finset (Point d)) (himage : ∀ p ∈ S, (radialImage p Y).dimension = l) :
    ∃ (H : Poly (d+d)) (y : Point d), y ∈ Y.points ∧
      (∃ x ∈ X.points, MvPolynomial.eval (Fin.append x y) H ≠ 0) ∧
      (∀ x ∈ X.points, MvPolynomial.eval (Fin.append x y) H ≠ 0 →
        x ≠ y ∧ (movingRoots x y J).Finite ∧ (movingRoots x y J).ncard ≤ q) ∧
      (S.Nonempty → ∀ W : AffineVariety d, W.IsComponentOf I → y ∈ W.points → W = Y) ∧
      ∀ p ∈ S, ∃ hpy : y ≠ p,
        (groupMovingFiber J p Y (radialProjection p y hpy) y).Finite ∧
        (groupMovingFiber J p Y (radialProjection p y hpy) y).ncard = groupDepth p J Y - 1 ∧
        ∀ x ∈ groupMovingFiber J p Y (radialProjection p y hpy) y,
          ∃ V ∈ J, x ∈ radialFiber p V (radialProjection p y hpy) ∧
            ∀ W : AffineVariety d, W.IsComponentOf I → x ∈ W.points → W = V := by
  obtain ⟨H, ⟨x₀, hx₀, y₀, hy₀, hH₀⟩, hcap⟩ := hgeneric
  letI : Y.ideal.IsPrime := (hJ Y hY).1
  have hHnot : a2_productLeft x₀ H ∉ Y.ideal := by
    intro h
    exact hH₀ ((a2_productLeft_eval x₀ y₀ H).symm.trans (hy₀ _ h))
  have hgen : ∀ p ∈ S, ∀ V ∈ J, radialImage p V = radialImage p Y →
      GenericallyFiniteRadialDegree p V (radialMapDegree p V) := by
    intro p hp V hV hVz
    have hd : (radialImage p V).dimension = l := by rw [hVz]; exact himage p hp
    have hex := radial_generic_degree_exists V (hJ V hV).1 hl (hJ V hV).2 p hd
    simpa only [radialMapDegree, dif_pos hex] using hex.choose_spec
  have hw (p : S) : ∃ f : Poly d, f ∉ Y.ideal ∧ ∀ y ∈ Y.points,
      MvPolynomial.eval y f ≠ 0 → ∃ hpy : y ≠ p.val,
        (∀ V ∈ J, radialImage p.val V = radialImage p.val Y →
          (radialFiber p.val V (radialProjection p.val y hpy)).Finite ∧
          (radialFiber p.val V (radialProjection p.val y hpy)).ncard = radialMapDegree p.val V) ∧
        ∀ V ∈ J, radialImage p.val V = radialImage p.val Y →
          ∀ x ∈ radialFiber p.val V (radialProjection p.val y hpy),
            ∀ W : AffineVariety d, W.IsComponentOf I → x ∈ W.points → W = V := by
    obtain ⟨Q, e, hhom, hnot, hopen⟩ := a2_radial_group_open_full_components I J hl hJ
      Y hY hcomponents p.val (himage p.val p.property) (radialMapDegree p.val)
      (hgen p.val p.property)
    obtain ⟨a, ha, hap⟩ := radial_center_coordinate_separator Y (hJ Y hY).1 hl (hJ Y hY).2 p.val
    refine ⟨a * radialDirectionPullback p.val Q,
      (fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha
        (radialDirectionPullback_not_mem Y p.val Q hhom hnot)), ?_⟩
    intro y hy hval
    have hparts : MvPolynomial.eval y a ≠ 0 ∧
        MvPolynomial.eval y (radialDirectionPullback p.val Q) ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using hval
    have hpy : y ≠ p.val := by intro he; exact hparts.1 (he ▸ hap)
    obtain ⟨hcount, havoid⟩ := hopen (radialProjection p.val y hpy)
      (radialDirectionPullback_nonzero p.val y hpy Q hhom hparts.2)
    have hz : radialProjection p.val y hpy ∈ (radialImage p.val Y).points :=
      ProjectiveVariety.subset_closure _ ⟨y, hy, hpy, rfl⟩
    exact ⟨hpy, fun V hV hVz => hcount V hV hVz hz, havoid⟩
  choose f hf hgood using hw
  have hprod : (∏ p : S, f p) ∉ Y.ideal := by
    intro h
    obtain ⟨p, _, hp⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hf p hp
  have hn : a2_productLeft x₀ H * ∏ p : S, f p ∉ Y.ideal :=
    fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hHnot hprod
  rw [← Y.vanishingIdeal_points, MvPolynomial.mem_vanishingIdeal_iff] at hn
  push Not at hn
  obtain ⟨y, hy, hval⟩ := hn
  have hparts : MvPolynomial.eval y (a2_productLeft x₀ H) ≠ 0 ∧
      (∏ p : S, MvPolynomial.eval y (f p)) ≠ 0 := by
    simpa only [map_mul, map_prod, mul_ne_zero_iff, MvPolynomial.aeval_eq_eval] using hval
  refine ⟨H, y, hy, ⟨x₀, hx₀, ?_⟩, fun x hx hxy => hcap x hx y hy hxy, ?_, ?_⟩
  · simpa only [a2_productLeft_eval] using hparts.1
  · intro hSnon W hW hyW
    obtain ⟨p, hp⟩ := hSnon
    obtain ⟨hpy, _, havoid⟩ := hgood ⟨p, hp⟩ y hy
      ((Finset.prod_ne_zero_iff.mp hparts.2) ⟨p, hp⟩ (Finset.mem_univ _))
    exact havoid Y hY rfl y ⟨hy, hpy, rfl⟩ W hW hyW
  intro p hp
  obtain ⟨hpy, hcount, havoid⟩ := hgood ⟨p, hp⟩ y hy
    ((Finset.prod_ne_zero_iff.mp hparts.2) ⟨p, hp⟩ (Finset.mem_univ _))
  have hdisj : ∀ V ∈ J, radialImage p V = radialImage p Y →
      ∀ W ∈ J, V ≠ W → Disjoint (radialFiber p V (radialProjection p y hpy))
        (radialFiber p W (radialProjection p y hpy)) := by
    intro V hV hVz W hW hne
    apply Set.disjoint_left.mpr
    intro x hxV hxW
    exact hne (havoid V hV hVz x hxV W (hcomponents W hW) hxW.1).symm
  obtain ⟨hfinite, hcard⟩ := groupMovingFiber_count J p y Y hY hy hpy
    (radialMapDegree p) hcount hdisj
  refine ⟨hpy, hfinite, hcard, ?_⟩
  intro x hx
  obtain ⟨V, hxV⟩ := Set.mem_iUnion.mp hx.1
  obtain ⟨hV, hVz⟩ := Finset.mem_filter.mp V.property
  exact ⟨V.val, hV, hxV, havoid V.val hV hVz x hxV⟩

/-- A finite polynomial system and one nonvanishing condition witnessed
over a complex field extension are witnessed over the original field. -/
theorem a2_complex_point_of_field_open {n : ℕ} {K : Type*} [Field K] [Algebra ℂ K]
    (I : Ideal (Poly n)) (x : Fin n → K)
    (hx : ∀ f ∈ I, MvPolynomial.aeval x f = 0)
    (f : Poly n) (hf : MvPolynomial.aeval x f ≠ 0) :
    ∃ y : Point n, y ∈ MvPolynomial.zeroLocus ℂ I ∧ MvPolynomial.eval y f ≠ 0 := by
  have hn : f ∉ I.radical := by
    intro hm
    exact hf (MvPolynomial.radical_le_vanishingIdeal_zeroLocus I hm x hx)
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) I,
    MvPolynomial.mem_vanishingIdeal_iff] at hn
  push Not at hn
  simpa only [MvPolynomial.aeval_eq_eval] using hn

/-- The generic complex list bound also bounds any finite collection of
distinct moving parameters over a field extension. The finite model keeps
the original carrier equations and every required inequation. -/
theorem a2_moving_parameter_count_over_field {d n : ℕ} {K : Type*}
    [Field K] [Algebra ℂ K] (X : AffineVariety d) (J : AffineFamily.Family d)
    (y : Point d) (U : Poly d) (q : ℕ)
    (hcap : ∀ x ∈ X.points, MvPolynomial.eval x U ≠ 0 →
      x ≠ y ∧ (movingRoots x y J).Finite ∧ (movingRoots x y J).ncard ≤ q)
    (x : Fin d → K) (hx : ∀ f ∈ X.ideal, MvPolynomial.aeval x f = 0)
    (hU : MvPolynomial.aeval x U ≠ 0)
    (t : Fin n → K) (ht : Function.Injective t)
    (ht0 : ∀ i, t i ≠ 0) (ht1 : ∀ i, t i ≠ 1)
    (hroots : ∀ i, ∃ V ∈ J, ∀ f ∈ V.ideal,
      MvPolynomial.aeval (fun j => algebraMap ℂ K (y j) +
        t i * (x j - algebraMap ℂ K (y j))) f = 0) : n ≤ q := by
  let left : Fin d → Fin (d+n) := Fin.castAdd n
  let right : Fin n → Fin (d+n) := fun i => Fin.natAdd d i
  let θ : Fin (d+n) → K := Fin.append x t
  let I : Ideal (Poly (d+n)) := RingHom.ker (MvPolynomial.aeval θ)
  let T : Fin n → Poly (d+n) := fun i => MvPolynomial.X (right i)
  let U' : Poly (d+n) := MvPolynomial.rename left U
  let P : Poly (d+n) := U' * (∏ i, T i * (T i - 1)) *
    ∏ i, ∏ j ∈ Finset.univ.erase i, (T i - T j)
  have hleft : θ ∘ left = x := by
    funext i
    simp [θ, left, Fin.append, Fin.addCases, i.isLt]
  have hright (i : Fin n) : θ (right i) = t i := by
    simp [θ, right, Fin.append, Fin.addCases, show ¬ d + i.val < d by omega]
  have hU' : MvPolynomial.aeval θ U' ≠ 0 := by
    simpa only [U', MvPolynomial.aeval_rename, hleft] using hU
  have hT (i : Fin n) : MvPolynomial.aeval θ (T i) = t i := by
    simpa only [T, MvPolynomial.aeval_X] using hright i
  have hP : MvPolynomial.aeval θ P ≠ 0 := by
    simp only [P, map_mul, map_prod, map_sub, map_one, hT, mul_ne_zero_iff]
    refine ⟨⟨hU', Finset.prod_ne_zero_iff.mpr
      (fun i _ => mul_ne_zero (ht0 i) (sub_ne_zero.mpr (ht1 i)))⟩, ?_⟩
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hj).1 (ht he).symm)
  obtain ⟨z, hz, hzP⟩ := a2_complex_point_of_field_open I θ
    (fun f hf => RingHom.mem_ker.mp hf) P hP
  let x' : Point d := z ∘ left
  let t' : Fin n → ℂ := fun i => z (right i)
  have hzparts : MvPolynomial.eval x' U ≠ 0 ∧
      (∏ i, t' i * (t' i - 1)) ≠ 0 ∧
      (∏ i, ∏ j ∈ Finset.univ.erase i, (t' i - t' j)) ≠ 0 := by
    simpa only [P, U', T, x', t', map_mul, map_prod, map_sub, map_one,
      ← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_rename, MvPolynomial.aeval_X,
      mul_ne_zero_iff, and_assoc] using hzP
  have hx' : x' ∈ X.points := by
    intro f hf
    have hker : MvPolynomial.rename left f ∈ I := by
      apply RingHom.mem_ker.mpr
      simpa only [MvPolynomial.aeval_rename, hleft] using hx f hf
    simpa only [x', MvPolynomial.aeval_rename] using hz _ hker
  obtain ⟨hxy', hfinit, hcard⟩ := hcap x' hx' hzparts.1
  have ht' (i : Fin n) : t' i ≠ 0 ∧ t' i ≠ 1 := by
    have h := Finset.prod_ne_zero_iff.mp hzparts.2.1 i (Finset.mem_univ _)
    simpa only [mul_ne_zero_iff, sub_ne_zero] using h
  have hti : Function.Injective t' := by
    intro i j he
    by_contra hne
    have h := Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp hzparts.2.2 i (Finset.mem_univ _)) j
      (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩)
    exact h (sub_eq_zero.mpr he)
  let root : Fin n → Point d := fun i => y + t' i • (x'-y)
  have hmem (i : Fin n) : root i ∈ (AffineFamily.locus J).points := by
    obtain ⟨V, hV, hv⟩ := hroots i
    have hrV : root i ∈ V.points := by
      intro f hf
      let v : Fin d → Poly (d+n) := fun j =>
        MvPolynomial.C (y j) + T i * (MvPolynomial.X (left j) - MvPolynomial.C (y j))
      have hθv : (fun j => MvPolynomial.aeval θ (v j)) =
          (fun j => algebraMap ℂ K (y j) + t i * (x j - algebraMap ℂ K (y j))) := by
        funext j
        simp only [v, map_add, map_mul, map_sub, MvPolynomial.aeval_C,
          MvPolynomial.aeval_X, hT]
        rw [show θ (left j) = x j from congrFun hleft j]
      have hzv : (fun j => MvPolynomial.aeval z (v j)) = root i := by
        funext j
        simp [v, root, T, x', t', Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      have hker : MvPolynomial.aeval v f ∈ I := by
        apply RingHom.mem_ker.mpr
        rw [MvPolynomial.comp_aeval_apply, hθv]
        exact hv f hf
      have h := hz _ hker
      rw [MvPolynomial.comp_aeval_apply, hzv] at h
      exact h
    intro f hf
    exact hrV f (affineFamily_locus_ideal_le J V hV hf)
  have hrootinj : Function.Injective root := by
    intro i j hij
    apply hti
    apply smul_left_injective ℂ (sub_ne_zero.mpr hxy')
    exact add_left_cancel hij
  have hroots' (i : Fin n) : root i ∈ movingRoots x' y J := by
    refine ⟨hmem i, ?_, ?_, ?_⟩
    · refine ⟨1-t' i, ?_⟩
      ext j
      simp only [root, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · intro he
      have hs : t' i • (x'-y) = (1 : ℂ) • (x'-y) := by
        apply add_left_cancel (a := y)
        simpa only [one_smul, add_sub_cancel] using he
      exact (ht' i).2 (smul_left_injective ℂ (sub_ne_zero.mpr hxy') hs)
    · intro he
      have hs : t' i • (x'-y) = (0 : ℂ) • (x'-y) := by
        apply add_left_cancel (a := y)
        simpa only [zero_smul, add_zero] using he
      exact (ht' i).1 (smul_left_injective ℂ (sub_ne_zero.mpr hxy') hs)
  let f : Fin n → movingRoots x' y J := fun i => ⟨root i, hroots' i⟩
  have hf : Function.Injective f := fun i j he => hrootinj (congrArg Subtype.val he)
  letI : Fintype (movingRoots x' y J) := hfinit.fintype
  have hc := Fintype.card_le_of_injective f hf
  have he : Fintype.card (movingRoots x' y J) = (movingRoots x' y J).ncard :=
    Set.fintypeCard_eq_ncard _
  rw [Fintype.card_fin, he] at hc
  exact hc.trans hcard

/-- Domination preserves the supplied complex residue evaluation. -/
theorem a2_local_valuation_residue_model {R K : Type*}
    [CommRing R] [IsLocalRing R] [Field K] [Algebra ℂ R] [Algebra ℂ K]
    (ε : R →ₐ[ℂ] ℂ)
    (hε : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal R)
    (f : R →ₐ[ℂ] K) :
    ∃ (A : ValuationSubring K) (g : R →+* A),
      A.toSubring.subtype.comp g = f.toRingHom ∧ IsLocalHom g ∧
      ∀ r : R, IsLocalRing.residue A (g r) =
        IsLocalRing.residue A (g (algebraMap ℂ R (ε r))) := by
  obtain ⟨A, hA, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f.toRingHom
  let g : R →+* A := f.toRingHom.codRestrict A.toSubring hA
  letI : IsLocalHom g := hlocal
  refine ⟨A, g, rfl, hlocal, ?_⟩
  intro r
  have hr : r - algebraMap ℂ R (ε r) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hε]
    apply RingHom.mem_ker.mpr
    simp
  have hg : g (r - algebraMap ℂ R (ε r)) ∈ IsLocalRing.maximalIdeal A :=
    map_nonunit g _ hr
  have hzero : IsLocalRing.residue A (g (r - algebraMap ℂ R (ε r))) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hg
  simpa only [map_sub, sub_eq_zero] using hzero

/-- Localize a faithful generic field model at the supplied complex point
before taking a dominating valuation ring. No regularity of the point is used. -/
theorem a2_point_valuation_model_of_embedding {R K : Type*}
    [CommRing R] [Field K] [Algebra ℂ R] [Algebra ℂ K]
    (ε : R →ₐ[ℂ] ℂ) (f : R →ₐ[ℂ] K) (hf : Function.Injective f) :
    ∃ (A : ValuationSubring K) (g : R →+* A),
      A.toSubring.subtype.comp g = f.toRingHom ∧
      ∀ r : R, IsLocalRing.residue A (g r) =
        IsLocalRing.residue A (g (algebraMap ℂ R (ε r))) := by
  let P := RingHom.ker ε.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime ε.toRingHom
  let Rₚ := Localization.AtPrime P
  haveI : IsScalarTower ℂ R Rₚ := inferInstance
  have hεunit (s : P.primeCompl) : IsUnit (ε s) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact s.property (RingHom.mem_ker.mpr hz)
  have hfunit (s : P.primeCompl) : IsUnit (f s) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hs : (s : R) = 0 := hf (hz.trans (map_zero f).symm)
    exact s.property (hs ▸ Ideal.zero_mem P)
  let εₚ : Rₚ →ₐ[ℂ] ℂ := IsLocalization.liftAlgHom (M := P.primeCompl) (f := ε) hεunit
  let fₚ : Rₚ →ₐ[ℂ] K := IsLocalization.liftAlgHom (M := P.primeCompl) (f := f) hfunit
  have hεlift (r : R) : εₚ (algebraMap R Rₚ r) = ε r := by
    exact IsLocalization.lift_eq (S := Rₚ) hεunit r
  have hflift (r : R) : fₚ (algebraMap R Rₚ r) = f r := by
    exact IsLocalization.lift_eq (S := Rₚ) hfunit r
  have hεsurj : Function.Surjective εₚ := by
    intro c
    refine ⟨algebraMap R Rₚ (algebraMap ℂ R c), ?_⟩
    rw [hεlift, ε.commutes]
    rfl
  have hεker : RingHom.ker εₚ.toRingHom = IsLocalRing.maximalIdeal Rₚ :=
    IsLocalRing.ker_eq_maximalIdeal εₚ.toRingHom hεsurj
  obtain ⟨A, gₚ, hcomp, hlocal, hres⟩ := a2_local_valuation_residue_model εₚ hεker fₚ
  let g : R →+* A := gₚ.comp (algebraMap R Rₚ)
  refine ⟨A, g, ?_, ?_⟩
  · apply RingHom.ext
    intro r
    exact (RingHom.congr_fun hcomp (algebraMap R Rₚ r)).trans (hflift r)
  · intro r
    simpa only [g, RingHom.comp_apply, hεlift,
      IsScalarTower.algebraMap_apply ℂ R Rₚ] using hres (algebraMap R Rₚ r)

/-- Normalize a polynomial over a valuation ring, retaining an
explicit coefficient equal to one rather than only nonzero reduction. -/
theorem a2_valuation_primitive_polynomial {K σ : Type*} [Field K]
    (A : ValuationSubring K) (F : MvPolynomial σ K) (hF0 : F ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∃ H : MvPolynomial σ A,
      F = MvPolynomial.C c * MvPolynomial.map A.toSubring.subtype H ∧
      ∃ m, H.coeff m = 1 := by
  have hsupport : F.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun he => hF0 (MvPolynomial.support_eq_empty.mp he))
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image F.support
    (fun m => A.valuation (F.coeff m)) hsupport
  let c := F.coeff m
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hval (n : σ →₀ ℕ) : A.valuation (F.coeff n) ≤ A.valuation c := by
    by_cases hn : n ∈ F.support
    · exact hmax n hn
    · rw [MvPolynomial.notMem_support_iff.mp hn, map_zero]
      exact zero_le
  have hint (n : σ →₀ ℕ) : c⁻¹ * F.coeff n ∈ A := by
    obtain ⟨a, ha⟩ := (A.valuation_le_iff (F.coeff n) c).mp (hval n)
    have he : c⁻¹ * F.coeff n = (a : K) := by rw [← ha]; field_simp
    rw [he]
    exact a.property
  let P := MvPolynomial.C c⁻¹ * F
  have hrange : P ∈ Set.range (MvPolynomial.map A.toSubring.subtype) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro a ha
    obtain ⟨n, hn, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    refine ⟨⟨c⁻¹ * F.coeff n, hint n⟩, ?_⟩
    simp only [P, MvPolynomial.coeff_C_mul]
    rfl
  obtain ⟨H, hH⟩ := hrange
  have hcoeff : H.coeff m = 1 := by
    apply Subtype.ext
    have he := congrArg (fun P : MvPolynomial σ K => P.coeff m) hH
    simp only [MvPolynomial.coeff_map, P, MvPolynomial.coeff_C_mul] at he
    change (H.coeff m : K) = c⁻¹ * c at he
    exact he.trans ((inv_mul_cancel₀ hc).trans (map_one A.toSubring.subtype).symm)
  refine ⟨c, hc, H, ?_, m, hcoeff⟩
  rw [hH]
  simp only [P, ← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hc,
    MvPolynomial.C_1, one_mul]

/-- Primitive normalization preserves the degree of a homogeneous form. -/
theorem a2_valuation_primitive_form {K σ : Type*} [Field K]
    (A : ValuationSubring K) (F : MvPolynomial σ K) (g : ℕ)
    (hF : F.IsHomogeneous g) (hF0 : F ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∃ H : MvPolynomial σ A,
      F = MvPolynomial.C c * MvPolynomial.map A.toSubring.subtype H ∧
      H.IsHomogeneous g ∧ ∃ m, H.coeff m = 1 := by
  obtain ⟨c, hc, H, he, hu⟩ := a2_valuation_primitive_polynomial A F hF0
  refine ⟨c, hc, H, he, ?_, hu⟩
  apply MvPolynomial.IsHomogeneous.of_map (f := A.toSubring.subtype) Subtype.val_injective
  have hscaled : MvPolynomial.map A.toSubring.subtype H = MvPolynomial.C c⁻¹ * F := by
    rw [he, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hc, MvPolynomial.C_1, one_mul]
  rw [hscaled]
  exact hF.C_mul c⁻¹

/-- An explicit unit coefficient prevents a primitive model from
vanishing after reduction to any nontrivial residue ring. -/
theorem a2_primitive_map_nonzero {R S σ : Type*} [CommRing R] [CommRing S]
    [Nontrivial S] (φ : R →+* S) (H : MvPolynomial σ R)
    (hunit : ∃ m, H.coeff m = 1) : MvPolynomial.map φ H ≠ 0 := by
  obtain ⟨m, hm⟩ := hunit
  intro he
  have h := congrArg (fun P : MvPolynomial σ S => P.coeff m) he
  simp only [MvPolynomial.coeff_map, hm, map_one, MvPolynomial.coeff_zero] at h
  exact one_ne_zero h

/-- A primitive factor over a valuation ring has an integral quotient
whenever its product has integral coefficients. This is the content step
needed to reduce the actual generic divisor, including at singular centers. -/
theorem a2_valuation_primitive_dvd {K σ : Type*} [Field K]
    (A : ValuationSubring K) (H F : MvPolynomial σ A)
    (hH : ∃ m, H.coeff m = 1)
    (hdvd : MvPolynomial.map A.toSubring.subtype H ∣
      MvPolynomial.map A.toSubring.subtype F) : H ∣ F := by
  let ι := A.toSubring.subtype
  have hinj : Function.Injective (MvPolynomial.map (σ := σ) ι) :=
    MvPolynomial.map_injective ι Subtype.val_injective
  obtain ⟨Q, hQ⟩ := hdvd
  by_cases hQ0 : Q = 0
  · have hF : F = 0 := by
      apply hinj
      simpa only [hQ0, mul_zero, map_zero] using hQ
    rw [hF]
    exact dvd_zero _
  obtain ⟨c, hc, Q₀, he, hu⟩ := a2_valuation_primitive_polynomial A Q hQ0
  have hcA : c ∈ A := by
    by_contra hnot
    have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hnot
    let a : A := ⟨c⁻¹, hcinv⟩
    have ha : (a : K) ∈ A.nonunits := by
      apply A.mem_nonunits_iff_or.mpr
      right
      simpa only [a, inv_inv] using hnot
    have hazero : IsLocalRing.residue A a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr (A.coe_mem_nonunits_iff.mp ha)
    have hprod : MvPolynomial.C a * F = H * Q₀ := by
      apply hinj
      simp only [map_mul, MvPolynomial.map_C]
      rw [hQ, he]
      change MvPolynomial.C c⁻¹ *
        (MvPolynomial.map ι H * (MvPolynomial.C c * MvPolynomial.map ι Q₀)) = _
      calc
        _ = (MvPolynomial.C c⁻¹ * MvPolynomial.C c) *
            (MvPolynomial.map ι H * MvPolynomial.map ι Q₀) := by ring
        _ = _ := by rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hc, MvPolynomial.C_1, one_mul]
    have hz := congrArg (MvPolynomial.map (IsLocalRing.residue A)) hprod
    have hHnz := a2_primitive_map_nonzero (IsLocalRing.residue A) H hH
    have hQnz := a2_primitive_map_nonzero (IsLocalRing.residue A) Q₀ hu
    simp only [map_mul, MvPolynomial.map_C, hazero, MvPolynomial.C_0, zero_mul] at hz
    exact (mul_ne_zero hHnz hQnz) hz.symm
  refine ⟨MvPolynomial.C (⟨c, hcA⟩ : A) * Q₀, ?_⟩
  apply hinj
  simp only [map_mul, MvPolynomial.map_C]
  rw [hQ, he]
  rfl

/-- The primitive model represents the actual generic divisor, and
divides the original integral forms before reducing to the residue field. -/
theorem a2_valuation_common_divisor_model {K σ : Type*} [Field K]
    (A : ValuationSubring K) (F G : MvPolynomial σ A)
    (D : MvPolynomial σ K) (g : ℕ) (hD : D.IsHomogeneous g) (hD0 : D ≠ 0)
    (hDF : D ∣ MvPolynomial.map A.toSubring.subtype F)
    (hDG : D ∣ MvPolynomial.map A.toSubring.subtype G) :
    ∃ (c : K) (H : MvPolynomial σ A), c ≠ 0 ∧
      D = MvPolynomial.C c * MvPolynomial.map A.toSubring.subtype H ∧
      H.IsHomogeneous g ∧ (∃ m, H.coeff m = 1) ∧ H ∣ F ∧ H ∣ G := by
  obtain ⟨c, hc, H, he, hh, hu⟩ := a2_valuation_primitive_form A D g hD hD0
  have hd : MvPolynomial.map A.toSubring.subtype H ∣ D := by
    refine ⟨MvPolynomial.C c, ?_⟩
    rw [he]
    exact mul_comm _ _
  exact ⟨c, H, hc, he, hh, hu,
    a2_valuation_primitive_dvd A H F hu (hd.trans hDF),
    a2_valuation_primitive_dvd A H G hu (hd.trans hDG)⟩

/-- A field-valued point of the full path locus lies on one of its
original minimal components, before any retained-family restriction. -/
theorem a2_field_point_minimal_component {d : ℕ} {K : Type*}
    [Field K] [Algebra ℂ K] (I : Ideal (Poly d)) (x : Fin d → K)
    (hx : ∀ f ∈ I, MvPolynomial.aeval x f = 0) :
    ∃ W : AffineVariety d, W.IsComponentOf I ∧
      ∀ f ∈ W.ideal, MvPolynomial.aeval x f = 0 := by
  let P : Ideal (Poly d) := RingHom.ker (MvPolynomial.aeval x)
  letI : P.IsPrime := RingHom.ker_isPrime (MvPolynomial.aeval x)
  have hIP : I ≤ P := fun f hf => RingHom.mem_ker.mpr (hx f hf)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hIP
  exact ⟨⟨Q, hQ.isPrime.isRadical⟩, hQ,
    fun f hf => RingHom.mem_ker.mp (hQP hf)⟩

/-- A field branch whose coordinates have an integral model stays on
its original component at the supplied literal complex specialization. -/
theorem a2_component_specializes {d : ℕ} {A K k : Type*}
    [CommRing A] [Field K] [Field k]
    [Algebra ℂ A] [Algebra ℂ K] [Algebra ℂ k]
    (ι : A →ₐ[ℂ] K) (hι : Function.Injective ι) (res : A →ₐ[ℂ] k)
    (v : Fin d → A) (p : Point d)
    (hp : ∀ i, res (v i) = algebraMap ℂ k (p i))
    (W : AffineVariety d)
    (hv : ∀ f ∈ W.ideal, MvPolynomial.aeval (fun i => ι (v i)) f = 0) :
    p ∈ W.points := by
  intro f hf
  have hzero : MvPolynomial.aeval v f = 0 := by
    apply hι
    rw [map_zero, MvPolynomial.comp_aeval_apply]
    exact hv f hf
  have hres := congrArg res hzero
  rw [map_zero, MvPolynomial.comp_aeval_apply] at hres
  have hcoords : (fun i => res (v i)) = (fun i => algebraMap ℂ k (p i)) := funext hp
  rw [hcoords] at hres
  have hmap := MvPolynomial.comp_aeval_apply (f := p) (Algebra.ofId ℂ k) f
  have heval : algebraMap ℂ k (MvPolynomial.eval p f) = 0 := by
    simpa only [MvPolynomial.aeval_eq_eval, Algebra.ofId_apply] using hmap.trans hres
  exact RingHom.injective (algebraMap ℂ k) (heval.trans (map_zero _).symm)

/-- The minor definition of generic rank agrees with rank over the actual
fraction field of an integral carrier. -/
theorem a2_genericMatrixRank_of_fraction_rank {d a b : ℕ}
    (X : AffineVariety d) (hX : X.IsIrreducible)
    (A : Matrix (Fin a) (Fin b) (Poly d)) (r : ℕ) :
    letI : X.ideal.IsPrime := hX
    let K := FractionRing (Poly d ⧸ X.ideal)
    let η : Poly d →+* K :=
      (algebraMap (Poly d ⧸ X.ideal) K).comp (Ideal.Quotient.mk X.ideal)
    (A.map η).rank = r → GenericMatrixRank X A r := by
  letI : X.ideal.IsPrime := hX
  let R := Poly d ⧸ X.ideal
  let K := FractionRing R
  let η : Poly d →+* K := (algebraMap R K).comp (Ideal.Quotient.mk X.ideal)
  change (A.map η).rank = r → GenericMatrixRank X A r
  intro hr
  have hzero (f : Poly d) : η f = 0 ↔ f ∈ X.ideal := by
    change algebraMap R K (Ideal.Quotient.mk X.ideal f) = 0 ↔ _
    rw [map_eq_zero_iff (algebraMap R K) (IsFractionRing.injective R K),
      Ideal.Quotient.eq_zero_iff_mem]
  have hdet {s : ℕ} (rows : Fin s ↪ Fin a) (cols : Fin s ↪ Fin b) :
      η (A.submatrix rows cols).det = ((A.map η).submatrix rows cols).det := by
    rw [RingHom.map_det]
    rfl
  constructor
  · intro rows cols
    apply (hzero _).mp
    rw [hdet]
    by_contra hn
    have hs := Matrix.rank_submatrix_le (A.map η) rows cols
    rw [Matrix.rank_of_det_ne_zero hn, Fintype.card_fin, hr] at hs
    omega
  · obtain ⟨rows, cols, hn⟩ := regularity_matrix_le_rank_minor (A.map η) (le_of_eq hr.symm)
    refine ⟨rows, cols, ?_⟩
    intro hm
    exact hn ((hdet rows cols).symm.trans ((hzero _).mpr hm))

/-- A Sylvester entry is either zero or a coefficient of one of its forms,
so coefficient degree bounds are preserved without a determinant estimate. -/
theorem a2_sylvester_entry_degree {d : ℕ} (L : ℕ) (F G : BinaryForm d)
    (hF : ∀ m, (F.coeff m).totalDegree ≤ L)
    (hG : ∀ m, (G.coeff m).totalDegree ≤ L) :
    ∀ i j, (sylvesterMatrix L F G i j).totalDegree ≤ L := by
  intro i j
  simp only [sylvesterMatrix, binaryCoeff]
  split_ifs <;> first | exact hF _ | exact hG _ | simp

/-- The frozen Sylvester identity is passed explicitly so the numerical
assembly records that node as upstream, independently of its current proof. -/
def A2SylvesterRank : Prop :=
  ∀ (K : Type) [Field K] (L : ℕ), 1 ≤ L →
    ∀ f g : MvPolynomial (Fin 2) K, f.IsHomogeneous L → g.IsHomogeneous L →
      (f ≠ 0 ∨ g ≠ 0) →
        Matrix.rank (sylvesterMatrix L f g) = 2 * L - (binaryGcd f g).totalDegree

/-- The numerical endpoint of the paper's root-support argument. It also
covers either one zero form or two zero forms at the actual center. -/
theorem a2_sylvester_rank_loss (hsylvester : A2SylvesterRank)
    {d : ℕ} (X : AffineVariety d)
    (hX : X.IsIrreducible) (F G : BinaryForm d) (L r : ℕ)
    (hL : 1 ≤ L)
    (hF : F.IsHomogeneous L) (hG : G.IsHomogeneous L)
    (p : Point d)
    (hgap : genericGcdDegree X hX F G + r / 2 ≤
      (binaryGcd (specializeBinary F p) (specializeBinary G p)).totalDegree ∨
      specializeBinary F p = 0 ∧ specializeBinary G p = 0) :
    (sylvesterMatrix L (specializeBinary F p) (specializeBinary G p)).rank ≤
      (2 * L - genericGcdDegree X hX F G) - r / 2 := by
  letI : X.ideal.IsPrime := hX
  let R := Poly d ⧸ X.ideal
  let K := FractionRing R
  let η : Poly d →+* K := (algebraMap R K).comp (Ideal.Quotient.mk X.ideal)
  have hgle : genericGcdDegree X hX F G ≤ L :=
    binary_gcd_degree_le (MvPolynomial.map η F) (MvPolynomial.map η G) L
      (hF.map η) (hG.map η)
  by_cases hz : specializeBinary F p = 0 ∧ specializeBinary G p = 0
  · have hm : sylvesterMatrix L (specializeBinary F p) (specializeBinary G p) = 0 := by
      ext i j
      simp [sylvesterMatrix, binaryCoeff, hz.1, hz.2]
    rw [hm, Matrix.rank_zero]
    exact Nat.zero_le _
  · have hgcd := hgap.resolve_right hz
    have hnonzero : specializeBinary F p ≠ 0 ∨ specializeBinary G p ≠ 0 := by tauto
    have hrank := hsylvester ℂ L hL (specializeBinary F p) (specializeBinary G p)
      (hF.map (MvPolynomial.eval p)) (hG.map (MvPolynomial.eval p)) hnonzero
    rw [hrank]
    omega

/-- Once the geometric root-support comparison has produced two forms,
all remaining requirements of the frozen matrix conclusion follow here. -/
theorem a2_rank_loss_of_binary_forms (hsylvester : A2SylvesterRank)
    {d : ℕ} (X : AffineVariety d)
    (hX : X.IsIrreducible) (J : AffineFamily.Family d) (Y : AffineVariety d)
    (L r : ℕ) (hL : 1 ≤ L) (S : Finset (Point d))
    (F G : BinaryForm d) (hF : F.IsHomogeneous L) (hG : G.IsHomogeneous L)
    (hFdegree : ∀ m, (F.coeff m).totalDegree ≤ L)
    (hGdegree : ∀ m, (G.coeff m).totalDegree ≤ L)
    (hnonzero : ∃ p ∈ X.points, specializeBinary F p ≠ 0 ∨ specializeBinary G p ≠ 0)
    (hgap : ∀ p ∈ S, r < groupDepth p J Y →
      genericGcdDegree X hX F G + r / 2 ≤
        (binaryGcd (specializeBinary F p) (specializeBinary G p)).totalDegree ∨
        specializeBinary F p = 0 ∧ specializeBinary G p = 0) :
    ∃ (A : Matrix (Fin (2*L)) (Fin (2*L)) (Poly d)) (ρ : ℕ),
      L ≤ ρ ∧ ρ ≤ 2*L ∧ (∀ i j, (A i j).totalDegree ≤ L) ∧ GenericMatrixRank X A ρ ∧
      ∀ p ∈ S, r < groupDepth p J Y →
        Matrix.rank (fun i j => MvPolynomial.eval p (A i j)) ≤ ρ-r/2 := by
  letI : X.ideal.IsPrime := hX
  let R := Poly d ⧸ X.ideal
  let K := FractionRing R
  let η : Poly d →+* K := (algebraMap R K).comp (Ideal.Quotient.mk X.ideal)
  let f := MvPolynomial.map η F
  let g := MvPolynomial.map η G
  have hfg : f ≠ 0 ∨ g ≠ 0 := by
    obtain ⟨p, hp, hf | hg⟩ := hnonzero
    · exact Or.inl (fun hz => hf (generic_binary_zero_specializes X hX F p hp hz))
    · exact Or.inr (fun hz => hg (generic_binary_zero_specializes X hX G p hp hz))
  let A := sylvesterMatrix L F G
  let ρ := 2 * L - genericGcdDegree X hX F G
  have hgle : genericGcdDegree X hX F G ≤ L :=
    binary_gcd_degree_le f g L (hF.map η) (hG.map η)
  have hrank : (A.map η).rank = ρ := by
    rw [sylvesterMatrix_map]
    exact hsylvester K L hL f g (hF.map η) (hG.map η) hfg
  refine ⟨A, ρ, by dsimp [ρ]; omega, Nat.sub_le _ _,
    a2_sylvester_entry_degree L F G hFdegree hGdegree,
    a2_genericMatrixRank_of_fraction_rank X hX A ρ hrank, ?_⟩
  intro p hp hdepth
  have hr := a2_sylvester_rank_loss hsylvester X hX F G L r hL hF hG p (hgap p hp hdepth)
  have hm : (fun i j => MvPolynomial.eval p (A i j)) =
      sylvesterMatrix L (specializeBinary F p) (specializeBinary G p) :=
    sylvesterMatrix_map (MvPolynomial.eval p) L F G
  rwa [hm]

/-- Fix the target coordinate tuple of the generic pair open. -/
def a2_productRight {d : ℕ} (y : Point d) (H : Poly (d+d)) : Poly d :=
  MvPolynomial.aeval (Fin.append MvPolynomial.X (fun i => MvPolynomial.C (y i))) H

theorem a2_productRight_eval {d : ℕ} (x y : Point d) (H : Poly (d+d)) :
    MvPolynomial.eval x (a2_productRight y H) =
      MvPolynomial.eval (Fin.append x y) H := by
  change (MvPolynomial.aeval x).comp
    (MvPolynomial.aeval (Fin.append MvPolynomial.X (fun i => MvPolynomial.C (y i)))) H =
      MvPolynomial.aeval (Fin.append x y) H
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append, Fin.addCases, j.isLt]
  · simp [Fin.append, Fin.addCases]

def a2_lineCoefficient {d : ℕ} (y : Point d) (f : Poly d) (j : ℕ) : Poly d :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (y i))
    (MvPolynomial.homogeneousComponent j (OAI.PiExponent.WeightedBezout.translationEquiv y f))

/-- Degree-L restriction to `[U:Uy+V(x-y)]`. Lower-degree equations are
padded by powers of U, so their added projective roots stay at infinity. -/
def a2_lineForm {d : ℕ} (y : Point d) (f : Poly d) (L : ℕ) : BinaryForm d :=
  ∑ j ∈ Finset.range (L+1), MvPolynomial.monomial
    (Finsupp.single 0 (L-j) + Finsupp.single 1 j) (a2_lineCoefficient y f j)

theorem a2_lineCoefficient_degree {d : ℕ} (y : Point d) (f : Poly d) (j : ℕ) :
    (a2_lineCoefficient y f j).totalDegree ≤ j := by
  have hx (i : Fin d) : (MvPolynomial.X i - MvPolynomial.C (y i) : Poly d).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  have hd := OAI.PiExponent.WeightedBezout.totalDegree_aeval_le_weighted
    (1 : Fin d → ℕ) (fun i => MvPolynomial.X i - MvPolynomial.C (y i)) hx
    (MvPolynomial.homogeneousComponent j (OAI.PiExponent.WeightedBezout.translationEquiv y f))
  rw [MvPolynomial.weightedTotalDegree_one] at hd
  exact hd.trans (MvPolynomial.homogeneousComponent_isHomogeneous _ _).totalDegree_le

theorem a2_lineForm_homogeneous {d : ℕ} (y : Point d) (f : Poly d) (L : ℕ) :
    (a2_lineForm y f L).IsHomogeneous L := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
  exact Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem a2_lineForm_coefficient_degree {d : ℕ} (y : Point d) (f : Poly d) (L : ℕ)
    (m : Fin 2 →₀ ℕ) : ((a2_lineForm y f L).coeff m).totalDegree ≤ L := by
  simp only [a2_lineForm, MvPolynomial.coeff_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  simp only [MvPolynomial.coeff_monomial]
  split_ifs
  · exact (a2_lineCoefficient_degree y f j).trans
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  · simp

theorem a2_lineCoefficient_eval {d : ℕ} (y x : Point d) (f : Poly d) (j : ℕ) :
    MvPolynomial.eval x (a2_lineCoefficient y f j) =
      MvPolynomial.eval (x-y)
        (MvPolynomial.homogeneousComponent j (OAI.PiExponent.WeightedBezout.translationEquiv y f)) := by
  rw [a2_lineCoefficient, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
  simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  rfl

theorem a2_lineForm_eval_affine {d : ℕ} (y x : Point d) (f : Poly d) (L : ℕ)
    (hf : f.totalDegree ≤ L) (t : ℂ) :
    MvPolynomial.eval ![1,t] (specializeBinary (a2_lineForm y f L) x) =
      MvPolynomial.eval (y + t • (x-y)) f := by
  let T := OAI.PiExponent.WeightedBezout.translationEquiv y f
  have hd : T.totalDegree ≤ L := (separator_translation_degree y f).trans hf
  have he : (∑ j ∈ Finset.range (L+1), MvPolynomial.homogeneousComponent j T) = T := by
    calc
      _ = ∑ j ∈ Finset.range (T.totalDegree+1), MvPolynomial.homogeneousComponent j T := ?_
      _ = T := MvPolynomial.sum_homogeneousComponent T
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hj'
    exact MvPolynomial.homogeneousComponent_eq_zero (n := j) (φ := T) (by
      have hjn := Finset.mem_range.mp hj
      have hjn' : ¬ j < T.totalDegree+1 := by simpa only [Finset.mem_range] using hj'
      omega)
  rw [← separator_translation_eval y (t • (x-y)) f]
  change _ = MvPolynomial.eval (t • (x-y)) T
  rw [← he]
  simp only [a2_lineForm, specializeBinary, map_sum, MvPolynomial.map_monomial,
    MvPolynomial.eval_monomial, a2_lineCoefficient_eval]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Bridges.homogeneous_eval_smul _ (MvPolynomial.homogeneousComponent_isHomogeneous j T)]
  simp [T, mul_comm]

theorem a2_lineCoefficient_aeval {d : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (y : Point d) (x : Fin d → R) (f : Poly d) (j : ℕ) :
    MvPolynomial.aeval x (a2_lineCoefficient y f j) =
      MvPolynomial.aeval (fun i => x i - algebraMap ℂ R (y i))
        (MvPolynomial.homogeneousComponent j (OAI.PiExponent.WeightedBezout.translationEquiv y f)) := by
  rw [a2_lineCoefficient, MvPolynomial.comp_aeval_apply]
  simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]

theorem a2_translation_aeval {d : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (y : Point d) (x : Fin d → R) (f : Poly d) :
    MvPolynomial.aeval x (OAI.PiExponent.WeightedBezout.translationEquiv y f) =
      MvPolynomial.aeval (fun i => algebraMap ℂ R (y i) + x i) f := by
  have he : (MvPolynomial.aeval x).comp
      (OAI.PiExponent.WeightedBezout.translationEquiv y).toAlgHom =
      MvPolynomial.aeval (fun i => algebraMap ℂ R (y i) + x i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [OAI.PiExponent.WeightedBezout.translationEquiv,
      OAI.PiExponent.WeightedBezout.translation]
  exact AlgHom.congr_fun he f

theorem a2_lineForm_eval₂_affine {d : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (y : Point d) (x : Fin d → R) (f : Poly d) (L : ℕ)
    (hf : f.totalDegree ≤ L) (t : R) :
    MvPolynomial.eval₂ (MvPolynomial.aeval x).toRingHom ![1,t] (a2_lineForm y f L) =
      MvPolynomial.aeval (fun i => algebraMap ℂ R (y i) +
        t * (x i - algebraMap ℂ R (y i))) f := by
  let T := OAI.PiExponent.WeightedBezout.translationEquiv y f
  have hd : T.totalDegree ≤ L := (separator_translation_degree y f).trans hf
  have he : (∑ j ∈ Finset.range (L+1), MvPolynomial.homogeneousComponent j T) = T := by
    calc
      _ = ∑ j ∈ Finset.range (T.totalDegree+1), MvPolynomial.homogeneousComponent j T := ?_
      _ = T := MvPolynomial.sum_homogeneousComponent T
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hj'
    exact MvPolynomial.homogeneousComponent_eq_zero (n := j) (φ := T) (by
      have hjn' : ¬ j < T.totalDegree+1 := by simpa only [Finset.mem_range] using hj'
      omega)
  rw [← a2_translation_aeval y (fun i => t * (x i - algebraMap ℂ R (y i))) f]
  change _ = MvPolynomial.aeval (fun i => t * (x i - algebraMap ℂ R (y i))) T
  rw [← he]
  simp only [a2_lineForm, map_sum, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro j hj
  rw [homogeneous_aeval_scale _ (MvPolynomial.homogeneousComponent_isHomogeneous j T)]
  simp [T, mul_comm, a2_lineCoefficient_aeval]

theorem a2_lineForm_span_properties {d : ℕ} (y : Point d) (E : Set (Poly d))
    (L : ℕ) (F : BinaryForm d)
    (hF : F ∈ Submodule.span ℂ ((fun f => a2_lineForm y f L) '' E)) :
    F.IsHomogeneous L ∧ ∀ m, (F.coeff m).totalDegree ≤ L := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, hf, rfl⟩ := hF
    exact ⟨a2_lineForm_homogeneous y f L, a2_lineForm_coefficient_degree y f L⟩
  | zero =>
    exact ⟨MvPolynomial.isHomogeneous_zero (Fin 2) (Poly d) L, fun m => by simp⟩
  | add F G _ _ hF hG =>
    refine ⟨hF.1.add hG.1, fun m => ?_⟩
    rw [MvPolynomial.coeff_add]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hF.2 m) (hG.2 m))
  | smul c F _ hF =>
    refine ⟨?_, fun m => ?_⟩
    · exact ((MvPolynomial.homogeneousSubmodule (Fin 2) (Poly d) L).restrictScalars ℂ).smul_mem c hF.1
    · rw [MvPolynomial.coeff_smul]
      exact (MvPolynomial.totalDegree_smul_le c _).trans (hF.2 m)

theorem a2_lineForm_span_root {d : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (y : Point d) (E : Set (Poly d)) (L : ℕ)
    (hE : ∀ f ∈ E, f.totalDegree ≤ L) (F : BinaryForm d)
    (hF : F ∈ Submodule.span ℂ ((fun f => a2_lineForm y f L) '' E))
    (x : Fin d → R) (t : R)
    (hroot : ∀ f ∈ E, MvPolynomial.aeval
      (fun i => algebraMap ℂ R (y i) + t * (x i - algebraMap ℂ R (y i))) f = 0) :
    MvPolynomial.eval₂ (MvPolynomial.aeval x).toRingHom ![1,t] F = 0 := by
  let ε : BinaryForm d →+* R := MvPolynomial.eval₂Hom (MvPolynomial.aeval x).toRingHom ![1,t]
  change ε F = 0
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, hf, rfl⟩ := hF
    exact (a2_lineForm_eval₂_affine y x f L (hE f hf) t).trans (hroot f hf)
  | zero => exact map_zero ε
  | add F G _ _ hF hG => simp only [map_add, hF, hG, add_zero]
  | smul c F _ hF =>
    rw [Algebra.smul_def, map_mul, hF, mul_zero]


/-- Finite prime-factor avoidance permits constant complex coefficients
even when the forms themselves are defined over a larger field. -/
theorem a2_coprime_constant_combination {R ι : Type*}
    [CommRing R] [IsDomain R] [Algebra ℂ R] [UniqueFactorizationMonoid R]
    [NormalizedGCDMonoid R] (s : Finset ι) (f : ι → R)
    (hgcd : s.gcd f = 1) (a : ι) (_ha : a ∈ s) (hf : f a ≠ 0) :
    ∃ c : s → ℂ, IsRelPrime (f a) (∑ i : s, c i • f i.val) := by
  let T : (s → ℂ) →ₗ[ℂ] R := ∑ i : s, (LinearMap.proj i).smulRight (f i.val)
  have hT (c : s → ℂ) : T c = ∑ i : s, c i • f i.val := by
    simp [T]
  let P := {p : R // p ∈ (normalizedFactors (f a)).toFinset}
  let N (p : P) : Submodule ℂ (s → ℂ) :=
    Submodule.comap T ((Ideal.span {p.val}).restrictScalars ℂ)
  have hproper (p : P) : N p ≠ ⊤ := by
    have hp := irreducible_of_normalized_factor p.val (Multiset.mem_toFinset.mp p.property)
    have hex : ∃ i ∈ s, ¬ p.val ∣ f i := by
      by_contra hn
      push Not at hn
      have hd := Finset.dvd_gcd (s := s) hn
      rw [hgcd] at hd
      exact hp.not_isUnit (isUnit_of_dvd_one hd)
    obtain ⟨i, hi, hpi⟩ := hex
    intro he
    have hm : Pi.single (⟨i, hi⟩ : s) (1 : ℂ) ∈ N p := he ▸ Submodule.mem_top
    change T (Pi.single (⟨i, hi⟩ : s) (1 : ℂ)) ∈ Ideal.span {p.val} at hm
    rw [hT] at hm
    have heval : (∑ j : s, (Pi.single (⟨i, hi⟩ : s) (1 : ℂ) : s → ℂ) j • f j.val) = f i := by
      simp [Pi.single_apply]
    rw [heval, Ideal.mem_span_singleton] at hm
    exact hpi hm
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top N hproper
  refine ⟨c, WfDvdMonoid.isRelPrime_of_no_irreducible_factors (by tauto) ?_⟩
  intro z hz hza hzb
  obtain ⟨p, hp, hzp⟩ := exists_mem_normalizedFactors_of_dvd hf hz hza
  apply hc ⟨p, Multiset.mem_toFinset.mpr hp⟩
  change T c ∈ Ideal.span {p}
  rw [hT, Ideal.mem_span_singleton]
  exact hzp.symm.dvd.trans hzb

theorem a2_two_constant_combinations_full_gcd {R ι : Type*}
    [CommRing R] [IsDomain R] [Algebra ℂ R] [UniqueFactorizationMonoid R]
    [NormalizedGCDMonoid R] (s : Finset ι) (f : ι → R)
    (a : ι) (ha : a ∈ s) (hf : f a ≠ 0) :
    ∃ c : s → ℂ, Associated (gcd (f a) (∑ i : s, c i • f i.val)) (s.gcd f) := by
  obtain ⟨u, hu, hgcd⟩ := s.extract_gcd f ⟨a, ha⟩
  have hua : u a ≠ 0 := fun hz => hf (by rw [hu a ha, hz, mul_zero])
  obtain ⟨c, hc⟩ := a2_coprime_constant_combination s u hgcd a ha hua
  have hsum : (∑ i : s, c i • f i.val) = s.gcd f * ∑ i : s, c i • u i.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hu i.val i.property]
    simp only [Algebra.smul_def]
    ring
  refine ⟨c, ?_⟩
  rw [hu a ha, hsum]
  have huunit : Associated (gcd (u a) (∑ i : s, c i • u i.val)) 1 :=
    associated_one_iff_isUnit.mpr (gcd_isUnit_iff_isRelPrime.mpr hc)
  exact (gcd_mul_left' _ _ _).trans (by simpa using huunit.mul_left (s.gcd f))

/-- Keep the common divisors of an arbitrary full system with finitely
many of its original equations. -/
theorem a2_finite_divisor_subsystem {R : Type*} [CommRing R] [IsNoetherianRing R]
    (E : Set R) :
    ∃ s : Finset R, (↑s : Set R) ⊆ E ∧
      ∀ D : R, (∀ f ∈ s, D ∣ f) ↔ ∀ f ∈ E, D ∣ f := by
  have hfg : (Ideal.span E).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := R) E).mp hfg
  refine ⟨s, hs, fun D => ⟨?_, ?_⟩⟩
  · intro hd f hf
    have hle : Ideal.span (↑s : Set R) ≤ Ideal.span {D} :=
      Ideal.span_le.mpr (fun g hg => Ideal.mem_span_singleton.mpr (hd g hg))
    have hspanI : Ideal.span E = Ideal.span (↑s : Set R) := hspan
    rw [← hspanI] at hle
    exact Ideal.mem_span_singleton.mp (hle (Ideal.subset_span hf))
  · intro hd f hf
    exact hd f (hs hf)

theorem a2_constant_combination_full_system_gcd {R : Type*}
    [CommRing R] [IsDomain R] [Algebra ℂ R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] [NormalizedGCDMonoid R]
    (E : Set R) (F : R) (hF : F ∈ E) (hF0 : F ≠ 0) :
    ∃ G ∈ Submodule.span ℂ E,
      ∀ D : R, D ∣ gcd F G ↔ ∀ f ∈ E, D ∣ f := by
  obtain ⟨s₀, hs₀, hdiv⟩ := a2_finite_divisor_subsystem E
  let s := insert F s₀
  have hs : (↑s : Set R) ⊆ E := by
    intro f hf
    rcases Finset.mem_insert.mp hf with he | hf
    · exact he ▸ hF
    · exact hs₀ hf
  obtain ⟨c, hc⟩ := a2_two_constant_combinations_full_gcd s id F
    (Finset.mem_insert_self _ _) hF0
  simp only [id_eq] at hc
  refine ⟨∑ i : s, c i • i.val, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hs i.property))
  · intro D
    rw [hc.dvd_iff_dvd_right, Finset.dvd_gcd_iff]
    constructor
    · intro hd
      apply (hdiv D).mp
      intro f hf
      exact hd f (Finset.mem_insert_of_mem hf)
    · intro hd f hf
      exact hd f (hs hf)


/-- A full-system line through a target point belonging only to Y would
lie in Y and violate the finite retained moving-root bound. -/
theorem a2_full_line_nonzero {d : ℕ} (E : Set (Poly d))
    (J : AffineFamily.Family d) (Y : AffineVariety d) (hY : Y ∈ J)
    (y x : Point d) (_hy : y ∈ Y.points) (hxy : x ≠ y)
    (hunique : ∀ W : AffineVariety d, W.IsComponentOf (Ideal.span E) →
      y ∈ W.points → W = Y)
    (hfinite : (movingRoots x y J).Finite) :
    ∃ f ∈ E, ∃ t : ℂ, MvPolynomial.eval (y + t • (x-y)) f ≠ 0 := by
  by_contra hn
  push Not at hn
  let v : Fin d → Polynomial ℂ := fun i =>
    Polynomial.C (y i) + Polynomial.X * Polynomial.C (x i - y i)
  let θ : Poly d →ₐ[ℂ] Polynomial ℂ := MvPolynomial.aeval v
  have heval (f : Poly d) (t : ℂ) :
      (θ f).eval t = MvPolynomial.eval (y + t • (x-y)) f := by
    change (θ f).eval t = MvPolynomial.eval (fun i => y i + t * (x i - y i)) f
    have h := MvPolynomial.comp_aeval_apply (f := v) (Polynomial.aeval t) f
    simpa [θ, v, Polynomial.aeval_def, MvPolynomial.aeval_eq_eval,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  let P : Ideal (Poly d) := RingHom.ker θ.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime θ.toRingHom
  have hEP : Ideal.span E ≤ P := by
    apply Ideal.span_le.mpr
    intro f hf
    apply RingHom.mem_ker.mpr
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hall : {t : ℂ | (θ f).IsRoot t} = Set.univ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Polynomial.IsRoot, heval]
      exact hn f hf t
    change {t : ℂ | (θ f).IsRoot t}.Infinite
    rw [hall]
    exact Set.infinite_univ
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hEP
  let W : AffineVariety d := ⟨Q, hQ.isPrime.isRadical⟩
  have hline (t : ℂ) : y + t • (x-y) ∈ W.points := by
    intro f hf
    have hz : θ f = 0 := RingHom.mem_ker.mp (hQP hf)
    rw [MvPolynomial.aeval_eq_eval, ← heval, hz, Polynomial.eval_zero]
  have hyeq : W = Y := hunique W hQ (by simpa using hline 0)
  have hlinY (t : ℂ) : y + t • (x-y) ∈ Y.points := hyeq ▸ hline t
  let root : ℂ → Point d := fun t => y + t • (x-y)
  have hinj : Function.Injective root := by
    intro a b he
    exact smul_left_injective ℂ (sub_ne_zero.mpr hxy) (add_left_cancel he)
  have hpre : (root ⁻¹' movingRoots x y J).Finite :=
    hfinite.preimage (hinj.injOn)
  have hsubset : (Set.univ \ ({0,1} : Set ℂ)) ⊆ root ⁻¹' movingRoots x y J := by
    intro t ht
    have ht0 : t ≠ 0 := fun he => ht.2 (by simp [he])
    have ht1 : t ≠ 1 := fun he => ht.2 (by simp [he])
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro f hf
      exact hlinY t f (affineFamily_locus_ideal_le J Y hY hf)
    · refine ⟨1-t, ?_⟩
      ext i
      simp only [root, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · intro he
      have hr1 : root 1 = x := by simp [root]
      exact ht1 (hinj (he.trans hr1.symm))
    · intro he
      have hr0 : root 0 = y := by simp [root]
      exact ht0 (hinj (he.trans hr0.symm))
  exact (Set.infinite_univ.sdiff (Set.toFinite ({0,1} : Set ℂ))) (hpre.subset hsubset)


/-- Lift the two constant combinations back to ambient binary forms,
preserving degree bounds and the full-system generic gcd property. -/
theorem a2_two_line_forms_full_gcd {d : ℕ} {K : Type*} [Field K] [Algebra ℂ K]
    (η : Poly d →ₐ[ℂ] K) (y : Point d) (E : Set (Poly d)) (L : ℕ)
    (hnonzero : ∃ f ∈ E, MvPolynomial.map η.toRingHom (a2_lineForm y f L) ≠ 0) :
    ∃ F G : BinaryForm d,
      F ∈ Submodule.span ℂ ((fun f => a2_lineForm y f L) '' E) ∧
      G ∈ Submodule.span ℂ ((fun f => a2_lineForm y f L) '' E) ∧
      F.IsHomogeneous L ∧ G.IsHomogeneous L ∧
      (∀ m, (F.coeff m).totalDegree ≤ L) ∧ (∀ m, (G.coeff m).totalDegree ≤ L) ∧
      MvPolynomial.map η.toRingHom F ≠ 0 ∧
      ∀ D : MvPolynomial (Fin 2) K,
        D ∣ binaryGcd (MvPolynomial.map η.toRingHom F) (MvPolynomial.map η.toRingHom G) ↔
          ∀ f ∈ E, D ∣ MvPolynomial.map η.toRingHom (a2_lineForm y f L) := by
  letI : NormalizedGCDMonoid (MvPolynomial (Fin 2) K) := Classical.arbitrary _
  let T := (fun f => a2_lineForm y f L) '' E
  let φ : BinaryForm d →ₐ[ℂ] MvPolynomial (Fin 2) K := MvPolynomial.mapAlgHom η
  obtain ⟨f, hf, hf0⟩ := hnonzero
  let F := a2_lineForm y f L
  have hFT : F ∈ T := ⟨f, hf, rfl⟩
  have hFspan : F ∈ Submodule.span ℂ T := Submodule.subset_span hFT
  obtain ⟨G₀, hG₀, hdiv⟩ := a2_constant_combination_full_system_gcd
    (φ '' T) (φ F) ⟨F, hFT, rfl⟩ hf0
  have hGmap : G₀ ∈ (Submodule.span ℂ T).map φ.toLinearMap := by
    rw [Submodule.map_span]
    exact hG₀
  obtain ⟨G, hG, heG⟩ := Submodule.mem_map.mp hGmap
  obtain ⟨hhF, hdF⟩ := a2_lineForm_span_properties y E L F hFspan
  obtain ⟨hhG, hdG⟩ := a2_lineForm_span_properties y E L G hG
  refine ⟨F, G, hFspan, hG, hhF, hhG, hdF, hdG, hf0, ?_⟩
  intro D
  change D ∣ gcd (φ F) (φ G) ↔ _
  change φ G = G₀ at heG
  rw [heG, hdiv]
  constructor
  · intro hd f hf
    exact hd (φ (a2_lineForm y f L)) ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  · intro hd z hz
    obtain ⟨H, hH, rfl⟩ := hz
    obtain ⟨f, hf, rfl⟩ := hH
    exact hd f hf



/-- The full generic binary pair and the actual distinguished fibers
share one target point, while the principal source open keeps the list cap. -/
theorem a2_full_system_binary_forms {d l : ℕ}
    (X : AffineVariety d) (hX : X.IsIrreducible) (J : AffineFamily.Family d)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l)
    (Y : AffineVariety d) (hY : Y ∈ J) (E : Set (Poly d)) (L q : ℕ)
    (hE : ∀ f ∈ E, f.totalDegree ≤ L)
    (hcomponents : ∀ V ∈ J, V.IsComponentOf (Ideal.span E))
    (hgeneric : GenericMovingRootBound X Y J q) (S : Finset (Point d))
    (hSnon : S.Nonempty) (himage : ∀ p ∈ S, (radialImage p Y).dimension = l) :
    letI : X.ideal.IsPrime := hX
    let K := FractionRing (Poly d ⧸ X.ideal)
    let η : Poly d →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ (Poly d ⧸ X.ideal) K).comp
      (Ideal.Quotient.mkₐ ℂ X.ideal)
    ∃ (y : Point d) (U : Poly d) (F G : BinaryForm d),
      y ∈ Y.points ∧ U ∉ X.ideal ∧
      (∀ x ∈ X.points, MvPolynomial.eval x U ≠ 0 →
        x ≠ y ∧ (movingRoots x y J).Finite ∧ (movingRoots x y J).ncard ≤ q) ∧
      F ∈ Submodule.span ℂ ((fun f => a2_lineForm y f L) '' E) ∧
      G ∈ Submodule.span ℂ ((fun f => a2_lineForm y f L) '' E) ∧
      F.IsHomogeneous L ∧ G.IsHomogeneous L ∧
      (∀ m, (F.coeff m).totalDegree ≤ L) ∧ (∀ m, (G.coeff m).totalDegree ≤ L) ∧
      MvPolynomial.map η.toRingHom F ≠ 0 ∧
      (∀ D : MvPolynomial (Fin 2) K,
        D ∣ binaryGcd (MvPolynomial.map η.toRingHom F) (MvPolynomial.map η.toRingHom G) ↔
          ∀ f ∈ E, D ∣ MvPolynomial.map η.toRingHom (a2_lineForm y f L)) ∧
      ∀ p ∈ S, ∃ hpy : y ≠ p,
        (groupMovingFiber J p Y (radialProjection p y hpy) y).Finite ∧
        (groupMovingFiber J p Y (radialProjection p y hpy) y).ncard = groupDepth p J Y - 1 ∧
        ∀ x ∈ groupMovingFiber J p Y (radialProjection p y hpy) y,
          ∃ V ∈ J, x ∈ radialFiber p V (radialProjection p y hpy) ∧
            ∀ W : AffineVariety d, W.IsComponentOf (Ideal.span E) → x ∈ W.points → W = V := by
  letI : X.ideal.IsPrime := hX
  let R := Poly d ⧸ X.ideal
  let K := FractionRing R
  let η : Poly d →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ R K).comp (Ideal.Quotient.mkₐ ℂ X.ideal)
  obtain ⟨H, y, hy, ⟨x₀, hx₀, hH₀⟩, hcap, hunique, hactual⟩ :=
    a2_common_target_full_components (Ideal.span E) X J hl hJ Y hY hcomponents
      q hgeneric S himage
  let U := a2_productRight y H
  have hU₀ : MvPolynomial.eval x₀ U ≠ 0 := by
    simpa only [U, a2_productRight_eval] using hH₀
  have hUnot : U ∉ X.ideal := fun hm => hU₀ (by
    simpa only [MvPolynomial.aeval_eq_eval] using hx₀ U hm)
  have hcapU : ∀ x ∈ X.points, MvPolynomial.eval x U ≠ 0 →
      x ≠ y ∧ (movingRoots x y J).Finite ∧ (movingRoots x y J).ncard ≤ q := by
    intro x hx hU
    apply hcap x hx
    simpa only [U, a2_productRight_eval] using hU
  obtain ⟨hxy, hfinite, _⟩ := hcapU x₀ hx₀ hU₀
  obtain ⟨f, hf, t, hft⟩ := a2_full_line_nonzero E J Y hY y x₀ hy hxy
    (hunique hSnon) hfinite
  have hform0 : MvPolynomial.map η.toRingHom (a2_lineForm y f L) ≠ 0 := by
    intro hz
    have hspec := generic_binary_zero_specializes X hX (a2_lineForm y f L) x₀ hx₀ hz
    apply hft
    rw [← a2_lineForm_eval_affine y x₀ f L (hE f hf) t, hspec, map_zero]
  obtain ⟨F, G, hFs, hGs, hFh, hGh, hFd, hGd, hF0, hdiv⟩ :=
    a2_two_line_forms_full_gcd η y E L ⟨f, hf, hform0⟩
  exact ⟨y, U, F, G, hy, hUnot, hcapU, hFs, hGs, hFh, hGh, hFd, hGd, hF0, hdiv, hactual⟩



/-- Roots of a monic polynomial that splits in the valuation field are
integral, so the polynomial already splits over the valuation ring. -/
theorem a2_monic_splits_valuation {K : Type*} [Field K]
    (A : ValuationSubring K) (P : Polynomial A) (hP : P.Monic)
    (hsplit : (P.map A.toSubring.subtype).Splits) : P.Splits := by
  apply Polynomial.Splits.of_splits_map_of_injective Subtype.val_injective hsplit
  intro z hz
  have hroot : P.aeval z = 0 := by
    have h := (Polynomial.mem_roots (hP.map A.toSubring.subtype).ne_zero).mp hz
    rw [Polynomial.IsRoot, Polynomial.eval_map] at h
    exact h
  have hint : IsIntegral A z := ⟨P, hP, hroot⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨a, ha⟩

/-- Splitting before reduction retains every literal residue root. -/
theorem a2_monic_residue_root_lifts {K : Type*} [Field K]
    (A : ValuationSubring K) (P : Polynomial A) (hP : P.Monic)
    (hsplit : (P.map A.toSubring.subtype).Splits)
    (z : IsLocalRing.ResidueField A)
    (hz : (P.map (IsLocalRing.residue A)).IsRoot z) :
    ∃ a : A, P.IsRoot a ∧ IsLocalRing.residue A a = z := by
  have hs := a2_monic_splits_valuation A P hP hsplit
  have hn : P.map (IsLocalRing.residue A) ≠ 0 := (hP.map _).ne_zero
  have hmem := (Polynomial.mem_roots hn).mpr hz
  rw [hs.roots_map_of_ne_zero hn] at hmem
  obtain ⟨a, ha, he⟩ := Multiset.mem_map.mp hmem
  exact ⟨a, (Polynomial.mem_roots hP.ne_zero).mp ha, he⟩

/-- The projective chart `[u:cu+1]` makes `[1:c]` its point at infinity. -/
def a2_chartPolynomial {R : Type*} [CommRing R]
    (H : MvPolynomial (Fin 2) R) (c : R) : Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, Polynomial.C c * Polynomial.X + 1] H

theorem a2_chartPolynomial_degree {R : Type*} [CommRing R]
    (H : MvPolynomial (Fin 2) R) (g : ℕ) (hH : H.IsHomogeneous g) (c : R) :
    (a2_chartPolynomial H c).natDegree ≤ g := by
  apply (OAI.Nagata.W02.natDegree_eval₂_le_totalDegree H _ ?_).trans hH.totalDegree_le
  intro i
  fin_cases i
  · exact Polynomial.natDegree_X_le
  · exact (Polynomial.natDegree_add_le _ _).trans (by
      simp only [Polynomial.natDegree_one, max_le_iff]
      exact ⟨(Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le, Nat.zero_le _⟩)

theorem a2_chartPolynomial_top_coefficient {R : Type*} [CommRing R]
    (H : MvPolynomial (Fin 2) R) (g : ℕ) (hH : H.IsHomogeneous g) (c : R) :
    (a2_chartPolynomial H c).coeff g = MvPolynomial.eval ![1,c] H := by
  let v : Fin 2 → Polynomial R := ![Polynomial.X, Polynomial.C c * Polynomial.X + 1]
  have hv (i : Fin 2) : (v i).natDegree ≤ 1 := by
    fin_cases i
    · exact Polynomial.natDegree_X_le
    · exact (Polynomial.natDegree_add_le _ _).trans (by
        simp only [Polynomial.natDegree_one, max_le_iff]
        exact ⟨(Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le, Nat.zero_le _⟩)
  change (MvPolynomial.eval₂ Polynomial.C v H).coeff g = _
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval_eq]
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  have hd : m 0 + m 1 = g := by
    have hd := hH.degree_eq_sum_deg_support hm
    have he : (∑ i ∈ m.support, m i) = m 0 + m 1 := by
      change m.sum (fun _ n => n) = _
      rw [Finsupp.sum_fintype] <;> simp
    exact he.symm.trans hd.symm
  have hp : (∏ i ∈ m.support, v i ^ m i) = v 0 ^ m 0 * v 1 ^ m 1 := by
    change m.prod (fun i n => v i ^ n) = _
    rw [Finsupp.prod_fintype] <;> simp
  have hq : (∏ i ∈ m.support, (![1,c] : Fin 2 → R) i ^ m i) = c ^ m 1 := by
    change m.prod (fun i n => (![1,c] : Fin 2 → R) i ^ n) = _
    rw [Finsupp.prod_fintype] <;> simp
  rw [Polynomial.coeff_C_mul, hp, ← hd, Polynomial.coeff_mul_add_eq_of_natDegree_le
    (by simpa using Polynomial.natDegree_pow_le_of_le (m 0) (hv 0))
    (by simpa using Polynomial.natDegree_pow_le_of_le (m 1) (hv 1))]
  have hpow (i : Fin 2) : (v i ^ m i).coeff (m i) = (v i).coeff 1 ^ m i := by
    simpa using Polynomial.coeff_pow_of_natDegree_le (m := m i) (hv i)
  rw [hpow, hpow, hq]
  simp [v, Polynomial.coeff_one]

theorem a2_homogeneous_eval_scale {R σ : Type*} [CommRing R]
    (H : MvPolynomial σ R) (g : ℕ) (hH : H.IsHomogeneous g) (c : R) (v : σ → R) :
    MvPolynomial.eval (fun i => c * v i) H = c^g * MvPolynomial.eval v H := by
  simp only [MvPolynomial.eval_eq, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← hH.degree_eq_sum_deg_support hm]
  ring

/-- Even over a residue extension, a nonzero homogeneous binary form
has a nonvanishing point `[1:c]` with constant complex c. -/
theorem a2_binary_constant_chart {k : Type*} [Field k] [Algebra ℂ k]
    (H : MvPolynomial (Fin 2) k) (g : ℕ) (hH : H.IsHomogeneous g) (hH0 : H ≠ 0) :
    ∃ c : ℂ, MvPolynomial.eval ![1, algebraMap ℂ k c] H ≠ 0 := by
  by_contra hn
  push Not at hn
  let φ := algebraMap ℂ k
  have hφ : Function.Injective φ := RingHom.injective φ
  let s : Fin 2 → Set k := fun i => if i = 0 then
    φ '' (Set.univ \ {0}) else Set.range φ
  have hs : ∀ i, (s i).Infinite := by
    intro i
    by_cases hi : i = 0
    · simp only [s, hi, if_pos rfl]
      exact (Set.infinite_univ.sdiff (Set.finite_singleton 0)).image hφ.injOn
    · simp only [s, hi, if_false]
      exact Set.infinite_range_of_injective hφ
  apply hH0
  apply MvPolynomial.funext_set s hs
  intro x hx
  have hx0 : x 0 ∈ φ '' (Set.univ \ {0}) := by
    simpa only [s, if_pos rfl] using hx 0 (Set.mem_univ _)
  have hx1 : x 1 ∈ Set.range φ := by
    simpa only [s, show (1 : Fin 2) ≠ 0 by decide, if_false] using hx 1 (Set.mem_univ _)
  obtain ⟨a, ha, he0⟩ := hx0
  obtain ⟨b, he1⟩ := hx1
  have ha0 : a ≠ 0 := by simpa only [Set.mem_sdiff, Set.mem_univ,
    Set.mem_singleton_iff, true_and] using ha
  have hecoords : (fun i : Fin 2 => φ a * (![1, φ (b/a)] : Fin 2 → k) i) = x := by
    funext i
    fin_cases i
    · change φ a * 1 = x 0
      simpa only [mul_one] using he0
    · change φ a * φ (b/a) = x 1
      rw [map_div₀, mul_div_cancel₀ _ ((map_ne_zero φ).mpr ha0)]
      exact he1
  rw [map_zero]
  rw [← hecoords, a2_homogeneous_eval_scale H g hH]
  simp only [φ, hn, mul_zero]

theorem a2_chartPolynomial_eval₂ {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (H : MvPolynomial (Fin 2) R) (c : R) (u : S) :
    (a2_chartPolynomial H c).eval₂ φ u =
      MvPolynomial.eval₂ φ ![u, φ c * u + 1] H := by
  let ε : Polynomial R →+* S := Polynomial.eval₂RingHom φ u
  have h := MvPolynomial.map_eval₂Hom Polynomial.C
    (![Polynomial.X, Polynomial.C c * Polynomial.X + 1] : Fin 2 → Polynomial R) ε H
  have hcomp : ε.comp Polynomial.C = φ := by
    ext r
    exact Polynomial.eval₂_C φ u
  have hcoords : (fun i : Fin 2 => ε
      ((![Polynomial.X, Polynomial.C c * Polynomial.X + 1] : Fin 2 → Polynomial R) i)) =
      ![u, φ c * u + 1] := by
    funext i
    fin_cases i <;> simp [ε]
  rw [hcomp, hcoords] at h
  exact h


theorem a2_binary_eval_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (H : MvPolynomial (Fin 2) R) (a b : R) :
    φ (MvPolynomial.eval ![a,b] H) =
      MvPolynomial.eval ![φ a, φ b] (MvPolynomial.map φ H) := by
  rw [MvPolynomial.eval₂_comp, MvPolynomial.eval_map]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- A chart with unit leading coefficient turns the homogeneous
divisor into a monic polynomial. Lift its roots and invert the chart
parameter to recover integral affine roots with the supplied residue. -/
theorem a2_binary_reduction_root_lifts {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) (H : MvPolynomial (Fin 2) A) (g : ℕ)
    (hH : H.IsHomogeneous g) (c : A)
    (hc : IsUnit (MvPolynomial.eval ![1,c] H))
    (r : IsLocalRing.ResidueField A)
    (hr : MvPolynomial.eval ![1,r] (MvPolynomial.map (IsLocalRing.residue A) H) = 0) :
    ∃ t : A, MvPolynomial.eval ![1,t] H = 0 ∧ IsLocalRing.residue A t = r := by
  let res := IsLocalRing.residue A
  let H₀ := MvPolynomial.map res H
  have hrne : r ≠ res c := by
    intro he
    have hres := a2_binary_eval_map res H 1 c
    rw [map_one] at hres
    exact (hc.map res).ne_zero (hres.trans (by simpa only [← he, H₀, res] using hr))
  let Q := a2_chartPolynomial H c
  have hQd : Q.natDegree = g := by
    apply le_antisymm (a2_chartPolynomial_degree H g hH c)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [a2_chartPolynomial_top_coefficient H g hH c]
    exact hc.ne_zero
  have hQlead : Q.leadingCoeff = MvPolynomial.eval ![1,c] H := by
    rw [← Polynomial.coeff_natDegree, hQd]
    exact a2_chartPolynomial_top_coefficient H g hH c
  let e := hc.unit
  let b : A := ↑e⁻¹
  have hb : b * MvPolynomial.eval ![1,c] H = 1 := by
    rw [← hc.unit_spec]
    exact Units.inv_mul e
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hb
    exact zero_ne_one hb
  let P := Polynomial.C b * Q
  have hP : P.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hQlead]; exact hb)
  let u₀ := (r-res c)⁻¹
  have hu₀ : u₀ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hrne)
  have humul : u₀ * (r-res c) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr hrne)
  have hcoords : (![u₀,res c*u₀+1] : Fin 2 → IsLocalRing.ResidueField A) =
      (fun i => u₀ * (![1,r] : Fin 2 → IsLocalRing.ResidueField A) i) := by
    funext i
    fin_cases i
    · simp
    · change res c * u₀ + 1 = u₀ * r
      rw [← humul]
      ring
  have hQroot : (Q.map res).IsRoot u₀ := by
    rw [Polynomial.IsRoot, Polynomial.eval_map, a2_chartPolynomial_eval₂,
      ← MvPolynomial.eval_map, hcoords,
      a2_homogeneous_eval_scale _ g (hH.map res)]
    simp only [res, hr, mul_zero]
  have hProot : (P.map res).IsRoot u₀ := by
    change Polynomial.eval u₀ ((Polynomial.C b * Q).map res) = 0
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_eq_zero_of_right _ hQroot
  obtain ⟨u, hu, hur⟩ := a2_monic_residue_root_lifts A P hP (IsAlgClosed.splits _) u₀ hProot
  have huU : IsUnit u := (IsLocalRing.residue_ne_zero_iff_isUnit u).mp (hur ▸ hu₀)
  let v : A := ↑huU.unit⁻¹
  have huv : u * v = 1 := by
    rw [← huU.unit_spec]
    exact Units.mul_inv huU.unit
  have hresv : res v = u₀⁻¹ := by
    apply mul_left_cancel₀ hu₀
    calc
      u₀ * res v = res (u*v) := by rw [map_mul, hur]
      _ = 1 := by rw [huv, map_one]
      _ = u₀ * u₀⁻¹ := (mul_inv_cancel₀ hu₀).symm
  have hQzero : Q.eval u = 0 := by
    have h := hu
    change (Polynomial.C b * Q).eval u = 0 at h
    rw [Polynomial.eval_mul, Polynomial.eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left hb0
  let t := c+v
  refine ⟨t, ?_, ?_⟩
  · have hecoords : (![u,c*u+1] : Fin 2 → A) = (fun i => u * (![1,t] : Fin 2 → A) i) := by
      funext i
      fin_cases i
      · simp
      · change c*u+1 = u*(c+v)
        rw [← huv]
        ring
    have heval : MvPolynomial.eval ![u,c*u+1] H = 0 := by
      simpa only [Q, RingHom.id_apply, ← MvPolynomial.eval₂_id] using
        (a2_chartPolynomial_eval₂ (RingHom.id A) H c u).symm.trans hQzero
    rw [hecoords, a2_homogeneous_eval_scale H g hH] at heval
    exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ huU.ne_zero)
  · change res (c+v) = r
    rw [map_add, hresv]
    simp only [u₀, inv_inv]
    ring

/-- Every finite root of the primitive reduction comes from an
integral affine root of the original homogeneous divisor, with its
identity preserved in the residue field. -/
theorem a2_primitive_binary_root_lifts {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) [Algebra ℂ A]
    (H : MvPolynomial (Fin 2) A) (g : ℕ) (hH : H.IsHomogeneous g)
    (hunit : ∃ m, H.coeff m = 1) :
    ∀ r : IsLocalRing.ResidueField A,
      MvPolynomial.eval ![1,r] (MvPolynomial.map (IsLocalRing.residue A) H) = 0 →
        ∃ t : A, MvPolynomial.eval ![1,t] H = 0 ∧ IsLocalRing.residue A t = r := by
  let res := IsLocalRing.residue A
  let H₀ := MvPolynomial.map res H
  have hH0 : H₀ ≠ 0 := a2_primitive_map_nonzero res H hunit
  obtain ⟨c, hc⟩ := a2_binary_constant_chart H₀ g (hH.map res) hH0
  let cA := algebraMap ℂ A c
  have hchart : IsUnit (MvPolynomial.eval ![1,cA] H) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    have he := a2_binary_eval_map res H 1 cA
    rw [map_one] at he
    rw [he]
    exact hc
  exact a2_binary_reduction_root_lifts A H g hH cA hchart



/-- Every distinguished residue root of the generic divisor comes from a
retained generic moving root on the same original full-system component. -/
theorem a2_distinguished_divisor_support_count {d n : ℕ} {K : Type*}
    [Field K] [IsAlgClosed K] [Algebra ℂ K]
    (A : ValuationSubring K) [Algebra ℂ A]
    (ι : A →ₐ[ℂ] K) (hι : ∀ a, ι a = (a : K))
    (X : AffineVariety d) (J : AffineFamily.Family d)
    (E : Set (Poly d)) (L q : ℕ) (hE : ∀ f ∈ E, f.totalDegree ≤ L)
    (y p : Point d) (U : Poly d)
    (hcap : ∀ x ∈ X.points, MvPolynomial.eval x U ≠ 0 →
      x ≠ y ∧ (movingRoots x y J).Finite ∧ (movingRoots x y J).ncard ≤ q)
    (xA : Fin d → A)
    (hx : ∀ f ∈ X.ideal, MvPolynomial.aeval (fun j => ι (xA j)) f = 0)
    (hU : MvPolynomial.aeval (fun j => ι (xA j)) U ≠ 0)
    (hresx : ∀ j, IsLocalRing.residue A (xA j) =
      algebraMap ℂ (IsLocalRing.ResidueField A) (p j))
    (H : MvPolynomial (Fin 2) A) (g : ℕ) (hH : H.IsHomogeneous g)
    (hunit : ∃ m, H.coeff m = 1)
    (hdiv : ∀ f ∈ E, MvPolynomial.map ι.toRingHom H ∣
      MvPolynomial.map (MvPolynomial.aeval (fun j => ι (xA j))).toRingHom
        (a2_lineForm y f L))
    (r : Fin n → ℂ) (hr : Function.Injective r)
    (hr0 : ∀ i, r i ≠ 0) (hr1 : ∀ i, r i ≠ 1)
    (hroot : ∀ i, MvPolynomial.eval
      ![1, algebraMap ℂ (IsLocalRing.ResidueField A) (r i)]
      (MvPolynomial.map (IsLocalRing.residue A) H) = 0)
    (hunique : ∀ i, ∃ V ∈ J,
      ∀ W : AffineVariety d, W.IsComponentOf (Ideal.span E) →
        y + r i • (p-y) ∈ W.points → W = V) : n ≤ q := by
  let k := IsLocalRing.ResidueField A
  let res : A →ₐ[ℂ] k := IsScalarTower.toAlgHom ℂ A k
  have hιinj : Function.Injective ι := by
    intro a b he
    apply Subtype.ext
    simpa only [hι] using he
  obtain ⟨t, htroot, htres⟩ := show ∃ t : Fin n → A,
      (∀ i, MvPolynomial.eval ![1,t i] H = 0) ∧
      (∀ i, res (t i) = algebraMap ℂ k (r i)) by
    have hlift (i : Fin n) := a2_primitive_binary_root_lifts A H g hH hunit
      (algebraMap ℂ k (r i)) (hroot i)
    choose t htr hts using hlift
    exact ⟨t, htr, hts⟩
  have ht : Function.Injective (fun i => ι (t i)) := by
    intro i j he
    apply hr
    apply RingHom.injective (algebraMap ℂ k)
    rw [← htres i, ← htres j, hιinj he]
  have ht0 (i : Fin n) : ι (t i) ≠ 0 := by
    intro he
    have htz : t i = 0 := hιinj (he.trans (map_zero ι).symm)
    have h := htres i
    rw [htz, map_zero] at h
    exact hr0 i (RingHom.injective (algebraMap ℂ k) (h.symm.trans (map_zero _).symm))
  have ht1 (i : Fin n) : ι (t i) ≠ 1 := by
    intro he
    have htz : t i = 1 := hιinj (he.trans (map_one ι).symm)
    have h := htres i
    rw [htz, map_one] at h
    exact hr1 i (RingHom.injective (algebraMap ℂ k) (h.symm.trans (map_one _).symm))
  apply a2_moving_parameter_count_over_field X J y U q hcap
    (fun j => ι (xA j)) hx hU (fun i => ι (t i)) ht ht0 ht1
  intro i
  let v : Fin d → A := fun j => algebraMap ℂ A (y j) +
    t i * (xA j - algebraMap ℂ A (y j))
  have hvcoords : (fun j => ι (v j)) =
      (fun j => algebraMap ℂ K (y j) +
        ι (t i) * (ι (xA j) - algebraMap ℂ K (y j))) := by
    funext j
    simp only [v, map_add, map_mul, map_sub, ι.commutes]
  have hvanish : ∀ f ∈ E, MvPolynomial.aeval (fun j => ι (v j)) f = 0 := by
    intro f hf
    obtain ⟨Q, hQ⟩ := hdiv f hf
    have hz : MvPolynomial.eval ![1,ι (t i)]
        (MvPolynomial.map ι.toRingHom H) = 0 := by
      have he := a2_binary_eval_map ι.toRingHom H 1 (t i)
      change ι (MvPolynomial.eval ![1,t i] H) =
        MvPolynomial.eval ![ι 1,ι (t i)] (MvPolynomial.map ι.toRingHom H) at he
      simpa only [map_one, htroot i, map_zero] using he.symm
    rw [hvcoords, ← a2_lineForm_eval₂_affine y
      (fun j => ι (xA j)) f L (hE f hf) (ι (t i)),
      MvPolynomial.eval₂_eq_eval_map, hQ, map_mul, hz, zero_mul]
  have hspan : ∀ f ∈ Ideal.span E,
      MvPolynomial.aeval (fun j => ι (v j)) f = 0 := by
    have hle : Ideal.span E ≤ RingHom.ker (MvPolynomial.aeval (fun j => ι (v j))) :=
      Ideal.span_le.mpr (fun f hf => RingHom.mem_ker.mpr (hvanish f hf))
    exact fun f hf => RingHom.mem_ker.mp (hle hf)
  obtain ⟨W, hW, hvW⟩ := a2_field_point_minimal_component (Ideal.span E)
    (fun j => ι (v j)) hspan
  have hpcoords : ∀ j, res (v j) = algebraMap ℂ k ((y + r i • (p-y)) j) := by
    intro j
    have hrx : res (xA j) = algebraMap ℂ k (p j) := hresx j
    simp only [v, map_add, map_mul, map_sub, res.commutes, htres i,
      hrx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  have hpW := a2_component_specializes ι hιinj res v
    (y + r i • (p-y)) hpcoords W hvW
  obtain ⟨V, hV, huni⟩ := hunique i
  have heW := huni W hW hpW
  refine ⟨V, hV, ?_⟩
  intro f hf
  rw [← hvcoords]
  exact hvW f (heW.symm ▸ hf)


/-- A primitive model of the actual generic divisor dominates the literal
complex point and divides both integral forms before residue reduction. -/
theorem a2_point_generic_divisor_model {R K σ : Type*}
    [CommRing R] [Field K] [Algebra ℂ R] [Algebra ℂ K]
    (ε : R →ₐ[ℂ] ℂ) (f : R →ₐ[ℂ] K) (hf : Function.Injective f)
    (F G : MvPolynomial σ R) (D : MvPolynomial σ K) (g : ℕ)
    (hD : D.IsHomogeneous g) (hD0 : D ≠ 0)
    (hDF : D ∣ MvPolynomial.map f.toRingHom F)
    (hDG : D ∣ MvPolynomial.map f.toRingHom G) :
    ∃ (A : ValuationSubring K) (φ : R →+* A) (c : K) (H : MvPolynomial σ A),
      A.toSubring.subtype.comp φ = f.toRingHom ∧
      (∀ r : R, IsLocalRing.residue A (φ r) =
        IsLocalRing.residue A (φ (algebraMap ℂ R (ε r)))) ∧
      c ≠ 0 ∧ D = MvPolynomial.C c * MvPolynomial.map A.toSubring.subtype H ∧
      H.IsHomogeneous g ∧ (∃ m, H.coeff m = 1) ∧
      H ∣ MvPolynomial.map φ F ∧ H ∣ MvPolynomial.map φ G := by
  obtain ⟨A, φ, hcomp, hres⟩ := a2_point_valuation_model_of_embedding ε f hf
  have hFmap : MvPolynomial.map A.toSubring.subtype (MvPolynomial.map φ F) =
      MvPolynomial.map f.toRingHom F := by
    rw [MvPolynomial.map_map, hcomp]
  have hGmap : MvPolynomial.map A.toSubring.subtype (MvPolynomial.map φ G) =
      MvPolynomial.map f.toRingHom G := by
    rw [MvPolynomial.map_map, hcomp]
  obtain ⟨c, H, hc, he, hh, hu, hHF, hHG⟩ := a2_valuation_common_divisor_model A
    (MvPolynomial.map φ F) (MvPolynomial.map φ G) D g hD hD0
    (hFmap.symm ▸ hDF) (hGmap.symm ▸ hDG)
  exact ⟨A, φ, c, H, hcomp, hres, hc, he, hh, hu, hHF, hHG⟩


/-- Convert the literal radial points into distinct affine parameters,
retaining their entire original full-system component identity. -/
theorem a2_radial_affine_parameter {d : ℕ} (p y x : Point d)
    (hpy : y ≠ p) (hxp : x ≠ p) (hxy : x ≠ y)
    (he : radialProjection p x hxp = radialProjection p y hpy) :
    ∃ r : ℂ, r ≠ 0 ∧ r ≠ 1 ∧ x = y + r • (p-y) := by
  obtain ⟨t, ht, _⟩ := radial_moving_root_parameter p y x hpy hxp hxy he
  obtain ⟨ht0, ht1⟩ := radial_moving_parameter_endpoints p y x hpy hxp t ht
  have heq : x = y + t⁻¹ • (p-y) := by
    rw [ht, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht0, one_smul,
      add_sub_cancel]
  exact ⟨t⁻¹, inv_ne_zero ht0, (fun h => ht1 (inv_eq_one.mp h)), heq⟩

theorem a2_distinguished_parameter_list {d : ℕ}
    (J : AffineFamily.Family d) (Y : AffineVariety d) (E : Set (Poly d))
    (hcomponents : ∀ V ∈ J, V.IsComponentOf (Ideal.span E))
    (p y : Point d) (hpy : y ≠ p)
    (hfinite : (groupMovingFiber J p Y (radialProjection p y hpy) y).Finite)
    (hcard : (groupMovingFiber J p Y (radialProjection p y hpy) y).ncard =
      groupDepth p J Y - 1)
    (hactual : ∀ x ∈ groupMovingFiber J p Y (radialProjection p y hpy) y,
      ∃ V ∈ J, x ∈ radialFiber p V (radialProjection p y hpy) ∧
        ∀ W : AffineVariety d, W.IsComponentOf (Ideal.span E) → x ∈ W.points → W = V) :
    ∃ T : Finset ℂ, T.card = groupDepth p J Y - 1 ∧
      (∀ r ∈ T, r ≠ 0 ∧ r ≠ 1) ∧
      (∀ r ∈ T, ∀ f ∈ E, MvPolynomial.eval (y + r • (p-y)) f = 0) ∧
      ∀ r ∈ T, ∃ V ∈ J,
        ∀ W : AffineVariety d, W.IsComponentOf (Ideal.span E) →
          y + r • (p-y) ∈ W.points → W = V := by
  let P := groupMovingFiber J p Y (radialProjection p y hpy) y
  letI : Fintype P := hfinite.fintype
  have hparam (x : P) : ∃ r : ℂ, r ≠ 0 ∧ r ≠ 1 ∧ x.val = y + r • (p-y) := by
    obtain ⟨V, hV, hx, _⟩ := hactual x.val x.property
    exact a2_radial_affine_parameter p y x.val hpy hx.2.1
      (by simpa only [Set.mem_singleton_iff] using x.property.2) hx.2.2
  choose r hr0 hr1 hrx using hparam
  have hrinj : Function.Injective r := by
    intro x z he
    apply Subtype.ext
    rw [hrx x, hrx z, he]
  let T : Finset ℂ := Finset.univ.image r
  have hT (s : ℂ) : s ∈ T ↔ ∃ x : P, r x = s := by
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hrinj, Finset.card_univ,
      Set.fintypeCard_eq_ncard, hcard]
  · intro s hs
    obtain ⟨x, rfl⟩ := (hT s).mp hs
    exact ⟨hr0 x, hr1 x⟩
  · intro s hs f hf
    obtain ⟨x, rfl⟩ := (hT s).mp hs
    obtain ⟨V, hV, hx, _⟩ := hactual x.val x.property
    rw [← hrx x]
    exact hx.1 f ((hcomponents V hV).le (Ideal.subset_span hf))
  · intro s hs
    obtain ⟨x, rfl⟩ := (hT s).mp hs
    obtain ⟨V, hV, _, huniq⟩ := hactual x.val x.property
    exact ⟨V, hV, fun W hW hx => huniq W hW ((hrx x).symm ▸ hx)⟩


/-- A degree-preserving limit of the actual generic divisor at any source
point meets at most q distinguished retained moving parameters. The residue
field may extend the complex field; no coefficient descent is assumed. -/
theorem a2_point_limit_with_support {d : ℕ} {K : Type*}
    [Field K] [IsAlgClosed K] [Algebra ℂ K]
    (X : AffineVariety d) (J : AffineFamily.Family d)
    (η : Poly d →ₐ[ℂ] K) (hker : ∀ f, η f = 0 ↔ f ∈ X.ideal)
    (E : Set (Poly d)) (L q : ℕ) (hE : ∀ f ∈ E, f.totalDegree ≤ L)
    (y : Point d) (U : Poly d) (hU : η U ≠ 0)
    (hcap : ∀ x ∈ X.points, MvPolynomial.eval x U ≠ 0 →
      x ≠ y ∧ (movingRoots x y J).Finite ∧ (movingRoots x y J).ncard ≤ q)
    (F G : BinaryForm d) (D : MvPolynomial (Fin 2) K) (g : ℕ)
    (hD : D.IsHomogeneous g) (hD0 : D ≠ 0)
    (hDF : D ∣ MvPolynomial.map η.toRingHom F)
    (hDG : D ∣ MvPolynomial.map η.toRingHom G)
    (hdiv : ∀ f ∈ E, D ∣ MvPolynomial.map η.toRingHom (a2_lineForm y f L))
    (p : Point d) (hp : p ∈ X.points) :
    let R := Poly d ⧸ X.ideal
    ∃ (A : ValuationSubring K) (φ : R →+* A)
      (H₀ : MvPolynomial (Fin 2) (IsLocalRing.ResidueField A)),
      let cMap : ℂ →+* IsLocalRing.ResidueField A :=
        (IsLocalRing.residue A).comp (φ.comp (algebraMap ℂ R))
      H₀ ≠ 0 ∧ H₀.IsHomogeneous g ∧
      H₀ ∣ MvPolynomial.map cMap (specializeBinary F p) ∧
      H₀ ∣ MvPolynomial.map cMap (specializeBinary G p) ∧
      ∀ (n : ℕ) (r : Fin n → ℂ), Function.Injective r →
        (∀ i, r i ≠ 0) → (∀ i, r i ≠ 1) →
        (∀ i, MvPolynomial.eval ![1,cMap (r i)] H₀ = 0) →
        (∀ i, ∃ V ∈ J,
          ∀ W : AffineVariety d, W.IsComponentOf (Ideal.span E) →
            y + r i • (p-y) ∈ W.points → W = V) → n ≤ q := by
  let R := Poly d ⧸ X.ideal
  let Q : Poly d →ₐ[ℂ] R := Ideal.Quotient.mkₐ ℂ X.ideal
  let ε : R →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ X.ideal (MvPolynomial.aeval p)
    (fun f hf => hp f hf)
  let f : R →ₐ[ℂ] K := Ideal.Quotient.liftₐ X.ideal η
    (fun f hf => (hker f).mpr hf)
  have hf : Function.Injective f :=
    RingHom.lift_injective_of_ker_le_ideal X.ideal
      (fun f hf => (hker f).mpr hf)
      (fun f hf => (hker f).mp (RingHom.mem_ker.mp hf))
  have hfQ (P : Poly d) : f (Q P) = η P := rfl
  have hεQ (P : Poly d) : ε (Q P) = MvPolynomial.eval p P := by
    change (MvPolynomial.aeval p) P = _
    exact congrFun (MvPolynomial.aeval_eq_eval p) P
  have hmap (P : BinaryForm d) :
      MvPolynomial.map f.toRingHom (MvPolynomial.map Q.toRingHom P) =
        MvPolynomial.map η.toRingHom P := by
    rw [MvPolynomial.map_map]
    rfl
  obtain ⟨A, φ, c, H, hcomp, hres, hc, he, hh, hu, hHF, hHG⟩ :=
    a2_point_generic_divisor_model ε f hf
      (MvPolynomial.map Q.toRingHom F) (MvPolynomial.map Q.toRingHom G)
      D g hD hD0 ((hmap F).symm ▸ hDF) ((hmap G).symm ▸ hDG)
  let cA : ℂ →+* A := φ.comp (algebraMap ℂ R)
  letI : Algebra ℂ A := cA.toAlgebra
  let k := IsLocalRing.ResidueField A
  let res := IsLocalRing.residue A
  let cMap : ℂ →+* k := res.comp cA
  have hcMap (z : ℂ) : algebraMap ℂ k z = cMap z := by
    rw [IsScalarTower.algebraMap_apply ℂ A k]
    rfl
  let ι : A →ₐ[ℂ] K :=
    { toRingHom := A.toSubring.subtype
      commutes' := by
        intro z
        change A.toSubring.subtype (φ (algebraMap ℂ R z)) = algebraMap ℂ K z
        exact (RingHom.congr_fun hcomp _).trans (f.commutes z) }
  have hι (a : A) : ι a = (a : K) := rfl
  let H₀ := MvPolynomial.map res H
  have hcoeff (P : Poly d) : res (φ (Q P)) = cMap (MvPolynomial.eval p P) := by
    exact (hres (Q P)).trans (by rw [hεQ]; rfl)
  have hreduce (P : BinaryForm d) :
      MvPolynomial.map res (MvPolynomial.map φ (MvPolynomial.map Q.toRingHom P)) =
        MvPolynomial.map cMap (specializeBinary P p) := by
    ext m
    simp only [MvPolynomial.coeff_map, specializeBinary]
    exact hcoeff (P.coeff m)
  refine ⟨A, φ, H₀, a2_primitive_map_nonzero res H hu, hh.map res,
    (hreduce F) ▸ (map_dvd (MvPolynomial.map res) hHF),
    (hreduce G) ▸ (map_dvd (MvPolynomial.map res) hHG), ?_⟩
  intro n r hr hr0 hr1 hrroot huniq
  let xA : Fin d → A := fun j => φ (Q (MvPolynomial.X j))
  have hxcoords (j : Fin d) : ι (xA j) = η (MvPolynomial.X j) := by
    exact (RingHom.congr_fun hcomp _).trans (hfQ _)
  have hηcoords : MvPolynomial.aeval (fun j => ι (xA j)) = η := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [MvPolynomial.aeval_X, hxcoords]
  have hx : ∀ P ∈ X.ideal, MvPolynomial.aeval (fun j => ι (xA j)) P = 0 := by
    intro P hP
    rw [hηcoords]
    exact (hker P).mpr hP
  have hresx (j : Fin d) : res (xA j) = algebraMap ℂ k (p j) := by
    have heval := hcoeff (MvPolynomial.X j)
    simpa only [xA, MvPolynomial.eval_X, hcMap] using heval
  have hdivH : ∀ P ∈ E, MvPolynomial.map ι.toRingHom H ∣
      MvPolynomial.map (MvPolynomial.aeval (fun j => ι (xA j))).toRingHom
        (a2_lineForm y P L) := by
    intro P hP
    rw [hηcoords]
    apply dvd_trans ?_ (hdiv P hP)
    refine ⟨MvPolynomial.C c, ?_⟩
    rw [he]
    exact mul_comm _ _
  exact a2_distinguished_divisor_support_count A ι hι X J E L q hE y p U hcap xA hx
    (by rwa [hηcoords]) hresx H g hh hu hdivH r hr hr0 hr1 hrroot huniq


/-- Homogeneous root divisibility over the actual residue field, including
the simple linear factors outside a retained primitive divisor. -/
theorem a2_binary_support_degree {R : Type*} [CommRing R]
    (H : MvPolynomial (Fin 2) R) (g : ℕ) (hH : H.IsHomogeneous g)
    (m : Fin 2 →₀ ℕ) (hm : m ∈ H.support) : m 0 + m 1 = g := by
  have hd := hH.degree_eq_sum_deg_support hm
  have he : (∑ i ∈ m.support, m i) = m 0 + m 1 := by
    change m.sum (fun _ n => n) = _
    rw [Finsupp.sum_fintype] <;> simp
  exact he.symm.trans hd.symm

theorem a2_binary_axis_coefficient {R : Type*} [CommRing R]
    (H : MvPolynomial (Fin 2) R) (g : ℕ) (hH : H.IsHomogeneous g) :
    MvPolynomial.eval ![1,0] H = H.coeff (Finsupp.single 0 g) := by
  rw [MvPolynomial.eval_eq]
  have he (m : Fin 2 →₀ ℕ) :
      (∏ i ∈ m.support, (![1,0] : Fin 2 → R) i ^ m i) = (0 : R) ^ m 1 := by
    change m.prod (fun i n => (![1,0] : Fin 2 → R) i ^ n) = _
    rw [Finsupp.prod_fintype] <;> simp
  simp_rw [he]
  rw [Finset.sum_eq_single (Finsupp.single 0 g)]
  · simp
  · intro m hm hne
    by_cases hm1 : m 1 = 0
    · have hd := a2_binary_support_degree H g hH m hm
      have heq : m = Finsupp.single 0 g := by
        ext i
        fin_cases i <;> simp [Finsupp.single_apply, hm1] <;> omega
      exact (hne heq).elim
    · simp [zero_pow hm1]
  · intro hn
    have hc : H.coeff (Finsupp.single 0 g) = 0 :=
      not_ne_iff.mp (fun h => hn (MvPolynomial.mem_support_iff.mpr h))
    simp [hc]

theorem a2_axis_root_dvd {R : Type*} [CommRing R]
    (H : MvPolynomial (Fin 2) R) (g : ℕ) (hH : H.IsHomogeneous g)
    (hroot : MvPolynomial.eval ![1,0] H = 0) :
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ∣ H := by
  apply MvPolynomial.X_dvd_iff_modMonomial_eq_zero.mpr
  ext m
  by_cases hm : Finsupp.single (1 : Fin 2) 1 ≤ m
  · rw [MvPolynomial.coeff_modMonomial_of_le H hm]
    simp
  · rw [MvPolynomial.coeff_modMonomial_of_not_le H hm, MvPolynomial.coeff_zero]
    have hm1 : m 1 = 0 := by
      have hn : ¬ 1 ≤ m 1 := by simpa only [Finsupp.single_le_iff] using hm
      omega
    by_contra hn
    have hd := a2_binary_support_degree H g hH m (MvPolynomial.mem_support_iff.mpr hn)
    have heq : m = Finsupp.single 0 g := by
      ext i
      fin_cases i <;> simp [Finsupp.single_apply, hm1] <;> omega
    exact hn (heq ▸ ((a2_binary_axis_coefficient H g hH).symm.trans hroot))

def a2_binaryShear {R : Type*} [CommRing R] (r : R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C r * MvPolynomial.X 0]

theorem a2_binaryShear_homogeneous {R : Type*} [CommRing R]
    (r : R) (H : MvPolynomial (Fin 2) R) (g : ℕ) (hH : H.IsHomogeneous g) :
    (a2_binaryShear r H).IsHomogeneous g := by
  have hcoords : ∀ i : Fin 2,
      (![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C r * MvPolynomial.X 0] i :
        MvPolynomial (Fin 2) R).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact MvPolynomial.isHomogeneous_X R 0
    · exact (MvPolynomial.isHomogeneous_X R 1).add
        ((MvPolynomial.isHomogeneous_X R 0).C_mul r)
  simpa only [one_mul, a2_binaryShear] using hH.aeval _ hcoords

theorem a2_binaryShear_inverse {R : Type*} [CommRing R] (r : R) :
    (a2_binaryShear (-r)).comp (a2_binaryShear r) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [a2_binaryShear]

theorem a2_binary_affine_root_dvd {R : Type*} [CommRing R]
    (H : MvPolynomial (Fin 2) R) (g : ℕ) (hH : H.IsHomogeneous g) (r : R)
    (hroot : MvPolynomial.eval ![1,r] H = 0) :
    (MvPolynomial.X 1 - MvPolynomial.C r * MvPolynomial.X 0) ∣ H := by
  have hshear : MvPolynomial.eval ![1,0] (a2_binaryShear r H) = 0 := by
    have he : (MvPolynomial.aeval (![1,0] : Fin 2 → R)).comp
        (a2_binaryShear r) = MvPolynomial.aeval ![1,r] := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [a2_binaryShear]
    exact (AlgHom.congr_fun he H).trans hroot
  have hd := a2_axis_root_dvd (a2_binaryShear r H) g
    (a2_binaryShear_homogeneous r H g hH) hshear
  have hm := map_dvd (a2_binaryShear (-r)) hd
  have hleft : a2_binaryShear (-r) (MvPolynomial.X 1) =
      MvPolynomial.X 1 - MvPolynomial.C r * MvPolynomial.X 0 := by
    simp [a2_binaryShear, sub_eq_add_neg]
  have hright : a2_binaryShear (-r) (a2_binaryShear r H) = H :=
    AlgHom.congr_fun (a2_binaryShear_inverse r) H
  rwa [hleft, hright] at hm

def a2_affineRootFactor {K : Type*} [Field K] (r : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 1 - MvPolynomial.C r * MvPolynomial.X 0

theorem a2_affineRootFactor_homogeneous {K : Type*} [Field K] (r : K) :
    (a2_affineRootFactor r).IsHomogeneous 1 :=
  (MvPolynomial.isHomogeneous_X K 1).sub ((MvPolynomial.isHomogeneous_X K 0).C_mul r)

theorem a2_affineRootFactor_ne_zero {K : Type*} [Field K] (r : K) :
    a2_affineRootFactor r ≠ 0 := by
  intro he
  have hv := congrArg (MvPolynomial.eval (![0,1] : Fin 2 → K)) he
  simp [a2_affineRootFactor] at hv

theorem a2_affineRootFactor_prime {K : Type*} [Field K] (r : K) :
    Prime (a2_affineRootFactor r) := by
  apply irreducible_iff_prime.mp
  apply MvPolynomial.irreducible_of_totalDegree_eq_one
    ((a2_affineRootFactor_homogeneous r).totalDegree (a2_affineRootFactor_ne_zero r))
  intro c hc
  have h := hc (Finsupp.single (1 : Fin 2) 1)
  have hcoeff : (a2_affineRootFactor r).coeff (Finsupp.single (1 : Fin 2) 1) = 1 := by
    have hne : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 := by
      intro he
      have hv := congrArg (fun m : Fin 2 →₀ ℕ => m 0) he
      simp at hv
    simp [a2_affineRootFactor, MvPolynomial.coeff_X, MvPolynomial.coeff_C_mul, hne]
  exact isUnit_iff_dvd_one.mpr (hcoeff ▸ h)

theorem a2_augment_binary_divisor {K : Type*} [Field K]
    (H F : MvPolynomial (Fin 2) K) (L : ℕ) (hF : F.IsHomogeneous L)
    (hHF : H ∣ F) (T : Finset K)
    (hroots : ∀ r ∈ T, MvPolynomial.eval ![1,r] F = 0)
    (houtside : ∀ r ∈ T, MvPolynomial.eval ![1,r] H ≠ 0) :
    H * ∏ r ∈ T, a2_affineRootFactor r ∣ F := by
  revert hroots houtside
  induction T using Finset.induction_on with
  | empty => intro _ _; simpa using hHF
  | @insert a T ha ih =>
    intro hroots houtside
    obtain ⟨Q, hQ⟩ := ih
      (fun r hr => hroots r (Finset.mem_insert_of_mem hr))
      (fun r hr => houtside r (Finset.mem_insert_of_mem hr))
    let N := H * ∏ r ∈ T, a2_affineRootFactor r
    have hNroot : MvPolynomial.eval ![1,a] N ≠ 0 := by
      simp only [N, map_mul, map_prod, a2_affineRootFactor,
        map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
        Matrix.cons_val_one, Matrix.cons_val_zero, mul_one, mul_ne_zero_iff]
      refine ⟨houtside a (Finset.mem_insert_self _ _), Finset.prod_ne_zero_iff.mpr ?_⟩
      intro r hr
      exact sub_ne_zero.mpr (fun he => ha (he.symm ▸ hr))
    have hnot : ¬ a2_affineRootFactor a ∣ N := by
      rintro ⟨R, hR⟩
      apply hNroot
      rw [hR, map_mul]
      simp [a2_affineRootFactor]
    have hlin : a2_affineRootFactor a ∣ F :=
      a2_binary_affine_root_dvd F L hF a (hroots a (Finset.mem_insert_self _ _))
    have hlinQ : a2_affineRootFactor a ∣ Q :=
      ((a2_affineRootFactor_prime a).dvd_mul.mp (hQ ▸ hlin)).resolve_left hnot
    obtain ⟨R, hR⟩ := hlinQ
    refine ⟨R, ?_⟩
    rw [hQ, hR, Finset.prod_insert ha]
    ring

theorem a2_binary_common_divisor_gain {K : Type*} [Field K]
    (F G H : MvPolynomial (Fin 2) K) (L g : ℕ)
    (hF : F.IsHomogeneous L) (hG : G.IsHomogeneous L)
    (hnonzero : F ≠ 0 ∨ G ≠ 0) (hH : H.IsHomogeneous g) (hH0 : H ≠ 0)
    (hHF : H ∣ F) (hHG : H ∣ G) (T : Finset K)
    (hrootsF : ∀ r ∈ T, MvPolynomial.eval ![1,r] F = 0)
    (hrootsG : ∀ r ∈ T, MvPolynomial.eval ![1,r] G = 0)
    (houtside : ∀ r ∈ T, MvPolynomial.eval ![1,r] H ≠ 0) :
    g + T.card ≤ (binaryGcd F G).totalDegree := by
  letI : NormalizedGCDMonoid (MvPolynomial (Fin 2) K) := Classical.arbitrary _
  let P := H * ∏ r ∈ T, a2_affineRootFactor r
  have hPF : P ∣ F := a2_augment_binary_divisor H F L hF hHF T hrootsF houtside
  have hPG : P ∣ G := a2_augment_binary_divisor H G L hG hHG T hrootsG houtside
  have hP0 : P ≠ 0 := mul_ne_zero hH0 (Finset.prod_ne_zero_iff.mpr
    (fun r _ => a2_affineRootFactor_ne_zero r))
  have hPh : P.IsHomogeneous (g+T.card) := by
    have hh := hH.mul (MvPolynomial.IsHomogeneous.prod T
      a2_affineRootFactor (fun _ => 1)
      (fun r _ => a2_affineRootFactor_homogeneous r))
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using hh
  have hgcd0 : gcd F G ≠ 0 := by
    intro he
    rcases hnonzero with hF0 | hG0
    · exact hF0 (by simpa [he] using gcd_dvd_left F G)
    · exact hG0 (by simpa [he] using gcd_dvd_right F G)
  change g+T.card ≤ (gcd F G).totalDegree
  rw [← hPh.totalDegree hP0]
  exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain (dvd_gcd hPF hPG) hgcd0


/-- Field extension preserves the rank of the actual square matrix. -/
theorem a2_rank_identity_block {K : Type*} [Field K] (r s : ℕ) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K)
      (0 : Matrix (Fin r) (Fin s) K) (0 : Matrix (Fin s) (Fin r) K) 0).rank = r := by
  let d : Fin r ⊕ Fin s → K := Sum.elim (fun _ => 1) (fun _ => 0)
  have hd : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K)
      (0 : Matrix (Fin r) (Fin s) K) 0 0 = Matrix.diagonal d := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.diagonal, d, Matrix.one_apply]
  let e : {i : Fin r ⊕ Fin s // d i ≠ 0} ≃ Fin r :=
    { toFun := fun i => match i with
        | ⟨Sum.inl j, _⟩ => j
        | ⟨Sum.inr _, h⟩ => False.elim (h rfl)
      invFun := fun j => ⟨Sum.inl j, one_ne_zero⟩
      left_inv := fun i => by
        obtain ⟨i, hi⟩ := i
        cases i with
        | inl j => rfl
        | inr j => exact False.elim (hi rfl)
      right_inv := fun j => rfl }
  rw [hd, Matrix.rank_diagonal, Fintype.card_congr e, Fintype.card_fin]

theorem a2_matrix_rank_map {K k : Type*} [Field K] [Field k]
    (φ : K →+* k) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (M.map φ).rank = M.rank := by
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form M
  have hVdet : IsUnit (V.map φ).det := by
    change IsUnit (φ.mapMatrix V).det
    rw [← φ.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det V).mp hV).map φ
  have hUdet : IsUnit (U.map φ).det := by
    change IsUnit (φ.mapMatrix U).det
    rw [← φ.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det U).mp hU).map φ
  have hmap : V.map φ * M.map φ * U.map φ =
      (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) k)
        (0 : Matrix (Fin M.rank) (Fin (Fintype.card (Fin n)-M.rank)) k) 0 0).submatrix e e := by
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) K => A.map φ) hnormal
    rw [Matrix.map_mul, Matrix.map_mul] at he
    refine he.trans ?_
    ext i j
    cases h₁ : e i <;> cases h₂ : e j <;>
      simp [Matrix.map_apply, Matrix.submatrix, Matrix.fromBlocks, h₁, h₂, Matrix.one_apply]
  calc
    (M.map φ).rank = (V.map φ * M.map φ * U.map φ).rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUdet,
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVdet]
    _ = M.rank := by
      rw [hmap, Matrix.rank_submatrix]
      exact a2_rank_identity_block _ _


/-- The full-degree residue divisor and the outside simple roots give a
complex gcd-degree gain after the rank-preserving scalar extension. -/
theorem a2_binary_gcd_degree_map (hsylvester : A2SylvesterRank)
    {K k : Type} [Field K] [Field k] (φ : K →+* k)
    (F G : MvPolynomial (Fin 2) K) (L : ℕ) (hL : 1 ≤ L)
    (hF : F.IsHomogeneous L) (hG : G.IsHomogeneous L)
    (hnonzero : F ≠ 0 ∨ G ≠ 0) :
    (binaryGcd (MvPolynomial.map φ F) (MvPolynomial.map φ G)).totalDegree =
      (binaryGcd F G).totalDegree := by
  have hinj : Function.Injective (MvPolynomial.map (σ := Fin 2) φ) :=
    MvPolynomial.map_injective φ (RingHom.injective φ)
  have hnmap : MvPolynomial.map φ F ≠ 0 ∨ MvPolynomial.map φ G ≠ 0 := by
    rcases hnonzero with hF0 | hG0
    · exact Or.inl (fun hz => hF0 (hinj (hz.trans (map_zero _).symm)))
    · exact Or.inr (fun hz => hG0 (hinj (hz.trans (map_zero _).symm)))
  have hsrc := hsylvester K L hL F G hF hG hnonzero
  have htgt := hsylvester k L hL (MvPolynomial.map φ F) (MvPolynomial.map φ G)
    (hF.map φ) (hG.map φ) hnmap
  have hrank := a2_matrix_rank_map φ (sylvesterMatrix L F G)
  rw [sylvesterMatrix_map, hsrc, htgt] at hrank
  have hsrcdegree := binary_gcd_degree_le F G L hF hG
  have htgtdegree := binary_gcd_degree_le (MvPolynomial.map φ F)
    (MvPolynomial.map φ G) L (hF.map φ) (hG.map φ)
  omega

theorem a2_complex_gcd_gain_of_limit (hsylvester : A2SylvesterRank)
    {k : Type} [Field k] (cMap : ℂ →+* k)
    (F G : Poly 2) (L g q : ℕ) (hL : 1 ≤ L)
    (hF : F.IsHomogeneous L) (hG : G.IsHomogeneous L)
    (hnonzero : F ≠ 0 ∨ G ≠ 0)
    (H : MvPolynomial (Fin 2) k) (hH : H.IsHomogeneous g) (hH0 : H ≠ 0)
    (hHF : H ∣ MvPolynomial.map cMap F) (hHG : H ∣ MvPolynomial.map cMap G)
    (T : Finset ℂ)
    (hrootsF : ∀ r ∈ T, MvPolynomial.eval ![1,r] F = 0)
    (hrootsG : ∀ r ∈ T, MvPolynomial.eval ![1,r] G = 0)
    (hcap : ∀ (n : ℕ) (r : Fin n → ℂ), Function.Injective r →
      (∀ i, r i ∈ T) → (∀ i, MvPolynomial.eval ![1,cMap (r i)] H = 0) → n ≤ q) :
    g + T.card ≤ (binaryGcd F G).totalDegree + q := by
  let Z := T.filter (fun r => MvPolynomial.eval ![1,cMap r] H = 0)
  let Tout := T.filter (fun r => MvPolynomial.eval ![1,cMap r] H ≠ 0)
  let e : Fin Z.card ≃ Z := Z.equivFin.symm
  have hZ : Z.card ≤ q := hcap Z.card (fun i => (e i).val)
    (Subtype.val_injective.comp e.injective)
    (fun i => (Finset.mem_filter.mp (e i).property).1)
    (fun i => (Finset.mem_filter.mp (e i).property).2)
  have hsum : Z.card + Tout.card = T.card :=
    Finset.card_filter_add_card_filter_not (fun r => MvPolynomial.eval ![1,cMap r] H = 0)
  have hinj : Function.Injective (MvPolynomial.map (σ := Fin 2) cMap) :=
    MvPolynomial.map_injective cMap (RingHom.injective cMap)
  have hnmap : MvPolynomial.map cMap F ≠ 0 ∨ MvPolynomial.map cMap G ≠ 0 := by
    rcases hnonzero with hF0 | hG0
    · exact Or.inl (fun hz => hF0 (hinj (hz.trans (map_zero _).symm)))
    · exact Or.inr (fun hz => hG0 (hinj (hz.trans (map_zero _).symm)))
  have hrootmap (P : Poly 2) (r : ℂ) (hr : MvPolynomial.eval ![1,r] P = 0) :
      MvPolynomial.eval ![1,cMap r] (MvPolynomial.map cMap P) = 0 := by
    have he := a2_binary_eval_map cMap P 1 r
    simpa only [map_one, hr, map_zero] using he.symm
  have hgain := a2_binary_common_divisor_gain
    (MvPolynomial.map cMap F) (MvPolynomial.map cMap G) H L g
    (hF.map cMap) (hG.map cMap) hnmap hH hH0 hHF hHG (Tout.image cMap)
    (by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
      exact hrootmap F r (hrootsF r (Finset.mem_filter.mp hr).1))
    (by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
      exact hrootmap G r (hrootsG r (Finset.mem_filter.mp hr).1))
    (by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
      exact (Finset.mem_filter.mp hr).2)
  rw [Finset.card_image_of_injective _ (RingHom.injective cMap),
    a2_binary_gcd_degree_map hsylvester cMap F G L hL hF hG hnonzero] at hgain
  omega


/-- The paper's wide-depth rank loss, with the frozen Sylvester identity
passed explicitly for an independently auditable upstream dependency. -/
theorem a2_wide_rank_loss_package (hsylvester : A2SylvesterRank)
    {d : ℕ} (X : AffineVariety d) (hX : X.IsIrreducible)
    (J : AffineFamily.Family d) (l : ℕ) (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l)
    (Y : AffineVariety d) (hY : Y ∈ J) (E : Set (Poly d)) (L q r : ℕ)
    (hL : 1 ≤ L) (hrL : r ≤ L) (hgap : 2*q+8 ≤ r)
    (hE : ∀ f ∈ E, f.totalDegree ≤ L)
    (hcomponents : ∀ Z ∈ J, Z.IsComponentOf (Ideal.span E))
    (hgeneric : GenericMovingRootBound X Y J q)
    (S : Finset (Point d)) (hS : ∀ p ∈ S, p ∈ X.points)
    (himages : ∀ p ∈ S, (radialImage p Y).dimension = l) :
    ∃ (A : Matrix (Fin (2*L)) (Fin (2*L)) (Poly d)) (ρ : ℕ),
      L ≤ ρ ∧ ρ ≤ 2*L ∧ (∀ i j, (A i j).totalDegree ≤ L) ∧ GenericMatrixRank X A ρ ∧
      ∀ p ∈ S, r < groupDepth p J Y →
        Matrix.rank (fun i j => MvPolynomial.eval p (A i j)) ≤ ρ-r/2 := by
  letI : X.ideal.IsPrime := hX
  by_cases hSnon : S.Nonempty
  swap
  · refine ⟨1, 2*L, by omega, le_rfl, ?_, ?_, ?_⟩
    · intro i j
      by_cases he : i = j <;> simp [Matrix.one_apply, he]
    · apply a2_genericMatrixRank_of_fraction_rank X hX
        (1 : Matrix (Fin (2*L)) (Fin (2*L)) (Poly d)) (2*L)
      simp
    · intro p hp _
      exact False.elim (hSnon ⟨p, hp⟩)
  let R := Poly d ⧸ X.ideal
  let K₀ := FractionRing R
  let η₀ : Poly d →ₐ[ℂ] K₀ := (IsScalarTower.toAlgHom ℂ R K₀).comp
    (Ideal.Quotient.mkₐ ℂ X.ideal)
  obtain ⟨y, U, F, G, hy, hUnot, hcap, hFs, hGs, hFh, hGh, hFd, hGd,
      hF0, hdivfull, hactual⟩ :=
    a2_full_system_binary_forms X hX J hl hJ Y hY E L q hE hcomponents
      hgeneric S hSnon himages
  have hker₀ (P : Poly d) : η₀ P = 0 ↔ P ∈ X.ideal := by
    change algebraMap R K₀ (Ideal.Quotient.mk X.ideal P) = 0 ↔ _
    rw [map_eq_zero_iff (algebraMap R K₀) (IsFractionRing.injective R K₀),
      Ideal.Quotient.eq_zero_iff_mem]
  have hnonzero : ∃ p ∈ X.points, specializeBinary F p ≠ 0 ∨ specializeBinary G p ≠ 0 := by
    obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hF0
    have hnot : F.coeff m ∉ X.ideal := by
      intro hi
      apply hm
      rw [MvPolynomial.coeff_map]
      exact (hker₀ _).mpr hi
    rw [← X.vanishingIdeal_points, MvPolynomial.mem_vanishingIdeal_iff] at hnot
    push Not at hnot
    obtain ⟨p, hp, hpm⟩ := hnot
    refine ⟨p, hp, Or.inl ?_⟩
    intro hz
    apply hpm
    have hc := congrArg (fun P : Poly 2 => P.coeff m) hz
    simpa [specializeBinary, MvPolynomial.coeff_map, MvPolynomial.aeval_eq_eval] using hc
  let K := AlgebraicClosure K₀
  let κ : K₀ →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ K₀ K
  let η : Poly d →ₐ[ℂ] K := κ.comp η₀
  have hker (P : Poly d) : η P = 0 ↔ P ∈ X.ideal := by
    change κ.toRingHom (η₀ P) = 0 ↔ _
    rw [map_eq_zero_iff κ.toRingHom (RingHom.injective κ.toRingHom), hker₀]
  have hmap (P : BinaryForm d) :
      MvPolynomial.map κ.toRingHom (MvPolynomial.map η₀.toRingHom P) =
        MvPolynomial.map η.toRingHom P := by
    rw [MvPolynomial.map_map]
    rfl
  let D₀ := binaryGcd (MvPolynomial.map η₀.toRingHom F) (MvPolynomial.map η₀.toRingHom G)
  let g := genericGcdDegree X hX F G
  letI : NormalizedGCDMonoid (MvPolynomial (Fin 2) K₀) := Classical.arbitrary _
  have hD₀F : D₀ ∣ MvPolynomial.map η₀.toRingHom F := gcd_dvd_left _ _
  have hD₀G : D₀ ∣ MvPolynomial.map η₀.toRingHom G := gcd_dvd_right _ _
  have hD₀0 : D₀ ≠ 0 := by
    intro hz
    exact hF0 (by simpa [hz] using hD₀F)
  have hD₀h : D₀.IsHomogeneous g :=
    OAI.Nagata.Workers.W30.homogeneous_of_dvd hF0 (hFh.map η₀.toRingHom) hD₀F
  let D := MvPolynomial.map κ.toRingHom D₀
  have hD0 : D ≠ 0 := by
    intro hz
    exact hD₀0 ((MvPolynomial.map_injective κ.toRingHom
      (RingHom.injective κ.toRingHom)) (hz.trans (map_zero _).symm))
  have hDh : D.IsHomogeneous g := hD₀h.map κ.toRingHom
  have hDF : D ∣ MvPolynomial.map η.toRingHom F :=
    (hmap F) ▸ map_dvd (MvPolynomial.map κ.toRingHom) hD₀F
  have hDG : D ∣ MvPolynomial.map η.toRingHom G :=
    (hmap G) ▸ map_dvd (MvPolynomial.map κ.toRingHom) hD₀G
  have hdiv : ∀ P ∈ E, D ∣ MvPolynomial.map η.toRingHom (a2_lineForm y P L) := by
    intro P hP
    have hd := (hdivfull D₀).mp (dvd_refl D₀) P hP
    exact (hmap (a2_lineForm y P L)) ▸ map_dvd (MvPolynomial.map κ.toRingHom) hd
  apply a2_rank_loss_of_binary_forms hsylvester X hX J Y L r hL S F G
    hFh hGh hFd hGd hnonzero
  intro p hp hdepth
  by_cases hz : specializeBinary F p = 0 ∧ specializeBinary G p = 0
  · exact Or.inr hz
  apply Or.inl
  have hnactual : specializeBinary F p ≠ 0 ∨ specializeBinary G p ≠ 0 := by tauto
  obtain ⟨hpy, hfinite, hcard, huniq⟩ := hactual p hp
  obtain ⟨T, hTcard, hTend, hTroot, hTuniq⟩ :=
    a2_distinguished_parameter_list J Y E hcomponents p y hpy hfinite hcard huniq
  obtain ⟨A, φ, H₀, hH₀0, hH₀h, hH₀F, hH₀G, hcaplimit⟩ :=
    a2_point_limit_with_support X J η hker E L q hE y U
      (fun hz => hUnot ((hker U).mp hz)) hcap F G D g hDh hD0 hDF hDG hdiv p (hS p hp)
  let cMap : ℂ →+* IsLocalRing.ResidueField A :=
    (IsLocalRing.residue A).comp (φ.comp (algebraMap ℂ R))
  have hFroots (t : ℂ) (ht : t ∈ T) :
      MvPolynomial.eval ![1,t] (specializeBinary F p) = 0 := by
    rw [specializeBinary, ← MvPolynomial.eval₂_eq_eval_map]
    apply a2_lineForm_span_root y E L hE F hFs p t
    intro P hP
    exact hTroot t ht P hP
  have hGroots (t : ℂ) (ht : t ∈ T) :
      MvPolynomial.eval ![1,t] (specializeBinary G p) = 0 := by
    rw [specializeBinary, ← MvPolynomial.eval₂_eq_eval_map]
    apply a2_lineForm_span_root y E L hE G hGs p t
    intro P hP
    exact hTroot t ht P hP
  have hgain := a2_complex_gcd_gain_of_limit hsylvester cMap
    (specializeBinary F p) (specializeBinary G p) L g q hL
    (hFh.map (MvPolynomial.eval p)) (hGh.map (MvPolynomial.eval p)) hnactual
    H₀ hH₀h hH₀0 hH₀F hH₀G T hFroots hGroots
    (by
      intro n t ht hT htroot
      exact hcaplimit n t ht (fun i => (hTend _ (hT i)).1)
        (fun i => (hTend _ (hT i)).2) htroot (fun i => hTuniq _ (hT i)))
  rw [hTcard] at hgain
  change g + r/2 ≤ _
  omega


end
end DistinctDistances.TrackA
