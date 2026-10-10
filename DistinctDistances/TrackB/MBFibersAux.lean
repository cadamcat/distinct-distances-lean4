import DistinctDistances.TrackB.SkewPencil
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace DistinctDistances.TrackB.MBFibersAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LinearMap (BilinForm)

variable {n : ℕ}

/-- Elementary skew pair on coordinates. -/
noncomputable def skewPair (n : ℕ) (i j : Fin n) : BilinForm ℂ (Fin n → ℂ) :=
  LinearMap.BilinForm.linMulLin (LinearMap.proj i) (LinearMap.proj j) -
    LinearMap.BilinForm.linMulLin (LinearMap.proj j) (LinearMap.proj i)

theorem skewPair_isAlt (n : ℕ) (i j : Fin n) : (skewPair n i j).IsAlt := by
  intro x
  simp only [skewPair, LinearMap.sub_apply, LinearMap.BilinForm.linMulLin_apply,
    LinearMap.proj_apply]
  ring

theorem skewPair_apply (n : ℕ) (i j k l : Fin n) :
    skewPair n i j (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ) =
      (if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
        (if j = k then (1 : ℂ) else 0) * (if i = l then (1 : ℂ) else 0) := by
  simp only [skewPair, LinearMap.sub_apply, LinearMap.BilinForm.linMulLin_apply,
    LinearMap.proj_apply, Pi.single_apply]

/-- Basis element for an ordered pair. -/
noncomputable def skewElt (n : ℕ) (p : {x : Fin n × Fin n // x.1 < x.2}) :
    ↥(DistinctDistances.TrackB.alternatingForms (U := Fin n → ℂ)) :=
  ⟨skewPair n p.1.1 p.1.2, skewPair_isAlt n _ _⟩

/-- Kronecker evaluation on ordered single vectors. -/
theorem skewElt_eval (n : ℕ) (p q : {x : Fin n × Fin n // x.1 < x.2}) :
    skewPair n p.1.1 p.1.2 (Pi.single q.1.1 1 : Fin n → ℂ)
      (Pi.single q.1.2 1 : Fin n → ℂ) = (if p = q then (1 : ℂ) else 0) := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  obtain ⟨⟨k, l⟩, hkl⟩ := q
  dsimp only at hij hkl ⊢
  rw [skewPair_apply]
  have hsecond : (if j = k then (1 : ℂ) else 0) * (if i = l then (1 : ℂ) else 0) = 0 := by
    by_cases hjk : j = k
    · by_cases hil : i = l
      · subst hjk
        subst hil
        exact False.elim (lt_asymm hkl hij)
      · simp [hil]
    · simp [hjk]
  rw [hsecond, sub_zero]
  have hiff : (⟨(i, j), hij⟩ : {x : Fin n × Fin n // x.1 < x.2}) =
      (⟨(k, l), hkl⟩ : {x : Fin n × Fin n // x.1 < x.2}) ↔ (i = k ∧ j = l) := by
    constructor
    · intro h
      have hval : (i, j) = (k, l) := congrArg Subtype.val h
      simpa using hval
    · rintro ⟨rfl, rfl⟩
      rfl
  by_cases hconj : i = k ∧ j = l
  · have hpq : (⟨(i, j), hij⟩ : {x : Fin n × Fin n // x.1 < x.2}) =
        (⟨(k, l), hkl⟩ : {x : Fin n × Fin n // x.1 < x.2}) := hiff.mpr hconj
    obtain ⟨rfl, rfl⟩ := hconj
    simp [hpq]
  · have hpq : ¬ (⟨(i, j), hij⟩ : {x : Fin n × Fin n // x.1 < x.2}) =
        (⟨(k, l), hkl⟩ : {x : Fin n × Fin n // x.1 < x.2}) := fun h => hconj (hiff.mp h)
    simp only [hpq, ite_false]
    by_cases hik : i = k
    · have hjl : j ≠ l := fun hjl => hconj ⟨hik, hjl⟩
      simp [hik, hjl]
    · simp [hik]

/-- Evaluation functional at a pair of single vectors. -/
noncomputable def skewEval (n : ℕ) (q : {x : Fin n × Fin n // x.1 < x.2}) :
    Module.Dual ℂ ↥(DistinctDistances.TrackB.alternatingForms (U := Fin n → ℂ)) where
  toFun := fun D => D.1 (Pi.single q.1.1 1 : Fin n → ℂ) (Pi.single q.1.2 1 : Fin n → ℂ)
  map_add' := by
    intro a b
    rfl
  map_smul' := by
    intro a b
    rfl

theorem skewElt_dual (n : ℕ) (p q : {x : Fin n × Fin n // x.1 < x.2}) :
    skewEval n q (skewElt n p) = (if q = p then (1 : ℂ) else 0) := by
  simp only [skewEval, skewElt]
  have h := skewElt_eval n p q
  by_cases heq : q = p
  · subst heq
    simp [h]
  · simp [heq, Ne.symm heq] at h ⊢
    exact h

theorem skewElt_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (skewElt n) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one (skewElt n) (skewEval n)
  · intro i j hij
    simp only [skewElt_dual]
    simp [hij]
  · intro i
    simp [skewElt_dual]

/-- The skew elements span all alternating forms. -/
theorem skewElt_span (n : ℕ) :
    Submodule.span ℂ (Set.range (skewElt n)) = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro D
  let c : {x : Fin n × Fin n // x.1 < x.2} → ℂ := fun p =>
    D.1 (Pi.single p.1.1 1 : Fin n → ℂ) (Pi.single p.1.2 1 : Fin n → ℂ)
  let S : ↥(DistinctDistances.TrackB.alternatingForms (U := Fin n → ℂ)) :=
    ∑ p : {x : Fin n × Fin n // x.1 < x.2}, c p • skewElt n p
  have hS_mem : S ∈ Submodule.span ℂ (Set.range (skewElt n)) := by
    apply Submodule.sum_mem
    intro p _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨p, rfl⟩
  have hDS : D = S := by
    apply Subtype.ext
    apply LinearMap.BilinForm.ext_basis (Pi.basisFun ℂ (Fin n))
    intro k l
    have hbasis : ∀ m : Fin n, Pi.basisFun ℂ (Fin n) m = (Pi.single m 1 : Fin n → ℂ) := by
      intro m
      simp [Pi.basisFun_apply]
    rw [hbasis k, hbasis l]
    have hval : (S : BilinForm ℂ (Fin n → ℂ)) =
        ∑ p : {x : Fin n × Fin n // x.1 < x.2},
          c p • (((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ))) := by
      simp [S]
    have heval : ∀ k l : Fin n, (S : BilinForm ℂ (Fin n → ℂ))
        (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ) =
        ∑ p : {x : Fin n × Fin n // x.1 < x.2},
          c p * ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
          (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ)) := by
      intro k l
      rw [hval]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [heval]
    show D.1 (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ) = _
    have hc_def : ∀ p : {x : Fin n × Fin n // x.1 < x.2}, c p =
        D.1 (Pi.single p.1.1 1 : Fin n → ℂ) (Pi.single p.1.2 1 : Fin n → ℂ) := fun p => rfl
    -- case analysis on k l
    by_cases hkl : k = l
    · subst hkl
      have hD0 : D.1 (Pi.single k 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ) = 0 :=
        D.2 _
      rw [hD0]
      symm
      apply Finset.sum_eq_zero
      intro p _
      have hBp0 : ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
          (Pi.single k 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ)) = 0 := by
        have h : skewPair n p.1.1 p.1.2
            (Pi.single k 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ) = 0 :=
          (skewPair_isAlt n p.1.1 p.1.2) _
        have hcoe : ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
            (Pi.single k 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ)) =
            skewPair n p.1.1 p.1.2
              (Pi.single k 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ) := rfl
        rw [hcoe]
        exact h
      simp only [hBp0, mul_zero]
    · by_cases hlt : k < l
      · let q : {x : Fin n × Fin n // x.1 < x.2} := ⟨(k, l), hlt⟩
        have hsum : (∑ p : {x : Fin n × Fin n // x.1 < x.2},
            D.1 (Pi.single p.1.1 1 : Fin n → ℂ)
            (Pi.single p.1.2 1 : Fin n → ℂ) *
            ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ))) =
            D.1 (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ) := by
          have hkr : ∀ p : {x : Fin n × Fin n // x.1 < x.2},
              D.1 (Pi.single p.1.1 1 : Fin n → ℂ)
                (Pi.single p.1.2 1 : Fin n → ℂ) *
              ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
                (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ)) =
              (if p = q then D.1 (Pi.single k 1 : Fin n → ℂ)
                (Pi.single l 1 : Fin n → ℂ) else 0) := by
            intro p
            have hB : ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
                (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ)) =
                (if p = q then (1 : ℂ) else 0) := by
              have h := skewElt_eval n p q
              have hq1 : (q : {x : Fin n × Fin n // x.1 < x.2}).1.1 = k := rfl
              have hq2 : (q : {x : Fin n × Fin n // x.1 < x.2}).1.2 = l := rfl
              rw [hq1, hq2] at h
              exact h
            rw [hB]
            by_cases hpq : p = q
            · subst hpq
              simp [q]
            · simp [hpq]
          simp only [hkr]
          simp
        -- rewrite c unfolding to match hsum
        have hmatch : (∑ p : {x : Fin n × Fin n // x.1 < x.2},
            c p * ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ))) =
            (∑ p : {x : Fin n × Fin n // x.1 < x.2},
            D.1 (Pi.single p.1.1 1 : Fin n → ℂ)
            (Pi.single p.1.2 1 : Fin n → ℂ) *
            ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ))) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [hc_def]
        rw [hmatch]
        exact hsum.symm
      · have hgt : l < k := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hkl)
        let q : {x : Fin n × Fin n // x.1 < x.2} := ⟨(l, k), hgt⟩
        have hDswap : D.1 (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ) =
            - D.1 (Pi.single l 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ) := by
          have h := D.2.neg_eq (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ)
          calc
            D.1 _ _ = - - D.1 _ _ := (neg_neg _).symm
            _ = - D.1 _ _ := by rw [h]
        have hBswap : ∀ p : {x : Fin n × Fin n // x.1 < x.2},
            ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ)) =
            - ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single l 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ)) := by
          intro p
          have h := (skewPair_isAlt n p.1.1 p.1.2).neg_eq
            (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ)
          have hcoe : ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ)) =
              skewPair n p.1.1 p.1.2
                (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ) := rfl
          have hcoe2 : ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single l 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ)) =
              skewPair n p.1.1 p.1.2
                (Pi.single l 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ) := rfl
          rw [hcoe, hcoe2]
          calc
            skewPair n p.1.1 p.1.2 _ _ = - - skewPair n p.1.1 p.1.2 _ _ := (neg_neg _).symm
            _ = - skewPair n p.1.1 p.1.2 _ _ := by rw [h]
        have hsum : (∑ p : {x : Fin n × Fin n // x.1 < x.2},
            D.1 (Pi.single p.1.1 1 : Fin n → ℂ)
            (Pi.single p.1.2 1 : Fin n → ℂ) *
            ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ))) =
            D.1 (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ) := by
          rw [hDswap]
          have hkr : ∀ p : {x : Fin n × Fin n // x.1 < x.2},
              D.1 (Pi.single p.1.1 1 : Fin n → ℂ)
                (Pi.single p.1.2 1 : Fin n → ℂ) *
              (- ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
                (Pi.single l 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ))) =
              (if p = q then - D.1 (Pi.single l 1 : Fin n → ℂ)
                (Pi.single k 1 : Fin n → ℂ) else 0) := by
            intro p
            have hB : ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
                (Pi.single l 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ)) =
                (if p = q then (1 : ℂ) else 0) := by
              have h := skewElt_eval n p q
              have hq1 : (q : {x : Fin n × Fin n // x.1 < x.2}).1.1 = l := rfl
              have hq2 : (q : {x : Fin n × Fin n // x.1 < x.2}).1.2 = k := rfl
              rw [hq1, hq2] at h
              have hcoe : ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
                  (Pi.single l 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ)) =
                  skewPair n p.1.1 p.1.2
                    (Pi.single l 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ) := rfl
              rw [hcoe]
              exact h
            rw [hB]
            by_cases hpq : p = q
            · subst hpq
              simp [q]
            · simp [hpq]
          have hrewrite : (∑ p : {x : Fin n × Fin n // x.1 < x.2},
              D.1 (Pi.single p.1.1 1 : Fin n → ℂ)
              (Pi.single p.1.2 1 : Fin n → ℂ) *
              ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
                (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ))) =
              (∑ p : {x : Fin n × Fin n // x.1 < x.2},
              D.1 (Pi.single p.1.1 1 : Fin n → ℂ)
              (Pi.single p.1.2 1 : Fin n → ℂ) *
              (- ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
                (Pi.single l 1 : Fin n → ℂ) (Pi.single k 1 : Fin n → ℂ)))) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [hBswap p]
          rw [hrewrite]
          simp only [hkr]
          simp
        have hmatch : (∑ p : {x : Fin n × Fin n // x.1 < x.2},
            c p * ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ))) =
            (∑ p : {x : Fin n × Fin n // x.1 < x.2},
            D.1 (Pi.single p.1.1 1 : Fin n → ℂ)
            (Pi.single p.1.2 1 : Fin n → ℂ) *
            ((((skewElt n p).1 : BilinForm ℂ (Fin n → ℂ)))
              (Pi.single k 1 : Fin n → ℂ) (Pi.single l 1 : Fin n → ℂ))) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [hc_def]
        rw [hmatch]
        exact hsum.symm
  exact hDS ▸ hS_mem

/-- Explicit basis for alternating forms on coordinates. -/
noncomputable def skewBasis (n : ℕ) :
    Module.Basis {x : Fin n × Fin n // x.1 < x.2} ℂ
      ↥(DistinctDistances.TrackB.alternatingForms (U := Fin n → ℂ)) :=
  Module.Basis.mk (skewElt_linearIndependent n) (by simp [skewElt_span n])

/-- Finrank of alternating forms on `Fin n`. -/
theorem finrank_skewFin (n : ℕ) :
    Module.finrank ℂ ↥(DistinctDistances.TrackB.alternatingForms (U := Fin n → ℂ)) =
      n.choose 2 := by
  classical
  have h := Module.finrank_eq_card_basis (skewBasis n)
  rw [h]
  have hcard : Fintype.card {x : Fin n × Fin n // x.1 < x.2} = n.choose 2 := by
    rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]
  exact hcard

section General

variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

/-- Transfer alternating forms along a linear equivalence (preserves `IsAlt`). -/
noncomputable def altCongr (E : U ≃ₗ[ℂ] (Fin (Module.finrank ℂ U) → ℂ)) :
    ↥(DistinctDistances.TrackB.alternatingForms (U := U)) ≃ₗ[ℂ]
      ↥(DistinctDistances.TrackB.alternatingForms
        (U := Fin (Module.finrank ℂ U) → ℂ)) where
  toFun D := ⟨LinearMap.BilinForm.congr E D.1, fun x => D.2 (E.symm x)⟩
  invFun D := ⟨LinearMap.BilinForm.congr E.symm D.1, fun x => D.2 (E x)⟩
  left_inv D := by
    apply Subtype.ext
    show LinearMap.BilinForm.congr E.symm
      (LinearMap.BilinForm.congr E D.1) = D.1
    rw [LinearMap.BilinForm.congr_congr, E.self_trans_symm,
      LinearMap.BilinForm.congr_refl]
    rfl
  right_inv D := by
    apply Subtype.ext
    show LinearMap.BilinForm.congr E
      (LinearMap.BilinForm.congr E.symm D.1) = D.1
    rw [LinearMap.BilinForm.congr_congr, E.symm_trans_self,
      LinearMap.BilinForm.congr_refl]
    rfl
  map_add' := by
    intro a b
    apply Subtype.ext
    simp [map_add]
  map_smul' := by
    intro a b
    apply Subtype.ext
    simp [map_smul]

/-- Finrank of alternating forms over a general finite-dimensional `U`. -/
theorem finrank_alternatingForms :
    Module.finrank ℂ ↥(DistinctDistances.TrackB.alternatingForms (U := U)) =
      (Module.finrank ℂ U).choose 2 := by
  classical
  let E : U ≃ₗ[ℂ] (Fin (Module.finrank ℂ U) → ℂ) :=
    LinearEquiv.ofFinrankEq U _ (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
  have h := (altCongr E).finrank_eq
  rw [finrank_skewFin] at h
  exact h

end General

end DistinctDistances.TrackB.MBFibersAux
