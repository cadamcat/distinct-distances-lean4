import DistinctDistances.TrackD.Profiles.RankResult
import DistinctDistances.TrackD.Profiles.DProfiles2Aux

/-!
# `prof:budget` (`profiles.tex:220–324`)

Degree budgets, mass budgets, rank propagation, and the balance of profiles. Consumers:
`secants.tex:211–215`, `depth.tex:91–101`, `sparse-cones.tex:127–141`, `profiles.tex:552–555`.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

set_option maxHeartbeats 500000 in
/-- `prof:budget.balance` (`profiles.tex:317–323`, eq. `prof:balance`), arithmetic form with
explicit margins. A monotone profile with `|Σ t_i| ≤ θ₀` and `max |t_i| ≥ 1/2 - θ₀` has
`t_1 ≤ -c`, `t_d ≥ c` and `t_1 + t_2 ≤ -c` for a `c > 0` depending only on `d ≥ 3`. -/
theorem prof_budget_balance_arith (d : ℕ) (hd : 3 ≤ d) :
    ∃ c θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧ ∀ t : Fin d → ℝ, Monotone t →
      |∑ i, t i| ≤ θ₀ → (∃ i, 1 / 2 - θ₀ ≤ |t i|) →
        t ⟨0, by omega⟩ ≤ -c ∧ c ≤ t ⟨d - 1, by omega⟩ ∧
        t ⟨0, by omega⟩ + t ⟨1, by omega⟩ ≤ -c := by
  let c : ℝ := 1 / (64 * (d : ℝ))
  let θ₀ : ℝ := c
  have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
  have hc : 0 < c := by dsimp [c]; positivity
  have hθ : 0 < θ₀ := by simpa [θ₀] using hc
  have hθsmall : θ₀ ≤ 1 / 192 := by
    dsimp [θ₀, c]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 192)
    nlinarith [hdR]
  have hmargin : 1 / 2 - θ₀ ≥ 1 / 3 := by linarith
  have hdc : (d : ℝ) * c = 1 / 64 := by
    dsimp [c]
    field_simp
  refine ⟨c, θ₀, hc, hθ, ?_⟩
  intro t hmono hsum hlarge
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let i2 : Fin d := ⟨2, by omega⟩
  let ilast : Fin d := ⟨d - 1, by omega⟩
  let S : ℝ := ∑ i, t i
  have hSabs : |S| ≤ θ₀ := by simpa [S] using hsum
  have hSlo : -θ₀ ≤ S := (abs_le.mp hSabs).1
  have hShi : S ≤ θ₀ := (abs_le.mp hSabs).2
  have hsplit (i : Fin d) :
      (∑ j ∈ Finset.Iio i, t j) + (∑ j ∈ Finset.Ici i, t j) = S := by
    have hu : Finset.Iio i ∪ Finset.Ici i = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici, Finset.mem_univ]
      constructor
      · intro _
        trivial
      · intro _
        exact lt_or_ge j i
    have hdis : Disjoint (Finset.Iio i) (Finset.Ici i) := by
      refine Finset.disjoint_left.mpr ?_
      intro j hj₁ hj₂
      have hj₁' : j < i := by simpa only [Finset.mem_Iio] using hj₁
      have hj₂' : i ≤ j := by simpa only [Finset.mem_Ici] using hj₂
      exact (not_lt_of_ge hj₂') hj₁'
    dsimp [S]
    rw [← Finset.sum_union hdis, hu]
  have hsplit' (i : Fin d) :
      (∑ j ∈ Finset.Iic i, t j) + (∑ j ∈ Finset.Ioi i, t j) = S := by
    have hu : Finset.Iic i ∪ Finset.Ioi i = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioi, Finset.mem_univ]
      constructor
      · intro _
        trivial
      · intro _
        exact le_or_gt j i
    have hdis : Disjoint (Finset.Iic i) (Finset.Ioi i) := by
      refine Finset.disjoint_left.mpr ?_
      intro j hj₁ hj₂
      have hj₁' : j ≤ i := by simpa only [Finset.mem_Iic] using hj₁
      have hj₂' : i < j := by simpa only [Finset.mem_Ioi] using hj₂
      exact (not_lt_of_ge hj₁') hj₂'
    dsimp [S]
    rw [← Finset.sum_union hdis, hu]
  have htailLower (i : Fin d) (h : ℝ)
      (hh : ∀ j ∈ Finset.Ici i, h ≤ t j) :
      ((d - i.val : ℕ) : ℝ) * h ≤ ∑ j ∈ Finset.Ici i, t j := by
    have hs := Finset.sum_le_sum (fun j hj => hh j hj)
    have hcst : (∑ j ∈ Finset.Ici i, h) = ((d - i.val : ℕ) : ℝ) * h := by
      simp [Finset.sum_const]
    rw [hcst] at hs
    exact hs
  have hprefixLower (i : Fin d) (a : ℝ)
      (ha : ∀ j ∈ Finset.Iio i, a ≤ t j) :
      ((i.val : ℝ) * a) ≤ ∑ j ∈ Finset.Iio i, t j := by
    have hs := Finset.sum_le_sum (fun j hj => ha j hj)
    have hcst : (∑ j ∈ Finset.Iio i, a) = (i.val : ℝ) * a := by
      simp [Finset.sum_const]
    rw [hcst] at hs
    exact hs
  have hsumLower (i : Fin d) (a h : ℝ)
      (ha : ∀ j ∈ Finset.Iio i, a ≤ t j)
      (hh : ∀ j ∈ Finset.Ici i, h ≤ t j) :
      (i.val : ℝ) * a + ((d - i.val : ℕ) : ℝ) * h ≤ S := by
    have hp := hprefixLower i a ha
    have ht := htailLower i h hh
    calc
      (i.val : ℝ) * a + ((d - i.val : ℕ) : ℝ) * h ≤
          (∑ j ∈ Finset.Iio i, t j) + (∑ j ∈ Finset.Ici i, t j) := add_le_add hp ht
      _ = S := hsplit i
  have hsumUpper (i : Fin d) (h z : ℝ)
      (hh : ∀ j ∈ Finset.Iic i, t j ≤ -h)
      (hz : ∀ j ∈ Finset.Ioi i, t j ≤ z) :
      S ≤ -((i.val + 1 : ℕ) : ℝ) * h + ((d - i.val - 1 : ℕ) : ℝ) * z := by
    have hpre := Finset.sum_le_sum (fun j hj => hh j hj)
    have htail := Finset.sum_le_sum (fun j hj => hz j hj)
    have hcpre : (∑ j ∈ Finset.Iic i, -(h : ℝ)) = -((i.val + 1 : ℕ) : ℝ) * h := by
      have hcard : (Finset.Iic i).card = i.val + 1 := by simp
      rw [Finset.sum_const]
      rw [nsmul_eq_mul, hcard]
      ring
    have hctail : (∑ j ∈ Finset.Ioi i, (z : ℝ)) = ((d - i.val - 1 : ℕ) : ℝ) * z := by
      have hcard : (Finset.Ioi i).card = d - i.val - 1 := by
        rw [Fin.card_Ioi]
        omega
      rw [Finset.sum_const]
      rw [nsmul_eq_mul, hcard]
    rw [hcpre] at hpre
    rw [hctail] at htail
    rw [← hsplit' i]
    linarith
  have hprefixPair (i : Fin d) (hi : 2 ≤ i.val) :
      t i0 + ((i.val : ℝ) - 1) * t i1 ≤ ∑ j ∈ Finset.Iio i, t j := by
    let D := Finset.Iio i \ {i0}
    have h0 : i0 ∈ Finset.Iio i := by
      have hival : 0 < i.val := by omega
      apply Finset.mem_Iio.mpr
      apply Fin.lt_iff_val_lt_val.mpr
      simpa [i0] using hival
    have hsub : ({i0} : Finset (Fin d)) ⊆ Finset.Iio i := by
      intro j hj
      have : j = i0 := by simpa using hj
      simpa [this] using h0
    have hcard : D.card = i.val - 1 := by
      dsimp [D]
      rw [Finset.card_sdiff_of_subset hsub]
      simp [Fin.card_Iio]
    have hdecomp : ({i0} : Finset (Fin d)) ∪ D = Finset.Iio i := by
      ext j
      simp only [D, Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff]
      constructor
      · rintro (rfl | ⟨hj, hne⟩)
        · simpa using h0
        · exact hj
      · intro hj
        by_cases heq : j = i0
        · exact Or.inl heq
        · exact Or.inr ⟨hj, heq⟩
    have hdis : Disjoint ({i0} : Finset (Fin d)) D := by
      refine Finset.disjoint_left.mpr ?_
      intro j hj₁ hj₂
      have heq : j = i0 := by simpa using hj₁
      exact (Finset.mem_sdiff.mp hj₂).2 (by simpa [heq])
    have hsumD : ((D.card : ℝ) * t i1) ≤ ∑ j ∈ D, t j := by
      have hcst : (∑ j ∈ D, t i1) = (D.card : ℝ) * t i1 := by
        simp [Finset.sum_const]
      have hle := Finset.sum_le_sum (s := D) (by
        intro j hj
        have hjD := Finset.mem_sdiff.mp hj
        have hne : j ≠ i0 := by simpa using hjD.2
        have hjpos : 0 < j.val := by
          have hnz : j.val ≠ 0 := by
            intro heq
            apply hne
            exact Fin.ext (by simpa [i0] using heq)
          exact Nat.pos_of_ne_zero hnz
        have hle : i1 ≤ j := Fin.le_iff_val_le_val.mpr
          (by simpa [i1] using Nat.succ_le_of_lt hjpos)
        exact hmono hle)
      rw [hcst] at hle
      exact hle
    have hsum : (∑ j ∈ Finset.Iio i, t j) = t i0 + ∑ j ∈ D, t j := by
      rw [← hdecomp, Finset.sum_union hdis]
      simp
    have hcardR : (D.card : ℝ) = (i.val : ℝ) - 1 := by
      rw [hcard, Nat.cast_sub (by omega : 1 ≤ i.val)]
      simp
    rw [hcardR] at hsumD
    rw [hsum]
    linarith [hsumD]
  rcases hlarge with ⟨i, hi⟩
  rcases le_total 0 (t i) with hnonneg | hnonpos
  · have hti : 1 / 2 - θ₀ ≤ t i := by rwa [abs_of_nonneg hnonneg] at hi
    have hidx : 1 ≤ i.val := by
      by_contra hnot
      have heq : i.val = 0 := by omega
      have heq' : i = i0 := Fin.ext heq
      subst i
      have ht := hsumLower i0 0 (1 / 2 - θ₀)
        (by
          intro j hj
          have hjlt : j < i0 := Finset.mem_Iio.mp hj
          have : j.val < 0 := Fin.lt_iff_val_lt_val.mp hjlt
          omega)
        (by
          intro j hj
          exact le_trans hti (hmono (Finset.mem_Ici.mp hj)))
      simp [i0] at ht
      have hdpos : 0 < (d : ℝ) := by linarith
      nlinarith [hmargin, hShi, hdpos]
    have hsumPos : (i.val : ℝ) * t i0 + ((d - i.val : ℕ) : ℝ) * (1 / 2 - θ₀) ≤ S :=
      hsumLower i (t i0) (1 / 2 - θ₀)
        (by
          intro j hj
          exact hmono (Fin.le_iff_val_le_val.mpr (by simp [i0])))
        (by
          intro j hj
          exact le_trans hti (hmono (Finset.mem_Ici.mp hj)))
    have hfirst : t i0 ≤ -c := by
      by_contra hnot
      have hgt : -c < t i0 := lt_of_not_ge hnot
      have hnpos : 0 < (i.val : ℝ) := by exact_mod_cast (show 0 < i.val by omega)
      have hprod : -((i.val : ℝ) * c) < (i.val : ℝ) * t i0 :=
        by simpa [mul_neg] using mul_lt_mul_of_pos_left hgt hnpos
      have hile : (i.val : ℝ) * c ≤ (d : ℝ) * c :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_of_lt i.isLt)) hc.le
      have htailCount : ((d - i.val : ℕ) : ℝ) * (1 / 2 - θ₀) ≥ 1 / 3 := by
        have hcount : 1 ≤ d - i.val := by omega
        have hcountR : 1 ≤ ((d - i.val : ℕ) : ℝ) := by exact_mod_cast hcount
        have hmul := mul_le_mul_of_nonneg_left hmargin
          (by positivity : 0 ≤ ((d - i.val : ℕ) : ℝ))
        have hbase : (1 / 3 : ℝ) ≤ ((d - i.val : ℕ) : ℝ) * (1 / 3) := by
          nlinarith [hcountR]
        exact hbase.trans hmul
      have hlow : (1 / 3 : ℝ) - 1 / 64 < S := by
        nlinarith [hsumPos, hdc, htailCount, hile, hprod]
      linarith [hShi, hθsmall]
    have hlast : c ≤ t ilast := by
      have hitail : i ≤ ilast := Fin.le_iff_val_le_val.mpr (by simp [ilast]; omega)
      have hti' : c ≤ t i := by linarith [hti, hmargin]
      exact le_trans hti' (hmono hitail)
    have hpair : t i0 + t i1 ≤ -c := by
      by_cases hidx1 : i.val = 1
      · have heq : i = i1 := Fin.ext hidx1
        subst i
        have hpref2 : (∑ j ∈ Finset.Iio i2, t j) = t i0 + t i1 := by
          have hset : Finset.Iio i2 = ({i0, i1} : Finset (Fin d)) := by
            ext j
            simp only [Finset.mem_Iio, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · intro hj
              have hjv : j.val < 2 := Fin.lt_iff_val_lt_val.mp hj
              rcases (show j.val = 0 ∨ j.val = 1 by omega) with h0 | h1
              · exact Or.inl (Fin.ext h0)
              · exact Or.inr (Fin.ext h1)
            · intro hj
              rcases hj with hj | hj
              · subst j
                simp [i0, i2]
              · subst j
                simp [i1, i2]
          rw [hset]
          simp [Finset.sum_insert, i0, i1]
        have htail2 := htailLower i2 (1 / 2 - θ₀) (by
          intro j hj
          have hi1i2 : i1 ≤ i2 := Fin.le_iff_val_le_val.mpr (by simp [i1, i2])
          exact le_trans hti (hmono (le_trans hi1i2 (Finset.mem_Ici.mp hj))))
        have hs := hsplit i2
        rw [hpref2] at hs
        have hcount : 1 ≤ d - 2 := by omega
        have hcountR : 1 ≤ ((d - 2 : ℕ) : ℝ) := by exact_mod_cast hcount
        have htaillarge : ((d - 2 : ℕ) : ℝ) * (1 / 2 - θ₀) ≥ 1 / 3 := by
          have hmul := mul_le_mul_of_nonneg_left hmargin
            (by positivity : 0 ≤ ((d - 2 : ℕ) : ℝ))
          have hbase : (1 / 3 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) * (1 / 3) := by
            nlinarith [hcountR]
          exact hbase.trans hmul
        by_contra hnot
        have hgt : -c < t i0 + t i1 := lt_of_not_ge hnot
        have hsum' : S ≥ t i0 + t i1 + ((d - 2 : ℕ) : ℝ) * (1 / 2 - θ₀) := by
          have htail' : ((d - 2 : ℕ) : ℝ) * (1 / 2 - θ₀) ≤ ∑ j ∈ Finset.Ici i2, t j := by
            simpa [i2] using htail2
          calc
            t i0 + t i1 + ((d - 2 : ℕ) : ℝ) * (1 / 2 - θ₀) ≤
                t i0 + t i1 + ∑ j ∈ Finset.Ici i2, t j := by linarith
            _ = S := hs
        linarith [hShi, htaillarge, hθsmall]
      · have hidx2 : 2 ≤ i.val := by omega
        have htail := htailLower i (1 / 2 - θ₀) (by
          intro j hj
          exact le_trans hti (hmono (Finset.mem_Ici.mp hj)))
        have hsum' : t i0 + ((i.val : ℝ) - 1) * t i1 +
            ((d - i.val : ℕ) : ℝ) * (1 / 2 - θ₀) ≤ S := by
          have hp := hprefixPair i hidx2
          calc
            t i0 + ((i.val : ℝ) - 1) * t i1 +
                ((d - i.val : ℕ) : ℝ) * (1 / 2 - θ₀) ≤
                (∑ j ∈ Finset.Iio i, t j) + (∑ j ∈ Finset.Ici i, t j) :=
              add_le_add hp htail
            _ = S := hsplit i
        have hmono01 : t i0 ≤ t i1 := hmono (Fin.le_iff_val_le_val.mpr (by simp [i0, i1]))
        have havg : (i.val : ℝ) * (t i0 + t i1) ≤
            2 * (t i0 + ((i.val : ℝ) - 1) * t i1) := by
          have hcoef : 0 ≤ (i.val : ℝ) - 2 := by
            exact_mod_cast (show 0 ≤ i.val - 2 by omega)
          nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hmono01)]
        by_contra hnot
        have hgt : -c < t i0 + t i1 := lt_of_not_ge hnot
        have hnle : (i.val : ℝ) * c ≤ (d : ℝ) * c :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_of_lt i.isLt)) hc.le
        have htailCount : ((d - i.val : ℕ) : ℝ) * (1 / 2 - θ₀) ≥ 1 / 3 := by
          have hcount : 1 ≤ d - i.val := by omega
          have hcountR : 1 ≤ ((d - i.val : ℕ) : ℝ) := by exact_mod_cast hcount
          have hmul := mul_le_mul_of_nonneg_left hmargin
            (by positivity : 0 ≤ ((d - i.val : ℕ) : ℝ))
          have hbase : (1 / 3 : ℝ) ≤ ((d - i.val : ℕ) : ℝ) * (1 / 3) := by
            nlinarith [hcountR]
          exact hbase.trans hmul
        have hprefLower : -((d : ℝ) * c) <
            2 * (t i0 + ((i.val : ℝ) - 1) * t i1) := by
          nlinarith [havg, hgt, hnle]
        linarith [hsum', hShi, htailCount, hdc, hθsmall, hprefLower]
    exact ⟨hfirst, hlast, hpair⟩
  · have hti : t i ≤ -(1 / 2 - θ₀) := by
      have habs : |t i| = -t i := abs_of_nonpos hnonpos
      rw [habs] at hi
      linarith
    have hfirst : t i0 ≤ -c := by
      have hi0 : i0 ≤ i := Fin.le_iff_val_le_val.mpr (by simp [i0])
      have ht0 : t i0 ≤ t i := hmono hi0
      linarith [ht0, hti, hmargin]
    have hlast : c ≤ t ilast := by
      by_cases hidx : i.val = d - 1
      · have heq : i = ilast := Fin.ext hidx
        subst i
        have hti' : t ilast ≤ -(1 / 2 - θ₀) := by simpa [ilast] using hti
        have hsumup : S ≤ -((d : ℝ) * (1 / 2 - θ₀)) := by
          have hle : ∀ j : Fin d, t j ≤ -(1 / 2 - θ₀) := by
            intro j
            have hj : j ≤ ilast := Fin.le_iff_val_le_val.mpr (by
              simp [ilast]
              omega)
            exact le_trans (hmono hj) hti'
          have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
            (fun j _ => hle j)
          have hcst : (∑ j : Fin d, -(1 / 2 - θ₀ : ℝ)) =
              (d : ℝ) * (-(1 / 2 - θ₀)) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
          have hs' : S ≤ (d : ℝ) * (-(1 / 2 - θ₀)) := by
            dsimp [S]
            calc
              (∑ j : Fin d, t j) ≤ ∑ j : Fin d, -(1 / 2 - θ₀) := hs
              _ = (d : ℝ) * (-(1 / 2 - θ₀)) := hcst
          calc
            S ≤ (d : ℝ) * (-(1 / 2 - θ₀)) := hs'
            _ = -((d : ℝ) * (1 / 2 - θ₀)) := by ring
        have hdlarge : (d : ℝ) * (1 / 2 - θ₀) ≥ 1 := by nlinarith [hdR, hmargin]
        nlinarith [hsumup, hSlo, hdlarge, hθsmall]
      · have hsumup : S ≤ -((i.val + 1 : ℕ) : ℝ) * (1 / 2 - θ₀) +
            ((d - i.val - 1 : ℕ) : ℝ) * t ilast :=
          hsumUpper i (1 / 2 - θ₀) (t ilast)
            (by
              intro j hj
              exact le_trans (hmono (Finset.mem_Iic.mp hj)) hti)
            (by
              intro j hj
              have hjlast : j ≤ ilast := Fin.le_iff_val_le_val.mpr (by
                have hjlt : j.val < d := j.isLt
                simp [ilast]
                omega)
              exact hmono hjlast)
        have hcount : 1 ≤ d - i.val - 1 := by omega
        have hcountR : 1 ≤ ((d - i.val - 1 : ℕ) : ℝ) := by exact_mod_cast hcount
        have hcountLe : ((d - i.val - 1 : ℕ) : ℝ) ≤ d := by
          exact_mod_cast (show d - i.val - 1 ≤ d by omega)
        by_contra hnot
        have hlt : t ilast < c := lt_of_not_ge hnot
        have htail : ((d - i.val - 1 : ℕ) : ℝ) * t ilast < 1 / 64 := by
          have hmul : ((d - i.val - 1 : ℕ) : ℝ) * t ilast <
              ((d - i.val - 1 : ℕ) : ℝ) * c := by
            exact mul_lt_mul_of_pos_left hlt (by
              exact_mod_cast (show 0 < d - i.val - 1 by omega))
          have hmc : ((d - i.val - 1 : ℕ) : ℝ) * c ≤ (d : ℝ) * c :=
            mul_le_mul_of_nonneg_right hcountLe hc.le
          calc
            ((d - i.val - 1 : ℕ) : ℝ) * t ilast <
                ((d - i.val - 1 : ℕ) : ℝ) * c := hmul
            _ ≤ (d : ℝ) * c := hmc
            _ = 1 / 64 := hdc
        have hfirstTerm : -((i.val + 1 : ℕ) : ℝ) * (1 / 2 - θ₀) ≤ -(1 / 3) := by
          have hqN : 1 ≤ i.val + 1 := by omega
          have hq : 1 ≤ ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast hqN
          have hmul := mul_le_mul_of_nonneg_left hmargin
            (by positivity : 0 ≤ ((i.val + 1 : ℕ) : ℝ))
          have hbase : (1 / 3 : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) * (1 / 3) := by
            simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right hq (by norm_num : (0 : ℝ) ≤ 1 / 3))
          have hfirstlarge : (1 / 3 : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) * (1 / 2 - θ₀) :=
            hbase.trans hmul
          calc
            -((i.val + 1 : ℕ) : ℝ) * (1 / 2 - θ₀) =
                -(((i.val + 1 : ℕ) : ℝ) * (1 / 2 - θ₀)) := by ring
            _ ≤ -(1 / 3 : ℝ) := neg_le_neg hfirstlarge
        have hSlt : S < -(1 / 3 : ℝ) + 1 / 64 := by
          calc
            S ≤ -((i.val + 1 : ℕ) : ℝ) * (1 / 2 - θ₀) +
                ((d - i.val - 1 : ℕ) : ℝ) * t ilast := hsumup
            _ ≤ -(1 / 3 : ℝ) + ((d - i.val - 1 : ℕ) : ℝ) * t ilast :=
              add_le_add hfirstTerm le_rfl
            _ < -(1 / 3 : ℝ) + 1 / 64 := by linarith
        have hbound : -(1 / 3 : ℝ) + 1 / 64 < -θ₀ := by linarith [hθsmall]
        linarith [hSlo]
    have hpair : t i0 + t i1 ≤ -c := by
      by_cases hidx : i.val = 0
      · have heq : i = i0 := Fin.ext hidx
        have ht0 : t i0 ≤ -(1 / 2 - θ₀) := by simpa [heq] using hti
        by_cases hb : t i1 < (1 / 2 - θ₀) / 2
        · have hcsmall : c ≤ 1 / 192 := by simpa [θ₀] using hθsmall
          calc
            t i0 + t i1 ≤ -(1 / 2 - θ₀) + (1 / 2 - θ₀) / 2 :=
              add_le_add ht0 (le_of_lt hb)
            _ = -((1 / 2 - θ₀) / 2) := by ring
            _ ≤ -c := by linarith [hmargin, hcsmall]
        · have hb' : (1 / 2 - θ₀) / 2 ≤ t i1 := le_of_not_gt hb
          have hsumRel : t i0 + ((d - 1 : ℕ) : ℝ) * t i1 ≤ S := by
            have hrel := hsumLower i1 (t i0) (t i1) (by
              intro j hj
              have hj' : j = i0 := by
                have hjv : j.val < 1 := Fin.lt_iff_val_lt_val.mp (Finset.mem_Iio.mp hj)
                exact Fin.ext (by omega)
              subst j
              exact le_rfl) (by
              intro j hj
              exact hmono (Finset.mem_Ici.mp hj))
            simpa [i1] using hrel
          have hpairbound : t i0 + t i1 ≤ θ₀ - ((d - 2 : ℕ) : ℝ) * t i1 := by
            have hnat : d - 1 = (d - 2) + 1 := by omega
            have hcast : ((d - 1 : ℕ) : ℝ) = ((d - 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
            have hsumRel' : t i0 + (((d - 2 : ℕ) : ℝ) + 1) * t i1 ≤ S := by
              rw [← hcast]
              exact hsumRel
            have hsumRel'' : t i0 + t i1 + ((d - 2 : ℕ) : ℝ) * t i1 ≤ θ₀ := by
              calc
                t i0 + t i1 + ((d - 2 : ℕ) : ℝ) * t i1 =
                    t i0 + (((d - 2 : ℕ) : ℝ) + 1) * t i1 := by ring
                _ ≤ θ₀ := hsumRel'.trans hShi
            linarith [hsumRel'']
          have hcoef : 1 ≤ ((d - 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d - 2 by omega)
          have hbpos : 0 < t i1 := by linarith [hb', hmargin]
          have hmult : (1 / 6 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) * t i1 := by
            have hcoefmul := mul_le_mul_of_nonneg_right hcoef (le_of_lt hbpos)
            have hbsmall : (1 / 6 : ℝ) ≤ t i1 := by linarith [hb', hmargin]
            calc
              (1 / 6 : ℝ) ≤ t i1 := hbsmall
              _ = 1 * t i1 := by ring
              _ ≤ ((d - 2 : ℕ) : ℝ) * t i1 := by simpa only [one_mul] using hcoefmul
          have hθc : θ₀ = c := rfl
          have hcsmall : c ≤ 1 / 192 := by simpa [θ₀] using hθsmall
          linarith [hpairbound, hmult, hcsmall, hθsmall, hθc]
      · have hidx' : 1 ≤ i.val := by omega
        have hi0 : i0 ≤ i := Fin.le_iff_val_le_val.mpr (by simp [i0])
        have hi1 : i1 ≤ i := Fin.le_iff_val_le_val.mpr (by simpa [i1] using hidx')
        have ht0 : t i0 ≤ -(1 / 2 - θ₀) := le_trans (hmono hi0) hti
        have ht1 : t i1 ≤ -(1 / 2 - θ₀) := le_trans (hmono hi1) hti
        have hcsmall : c ≤ 1 / 192 := by simpa [θ₀] using hθsmall
        have hθc : θ₀ = c := rfl
        calc
          t i0 + t i1 ≤ -(1 / 2 - θ₀) + -(1 / 2 - θ₀) := add_le_add ht0 ht1
          _ ≤ -c := by nlinarith [hmargin, hcsmall, hθsmall, hθc]
    exact ⟨hfirst, hlast, hpair⟩
/-- `prof:budget.bezout` (`profiles.tex:258–263`): on the system after `j` cuts, the carriers
meeting the piece have total degree at most `e_j e^{θ s}`, and every subcollection of total
degree `a` meets the piece in at most `a (∏_{i>j} D_i) e^{θ s}` points, counting every point
touching those components (eq. `prof:mass-budget`). -/
theorem prof_budget_bezout (d : ℕ) (hd : 3 ≤ d) :
    ∀ θ > 0, ∃ θ₁ > 0, ∀ (P : Finset (Pt d)) (X : Piece d) (ξ K : ℝ),
      PieceGood P θ₁ ξ K X → 0 ≤ X.width → ∀ j : ℕ, j ≤ d →
      ∀ 𝒜 : Finset (AffineVariety d),
        (∀ Z ∈ 𝒜, X.path.IsCarrier j Z ∧ ∃ x ∈ X.pts, toC x ∈ Z) →
        (∑ Z ∈ 𝒜, (Z.degree : ℝ) ≤
            eScale (cfgB P) X.width X.path.time j * Real.exp (θ * X.width)) ∧
        ((X.pts.filter (fun x => ∃ Z ∈ 𝒜, toC x ∈ Z)).card : ℝ) ≤
          (∑ Z ∈ 𝒜, (Z.degree : ℝ)) * tailScale (cfgB P) X.width X.path.time j *
            Real.exp (θ * X.width) := by
  intro θ hθ
  let θ₁ : ℝ := θ / (d : ℝ)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hθ₁ : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hθ₁d : (d : ℝ) * θ₁ = θ := by
    dsimp [θ₁]
    field_simp
  refine ⟨θ₁, hθ₁, ?_⟩
  intro P X ξ K hX hs j hj 𝒜 h𝒜
  by_cases hpts : X.pts.Nonempty
  · have hcutDegree : ∀ i : Fin d, 1 ≤ (X.path.cut i).totalDegree := by
      intro i
      exact dprofiles2_cut_degree_pos P X θ₁ ξ K hX hpts i
    let fpre : Fin j → Poly d := dprofiles2PrefixCut X.path hj
    have hpreDegree : ∀ i, 1 ≤ (fpre i).totalDegree := by
      intro i
      simpa [fpre, dprofiles2PrefixCut] using
        hcutDegree ⟨i.val, i.isLt.trans_le hj⟩
    have hsystemPrefix := dprofiles2_system_eq_prefix X.path hj
    have hcomponents : ∀ Z ∈ 𝒜,
        Z.IsComponentOf (Ideal.span (Set.range fpre)) := by
      intro Z hZ
      have hZcarrier : Z.ideal ∈ (X.path.system j).minimalPrimes := (h𝒜 Z hZ).1
      rw [hsystemPrefix] at hZcarrier
      exact hZcarrier
    have hpure : AffineFamily.IsPure 𝒜 (d - j) := by
      intro Z hZ
      obtain ⟨x, hx, hxZ⟩ := (h𝒜 Z hZ).2
      have hZlocal : Z ∈ X.path.localCarriers j (toC x) :=
        ⟨(h𝒜 Z hZ).1, hxZ⟩
      exact prof_partition_pure X x hx (hX.vanish x hx) (hX.proper x hx) j hj Z hZlocal
    have hsumBezout :
        (∑ Z ∈ 𝒜, Z.degree) ≤
          ∏ i : Fin j, ((fpre i).totalDegree : ℚ) :=
      TrackA.fa_bezout_components hj fpre hpreDegree 𝒜 hpure hcomponents
    have hpreReal :
        (∑ Z ∈ 𝒜, (Z.degree : ℝ)) ≤
          ∏ i : Fin j, ((fpre i).totalDegree : ℝ) := by
      calc
        (∑ Z ∈ 𝒜, (Z.degree : ℝ)) = ((∑ Z ∈ 𝒜, Z.degree : ℚ) : ℝ) := by norm_cast
        _ ≤ ∏ i : Fin j, (((fpre i).totalDegree : ℚ) : ℝ) := by exact_mod_cast hsumBezout
        _ = _ := by simp
    have hpreProduct := dprofiles2_prefix_degree_product P X θ₁ hX.degree j hj
    have hjR : (j : ℝ) ≤ (d : ℝ) := by exact_mod_cast hj
    have hjθ : (j : ℝ) * θ₁ ≤ θ := by
      calc
        (j : ℝ) * θ₁ ≤ (d : ℝ) * θ₁ := mul_le_mul_of_nonneg_right hjR hθ₁.le
        _ = θ := hθ₁d
    have hpreExp :
        Real.exp ((j : ℝ) * θ₁ * X.width) ≤ Real.exp (θ * X.width) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hjθ hs
    have heScaleNonneg : 0 ≤ eScale (cfgB P) X.width X.path.time j := by
      unfold eScale cutScale testDeg
      apply Finset.prod_nonneg
      intro i hi
      dsimp [cfgB]
      positivity
    have hpreBound :
        ∏ i : Fin j, ((fpre i).totalDegree : ℝ) ≤
          eScale (cfgB P) X.width X.path.time j * Real.exp (θ * X.width) :=
      hpreProduct.trans (mul_le_mul_of_nonneg_left hpreExp heScaleNonneg)
    have hsumBound :
        (∑ Z ∈ 𝒜, (Z.degree : ℝ)) ≤
          eScale (cfgB P) X.width X.path.time j * Real.exp (θ * X.width) :=
      hpreReal.trans hpreBound
    let ftail : Fin (d - j) → Poly d := dprofiles2TailCut X.path hj
    have htailDegree : ∀ i, 1 ≤ (ftail i).totalDegree := by
      intro i
      simpa [ftail, dprofiles2TailCut] using
        hcutDegree ⟨j + i.val, by omega⟩
    let pointsOn (Z : AffineVariety d) : Finset (Pt d) :=
      X.pts.filter (fun x => toC x ∈ Z)
    have hcount (Z : AffineVariety d) (hZ : Z ∈ 𝒜) :
        ((pointsOn Z).card : ℝ) ≤
          (Z.degree : ℝ) * ∏ i : Fin (d - j), ((ftail i).totalDegree : ℝ) := by
      have hIsolated : ∀ x ∈ pointsOn Z, pointIdeal (toC x) ∈
          (Z.ideal ⊔ Ideal.span (Set.range ftail)).minimalPrimes := by
        intro x hx
        exact dprofiles2_final_point_minimal P X θ₁ ξ K hX x
          (Finset.mem_filter.mp hx).1 j hj Z ⟨(h𝒜 Z hZ).1, (Finset.mem_filter.mp hx).2⟩
      have hvanTail : ∀ x ∈ pointsOn Z, ∀ i,
          MvPolynomial.eval (toC x) (ftail i) = 0 := by
        intro x hx i
        exact hX.vanish x (Finset.mem_filter.mp hx).1 ⟨j + i.val, by omega⟩
      have hcountQ := dprofiles2_isolated_cut_product_bound Z
        ((h𝒜 Z hZ).1.isPrime) ftail (pointsOn Z) hvanTail htailDegree hIsolated
      exact_mod_cast hcountQ
    let unionPoints : Finset (Pt d) := X.pts.filter (fun x =>
      ∃ Z ∈ 𝒜, toC x ∈ Z)
    have hcover : unionPoints ⊆ 𝒜.biUnion pointsOn := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxP, hxA⟩
      rcases hxA with ⟨Z, hZ, hxZ⟩
      exact Finset.mem_biUnion.mpr ⟨Z, hZ, Finset.mem_filter.mpr ⟨hxP, hxZ⟩⟩
    have hcardCover :
        (unionPoints.card : ℝ) ≤ ∑ Z ∈ 𝒜, ((pointsOn Z).card : ℝ) := by
      calc
        (unionPoints.card : ℝ) ≤ ((𝒜.biUnion pointsOn).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcover
        _ ≤ ∑ Z ∈ 𝒜, ((pointsOn Z).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
    have hsumCount :
        (∑ Z ∈ 𝒜, ((pointsOn Z).card : ℝ)) ≤
          (∑ Z ∈ 𝒜, (Z.degree : ℝ)) *
            (∏ i : Fin (d - j), ((ftail i).totalDegree : ℝ)) := by
      calc
        _ ≤ ∑ Z ∈ 𝒜, (Z.degree : ℝ) *
            ∏ i : Fin (d - j), ((ftail i).totalDegree : ℝ) := by
              apply Finset.sum_le_sum
              intro Z hZ
              exact hcount Z hZ
        _ = _ := by rw [Finset.sum_mul]
    have htailProduct := dprofiles2_tail_degree_product P X θ₁ hX.degree j hj
    have hdjR : ((d - j : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.sub_le d j
    have hdjθ : ((d - j : ℕ) : ℝ) * θ₁ ≤ θ := by
      calc
        ((d - j : ℕ) : ℝ) * θ₁ ≤ (d : ℝ) * θ₁ := mul_le_mul_of_nonneg_right hdjR hθ₁.le
        _ = θ := hθ₁d
    have htailExp :
        Real.exp (((d - j : ℕ) : ℝ) * θ₁ * X.width) ≤ Real.exp (θ * X.width) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hdjθ hs
    have htailScaleNonneg : 0 ≤ tailScale (cfgB P) X.width X.path.time j := by
      unfold tailScale cutScale testDeg
      apply Finset.prod_nonneg
      intro i hi
      dsimp [cfgB]
      positivity
    have htailBound :
        (∏ i : Fin (d - j), ((ftail i).totalDegree : ℝ)) ≤
          tailScale (cfgB P) X.width X.path.time j * Real.exp (θ * X.width) :=
      htailProduct.trans (mul_le_mul_of_nonneg_left htailExp htailScaleNonneg)
    have hsumDegNonneg : 0 ≤ ∑ Z ∈ 𝒜, (Z.degree : ℝ) := by
      apply Finset.sum_nonneg
      intro Z hZ
      have hIrred := (hpure Z hZ).1
      have hq : 0 ≤ Z.degree := by
        change 0 ≤ OAI.QuarticPowerFree.affineDegree Z.ideal
        have h := OAI.QuarticPowerFree.one_le_affineDegree Z.ideal hIrred.ne_top
        linarith
      exact_mod_cast hq
    constructor
    · exact hsumBound
    · calc
        (unionPoints.card : ℝ) ≤ _ := hcardCover.trans hsumCount
        _ ≤ (∑ Z ∈ 𝒜, (Z.degree : ℝ)) *
            (tailScale (cfgB P) X.width X.path.time j * Real.exp (θ * X.width)) :=
              mul_le_mul_of_nonneg_left htailBound hsumDegNonneg
        _ = _ := by ring
  · have hXempty : X.pts = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpts
    have hAempty : 𝒜 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro Z hZ
      obtain ⟨x, hx, _⟩ := (h𝒜 Z hZ).2
      exact hpts ⟨x, hx⟩
    constructor
    · have hBnonneg : 0 ≤ cfgB P := by
        dsimp [cfgB]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hscale : 0 ≤ eScale (cfgB P) X.width X.path.time j := by
        unfold eScale cutScale testDeg
        apply Finset.prod_nonneg
        intro i hi
        dsimp [cfgB]
        positivity
      simpa [hAempty] using mul_nonneg hscale (Real.exp_nonneg _)
    · simp [hXempty, hAempty]

/-- `prof:budget.rank` (`profiles.tex:265–316`, eq. `prof:rank-budget`): rank propagation
through the plateaux. There is `C_d` such that for every `θ > 0` and density `α₀ > 0`, pieces
with small enough tolerance and large enough width satisfy, for every `ξ`-plateau point `b`
(after `j ≤ d` cuts, `T_s(b) ≥ 1`) and every subset `S` of at least `α₀ n` piece points,
`H_S(⌊T_s(b)⌋) ≥ σ(b) e^{-(C_d ξ + θ) s}`. The loss `C_d ξ` comes from crossing clusters of
cut times closer than `2ξ`; consumers take `ξ` small. -/
theorem prof_budget_rank (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ θ > 0, ∀ α₀ > 0, ∃ θ₁ > 0, ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (X : Piece d) (ξ K : ℝ), 0 < ξ → 1 ≤ K →
        PieceGood P θ₁ ξ K X → s₁ ≤ X.width →
        ∀ j : ℕ, j ≤ d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
          1 ≤ testDeg (cfgB P) X.width b →
          ∀ S ⊆ X.pts, α₀ * X.pts.card ≤ S.card →
            sigma (cfgB P) X.width X.path.time b * Real.exp (-(Cd * ξ + θ) * X.width) ≤
              hilbertOfSet (toC '' (S : Set (Pt d))) ⌊testDeg (cfgB P) X.width b⌋₊ := by
  exact budget_rank_proof d hd

set_option maxHeartbeats 500000 in
/-- `prof:budget.sum` (`profiles.tex:258–264, 316–319`): the recorded times nearly sum to zero.
The lower bound is Bézout on the whole path (`n ≤ ∏ D_i e^{o(s)}`); the upper bound is the rank
budget after the last cut (`∏ D_i ≤ N e^{o(s)}`), hence the margin `ξ` must be small. -/
theorem prof_budget_sum (d : ℕ) (hd : 3 ≤ d) :
    ∀ θ > 0, ∃ θ₁ > 0, ∃ ξ₀ > 0, ∃ s₁ : ℝ, ∀ (P : Finset (Pt d)) (X : Piece d) (ξ K : ℝ),
      0 < ξ → ξ ≤ ξ₀ → 1 ≤ K → PieceGood P θ₁ ξ K X → s₁ ≤ X.width →
        |∑ i, X.path.time i| ≤ θ := by
  intro θ hθ
  obtain ⟨Cd, hCd, hRank⟩ := prof_budget_rank d hd
  let θr : ℝ := θ / 4
  have hθr : 0 < θr := by dsimp [θr]; positivity
  obtain ⟨θr₁, hθr₁, sr, hRank⟩ := hRank θr hθr 1 (by norm_num)
  let θb : ℝ := θ / 8
  have hθb : 0 < θb := by dsimp [θb]; positivity
  obtain ⟨θb₁, hθb₁, hBezout⟩ := prof_budget_bezout d hd θb hθb
  let θ₁ : ℝ := min (min θr₁ θb₁) (θ / 8)
  have hθ₁ : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hθ₁r : θ₁ ≤ θr₁ := by
    dsimp [θ₁]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hθ₁b : θ₁ ≤ θb₁ := by
    dsimp [θ₁]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hθ₁small : θ₁ ≤ θ / 8 := by
    dsimp [θ₁]
    exact min_le_right _ _
  let ξ₀ : ℝ := θ / (4 * Cd)
  have hξ₀ : 0 < ξ₀ := by dsimp [ξ₀]; positivity
  let s₁ : ℝ := max sr 1
  have hs₁ : 0 < s₁ := by dsimp [s₁]; positivity
  refine ⟨θ₁, hθ₁, ξ₀, hξ₀, s₁, ?_⟩
  intro P X ξ K hξ hξ₀K hK hX hs
  have hspos : 0 < X.width := lt_of_lt_of_le hs₁ hs
  have hsnonneg : 0 ≤ X.width := hspos.le
  have hsr : sr ≤ X.width := le_trans (le_max_left _ _) hs
  have hNbase : 0 ≤ cfgN P := by dsimp [cfgN]; positivity
  have hBnonneg : 0 ≤ cfgB P := by dsimp [cfgB]; positivity
  have hlog : 0 < Real.log (cfgB P) := by
    obtain ⟨a, ha⟩ := hX.width_dyadic
    have hpow : 0 < (2 : ℝ) ^ a := by positivity
    rw [ha] at hspos
    exact (div_pos_iff_of_pos_right hpow).mp hspos
  have hBgt : 1 < cfgB P := (Real.log_pos_iff hBnonneg).mp hlog
  have hNpos : 0 < cfgN P := by
    by_contra hn
    have hn0 : cfgN P = 0 := le_antisymm (le_of_not_gt hn) hNbase
    have hcard0R : (P.card : ℝ) = 0 := by simpa [cfgN] using hn0
    have hcard0 : P.card = 0 := by exact_mod_cast hcard0R
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hexpne : (1 : ℝ) / (d : ℝ) ≠ 0 := div_ne_zero one_ne_zero hdne
    have hBzero : cfgB P = 0 := by
      rw [cfgB, hcard0]
      simpa only [Nat.cast_zero] using Real.zero_rpow hexpne
    linarith
  have hXsizePos : 0 < cfgN P * Real.exp (-θ₁ * X.width) :=
    mul_pos hNpos (Real.exp_pos _)
  have hXcardPosR : 0 < (X.pts.card : ℝ) := lt_of_lt_of_le hXsizePos hX.size
  have hXcardPos : 0 < X.pts.card := by exact_mod_cast hXcardPosR
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hXcardPos
  have hXr : PieceGood P θr₁ ξ K X :=
    dprofiles2_pieceGood_mono P X hθ₁r hsnonneg hX
  have hXb : PieceGood P θb₁ ξ K X :=
    dprofiles2_pieceGood_mono P X hθ₁b hsnonneg hX
  have hBpow : cfgB P ^ d = cfgN P := by
    dsimp [cfgB, cfgN]
    have hPcardNonneg : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
    rw [← Real.rpow_natCast, ← Real.rpow_mul hPcardNonneg]
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hpow : (1 : ℝ) / (d : ℝ) * (d : ℝ) = 1 := by field_simp
    rw [hpow, Real.rpow_one]
  let Dprod : ℝ := ∏ i : Fin d, cutScale (cfgB P) X.width X.path.time i
  have hDprodNonneg : 0 ≤ Dprod := by
    apply Finset.prod_nonneg
    intro i hi
    unfold cutScale testDeg
    exact mul_nonneg hBnonneg (Real.exp_nonneg _)
  let Tsum : ℝ := ∑ i : Fin d, X.path.time i
  have hDprodEq : Dprod = cfgN P * Real.exp (Tsum * X.width) := by
    calc
      Dprod = (∏ i : Fin d, cfgB P) * (∏ i : Fin d, Real.exp (X.path.time i * X.width)) := by
        simp [Dprod, cutScale, testDeg, Finset.prod_mul_distrib]
      _ = cfgB P ^ d * Real.exp (∑ i : Fin d, X.path.time i * X.width) := by
        simp [Finset.prod_const, Fintype.card_fin, ← Real.exp_sum]
      _ = cfgN P * Real.exp (Tsum * X.width) := by
        rw [hBpow, Finset.sum_mul]
  let b : ℝ := 2 + θr₁ + ξ
  have hplateau : OnPlateau X.path.time d ξ b := by
    intro i
    constructor
    · intro _
      have hi := (hXr.time_range i).2
      dsimp [b]
      linarith
    · intro hi
      omega
  have htest : 1 ≤ testDeg (cfgB P) X.width b := by
    have hExp : 1 ≤ Real.exp (b * X.width) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) hsnonneg)
    unfold testDeg
    exact one_le_mul_of_one_le_of_one_le hBgt.le hExp
  have hDleT (i : Fin d) : cutScale (cfgB P) X.width X.path.time i ≤
      testDeg (cfgB P) X.width b := by
    unfold cutScale testDeg
    apply mul_le_mul_of_nonneg_left _ hBnonneg
    apply Real.exp_le_exp.mpr
    have hi := (hXr.time_range i).2
    dsimp [b]
    exact mul_le_mul_of_nonneg_right (by linarith) hsnonneg
  have hsigma : sigma (cfgB P) X.width X.path.time b = Dprod := by
    unfold sigma Dprod
    apply Finset.prod_congr rfl
    intro i hi
    exact min_eq_right (hDleT i)
  have hRankAt := hRank P X ξ K hξ hK hXr hsr d (by omega) b hplateau htest
    X.pts subset_rfl (by simp)
  have hHilbert :
      hilbertOfSet (toC '' (X.pts : Set (Pt d))) ⌊testDeg (cfgB P) X.width b⌋₊ ≤ X.pts.card :=
    dprofiles2_hilbertOfSet_image_le_card toC X.pts _
  have hDexp : Dprod * Real.exp (-(Cd * ξ + θr) * X.width) ≤ cfgN P := by
    calc
      Dprod * Real.exp (-(Cd * ξ + θr) * X.width) =
          sigma (cfgB P) X.width X.path.time b * Real.exp (-(Cd * ξ + θr) * X.width) := by
            rw [hsigma]
      _ ≤ hilbertOfSet (toC '' (X.pts : Set (Pt d)))
          ⌊testDeg (cfgB P) X.width b⌋₊ := hRankAt
      _ ≤ (X.pts.card : ℝ) := by exact_mod_cast hHilbert
      _ ≤ cfgN P := by
        change (X.pts.card : ℝ) ≤ (P.card : ℝ)
        exact_mod_cast Finset.card_le_card hX.subset
  have hDupper : Dprod ≤ cfgN P * Real.exp ((Cd * ξ + θr) * X.width) := by
    calc
      Dprod = (Dprod * Real.exp (-(Cd * ξ + θr) * X.width)) *
          Real.exp ((Cd * ξ + θr) * X.width) := by
        rw [mul_assoc, ← Real.exp_add]
        have harg : -(Cd * ξ + θr) * X.width + (Cd * ξ + θr) * X.width = 0 := by ring
        rw [harg, Real.exp_zero, mul_one]
      _ ≤ cfgN P * Real.exp ((Cd * ξ + θr) * X.width) :=
        mul_le_mul_of_nonneg_right hDexp (Real.exp_nonneg _)
  have hExpUpper : Real.exp (Tsum * X.width) ≤ Real.exp ((Cd * ξ + θr) * X.width) := by
    have h := hDupper
    rw [hDprodEq] at h
    exact (mul_le_mul_iff_of_pos_left hNpos).mp h
  have hTsumUpper : Tsum ≤ Cd * ξ + θr :=
    (mul_le_mul_iff_of_pos_right hspos).mp (Real.exp_le_exp.mp hExpUpper)

  let top : AffineVariety d := AffineVariety.whole
  let 𝒜 : Finset (AffineVariety d) := {top}
  have hsys0 : X.path.system 0 = ⊥ := by simp [CutPath.system]
  have htopIdeal : top.ideal = ⊥ := by
    dsimp [top, AffineVariety.whole, AffineVariety.ofIdeal]
    exact Ideal.radical_bot_of_isReduced
  have htopCarrier : X.path.IsCarrier 0 top := by
    change top.ideal ∈ (X.path.system 0).minimalPrimes
    rw [hsys0, htopIdeal]
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    simp
  have htopPoint (x : Pt d) : toC x ∈ top := by
    change toC x ∈ top.points
    simp [top, AffineVariety.whole, AffineVariety.ofIdeal, AffineVariety.points]
  have hA : ∀ Z ∈ 𝒜, X.path.IsCarrier 0 Z ∧ ∃ x ∈ X.pts, toC x ∈ Z := by
    intro Z hZ
    have hZeq : Z = top := Finset.mem_singleton.mp hZ
    subst Z
    exact ⟨htopCarrier, x₀, hx₀, htopPoint x₀⟩
  obtain ⟨hdeg, hmass⟩ := hBezout P X ξ K hXb hsnonneg 0 (by omega) 𝒜 hA
  have hdegExp : (∑ Z ∈ 𝒜, (Z.degree : ℝ)) ≤ Real.exp (θb * X.width) := by
    simpa [𝒜, eScale] using hdeg
  have hfilter : X.pts.filter (fun y => ∃ Z ∈ 𝒜, toC y ∈ Z) = X.pts := by
    ext y
    constructor
    · intro hy
      exact (Finset.mem_filter.mp hy).1
    · intro hy
      apply Finset.mem_filter.mpr
      refine ⟨hy, ?_⟩
      exact ⟨top, by simp [𝒜], htopPoint y⟩
  have htail0 : tailScale (cfgB P) X.width X.path.time 0 = Dprod := by
    simp [Dprod, tailScale]
  have hmass' : (X.pts.card : ℝ) ≤
      (∑ Z ∈ 𝒜, (Z.degree : ℝ)) * tailScale (cfgB P) X.width X.path.time 0 *
        Real.exp (θb * X.width) := by
    simpa [hfilter] using hmass
  have hmassBound : (X.pts.card : ℝ) ≤ Dprod * Real.exp ((2 * θb) * X.width) := by
    calc
      (X.pts.card : ℝ) ≤
          (∑ Z ∈ 𝒜, (Z.degree : ℝ)) * Dprod * Real.exp (θb * X.width) := by
            simpa [htail0] using hmass'
      _ = (∑ Z ∈ 𝒜, (Z.degree : ℝ)) *
          (Dprod * Real.exp (θb * X.width)) := by ring
      _ ≤ Real.exp (θb * X.width) * (Dprod * Real.exp (θb * X.width)) :=
        mul_le_mul_of_nonneg_right hdegExp (mul_nonneg hDprodNonneg (Real.exp_nonneg _))
      _ = Dprod * Real.exp ((2 * θb) * X.width) := by
        calc
          _ = Dprod * (Real.exp (θb * X.width) * Real.exp (θb * X.width)) := by ring
          _ = Dprod * Real.exp (θb * X.width + θb * X.width) := by rw [← Real.exp_add]
          _ = _ := by congr 1; ring
  have hsizeMass : cfgN P * Real.exp (-θ₁ * X.width) ≤
      Dprod * Real.exp ((2 * θb) * X.width) := hX.size.trans hmassBound
  have hNlower : cfgN P ≤ Dprod * Real.exp ((θ₁ + 2 * θb) * X.width) := by
    calc
      cfgN P = (cfgN P * Real.exp (-θ₁ * X.width)) * Real.exp (θ₁ * X.width) := by
        calc
          _ = cfgN P * (Real.exp (-θ₁ * X.width) * Real.exp (θ₁ * X.width)) := by
            rw [← Real.exp_add]
            simp
          _ = _ := by ring
      _ ≤ (Dprod * Real.exp ((2 * θb) * X.width)) * Real.exp (θ₁ * X.width) :=
        mul_le_mul_of_nonneg_right hsizeMass (Real.exp_nonneg _)
      _ = Dprod * Real.exp ((θ₁ + 2 * θb) * X.width) := by
        calc
          _ = Dprod * (Real.exp ((2 * θb) * X.width) * Real.exp (θ₁ * X.width)) := by ring
          _ = Dprod * Real.exp ((2 * θb) * X.width + θ₁ * X.width) := by rw [← Real.exp_add]
          _ = _ := by congr 1; ring
  have hExpLower : 1 ≤ Real.exp ((Tsum + (θ₁ + 2 * θb)) * X.width) := by
    have hNlower' := hNlower
    rw [hDprodEq] at hNlower'
    have hNfact : cfgN P * Real.exp (Tsum * X.width) *
        Real.exp ((θ₁ + 2 * θb) * X.width) =
          cfgN P * Real.exp ((Tsum + (θ₁ + 2 * θb)) * X.width) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring
    rw [hNfact] at hNlower'
    have hquot : cfgN P / cfgN P ≤ Real.exp ((Tsum + (θ₁ + 2 * θb)) * X.width) :=
      (div_le_iff₀ hNpos).2 (by simpa [mul_comm] using hNlower')
    simpa [hNpos.ne'] using hquot
  have hTsumLower : -(θ₁ + 2 * θb) ≤ Tsum := by
    have harg : 0 ≤ (Tsum + (θ₁ + 2 * θb)) * X.width := Real.one_le_exp_iff.mp hExpLower
    have harg' : 0 ≤ Tsum + (θ₁ + 2 * θb) :=
      (mul_nonneg_iff_of_pos_right hspos).mp harg
    linarith
  have herr : θ₁ + 2 * θb ≤ θ := by
    dsimp [θb]
    linarith only [hθ₁small, hθ]
  have hTsumLower' : -θ ≤ Tsum := le_trans (by nlinarith [herr]) hTsumLower
  have hCdξ : Cd * ξ ≤ θ / 4 := by
    calc
      Cd * ξ ≤ Cd * ξ₀ := mul_le_mul_of_nonneg_left hξ₀K hCd.le
      _ = θ / 4 := by dsimp [ξ₀]; field_simp
  have hTsumUpper' : Tsum ≤ θ := by
    calc
      Tsum ≤ Cd * ξ + θr := hTsumUpper
      _ ≤ θ := by
        dsimp [θr]
        linarith only [hCdξ, hθ]
  simpa [Tsum] using (abs_le.mpr ⟨hTsumLower', hTsumUpper'⟩)

/-- `prof:budget` (`profiles.tex:236–255`), assembled: balance with explicit margins, carrier
degree and mass budgets, and the rank budget, for pieces with small tolerance and margin and
large width. -/
theorem prof_budget (d : ℕ) (hd : 3 ≤ d) :
    ∃ c Cd : ℝ, 0 < c ∧ 0 < Cd ∧ ∀ θ > 0, ∀ α₀ > 0, ∃ θ₁ > 0, ∃ ξ₀ > 0, ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (X : Piece d) (ξ K : ℝ), 0 < ξ → ξ ≤ ξ₀ → 1 ≤ K →
        PieceGood P θ₁ ξ K X → s₁ ≤ X.width →
        (|∑ i, X.path.time i| ≤ θ ∧
          X.path.time ⟨0, by omega⟩ ≤ -c ∧ c ≤ X.path.time ⟨d - 1, by omega⟩ ∧
          X.path.time ⟨0, by omega⟩ + X.path.time ⟨1, by omega⟩ ≤ -c) ∧
        (∀ j : ℕ, j ≤ d → ∀ 𝒜 : Finset (AffineVariety d),
          (∀ Z ∈ 𝒜, X.path.IsCarrier j Z ∧ ∃ x ∈ X.pts, toC x ∈ Z) →
          (∑ Z ∈ 𝒜, (Z.degree : ℝ) ≤
              eScale (cfgB P) X.width X.path.time j * Real.exp (θ * X.width)) ∧
          ((X.pts.filter (fun x => ∃ Z ∈ 𝒜, toC x ∈ Z)).card : ℝ) ≤
            (∑ Z ∈ 𝒜, (Z.degree : ℝ)) * tailScale (cfgB P) X.width X.path.time j *
              Real.exp (θ * X.width)) ∧
        (∀ j : ℕ, j ≤ d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
          1 ≤ testDeg (cfgB P) X.width b →
          ∀ S ⊆ X.pts, α₀ * X.pts.card ≤ S.card →
            sigma (cfgB P) X.width X.path.time b * Real.exp (-(Cd * ξ + θ) * X.width) ≤
              hilbertOfSet (toC '' (S : Set (Pt d))) ⌊testDeg (cfgB P) X.width b⌋₊) := by
  obtain ⟨c, θbal, hc, hθbal, hbalance⟩ := prof_budget_balance_arith d hd
  obtain ⟨Cd, hCd, hRank⟩ := prof_budget_rank d hd
  refine ⟨c, Cd, hc, hCd, ?_⟩
  intro θ hθ α₀ hα₀
  let θsumGoal : ℝ := min θ θbal
  have hθsumGoal : 0 < θsumGoal := by
    dsimp [θsumGoal]
    exact lt_min hθ hθbal
  obtain ⟨θsum', hθsum', ξ₀', hξ₀', ssum', hsum'⟩ :=
    prof_budget_sum d hd θsumGoal hθsumGoal
  obtain ⟨θbez', hθbez', hBezout'⟩ := prof_budget_bezout d hd θ hθ
  obtain ⟨θrank', hθrank', srank', hRank'⟩ := hRank θ hθ α₀ hα₀
  let θ₁' : ℝ := min (min θsum' θbez') (min θrank' θbal)
  let s₁' : ℝ := max (max ssum' srank') 0
  have hθ₁' : 0 < θ₁' := by dsimp [θ₁']; positivity
  have hθ₁sum' : θ₁' ≤ θsum' := by
    dsimp [θ₁']
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hθ₁bez' : θ₁' ≤ θbez' := by
    dsimp [θ₁']
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hθ₁rank' : θ₁' ≤ θrank' := by
    dsimp [θ₁']
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hθ₁bal' : θ₁' ≤ θbal := by
    dsimp [θ₁']
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hs₁'sum : ssum' ≤ s₁' := by
    dsimp [s₁']
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hs₁'rank : srank' ≤ s₁' := by
    dsimp [s₁']
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hs₁'nonneg : 0 ≤ s₁' := by
    dsimp [s₁']
    exact le_max_right _ _
  refine ⟨θ₁', hθ₁', ξ₀', hξ₀', s₁', ?_⟩
  intro P X ξ K hξ hξ₀X hK hX hs₁X
  have hsSum : ssum' ≤ X.width := le_trans hs₁'sum hs₁X
  have hsRank : srank' ≤ X.width := le_trans hs₁'rank hs₁X
  have hsnonneg : 0 ≤ X.width := le_trans hs₁'nonneg hs₁X
  have hXsum : PieceGood P θsum' ξ K X :=
    dprofiles2_pieceGood_mono P X hθ₁sum' hsnonneg hX
  have hXbez : PieceGood P θbez' ξ K X :=
    dprofiles2_pieceGood_mono P X hθ₁bez' hsnonneg hX
  have hXrank : PieceGood P θrank' ξ K X :=
    dprofiles2_pieceGood_mono P X hθ₁rank' hsnonneg hX
  have hXbal : PieceGood P θbal ξ K X :=
    dprofiles2_pieceGood_mono P X hθ₁bal' hsnonneg hX
  have htimesum := hsum' P X ξ K hξ hξ₀X hK hXsum hsSum
  have htimesumBal : |∑ i, X.path.time i| ≤ θbal := by
    exact le_trans htimesum (min_le_right θ θbal)
  obtain ⟨i, hi⟩ := hXbal.imbalance
  have hiBal : 1 / 2 - θbal ≤ |X.path.time i| := by
    exact le_trans (by nlinarith [hθ₁bal']) hi
  obtain ⟨hfirst, hlast, hpair⟩ :=
    hbalance X.path.time hXbal.mono htimesumBal ⟨i, hiBal⟩
  refine ⟨⟨?_, hfirst, hlast, hpair⟩, ?_, ?_⟩
  · exact le_trans htimesum (min_le_left θ θbal)
  · intro j hj 𝒜 h𝒜
    exact hBezout' P X ξ K hXbez hsnonneg j hj 𝒜 h𝒜
  · intro j hj b hb hT S hS hcard
    exact hRank' P X ξ K hξ hK hXrank hsRank j hj b hb hT S hS hcard

end

end TrackD
end DistinctDistances
