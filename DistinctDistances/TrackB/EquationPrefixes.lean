import DistinctDistances.Bridges.AmbientHilbert

namespace DistinctDistances.TrackB
noncomputable section

def equationPrefixIdeal {n c : ℕ} (f : Fin c → Poly n) (p : ℕ) : Ideal (Poly n) :=
  Ideal.span (Set.range (fun i : Fin c => if i.val < p then f i else 0))

theorem equationPrefixIdeal_zero {n c : ℕ} (f : Fin c → Poly n) :
    equationPrefixIdeal f 0 = ⊥ := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨i, rfl⟩
    simp
  · exact bot_le

theorem equationPrefixIdeal_full {n c : ℕ} (f : Fin c → Poly n) :
    equationPrefixIdeal f c = Ideal.span (Set.range f) := by
  unfold equationPrefixIdeal
  have hfun : (fun i : Fin c => if i.val < c then f i else 0) = f := by
    funext i
    simp [i.isLt]
  rw [hfun]

theorem equationPrefixIdeal_congr {n c : ℕ} (f g : Fin c → Poly n) (p : ℕ)
    (hfg : ∀ i : Fin c, i.val < p → f i = g i) :
    equationPrefixIdeal f p = equationPrefixIdeal g p := by
  unfold equationPrefixIdeal
  have hfun : (fun i : Fin c => if i.val < p then f i else 0) =
      (fun i : Fin c => if i.val < p then g i else 0) := by
    funext i
    split
    · exact hfg i ‹i.val < p›
    · rfl
  rw [hfun]

theorem affine_dimension_mono {n : ℕ} (V W : AffineVariety n) (hsub : W.Subvariety V) :
    W.dimension ≤ V.dimension := by
  apply OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
  · filter_upwards [W.hilbert_eventually] with T hT
    rw [← hT]
    positivity
  · filter_upwards [W.hilbert_eventually, V.hilbert_eventually] with T hW hV
    rw [← hW, ← hV]
    exact_mod_cast OAI.QuarticPowerFree.quotient_hilbert_le V.ideal W.ideal hsub T

theorem equationPrefixIdeal_le_span {n c : ℕ} (f : Fin c → Poly n) (p : ℕ) :
    equationPrefixIdeal f p ≤ Ideal.span (Set.range f) := by
  apply Ideal.span_le.mpr
  rintro g ⟨i, rfl⟩
  change (if i.val < p then f i else 0) ∈ _
  split
  · exact Ideal.subset_span ⟨i, rfl⟩
  · exact Ideal.zero_mem _

theorem equationPrefixIdeal_succ {n c : ℕ} (f : Fin c → Poly n)
    (p : ℕ) (hp : p < c) :
    equationPrefixIdeal f (p + 1) = equationPrefixIdeal f p ⊔ Ideal.span {f ⟨p, hp⟩} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨i, rfl⟩
    change (if i.val < p + 1 then f i else 0) ∈ _
    by_cases hi : i.val < p
    · rw [if_pos (show i.val < p + 1 by omega)]
      apply (show equationPrefixIdeal f p ≤ equationPrefixIdeal f p ⊔
        Ideal.span {f ⟨p, hp⟩} from le_sup_left)
      exact Ideal.subset_span ⟨i, by simp [hi]⟩
    · by_cases his : i.val < p + 1
      · have hieq : i = ⟨p, hp⟩ := by apply Fin.ext; change i.val = p; omega
        subst i
        simpa using (le_sup_right : Ideal.span {f ⟨p, hp⟩} ≤
          equationPrefixIdeal f p ⊔ Ideal.span {f ⟨p, hp⟩})
          (Ideal.subset_span (Set.mem_singleton _))
      · simp [his]
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro g ⟨i, rfl⟩
      by_cases hi : i.val < p
      · exact Ideal.subset_span ⟨i, by simp [hi, show i.val < p + 1 by omega]⟩
      · simp [hi]
    · apply Ideal.span_le.mpr
      rintro g rfl
      exact Ideal.subset_span ⟨⟨p, hp⟩, by simp⟩

/-- B30, concentration.tex:1045–1046. OAI's principal-cut dimension inequality,
without a nonvanishing hypothesis, in the shared affine model. -/
theorem principal_component_dimension_bound {n : ℕ} (V W : AffineVariety n)
    (hV : V.IsIrreducible) (f : Poly n)
    (hW : W.IsComponentOf (V.ideal ⊔ Ideal.span {f})) :
    V.dimension ≤ W.dimension + 1 := by
  letI : V.ideal.IsPrime := hV
  letI : W.ideal.IsPrime := hW.isPrime
  exact OAI.QuarticPowerFree.cut_minimal_hilbert_codim_le_one V.ideal W.ideal f hW
    (OAI.QuarticPowerFree.coordinateHilbert V.ideal)
    (OAI.QuarticPowerFree.coordinateHilbert W.ideal)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually W.ideal)

/-- B30: no more than c-p dimensions are lost by the remaining equations.
Minimality of V over the full system forces the last selected prime to be I(V). -/
theorem prefix_tail_dimension_bound {n c : ℕ} (f : Fin c → Poly n)
    (V : AffineVariety n) (hV : V.IsIrreducible)
    (hcomp : V.IsComponentOf (Ideal.span (Set.range f)))
    (p : ℕ) (hp : p ≤ c) (W : AffineVariety n) (hW : W.IsIrreducible)
    (hpre : equationPrefixIdeal f p ≤ W.ideal) (hWV : W.ideal ≤ V.ideal) :
    W.dimension ≤ V.dimension + (c - p) := by
  classical
  have hall : Ideal.span (Set.range f) ≤ V.ideal := hcomp.le
  generalize hrem : c - p = t
  induction t generalizing p W with
  | zero =>
      have hpfull : p = c := by omega
      have hfull : Ideal.span (Set.range f) ≤ W.ideal := by
        simpa [hpfull, equationPrefixIdeal_full] using hpre
      have hVW : V.ideal ≤ W.ideal := hcomp.2 ⟨hW, hfull⟩ hWV
      have heq : W = V := AffineVariety.ext (le_antisymm hWV hVW)
      simp [heq]
  | succ t ih =>
      have hpc : p < c := by omega
      let g := f ⟨p, hpc⟩
      have hgV : g ∈ V.ideal := hall (Ideal.subset_span ⟨⟨p, hpc⟩, rfl⟩)
      letI : V.ideal.IsPrime := hV
      obtain ⟨Q, hQ, hQV⟩ := Ideal.exists_minimalPrimes_le
        (sup_le hWV (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgV)))
      let U : AffineVariety n := ⟨Q, hQ.isPrime.isRadical⟩
      have hnew : equationPrefixIdeal f (p + 1) ≤ U.ideal := by
        rw [equationPrefixIdeal_succ f p hpc]
        exact (sup_le_sup hpre le_rfl).trans hQ.le
      have hcut : W.dimension ≤ U.dimension + 1 :=
        principal_component_dimension_bound W U hW g hQ
      have hnext := ih (p + 1) (by omega) U hQ.isPrime hnew hQV (by omega)
      omega

/-- B30: a component of p equations has codimension at most p. -/
theorem prefix_component_dimension_lower {n c : ℕ} (f : Fin c → Poly n)
    (p : ℕ) (hp : p ≤ c) (W : AffineVariety n)
    (hW : W.IsComponentOf (equationPrefixIdeal f p)) :
    n ≤ W.dimension + p := by
  classical
  induction p generalizing W with
  | zero =>
      have hWI : W.ideal = ⊥ := by
        have hW' : W.ideal ∈ (⊥ : Ideal (Poly n)).minimalPrimes := by
          simpa [AffineVariety.IsComponentOf, equationPrefixIdeal_zero] using hW
        simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hW'
      have heq : W = AffineVariety.whole := by
        apply AffineVariety.ext
        simpa [AffineVariety.whole, AffineVariety.ofIdeal, Ideal.radical_bot_of_isReduced] using hWI
      rw [heq, Bridges.affine_whole_dimension]
      omega
  | succ p ih =>
      have hpc : p < c := by omega
      let g := f ⟨p, hpc⟩
      letI : W.ideal.IsPrime := hW.isPrime
      have hprev : equationPrefixIdeal f p ≤ W.ideal := by
        rw [equationPrefixIdeal_succ f p hpc] at hW
        exact le_sup_left.trans hW.le
      obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hprev
      let U : AffineVariety n := ⟨Q, hQ.isPrime.isRadical⟩
      have hnew : equationPrefixIdeal f (p + 1) ≤ Q ⊔ Ideal.span {g} := by
        rw [equationPrefixIdeal_succ f p hpc]
        exact sup_le_sup hQ.le le_rfl
      have hsup : Q ⊔ Ideal.span {g} ≤ W.ideal := by
        apply sup_le hQW
        apply Ideal.span_le.mpr
        rintro z rfl
        apply hW.le
        rw [equationPrefixIdeal_succ f p hpc]
        exact (show Ideal.span {g} ≤ equationPrefixIdeal f p ⊔ Ideal.span {g}
          from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
      have hWcut : W.IsComponentOf (Q ⊔ Ideal.span {g}) := by
        refine ⟨⟨hW.isPrime, hsup⟩, ?_⟩
        intro J hJ hJW
        exact hW.2 ⟨hJ.1, hnew.trans hJ.2⟩ hJW
      have hlower := ih (by omega) U hQ
      have hcut := principal_component_dimension_bound U W hQ.isPrime g hWcut
      omega

/-- B30, concentration.tex:1045–1046. The consumer's regular-prefix dimension
property follows from the actual component and codimension, with no new local model. -/
theorem regular_prefix_dimensions {n c : ℕ} (f : Fin c → Poly n)
    (V : AffineVariety n) (hV : V.IsIrreducible)
    (hcomp : V.IsComponentOf (Ideal.span (Set.range f))) (hd : V.dimension + c = n) :
    ∀ p ≤ c, ∀ W : AffineVariety n,
      W.IsComponentOf (equationPrefixIdeal f p) → V.Subvariety W → W.dimension + p = n := by
  intro p hp W hW hWV
  have hlower := prefix_component_dimension_lower f p hp W hW
  have htail := prefix_tail_dimension_bound f V hV hcomp p hp W hW.isPrime hW.le hWV
  omega

#print axioms regular_prefix_dimensions
end
end DistinctDistances.TrackB
