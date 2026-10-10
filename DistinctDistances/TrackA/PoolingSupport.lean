import DistinctDistances.TrackA.Hilbert
import DistinctDistances.TrackA.PoolingCutSupport
import DistinctDistances.TrackA.Intersections
import DistinctDistances.TrackA.GAProjAux
import Mathlib.Algebra.Module.Submodule.Union

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open OAI.QuarticPowerFree

theorem pooling_locus_ideal {n : ℕ} (F : AffineFamily.Family n) :
    (AffineFamily.locus F).ideal = ⨅ V ∈ F, V.ideal := by
  exact (Ideal.isRadical_iInf _ (fun V =>
    Ideal.isRadical_iInf _ (fun _ => V.isRadical))).radical

theorem pooling_locus_mem {n : ℕ} (F : AffineFamily.Family n) (f : Poly n) :
    f ∈ (AffineFamily.locus F).ideal ↔ ∀ V ∈ F, f ∈ V.ideal := by
  rw [pooling_locus_ideal]
  simp only [Submodule.mem_iInf]

theorem pooling_dimension_le_ambient {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) : V.dimension ≤ n := by
  letI : V.ideal.IsPrime := hV
  have ht := trdeg_le_of_surjective (Ideal.Quotient.mkₐ ℂ V.ideal)
    (Ideal.Quotient.mk_surjective (I := V.ideal))
  have he := hilbert_natDegree_eq_trdeg V.ideal (coordinateHilbert V.ideal)
    (coordinateHilbert_eventually V.ideal)
  have hd : (V.dimension : Cardinal) ≤ (n : Cardinal) := by
    change ((coordinateHilbert V.ideal).natDegree : Cardinal) ≤ _
    rw [he]
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin,
      Cardinal.lift_natCast] using ht
  exact_mod_cast hd

/-- A reduced irreducible zero-dimensional complex carrier has no proper cut points. -/
theorem pooling_zero_dimensional_cut {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hdim : V.dimension = 0) (f : Poly n) (hf : f ∉ V.ideal)
    (x : Point n) (hx : x ∈ V.points) : MvPolynomial.eval x f ≠ 0 := by
  letI : V.ideal.IsPrime := hV
  let A := Poly n ⧸ V.ideal
  have ht : Algebra.trdeg ℂ A = 0 := by
    have he := hilbert_natDegree_eq_trdeg V.ideal (coordinateHilbert V.ideal)
      (coordinateHilbert_eventually V.ideal)
    change (coordinateHilbert V.ideal).natDegree = 0 at hdim
    rw [hdim] at he
    exact he.symm
  letI : Algebra.IsAlgebraic ℂ A := trdeg_eq_zero_iff.mp ht
  obtain ⟨a, ha⟩ := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := A) |>.2
    (Ideal.Quotient.mk V.ideal f)
  have hfa : f - MvPolynomial.C a ∈ V.ideal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk V.ideal (f - MvPolynomial.C a) = 0
    rw [map_sub]
    change Ideal.Quotient.mk V.ideal f - algebraMap ℂ A a = 0
    rw [ha, sub_self]
  have hev : MvPolynomial.eval x f = a := by
    have h := hx (f - MvPolynomial.C a) hfa
    simpa only [map_sub, MvPolynomial.aeval_eq_eval, MvPolynomial.eval_C,
      sub_eq_zero] using h
  rw [hev]
  intro hz
  apply hf
  rw [hz, MvPolynomial.C_0, sub_zero] at hfa
  exact hfa

theorem pooling_lists_subfamily {n : ℕ} (F G : AffineFamily.Family n) (L : ℕ)
    (hGF : G ⊆ F) (hF : FromAffineLists F L) : FromAffineLists G L := by
  obtain ⟨r, lists, bounds, hbounds, hcover, hsum⟩ := hF
  refine ⟨r, fun i => (lists i).filter (fun V => V ∈ G), bounds, ?_, ?_, hsum⟩
  · intro i
    obtain ⟨E, hE, hcomponents⟩ := (hbounds i).2
    refine ⟨(hbounds i).1, E, hE, ?_⟩
    intro V hV
    exact hcomponents V (Finset.mem_filter.mp hV).1
  · intro V
    constructor
    · intro hV
      obtain ⟨i, hi⟩ := (hcover V).mp (hGF hV)
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hV⟩⟩
    · rintro ⟨i, hi⟩
      exact (Finset.mem_filter.mp hi).2

theorem pooling_family_nonneg {n : ℕ} (F : AffineFamily.Family n) (k : ℕ)
    (hF : AffineFamily.IsPure F k) : 0 ≤ AffineFamily.degree F := by
  apply Finset.sum_nonneg
  intro V hV
  exact (by norm_num : (0 : ℚ) ≤ 1).trans
    (AffineVariety.one_le_degree V (hF V hV).1.ne_top)

theorem pooling_family_positive {n : ℕ} (F : AffineFamily.Family n) (k : ℕ)
    (hF : AffineFamily.IsPure F k) (hne : F.Nonempty) : 0 < AffineFamily.degree F := by
  obtain ⟨V, hV⟩ := hne
  apply Finset.sum_pos'
  · intro W hW
    exact (by norm_num : (0 : ℚ) ≤ 1).trans
      (AffineVariety.one_le_degree W (hF W hW).1.ne_top)
  · exact ⟨V, hV, (by norm_num : (0 : ℚ) < 1).trans_le
      (AffineVariety.one_le_degree V (hF V hV).1.ne_top)⟩

theorem pooling_degree_biUnion {n : ℕ} {ι : Type*} (S : Finset ι)
    (F : ι → AffineFamily.Family n) (k : ℕ)
    (hpure : ∀ i ∈ S, AffineFamily.IsPure (F i) k) :
    AffineFamily.degree (S.biUnion F) ≤ ∑ i ∈ S, AffineFamily.degree (F i) := by
  induction S using Finset.induction_on with
  | empty => simp [AffineFamily.degree]
  | @insert i S hi ih =>
    have hiPure := hpure i (Finset.mem_insert_self i S)
    have hrest := ih (fun j hj => hpure j (Finset.mem_insert_of_mem hj))
    have hnonneg : 0 ≤ ∑ V ∈ F i ∩ S.biUnion F, V.degree := by
      apply Finset.sum_nonneg
      intro V hV
      exact (by norm_num : (0 : ℚ) ≤ 1).trans
        (AffineVariety.one_le_degree V (hiPure V (Finset.mem_inter.mp hV).1).1.ne_top)
    have hu := Finset.sum_union_inter (s₁ := F i) (s₂ := S.biUnion F) (f := fun V => V.degree)
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    change (∑ V ∈ F i ∪ S.biUnion F, V.degree) ≤
      AffineFamily.degree (F i) + ∑ j ∈ S, AffineFamily.degree (F j)
    change (∑ V ∈ S.biUnion F, V.degree) ≤ _ at hrest
    change _ = AffineFamily.degree (F i) + (∑ V ∈ S.biUnion F, V.degree) at hu
    linarith

theorem pooling_rank_of_kernel_inclusion {n : ℕ} (V W : AffineVariety n) (D : ℕ)
    (hker : ∀ f : Poly n, f.totalDegree ≤ D → f ∈ V.ideal → f ∈ W.ideal) :
    W.hilbert D ≤ V.hilbert D := by
  let T := totalSpace (σ := Fin n) (K := ℂ) D
  letI := totalSpace_finite (n := n) (K := ℂ) D
  let evV := (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap.domRestrict T
  let evW := (Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap.domRestrict T
  have hk : LinearMap.ker evV ≤ LinearMap.ker evW := by
    intro f hf
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hker f.val (mem_totalSpace.mp f.property)
      (Ideal.Quotient.eq_zero_iff_mem.mp hf)
  have hdV := evV.finrank_range_add_finrank_ker
  have hdW := evW.finrank_range_add_finrank_ker
  have hle := Submodule.finrank_mono hk
  have hrV : LinearMap.range evV = V.restrictionSpace D := by
    ext z
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f.val, f.property, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
  have hrW : LinearMap.range evW = W.restrictionSpace D := by
    ext z
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f.val, f.property, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
  rw [hrV] at hdV
  rw [hrW] at hdW
  change Module.finrank ℂ (W.restrictionSpace D) ≤
    Module.finrank ℂ (V.restrictionSpace D)
  omega

/-- The ratio used for pooling, keeping the original shifted binomial rank. -/
theorem pooling_choose_ratio (n D q k : ℕ) (hk : k ≤ n) (hkpos : 0 < k)
    (h2q : 2*q ≤ D) :
    D * (D+k-1).choose (k-1) ≤ (n * 2^n) * (D-q+k).choose k := by
  have hident : (D+k) * (D+k-1).choose (k-1) = k * (D+k).choose k := by
    have h := Nat.add_one_mul_choose_eq (D+k-1) (k-1)
    rw [show D+k-1+1 = D+k by omega, show k-1+1 = k by omega] at h
    rw [h]
    ring
  calc
    _ ≤ (D+k) * (D+k-1).choose (k-1) := Nat.mul_le_mul_right _ (by omega)
    _ = k * (D+k).choose k := hident
    _ ≤ k * (2^k * (D-q+k).choose k) :=
      Nat.mul_le_mul_left k (choose_le_pow_two_mul_choose D q h2q k)
    _ = (k * 2^k) * (D-q+k).choose k := by ring
    _ ≤ (n * 2^n) * (D-q+k).choose k :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hk (Nat.pow_le_pow_right (by decide) hk))

theorem pooling_choose_polynomial {n : ℕ} (C : AffineVariety n)
    (G : AffineFamily.Family n) (D : ℕ) (hne : G.Nonempty)
    (hwitness : ∀ V ∈ G, ∃ f : Poly n,
      f.totalDegree ≤ D ∧ f ∈ C.ideal ∧ f ∉ V.ideal) :
    ∃ g : Poly n, g.totalDegree ≤ D ∧ g ∈ C.ideal ∧ g ≠ 0 ∧
      ∀ V ∈ G, g ∉ V.ideal := by
  let U := (totalSpace (σ := Fin n) (K := ℂ) D) ⊓ C.ideal.restrictScalars ℂ
  let P : G → Submodule ℂ U := fun V =>
    (V.val.ideal.restrictScalars ℂ).comap U.subtype
  have hP (V : G) : P V ≠ ⊤ := by
    obtain ⟨f, hdeg, hC, hV⟩ := hwitness V.val V.property
    let fU : U := ⟨f, ⟨mem_totalSpace.mpr hdeg, hC⟩⟩
    intro he
    have hf : fU ∈ P V := he.symm ▸ Submodule.mem_top
    exact hV hf
  obtain ⟨g, hg⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hP
  refine ⟨g.val, mem_totalSpace.mp g.property.1, g.property.2, ?_, ?_⟩
  · obtain ⟨V, hV⟩ := hne
    intro hz
    exact hg ⟨V, hV⟩ (show g.val ∈ V.ideal by rw [hz]; exact V.ideal.zero_mem)
  · intro V hV
    exact hg ⟨V, hV⟩

set_option maxHeartbeats 1000000 in
/-- Pooling needs only the frozen component rank bounds; its cut and
finite-union arguments use the original polynomial and linear algebra APIs. -/
theorem pooling_core (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : AffineFamily.Family n) (k L L' D : ℕ),
      AffineFamily.IsPure F k → 1 ≤ L → FromAffineLists F L → 1 ≤ L' →
      C * max L L' ≤ D → ∀ h : AffineVariety n → Poly n,
      (∀ V ∈ F, (h V).totalDegree ≤ L' ∧ h V ∉ V.ideal) →
      ∃ (bad : AffineFamily.Family n) (g : Poly n), bad ⊆ F ∧
        AffineFamily.degree bad ≤ (C : ℚ) * AffineFamily.degree F * (L' : ℚ) / (D : ℚ) ∧
        g.totalDegree ≤ D ∧ g ≠ 0 ∧
        (∀ V ∈ F, ∀ x ∈ V.points, MvPolynomial.eval x (h V) = 0 → MvPolynomial.eval x g = 0) ∧
        ∀ V ∈ F, V ∉ bad → g ∉ V.ideal := by
  obtain ⟨C₀, hC₀, hlower⟩ := poly_hilbert_union_lower n
  let M := n * 2^n
  let C := max (2*C₀) (2*M+1)
  have hC : 0 < C := by dsimp [C]; omega
  refine ⟨C, hC, ?_⟩
  intro F k L L' D hF hL hlists hL' hD h hh
  have hDpos : 0 < D := by
    have hmax : 1 ≤ max L L' := le_trans hL (le_max_left L L')
    have hCle : C ≤ C * max L L' := by simpa using Nat.mul_le_mul_left C hmax
    omega
  have hDq : (0 : ℚ) < D := by exact_mod_cast hDpos
  have ha : 0 ≤ AffineFamily.degree F := pooling_family_nonneg F k hF
  by_cases hFempty : F = ∅
  · refine ⟨∅, 1, by simp, ?_, by simp, one_ne_zero, ?_, ?_⟩
    · simp only [AffineFamily.degree, Finset.sum_empty]
      positivity
    · simp [hFempty]
    · simp [hFempty]
  have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
  by_cases hkzero : k = 0
  · refine ⟨∅, 1, by simp, ?_, by simp, one_ne_zero, ?_, ?_⟩
    · simp only [AffineFamily.degree, Finset.sum_empty]
      positivity
    · intro V hV x hx hzero
      exact (pooling_zero_dimensional_cut V (hF V hV).1
        ((hF V hV).2.trans hkzero) (h V) (hh V hV).2 x hx hzero).elim
    · intro V hV _ hz
      exact (hF V hV).1.ne_top ((Ideal.eq_top_iff_one V.ideal).mpr hz)
  have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
  obtain ⟨V₀, hV₀⟩ := hFne
  have hk : k ≤ n := by
    rw [← (hF V₀ hV₀).2]
    exact pooling_dimension_le_ambient V₀ (hF V₀ hV₀).1
  let cuts := fun V : AffineVariety n => pooling_cut_components V (h V)
  let CF := F.biUnion cuts
  let Z := AffineFamily.locus CF
  have hcutPure (V : AffineVariety n) (hV : V ∈ F) : AffineFamily.IsPure (cuts V) (k-1) := by
    exact pooling_cut_components_pure V (hF V hV).1 (h V) (hh V hV).2 (k-1)
      (by rw [(hF V hV).2]; omega)
  have hCF : AffineFamily.IsPure CF (k-1) := by
    intro W hW
    obtain ⟨V, hV, hWV⟩ := Finset.mem_biUnion.mp hW
    exact hcutPure V hV W hWV
  have hCFdeg : AffineFamily.degree CF ≤ AffineFamily.degree F * (L' : ℚ) := by
    calc
      _ ≤ ∑ V ∈ F, AffineFamily.degree (cuts V) := pooling_degree_biUnion F cuts (k-1) hcutPure
      _ ≤ ∑ V ∈ F, (L' : ℚ) * V.degree := by
        apply Finset.sum_le_sum
        intro V hV
        have hd : V.dimension = k-1+1 := by rw [(hF V hV).2]; omega
        calc
          _ ≤ ((h V).totalDegree : ℚ) * V.degree :=
            pooling_cut_components_degree V (hF V hV).1 (h V) (hh V hV).2 (k-1) hd
          _ ≤ (L' : ℚ) * V.degree := mul_le_mul_of_nonneg_right
            (by exact_mod_cast (hh V hV).1)
            ((by norm_num : (0 : ℚ) ≤ 1).trans (AffineVariety.one_le_degree V (hF V hV).1.ne_top))
      _ = AffineFamily.degree F * (L' : ℚ) := by
        rw [← Finset.mul_sum]
        change (L' : ℚ) * AffineFamily.degree F = _
        ring
  have hcutPoints : ∀ V ∈ F, ∀ x ∈ V.points, MvPolynomial.eval x (h V) = 0 → x ∈ Z.points := by
    intro V hV x hx hzero
    obtain ⟨W, hW, hxW⟩ := pooling_cut_point V (h V) x hx hzero
    intro g hg
    exact hxW g ((pooling_locus_mem CF g).mp hg W (Finset.mem_biUnion.mpr ⟨V, hV, hW⟩))
  let bad := F.filter (fun V => ∀ f : Poly n, f ∈ Z.ideal → f.totalDegree ≤ D → f ∈ V.ideal)
  have hbad_sub : bad ⊆ F := Finset.filter_subset _ _
  have hbadPure : AffineFamily.IsPure bad k := fun V hV => hF V (hbad_sub hV)
  have hbadLists : FromAffineLists bad L := pooling_lists_subfamily F bad L hbad_sub hlists
  obtain ⟨q, hq, hshift⟩ := hlower bad k L hbadPure hL hbadLists
  have h2q : 2*q ≤ D := by
    have hC₀C : 2*C₀ ≤ C := le_max_left _ _
    have hCL : C*L ≤ D := (Nat.mul_le_mul_left C (le_max_left L L')).trans hD
    have hmult := Nat.mul_le_mul_right L hC₀C
    nlinarith
  have hqD : q ≤ D := by omega
  have hbadRank : AffineFamily.hilbert bad D ≤ AffineFamily.hilbert CF D := by
    apply pooling_rank_of_kernel_inclusion Z (AffineFamily.locus bad) D
    intro f hf hZ
    apply (pooling_locus_mem bad f).mpr
    intro V hV
    exact (Finset.mem_filter.mp hV).2 f hZ hf
  have hupper : (AffineFamily.hilbert CF D : ℚ) ≤
      (AffineFamily.degree F * (L' : ℚ)) * ((D+k-1).choose (k-1) : ℚ) := by
    calc
      _ ≤ AffineFamily.degree CF * ((D+(k-1)).choose (k-1) : ℚ) :=
        poly_hilbert_upper CF (k-1) hCF D
      _ ≤ (AffineFamily.degree F * (L' : ℚ)) * ((D+k-1).choose (k-1) : ℚ) := by
        rw [show D+(k-1) = D+k-1 by omega]
        exact mul_le_mul_of_nonneg_right hCFdeg (by positivity)
  have hlowerBad : AffineFamily.degree bad * ((D-q+k).choose k : ℚ) ≤
      (AffineFamily.degree F * (L' : ℚ)) * ((D+k-1).choose (k-1) : ℚ) := by
    have hbadRankQ : (AffineFamily.hilbert bad D : ℚ) ≤ (AffineFamily.hilbert CF D : ℚ) := by
      exact_mod_cast hbadRank
    exact (hshift D hqD).trans (hbadRankQ.trans hupper)
  have hratio : (D : ℚ) * ((D+k-1).choose (k-1) : ℚ) ≤
      (M : ℚ) * ((D-q+k).choose k : ℚ) := by
    exact_mod_cast pooling_choose_ratio n D q k hk hkpos h2q
  have hchoosepos : (0 : ℚ) < ((D-q+k).choose k : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ D-q+k)
  have hcancel : AffineFamily.degree bad * (D : ℚ) ≤
      (M : ℚ) * AffineFamily.degree F * (L' : ℚ) := by
    apply (mul_le_mul_iff_left₀ hchoosepos).mp
    calc
      _ = (D : ℚ) * (AffineFamily.degree bad * ((D-q+k).choose k : ℚ)) := by ring
      _ ≤ (D : ℚ) * ((AffineFamily.degree F * (L' : ℚ)) * ((D+k-1).choose (k-1) : ℚ)) :=
        mul_le_mul_of_nonneg_left hlowerBad (le_of_lt hDq)
      _ = (AffineFamily.degree F * (L' : ℚ)) * ((D : ℚ) * ((D+k-1).choose (k-1) : ℚ)) := by ring
      _ ≤ (AffineFamily.degree F * (L' : ℚ)) * ((M : ℚ) * ((D-q+k).choose k : ℚ)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hMsmall : M * L' < D := by
    have hMC : 2*M+1 ≤ C := le_max_right _ _
    have hCL' : C*L' ≤ D := (Nat.mul_le_mul_left C (le_max_right L L')).trans hD
    have hmul := Nat.mul_le_mul_right L' hMC
    nlinarith
  have hbad_lt : AffineFamily.degree bad < AffineFamily.degree F := by
    have hapos := pooling_family_positive F k hF ⟨V₀, hV₀⟩
    have hsmall : (M : ℚ) * (L' : ℚ) < (D : ℚ) := by exact_mod_cast hMsmall
    have hstrict : (M : ℚ) * AffineFamily.degree F * (L' : ℚ) <
        AffineFamily.degree F * (D : ℚ) := by nlinarith
    exact (mul_lt_mul_iff_left₀ hDq).mp (hcancel.trans_lt hstrict)
  have hgood : (F \ bad).Nonempty := by
    by_contra hn
    have hsub : F ⊆ bad := Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.not_nonempty_iff_eq_empty.mp hn)
    have he : bad = F := Finset.Subset.antisymm hbad_sub hsub
    rw [he] at hbad_lt
    exact lt_irrefl _ hbad_lt
  have hwitness : ∀ V ∈ F \ bad, ∃ f : Poly n,
      f.totalDegree ≤ D ∧ f ∈ Z.ideal ∧ f ∉ V.ideal := by
    intro V hV
    have hnot := (Finset.mem_sdiff.mp hV).2
    have hVF := (Finset.mem_sdiff.mp hV).1
    have hn : ¬ ∀ f : Poly n, f ∈ Z.ideal → f.totalDegree ≤ D → f ∈ V.ideal := by
      intro hforced
      exact hnot (Finset.mem_filter.mpr ⟨hVF, hforced⟩)
    push_neg at hn
    obtain ⟨f, hfZ, hfD, hfV⟩ := hn
    exact ⟨f, hfD, hfZ, hfV⟩
  obtain ⟨g, hgD, hgZ, hgne, hgV⟩ := pooling_choose_polynomial Z (F \ bad) D hgood hwitness
  refine ⟨bad, g, hbad_sub, ?_, hgD, hgne, ?_, ?_⟩
  · apply (le_div_iff₀ hDq).mpr
    calc
      _ ≤ (M : ℚ) * AffineFamily.degree F * (L' : ℚ) := hcancel
      _ ≤ (C : ℚ) * AffineFamily.degree F * (L' : ℚ) := by
        have hMC : (M : ℚ) ≤ (C : ℚ) := by
          exact_mod_cast (show M ≤ C by dsimp [C]; omega)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMC ha) (by positivity)
  · intro V hV x hx hzero
    have h := hcutPoints V hV x hx hzero g hgZ
    rwa [MvPolynomial.aeval_eq_eval] at h
  · intro V hV hnot
    exact hgV V (Finset.mem_sdiff.mpr ⟨hV, hnot⟩)

end
end DistinctDistances.TrackA
